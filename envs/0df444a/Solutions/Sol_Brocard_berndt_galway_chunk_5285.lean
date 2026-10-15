-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5285
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:21:43.566101+00:00
-- url     : https://prove2.me/submissions/1fc23835-95ef-4792-afaf-484fa282e0d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 950359712 ≤ n < 950539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 950360962 1250 950359712 950359733
    0x609030c0204230c130b07080c07060c060b1f0804060f02070b0906070f09060f1803080901020105090721080c0f03120c0304030507060c020a0213060503060130 70
    0x1d601034108900740d40040d1001c861009980354510f41040940c40f0b1859505091189440100e0ba01e100c41e10100031003084074019000542c0a800058900081042400c3c101a0300390011004a205400d104080c8a154418540740400c1070700c000d81019400a1f4480c100c24641902c5410084488005020407007150040031071441a00e1041d074071008940b40c04441043c0407a8030480c40e04c00c10300000c1000b0300c51802100d1a50242d159840b089080c44011a904120600740c44144103003014002c449200411403007006600800e03406072214005c0b80020f0039603001916084590380070034010711100d00f003024408a100c030f20840d9141c40e0700702441c0a130164001e86107a0800c60050600c100326502011000b0a82c00141c18070701c14040d0b84035803032014180800d40300980000d01c00c1c801e040001e42207a0002c4951681801220540d000e21390005800b2200da8001250258581a0800030750904020382400741c2060b104003141c007611101121901c603402d9000d880c169030401075000512851150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 950362212 1250 950360962 950360987
    0xc010906060602031e0f040527010f08010c09050f13090f0f0506070801031101080403300e0a0206070609020636010509030627010213090c050c0a060903 67
    0x103040c08420358501c1d0280d00c0c0d801880030741244000c4101480c0030b00c00420201ca660364a01c09117182014188014054000d06008403400c02c882820344030441c1e810f000360450f000745100221030005a0900c0903650030340341c01d100030509100c1007041c20b110aa640b141c6030020b03000142e402e4040240b8402c40700024049031180030b014400c2611111041c00303814103032241451f00400403501103484044084074007070824400074003d51a6400c030302c90250321421146800600a01d03200901e03d96126904003481c002c2604c0d43c02041300c1014a401122642c0601c0c0041803002d005890100007a801107092440340c420000c0c4140d9585d030303e9100715030b0f5880c2a6140b0755103500a0713110328504d02900030030f400082841030082c0c10700805920020362281c003c507918100060050301c03103915889444050a162202c0740d000b084590448000d4803602403010300302120000c00715182c0c091401943c42c0132a072881448400300321b01000301c00051040081c1c0d8400e0b4a42c42000010140c41a0804076401c40c440300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 950363462 1250 950362212 950362223
    0xa03020f0411120406150806041b05091618030506040602031021020102012018060d0e03070209130c03030e0d1401050a0b010504050f0918010204032d170c0109 70
    0x90f118000e10b20125141d0b10982c895803042050b001c014070b00b00366500062203512026807261000500048410809080f00600b403111350030825124000903909890480341118940d151200303144442d60b000c0444901d00100b0900f010f6107034103548516440d4000108058072207a0004045100703001c880850b01c00618511494224202192914090817404100180d0041d0308000000c84101141420340d90708100014090b0300d0441c41d01d00544c00040174201480c0d00801c14090484084c805011b0480f207000480c020310303942c40e018810800f0340c1030060070001031410350081c408002200d243e07085050f0398240c01c103c00b24000c0140000d03503101c0260f100900d00102c0056814003403405410076405400501d606101d860851401100c0600070351080c0f90348444101c00885c014140303404102d0708500c991104a04240313500110070b003603031302c1b80d4801c0300d03c40c04207880000050303949014200d504c0d84505404070520190344a41121494414606000c04800600d00c010b400095002060096004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 950364712 1250 950363462 950363467
    0x90a0b0315061306031a0411070c0b0310061d0307060c050f071203050706180c06030c021209130b0d080a08010902030c180f030703120e03070e04170f0c0102071a04020a03020f0411 79
    0xb1700c4281c03160781207078908607000b04044100bc10091030101c00d591280c20400f440e4070800e0710b015000c41d244240c440071002407000b080c940704120784044c40b01c040645229200c10749000719030328100d8074001e00410131209541242a09100000c03075250003035207507500b6180882d00c0360003506100004180348800200d94107060500401040103040c4800110340641e141000100341046081ea11840c02003034445880504000c4025140350181d14007984402403580003414a01510100740000c0307291314190b489400100c1e00d51505079000140c035000d00001c0005506500380200503106c1802107040c954110301c100c0364020304503196054480c4151000030201d60000360f803814034071960300c06030130f01c140010010703500c803a014200002c0b00c50850305650295422541c9a440b440c2c1d81480004400603030030310801503900004607841c05440e6003204180016580d01192600354440c03030407070a02400850700d080c1084090b94602825100b03c07034058500745090041c0d00001401004500c401c0c4000e40c1c400b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 950365962 1250 950364712 950364731
    0x70302011e050f07050d0e0f011410030b01030b0c0c060f010602070b1e0307020133060309052e02040e16020a0b0106050f090a0b0315061306031a04 65
    0x5420000785000641d400031041c4200700c0c4440d0548034202c0d2580040810f03c004a4580792041005240c1a040040f002030b101a00201c61414900070042503602c0f170b034580c0c0c940d001600e0340014044e0401842065509510718699880420200500c00901003a0401002904d1080c1c001c0448000c10002010b890552500103241c015960080c060400140b2a208001c1290b00c0d030181100c4001211444819071400d20529001da2a480104801d0031035403520712910025000342c18403158607914034060b019148040c940325802c07102950182003098204854040410b8000c624500d584840380500340b002040351070400c0091806c080b00c020154400a8005914400000d685001c0c0140206543d0207442c1d55004031381c2d0f0144240d010b0000034941c00100207046c01040101402003080340c05500b0048900c0000e0041c8031103a0007110702e800b001042294503034103070440003006182224840d007025040801c54418080d94040d010a25550701441e441c01e480b800781c00f444c81d0b18001c05c24408240c4c1d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 950367212 1250 950365962 950365967
    0x18241b0803040b0a1a060d0213050a0602100b0307140108090a0b100603140c031f05040f050a0e0f1b040e03040603060305100b030c0d031709010e1b03190c0b0703 71
    0x11a0410f00701450034200e9a840c443c03170118400d0482d002031450f030030b007904000c441d0000c0d070280b01200f00e0ba140042000903552170750042d11008000c29000380041c003c9074881e203000d8601d000d040c14400c2c0c01134a810b0108072803010381115202070070b00c0d021010350307130f007030302036490001455005091600d800c01000090300d507245d0b0707080a42c1c0c600c0d5001d01001c8040da40d14900b40d40240d5203c003c0ca00284001855105402c2e8030b42c3c02c1d40400d04265841503500c0c40850211400d4070310520203561114104901c110311f5000d48490420032400800b040c030003070b13918641c85101c41a0100c45002c9681540d00083ea1540c1000c089640110182c0342d98542d2010040e006245600c0304030740500404511642501441c40b80d0f40541c40081c010b0054210500c1c20032010780d0400030110140b01c04074042080c0400d00001562240c038807180000780c6540d02d580d10906c0c2440910221203066800e040d0400325840c00b00340c00e4040d07160017101c1d242100d07007481c1142d11081c450f040948106000700d100c00c141076 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 950368462 1250 950367212 950367233
    0x408031314011d0f0724090306050f01050a0815010e0705070c08210f0d09081c0507090503010908040b0c1c030b0415050136030318241b080304 63
    0x20380c00c2048400f01d41404013201e40720165131080c1030380214001090705030074900840c2c914400245240c0703120520788aa0780d0004884003515030302c8035007100c00c00510150620020300d00151218000410840807100b206802d6441c0500400c40915481c2c0701117014580100d0aa0700c0341944076021004041c0c403582040d940e11020103654880020b04003010030f80881080450711003a0300003444900d0607031901c00200c01342100311401c80f1050010007030103090308101c11145480308002d64002c00c803824070b03000c000c0c80165260402c0f8400d91400a1040010b695003003118101d4000394400d540303d1182c4041d460405550440c08803005900d200d40c8844550316600c40303e480e0004850401c880c4d0601d041c109886941030050fa804180e074010250307024031104041951440c203005140119204d410380c400d0b0303890010341c000c0340420200e9211032070b050035408440380036000d40d40e242c41078120740c0d0410128140f840b0f01070509200d0000d4040c0079450301210301c0d034030f6990455482c0b075481c2018039000f40540c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 950369712 1250 950368462 950368511
    0x1905090612120c0f1e0304030b10090203041a0106030e07030f0f0807031e0c020a0506031005030d230702010f080c13060e041a0907180f1203110105040803131401 71
    0xc1c0103104030b00100305c6696000d06001540d210045042c642141d5031501140000740154540080c1c00340300041104150004510852007104003d50fa2040300041055001068002d14203050916030b07148187c11000400b0000c490304541e0380c40c030b482c44904020315250415a4042d040060001d00141815040110321045d494900c0300d07030f01e901002c85421500300c0300804d402503028240b01d1003000a032520b18003441d00403900c0350146941b80c1c2d5481c0001d14040c0f44610711000301d02d2190600300414080404a03220380c1040b44010318144895000030101c10b00c0b01004000e010281000c204004440340507500003182c03410304200107540b0b44001030401c0c0c415084c001e01c5541454100c0303e4100769090f000980c401c01605c802d6464450a40c140e49242c480c1c040c3c031031200f2001200248440d641d086100042c802200d002c0721001007410003c0426250000072003a982c102b805020000d01610101c03a4806d15140d0080c41010b124034107291340c10308140c2c0c070307010560810342080e0440840d4462004036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 950370962 1250 950369712 950369743
    0x409150e011203080c2b06080c042a18031109090120030601110709051503070f0302010503060a0504050405060126060115030e0d05091905090612120c 66
    0x6a039071854002d49441840000800042e06000031a54207540840688000402c84c10006504d0b072005030305060110b603100351020416111f0384100200e50080c00301401c8888156414083c02218080c0c407402d120b03100041003c450400a6904e00c0780e449081d243d050707040060550000196a418100c0c03050250030713201071041c5509000304070f002e0f60520a4110404010854141c543d86407003031300015030801001c06061181c0400d04c0000344138144040c50141014400010b2141001410324504840f0003880c103000741d0000005002c40320307440d64888201ca909107441656903446001144400d4190b40c0b040d03412604000500c001c03c4004554581030340d61024048180e130900f0035011201e800a03600419640e00000018401c0c1d6001c0104450700c080a4140801c0001403000e02a1401007100c2058001407400300e1505424a0540c00003640400001040380c4040c0c00c0c0300028140d41da029041510034031001240b8981c4504c14040a490f0030298445281c13075249401449465003c5142421078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 950372212 1250 950370962 950370989
    0x1506060c02130905030c070608150f0604030b07120e03030f0c0301120212070b0c0a060608060106080a0b040e071823040f060e0307080a080702060402060d020f040915 73
    0x52251095900e40c40380c5400501c0010018507104409005100940083d510717400104510102d0300c10421820b4005d00c103d98604e07100c0d241800c401c0410155241c03983d07204000301c2c1c02221155460b101514180d036000080d09080c0d4481e041c0650b0360000141d6a40d01d0141041e600b0070802e003000c00a07620416081c0c0c020f03a015a1110010038013407000b40100c1500e204030800340e40c05030510fa13100151940c000d800300c3d14001c2d01d4000e5209070f900109464a0305600164060701000002d0146100400460303004140e036506018000d00340c8840140b4041d911aa140e0b0f04850a030740710780001c46072030322480a40e80416162141d03c500500c01984920f1040c3c00d210300f00000d0201112911a030345810750a04e2115201c030307a1082ca065080e400190f5800d42c031004601c0f91483e060005143e0a8403844102d03548140b0700790060410703a030040030f400641d0000801c000160300c0307800803124800050703440141e56501c0190460b0300b600072500f20600c080d00d032100704468401c1c0901e01c80300340e4080300c00f10007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 950373462 1250 950372212 950372219
    0x10e040b030619020d1508240c31050a1205060103030c02031c0e091806010510120f020d110c0312220f0b16051e070209041506 56
    0x10039100c1810080750507601c02c100050010229402c0d42c400043c510002501e8080c14260b448251403002c415111000107099003081100001c211050081c0c3d0065529982110f0124040300720840c028182e40e0f0707156000460041140c0e542c0500105224006c80c01c4d446000303003407070016408086004590043c140b80c4000f1034032090344100f0a9a40798810024142d036070965904a03900c0f980310404036094070404d140d40c021038119503070210140181c0c0d503d130b050001d204800c12425890142c918a0542c1c0000d000c1c0005007070108009056031000d5a072408041500325080f126000c040c22901030301450030b14103520034104c1e038008084850704120240300050f40402c81000b2440781281003801341c0e1040123212541003503c2c845503407040c0034942d07400c400070303250340d44452011110404480f40480d14000c0d8007085010680030350445000e45000c01d9040b1220005065071052032034195031910403104e8040306c248201d084032203159004d011044241010f1503c0d98800c100c103050310910505090012 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 950374712 1250 950373462 950373469
    0x110f01090804030f0c0509010605030a1401030f0212120d0501080f160303110c180403020d080c040302040203100f0b04091a010507080306150a180b090303030711030409110405010e 79
    0x142659000041c0901d05440d40d500e012030074032048801c503031200c80315200150581d2032080581c000d24043e110295640303454200038003101e1103c1c01200300203c1c0034005101041d140800048600d0341620200300306580c1104851400e2042d81001d920380c6400507011515400d40e07000681242c2d0f614046030301d462000f410460b107a4911010701291903059000c1000460301c207502042e44100c80c0d0741a1031111503218040342805034507205c0303c0d070303103245000c14001010380c104216a009a080e103030400047c18000b181640d0b9200b1840003031720540e00880440d9420051003086402000306500340c8103600e607600c038a40c002d50403030312942001520340680c0358070302e40d007a085450861405135a12454020b455954512a400252090360440d003c45055070107400c0e076000a02c032103651a102e52840c4440242c0c030003600d00c2070b604455a00380c41403004d200e16803800410b072a0040c0311814034061135180d0242080c074500032a40904070b000e08002f042e40c400341842d00100240d41c402c0c0d80300700c45400d0b1032050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 950375962 1250 950374712 950374721
    0xc0c150718081b0d0606030203033402060906090402090913050d050a0504060c06291201020903060604020a0c05060a060e01060e0a17031c1a10050d110f0a110f01 71
    0x28802d60301d103040c81803c650300d0070080314012940300b010001a51512500803d1540d089440103c061600c00c240441c3c090061015030700e018001400c0315182d8040f00c2d404a4400d011360365449004100104080409544580584140c50310140074a461071602001082900003501d1050322107025041c81c00909511070411a0503100d2503880315460a49082c07811681d400c0d035610b040c3c0740c40382d944200031120082d0100c8043e00c02d8282c414400350300e0403070003005000380c5001d00b10386c400d038410860b040c1c035602c01060a9501032400c5500580701d10f00c806041d9041001c2c0d58004ac0b2a0151904100e1010483e6010700c05582c030901100006a072103400c182c404190790b0402c0c40e400702c0021010041c4123050980c502e1039040000a076414000c20320352202c0e200101c0c400c1d01c42d000d51221b1044203440424160220303090401c403002d449880c1c83c1b08001e002d52003692806000b6503203030b031241320808800700c080300c1c03001858842d1179076141e446c2075000707012042c0700c1050740e050f0107003d01440c0300200c14042c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 950377212 1250 950375962 950375983
    0x109030e04050a0f41070e0402040b120411030f060a02180a060503040c0504050708062202040902120c0306150307091203050d680c180c0c15071808 65
    0x54205131758a86410947e1406004c98240e68016000c01010900c514142d0190040c0c882c0d212001d0040e05040c0b60000184069101c070304d02950161042010101c00050708940240d21004010390340c0242c0c0c50282c01c1c009114510325008207922000151680c1c0c00b400440c400c03030140e01350142c1d0a031103030b00b0071096030800d4070400c0001e20400f010600515100342c002d00c141d030001446e81c0e03610440080303500990704643d200048240c3e001c0345403550080c3d0503030015405000007001a240d841d10344000b41c03040c5005400f0410f0305601000064046e801024041c0c050110340b80c50940302c035024030f0002c107254042c0d4030103020b017820080c0002c980e6840d07680409a68049075403051f0014448010400c0c2d00c181a00002000c004074048401c0a0031001d0403104913207404002c0c0450005c208031174620788607251105600030011507031001c3c059019112110707003040000b000c5542e641f0383c1304030051920403142c1c00002c04250364010b00100540000c20008844898400e65a0383c07541c4420054440c9030851 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 950378462 1250 950377212 950377331
    0x2030d0c1a150609012d030e0303010506160303020d09140d020601031110021e0d1706010f0806031f020901030b0405040f03082d06040e0109030e04050a0f 68
    0x2d0340d400c56490000050036002c20306140224000d41040000381400b05581e407201882441e2040502c0666414051010820040c00045145524050108440340720301103c3c0d60383c281d5038203900d0080522070b0b0102ea4448070740c241c041c418034195003842e0102a800190018032845030103e041602e60011a01030b04913a00402841148140345003441007903425000d440007107001d000d00d00e00c4903a5800101d001103142d5400240f40c003e80a100182c404503410401412100182c020004107a070302c240c1c030201003040c901e070000068940502081c90142c20300e007683d4842c004103501c00c0030748d80a680642001c0d58240c3c1d042c40300b5500803060104a900c144c1d00070b4860b000042c031000219003d1150740c0d4000b900b8085031303100c2c3c01d143c1e4040c0328410752182440192480030b50038010380345441e011360144503a0643c000c01840c00c156a01500001895540500491311580041d9224015a000745c48840e40940c2c2444030380a444112804a0781c11003107038501844007000c0c1003030507040e006015506214403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 950379712 1250 950378462 950378491
    0x8010507080c030c07050102190201150e06011232010501030207020906060c07180204030c270b01050c030c0321010b0a08090a020a0303031409010509030a11030702030d0c1a 76
    0x4400d203040b50b50000b8441000c82c0410420100010070910092980c200d810404400030216528000c3c207541c041c0c91180f400c4001d4200c00c1c41491805032005d82c210909091841201d00200189800b400b040007024404a44c9078681d04039460700607a41811644816504200e180e8031000103404a00848101a4120020400081d000d06009000f4207103111000d0846040036520040c81110713210b18400081b080740c000c501081088691440b11024102c8071890410300915030501d892208443c1b410410b0150b1514007040450b40150210358441c0e110350241c90340c90f80c100ca1802c1e500d5114a4800f8800358541e0032600006800f41402c6058402c0922182d25081c0850005c441c422009404401d65001c4c5084810040c0d0b0307001c9901c0001c6100b610041011005141a2044000010002c000301d9050108101090b00044121071b15400710b07090841c454030903072040c24030f18021111b00075051702c50b9000000880b60000e54805070350f48500445a28280c4450401c4072501d410340307201010f030380f6a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 950380962 1250 950379712 950379721
    0x102130311030a0605010b040e061c030f090b030a020a02070e041a100902070b0109051e1602030d02070b0916030215180d030f110109020a030f020d12180801050708 72
    0x10307a09202441a0050454810740040d880b6401104d80a030b01a0002c04400a020425082003090040e0302070f20440350740c1074034600d03008110110b01110718000c04100c00c2c9a069524607000c1e0030380c41c01800850003165140d15218062400943c4540010405482042c60000d100501c002c42c861181e5440104040d822400a0400c0542c2c42d02500c00f40740c00d903024902040641e00752001d00921401072420107202e5240c8240c0e1000c071140036000c3c0100040194665215118404501d84c1020b040005810035450587d0101d007980948991100c0b0b40b800003a44009100c4554040340c0100d0159050b01c0307018503074183c0c43e00c1c080c50314480203422503c0805103504003040c1c1006411a0325004420544030070801c400500c0c203070303001c0c3e40c101d0226040351a21060541c1c0a102820b032081d19000802c9528115000250801841c0c0710040070911202030100031911680c400d40111984003413030400c2c03038041001c0501030322000b01503100290440030f00010702d60014014180240320b191100c42d00303600d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 950382212 1250 950380962 950380973
    0x5041410052a040e04060614060711060c010204050402070f0201090b0a021b1f02060907050a0e011703070b0709030b060409112b081206040c02060f07020c0a0b0a020f01021303 77
    0x10910503601511030300f0700c40000c0e40d640560003940b04920070800003482c181001c905101e440d01154105010741c070107005280010f602106000500324003199065141c5a60040d514064401ca40149411600108018080140c03580d1001042c0c0d00c03d8031500e001607100e84d4416210b0241000e240c0050b8003c0301e41e0720618101680320742400c030001c0c124015610362910410789504203880c0d40001030f401041041500e00b010b200240143c00125244001a40340501c21030000206000721a01d4034ad10310000c407100001001114101a80000803501d02d28110b0000307400c043c00c510041d48c23100d00440000714546464825001181d0f408002045841000c5090010410415031241d803e00400c003000300f51a201c1c601c602003001d100748809a910441c130791250006c11005003c0750301480c1000d01420540d6004142180e02412546210ba00c07030340c0d80c804c1245409409840e464000072140004141030000310010000070000d40c088400b203840c0c001c40c036400c0307228401080208504112080c400200b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 950383462 1250 950382212 950382271
    0x71403100f0b0603090a03090b04080717010605090108030c0c010c0812130506090102180a06020a0330060e060d030f0f120c0207030c060507260d0504141005 69
    0x51032030300080e42d40d200001040241d8416220062540e00008a0000b05540088110041c1c5103213800c290509141603045070f40c6403468052103111003600041809105003d6200c6001440d00401d0540103581d40d070039150303c03503102000e003e0007801444c0046885500400802d00d16560028000b441d020201d50b00704505940603000c1d15100140e64a400081841049401d000320414400182c0c3c50b5545a41501c4102c8400c11090042d14020020841950041040703402d00c0c2e0035082020451104429003900d1581e90100030950b00c021020a406203c0150300c62001d03595802c596100ca901c03044104038415039400780040001c3d940c00d03541540380d4424140d004460120b400d040d42c140f0030018480c01079424a50036480144d0100c1800c04c02d218111034800021b1000f420f00603d44000c60311000c00e1704000c6581c049070040028211282a80500111010484841003c1089d414070789008041341d000007400c4c103424441c22080241c030520600c140340c02000300ca40c40042d180400030780d5103004d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 950384712 1250 950383462 950383481
    0x270b0a0e030d0509030c19080703080c1312030318020d140a06050108150717010b0f070b040506061e060318010b091503070b090603040f02040e0703030e0307140310 72
    0x1d000030300c08191410000e02425004500940c059600c0398492861a85000304680c0a0040300700c4180b80e0700e000c40c480000b144d46058240c549050141e48030009030129220303580c0f03d200100c0d2003c50001d10454001c054400c90352080d6024040e50322170041d50104650a450041d45c0040e8200202d0005070741d850f50340b10100110000c2d180e00701066100c400480b24260300c0a61150021001c4410606044e06490303840030072402c0549030790f4400c01042040d0f00050060b4030043ca40051207000d40010300c02035544903640689001007518151400d192285401d4540e00d0080381a6480618a2081c0c0040705d504604003070240e90440c3e0341d500391b00040350481408015a5540c800c006000c58a608c41c15600c41c4805245103095607082400f49464103119034030034005c8060030710411109a580c0000c030b82e04550481400308400c00c0900014004103a030501880641c80f0b455400010507800c00b04219100200310207440800c0e68500040c2c90a1444014440d403540002d0503a201c040f41d554807421aa = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 950385962 1250 950384712 950384741
    0x30e0904051501331404080109210903060e07171005060f100311040f030f0b090309010e0d02120706030e070b040302030601051201090f200f090c1b010906270b0a 71
    0x55101040c04a0450740c82600b0400c510307510340601d0f0040c001200801c0e001403081511107220030fa122b40d0010005840ca002c010516503c0740017220658004204110140c1000c5010b5018001c01d8400c580e51200310340c1039040150704060001c0c0303c5252032413030060590006003c0c22403600360440110020b00700543e022803c00c0040c072010030942d51070007111001c1c40c0310320508210000303181009070004100903d51051507000f0008440a664440b01800122001740e806145074115403002a09083e030051194407540703e122800131307250754503400c8500c1102034081580d2007503031562001095803046003c00794065021000410950405c10b841003140d80e0300c880006030107813060f83c6104542611107030136a44208100c0144607484041601202c288904070740c8151044a03a034003240000b04014070800b101c9a001c986280700d00d122144906030309110000802a1000c203203805401000190f210310340b44038001da600750030000c6030500c149281d50841140703405a512440d1200140080a00ba400c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 950387212 1250 950385962 950385977
    0xe0318011b230f070801140a020c1009060e010e0c0f0111060c071e030801170303090c092a070b0f0c0405060a030603050105100806070905060d09030e090405150133 72
    0x425220502ca2600604441000422504d1f1858465000c134800600b0b4181268410066180b038004001400040400c2007c004580001c10b81000002018a4800c25886509285d0f154150100c08a0300e11040d07035003260455000291480115422126030800410075401140400c1480140d031000e881c00d984a1780803000400d001143c114280c0c082007008801090100005110381d000300001c1c00210916030000b142103141103908507640e5280312900500481100010640421f035410005010b01c50004e599450030300078601860040e40f20420907520310310a03c01150300d480c000e5044034014951142400d05103401c050070491107510400310b0314140740e641d510000000d8020b000381c1e4840c80805040125151902403864201880100395100f0010311440030b00240e6200c106540a580d00c035000010900a07902e000d84210310b0641c0c440340d012407050204410071a000a003103060300f68100d10541c403640c0c2c0b404225868a00040604909140400c0000303190a407029107a1f5404c070349107011003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 950388462 1250 950387212 950387233
    0x90e060d021203091f12111e18330418050414070b04030822032d02010507030809010605041a0f0604051c05010e0318011b23 55
    0x1c140602c958602c108a403c0403941800629000d000c542c00c0811182c0060441002800000e02401000d41c10700d5180d41d80740c034140690b1402da01600c807809013228200300004810464030005410040300c80000680036a0707030154030b081a13002030f8000c0c000d050800b01111a0f807001d4034035904a80030603450051051000240446901440034040d035092140003d140c2801c2c281104840019190030100754450502002180b0442c41201d00b182d070402d000c0d50b2950700d1003001c00c0100005050403030a60b04658408824030070204c0280c210103441ca100c41400018840110060700d40724000030f8049001803000c4004a8002e60007194002c50640002074581d45a0000070111441424002861510300d06080000e040c0008500310740d5804441d000e007081d00c0c010025803174114031411100d0b0500400c02004c02c0000940010020304a0070042d60703110f4041c0036840203d21101d454170f900145494000c2c8040e0200402031504480c1c0168a01c2580040303030b0900b1010402c840701520480c42400d0a14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 950389712 1250 950388462 950388469
    0x30a050d11182b0b070f0c080405040e070f0b040e18060a0b010519020609070605031b0903102d0507141e043f0f2405010503010f020703090e060d02 65
    0xc40e00380e48200b280c591136040c000c5004141018142c111401d004019a040011034210300035181240d1081f10003280818417410543c0c28401250b012815124403400b010a10404000c054426210700240c001001e40e2407007800c600443e1608900010303030f0842008290120f01702c1d0405401c19078181481494008404d10041c03020304424076850058214006220001d0400c1c00003d000300302901e0141d0550404a200701891402c0241d0307030030801c900181900d456182444000440c40e5218410491081400c44000407050f41000d2001400450303031010003002214800c1074016581c13032b41c07103840e907041d6000749034031075845581d840c07400c19013808071401080e5442d8000d00c0a0302c052445001900070780703144810117a40d803002c1483d032502c081c852003845103070a40b05507850b02d42021803c0b24200b26400c2c03450030810000e000c1100c001c4811000351a108490300f0003412960190000c004004c4101c1408041b0302031400000d000400c401010081c4101c8000e206400920080c0900680c40c15036000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 950390962 1250 950389712 950389789
    0x7050f0f07171c230c0d060f08160e0114090402150d0e0d030c1e03110301032001091d060a0905040c060f020d0504060f11030a050d1118 60
    0xc00110015039030700d481a40800f030003504c00c502880d0214a82240d9024002c02000301c0085c941102c0d4100032501b10b58001040d04060004c0c90b03616200811507842c0d00c603c680f90464808642001036803038800041a008200046040354414440100d80080503010010340c0d02c406801070780c0c00598404640381c8042c40348028400d03264840310000d400808104580d00b0082104955420715140880700c01d500c0740c003c4601d040b440c0c440c04c40210b40d0403201070150014007500c074015401007070100000c0100100d80c50f1003406030540d10401c14074020000011a105006070081280003003190030401e40c0301c5d46e050b0030766070400c2005260013a80350f15050120101c800c1101c040e520080135000c100102500003802c402209a644080c121049642502600500c40c51096400300300d00404400021403142503074483c03e12000c000c1e281c3d113400f03130310004206411100302d031090a2703c0e10050202c05010718080740c1c22900d0150f4546155810b0307030f04101c200c181441c950340e501f620504c418520350310030041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 950392212 1250 950390962 950390977
    0x50903070201091a04051320030402040e1b0d0c120b011703030c0f091c06020c010c0c11010f05071416080115030b100b070b0f07050f0f0717 62
    0x159154101030000500380c203c0c6034010110360141c40c460850a440c100300315400c2c0e60041e2400005240d17a14102401800c60400e580c22032841d46d03103507c1e0440e0089004600640c000c0750300380100004000419129a403240c44ca10359156a40c80042e10703414041002a500d0380150500501113a03582c0000c0c0310701300c0031842221040300702e50040c04020000c4002c00c02e40b01c20740c0001c508524104007a51660720400200c1d030b50000012660072140d507200460341d146c030103569184001b9030740700345091340c00382d0016401c0d12007030f509100c1d03003500d864420f41c004272200750050840c50004040c40700645481d580d140e01d4500700681000f9140209801d00300b4602c101000d03100518146066003503010f640303c0c2c150480401d0b03034144041540009400301019064030341210b0041c1c0785840e880b9041c21b04044940c40041102e8000c5001014400d1880900d88603510a80340000c499960140c202d403284102e00075481040d10601032582d21140007000b42403080e100f1141c500d4001603001e18040c081c0c01402 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 950393462 1250 950392212 950392231
    0x5060406050c090d02270c0a03060e0702190804170c03010f23040302030c070b04030203010f0c172e0f120c03060c090b040306090203010609050c09090a14130b070206011401030c02010f05 82
    0x1e0041c8c001c9506214900060428100c07001142c184500c000351a9400091822880814503196405100c01141154000c0c1082541014811810700c90580c4808070581d0f02d40c443d5103440650002100d81e801213500042c6100460402d10010440c8510244400f901c26011071206012000e04500100706050240c129001c00e035071211314500c100b40c2501c4148050031a81c90a0241c2401c481c1e40041c580e01c003008810f0043e410f60b90703960003a0f011100f002241425400307a0000030400040342401c17031406841116441c2c040c2c00d91158161014444c400e1001030a0034512401080412174035803010020307800b640340070802155200b10022194000707400541c1d0042d40e86404d14118a400d20540c1c5c001c141c41e520520140c41c001c140311409000303c4400c1d50103000c41c1d20002d80d01005d81d81c0544007203c5089186002810010303070200504d041c100080b2024070200d030101d03078114000100207049512000c1300600400c0c1031001100985070090b1540305641d211985580c000c045402594800c0f500d54 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 950394712 1250 950393462 950393467
    0x5070509040f0c0b0406080114040e0106090b04140402030a030f0309050a03080a051302280e04120f0c11010c03110609062d0c09010c06050405060406050c090d02270c 73
    0xd09110780100c0c41a4010366480800f00400c124140c7c00c07008450445880d4203091021029220118015001e0341804000a501c0c1c2000031407a04c10700d6204204400d41614104802c20f8040400e40750700d141a5000380d8103502c540c0258000030301c41e0082844410051402098014155403010720b0040310030301c00c40200d003a12040040c0d403043c511032182d200301c961a0300c1540c603a60f038000c10007800300707042145108040e20108892031000d0807034000041240f081c82c0303c418602400c0240245a1254642d80010303517018280415522500a40c52640d400200c4451401201801540c00c0d400701881107003031000b2504180e5100c241840054421008240034105031310b0100c1820650507001c20b6803001c0107907007038103440010455851640e880341c07500d00d515546401da44e0058409070040d2000414043c03c28040004010012036401d004912914080c80f058649010280007801034400c40d5030441c000c07114841c09840c1c41c01c42a42c03140302107541c001014103c0383c0c2000c0c9401080385e400c138000900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 950395962 1250 950394712 950394743
    0x90c0e040b04031b020907141b160b0a090b0306040615020705010810061d0f0a030303140a02040b120408130905010810020c150a0f1a0a051014070507050904 69
    0x2011064094007600d1207118900c02d550000714100f0703003c7c02c0281000b000c40084003414504104550790804000380c0d4010075501903d042d542e0700c0100d1001c20594141e2040041c0c5150002d003912070240c055101c642c2c00a0500001c02c48a42004205a41c042c0d101d43c000554040d5600e802031003204158050910030b4103101c00035100c00d1000c0c24108070350402d0f40040169a40c02460a40c5801c02843c0848180e88250000b50700d260301c00a072541c1c05280c44030000308260b010b0344481c04403203d02070b03a49000e42d43c07800207800728051031082d210489010401e202c00c00c804440c40781d500620500340c082c00d0200c1442c5625484900d074100e51078040e074820040c810020104021411500d05410035454500042a04c54a403d082c103020102e8208040104100500c40c1e00054200d03580e1480400c140307890003138801a180d024003030303170740c0110000f40c00800d441c10003e034000304c81c5c0d100f43c1320700105048100c0a03203600d41c03024000340c038680124100821035030341e410300b0704d03001d14060310b00c03000031141 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 950397212 1250 950395962 950395967
    0x405060f030a1116060b0a0305030a08092e0b03121b010608010e190c09020703050901080a0e07060e1507050105061c0209010302010f0302070b33060d090c0e040b0403 73
    0x43c40800c034078030144140035811401c06008641000145e01542c0801d03107451a00c007255442005810040007408040f030420021948a4092446100d014085903c107004040700b601c1480c1102080c42f0404800b62245030035007000d40c11500c0b6965001c0e00725040c000242a14403600d400c08040d9440d158400c0c0c4110140d0070302405800003512500c00200b05840300b1080c41562114020340c9000c3d5011000204018406000070840040c913188406540d107030118600100320303038004481940820010700108600e403665214030600300010790000d0100c241040802c0c2d44640e01d460030158858001003500340c0d240c05490190040502c5900049041d0038508200129840c10814a1804d0420840c104e400340e034030200300904490302807c0c061401c0c0004501200a0721604c540588480d545001703206200d01c04c5412841605146003610005500105400c50800321569620758030400500042c1169102c1340c2c8040b80b1684503040c0c56601541da00e402c10390b90300c400c49050725610f06841c108401e042c9c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 950398462 1250 950397212 950397221
    0xc0106030c1707140910090504032c210115091b110c062a0606031011030a0c1709060a1821030e01181502030112060905030405060f030a 60
    0x41680c041c0880f42c0c10000000f062840010388030340b0404092021411a102c0d205407803000e440511414440e82c5011706010300f54400c0c2388d5501c2d916035070b203d800317a0707076082c81a01e4040007190051100052a1425003c1124010b11219203072081d542c50303030800754400c40510b1160052031104004641a84410b00b940e0100d01084900b400b40b2800c074620400022000c20490491401216501d4a4180340707540707000455100480001c007440401041240d103100040c01511601c01101268020701901d03000c10103940103050f80c400000c4041c00031078030f21030382a0050015511540b4211515007881c10312840030316820b0707450000d01c1d0012070a20031084880c1c086c2a00c640351042403803500510b030390340d00e0507076504c16002080400404140348010910a80260000c42c440c0402030102070003419071300c10302c4941a10101c441b10484280d0703900220f1b041c001d480c12504c07000305801e4800c2068032040c024100c2a031003201c01d0300040001048642d507000c06070209100416900781c13649051035040c0b00301c0c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 950399712 1250 950398462 950398499
    0x51c1505130b04080d0612120509010c0b150603042004141f0b0c0106090510030b070f0504030b07050304050c0109210609062a030c081b0c0106030c 65
    0x5040c5410421aa124211080c40480d4401d03003000d8a035890b424a05100c0c000c0000f413000e030358208a03000030750300016030a0001207401140b10054000842900741c416210b4011224007084852004001154080c82c0c010761090b0800c91070b070020080d840c00a03a03144c0c01120100c0300d5002c004580600d84c0d410008059000c030040c1c4081044030401c20050442d00c8000f010040c02003142c244101a0b420748003068801407000c5d044050b01c1ea040200760714042c2120380201c00c4078524107070010b030b0f010898540344400c891700292000070301d03224014112113070103420031131034140041000000000b403030101c2070a10070081c55a609481c0c0c00c051610364181440d142c04c0341e0402c40d4501051242c0c10340c5509256004800544000d5102039a11f0484c0141c16000d801a241c01d1070052a012030b54880440e94003003410000000c9006101c1c0c003020341c11900041184000a40d100c1c0c00142c5015011346c426804542071007c59060400114040382511203a80003151840c00d0f070b1004111515034030a480303118 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 950400962 1250 950399712 950399753
    0x907120f1107081201080604021f1115220b010909080f0a020604030816210905120d14150f040b040e0c03010c02070b0d0c03090c03030e0f090c03041209051c 69
    0x6081580004040d084a20001036007005a880ae4400450203801040c00304015242510492051001c4800100d030080310030240b0400e02d0302081c500e51500e00c03c0d640e04268000d07800540759080c1624a0010300800340100c03440102041841517500c1c55102034000140954020451446c0c1403600801d00100581100f1004654000002f0300c59040901c0003404031f08084044150300c602104440540100c49002d003240c007640a540340e00c0c608910061000207182201480440344c0d106042101100c200d50096104039182c40c24034561418050a13a07078000c004001003400c0c07a40d14009800c540000c02e111040742e10120120580f270800b8022101c81c6112800a000c000e45000c540c00c01d03502c11a20b408d42450381c0e0b140c00c60201c41c004d900c5038884540140100d040240c880c54060301008034400c0301d0b07118030202a603440300c074902030300000d20401072226003600b59202c81e540e4800310310000314101c05028034040c0104903510394807140e05625030310910312081e40449052054184c901c00941800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 950402212 1250 950400962 950400973
    0x5060c070911090d0204050c0412060501080c0a1203030f1b030f1a0102070506030415020f040618031721070216090c090b0703110313140907120f110708120108 70
    0x341540c40503204c0341015010359000c43d1581c1c801d080c01c0107921490300074000781c0d03415100e06028480b40e51301580c1642c41101c100c68444801c441049400400c51060f00e100c040e038510407900080c07080d000050b00c081c980d20080f4a0008044a020070741003041078807000030784d50301c8a001122180d0700134500e09170040001500c20084802c0002d458110500500d40038500000c00f0130300700040d00b07000600300307050304804540310004d000c00701750070b6801442200001b4555060003280800c000c1002c50441b5449402d94140c0d8001c044181c180303400071a078207004c130000e682c506103120b41102500f503c10f0615502400409028240380041990160003c0e901e9900d0501c604050503000300610040d42c81c06010030f0307201e200501d411661131681110f01c40d454080486c2c9010806030031281c8400f030721031150502c102c9050302d0050015000c4110b521000041ca240c4014602101d29409950000008080400d41c0410003c800000d0f0b44100011903031000700180701c640062020350280c0c094a4003401626 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 950403462 1250 950402212 950402227
    0x307090c1215060e01051201060804150e0c01120e060720030301080703060e0a060e031b0105160e01030204050406030f02100203040e04030f0c050a030801080f070501210605060c070911 81
    0xb8004681c074003520040c440c45401d0000c40f41e010f07a0a40341260110518195690f071134a2000b051040140c1c0c0c00c503900341200b090901c100c00c40d4091080014220002024100c00510044500c030954920305490745540e9802860031490610140d8424941c0b501c80842205103660714141c1003120780040c1605070002c0c801440303400c9002c07074400e00f1260460800300d00706c00301512403420003041c0b0400038402454500480c44100c00400034040d1710301c2e1410000034120b14a00c2860a95608407075401c5113034001c00c1030840841c05402d9a12030b40310f0600d801814a9100c0340818215000c0ea00b050b45c0203158040924214a8601c59070060004644091400e05107030183c03101d01840c020704000c0c1840106100b004009128004004040750440b00301c0d0180b034914140500195030070b0150300207034014912640e82c000800110b41d012204181c0d91803000d42c01e0701144006105400701180c0716561501e00008103540c5110250042c44d000c14060501c1c507141c005510101d40d118045c3c0c1c0c00c207801c14003421 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 950404712 1250 950403462 950403491
    0xc04020f090409030314040b0901110a0f0807091a1b01150306090f17030a0507020d17041a160207061418031203070302040608060616200307090c12 65
    0xe40001c0c50503030307010942800d030b45401e801600e503800b030304c4c0f6400b00c64200700801c0c88001328005003e5860b00000f0401080c0c80f40d5a058144510950717000440c00188084e83c0091042181d19446081e0745000c484440c3c9072040c007101e58900c446076200b940808561312041407410110040200b00ea90000c000e29105c40b42c44405000380d0307100c0a4800355440c201042407000c2c0441e185030481d8007607a081c6a0212008003807400d90016a54000010701c0c04000a420b28000a0104659101c0381c0301d03610801c60201c400304c07080350010012a0000001d81c0c1c5143e00c0510350305100c2c02240000715140440621501c000d203040d9480d0720410030889001c40ac2e100c14250602260080505c0f9001d92654000c400d000c41d1038142481102c6600c00000400c00030503580c181d003d0020f5a045d503481c102282c94045c00c10006005411001010f10f5401d841480081c0c41040c0200010901891304400490039500081c2007103015440710b60301e562501107961606034402d02041d60b5041c0400100034400303600741758 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 950405962 1250 950404712 950404717
    0x100c23040e010b18090403030c030b041505040e01141315111905190e031e0c120f030d0c12020705070b13050d060221040b0f0402060d0c030e0c04020f 66
    0x10f91040700c40001d04c0d0500d84400110b61101003001400100840c1071074038000b8000d104556462000a241c0b030604985480c040c028100c004075400f61240240d41000c0400000307085c0b0f44100d03102ca41d6994045088000400000b910034118407034080d03660442402c0c401c0308081c1c012807130b1003001d26025a1210302040309042e600c07900c0d008803140140c1116294281e5482c89803100c1c0c140c1514400c06c01d00d00c80c03a404894141c1c908829003d445204101507404030a00060910780910303500000b0040a203410031042c8c3c035840d15074200455074010700c01482d050440e0b016034440c040305501c4e403141c0c0340101e810003240b134000f802c024411454044180c0b1503a0710340f9024042c5003e504000202c041800d40d40180c24800b418000303044030396000d5946403500c000d5111030030300c09031070180c421200151010703004501c1c440d940101030a441070780c400e07052216080000740126030242090154070754803403080c1314801441445450000b41c150f85504003034900200b000c003c500c01c50040100e4090010351009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 950407212 1250 950405962 950405969
    0x70615030b37140a06050112020c0a0209061f1e0c050a0215040f06050c011803080f070212070b24150c070503030c071505030c030408070302100c23040e01 68
    0x8803440201000d0780b0340c1001d019400d540c9041903001c01d00344200502550700c208200c3e00c00342c0350b8520218040344200184e0180340140078054100e404a80d0243c2495151190b1000c4001d0650101c000b8215150081c102d00011850004112031803d100404500b010078042c000c050404c10720030850303981d5466407649010030080c014415080307140c19070304000f0203170342c00303020b003084d104040c00e4036008010126084070780c200900d90b08160524110340d198155007000c0035015a200403450707440c150541e4078000050130041c00c509c84d9030300428902e68160040c2100500c1120720404c40d0428640c0c242ca600c15140081040e0745e40b4440360308840d65544a401d001c00b0440580507161010825028107012a135800581c15010000fa0166421801701d9102e003a6150202100b503203180740c0200301e0303190104848020b03d1210810205000ca0300030400b8002d00d42c4248102e41c1fa203070070a500b04040c1ca44100c00e00c0042000005d020301c40d00800102512002184d41c4c0c03550400d46012004000c0d18810310 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 950408462 1250 950407212 950407291
    0xe040908161a0117100506010503061923042307030b0102011d0a1401020f07031b140f0f03030c070b060604030f032f0607080606070615030b 62
    0x11007610411a0700303011100740d28410608141c50b9039461402840c120000d1115500da8001d880c3ea280320720b8054800c032400b4803010380d82c850655503400140000009082840c40c01c20a0780b0381d00040d0819208030119080b00c5135514100360b040d012062106a5405c40c0c0c1c903d03a0110101c8a00d4a003a820b01c0c2d40395800341040ca00424081518070040c0d00500060070328001c1d03d500c40519049014000482249e5a4800c040320000c3c4003c00801030308078080e105800c004404100000d801181c495040c1c001c2a61a80b542d280e10314201c2d41d03504011092904120a4581041c003190901c200103000460b101c2da8840c002c0e41ca0340c9040c1103c06042e200e4014010641c00100000c103003540c45900603140030f9035114662050115940c10080e100c0081074180380d031200d000b80c15148508414a0042c0403c480030001840a40c0740c019085d107010310020100d5402030024461070004c41c0703c50254540c0c2146105d030346200d01c2e0444c1004400d040c0003d1406455114452007003444401250310403900c070b95585c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 950409712 1250 950408462 950408497
    0x6080106090e010c1d0d0f120206100e0601050f12040f0c0b040e010e0c1e030123030d1d060714010506010905310c200d0207051e0603160e040908 64
    0xa4000481d00360b4016800307421a07c484016038100a03005a4050402d000c0e1b40840310240d80750814640c0c0756265004500b1440003070008140c0c5940a00301a0071003580100905050944800110700c10600c101c1b01030b40c070109031080200078451442040b0003c4c00c0003150f40c0e49020b05140304101980d0042c884c4840a00c0c900000074040d541000a407410783c4441c05050118040d200c1030900c0740c2e0802c1c019149030000004500401001c10340700d0116600f80a0041e000c01203900d8802e44880d41c84134840b2612032400c0410044036500d2030010114607202d4400d40391440f09001819084640040815041c0028590207000c565a03000026954001f1040001194595002040541c0c000310421035039040c07d121041074660f0b00200300110390756202c010311000c0a40c05840e242e075420032446410258008540600c0350f401c0c4420660340068102c068900488035020206155500403101e4032a4140c00ca000440d010340c0c065003030880c7e08400c442c24800c101c501d4841c50064416856499941c8400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 950410962 1250 950409712 950409767
    0x70b1308070f032001080a0b04060e0a0f050f070507170702130f0f09080a0e061306030501170d0912020d05100501080124060c02011206080106090e010c 67
    0x415108000340c90000e094900503640c4841068241c403480c00b0864040610201138607440e010240c51320040d42d016942c600840e152100080c009118418004d030300a910b51401181201383e0500301401801c0c03040c00010700c5403020400008480c0040c1010300717040940c130103002400b50b1101c1601c19941e0454811108498658190349451107800c0c402904841c01808840039070400c0d501c000c020403407440b41441030914000c00b140c02c03129003d0000b07000980c00d000e00f417440d5100d00c0020fa4078160140500e0b01e4101e00e00300c400740f140c3c1c80e40c2c041d100194458006202846a01e59001c41003c0104000c0000c06080103025145145600646410480c90241442950780b009000405260410309403550b81c4030901890020384024080c20364130303600301070064091020071070240f0303110b08030f020942c0c404a091000445581d141900140d0401a401d8940300c1a940710303200d001c00400c01c05000065003403031300182c5401c0d41d11490012100707034502000d0410b10b5400c540f4900f4200612000c003500c100a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 950412212 1250 950410962 950410987
    0x506070b093f091806180414070f0f0b03130f1103190816080715090b0601140d0b04020d29030a02030a030807020c09130b070e03070b 59
    0x900c0c80a0501008400c0307004211006480c07406500c01550b00100041c074000c520b90700416110307100d05240c01098000c80c1d07078044207100d014150001e00c0240101606100095084aa55001e580a45d0180d5080500d041c1c8100c003008204024481c1d0f108103004c4902d030036100e24200001c0e1150755446080000020003400b0042c109803821648000c80055020701c6040c4002211403903642e5a02074130428a5003814104025221a0b03501d0380701412900d4192040c401124410a00070102c2d08001c0a011020029805403040d20245131189000103484440b401c0c0380c2045000901101e052000f02c03941e00c2410030881c8120764043d4107401002c0340c400040f10210300203100d10281c0960151815001080d040e25904540b920315800c4000d960703030500001704258803000100c10080d4141d02208841e400a40550000ca5102c506801a81c031005010300c00700d80d0440086a4003506d086001a0b404100001d000d000f80c0c00c4049482d040b03a504070400c0100c0da8801c102c0c0034107404ca040101e29060a000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 950413462 1250 950412212 950412223
    0xa11070605130c06020303040b010f1a0f131517070c0f0203150106120b03190b07051306030608060901090308011206060803120603190c03110f03011b0207060206010506070b09 77
    0x40e440000e0484480d07890034006e441c1d4000f80d0f012580e6170001000041e01c4042c00500c0000c1e5840c0c40e2050703688032070040e01200d290748000088441003c0900c8805111560001454002c2c48148030030007c219400e40000c0070026030b503074000348040d50701040c050300039409620000040e9000c0000c1c0030209a50000900c0d082c00428050444002100046059640304251820070b001c0c107603060103113203051000c150322880d03407440d51440841c8410f94503001c101d4503454603400c030250b41070071803620144074440720125a95802060200351140810060400d00700241513000945000800c2401074550b002840c1d044107110705000181406004400d100c40341d40f25100801503041103a42d90082c5111118032000115000c0744280a803c0154007682c521585a02e2015071028003128180d003507649540c0e01c05c0120101c5900701e1840c1c0d407560260b0310240b098071040c440b003154200e050050000300070300e8110703150001800c540040c0300421003611008155202e8039448a100035043c0c0c5e822109a2411 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 950414712 1250 950413462 950413501
    0x501020d11040f0b1908070c14160b0913050601020c1c020312190507060f18110a08030f0702121c022b030f20030604050a11070605 58
    0x680c0303881407424400c1441d000510032141094030740110682e450480140714040c0d002e14a01c2001c0c1c200034801e03240e203d00300c0c5503400529800d00d4684c5211648030721103449c00c11310050101354010359250851101008420004000000c2c07a1440c1c001304802040d001c5606504008000d5103030030100c2c0f840e82c000d11187c1492540078000a0f81481061070505d000002ca4005070301030300620700c4094038180e94600701ca40907000c10ba659500c070b0000304011100c942c00404165507960b501c00740020509140d014000b00c01c01240319290217458a410020307070301c90070500751900c03425250504001d503d0003c02580e4117002ea07200700c0e070349410060020414017500480c1d01c00f814000d400780d4007542005500903109034002c40e0308503044c42504c0002c140f120540029000d000d002201c0844407550310903000f4501034110500045070580c00140008440040c164068050240100400110f420f040c41099070140064001b885440464a00e45401d0b100c0c0700c6000d0842920340b80000c0810140104403081c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 950415962 1250 950414712 950414737
    0x5220c0306050d08030609090102130303180320150c34030c080115050916021c0507060b0904020f091005060304060504020f12030a0c1403160308072a050102 69
    0x3494603003116285c2c000c880f580d21522918000c14582c850500c255103a0f5285034500c500b40c1c605603102510280d03d1600c01c2c0400d4500d5803004000207102c0c507009203806008c94000e2091140ca01c041102c1002003c0000c201c0710000c2c454031a0440000607854200e80c010342188030f00b0301c000180451160390300000c0c1021161580c9002080001c1c403021031045034000c00003040b2190004c0214901c41c0e211344100c56001a07040d003c180c1d082042032580d008000e050045800185100745038490690032500c5150120b1000b194440a00c401400307035202d9205e003140c40843e140f60560000f10b2040e02031818a0003207aa1a0008440c41401e8002e00040c0c640200034507102d1400d031901e80064078003120204d0207400031074500b80140c01e2035070981140c414000083c50030b10701e14031411140305070490401d40d0b044080701242015480140020440031040241080d18044541409807803041c0c0540031500b00103201e44410b07042c500303a5008a005c0802e08009064203011400c081c1d02a0040c5080c0215 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 950417212 1250 950415962 950415979
    0xc03040b0306090a050105090c030901150f0f0f1508090a0606030c240903032105010b04050103061a0304020f04110d060312020c010503060d050106080303100e0105220c030605 77
    0x808000302000345224003000c0710032800a50b9001c0401c801e40c1d50130720620340c0050340d180100c0c1c1c0b0300112101a40d40601c2e868000034800e190380c200041c059203e5800f50b40c0304070b507209080c404124080c0e004806083c21030f05403c038061410f0050800d00d0700d80d403c00703801c0008a0b1b01150301000d080c4402d00d42e540d0001d40910249803030342440c0120600030701c0b685a00c9201501c40e894444160400181c03803e81da03407550b8407034524540b010348240b049540e03800c060b40040f20302c2076100c0d01d00e4030916000c0c091a0b8035040d101e41c1803000140840f401608180038603009501c6080c8401403507811a07520036810f684009025000902040181807d5080c0ca1900d0601042d05605038045900000459010b140c400e050341c6805c4c0c10a17a02c0d03030703110080c8074001001000010711030f00300840c21541141c8a0800000c0742075030743d040b060558106030307141c0703243c51440003007007105003002e028007405040100d031103400083c21183c40810342054001e9103050380d80c035460164001e0340690b000200511000c1e01418 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 950418462 1250 950417212 950417219
    0x109030b10090f0e0a03080c30090c030d0f02031902030d0b091017031201060206040c0815010e0403030605040f020903210f300106030e061009110c0304 67
    0x54030141680904200b0a241a60a1014801034021429104180c40103031007030314000d84046800140050071541a20301c1007204501c0e00443c090204020402680400341c87c2146164601d481403020b81042016032200380d2800055401141b4820114891f00f040c901c990b1075040183c3c1140602c0e1585200d240c1c100041e007020030b4020000f0089680b0003101003201034180c1c802c000042d8026114540010707910802445070388603185288001596260481e030600061292403231400c0026000a0010b030803410501c000c006019a104000e0542240500303058407410018050b0318005103d4803100c84480d1000c60145030003a80040e001c3c00c000303842800410004050b01000c0c0d80403400d21070080c0705285121110261440081c011071865052003468030f40025846000ea41140c070701103448041c4c800d8580c140034200011405160154034105c0c00640c03400301c0180444504010340305480d0002030400c000c0700800140f035000e0f2a00d029001502070b01c03180d00350040e0702030190001c445200c0001c001c07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 950419712 1250 950418462 950418481
    0xf1401050d0f050726040506011a1e040501090801050705090906010c14240f0105060f0c07030303050118090210050a03111215030d023012063c0109030b 67
    0x111070101c01d05c920b241840904941075252250455000d00f60750881c40041c01a0f44000c2d44c5001028141000141070000303441030108680449419100d55010020702000300d540c000207400c00800518008006600d01140e010301544500d0420501c0b4502060004002c1e0f8010780d44000200d4108015520303661444903000d6a5104e0708052661120300d2450000f40c1303a80b1042d45602c01d40104107001c00c240d10745400e10a598201c40b03100e05003150103012603500c0140030084240294080d91b0b02144651504249940c00c0034040907400185041080c0c440241c0c450904070180d00b191454043e55810500c9011030052100c081c04900f0031070002045480313641003047d802d0085100c00c0c0c40382c01e10307030043c0700701640d40580b140f0002c05078005103901035494030900e2007522500070342c4e0616000407406000c00003081d03100344804c84043e0b1900302400b985042c5101641e03200064100c2e0012046c039903510100340ba090a80081c1241080003000c80100d03449001003400079540722002e42c03403c2c24140f840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 950420962 1250 950419712 950419727
    0x20d0e011b0c0603110901091203110607020127020d0201111906140112030206010911120c190201060506090f0f0607050609010b01020c210a0c06020109020a0f1401050d0f0507 77
    0x12000085d0402c0132110fa4409a0012608103c505848240c140380c82e2149038422400c1c1e40c502503003882442880e00e4503000c010700c5001c2c0716000c2c42e0300000741d076007014501900104030440110b01c074054400d00d07072340107860f01850300540f9030f02401c040703050344210100145001e41501c00900c4174030116216408110058000100441d1007402d0326030280e0301e594501c02c020b1120307040900160b028000400580d00c69520284c00c2048087c3c0d480e281c12100d040e00000504145c6422500d140002241c9518140080303084214004500c020b000080c40c082c001035003030203401d2500b440b43c050280409134950310342c80e41200d4010090304154480318a424a5500e5440071140301005500382090f04403190b20101e82c10000b01d42c0200001405500b0321000c180000061703407003003410b2003110509000f1601d4a00796000030b00b0140c2c0081800c00c2c0c10700c14804c80c594160f2009549034040c00f0305009034401404150402e080a00e0040d4540c2c034002c0d00e5002400202600300240c2d032928041c0710806600081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 950422212 1250 950420962 950420969
    0x10e010b0a181e1802030c04170a02090c0703021c05041404020d05100315021207260405030c10150909020a0e190506010e0306041b0306150602060105060a020d0e011b0c 74
    0x203829010420080e05413044c0d110407210064155000c01043c4852560200c9140d03c88038410700702d400020095001c507845040680b10940b8801c0e001c03840078205541000b906045d034400e04c034078031031140400a001e4018010f60061003040403c899081886440740c2d4103a400b41c0c100c4038414031071070a002c985040c180300140400d44c0c040421034840d90840c45603008450103c9680800544e16988540003200c82401e04000c2c1254040102e003208207240f8150ba00c0d0f4001c82c0100c3c06156561944095a80740c0081c41041d066002e090064443c1400c02142150044660409000c518030140c1e10000790021201e030070000700a007040e020700c0405400c0184101245403031a00c1040345889403c01550a0715944079034030f13810380c00b450028001498141020800ca03003548880680c087c0c5a58859068860b039564910b09800f000da42005100c0d03040140c10700502041d034289248c0300310104000d4035031042e030121405102d10303d188000280d1244070302606001c3d40e01e0410020414518012002041e00d10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 950423462 1250 950422212 950422229
    0x21305030f0d050403060b060c0105310f022b0309050102070e28060b0f1801140f0f040911030a0f510e010e010b0a181e 53
    0x10003804950020b00c82c404007045444450a00e85584d6411025021070515550402400c0c01800000002402002c0c060035062031080384501c4602400034450ba0100040124010040035001c0812910b9800c505101e8040d00c0744c00b030904d07031452116180e150000d039000b042c11080078035006040c0d000d1745040c190f590903402d9030b2040ba034854040100400c00c3d40d600a2608415204100103070060b49400d00c40c140000c004112542e071013a86c80c0f04d51304180c0703044284c030030001000c2414140300c040f0b48030011400d003004240c400015a500c02035020700e01d40c03204145000500035603070140030070039940286075032001840204140f03611011160070a0341e61420761820b2000081c454541401100899900c0c101c202c034102075441d5aa0110a490740300da4040d4007508171040110001803420f240c55103101d030385c0503c031061901400c0007841105078071002000d11100010b00150666a040303851441881c540003106100100400840ea0019409074104000c9040300b40020400111500c00300c49210 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 950424712 1250 950423462 950423473
    0x503180102040b0f1b0d030b0f03030a0f050a03090510060915051f0306051302030708010b0c06060108090c0d030e100504050f010c0f0c0e040b15010804020f031002130503 75
    0x19a0180c240d005078000c0c811509001d1105691010131034014000c3d08a41d00c0481c04d903d504407030800d080a05003410070300000d4407048443c107541081000d071003005106500039860701d1007421000309103018a0311020204030000071505042440f9411003c030701c58028040d103525503207800010004100d5441f8100702c3c40d0820a000c0a280780b41901003084039005041d01c41c000030808640d10780d0f60050101c1c2c27000c0c590b5400c0c011642c0d132201c0f1201c41e42706018040c016501e00380404041e02d6810142d00454401a0810403242680c2d408511140c21210a081500e619120102454200a41c4115054008041000c07542c1815803001d81054001d006079548901c0c1e2079140310850349446640142900201c051840030015442008210507050003030031075800b001071039030350420b01d10813592025046000c10307000d2006210007008044c1c0c2219000d6a04102e02401c0070019140d59001440030740308072050588025691000e012000000c50341b03000465a855548200890010b4180615070103449070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 950425962 1250 950424712 950424751
    0x303070216060c0213020a090e04050c151806070c051305040308130804140d050a030e01020106060c0b04141e011d210315131a0603130627030503 64
    0x100e10803e00140c015196410b103c0460840802a5012244400c204011440c00048450407428243d0159108002601000c5c020108100302c28040106180030b02201b080003015940c070003404441440401e40325030f600c62615084c8034600208585c803003074010b4424047c06044c040c150f800340b440307913100e43c90f010090b1310b85585080341c2401030400142665000c00083c0007522549040b4024010002c025100701522581c2c0d40d410f10802d02011004122405102441d660b0203000c3c601c041e0031685440f104180e50f50301c80c2240244080c0014180206c0307001380c0050700e2803d014a0740ca01e00b00709c1040741c0200d4106501802880c02910343e0b00b580c510f24114444034680425a071a00400001c09a01182c2e00c1c000c50f4566584042c08551201c032400c141a605030b114806a80203000c00c090340000c801c59002c90302211604a0210184211010820040a0092a0440100c168220f6000111070302e881c080e806544007a070500744c42240d20070070141c4c10190300000443c841e0031000b90815206a5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 950427212 1250 950425962 950425967
    0x2090a0f060525141b09040c060c15060b0c060f04030e1509090c03090d02010606021932100b010c080f130801200336030307021606 58
    0x8250180400180c810407a1100b030440c103080000b200e5488041e0140d6611240d9a203aa5401d415031030346040f030304072903603800d040c02d003503083e451841806452602e102d242a555423885881d2900461040c060000203500038403041000c2e8481e000c2035404200315482d2103100c4c07803034103420504a00160744070b000c00040101d05c0d0055143e00030360340740d100d80601c4c030203802c100300c00c150041003506200317442403010001d40d41c0e40d0349003d4050584159902c0d628245a2001410110030a03a0350044da810301404218255000600d91415581c401024400520f580744c0034540c0300c502c0710f000310b01442ca06562461507a24040c04015400081d00300c0e402c80503054403100590315143c80d890301082410103000040394000c0700501c8582c041601b000d1404000c00d01813030340c04400b0b401c21141d5a64804d20b0986415004210036041c00d49041138604500e002101484164801a11079880030031031001c1c0c40c4507010041840b84104800c60907a522880c240030001e42d100c0041075216026480d4020000c1c0850 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 950428462 1250 950427212 950427239
    0x31615062705090a080a110628021e070215030703060504060e0403020d03051005030109050102030a0b0d1106181c15142a0c06060f100f20010e210c1b040b090a02090a 73
    0x90008106a480349000380720410700e412031141070341c019194103030ec00b0520f10400b00440c400c0b00107850008042d401d04c0103001c00c850503038010f404036040f0760045c0800f0a0700003036103440183c49071601246c1c0f55104140064980b160342d0216402d5802c161035202000419000395114020b121410005c48458000300502103150580152002c5c1c0303030207a040080e0801d0300c028035a004118181220040c80e15008ca016001113551650b013003400000f02c1382c2044020f0000081c102d229481c284004001141d4030600a20060400d800120041c20305040c0035201303500f002680b0082030f6007030340c568285e008213648904045401502c103400d0080d580c0c0091130710201401060600341d0701c506c090014102d00307565251241781d022000060440314070005060034001c00c2e1001180d100500b0f0500204001c00018a611095000c1170110610044141035000100124020004100200300447c000c0118008241c20b2030f820f45c22055000801031016840e400410081109a4248450030ba690786441c4070b01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 950429712 1250 950428462 950428477
    0x60507141204090c020a0b0c070317090c0d0f06150609150c060b0a08010606050a030e0114061302070503030f01030201110708031615062705090a080a11062802 70
    0x8100c00c2c0700c00d2003260748607446019400624011102e848030152180c0320341d09400c440d00120680c001590400b015441400207020340080c180c2d48c042da007000481d00e501c1f290083e0304640549008020b0b241400180350718100410b80043c0308011001580d904040c0742071b014003034103000c42c40c18440081c42c60842484582001304c10740e140740649040b942e0700806041080c404c194030000c00c800100b070b805d00070b10030180208460748400d0340e500365a110240980b140d140b001103040c0d2510280c1c1012800d01040d2a6000c00216a1110a4482609420028007928601230441e00c000f00400c8004907400d0700c0703075050303038002d0f02c5207008180504491035035041e041c062504641c0081c0103800e604020000788500b094030481a0111041b51030003110222030941d40289100c0c2103150701d07911000d03000800c501c1e801c1d00024050045207000040642c0d111005040103094000000703041400030b11441c000c10107d048030007914401d0401845418500000c20904003441040300115500e15510780b00300c2d25003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 950430962 1250 950429712 950429743
    0x60648070806010b031f0803040f06030b1011030d020a0801051f0905010f0201090506130624062f0d0f090e0606070309030503030a0e010c110316020f030706050714 72
    0x2da031300782074503480b003504064601e02c0d2180300011881010100b128041c0050b1020354010741e10380349400742c2c0d090b61540540c06103084c1072130b10001e664503031103030410650b5024090414142002013080224911320458681c3d424441c40030545032841a40801c03454100c03241160752041d0f00b444031001c0b580d01c080b006c16200c0444c020031303030070003165007c0d4518428810721800001a51156900c5680c203040c02101c0900c41c00c06c9190145041286ca80305480c842ca0020303020b0041b281680204090100482c0104024002241560070745d600044028112010788002504105c0c944100d00554800290300c1550100b00d4540044801c1486010700d101190a00e403901960758a4040071300c0403c0d8407030344095007000030040707020010800410003507004008004000680042c240038107801c603140c54840c0402c00c554521500401e440c0041601e000700907000006e0302148450ac0021000928010b450790580110000010082d41081c060112640100f8030b035401043c4400b4000e45030603101070100c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 950432212 1250 950430962 950430973
    0x303031103091b01110a30020d03050c070c060509030c010f0f080c0c1501080f030304200d02210601050405040201200c0307030c140a0e0606480708 65
    0x8034100e00020f95901d9500604000309034144074981e050400e4014101a60041e05d0442520012064409042c80d403e280a51b5900d80e5040580b000351140300000042c2d08040e2504c0103d2603600411003155902c0d9406501102c034035550707031009070098010850441c841e014450100042d54000ca041c00d002c60400e90790b4039a2900c1002c016204850060304502d5010b00912032038010031010403408030040c443c10041084ca61400402ca89420317004040301d4810b400c140180300001d1817800780d5040509201da0305446520100700451624040240044e41c00944400000c00282c42d01ca00c900e0504261010b880d05070380c0340d400f44410356405a03070090000e0070304031640082c00e0b0100b1464811304140070035201c07150b5582000070310f40809030304151481c1c08410010419007040702d0584a074800c0c1030f582140320500c0d160100405501c001d02060140c0340004204194582c440b2070080d1007408035084100990040780031031b03240f441038811621404c240d40040015038800282d40001c40386240e00524 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 950433462 1250 950432212 950432233
    0x1109090309041e02070302061602070305060f09030d11091206060d02040b010507050105150909010c0807180503060c130b0304320607020d122a090b13030303110309 72
    0xc003c20102644500140400c059000100b24070300044c05558040d034001c1c80142400500f008150b060101024150b5019100c200300042d000710f070880c1e006065503518400c80d03503000050390035841108040000c4619201b604040c080c2c00d00082e06400d142612054180d280c140d001070f03a50207090310380c1540405003c59980c0103181c203030048031040006141144c2000038941d00c413800d4860603502c0017826a807032042603529041c20b403030b943d0b40915008002d004003401c010010703102e0305014200030708102c061010040c6030b11003503136914014900a42110680e00c3c01d140d4444154006c95006188aa11844002241101c0f507050b0780c01150270445c5c08a40c42ca801342a1103901d0140d20400038087d06456103044d91030014859a0300c103607240d030064190510030903c0100030000301100351058520700005401742020444010100300030f0120800c0b190321500d581034400000a50040108110000d80c2500c0030100c1c0702c4000c01c40348039440178804040184400d400c603020444058502e580b240c00404e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 950434712 1250 950433462 950433469
    0x6050408041a030f060a0326270f040209280b0a03050609060301150308180d0309030c060806130c0e060f130e01060807200102070f1109090309 63
    0x45410500c034896481c9450358072803020855a6496150740205000441080100d0400c00c00c0d40d43d20103800c0318101c8019080d6910080d52401c28550a01c54880641241c1482a6103c0444214000202d100460b0400020f103900d41c44175a021482c0c010181e035110a800c900f0980251401a01c00a25401e4036000b20100c060003c3c9071202d208103000401c4000042c0e9011441c002c016401c5203035804181c0d407500209100c8068000f40520f40680c0c908004004610150b014600541c0c0d840201181e80e010124415104031641c5003111b5400403401c0c000c2020590414908001c60303104844141c0103c2e075420f01a0384a001c00c45501750041c4172040340f00d500e415194891a00c40900f401d05842060440c0003042943d013040d0805c50f0066000208030745007201e4416180010214000020820340c1020070040c00d038a0b001d400030b0148031350500032808481100e0044bc0441d40000000c540b200c965003003810761210b02803020345e218160108942c1726420000071461203440400c0045d0b180040a0052 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 950435962 1250 950434712 950434721
    0x110f0606060313020d0f110f100f020304030b0f0403091406031b070c0f080118110906150c030a0806010e0102070611010b060408010504020102190c050d15020a120f0908030406 77
    0x40f079102810b41c480000580d1a00c182516503405444a05901d010510b0444081010502a1440340c0903160403251036548181116420440c240381c00d0a684104200982c6075004540004010441c24030800044580342c4000074071542c0030360395003140c07039a483c1a0801e24a98407407800e608035004000092201030400341503044c22148200b8189002c00340e495696166125410502c84141505d4040280303240902030300101c01520f5259002c404069603d170260110200f07902405072407468000b40c429980c403020b82c4c002880f020340043da1580c6e60030075280c40f44c0c070402618005c9105000490420b500c15840200300c040107800401c3e9079401e00e1400d1b10000c00011681030740d507413100040002034884030040c00060003108004219400c19100290621666184494050800740c50502c0030810200410b801c032081903c1381500f8000714102103c0542121701d1030ba0000b4000110034001c19402001c0d481e01404517038041044140c405441800e40c2e4504102031300c001c0b811b00c0450701040c421b912 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 950437212 1250 950435962 950435971
    0x8040f0f0309230301240e0a061a090a090c020d080c04080d20010207030518060d0e0a030e031c12060f0803031f050d030c23010b01110f06060603 64
    0x4220703015695590700c3d428090680e8420300c20402a141c4560b405040900940030145071940304014014429a02d9080ea02114803404070f60403041e0010501300c5d69541d100501501000007592900010082000c0c055482070080c28002c0c81c80c8500051032001c1d0744500742070403013158050507482c002c01008903084e807006001201c101d80100400200607108111140c0d481d603d07a00d502e03c00640140c0d0b4020007121804030030306143d0041010781c001940c42001c641c400b0301c20500010780c965090011809500500010a0310030780713048078600344424005500c100c00d51003555105c15400d100c805158881c004400c40f40b03102401c14000c581254003036804031070004c01e40c0700005801b40e0b848034000c03406101a44504c0702900000b05000c0448c40782014984030700043c00580031000e15100218440c8044900054100898104000c042054100c6840ca031800d0f000d00755111801c0d00541e4a00800d1013044060114100407220f41440c1000b1074004030004036440503140f05d5a0340414000f50b94002070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 950438462 1250 950437212 950437217
    0xc0e060319020907020c0a080c1807090b0a1b0c0e060f031e01090804091433010203070605010e07120b090406180605070504141914063708040f0f03 65
    0x2c2c1b59580e500c55600303241c01000803400805500c0301c514180a02144404000200084a081003080d00c6400400e1034003181d11010f020340d6695009081100c0c40c01c1c00f41e4000c80c0501903000a4014450304a2807501a01c4140c003522800d40c89160401021050008459416401c05013001074108521484129003092190012540403100c1d074032080c880d07200340c0004d0b51681e0b6170240340410040c4134880c580d21840840c030701c1001001700000a0107014460401021804810280400c20b074030038010b0350001548201c0c00e0140d9615425120008142143c4a0700040c1c9559161a14800b05000e148106040508415a55195034035618041d140c0591481c00180d240707005000052078500c1074511459040c3d0320207803190300300300f4008010b184203450a480b40c54600d80840b2000c0318003034014112036045040d062220354010118801d4010010501c03e0001d00791000b051055170410211142c0c40c01c03c070aa206042024000c0d584488140e502801c0484490710384000184204c10746001e141c02030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 950439712 1250 950438462 950438473
    0x18090a1e0e06070206100302131404030221280c12020604120c020117180a03170a050412120f02030a14010609150503040602090a030c0e06031902090702 67
    0x10865914815110303210050201e985100d1181d07829001d100c00e58002c0c2041c4041d00660809018200744c2404030f0002a210710441a00601d2048003540080708840e10540d0005d42880c05040c040d40300e0700110100350084000d207010032031a0044a08544601d400c20200703103440020340045d02107c4031900d0b6001d091040388034601c0040386c0400b02815640c0000d50040003140340c2403421040440b51095980b0a2101d01c4c01e103400140e800c03400000d211480c00039000055035070014400300c0e80c0c0c4c200b002e403405801410882818558070802c80d00c2404079400300c240342910780d84400000c49a0845028044c0b070300c4201c481074070f07034400d00640d8a07114403684042100b181c1d822000c012603005a514401b696030b14640c80100c8180c03516964010005400c20030005031600595143d82001040e404080120000001b42007260940c181c62000401030841c06000d234403840d01e02070400301d40c0a1003046030140b00c0040c0d168540082e110894602116145a4080441e8280100d086d4090600380c00e60140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 950440962 1250 950439712 950439731
    0x100216030e060c0303100810060b0f090328030305060d05070308070c050402030a0b030d020c0a2105060403050a09080c030a022215090b030a0512073009090218090a 72
    0x400145002e11001c03106e0008083c98400014503000484001225140c10b0a204200030404101a105000c1560480035628044900045c0c10f04920602d001e0000d13100d08107804141c81950200580c4034400d0714200207a4540100704036200015100041c0b103644180000e03c000b50459014102e46441644981c1c0c02d075840300c0c002400d98004417000540203544031039004261400700300b040503040f618006007502042d10800302e599600300317000e03c419500c8011007545c4040c2e0740f481c5040e0925000001c0c0d6031388d4202854014400d6000c01000030004035010b801040f2501e000c21100d0007414020000d00c1200116402e11240c02242c02031071402c10f0300c2ea80b850100d0492401100c0b0300714145100da012060414810000329480704034001d01035442516140c000800001e40c006c00315070000b010740c4c0c41d001180741080714401c1d44043d03503140f00c00380354020301076140d0425a00d6043d070064603401b440c16110341c008d400301c1c00b5402e4007444401c8090218001c0d4103200807016002610300390b021032900c08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 950442212 1250 950440962 950440987
    0xf02060c031b0a0614130605130501020720150d05071b03022a03101808070f0209011203050d270804030c051012050c04090606020c03100216030e06 65
    0x2c07191800c141c3c110f002e10008204403440b83c5120018034000320641c42c100982e10f58103d00302d000c8003c0a40741d940010410782c10030944681c07290366001009540e114a146030250140014240301c207044100a181e803892807400d89020f40c000b80d00d81d41d400d800c100301092114054400501160103115504102040c18003500d0000203095000750010f0a10280c4201c2c41407010501e0900b03000c500229001400044d175010611900346a410702c070100e0040e00c04030f004103015003070310402000d8810010742102000a10454558264001c80792092940e81e1202c031000c002040841c02070020b0410070001d03402103170540c440c45402d2580d600156051200b0030904038180000e01c401e0b504072078046000c101f00f05c1d200907000064081520703015640000e100e4041d0100402ea4142824240c80d100002c52010304401038400034640d000c0103006030350f03a841020b0340300c100003d0000d0090203170381000e148903201e60003103c1510040c801990741d5040b60b03440132110b41071166031165001c0ca0070011411002d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 950443462 1250 950442212 950442247
    0xf0204060f080a12050901050418020d051905010b120f070c120908010b040b0a0b0304061e060810091e020d060c1e0906050a050904230a180f02060c03 66
    0x2a80c08001d003400500f41c101421142e040506482c1048000c01c01d014840c0d030b0217000e99040390010aa91485d07028111000c2019000d01101e020280703103802c0c108840280710b400340f0394138a603942d00308210907600c2c0c18145540348244002c44124002c01c0c400b0039010721364103404981c07200d042d203040300140b01540c0c0e43c08210100d04000da40041d5008006001800c1c0a01c40c0714241034080341c04110071000c0801288031080c06104403012880003000040a00c401034004101ca5030720007043d04072076462503480d80020581c034001d84681c1d2040203e0500703151194480d03140e48980103880d0b03c128501c404c2101500d2221404100d07000b003d05221440002c815000314030090300240c843c0703110708042e10380c405046860b802c039001c100400101e0410100381c000003215070031100c038607241d6620520000030601034210114103485001e100103c6800e604005803c042c01520507040600202c225401e88032041e49540c48043c045080f0491204014604000100034015401082d07a0614020fa0510b00302031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 950444712 1250 950443462 950443469
    0x415090606140a030b0c090307080d020114071107210605011203020d0f0909151e050f190e070c02090106080403080c041424160b06030703020d0f0204060f 68
    0x41d88414090140203100344001284030800d03943c85280602e1034941e88148100074041c00d551303880c0002d040c8580e032014807440003e000b01c002111849620400024004c2c542c18940801e08900382011aa41c01c0c803940c1010070000c82078006290f100e081c07003841d03020109440b04103448800070b00030318800103007036015850082c0340c007605001004a5a05010382815070710741a10f420044560124492070390003040e904152036501c00e0018180d41000a581c0d94806160806074030301000701e00110b04081104581800d0f5441a16080800c4040000780420704925541500300c2c9030399400c042c051120001c100c7e9034004154544040c41c007039a0303008a20240400c1e0012000103800340304110070b02d03070055005e40e08440c41c25900f40c549450710040e82c0000c69034080782881441d1052052182500f22078140201107202d00d6060f64608000c42011426091400704407a40d40351440060068034001c602c09084940180c100c41e01c1d129582d075100700b07110000c00b003264002c0c0e80c1e103400310740d502d040001c08016 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 950445962 1250 950444712 950444723
    0x12601030c060503040b01090506060d0501080d12110405240a02061501050a300c1d04020405030618120a0e120703480509011e0e041509 60
    0x1941182030802040c00c094110703000f031240402c14440000c10140340141103a03160040007134561280c20000e00e8600c59404030204003401d010001c07440fa4000314901004e04007130b803610001144440380b030500740d400650039090800004c0c0007c109604052900300601d5010001080c503100c2d5298180945800000e031800040c0d2002e82003055228030300c0c50340696401c00b420017070304040350904c1c000c00420321120018041d20000c0c00742407500300d400e9424a1015600d040c08d00c581c9112020051080316812010856020303030041e040c22500b4a032080340e0507140058068803080d500c1d804038800c001642c607207040c418400c0d240c4088040705c07004081d18500701559905c01c8644a00c000700f064441e0000b44030303041c0340c01503101000020000000c11100c4490720f51890b281803020810541407650810b4400c1c41c5400c41d0302100280340d0300040d91400d8810403030340c220160340c0b00c0c1544da08801c0d00004212145c041c19070b05110000d1140d05c0164401d1240b1000c401d01340580d13001d2803d450010078219203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 950447212 1250 950445962 950446037
    0x1b1c0e030412170403050307020d1a1807120b01090e071d0a050f0f0415140c0903010c111b0402071a041707050c10110a0b01081902030a02010e01 64
    0x1c100c0d41c107021040c80d0f907000e41e00b24249400d540310180c592250002c0240b05012502c512820011001d00d02c441e98085200c18020910341a80c050706d82074215220410540140e020104400a0740c014584800380c2100b0307a40c00c5682001c40c0f45000b0140d0002900b494802c122000aa50020310200c01c2c04100f406a841078504120400c1001d45c2c00250000d007807504283e040120000c04001c1a41e44a60040515010f4022440305000148424400c500428100d002040075550b03181c0020300c03500320250300800c8030866151080303070358140c00c40d0044110303000000901100400c011413450041e800605c014500715560b03488064042070b14460024030f0f0103507400c100c14044423034251f20a52000111503464000c02e41d039102d860b152403420781840b40340c040c511030114a103d04642d01d4000101801c440ca9411142000014500240304448091191007030417101d0301403500c1401d40c0c20764054018010000c040d8015640c0c0501c8443e10f604204c0309042e40118102090040365944510205114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 950448462 1250 950447212 950447249
    0xf031e0c0102100902090403030923030316080708040f17030117100209030d110703021804060f0b0603010306022209021803060f01050d080f1306081b1c0e0304 70
    0x2818654510440b000c4286010000000351b21070b00013043e0322551500d0000360030300075403030410064802c800a500c2544080c3d1000b03030a442d0300100840c0100703509080d001170240d00c00d0084503481c0c07048403128000f41000000c5000030b0000c42110074054803890441d440ea80b01c0c00445a00c5800c00d82c042d2500c0e0701000c0c1e1a800c15003050064220448010106514040e407010103c0c0d501d8498107003035030401c024000112400901070000c00051a4010002c0b00c808081034804000c6040950f030990b070340c92801c030007584010300c10302c68440540030240072141140e180d9180e0000070742210f0030a80e000c3c1c081c1200c408000107a1740d03521001d01210100140c49000387c4001d480321500024809000b0b9214106021050107081c91150444004840d40c495000f00d81c6804e007014001c0d80b10251640d40c01140c84600042c05220b40ca003607404540c1d448040d55103130920b81700180d01c017034803200800d01c040051800b043d050400c0b8240742c0d100c3c03500105004244254103859a44a640500b2220b44201c4500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 950449712 1250 950448462 950448467
    0x71103070f030e01030608031b0c03010e0601051f09030609020105070f0803070311030118020906070c0b04090e19110d0b0a020c010c0c120503060a090203090105010f05030f0c0f031e0c01 82
    0x840c401e5074203180401c101d5007801d007070503234034800c0c01e04114021202c42d42c14481103004102c00f240c1441d029000380b00d1010ba54040c959a41400e000325031054560840008100c0355071030100c03c09119030342c2c03004da850b459a01ca690041540c10416810071800300704442c0801e00c80da845079aa6840750456a42d1b07071401010080c210340303243d403c050a40d0810001000030045110850303180b103207201030040e0703105103240000b80148a4a00024044441e8150008444190201a00480740c1091061020b1065060341540380c2444500d8030803240c40c08090000420041c40c5001c4500c100500041180100354492210703a8008685403400c180d00090007445011084c05041d0302c604460030900214856552688000c043d441800002c010740400024003543d0752200b4400206005942190f480c18030b0408240648024040d21808944450300081c1500b0b00050f002c1702e41e5004d102604034222180204204520700444c240d80c1407084d407941c00b40c01c003800b1803a100300b0102c0702d0003000a0300303045001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 950450962 1250 950449712 950449727
    0x3141312110a0213230a06170613060f022a070f060c050c0d05030c2505040b0402070204150e0c040e0a023709050d080f03071103070f03 60
    0x5400402a41d003168040c58640018158400c07541280c0c03c07800010440320020040ca40c001d91980d960399040e035220201003120710070b07038026a20641c0c00c0c07103101d856003242014501d044041803c10740c8040001021040c1342d00131901000c0c03140c500455800ca03800b00396004d980050b4540314101d100d100800d820071030032000400c100d15403140503052071380c40c0140c9040d405c0c2451190000f80150030356204200801482020207842c401001d500703881c036542c180150780381c100c1c01c1e05250324441d01c1421652503000003244840951490200c2030580d0600041c000540b550858050704103400780001c3d4016540e60140510180c0342030b4402122528084d20043e402c00050304c1003030f229504100a10980c105415041d500c01401c00c4050b0340c034211508131144400302d42c8100382020510285c104040744494104010780009583c0380a42151103d00304800c00340d4110f401007824100300064040c0c456204007039944103440d8101170310070801c0103040030b04513880140111924031040308c0355802c141e040740c035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 950452212 1250 950450962 950450993
    0x608010c0206011707034707030c090510112107020616020a0602010501080d0302030114010e0a0905190606020a0f021e0d0b010623030c0a031413 64
    0x2481002203904000c0d480e0081805203401202a10000c0741d228802000603078015607012420b0040c100e001c5062410550308494403000c03a044d141d035a4a14550042c00c2600d540c0480301804007607071140c0c2401d80041000c1c20030b560601182810010701b80d550315141000e40842c40d22042911040107a1141c10400309504c903d900010300100252a0030703951040e140065415500d150b0349200040602c1290b118109009500500901300030804903819004503049803044000c0b202410300410040d8103038002401000c14803594008002420361084211501441010f0a4114082d4642104e201074410482e40c0030b5121121801240d00c80307106108480c0284403510103044000b1490350f5040e00001c91402c064030801340d03140008001e07103111151a9032041e004001020301481071400d000c17400c400344203683c00f003502c080308505a00352140c200000136003001303281840c40d42c038040440305a0300310440003010541e03034607005030000c0e00f40600b0310b0090480c00f8000000041038030781110310002206 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 950453462 1250 950452212 950452229
    0x60f0507270e092d030f03040c03050d12052a030a06080f01060e01050a061b02040e03070b0609060307030209010303140702040603140c0a0b0901050c190309080c0103090b061c0204060f060306 84
    0x4e218905903603005c000d8a80c46001c80e1741e1659a500d40d41000005489540c002400c24020340001106c86e54203c03000b0380f18032020000c1400603588008451020000c182007070010140000c1040c0350800359000155400310501d80002900c40d11130407001d20b0084141c00800d1580e40d1068103102e0547e10a1143e070040c83c0031103460680d03604202008200b4540940581c011f4605c5900f08000c668868100900038805501100d84880303e07402d11050003402510080e024040e0383c0c003c5881401c000c01c07000c0c1900d401070000c0081ea442c4d0b58080707406071028400c84001020030b000b89001607480e806140001c500481040b005000718280d25402c2580000c45503101e0b2030068010017580341d0360707003c3d2441d410003400c04548450801c1701c1542000d0001c500340d9081001d5481110816800400b81c5041da00041c045400395501d400064040b1030001c0c0c006001c1c2104180050cc491a1107035680f80100c6140c1c50140c211017050740807030281c0322203412070321100110890900c0300942c107111704402820f803403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 950454712 1250 950453462 950453533
    0xa030b01260601060f0f020703120e180411060a21021809060109230a0e0f0a0926090904033501030807030512070903060f0507270e09 59
    0x310001c5c100c50103c82d13159050001c44c1c0c05558200b8001d10240e001580c0005480d9500a04000014120000070340402c2c4500d030b144080405003019219038a12030703940244020342075184101000162340165034400c040144a0703081058020340d010858882803154500540c844400e4200030340b000750010600c9008028035410000c80d07a038040d81020858040ba01f04074000c00384e0b190400042071240e2a9590442e008490010707000300b500300c07001c1c40782e40303a104000000d4546001c0001620b10040d0003500143c885414202a00d241c0c0442c03641c40b1000b11170151400c400d00c00421982501210180c1c085010041e540c884200011707174141c07012001c4007100c0c50003a4100c0c4003903191081070001800040001c1218003c25020710122400024a12501c0d0b0a03443c0642c4024482842c50004030b4015051548100c800541c07800b9050160005484590340300086061030428000411111006611800b0000407507442d43c0c02c215000b8807804002d04401da502c1650f501c0d5101120030b0300601202e40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 950455962 1250 950454712 950454719
    0xb01020d0f03050c120108151b071112060703090201091e0306111c020705100207020330040f050a060807050a0503070903080307020c0114160602090a030b01260601 72
    0x802401c07840d903001800c000a46440340200540140140807654070081c0b410030010601c00c100080000d03038106060445a080d0b5a0080252840c20f00c0c8030b501440600c0c28880d00d8000b85c101d02001150540c040c09480d00e41e1511901d6034a4910103640020100c0d40d502100815540e11450704c2010308a4484000020a084100700c00703a0f44041c070001d0145503450b41081403004d88241110000101c19010302505051580d81200962010408130744034031070b00d0072680240d81503000b507440d40382d00180038105242c3c200b40b000d03100c20383c0030407510711303188000c140c9010400950300035001030f02c04a091107904ca42070405200c0700b584260800e40074812040f007048030310f80d80038048032044800d601c2d10503100e4849120903034109000c1d410040c043d81d800300400c0076441c2d0005640401c1102681c0300d01c01e5443c421360300a10341c800c4d00c040500c4c46451124540124039580c00806441c440071b0304607980240d482c3c4400040314801c0e0801c12400b8801c003915014080d035502c50b07500c1c0321821000780085515 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 950457212 1250 950455962 950455967
    0xc0218130209090321042315010621020717040b04080705040b030304120503041d060118030201140912010f05011706070906080601050712210e0a170705010f0b040b01020d 75
    0xb035018403d0404002c000018040081d545000c103a09031111540d2034a0600c0d061219442380448040108030301580000029014071491010381c103c590f004a400a92580040721000303075110100c15a0070152031540d2592003545000204014110701000c10b80356030070f00c8081070501d40150700051045083c4008207900755408403c840485080314903c00103080d042c60a0760541c056a40900f400d200c00c420701e548000344018660384a10340c00d03030b1540c14481c0c8050400034804046d01010303001410404c1d18410802c0071000070119440010400300a13070f1010311707a980c01d4881341c55018424035200c100400030301c412240c40c06540040f0a01070b05c503500d0a050010406000351191008010f1048003241d001d03402502102c4d009904407084460802e01a42c01415051460006410a889210303450003a441d03039200da420b1110840014190b01c0d825078544400c811310303503000e003078100310100901000103500344600154a0500e000200794010904200811256862600c1d030664000741546481d031a13 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 950458462 1250 950457212 950457247
    0xc0e030120090d0f0501201c181b03030311041404090303020903250f06050415030e03030906100e06011e030e2b0318030c02181302090903 61
    0x2461602802e0300d903000107000a803000ca070f51002512101c11070036040280601900000301c0c0e803080c8200e181d00742c0644407445c1e00f144510b40041c1312200c410052181402c089801c6101c4a0f04800c1c010000030007540c03940542e00b96000598040b80120300420020140c05000c1c507040b10300000109400c082c50300c207168640030710410b181c5200f1540c401440c0105400307641a0b41480002404603024840b02a280000c02a02a074814070400e80100000034030404030b01546094030340a6883d103052600d80180092100b0741c2c0704804041c0b507214901c0344400d1100700050740c401c07050b03031005001c241403400d846882c000041d0003041c1180744040400190ba41c005005283e03114070300c0880e440b003800c011412401400104c41003c80c0d40141186078090a02c402d5150310190030a100c021404581c0c103e00340c08592103008006110700d40380c0c3c13442d40441d000d9595880030500181c0a840700d50071006600390b90003421500c66142054403030000c03040d0b0400041060348100b94034000c3d03103491510302c00e0b80c0881 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 950459712 1250 950458462 950458511
    0x120030f101d0f09030715050402130e0a14010b0d020f15030c0d050901060609031113050901090b100f06050c0f060a020304120e03070b1602060f0a080702010603170d0b10030c0e0301 80
    0x7c0d82c60f580400e08548034043c141c583c080d030003c81000215101d540c481c0e140d5550000c280d400c4041c180251070340711010702c02c480d00e01c9001030881103811f00d550b090000d100b411190542c1c1c0003c008292036003d85000e002035100301141c014243d6151605000780381141c03005031240740750307038504841840b103203402604a10503250030800b0b2650f010510000505400e9042c04d052a0b994204801d018520702d0540100d468180b0070100c001071691039401c1c407559680a840b60b00301d040703c3c4000c20469940900005c040c0001058241e50511a150110300d03c0d202046c0e61160f8020b50001c20001402628161119590594580200d65190400c00a55540701a000d00e0075400400100d0382510410015805d00866000c1c01540d161018100e5060301034000309034001c0810f00034400541110f06c180b003441c00352580900003200c1d07105207002c07a08840c2c0280c0b40b1300407890b80e58600400c17569140c1428403001d90342c6981c04280c000e0348900041c18000b200042900030382c1480600d9600c00c0d00100b109180 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 950460962 1250 950459712 950459753
    0x80a02030d110a02040f06050307060527191e1706071107051e040b0603040507030b181506010306080f1b1909020c0120030f101d0f090307 61
    0x849148000c21030403c94007038030082d8071500c0c0c00314024956032590070890481e00e040302512141355039440151964450354090381e503800b0301c07900305030f0b125411250700c02c0c0303010f03000740510b8040c180e5030b900c41600000e5a080744200ca0301c450b085500800f01a5661005400141040101c60000828096603a18041c0040052020500c5c1c0702c0d07810102000260300a110080c0140c520720300c548140381c4125080089103005900784a00002d16050000841c0d0003558481e0003483c03d01e180d6200c159160501a180358001e0000d040d0701c5101010800c8030380c9200010f0007901d002818244000740445802c1d0b1303c0994203401208103030700340100105407540306208404650030740511000000d4210b15001a0762950000c81c41030106240707000380d01034560b15000000030000011000001c4540c08500700381c82c200e442013040081c100c4441e200710305800001c0c5080740401192284a0502942226020100341e4240e880c20401d131405c3c00261b5580100b0342c00c002d180b5198032034a03041d40d004041c00e2070980 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 950462212 1250 950460962 950460977
    0x705030d201902100614040c090f0312120903031d07080c010c05010f05070804050c150a120e10020720012010020f18010801230409050a030305070207080a02030d 71
    0x290503009020000d01058644d1080081e1030b00c0303081d0704440d0300e42d02042c9070107a0316065417440880d005da46902d0030b42d10300c80340c0030b0070241c40c503a58040c45900b401c0190081007508003140402c1120381c0103d4074050f210381c6010598901d00301c2000398410702c0c400d62445c1644455070400c41c0010205103c0d1080c042840c00b5081d503a05402e00030b01404850701c0243c8942d140c06e04000c900e0340c0c00b900300c40c0110311400c00c0d90101d058070400c02803a200300e400e031305070010b500f0482071a0141c02000035082c2001e0100c40818240040c2890a0800d10724004800c00c1d560002520400c0008404540c0e0120601c50700600042c40c0d0040001c004003107550407454034140100c1c1ca072030780b6102005000c0440c1da041c0801c0d1340c1d5100c405581966600007100603a80410703007090301c0303d140d0701031400c10703050340d18030440c14548122200c502c0f14107104035141c040c1c115541d4002c201c0401c40c02d2295528050090300c0120b140c3c00c052800a240c01c03001d50041406811100134000181d50209860b02d10345002d06d0300a1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 950463462 1250 950462212 950462257
    0x80a09110424030f03080a052214010f0b0103141003030c0c150e2704120302071e02030c0d08030411010e0907020a21090b03100b0705030d20 62
    0x1989480c40b424110071450900c000004c21080200410116119a0314840c076510b4500294082e14400d6070144082d8003906120160703061140f0702044407038014411240f640806c0015207084500c4075010050068450100080950b014000d4000500011107a1401840c1c0380b41905004200c40c01f0040412002c1342c0f42d001401303c0340c60100c000c0c0c000304825179030100ca0314001074049201c04007410301814000c841c0304580d0180302d10710307245080400303900c2031907030364540d10450090382c40b0200f8400d040d424000c0c980464161501d4485984025061440c403000a004147c0b4004203070411600c642c940c0c0d50448001180241034a4101c1d9209400c00d201c180984016245501102c0700c464000c040d10080090155000811226860103180381c050110b02c44c99805c02115100c8283c6808a0182c1800b000108040001542d205010392002c10070a6224441c44065901c04042604c0c0d5500106010000980702d12550030301c04800110350780c030080607581e00f62090046290322110351141d1810740 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 950464712 1250 950463462 950463491
    0x1407020d081f051003020306010e0429030304180209040e01020a09120c0506030f1e090309281205060105030c0a14131b0806060a080c030a0f09080901080a091104 71
    0x2c03006810000c012419140b0043e100034020341048501d6800102c441d0904034141c00c01e84922020380081c42d08500721207044014052145845007040c503018403041100107412a20301d4020036608100c604050b0790342d5201420403081d1940c0c00403c20080c3d2042010004040c0c01200b038501725001901400708102c4281400d2526180c41e62007241c10036000420440c00c1c1242d4103040c0d204400c5d40008541d504080ca441001d10241110103210f241d0041040700f041e031502040041041002c00c40704050100aa02c180142c00e40b25800f4940c0d0383e50300000d2070104441402801c1c09800d05034001c048410503040010b60798100c61180800c1c2581507100d4016507124580140e00701110000e00388100d0896049000c40d102000d445240012800c901003415440e080307040724a0459560380e40940f07a204c100888105520161030044143e580300310040c0500018010480018024503e890f12424404005040000024070960040c3d1411420400040c4400c1004204020990f400164000700c800071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 950465962 1250 950464712 950464771
    0x310061d060316030e0a051b0d0f030e0114090d021c0209100510030b0609012f150a0e10020a0513030506010906080610060c080409020d1407020d08 65
    0x50781000c8004104518001000c1000c406944a0354040140164171040d440d2076000400004100d030b0080c03082565400d400140c0c251007058000c0c100240050127a40780c1e070020821000c21408903400c1c4029038180d6822080c40d500385149000382d80e14050780080054082c0c940280020312403c42030403007541e103c0e103001d00002c015a0180205140307081c4000441042e002c1c0b441414400c1c5d03000400112703c503111703004031502e450000d0011800d040071a001510704250302c960104112200142e0903e842a946001c03440240300c0034080c1009236280d14500740321010040080d0181810a00d4101540c00001103004110029410058685601d1101128103100b600f0680074609006140401031207000f00e94039040710301e65903003001b0079541c40f45501c1d111202221001c08003a0002c500f00100d5000308500392041e449140d62924283e11082110102e8020040c0c0381c0b101581d4420803980240c4002c00181c010103140000d1501c04c4600b000200107100c000c14802020b08600c1c40c0c1880d0b030102001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 950467212 1250 950465962 950466017
    0x1e110c1f020c151009021c02030a020c1f06060903081902030d0e0c03010506010804080f0c010b12030c0f03390106060203191404050907171e0606031006 67
    0x603a1640b11035002c072402440301c280d8904081d0002008001740400c4540708441134640b0203d03540081e4610940150025040102503203802c640030001482d41c18070901c011919806c0340707006000300c5110604201c0440780150442010b01449240a101184e01c104c01d9880f82d010f00340540c149000018402c90441c01607614444101d82450034891000b07101150303a1420142c160020020365550307000440300f4050039139001d408024104000c50f011040301c401040b1503100b0300c002040c50b0955901043c0980c04009401c0035980001c03410246003001400f00580c1050000000c6081804840d010100305400a81c6d452101c03465032000c01c0034000c14098420100550f8000304070740c650356103000e501c1e236000c1c150210030034002d0101d2111050082c5a41085000b030000b009040c6400c0000b400502c04015000c0381c20300c940e00003e01d0811030040c90f914856605480c0000390402600051011054090440f0744220001e01c1007000c01d282d058021001c850041c60400e01060340d211290758000502c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 950468462 1250 950467212 950467237
    0x10e0f01111630021e0907050702131103070507050109020d06092604060503041e1b05030105042d05060a02181207140604091e110c1f02 60
    0x1200744041450000c45001c03035241aa8080b03c100d6074160218031000342050b0b100311292203100c0d00b030160400b0a550b101c110001204030720b50130f0300c8030002115514101c44a000080000a0a008504104140350765001400101340416071b40351050b12594040200300030100000862060148182508282400d54020f010000390598504040c4058001e41da01640c8100c13a81003031075041300e01d880c10448580f036207166140c14642004021110390380060700903140c2002c15610500c0110700300c040c5440852080c18280000103113081c0461060101e64090b612991401c0100804100110918501c400d608039103451086084460790000c0c41d8841006016403143d00100625600d0f198000c050b0a40404243c1404000322820000d0440c02d000c811001038010034000c00150510701c0107074680c064024000360074030b501c8440c6402101c42c140d9001071444c1c40001c02c0d81c00f0350510700c2a000104110b0704007614040410381010750310703040d54080900280d241103035000d5181c2d40c0d07419a503100c01c200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 950469712 1250 950468462 950468473
    0xf0604020d0b0d061b11030a2d0f080112030e1c05030f070501060b0f2b1e06060806030601060c03120221070801380415090e0105010e0f0111 62
    0x90030410700810621102c0411600c07131800c0e02e071101b402510b60707440e01d801c103500642c0740c548108403c0320000101031110102e030384444029080700d8051003400c0395004ea00c1e80c841e4030010a0003c010683c081c1070340240c00340010a154074010a5001c142d401c81082c0c107a0716450380780140b40030345608a1500310083c02c01d001c0428010112014000201410f80c0031b580244581c5481d82d070f800365188524241c40c0015042000200004048130a9840c4094041482c003545042c0003c0e100b8242c4005403210806808503191b003c0922045101c2d45020388068980001a4078007540403a80e02c4c10103001d12414032031018a95820948145e0550f810400c2010040d0349864031141c2803030041c14140d0380919205142c0c2c0018603002d2183d45400c0c100d0f0710f0700441007003450f02604c1d124000b03000c508062040703066101061710055130b40310040000f44006032595019504559004211040c540c01900074404008010402607070700044286464900300c0b07104841020f90030040e034128038281215a52030049 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 950470962 1250 950469712 950469739
    0x40816080d081905090c0a0b0a020601080a02060a1d1903140f19080c010509030c062503111902010614010201020705120310080312100501080f0604020d0b 68
    0x4042106080399541012505a0001a103003698a080115503210010400a0384900300408036040b041e08900054160b541c000640c00224081034403903008402002000180c4401d015410402d040c010302d40310000d01030100320341e80002e4241c82075032108410011a0b002d1a0742040c4500034140045030000d01c58000031500000241c6091150700c41951a46d040800f07020040134041903080b08034a40d400a0720001982070360302040340a199070160f40d404000c0c848010b401c10309106541c00f80518500450329614888526440c2010003084040211600843d0a4001e1000b190ba82444041c508004c02d026111455103111801030131300460715550030040d08101c254041d0300c0901070b14075818940440100c5040103a00380e00c58004000d003164010003110f0341c9042468081d6410600342c5800e80d4100da42d44284626541000e01441800002441444429100340316020300078802820500c0e91403920524201040c0d034001d201c1809980c0000307161912081562100220300401040c1da98805031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 950472212 1250 950470962 950470993
    0x210050c10140108030304020f1c0816060608070305060a0c050c0a03080604061d0604050402150c070e0f071d120a03020718050405030a03090206130b0a18050d0303110408 75
    0x100c0301c0403075810b019940042020380c0301000726407080d034003c0c010702003100701d040c1482021000d02075445a1054074580ca0702c0007403810310052045211409003000c0046039820880e00711041070f40280c40682c40000108001000800c4c1c0c103a008880f0b2400181081d10460180c4251045240260081c09060400d1040640000c1100c0c000e184c103480401041c0d13203404121600c187c1500f0741454014407240001e50514064200c0c036402032000d80301c00442428000440700342e410480403180c154101050500c40101c41002080c2e1242c10282d652005007401500542040b1000000366034035003a592020300141c8400d2650050300c07800d04200c4507071400604000b0341b510780c18043c014641e807070003a070180c0805082c00781034007881d000b0024500d0030300d03800015401040082401ca0b042003091160545c007000103d10b032402070080c4c418080e510101c00308000c00140c2c0740341c0d150068142ca444148101e03155141c2240d900340d0300d03013400555004c038401d441c10140510360162200e4030030b081c0ea60070000c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 950473462 1250 950472212 950472221
    0x6140c0a12020318311112011409070504140111070920120f070c06090b0702240115090b0d0914030301060e06071110020d021009020d0210050c10 64
    0x480090495210b4402c10200301d01058141007905940d00401c0490341202d4161000c40c0c0e100405040010b6060381014600255400c002285010b03d80c0c00801040105031403038007007020010450704ac6400d4a8050300141c8207002d10b0040c0544840705810000050b4021156104000715280444424955407a2071801801d00200da0300381d113520b400b07402c40c603801c0740301c0039210345404c1210f1405030380c2c0e2200f81d00402184014600b900b006203454070392000c659603200305600c29010f03461301d000b02c0c0b410340b001a04c1c5c000d020010070150b0301c4816210216a020446407030544001c04e40220b403c1405490490f40051b282d000307450700345000100e003d441c01c603da006030612842009620004018080902d0f100d0209110380c1001c100d0340c0c20000101d10b0110700070b00d080c03882200e6130702000c1d0403007010665001c0d21120420259200600d84204646c040150702c3d6001d16400c800c0c45601d00c0c41e40030800d4030b1310b1040001c2c042c80600c4030003600c050050050320842d00c0580115080241c01052070000780 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 950474712 1250 950473462 950473477
    0x708030f13171809250216091a1905091f081e0307030f0e12030a030614060f0d090305090904121806020307200415090b030706140c0a120203 62
    0x8a543d00c011004605000c01074911444e2030007108014500041c00c01050001040c0000c0d0443c01030040b840b2425502d990a40060a16202d00040d0800942c00c4074040d001000ba1341c910035500106d1000c042c18a1030000815504282d070200790540794039014113003842c01005040342074030745c1d1a401724a8460021300d41c80c840340c8030508000c0d03000011050b1500e03842898005000212a01403284040c2d005030300d40300300d82c04003500001007132149911b40f905541058146c0350029072075402c1007104c1d1001c610400800002105c02516122028903810000c0c860000040c00d0117807508103180515009105032555640042c040c0039841c42e051402e540000740e2081d240c0c010800210f1a8144040c00c440040c0c00c3d00e08a0700118505511070319004200d05400502128207030141d203410155444600a1003c261000b0120304941c80c00c2611540989400980a9000340d00600041004552003000001a04003644000790b40c3d0a295034820309124005001411240b0301507903811150341d0010050101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 950475962 1250 950474712 950474737
    0x6062205041a0915061b0304030c09020d0c0914011404080102040803071502032202030718060302182a1603050d050604050c030712061206060f09020708030f1317 71
    0x700d0341d035000d0380680704c01d40c07082454126505004000e002191841034006043e5007408490810f0b5895035002020811500204600b54001c9031000508906001d030009a100790300b4200043e0303081075007092249040c224900e040209940c01c15a20507103205c01c07100981048402035550780d440311621556030b44800c038211054486540148110b84081c82035a0040e15210400c0c0c10700b104101e041c45e40c01c9141242681e150045e003c00142c41c010700380b07c203421070002660101d001c40c514010400b61404680300c1d034080281034801c2003c602c0c40082d03525640e04803246c030081c081c00b0242c01d01034540a0170700d411001e00303041d00c004028035800902030300441e20724800078802c1b69a034100340720580d0310036600444c0c0303843c0c1400802d402d00e000d01071030a68003001c0000001c01c2c2d0784d540c00882e04031411304000c0e907401d95214418803541c000c1121502c040d0030820001c0d4540045035071650010311000341012440303180300020420b20f42c03a030b0340d580c034a075074214a485981c10041c0c1c00f031255a60120005900 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 950477212 1250 950475962 950475979
    0xa08070c020609090603030c0a0c080d1e0c05120d0207150b0a26060103230f0d0f0926070611061303090506041203090b0306062205041a 60
    0x5005100345482880954060a00c605111854040c010300020107410716a26000522040103e01000c00900711018000c00c1c501090525003c0c1d600e0604520302c3e004020845843d07044050442403038420306680f21075140c04d908274003041c00c1c03403410700543d84105400d002d00001c404011903225000b0780b080c18054410490020b10096130401104c4014451940066071040200010326102210101d1009040080c5054221074a812810940d00344c00c00c071403010609400c80321030f504445001c01d1440f002c0c401441c002c0480c0348815907032030390b07071003084204044100c1400c14240314044c0a0020900902210b104040d207404150054028800490041c440c151000518601c22801d0751a0030005401400e04d5031140076244118940041003a0144035000c04000359070f40300e41c0010b100600c2c18416180f4075540314a80100b031078200d036100c0707002501c090003441426502c04085880c5401e0074098040c0407440c2c1484500702400e01d82c0400c0d449031814401140001c416030540d4500710040310140c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 950478462 1250 950477212 950477221
    0x3050f0a2a050627010c050712030905070e060112050f150102031c051e09060907050a050603070503071404140102012f0a0e0d080904150501080c160c08030a08 70
    0x1d034115000ca401410660211001c50307030350258100d425209044c4018650440200340e003400703095401e5402c3c164001580003c4041c1031080c43d04c0100c1e0407510501d01800005010f071a2159100440d000d640c56001510700804c4440e80240c011082e4003510f690103100d540303018000e41603000d10403509001405451180d80e2039a61001c01241d81c40c000d51640c2925116404030140001e03c401414100c02800011500c03400d034001408251090650200a10316444d16aa1960400d0020b85c8218018001c5410501881d501c0c0f6090725880071241c03518680380da41d200303002c4441d150480c001000140c4001400300d84089002c00020a01d04281c000b80800d41964286000d000c0c064001d00c041c05151990100c4000c0922000f05041c001a1802c0310b094140d0b18001000c03c08108005c0714100e400250030500307424140203145464480c2c081e2014003d01d01030000c0d041ca0b50040088c401b00d0000250340d1800801c1d814440240343d00064151501a1920703403007a500c0c0d00082c03090700441d56002c0002d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 950479712 1250 950478462 950478527
    0x1b08071106010f0621091101090e0f060409080706050408190912020d030c05150a1b020c10170c030108011d0d080c071b03020405010501110a0b0403050f0a 68
    0xc1c12a101c043d0001841842e141342120481c0d042200c000425100004840c0c0d03500d0320740601e191903070043c20451101780240c0009804079a4030360100020301c1c00c1108000280d000c00e8905648940140d402050401c1c6030300d000111031040020040810b8078000c01e00082c0300300e16010f080c001c06081c0d040304102075003690a460603032051091405e01c003240d803080300c018140008801d84c0103121741070161203140696034060034455081d6042c041588d00d40100301b1034074514054a000103d41041c08220000021002511008980b0031940a00c094641d8221954400e0300c6103030510300760031115821801c0c13142402c40d041e0b00a20031000c4c1c542c2030180d01e1400000c5d88000204544e00c8000038004001c40f544256140040284000540b400912a803004604010503402c01412030045144400d030a62040008455041e0031450400888108000e051140002c1848032542c10540504441d030b106d00e41214240708400112247d03040c00305a11541d26044058100440f2401e0320413581e9154102e4074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 950480962 1250 950479712 950479723
    0x9060a03020d0b0a1847100b0c1506030f0d05030f0109060609060f090504050a1b03200702040e1e0118030c110d061b03060b0903120d1b080711 63
    0x5888801c181100d004035402d40c8011961a0812032850740000b100041c00c0500b0f8801b201104100060b07500412901e200054110006801c015198505040203940000c1d40c68000a600c0030709002054041440c940c0c0400034800c0054000781158540340c13601e84014080e4006030b030310210035041c01001040303030300c2580520425106e0310366444402d0340c60b04208484400d046141c00040c0305014001003096215030181ea03120798180c803c041268401749044060782a07d511035041011301d44100b40444c0405505152080321075910195101c0002d40001801000e0091450750745210700d051000101c00451240e10403100414001c120741c411400d5a080200414040200000e030000052800200044e50200840c1805003140b081d402090303480030229110000d0100c0000780d000039001c086503140c01040040d0a03005101800c0140181c0466580d46a015003001d003202e0100302182282c55a500164610a1840400c800f14042c0ca00160410005540384000110140d65007000c00790300246 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 950482212 1250 950480962 950481011
    0x90506011d160c030f1812050d08060907030c090504050a060e0c0a0507020d050c090703020c070501021609050910050f06042712022506110f0303040209060a03020d0b0a 74
    0x31420005051550300f01e403290341c504c00c80d0003400350400d40410020800b45404015054000c03081d501f15a282c241145442c0c1004103040811003428100845a1a011482508000c0740e040204000c4ca0640080c0c40d0b400d6142c0006401030300e041c0c2001140c4e0301c030360004d904071084103910250301e8448030700c00e030358070f200302030b00c0d0400310748200040d00040c00c0491241942034007420a03a1900111140081c44070303082601c2c200006900481c00454078002444010003c0c1024001440c2000208160444a030910310540d04610b03070f6080040c91110051041c03074624421a101000149440410340040d08800d4803400c3c001c0e80f4040201c4047c1ca105e22161380c0d8840c08900c0b000300c82400d0f566070818014140d1440c400c43c06101072041482d480d0304000a10328084490800780c80d401c226000302011000420300840d540803c0034854000804001ca0380c01c40d8040e82c0c803a80a0f034a0340082000302e0051f80c0002d400c104015440d600b0701013000c9500f4040c201044081c808880856484c880400d00e01c00f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 950483462 1250 950482212 950482217
    0x1020306210a0b151e010f11070e0405120a0207030309050402091f030209031609230a020c0a080d0c0201060e0108370b1009020301030c0612090506011d16 68
    0xc1a460124103d40020b540c0001c080c01d00b20342c08001d82c004920200514014a011751340082c0110103a580c200703c0c0308505880616100e01344e12010482e8a94500d0184a041140b81c001c1d800b01c0c090010030701c2a90036000a0000150351154125002903681140c0d12069000803907040340840d5500d0b1074003ca983d4250001c0100070008a0801c1c0c05c109500301c42202010301d5401c001140041c0c90900a861280c120307803450541052802c040c00c01034907810460080c10011040446513038003650b00b43c0a400013a01040161210030848031b080c03900340c11100c003030400c2c400441e00d5410300c10250014407012090354001d1100c1a5034681c2403030301d14801e0051491640007514241c800c00840d0701e24a00d0528040b000340383c60090005c42c1c0903004421a0141d0381c800164041255610340d40d00020000c20002e10214550741c03460310781943d1036440340248800c11a4550420840034410303045001045d4112045e04c5841d43d5a44003079113416241e09000c0480c0119030009904c2c1d002d400d400390f06220458 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 950484712 1250 950483462 950483473
    0x5030a0e011104140109031e060509011404080c010b0a030b01080c0f241309060303081303120b0d0b0108010b04060920030709030609110112020711061b0303090102030621 75
    0x80880c025010f1110305450401c4140000000803996032068044036800040d540e08c4a00b4036414000144e4000416040782a13040c18101440240303c0603025510942240c092501d90a4816016001d010b000b169680e0140b000c000100c280140827400d01d040303907445400c0329212445a03040c04403000c1c08c1f4140c2c590054a0700c960700c0041500c0d88400c22110740208070f01d4a843c1c8038105920001100da00b0000710b00da5655401e104050f0040c285a41010250000c88003030f41255400030041c4000642c0091200c1d11200d0034001a280e850b03202040e264404140c0c8190b45c0c6901c0318074001c04000034041c2c8a5030034000d00040030282445080c48018007005a5030783d200d1034074074100c05a840500701318204100c100c000004280c4500c240d070000c42c1315100700f69225121000041c0051030782c1040c08041c034810064100060f8511240c0390b5101010782d10300751140341c50100d070007502e42c9005000c5c0c0280000003c1005d10a410360055104090440c0e0700204004540c180b0101407103809001c40d0f865224 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 950485962 1250 950484712 950484719
    0x8090c0a090c030f02030903180303032509030b070e030706050c060c0310210302100b180a020c011404120503040507140f10050307080108160b0c030d090305030a0e011104 75
    0x40d500010404045403d011483c00c489071030740300c101c4c0d000700e80030782c01c41d08045071480300606207080324414940200c0085042d0700340340042c0360280c248203404504694190654412160003071840600a40d00312811394801d05c0d1410014100d95100c0704420b219015400f030214500b0701400683d50b94107501c00050001d90b0f240001c2214075031000e06103212a002268000502121102c040028001d140c00e49403010451840c02038904003002403120403450405640f00d0071616100041d40c26400c29600000150b1202c1468100038450310300384501550a2038001644005c11002e040d00461052460132104440300c0811607160200b500d000b0442e8012450820113102d15050405000304018030702c099481d899800250841303050429640410000700400a80541212000340103016440c06410201e0b2021060078000c1c085001e4106e001001280c10b100d141400c105561031a140c41d08208901842814007918a40040314110041da040c01c011802140042c06003821101d03500b070009090504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 950487212 1250 950485962 950485979
    0x1d01050c070b041103071e08010b06160f21020f0a110d080c070f210302030d0f0b0405091f020a0e0f01210e0c01180330020d08090c0a 59
    0x30040c00544e0a01c4050858104c907580a200180081200c0c1003d006c401d903880140c500b40303049617484940303240d250404041090f10b43e001220103008800c0c0001d207410440349400780c40e10940346000303000e00c3c42240c07a0b2103104091030150454014150211041400c2615440d07642e40e00d0f50350002c10480c084000c4130718a04110071411032162003840e0281c186820007900d28a0b00a5541c006400401462010030000c90014420044210740112015208056890207940d0388104c000001e42c55030344282c60b00c41c401c11035016074640c001c001c006000300c1c2065400196146600483c000c1d0f81020b40c0c000c6c2040e10550710851340e4001240e00c2c0c498025a1400130849044c0c0891070413410700c102c2038503450340210140d51801c0710161280000802954a061803450f00105500b070b00d040c0500074072920300758a80d08400c041103e5010b6881d51624480c3c50b42d0f800d41c600f1843c60f078119811401c2c6c802103c2074020450f4a05c84c0d030140c0c2c890344140d8521310b11540d9030401d08565a00210044400d000c0b0b0803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 950488462 1250 950487212 950487233
    0x18110712020f0a0b0414060f160918020a200606090c0f0721050403030e0f010309050a060c18050f01030b03190b0609011a1c060b04091d01050c07 64
    0x200394019140c514030103000070303400c14841c1c0204494070520001000100f040b03844545101e00035213030040209140802c01c1e000c43c00b0000c0c054441403900b00300e0a095261040b00c07020302500d10609801400c0520000e507a01039001014080003282e20a00c0d04185802508417044c3c52016500003400d00707071501d50500100100140850344240410070a00c007449000700010084a4850000341b410000690780601d0200700c411043c50270070034200310406c0401c1d07009078852134100c412902c00001406d540c0040c0e00414074413100a029020300b900e5101071200315071140024044646425550b4108416210042c80c004c1c0200e81d40841c01840381c204c654800c1d032000c114020301500b00c1d0780b818058004205100c1010784215110b01c044001c010f4281080704555004200c4040120030002c8821b140000b203006902030403014009010115020b42c0d815000f0350001c103e8000000d07074442e15448200e000d01a0401e42e0340d08045401005c0300d0b110030506c10740e031188050044081c1091503550302c0f0b94280 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 950489712 1250 950488462 950488493
    0x509010c0308100b0c03030603010606181e05270601030b130203100b13060201110c0c1306090606030501080c09090d0309050f120702010f0e0306040b07050c070f181107 74
    0x100840c01002c030300c4840b040020400c05849170b00031622440e0110425003500d040d5000241080001c00c01c1850b00e800c1c2840fa601644e500c2541c1208031000c20403421150251540b00c9903103c88c1100f40503025201c6800d01003005100240041050b40d202c0c001075003900d0403582c0b010341002c81c510901d60343e8181a40a50b0f08a10000b0002d4070040d0785240340703e01c82e01b120018140e040c0d010181040359a409109545032998030651080c01e10210040080d1541c95a50050703005c0c2542e500851072410483c1c6c48400030b071800b200c00308012921440010f0050400b4091054a8824044001c0080c0b43c203484c0e507440f42c01c943c030080004038071042003100500080c600440d014441e4401080d0340360014020700c02c0c44000300c40000d8131030f1000d00004010000f041d031610b09001d6049001800c649010903074aa10a41010758051340c1d4a5100b01200c191141c1003000309940146c45020400c20904802c06048582a0f40d05001c0c001881e4862404c50b140c000451818070707010006240050004c00d01403220 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 950490962 1250 950489712 950489731
    0x303050903070c14041404120804053d090506060f04021201030605060406051503010b1803011d070f06020a0215040b03130204050a06060c260a09080c010509010c0308 73
    0x1855003c1c2e580c5800e189494019200300c40d8200031240003424180b24040801d5005100103060381459210750619050000c905410804004006802c5c80313010040480380a0025100890000151080c5c11180065241e840301e9420b900075070900c4840c80f0b0082c0240d003034110f00507014640740d45041203064001d451103550001d409200a18041c685454080d008500800d000f1440c2e20703100d4200400c44000b0f421041c801c440c240e03140031402ca1031401340c2e41515082e400d8a544c030031800101d00070006e1441c81c01581517007422040c128002c1c8041a000e001501001110312482e102c800381d80b1000b1740fa018140060b4014484c3c440035180c5030360b1a44a1105403c156440d080e21030807078521030b91086032000d1241581c0c948910840c00d0510070582d00400d401c41c1000080d0800c030340103000144403000a800305002c03541030503810829650f80c50300d91078a1724150b991803420007405400b26140f0312560322903020b090019285540941c0440c1c4003000c0c140e607039255234025035a09580c3c0e0304020b00320256 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 950492212 1250 950490962 950490967
    0x150f0f04150f140a180605071206080a0201021e250f0b031b0a0f0804060f0e010c021612081b061e1005011b08071208061c0507030303050903 62
    0x52403811071040b010030070445000031034201203000501241c00c40c0904042081440d1440b0400c21840103000160410b40c031020118154071400f00466000e09191340044000d494280009140c400020309140014801c3c0c099440300001c1e881c408a00016001442103141c02c05403080c284170303110889808859070b0303803a4000059a19165005c51003d16a0400c40703011000105000900700058a005007142e00c10b840b503440d240e00c44100901411043c0c01c4d03441400350040102e0100000c64000d003080030f0322401e0401040300c49a401034068903404101c440540101808401000500c40d0f4400075940b12004200c00403395549150701d070f5003c120024051110b16a2080c05124148400740c0140300c41c1c0d0010707a22a10b02005581c0d01c84000c0c00401c06105000010017070b60b600404146a90144e0200500d9042412f04280c0c5003441400c20041011ba0700a08100b0b00d1600a01e034580203440076500e4030420f076505440010707403406210300a04070394850002040040d00c26044584e1087e00841601d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 950493462 1250 950492212 950492243
    0x603030f0724050108061303020304060807030e010903051e0c0628090c05010932030106180f0b03030309331603050603011a060703022508150f0f04 65
    0x1c0e002d598444861140340c440c001040110010000300d90410000d5250030484185590040e54074442c5205803c103000400000603011030181d400240d2021107000240031044c900d00d4014519402108500700c402a900c14a4081040400c00c1d0f5803103080d508002c010944600c010342440744079480c48080c03001c0038101043c035031034483d000c0e10092034400e4010001c528182400501303031080d2034021040c014820794010b0111103c02040070580343c82500314581e84074844020a0252001d41c103c0b2400e400c80c4244c03004224050f9110300c440e0056135000704080c440a8042545038403003036505000303a9101d1a100b00c4907000610074118414421020928420207040b600040264115040030303203c000c4c0720402c6552509401065030258040340200007564540c040d4100741c1c1054280c0c1070082c80c01150181c1094001c00104c42400203200703c09429040101c0c1320f02500742d4601508069021310018450a0f0000f091858028159490500516900e14692071a130350801041901c20414403110310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 950494712 1250 950493462 950493503
    0x5090402041a120303190e0c220c050301090c050a050304080903010b0d1407060f0203072019090f0903081f05060f070c120201053f0613050603030f07 66
    0x91000c0f03600304040c507103c0c50100703445074000700b6100f188040c01d41810080310038410041540b01401c0400c507000c02e402082e460f5080d940c40900c0c5a110349407450700e030240d04404d400c00050b42c102c0c0c0301e0700310a202031b6141c07d40848090050740040004203038180041743000141c001000e0501d1186c0940002400b80d03512001442001d4101c1d015a41544048c9504102500a008080103403000703050000140c07405d090f00a60701d02c607070400a130204000750710b9108801c85807001c0c04000440103201000ca00d5208444245581e054070071580c005143c04682c40303a0b45903a01450045a4060300c1c0c0c4241551581c00060382490010a8200e440400e5200890165100d0024200c0640c80611b09510388640b480c00c11001d5030190010820010072801c003800603a400000c840100300c0105622450203507119861143e045011030700c2d02080e0341025016640381c141440a485050204c441041d41401580304070215401961525010342007000016000c840c40c0c4010302150740320f681e540d1442605c400c4030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 950495962 1250 950494712 950494729
    0x210c0102030c0d0e0708120c0115060509030f07060c060b010c021005041a03040b0403030e210d050a09020307090b1810050906060c280f11030f0705090402041a 70
    0x84020012844600070a054440c1318031400d218802014800d08150059940745a40007240001c868005014001c0030300c03c1d0418000c1204401045e07507019101c0c1006805030f008141c40368001c0c420402e1404000d40700050030800c444c01500c0d100310360f1800d5192140500944030740c55040c0120401d00a0051f158685a4000d856440d6900da0310b407070611381042c840da09002e102c0007016034140203000104040e00001071f0850b0341428000781d003840f84803251341072101c40b48400c60403501c075821825110303600f40010058504a0802007005650750203042c0b088372001c0b20041d4259020a10074001c1701101d0b4420710354144010050003c05010300404d40200c0310440d0340512450500004010f00d04004039074607040300c400c82c0c0c02c908000034503980507640c10000252040680464810300707114004488000c0b485a0002001400b141040c200490f15000360204640644200c50310110b480c840403c5200680380001c00c207980703c1e1102d8007000040c10345d4914440f504a40355180004070f81c0ca8411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 950497212 1250 950495962 950495971
    0x90a03080c071a18130605100f0314070215070201110f0c01050a0902131a060a02030912030306010c11030c0303040608010303020c1804020d0f05071205060a020c210c010203 76
    0xc00c0403608081440f040f100124028404044090014101d0390450780c04502000b0400c0e0b40b0406a0a008a21003015090350360140717400200e01c404121a203540311081e24200030880d04c050012161084040d41502c401304c40b03050040c3c209075400070800200641481c1c0124013440085814185007903030540c1c1d41d01c00c1462030484c01c030008140625000c02c0c05801e501540c102ca04202e00c1149401181c0d54061801d80d50084d15512a50048404862044000d10080c017405849e11f071100e202c1d02958aa02482c0b4091181041012194402c200041200d10030b82060b0759200000c8400d0780d8140340c0074110503840354140101107860300107403010005000240302075518103aa6500d18100a4201080da0f440113025200d0007248501c111081e40900340c01640c1034810f480848680e0411580c2e07402e800100804500030200002807140c0d600f00e11283c0c05010700c040e101c507502c034045040c08070b00c58483c1003281034000030705184181030300c05962102200c48100051900107425407080c22a84106c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 950498462 1250 950497212 950497237
    0x3020904080a2a0507170a12020f1506040b0d03050a1d0d03031e0e070303050901020a060f02033106090c18020307110f250306091109130f0305090a0308 67
    0x2000341d814000d013008200d0013441c8101c82c2e01b81d00c1c0c00c0c1000310303910741c094000b0140820400300c65145410f842003140b0704200c450740c0c00f964102c0c0c0141d80600b1888909a6a4074882d50803c00042001e2808101d0f40072841d0745a100c6c0c40c5000a10441541c1030031140031660449000805078120503100d00c0c580d0401180719540005550b100d01100e24009003c807591004884c6c0b07403064080d04240001030500a503a0035041c080d40750504100100e00d8040380d50340041c000e900701155100500e220390090340c0540600d0f28803001c0401010201c0301c94002c0c1038003a400703808000c0058008695158014545140681151344289403660340581241d03101c8904103402980c00010030480c00d034008a1079035440106405441c21901c940581d55841c801e0030211100c0c04480001702e00810415080c2c81c005640c0050140001c542500f071180f0848045046980100c515100140d00b0f89048114510b08035400343c2c5c00300b01c00005440c1214581c000034080c0c2d030040c04c000000701c00305403840f01a02c0c1111690 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 950499712 1250 950498462 950498537
    0x91005150a091505041211100f0e1009030f02030a051f0506090103020108040308150406030501060e01051c030c050a3002032713060b1b0703020904080a 67
    0x107000003480c0700c64a40c09481000440d41041c80c1c202c0c2e0200449007150989581ea611224081c1400c07101d401000354200e5004043c4c102d041600c40d002202201080e081d5129030100848040612035030142001942002a002e04821b0000564058080a00c64005400c60701040150b90750103141c000006c044500b230301d4081c800c2c0c202c81c541500035150701c0071058490407803551456002900380751014000809001e10301d40020b0708210300701044850904002d00c1407194999908245009054500076800c1c1608a800042082e04007400d5100544c000406060140d03525520129903070700c4102801c0301c680c0220100c0401103118611903040800368840b0001e414070600c01c032400300701c010044880c1950414400e502025aa14140b29010006907a9105a0840000025800c6a495030030150324518180c40420f00083c510b01400c2e80c144a03004100c003a80c010340b6156640d541601c00294007205071000100007a028070007525015000781030803040005080c2c10300000c081c0d440d11004d10a51030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 950500962 1250 950499712 950499727
    0xc13110703080a184b0c0b03061f0905092403120a0f141809070201090803060f0f03010f0f110903060411030f0f0d090801140609100515 60
    0x140c844d4002c0302c030311940d14002c040a00c1c0d4999031550b00c09890500300b030756204e03040341c2c222a0103440e06410f1030361040f82008401c1903c40050f06044c10510544034003107001008603880d04032808590042c0d40c01400f8201d1162182c0d072001500202d45414030812120035000580c41e1280d20307200340180d01845802171401101c0300b00414944884442ea48030341e010034411918005140c0448854000a180056144e0007042c41515102018400008030b11000a03000c41c40702500c074480348a0079804c945e24889520b54010803400d1304c01144014060741c100b08080f651a00c1c1c00b020700c1400c0138015000c4980f002982000900319965000b0094079036440b440c1c440b214524502c901d403881e0600140d00f9083c4a05100825500e1400030401072403045102d002c151195010407484082c0d60b9040c085440e41d152000b602500d5600031a40000407400d0901c000c03420071410300034580100c2000b50840299550102001141c0030050300c02c9001c011a0040800d040c1c8519140790101d0044801c90f0703540b05203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 950502212 1250 950500962 950500981
    0xb03100e06031f0b0409051005010e090d02150601090503010e0f0601210204050a020903072705010b120a0e1b090c030118091e0f020307090b030c1311070308 69
    0x400402191294102072068903c4000248400400c10a410700004038412101c012030010560707020050300c3c600c244070800b100c840203904410306983c181142d0007001d44424016a0b580c00c40e0a6100000d0b03001441e400b100c2c260f00c940c90036404001403400c0b00642c0c3ea01c4000c071313003102d003940070205060b0014024050450801c000a500600720480d98030041c403502d03000f26800c90403061b0007c0c421601c40c0d010601c154807a80544905900080540d04000e40c0d0704ca03070940310451201004500c041ca0b5080c6940e003101d070b102d03030350480301d40c0c800440c54035060400b0b010115030001c00c403001655481360400003010040003225081e00c040402d085120300641c0c02c000803038800401c100d08002c002c000500c58130300c103201c9249400c4a0301c071020540701032a14000ea031105000c0d900c0f0b4410400c1c42d50910612103000b4500003041d009409580501d5201c0003540181d40b19000b40640641c0300040140302400c02c0c860341113070041c4501001454500c03142d0303824042d6010f10400c1d40010415018000e4015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 950503462 1250 950502212 950502239
    0x1061d0709061107180917070606060203160201030e150a02040905150d080a031107030c1b1511030f0c06041505010303080f0c09040504081b060903070215040b0310 72
    0x56042c030030002031410394415581c06045c014003050205170000c030129050300e41c010500e01540640c2d03085030040a40300d04c0d00300f0f03040054180c7d0101d04122001440c280040100c4000041a41902c9441540c0d41c0064029014030080d071040c5100301c06004481c01030801c03d45009540d141c1000d0f1703a4600c1e1140700300a0380c101404580c502c00c2002003841e0383da550781b03425030a895402916180c8505a01d04140c00901c0101c2c204400064006600810542c2c01022903000c0e51241c05e002110561104640310300030114052401641070460400102c0b9002d240c0d6a200c030200c101c226440c0076400d6002c40819005003078016216070110b0103001c01c01c00c0d4402c11001604441c0d0003046198550380b00180850301c044c140146a0303c16601040700c001100c02264142e00700908140094202450701c601154400b501c2c2c0c1060407021081845041c030082241d90088104000860a01919800b088004c4010009501007941c08100000b000c001c1140554450f940030065407200364035004480440300c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 950504712 1250 950503462 950503469
    0x170a0c0314060a2d080c0406120203060703020922050601090e0709090b0d021c061a090406051003020909210c0d030c031e1d07120602090301061d0709 66
    0x766958010840c5540f41c4000d40e404842040c0240e6a80307010705000c14000383c100380c1d0340801d9000d80c00c4010401c0c0e07030005240313040040207403010002d559881341c1800001f02c1d1540001e5044d0800b0001c80c0e401803190700901000000204106010140200c040a1180c1d24003d4035000c0d0742c03110108080c130340c1c000c0d140100030030406c04840a10314102c6002000c0710210b0080440130390359245407a40e40d484100c5140542503015210780c0f203404156003054903102e06010b04480c03003401c190101c1222409070400f00303003054000e4105d06007a1115610b10000d8034008201115070122000008050394518030b82500914a2601509007c0e040c0001c0c940e030345400107030031860700b0410000140105400104100c481c1440d01c4e0005169420100c21806045111001403c0c0b000720b8002c2e0840070425030111151091580c078007460072003c400348588951140c444d02032100708943d8054086110f540040a5001000300005105a2034903160030315000b8040c181510750211340c04110180b0381011404014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 950505962 1250 950504712 950504741
    0x70f080c0f10051b0c060d0212071407080f45090609040c09020d06050310050601140d0e0304260c0a050d110a08031e0a090510170a0c03 60
    0x5120384074001030071600c14032900c4003410012103a18494004c0c20b015003611000000e204c50395072145800c0300000394001c10021441608050045510140100c0d10445156000c0c7c032141e0406ea01030310703200300707075003112588042c00c240030444144001c2006045004402048101c4056010081c0c084031403002c0c00d400507482c200c040c900c03400c5c1c15600d1400440d8052400c0300e040003140d0700e40c0b820380c0c0c0c0c00410340d100048444c000308140c0810852508544165402901220039404c0900d60003401d540d01519142c1c0414004988601040a51001806540303440070000c034407003c500280d9481c546c4540c0c407500380b4044188104403a00d0030218902c2410038138000414a005401700000c0b0034000c540f2407980308000c4022501c081220700348201046040c000d1101404955071020f154881c0d1143d600c1000c0000013024041c0c0c0a05e412003034072201e040300d0381c400e4a554100402e020036401d4131054402401101e001c0d904000301101195881031101d8840410b01141c072510107002e4645020f4000e44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 950507212 1250 950505962 950505979
    0x20912240906011401050c060405011a04050f010915030f0b040c140f0609041d0a03031b0c020112021603030b031603030e21030d0203040c050618040e070f080c0f 71
    0x1c005000103159041d15240c240030f200e00098400180d41c0c912803c84c0c5544940295030030801848010740c070001003880c48181d406031128096040000700e40c8100c4803400000f6001c070051003450099484001c807580d8641041800c50303283d46548428404446040315070420080c100410484e0550403000240213042200d854406e9500001d50000050544103006604c003040300e030110740e10b5400c841c010441c1c0043c071508040c07440382a01c1d1601514542039000c6070800c60040d00214a148280010040b659224943e100d80c5d5401100c140303403180f2076010015000e0102d0003c00400601d1390700401c1c841d40f03001400b014103009140c02e000c80700074030038101c04d07841c2c40801c007007074201c003145130f07020800c8400c8660b80100a032001400401d460f49261b0900c0080b520028154080d40198012801403c1000c001903072030702040790920400c20540c144104c0051105000c0c20580c000603241c955000036901d409844180b0800500042c3e80131954a0380038803490f0889003031060319400903036025600701d403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 950508462 1250 950507212 950507221
    0x9020c070f050d022b05030915190503070c08030708090f061b030a060e0103050a0303150b0904230c0a030f06120219080604110f0108091f02091224 65
    0x41038070b03444480207400380381000043c003060800307203002da10301700ea10001200e02130b560790a0050b0380307401800815003c0c100868881c04020f01c4401074641c500030b10241409140c0741c03004201d84540028103140140141e0224441c00a80e8035005548101c0c0d042e070b200c4c05145425000d05103071106000038500b054110070280881c0200000e20246030b0014012510b68075201c0101da070000f000594403030740c00c0e13404400020081203008a034180c1000c0c0203560a02400710070240354041d000051190200240007002480c5241c2041c0c3c22114900313480281040b290b24400c1c0211841d808129904a88403400050f00c421054241c4280d002816940b2130400c4a039041c00c0d80c1041c1e8030090940a441000340d002c8a49402d120910402d010780192400d85d21582007520b000e0007181c065a001c60f1103040d00c1440d214040d4844c14400748203404603001400b86912081a0390b2003400000c00e03081000d038007005040d03481d44810600c0e040038140c1d0001001c19104118010610a000860071040765048000b8803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 950509712 1250 950508462 950508469
    0x3070b0403180609090c0203070506090a170a0804030e0f0d0302030c010606050c0304091806110318010b010e100903081c050c041406031018050105091e01140a0e0109020c070f05 78
    0xa130640312501d03000a001c0c80030000a80c518055044020424429042040110300000c02c5001d450b601c40d500c003025614031464800380501400c1030502c0020708080000780400c0c819484850308840c003400b00d1042501e001e001c241c00240311a4103034003580c00041d103002d2242091140400601c1189030007400c1004105015032640b14920420f64680c1c0c40310649a059039200001648456001a04000c240d8140a040030300303800c2210140b04800d04900043c4a480f0107014000403940305a4919244e40c0c020800c204103924403240d50002c002e00f074540800014100d400904001445028454840705176165440030b58030020300020414030306000810101c1c140700c40d888100201211103580701d03030f100300c2c8507003a80105030300c610b04c0300d00d055031402d01070800c80d03122074140e1300190303040e010b035a445011001e400c1c05200d060781d00001207100100060003040300e0104130705500400403c5400d903030f031300d0b4050180004e030041410703517a0000e0400740c00c2504008500c000c1100c194090410b07880d14001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 950510962 1250 950509712 950509727
    0x90f14010605211f061e1d1306050a020927070c0305070807082502010806092211180906060a03020d11030f0f150a020310230303070b04031806 63
    0x414200e00c0d148130980d0f036565001c0e04001c018003095988440c1e240c001001d0025495260721a00c108228480c100b01c1c5400c2d2042c00e664810b01614138002c0e4440b010740e841400070300e0010160b0400d0343d4240485901c99440210086020307140810b145a034451400100841a4020b040d50050164203107106000913000000c0e0f444640d0440b09040d115001802c080d2158400c2c407040d004ca404c0380e5150100a4580f0758509070842c1e000303a80394060f6030b503084244071030f003801500c50b80c00d60035400c0b0600c1c580500c42c8103414041c0307200b9400e5031200c07255200800c0901d8000e101c1101d400c0180760810155980802c8100e6010000301e07401d04400b072540d00860f00000c840c40340540000d030006130003030860f00c040003000300d1742c040715044460b42031290155580340c1c010b100705d0343c403d010144c0c08a001c03d81c0c00d00070b882c0540c0d00d0300321820900303103001907034401c40802c07040c080c1003801050500d1500d5074003400a0201603029112810346450286401400201e5410f0405c000b110010b0b401d0200d154042c40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 950512212 1250 950510962 950510983
    0x3030d1e050402010806090a0b0307030f0506151c060209041503050f150a02071e081b0318010c150e0601050a0602061303211b0f0203040303050d090f1401060521 71
    0x8a121540d22381009a40c042c2c03c10107101601481415800000c0141003455400c205004006903045a12039000c04030301840e2446032254130400c070801107401c0b1223340900680c094031a140c010702c0c06011f900850309542c110301d04441060403101040050003418410810004480c42c0134042000c0040103a10118601501001c482c5501040d00c204010402c40f4907030309860000800046540d0070b2a10710066030118a00700401c0a003d140b1144140d400000c1c2c444c0d00602c0f9440b141c002c01c8010045452040040c401d8490b00d074032540c2c501442c4043d10134071182c140041c015180310341c14001400040c18055002d03008540c0700c1010080d400c0c1e226007000000036854500840361140fa0724101200909621580d4011842c2499907400074982c5e070b0404503156141d4442d08020204150240d8990280b44005008508104500b610043e419072214600d03d00c07030358035150302c07a0302900d8078005100e9103a101c4030303143e54842040c0240e10300700c0c0e405090302100300b80c03103015507426020442d100c502490 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 950513462 1250 950512212 950512219
    0x80705030607120207152d0908070807052503060b010507030c1b260c0a06080106210c080906010504060803070b3c060a061b0203010b03030d1e050402010806 69
    0x140700e80c00c000d86c81009851801d06d0100a0020740c801400342c04804176400c1c40c011040b034624041e07211148060246040d0107400c00105818690a900ea81c07220350702000044666002c0c3c1002c0a10b0380d2f410740d4114902c1c0811103910340341e190451411030102d500d910801d40c1802021311040d00000d501c03070b00c1d00514592244a9080300781c0300c000808070742031031908040040c03420324071014103800d20b0029100c0c0e6500c1d8a0200c50820148406001c0c1610480c012200040c1b1108010320510380280103030034440107401d6042c00100c030051002c504071159242c4150010344200305000d000c080400955000d072800300c404001c95440d2035400b6175030380714000700106900c2003207001409a40d87c401c980c102d00310086560310203100d241e108031840b8450074001450503844400c00b10b07004e41402d000c0c94044c4c0381c0b00c2e11580c404919641820303100c0601da240403070f07040d07407640d42d0362619450a0002e03001d10789004034042030203201a42c4d0039903440f00984040280783d10b48010440035031b0f800001c00c1c3d00802e00780e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 950514712 1250 950513462 950513467
    0xf05130b0a03061107061503081b070308040603020a171012030c0213050610020633180601030c0318060902060f030405070e0708060a06081e0a060807050306071202 72
    0x401e00c1004698000b07002a0b00d44482a1504440b11000304a45403003010300300560340c1902215101c0303c21b54000500303c0002030000516001142c19904058610442141d181e10b54940c0e6903a1264010703002200001e40204040c43c04a4104050304411030b2654200005490310400c106a89105845a8240700030f0000020307003032500a1410071103140c1c000e00350882c4440d4200b052030180c03605480c400c0c00340340c0d0600e40900e42c80c804144c240c003c0c00004c540e800f55100c00045000c08c0c42c2c113456480404041389008a00e0366581c00d40e003d810b1490500040c02502d4210005000c980c1c41e040523805241c181010540e00200040043c03009907488400040c03552803a001181d401c2c0640320340c0d1004282c00006100511000250050841d50140351624031555403841c12941d07490306032007081d080912070b0010b000d6140030301581c661020341189405080e11004500884000c42070f40c01d015281e5031203009101a01e003c0c40740034050401a030040200341031a800043c0310019048681c161603a02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 950515962 1250 950514712 950514731
    0x80609040209340219110906120609010e01050709030c29070807151a04050a0b100e03060610121a09041b050f0f01050705030c0d08040605010f0513 65
    0x182e441012a24040186041c0101001115088800b800310f4a900140c07013081201d5114420b000752094506a00401481200020344140010140d002d030245501c0000c800310240d40c40342c100007091041c40c00f84008124040198070395801c4030000741c9000304212050314248042150f4144440856004051921201d003580108944040d80c60315681c805440008022080c8503041c8054401e081c05040c02003a844601d4510000721050030760060300d0592001040b41072458642c0c0801c1e40551607890110f0054a00b60010380c01034000305650300858241e07051707040d00e42810058070341c1c00342c41590104000c440a04010f07210b840e01e41d01620903070340c456003902d10b0601c3c24217040d14500c0002d400003509050914040a0009504602050300e680214002400f8136100d500941c204002502c580051580e0311300448140d4442c40041d0380d01e100c20000f507901c02d5010058103944895a42d1002c0713203030806180880a40d081a4006482d8588011060141da961111400100000b01000052101d203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 950517212 1250 950515962 950515981
    0x60f060c08071b03050610080604031407060b0a1512050f0609090a060609020405030d021609020906070f030503091204052214010b0426060a020304021206070e10080609040209 77
    0x540310f110204062420720000821000095142c0a80344c0004402641c94540021603541d000484000e40010441071107800c241001e000140030ba14058480071440f00c0100740031602da00034035401b03102e1250303e446841074200d50041c4080d004140c840000d11103030802c500312404030603024207020b04c2550580085030b60309608208480189a00002c10b01425564044a8000350040d00c40c4d940070f80120700120410304e1000c50720341d41c60583c901d41101030b0750616040f60001e42045e01e19580140c000c01c09030012440343c11f00038100c2171113a50741070b549103402d51a860801d1310f0655010480b000610041c07040b6a101001283c2c0c2c00b40c1078a11912a5802900d05400f400580c0546201e8141d10340c000704000703120700000d1050b00e4001070030300190769842404c407820212001c0c0b03c3d02c2c00d400030804528410b03065002117400500040048981002409950341407280c240c6844001c116955401240e50400307200c001c062107040c1c01c0805845c600100032540311040104028410203c54000400410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 950518462 1250 950517212 950517233
    0x81b1c0809130f0906050f090a0b070c1b0f050d1203200c0a050609030406090e0405010605060a09030606050d1a061c0c0f090623041b08040204060f060c0807 69
    0x8a8618050184610102d030100c010407134144240d0321207007000300041c50701e201300300034034001c1c40e00303074010040e10240c1d484d44448250040c3c10b58040003080c840300c0c0301003501480c04020301503109c0e90400c10640791161044005425504c418094600d411055011031110789002940f9045030502045544003d0074140301d485400c1001000382001207204000b00070300180036400144a0404c96055440b40c01c003642c0c0d0b0340503a00c540f90000d41c200e0b800740940814008480d0b0003501c02c04c008520940c8880025449400c1072410400290f90054100144010f1313001d12002071500b030f6801543c1070700c00e4403040c20700e54074001102d21074808203010803034548904e280c61056411504a410400c080d0b07103014880c015040c85446400b52900c4c0740440d8000c50791145108440c81c0e84201c1c5a00e40a14002020301180c5101181e40719546841d002040da800580212056240d903803036002e079252501c1008210391160b08031102050510600707020854204010400c4250024510b40e00e13031036030b4580000140b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 950519712 1250 950518462 950518489
    0xd0203040c090501032603060a1a0403050f030309060723130e0a1a040204122a12030f0c030806130e0a1407060e0303090103020c010b0a081b1c0809 65
    0x80340f400e40000107100e0940c50f04810482054005000b130070582460302440d000c1a50b12551108040320704114800301d0031807684202e01843c0340c450030507940744c481d40c0c24003089142c1c0d5804c03600004100001034409220b402d91000460034400350016228041010703902d1074041007070340c0c54400244602c59103c09405880148102450070300c9a2a200301000090105068400503004e84200682080e103030500a81d010740b00680b118548400c107a03126541c080404e841c04400d040c8444100320341105800c005070b0064040d9070039600601c07a41c1d250040040304000e00b48010842c006451000280e84000501e401880458101401c0c0061180e104000d101038004268a481340361310740810440e50070000b4000446403c01d940d82a41e4401c01600d8005c0e6444030b544d419041040507201640c060b40c082e1002c2c451100002032001d1003e004107080720101c0d0007904469010301c510146940810303141c40000101696400b420308404c1c20f07200040c0c14039a00c001c10608011914050341c1c0c6807244a070044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 950520962 1250 950519712 950519729
    0x9010e0a060b10091202010302070f06090b0f06270702030d0f05010f080714010c110904030210051605040b0d11040303170109110a0e04060b070b0126030d0203040c 72
    0x40c1030140340c4440184094581036010300e0160381d5046a090040d80b41c24201c0701c2500000c2410222940110000c1d44040f1b421940c5c8040401d059011031400c3c80341c0e41c000c912035034400703845080020096540701130051400c0d1013815910a000c003031440098854500160080f6140c2054a82503016400c60044802c01d0160a26141440c480214217402c00da040300c40030640d0410440d01e889599440388041c0c0285c1e6404c1c90b000600000e80d500c0b0b80b42098207903026400214110b40c3c10400502c04640a48043e40160301003451144800024460140c2200010131401d00c1d80002d51009802401584900300e603500004c540b900c00b05005410180a042d02c840101e1340e1240c0724a006024000c4801c6401100708503071001141c0320903a403048441c601d11001e451810200906c1c0103e032404691504540c015840d500001102410301000d0710035503102da1907000b199030407c18852421706000050000205848818410100340030007203950303a51000b03c015a0301c3c0c0d83c1e403c02e030146070840d0780131041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 950522212 1250 950520962 950520973
    0xa20030d0f060e0105042a12020307121d1506040e011b090506090a03080904090c0b0903150c0a080a1b1e030908030105060702240306030d0507031709010e 68
    0x71048254000d0040e1200181c0064282e40c94209100850f040c030b0b04030303800706040418801c62503003010708580030400c1175251401116620f003150b041660000d480e18004651b0141c03001c0c00802c418041e00e05149161a0955005007180e0310081e500c0740c01a19271000a021300b00402c3d03043d110342e008000f042ca48e08000780800305014075800c0b680490b01c054600002c420b2000801e040c40c11300101c03110044010644180c0e5821a1202030050340402c0c0c3d1a54480e948002600c001030340c881e030034001050700440702030702c8000c14421700d03080404400340680390211000410080c18110001c1e9044603100f81313004a480d503900c07900b0200804140c1a991700d0b0072008600d055003507a100c02202c00c1016400385800545458400640a8480e003a07001001800144014442828901e02401c10070740010401c141100c03030b000c0751000788011200809043d0400004016023401d040104003403094040c64168175000d081d4500510440b074442d400200d4003142e81c00b2900202007504180d01c0e9541b0f09043d40da = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 950523462 1250 950522212 950522231
    0xd0506130b09060c030c0309030d0f02220f120302030c01051923010b0c1204031110020a0506063a0302071202011e1814090a020a20030d 60
    0x4040c0e02003031044401c0319100000645402000c510f40e80a081d0420200b8255110301d040604980c00c020221141407000344010240146103014007072030141c2c03500340180c0d5006c000030705103100c08014403040040802030000304960503034038410908903100d010b050118100e461804070700b98800c00b448004c0c1c5600f407805202d40e090304482411a00304100508024405021003031020110484801c0f65000c1c1102c0010014244820010710b116141032055600b51248010000318a80180d041a6401141e400780c801250410303079210641d0003024002803455034404d80c1d903595102801400c490096182610511354260b2065482c45000074200501984819400d02c0c0d4580c201801c0d03056005100305a40052560103c81c080803046806940e00740b1811600c04071584640a422079100800100c880c032498404550510000501056040301116401d9042045070144000e4840c40e140b41c8100004920306811100864070055640c0075078500406103140d40d07041d030043c01901e540d12400c0c5000207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 950524712 1250 950523462 950523481
    0x50f04030b0a0c0318170f040803030402030111040503100917040e043003021b1e010c05040f0e151f110d14030a020d1107060506010e0f040b0d0506 65
    0x1602c106801d6070108080091403104a090f03d9001d41904440f8465000c2880840c3c0d066020448655a400702d80d0320b0300c0c40c1d203a8402c0c021b80c0b040d440b848560300080306120841c0b60038040d07050740b0707001442c0040c106818000002d44074294600003400240d5036941c0401003204550002c0c15010f140b01d6400c0c1c4960351211702c2031200d482150115003915010580030700c0300c02010300b40e80080c01d60410042d4000b09200701980250b106043c03035994030350803039542104851f040001404101d2010b0040040102001841d400e60310040d40d00c43c18071a045c0410700c0410072250a031703421203007941ea036180310380c90b40c00908120500d2a20402e070000410f641000500e11f01201d070450b00c0030245d8a000210300645070385500c40d01c1e0700d0480e10000b10201e00c0340201040c0c0502458110080b03020061414080a400c40104e40c10914a0401e2040c00314950301401090b1007400d911074828207140342404000030008842003040041f061081c0da8400d0444071586503100d50364601580107007240c10506244260 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 950525962 1250 950524712 950524733
    0x5030a030905010e090f060d020f0a0b040608100b0a050f0c0d030e071706070f17100311060711010f030f021605240a091110080a0c020309090412050f0403 68
    0xb1240400c15405079900b150a000400c01d02c10750282c17101e003980da00c81c0303804c0180000070300000b80e83c4519414048040f0341e8070602c04038010200d1031980c969071441e00300b018140c1400100502c81d003900e406001c2003601724640031a6000306a2341361255598031942d42c49030181c0151140c00c0c04620a24040404172a00b50b0301040600803000e04850f00300341c4c4d4940b00100c80e400303000071071841e4012002080213a07001c1e00c05104d5801045c1050700c40c034210321000d8450350800b22289081d80c00200300800030300c000d9507035002840e08140d4203d031400700c4544924881240c00c0b003d950400c00d003400303001c1e0410310a81c080c12580c1800c2c0c00035541c0d2000084122203503643c0040560351030062503100388138100320300303025204500c0c0182d0f80d259941c0c0345c2c02e40000070074030044240c030032000040e1030314025944c0c80030b40070050445480e900b490b410300350001002c03103810703110307450035544200501ca4803039032f0348214164040d9000c40203500c000d40c3d10004072243d024000c107440509001003008810403e80a00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 950527212 1250 950525962 950525969
    0x13080a030b010e1e2106161e0206070807090b0f0c0c2706040204090509060a0e0f03182403092112061f020109020a0801050c09061305030a0309 63
    0xb82d544114058800308148038450008120b03000c00f82d4080a01c16041c02640703100d00e500304e05e11240304103040340700c11414000b0403036111016200b00351008081a07084640148404c8d103108403500100030a06000e5030b580300c00360140c1c040c0954100040d40300e0344030307540344005880b6605441d134451080b18260078031500501c802030580d014001c120720741800c00020460254080800b82c0b280d040240100d100304140c00b803c1550865000c10000c00c030a2132a0140d1401407002ca40144090f180000c040000c5560280c00000684c20409042d900c0001c00001d55030307542070350403288881501d10313000900740d10341c50001401000e09a40d403d82d003103104c0e080614410782d0300a040e101c1e01502a02d030000da821030069485003103003040c054252502c6494000f940e02450180050a18443e00b4440d8854200c00c6002200140c0d1034503592000c40c01c5c6040c0b07150041c10014000d0055040985006105003c0c154425003e5000070681039900c4600d24407440c01404003070305407100e00d80784e802c0040c42141d44e4007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 950528462 1250 950527212 950527217
    0x90f120706031103061507080c010614120d0e01030209010e0d0620031b0306040f06090b120a02310c03020d0b031c14091309050f1c0813080a030b01 65
    0x3407610380e402070f80b081240e21900b4014202c000d00703403820500303d0168004000a8605c01300034800c80004040900c20700000d89410380d001d105500281c6e0400c04a0f600400c600c140c40c0e00480c44000342c42d81c0180e40c50711401000d00700540c407003040400490390310780381c1840a03074800c2441c9945014043c240e4072520194012070149410003e01050101c0c440c4800d460141e08500d01008811003d10721002031500003400030404034521200c007507070600703541498010040081d9030341e000c2550361805807031b00140c4c0c40195016018003890354000406011030040d000100c2d0307215100d80a04965070f03060780b44c4541000305041006818a0704018001d400404d2078503001403510040d000b0510300055080349c1d205103a4500c2d181000545c5d411079100428001c0304a09034018480c04495517122102001854050240020341e205135050151402266001c061400d8100c0303002c08540c0400300740c61824684c001d05084400c0e0300c0700b5500501c0300070602406051058041410a0750540c180c10540c1030140c2603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 950529712 1250 950528462 950528471
    0xb130203090c0a14010302070311060405161d042303030c0706050105180a0e030c0316051b0a17120c0d0f02031309090609020423090102030601090b090f12070603 71
    0x403080c000d65038840d0162044e146030404030901c0c198070a80042c8282882490190841018000040d1030000199400c5851760054040c3c410b000f02819440d0000b800c50501030500c500b0144114241c00d50b014202821401480122007801814100c211958180d40001c40b513480c039040c0458201c1d40c2281a00322030351410a0000201072500200b194580080880a1201d03912203184000042480e850391503064042400b252122a100703102408046e41a61540c660508540c0b0b80107040908840c08010070a08150200c85143c807040c0b501000c4c3c0d2030903503200091751540f030358080c90040344c440b11000c007407800940e1060003800802d0303180319440991108030318400d0303012040e600e030300608040050480c0441d0042003242229045040b1840c001d15001600c4142500400c0c2550b801d6480c0034045801c440314000034103c445101d40d0f020312010021425820070300002440d040d40e511904c8a200d40201d400030701c40d40c804800f207044074001000c4507402006090034545844061003510702003441c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 950530962 1250 950529712 950529733
    0x60c040e0f010b0a030e01060506030702010603141209060c030f0409060302010206090c0108061020010204081c09050d1109010e06190f03140f031c0b0d050c04050a0b13020309 77
    0xe01e034498140c2d203050500c50304000380b6200880007482d0381d940202c41c42d03480f2900042d2584400d00158060101e07a400403e0303147c11070a00038445c94204038004581c1d407100001b10703401c0080300c0c1036803107004003142d04aa54420361075090b883c60080c018071020301c1c2000100061100032031b5111030200e034402e8080c0c52584d55a29065510341d1085062140400c10b8080024100d1410018140700d6a03801d040100341c0810036a80c0c0e0280c240d005400b40c0b400d031741c0000c00f40000c81c020072546012760304094240032845090b5000501d50321303007842111300074200c605881007000000484c1c0130b01c0c0c110140c0026180d45e0343d20305426502030f0560701d00b40680402140c00b0070408400e442d00c8243d030b490900b9182d580c1c0c55541d034408a000c01c0c000c0c0400c80d0082d90742c08040d0503810b10082c001141400f00316007504414141da8001c0340c10390b00200d4400c038908140c00380000c802250800c100e450441d0006141d5892034007032806895034215041e40146040703c0c602481405038051800750b07174504120364002c0344 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 950532212 1250 950530962 950530981
    0x6050907020114041e0803040b01030204110c030403080f0403060906090b0109060b0f07060e06070327030813080c191703071d0402071e0b07080115031d060c040e 71
    0x42a403881c6001420380001501003481e46030305c030f0224208401c0e03a02c804242c40c1c0316110f2a820540d822991081c0b0807004101313503d014014101015400c81601e480c0001106440c4d81d24880d600c0003c0c004640416603400709261007040d1401540c1001041c86460058a0b11100034204038208907107845000c2d0007c03070b507584648940030603138403440a540d2801c04920324000460b040088215200d40c0c407103940d56440c60302805200d000780040e441c0444c00191038120b40d80400c202482210640300020280c43c04254440308554002514609640102143c0c0c01e00c9040d03841650441c0d100f070702c100c0307805482c004660358400048601591383d40075100201c04810540d0300c000d581400004040141005400560041d0035041d003800901c0185008415500c1c2000b17a084d1503801d2900c0706102540c501440171560201d54014a03615001002d0360402c400c0500b803166501000c8201540c030070680c1c540ca01101501c040c100b4001d411140f05240940802c030469016006051402d41e44001207800074a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 950533462 1250 950532212 950532221
    0x110c102c0312030604113f0a0903020703050d051206030a02060306090c1c0203160903020306010b070303060914011a09030303130f021005030a0e0c15070305130603060509070201 78
    0x144010042c080760041420806140d410141046a005950340e2100c11480030403001071650f03c0f00b001c428500e0840311201e40035501c2e0051a100c0800805000007124100c1340020154400300500b4002520300403802d080345880041d41005145109522082001603045005080031501c0802018400e64520b030505803212260400250440303424004204d491070804c0c507203a884503441d0021418426513040540101d0450200b9001442d030000500c441c45801d01e800e032808440909041441c3c600e50b81c04255039a02c1482500307604000403c240003058130a030001401000310903401c0c0046460700c25010800c4100384039134070502150f9080810010f558006484034034400501650035940c4040d0300c2c1d0308000221004a91509c02c00c0801401a640c204120203002d400c0c5c0c0c1c8158503860001d100c141250035418040c034842e848081c1c8610b00c0d41d0380009000400080070300701342c0c4803616072605548a00400302482c2400b05103110100e01e01d075040d803006040320801c640b10026515500c0b016800c95 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 950534712 1250 950533462 950533547
    0x30b0d06061e241e0e01170912030c0706050a050f1b03070f09231e130b0301090c061101050a060b0313030207050a18140f07110c10 58
    0x100c807054a4200403562201000380210050b0420031036840c80060030408000c015106440420383d418288400d551f0b114607024000c1840c1040c1000c0c0e81040c2213416a5003d105004c40c81e14903000001030103d07880c050030341c1e0130729600c8403040c8040e040ca9108078024104c11600c90903141100c07000100c1740000c0e0f405005030300789800e00e40d80c910303111300404440500e540c0401d082444001240001c140203c2d04c002c4040ba0840148100324501d664200701e4030b170380d01040c1e0480d120308101c06442c242e921030740101d51171180b48000144045500021030701510521a01500d40c24800301d0000d942c0303400c040d04629280110000b000f80d1341d69050600d00715075050040c401c0c0c843c0c06100080203184101d0300321b1000c0d40a80100d400243d0303108001a1008010307005138003001c49034082e80b68030780024050b450078584840201404c074500040c00e0882c50741e0041c5000304101c1402c001c0031924070f0a128110790719030040c06050000788040c60140c240b45500e0414a074144241c2e1681c0d041c10200d1074103801a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 950535962 1250 950534712 950534729
    0xc04050406200c061f171f0b0102060c190507021207030317130b04020118090203010b0403050f0f0a08070c05041a011e0207230a08070f0902030421030b0d06061e 71
    0x502d007485175041d10f2550b5986c0310001880381c01c01c248082c20400f003040400009041011454400c00d80009007481805010854102810f10400000800c030345100100940d42c0e24103d911900d807030002844021144424a290b809140004002e040d403014509072400140fa61902545d22001a0a01000c13000e620280000303483c0b6000c01e0056205200c0481c2458002854401c0e00e519603816400703d074803e90000f202018001000c000308402840760540049006010308010fa0f10b45540c03680743c2c0039000700201454000101c1c8000c006050900d4070107814003070010841c0742090b4107403d03c14001c110500c0c1c040742420844505080110308500ca4442d005d41c00b40800364070340601e00905d030b9280c024512800c004102100825191083d0400003081c0c800700030300c042071078281d0140a1711419042029024010001c01000c5242c404103040181c40b0b1221546803030421f00c00880041c2150011283c0c0038038404907180a2110f02d030002e40650ba60800058140c240450140e860a00303030340301d207000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 950537212 1250 950535962 950536021
    0x1803030809010e0607081008070f090b0a091505040e0c031c03060515120f070804121101090c030c05040207020904020f010e120303010e13050c04050406200c06 70
    0x19106080340c6410151910000c9030b84100c009015082103400c4901c4000500c40a007001601e00f00651048000c1c0141c81c064240d8500b81448000e440740c0c0d602401c02019150b4011580d251211125080100066282040310000016954080f20660b2166a01c1603007010703c0d18155840129585042070710080080c146125011194040070484070083c034141a5079140004241e10781c4da030f041014220309021280d03202c01c2e0511500802c600a0040720081000c6010401c2a5800950030394100e0b4006072001e95030074031801d08840038030041203c000c03e0b50a104106080221800010003904c0c4a0b6000c140700c162140300344401c034060520080c4d84101c88e10b0101d80036040100034480b54810614040250300000404964204051070041202d6030000004100c141e0440105680040891400d810f042d032071034030790540e40c0040b030060340c1c840d95958021508114044c1d0224450301401d40c18926104c0b850952842141c00c082d2400300c06004490006010440d40b03181d0b1aa424010b410400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 950538462 1250 950537212 950537219
    0x1c0b03031e0301050432150604080601091b021533130b01020706030e0307121e0c03080f090f01050903120105100801031502040918060b01170711071d01060f18 70
    0x20950180503020b0110f007d0703034003007124050301c0d407034020300151070741d0001055954501510501182d40440c0ca920006402064007106560b0100d1451203100650800100d9602c561007100b040e40724000b151490800c010030208010540405082e08035182201c209603d503003c442c1d100c0a80700304c280c586005030800f1000740a524040e038002c3e911140894100c90400c1010b680706181c000e0402110340114840c841074150b0018000c2031060b14a4182c5064445141e1039a400750118030040d01030f07400303198104001484540c0c05c00c1032203420084d080003444282030141c001e5480380c1c01841d039000c03000042400032545080001c188101e00b00f440e40c4078102a0b10710b490341c0500d020340c00a40384006400304800100e08005014200504158100510b403000603850084c0448560740780c03c0303040c09000414098050600b4111640c000c10034100f140d804031000c4115800c208040d0403180e824040000c0c59029901005101c605840045c1c5450f2140110a00207031b803074862042c07021101000110b403d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 950539568 1106 950538462 950538551
    0x32505010e0124180e010209090c13080f060a09021c030306180515040b180a02120106080c0f0708040b16060606051c0b03031e03010504 60
    0x10068910b01080d4440400c01c1000504d42c46a5491722820151000c0d0101d92404400901400c800c0c9480202076000303400501c1110b800f01e0b403030300d00480c032024005400c44403180c0120040a1940e1002d0b6a4009810700a208030707008040c401c04a0030099410030302c1780075603210b0340b000308526080030200c10400c0d00240c280c1007014105424171400d90740c0039000401e2000151404141d5000520205095602c5840004052a502d00400980803240c0c0d01030700e407400c0c0c0300c100035085d6640c0300821686030000340c41039075032520100300c40491407145800810071944511050340c1003a542d101d41c0c0041d900480440c00b00b041c00b00302500104400c520401000d0b0990341090340c00c0400038001040d005c40100341642c00e843d603a600c05005940c0c20005d544058464628000c00b0426610100080d0b420030322602d4003c40c148614200c1e02c042040703880000131000d090700c0d000f104065218 = true := by decide +kernel

theorem cover : BRFrame.Cov 950359712 950539568 := by
  have h0 := BRFrame.cov_init 950359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 950359712 ≤ n) (h2 : n < 950539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
