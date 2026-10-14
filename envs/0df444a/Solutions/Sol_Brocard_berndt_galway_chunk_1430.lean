-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1430
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:56:57.746577+00:00
-- url     : https://prove2.me/submissions/b30c7e5a-3a1c-47f7-95a0-4e16b0f5bfae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 257014388 ≤ n < 257194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 257015638 1250 257014388 257014393
    0xb130201030f020313080c01180308090c1e210a0b010f06090b040e060409020d050102210f04020415031b170c0a1412010e0d0318030905150c010c020a0203 68
    0x8502c108003104038481214010070070424040c203400850824000742412001900c000901d10000d03c003458503005010b40b00300d00240c5a9810440014000d000070064000103440304800b613080410a40941100350580500840030000300e41d160f4800100d02a8640c0c04907000d5502021107800d0440b042c80003402130b03a003211003242c3c00180bc2c0f0b220b200550203c40b003d110803824141010340a258041c8003805840c0c0c80b41d1200c201c800940e40d511544101c45224100059907a034001008000c80d90038030190f001d01004250422030320140c0b8a50860740f050781118002a190a00102d03003102d035640d41c0000d00880814004214005841c0c09014140c0d1840120401065031001d107165944855481a42c0c025008060400143d41481a41e0a224600030400b407844c18002141500b120345010280c032265000c100070b004241d42520880e0601e00480d041d241d0034a0868501400c4100c0030311030640110f4440f03020040c088802c009403244855250020b1001084a40340255200e111140c180d00c40d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 257016888 1250 257015638 257015651
    0x4110109080f071a12070c0302010b030a02060d050901091a0103020102010506060f1b1903020105040c290d020909040501050601082d04020a03020a150801080303040f0204020901020a0b13020103 85
    0x410008180d22010800070007401110f0a00001d07103130140800c00b04004490b81408462642c0d1100e00403244108250380d01c00900c580135007030013800c0d10000900c4a0081e0498202c010158031160200c956041c844000441c240e220700315454010051003501030314040050109144003a4400c0e1800d040324000d030b00034401d5417215010050544110881105801c008002150318108001c40200c070410060f01682c1824800721009054070301c0c644002c800503559071040104205202070003002600c03001050000080410342c03203207ca506a560440d602c032002256450344501550111901030310081c1086c5081d040c14a040c0340a054180e0b043d42c0401c89078000101c490400e0300304480e200d0750000c10124075611000d400c040c0003034060001d036000204c0000200150301e451705500b006240905011901407411900105110810307000042d05400c10002d100124405440c110f01054043360010f07510040c000050b4030344105a207008040785400410005680c0d140200c4c04103042c000e032402c2c00704 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 257018138 1250 257016888 257016899
    0x71e1d1e060607060b0f06030c071b03050d08151503040302060601030911040b0d020405010b1b0304050a06050d02120a060602010c02030903300f1902150f100e04110109 74
    0x2000c210703203031600440e06016032004107515400c40003000d800500b0201401c222440820003da1044801c020215000511501003180380c00504102d032049150300700341c060945d0303211030322001803a4480041081103001324001040d0b40d04400002d640040684800c3e14182c402014160411901030f80940140301c0040c03000d501900840d084a540540c24102c5640c1810030031001f80080030300e040e00f00071241054001a01c1d180f090340e01829056581d20346403d04000031908000343d042800c602d5403c18002080581c48205018094030794604185480e41d1900b000800240070b280e030b101c00180349042c2401682001640700c1001d6812950082c4000d01141405913900c2c030901d002e82d50507074880026000100d81c030b03079003820328400241d0200c815210040d061840c61b801450680742c07030f50400032306a4a02d0080b82c0c0003070790791480350025041c040c02c50001d21601f1070000301540e009200d0b0307000144400540110b00d03000303848006096182c40c00c060910070b041100083d80c035030200e107a04101040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 257019388 1250 257018138 257018191
    0x21005030417160f0b0a0e0a0b010317090618010801050a030506010302040e120d06060f0c0506070309050c061303020a0506040305030a030209011206030803160809071e1d 75
    0x10071508800d411801d0032000c1030700110360303104003c42c010310040c1c0d5002e01c000072800d000303001e10a405010207403018141a4510701c11511410300031400d5900010000000a12280c1c5081c1103d403c00410815034511201e0300304680b0401e94090307840f600002d22102e00030340d05881c1c0c4904070020b80e20000c05a80702c87c10300c01c150601c0c0c00301030119400030004000516203a044441c8042d80c031000e40308801402540130302541c00001003125840c0d1100002d101c5a6404011100c40190a14240c1c43d85402d585549440f02c1e0094010001c2640303800ac076005204040009910081001d000c0c00ea03100100b80e800c0c1c00da450340f40800ca1180e08042d0000546262280555094a4220307010b58940301000006500a50110203c00e042c4009101e100b0b403400700d18070903400198010b100040e900d14055018501d15001c0000c1036041c4004842030088034900026500c042e114181d1803a100840310404101d505030059110101e94034242203083e10030391803161a28012032002e0b420498100c1030700783d040b5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 257020638 1250 257019388 257019391
    0x6040b07030513060f090606170f03270f0604060905030c0f150307030902060d0507030f0c0e150c010204091b05031501030f0f0603030807111204030f031e02070302100503 75
    0x62124502d0700f080d000c6845944012045042e4081c0010907070b290b680d9840645009074060352074580c2c1c44004a4a030401800300b0303070807038507500043c501d03200c00000308912058010000e201d0400b212540c0030410f40b200c111000c209440101415140c2e552a10300034008149400f800c1e019006050500c4a00d04264510361243c040c000c043c0c01e900300c540000f140598000920b110205030b20b4074244009030b00c0e00c000800b0805a03250303000c605850a550060152000e001507030011503d03041113281002c0d44401d91551802003103440c0300c0306d8484e403110040140a400c07001e44103540300190001e1a0881039121192807141e12030001d4905500084c2901c160004070751502921a519202c042552301c00e90009203c01d46082d8000b0b2550000040c0c1030440d46241c00032404204080d0501c800103410042d410700c1c0902c060000c1055040700c485c6281680510701c00204580c0194559104250291246003001a56001591900012180025515082e52206034000d9180c0040d2a4581e446181100d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 257021888 1250 257020638 257020651
    0x1030e07032d06090b060a050f1f0507050f0d020d0c0c0b0706020f030907050906030109021c02060c120304021806010503040201140408161406070506130f120206040b070305 76
    0x2445440310070144104190082604000c0030040318000140d802d00c104c6440500a50300d1030900e1528500380f000070f2410740c11a500c00ea40b60103a0b046941e0b950031085011603241740e0106004032480a099602d409802802460303405111481300030002e0002d5a02c480201c15402ca0b04440c0e41c0907001c1d81e01085459024115000a00040c011310203224002c20f8a280b0800c00146081841c440d024440d40003910100c8aa400c4100302300300f50310b0000b4074160440411402002240d90a500103441c03041611003602c101d41b0010701c410155079424066410f00c0c142030058400804503c1c100700380551045408034070508103200303110911445524158031036081a1903417442d5880d550015245070824901094015808002c0403c2608040c003e8151800d45942000c0401d41003d11040c0e5951045105034001c2c070b403e001d8880400e0740010540d0300500b60354020b498440590504481071201800080c1902d42e180041c0c48100b540044e4440c03046000304040e00aa4840c000102c0507a541035600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 257023138 1250 257021888 257021903
    0x1e100e1f020a080f060f12010b040c110a0b04020a0504060621141828020a150905220204030b060108070e060306060a050d0903020102070b0c04230105090d1101030e0703 74
    0x900413805065020b41c004100408101141c680b0500040ba04610303d48038040ca40d45804840740113041502035002c13000385508014a4039803407036000d0f40d604c20031408040c0c59944040082070554981002030070180c1130140080c415640c9078000a02640346c0c05115841c15034541e100c0003054810340c42241700700c007201c20700c807100c81d1100c44014940340031156901030140208600402c901d240f464203964141c00f803184c0c04941c01c1c114010042510802e9008402003800e6500c920f04c40c540c040170010644808954001060030800c25140f0030b0414040d8100c002c91001402200740100507508500c9104247e8a01c5080e945440d0b048901100308412143c11100a00202e42c0a02d0f00d04094800312100e03180c51420160907648002c1038802e880410741c00b50350300062140601c88410351107984522a103468924052510301d0600500c8241c1d500340101503011f0804190f90b0f803045080f90301c00b080c010100042081e507414000d0701201c800c0c110300c0c0482c1c6000d19001c01d540e0701240c0c1900b00d81d000310300b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 257024388 1250 257023138 257023141
    0x51605160308041514060a05031b0108070c351201031101020a021f0212130b13050402030403030e07081219170406230402031e100e1f020a08 62
    0x4003550a4100900204c544101c2100480c55070b1085124079a418203065414640604150060100c8150140c2203113000350080080399201c8410070b11403200a1000b840c1c100150f94400b402107c1810041d40300500f010303000003841000e810742162909801070019544c040345038480d090400c040c42048241280011000010808180c0d039030300a9107000b0040c01940d402131440d0703001440c000003200c0420a545403074000020b00d07941c108503002542c0c213205106450b025524501d220b003102140b00741c0349204000100d1701c0c00920711402540c0141030150085d516400c092401a014101801c0c10282c40d00c10008006100200000c500d06107004400708503261443d803050740030a200703d07808450203100055600d048502e000c2c542c1c0902c11402988001815614082211806056505040d05100311031083c4000f6030340104039880c10406459101c00ca403540030840c241400c01515441480ea03260076101503518401180300950304649a0003403000038800c500b1141240120700703202000030306520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 257025638 1250 257024388 257024393
    0x11010f0204060813030905130e0609032b1e020712020c0a05041a03060c03040c06020c01080105042c030c010501050a030b13050c03060a0c0f02070510050a0e06040905160516 76
    0x52000c000c99000c0e1420412098503000410300150b00c002d048e0a1250303035183c285112040034814150400303054409140f61500c164400b08020616211401d4205ca4120700004542d46176070154614944410521600c000e03101e04100094000c1c15058030b81c10b5401a0789136500c1e20114050001c850020400c0c0801c9080c001030000506902803400840c0c86090403d8107180e030100041c0744aa403007172420654a25061030010345e600c0450f4000d50030b640c00540303612101c0c3e8102c0000e90540d2019a000142001040300201164032510684141290086070507d12654080010400c2085a50003808280d07600d4041c0205034260f0f2101400b010f00d100e0114021040102800800b58015011100c2c510244800a030410b8410f860b6520300381c0c0d469001854850304450001c44201c0c0a0000d041d0403407a140100e0000750091a00c03404001c400aa40c032445405401045800080038210913151034031340d0405001020107403003a00c840c00180c0c90310641203205800b00c45012644400040d041c00c2145e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 257026888 1250 257025638 257025661
    0x1a19030c0f2f0109020301020301030c03020114090d12050d0c181d0c090a0e13021005070308070509151306090b1303030e04180b0402100f17040203030408060711010f02040608 77
    0x421001d445541302d00020f40582e9003400918041e45c002c5240680c101d00e10700c009070076101403c090042c2c4100c1031045229035618220218026078104200804024682d41d01b101c051103a040c0b28020366240074013a065a03a8025040400c1754507002c201c04040741c403252012005110301045c00c88412070200016034001315000602000c0c0806002c02d600203031504000014000101c505441c00300003041c519083d850f04031103c013203240660402d546800c1494400400c0c034400107060000384040001e244000e0b480710041c0850036101c403440e4680b500802c5180c903030300b01010302c1307030702c0002c0d4014001103041032504085a00070080800f14030100c0d85103503406c0d613848402c901c403190b03c1071742e40f0300f00350340140d00345140707124144551808115403401e0b104001e01103000012010400180d803564400c2581c100c400541e09070420400c82c802c40c0d132035100103451031040e9003200301180103a8003070119068001c248060743d000750a009100b442080c2c64000304030300561080d100012032487c0802c503508001d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 257028138 1250 257026888 257026967
    0xb0a080c10090305060106110c1005030f04050304090207081809060307060804030504050d1103010f0b0a030b04020307120309081c0f050d090c0f0e010b040f1a19030c0f 74
    0x3801d00c990b03000c1c0d40c0d440d11403d01c0300076808000822100c40c41c800c0290814440c00401841c05c4485c02251140304030002e019000042c21401800740c00004542441030420a40d001014a030200355550b040500d04002180c10030440740c5100e035200c013600030380e9180038109a4802d03000600200001450b0034011203200d03034040c0c401e40501c1001c001c0412151580601c4091240c020300340a4440c44c2520241800c44a15040c0d00f00683c0c60700c0e4190445a0340d400ca100110798001d03800514940380e50001078201449a40481c600e020000904810140c000f0109400c90ba0b8080540346601d0070f010749403041c0c54100b0a9100020400e02d5202042401400581840140308000040d04c000550350340303018001641001880c120103010400c0b1001034000c0d21030240c54034401c19800c00703103800d60340c1d52042158080c5403800354082d03104e450b16900c91411760b681d8004140000760b825841c0b10001d001800c2d103814500006032188043c030400c2d07006581c030456680004080341c80301c0c61800740003130141c0c40b0f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 257029388 1250 257028138 257028169
    0x609080606221410291c020f0304110901060e01080403080703091203020309010c0e1c0f060f0b040c020a05060a270b090c01020d050a0c080c06090a02040b0a080c 71
    0xa030f541610000108038890140704982d00c1e110364500c0e42c10500f20007802290038240c0d00002111010307242d030f00705422080d5a40640e02d00c920300c052460f0740c01500c0203401400c0a03408094008000c200034003030f00000e040d01e134070001d4034268010703601c03003070111500e03118001d15a01285015011500080c4904a6192b00c172140d4540003600b8601c2d69a241841a0100c0d01d08000a40200621100006c00c0c4913403001c02c101c03820203092181c1c100001c00d52418070301d0100003c5c1e852050061050000d41c23408051291380c080d60400c203210b1070000711402400c9482005d0f000e1071612004a10242c00000e180e0b41da0780c0c010006046070366411141c1809407510100c400a4501c0881c14860302d1100c40108800051060080704171a19062048501d40080c502999045500c50318000c0b10080d00501100e500c2a054a05481300e00017038144145288107606944415100d550200b140010021801c60600c2d4800c40e410301c04410400e08000c1c40c84428000c103040d0350884046000750303143c0b00284410407803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 257030638 1250 257029388 257029391
    0x12030402060f120402040509070609090c110313030605061c06050c22080f0607080408090607230c011d01050702041404030206100812030a02090109030b090106060908060622 76
    0x500740c03032a048441e00701c45070f55510125581d041c0811403809000310759019140c80000c002180c41c0a8000300260703103078030030003229030350360307a80c00501610a0016000b860407680c11659901c080582900d074980191006880d2180f40030702140107464041301000c84401d000341280c051900c1a2604401000b01510500045004002141240d01e4a8400b00b200182c411003002ea43d81c83d203480c203818103846054002c0f940d00688100321100e5007101c2440e4100350000c40a5417582c514002040262250000240881009900078219040f00c240d14211035209501070300c01a010348401900d00d0729602c0f08200b035060348812020050b511500180000900040002c21500c44074692801e414805a40a40042e0085000c1000c4014410329000041c4a910010440d5035607030a0002450302024000c003424071340000341450160f1107640113001554200f51100040c0c00e000d6455070007401e40d40304078401308a10704000034801c000410035034461000501802c6400103d41600d4021440c20701300405240d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 257031888 1250 257030638 257030647
    0xf0a020c0324060607050604030c030e1c110f010504090e070504090f020a0b0702031903021509030a0905060405030604120504031208060f0f030a080d0e150402100206091203040206 79
    0x6a40c2040801c040c02c8401c0c92890118810920308891004001c0006005107010490003000500011748140d000d5054035094103202007610f0300f00c580603110315a065200d0705401c0034020329001c20002500e10740c4075030b0041c503000e48001d003800b00300c48941800602003142800100195407482d0840e02012002c5030694140c907495500103021560900c80598141d001c0702031403821030915451030000303060310380000e40c108101c07540006c0c1d03103c2c2240c4c2204a001b041803c403d0825000f00406200400a500300c1d0f0101d103402c030070041d6a03801c45203000c400070303090700000184ca04054007250141c43d4054042c00507595203481321201d40807496100020007000700030000214800480d0701500c01001e6880d521030f400e180c000c00a2407200e15004612070040035003101e0180d40c1c00501200c0b85540020001c1c1c990b0700004180c0b00400c5000214081ca01070303480d521035101c1c0c0c0c140c005441980700300e890503000030400314200d81d00c1e00100c0303030702441d80e100100c0074008101e50805190700c188020a50780c40d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 257033138 1250 257031888 257031913
    0x31204030e0405280e01020f030103060b0a0f030b06040c051204050105040209150604150e060c01060e100503060f040615030b041704060503220c091a0303030709170a141f02030c0f0a02 81
    0x12399100b64029100240ea0f40e000d1911480c02c0032031840108002c1080008550450b29200e1b02c85101404540c410340d0f0347d807054080180142c0641d05031042603800440d05280500f8030354060007044400302d218200560010b0104d200ea400c1d14040500040c0c1700500b0301d42891b1626030402488502142400f21481040100d1343e92180200014030600c000400e4091400c250440040e101030036240080d20b0501050089490001c1c980c0c1e8840147d076200e002c1038456051000041c400400d051840b5800980080240208c015019006600c502d940880c03001e81c5068402c51b50055005040001d0002c20101c0c2046c1c041006180000303511814130080700c8020788ea00545405958000310400c0c3c0c960400c90803000d01040e02c03284034181500918518030344100020700d6003116020b400740c002c14032201680315182c00c0111076410756000c80300c4840d581003d8205d941da1850300c0f0404442e241c107010203001c6100ea500980e409103212110207800d2080d055022405a005030b044981180701d44401d1441 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 257034388 1250 257033138 257033167
    0x20904110f18031c0309020f060d0b031228020f1e060a1a061804060308030405060a1505010c050a0c0e01150804020a03030503040203031204030e0405280e0102 70
    0x460000e45004a9600e800d5101c400101401c241000b901c00e0f00110001312181038010b0003003101403014a800240600c580c8001500002450f0145030480300116150314100d9046c2d00c0140641340480c112500520400702c5a5010304c1042200c4c00e42ca60200030069003131024141200441d10107005940f000b04240c54a10301e0700c5054041c1070b0303002c04042e02410503080140401078000c11034940602c41d480c0746040181e0841000000c03140144400141790380d1520980c80828400100244207000b0b10f40d590800461581050b101600d8030300480e00460f0202103e071040c0110a44441c0c03503000d4240c030f0400151441c00e070707900b402d5500d03018815990000031a40030625000e00f0740903800c4a002d50415101c101d20350400301c107180c14000128240000750f0b603808110f804480c0c0c54039050350f07241d0361440843d003140107143c2a44410344108080c0001c05800c03040c60200d4020a5034204215607440f082080050100701c80f1800780212220900308840084d0030580700c9610600015150802c9040c4001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 257035638 1250 257034388 257034397
    0x3021024060809150601020a021f031103011503020702040207051608060106090303170406180b060f04140601030e0115120501050f0108061807050d0f05010b060a05090402090411 78
    0x1280003400d060030300d10525000d05608054815898480441d1400318081580c918107480d015903a0110f520014060703030310800815000b0b40d40a0410003200000d40340c552803100100014201003410005100110705040d415a41264861050303c05899200103040d0025841201c080c0d801c1902048518041482049814182907110078a4000507150401d082d09050068101808020285004001281d03014070b40d01d10001a41040a03625140c03403400f00001c0a40d4900f8440401040074004240240e01d0070303551055034159807000d4890614000c0000325000c46c1c8075015003034415404035105500c60780c40144100d8103a000000d0301c1611414081c42010f0301c0d400500302c0e804403802c05040107802c0c000e179500007171200c01855941d410100c0245d166040206540c04140b01c584200011036400c2118400401c030140003444007003036500301025040d142d403405890710760a212810442e410080203d0740302c0350943c1d8802e8101140002008041d6014802c3c0035802900e4120b051701454a030030041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 257036888 1250 257035638 257035661
    0x5150405070b1c0506011e180e091608070b0304030503071205130204292418030d020c0102120903070801143705180604291b07030210 59
    0x6036030000d403070000c6401c3d640010000c0381080411880052503a40b441c00c0766040900030704210140c23440c40b05000d0b500c2c400503441804064014801d2000201c008180e54100000c2c1201030074240e03403212126547c9128600c40c044074043c0402c00100803a1098000c1d680203031403403502c030581c40145040769007541c4007075648109402c181c94000c41180352a2140144803240d040c0341d000119030094035407800036001c019581c090b4541401034400d01400c1456509075680c210307511921a540000202c1134816a8403106009201d1020011800d90001941d201c21080c164010180c6103181014100d4980000400703d4041c4224540410034000038061840c1140c1e080102090620385461072000650784110401000265070500403c0d0883e05000001d00ba0b54024000c6455101c0e000d0b00203040003d03035041c0307081d07015090a0008002a805d10500c2601c0d144e4102031051458200c52036808030140c600d00904560143c03400c8491000304054900385000b80142d03071421100c2400300060740c1d03400500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 257038138 1250 257036888 257036917
    0x2090a0612060911091002030705070e0f06013b03060c0a14210c0706050f060102070807060c060902120706120c0c0b04020409022b0b0702030705150405070b 69
    0x8403240c0000c0c0c2d10038800288100c040a0201c40d007040780e10080c52054204580c003800010210030b0005008004940d480303540001119012a5910000104007600f0703205600d07600c3c81080454100c0d0700c0b0300c2e41011107032a5500020f03001c2283c03100101206011640041038107031500f02107051568140b0800380303c1c540102c1d0710340c2d41d285d04810061500c45185030b080b125003010f00c00501c0c5070550080c3c044101c0d01011121140d5101d442e69504140a40e0030014405030403c1c0410544030300c0c00c016180038010a07001c40b0710594846814070b449041394000d000019084405990100d10746411040000c1d002070144030462001a00302030030208150819800300d408821500c1d02c3d1880392040320009031161074288080c225541c3c0e0010300d040c0290006c3e1003140c440c100c503400c2d941c52100c2070300c00d40110b100c0901043c2d0300202d08989618041c0040d2a02c900d92000105076500203c200c4020301d03400000b81c42c0c06401501c01881118015009482501c501c0c200400c0c80f1482000070842c58829544 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 257039388 1250 257038138 257038157
    0x3031303140a090f060f051e1911010c020d171305032d0909061905030d030c02070906030308011a090402031819020a0b0721030e0f0d091802090a06 65
    0x1c04a4545201d0f4844400c000e4460310846e03010b03920030240c44078800c0007462814a40d01c4441e010217103010300000240032500d016507041506821000000700d091485000703200c5206246801d80e00c943e4003898560210f4944040b4003d40710a4501c410b80c007040c141d00c20075944030a0344134a0700d540c004418008000c03688260036010b496070304c02e401007540d449a400030f18014200303000c070307240c8000035001901441c0030044e02022980070ba4510001350001401b05c0f01200e0702c40da002005040714504080141c000c0d21740101e06100c0d80d0217101c00340ca400d40c42d6000c0d9a46071280c10b1840400080440300c0442051241400c1a031300c0d40001c50046228100d400e05100324001440c0c10407440646000e440008002e002e00103880b280200c10031900000c003600d49403103c600f41014052aaa414440158a100d07003021215426500c00d0305505901005c403025624445c00199541c403800701d0803000308108200800c48150414030421017858a28005400d1210340c4d80031600c1042c00c0d030420408a02c6844 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 257040638 1250 257039388 257039399
    0x90201080901090312020c0a0f050615180408030601090f060504031505130204110d020d090515070c0b07030e0a0302010608010510230102160e040302070e0903031303140a09 76
    0x41209400214078002041440c00f80d07500079040005205082503a9600814603d803a114240b2400d110b140d0070070500304d40758035503181640d19400102c464104140904a90a110382003040380341003880f00042d0700c692151a41d03115688540c1006010b01c1c108034a864000c24181030380703260f00b4010405511110340301c0e1b0661401c081c9240340c010194002078038100c00c004c001c00c0032013024111b02c0d03015100018000c480329411000c9104641240d0901070001441800214241c0c0c0030b0105203005105848120142d2140b2010203182507a80e2000200e0f04501e0901040094241d1504110715040024030800404d01150429503100b005402603556400d003000008820301034a030f408a00c040c1c07409140f5007003840c100302c503032a410300c50b8100c0c14174581c442e545070340204000307a00c000440c0d003c034000541d2400d040e98504d20840c1e040700107000d00740b00050185201c003070407402040f00c04069803d5607110205011001c440d914240d0400ca005940d580f50b00d02034000600c804242c2d5a01c0c0048181401d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 257041888 1250 257040638 257040647
    0x60b041107050d140a0f0e0307150206061305040f06020d02040e1302030d03150306050907050d050d030c051314010c0821010b04050d030f030b03070f090b1503280c03090201 76
    0x40180c21541340030081c0341c00d0716a02600300400164181010100e0900c460046868030301580c02816072180c00c0c110341203201d50002001807140204440180c0c02c2c41600065030203440013550000d10781c455100c2600f00141c05900a0401121011001801c00f039580c80102e568500564091548071940b051180c250306007404000c580d14030f1400d00f0301109043c0140d4400040f035501c005044c480d503031008110030843c14003008004180041240343c0303040980c01d0103600c1c4c410120700343d40841e2400004000c0700c1c0c042d0085c2c0755110065400084582d1810b11188001101c0341907032170403c0036051200c800a0280d10143c418081080c01d04092014a0980808031044c1a0002190700c2c105010402460b0703604203044c0c0150341e1501d0212400e10b44458180d01410042d5105a4180580c41e03021132074100480d100130403541d030300f0030a104000e00a02403003c00c4403c2d0218aa0f041420070008210038410400c2000d110044801544a6010040700808450b401800080001d840d289400103543e4007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 257043138 1250 257041888 257041907
    0x1b0f03050901060b0f07020d021503010f0f060e01110c04060b0408010605030102030412030c0c0c2304020a0903020609130219080c0f040501031e09030915090503030403060b041107050d 81
    0xd14002c00415040c901c58030000d019588480750400d40c000381b450219103500100d0900c032a4040c1c2804c80c056140400c501d89a0401d00911202c2031000c00000345030351200d4032010032284a03840340c4e41040c43c8680119003c0103082002c002910507400380324119203640c4100d000034a40514072039104c6082660003820740d070442c2d00242c8a80e006000340800703d00c90000c2e0f04070310fa0080c2400100450010030540f024020fa50380030307040c51025200003503c507504070700703000380046500790780560044008208002ca000d01c140f2000018024241070005050000c024584440001d014440c825800e1402c80d050b0b901003150b03074000b000b204502ca10718542040511760407400b50020301c0d00f811000c1c031030b00c80383d805a4880c29042540b00c000149000d00c46214401003040d40c001c0500102a407801c0113030041603680314100b50303414604a101c2d40c60744161060400d68400038040d40c502403a41c2c032244060700c003440250790700c19503c10040c0044d49582006003c141e21500c0940000700c903100c2c01500140d0b2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 257044388 1250 257043138 257043151
    0x33080708040602210a060602030a080c0306030705030d03020c060703090f17040f0909050c03030f031609030609050f06070906051803031317120319020a030f230a02070c06080702011b0f0305 83
    0x8c4c064040052f800128240d03004480c0c0c05441e850760b440354002480c09045500c403903054050607032a02c00310703a807607001807200c40311000c04c94020f9160007604500300d68410304041d200b107811030400e0000803000c28140e540c2120f078a5403103051a894081c90040c0c01180e905c404a0356584112905c00c005052218a11900d0114007840c181a190518801207220041c10000e00d581000c0c62540c07903078050100b1102664021008101c5500d1500c1e209540e40c00640c0c0a6046220700400980d499115070296415184141d03140c608207000030601858014408440aa143c0000e1006030421707180034074104010045620070036910744001c02c82c40c0c18150401c4c00c6003241102001000300061601c01a86904141d0303980060ba1185a11811030061820056900308541802e800010440611000c40411510103102c0d80d11703a00c520080e00100e00c240200140140003209080180a008804c01540071480f40000704030b075114201107440f0001106140c1c808140040040405190b0503c2003650042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 257045638 1250 257044388 257044393
    0x509040f050d1205010918020d061104090209180105060a051b0607021507020a031b03030b041a040b030610060f020f0f010c1b110402090402090303030133080708040602210a060602 79
    0x10441d0311541c7c690210300a80070342e1040755850108020395210342d4006005840080c0c03580c0c0c5501d8044007030360101849600c00c7c410444484882031030f01044d14100c80c4014000c80c60700340d1003a0305840507000320642c0e9003046081d07060b207450074605100d0075128a0680d030180c503205041c408081e0240c0700261401c011503000e072040d100003940042c8030308103103214030101c10301c07005c454a011130207841101a003a4205041105003c49501c1802c00141100c008640512140c0c2900043c9565500100c60100f1000c0e008a010032030383d1302403105c0d10307907400140c8142d5480d103084030b801e00c1c034000d02071f50314506980d520740145017401d50000d143c5880d8100340c1140d040c840c25a2700d450719465a4050160b03c070b981e0014210750781340c1d0385504131075280300c01800b901c1d00da42c0e43d0810030401c0c0800c0c036000a01c14107511809400001c4014214540919a072275600c9240c841074001c5402d1034009104076171941d400c0040100300b50103c0c445901802c20f00f50400818501014648103891007a8014410365 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 257046888 1250 257045638 257045651
    0x8071a010807082508011a040c02010b01050706050403140703050304021903031e050910120f0203060619050d020c06160305070207090f09060e0307060b06070c0509040f050d12050109 80
    0x4000401d941441c503082880134000040070740140182c400540e03010000541c80c20f1801c4c0c0c01007034821403d09001d00c0403a000c02c58000032100c01d900340c610300c4010380c0c000340c02002a9800141141d1046411034000d2030240000406c8150001003503020140982c0440c101208020841c9030454400104800390300e4604400d91855401904d041402211140c02008060040028070301c910182c4803062030050580301d00300781034000580a03000c00160515254102042c4807000d9105008884c00303000c000d4503842c9014600d1080c140c01110f201e0725001041030802800002c05420300180200316030b00e002070314581c00c0c8601d4040c2c3d48410034155400340b50074003041080050700408c0100807906662008641541a03810b0a0011700d222039009090500d49550003c180000101810515104840c100041044a000c0142500a00f0030003082440c2c1c0c50028052f0b41480c0041e0f90b0014800c2031303047c100d0111070b40c655040c200c541880300006403440300b80b61240d058502903180146445041003042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 257048138 1250 257046888 257046899
    0x50c1e0109051f0e0304031110030e0d0f23300a05070206150a1403120c061f0e070e2d0f0111060c07151a101805150708071a010807 58
    0x500b284042d02c54070580d0074008203601070b40650402a401d028540034cc5170664200d15000d050f203020707071f400f1400090100c4022240c004005030780d80102c020f030a41041c00c01d044060140e9520190000d06074051042880413006c0b07003c000401402520090300125140c9015030009140c003000174100460a105001481029180e460110068a00c60324074172000d40007410209140c0000c100700c3c41e5805a00040d4083d03501030103d45e060084c121400881e803862503c1c40036074080401d074010110781120b10008110807078040c1141070444900176085c45e140740c4101c4401c01c00d40001c910981701480d00d0707044000081c40d0400da0740e003030313a4400d00786420403c00d007291031035030f40710010300641c40c2182c005a004280300c60f80295940c0e603609440d06004240c03660700c82d99000a170321085c00d800b80070124081c00d0080d00424420102100c04000720381010304d49010000080d108111407145104200900404616544010205c40c0e0150052600821034010200b9000e80140d0040340305401c100801d02c071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 257049388 1250 257048138 257048153
    0x1021b0a0308011802041707050f0306010b0a031d030a0f08013609050a030309020a0512060a0b010e1305040c0e1306020c010b100e0a06050c1e0109051f0e030403 71
    0x5540c00c0c070018500030424135206400a1059400a0342c04040400080005404c0091160256802a01d210b82d0051000e03090541d603c00a00900100c80d0080c485005610f101c0d42c01222150b400a05169803650000c51440c1141e02406a0200203000e250301d00349503a800901c038900600310030704c0e190302c0303000103c480c0103c401c9100da03000c0c1040590012003400d60101e1700025805da400c401a40c011010b5854041c0050121200403401940510400105850030036003045500722a18041c103003558172402840010f021807443c282c1070000e18080aa040c0d1604466100780410403040098107050509040444c07044960061118a0803102000240d00031001408a17044d4002d1002d6203c0e080c0306e96003070140c40017801c8030b50045014481e00d101c032644810030014441c4142c841410080d100c0c5022905403050900e40740e15644210002550100e4500c070030f0241144403400012043d07041c0c0d4030b507400c103a1842d041156050481c810142c01014a100d81032442000030003c525251641e502d20a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 257050638 1250 257049388 257049391
    0xb09090703030e060909010e0906090a11121501140a09020c030f0307050c0d0806180105010f0c0c0305030310061209120c020609040908030a0608280515070201021b0a0308 75
    0x14204020714420000f15240c0074181c0d014204c009080c05010b6031224504c035031714402120040120f2050001090b805a0302141d00701c3c503581c21081d030302c0c50004e86c82c05109038008146502030242c1b2031401c1031009101c903102001d000c4c204c501c03070411041c04804200500b209107600a60800c502c104a40032040c6c0000040300c41d503420400085450740d4a10340d0030b40ba2409808841d0046025408a02400da07910050180c492942103501403006c460b4010b00c030040c25024000c0c0790202d040e50102c006064055410142906d1103110100b80845e2030f45d0310142542c20684a269841c909007106014003900804d2150f02c0c400c41810400c2064801d807681c0e13504803103083c900b0301406080300c0042c09540b01d1104070754149002070000d1101178103d00c3d0440d429401214005042481c00c86c000c58050404954441ea241251012070080c1300c102001000036010540220f844c0d101d14a000c1c070a900e442c2404070700c121619000140c440900e49882001c4132100d10386001d840d082000d01078006a00014501d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 257051888 1250 257050638 257050643
    0x1a01050924130803030709140a0302040f0207050a0c050114031608250801092405060918010b091003021204060b04060801020414030d020c1e0307050a03080309010b09090703 76
    0x400e016001520308101c60310814070200303001401081c000c5524800040213602a06250382d603c90260f644100c8101d202a620241c164840403000c02040035292a030003995514030b505000600e05112540e800c0c1c600125420111038a0070500780c10042503030040307600550316162441042c40c501c1c02003088805c00e40340e960711f8018485000080350402205013021110808040c01c1446025003480b40940498000d101d00351f6801d06101d1340c01c90f032850f540c1d0719292103513403051203a284900b01000c0100c160031907024144c000c030381c241d0741100c0c0c102c200c0d00e503034002e001180040343d81d00b0a04040c4110a410782e0038080606004000541440e0340359600c99500503000a80028403980c144005809020580c3c8950070030b42c000315000c940d001c4180000d01e41c91a0413401c41c0d01f0480700b15800c0c2c0c1c0300c03041000a151302c100b0b41c216180d8a001001c06448903c00000d056500b299200e20004515021a42050307925480220810412b42c109114860321030030700b115103131424500b0105440d5119482d0100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 257053138 1250 257051888 257051929
    0x2161101020a0c091a0604091505030106062307050d2102071a0703090b011701061703070f08070803010608070806010305091207060608060a140705090a0b03071b061a010509 76
    0x804117044e80201c2584041840140034a6a842c3e50344500d00107050440d000c23144920350034500080d070f8507052151008072401c54848901a9a22248003606084501d20101135084200041d000242007071103c401d0400454076481410703050070108036600810920440070013403040040d0000326040b00c02024801071940006040c50341d60013802c40140c28280d800904c400786031400400d460000020070744208003d40300030054a6079650081542e10b0038800e08100b25041003000030081072401ca10040e1042c000c2d1201841d003070301c582e541300b00c69000340d010000040b240b00500221039407100c481508240d09281c20701c114140007820540382d8000a01a07031840400040d600308100e100d400c003070006c0c2092000d8078051b28104c040200613054009640703014540c1e14001803c124003503800c1d00c0380e03000c0c0075113218007903030501034061090381c0041c0810041c03200d0180460525070485840103040391064802241c59074460042084407e0640c0400e81480340034440101c490f103e05c2c2c0700c0350700c5140003943e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 257054388 1250 257053138 257053151
    0x30b010f0e0612030d05091c05130b090105040e04030801170309011e0309060501080c010206090f0705131e0e07090b091303090f0f08100504030c2402161101020a0c09 73
    0x40340c915505c24108001c050380d00740300c10002c00360408100d40c1108008401d07040c3c0d0411a56008680c1032040d88903515450810b40d03000c3c88031003d20405800700c40d0040c14001c0ca401e4407603600b041030f4081150201c0000307000c0c1005200c102140402d568516251200444c1056076603030028008000035003640103681e00d440c0541d500316200340c210903034554012004001a58490048903140c0324a400568017510414012036040180007400024119107140940050b42c108000c11140001600780c44c403015840c0d414a06110503c900c00d401044961800000c01c8490201d00c00c0c1820340d0781d40301021a40c50f01c0320414107504e595640715072000c004001015003941d14a8107492a40491304605100c0da0b659801040f0302500c100c103d02521403500c1124400c0b541c4034010810744104850040c0003c602420340c00c0003aa61a11610010b030741ea4604481e065048101c450803078004120140c1c40040e15012038082c071441c038041034044c1e442071000c1c0c410035011785c440880e11602032040b244c809a4604 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 257055638 1250 257054388 257054419
    0xd0204020d020406090314030301060f050a020109080f0a0207090203060a030201110109080c0d0e0a03030905090721060e0915011809060507200705030709020903030f13030b010f0e06 80
    0x141100c80d46075107101e0454031280c9030080140308600d14001190130340994200540c40010002c00d880c121803031a9902c250540c0404402c035101d0300554072000c250364031055044005074004001e441d019502c40921358880f40c2c4403400030715000040d4000c61006104001740712140d00e580381c6850070303650203090802e901100300b40160f005000303c010152901c000840d02c40c00c442e201080c0f103100342c10782d65580100b4264541c20001074001e41c0c840240402c1c1d1028040180342800194030364841000c1c10031503082c501c1e80d040c10701c00c2030040361000d110039035488041c054800f400c1200c1d504400c44400a05c49a18210070308131a03a1410301950000200d04070300b100c0b03034103d190801248a80d00c0041806036042001d03010f0724040104900c941c030a5601a072a07825890b00007524411148010300034030f01c09150903808e030001c1d03000091458160200700703c0188007458040090603c3c00b00d0109900030140385061a118054040e0040001d0400c1d211007000740210248003550000002c07142c6503803a80006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 257056888 1250 257055638 257055641
    0x302070f0203060103110910050306060d14010c050a021b030607142710020123090705030f0709050105010516120917060906062704020d0b040602030718060e0d0204 72
    0x2140020761611500c3c0002c81080019101c1c102900c105a0303440300c00351990041000074007202c2c011039425a01140010711580303028098004881c0c0210200342c00c5601c1200701c103095511100c03250000c40d000040d4203911940c1005111844401d1a0160b0b17407098030301c00003c0c1c0390800900008104000c0c0c81c1c0e54070300d060300320089507420f03500210741d0f00c6080c2c103c82d80c1d512101520a205480b5030746140180383c005006010b520110303000704e504806161f501c0b208502250b000508109014402c0c2e0070f0105090700c040010302c00942254000300441c03842e004a00056580581100741042418015040072038140407003010116804150403c1c91181c2420866044c1c00c1e9500419201d0381c4031f4004544e1803404078507140244100d4094507059030b100c07024030102ca84401d2882c81c59141b5000b142020050200c5000d2f0071610043c00c5800140340c0e41c4414499140959081c1e401690000600c100182c100c7c242940115a200c4105540c42c60084042c00c0368810890190203000444021400c5688a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 257058138 1250 257056888 257056913
    0x10b03061b04080712050d0c0515041b030b0609060f01091719030f03060f06050714010b27130b01140d050f0a1109040506130311030403110913050d030207 68
    0xf40412615016038560700c4240c11525070b42c0550f0039020b21480c1c1940d81c0d11440c441400517401900034100c0c1c0152a161020020004001380e5148400c40d0f44644c1c00309454003032200075070041a4040090404008212402c0405000188209090f00c800f100c241d0304200000211286c006040c2d12060840101b14103024030301001c210b401115284100826400500c00d284d880000d903010004c06032200c0d20410400041e01423030307002c6402400004000383c05c001a02e6002045103001040c2c2c0c5440802007060031245005e454100042c4000c00c0d0000c04c1060240c5a201381083c005004000c0a03132501c1c1207504040c00380303071002c88222000f143d203038491360282040154000121682c0010402d400c580704c0740807000c11503814045098030051450891800c90090790090040c18035520388800034110000c0d00c042c11400d10044000501203118140f010388020750140c1030f03210849a607101080501000142110360b03c0d2255140d00000c10000503001004003070b075060040e611100c4e82804000001e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 257059388 1250 257058138 257058149
    0xa1b03090c08030c1e19080406020618030f1c090305090306070528030e0a08130803180613090216020f1914030a0606090c0323040609020406150305010e0603010b03061b04 75
    0x4602040c10040c4500081086405036400d842c5a034032000300801c8202424cc5203400940c1c0180404445442c80200400b9058a07003180811018103401c000300568038540d00523808244041440718190800740909075000f00d092401e64580320f0200c41c0c0384162041c40b05030342440303107510403940d595034001d50014891119107011034094940500e800c07141c40d440000c0c04020000c50540008000100201703940250000d2186001403201c04000d01400390000344242e600000060030004440d28141f00078403035207000002034070400080b4014441020ba1000b009030041d4040c04e4103601e13070030402041409940c02000c1ca400c05805600000345000b401101c0036080c01d240c054009500d0010354401170a100070b5460038401c145143d1440c580c0c0e803022504d0511407140450025002600a600c003c10140c402000040c65a4642211154102501c1c1210700441d079940300600000400c2c600056000408034002c1c089448840040390b00e1300c40140c80000d0700c0b180404800043d24907c41600c02426 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 257060638 1250 257059388 257059423
    0x10e0c070b18010e010b010210050408090901080a0c0b030c0304020f010e041401030c0e010803040e0a0912020c04050609060a05010305041106070302070f05100807080a1b03090c08030c1e 82
    0x70b00507504000c244030307400c00d080103618000c160030200070103004074808030a05070003400c17100c00c5040b5503001500008100b2521407208001c0c0310407507a04d40f9445406401d0070701c01888000d140385002008448250032111072244103000304000003086c441202c0d4020b0781a184006120341510050310a4403030500c070b07164840e090050345a1414008882a412a4050740c41001d680380d8958803119440c13001e01a0607416041003005000043c0d01081098011000d8540001d601d851612000c114003803103500040142c00c811254907107440c0600540d0b80258084680315041d041603000100681018410b013410b054607040040c0c1442842050035980c0c8602820f81c50342c90081d89002915511203020300c03040a914140c01041a0420081d000300d03600d143c1c1c13030701e40e819100c00c0c1d0141c1d04250000c1c8090141d03610f0310084584111110001d0000c1c0e445c0751008503c0205500e404241c030b07201034000c0c2609170b1050143c85006400005c0800350b61a40703020142c0e1132558118401e0030412500001311a00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 257061888 1250 257060638 257060641
    0x2060c120409020705010f0b0f06030915040803040b060108011428030f1a09100b0d1205040602010e0a080301030b1b030c0d0b040c210e060109050601091a03010e0c070b 74
    0x81441d0f0001c0c518944100001c100b0f1000d89040d580807a10745107007094020071000c01080c69030821000035508608034800704d03600c3c031314400307000e0070150411542140e11603404424001040303060001d2640262007401e00e03031840d6040039009003144244071078040c862401601080c0c401402c18809009c101000c24484101640341c0c100a10048050007013140c102c440160000c40b03442800c03a400d4080e210640103412014482c940403406444e245180a50044402640ca000500780c01256500f0801603110180c0315841c0150103404c581103100860b2440d00f0503180c0a002400881c01c42e0305481e4407501c0d13030240341c60b03100c0c40e1030f1001c40c010b12a851080c800803d2024024542e000380001c111825003d00c4120000000e10081e1307001b403c0b200010456001081e00c80f020075900c1802403011001300003e005420078025440c009081c1c1c4a0031560b540d4000340006540e00c411300001400b0600c0f03c0000e07800c1e083c00c52034280c1c0303c1442484000030040022a43c15122841140c0000340c0082c60700c00706 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 257063138 1250 257061888 257061899
    0x90412200a1e031d010306090c082403070902030a1b03061e0e04030f050903010903080108150420030c04020a03152102041509141602031602060c1204 66
    0x4602030030390250303402c80c251444549a04815841c484229505550f00c849002d210f280e66103290600307540450515480e03070800b16070014907104003801e80c03441d0f94620305207003410290044a440800b034082e50405030041e0303a40d44c54a00240c0b501c122603400500603940e80e9a249802c000303044804600c40f0780203107034519038107071039042d00500300303489900014400820311440c0c1c40480034042c1c402c03d09500200d40026000c00c3c02060324448801683c1055803428030b0311400242118051141140400c040b00010300400c402004911002d074220040d01c030342410951100d40c0d04548a00400032002c4d0640c0c44803402e5101803200c1c1c085070b0390150041d5216014001d001d0040c004001d10284400701b03c900c00a030540034030707049415940c10810000704440a5400f0702024003558241403900e0710400c540000c0d801d035a8032030321140301c80400c020241c1d4246060b80130f80b045440080c41c0c045500234010a0400c500010101d103e9a904030b90003030780c2d040c00c8800e090620320030b02040841c020b00814000369 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 257064388 1250 257063138 257063143
    0x207060306050307270b04020313140c280801060e0f060d03080a0b01031b03140702030304020901051c17130501050f0301050d1a07020c0f010e09041220 67
    0x1510200d49003441500d407103105260b6500100e101d120400010b80c40803940b030004840c4c03200c60714041d4020106000c045800402d0503030f801544c5140c00348280ca5622000d015412170040000c6540c00b003e040c455265000241c0c642611903251300c0304214455484c0d181220301c100007401445440003d2080750350f00d21100b080107104445034601c003000a00041e000e881d010400c00441641511100f42e2034462a812000422224200078141a920885103070740200c1c1e80d0440800c00440c0d90f010030380c0c024012582c00241c0c0081d0400c1c0955005000703100044c0d94080681e41501c40030f542d080341c940111180b03008041d60814020f0b00c82400c5090008521420703070010148002000f01840c1c404e070742c0704011600780c8507141d40740c00314400900c01401985440e520124150340501c10280c0c0301402001604e8000b5000d4500c4c0d805603009081e4101c8905000c04c04500648003400d10850304061040481c540d1500244000c24840c42014200007250049170044451008110078000d0142190f04003603 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 257065638 1250 257064388 257064403
    0x91103070506040f151b11180f01140a03020d0b0627070302031e0702010b01020606010f0921080a170a1803030f180302150108060108070320090c0909010501081e13080a02 75
    0x12302035162074010745800361100c4242c0780103010115103907090303a180c8403a075801c4144a102c20703a48007101c02c90020260b90b50b510405140b60084008000340c2c207010303081014100e220084c4800c040d1030600d42d200c0b2070f24481d107000e1340000c4904003da85c80d6140c81d0fa41c00c60389990b00c02054445150340520081c02d0341580700002c6580d01f80c00302d401d26141c54006440d034250058190002980c0000c00303000c10120f1200d10030159029800700c8030950f645503500c60717481d040303d1030540005641d0552842c0300003034451130a403c100441c1c420001000400102c1c680c101c04008080c050544503099090b1070625540864080c10110400c0c3c06040c0e07030340c076009444440c0c044440503a081c180b00040340e0b41101080c1c842c100c5111310002c3c005a07195540740d0550b510140701c98100200180c414429070384070b030047c491013113482443c2641d40b6418070381000742100061300310904212006080244c4004200489008640301401407582c0340c4d91112030758014610080c00500210000c10901c031030b5030b00042c061 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 257066888 1250 257065638 257065673
    0xb0d0b040902060415020d020c0a1214060414010b0117010306090212010f021e0c071505130b37200304090c0210090809010c1401091103070506040f151b 67
    0x11000595540d03c102e035103020740c40f082035100f0ac401c4010000070b0340e071030f81c0c020f00c0754818001074062003c4071821500308179044070295400b0104100440b42c035070003031265142c90319007420b0402881440003038040b851641404020002961000391000307641e10300b01001f01c0c00710a80002c2c030103119000c041034040e4000061070300703004059840d400c43c08014036041e200074003116001003042501d40742d101a1031304000d1200f102400020401d4840c0030447d8074030400500f6141e9500c40d030390040000c1410b14280e0201c240702c913034007020f50841c0b0b07903201208810029066a00d440c2c1034004041003404030500d14404500c0b540e2000089c0082c102c8900e8101200001c056001e41c2c6000c000340320008280c52504500410300b480070000034034558010300290383c202e80a042000140c0c0042d0ac0d40307600b120f11100041c0d80c45d00300d1000004840c902000054007900044e169982042e150001c000148042400740c0010710003a4145541100c0c81584c4254504c45500c15102c90741580c2d0912103000080b00000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 257068138 1250 257066888 257066893
    0x1f0803090312041a09010c0507030b0105120303090c0118050603040f060509030c0307030c03030b030a051015380307030609050609060d030e03011d03031f0b0d0b04090206041502 78
    0x24504150901003524115906048142c000e03e40b1041c040c0500d41c01703501c45505025100e15550082030b420031004010750b200301d00070200c039410801000a10f03600ca404840c044d500410800ca40d001000c200660601000e003050300050307141d43e0034050b505880d60415234100078048204014040b1000d41075500390b01510042220751a40c1103603917203e108410305418550f0007080740ca8001b0740301780040c45401c0e000380750014481c0f103000000390500a91040a95169202e24500481e0b228284151000712070b07408400c185203440e1103003100341d070440c800095000110f004040d550042c060442035412070030a0084550328540300801a0042510b4010400300515105c0010103030b00742000c84078003c6000504000016960790303800c9401a205c09810358041d52100400c420b6030303242d0001368014401d450302440c0c40c0e242c41c4c07010310740300c01060040c001d680302070b201c0400201003010101c800b02401c07018041201005900810301915010000940080c0005000980c1c0c09002c650364078410110b509 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 257069388 1250 257068138 257068153
    0xe12010614010c050307170d050109020a110102030106200a080313030e040603080904180c0b25080f0318030d0207050d03060605030c130902030403050c07121a1f08030903 75
    0x1101d03040f165000090803a4002c100d80004511305215003131542d601c060181c0d107042c41c00d42098040e118280d0114030394940100da51121240c100c0403501a0354400c50007103017507600d0448000c00359011010702601d01c08001900560089044c00700c04140307500110442c2e504c0c101801c1c14145007007000c20540004205250118051905002e01c0c01160b40000c095400c2c003403030904100050600c025001c80400d1242455000910858000030040100c203810075214100e04540083c850900300340e03004007540d0385066030009814102901d0f03141408034480c507201c0d524007441013a00030400701884000e10001c41c80da1070100b61a001032850500c2031094403441391004105a0607202540503c00c0481d2050002582c01014180505149100140e040422030b507a0303c1504c04aa00c00c1e00c0940005034000303a00500348008006142c0104591200080d5421450303c8814802c07600c1080b2801402d1503401113603070200d2030140000e00401080400101c0c942e54103540b960382e070100c040d050203402940c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 257070638 1250 257069388 257069429
    0x90503070611030d0209010513180e01021c27051c30090206030c03041406010605190e090901090c05030a050c0d081218060a1a01030504030e120106 65
    0x15040140200400450809a981800c138000c1c0d0000856a0704000d000e01c0300002c040c03500780085c4020140f180d02403409480c03c030701d1a02500e81b01420401107a004100740700340c461400040b0410b0394442e040000380b011044c07000c0010040020041c40703161031074840c0c402c2823080c00718045903c014014807482a00c03503018020741d400da206048142d1029900c4050344801c401011600a44121a50b8001600b09507580003e2250f04241d034600300080b0b012003000108107041c018001c3e203041a0780200f03007a40c5007d0380100300e84142000090365803003081c0c0d145032150213030040107911103000740050864a4143e02c40d80c007c0c010590199031082822900180c0d0342000300d2040000768021000c0d0169460100038481d0380145401d00300c1e040c4804102c500040c1d801048080d0207031506880209906451a01843c50720300c0207481c0d104214500300e01c007004080040b02074400b8a0003030801040c0740e035560505869888c803030100c55400c402003c511805401043d40b0480981c1d0000d6a404407441d07240 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 257071888 1250 257070638 257070647
    0xc020f15180117060d0201180b0a120608030c03031306060f080309030c0a08150411030307030f0801060503014e1e0308180102360910090b01020c0405070905030706 72
    0x2d03115250450002c03200c00d40503512840484011404101e900c1c023685a544c281580ca0740e01946c0c402c0c0c000f5800da1500d400c03006841c0515802040d22400440c245050184010303103a20014064000d48490f000424003003025a80012008000e69138011101581e03441c2e442c1e8580d4000c0d0070440c4203005042c40c1005030300e05404e601d0260f4070300340f00074a9400c41d02c045a403007400e40904140c88410102603044c10642d0104014251603120307543d0344403511000c4802404c0d03c0703410303003050044c0b00c814401032118560307031020584202d120681c04510022010044500040b111120000c0540484080c05003030300352110740301817188075540100c882e04c402c1c21081000c18100c4401000141158049031540506142d02c882031107500c4001803030800c45540f451314000307034600f1000419100200c0d080100503900700100c0c150f00183e55000840c5421915490030f464140105080950340700007003140d90744204810301d03626001500c100301a040c00c48025140710198442e4038843c1c0303c1c21001041481c410f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 257073138 1250 257071888 257071891
    0x5090415060f03090f17040f090e0319111e100603050c01032409050106030506120c01121d0703020a05100507120509060a0801050901090209010c020f15180117 70
    0x40d641d5001450b0710001d0407009820442400d807103142188001c00d0120300c3c0c2e8a483c40d402d4440d414115030742c0307103401e0910421320101c0d40103201443c1f07064040c8603030000120440d10804800307090140c481d0719800d402d560034440485800700302e20030710040c02d90300310700c46115881c6610305d0811181d000e60320400c50029100380e0302009040d43c0100c5802450341d40a07030071070382e441c0b90001c1e031640880405d00f00a2401044503448600c0c0c2e540ca4000400245400d17200703e941154040d101090061b40c1c0b20000340d030300d2341019400e904003c8041d10305158244170754000703025424012070307040c4081988407005a4424040c04168441d5044401c0005c3ca481e200010740100310311504d581c0d040070f0f0640c8030700c000c52007031801403000d01c181080901030550700e440052a6000b1503492303c412a504120901040180503088100198810440c02e000c50307820081103016a5811148460613224240c003150a09046100786c60640c8004500c41040d8485a1488103070303e078003030383c1c4e0000c11042002c0100c3c02000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 257074388 1250 257073138 257073149
    0x2070201090314010e0d0f0f0813021003020c01090503071502040e0c0309010612050a031d0102150612010c050705010c05040b040b09011404060f0801050607110909010e0102070305090415 82
    0x24101c008000203048075107608419400c2000000394140c2d0140010305040d0700c40314420024619241540b0f8007a04130f100c0d501d414007646091600d03840c0c0403403018603604004001030311441c480310b0030105e5180700390122200901080700900c005103003032a043c1d5980d000200100c40400c0b0500c20900304a00758400d0300d003102c01e400c010407140d44800c0c0c10450550300140559100c1d5480e100c0100300314501500e011443d42c400d0009116454041c00c00802401039001400e156000382d001c11449a0f0340011446140400d171180ca034a2921071f2400103900d08664082a1040d50030318076a108002c2c0c024002e482a54083c40003440341030342c8400b0445444c8218000c02c180200180f00502001c5801c00c041c100e481010304040d10403541011041403150003036440540001d0b2520046690306038014042c3d4010241a1105c0d41020003a581c0e0749003500c0c001038464003504814000460301d000075040f1520046034600219560421810010316962003003240700e0040382030040c503904121140d1441d6040b901d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 257075638 1250 257074388 257074397
    0x50c0f03011505070c0b0903100e0c060d0914160902040501120903121505010f08090304091503120f030513051005060607080f070308060a21140d0c0c0902070201 71
    0x28200761011200c518486481010030000307104940004d00007175021009005101169502c0d044c01d50101071038081a03c02d0030075021305008022072807800018800801718400c0b07444d99101c07000d00698070014a0303843c002070596a000380d0512201800031800556908503401214501c503241c00441c4140c0c40340388140d60009402d20100b00882c0b106074000e0b04120720a01c1d03c960413992401c1040240c5091070702203106090341d0b000c20041c0c3d681000902640c00301c1401d285500d0b2901541c9191030740198400d04c1a01501c1d8051348030302404442c40700024690100c0c544c03d146690a4000340b0b262248850304000c81e1401000ca8242055100881c1d602d6a0150050450008010b03a98024000142c88560030042c20b001c1d85002800103000303041340c0c0c04129002903c80707003035060060070504081c080030f003d0703c15a14148005540032103032245403080302a04900200192071300280c04e4141070081c1c4054010324a0b1182d09580c803410032803a041c000c122600141e51950454001c901c1007120090106 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 257076888 1250 257075638 257075641
    0x80a390809060a0c170a0608060109060302130b060f0f030403032d0b06130b0c0606041503080c030708040e0f101d100e1303110105060105040b0313050d1101050c0f03 73
    0x1044a6040b43c0304c58141d51a024a1844049070001203900003901c100c60450707202c1d201400608010080c0500401c00000248029460b6401188504e9103090b1144200e5880b2011616191142411036003254000201981c0e29031440c4c040d42c0f16a0802c0d40d003103002a0500101d022004030158002c00c0040200c0c4000c4007100c13400c11818000e002001030700d904541c3c00d00103c40303000102d00301c0314001e0104000d8a903941070030000040c14001e0050040c1d20503031403d094891640c00d280c5454060301c0c0d000c0b4105641d140c040000b540b0714020400f0007000b40a00140208008025a03a618002c0021001025907601e880e040804055401c0c0503000c0301c3e2815118031070442251800342c903005904e8034200100d00e1b40b690f4400803e5082111788107952a20030081d041050f900001407140984020020001c508000b000207080d4800c501c11203a030581c01101081045440b84c504a140aa12038100e4202d125200c401400b8445482584001c5502c0c144c002000e0f0642c03002101d0301c112103a906d20340346 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 257078138 1250 257076888 257076901
    0x3150609020f1801030e0d02070915060917070b07060b04180209240a1e0f0e040b0403110a03020601080d0c1208041a070c11030c010c03080a39080906 66
    0xe140c07881c21041c105030b25011b01070703c6103030103018052506402c0d17405032021a041c00d6a000c20340e5000f2a40c0d0f1040040c04004004e4554415038590984181c8400302d241070f005001c51510b000100c1c1c000304506840020400c080028580c002181c1d102d06030380500080f4181c003182980031520302c00181d0004c0c1260000303231900c11008d00c645c1d019501c0420596204045c08081030b94500c0035040402c10072004002ca0031042c44882a400c01440402c1d00b8201041c00c101030184410406403008101300700c0d200119040600075843d0a5015142a0880b0a984040d05000795620b500b80701c1c0420314080c002a000f034861013030102c440c0c032a811107404240030080000807a9947d00007002a2050078601c12020002605029945e000d80c5c0d1a5a59100040702e03400c00440d06c0000200a0b482a4400484402030780d8000e40b81c8240316402d42440103069884c849550042c1c0240603003004010351002d000300940d80040030044024400e010070b850f100e121010b050b2030312042651001e01d5540000001041c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 257079388 1250 257078138 257078167
    0x714040b192102090a030602071103061303050d1508151f031709032b0206070f08280f050415111603050d09030e1f2102090a03150609020f 61
    0x5894401401c080341c17455594076960f049030000c4004071a00041ca8010310b40a241c10003959410400605030510a08001d6030051300394400c0f10038214483e61030328944820030300c1e07110b103d100808403201603a034040c01c51071030f8000342002180c50842c504801120301031100031100f07814007525444005c0b13204080900ca0340701c8860b04095091275140c490116004070b6907901802c2e00e0340c0c08446000c2c0d15811020650080d09114000b0101004c108840440603038481c0d00482d0207408c24445038020342d020040080c9000f41d0184045610703030300c07810502c03110150105640031500c81c1e801903c181d601031a4980c10401925218130068034103001c14416071101000185800d081b0a110741061840c10b40802120019180160000d4010850514208010381000c404610350100076190204410f1180c010240403a081040e004542d062007403828014840c01e5811126081e40091404068541d00d10b4400e412a0302c40704007180150410500045004581c000d503415580c1d03d0004a04082d0800750400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 257080638 1250 257079388 257079397
    0x6020105090a20150301080c0d0b040f15060f08060115080403050a030605030a06020c100504050706050901021513050d020d05030601050f07020a09021305030c06030f0714040b192102 80
    0x1000260750003c42025541c0415246800c207001640c0d0791250b2502c0209410180180d14040c003c806401d58000000e110301c803460340c00f603070055104001503d1418520304814402019012039460300001003402c4010841e018226540704045441e9681c81d91704616902599002c0000811101c1d00407600290089000d424a84903d160005200e42e840e80000d150644122084e100103a002482c142075500c1808107001c0042c481c1c00c240035604140e92a5030b95280c052049108000e0041101a02688240032044a03016110044101800c050400c014030186a40301256244104d4003a40003007800404d801d4071a000586a250659a6500054800741e02000b515001c8120400c0030078016640c01040c0c0780a07204003600161510a44480a11703135034403e4201038481c3d406082c010790141c2ea00e82c21241d1142c820814040c80c0e0f1500d18081e90b2581907141b407040100e00101d0301044602841024210800c1c6484012850b01900032007a40d10b60300e0349000ca00d41725008201807060090036002070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 257081888 1250 257080638 257080673
    0x8060708060607050102071b090b03120a21141605090d0f08160b01080304050901140d021c020108010914041115040e100501020c030a060f0908030a0203070906020105090a 75
    0x750f01d031440a42c1c82508a0380205400c40c0d4080101003002c41200d100403425010b040c0d029030401c41c280c00030000070307510050050902d1984c0c0000403440e40e0148514040030521000e190301040c02d9014400d1200035124801d1000100e00740e6100017140c195001e80100540c2c2c90503120607280891442c14400c0c05100101c0a449170fa64103032001001441d0a002090300110f04285409140c03010f103410b0540340010b9019012139402071009000d241da030fa03181d00d811030310030075141c1010041c480c0114101e42405080030358030083c1541070301c140c0d59100400c03588c10b42c800d0380d1f601c00710703a00d6040042c00c403a02507141c0840c492420340021f000030f501021040701034500030000844200c1140210b80a5071007030300010304401040c024806a4103002c600b074400380009001800c0400001400b180d40e80040034800780040c1d444c0c2d0280c0c9070300d10791540724481490304081c1d525580d10300801c9080c080e52080d6000c1c0002074122100280007441882070a004400810140c45107022689802c0209070043d44030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 257083138 1250 257081888 257081899
    0x1902121911040e100b1206031b03070b1303060908030a050a050f04020609010207081b12030301151b0c0e04141204120303060e04110307060c02011209081204051c090806070806 77
    0x5c00d2849260010b4100340915200d41d420620b0310106140c208a5200105180812030b003010a60b02d650108002c000d680030108803585401028114050469030b903030000c2c0000c2d14040d940000d1050800085104403c0c1c48014011034444030004030480300225906030118502d0000f041c0140751030402881080014070482c0c080f251039403405c80c1001d4908000c2e1030300e0600700b460032003035050001c541445085640050350a540c50403d10f0320040490724295000c00070020b8920306171f10404009404115000724440740030356211180804860f48c10b850540f012030380384110a440704000254050580001004d2504052900c50140740304071050000301c00380342c0c90720340114400d000c644220748120b0007800c800c2e80d007014010606040081e9500400f0801c11070990301300250743c2050907103800502c12100003410f640036041c10304003801003541c1c060802a080041c401409400200c8000400d030701c0f401a090141b1521040c5c03501c2480303100e0818a50000e4000820301c0340180c88156000300e02408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 257084388 1250 257083138 257083171
    0x10030504020d0c090b010212040305030a0804080d02030f0109110c150705090d1514070804020d020a0504020a0804050607020a050a0206070f0c0b030415050705121902121911040e 78
    0xc0f4101d0558807900b1400e0305039038413446081a5a41040304100450b00c81e180340b45000e05680380c03107882c1c4c45200980300074003a050020804101290040740d060f038455034011900c0381444015550101e03000e103c1ea4103041d00303000303c24000d01c2040c0101c1c1c83e101851320045c100c00c00f44c10410803030707040c00500420a0104c140710045254036001c2290400f544244c28200c1c1208a20b50b0050480c1d200505280c610100c0c5001c00c800e860300300703140356001a01224042604005840010310110050700a140c102e400410480d061071f03082a2170b41c0c041c51040058a105940303400040340c0d9001040c10150290380402c0e07000004d424900011b000043c099080d014820440781c85031074031840a40d0006202c550004208030501405141c4001c0411031003209112504101c1c0b0000c100740140c255454020322481d011030a8460416000e900d0380c450394105544501e01c0d0200c0c080c0c1a002140c40718103071000c12258007615a01882600e00f40c14100c4941c50034107007000100203010400606d240c00450900ea07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 257085638 1250 257084388 257084393
    0x40c0e040c021c020c100804020301290a08030a0203090f0d0507080d020105010e010e0402130b090702010605040e06010b400305160b0d0c0c08040e010806130210030504020d 76
    0x5140d0481029800602d001e201c2119210708107049041e95500b103410032042850259210b01119401036210b1403c41f56a4544c1e00000e4014600f801c1d0111030010a1303041040c107001001000d001c024011035042c800660b99140e86606e81c81401101e40041c0c0040189032600e2400071042444505c01801c6c001082d0102d54800385411140d410000300e075884010105101e5509000d00c602400034510004015494204034100c4400040e00003031103196116107540d91420030b584038880c020780040400f0500c1c28540e03c040d00904041c040d8a01460030000c0750b4030f01e0400069214100c41c1c00c00503d81c0b0384504e04c20203071780148003003032092421900c4020301804070b500104014a09814120340600b07043c03a526040c0d190903803483c008003941100f8501080804d480310295804038204d48400300d04402002401c07280f0203102180148003141c04140401c0106024003081c0c1a111200111003c80e11a02c201401160380380c40001e5010b0070a207000f80b80c56120350095030300b15101030010415800c0340e6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 257086888 1250 257085638 257085641
    0x504020403030201051f08061605070c0e011d10060e0d0f061a100c02060d060b030a020c0f0f0c13060905090c04060b0a0504030f020604081b0f0604050609040c0e04 72
    0x660090b00140e4448080c00164400c3d0b90030403101300603500101c50020310b4100d20588a4800401c414002d0781140ca00c89440c81c011000c540c41e440e1b008030f40f03020158448448107088032f400c0c0580110882c0d4015050b4541005400890040c404115014000e40c03401c01e0032110315032244412900003010468120001d2000340403204071030b11400001c50041d0301000c00d540f0042c0950145407090a4501c0c0154802e5046802c1e81c50891f010303030350a0b03602d5000c408000c0140030680e0040d00c820b10000304001104545038042d0650034140001e850181c913510100c15a42c00d006801c1c000a41c200b24a5580d95280c4542c803681070b0300712150042040344d582d4081508440003100d22680079003110542007928a0244500c001400601d03180d0f90070030005040c000c000d8055400f0091060000001000039583c1d000c083d6402000700f0030403554580c4403a101d151304144500f0000b405202002d809482e1841c14005840617164086c2c02141400703216030070000548658100d0100780040c2c0c05061806451741e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 257088138 1250 257086888 257086897
    0xb07051306030603020f01030506010f0e0f0a1202040509060106020d031e050703091a071b05280309140904060f060302030d020a1a09070e07020f070f150f121104050402 74
    0x982c600041d4280340d80184164800c2120310ba504052806040050302c0e0703081554002d203c42079152403000040c440c004902c842114006917a80603016020028040c1c0c100d00c004031859100380e50511660320380f0050113940700d40038007845004d60004a1104029440303a0300c000107c5006007004110380030341503944000c44505860b01c0002988850540c030604c0340b0350f104641703440c031048201082480c0005c401030038014008140010030a003201d418051190070040301f030355a11401c03005440114881e07001e04c0159141a82240450003d040c000354280803001e40107004030010348044400c0d80d455403031744010100c0b150503906003643c41d1700c04009070b03c041090f200007243d150001c4c0f0400b201c0e03040840c1b10040d94143e024900c3d072201c0401035102d6003c40c5c403000b00e503940c04044070603403a03819081e4281002e00d80c201d01248108480018120782d5036040030708889001e40c90008a07186030008981c8400140c4c0e4900c04541443c1e040c2d0510200c1d64081ca0198013040081c5081075100c20006003a60321 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 257089388 1250 257088138 257088149
    0x21303030816020d0e01030e01020d0204060c021804020306070804240c1409060d020a090e251706011407080d0c0e0a080c1504030204052e0e040b070513 67
    0xd8240c00c004035075000c91600b0081c600030f0300040181c4401e8031001402e801140c00c00604040c2c0310941c03a040300500b501a25001000c0400070340d00c42d5140c0900800300c0b400307500e0503442402440805131044034212200c5014075000b8001d007582d81e41c0c4100c103840c00340000c4c02c04c4600c03402000107440e655600c2c040c405121071651340c0204543e0704006004001001c428600344914508100d0000c842c2e6840c000c444001d01e0029026890304c5950a0585d408a516403206070400016020002e4000b07007141100b9138103451280340200c085484c002140c9940301c10000c40ca15403032000200d0001d43c0201a48410b005403241994607103070704d5907508a403a40000020300b0700c1035110003503000d0250b004508180b0350769003a281c0c54003880c544007841c0d0369440040121070040392800d4131804040c0207003040b14050b5401510034800c604004d130f1081c0c0140c4162054680d04203000710800c4203404150146400c0390b40c05840304016032502d0302c1d01c8103219400703498001400402c00c10700301c1c4d030340850488800410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 257090638 1250 257089388 257089397
    0x6010507140a0f110a120b0c090904050312010909020915030304090218030c1203040905070c02100e0315091209031501030c0e010602120f03070c05071e1208190302130303 75
    0x400f00c0c54443d011810901d0b0700c034440c00102c0010301042c00e200c6a40784116802088042483e01e4154503400b0038401c4508103078025140604100c14003070300200134408418000300d04e0503140c5ea6003400e001107842062000750301240c84008291920005100f0415403100282500d190079503c00c411822640b20307083c0144400211080300c1840e2400384100c4c04600015103402481402c01c030807003500c0e8801c50140c0f1500c0c0d5560340100d042d03148181e0012a206038040c2461003482d40034003018040294113403401d8400e10600640340c0901c0d00900080b405800c1070001460014070000700d03a0019004052940e8140c803074054480042941800c60714000c501451255a0390703424040300900703050050300100c0556005801d101c08401500d02100c03080484034489585070307200d2650440c2c402026030b0300030f05180300ea0580401d0106515402561241c0c0700c2e49580040317640c60319005601e800614015043c0003045c090800c901ca90340c1c9007000020414600140f420080109400b04041030b60070541c00107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 257091888 1250 257090638 257090663
    0x30f03040f050f061e0a03090b04060516020a150b03030706050a0b100f020d0c02030f0f0d02010b011b0308070c210e0315190f110d060e0f06010507140a 67
    0x604090500e0001d02005035280361619104107022900300b805c1d804440d1144c840012041d050034072903400041d03511351102e040c1c842c0f4101410040080d040994101d103a8403440203c501100b03000059020101d98003d04c0102c60038442c0c00480028080358203a55010f003c204111000605d151082521034074982c1c00028180d480501400303c0442ca01d0342010500001d1545840860b400047e4205c1c200c00310300e0b0031003c0d020148080390030401c481c14180032503c14021000400440071400310080c010950080040c20600d800455610302c1c1c46d0030302c40f041010040d410020920840c011a40702e002d44c10a40000300e42030340d4031620310349016403003080d00d02050002e141a03030388800d440c14100b0b4128018816940c141d01c08100e8410044c12500503541004501c0010f070655410256600328503279405c102c01c107042d1454038015440000c4c0724003540d15050000c559003056600b0580118034403c2101010b0f9165170055a590f400b50806540f20040c48200700e0020800f00700304c002d040c2c404c003000f06a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 257093138 1250 257091888 257091899
    0x10605060409020a090807120b07030f021306030c0c21050405030f0f0105061206060907020f0f060105090603060106050d1509110d050c040b181c03020f06010e010b18030f03040f 78
    0x407281176400249285d00608000c2102e1190080005e0105d80c0201e98403841d070b155050160010700b01800315004003800418010300720b030303120a100402c4803a2a2000d101c014020282226492081e500c0100100f00c030f40c205810f008c0103a035080c2030541032403d2091507d51600b00107490b0126408030350000d94090700c1260400c0d0401e018094014405803000000b0104840c0303015214100100401d01035170440f00010123851007008100044500b504c10350717485e03101000c08541c40c0d04090284a02414117100450705500303001880b036040b02c006032798050504495030350401c05442c110120b00d1348140c8544002c580000c0a01c544401102541c00c2140e0b034004240d203010503228010505000e0040501c0100403944032481226072800785418040651072a1100280584181c03604889020301c5009c0c0401c20990005084820710300000701320340c41aa6074034800b011154090048002081c0c06001c80a0703c11200440e0b40d100250003010340b40980700800d03009103107800c95401903100041c229802c020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 257094388 1250 257093138 257093147
    0xe030a020a080f1c120903230a0e03030c030304020108041502030a020d050a060602030405040c0c08191e0918021e09040c0810030b130f08270d0212010605060409020a 73
    0x1801310030002c1620031840d03503a0b4040c050010200c4810360b600c2d02e039103002d410103100f1175004420710300c680c04a002d0761364070400c1484550002410078000c100210003800051600005680c4140e507854010351640d0707180d600456807200301902c1106c90001140c114142c05285001842c400e4145103801a06c80c442910000c1c182c0c0e10140122000720f2500c0e04c140516076000c4125010f0340d4080c1c03400700e851500203e0445090341c003003e010307281d2040800c1540c1150105640042059580e65414040d8903c500c4134500346c7c89100c03071201c0410b43d011010020002e41c0444243c2d000d000050041c107001407038482c80141079035400140c03022080000c00a4042c80d01b8440d250f204071003441e00c2d02070761404030440c0035039004500029001c489070000141c03800a01d41d10003d507243c0e00580d40091015203161880d92074000c065030500704030342400100d01400585140e040b1010340103005030b00b03c0b15940c09010300d00c810345039500380039502c40f01c000c245038540070010002000a450010303038900c482e0704001e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 257095638 1250 257094388 257094403
    0x30706052221050408010e010b04061d070309022d0123030f10080d0c110904050a021207080d0207050301150510030b0402130b0309060a020f0a0e030a020a080f 70
    0x41224441c042500480c4a070400003680b540d10420102407042c44100690b000d01859001c0e03c01076003400303202241d5402c19000706103031020645081c0034864031101c01e683d54100c000d0f101304000ca00140001c010510942181c44080e001a20403210000c008140140b19000102449c1104403100c103011840e507444900d418940c2c211184400d031050f95815018550301c4003500c80f4501541000c04282c90401140c0e1080c010b1060104690006492200190100b096007205985116046031704100900706488801e100f141c1c0000680345214090f0708100203035042c540c41a0081c841c00d02c2c04284803400b00400b03403081d003464008061061900742094291281001c66030907201e000041081140c68811512480c00391074103011500f02d01c902c0200d0028081d03094060784001c000d02000806262441c015402050254180e8500e83da403e030340141648244a41503540c136100b0440d903a0401c0c4a00310140d080e54006041e141890065000140403008541108009030400114042c0502e410030900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 257096888 1250 257095638 257095681
    0x12130c08031207031b0810053109080f07030e09100503010b04060e070c05030d0c05030103120c0b0c0904020409061d100312050a030b0a0f060e0301020301030803011208070503070605 80
    0x41c032031000913428120585c1c1c0d100da420014001c02501055040303115154000190030043c000c001c0d1018403640383c64580d445000e144441d442100082411442a800380032100c6801103110352500230450348580240d40002015000c10507030b001d14040555580c48100d005a4031608101c108030305100400d42124074050b8080d2007603103071420030491400c00c120b803554000d03c1420b02e50040c481d02c0c20b140381184918100c000803d881c0c003402e81c100503002030156050324020034106060b01001c400a03074480c007201801800c103012000024141d220050010041100040c10150620742d4448005050b42d5098002c42d450b24081402a00c400c051007901a501c00140d50324140406c2c81c40c0c80e008944494188440f0400c900040d00e075904034060380004441070b07009400e0458040d031ba00304404180c0307a03c1c0688000640d09101c0b081d00f51805000b40d9050b03c0d007000c0ca00f131071039180401001c405030006d80c044481240a028481c081071041c006441c10a005003c04500752410b14502d500961444002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 257098138 1250 257096888 257096891
    0x102030901110304110603040201050f0703030917070515070c0b1005040b060f0a050d060302210f16182c1014040204050a1518050105010903050312130c0803120703 72
    0x20007000c14070090985e41448416280c90b40c1d40c0d2207a0004898034842c8581d10b826512000540070201a49030b8040140036028840505280010300401003ca01c2030001c054029070000b40074030f00c100851412180c000c2c0250a2414070440f0540ea1100d40d01c900701d541180104d5036100030401410f2074060310303074111001c0b5030035403a0400e4040c44450f203001e408200400c111010400014980d421341c001d5020315001070201070095185081c148004600c4040c801e41400f82d1040640600000946d0003d00298000000210344c00d11824000e005903843c4403044441d165a03171803c110407980125412120b140000004131020038444500c3c06a0060600e20440c0c80c00080c40aa400c40c481c0c3c450304580e046401042c0354490510740006061641c10020141011520000791050099800042c2009105083c130a83e80e9901c015240a11f45102c05007240c1c00411000e0400c0c0b0f10340f15171302d501c41e4800d80505021005525035844004043e000303d000c40d4170003d0392400e0b81d4003404600ea070083c042d140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 257099388 1250 257098138 257098141
    0x210060b12010e0402010903080c210c0c060903010f0213152604020f0303041503050901051303080a110423040504080d090311011407090b04051e010302190201020309011103 76
    0x4000c54065051042c0f040d4150500049000c581c8550140d8000f96040242c5507102c22010307007446c0e10f03405680400050390f40c1440036408009041b5095070600006080a0b00d4000407600502c03016500810140358595624108003c3d421094405407109034070800c6010b4401341003501c2d48444035411402601801003025000b203034481005450041d10018044c0d15101e03031a684041510881c01070061645408041804148000d0f00600c0080d202c00550f4144803a44440803014200c42c010346000d0641301c2c1c01ca83c82d0740400c1c06400c005420405940001580601000800d81c058015801801c504e2448d05411100d46800e9138215070b10b03107012030302000641099940c0c000244950803040c601952128a601c044c140a02121010f030001c0000900405850789220f00081508441c0040440d104100c00b01d070b0100c0ca4170541d0160303140540384100c1a00e04d801e05483c445010317852913041540030002900c10000045039000450b9a43c0c00158490074102901b5007901d07071038081c64003c01010b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 257100638 1250 257099388 257099407
    0xa0b0f1009020703031e0227030d1b0f11011115042607080405040c080114040f0b120d020c04020c03070f1b030b0a0b010c20030c040c0210060b 63
    0x5054421a4000c81c030041c2e903640c46280642c003a1407503003200c1c19520009008508000c50380d0b00203000381c46d40341c2441c404154680c0281c004e401440c0421641541c06000c445000f51300130b0721f904c80020039512103880c003895a552004810405c20070308858540c03419408000c1560007840314003c0a02c0d00d80540308000c00c2d400c418404032002003000e030402c80c00c2b50101044280c0301c16007062210aa000441e565616810aa12503038030610843d40111b1500d51188101445614071a042c3d401900e5000310520029040002400414110211141d6142401d80c010780d00e4141107424400d24002400218511002c00780c1070150686983d40580c0c01040031003018031010044a40c59544011803200c1c00300d49007014010620789190104c070614003a80d002c814040c40501107442012155400e00484c40e111004640307034040300d000180301400d2081c03032456580c0101c004501e411400f5040b1a4800505400582650002440f10700583c200f00b02006080d00e46000c0c40303000e40154130140d4038004018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 257101888 1250 257100638 257100661
    0x50c030103020d151d0601050a0503071a0f1606050a20040614090a081b040204050d081c0c05070201030b0a05210f0a0b0106232710020a0b0f 62
    0x440f00400c002e512504403007095050b6800003004140c1465040500d001003807006680d100280034461190716980000140c1d450001144415150310703101091101070903007440d1b10682c110403030040e030b03070102440290f45104101621062241c0643c60104080c140344254604540d60254545000944008080345020800081703608440741882e00103410034091100008a0041c2071031561310206640c0c000920000000d02e1584580d1582401908034092104000407031080d4801d50350024020143c0c600802c09030005000c1107002250751440000c58810050102c80410302c40b480400c03c042a49001c0d960306110302c40c1c00c0f204c20b84161010f030303061100040c0c1140010342082c0315074514247c0160a888140501021044004200c0b801402c2901c2c00300c035216000d000307480014880ca840650f042101094609103260030750001307440e01d81a0182045e03910b0040700c0300110300d1240e80d020952510f83e048403082e00c410340d901a210000d01407038102d145030b40c046d041065020350203003402800d0350384c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 257103138 1250 257101888 257101909
    0x10030b0a0e1e01020d180b0a0501050108061509030d0908010605030a02030a0605040201020a0b01180c0e010f030203060d02131a0603070e010c11040c0806090604091e02040615050405010201050c03010302 89
    0x661841c2c0700c003606400182e501900c0341d07420244445003010000c06042200e4146803194034800e0034446090b80d610328480003216024410350380002c080d20013280580c10448005008500310350780c0b4900e001c910a02013071501c40c0d007910b1480003865405040116a00a11907200604000c80c0502400a6250002560398070064400351509507664003007400c40e03000b0442140c15952041c14508950784d0790780342c541038a003094240c0e900f0754140303a00d140100d171203200f854401c2501611003207600d44c04c0c0c42003200203400040c1651340091002c7c403424090307602d24410100c2c4018085010400c01c01a032259240c58140c051a140100300a001740661030b9044050036200907000c0c44c003800c2280407030070079000c90b4074810100c98010307140008281a06a201214910404d8242c0320018030703884040a020885040081c0038200c40d000c3c124090150064030341c1140c0c4103000501c08502c150311159480c600c1d50346440454080764002404000a51302070041646c0321340c038070242c981150b14540101d03855421 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 257104388 1250 257103138 257103163
    0x9051002030a1506020604050c0a060f0c061814010e0303010b0f0a1209060e0d050306010909020f0d020c16051f03180803090a0c05060a1e020a0b10030b0a0e 69
    0xc010000400c50340265208410499400b003481000966070080651114030944043d44c00c3d018010a034444c90905034000c8013114200d9070b600d051940c03400f004403402d1000d03103821910301c1d460740005034140e0740310100d50040c540a140e03000039070069000e0590848440c1040c4504580051004110010b68a02900c020b520300034103440d51038000e40c00407500c1fa116201c9041c40e0614000100080c40260b42c0652404a0204100e40660600e41700589190100b1282240010202c250600c211009074015010000151140c0e9040c0402c80c02c043c810390b00301c40c60345140c950001020340c001e1410a250400103003015142030b081160b07802d9644071130800d5040d14006142d143d4002900c007025000074140c03499008a0a942c0301d00f448880903441d8410030310107940004643c000441c50b80b818504403143d10405484040c014240c0c0c1c412141ca804090b02160258040c00e505600424003007924144203400c1d00134a421110700314a0b2607410418041c050400171840c00f49085c100b46000200380320f0400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 257105638 1250 257104388 257104391
    0x1501110c0a1206020c010c08090c0d170901030908160515040825150c0306080102030c120403110a030906030c030c09051302070c030503041703130b03060a09140118090510 75
    0x2503e0801c000648901c01c2d07122000d6191000e0011041d604c0b241090007403541005450008055404020300d410b80b038100906400b20344c01c012154280b52000402c01d48606040216129285460340010340c0c0156281540000924841808015007071020380403000611086206c141041c0c0c95000480c06a014182080303210f803050410340e02012040302c841140d100402e40d0b60001c0703a41094018016510942020030308041d0040340030307101030098910645c00d429245040400b0035050000704030300580700b502840800900f18090046c14000e51130258041d896a00f4041d04d0084018110349d000595401010300e4180003a4a46a0003003041003201c10413a8800c1030b8a8014400c14000e100f12440200111049c2800004101d03011010707000300d03000009a400300e03182c100e546070344a10600103c3e10012121703a00a02c03010103103201454000b48050214030416440361084021207419401a800f0505580c004100220402400c0032404200140c1400340000c01d6a9003a500d400e00f2a060302520b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 257106888 1250 257105638 257105669
    0x170604020607141f05130f02060702010e090703090b060109031a0c0f1201050a1202100c05100c020c0a0512150c300c0901080109180501051501110c0a 66
    0x1100200110042503d0f03401078035001014800e0a00150040c0006054464206800a42140c1000d24851030b0039070409801d0342495416402c0084540c0161002c038180001ca00b84900d2a03211a0706141c820441c1d5100002d980140e42440e26008070001c00c090b04120843c10140001803030601080d061904040c00100513444070203250b050360091100c0c0c03110056020882c80071284503009405c0c1299419910f1149554860040c55000282d03900041d40140a045100c03023407070712403101c812189001d50252071240f031203100040152440d1031001001a440a040e40d066868000d881700c4c010b0000f1101d20b01250b03090820303603464800d002c142884d603203d0500080c06500c40c2c94101d03114000c01a84009c41a8152010441541480003070052242c10360030014244d6981c6000311541e040c8140c4807881c00ea03103003801100c0508100350000c211090340304982000035509000d41c9018846828500080050390400104070107000d0003070039016440482c80e0b00365504c400c25000e044e218101401c0d6440c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 257108138 1250 257106888 257106893
    0x80d0c1407030b070207030b10030206040b0c0a0c0e061f0f0c02030a020310240503030715090b01030302060612061e040f1e020117040c17010608030313030207170604020607 76
    0x41c40a107610103005580060b04002c4074a07804281d038400e5a2086415482c2502c1d02c6403807950603400c81c04000c2d00107404220500064040c500604059240c1c90308403604580383d0f581e03507420407085034050f0011589903800d2119074038085001c00d1400c0c040c0201e113040404900c10050110400c06050414004060307112415900c050000c030240540103001c0390b0b42d50710251184030052540c040200e07514007aa0910590000e1414002c808a5400900460421556840701c5401d60360840301c200c205580e600501e00014218104c0900079400303600a0081450640180a4030070840c2850070240e8020345d0402051100c01d140ca2644044150300c2c01e002c1d5560f510f0100400c03810248040c010600000e0743e1800a101108240410352003a61000824054031443d000c4045003070364024a04904640e05000ca400ca50001c040030603004070000c2180741c2d1f00c1145908507801a10058001d6800840303603c01c3c141c04102c400c000b8070260f451f001c41c0c1c0c20a01d4003251604c5d00540028820000080c1081c10f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 257109388 1250 257108138 257108143
    0x31d03030903240105091e060619030b03010c1106040b0a15121b180e010204050d08090a0b030f040f0503040e070c02010f030b06180a091410080d0c14 66
    0x4400c140074040300c400141d49a03101c480f05800b070041c10100d041070b0300007050604000b1040c43c06066040414001e18130700300384000310300350014691604240c00b03000d003105000385407020529401e500d8070000b603013004a20030b01d400c2d43d082001001c00c1c44078040203160b41e440e000414503446038100d4440302da282c4450903e140036001040302c000d03000b00790390400303d44180007009203c1094814102e01e88020300188414100c0c0e0594400c0301600d844c07a280e0f041e125081500402c1c80c0e0072801000600c0c05171140002a52682e10303990640d042072000c03860b0002410400940006803445001311801c40c03030082c69000303c2e00e600a00c010400310000c03490301e081000c10403d550140c2820b41003640580350140000341500c1c018003040c0e000032462003100c10024081d210b110368882c009040301c0d1800c4020801600001c840c46211391304004c07290320000d01c03980a0322078181c210000ca401c006143c1002022000002e005420603400d542290381580d003070a80281d4a8a9020340c04402d00c07148516000d1902d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 257110638 1250 257109388 257109397
    0x10f12080f0f030703051303080f07090b030903040f08030702060702100e03010219020c04050f1501200a140304050904020904060b12031308120d11250b060409031d0303 74
    0x101c0e80e040850504410b100940282d849105550740400c156a1401c07000d20094803010400b90200e8074003004503031281220080b03258408a2806e00f110039682e0b0b4a0300205580c000c4540e01150b41010805001c0c0042c4442540300a0040c8401503081c0006900000d0701071061441c0244038290301180080203a005a4500c8030400380240215141d43c481e00c0034001000018030000018096050075a125107064442c81d40146050b004480d201d80d02d0303015503c04440c0014a0b1414030002d040c51049804061307040c0310f031084c189400360155010070724042030300d41002d00000091350010322091102e91602e008096006d90125091601603c690602d540240302c075020a0381c02a4018501c0080460000001c045c582c15090344010070542c0c0d0318056854040240030043c80c442d041140150400f000e821411611521031300c01403602404030003080c0306442000c80c44685211982d519003d01404003440c1d60701020581d81070041c290903950041c9041da080307901000d43d0a1152240007251810802d44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 257111888 1250 257110638 257110657
    0xc0c0b090d0c0f03060b04230702010e01050924090d0c1703040c032a0e070219110a0603060503061920030f09030a081527070207080303010f1208 64
    0x2030b000d1030301d4000410074a8202e002c02e4481a0a1402c060020f04045c0b2802541408025403448604003400c8030f680c94160140c070f0002190748492040c0c0da881f0302841440d00a85101d8010704074259640741d82d1000191098404180d890700400b0081140c10128070382d000c02c0100d00e040000740e401c03490001407280c825401035240301004410042000076130480c2009687c00386c40200030346d20655603580c0088503100d01c08140c9100030401080402030480d01039800500314010748520b10341880c144d0b00c50462100007900d146c90200b060803038034100040810068601850207021039410100400e50b0b400c0701420740d00c08440c04500d002c140d06419400381520440200507500080103000c0c0c0d80b9050f82003600c1c40c3d8111014400800c4a02100000700c2c0c0603100315071506c000c01c0d541c0c2200010411545110035030000c1c402d0348032079480d43d800c130044d9614100d40c0e24010039074106414024540811500103040c2e44d8400c000500000c40e0070004002101d1070940c00360010209850100b450303000d0000c58 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 257113138 1250 257111888 257111903
    0xf0501080717280b0111030f0703080c090d030504090b01080103020a030813080d120b0904050c09041a1303030b0f0609130b04020705032d03270d02010209040b010c0c0b090d 76
    0x34042e0f18200340d0003031541004240d8803020303048284920701d41c0300e114203d0340507200c080400c00e4200181c00703945415409491f60303040900307040e103080c04203880324540103040700007401c00030701031100e1400e80c0300307000a5210078030f0b0141c07641d0704550100e910b041090202034071880e008208540048503d81c00318010780302c060700b502c42c850007149015101c5800c006901240700d007064242400c5081c00c0301d00612850b0000700800d4028180800c0c00344d6400040e00c2941e40380e04040201c42c08482c4591000d0141c5081c61003402c82050f0b03030030b00034101c40c501a10706204825000c00c0c02800c0c2e9170f039401d5414040045481d045c0245000251b040140000c110503a0424000700d401c00078040c011001e4910004c42000c42c1c0c108a00549402060039a1082344020551007400810506d40158900e00d0a0183d2250080f1900c0c42c2c1105030b6240a00511060006179000a900350560600d40039030410b00303200b801d01300000403030b550b074825162285000740302c0291400b0450600701c1ea501e09094084c5504940ea = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 257114388 1250 257113138 257113201
    0x606030c160507151b080316051201060e0f120a1217160305010b040e01060507030e13050411040e060f0603011d060405011406100e01050904150f0501080717 69
    0x401107642d0410714000d00100704540e1003804802c5941c07040c00345c599480308450340b4617690f246180302c5070703d40e030b80b400002c2100c14490441c0c0c0c8941c840f855070203000c1644031588014419402c1196a0746d282c0f10350b9020340c002c0c2a0a54a000e0001140c4003460f43c13011245803d4420030b401101d41c10010303040d05100f800b644051056607101c02c209140110030703a1703805000a03a00e03400d850741e0a2003a03100d01c0031714280050042180911480c06010b0440c0b0034540000640d4410001900c24901e004140346e4590342c0b40c0510040241c4075800804094054400f401741e141c1402443da00c6240040c22280c04c02141c500048042c0e13003e50002d500c000b10720180c180f440d02107201d0b0b15990b1408035400c6410b03603c0c041c0c00c801d003482582c2c0c0f22846140000d18020651009102c21500b5060302660241400400c4c007031031200c0c0d0b03298015031807415040d41c03c00c284545840700f02c0d442018280d0200c3c0c1404014001e01010f02e902190b0300700d40c819001852262038840e0880c903607035001c801400c007001c0a031050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 257115638 1250 257114388 257114399
    0x4050408131d15011407050307060f1a0319020105030907080d0c110108010510120e01060810050a090c120305072001031506081501020705030d110d03050606030c160507 74
    0x1040c4601c01c40c01501e20401690f40c00901000b482c00c448501070200d010b0f0310341d4014240c1a4001403080500c0303442a2400c0a015545090944405001c56581c00d500c44060046455594081c0c1c040c0a00880041c80c40c6003401c42c584404104040000c0d0422130b00000280b54400200400c500a00045086600c0b12a058100038201e01407400210b6a56030440e00c00e1016602c902c02c0075050b43c4001b014160054544181a00e04483e00c0981d0420b460b01c1d100c1b0850030314000e00c113440c02080c0300800f41904205803030760901160340052440d0a890300c0c2c68402c07404600d10703d1043d005d80b00204034a542d081e00c40c0c10103440758002c985000340845e0807120310340c04004005c400c420b501e50080c1c800f44403d01c121540300c8248080b6000304400103d062000402e2469600d020441901c0180107480e10941c81d000400e00300b41d0303045140404075010f426604a506001c100a030031026151800300704506060000400601c4080c18010345801c0108118006840540180e0a55940881120031256a91 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 257116888 1250 257115638 257115659
    0xf03070905090a05010e13111801170f1b0a0b040b091206071202030a0b150301060f0c0c060804020103110304060f05061005040e150307090501091116020405040813 72
    0x38051980a070b89500d0108860300124028a4141c0b8541685140242e640c1d1517184060030800d182640d24000c1821030210640300c1004052562803c480600c070550304050101e10080e01440700409181d10200c000e101e5541f002c100c0301c0e00d14894020041c0a140740c0c1e8001444070310b441e00000180e010005002448110200003442003000130364001024a03c82019036840e100201c58100200c0d00d5040c0104000d10140e00559125094640028030318240002040358540800341c90100084000014070801c0e8002492010344480c3e0314000d0301049090b503039410051601d1185400340300d090300104007160301a41000c10580024481c59031a842c0c14240600a00805008110258581700120b14242002c40042e503002d01c01c0c0c0ca0329807800e40740410305920f102004145484007a504804000c00f0768003071001c0002800318440208031541000d07042011681c81c00d80b00b029460342007103082401034203100d00e0281290122030000c1e440e03403681030940a520621800e040c18500880f40400c060011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 257118138 1250 257116888 257116907
    0x30a0c030b01030902030c040b1906022a030706181a0a03050c0a05090913051203040b010803040321020705061908060405010503031c0e0d090302030606041b03090203030f0307 77
    0x990341884080e560380c00541c00c032541e1250194058001e040c0d0403042e400c1c0350700002c1e03c0180140545511404031000b07140ca0031025000100160801700200c441a6594203002a028944485005210b40a480001d03a07030012031142c40203000d1010020b44092490010040081042d03481038009040b5010540c0310726402030b0f02400100b89010003098031480c6030407c3c2c403107120f4036850702403800c0d80740410040610002841c10301510709844210001550502441e40a540d25160441d128242464130041d5404140c0014103950320501c000c001003509180304120302160441c4600254034207160480c14103406030810b41e0040c0c00001c0c20741c0d0341058807590503106800c2c0d40c3c990300c450b02d40904000540b4020701c00c03ea07155009000101c0d020211607001d000c0d03051000d40001d00c81c8000c0d81c1e20f509100b07850a400d004150004010425810144121940250f045404122903205a01044070184800b0180c0d0200b56440340038404545081040301d842010b1a80c080d61646815035005104950 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 257119388 1250 257118138 257118161
    0xc210509011205010f1403071503020304120503070f03090515101403010b0604050906010207170102030105010f020a02010206010620030d061e1503051e0906010816050901140103060b030a 82
    0x203107501c0440750b025151040310f050b04c642c10301905a00f8030305070740f41044803070500d60664103021b10000058190000d055440180016840c050f88a28090521141c10040385421a040c00002c10802c02d03500c1e071054840d0f80c08403407800c3c001001003c0d41486881c01c0b07038404e10340b140c2c1203450b810b002c6181c2c030b01c001001c103c0310b504108540054400050509a034504da06003a044042800240080e1034104000d0f5449034041c4129912a95216403141c80f81c07203040420841a5030000050200b942d006441070104030079800280603540e102e0b40000d41d0f8050510400b400c200c000880807940c0940d0390440f640c0d420290044948071449101d28000511b030510070110701c1c0502c040342d00464500780c2003071000c9540110102c034001a00520036070182100078401c100f04078031043e0000342d41d82d10320042806081070500400003036041000191900032250481c1d05400003801e41042969a0307061800d065910350598080c003502e03148011780c0503003103d07044840c428802200b00b00c9a003050740d00c54084a40c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 257120638 1250 257119388 257119397
    0x4080729090f0c0a0806010302060d1b0c020f09010e0f04020103060b0a03150e0903030c0a0201110a030b1e031b0310020a2a030909091b0b0a0e060a050a0c21050901 72
    0x3c44410099060840d1103a041583c00200040001d0720300f0300c01404140d00451000b0031108843d4000c4400910400030280100ba00c1c100d0304015030401c12400c100001095400e91100c0d41480743ca51040d24000780310b01c4540c4040e0f40040c0459220b41c1002d0000c00102d000700e52a002c0c250f01c00380182181c080d0359036041030004c2d80082c88000c4044041d008101c00d03005146591524140c01c240c42c0d12410760b040c150745d01c030f4076800d0300c0b159064000c1c0354105050341c00084032103210381048031684009080304030390030006894141590b0041080980700340311002c0c0d41120104200400d04140c0051307e080c01c200c0c400700d00824a0f40e00060740d507014000b000c000803500500c0700c16480743c0c401055005000105c01f00e80c24818000c00c3e921802026001d40c0032410310000c0201c0591800030341c1c1c0c1190900303400104070a00019040030440c0706542045680328104608013400030610300510301034600f008500070009050140300099040b005002da00c0441451034a824050495840154810b0000c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 257121888 1250 257120638 257120653
    0x90d06200405130612020d030908060c0307110d05161b090902130c08070f12050405030a0e1806090606120c09090a0903080103030e060c07150908030304080729090f 72
    0x1480c603104413400c0d62224003070ba6200c03070780035001d005242d00081b9040b010311040820200322140708004051203844031806580d40da181220f40144003100b890380f10b401070703400000c01c298101d4000b816038010803001d1031001c0840c406030806007a4454013034030030403100707000c00d102060000c2d658100100345402603600d002d00d14900d0502c102160405200c5c000001e104101080c103140c030a6120711020304092400c0714032030607103204240c04c0f01c0c0155270440d103c2d0302c0015401003154124400c0201800c0403070781c004080104141e00c0071280c0009001600c501034800004d0074965600d800d035007101c0070000e611034451a103d03240306040c0d800f03010080e10400542000850020303050040301784441c0d060b503030340141da4a195000c0e0f514064808130305510480c2400307403419011042001070010000c01489480d4250601030180041840b90402c8203944c004200b000085039091301150941030b44000c01014115103042007a407000342100001001c0e5021a0900ca24020006000203403842d0050544015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 257123138 1250 257121888 257121919
    0x7080d05010f12020904020a1e030210090e0f13050a05060906250e130c0c0c050105130b0306010203040f030506040b01080613031808121306050a05090d06200405 71
    0xc2c10329a1041501519444001000501307218407440c0d0450302c080c0031a909261500103103c8101154118805201181d400410035440c03c103c00c01d141001c2c1d42804044e590401d41c002c0d010604c0182000900203103c40412400001c0024000029420a00f9280d038014246001603c45400b0303502c4403502d03c20b1101188200c261101d40b007581030f5400c0f07030300f030101060040d06072900d00942c4d00c11944207200ba154084900d0443c010040034400c5075545401e02c00d858500354000c1030854004074100034082c004022131850464141c01951407014001c3d0312580c500004078614811a00b1035210507401400000030001c002504a00031803084181401c07070b80e21000c529544140494105a60708081407202000c40c0c0101a074041e103030905004000c40780d48504200e860080f00401d5220303083c400065461079a000944204007400141c90443e2406a03403400003041070140d144c4044c0310f01110300821042004c1940720b94550f200d01a10b100300c0134690364543c0c9035504144906800f038290342c00f401c4207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 257124388 1250 257123138 257123159
    0x3010c050a030506031002030a09031b0b040f080f07080405120f0d03021b0601030308070219050d050313051c170103020303040303110312090303061f0c12120207080d0501 75
    0x4428045944560034a1203120007180901800741c40745403d80245160f51580c070440740019445440e000b840420803410520300140b40c1503417401c1d2181c50000c0c440105c03002644510b42280c1003600506a0148010f0504140a543c8241c5c1c181d141c1da10800078015082000355006007041f164115280740c440c02c0d17140d172400c0d2900b075210894090ba8000320342c40d0484502030f6000d030181d0340c035100a12050207003540d8480d01e460130a80065000c15160020070440c07960400c42c4100c40d90300b040141d400500e01e50344941d612907008840d502403050100010f1351011804112104494002c81121084000c4242c1040d54180510440700003810b40e4a0f041d03450300845002c10704996000e401940792a14585080700d5031100411914441d003c10000300180c1101c40d1031490092440300c000d951b0340e00340720301044500c0c01305075030070500c1d40c0c0e11100d490a080c3d0042203e421094022100d1100c01600e404104c4a072540c420108108920200303c030424096288003804484500a20410041c0d8a0385403094 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 257125638 1250 257124388 257124401
    0x60312050712080c130b120c0f03010509180102120f010504020c060c160b0a0f1b051c0f09030804300f09030f0615060305061003090f141005060301 65
    0x40901c0c80491124400341d00c83d6031090b84c02403d00600c1414640710f144c1c0c02e40825890b0b80030384500100801c10302c9039029540b000d503410601001d103a6107020640d10b002ca0160005119092003041c2c440005019020610001603030f5200784c800171991040c02d8250089074550035035202a2610f10040041801d040c2807084840c511000c4008240c650307507208807240d80b5803044500c0c01046544030b03260400544500f010034042c840c80000824044a0483c41c10308440c400e030300c030401d450b1485034808151a00300301101c0a01d0804070414180040c10700034840500071400345640740c82d1074141500d0905600040090049100c1d1038030008030000300d00120340d01c0c010324550800001e5511901d00e071007402400b000080035018103000d403469070349403540c102c2c941e0b000c8410ba48c650385650504030034010f0840018041c1c400703410100040d060510101380020458541c94003415030f584111400d00c0952000010f182d035100c4031000d11211010301882d105c0c800420790030403541c2030801007140c43c0b03410f00802 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 257126888 1250 257125638 257125643
    0x20f0f0c040506030a020d0b090c040603030c0305074205040b010b072402030403030f0e120c010b10050703020f0a051027110109090b060304020d0804080102030a0603120507 76
    0x400c940320081040100070280948040d50520a4907445c10045c1c07916002c5160603070140380c01c080d003440c1440030282825890843d1520440c0b51840901c00207070031504099820ba003501d8480c3d00c0c0c03c1d1500d00700f4000f10000a200008002c5601d02c0b9402c848234108000e049100c0305c40e18010071007000c0c100015200203880c01080301c2040700c01400602840c602a144050050a1a44483da0b444084024a1910400b040111900041041f00b89601401a0200114011402c03c42121080706654486075200e1815a41c18400500000d440c0c409402030030060100504c41d54054003036a20107860340d032181b0030840160082d0340909031a440081015040b2035000806012811040c29401000340161280210f201d0b000100201c510780d1762001142003588902d4000705610004400980407031000e9011108088c2010b40c014582d46503101500e8000d030381038407803100f07071020752070b020280e03004580107206258030120800030300c44d0307964000c2c40c21280525800d0382c2e441000c031800ca486100340f4001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 257128138 1250 257126888 257126893
    0x15030106110313060801030c12051507030204051206070311161e05010e0f07140a1802090d030e0f0907080601200a0605100b0901020d0e040f020403050d020f0f 70
    0x40000364024a0307520200740904042e2483d112001e0611002c1c00d0040d0052000600250014400c200f0141000009041d03004200ba07241303001070703a5541d134940040d140003001d02c90180105128500035010f4402070907004008020741c140b208225559190700316010b40009050580c500808002441210380c0c010024209404000e0a915101c00c90303020169407183d0300680210b6030b000b0801c00c2c400c044900ea00400507101420f00c2400980c50311600340c1018100c215a1000e0b0106a070f51110100c045480c0380c0960f180305003ca0721100000d000e424900c039041984d10100d60109984804807104c5844111102406208150240b0280d80720403241580851100000301d4080c1d80540d4a945403142c0400c0000a4607043c08147e60078a200d000b42144d55945070418400ca01e443c02c00108068001e2890050500c0b078a4030001303656036080306000040c0101750003190240c0c1c031070790800c070078000c40d4071750540d540e41c8d43e8a0440e5076843c04122a0005016585910001c17803408940b640c3d181401000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 257129388 1250 257128138 257128141
    0xc10090308150d06061205060a0204080c0f060d05100812070b01060c110621010806060f060307030b030a0c03020319080d0c1e02030310080a0206032809110f1503 71
    0x21002c01040501651540700200301041e0340081c560703000d4000542a032002c0010451400e02d1721902d00300c0040d09030303034200303005200501c90787c000001c51805101040303410000300100360300070900c03e00c5480100200241003000b0805001814050002107801d0030044070f079000c8400010300b0042c09401401059128803000411400e449011040c024501841034000000c01d42030009429070302050341804a10140030704040150800b5003058018400c074400b9140600e402030011350880c1402d440e851143c0408400304800901c40d5014008400c8042c0c01c90781c0028440c1420030700c0c1c60403880700304d00c00d01c55a100c60fa80c0041d0b4811076208180e100d4401030504581d00c540401a050005e840010401e41b02c0e8400d180c0c05000e0b8000750b041440380c010315500e0800020146103030046410900140d030062185800503100c48044982c00306207a103851a804d00360700490004940c8045282110301d0412107400103012515031426401007040360742c0e910104041c414070190a601c5102040200b20a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 257130638 1250 257129388 257129401
    0x1b031e04061509050a0605030a05060f070203071a010315021c0c02030f13150c0f08070c03050f1018051231090c0e030d030b030313060201020c10090308 67
    0x5800a401500c6400085241c2e50510000ca6a850319544490400e0fa125800d100c9408102d1003003001410040d005444040d0f21a10b810755030300006446518610b490070000b075203c0c0d1091069031090f0b5405542c01c0f44c8075240040c1c00c1c3c41c5c2d01080c01b0964110942c102c181e11182e0380c0384203c03801c0e2186030360010354000d02050400001c0c81984400029800708000307402900030050000c0c004500ca9110f0b19007203e08020007000c42001001c500002d0003446100701010503051228801100ea0081a00d60344158600d450f1481b40b21550005040744142c80c00c040c0f00f1b94000c1504145403e044004001c01084902240e591035001c10003d081500001c00400940904200410703181e1011b60030b03030115403d81103840b0b80782480b0611030b140310002a24103000e20b4905010b030340c40c80d481526080f001404407030006519092060340380810b040d5915069030458034207100b61843d4440038040741480c255102e034040e020b036111802c400d5040c0070307006211303e048005100b15a080c9401d0741d110020365460b00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 257131888 1250 257130638 257130691
    0x1b01020a1104060b040806010911030403051b030f040b0c010506100e090c0c030c0d031505060405100207090c0903060b060f1218030a0914010e03030d0b01140703081b03 74
    0x107258194226455140c003056107103a02008100404031900140010742c035021070320080b981c1034a1000248001081400701180c2e004003514041c0c0540142c81c407280701c5004d0000c1c507601c107910080c1c1244001003000610220400091300405003404001e01481d5a030134200903c100c05c0070034406c04140012403100c014104003403107940c4844d80da00410300d040303407420407070349903401000044980307500c180d45c2c0381f001c80d80c1402400b81c0031500d5611403044904001c00a0141d00a5000319800303804003003401000c10348200207000007002c0c2c28508000f0344c0c0d61150020300d40341d498003040d90729078105030320780e503041c10b00c2c00444800e001881410ba040c4808803d19460800c00640071800106042006000801080c00105020741040d01c035031700200d19180c41c5480701c4500c0020281803120728448010642c401000310f545a581010b000180c5580010050b9946a10601703070000140d004104030040607044002e0f540038101096030024400e0800e420841f06100c03c4600c200c0c0000b03401c0d4864890040d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 257133138 1250 257131888 257131913
    0x60c180f14030709060b04080708060106051615050f22020f0105030916060201060e0c0313020111100204140414040f120c020d05010515010507081204080702120c031b01020a 76
    0x102614070f41540c80704030b20107a40554002807200c0313034002010031410400f0828170008008d0b03500684200e42c5062405011800391000008020040742111070030080207003602c0c15445800c010400c0b01d424513442c8444106000c40d80c0c081092058001511203a414601e1aa202075000780078240510a00004584603000548204602e1080c1e021181c8903071b00c00d41d161800b0307215a500002e84036150031005400395401804102e09207004000348a003411404010041490302801c20a0000324000c0465180c04202481c61103071900c003080c0410020744a01c941c00d614402180c0500851110030915409800705540040100301d6007000107001840d91000040f08000e175080c60080711056401103002d407000080221785a955603003c2140104c00e90701030f5aa00102882c2403410001c0c00d556120203407040217110307001e141c201c00c002420024100100c0e00040e034081c0201d98014144207801d9650201304400610901450360440e4250181202d0250b1100d016401086103c03503d84480000540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 257134388 1250 257133138 257133179
    0x140a02091203071103010b0a122423010e0f0429090109020118050607080c011808040e1b03180f0d020d02061b040501050d0f0603060c180f 61
    0x140c6000d40300d81e2000c18000351054900400c205a0f00e1340001c403c00d401c59080b15280d07407190808241c144298440c110498034940d6001c2c1c0075094260307624020311f0340502c100034040e14032400c040c4400082200040060030b600080c3c10942580d980b98801040d06071421501140007207a0a00041c010030810400031420600c64500a00d10b50b000184021440354100c9079130580e45c0d11034582d00300b1564440c5207001095982045031102508050001d0789520403d44060110725000c203800d4402082075000d8000b020f00d445484504014616000c09140c20610500503007020304400911001d04010303182c15005c4803a58110b18642e91120030380c2c0c04a1a5502c1401d17140b2404502544800080100b10b03503002c1d10b90010310880845400c02840c10070024442e080b00d00484008405d80d10080c003c0d41d095910900300940c603442400329007001060030007132100486080000002c14400c0303d904c0041841081d48d200600d280e9201407046940c07440d8030503030311483d003514001c100400c079140402d00c4508 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 257135638 1250 257134388 257134399
    0x1f020c21070503070b01080606010806090a020729070906030e030a0c151401080c1c020907020f1c0909020903150709090f0f0e0f0a08030402011e2001140a0209 70
    0x1016601c8003483e64000d82c0088031514404801442641420401240e0041342440d000c0c0f120300d032840c0410b90075030700074150718102034000c0340c0e503c1045803001c0318054044681007801038070780c0605405581c1c1d0006446a001241020700c6c045049882409882c54030140d0400440c9841d0020740120b4440c180c460050b203c2140070035503001e000c1c000703000347c44014000300c480d9003141d41007040c802d0030840001d05041c42646034140e0045403206185020540070b8046407049034981e1011026400c4c65240910b940b103e000701c1c070320396156000c001c4901103251031546d241da0b003564035496480103d02c50405071652661001043d440d10390380d100c800302c1d40f045a500d800c8111a680e005140c059801241d0407045031502d4800e25000d039400346c0700d00e0807460b0718074005114800611558648500e24440007034100b010000000341564061400004241c608450544020143c0d8100601c2070071350f0000c1c040c500044620035500d003481400b0b02c041400100d0342480440e116183d00100950040d4007580c4c008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 257136888 1250 257135638 257135647
    0xc0804230618010e0a060903080d0e03121e190c02010615110114040f03032c0609060108030a142d0711090106120c0908010501081f020c21 61
    0x2601c0d408040d140d4480c41100e4400444181400901a070300c1036115203014800704141005910b602c801401c0803a9003102c505527899039084050300203404005420809440300160601490607141c407181d100d030059100007852002c4400c030b400314100060382c0f019102c0c4180c1c0d505003908030f055801155054060f0000003240c595548400d482d0780d85c0c00c00008046032032201c5194400340c0c20700952116203001d40250700c181c9880c3c0d83e684032440303140304003030100760f0358403000041584001c1803400200c0b60b1442d00b554030009402c0040c2d9550f011280c4400701d010302d200000b80d41100005484071130b000340d111140460800b0076100030380d41040081307000920012640c095040385060700c0b928081d484150300ca1390362580742841c02d500c4046140082c003c06c60740d00108181c6074451400952000900004220300c1042c401c04c03110410b0305e40000020754a040000615180c000880c24403078402442e54101408200f003480c4128000c0382c152821581040e40c0c0c00340b00d05101020580061103c000380f030b040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 257138138 1250 257136888 257136959
    0x71e0806090c1003150e010602011a030f0307120507020904300f14040509160f020703050c04051801050106031a040612140a05150712021804020c0a060f020702040c0c0804 75
    0x30000e921190162f50f6804920f204001c039800861940c960640051086d054203120103581ca104215001e0012800c05010740b100c01d204008844903507400130500500d500701030501d18011900321003c900042d44150040c40c0d0581c00a842c40d0a000490300d0301d59890185482c00d6401c100c0003e22150111000c1001007015541c0460f2503020b042006881028001c160801a1030340720441442000d40d800b860040002510001d5848a000b83c150350205540d1154010418003240441c804192542044000b041c51a410360051108101d00009080f2050341c8000b403104a515a018800f8100409881000403440c8d40d00080140241042103540340e0039140c4540d4100341c0f4a812101510b50001300303001540360310020f802c03140100715a04503d46440c10031200c41e04c1d8010350015010360307004150b03095024401e00c0341d94140c2d81c010034184404840c140d1100000e51101d0703030882c4190301d4500403681d803d20860740060300b20ba01c80081c514040c04c05001d10020040b00d0917019954078803064803510b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 257139388 1250 257138138 257138159
    0x60904021b01060303022b03020d0e1c080601091206090503120f10050a2102011103220b09011b06021e0a0906020309060706020c071e0806090c100315 66
    0x400c05541d0000103034241903140003800c2030b81000da900c41d0241303a400030b250321a8606000040b050594200140e5036002608090b01502601e0785070842406401840b00005460690340c091034079a03aa518225580c4000045d901c1d10014040e07826074611000c0c445001418a6108400f0103028a00f204e08010300915070070021903044078259090445a0b007400007000b0030301d0a18001d40000c59094401c2c0e42030035000341c9410318130698411481c2020120000356401040c80341c11104520003620b0765007024103000610704c402104180e00d20a41c08400241204d1040103503440d03c40169503001211340303110b9070301c80000c1400e18191a0707160301700004444500352a2211143d2441030b0480d03500c0d04207080014010980542c400703002d5400c01c00042c04166109001c45100951002c4010303165004e8281c4180341c0710700713600305030014001c6600000f0a0021526018210b480c050121202551228074580d12010303d402c0722900450303203003101c07031540b40640c119045005407103440400007541c030310740200d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 257140638 1250 257139388 257139427
    0x1207140a1e030201051302130b0f040203090c030f0f03120712060906140108070813080c10020405190303020c0112090b07031b090803030f100f031208011d0606090402 73
    0x40301c09000031011000c164080c0519035120320003804501e051000d9401054030348030034003910540300342c6d261020203145d0b84600092407810809041151a46086a10555160303010307459240310f44512070f4169184c5200084d0008005440400b8500f0403506070810210824080c083c0304c103201690903a400c150340307135224900c001c2c40300020208005240038000b20310300d010030300000c1c100000441041104c80d040708e2295000404044050201c9500d410b0040c03c0e400b942c0c100c4012070040d40c40303074919003405d50040c00689008076901101e1050503a81c0038201c152a00c4002c0243e005203100e5441503008080c241c80340204408085014611a0f40d1414100c50850760701c0003080da00e00501c0c0d14003510f00801c000c0e5810324245601c000b0305180d141030341c070f0100800700040223411600182680c01400c030710030b005010000303200c80d21071386a1400114281c00c11000000242c51080009030340320140360300100d40c036203405440c09507444a000303000841c0d01c4140c216030400d03020031007003015420600040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 257141888 1250 257140638 257140673
    0x11b050106090f0b0a06051605070306060e010b18010c0f02040c17010b04051e0616110118050d15290405090303040b0a0506191d091207140a 62
    0xc001d414825420121640d0b441c0c0c48516034548a14040d442d250360303082c18242c840c0ca040c895254031800145540041a07490014441d02429000004100064100900380d85488007030700c8080c0e80b0340d2640815806880c12006500b1038560300d60086500076868000d50a02070034040354003803000d0b004a801c0d58044141c4000281000351501c0c9104c140b4030b12540500300b02c100403071406141c080000c40340c800b000000b4039100403202d44004903030782c0d0100b2613031001001c00000240305114100290400c0860007000c1c04100ea1302c52082401400006400541e000140303c0c9080406c0d64442c0341e41300c1001401145659900d4440c03c0c00c181c0701940c940d200141c100480c500079180401480705a07000601640740581c81401840009002240110341c422015140043c0079903929001980084140c240c14070f441e5540072000c40e0b0302c0034064003624000e40b880310340c41e600e40ba10080141d5131001d03001c00c51943c807024011030f000600321100c0f054103200360101320380e0301021030303114805c1c80d85505244 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 257143138 1250 257141888 257141891
    0xa0b0708090108070e010e040b040e060c04061b0b1801060b0c0d0207120b0609100506030408070b070f0f03020c0c03030a020304170703020a17010e0f0708010632011b0501 75
    0x4107400d43e40300f40d403140c0c0f1000c2440c0c0089500301250010704018140c03045a0321403500c81d0024080398445ea8032054030f2041d01ca003265191300740a024211076901038050b04001a01081c00100780c598a00c1e040d00300b00354844601041a9601d540c04103110ba241e501e408081d54840d070000a1101c2031002a24210583c0030290441912003807001c0d1810b441d691018001c1c42d403041c5200d011416135545150b00c087e0503035a540743ca6a031501101c108449070f402c4681d0007040401480184040c50000c0d0410b10b105d50300c8040c5139103510b481030b91003074004119140051503c0c40d900e18064403a0300a080b00030210403c03144183d40b8600080d0454100040c03140042e8030200d01004070062050b4044030092014014015581c02c40e0045030410945006103401071080707612071030700c1c24004d6010b10040e2010703030701342c461300680c2e142c226488145d240b280c1e6035150300f405408500481d4803020415260320300b02c04d8101d91400000310701107160600c4029410320102c1c40d03661a40800d080603e80f1000c2c450b400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 257144388 1250 257143138 257143147
    0x7021806030c040e030d051e0403051c0207050717030d0617070b0a051e0705030a09032105030604150b0c0106030b01140609010804020307050409061e020a0f08060a0b0708 75
    0x1410b1918011464580c0f0441c20145084010b840110443c0e40c480c21885010403d41c1d141107542c041881c03201c2144031401c44520800080c1a4003401034070070b9080c07581d503013a0741c0c0c0244916034003030b40034051002e0301c0360700841d4082290b00300402040900400d00c00030380307060207003904203102111036507031054241e5000402c801c2d03881c1100b071141301f01910804078074a050541030003005026005000e41f040c4403441c00c80170b0003040d00581080d80c40c15507014040703e94414014100a00d64500707480308842aa4041094800b54140050034600c6403500382d99443c11035549004020140c58180c0c08c8400cae00c841c1a5000ca8241141c0f0020880d40d1004000400ea1130300d03615024a4900c0f0507030019a40e03244609042d00f01da40c4420031201303120002d00c2d21000b582c5880c0002400e02c0103540c171841d80b2501d072050102c10480b040c0c01616090620020100c0e0711300c1e40c60103a074240d02c00d101c41c080006407001e015202031409032000541080010700101e040d1900c0783d41510243c1d02c5000241d80c607400108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 257145638 1250 257144388 257144401
    0x6060d033005180615060415180f050d15020c0706110606010201050f010302010507061e1e0203070c0b0702010b03061003020f0a050a06110a0c0306060317070c0501030908070218 78
    0x5030715040340d0300046010403808080343d0603484100142c6a08600c840200994003d961403070305441c05030450007440f44011255010261807512551007500d0320a03188840060603500b07503401b42085650281181700052000e075110218102e0002445c2080c603401d00040e808907208210700d0b001741020780c583c0300d2640c602014841c0751840003024030f411a81810304200c4c001c0c2e140300300c0c2270440340c0c21b080c819140d03005490544040c119088030b130b0380d588400703c8481081c0300c4903130482203080420400d55080c0d80b10800c5a10207910041725a4000701d0101d150100010308a008081c0d8410301c00e02c000104611840c0000381000c800f900c0743c6006903001042803056152172401c1c0d4030010800c440c0a2a03451504022803445866803003110700b84600030010410981007402000321840e840051080810b03260718041004012500040c1e9144c080300980c4221070354600122091035410280350480341d4a040011000ba011f546000c50ba4803006201c141e006031104108100c210411503008020ad03d03105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 257146888 1250 257145638 257145641
    0x504081e03060f0906031e030a031401050904022704030914030609120c0c060f07140706020307060b0a090509010501050f10081605070b071713030206060d0330 70
    0x480c21101a000c204140142c0d80d4800b000100d41c100d0030b456070245a61071000007401c0c00f14030340c2801d00c1d250310703048140e2010101000802d00c0c8245a1030820491110030740c80c0c2c481f480b0034050a43c20a61403404a005442e05041402504080f01d02e90130801c000c01824040c0703010160390440105015980912a42c9070300d60302c0103c0190250300510355850711010088ea201d800340e5543c585010f00280007a40c20405000c2000e840001030710b065078560007010a0350440e404040191050b80303904c1040318084401080a03c1118442c2c0d008604081c81d9403581c20003410f0084c20598451540030700004c4598050090368400c080700b400020b00c5603d44814092003030318240030b2a10900c1150124500c0701c1c0c009000681080f02c41c2c444106208400c8420755007442140400b400050900c0c0400840030340c000d20b0540072180e07070356244006403205144440903041c038610080c0540c201d0700014195091070074440c44d16500030701c0c088124030389150850341004c4003820710a41405030101980340344543c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 257148138 1250 257146888 257146927
    0xc0c010219122304020d05032104050c09041a0903040e0a090201030e01050613020d021e0403050d02030403030c110a030c0f2903011211040212160c030806100203040801050408 77
    0x2080121a041425200c00c00482d0300f0003080280300381a22803024041c4031080007590b028401d841d55070329802c80b400c4042c1411603400c6604a43d03511071590800128284486414012a8060031500480c040d040126040c0c54000700703149000d01c420702001456242c0b40c2131060046035800030000e9100b006000050a403106e450384406260b040c541171140d151240c5080e90f016114000700140c071049803070152806803180d04030320300d40041c5104500c071100302d40400400032a4400e00445105900390780059880e405148406404141908400b2000c0760852344d00303043d84280108032680c481c1c0ca9956002c000d00e05500904141d5503202c0052111050220644841e001035a6000c0c84180029072407645034441401030711514103c81c154a03081190603c4074280301c3c0d60081c415516980707000c3d11b5610300d070002c55020383c601c8540d0310150785030b6002d040c110380306540603510800b0540d1480140f00458800e0103590302144130402c000140c61030280301c1d00b0700451050911580e100703c0d4040b5500c0d20400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 257149388 1250 257148138 257148161
    0x30702030d0f020d02070b1b0f011104170f0c01110c030a0615050906100309020303120a14130b0105011124010806011707060c03120f0f0507020f060c0c01021912 71
    0x800c018403518220364296403070000c0f5004010300c0401401c111600740303003420107403030403cad82030181040c0e01c41ca582d000381095492030385041c1c034000700c0260f2081d070b104002c98500316250010105e0002d1548261265030f440301c2081e04440082d0382a00c0400d203441c040c0c500545020342d41d650344898604001807960003c1000700d0306d10f0b01501b170001c00500c03480f5400410205056540c052082151400d0059424510401c045541c0d540f44c52002400a002d0302031180b00542d03808400643c511500320307162840d6640041d10003105078200001503428540c1a48244000c1c4114020481c42660300d440189005d030b0198019040e0754500b040c0c8a02d4518107030040407820b9072600c006102e2100000f406401c80b002c502c0d1a490142080c00c00b59429aa07008081c007600b8281411200814420b800c050505800850204180c1e641c2d00b0302241c0340c20304011002c4041c0c00040c040b40f4000c1c12070b0301400c01540e10200052034201c401001990303020b0074401203404103e003182d0b141e14201061091316800c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 257150638 1250 257149388 257149393
    0x11040605010c110402030a0b060403120f0503131101020708010c05070b0c040317090a050d08070201121b03051b0304140d05030f1305010f060b2802030301060c0302030702030d0f020d02 81
    0xa02c941d440040d51030222a2050007641e020000900b80c100a41240d2020310b0042c10499a0300d44900f0242010b91940300d4980100e00c0d42614100820310440c2200d100714003da0644881c002c09556189100c110030340101e0451082137000304103e031082c42112202c03040d40d101d00d540c601c114504a00e006200030000882d1180c188010000724942e86901700900c01c0c0e43c4091a501c100c90f00002e02e001c9507903080075400501c407d1102041044200041c11b0460003626220344198040c0710100039503491180841c5035260500c0d12900c000c1c0a50001c40c0c011070041540703a80d0401c1c1d040ca440d0103400c00c0700c0c241e40d0f0044101e02107803d10b8060111048248a900e0214a180340a007000083d085003c0c014094134400b001102c81807000039485062030060342c507014040c860703840300070040c0c44d000011251108651155070040b00a0403445482e040310003034010703600f16071034400291102642c1200503025404100032100059906000f199451080382c2c03034078961140540f000a1420001c41c40350019035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 257151888 1250 257150638 257150657
    0x3020d06140d03081f03030906120501030816020402040b0c15090a080a0c1109010e0601020d0504050a030209191e0b120601030803070309050115060e0d080909060a0b071104060501 79
    0x30b0702c03500041d07415150981401a0240c4951030317010103c001510030400b50301e0306018044109680034102d407040300c0560351220861292840d040b012240b0a101c020400c5404001c0985006100300310301c070106000038401800c1940d52005a50543e11040c411541e540281c1c61070311070803000218080c1c110180c0d40040c00b110040303503030b5000a07102d03d82012083c0311003106039804201c800140c41101d42c001818020341540d441804040c44003041c1ea01328054000d0300c1801b4035640c400e8003500c00701da000a01521901d440e40d001d20070740700000350101e0b0030022009601d100d551058000c00d2001101d0a00300072900d61886c180b001265080d100480c410450024005482c00d40010340ea41501d0301720f03102940d20340703880005500510384848001d00550900b460500f4081003c00c001c0200c8200317880398105c07085040100040ca40f5801401000400300f0f021501484c20050103142c2d00002c09845511913903281c043d8668180c10054045500e0421f5494650781410706020f07100041200703080c0384801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 257153138 1250 257151888 257151929
    0x3050a02150a0c15020405060d14090312040b2a13090203041a071b0606030209010b031603020a020705131a030f0a020d02030c09070f0f051303020105070212010c03020d06 75
    0x496100c018041c020008030070281c2404130450341150700078400181080c0e0307600809a403500c003600d0300503000141c010f0070383c00041700c40c500401111012021510352004a40d1141e859034a54000030300640f0f2142d8070b010000c207041c0d88040c0865030703c0c580010381c56156600c0c01c5102e103071000341c1c1d00a105490300502c14400002c0c0030069501802c10981c46001c050b83e5200c00c2160002e00e01c107030404e00f00c0194100304041c440254050000d4a0094501b601142c0c0c07182c2600b00c1c60301c02900c054101d10b0041c10040d10045c07080d80a40027010380d9105903583c0d03907629000100d124000752516040245e0380d580e5001004030340001c01c441810142e000d0324012105800950716205c0688010340181c2e1012280c0085580c00d101550020000512200c0c2e24281401c000305907400500705036000c90702c031051450500d4050704c00d80d2a003117032203e10144c025055500440e83c035089428102d0304060018544c0f1062403081c0108045456141d400584034001a0203020a1310740c0b1f58050043c04000081c2d40701e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 257154388 1250 257153138 257153147
    0xc070b09010b13090f0803150a14031e0f030f0d0e0a051f060302040507020109053f1b01020307020106121509050a051b10080f040b15030102030103050a02150a 70
    0x201c65403c81000034400000d03041c03008103202180c40c000d01c0c0782c80010800080262030f8100101840041d40c107071038421b4072541d0702ca2466a460b060241d1503405680ea02c02002c1828640400301940e81055820100c01c07084150f1450308450b071040d0551901250100c41020035124421060b44404020b0014002e180c80b01600c900443c03200c0141a00086165603500c0d415400100c0110b0380500204150300e0803001c0240204244042192940036081903004201090b1070054503501c003041203a4000e01860b09501034100c00c0380e0041420503400c0c44104214016207991044101b4104c001603030300c2c42e201c90f000307084a5a980000c1c00d0621582c1c074041c046a02c0c3c59420510240032030b00000d2100d003605000c0e00c1d040c0141030061007885504a01d903e44044813080c04021791040c2c1e12940300c010920000d880041c811100910140c10384030000300401e00c1c001d051504036480c104100362240346000424207a0b4002d8006481590010b28068118141078508203015900c4d89001e47c10209418802031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 257155638 1250 257154388 257154409
    0x40507020d0c12051e030a0c050403121b0203031803071d06040507090b0d060603060f061719090302071e0e0a0f02090607031d0f030a06180b0c070b09010b 68
    0x50109568100c3e4440643c09181111404c1e1485400b03041c01c0329400711401025032007100c824104038108090742e80c038039001d0020303030f016284c0c801410f41c110560b805003100e200d1014200b166268081040140140e1014001801c0e0f00c2044c2c1d02000d00e15080b8024140340a40942c400c3e401c84541d05003140f09816543d14154002c001120081000e03110b00b04c0c2100d540a0540001c1815000028403128132042580700c1c00803104181c0b014041940e84030b1114091351080c2c422038000c1500000b100e00c510200d00902540304581c0c5c2c201041e01004419001e0480d6408041240035034040e404c01d00c0400c00c13080308040c0e00010703c451650007a00306441002441c038090107085088e5181c080044100f8903a0301601c55044010b0125916180380b410003c01508400c0b1128561010420006041381000d07607020012400240c01000c00a0007a61041c0080109401034009900603000c1c1d98001491500e02c80d0007650500308590b11019142410030004c00d028080d2050390b0314104130096580c58442c1d850 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 257156888 1250 257155638 257155643
    0x110a0b19110a0812070801060e060d0c03060f0602070911032503020408030d0f0b0301090b0c0702040b0a0308070510140103030c1b1707080105061503070c05031602040507020d0c 78
    0x201051a540e8101d0b4980720b90b44100030005a008a10034540080c1848150701c0341115545980c4a640d9a81e400c0d00c0c003541c0c404071a60018000c2108102204583d001503801c0d52061800051556907440c01e0b03802c801141d0815001030700203001c204072240142c0201922508181032051840c1006841d80005c2207a02d034003200c83c41041ca809424060082d4195802000500300b503da9030844403043c03000511400610703820941c0f400804030510300b81442808621a401a0b04071100d03102c035112100d01c0e07000801e049a000d503e64180b02d07010307150342c0490001940b09e8448641c64611501c0c2c85401c01510181d4001200c0c40c01ca414604180320308207160459130181444c069440300c038109214660408840100d2401030443c0000f6904500035501c030700620610103944a003921703580c1c42420ba4900b5a03100d80e01081c850b006084100b002c60086801415900b018050b100c5540e65050a40d003044c08025901d80942080708294200b90140f584d202282e480901040e01d030b190b01c00b800c10035610601 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 257158138 1250 257156888 257156897
    0x15050103110c06090c01201b040207020a0806010f0b1204020108040206040e04110a08010b031b04090203070b090a0e010315091106130f0501090302060406080910020304110a0b19 78
    0x2101201e1060221248000e1800503500c1610b449961103540b00c0d10b00840a002505030642c48a200a032118a200350f5054500034080c1040d6000749650150550fa5401d54042d0b0708116000042e920716502000800504c0f001d456590316041107650007142c030303600018414008000381350319594240c407003a81c0294242452112900d0354008030701d69010399045138501d150f5440c01d1109000b44c0c4441580f40b990120396083c44148c17103800007800d841b205589a074150307002e0720390895000d10b10302030015083e50140002405580940010b8580303510b070b6000c2c0c100600001030004141c02e03c3d0310300c40c014050141303104110b5499543e94051003240c80d014148074076600d01800040200249070521005030040c40d081d1155a421041a42180340d44140100d005084c0300010325940141303000c0040302d0300145400d00701885c0030341c181c80d2060000c12826580c004c2240003050740c00f9600c09180242d0040d080403000d10168024405482810741000000c50030621104c00c00d4158045200c1c5500d105160 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 257159388 1250 257158138 257158151
    0x8030a020d11191d270c04090b01050301060e0d020d050d02030903060a0504020603040f060b03010213090c1701050f060706110702100f050a0e030c040c030f06050415050103 76
    0x1a020028040c02a0050415040010100140348910007400c0441c8807018402604409640150344101d500300d0039000a6500c545407826900d044055502000500e5440176407810310181010000c4008a8a12414081c082800c0c00364040522950003426400c2c280103185504181019200c0d9110a0540b0710038002040f00104640f10614403a0702e440d405011941d8480e01c566000c2c1d00c0b234205044040c000c0c860b0704002400c0c0303201401010302841d005000e203031a40e01c850700e8043d1344004040c0d007542e1311a2903400071044c1d03840900c0242903000d8070004855a041c01c00341c1e440d06840311390072a081001024203c6190300480341030024112082214080985003000c0045815400b070311901400c014500a074003600b45050000a0001c0ba2084070503110200300484295100c0101069420000d5000d01c0301c21401030140c070082c8102d0308000c0403103101c401220000360035508102080c500094480203050302e444060300506d0702070401282c0603c110307021500010324840340c80c4102c03410180c5500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 257160638 1250 257159388 257159401
    0x3150909110d1b0803030604111e0a0c0507120309060f1d0f090109020309010c1d0f04140a0f0b15070219050607050106030215121b041701151d040803 66
    0x224108010f005200041688541e115000e80d180d41040f1080c40c00f030b0f41002030903400c03a041c00342141c20583d0401d0f40a003040038041d1108800d508141307040c0e0240401c411007980840e204010300710040884904980c182507462034010b000710f80690180c0c00340050211800e040a402c000320744039a4420705c0f001841e042c40200020704518a40031440e030811581000030038014296002035100700f1250000303001c80195803004071803000000cac01e40f080d03403090318102002ca45003a61203405074002c010701c045211054240c0c801416502134401d1594155514040211806203001e220b10b00a4210354101616102c40c0348000c681c07080c8100240320302c80e552441e004810241c000d02018050203820140c40d125985080742c020012408103a11800c0c502180e044075803413113401c90300c483c11038030340b079000b152100c2000003000342c0e00400e600c030840b80078800407481c1d8102e00010480b8500e984004548121400d1943c3e1807145960002c07114407071219220380d5201c0c04103480710740140d800650280d899440b0b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 257161888 1250 257160638 257160653
    0xf010e0d0c09060803030103050f120d051f090209090a150e0a0f0509030706060f0b040e0402030c0306070f0801080d02120313020a09020d0b120613021f03150909110d 73
    0x1604158002840e05102013101035001010314140c0384204101c8140351111201c040da6030310400720400c03054804001188500050347c21035030700441c000e5404040800301c0d51944003a0703400c58201d003d07456030104044801c0c1c90840006d5410100c0d41004200403480340d4148000d1809600592520030042808a101512903074000b14091807140c00130406410500c09458581d8454841502d00700d04001c0042801408200c811040b81c000310601441d061074050590b400501c010016079040c003480580120740c1c2c8080c412140304045682c2c1d40640703c5000240a0b150000603000200340d58008003510903400d170001160b006254810030b0041c0c403940ca0700390010b4682c0d80d10305c00a4105030000c0f00094584595000380000302901d91080c004201c10380e00380103010146c3d2408400c2075102c1e1002c126021911443c81c40446e002800151a049032100d400c3d600142c036100110020380c0e2544060098003000803060058211440c0500030405c2d5030720340c4d40c0c1002403a80302c0c81c414440e0f50700c98010407501 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 257163138 1250 257161888 257161913
    0x30f0c07170a030f0302031012020102100501030c09060902040b09040207051204030b150d020f010e0f0d080d0b060a0f1d1f021c080a11130e04060b0f010e0d 69
    0x103000c0c11041e5003810800454072952040011004240301da407507014403078000d0081d01e1146c07941c8102d1100039454040003800c100103511040e81940540b0f80c4248030700381ca44c041c0c5e034065070098044846040c40e100c81c0c202107a140b58040d080390f5206000c00d109919500c000c80b0000b000485003da202c101904002d801c01c0504042c034402d08a000400004000f00070100500c01c08181c000501d203811000184100540c05810081d404043c0502c03140d004d40c000c0110b00c15003200600b030300c615040c2c41004120442031801c02619000070215141c110403002e4080c07960002d0050b100036003084518803018181241c6012407909101901c40b01001c4002e009000002c4010024a481d04444000003030420b503089000806006004000007540100c9050740007a441910907070304c06a40d903071112500b0000b05180e0511810410301003060749210300940e00c00c1c0d0301412421140f861103052500e4074804644000800070b008168005011400d82c2c0c1106140c68075200c10b41d180e1417016100e14110820542 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 257164388 1250 257163138 257163149
    0x1b220207021906030c0201150b0a0305072007140301090b04150b04050c070b0106020c010507060b060f0c0f060604050c070f0203010912020f06060a0803092209030f18050102030f0c07 80
    0x6002c1d40001c1d07502c2d03040d0404090055507070020081c1220421543d644a1796500424004850400c00050014480c0e40a04d901c15400d03c0c003020401c54414514a40c060740317940c1021240d01c22002801016819201201d190004a0007002502541c0d500c285001a0007000a41610200408c0c100c00109540012081300c4c00288108010300e0070420038103094202d40740a5542c103d1010021420900000304100d4081e07050f11044d092580301d80d201070203400a0200140c0100d4240000303000c0070030b030300d0281404001820180212042891301a0b16007100280f07007911450801e02805812920401259101034108a1102100b401400401e0150401d004020849501400088813455001c20900c10308070b42d1708241d5065840c0c2c1d01c200303d400c001c540207032000b40d0804c202d0310500349448030b01800c01c070031100c0c6841d5121600f80e10300405c5500c046070980c04281c0310240c0990640c0d010b1114054040d0300310b4500e1a0a0424000035507038060207100d10b482c09000101c031a208282007207658002c0c003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 257165638 1250 257164388 257164429
    0x12020c0a0b040e0703060e06040e07030b0f040308070302040506040614130b0c07080a0803011e080708010605150a09050f01030e0f0c010f0206071704060e0303091b22020702 76
    0x1d40c0d81c05600c2441c2d0051261118105036000801d021318441e029407400c0340c4802d0fa0760244c0c2d0f1540c10070400103082c4c03001703141d003580b007500d06c000001101d15104602c640070041c04050b10349001d090241151303500500c580c0c01c0501c10841802250344020039203050b10820f140522400e0040140d418641c031414441d403031083d9401600081d0914920010f0179048070400075141c920741c0d0b4a41e107030796a0000b100003c0103020188014400091401d0b4844010154200e500c1d06042c0d03140c2446003481c0d290b0708054000d075100c0f60140014201125141600103100c0c010a181480030b030b50041c03801950b801a54820f03c07448541d11305036031194104104005030304007910411403100e560343d0368825051f070406010a181840d01c1c11180d001096951099140b52141c0d880384400d101d1401000d84010030444020f0b0392a2486240743d442080914802e281c130400801845140c42425a410201d40002c0d500c580f0264a03200c03010b44010b881c03241c4400304e0389070140c3c03203500610000e008400003d1000c2c00a5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 257166888 1250 257165638 257165659
    0x7080c0613060f0c1b0f0f06050601080f042a0b0a080108010c0905060a0309170301080f0c12070b1c0e060406050c07030807050d150b040e1006020a12020c 68
    0x45104640d2103107240d02c200002c110a244440b0700e04140d1302840061404640d4000350407640c10705c00070005154500c10500c40f1018680703a5604110707071141c442e056400035a94420049107580280400350407441d80039100e0b100703251540d500c60621a01c8040032005010514520300004401c454010140501d03281d19078883c0840c003801040c50780c00b445204450742c00c01d004592464001e4a00005441020f00824606800344c0f00c20b8000c0c01c0d0500040b0383d645100101813000513003000265010308401c0026040126071204968a00b0461704115481065203403079100c021040001c0c5841160700c0d152016495070490a2840002254034003d09451420003020f07411643e03010514501c13840c4100c2e020000c81e220400d11120134081c90a000340454142c0300820341c0940120050624000141004603521000c10981030b08107007194800d10142c0001324040c01080795903980540d100154070203900901e0b04e00340c8000c2d990a02203402034201c0030002040c907003880c030038403203684800703405040010303203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 257168138 1250 257166888 257166901
    0x1809170c0a0227010f0f0509071407080d0e0c0a06140c06010e010e09030a050d090206070c030c2c04080a09030804080618030307020c090a0608010f02030403020106061701060507080c06 81
    0x191403d10340b60000e601c030001c0040390388100302d0007000a0f10019841d8030809030409060040c1102c1c050032140c140228011107408000c6c042d00100196442115016295000c4514500c140d902c407800300c6040d0781000e00d481009454030040075040300e20618081c0400030041451100e04d202e00c8001c90224000c03140007158043d043c0784031034101d0344a01e032049099075440c0c1204d5124054a90000d00041e0208030518100240e07800040b2a140000e000d545020381076030300d880c1030040030f031b108840314504024201701e001c6070040c1000d1070043c62400900c0c4505444ca0041d810140248010a080008a540c01d100b42c86a60007201856011658564036a101c1c1c200e165604800c40e6030401c650251401110700000200a4a010314816002002140c42000801c0945400140134100255a503031000a0001d402d028032040042c800200617039a00705820000c0c25550301c3c0d00300f0014004034080001d035000402c0310440c1100d0b04c514000361a0724451502e00c0c003600c11081c40410310310404091046 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 257169388 1250 257168138 257168179
    0xc1403180f010e07060f0f18180b09070513121e0c1802040806072106030b0f0609060d03030203070e0909030903060709080a11030f01050c03011809170c0a02 69
    0x7080c00c00c0720454050545d2120211507140e0071b4101c5100003184206450309a5001e8456040e0900743c1c2c04030610b03140d13204c000d807400e8002c3c41002c2080046d00c07109010018244680840c0d000702c1140340151030b019140700c02c425110250b100d04401c0210814100041c064215100c00c0d40114445070805038a1650411405d44030700d900904e0240c42ca075505021400080d4802c480c2110303c030501603d11551a03130003e031801c0303041120b41d400010809560100b05e1205200704005036204800140c0700341040c4080c9102e419004101d540034491400038051190340c2c2c0d03042589200d51514001d43d80356181d00381245d100110110560b0098000421701c08112004009001d0701e40c41502200c10070782d6160070458900400384141d04260300160800000b04140c10b080d51515107025045440030faa40315003050031513030101e404802c0d800c00400103028080303203955a110017a0b43c004050040f050591a00208940b040004e4010500001211000c0d00d005019031001c00b03800070a00200014184580d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 257170638 1250 257169388 257169401
    0xf0301080601090212010509060a05031f0e07062a02030a030c05010b040506010f0f021c09081902131a130c031409150702030c0604240c1403180f01 65
    0x15001d004201c00401c0d540c10901c02d80c1c60301c03082143d40500c180d19080601840034000340002d600850701000110355620304201d1004524151600d100714810b285010720101c460b1a0031001c4903801624042042c150300c0208041c0700300c15a01c0e282242004c2c0305040d0041001d04200a4140c003035503003200300741904140c8160395140224024080740000c00100000c50304d0459030203022800b059014451144651964645400c0c1c81c0121b905d0000b2651580b00000c0b040ca000200060100030300340400c41082c42034140401c115050030404a503282d001504580c241c02c0b0701e04140e07a4420464014051034045055131100140404c0c4003101001c0380c10003c1e0440c00d0521001c60b041080c400b01c21036090704070310300ca06042c201074500104d2840036241d07120030150900d011480305020103060003409020840c015441240024010b2581d01042e00500c044600340c05401450041003009090700141c504540503505030605969a590307001118041c0100e41c442113140c819840c103a100c0000550002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 257171888 1250 257170638 257170649
    0x10504170304050411070f2003070801091e080d05060a050405040b010f150504171e1606051c0e10091505010905070507030309020d0b1303030c02060c09150d020f0301 73
    0x2484450030080c103170810b034490000e0050581468980c0b0202288010a0003c50ba5a49200380e0183d903049900191030131034260007020442c1d550781c844804100c14400240840c512280020f20021401d8480380c0c0d050044c41340c41100d268440c40010f88070340d210004079010b444010004c100314107082c2014517501740e0034042d94801c50414080032540c030b01d6200c100e40c0590747d603a80705843e003030500d4240c14801d0f0140c10829010b101c1c45480c08503620201010503811451172000748142210540e00c240c40143e19440726090103010424106100b41d09100c10313559400b034050124130b844103000654500b4099480018000380b90222501c104420030001c00b40301001402c041c4081e90b01e510100c0c00f00c4400743c61280200728200420030009009800000b0030900081408507848000d45076186003c4049411900300f501d500650030800d1b4042c0709480744140c080c40101914a088182040a032043c413010b5842150b030061010841c554410890300101a111029511506003d03107410960b0003e0141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 257173138 1250 257171888 257171891
    0x409080a09050f0f040b0a08030c0d0215041101110f010e0706170105010807120912050a120e071a04090c0c05100b0f0609030109020409050f190803040305090105041703040504 77
    0x41500d071001c01284150f000911140c03151490104010003403880003401500204000000a1a02d0702031000c2e000442e214800f4148000b0340440c000d0400440138800003091001005020220b21220f0517100011003c7c24441180d0b620a80c1c01031402001d580010b00c20342c24032620950904001c03408804403052900c5100b2080441035240e4030b07540b424080d950003d03450b007000403510703480349102619941081c0d1001840c2c04890303c5040400c082c5201103004200c001480400072940584407240030070103104100b0521850000c07840e1a00700c0b41c0b15111450447c103a49141c03030703d0b6110484d1f00404181900b0058035843c42d4011748101c07807041099a02c0e000e07089003802160414042c1e1402c804004001c40000c5501c402040540d8119000e400d80541d40c0d20a03400c016203480c4500108940280d009025204011a49920b480000d0484208440c0d544044c8000038202d00c1c1900e4000303602d07061180d203074104140121603138042da42c800b611049450030418150800480140f0542e80260340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 257174388 1250 257173138 257173157
    0x2090a15060923180408041a070b010b1b0a0c0e0c03070207030303020d06080604260a0e090403030b150d0605121c051c050609130b04030c0f020409080a 67
    0x25540340c1010310a480448a45400641119540f03050b82110300d0750003024401449072042240d28005021181185d4000c3c0014040c8603410840c4c010a10040d8a120782038541603003030303035100380c120700c18440c25510b88404504010740d54159041c1c01100c50284080703404907170790f03800c101c09680c815128101c1d0112503840415444018042268883d00054000788445461560124000e510001c04270082656550010a404000780945401a4050716038280d01807011421104144445800603009050070403000c0010380e00003520106200046a081d490380c3d40c0c5080607400b800c10704281550020a03001800394018a40020340303030000c1d9400007048561b0301c0e1000e200c15103500b075030a071001d580000c03890711502c881c0344064060310013145444c0382001c002800b00010f4858803450300180075217541c20083e4900301030301c885501c400b5104c18121503100e9610344039901540074001804206030103070342d841486044000040c29683c050400c21007c601801c182880390811071050000424008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 257175638 1250 257174388 257174399
    0x20f0a1211070209010e0402040906020f031008030a021513020607050f0c04060b0301030f030e06030a02180a05090c070c03170d0c091a0c070f0801052212120902090a15 74
    0x302078070b080a6000d040c0407080d0b420964400390f5894000c000b02c2e842612801402c0004000d40050191281da0310f5001e074490524800b00081c184c0c05400c1280254024803403d01c6150b400185200003012080c00c00c400c0d500d072240c4140e1604003150b0301941001c0b000800808200c800166400490100416100f003115038000f04005e403491403251700550030301440144013044a070000c0ea11314600c2800e0002840e44c03054041002c82e0403c84918840e20750100305040c140040e0f0040c1c1ca84844103d500d0001d040c10000002d5041c40050880c3d4544070011400f501005a5071603100050341d080317801450f410b01e046d034004c01a640600d481c03135403250414031401c04203801405c003503086d161007070058580074500f00c60058031500301e404030703200c02d01c60365500050b0881daa03400600542443e02c00413440d0702e09408072030b01c0e80100000c0890a180398921740b2010941c207001d80e05007140785150404400d01410060300203042840c0000e94820320360030a20008200c030764440c9410110b840740540903d07940c0c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 257176888 1250 257175638 257175671
    0xb010b0306010806040c05090a0e0a060e10060c1403160c05010201090b0609280e0607091406030c040e0a0506120f0307020f0a030507060306081006050d15020f0a12 72
    0x741c1d81c49000c00c1c412808903c45140540152002403038034500310b81400449400a030000817107901c0b4080015107070f818400500641e00441e806001c20540d04006800c3c440d40113074141c03d1a00c80c610801000c99404002c0140003211048201421002c80382c60b00e0f50f48101c04c05820034600b040b510400d84a60002d015401070040c0c42d0926000020488140c1c0c42d1400d02c8010b000041017104014500c0d2480d0340100744e0450312000d5000200c10000d004101171114600d012000390281043c40211141000501041c20b14100e0a54040c2d482940f04d86802801c1c020a00071074000806050200c0c04004204408d50b001e01c0c4210300403980a0700302c000c146410f503140e20020300e509403150000c00c07440c0f000d4100000f00192011000d080081c2ea140e032629034030305201054002e640081c1d02d50308100200202004503000c4141601801c0080910708000105d04a0703482000500ca940355200a280c0148158141c4962903044c00c5019503c140c80d401c010f003100d003c403031002001c41c81c040029a030540078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 257178138 1250 257176888 257176891
    0xc08131706100909051b0a08010f020712030506030601150e060d1b08010f05040b030c04150303020d0e10030c0e0a0603090302010501120f03110a0f03030b030c04090c26070609030b010b03 82
    0x1501401c20480e0244510305589070440080c3c1e04448410000581074002b4410841582e0300e8400058860643d4500403c01c01d90302040a4100360401080c00310310b0b940802d40a0440702c880004118503442c00005680300f4004481080c0c0c003d40118440d5207404068004000c201c2d1050080c410048062405035031400d028000e6403081c14002509000700c0c2045d40c40720600c004001e0840305500f204200103820750343c000b05c1d62117082d1203800c0200704050701041802209917950a04080200183d804201152001240a81003544482500c4803541c012841074001e80d0002d490090310781d85600d800340c058120750408800661a01c0700024000600840c0d120165074406a11528480d1684044a058000070316410300f40c000e0072100da00040494031140e070a20f10a440110350b070420101094201826005120f0003182446680c1c40000c05030b030704c00c90a0b03920422013554509002450a52540d800d8085100303140708032200420780a030484980001c0320301c15100d00b0f0050380c8911130031415020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 257179388 1250 257178138 257178143
    0x1180b01030326071b020303032805070516030c050607020d0212030402060a2105040f0c05030d080a050712020f0d061e090f09060c0c12020106060c08131706100909 72
    0xa460100342c4c03031480780c0b85040e20381554002c0d601c07000c480c5070002400c50f8025280302001c20080504110302180c038541814420110140800c41d616100401801e14860305d0a03840702514045a18020540102d246000140d0004201c50703103482c1583d400381d503071848100c140d8054418010064a504138200c01c5030701c01d660140460b4184039444c0b50a0720010008911030190047c900100240280e49214251043c0c0c0501d40b0700b50266001e0030f110040e02c04542006020f42c102221030402d1580001210f034001000e000300103401c1d516400c040310b8606144d03520114560000601c40b8005a03190007034080c11003503080c1003180319502caa4a048900848003070900030851000100800500d80d031050360015030b09003000c00d5200942d5504030031178140d00b80e61000303d44070f028001c0600c1070041c2c01c0f03e041b600a00003040418180540a401c61880650040c1114000201c083d259041003071140003c210090002c5151441b110300340307031150021503204c00381c00340e001c00008007090b00780039507000da03038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 257180638 1250 257179388 257179457
    0xc051002120309070e0705070c050105091c290609060924010c06113c250308011508100e0907050604080c040b0a0b091201180b010303 59
    0x250780c01041c000c54200800c001e4450080400c001101403204401d01d10a13902d9903261503850030a46841003401c40541c02081c10020140028000f5450b00c02d1040080c40d101323310106c0003c0320740b618003036031b51440c240340d0041510074041c3c000d083c1c410201070b070041004507400b00140c0c1d6910140086004101c401c0350301c0340045440c03000b441110300e87c00c1c003410070185020200d0788840c4d101c01b4150f6200084030718008400040c2200d41e8509412440d103a41c00f0b00311381c03510840903209038501e01103040c0b0015a4924000a10a440240900c0041c508001d4404040f2003402c55040141c00d41109100d4005010408100c202000340701e100880d00c28a107907182c0c21201414500c00e1800104000e05000b0207100f10356011400e9502c600152004064020040828640030b4040c0810f8440c4018814010540c9200911040304010156020034000b55610218040048192809000c4e021000b801100056840e0020701c6110448070b8141c90080e1610181080c01a0f00410316a44c66200c004452 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 257181888 1250 257180638 257180653
    0x50409080f070611070c1502060403120c050721111f0c020f060a0509010606030b0f010513030b070201090314030603120f07140a0512130302011202120f040c051002 72
    0x80349020181900728040c036030000e00d0700c1202d010304c452a80b10020903240e0b2210351804010302420b000c0300c4c0c0c12800d0b4a00c0907003602c2c2132a41d4050908025210b6184c03525441e981074410b15441841901c00031a00030025800215901102002c80c0c10385044100004100c5100c181600200140c1800c008241080d04101a800391a405004000098010701103000364400602000c004022141c000d950040d000180c83c208022503500315809503104105050030b202482c0303c2662034660005043d00207003480d07175403210f011500e03140070710043c0c00003024900300c0300910040d20303815440703a4102d5109031640c690700682030f00030034614001101d40c2d5074190b0099018a07419003070a000b170420b521500d00c2640c10110702e5981c0b5210039003058091074190340014411000e2000821400c0305a07058404440e10b401000c9116000049180c0006810700140068002c107810095044170720884000350034103050f0410340d000e205d0420b0700751000e58502035111130100b280d1809a00900c900690f0380c004000381e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 257183138 1250 257181888 257181907
    0x41104081c0c0210140711010912020a090e0115080a060c030612141e0c090c040608010e0601020c0a031b0e07022107170a1707050306060d0609020a051305040908 71
    0xc4099000e070403420011176904e1200086850b002800085104520390800701c40d200c00010040041e80e0700404c2c0050150181c44050384a440744101076454100d00820700380a0303070710100d01600302c0301044004c40025074400581d106000c01c0b0002045d100d07040c24840c6594600044058600d01e014661156142d00d10040006203040d80281d02d6860340401d540754201c1c00040248560301c4803229044c50381140c4001c80041c90413000d041d5002643d080d80509140c10480018610300050140c0f0801081060118800768001c00500f08141002024442d002d5200d1070180445000c421500c402e61030114008500c0c02d80e1204a03d01c41d1031a40e005103002140303840748060007620301c032008001d14030410050011030360036100000f65451100119a44440000c5d004100302c149a081c107598003100018480a04c0d8002d045980045003210104d41720049031600c1001850030394400e451983c80000ca04a9a40d044401b90a15180c5607503c01c1c29240da5400703001c2030329160f180003009000c08120032401c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 257184388 1250 257183138 257183149
    0x609060a090306020f07020f0913031d04050106090e090f060712140f190203070c0206030603030c010e071a040f122108220f140c041104081c0c02 64
    0x528041614116032002d6407a02c89074100d0f444918114039104d00026200d05500300310001c0c100da5070040e140c0d10a1440d0400e001480700411610050402004e031001d5803840000004207200184010300401c10781d6955800900720250610032000200d850b0790018042c00e0020600000381d003000009814590703694401100c044111000c002001c607035a080d400c61040d003040c0c846101e030310f450385c1d204a14203000c641c00300c816088104050040e0b00420800c0811907000125102041c0d0590340c25451351288000a42180501e406001d080d6107840c2202211020028155013150410940c411250350010a449d07001d103c0c41c0508c044241000c801000078010002070b11600e140100c0ca40c110b1228081d90000d40090381510510014203e0380c10710003a40f00c40c4e5507813400003140301c4013840840c105595107014100d10007000341003e403c102d504030160340305101444d22080014400c021201c1120240c600c13941240c0101d0a0b1845200180e070b000400ca40ca49940140d1a51200400b841c003d508225 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 257185638 1250 257184388 257184397
    0x17010b0a0c1703040c05061e0d02090d230109080906070c080609010507091202100e03010e010e100609061809031827020a050f1308060403020f010c0c02060906 70
    0x400800c2440807020603034142e00000c07141420020ba660f2130800381821241c990300c4d900100c4c49003d00f00520a003920b250354080c400b0581e401c1e9416191951102031900900448410a03003280f00550480c04102e4040e002800c120000b46603811101c201d1140b6034200c80c500f6200801c501c200704444042031810001070840e85110340b860302c40d400c3d00d454603541812000c0d2610540c0d0b039100c03801e1187d0140c0000b010b070701030460108000650744568000507410510001c2c281c040c04000d1032103903900d071400e40060107100000f80091005000c0741396481d954540c954100341d4128500540404c07080c10314000c2c1421a61119070307001050f030302c1e9101c440007800360090440910020101c12a441040c84180000400042940f101d00000006050820706014805076088a04c100144807850760440d05503100034920301901c5031503d20201882c035075000c590300803c02ca07102d000100002c0550000f662070b101081039000340085840c1e84419a1080043c0e20029402030050260b08900d040032400761 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 257186888 1250 257185638 257185657
    0x5060a0e0703031103040306090b0a060b09090105040b1302040b09011701030b1f090c050705010c030504021507080d06031202150108030307050711090403050c0f0606130209010915020102070201030c17010b 90
    0xc5e0f140c181d0b40d41e1a0411036a0701d8030115421070b000301c104012514103102c0c540c000c0c14051480c0f46007641020000341e4480b01401107521440c0e440820a1031a140c62407028400c0740c580700115601e0361102e400410307903000b0581d0380e8005801280381d0819600c0b41d01d4130320b04036079111140888984800d114100030000e0341c01d00141c0040780341000624401b050040f507040c0300e60743c1c8409590389186d080460030f42e0340a00006052500784014040180c60302c94034a0382440e5483d8102d522006070b40791024041c41520070b503840c854202080481440412084040107441c2a000c85401812982403840340410921501c140c0c4e410a00c005046140500000c007e483d1280c4414080d859111001031002c60041c0d5095000030004610702ca031005007040a44600b41100009007ca4901240000c2d903119403080700c030740c40e143c005c00c2d601d41d203034010020341d4050f0070801070182c20b41c40040d40080c006c1d005000c050b80083d0510310829001070007481c807800e8205030300e28840601c1e03081441010382c41c1e1201080c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 257188138 1250 257186888 257186893
    0xa030207031b0c05090c12010b0906070623101401030f0204050d050a120e0a1505090307061d0a0b091009050a03061a0a0b0d051003020d0f05060a0e07030311 69
    0x84103000b02c240242500d0040c42400c1014040f4180424841c00180080c120041d0301d408200c050510f107a00d01125044030f02181c1329550300e0a010011403c0c0d03000c0c1500040c80070b070500d1a403410020105510045071750748403445028986d5036501480c004807061040c100190005054001e05500c40c1c1c00203a0488003100016180ca82c2e1140803c65041c1c0c000025a5117800c138005480402071503403c010728000c80d500e84070115403186030000725086440e00c180c030001c1000e141048042402a015220001d60007010307590b400340e81d06000b40c00e0320190a10001d5a5200c0c00c002e00040c680b0a903100142c1c2e039600c144a050180d560180558a6031180d010310a008500c040002c45d643c0c1d0000c2d04000e50711448010505140641d00340c509500c42c0051503108049804007405805402410755059041d82c01002c00c458489640f01c011410040d04041e4000c00f000c0520828403807800440e50001d0711800c119100b40d03880107400412610464046e41d45900054010030100344a509098404400c1034207 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 257189388 1250 257188138 257188157
    0x9070201060e0f0718061e080106140c0f031201060f0f0c0b180f010f06120b04030c11030d0302070b0603060103020a090e010e030c0d08010b0403050d11010207150b030c0103060b0a03020703 83
    0x401400504160740420f00081f0340c83e500415108101c90040400e00040c20003040380e50401d5005440041150104603882c01e02041c1c0c917044180400c02042e581e075054003503a641300f078112003c0080c500300740641004070740e08806600d00a44640514900031409988441080707440d66185014120041c1a4110108948450010448091107030036211034a0710000035682540e140044141c0e54586e20180f074031410030096a000c42e60002ea42c2b0b41c025454034100a0320741040c6002c40002065800311901842803042c0c64045c20741550080841c02d00655000606030390307003010181d60391424040290080c080004c20000350051b60803461020521320004074a00740a003811501c2c40e000390b404ea90081e4050003015102d650484141c6016003e0001c6071450103096456a0790f981d40000c2d0b40c8000c2120840c02508140030a605039100c07660312185e0441c52105019501001e040d105030000e20900418000d440b640d03009100302c81c202e440c8010114100480d03030006070000e4115070400c2e014805082e1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 257190638 1250 257189388 257189417
    0x503010807051005361f11100c09030201080a020a02100b010504030803040c030b09060106020307030c0309080d021605061303020f0409020d081306030e0c0d05100f0b09070201060e0f07 81
    0x51180110030342d03c176404a5001044c00c0786014411325001003401030700780610442e802810f070089500d5441035810701d1003500300303103000d124074003070004a002e00d0b417070f10703100d610003030782d0b6220301c100c41101e000b640c42e9040c54440900007801c034450b004010300964001c0101500400131031b0000c00003c5c1c0141040d90429680e0b03221040294800c64080700c404a8001083c030070440c0d602c00c00c6802200303950007840150b0400d03e020b5603902c6001c00207001d00900040300006c2510404002c00a00110800c0d00c07090058880086d54130304c410305919003490041c0002280c141025000d544c0300020103041615904d2540d008d001d90303500ca4180c06604540c540d2072140158690f03800e11a9030314420b007002a034074000c5914141d40f81d403854008400701410002c21440d10580080c2c0554042c40841e52409074000034a0920303d40700e00903038a114003d081160608641c0503e90100d6142030040d1000c3e8183d0340c030b08c0b60807800c0360341d5401580f20b4030141c5d0f808211250b07000034115903c0b41690030000e00140606 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 257191888 1250 257190638 257190667
    0xf050112030f140c0102070c06020c030d03020322030215061903080d062601050702030a140307110d020705010915020604080c0f1204050f0904020901140301020f1603020601060503010807051005 85
    0x1999104c0b4140c1d00001c02c082000b5000480c003000780a03603c081c000e401c21000000f9150680164030070205900800418003609860300d031410403807100140d0004902c0c103840e0180d2101030218501d16031031003010000c5d840342052500d480c00c103503801050742509400c60b0b03036400701c40d04645800e4460941d41c2c80042081c05052520351400d4000d0050f004c942d0215024560030b45030010140c2e021500184400d811840e001614003110451000825031203948103201201c8001e00c07606240781e18031521540d1203440760042041000d40301d0a0365848240c13034446040c02030070f510808907940142d00c04000180441e18580c0a032100d881f14900f50b8500c180e9602c40c10785003108208440c8a19080040c040281380b40103a4049820042035581e108685010b40005041000511507146208680c40e08609180d030294101c8151003e130030440d9440f409034a94412911404040484c054440d40002103191401403041c0c2c0c0c12503171140010700402d4100703030034088031030311820070344060190a000d040944d8100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 257193138 1250 257191888 257191897
    0xf0c0c06020a120207051c061514040605010201020702061902154002010f180b040303030c05070f0f03111e060601030b030309090408040b0a03020d0f050112030f14 72
    0x303940201010340850604058a8011181c00400c0d90b001060400844d111242d101260200800c40a05001001d040030405030500c80ba500e41c0303006508801003681494040c204012080540702005031944a000680c201c1c452000060741c8848203110454540c000c81d51005841c1c0200d205440029641c01d61a2110000550780980c40e04a981040c2d40780b00127503403000c0c00001039008404040c3c0c4820300030300a110210a0003034100b05214080d040c0311805610000300320302100441581440d591104402660464041200040c0c24045402456072041056480f00d43e00440c0b9410b8070300f19aa034110a14660b403c007181408290500d074466004d0034041ca0080c4a0b1012485464040c000d03e00b9090110050031030b03050500c0e0802c500100d0f1000425165480c50a079081107098483d4241340007180036941c02403598001c0000c9040c0301e00e0380354000d04090744415400744210007460000c04140c0340309014144400a58904040c003007446207082e030300040c001d82041d071800d1000413040c101c550707c0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 257194244 1106 257193138 257193149
    0xe011b0b040c170c030c030c2101140702161e030b0a060b0a05130f0506090907030e010e070503070b0a0f110c0901060e090a110a0f0c0c 60
    0x3410220094100141c4500724a1180c83c060307640c8040c0c4150700c0e03029024240a13005941000500884902c0300100841e4080da5948524404071092040c070148030b44d03c5100c00392030000040c40c118021035003507000d0305004040c14084106140c2560120341490081507001c000c001114a162082c1d0783e20281c012840e882c0e003580c0c4000b0340081d4000710308114000500108064101000f03084040d60b020441d402199908151100d81c0302c00c2c41100c1c2c000c00104200751a034505840541e9100c045030a000404c10501c00328182150611601401564050700c000d010b2854200030540040001900340344c0b030188030000007031644900324140400d000c080501c0c503656410030300035410410342c05406e01800c0c0d030791610010301d40189591814014540f2001083c0040c84900403030703522070a02400305142654203141110b24181c0304100c10700f0030905c84044400540c000b81e44a00508 = true := by decide +kernel

theorem cover : BRFrame.Cov 257014388 257194244 := by
  have h0 := BRFrame.cov_init 257014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 257014388 ≤ n) (h2 : n < 257194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
