-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4687
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:24:50.700992+00:00
-- url     : https://prove2.me/submissions/fdd69b7d-7f8a-4246-b41c-197f18fef9ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 842805755 ≤ n < 842985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 842807005 1250 842805755 842805791
    0xa030f1206241206141002070503061302060f0a030f0e0d0f0c170a020708062406070201230d05090d0212030c0405060d0506130908031b0c06100e0a 65
    0x10b0803a80010344800d02d040e4032405041c00544a1000c0b0b20200301194a030384692190680e484401e510400c4030b0448030004501c0000c900c0e043d1740c8084c01600c0c4039122003219040000517800c003243d200f00c00340041600c0390640009412014603d070307800f041200d01e01c44103008564040c8220078840e001482d80d54202900040d41c00e4410205140110181442d820b000c1c5008041ca10514200d1200007440e9040c158006081070039204c3d000261101c688031700c41171884c40080c2c030380d0703c00389050211745200c00c40c94920003808000b8010b0401c3c41601550600800c0f82440c4c80c1d171110409900818000c180d0440ca10030075070b000d080c220007802d604a5056002c1d56844101343e5000900034000005240074030078900b40d800501010f4034140d1a203c448110324042e0008031401030203051071070382c00085c10419006e2206c0c41500030044600d1600c0725101003014180d203080250200d0010071105081030b000b0480302d44074605203860204400c7c24140c0f450140b01010300000903180c00d01d0603480800328005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 842808255 1250 842807005 842807039
    0x10e090a0b15010c020910050a0e1018020702040c09080f0106031a091c03020711091b0f040509040609060c021212100b030a0c03060510170709080a030f1206 69
    0x7800c030124020b64a80100c0742c011000800075040207100041c000c1060030039510000703403842220307208801038444030314420755001100c111410b2108000100400419150034400c0403603540c8025241c20100d402080030380703803009030640010f8881340040181c80f0041c45032191059046c4000c4c001c0368956107400903440c03400c5800400304c001e0000800e0340031500f080080000d800e41c0c82480c1e41502c0c10038000d4001d41020074180c8800c1d10006060b641c625100003d01d01c240712842c02c0c08841c00c03016003185c005401c5440b641c00c20b040200404144c5654290103644100e00c01c14002c140011540717044015a1070408a442c15907201c48260000040600c5c1075400c1254008041c8055580c0d0034034504454200d0390101107100b00010500440e000c007508041c16030111620309200142c1d0710381c240100d082083d0001400a81d44c954010702d002c3d000760380c081e08100d0320300d410000340b502c5001c101c0c1007108244044001c151002c42c1800306541090550150403004242044228039024259456442e20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 842809505 1250 842808255 842808271
    0x4030c18020c0f1501120302100f0f02040b0702130b090a0b04020f0c1c0801080706050c07080d120c140306060901031508240405030f0a0302071703010e090a0b 70
    0x150180d00c12004035078150740c02224050704890062441d42900768603090200c20801005030840d00204004110325881030100e64180d0040c110210848100001840e0721199454029190304240300c030b07640039001a001134988000d070303155a16002d104015202071640c02d81540d0604262030740040c2e60f1500726665010302d00300300c04291403c9400c0060001c0c40b0340b0720341ea55081400324040c000caa60008803405041c2c40d10300101541c2d04100700546100f81d0074490110f40b6070103507409102c03c504c2440a029202c8868044510803521441c1403402d1039074800c0c680d00010001e0f011414408914005d9030f84c4c03c069824554201382c40c61012612600c40205890b001c0c120000303403070106920903402901c0c2c0414261810b140036031641145910f40034040c402e00220403200040d003410900802d070250145034424011031030503400a0401e80715402445c0d803202410780c00d2000b180420701960021590781c4200d081346643c3d40c1404091300c40384c013018014643d0782c5c0c00283c40d040017a0003000129040115 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 842810755 1250 842809505 842809529
    0x10501080c09040201050d020705060c0405031b100c0c080307060203070912150207020315040501060503011a0a0501030c050c0312100b1603080c0915040305010c050c0d0e0d06050f04030e030304030c 87
    0x12000941f01070300c14010002e00c5c5104200c10810001c8900020b001500d000328195039400d003a0100c42d280f6540c0040400e64400d10b81650401298000d080b07130035100b4845d4110800701941c0d03044980c1182c00030300e01690b03000c2d00003003000302c3c841e406003145010700624018001c00c01d20540322403d000c05132400c1c1d042c0751540010324000390740c1c0c10003541c051408400e5035194a40740920308140a80781c10303c1058000c3d030070090302c1c42c2c6840000c90703283c40c000d1004d81034030b200034549401180a4080314803480c043c442c0810483c8a121814002007081000c04a0032016904002b10304040d07200721684100302001b01404522182c01c01c0c50720080005400d0700c1c11240c103480b6500800d5080c49181502a4000c02c000c141c112002c0a11002d84100e901a038001c0204854904069486100e8a04804065003020f100c8062040c0034402d9a0005140500781c14120340032a43caa900700c0e0340645428624451590811041590018001c40c0f1900241e02640c103103803660b41c0d0414041083d0240c4090810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 842812005 1250 842810755 842810767
    0x406180c180b040c110c01051c090c0302030f0601030b01151d011e020109060b010e030d0804150903021606091a070f1209030c09060b030f07030e0f0c0102010501080c0904020105 78
    0x4a0b030700210603441d802401007000340326901000d41700c58428001044680240e441c843d03c6c07507001c1d0302580c0c8110050002001503000e0300550000500c0c02c02d0045440104000700480580c8040054410401c0c04400805455044d410f00300a0150140d000a00a843c1e04c021341d61081c6d44406415400054585015202c0070f803040140c0d01140000018141001c0c40948030701c0d4550f054006980c1d15014200c10407500e0024001102e0312a02c0600e005d8140e40700040d221983c91240d075825038000d01030030000f03240f0850028282d040d50b20346081540140d00080c1030310070400e000210040100183e0070700743c4415243c8043e905408207408900745160202060040911406c800c903480301c0b50f441402400758030064070000c1d000301c80a0209a401c11140030010039021031394070410f030980b01003505690450307171851642034443d58000c00c1c420401d03460300c03d20315910104100d0380d14611842d101401071301400350002421a141640543c180d40d03c4200c1c0090300e500d5060b502504a80c0a00c0c0003581d90f0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 842813255 1250 842812005 842812049
    0xc040302010e0111120307050403150b0105071218030c05010e0d030806271810140402060304020d0b01171515060c07030c060804060b12060606090a0302090c030406180c 74
    0x291084200c012000001041044240d8000b004204ad2440780c078620201030b080e44250710854049110702404600100700d400b000c50b83c60701d80c0f4125140186400144280048884030903a100d1b64400c540b5100100018842e56810185c0664010801e450358500324829450080034103201418050007074947c4041c45146000d403119005a11804502540007400c141205ca0000c00031410758210074000e170300e076001d0301c404a0300075902c020b007042206134440d441d107808110281d071020340101e900003001c031360442c0003840000c05240240b07903821507415050f81816000c1c0c2031100000c11944200448000c0140e0491040c40341c0e8009442507070500e1700c40e6080e900061829605410240150b151803034000707482544200341e90712561142c041404035000e4182409151411f84c0c8500041d900041c0010300c960802202401c40f6000007407482c01510f41c2ea8011803103a400540d042241c41c0e03800020001400058040c1c01038410a222020341344400903200ca010050036030160120f4854107506100182c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 842814505 1250 842813255 842813263
    0x11030705120d2304030303020a03061805071202070213092d1e050607140f040b03010302040b15031807091a03010f06060507061805010914060c040302010e0111 70
    0x90040a85a69404200200d4060303507403040030340d0900010000c201c205200b101104800c40f905104050150420b0b041d560b05502030341003140300c4010141d0f1684005108848400640715201c60f21000007000d040140c001810f0142c152030402000e801000300800507120009018120f50084500050a40113440c00c0000d025480200001c0b40e2090b450b60301010055040c4103181c68410040701d00290354003041920b0707030401443e015100750400c0000411442c01102c2444891001381c03100e07403420781001c1090509410640010b010200040018000c40c01c007032088810360902200d0035200c1b102080075500355440018884500726030704404030700303107050100540c0b8040c080d80081400340e0032186212060860030000c2403031080d824000c1085602c4614407803641541c01a50343c0070f00d4642141c03036000203442007081415881078010031100204c0d5083c413034805120322545001c0c005018185140d440e1102c05846001140c2c410001080180e802a881c0b404030542800c19603606441994480d0074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 842815755 1250 842814505 842814509
    0x320040b16060e030a091a03070804050f030c100608070e06010c1103100507030c0e09010510180b0a11060f011211030a0b09071211240403060b0a091404110307 70
    0xa00c5050100c1c4024600c0f02002614000e4520b5444040c0c181c1c0c0e590b480942071042001c003090207002040031a804c5403056011701d5019008004a5100143e8080030f85d00c5e5520a011404840d0000c0110380e09040b154022200280070b28001000034505000a0303506010014000d1414002c02101400400000f05040181701200609940c1c0450945041f00003a080460b1140e0010f49440c0211a00750300513504d0764000392024141c8542c48e0300342400d0280b50445001d003a02401140c00c04428415401d0f40d182d0050f121101040e92030b14842d05025003400240d4155a1031504040b040005001c0c918580a044841d00442841c0103101820110595642401255010b024414500050111500e43d0a0090702d003d8101c5010694680740440d080c0c000440042a409446080000760b2a110000d03e081c040d602d560001c0710300c860070b8440015401603108135036658989003140410318004141318014000d000302442100c1146410403400200140000c114a42c0b032844030003141c40404c14000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 842817005 1250 842815755 842815763
    0xa1b08070e101421010911041431050109020907020a050c011b0605160801210b0a0212010f1802030c1b03091525031707020115090504030320040b16 65
    0x91030701c4200c204d0340c0a071841050940c3c581c41d80903070080c01801c0c5441111100710380015114150b456803285801c036140b0710012003502480260b070008001d80c0300e031a10010700c0e20403000050314081a106005490100400ca4415034200e1495100891004105000b41010900e0001401c500e4521060030341940f41c80041e00982c1ba00040012040c5074020084d0030020070f032984185a80d0b1240f55903c6070301846030307443c0d00040001c0188001859542c0154024544407409801e184503d00e00e501e40c2d0394244d01400105400c03800400840d03c3c050311180784000f40b079000b03500d1071138000c18050907480b502d0b080106040034011054030400c01801502c14980d0010401c01c0c0b404c030300b0682005142c12401540181300b000001e05035241c010480824080c580c5921500380341d107984107020448450050080007503548840703652014100800c480c070b0250007007160001d01303818107040043c100d0383c99180c001550b0f080321000c2c522919002d810b6030200d0321007200255a07101201d03030840768a0302c0058010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 842818255 1250 842817005 842817049
    0x51207030e0909031309020f070519030f030c090e0601030f06090204030302300f0418050a0513032f010e0d230d0207050a1b08070e1014 60
    0x410541e020800c1a000c08007141e0342d000644507580074949903c15410720396202d803103181e800c0003001c04136009000082e200906003820b1071902d0b22814109403503040030b261400701941d858010141c110782c1205191980345030810034810780e50006040c2c9020f502641d0360a2400100098071a842a00076042e407025804e820700c800f42c0d0703944011000e50132502044015004002900c0049094034407040d14003100c0c80403004018100345445040e80d80000110000c1081c20000820301009050310071607480da0802d00015145030030746042c02140d4002e800c2000c5c526a50050b0008282d0203440c0100703890704030036244c0d00c85a0544040040348155112003400c3e50900303038161420302d00400d196441e5000350b00c2d07080f40c42c080c0300c601c04a4840140c0480240c90414040c401d214100c6a0242220a209904894006100341c4900040100390200ea080b000070316072081c0300f04007003808450010001c411620f10241411500c000751070405001c4d03564488102401d0314a15030380c480c130564150345410700300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 842819505 1250 842818255 842818267
    0xf03200a06020d0e1516020d140a020f0d0209070503070c0501090c0501180e0408090d05030d06050a0801020903060c0915040e040303051003050a14120c011a090c0a03090512 76
    0x282d11540d203003e20101140c0d040012500303078209400e50390b1061032040041e038509803000d010020041d0340340900760b8100c458010000c00040380c0170030651880104000030314145440c1d1041110540d8a44020b6004038282c071480e02c01a21862001364105800e820020b40303036074a12004488450018202400300d6003001d96110901850f45158030a8600030381c0c4d01c805c48076481b01d003020400c3e4644220100c03040c150700010041002507003d001015030042080c61000900d0712240d00d15080058402400d0395190010085860700d011102c0c02840020b0007075042135065000a525000d00070096480c140c8001491402d59031841d03010144c4032070304140c41e52902e4617407403801c0d801d10086130108d010074500741c0846c0030010024251812254808010408000d8039682c400d10b40d4004038136052688140410801d805a140c0050400d06040c20300005180c00c5c8603a07403440705424458242e00a502c0c070010302194659050454450310020b0a000c00c90550500d0018544600001c3c110140c1d600824a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 842820755 1250 842819505 842819507
    0x1005030105030c2d010203040317031503012702041103040f060b010216050105132c10050105040b0a0e0603190506150406030c1101060e0f010f0f03200a06 68
    0x165059030340c00c0c1c084840302c000240620007000c0307100034500d00d42d070741400701c003880c054249001c0a520101131042d00d003010f80c0c2e5035854500c14442c0001008005000c020851100881d401c0c014a00c20308034001d0141e04500704540303015940340481103507030707145512100302903403650f800401d0b8020610b840d9035500e140c642444500201da00c401125401e041c041b142e00303103601c00101e0745062086041034071003080ca844019915540305521010300450703001c40c00502c0c01e9003038951b2001c400402822500040b0281001518148010448038a000e03039003030140840d991000669003a9040c02012030740e6060038240513191810072840c00e6501410000800c0203a00442c160760201d50140c00e414002a110701e41080000c112008003030140500500c81040003500c680c010990100300f0382802d000001801b01c80c030f400d580090f0842040000c0c40030070301205000258003203004043c16182c41070000c1c181006080d58100d2480040d000c54102220700b985010510940321078041c00805800c4046c1e0b403044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 842822005 1250 842820755 842820757
    0xa020703030908030301050f0904021201060f090e15011e0e01300308040303150b0d0e070506130302040924060311010e0934030b13140412030b1005 65
    0xc03800642c2d0910001402c0e03030300000341c07411380d08024842c0700482c8010060107802140100706982c0080300180d0501d10000030320440001c0c100d608001d07900681000d2840c82658140081c40510703074072208018204451803c070031419915034512036030154074803d0b041c24410f040c80e0055107004505c0300c00000d840100550010320148100301540b00d072140c82e5968480210a080302030082000ca0001800191080e44005142c0184040c0a01d5803a15107520307214a0b000340c0f048000345070703894072050584e010070400c4400802d812207885103803d40800b0628030aa2452000034080c41d104c0c40518104a0980031845500350040c141640303030b00c419480d90014141520007550105101c0180c0899544210814a403e10010740806800e4550945145c41d1242d188204182e42d480b202c01003008071030f200400351036666035039000308500d0400420402c0c010140501040184e152054529240d0f01c00e01c2402c3c1d000e81c00c110480000302121742d0a801805001e030680e81d210307000c9044800d9107604a4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 842823255 1250 842822005 842822009
    0xe060901021306030b0102031206120304080a020a15051c020904090302011d0c0a05090405011103180c010801030b070f022803090906050603040213020903010501060f0e0d0323040b0a0207 82
    0x806060100340c0e50f40010303411114010102801a0400c00007500c0d80003812168580001c0e02400d0040300c4001c00c0111400c0d03070020b4114540c6900840d0f44c22081d480d041c1e2202c4c0207440c0102d10032401d08078804000e02903100b9116103c00f40014270f00b201c104102c07039606460807400050300c1480700c0040341c90000d00070001c981c0f101d210482c0150004021000008140b80c20760703400351078540c11900705010020314603401070040b2619900c40c6141c61901020304d0140d0b014580a120010080c0c100c01c07005803c21070945403844c1001165401040807071000b10711a074014965003440070340d02840000c01c9007440ca41d5056107980da9008400807151000451074010800c1c001e0303030344d42c006a45414105099680c00d10400da0b100000784041005850030020980041c0110840185012980070121303082d12002d80c050030200e13204824182070107070014500a06428200d580104200782654090701480480c60003080072400d0b516840c2400114104807000790072070003c6183c03601e148280013540c03840070b4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 842824505 1250 842823255 842823277
    0xa0614071707151a04110f0406090510020609030304081b06040b011d04050c060310030b0a05010e0c070203060126070b190c170a05040510090915080a0212010e06090102 74
    0x182c0002d507644d10034601d01030a00d505090341c3c91003c10811000d011010120030301ca9404200350b041d840e03078020082005101c1500d410314001e00e0103003004240503030007031103409640142040000024010007102d0b406640f080c1c189484240e0540701d00822442c040c04400c8600c250400e10051004800d04503048424818002c40056122600a05c00c000c0903100107240350b011102d2a005407030450091341d1704c001c01e4800c1410040d41d940381c4d14154401078581c40d80c0300b550303000144940159180c1c507990000c98100c01c1c500c2d01401e42d0120341e49080c144110612494905140c50207600b083d0b0542c40945600c4c3c0c02c5a150130384821601000c0d51240700120b4661420308045104240654050603002d90015807414003160b8000003110140e0010341d11008010041001141c03a5030344c03a800c1e000c0751110b0740c1c2d801d526034200842c403402c40314031441e4010040c1c10f1440030410800b0008085000f103030b040d2a85412002d0100e25540075003400d08028403d40112010000b5080055002c1d00d14403500c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 842825755 1250 842824505 842824523
    0x4030f14190c06090303020304171507032403081e090d050c030c030c030307030305100513090201092102040e280c0e010609060f0905030d02012301050a0614071707 72
    0x70f16a010b4600601a200080250700103000030410400c10900e41e0710581d202d20300b070b148a00c3e0541c0c42c0c404104c008031100d60120341d44104c01400030300c81c00000300e6000891062021001e085031103400d0346004040b10b80318190a01048981001031920654009500141c810100c502252070000c0e120308402000c54000d21035144002d60b20729002030207005840d00540903505c0c042658400b10f011f010018690f19002d054424005030544136120520303000040c030a000501c235520351000511001c020f0b80030091210410070307080003c170f070512381200d40f690381220002540c4c0c03c40c4c0510b6090403207074003018a1071590415121a400160b803494101e181c428101021685e4488940c545801020b0281e87c0008034800c0382401064042d4000005010789400c001d81c80b40d50b9900004d2803c454410710310300503511459050125440c0c60b07840880481d5400a2640542c18600890004002c80c0309030010840400d820004850342d103001c503203105d40c1003401a8000005920042921350101204582c0c0d124 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 842827005 1250 842825755 842825759
    0x2a0105190b040605060f0322121b0215070c0e0f0907090c0504030609081207050a02100b03030307140c01020c0c0f01050c0d180f080120040b04030f14190c 68
    0x82c09109400690700c0042156003040910b03910314800e5040204449031018210600000801c08186100f42042c411541040e90103c0e0344801003100c282c89220000c5c0c21800c00e508001a9245401045009144104035441e209035041c84078076540e4580c05021000d501d0414814400c0c21104003600c111004000c4900c1e099940c000f500850302c408070300c4c000040d8184030a1002403416000800e80f14003549230107003000604007400d01150000c0d54080003003a400180e017031401e9018004c810348070603160000c00403046c004022070f03140c2c44002c04100030000c5030740c1c0c18070744180100306950104615100864841c0040c10649548040c6501d03030921851740003d500b8529881a0122824408964050a5103944c010303810f5070052020300d51a0682d03415108045507062211405c1802002d2410001c50f015a0390410140f0704241030117440c1c42d10314104028400a410402150b080303940c05005440116203504203d00c042000300c00400f580d008818402c92000000002c03017850074000c48403092443c0e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 842828255 1250 842827005 842827009
    0xf0f030209121e1b130207060c0e04051f090203090106030c0311010813050d0309031b0303090b0702060f0f15040f200a0f0813140f07060905062a0105190b 68
    0x102c03980e00695080c03580b00c000140313241028680042500c51030240581400f10030354684d800c0d1860380a585000a2024850314450b181600030b4603000f05103916140e04041800d248a40e000c20b9034040c044071541c000000c9442c80310254400070007590030810301d40d01191649040d50000700403e130000c2c0010780c1e030400718018049111146000c50b0f8004010882042f02410030742c0640314000d41a801e106280b221401c4100d100340107881d219209a40c00a48402c540c0b5010384e21140c054070032421940030800304034241000311a01a0410852100070503103559004280004001000806802900303007181640c41e80d81c0f0790043c1c010342d4100d90401000404e03e2144280074000d03006100001001d5145010b4100c2c095144140c00822402403ca003e11440d00c0e801e0540c155038640741025030101700c5202c07103000c06000c0c50000d003001b403900c1513969140100141d1103024030031f003481c80014103020303005c0c00034005e1541d405102c10310710003800f00b032515420f10f114100da00d84020f8070241c00c0c40300124142c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 842829505 1250 842828255 842828263
    0x31081c141602010e0f09160809030702010e1c050109080a020c01020a05100c030b06071101081501080f07050705101b020c09150a0b0d0c09060305070f0f030209121e 72
    0x14001210740000c608140c004503070030110048401e800c241010034820b040c0d12600ba119100e10301a55282c01070512900c802024513000074031398211500140400c90040c0c1c0d000c1a17140d9010400c440765082151a012a10454825204005c0ca6503180135018810008641c016003020401502599092040e003001640c45408500b0024141c2d0480c07480d01c8180347c0c00e0707809001e2501c3c171840d00242601d0170f880840c00700d500140094035065040c1c0c00c4a60341d580c1c40921181c0c03040c07050410300c10104002001800010018210031104900c21002402d514414829604120f8004040303a00521000701104000c114005141e0ba01280c0c13804900604c3d8000110b0f5131078050054240f9030141d4400b03c0445800901d00380e9103a10800c0300d4000140c40e4211801303481425920140041c06401580c4082c02e2520194006c0341810306010410020076000b80b01045020181e0804180710444008128000d209040b02d0552140700801d00c2100154001a10500c07001400807515039002c0b42c05800d561 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 842830755 1250 842829505 842829517
    0xa05010614010f17090102041206020304020f0a0f2306030f10150e0d170a030b091b09041e11071205030f0106030c050d020f0c100231081c14 62
    0x3090420784c01c0c90304400030300d6074140e006940c3c000041c00c158071004410001240c0d03a009960164020090000790300e04904203842c1d04000b00da1030700d03200340740030318500b10444540301e2051082807181401c0041010000001c4500400900c4030703542e440e150b46a1074400d041551200c031014000040421100200440504043c640da00c807505e010302421f080010070f0b0f0000b0008c480c0707001b40c2044141c0024850001d409444000d45000c583d0200c22403c0c045c2c031030030041c07140700103070204045044114407041c201d40059405460100e80c1c04040700f84a03800091041c242480c1d6450011401011030919000d00a554481c0c90079645010720008122010700041d200c0645000c1c081d00100134460203540141c40c0704e0405d00781241130030455190b4101701d80080742000c0d441c00e4000780d81c0858000c1806595182c820f840c01c11420079540c1d80388818000c0d840780d04007080c40e01c3c05215131095078103000c400c070051a800045611b440088605540078028801498000c24a000ca15038540c1e18502e0940380 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 842832005 1250 842830755 842830757
    0xf0303090a0215090a0e01061e0903020409060b09070c03020610061e140d020c0f120301050d050a0203011b0813150f141f05031203041209080a05010614010f 69
    0x40c0c0700c200c0c1d000c0100900c0d04880d50800d001d4200b018045548811584034024050448a011298174041d030141601c1d1174820403e00c00140b0000c1402c1c0c20342c012224400b40da4042d00c0000303181c4694600900201241d001c0c46600040c000700b04008a6030050351011424487c2d070964285403075001d20f5802804840c02076101007170407440480500305401110304404892031800d030300153b900c5601040c80c0d0b84098480c40c2c202e41c000810010380c0d07204009082401d801540105043c0802c0054090f990106015461240d05490960001e018040000e0494503400900070000603990101110f85140801c6813140412071000010312828200d04c604050590026403465030389d80c11600c0e100042890700b001c07183c1c4654616140c0b01034850314251900c1134100741e031035042003400b0a4286200c07000c01d510192280c0d0000c103011035500c3e604010361750015404015204c5170544d0443c29905005070350064141807003100c19030300510505402180440700f000b1030740340d040c20760b100c0119890700044003c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 842833255 1250 842832005 842832013
    0x5010c0512090d1b0e0609040b01050f0409020301180309080706050a0318050f06010905010b1e090a031502090f090c03070804170705060915070f050a02010207150203090f030309 78
    0x1119807070080100302105000b85403040307507440d43e40c0d40e99000740100500c3d0040400c0c1c40042c040b04040c1351085812136412100c80e4814a01991404a0074605000f0107016a800c1c22200c03070140c807a501b003081710507030041c028029100500c0040c14440f00054007500094128240020720030400301d000015213030680d4039503190030080b41050300500444802c0e0302020151074022000704009211384409a0304001c0075040e0343d490701c11104156103042c2c01131480ca03e000c04c10308000001c032040c4443e05002200c5443c0d250303240240000c0c0860019031000e4521004004503001c183e500c0d50041215440840303410b5840c0c82c0009c1800001001181c12a001c90020008540100d000b41d5265034814851180101c1e000000301441249400903042140c032503104006020549106120700030f103042d0060308001c504c1c80d00b543c00615070094001c155003846800111403075118403e4048440041d040b9040f4520021040c154200079442140d840c80d4501803a00c0149992601100701c9015210b944010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 842834505 1250 842833255 842833273
    0xa0f03080d3e1213030206090c03071202121203160c0f060b1203040b09040614010203091e0405010b120610081504020d181406160f02010216080c0705010c05 69
    0x5000b100c0d01c204107140b07440018420807909052180c0f0b83d038881c41a82c0c0c050035a034501480d002c0e103460000382c02c2410982255100e02215140084c1040440f2181d011017005110b050012906911074004000307014000c80d1790420300e100b481d0000714040c400c110102c481c400c519210881d020007040a0003042c0c44844a200004146240c0141d03d0100f8010f0840c1c01030f5405502144ca554410760200c04845404921007034a407403d8030a0398010030241c050301003003a040000003512445141c600318441c89031500a008410360f4007080a50441d00540200850750319009001104d400c03032140001940d40e040002101803c10a1422039141c281d92526002c0e07446d603d0202414407141c40707625070429400c1c894080b032031700e0500640c51400880d00158010b10781c24200038090f0a40c1ca41e5148840c0e20a00a0100c40d8240e8070043c0c1c4802114500842c1c402c4407841c00f00d01903c95030444c03000c05101d8092030b90074004048028250100311008031342c4180d03500c00054540158801d00034001c0e800440c85 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 842835755 1250 842834505 842834591
    0xb1e0d0c08060403022505150c0d091d01030804050103020c03120c04090606050a080115021005040b0609060a0b0a0513170706030b1207092c01050610030b0f0f0a0f03080d 75
    0xd1404c0700200800c8c00c0e06240c0e080031141e00e0501078105101c0004d400010420021042c4140d892282c81140c3c0248559030460300e8500e0307188214458603040590019501c800e44105006580b00d0f109a6803464901d403d0106141006070424002c0c180200e1a03c0c1c0000b5100b4001c400f00c0c1c135111a03d0f26400c1180e03182c04030b48644034885800c41410340c083c1000241b04140103214051180d4480c101034070b01c80c1032038408e00012210082180d8000c5560040602c081040c0b001561020442490308a03a204842e080e061b40042107079201e04083c0c0070100c1c8102400720702040407016118241d40030025201800c0070801c0503645a8180d082e0354004240030701c0f5412250708011640c0d0305405012014000d0800b4040845940102c0e01c4100e9543e0b00901c5200d02d4001000940e80c20280350a10110351134500080b00d014003c5900307032052418017411450342d1a80070000d402800c034031407900c00a907a6414010081d070710112100340070b149410190450f808184203d81440b1080200c101c80c5440001c40c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 842837005 1250 842835755 842835769
    0x603150403020f010e03040306140702120d2012151c0c171005010501020706080a09170a03020903012a0813050d05040311040b1e0d0c08060403022505 66
    0xc030980450003409030410004400f401003038207541c107240c019541c3e1851810304008449030640c0c030b105145544014000305e55070006001040b04490740700381d03580e98a10b00c980c5009144400001c03644407880c150940034828840e010341544001540000c8242c0d80d988070b407a1607a056000f040f0b40c80035610025071808428400c031145100d10800c0d01401981d29440e80d1008101444003920b0103511101042031880440d000b00c1c1c1c010078003030005006040c10309130094885c90b0000e107990006503131200e1000922040c00c10802001c4508420f0a55600c070b034820040c0658812001c990282d0300f001d04669104503d0b000142440414081030140c200031200202c880a01c050300c00e5030107a8448500e100031030304c00d104601155201d48c5a4035a541e19628040707203c242c14141032031049240402e400c542d6195004649481101c10030b00f0f552109040d80043c00c540c01d000301c06044000c921001080700d29000400d54080e9020b42c08440300741503c80449403100c1c41c102c200115500d1122030800031402e081d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 842838255 1250 842837005 842837011
    0x605011d060a11030405190305210a0f1704030503090714030a02061308060c030a0b010f120f021c0203180313050f0f101d040c0203041206060806070509031005060315 73
    0x5082e039142681c6c0ba4001000c0c030601402c0c4050070429048100b0030007a040180c250507040f07580400a43c080d9800440a2500803045014207204030807540d940c0c4244070321301480d8040380c1c5140c0003425040c42d08000b0829001141c1404851241050100e1040200c01254000d030b0401401056101c40550904c0415040300a003003841d00d000c20004228580b090008a105030040d901041d00c0e40f800042e2141138070809511141407200c03440c40303042c0f42a48208a02c11040096501045050703800061030000d20461130010440035002e299260031001c02d40085000f10f840c0d400c3c1050000d850443c0716201d2245400d00900c498060000308590705080500e044080d00c01082c0e0032034a03c0030303000700f020791060400080c0025050101e07080080c0941c040d0285038282524100034942c04030001030342d80d02c0380d0b005001000c140c43c504201000280d411001c0a4030105007510701c2800d010364080d042e40c12458040c0c0c07190058405003044652980b25040c841c200040c010718089141440c1c0011041000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 842839505 1250 842838255 842838287
    0x103150b0604090b0a060e030a060e0c030d030905070b03130f0c09050c0a142a0309030319020105010e13020907030f240503030717030c04030c0303030605011d060a 72
    0x12204035416940d5a8040d0000308045a000325240c841c8034100110343d07800d03401800030f11070340e00c40c1d02c00240c400140d5600c075660301080c00103032100d41e40007852501303900d201d100307616100300c0680440e241d17459000b078291984110203c4011a0302e41c4814080d03400f084902e800c454400c02e920320003140035069aa10392318082c06107240100d840f0500744080e140100c41085200ea40050241200795118209002c0c10780c07090f040300c1c01c0054880041854040849205a411200402000300000c007807040341c00b100c10050440755921140000703d5606c41c111910f000140d441d0800000c0c0305c8a425072114800d240c8990300540d560318580c00c0158421014006404055503003402501c7e10000788150004040d01d41c04c0e03911000810006c26608190b5604132134000e400910007003000074140340c26101850000610a03450755564411455640140e5001509400001800005068140c3e0102007528000c0c1ea8507030340860f8595207000858a642005c1d5044042001101e080c1407040c000c80c0026600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 842840755 1250 842839505 842839511
    0x90a0f0b1e0405030709091b05220e060f0f0106020a0f0308070e0a080619020c0304260d17150a09180f0c0806060102060f0103020f060415120b18010315 67
    0x583c00444e252011942058500581e288511024400310001070340444100700100503050b418900400d0b0180e883e00c10046c0d0789086030000c0c00e990261504030080e242c1c56032040341c020745003800b0f98841158068900640c584c148000205034144081241107420390024265103031b0700030580d400c58540c40010728031020851000e0b030740c10490350340e050440001e000d000000c003d02e04101441c00440c4d40e030f14074000500f910400560398503820220a65080361251540e1000c01121110740e00000022200c00100c580640c0210070040e0342c000d80115441840300501c0c441a0f50707410419442072040b105c500d907110392250001c10a0484a030403400c503444501c000034960282c25600e44500c180081011903d81c426480e050101d2030041108070717489502440207004c1420451104c0c0346840060001074001c00340d170235015132242c40721012a0001d04281001c012a01076444008001d032940e10844c800040c1806040c0e402d0b8600041091118103109800070003507461683d03a840d200110658100384552 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 842842005 1250 842840755 842840759
    0x807021b210a0609050d03060608040212071d042009180325111c0605070203090607060b030c010306080d0c05011104150305010803071a04050a02030111090a0f0b1e04 73
    0x1d040c82030310401d603c1203002144030f56440c944241400d001094040415162000c10022680d005a485030002d4041c1c440142c0c05c10459121810042d444d0040e010701c03280109001c1d024251121001e100364040c0145a03240e440c07418035106042081004a6800508103000c541c0c017808420022034030140c5030b02100d00d0141e141e0384001c0001000606080d101d92101001002e00c80c4100d902142000215401c4008000303101840140840301d1a010701902d503640001601c45008104865441c64001c01258031140189024030140c00b134480f100e4000d0141d070740c40900d694084c2c090314003038030341d254003901210405400c1101c3d1296041401c0c0e810350348410605186040150050010300100359401c22003801c0f029000e0b0581d81d043c1d10041079a807041003070001103600440b900302d442103c0c1001020507159810101e18009080784069855480c00131103011854803c0014059414181c41c0400d02c07640c4e070301034282c1c8010144030b10240044100a00b01c2e00042c0040d9140212040380500c0f0b0403c0e0f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 842843255 1250 842842005 842842069
    0x30a0e01060e070203070c0b0a05070f0f0f0b060f040507020712050709060306021207021906020904230601030e03040e1302060c190215071104020f1e03070807021b 72
    0x2401d83c0c010f0b0250b040000c0c1c0350306000740d50781d01c0302c0941100903016151100c1d51000070802d01c21030901a20340f012022402e4104501414890640c540065440e01c01e42980d0901543c1a00280c40c16880f131035044007c0c243c075050a011b46841190540c001d04040f500e4240c03d44072040100070b0072605401810340204d482c1010f803140f02d000e94000c02c401a19100c01201d1a0b11107400501898295404400510880f000c4050f15015442e80104090b032200001c0303010070090444001801e418030700107078042c25500c02d41003103584030f20030990303003030061260705079003183c272480340e40514031108036030344001002070140b200c07015515440502180d141440c445031990800d02600c03168170241030b508141500394070704144e100200900b46000b8600d0035009544131911031228214042c001c1e41c002c103080f8801b50510040c0d4000344510a030642c0b00c251010307140f0b011340e4330031030f1100c1c04a208a004294524400940d00309400c4246803800040003c001c00c00108011a84090f40c40b1001c81e140d40d0030385 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 842844505 1250 842843255 842843279
    0x1090b0f0405071a0715110d2f04050d050c06180906060f0a080702070906080a02120f1906021905030912090d030c110607031110060506030a0e0106 65
    0x140304040c40340300c00380c14949821420140765600c0108942146050350b10041000004c803000580d0010003900c82d4603500781800d000c3d110341160115001004140103008201e20f810541500080802c102c845052401070031001282d40441c608a030364040c0301c00d020a051540e0521000d41c002c4c030486966100c454005003680d8407030b90401c6071100200c5044078090605000349504040e003112110304090017031070a90003038000c01044e4420000004041481c01e030080c06450064032907118240405a12000560395500c4900300490040520034031401c021000890780f1164110200c0161400440c840000d08a481c2d6103101903d030300740d007000b14460f051341c00350034008200241e817501e980b81d18050740d025045c4102c4041e401c0317002100300b107001e03030a41d144461010015450305241c50000101e062440d901c0341a8114140c01c030a0014a00c0145500090240c4001001004440100c9200701c415820703500c1611456401407004d00c08030305101072682101c4407546540340006001c55482940d4090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 842845755 1250 842844505 842844511
    0x60705070f2303030703120914010606030b0f0607030801030f11270a09171b060c07051c05071103011e0f0b191a0f071b0e060a031401090b 61
    0x300389a20003010241140b40b25a5003841c41c00b2806142000b070161005401c2e05200280441d41c2a03079501c680c0100824000c40300640d0050780b000700609a1140c2c8054020075064199512a541d91668004145080c0040303501c5554140c1d1407202d61392859990101c8007812032070440e20b1203010380e858445a00c071060765a20f85401c00342d00b5150b90880c9400c9400d5a5000350488180f01e041040d5034020404003c404212134100060b0184e139038030b000401c80504840c0c04070042c4039006010501181d903901c2c2d0003400e07425004030155240d81602c10000307000d4201400d52000404c3c0b0600180000ca000301804500029001d000031440c848001c0e00110240c444501c40d09400c0c2d610042402100328a22030002d28807001d0342c0c1404210940c2c130741c00580040901c11a04038800a220000200b8803840039904101815012140c40f144140f030030005100c1407200e0000042011107000036040c040e400d006020f600c1c05014615034500715141c4501c1215101c61031240c0c0e40d04e49002100040440401d0340c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 842847005 1250 842845755 842845769
    0x7060c050304030f030b0a0302060a0507052b021f15080a0b0a050a0b0319050a1b0503120405100c0201031e1d0f120d090b0405030309060f011202060705070f 69
    0x740e00c1c41c1528001e880c429152060004161074800d18910a0304e90585c9242500c0d01102c510b9118a0200d50484e201c0c860f0340c000074558001c2001310041c0300113030500300040399030720342c0111580d0100720801c0f0703610303101c40c400707200b00784403450000c040c001d11070740000c2c018011b4040e50b4403c20b40380c0d90340300e00c3d104a0540481301c0041d04420003000170305500c515604080700b0f10302841800c40e0080003c1d0f40c0c01d16400015070504086c03826004101c001c0040740301d015840415070000f101c0c98500314440f41c60303138070440340640078024005050300d01000c111000c0c0c0301c0c01403000f505250540030848005809040072030504d550785850443c03200e04210004448100401c0c04101040c0002c1030650701420002040c4403903000d02107241e4110700116070864109002c24400c0e81350f00034a40004003030310b09510080c2000c2e01c504203000620001200441c86841000101d410b192144d00142100b240244500d08509035203032103a100502d4064020000280100100c2e2300041d11000310b680c0c40070440e40420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 842848255 1250 842847005 842847007
    0x90b0705030307140a0f051303050118050c030303011a0d060323120316082a0a030b01020a02090a0e07080f07030c090606081512060c0d140402030d0806010507060c05 73
    0xf000950000188840080c40310352141800d112020150000403825074a005100c0302180400c2421030f200030314401150000024412a402d4440b01403c1c03031040c18040c1c2c1d00e40111047c260150a0010441c0d0484005600b661413080084882e021903800034401d1480c1291560400000304e4001071440041d08650104c070801030034008030322032402d16110900d400440381442044518040803540c0c022601090911000e03c2d40c40354100c030b04000d411900f4010780002116149003510849011f80240036454808025000d42c1600690703413100070035402580710912800083c0c61010315084044280f0281086445668880c0b0009082c02035081c008403180c0e100c410100b060103404880e6000420684100300301c454280b01c0d008046010080101140220030b4100f594280c0307c40350040c000900329810f80701e0a044c030030044115903024141c10901e076801c01007030380c0e9140200d6509a004a500030010b08034102810403c0c0c8031144010046414424103200000110720903000d440c03220101580d4031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 842849505 1250 842848255 842848261
    0xc0c051c0b011401022118010c050111030f06030303100603020918090a0624030303181e060501060207061e030e030f04180501051e060d020d0203041505190903090b07050303 76
    0x245403501464060001c01c04444821844500d0383d803c0b00c40101d055031100076000c7d504001625442101d000062181d8a0200b074481e007580a04007540c06420f035814442410741b91340c000c01d5035902081d2112190804101d00c20081c2038002c1d4000c10f2103480c0541202031907401c1e407030324208038903040311581d606421401c4047c0c1000100d00c18170018241e08050a0040e24002c0c1800c00748400303901004040c035944815100c1c01c1c2200b240d401d8542940084d58100103ca01c000a140354180d01500300c030224288000824400c1c0045492000e42e20b0507501c02814503201d803010803107014910580c2c4141039a509800c2003103001400200781c480710402c80f4030780c1c407032030451042c0901c151110382251191030000140507560b070b46104515542900200305102c000b5010003c3c215121f5101320312003035840014146c3c0c00980540103103105600070349070a0340101c12071148009841c41140d620060078400b40e50310003109860750050320b01c0b5000340307025080a510396002c1c0381c060740107000a4807264404410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 842850755 1250 842849505 842849507
    0x30b12010501090b030106060206011403070308030a0917030105061e0f0705030a090801060b0703030213050a1512050c0405060d14040f020405100b1815040902090a060c0c051c0b011401 81
    0xf52004a51094008007c0185084030080d00c4072810301450254030803030b2402c1d4605503020024240a03540002080c0e940e81090500742c002008000740c102c86100059510f005040708800c10341f03041700e40c003400061505031880d02c070304000500070350541606041480702001d503a00a80180249520420080d951070b6641ca0700178250681c2c81d0721038080c0340e05065083c0440403801043e20201c0341c0c14200983c8904202c0308004096042d50400f03070708007003150400521500b50404030001c020a58954550346a01001140c064500c201ea00107601a0204020481800c0080c01081d07942201c0d880001c09243e00800715074202c4e000e8130203550750740310026080d05514041c840c0c81e0b000039400420540d0149410f503450300341e0203040039020282a50400150f043d4443c0b120320906c451244039503070343d16910f03410700382c000750010030a45004210070080461080d014844000030b8680007482503642520308801c2201041001c035821030b40014030548400050707040c0b03043c68064542d1201d6001c10b440c031000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 842852005 1250 842850755 842850761
    0x90705090109110f0307120c091d010b030c0a020f012406050309120306040b09010b0301150f05040e0429010302010201110702061222050d0806040c02100903030b1201050109 76
    0xc01c102c45031400410b148078002c1c02d0202d411044018006584076591060113a800e0551001a20740460400380b42c0ea101e40d80c003241c0d2100b0b175082600c0e0311403c00107503241e0504000f024020502c2142c000c00109591406980107044c0d00b040600c1212001e005008410342528082c2c420b000b45010b451204002690081e080a000762841c1e182603070940c43d00200701941c0f950480f0a0001c0e6040020210720305464a030040442420040e14485c0c403940c0d50300d00e602a81e03000740300e001c0b642e6450500020f0454400d082c0045444050342c0d41c0c600701410f00801c01c600c20380107802100e0034480d0000b0310880a40007080a12107200d0b8030000985985140006801d540010514a0040c081041a0070050703071a9000c0d18805100c1c290b0349034003a6601c0780742e0307075082e180281c8684c00c040901c09a402040400582d1740c6180c1d155507100d501d84c0d00c400040c402640d01a079040d40160f04100d4024a01200d181e000c050a54001e241c081141341a038008512070601070303440c40c100340e5142c40040c809012540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 842853255 1250 842852005 842852009
    0x201201f09120f08071d37030b04060e03090a030602120714040b07050c1f02011a090a0e010b1e1e0619030f0204090b0f030a030516030c05060907050901 67
    0x10520031110b00c0742000c004d200c00c038020844000c1c40110f62880e0000c9415081c1c9000c0c074000580041c0a03100340340b183d985071400c500c022254813440e1400d00302c03200b03101c01000d0044962025517000c09407100c0c1e4451001e02249404440188828088003000d6514031902c2d1000354059000143d41d403c008032441d400c10002031904c0e041c00382d50b01c0c006812403038840840301250201880c2503100c01461500078100305c10340b6202e55202c0b080c1551615240390b03c0d189002c0102c40c81c0c00800203480c0104010b03100c9404501c5040d4040c0d44040080e040705000d80140240200c400000035403412810001500101d50f00d0320400c13a20102030000450341060154142c5604900c40c0c00c4480b80e2411002464074031030f03a01ca00007a85c0f411044120a00d02070b8101940000b10600155115915000d501004000003040c2920440391a60800078502340403c402c42d44580598550f0b10741018060b4910040712a0f003800c50421501050140104005011883c020070308100034200c01454a02000b0f220401a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 842854505 1250 842853255 842853257
    0x30807020c03030d0b0112020f0c060f0c0d0b03010b10050c07080c1309030c0606080c041103090d230403152901080705040315091e0201201f0912 64
    0x107841d401c156a900001503c03140f091080001c50100c1480740103c0c0c00785241c0700c103180424001303d00300140c0c0b500c050141c4600c1411b4011108665905e03018002502d40a851700010040c0400011000c0780d0301d504006000d180c05030000c9404101c20001c1103030785079807038207480000e640410700300b001030007d02061004110400040c03807141009000a281242c005840c07007080e0303030b4407070300102098001c18800802941000c000c108043e41c4146941d25444450030680c862131514040a0200910034180c0f4040e10344c84000b0020b95800074015903418041d0003442905044d800310040780c0510440040c0b01440c858101d4a60f981d003000303000000d0310810503103105050024064036442d2102814081c070710746400d10340282d0548a0440544591086400250031800d01900f00c004c42c88884d0050108284540342d8070410307007440f20200c02c0000403481c0090019010805108200b503521241588444110040d1041c0066a0200940d1000455100c0c0c81a9450b0f90400c81440803044000e43c86042c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 842855755 1250 842854505 842854513
    0x21c0c0203060105041512080403050607050a05220b070c0503010c050f19200d0e060f1e0c0610080d0206041106070c0302151c0b03060f040f020d0f03080702 69
    0x103a800651501d0b01400741c10b004954566281c0c8060b1034002d405401809502c0710a580e100090506a1442d8440d0005803000c0c800e048c082000d103480381088444500241e81ea450a024143c2c42e601590003241c1c1d0403010712150300f03c01280920040f001405076500c240b0030a0a10b030710340000d0500390382da250410401e106083c05a440c01c0151003040300c200098424038800847c40d034210540350341440966060b80703001c3c80c0d040d00f4001d01d00060035100b829081e46490707400501d100d04202c5280700d081d00329030075802c041c4403c44072000d181d400f803900240d0015001c1d0600f0301c1514802e15140040b07810369280b00301c11004004041c01400395400c614020310142c0302520b80343d241e0598400c410004175010314400580c0100384904140a8000b8503801031100d480f20340240064a101d4100d1020815540401c24258100103401d21400001c10701c0903001d002c0c2c6644840e0b088d00881801403050b0789000400d1910f9005030b0f00c005e450440a4450314824001d109142001400c810300100040c041d544 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 842857005 1250 842855755 842855777
    0x2d041802030601320a0f0e0a061202300402180c071106070c140a121a04150501081e030a0806090604020f0c0307021906090b030a0e0607021c 62
    0x1a0002091000c03030301e82c003026034000c00b0050607104604403100796444074410102c0c00035045d5500600b00020780c07600340d070381d000400b91200130424440c03618070403540486c520400e00380040d80c2a0700a040c146240100245910742e80031060141200c1d11001059040503050404c000c600c1c00640c000795001034800018218600b0986e02d540e1031190003406850103c0380c8000301505d9030340c50b007184e11076540f1002c00141d1aa58101da07100e200070a140c200e200f55800324001c0b450601011000140c150441550354020603500000c05805c00e002d0001d0341e2a0404030002d001125460141500a01417040103114400010542042860b5043c2d040485508100900206160b0092449401c10411101c69007686c803220000b80003445613a50240001001050051603520007102401c4598000d85954a0300a5860041d01c01c10391140074000c0410101d41041c00800c1e2580080e588c080096000001c0c075003c4540c1d003c0c070300b03881201c0c00001a0b000e140c070203001d6044070840500e50502e0341001e00b4000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 842858255 1250 842857005 842857007
    0x101d070518040e011406120a080d020f070516030c060e090621010e0a021309050d08061c0f0c080d050406080604141008121303082d041802030601 64
    0x12003048040c680c1c0e4074451194245658a6502600100140000030452818040314110700560111285440f0301782d400c02c2d11200c00404100f0400055000711400d1070594902c007000300941007030314100c0c0c01c840d050007954009a010425942c845406104011700e65246203417600141d05c0741c0d0000010024440c00b40c4004d900c40b014555000841210b03203103140b0f0b1b40b90720b8808800c81c0e02c2200c040d4540c04e02d40c034074031a11400b0507103440580c02a600071140b11a0f103040c680949800301d400505175440080034110f0503204003451038110380c00409400402d6450204080d01c918003410540b039030031128031188200300b2100c12050041c42d0000140c41c1f08861114040c1050047d440b07000c0601940e200000c0341c0c2e90b03d0b54080400541078410941203814581d958001d255814081c1600714403424500b05424422030007602c41d080302002900c2080b07400e5a0704c14040350000d141d08100c1581c02008000e5030340c82034038500d011204200c0c2260300c072454000f030b14000d403050202c1c44418900c10018400c0503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 842859505 1250 842858255 842858257
    0x50405060904020c1006090c020c1002030702090709230f0a030b0115090902070b0712020c0c0d05011d063705130602070b04021201140a05190203101d0705 68
    0x1079101224011380b14501c2007042d03414055085c500360701c8240340010200d040044d0384d200d0451041e0603800ca40300081254140684032178510300d400c025a0090140a005151402020341d100001c1d1409986039aa82c8401102c9450340e01645189031451604a030203e0900302da202d441c494080300e28000851940d00c03180490001030282c0d241e03601125054084841c083d441e403070001c0589020843d40e0b81407506081d5800c071010b56800c00010b4120010404d28152070094a10b41001c003005400c16103107034001c121181c1c02e550001c482c95502c80501c1c2d81d030301e240e0702e168031031318540a0058202d515050103030200c6102c1c0060000008040080584588054080d4a00d501010070000054584811800c145908a0140c2c0106410700028001c0c0420000380d00540c010340c0301f928006100102c583d11282660030600c40703258141c200200084680031103810568203d4501000042c175842c1c6801d0510681c0d0040f1104803003024000302c108848101da00e040c00031501d44088000080c00c2c00b010003401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 842860755 1250 842859505 842859517
    0x1c05070201080103140c0a0e010603050c040b0913141006020f0a030806040e01020717070c120f02100e04150806010f15030c120603060e011415010305100510050d0c05040506 76
    0x4030340b1080717000d03080030408216064183c8402010500003a03641c585203941e1036001d0141c480000d0501012424003030003401070720141c540c429a01420640c0035418440c9645c40c03421102e015980354000c0c2c400300151001c07001d00035441504254981c5050142c003a02e4515241102c0b000c80c1d00070407030003001c254080680c54000c0d00480700031940b44100b600c003901900a200000d40708007101c1880c03031501000c49009000b03041c852000d81404640c0c4225080c02d10304052400b42100105201c100c3c01441c0c09020f2440c48006820400c0003118000e000c40c0844000190000e804c0d61401c0341444030183c10400e00e401032040c06444e030816030a1804140c9041311000c0305e070f428035468903041c00126002c2c1c0c180c01d00462407a1420800640e032810b00c0c2d8082d1082d0414900390703502e40321820148200e5072109500c50103411044024110344080110300511000b00084030b042d0080e80c1c041010b43c0c0311140a502914117940340e079124001941a030342201c66540307805040c494108401c20a90701c0306070680381 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 842862005 1250 842860755 842860763
    0x4052a150f0a080106030509010605010f0c0321021b0106050a051203120a09152f09040203040602091c0f0204050a0b1207060207050a0e0114150a021c05070201080103 73
    0xc0c2403541a104100c0303004a40989080070408200c41506a9000103582e049031030994080c0496110036200e2800c981280c000c0c03a0000d09076000c83c20925000f59080e41556210f8900b004985860100c5150414807440c80703008403680001d46040c5000c81078041c091011a000004c0140724640030008001440703a00c1614081c02d09100c8915000c4014010740e208aa040d501c0c5900d145026420070000b40501203040351501c500003401010820503100c1c41020120360f923400c025080c0e00300d4081009040f01d0200a104078002c0181c0c2485459034006140928422000980c46a801004200040c4240b0700c208142d0300e4000e440c4800300f8841c961034152a60150740c0042c05807120003c0c1001f40000c0841c041c0c0000320b90291500b16800066002c0403604958281c80c0c24907241c4080205601162190180c04103003480107104a000c2c412901907030b11001480745400c1c00d140069000c0c05d410005140c00960000f4215082030340990100d40d442c0303075192801034034116096001170402c1c0030600001e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 842863255 1250 842862005 842862019
    0x60305191b0819091109071d37060e0d030c080f0d150509010b09030705060a0302090a0608011a030f040f0309080708011a031204140612040b04052a 65
    0x1844900c140510f002c04454110000d004600302c0c0c1c10b06040c1301721074003550350042c207401d400111036510510079001400c5241c00040240030281d02001141503210a4a040f0600d1032840300880503200d00703d142c0403450703890341058064a8000050310400c03460030800d000b03030b14070094900083da0068112020503031055980d601c03110303940491151409503207003c4d40d2551601251b01000c0341c1100180040701c60845407100c460ba00c1e00201c080d64011403110507015808040103004034500030000d000264114030b401400c10320003d000510040c001e40c003010100b45140010b209101071300b0481c1c1d104154005815145050402c8000e141d00d5004001820b0102d40362980010180310308040c90043c8040400c0f01c0b0042d4a03005014002d24114280244000340940e422440382004100854104440945581802c0c60300c4808d13140b1031080b21040d5440002000f444054a0004502a0086010300f0210001e0701d0240b03003140c5044072228000c0310ba1640084618400c01e0300080e00121541c00303036500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 842864505 1250 842863255 842863261
    0x3030a080714120a2f0c0a06050106050c0111031005011101110417070503210c0f010606170604051506070201030b18090d0807020601060e010513060305191b08 70
    0xc898881d0035010303a241400001900c2114440c0141c0d201d4002c52090404008880f84500202e4849900807017030401004203c00413034601e42d00e000500203420111003911104c6075607540c0e407002c40350241c00c820046a008200201141000d11a42e00010090400c086c514100380d22240610201440741d03504000d803600303403591415029000903010156480c503082d2102c0c1c981c903540811441140e0400201d12651034002594a0300045100e10703007203c0c0906600e1030617848900185684101e003420164400c10b40348660380002440f40e81d000f03102e142d460b5450804000750044044c0b01c090070982c0300300d04282c1404103411064a044e000742e082203801542e1038000744016000740c95100744290b44004210700041c61840c5000005220300000400d032460980700c59426103d005003544e040340140e0240c40107003c1d01d4022031000483c00b505040c80380c10045050312240b041c0702039420020009403641b0030f000c640b0742200c45000c0803042010b424001c154820742c01604403076440c8088401c0084005c04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 842865755 1250 842864505 842864507
    0x70b0f1b0f09040902090108060a150b033408070305010602012c01060503011503020f030a2a181b05071a04020f091f0e04020d02010c1407061d010e03030a0807 70
    0x20a0100e0fa40c05044983c4540c0d6423000c068a42e04100c0320700d0001c2d4240040b03006401404200201034601040041d42142c0700c42138001c4801d800700c400703030301d4106071550304540710500c84030080c000307401e141c0e240f0703030249000e000090940c0c506a1107042503a0502e503980c3c1d140007415280305c4203000a8a02c00b1030000348035003c140504043d078407260700355280482c03440540080701241810b41c0c2c02034030458811807414050642d134080408001e040c00d68603050500058030b401001803031251002c201c0d01c2c01c407503c0b0912803007051010881481d082d80e448040072600030191019503008056401d00e1420b043d202d480c0e5928246000c5640202e0040000000b4115640e6103401d0921000107030071a1194504036080b00e1418500c1c01c100c50000f00c2c0179400240700001c99840502c1194007a0000445d4810b40c0d005440359900041b044940c0e299519150000c1c0c10100400c80060000340c0d107401708158030b2003c044002144d080c00a04002d0484601325954030000112480c66800340740001c0c40c6c0c2e9851034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 842867005 1250 842865755 842865761
    0x1504050613050304170a0210080408120405010603080c03030603061f061101020c03040f030311010b010903061d030a1d06040f06350f0708040507050f0d020402070b0f1b0f0904 77
    0x219048628210040701001500000c44101b120310a5070201c11901611400b601d000030111402004552708000030480c04581c40415504903114100200b0019180e5940103a181c0041400b040c50780e0003c000c00030249000c20076160171426010014801d641055004524403e20780100000d1003190300f44c1079072104095049410303000112007960380722034030740c0c07104113035010f203840107400150b45484550a010410300c501c20050405846011171b451555072504080d00180b21800c0c4005071140c0010402201400140f650401941d580002c2d035206c18202544030f610380c0900c500407034060100348500d031110080303041582c002c1c2c00e040e003854203501c42d2408014061003490a00b40e440c5c03400340104171942101203005d840c0740000140c031a503c4000444001601721806080c0b58804201000207003004c0600c04000310016221141c0c607100d64001c6016039100000881354454004200003c00030529100d64200e41040000c042c0c030350140361b444280d80503060000c40c1180c80013680e68400c2d5210742c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 842868255 1250 842867005 842867009
    0x60f0a2a0f0c12020307020109060306060518030a2018040807110d151e0b0d02131103040b0f0c120114010c02030a050d030b100c06051b07050c031504050613050304 72
    0x224418800d02d4143d5009407260440041280402c00508011415600034040c8030107880190342e50b1400e00401419101ca541001d150b01a098001d071018500490100131201041800503e040e04001d000031b0184030515070b40014095404d49007009120018616104844c021034111a1131214050044002001c5024240004103c4403021504d00310028490b00101036400300e45000c00341041c0f9807540002581c503200c0d450b542c46000564548010b190250385480400ca8100700001c04444a682c00000c2d2f030300507141a2800840d500402c91070485010340203510040042070075080c001407103940e2060401c103000d084141100c94800d111143d1041314460401703a0010112807880d05282402600c50040024210019080c0888605541818002c00b24140402c0d0b607403c11215258540704c0c000d000c0588103103018042d2080720030a1000c0030016205e99409400504042c081c0700080502c0c0035840304447d50b0240f0000d003000b000c0b0340003003281580014145010401044a440d15078214804c0d0303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 842869505 1250 842868255 842868263
    0x9040c0f03030c020f09042109090606031b140313080f18030706020c030a0605090f01140f22020112093201050412110f060f0a2a0f0c 59
    0xc403600100345540700b00600b00c60360090740c100c0c040141003014003042070021240984454010103204003520440d0807020013030f401526110301c1c0c0c252690118402d039221640501c000980fa04914814094010740c400c1008207907042c00100c0c038500440300466800000e12100342c49403045920f4080c45004412070308403c0440d011a984c2d02480c1148081407682c803c9014082d109034400401d040c0d0000400022030a0010020000100982d41c2e400c0600b0f03001340b8410250003164080342002c0000d0103140d02d440501140801c3c20303d40140c2081c00841c004000d4171001c85103034402c80405140040f549403140d020b00c0d00411324056070f20f08002524800c1e84c01050110616100300b01e14480c0803004050840d90106641f142c142c40c9012400d0b00c4042e03030b029080e105821070080c1d40da070042c40d08003080d2031110181d0746030144c42e80f61582420b90803991550069422010040100f00c11f2081092035020843d9100c5001d6510446510b0007aa80c0e24050030f000809000c020068007495801900a0740 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 842870755 1250 842869505 842869529
    0x7050706031406041e020c0a0b070807081510050903240108010f09050303160210050a0209100c200114030a0906050f010614160b0a0501050a090b0f09040c 68
    0x52008001d005110301c6108510002c0700c44040f4038540391501071200007080321240c0c1d2490031518080743d4002d50003080c8500f0030344218860000041c082a40161081a103611000b18034a070003c0b02610b60034000f00380c40c4c408825040c41c01c2c0191b40391030850341d401035140380241d03c50544c0c00219103041100081110701d030300303800510541030045000250603685040000e010200c150b5100000340e400001c4000c0486d00b040c000070350050030034108080114940e20403500c1082200a9a204444007552000d080c01c0c2c000800607618144880c90107801c0c0c25914000e80317155a5500c2e103c01402c044801c0c84256070100f407040c84980e109880100d0001d4074400182c0c0d8a0401400c461300502c18920112205801e1900140001c2200c3c0b21690484a20f62a54400c3c0d4080c406100c42c2503000205410709040c5600e4110042100b510030180b040c0c81100b4005101d5040c0b070100902140742d940603c442504000c054050768641404245a20109440d128100c0d240d919060081c00352a411102c1d54400c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 842872005 1250 842870755 842870759
    0x7030e0109050a0c090204030804090f06051e0405060a0605030403030c02070b040e0f150d0308040201050d0f090317070504050607020f04090b0a2304030f0201140117120405150c03070507 82
    0x1034040380240718103210380056941300d952804c2445c140e001c5c52101402c10314081c081000400d90b907030095444030040140005231585c890000a61900350192000d82c404000400d500c03941c200303817050903000442181c0b8000103518244004000388401040142010b031039a01c16402c042c004c2180d64003400070700903542e07103564440384900c1c3c6e41102140d100342100b50110102d005080c01c08a8440000030107400c03400200c0481c0c0703060710040300141c0100e0420004001d2452000302911404a02488201d40420449140d0a0080140281460302c81200050206100b0003542181c1190b088410646101c0e403581c1c810300000304e41031005080c942d005410101020100105203820318441c3e90146010000a0090190100b408517102c1c550340020204402003008203024000a1090741307200c1c800170609041480d00741c0003403403081e80b040e40c140007400902c40b041e180a010f242021020099403600301890000040c0c00d440c1da42d41000c8030030301c00088440403200700384204c44c401c642290032185641d0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 842873255 1250 842872005 842872013
    0xb180a0e0a0c1715010c050c1e1f3501030b2401080a02180a0f18140408070203030706060b03070314060321040302220b151207030e0109 60
    0x7109005040054041c1003000f020503e007118044c0616030640c18101d20040c128019a02198500429a03043c895540168184d40d41c4540303400f1030f02040c00e24910500b541005000e403402c15101c5d4001d07121112030914011551100c2d005001501d03e0005801402c0c156061088480c01e050782c000c41046420004400d02c024020b8040c080c0c1c03c507502d40380007680092401c0d440341c5100d04a080c0011060b01c0405c06031084d5401402c0c00c9843d0042144401c1085000549000700030382c8040103d5113548420450100c9001c0b00c151044034105043c000d2000790a801030060030010f20003081a140461500b0542d207040003602c07052036001c0c904104503500c90f9044401a0411681781d030010781005060b801e11012289100e000f824094010400d4890300800c0d83ca04005200c1503a40d2010140800005a030b15148026050000d100d0031580010f41865844151039032980114050113120700c000302044d8181c81102e0300c1d2071716029a102c10340c590440890181045001602c1e0940c00c040040b0148 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 842874505 1250 842873255 842873261
    0x20d060207020108010b07080d110c0102070605060103110c100c020c0d03030504050c040c0203120411040606090e090f03030a02030907091b18060e01050705030c01051317040b180a0e0a 81
    0x410b000340c88031001e90f81e03103d0484001d0700c2480e9000780080420320003648403880301d4100f04400c031010412642808064500a803c90704003080507146507490350b0030301000b5609441040440200004410300d40041520300d2641c42d0b29502d02a9011a50303051490074842c420300c50f00003a10402818901403541314140103014113000d0b2003d44060250f0b1041d00341501d898420503100f4411a0043c43c140500c040194000c044024019140080304014080b4240d40da403040700045c0441e40c460b8030000c0c0c104281000e50306401001844d90783d1090403004510600003003600d40c130008080300540e4903a16107140504007a0b95601102c6103500b03200040401c0c24140010001080c455135820001061254003002020220b01c22400483c0c1d00b07070142c500310b5100c1c02c01015000e00440480703140008604245013103400c1118540c030203254240c284010484100548000c0c2001e4810090819042815042c487e101d520600e184107401219158020b80b201d204007401001d0004100d00203161007005400a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 842875755 1250 842874505 842874517
    0x402280201050c0a0804031d040e0106060809161e090903030b1008071e0c050d08070f0c0804061b21090509133306150507170d0207020d0602 62
    0x155080c800000c9040c0d049100355180c503440c0c5e81d165980c40d15075031420b4401d841009140786409000d01c000d61210380303c0380661050a901500001065450b00c04001c02810000c2d100044603001010200c60f1a010b20090704181d50f201204524a1503031140100702c0203081fa4069149207041c00355020070315400d42e112654900041d903080f0500703145800e00311015101241c942011418101c5d602c8200368190040a01c0f00120b0304142500d1015a02c9441c0740c06401200c0b40005641c03035080003001680496641c42d08186410841010a52540c07129a5400780e80a000c0c02c1001b400c9158034402d00785000002c800350030101c11110b02c4484000c440d0f010078440c4461012441d20100010282001121948201c003800d27000c005400d099a2810145442e1900e0100300c1c4407a1075002d002514807903400858160640340000328145082a0001e080010303041442c14006c0c180030040200781c004102c00d0b20780080d030050594490100401c3d05c024020a08082c0d0040101060399080010344e43c0146a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 842877005 1250 842875755 842875757
    0xe060417011b030203060307091d03040f15050705063403050604051b071101090509070c02031c080721060f050306010905090d0c020d0803091c080c0f09040228 70
    0x2400b4408007054040c1d00c81038601e43d030594001402040010720707030ba1125140305200055560b02d5400704c01c080d8510b07041600b1440040520a60400100122031011290301a1a051050600c2041d884040e2181c000600200103004c1c901100858004e01a0791a5451200e4030144200840d0640005005090850701180034038074210104150700c0d0703041083c90030038150f510200c1c502001d070f584041096803400f40305410f029101e0800306860fa01c6504045c4244442d596100c8079114074010140307490001c0307104106105600c085402a0f50b40216115400003a0307040103895040c1074101454401c003119102d01c00f80d850320101040e40d03a0b50038001300844070104d0846007581d03203a2030303e1130440d481942c184849a2108850391032150260340c40c80702282c001802012040400e844622040c0e0040b9a00b1070613420841200d0501526040e42420100745454610002d250a111168103440f40000c20160502c001c281d86045070b40c0e0b0380494500ac405084c8007403045244581a00b803101034105128 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 842878255 1250 842877005 842877041
    0x5040c0509011d01141507060f020304080a0305160c080912030a02370201180f09020309010f09020102061b160503090a060e01090509070219050303220b070e06041701 73
    0x20080324a8174564100b040092641428200d45688204140d1020300c040725003a0700c941c001301d0403000768070145101714052070400d0358132001300c0c0c401002c41c2d0004114150b2081d480b102000c0c25544074020041480d81f02e02d80540e10003062002950140000901812030321001901e40462035000c20407444048409007800f14002101010030490821042000d411b91640107503140990700c1150302c611041042900e40f824141c0320140d20ae505512074028604268000003881f064030024450f0382e182210090040003007011640c0000d4039a48058191105210700481b9000300041c6482200c034180461460010b561185180154036900720021051050240590000d10070f40112440c04648034140d44241585081004200000e200540800c0443c070582213840b074071040c00c126440c0e400d40294002c54680ca8207143c84502640300d15040b0402c42103032001c10300091401040c1c0b6420482d1404c01100340380d032102c0800c00714021a0300500c0c800d0406491104101c106500c22105042802042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 842879505 1250 842878255 842878259
    0x1080d0e0d080f07080c120a1106070210050a0e1c03050f09030f0f040816050906010504050105030a0507020a050d03060906050904032003091302030f070c050a0605040c0509011d01 79
    0x1079500364001818500c1d0422035044045900c0006044451103030f00a20b0520031055450381c5004021411480e01038000119407258079000341003401c4c4110104024201c514081c240203495050f6440103001e95910b8070f021549603020340e0002e40340c8a1011040300c1c10100c051101c00d2480d2141501880400d1401021441250b07804902d03d00c600c0c1040c0055141110700550070a00e130780103104a412131f031070030310010031425824401e400807602c3c075040350b0403500d0800d020880c4c1c05001422003818004104010000e42e60450256984482400d0000540f40c0d10304600b41e09010310004024540e0240444446480b41c140e4440011740e58030700c2c07080100b1a100e80a10020a409030307070140224090103107504424042c00c01104d00803c41c0d2041d2400c019510001c155441c0303140d12055101500130040061500301c0b0b0302030b280d20450b00c2c5402039151401d91540f03512484021800741c84207440300005400c2c85802641c1d1401810042c000000d80d40e980d000182e0009100342d2024a01000b42d400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 842880755 1250 842879505 842879509
    0x906030f060403180b030106030b0f1c02061303140d020d0201060501140d1118040b0d0804030209040c0b0310030614190e0f07080c0102060a021809061801080d0e 71
    0x18050a1400d0001418240c4550318140c82c82d60394881d68440020340c1103c081194510743d8040e6008102584010800700c0d040d001b08000b8800c0c0d076654600804002a220345440400072101c115990181d0306184d61b80a2586461407201c05600040e21940d1703041e001080240340040d0080d03030702d80d4980c02c0d500300c040351080c102c0c2607072400d01c544d90020724440c20f00c0c0c0c2440000c030014240f41407045400a00d8241d00c88289595070000c05420520320681c0f030409499061074081c07058a00343c1140c0c0c180c5e40f03039140d41d2286440d000d5800060f000d0842c80d4009010405108040c40c080e1070404109512403400c0f0b510310242403d5070200f1982e50f410420351814140144210741c1c010000303180e89810142036515800020050100503030503074030070350034100b55116084c050f12001d88141b00190820510b100000380ca0003801038503034030313000303204103e44140e03034000c215100c08032101101c482c51b05413200300020b41751017541c041541d49007085400000d191500081c405220a000341c0300c0d5005100d100003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 842882005 1250 842880755 842880763
    0x902010203091f1106060a33091505030603060c0a2a110d0b180712080307080702030a05090103020a0e0909010c110102070f062703030f15060c020907140708030105090603 75
    0x6d8164102c40e00c082c051041c01038800805090f00c40d40310b9045000580c200541c080c24400c508003d020038440c0c203051040c1c0c1d2080703140701e0150700340f4202145182082000f082d070f0f905000b45031200c015804102c07240e0191040a100840e040340c0001c01e8031119200c02801851031000804070303502e048542600c20541040c418078001c10b0b42180900c1c60b1750395400c641110311522100c501d60b80e406032210200700c81044d0701e810100a401401565128581084003800061024251006540c4240260708040354800d04542c5a80f2084c640940c4664070003d041d02c05191009890340d00880017020841d04145c15405903510041c00d81c0e5a0f001004014111401c034031940d800035101d01d88007080080410f10301d17002907002000c044030290b02400020384007401c0c45001c2d4400c40002e03403910412303c2100000d001d8403020b004a507002107200c070303e091405001e03000c1c4280700034003510346140000c140da0302607400b0702e912140202207165191104e00e011055a0300c00d004035807140e00e03400c004c42d41a0034002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 842883255 1250 842882005 842882011
    0x15030d0813020111071208070209010504050103211e120c0819090c0902070b09061e0f060d080a05121e010b03091c210c0207090902010203091f1106 65
    0xc026000d008540d800440783c555114144c0a0284601d0302c00140300d8000750340148060b4061000a40c4609107481088116003040e0b110a00c103604100040c004244154000040e4400c0e0005001c4010340480d4140c0c1c034446003405041d4082c409404e40d13100f030741d001441c030117164200290400c1551414542562403081c10fa03100c841010100407841c881c00030360340c0800c1e030781c1e400749405501b0740c0e1383d454088007641d20103141140c941030088180003102e1b02c100145600302000c1c04004110a0850158458550b0f0050490b220140c0e00c0340810400d8880140d440211908810000d64400c1e6a03940540581c0c84880242c041d0707201d840c0001d1003440201070a080f004c03400c100c010950b0746040e008880da6040640b10804078010002030244580c01051382c04070342c854948a412070884e60001c8950100500c1d012a1001420311000c0e000080e0b0109440f000e03607030310300400501e40707541d800100e2945c058001010f4000080380081d0780000107642e046c0038481141d640707415007040c10044041d1542003c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 842884505 1250 842883255 842883271
    0x61415010f031a04110c01180506010f06020607030209040914010516050c120a090f0e0105090f06031c0e0d060b03120c0a0b1510030e161a0a02010e0615030d08 70
    0x55018040c00c0c4c40d05810410803014000c941c02d090210705404942143d00400c0d41082305071007618500c0c10000700780074003401008403c000d2035599150840294071540e0080c8140101640003440c10125a910341c070885401d500a0054040c00d16400e004c54024070081c3c1c0c217101000c2c440001e22030340c1740c440c0c0e08a680d070301c0307012016102e6200008492600b5810000e43c03042031040148000c91102c026109103001409000c01a210030352405080c407100071030103840d5260b21816981002295180007031110f4800f080d0055a80001500c030000311000700d800c2c0c1a07140d00c0181d6160540c140300450f00f14840003a01102541d4002889a595002502c07404001c001c5a4112121140204500c44110f41e404000f400043c100c01c0001000203810405801d44240401e5075004002d02c10f82c820082c2401b403000700c5952035000c90405000c01c040d102c05110343c00a0040001300c506c4014401e402c03007807420348508112201400c1090404801031701d4010024001e109802d100e00c1540d01c107541c0e080c021101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 842885755 1250 842884505 842884541
    0x607170114150a0201111c0b040b0618010504050d080334080901090c03061a0f2d030d1d06070816020117070e0f0f0901060c061415010f03 61
    0x164146a40c990300f24107204001e44d50b840d840140c03800b101400510703a10060400d0140765000b81c00c000c07000c032003152000a004501d0040c09107090344880381203581c013a071960110003e90141c400103c405116941107e40c1007855012503104005100780035600032003007641902000401083c0d6107514000304908104905868000801040d0182c0d144641001c0050b0011904103019122042071801d2584100c0e0940e507200b90300c031218007071041c40401c00c8800b1a1564011501100018491b845020410a140c0f0441c0c0d1a000d16514074291082018005001e03100b40400464008d0118510303800d612181001d095007042d40fa00c2c1440840d00401ea014003280e041140c841d4140f8051a29280128188000401c10360210789010b0020303441080d1650360011001013040a1010a0580311f08a5028017081c034024451a83d940c0c4080d412740d949480d12100110741307401c1c0304016004081c0c05c038a0080711101402404140068104072100c02030300d9017020305031100021411034840411500f08054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 842887005 1250 842885755 842885779
    0x11030c0f03130c2606091015030215090a0e070813030c150c02010c0207121b1502030301030212060f011401050c070909030f0203120a020f0403050607170114 69
    0x8085000e550048440103080028403116510580710304031030340000c440815060a0200d00d0306412500c640c1d4103800401800d851b00f01941c2c000da807110600020310f003e6031075082c40e100350310542040d40300441d0000c0000142c00d0b01c064001d2030a50203c40481c0c006c80050102098144100590a02441e095984c0280d950703640000c050003200156422010010011955404241c804040b0001207003d0540014a91442c51020b8215000301d0301c40019500118410008400e0400b100001b640e00b050a1500401440c0108004003000d40c210315460b5056401120070b00354000061070681e4800e0385c50b41d02203441e2078005c6640d01c4080b01c80c0400780240070018407810002c540f04480303024040c1009802c3c000b80c00390150408100390420103080da0340304a042c050590140c000d405154080c0091480d16106030031146100400a00c265015500092190304121080302114010760700a070139140070341070508009200f1442c4d542000c84d8001f10a001040b20040d421074501c002c8001480403415038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 842888255 1250 842887005 842887027
    0x408030408090d08071202010b0d0c03120203160602040f090504120f0519032f04090c02150f100b0405180a06052206060302040f0b1803011a0411030c 66
    0x10b804045001d400183c032203900000601c1c464090140d4511810400b041c0007458000242110400c0b4030030703881240188000380100c1c04114400c801d4917007001d400c3d02140a101410780c030354130445491900c98012440c14006009540e4007410580b00c02d0264840000d9886562400303491003a10003602d281d0000c10000006070081c030300340c1c1c0380c07183e40d0030001d0a04014141b180c8912011540031404a80c9684018040010748080040d410044180f912003428009086003114011405064802c42c2d8813403030080f41c1c900030044055085080a00c403921441c101e01d84495080080e100c00409906442d008174410b00c0390300940f000e640c4042c0ca21080c2504074010304120800140403502d446940762000306a903194107440c07643c8031030710710348025002c03010380400340441d25564024400c16106000610215803040c10340760881d155034288a45500403141000e9080902d502880d43c10b6180c01145100b9070170700400480c8100003150100207409089003a01100d100441c0c2c4141680c1042010100107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 842889505 1250 842888255 842888257
    0xa060c020f0a08010b01120213030b04050705040903052511010c020a050402181008011212020f0f0c010311070c062f01141806040602030711060c0705150408030408 72
    0x62800141000030340c01032180401c8404082d90000d80d100c1c0d442d000000000d5802004061001400403030461524440381e1000c000c10581b4003006211040d083c0100381808000c0100344090040108100182d10302880c000d00b503540010000eaa8031001216406a2840107205003842d80e81c0104032800441d080b533004582c07444003107408a034030000050010400d9203d520180c8406400080700310700505019042005092100e02e03100300b0048404c0060003d59040400040384507404003800c0e20281823804113034142040d211002c0d0f0f40348100c0f801d454070100001350703641d140402a02e041025001c452449a0a2300c11018043c1a541803800c0030005284075241403409a450311700c410703000744084040308082c032041130102442030391251015003031903510104041e00304502000030321040060032996a2070302e50090010708ac841d1b0210018000f140a01e00c1c801800c0440d20a81d10b451400301c1d4828140d40040d44292441e10030103030403110540042035954081c581010701d10f41943c0d159a104031503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 842890755 1250 842889505 842889527
    0x114010903060905070906050d050d050a17040b0601180608160905090103081206060406020a02010f02070f0e04051b03031903180605040204050a020306060921161a090a06 75
    0x40001019001000c1401c0d0b100b030f4002d2a20980280291a00d0324043c2c20954085030011441598585011400507000254400f040d4502d800c010791141032001003520741d04041c0442ea058188100100810441249419481003800343c070364541c003955400059500e41c03c24000c40d00401d99030740214213a010004180e03907000b0380e24904500c805031200d010600422007a441103a00b2070b80490700541e070040e4034030308070342c0201d0607201d15080c80d1421400031f6a50113844006410300c82c00b03017500c2e1034082c820702011000d000350702d81030780116545001928182c0c10883c0c06031050300540100c401c4080a10220001c0e40da4010700031802d1054440e02001c40d00b80c201d01d003405050b980c92440745040d2440550040060140320009401d00c4d1900501c02900c0d00145210281ca104004000c4c10713a40d95001e0303c03002c08055030103101c4903844001080f420101134401d625070384651041a58031903d0180b1100c1139416600c1074a040041225613403141e07005605241d41e00900700c03942030000911a003040701d9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 842892005 1250 842890755 842890757
    0x31060c02121b070815090f0c0a0b031005040e07090b030a03090515040305100e1b03070603091716150b0901121e060b030d05070b011710020f03040308070c0308011401 73
    0x203c0e40c0d40d11a02c03c0d107131440c0000144410541079042180c0d40d401030180d10300801405010b0314000700b4007000901115842e0281800805010001c220a00101c8100350054100a403040001501d6451016506c0381c2d244a030f096a40e0600500844034240480c0310030352281c0c9502c500c40c115041204100200c2c114584900015909100c0003000c65401c203d941c400b07005014002800c0300d09031050b5030500ba480740c482c402040304908004081e48000034900100c420724a800121003003a85441d00c0c2c4803004204080c4800c1001c03403901c12141400c996800c641340b01d01900c1d900382030810010015241c0003160154030a200c040108020514642304900f1680301d600c5000c081c110307413070fa1040f40785003c003015107085a682c00e0381c280d20b08040041e078070003402c1030420a00708891542e0304075000328140103028030f0701d464016461031032500300178212880e10301800540d2070742c92070452117100f5002100c041c0c00142c2c403800070946541c00307901481401c0c2d41680d241809a801d040620300c0c90240309008034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 842893255 1250 842892005 842892013
    0x30e0d030b131407030c020f0109031e0206070f051e0304050d0809060907090903050910080106141602060a02010e06012d14120f0f0102070c150f0831060c02121b 71
    0x408c41d1a420302c109000e04e442500c0d100300034520720400e64441501d040c1c2c50300940d448401401a055080018a481c09800d8600740703960b081d41000404c40c000c201d128001140c0b0000c01030004010022a060b8603a0241c0c0c1c1c2d8031401603940700c030182d0b5104003d949004590300030354010b10092102c0d80103507041d98007034200b10745041803030f50220744021038003a410000520220010702242c1e601011490700d030001c20341080d04104045500c03d07440185028003d200b0b01001414030f12082c000e400a00c0d0b11070710034095410340c1da95540d114224600300a40c641ca03c280c540e070500c0c1038600c3c0d00720742e005a4032408242d01d45507003c041800281914000340551502c102c40c40007018080400c5446d122004840016850725074078a00840e180c0d44030b401c64000d802000e12200412a03101401c0b51004041d4a01059aa00c40b044843c1c1510b0342800c0040c81034001c07010b810840b01c101e140d0005550301c102820040c06151003002c070707110100d4800049031008100140c42c0d241d01d9041c200d08400540300255 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 842894505 1250 842893255 842893273
    0x31002190f03091707050c01020102043005010e0714030a0804091a0901140307120807020910050306012c0103020105220902130806130803070f030e0d030b131407030c02 74
    0xa0010004e005014120700310b0002001d00420609001021000d0300c2800290b04041c20094428800c0d0300f1040c4d90600389034184600301028000d040d148890745d40000c000c002031180107640c2500c541d00e42c000c03104410320380b80182405081c0041c3d40c03802d8980000d042c605080c14619a60702078221159400e2204118801a2180e6694401a14000c11484c08180c414500000600d418524150702c0720841404840c0c41c0804950702e401102d0b0304590441d003c402176030754868809020a01c82e0042d54052003444004100e5100816020b03050181c6c03890341411004c0200442e0644080c2404001d0010b8024400d9035109031443c0c04141510401c419103114042c4c5174603024003242c0103045070f09468036054030304218001c4140405a048110a4040b00b007400407600c0f2201103100181a404c10400d05000810486100b644528003440c2c1d58800c0c0c6a421922040040140c1124a0403c0c89191000c5006175011f03014400d07506500400c81c0300107200e55031204282d000301611680c03e802d6000305084 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 842895755 1250 842894505 842894513
    0x60607050d08070e1509100c1410050f0709031103030d090834110a0b130608061210020306190f03060c08040b060d1407080c031002190f0309 62
    0xc064401c86299a0250300345440480200300031404401070b8060403200510000140c0e0480444400501c16182c40b024800c0c500c030201c440e07400e1580050009400015409420f070f401080c0800380b09c502817810300c070071b4548441c07104038004240d4001000c52a000304c100300041c00500340a11f0302c4802001c0d01d00344943e0399049021790364240c508850740d080001c3e075440c5800c00140e02000035990080000d4100b24040050304e070081c50203102404181d13070030401201990710341ca8200c001d441014411034a6040f036180410358800070307003c2ea0340410160790014400b1f04044034410600d14425006045141c800711040b4000e51028210702d8100c000b011100405030038006624004012000c0540d80c01407643c1465012100240403040401c10b4800510001c5135000b15200c1e04104104c542c2458100c4a01d070121003041e064070344182e18040c80078001455480824581030f4800e00f9010384040c6c40c46140a80304034890382194640c4040380383d0410358500d1040d0708a2002d4203090800103001c01240d22 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 842897005 1250 842895755 842895763
    0xc0108040203211b010203090a060e0a06020414040f05060325051c0c0902090a030b0603010f1e05103204020d092f010e060f1201050a120c050906060705 67
    0x40014407000015101400920b10301c4131080102000f00850841c1416200b07180c41d2418003c0243c040c0d62074012400c89040140444130700c141c0e02c41421591103039a1a10081504490604144100d15040505403000214020349110700d0006000c3d00100307040104102d044034a40102c4242501c0d0800e003c00c03180c40e420f0f4410503444148004e41e840304010b01e01142102826001502d500f40180103201c01074135401510010360743d01c0940c6070705a83e41c000101e40140844081d101030f4900300701c0500d0442c102c8601080700d0700c0070000c0c1031040742e8683c0070101720003400c1c0c07183d02551524031010103c1a0410800e6513041c0d03d5a03100d051020f0f40000000301644c10114401c805a0b681e00306240c2000341c02504004045404406119070641035450b00e030b07803450f18101d100d0501c0001d44040203a6500ca40844001a104c411001e44420039580c46d020705110901416001c1c4c2080580442e101841e01c1903900f0a0744d026072010100c905041c03d2085038040a0f04564210b03605110240021368240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 842898255 1250 842897005 842897053
    0x120809150405090a0626100f0b040c050909060d020d050d0302210712050702030f0310080601080a080a030c090503150a050703060b160804050603010b07150605030c0108040203 77
    0xe4220307900d55052404208810a0150101d04054038100d000c1200c0e0710500100201041c824030059180e030f1081b41c51a042160307080e03030704500d10315001d0f0b203441c0c0c030801740d00000c8581005d03601000b590002d0182900c09125500445511001030400a100c92411014010400d88040d00c0f05141c1c00c620b80c0c40600d00741c00d01d5030703510220707401050400c000c5078256104d10004000c0522803142d030900800141804800741d0000c1001612203000606080c0200203c1e0888580400e000d580c030316101001e40000c1c01c9a01030052140100c100014855000040094410781c01ca004180352030074603113040d0001d01c0700c650100306009500d100010280d07004e004508204100d15860201864840c8041c81141d800130886000c3c540745c21418001d412544064407182c1007900d80d2445101c0300d03820545400c0c040c5600003a4405c070001b00100700c0809003c09003203a544500180719404941e1a044010b68546009140c0c1503842003080e6181c41d0b01c11155590418009402e46188018554118181600c50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 842899505 1250 842898255 842898289
    0xc09180a14151504050a0305010e010605090106090e07091502030702090612030a03020d09061e05060105180603070c06061e170d1206050301020304031710030c120809 73
    0x2490421000060340c0c000d200021854003803070034480ca81803900c2051001002c0c080ba00940c11501c1c80b506000004040318060540204075500c43c3d5920702c0c040380a02900800544c01c0d5080880016803814107c9041d0b050324082d0311001c0307005003000c0ca558004074004011904204079000b002403180c68510300081075511a0740516580d1a503801440080200600b02500881e06c026500360080b0020090343ca81c61075526000d2781c0e40c012008400040c2100d440040d241c1403800e10002c40c000203c920b009120340e40008140444e41e54100196094020140072282e106501c43c0e07042c3c41444c04900943d0310410b142031104140300d142e1142c01c00c0700c0041c3c1040c0000703d818040000c00400900d00e0b04018442c032000385c204440101c400684a40d0550658001e02c4290002607102d04500d4105201409002e0b000315100e1a10f401c1c003c00c41007201d14440c1c101111440819264004100200300b0f41e500142c2000c1501e14068a40d40c01105100050340d09240a00c29080f0940d5040c00340d07030b00007041e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 842900755 1250 842899505 842899549
    0x3041a120f010312080702062d09210403050a0b0403030213080d122a02072403180b0105090a02040305010213030515070f0503060117070807030e070806010e0c09 71
    0x1145030140c1e80c6042904e07100c05001a840801c08080c0d8001412580442000f000712280c03030307002c41c9800320806c0101301038900500c5001004002c00700050005890f480030300030102c1001c1c0407000e8407601d2040703000c0a0601d4008207441c002046043c10403e410900c607103001441c0070766048044c100b8000580210a240e00180342040e031030740d444580c0707615030b22040e4000c00640110010a4506080d9807803a43c12010105110301d018500a00c00d1400800c50f2101e184400b40894050151100d030081541c0301191034580700c0c100c0d030504500c04417200b560100f19101541d007040200285150011325004a1f50740801001c000200c003030001e4002c086040c2d81680c051800c526002c0e04020303c0030185958000c4210403c0901ca0303000c00c003e09124254103042da640c0d103508004032518882801e40c038101c85006403d0105640d403003e09141701e58140d6a04100f003032080100151a10314602c100c004540c8900018400103807032904050300300c00100c43c658130b802060804034a81c00301c400180040b002c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 842902005 1250 842900755 842900759
    0x303161e03090b06040b0105090d02120d11070608070f11160306270c0b0f190e030f01050c0406031a0d0302031210030209070c02040b0a080304091a0303041a120f01 72
    0x8079030051900301100305c5e0107022041320100006c08a02450200078403c9040c5039040c0159158000d0300c0f5240b106010940c0e0304440000310241001090074040c4115100740080020b529104004040c060000c07592038050b4088448000c540802ca008480f544038050385090301e00700d21380e50f602100254420003011843c41e0008491402440c8040c207103c1600382d02c17200c2540026110340d004420b84681d40352203a107410310054680064010b101072001c8240c3d040b1a820301032500310250800040c021400c964075403642d51072a070b098070016100152603010500c4107001c3c4501942242d40301c61400b411112428454100103540521030340702c25005600700058440c00320501e0035829a001e0b83c410301c140840740c5103a0105081c610b004111200b005040f101d540b0847d130390ba8000700c00c003a0000f002e10b03a0040c7c55140ca5503c0c2d60051103807042245c5403646507640b511f41c050585940312002000355080c1440c094481c421140001c0030341d45003072001c200540034109203c03040c500404004040f101158 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 842903255 1250 842902005 842902013
    0x20c012007270b0303190507050c04020f28080a0b13060b040501020d0c0312111905041d04020d0308040206041d0a0605011107060e03070f03050a0b16020303161e0309 73
    0x14003c050742600980017001400781401a00980300b42002d401d1400c82c0c0c0d81c05042c10080d041c1150300540d180d002d40002498004401201c000e40b085010342003a00652416442290b804122007034411404540b0000c0068844080e99100800000010386110a46078034407240008940482d008038075904800329060101c0d50b8100004c1403014003905099040c510b0989003e00121307680026000660385174401100340c00f400c0c0040e00c2d9241300344209081050407040c8003134080e401900030342c52000321440a010000300b409c08618040ca0b005050100c0c014a20b4504441d030810040007641c00240412000641e400d5000c03031240040803039a03585a590400d00d4985090b135101c0e03440541000110385021b540801c001c1060320884170341d0b04007010662122004a420141d00d90f000a01c4c050780e6070800414000c2c00306651184512800400d1055940d01c4071007030f102080510108c00581c07040c80000e0040391408030300b41d060b01e41070825a0200855411185480e038001c41007000080d02d48560300100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 842904505 1250 842903255 842903261
    0x81303080c061e0c0d021303060c03050121081204062703080601030623190f030b0907080307060c0509090114100e130b0f030d1d01020c01200727 64
    0x1000f00400a0300c00360811001842c41c0340164007680144c00c0d40010a0351001c99942904401141d01240611104d100305e81c0c0070b401044244150f1004840d0000c400c0103800b10818091403139540603003001d090049450b1043e1040100070000c49055941c1d28002c07590a900c08800b9404100c0e01d041c5c49030785021450004c28070f49000c0c0010341811300740035050011041800d076040d4070801071040f00d805820208002820103240741d422190740c1444d1440810596400c100c0703101500c0c003c0c881440c04d5103641c030981e60798010798410290550000d01407400000d40640208845c0c0a8900d08542000b0081000415001080e401144500c1807421941d00c0742c18130007044501d480f150f0501943d09041c16020032012054800c0040380a5550b2024012540e1141c0c240f014599016048580d02e2101002c0908003000b8a45200007010803001800f405602c0010840c504000c185c0d60034050080c800e0340403001100e00803520101c1e009114010800c0380410014821403e031448404078101403a0800c0022 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 842905755 1250 842904505 842904541
    0x30a0215070905011b02122104060503060108070c05071403010e0705090c130b04060f090f120b0411100e01030e0c0f09041b06120621081303080c06 65
    0x3029124000c0004894101c03030100c04444007030800d01e6881d00e2244200700030800d03543d8000c2d4400d1a0a09404000d01c0028510046081c98088900980074549240c509805140726103400644200001401544900c03045a085011810140c00512403a9101c03400c203e03040e0000644171865900550291409002e641800c911000c0a08602c03420000468042c14000b0000641d190000030000c01010114103003100903c07805403941d80319511203200410700e420484084001411804000c14040f0801d0f01010458010812a0302e1041c1030790340b65400c001d0000c00a881c14000c154420320b031a1101c0c0c90801109205a55603000403558900140489d01001d0f51071003154010701c0c040b0a151a0f00e00007541c005007c41c2c45071b142d9991858821002440c0c4040a0303076522000741c001030100d0b00301880e05012545a84c0a0002917100c0d8800c541c04580b00304241c000f00b10000c903d1000c98810f400034030351a009840e03280d041b42e4494441012170380c00103030310401c1d40d80a0001c004805100c0400c03084 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 842907005 1250 842905755 842905783
    0x91d0a0f03030c0c0f060b03030c1504021237060e0601090e01020403030c080d0213030f290411031908180312270a1d06060901050f030604021b030a02 66
    0x201a2002e490300e5081170200c0200030a22035031a140c5030036a98007001501c01ba4110f200c00c881e08064075184a0b106000c007550f04a0258008c040c2045c0044004140843e4801960418000701d00c100758404298803072031200001106d078a40c80100c045007107802010560340006004207015403400c00c021080f2101c90032030300241d13441400103000190f44545c800b105160440703501600c07200201500b400a21a40d84880341e4507142c00c2d000400c0003003103201401403501518500d5000300c0001c503030716000c0c400403421981240b1408001000230703030300b6100d0070b11074140a002c68103c030801546c1c0c5400707141d00c64000d0320481808200000c82030102c28a499a2060690250407000d40034100c0c00164000d1480c0310304d20055010081030b0240e410441c06802d100000c08590080790b4420300b40d0180744600f60180c080c4210100028800d04204045035144101a0341d07044c9000000705490074180c00180c000c0d64015000c00607200d844405032210500300319030801840d03807103403a4080680741001900e0301c6d80e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 842908255 1250 842907005 842907017
    0x19021b06070e150304020402090603190b01451707090c090302011b051b04050a09150e071503021201210b15030d03050907061701091d0a0f03030c 64
    0x962629502c003800d40c1c3c030910485098594840d840010068000e810318250003640107c100084442141c3e51003010303048540080002501035001140c02e07624410b80c054000d600b00300d002c1c0742d0754030f40c03a030310308030118080c0c8000400d414088510110210711b82c000103403c4000d000081307400b4814001500200117441081111945850015180e4a83d0b8480030b4140004800309003800000f01c0c1a959082da03018080c0d4201501c1c8821717101c80c01e50100d5503503000b0ba107044001b400700013043c4039441540f50805822020f40411083d24405000640c0e0307901da4034020040001030401d070404405403000482d44025890b0804100f01610300c101c16409802c801564102031400c038032106800781615a00701c00c900c5015980d07014034008111803172450035054403c56078011601380e81a840039014508103010740d034850b540c0b440f080310a00c850524804d51062a00010440f0245c1a0f122280c2c41d03e49444010404440d800e40070304241d8041700681d00e41c080f054000c000c01d03900d44558400e455240c1014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 842909505 1250 842908255 842908277
    0x625050d122c070e0103030518190504020f210103050d080f01030213020c0d350f04140303090a0b0609070c0f080f040b070c08030903030a0819021b0607 67
    0x803100d404003019040b440c0c4402c0e684078184480248100b1001e01100c0a503040076517560315000344681e001208042042c03c044048031960710782001044d103584032040103e5002400d08003000003d60048014505031502003013038402c48000160b04c503591885100c143d011a41c03442c10818101303207502001030f040080742c504103c031030840d9a40c807505481d01075500c000705070010038000000707210703041d0102c10070f2080b000f01c044060790040c0700c849620781c0944401d28000b0071803211400484080244018220008001140c80360482d03d5070b070b4054011424100385100406155040d03500a0300c01ea046034110400c4038003400040d0a210b41c000a007540c0a450300e01d40b08c0e10041c10780181c5074000300010800e4032030100b88502181601c0900e5947c0c80030030b0340c0b141e48040b541c0841d40018030441d280794030301a001986803000700a0314010900580503524022515038115001500140301a110761a000c580f0515026544041c050500e043c500e1703103450700400c40ba03031490040c1c000c121004211042442c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 842910755 1250 842909505 842909531
    0xc0519050a0f0302100f020d06060302160b09070b0406050712171303110d0f020709051312022802040b1005181f0306031e020a050625050d12 62
    0x18000c9402c2c0c000c9450280340c6034500d4100d05006400b00f0038140749003803107031400c256501c81c1d00410001d90440d80c1041503075a1200240c00b43d0080e4140328079007031001074111012984000d84240d0190f420420355982c0b5890310070003a02078120340c0080002850120b4060204529016020102e0044d030801a106c3c202e0000000030105004040e140b803400380408001c100b41c0181c9000a030012044150383e6886a4120020f080d841e212910400510800c80000340b9240140f1485004030000352042901c1200360303c0b0b407072603000c094961008610440300403150070500f02c660f8140843c1a8004801002e0081c0108000d5a4242c103015104034a00b8101c095090381200444010307400c0120203410340d00d071003800103151003010302c9102004c800880c40750949603410b600c4101074a20940070501d5014182201c0f010100d42040001d4015120300ca043c46189800c50107081190301c0003034203003510172820344007500c840840101110307141e002000102c00150496030300780701c002702c1c05403c001d45886211 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 842912005 1250 842910755 842910763
    0x2040b13320c0a0309020405010e0a0632030f01092003031c0b010e06030f091513030e0423090f011a0d031106040503090103111c0506040e07060c051905 67
    0x5000007500001100c038400781c0641c0000075a1740d0014402c03c029070303507820035000e40c0508849422a1528160b000300b594107a1001442d407030b482c2c0410700320380301d400d0b40c0c001810b0b1090090383d03d074144141d2a048540410074000d40c44001d1140790a40c0c403001300740c3e03c03a6001d81c00c807064181c0b01341c10502c841c0d07001c41543c090010b45c40c0803420b0041044215900143d5010074074004103a0404400010000108a0403a02901a041004c1203072b003018081e80e080e1070a824203072050a2612840c00541d030100f40300344480c025021000704001210030580340146045024031142030361502801d020008945802d00803c0c024485030b0009000c0c402c84c00c1c103a40d00349843c44002034421044074900000f818442c0b02d0b80d980702801d450841d5a230341424181150b803a0006103080340001d0802da420001080345400b66035920400202c13126030701c6c5000510714040c1100038215500b00f030399a000c0014a0001704001402401140c80b240c400c81021305045043c0b100c221024100c943c0c40404a10000d60002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 842913255 1250 842912005 842912011
    0x9080f0102180a05010522090c0201090b06030703050703060e012910090f0e0a020f03092a011e03090c150912020603060112090b01091a01030504050c060702040b1332 73
    0x4034030b07c19000e8045000280400d03c0d90840409246000c1c804e0a81f1a0154000b0101c18010040c031000c0d07640b036000301543c0c1c00355030000410a070052001040041c44581191445041d290000302d450b02090300c11003807604040c01c8100165501e8164080903040241e459403c804846c80c044a0315410b00c1c039643c1c14521076200d540b0030a0000c0001480d2010581c0c141d0340205412440e480d44c80c00c00a800c41d5642e90500d07803012074540214280e0084404048181304c0300c030b4040c1c5a420514030f4660002420402003d044010f050f25141d00c540014580440303a0301403e4110400b4a130100c030ad000003001e070100303074100c1c8007030034404071101c80980e036900240c80d4400401d18180ca10102c0008115015000300e0300028250320b911000031404c403220780c100105694480b2083d2310328000e620011410760710f09903400b03002ca0b040004c003550340d410b028006143c164000f50000c0340500a48000c10120041c1e05000ca460f41c2d51100400703039000003c04112080c0315031140107002d80e00b200b18107103486000030f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 842914505 1250 842913255 842913277
    0x3050109030f1709070b130308030103111203160b130b071d040203150d15050109330306110702030303010f05150403330e10110a08010b0a09080f0102180a050105 71
    0x210b58035005074112207087d030107194407a90803601c2e075a481c0380045214214042d4144280750b070038208915824008140e480c1d5040a485070500300c0c2064444000c0600060300c51400003517410420404a80440d000e2402150ba5030380c0d8500c80443c036040044c80c42d03a1015445e104034010418420103142c40d1075000118a8210b03444820544945080c1d0240841c1c01c1e5a248800c0c10301e0300006440302d030b03a80b2044115601c40c0c07009a100710f4018000c0740180c220104440410041039040c000f20fa5140d21150013490b80c050998a8894a174002070700d1900700340e1203441044a80d00003408103090421a00321800e002e118110309050031aa5044a00e01c442034050002e10340c00301d90039444a14140f58101c1c0c00100340c4040080d02c1441c1011511801d80119803030940d4104049441e807041140c048a20807200e40e40d40c004036034202182201c507a0701c020a01c00810601a90204200c0703018030850b56016181d0000507600d0040e841040780c401580200c0a1003010780b02400c01059030407100f1101e8480310 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 842915755 1250 842914505 842914507
    0xa06020c060a051b0120040e28020708030103060e0706051b03040b0d020706060e2412010c081906030b01090f14090a02040f0908120901020403050109030f1709070b 72
    0x106800c219031a000f000d500c513810f081460034a0166030419400340c1110b11032000128030300b10442d031003210345204030f100d440d080102040001d02c04000315803020f4603007190a010015410001d030b5010044c3d07045580140d44034140000104100000c512441c4402d09918002d8606145002e2014005025160352900a44001042841801024002c8401400c5583d090740d07201d00c16015040000d40180e0390484a513403a20901207041c902c00c501c15440b8203014184895414200250300c120b042070342008581049600e40a50002c4100b80661a120501950380024618000d0710400040030b52200d2103205d10701d0048140080303440c0ba501c51f8155051107a0224075400c501c09244000c245449440c0c0d06498408188012020702141c3c07044164021942840f0803400c070710700d80b400c403003a010b80101a250108030a543c5c40d0b91180300355a2240b0010001400d143c2c0d2501c549094030700d090030403400152040d001c1da22040c1c00084020918030400038030401ca1806031503d80d0349609a015115407154 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 842917005 1250 842915755 842915767
    0xf150e011b0203061806060d020a090e0a02040504050a12050c0a030807050c060412020709060b070b060d0611120a0c1d0301020d060801270c0302010509040e010c080907050a06020c06 80
    0x5500081040c100354054100e0300b403881d19005c1044240701c1c1560320b0809001d9140420b54628004104a00c0650000d0020314003d01e0415018000c10174500045002c2c05010500800b694852045d548214022805083c124086141c003541d0600b51391400401c0c0501030040310b0b0041d50015081503a940d0508100758907483c2c1d080151802c3c020059084010320801d0108000c1094006506803059126001c0380c801c540c540c0901c4c0190b607901e0040c030035403071001d00c07041c804603401d983c00d03a802043c050003103403800c1c441e500c500703040e100c1c454084280c00f0781c0041c40d040d10210400000360300042c241010083c2c181c02003002000303c98480c4070340782c220030510256038203039070298103d6962a564041c100700c6650f4402c15640070f08000540d9031040c2050301022070040340a0103811954a50002d0640c40e02c86c1907034010b503066003240d40540c2c1c100e55507003d40001410b0901c500d91904240d88c0320011649082d0030203a00d000b2031031700802e001e907030152002c00c101d9800048000c0315660880300741743c40342 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 842918255 1250 842917005 842917037
    0x3030c180d06090f0605010503032b0b0d03030c0e010e10080403030e0a14070602030a1205041b03051e160b0904090611030f0a18060e01061a040f150e01 67
    0x1c540800140c142d500c1c0c80c003c074080020000000c60b18510508050010381e0381c0710201a168080ca6a8420707040c008000d0400203c5100c010300e11001c10028000100720701e6400c0400c0160003103050440200356282e0820b000b954010740008286042480c040003c0f190341804940300000103a5070006014646004c1420180650403105020184070704840644410b402c1251202440008841c0c072402078200200c0c00e0362010003210b2803484a43c950305d60003420440d840c0f0043c0300090040c4e0343d802d92588800303590b502502e100310096020300003c20101200400301565128082c0c0740d4162075014070600d0000b1044000c0c03130000c4078440380c04507440e03000510208028240340d99000300307090310304218600c90a25083c0514010b480d0025901200d0346d48032805011140d4000403803003807034011f59400b80003440344c3e00400c003110034400020601031741d070702c800701004000c40c84161080c4801190922030151002c1001000b011100b025200300e072246000075104c4001115003e040190001d907a010310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 842919505 1250 842918255 842918269
    0x7020106031e0b0c03060117040312050103060b03012904090f3804050a29101403010207021e12030f0d0524012012091203030c18 57
    0x150b4010440c040c20340728604284030000d000c0791040350340b20108030114001e00c1100e415a4403861041c5c42d23524044801403510355420000410480c200300302c81c410441d07000042d000d164000c1d13210b203101041002031641051709554200303040009060b5404035005a02c07000f40100303001a402510300040214490401e00c0c018a00071101418004860700c03602c0701030203016540018080e410030400049075480542c0c0442c036030141c4000d8030300e501c004100000304802d0030076180b038454980c403150314904000e800da020000080303130000000740c0507550403c0b8040298026403900c00d0110002c40c40d0092660004a030101c800d2100580c0080c404c040ca1495100c0e0000380d2149010501101c1d160b508182501080f64090000f4030340440c10100400d008081d00400c40d0200781440c5107411b0b21604050046412050140c00e8248022000008a480039000d0121a0703150721192025551f958400051107041400382401d903a580d4410410021000c0441d02910070720160101d06080c4076001c000020f0031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 842920755 1250 842919505 842919509
    0x90a0f020d020c0a0317090705041802091302030f010e100e0a080409050613110a030f0f0c02030c07081501030f1104140a0c050c1509070e04030807020f01050412050307020106 77
    0x2640340b00103042c2010035000902001c202d0b202e40c1d44c00c114122a0b80740765511080540c0c80043c154407865081c00f040c82e06420a00312005a2090081c0982041c2c0001e546503c00f81c035011401c1c0a145101015424280849401c098400009120552504012981c4c2e101d0b0004448952a9603690305590035030203000d1003440c1c2d50001030780c1c2d4440f9251440c00d00103003030555100b4480c0414189619051503140203520912200100701410003031100400d40241c146040700140172961190407155101c0ba0384140c0c00d82d030311a5801103480d84103112000b85400b00c1600194901e80c456000411415101c2c00c0340c50660760f10044800c03190002e854200c0016220903040c942c0f040c2026031a4818845142440d0312901d0b500a091018002603d0241c3d5a0320440d581b641d40b07a00321810040081c0108005c154101103582c0885041607a56002e1030f00c5884140d0301200001c00540038003554640c10003605210842c0800204068201136448a801340b100d00041001d00c400800017841c201d000703601c0340d40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 842922005 1250 842920755 842920777
    0x90515040b0c0303070206010519030f020d08030106121d0601120503071a0411010c030206060103150f0b0a0f0806010c031d0d080a111f0e0a0f05071a09090a0f02 71
    0x9141e902141c0841d480750130454400c0300512402c800052249800f441041440c0000302030000c001e0f0440d01c4d40800603403081416a0000e401800760340000348004002d40c02091659600c00f8030340902c10045050761554100884190454441e1540040c808208641155020f54051031414103610b840340c194010040c0140c01e000400000755022844a600702e03125900c03407401010003140301d03001520001038001c80070300142e01c000b0010302554000d42c0011b486002c9020b08115155840c01000c4101d1007076046007502c03400201c5d884481c41c3e0000d824889100850030180998a0000700007003111003140c00103030400540d00a92403003004d410342011030f04072014240400e40d6145080000341c90b4003140b002070008121043e0044154408110000b048081c0b0030000081c00320700411402038030030841c4182503802110a81c400045954541176080c03482030010f41806481e00f003400003090100c10301c031400300004100865880e82d6a06903980e1000c8614000503002000780c5403d4002c0c003030707611040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 842923255 1250 842922005 842922007
    0x20304050a0501060f0510050a1d031e030d0615020a1101050c0f0717030a050d020705030f121e09101d0a150b04060513091a13060f020307090515040b 66
    0x410000042031655003906c000740d94065851081071021100741c07080311140302c0010030500160300c14100c011002c03199040c00404440c2015081d20014803506502c1e01800c002d0350002904400c01c2c40e182c01010020010b1681207140c0114120011752212105c40300185480282d042001c4540e020b03030182c500341a5240c0803901004070400c1c0ae55a224184d000d04030030a140d81030b0413546040c00000303d50b5001c03c2a038844d8200f030301d5008100e010b07402c001822285800140003a0084100b5070028010b130501c080c2d404540d82c141405241c00b0a100701c01e0b4620480c0050f820030642c0c41000400660480380c001d00055040810800b00c0c68541c1d4045e82542a805400d40d140203112461000300200305030301c0402c20000a10000b000100c91881c440c2980060316410b0700b40b124801a400320251600510200395140d039040540340e0500c0c412a810404c000f0340b191480c080c0112442385400d00b40409000714030394106204082d050120900c1a140300d40200039060740b6085054003564001d141d059210f0b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 842924505 1250 842923255 842923259
    0xf070c090c020c1c0807060e120307120504080a26010b0a020606040e060106120b0907091502010606050f0901021002070506061806011707051903050a1505060904020304050a050106 79
    0x440203000480c0018006100d4000c0701c1d003e500c1c00324082c41e00310ba98284009140310b80d503942c01d0042e80020000f5142c0d142e6881c2049080d65050080d003401008421500760b5a261455014200000355209842c6007460708081000042c104000c6415010990503c6182206c09000210480103520040c2c24813400352400020460181c0c00600f81082d90350302503aa0030b40d00c50040c4800c40b6510725080c00181e01000c01001541d0142483d602d0000500d200800d400740f0000115108070001d440403c005030f1406010818648030201d4514581d20074030081c02f0fa00c1c50030100804a02030903110302040703030000595480c641c3c020040c282c01e50442000646d110145401c0031502d541d01121130364040d00101d9035a1881000710351003603118006c16110f400041088078064241000000d010105209040061150746401480040025141030fa030105607494101c61403c00c0c0c031710701881406d042d03c048a0a00c07581d9501025150540c009a40068803992181030051a0150080c0060419444c02ca80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 842925755 1250 842924505 842924519
    0x10030911041d1507120b1c05070801141008030c060c0a020a0b0415051e070c140a0b090f011505040b030102130f030308071409040c05090a060320090306040303020f070c 74
    0x2544e21941e81a02c3d0013148814580c1c034241526680c1032004e500160300040042c500c00e02c1c0444022180c0281e00b1102000d03240c04010342114441002e525516000404006002d203c81c2c03080000b41c61034501860800b1f0710610655030b50710010b0003c80010b030300403445010b03840c4204200301300c0d250800c080c01c0c40d81c24181441ca8401c00d10009441c1842c3c10300e000a0702c20700f003400c10b41014041101c1780c841207a5940b8011110b04500c058101e0702e40d042c1428070304036450104400380c0ca00c0c0c0100f016030107a0408010040c0790a90581c64485107034184100240302102e2158102e080310815100032070080c47d0500024028821814220f10104440801007240000210703a981030b40c6c82500c0342844c913100d03500207071031102e42c130504a55220301c01c200700100d60600d0b07045082424540c3c203105080c05610400203038020200d4000c000085d80d11030488540e4138148081d4080f102d08201441d1429403072101083d101c250080c4003405050b00014100f03a003074440411503101a070002803900c405611121 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 842927005 1250 842925755 842925793
    0x170601120212190507050a03090501021306110f0607022a04110d050a0b0d11010c021f1806051e0c0706091d0c03060f060906071110030911041d 63
    0x14001e00701100448880102140504c65180104840d0300d031607040c80c840c100c1c11000750041d0038040302d503075400344601e8000c049441001c070068211512500340f00001e000c116807030f11080c0c2d41c1d10403455101805200c691a0003041104040c0107019034580b4000300110f000380ea4550000c14a9000f030f1904407601d19041d8075001900184030350a505002503101c10034900240d458103001c41d075100c540440108001500118180c1d4000c0d810304001c41394442c3c42c0c00003202d21100080c2900251002032250009940c00b2620507066400444111006800d1810044c0a406031030400002c0118448840a54603001426200d161004808545d001d6448540040400c10f50703102d0340d00024100001c6140c02c0200149180c13103801402e84c101e06564505040286a0074107181c2e0f55006401080002c22603100e00c8001d04030039001d05c41c00181c20a584051000f80410000c0350807c0519002680c1c000660f401c2959005010444012846942031984008000800500b050700ca00c104a0660341200d0201c1e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 842928255 1250 842927005 842927011
    0x21807111507021c210b0f0a0b09010503071803050307120503070215101212020d0507030e01030b180702072103021c03110708091f170601120212 64
    0x20241d50462800603803030711405609031075990168000100c400c1810307040c2010084044900d03d0104a021045044003101d5541034007002c0e0015110306451445041c010050203410348103507400c144042c580840c1c108907009040c00113041240000200e01c07030343d2051640707900b414010352740d03421480d41c4c03860b01c2541c96011100449280c00e1188040c4800c40c003a81c107a034402d6015402418550382c07000c507844a502002131466440780400c4a0109018010280c4003240921940c4110074400380140c5c0079107030100282c80c8904103d030400ca524002648a400d07108140000c0c200441c00d41949000180910b103015541c501910b0b290003004071007503000890108403800c0304140072104215030303807860b001c590f0707160041c025a02c6003d00c0100e000c4c085d1101c0646040310306d0002200f0700401880e40e0315038404141079401c1c050105a002a52801100000c03d1031a00500450004060b901c0500300d820315040800100381c1200010f025640181855803010700340c042e04560300ca07006001841040c03415 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 842929505 1250 842928255 842928287
    0xe121f0507081e0a0c02100e1e06060a031103010207060f0207031d06040e0a09140a0309050f10200d0917030a051603030239060c0d0207021807 63
    0x2840110b820b01603072480f00c4100b00c0300b101c00041c0c2c07a42d804160302c0203019004c20100851198041d02d030407144070b0b80f04d40312148050703030080c001403800143c0f410014410b0614603001904580203029290703542584034011a41d104008400012940b0b001070300900502c1f0015128a05042c000d445155095004000302d034804c0e1184104849080c0005a40c070100740b10480e00980d08100c2881000a0807042561000f041031011071407409540c2c404030280b40c4480c42d1000d5901c480c14000415400c0f0b0726800c0a014141c95018030724601c0302c0010f4612500c00726650501c1a41c040a910642e903203800b840105031140d048410807050810010150387d041e21801c2c03968400c0c9901100d1190003c0206d9280c2e403496034645003002100c1031100110f07c3c60400403028180e08000c0e28201c074100c1d240d1a100b4105902d00301050741405503405a42400e4810100d415402200400590180b070b00161743c00c402064100580b207442520108064291101c26184500d03100390801011541c4070382c1e40e410090354 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 842930755 1250 842929505 842929517
    0x23160c05241006081f0f0b19050901020c090717180106080f0304030b1e04150501120209012306030c030402010f0f090b030a021207020a0302010c0f0e121f0507 70
    0x1860320081c5524185000d81c0d4000784910010540005d040e45a50f405041400311a114041c0d903000b4086c0400c18951100c0090036000c2214203420031849010248030a45050451400c040c110000392110443c0359418407070783c1d00034045621184074032041000845012a00419403e0240b00700c016042e0310b04021341a5820b00d440464200300200b10707130200d0213050000b1130030030342960b0b50b1040e021001085c40b40c0c0e40b02c0c44010002e800c02d1118145000e9401546240f01c21880c01c4251015100140c121288492a840c07110005899208815044905501c1280035002e40c2d1301102d03a05e00b03111001c459000c0d01c080103001d00743c120100114040c1e4404d80340c400f03400741210015610307001c41401880110308610307410441021040000c6a204c88016001850301c2842c04240100340e8042d6451001a4020541c201c10540c0900c64100001d4150800d00104080050300030010744001804500948903103036240150042001500180d002c200403e1910011104c0f0303a03402040c08990325000100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 842932005 1250 842930755 842930761
    0x705121305060121080306011715040507051912180c0513110301060e130204080f0606090c09040213030f0f1118150f090c090423160c0524 61
    0x208013081c4920709100002c41c0580d02c9000c01500001c0105040c403544000805407004524080c911416443d04130305c810440a10a100c1228401404030702800710410180f952800411100c00302200c0794a0580c03000d07250018080702510300620f00d0541c4586404c0c1c41c10400208840a400792002920780c40749441c540404d50080d0b07840d0a88515242c4400c0005100851148550880c03034400607101c15028604401c41c08201d070310a41c070020054019850020707181c40117118a40c1c1040d42101d07010505c0c10043c06200fa14401c0901e201e100e16800102824440803003a6031307400071034005540780e1040343c507410300c0402d103039000030219090410007210b10050b190000a4010005400302c0380812690342107803004c0c1070307080440495440001c00c20803c005035103e2400610480c10108126211301959080c81b0070b0f620b5010608941c00e80003040c0d1441ca02c400841300d0f900c00c0c00f6407132003c2c040044550540d1007402103880034200c2d0249007042d821950080d043d040aa00f040d00c00030010396 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 842933255 1250 842932005 842932019
    0x7060912052115011803080304080403021003090308220606060201020415051204060b0f0d05010b100203070203062205070605090111031303060b0a05060c1b01141207051213050601 79
    0x102e0110b800542d038044090002103d548114401040300059a16142030300351281c07280d071683e802c2140c0c100e5211000140900450401c80075691032150f03035040522004247e030782c004d800310800a2229000400080c8034141c0000655200c09071250411400c0101a8641c600217000c0c1d8050700440440e442440e0110012600c16800c840b84d0101c0c442c409549070310f403540d5810103410b221140c0c541c040c020040c504c0441d039551002800340ea00c940000a40d229000c4280800f400d103801045065400c20321601e800350302c01045031944240501c0d01818010a03002c017030301d40c156200201038031900c2000c2001ca40550003000408145500362a0b00e21034014418070150b80340b20700d10400d051840d0f0300c0002c000088698104c0010b14400901c3d844040d270300c0d81d01040181e00b022005119540c082c045018160184000c1060801e5081c0f80c001c006d180c040b40742007c0792160b0a0400700c04000080000c18282c818011344010030380400e4000a03c0c240074a080080c4c10f209102501c8500408000240300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 842934505 1250 842933255 842933317
    0x8060c04060c03140c010c110d1103040306020901050c0d031a121c091517090a080301120c0906080d030e01150909080d0603140d0c0201140706091205 66
    0x71aa01c2d5940020501543c0e0100c0d60301989052080c8440c00030b11149035422828021014041100d1395403115a03040c0d02c03207091402c01441881800e01c00d1500034500715090120860341a00d40040c00907a65498410040301c2a100b9004402038900940d1112039030b403549034010081d080107201281c41042c2c8058100500d00220340800f007000c0e441800400041d1030124103040965480c0e06007844400d0781d64194100f44400240329800041c00c60a0944201c40d5145c41941c003d400d01005000d1070006030341700e107030130310060042284141d410305050041010580c9168050046c1c24010b108441e80c410985c0e030342c1c003151580400424209402d410083d80148503981129020540005500307181c00c1d040700003421280700c00d071810a010054054900c019014110046202e05070221070502c4401c14503040c29103800061040111400460300580e0340150403000000d003d075441542c1e01200c0c40d050b030041c481c41130700519101041000a142c542c109014008050303040041c142180d895203000488 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 842935755 1250 842934505 842934509
    0xa0509060c0a0806130204090606111b131107030306090c0c0c0b16050312060a150f05090f12030d2003010308070510060f0302010e0904020906060c0a061508060c04 72
    0x40480284490210340b8440e860302500480c002d845c80031403006044481060343d0094100d40d4140e80c48210402a040d40088020841d0015030043c054a1001e078078a030701042d510070070342c41c8038444403400e58169481641c404101088030746c1049549401526025019007598402c4103a2949015025080207018201c00406540c0c00034404021a050136004c100702e401400407202c4007015200c47c900003c000b00010921141410454030b02c03450f000c1d04001b0294140d41000c900c0020003100100c803d50444045400032505080450310b40a164001c17410044004560380d5004001200c00c100e1810040010069940c001c2d1060010787c4195210102c030700010421001c00036400c0004001091911004c0c00380d40d8411400c1e1412005200c5000c03040c2d403400e0700701c000b08580403042002150f03003011064290010070b9a088041d0711301900000c11a9400500700ba010307240c00543c900b68135100f44014007aaa5000c4d0003002400e069030f0700309910442d98014814036200d05004154807200d21010b9a003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 842937005 1250 842935755 842935771
    0xf0f03060f0a0b0a081b010f050a0e0d1e0b010803070f0204090305070c080312180d031508031209100608030a031a06030405030a030c0f0f0e1908060a050906 69
    0x21003070312140d4640c40c54603401000040c0407592250000c1996441007014401410b00394014030740056098005000d5640300790349141400300c1c140002c201d05409c0000d8414000160070480d2007441c500b000320f1140490600004c08400b00b4044450b4040b0f002d20729640f001d4010300d0083c0301683c84142c030130781e24460740c4405402146d024607001c2c0185810741101902c9c80c420314040e410a22556101020403810780c100040b02e410101d02c6c50501d05544e0340143e404a000f460210f508180c03020300945641c9582078140416032540c0c4c1c041d01d4906032081040051403000200d99a552000d0520f41481c141510340101d04d010341d00201c1d04d010046c0c050907090342d800c4806075240909070381d02a0024070044002c61582d0070181a2843c0c1a030714000514450f900980c0519a101e240850080444400c5000c810a00070a2000c9440d0140e2194030055028464249020108104030010f200113400b002840310311036001e04041407400c4046401802a2100c400c01d01103a1a1008000e468200440d0501 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 842938255 1250 842937005 842937013
    0x20a020c1903171308150c0406140a0201110307050403051902092406070602030406150b040504020d1e2703080c031909110f090c040e0612010e0a020f0f03 68
    0x400499040c21031659880880c1002134500729503007010190000081e80480c880d60400800760036130007958035180d6809240007054500d050f0406030080c01021303201c00003203400c00c001706100344454000d600082e0405000760b00c5075202c0c03510740d8000300782d0313401400201d91a00801d80c215032400b029000f00f1803820b6008009102981d41c1ea000000c00665401e02000c0c4210800d11400e015250b03800149940340c05410f000da600d180c43e05011054445001070700d03c1c00082000100b140401807400e0f10159601107a01603a00c0c00068151030280c42c00c0c0240741c0446814841c0700d01080c1581c1e0100002100840c59000740801c0581540b03614207070004080c0200742c5d030304005204480712900071984151444590720006590300e2420701242c0522070b044840007a000d1b40f000648c604200e12001810085400320040c0c900002c6202d02402288204c1c01510320701c801040540c2da40c00c0d07112620010344002000210351840b8655070311511403a09a000c2d05000160482c075080014852a811501400030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 842939505 1250 842938255 842938259
    0x504111002280f0c03050106030c05031605060906091f03060b040803040302101b0c03110d030c0b13141501050d031e030612080405040507020114040b041a010603020a020c19 76
    0x20741c1c0e10010b59003150300110500203900000e8082d6240c0c009540a1800001c0b07103421880c0c901020f00003a00118800d41c0441304144014401d01035045c02d45000f602c07020b494a241001203120b034054454000e6202d0a0000150303c940646540c1050f0100241e9040c040180d841000000074815801007003041e0b00100018009404d10080648104800d460702e81748442e00003070000d0305024807035812200b401420104100744207130024a044c0815049820706020342c3e080e54042c00c0102d111030f00400e001510000076202c40d61586150f0030030754001e48a94410392403045251340725011f8402e4842c42d00c2d1401e002181d40e0402148441d0441e5060301d8001d00700a6210008040d20f94a81500040686034400031528190036100c0b40c1c0201e01c1401d040d40c445052508000540701c2c01010b02c421a8501018249070441c03000c00241c01c0b83d0040700c80c0000e5111424208282d49214003840c0ca10552000002045a410f60080101001540c2500c1515050030100000740c00c070020200240000c2c6c03e82 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 842940755 1250 842939505 842939563
    0x191d16080f04080d050a02030a1a0f0108040f1703180601120b041106040b0405120c011e021c0c06050603121804090609060203040b0a0902240d0504111002 68
    0x8103030b80050141c860182400505010354090380d408680d8280355036004030611841c0032040c0645440b0a500400402041440c0300c0800c11310129806290b04004500003c5824007030149035000c60940c2181040340103029912104256034020341d480c080e01411507c8441c1002c402061860584010801003e014001c41d1980748c42000c002c0c00a40c1c0348081c01c1c1d50500c0c2a03607080014001005000c0703e0343d49a51401c010030004a08242440442d0b400401101d0b586030703401000b094942d00018080c41d180e03001d014040f850700c1040c2c0d140010b400070b0842950503090300010b918104a124a600b8416580c84109058071401c54004402d420201400045240f44841039840342443c00070300005940746264483d10261500c024050b40d20303590000c140700a010f0069100d41e8080400f01c1c090081450b0390380480e10704403a21100c5507299045895485a181e400b07400c54208042000040c0100d0916040c409006114100d40d40c0c031840040c0c0b58481c030300c0e00114418040450b0640482c0d02c518400c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 842942005 1250 842940755 842940781
    0x20301030201120603210215090d021002090306280f020409061710200304120207050d050d2a05010b090718140319050708070b0403120e191d1608 64
    0x5100c42540200390450140d00d007108d0344203104600840050002a4090b00040d08002e6603105180c4042e004001c0d5880c0c94030001070441d003202001c00d00c60060143c0c1c050290328032284401c155070785410100640341c3c501c2c080d006841039401c1c040081200c255503043e0302d40c0c420300c1c00c620030216800204500f4284101c96004152a54440c81c1d00d1a04a00c2c0c80c0c043d42455000300c5040300d001b0480095041d074070b541080301c03030040d1005681000c016845525220340d0b030307040c044032203080225645032110801245e01200c1a11980401000c0e84845c99180144c0a4003e07480714a000320011400146514407034031607485224043e90752840707440d091445500b0860810080d1503058814005564070301300150514031801401a400303040c0403030808010900707100440c1c4c0310017024202840305001045408901d210310784104d0074543c5010b5994404501d4004454018400c544104400085e2010000c402c541c50100c0b048000b9040d5070310720b0800442ca900305841c0c01300080801c80003401c80c521490f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 842943255 1250 842942005 842942063
    0x29040b0a02040906060527090429090f0c04050c070605131a010f0e01180218030714033007050a080703031406040624090306020d020301030201120603 66
    0x148001d8a080d44411012060320078550090002a10010700f4604420310203610103070640700e044a20040b0040ca00016003403c00103080a00301c1480160030201d803800380000c2004040b440100d901c494031303102145d941c940f841ea10460b440c600a14500313110614080c0700e128401c08003040c0311801c119042e15003400034480140b00004400b0803030443c8010400c188001840b40004070f000f84459818400441505500c03035019a8440000d900140314500203c00380c034049030840a0010b80f034242110100d2076030b01c2c000e1002c5400d8040c214002c10450202c1103800f4000c401601161019a2020010060501c1007103d045480700140c8180084118540c02041c0c1d4502030004c0744d00500c4035445402c81d1368480b6504801003540c81484294403442c03240050350050302203c4c104005031500e048940c43d04800382d0566400b400c2001640307a030f42c5c0100c01010181d90810400c54881918280b00d0f0300941c0300303000a0b40451685905e80c0a0340c545401100140e13984641494080c880c81c20180801e0080e0f8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 842944505 1250 842943255 842943271
    0x10050a1d06032a04090506122a04140a0606090f080d03020f2215020613330b0a051e040f0605030d020109030f0c020132030a02030429040b 61
    0x11020504580d0449003e8009417180c0d8000150324100507003041890b1002000700d5240ba084081c00d2500f64501c0b410080011200740d620b101902c40140009004100014813400000541003c0c008414120b51006c02910030584440c0681e0b0744501414032141c0a0b4419042d0750b81c0302d540b10b1402d2034403070340107041200d0003106100e0800d182c05e050101642e41380081c0301e201002c481d200700154151a18840030120440c0080c09071410102d00804d0744003001c400c00ba2400c00ca81e43e040340c0001344050200440051440003e4550034400c00040150003101c01c0c841c800c1800300808a598940382c1c00000d1b0340c80c200304840001d80091401e21015103404540b041010381e85003c000b90340e4400303003c15001081c3c41c0d80001040e48a51402500400c007455451040051805907440144d82040500d1780d05100c200320161003040d280340c9510b00311900d1104401e11540403090040f9070000d6009180214460080044490701c200800003100c1180620300c0c0c1c900c400c09003c07402148004030745640020740 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 842945755 1250 842944505 842944561
    0xe18060d030e030f010c020d030c0c32030702030d181e032a0605040b09120a060912020d03050408030105040509070803180a09060e0601110c10050a1d0603 68
    0x10000013030a18482607050000c41c0d44480304e10010960500c44c607512454070b800e0401401624410082c4288043c2c40020008144405400107800240d01514201c12045400d0000a00e003e242d0700c0e103e41040c2022802840f4961207544014001e495030180e0075441c0505a58840c40d00000806074124078080c2100380d94180c402202050702c0f0007a8078030009980c4c0307440c3c08903070080b607501780c51210b00d1b071181040040512040c4112030144084030400c1000700c030718411010505030240e08044500b4001044e4520b02000700b402c104c0d22251180c41060103400307070b8003450006030081d01550021140105482070800040c415450585d0080c1d41088408044801d03880c4c85481c1c01c4c0c915480150340d83d401d21080c4100c101186084404400030303119120741449030074540a0381c500100320107040079062003080390510b0a00341c0200f20704008032000078180c070506140749801414981c000c2210700002501e0b01c540003065608a01c40000d8a4009070201d031441e550700c07144082071500d0f41c4003403200c801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 842947005 1250 842945755 842945777
    0xc040c0e2707080118050c0f0f0d18260d0e0f0703030207080c1c030c0f081c050702010b0a0605030711120301050a080f071202121504030e18060d03 65
    0x1e5039071100d11a01d900e0322040c20550504602c0000e00b42030040305070343d107824081003222008405054031410101c03640f50329111003600f9000d9500c0e002d410b2081c501c00e481d201946590008140b0146000c0d8003558034a043d64074006070040e079000d0b003810f181700c4940c020000702d20360f04402c2d4000040c03050b0000076200b41501003944142040010f50003030340103900200042c49903900c24803114809842c110b807940c0d510803c08618a0500c01c8102d800f40520401a03460414000082421240d09500c0340300300b0b5407a004044a038620031400124003002618060015900c9401489175840000c0000c051441c820700d03003c4211255407005000e40c0820080c070000c007480c441c04000c111314040c2800c11a58485d81044180064414190301c0200194030121346007118903c041090000e8030450443e4040d880a1030011030b4034400c190020303419a11450101c0b0703036005070021070b140c0114401c0d5101d00800c103c2104001107002c144004c0041c0404000106100d4600412242c00e024031078100070540309 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 842948255 1250 842947005 842947069
    0x15010c020301020a030c110a0f120e0a0e09010b01051602090a24080c010903170a0507020904050619050c0901051b0613260409020a12020307110c040c0e 67
    0x180000b41302001094403100300707250301c0390080c1c500a1618a0179008000c11b25040d00d13640c007421444000a44100341010f141c0c0e245ca0720540d0700004469016018481581e6149640c4c0d503809001c480c030080300e5103004041c3d0790302d40c410804c81e23115540800003200c036101307250200108200041c01441c141c40c1d40705407603904129074040c82d0000e1091401020b00442c070301804c0324100395000803114104a030205007400000c0c541c120200c10051420212504c030758001205469510440c05c020758400c8043d000c000c10400b00240492107043da28810503d60180700301020b05860741039407440002c8030248602c0c802d0707500c9007000d4240c980707140b42c0800c040e9000c80c14690034404140d4004020800c40210380c8203009440036003064001105440314080e5400044031a280d00680c0500e08602d500043c602d0300f820702c202803510340d0703e1941e4411980c03405c083d200504171200c5080020f007035006a1100d41014602880742a410f00312540300d07034841001040c2000001c85d482021000240c4160008030448 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 842949505 1250 842948255 842948257
    0xa09170a02010f08070c020406090212011a120c0c152a0d020a231e030907031515091d01020403020a0509061903051b12071e17010204150504030b15010c02030102 71
    0x1010071348ac0050f030b1409801c901100108050700b0000303c2d40703040768040c03500140600440d00d62001d0914480407a417507282e5004618400c1c1022a2402d00c41c152911a440760503041050107000c00c004030990060840e1007060704880314050015604006200d4080e5483e0319400070500e50744681781100300074680e61001032040201d0015245070500100340054206070115106c0c1c903031ba556495150462408213060b9680e6051800000c1028001c81c0a0000d541129001440c680c16620043c402043d154041303000180b10036035070304501e100d915044207801c40c0d041c400c139410369802500c40d6144a0038101481503240010705803940200c0c12001e4903850b08410381d0110045d42c8584081c14030102d41d80c940080400031100032506c160314401407500c1100c40000c0c06021248860700c50300820360485500b0442c900c082c0c0c003007142d115140280030054101940100113031030206020507041204468101c0da98000ca0100515410307003071001c038043c803100002801036510149485415404641c0c00300e426 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 842950755 1250 842949505 842949509
    0xf0f150102011515020105060904081801050d2307170a15030510090308010927050f07030f060e0c0d0807050c060a120c03112a030a09170a02010f08070c020406 70
    0x45050700541309010503428000c5940184089485040c14201625807481e507104000c130a0015100c2c1596078040d5901540a03202e0340d4400030410000400f1144140c05011a00b00c5940c001112043c000f8011a00440d0040c0c03241a407101d02c0546c60303407841c030550000d010070130300e002d0320f01240007000000580412282c0c1d41410000c00c08a480c251070300d0050100300301a041100650b00388003240034801c800348140e0780c119413100d80700d104008141c203005040018401e141e50450040c06008401e216005a40d11811407043c50b040080c0a14210f40c1174480f0785440d0f84550020044511802299040340501919405801501c0745a400318000079002c1c1c2c0320140c0a80442c02144a004580c203e51040081d4070b40181002d0003902094041c10015119a40d010b05824000041c240c0120030704903d07410f00c680c00300044075518070b404580a801ca1b4058403a07240c0350b1817080c030340a41000011400290315039045e1107402101c040c2c03880039102d42100a01da00b00b0041180340300c00160743d69010b0310780 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 842952005 1250 842950755 842950769
    0x220204150308070c0e07050a08060d03270503060c0a0c0311010f18110907020c0d110303070f2003060a021b0d120c09180e101e050f0f1501020115 64
    0x72043d0301e4080045d5910a008005e00c042c0701e414005640e40c6900a0426540400d088400c40c1542070030740f13003d03940406c11441842803c1c50403c80380302501d483c0300d481340035190308504aa590b55240044030311184146080d803000661807110800000c1e024407140000c00301c086001154075001024220211001c91000c62030501c03240315540184035401d075410400b00000e46003890541f4210102941d50341d4442000c60142a24007150340900a069104020101e0018145d07079a0721242d00300f000ca0811035250a8070300718030241420100500c04e1075a1740c0e500c1c6000e005003401e43d0314268030038002d4105c508108061507c48a1110b524141070008104068070742d128002c040600d80c0e80241201c088150400c00d00c20150824450146040f1070309145114044010508041c00c243e582e0801d941032065008042c18210301a48008401144800c40030002c1c900f000341e030303940034425501d1210648020419140314804642c01c1d400c82d0a20a80c56070b410300020690705440303102202e6005081c4d01502d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 842953255 1250 842952005 842952023
    0x311060405060f130317070e03011a0f03030304110405061f11011118120313030b0613060323011104030303020301090c03060308040b0904150801090b22020415030807 73
    0x208900415038103e4000145103000c0c45450003641c0d006e0100b245580201c044c548441d000240c045100d8800010f0658014000b8007007540007110803141821000c1e0b140d0300c1111511480c40c094100003054900c901d41102c90468480c24403410b00c07006000c06821700d900642d10310b414a061744904a02c01b24000c1e0682e50304002a980c0d55035090131280303171300341c01c410408003044942d00c07802c5103092101e5092011103030401c842080c0c941d030b44c0c5180f140c540d0180e05008040310010900840d01100741c4640c3e82070b44d904c8203882151001808540706400014103020100c0e4802005182084910203907010040000490189901c0000c19075005a44100c000980002c018800d054190090700d00c050611300b01800b1250850743c4261442c001c1e80a05200503c0c04076024242d591540c0105181017078000012214580700c0000c1e40c0640340d000d4064912410a00200f00c14070440a8001500c0b00c264064140880742507007080090300c05031400388441158200007002060303038440209889032192a9603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 842954505 1250 842953255 842953261
    0xc0b070318050d030e070f0513091a010812030f130203070513090302100e0a02010f120207030e01022416052802070b0702010903030e061e030604200901030207031106040506 76
    0x702541c0b25117100c1425900000740810004803494568002e8030710445000d1401001c2c0c40a510080403034100c050940d104640391410410611280241664604000e2b9401e0009048200c0000e200c156401440450b41d070002a8182c01c254480b41c00355407009050b620000d50340c600041102485445200031241e850030a2810140c04110514010a240c4020304c0040048122140c60f0018184068180500181c00c0c3c0681442442510000503409000b15250349150500502149a458019002d44170f4608440b41407928040e400c035500a140325580c1440d42c5040081e40c0000300c0f01a50828843d0600800b8403258921000359024105088180b00003c80f00d60000e1411081d68030490b0708040401840000d80d80c0008034406407034150508888941480001c10000d100d00407148690564102f1000740202d56600158000c00c070131141030002107400341d10300d0b071415001d1100c56040402000081000d5010350044c0142c1e50081c00c0800f401a0b2a0800608008084030111590b801000030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 842955755 1250 842954505 842954507
    0x2a02030a1119200f13051306060807090f1a040b06040b03180618030a0507021804061b26040c0e16090909020609191703030f01090c0c0b070318050d 65
    0x741a901d06000c503440f6411404c0c40f004107100300c40c0f8000d078104d01c0341c950002401d464a030001090090754001420800d19075540e000300c0d2504024004c103080c0509000c08104030b003069020b6503520030062102c9800d02615101044014404100c4558000d4010301c400902456204003540c4519010640100040960f1041504104004008071980305e14120b07003144101000041c0d0f0002d0302d081c140243c0c0d81030b040c0000350041e000e8003240002c0c0c3c00204200b0042140c55044095060701000001203000c6a502d420390312241d240203040400b04802c41e0740801c85102d101800c1d0010b00800c003651909440f44001a085101103c02c0d0060820710000c4280c016070040c03034080103040301c2c1d40401903501c555000071201d12410343c43e107202e81d40b090101c1c81190100d100300c0d40145030790100f000628a04111598507508215040b040d140d80f0407000188400e028000c11104c19819a920a9940c41f9603a8202c40312002912603020103a0365902400500d0048241c50040c0c1d0003107000340010003400d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 842957005 1250 842955755 842955803
    0x80a0207020f131b08041a04051f0b0405040813060e010c020103050c09030f03070c090203040f02040207050f16051203040e181614041a0603070507150c032a02030a1119 74
    0x200820315441803002c110101e98007042004080310440c0c0304044201901d0100009020141448cc1d4028070f031078107000c1044160001040002000051044040ea8882c4281c0c0c002c0201545280803440a010440040d842075001c1980950100705c01030400041c03c0c080703840c116880030305441551000544c0424000350800080043c00c104a00394a07500d41962403400004002400034016070300410403000b004000d000303480403c1d55110032902110b0020121600c204c010303104e2240241d003131285002c4144400700480d025074100300c2013450035032030304080541040f0562155801600401030341c2d000000340390000800400380124445200341c0f245040004643ca240072006280140c00c0c1155100c1c3c0b911803c1c0c0390f00c102c003400d1250b00c07081e044c1000310325501c40c18401e0b411245445415800e054041d4401004008243e0040c2009a400131012a200085400500c003507482408800c01a43c8105451031400042c0c0040c1c42c0c3c4146031012007600c091514904961020965882c2100441591 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 842958255 1250 842957005 842957033
    0x1207080d20060903160f0209100f09110a0509270106110606030a02040c03090803040506100602190f14010219081005010512131e03080a0207020f131b0804 68
    0x70018040b541070080c0a180d0728840c9030400011050300c000020709001d00700010001044c0c01070401101494074041d00b02031614503001e0340c11860740c02040401c81c0c00b4076200b2040300d8111002c1c45498030348140d400791155045071003256482090004111031010b4103282c44030725102080030300d4250794100f6602402c44515056440383c03580c868800c22030107039070005054440c290103a800040489082ca01100030f010941009440c1010000070f000c20480300040b01e5100b6200d282d2140c080c1c50f19207030300300d8a505840340d04001201d0003006a6010030b044000552405205a68440002d4821400785081e40c1140c03150b890011a100180c00c106600840f286602c00040007200d45414100800a00300707001342c0710340340390211340352000884148400d40d8010b107090300041e45540130490313240010f5084404480440014511801207452006103000303560500d41d000344002c00090b40402480321400102c40e0b68212251980d0100780b003a122085403070803000c019503a07443d01d0725041c107200208504803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 842959505 1250 842958255 842958317
    0x90f030712062906120c1306020f0d080c1b03090405040f02100906020a0602090a03050a0c0f06051206130908041715010f0b071103070e0a0f0902030c1207080d 70
    0x10f0300380241103a940740f0031519101d550146480e41034454020b84d098a00440c24401441513030024040b440f82e40002d40e81d01d058003174804507002c04001d0941180c0450081d02c41c0310824000340f203d960300e605518051340c1c0241300345003100d05004032800024107480003130f68140c8040714001c1c5040c0943c14801c1c0c0d060300012007414480c0c5c0710391078014000d42d507032841c01c0c2c083e007032943c0400c404e0101d6440a0324100115003220890b00c0012140c1032640d490038a40c8034018108540f02400965a070281c2c00b43c641400c1514180900c81da102402d0148a040c491401c200381030f42c401d5124006410380c030103003001e4800710745001d03034104076a010740d403a055014500540440340540100981e8100341c2e000d4094502804495484504524007040310740860010b90381d060103030b1701c008107890034007581280c41000d08040501071207c2002e420401c851103a60041e4141e00640002c0c401414102640100c0360318580450720880c1e41c1da4111401d01c2c40d0341040d407000a01d4440c0840c200c15801e00440c10040740 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 842960755 1250 842959505 842959571
    0x60518130e060f0403021c020a051507081302010c060c0509130218030a0506070e01020a1a150f090c0f0d0f020d0b0315010e040f061a120c0303090f03071206 69
    0x20a84010351f8580b00d48840e5160b038030302c0b8068981064400c0c80204015a40710040310603a01c000c039074040e0001000c03221040058064800188407101c3ca03291180407039010b03140c0200580d09615050040d02000301c1010178800c1c00c01070311207076841c0c00c5025090311604002c01a210002d03000a00c08001c000035550b40b180d8881510b400100c1d0740405d00303d400803001d040c610100801c490050b4100049080040c0103100700c0d40d0500e8280703200007070f840d10075140048502c0d84a031f0342c0d03002c01102200528100b03402c50554000a5180c03040d080c010051155080710103810101c2050880c03003983d80c074103640f00c5203540104145189101c81d000301481841c00310054140d0704400d00d008000e50005104000080c01e00c4d101107010b11100c0c090f580380e051340010b020b1182071240c041501480220700d00035805080c0744000b4218a41e801b0401c0e0b42c10620007006103281030b1401c420045c10b41081403001d0750601403588000380901880000b5510a481120701160580c02100208400c00b00f00314a8601114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 842962005 1250 842960755 842960761
    0xc08030720220f140709030209010b2107050f0f0405100804050d05071a010e0f060402040605040611030d0e1513110d140106120b160207060518130e060f 67
    0xc1c1d00c4240300c140401c0c6000041e10003c00000507002d000c1e0711002c0d0740341842d0350701841602075225406c0740950313000b42c52910169a07030304180e1200d442902d03500d801031951490494052186803d00e55040034040c5070040c140810441210025440b460040460010014041010b4100090310700f01010b814244102d240c681900c40c41c2e01c0300181c45001c0c0420400190010800103080100303c68405038000d0f0303961301d40e1580c0c12030b100c0314401d03030302c0f10103c8030b072040000c45928090080f05d040c0d40403a41c0742428a407801c04151841000412030071444c2c0828058101070011364031400304502065401010300e2701c40c000030000743e0007000e0000000c100c140d42050380420a0030407a50f40d08501901c0040c2d4011003810200c8202803030040c20480d550a0000016a10034049017501140c1c5c09400600d165440b440482c100c0040e13402c0309440541c01124041143c107015001a00c4099802e0843e8051040c20318000303030040502d0400340d00801c0d691445603104032400c01846a10082603001011242 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 842963255 1250 842962005 842962039
    0x503040608090a060207240c022805060a05010f09140f06010513030507081009020901030b06060f132301170603070f121b0308030c070c08030720 64
    0x88540d0040e042401250408241403000811400440f00e030007000c119240c80461400c0025100320f0700440380e44070078040d201d0704901501e00c1031851004168008105040b4480c000d48014000d012015100c0d590816880c000b08000307000700e0307201d881803503400034007507051020040509040b500880b06903450050424a09010840341c40c0e049502d0403214a030a0f62182c00480381c0d4417440580804c103240f10030000040100019180e01034400300d000f40c50b2054040c03081d107401c40d4881074000c0d40c41708044004001140c514a41c241d000307400a400c1e00e140c841c50312a0200d040c1c0c80703507200000452551301c0400010244042408403040c0410204800e040c811000030404045c0f10b003800a07100480000c561280e0341005220020500758403060070041e82c81e08003030b05002c00c022040d160070ad180c00c420081d0040d10f692031801d072540440220f00b19181c0f008000d1050f0880c01040310010f02d505808500c1000800c05030040e507100e4641c2180081c5540078040c40800d407004224090107880c006401c2503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 842964505 1250 842963255 842963257
    0x61401120605100506070f1205070c0509040219060914010c05100f1506091d2502010b0a080f12090d110312040f03051203040b0c03060d0b012306070503 67
    0x850740185010499455400c250090300005601240c2c2c082000102c050800420b038140010b403e01172400a002c0e203120802c151107e201d0103000411142100d0410303c440d2511484a07034105002420700604090082c001d644508c5550f04194040340400300100300e000c00e00303188e102801c1c0302031a12494189281e9107452351068140b45180e1030741c0e110354207810304404940c048540b00548414101c0c0241c0d890f800a01000d8150099802d980180c40c404d1000e907554500304d03406800110030641e058a00708001c51000268400017400319520f9601c030302d80d10759803e0b040a0213450800054400b0440d4418402e1074422285040500304006000f5203400d559031b0410b660400d40c0140e0044403886107840040d00f040c590503241c800d01800031801003141c0d00c0f840c0c5801c080e03034810401c48000c0d00904101c5800c9020440d0020042c604080006071003149000103582c1108025040303500c032030040daa442c825424240c000000101d03400180d5107000e418088026502e05040d40c4080c03811881f500d8041e02e07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 842965755 1250 842964505 842964539
    0x706050114131d030d020a0306090b06040509040311070b0301051c200102150a0504030f0206010b03010302040905030c010e06070e01110a0b0c0c01020a1707050310030b0c09030303090a061401 84
    0x400395900c115045801c08601c0c0c0343e044451000607203a58540d2101c1d604000d41003140b85c030b40007034940304001c21404002d104509066400608050500740b40c5820007804c01c000510031800c11141c03400448a820040000c3c1019100d551211034996042c04144103192132121040c92001d80904594400701d170b0f0f10388000d03a400003240c0450088201c42c0c00186c0c508800b881c04600c0e45615942000100c2030150f2040d4044c1d03201b5500c05c40301c0c540142c012a0341c3c54081c06001414035041004000515007030740301c06070207440303102542c0c1890041038a140c00c45508084d168800d8106078104100c860b4401d00390000c40c01e090801c0030205010740507081c1e40743c0003140000c2032004003901150a60840001382c0d110314400c00700035951603540641c02010302c00c09000b26070398035001034042210f4600036001c2d2440381004522201c1d80c0c03491070303c0c0c02e098281d01604240a40c103080000411a840503c000c3d4820f11122006080000280c50312000300ca201761089ca111860603001404401c40e101e4046030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 842967005 1250 842965755 842965789
    0x81302010f17041101080c030f19061e06180620190305040f060f0c02010e0103060f03031106070c032007050d030f091e030807110904080706050114 65
    0x40118500c041070700c10422085080c07100b60600400c0004008901034030701010b000a0340c03000c400d5190610807100c0c80c001a5010b8091b040c02e003000035241111107680b00b0015070858808500e032130391101542d061310381e03c110256815201020601c14650464004001301e550b9140010125251080060400c1e4003046c281201c46009560103500f40f404001700c408000390b140103050036960034a000b61450340240b10300320380e41c600320000003042400f909501450506588490f00f00144580c01165001c84000505041c5652600c0c08200d6202107003054002d5840f0782c0310003d1098104403100e1400c10020117120405c8060300394140002d6108a070161518141e002203c50740e0020110b260030403200d038000e42e4002c043c0d80705501c1819404645408030701140d0322a00c03406902c84095054498a0740c420402120018204100103640d010040c00b945001c1c403904140d0180d0040041c0030207000f52010341d000b841c00708030241801000d126440c010300420203004580d240040105450342d0945446034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 842968255 1250 842967005 842967017
    0x601082211060910020f0c0307050d030804030311030a0905011118010c170703050d0b0a080706050d06050301060603090b090a032c030109060c1404050d080a111c0f08130201 76
    0x200d074407450b040d81c83c40d00c0000d02c1303c41150242c000080d599081c9000b0b00510f4460346503010303410700b000b14a034826100084e12103071001003503440035a920b40d0301038422020159140c2c50280b200035020040c600541d00124003081c8540142042420358400c0c444203425a04104107130400d4260304024020f400300300b800d10755440115030404850a11940201101102000800400302340e0301034002c00c4503c02480d8100403001200061061b071000b58094202d060f44482001c3c00031a000e040a460300c049082c001098142c3c9907808203003500c4050b440400800e40300c0c0c0d90801007010340c016055221183c500200b54807140c64500074144440c052102015482400e8006d80c3e13400b0b1040500f041c039a001d0300031300c50302040d440c002d0000c086046000c8006100075000009291009040307130304840008088902c20142526616541c0c0d018010503028001c041d21000d0000c48280300c0c1c0d044084040004d03e01d024410880a4208030340740b42801c00304114001046a8465032013503c0c07240980a103801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 842969505 1250 842968255 842968283
    0xa06031407180b0313140c0a0e0c04051203030711060c1614010216051006050d060b2815141b120d0519051312090509040501020306010822 61
    0x9869212a0700400d0f006a00041003040c0140d91008180019200e084045484c032400d400843c1c550380034010165006410b24010005140b920255540083c041d0711414a450781e00c90014030041d1060b40d1003901c076007002c07040002e8246c0021a54018100d4880900140d02d0400721000d058403408503250821760410031914213101c0080200401c002e1b8400003103517101501c1400a0307a0712031300c8400700e545100310399120301d032040c20b4003c0c031003100c0001c0c01c080114852a17035110b010700000c9030b4494105c4010100b40c102d41800c60004000c11000e100f142c060203003040f85952003e01e40180c03440600c071466500811100c40d00307048842030034585000e003d51007041035109040c04000024800491070100b010342040070181d01c124000c0e0590740304261142e40500e034801c01e840044411050f1002e0070304003240482c0040700400c94035912032420301032482d107950008103003940a0300e041d5866903001c010400c55503008014280c100c40000b1f541c0d0032520304180c1c0803082c030503818002000d0400c600300fa = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 842970755 1250 842969505 842969537
    0x61802010906112416180b0702030a1205030a050f15060c0c06030a020a081302060f0a0c0501020a0302090306060312031803090a0b1c09110f0f030706020c0a06031407 73
    0x2506007070043c48141402d00140002c4c80003c0a5040e03404182400048903041e1281d401a0350744c40c08220701d0555098400c2c80d04809620503080184140c0c0c160095500c0d13480068007182c26160040861380f1481e0316400c0c10030040c8129080107000030114903201d4203118801040801c070104030b0070304941255072003e00d040c2060514120704807281d0020000b00030b205600002e5005443d6102da9561031101c281d50354100c00700c414120f003602942110007000000c840401c18801040303644a02c6c00d0074200d20115550719400ca9002407200c40000e907000c07038a1105450107108850f007000088000b41210911000c0c0040c640c40702074603280d182c2c0481018281104002d00c191740001c0001480b0030141d6a80300d1901301c182c2e00071580c081d01c06011810342000c5841c68442c042880b6080104d104c1030010351014411045c0f004aa910391003440d00310201840d65082142c0c8001c0c04403580030f02444050718003030050340c002942105042c10300340031007144a144030300c0440d81d009101d85800c0e420049140e00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 842972005 1250 842970755 842970763
    0x507020102070f030f12050f01060e0a270e0c10031503021801090524190915081207110420070602090a05010e030604150e0a060906180201090611 64
    0x101c000d043d81142c00703204040c1908614201003401e81078569143c201c3c84960403000701c400403100303011010310030030041c00302c5441079071700348030703c00300600304a1000f529246021008007039005104208400c0c0c59082c0c0c0344000700e005500541d440c03000181550b0741c03800001681d040d08007404208255550b070344002c100802d810060011a0098202110700800407641c0f054144240500c40d000313420003001c40c070085081485001e0340701341001e4001074001d400080080040e18000d54130002c41801e00086105a240c2c490700300340e5400100000e1406240483e520700340030010400c40e2080405006200c08240035500340c1c8030140084a00040c0404506d0000100700f000900c042d0350b04c1c4c0f01103514010000140d0003041912006c03110901856030b80c8004450341036843d951540c254010001007000994980d0446244600381200403605080c0e503507071705240c000c14407000d40d032598541c04048288101c1d84903d0008101c01c0c11441e10745e0031940c0000e807107030b030807803043c101002645286080390500500c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 842973255 1250 842972005 842972017
    0x50a050a0c060b0409050c1e1507032307140303012d03060507020708070519060f12021c110412020d0303150909120207360f050f0a1802040507020102 66
    0x10810420514030f070070050f40d6404221500341c001d6007802e0b00d0700c4032044404a05d2500e210000c1581144859550b41245a4ac0050104a041c40445196064a94a4070072070303913a003201c020100c0351503003414100611100102d143c500078a410400c01408005d10080c80303d0249403041240b0700a510410401c07620210407035001401da285804140500e107a40880e1402c00c0361004800c07600203507102d400300440c030014104111181d24484100f009100c3c005c02d82e0307841c848041d0405e07800100c96940d004090ba4040081450341700c03000065034444000e28800c41b150000b0350712081c2d0500d400c0484c0090420351025020f4440c0e6902012407082600c41d030010a46450074007030940d900c5582c2e03032b0184090b14003580210f82c00c001c54224501f50f030748009000c03000c0f1400070340d00040308101d040807100717504000f8220102c1510504840a104041d50180402100301e80c07000203058a81311484104141001d480c51400c4c5081c41ca42c0443d15207190307041c103062901150002040c6c0c0311107400380e009100d54 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 842974505 1250 842973255 842973259
    0xa180602120714030d15090c0c060b040e0a12120204150c020a12060504020414092a0a031506061b08030606070b0a050601080709031a0a02070c080f010c050a050a0c060b 74
    0x100b4448000d1690030250801e00c1d000c070b006e582140c0f100c0083c800d40710112034900009001138020004900e17507400480e00014041c10004202d0b0070707401c0c0103082c01440c0398103035804695403001501c01540b100f0090141600103138110b040504118010300c0c04100071a1210410615062060075555104541401050f080d60760496420280c03402c0c40107410120b82c02c0e0f10491505c2c0c1c032102c2c6000601c076007620403504240a40400c421006200414603860110a0540403003880107001e5a12588014805507020321214460f03003140148c1c032000e40311140c00c00c004000e0284401081c0c031020400c00a0a0340c1c2c4211f1054890f40c401d404107202e801500006400c01041405000404115a00440c0180030070303a02e20801c0d96a801c4142d91041c500c1c0b0004091a4800700720300d86a9a00c4981141c2007007850380091301d401e205417114240440184c00011454001030740c81a514082482a1500d110b01410001d042044806003d030a90094118100c140245071340c1d04410081c080e17014901110300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 842975755 1250 842974505 842974507
    0x7120602040e090709050f041a10090c020a110a080d050a140429031e0402150c16090c0917010e030a0306050a05041a12031204080a18060212071403 65
    0x220031041a41c4640e5442182817652038100410342d505e00800c0054032954110700c0c01c00740c40800e80c0005c0411030b030060680503042c8546d00081030000b1075014400e94280c0550040240340c4e01420145503541d031701d901ca148520100141044150008104410081a1801d040d40c482071506415611406010860001c0110020f00800c1e04648440b039240c0100154154424541c0d00c6100c003000c2d07100a9520580b104d07140c03075103501c070034080b03a8480e07030700c1032000e0242d02c1c64802050200380943c01840c4040c0c0c064002640402000f0344da08407500c01424448018400155084000b6001d6081c41c01040402e840c0523000407003605013500500d0000c850402240d0b96615031110081c01020103005485c818500041700080600d41400795500c03006403c40701d00c235034604403020007030007820b6040c28006a010074032a0091440044114030700c038074001d440721941c901011600502e01001d01b03a0b1080004c2c80f42c82d00340070840d4009445000858a444410743da208103041080707040c0d002d40f002d2101448 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 842977005 1250 842975755 842975761
    0x11713110f010806091b030a0204030b0a05010b04050409050a02040509010c0f0201050c161b1514040305030f160b0708070e030133080f0f0f0a0f20040e01050709120507120602040e 79
    0xf1149c0c2c001c2040b00e00403592070780c042d2210791660040da1781c2031058280c2e98038240000d01241c6001c1d0b001034050344c8a80c080703481c4002d85901180540d10200c031100096503680c8111102c0540000c3c0280a0b0358461000700100d180c03406c98040513000e102c11103403841d2041030300d520820403500400c40700700164480d0030041d2551000e50103e4243e40305906ca00281c111882c200280e1342c2c500903035090f80d603c00042c45c14096003010424172600080806064007540e80c0d805d0300030450080320207001d000303ea40c3d441f4403442c10510140240c0041c1344c03401d0090385844803800362142141c40c100c0a80c511a191000f06252211907500d41041980110a2600442040f141030403c00202402041d5605003070301c14603460212001c0d02c5180c011800f611010710700306d891b00016800c0c145070030000c00f0070080130507d000150229003103415040c1818010707990fa900340b01d03842d6044100400213110050035007442c0b1260f80d540c3c03912002c4078443e00f02034a214080e00410002d00703805450241095460032a00c070f04d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 842978255 1250 842977005 842977021
    0x4032312040606051c02090103080a02030913090203150105100e0316080105060307060c08040e130614071416030e0f15071403090a14011713110f010806091b03 70
    0x300d0702d40f03e16442400445003c85000150003441d400e00e0760000c10f2016941c2c61a107950145c1d81c003074be002c5811800100009119590344600001144c41101c8000810b03040c68070501d490482c0004070241c11890b8200100615566543e08140309001450048c250203411400f281c9491008504811250745119000c07501100541c08907118030001c40c1100c004a03540d000558070315080440c05002d20f00104020320140405d140030380d4010b0060745020604914176144d540440c3d0080c401c20101da0030758420300c0b0420b94072100d292028040c00080303a10f404080c8d000c0510401c07c8810003014803180e90205206a03481d003285d030316150005011500d01c01001042220268804031088404001c0b400c21040d6840000054a81c10440034083c410ac190800174103405c030b2005190b050b8100803d140303140703009101e070840c5030380140a0b040075140d09800b1864514040d040341d0007202d004004039410014240c3e840f200040d04070505441a4019440c0c000c401c0041c024848102100c100c0000f003400307840 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 842979505 1250 842978255 842978261
    0x7090330050a031409280b0718080610060315210804080102030c1b010e0a0f0609060e01060501030f050c071b0e0f04061d100e0705031c090e040323120406 68
    0x1008041c80304540c01354040c00039210300354090304140c60540003d081c140a02030b103c00c03002703d891080b01c4040d40c41c1039032440c0c608104c8034045580e000301030810619406020790004440c0c0940d42040050030811404008115402c5c000c1101c0b02c03007440b0005001102e000c441c081d04003200251358a1230594210401540400c0360611000d9095040314030062042c0f140c49085516a406010603052640780e600a080302c000094602950303d078a040001007440c410080c501d41c102c8008207440b49440e002500701d5900480b6403604600f8801000103518800c82110fa410742d1103040181240d03883c4402d0400e0f01000c0d04070b010b200f00081700740b2440800701c0050602c1280308103424410100c8010385848040c0c41d03061101910b900c0244103118103d1160402441184000c0858010744c0d520170002e4500b410000502d00c03022100c9082e400003a921000050240c14116800045418150b80040c9040304540404180044076010012140ca00d0012140032a204034250002c03030038075041903001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 842980755 1250 842979505 842979523
    0xd0207050f010b100903050303011a09191404020f041e030512030142120c050c15010501050f180a0b0d0b04050702150907080607090330050a031409 65
    0x80742084d405031000052142160a050b00ea0200103503085918158480d0024012020405110f407400d1142002030307100d003031040e210780701542d5003042880d16004840c2142000016003034000c9004103e4461001000760441d0304440c4c140070b503207440d000e2840b0015070785507298200803d81d020350f0740100ca20031400005181600c3c1d03408102d802885540e0308403600380040e100001d170f80b00c10400200c0b800c070b00440c4141440303000909046940500800300802103452042c40900400e0010480390200c02c000c00030751014084500b84000c071075043c036001030701d68095005d04c0d90682100107912841d50138174450300c20003070038041c01002c0c0107500d4a15280040d00550784651030700d80790804128080c80d05026080c013880d0103030040c064030400f01e04035601d0080c004111044902c6000130004503c1c8007005a51b101c0c401c1030b6035a081c2d40d801c61614005c5041400d5140742c803504c0025511502000e21030100c0b4085189040031036039075082020960103094070552016449084104100780f054004c0340c0329038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 842982005 1250 842980755 842980759
    0xd14030c03071b0906060906050901030b19060e0f0d021c0b0a050405150106081f03080d0e060912161e11010f0305040804030f051e0106170d0c0303020d0207050f010b 73
    0x3c0e003521442c1200c1211818420500010042c1c0c10070000307540501b004001808041c500440c6085c18034000c1440340f070480b08190031060080030104040c0d41c1c410035001207814100c0f00344540c1048400003c13421042c40c031019100d606c00751400301041540f4090700210a0340030038840c12509d0914409002407200300d4094580d800b40d07048011540c810000303080c0c1a40d1094540a0302030325284060f001c0d0481b1b10b641c48030300d102c006c0c0022001c540210040c00b07100d04102804100c6480b5148900d0612102902c10075240d170249400b2540c104c1400f0607035402d4170f00e522000c0103c00e054280070780020002902085545860400c00040c0200001810803160081e03c070a0780c940c500c0c0400701e00301c8100b1280906420b00c01c0c00113000198840c1c1a520718a400345044803820b00c8582083c41404255451a43c0140c0d9220010010407450031030700581e251000c8090803604400340405040340c1e4400340000d00301075000815480e01703501036054038616034216044944040c8103a10b01e500070b061b031540c828 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 842983255 1250 842982005 842982053
    0xf0a0c0e0108031e0a05041208031e070906030902041410063f060308030f042006070605092e06080120070302010207022206050105090d14030c0307 65
    0x8909010004221081e2850a20801245404d80495100540c01c50703a200d404105041000080360040c41040424090180810315030301d00700780b0200c00c1c440502d80d41c41e21040701e00c03804000255400061110484a2509010869104520010b00100060b410303082403040f245081c001e850520500704000e682c026140d205500702d61000560102c1c82c03038540f400100c08110b0302d448160080c03d911140500e034108001c5607858a8ad5520700550701304852040b1708105010400050008002c96001410342101840c00d450130617201007549803007203890240c60540c0715404541d11a104100c000f1000e1107030180d035142401c6640c0d850280a511800e0000e5290900c107010440842c10320400c13149a81199242140a543d29165803158121b20010390070365600f4410701d00540c49030307580c00340c0c001581c0310216550f44040b5540b1046440035003015042010a002500e210346900007010206500000850300101d181840c1c0e501d184101000710480e4080031881f8070410800b1100030318101080c241d04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 842984505 1250 842983255 842983259
    0xe060d02120f100f0332030a020c04051e040507080102030901020705011d03121012080a084002030d03020903071a040b0319090309050f0a031a07020f0a0c0e01 70
    0x40e8a91000d80c024401c0c100c200c40020030008048404c080c038000200341506d03801040c000c2c21700703c51030170364440081a504001145001941d050283c03040008040350300300907900782902d405d081e44115880d100c080861170000b28041c405c04101c1c0c18000d040100081d1740c0da280c05503102d4040e401102c4103e41c1907080c504103c050a940e40c0703448144000540045050a205803900c160b0740a0141130201c440840c04008100c04000c40c10f02644c0c01d014581040c0e89201c203100c000c03d00b0000812412201c49500707072020015650018198070b0350040c10081d00d0200e5841c1a40e1220080d601c4029810700c11007242c000981c0d015000b6005403001101510801980d480d00311b88504840d115519240ea801c0106001d680942d0010b15080110700500b038000140c512000400c0320300c40c070000e40114010140802851500c0c5c81038049a1100340d40700750042d451699415010700c02e5030544010110148002030f002e52081280154010101040f15043c062500308000300c2002d60242000681c000400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 842985611 1106 842984505 842984521
    0x20f0d060603080912030a090512240f10030512030a1803030f06120213090203010b1f17070804141c0e120c0a060e060d02120f 56
    0x70540e101821020054004c05e10055840035034410418051155403244a240c111001502c0b4001c184524240c1c079401c3c41607040d20301c1e01c54000700001e03144030441d0301c40302c40c024240780c02c06154a0b103c010450300c1c020098040a4000c1d400491071003814038102005590141c18408000303901030450244820ba2100da00c1d043e03000948174005009810850b02c1003100034800f010b800c640340743d5541c3c08035007040642c1801309440380d030383c02000c0c1c1592020b4106081e182d200920310a1120f03200d40c580f0707481c0c42416100c20009811103292030b00c03900e08000e10b24041d4956440d0480b16660359660380000c2c8420644400450064400c107010701c03080102d20345a4000580c0307600c040d20340054240b1400c8425603e03400c0159100c5803c003601911400c008905036513103450300c0c00841f0201030100704036108941d0045071461002030012640400c00e03480c0c600429041701c0b41c0f03440e0380310403c3e = true := by decide +kernel

theorem cover : BRFrame.Cov 842805755 842985611 := by
  have h0 := BRFrame.cov_init 842805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 842805755 ≤ n) (h2 : n < 842985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
