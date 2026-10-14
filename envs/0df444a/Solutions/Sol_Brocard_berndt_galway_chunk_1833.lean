-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1833
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:50:15.495844+00:00
-- url     : https://prove2.me/submissions/e8a01e35-7699-468d-a665-eb6487124ed2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 329496402 ≤ n < 329676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 329497652 1250 329496402 329496407
    0x180b06060f1b0f06010501090e0112020303090a03030807140412060e100c05070b0109020a020d030c051c0e1506130b03071a0301140d15050a091b06090801090201090312 74
    0x520b403a02c01c0322104004106058001c0450001400900c502c15140142d980d0303001110801460300414069280c550010029003142c3d00c280c0c00300710700c050180c90400842c98005444044183e10650100321032004001000d82d00c01e65a6641c0d08601803541d0415090800d0784603203840f0144000c0c0f28a81d01e0f40e86c036800b0807040200144883d0021414040d542c1900742c0240b282d0443c1031300711481c00c40e10b000401c01d46130074001d40e00b502c189035004002e40324010350210090150301003071109100302000940d03050a00c1155007030715510710b8007002c100f030011300c0d540174a04050070344490a080e09120502c24150758998510942607000350000c1000400e00300001d00300000c55001c44601c4494180504a0001ca44003031030403100d085440048812640040c0a804502c00c0710040410700580540b82441d00f4641c0115001280c010000500c00ea09a0340c0d0820746072440700ca81500d90301c000c409c100b429427003100300c3c01900c0400c00901040305168000b802e51201e600008001510303880c002c001d01803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 329498902 1250 329497652 329497657
    0x2120d05100b0a02031209060112170c01020f041403120d0f0204150201090b091c2d03060f0b040b16021201050a09030f02060601020706050306011101090503030a180b06060f 76
    0x20001c2c4940d0307940c0d2031000f00a0350740e5100384840e50300440b005000800344c0d4004180c2c0c0341221000c541076580400036070354084c0e400680648400c00305c2403c0c07144100c5100709102421200d0100c40c191a581c070309090000c540c1f10340d0f480a852080c0d1010152024a107010b005848000d00310400c007040ca030b07071307110726100180c0100e4010000c045540301048118550540244801d58003c00403020251104031440d61914600c0c01810862510b00c68150510780c4a0049025204c220850030001e40000f103541c00c0b01c01d211100810006900e3382d505005440401c194000100004108c0e035141a291408862480c00382c40d440c502d41c03000da0008402551130b9107191a44003000b180081285180c144081ea0003410304683c268000b448907060014942d0000075050b000c0d15050300241400c0d40341003011903580d0700c000c01c0c00d810014011444d4400701000d010304009244120003860712403402c6081d81048580d0a440030307100026140020000c030340800380d10754200c041940d480d03641b145803032030004051 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 329500152 1250 329498902 329498909
    0x30501050a0c0314040c06080a060314060906100806040816051009110402041d090c0d0b040b0a0612030f0c08030c0712020105090d030e070806011806050102120d0510 73
    0x25400d00041080801499011140302c06864070200004501040c0c4015012000c403401012200c0446003405828001c02005a100d0321040c00840c03895201c1e90740c00000007034030008030102c0d03101d0001d0225500003400510341c80740307005a0703051460b8540740140b66a0000980042c0c0039107400603140c03031804441009015030300d800c08111004bc4e00c800080c0001051500c070305440d019410300102e07100745481c1c000c840480f0000401d4a200240d90003070709900c0d0388003030401a1503104003203030740850783c40f009001e9416178000c107480d00140c50207040c0360004d410001c0c5078203403172807074080c040c00038000c6080035028050301b6160080c232128401c142520440042d00000d071920705e01004204c1c0c0400747d04001c1c1a40c40c440c500a24000f0030100043c4d00f82c880540d100411a0040505c24000c1e170302c06d61102110401900450b06840d179101402c504040302a04202091400350100221141c168050b03000108402e1004011000c4d03c0f501c0740e10180501d0ba80d0003909604c030008140b2040c01070102001070b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 329501402 1250 329500152 329500163
    0x21c0905031e0a020a171b0d020f060f01090b0d020a12020a0e01030506070c0312110703020c0a030305030c070809120d11120a03021c1d190206190203211b0703090e06060403 76
    0x214840075051032341d206413080550006210362024181803200c04070b0228002c04a00c00c0507000c0341d00300400e02010f850001000c5421080340c00540025946240e2024024090070400c42c05514460050003002d18694200c0f1a0031006c5600410000e0000180c3c16401f03801403400180715150340c5400c0b50389815000c03241d16424104031501000307000c0c1000030704c005880380d021105405148024410b801886200203004140c003800002c0c40d5240032780041c091544901c0c5140d107810300c004001011811030950300b07100d5a000c20034240049820a80c99048070000da801090311800c402c40c521018807802c2c07428400c142c0c01282d000a81e0f0850b4200c10741d02c40d040b03d8288001c00441c409904c0c1d40c04007541c0d510541c40745400e8550700d161a031000c52a06500500014a85480c0d82c400c00c544c00e20501c0d02e581148000c200d69681c3c5032402c1201e0a00c00206540600705003030031406958101070800e038598080305c0030010400043c0d0890070101c210740703051180c409503a444800180c41780c002c640c8050007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 329502652 1250 329501402 329501437
    0x30e0d120503190b0109180207020919050915060d03090b03070c060b010504050102151519090b040c020a030e010e03030714011107030210021c0905031e0a020a17 71
    0x406500035002d14402c2e0080040c81d0a40f8040039864015110102c00307650204a1170f480520618041d6142004080014980546800d0342640841c0c00d0031000ca0300d280180d0003030711050f0380c18401402490741100324079004100c0070b090400071100500c00a0b000740d20a5020595080030140034290f00c00080440411040c1c40703140910002e000041000d800b241e2051419200140a42c0100c0c195801d4030300690081c038103081c0d000c802c481252005041c04544442c103a9210704a69644408081c0042d10b008640070424500180c07801920081d510f0741d803156003401c140c4010301c1d07400141c51200d00d8252800e00342e14111200142c8007800606612070301404009008402e00041c4d890b102c011aa0307010007040410f0f244880203045004e54040240160401c166000f2801401d4024000081e0002015500034407110f042c032080700d003079240840b1b19810204141d02c40c0183d4549240c024401101d0251601c01c140400035200c6a0012006040b4a60300f5000c00c243d5900310309882844e20800402c49 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 329503902 1250 329502652 329502683
    0xd06050a0e0f0f100909050304080f070602010c02150f04030c02060a050a1d030604080a030213091b090302060427020c06041e110904060f06030b0601090e13030e0d 72
    0x3241078400316a141003601091000c07650030010400010322078801601d81100d100c1c20b21246101600e861501030364a4030080c440403404845c00d200c0907109201d040d008010007403130300308080d00707451006000c07005541000313030180d00c000203080101d40c0c80140541309818555461a05590b034415060020707421500110b0998007050f0070400a0100c00059200ca10064410002e221400090218456090342150b00407400158605014140e0340c40307942800760a10210728039000c0ca07090b5660240c07036510740b80c0c2e500c21000a0000c003114032290440c13a004800d54199008541c1c279104034414181900900545a000907080b02c045a0b03041d01200343c255941d24044140680e2114292030986500104540d0829056400404c000000c1e0384020ba40401c014050200300c12510000d10603104d4a403180100341201140e0321902c400345100b51408030035810b112000601c0384140d504207a600ca00d102092001da20001c5600049907541450301301400700c00c000101e032000e5000b05000f0a451207905d0000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 329505152 1250 329503902 329503919
    0x2100609060801062106020c120c010501060e0306072c0612061503090d030908090409150c020c030c09041109090601090b0d3210090519020a0b0d06050a 67
    0x1252200c200034041c16480340380e01441c0030309444104080c0c42c13017407401400040e1180c0140603128940380039034541d081c884c0010303400c0e41d10001c400b44d402d075580e6006000143e00301c400040510002c7e4020000340c030301188060060f03100d8050303d8802c012078020840518180f20500f001c1000d0180510b81c0707a081c80c0300440c018a2040d5545813240301c1c80100d04d005203040c4c105a0b445151090018000e490131301100354000c1090341e04c282c8070f00c882040f134400f43e5200c50241030703600b52203120048010040002d0340002c46009020100031074010035004000d41e60001110401c0f8034046800c07404685031441c0040164200700409078001c0c1601c0108411400701041240c1241c03107251041c00400381301001c00045000042c002088021803004042450611807031060314103042d12445481d0840750300105181c04601019440981d4441d201d1904001c814045c11050342c00340d04040e14501c000e9030000300724080c00d0045040c640d001040038041507071181c02240082402510200c4030300e0300ea0110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 329506402 1250 329505152 329505161
    0x609070801060c060e01180f14160b0903010b04051f0602030c0304060e04020d110403030e04180602031306051003050c0a08121323120a020603130c1a0306090a06230102100609 77
    0xa44014820050525189d50040303000008100018071004516080c02104400c60304a0031102e501591b845504030b00729100c5203c0d042c001c102c41c81504545240e180e0b401d45031031107950000030444d0001d0142380428040041a1800c0d1500350802410000aa50215000f4000c01f1054407685007001800c9030043d00050040090b64040e03600c10020b240d5950a10040d91500d03000d01341545117018035100800e000c2c0d8041c5800c004000f104205c03505043d164101034541c25298030340d078090403c004004000d010040515118400e17514100d010307203000c804903150a91001e18920402c0c00081d40740200c000504050050030300004140001e040001c401c074900506101c503d405060300d007908460501000454810042e401403195156075a4148401c003502c080b90070850b486c19244102141e041c0d0a110b52141004079942c4940d1685018020044151406015640203a1a010080c0003c02c4407088280c405d0b5500514050340c80e8480300100d01d0711600104000303030301e450640d0120ba00e1030507411 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 329507652 1250 329506402 329506433
    0xb1003030e013e0609161809020a09050a06060c0c030201230c0309040c0e0a1e0f080f01051e040206091f0804032015040503040f0602060609070801060c060e0118 71
    0x1c44d41d0565802403a103a0743c1c3c03540c46602c040511719900c1000a24003c0c4c1d0320746002c003407160b0080342c7c0c814190702040d442d100d80d0b0041d01445455104104c1d010803180301d18001030059181c07000250000351501d5203060307040d001c041c0c1044a1103402c00c1c050045144141503c681407a0100c0c0d44c0c0443c185065142d42104010b18030440c1800180c50b51a4401d0b858190040030050440d00b5181c034100c0000721200e0450a1180301c0820b5400000d58105440040001000c598020f404254400c0c64483c1c2110401010070000b100c0d02c0c1c904d82e11030209030784950780c0070760305451255540c4994000141c6108803054548d24a460000c1c45800003944007085a001d01e1190320303011701110300c072622800381d1340c1000f84817800c9901c00780f03c1501044030780300c6141d001409402540d00d8151501e5221040c0c0d261608001c000d40d010900f030203054140807900c10340c409c0041c68a0300e000c0d4104007005102100c4c0e000090461a12809101504d03d03080d402030b00042507a24940c40d11101034903216400a11442 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 329508902 1250 329507652 329507777
    0x602010612020105190207050d0303090b0f041502030a020f04090c110106060e0120030705060103030806031606030b010e1011061005061605011112040b1003030e01 72
    0x80000501d1268501c09455450707058441d1340c2007240c0b0f070200c11500f00c10005810114441e2160001e00c0341c1f0f61103d10000d040c084d503008207110040c2d0802c48103881020305a0382d203040c100e10801020918070780086030f17201d82100c805a501e4646110210190042d260f4100c040800001e000072030030001d80c45007166121b20f4071114200c0100c0800b5600300c2c0d105220b400082440144076010641c032500782c0301114411040b094a55603188a003031840c681002c403084503994403041c014818550400d40e11503002001320001c0c00075105ca540e01811700381c510310500341455140d100c800700d1b9030b00501000c003e140010342208402c62420708024020320210342c2804003406100c0114000d83c0307140b43c100c81a281c01030b19013031501c0040154403c1d4407800f45429112550780743c444446013109003008007440d1030304990711040703800c045c103201e070345040050800e01c00d14046443c04c000281c0c00540003414000c0c01d00b4902c4400c0d082d4541c201c0b00c03001d40e550391003a03441c1011380b40b13083e036030444884680c40000304c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 329510152 1250 329508902 329508911
    0x1080408221706090c100203120f0106090b090a1223030415050c0a0f03170718050d0b060906030a02040f020a0f020f100f24080c220203060604050303070c060201 71
    0xc01d440f80c442d0002d0b582c014054210398007016860500c0d1680104030403040c4100c1c0d261103801c52010907890380c16944650a60414030041100d00d174011007000181001c510070384d14004c1c20340000340c00314145100d02880302980b00c9070740c8140402459252400030165a1400404400c4c40c401c54403548035010304107501101d9078030704020b01c0c030a00594458030400310062000303a0030740c1c0b41d00284504448080b0100504059210000d002100b80c843c0541d245880c0c400b2104240c0100c080100c045820450003101d44112040c04a082564255044113095405070310076220000404e083c0351070180080e4220f414050a400d842076140e00520f1400740503a507900b071481d51403200b2600c03140000c00003440b9510040d00701030580307140e520120f1541a021030005c0c4e07e40003080c4c410980c0805102c00100501c7c1004100b10303042090010301e8188200b00c403450326005c900901289014603050021000c60707404000a01d03075444903c1240d001e000014200c17512902c40f85048080004a40552401035081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 329511402 1250 329510152 329510189
    0x30b0108150306040206033c0609040b0a0b06040803130e0f010b030403050921030a02010c140723010212100e0112080a0c02090106031a06090307050108040822 70
    0x80c680e10900081e401006052540c489408110f119000a405201000304010401c04140304420820306800050321a00740781c140604000311901070002c0c0074034081e0314070004000020f0202080f055121400305000913800604201003604d41c0241e0f0020000c2d4407000400200d244c400280503c104c0302900d94515641d1394423481e20468a10a104440c0c0d0f80f60180302050000e8002c070007034248100080c003048004140207001928681d202040e807040d540002988038041503080c0100c0115840c0e030306046070a00740703180380010300c1e06c20054003424907000f031001003102c074411190036081d000e1901d0007036413a02f48402c00d85001c4542540c2424809506d507000241042c003880f0f806040750440b0715492852885503c0340081544080002010061070b01003c2c0e00503900d0030701440c041c2a5076035000542d00389a00c03094601e4400d00c90320321311901040c094040c4070381e000101c0d00c1c01d030341d4280703012880f64070760b450004401d01801c410021040ca844845107410019400d542c403c032044001c1400040e445c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 329512652 1250 329511402 329511421
    0x601050402070c0e071209150e0a0c120213050115021c0f050c0102120423010504081603110307030e010807030c0e1504080a140115181109060703030b0108 68
    0xd202d200030502c60100b01c04116803420704028590020a40c00c0c4082c814a5210009040f200d03611011107040c003d90500640a4009105043c01c40840c100103041c401d100d40ca401c1d103c42000e21503400c15444110030700d4210f4860031041007030192010b0051195503141c480d00e5108000b10b981d14801032092000c00301c0b80c0c03240411088584996510b03008411040710318101c03041e07032015101030460740d02005401112003551030b0b4503100764017606c404088840e444e000d40820f0042c0b52904c40e0f42d681000113001c08140010100c0b004283e55103017002071880310749001d80b540b40a034400c1e0307407040c08046540001d042e00071402040803070007649d8a550f2940c50070030a408a44c2220030000c0060280c0c4c3c403506150500d809010342c400c0c4a0200c90b81030075900c2e0701032440c0511702202240c01000c0821381c0344064a09004c0c94010b0f2091040341c080301800c00020040e11000421218040c0e2745442c40752070900c11a80848010303910140980d5915861410013030003602c400c02007140002d00180000e00102b5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 329513902 1250 329512652 329512657
    0x604060603121d130e03070c090b0a03050c040e0106030506010b07060f0e100b01020c0a0611070509010617060a03120305041101090f1a0405090423030a08041b1806080601050402 78
    0x54801c0e5904800344010b05020580014642c000c1891742d54518204030390b0300800103001414450b440b108030950401c222002500c89c4004a54003c0382174803001d1001400104450118041c1500d0000d125042800c51901400341c513400684130340504d10000c61085608001811814002d01c0c082c040b413060071040f0011191a201e550f5035a401245a040001d0b0032600420000c2c0340501c12141d1401ca540009071182e03d040d449100407510341200d050560038180104001030070115907405039036160060281c0b078001c150300d00c03000c914003040c00500c0b19922114480003550b0010f031803000002c8199000750040000f0f840540719429002600d20700d07588036a030307214180c801001519840600e0071401d031a901828036030700b040100c07040c8804211510b40d100034500c41c50080d81e152044031840701c030780410071200135005116500100706da00261a0400340340d9810a41c03201070b0001e11111009140c0c065409a009440030000d005075149956129411940c181c0d4541803d40f00181d030b85100300300891 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 329515152 1250 329513902 329513927
    0xf0f02070311010c02030709020a020a02040e070602031e0d020d0506180103030e12010609091b09110714030904050f07031d150721020a030b120a0209070c0203060406060312 76
    0x803045842c1c440e030305501c00e2076031010741880a82140d68290b01d1f0f0941900b6604450020310060380402c0c10b50055140c640524210110018042c0904c6410218025201c0c411a211049480000c52004002114100c00c6500fa051003401c00c5440701240741a8002405081d5003107071150001036007a0340c03d90350310080d26048950546a800034802c0321004c2c03101e0306030024111002e0703540c0c80780d000445134041d0040c0004144a010f6918100110240343d0980c41d00b5604580411442d10118022620402d0100c503030058000c1500c00b1100183d0000a14502c5031501d01c540080c00c00c4280034802c000300d207143d4042c2003151400d2141c80300d048020407801c0355188040000b580a4945d0b68450b481080740c1070340054181c40d0034a400050801e82045240102050f6140250300041c0704042c00d44c903100d1400211403c41d4500c0c1d81d455a6603940b592030704108030180c40b07940440d000c611540d006a0792400d01d2940602501d80918103414920700800c01488145d5500c41044c1060360400d200e5802e49015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 329516402 1250 329515152 329515163
    0xa110d080406050a09050f0a02150c0309040b0406260106050103020a05070f0203010e0304060c050c010504080c09190e0c03060109090c061409120610060306060e19150f0f020703 78
    0x1d81c0c032900c1c1c1201410b00580b000d02c4942e55400c5c00c1000c03540034441c50031074a010100030074a5500c0d51042c030803111a100c40052040c002070080c446d040501004599140c20216000300d03011600c800010000c00306544007070050103003201c2000c0780074001c01d00e090325408481d00811000d6a164019800d911890100400041003040760900203a5012030010340c06001600020300600d212200a16550042e00188003007010b249503501000010801015034000a2800c3d0341014030b00b01030207581c2c01c102e0514078401d0f0002030000310540480501407041200015041c050b111031103008546074020100da06000b4003c003800880c00d13149074051185d1603548640c0e03100340745140060880c0c48115040340202254400c024808090351540240f030103c95240c0090f051034240560728031501600d0303502c68424181050810040c450304808002c0e003007802078800e601080b00c1c86010130403c2d00b05410211014100e2680032240c20f43c040700190b840c00c02916034000d5034110724802e1380d480c103c03407000601 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 329517652 1250 329516402 329516417
    0x606020a02041104080102121503071d04150c11010b04090f140f0105040c06030c0806060a0e01050409060f1d0603032a1c0f0c150209011403070201020a110d 69
    0x50600354082e40943c0140810641015101c0b56101d09a9014464500c07200c9250018810140d514080700841000120000c00c6141e1030442804540b203110020b002d0200c00000008003401011000c180c04080c15000800400040d000054886680001a51100c0d0310780408034116082500ca00710712141c0100d90050001070aa4806e203104004c88500c6213140946040850046003d000c0e20340624842c00b441d02c0c02c0b9092400043c115032000120004008800d0203201a548500b41114840030007490607101034001200180d55500c07407a4040c1401515041d80041d00d46046899801034074141d01c43e41400d882900c1800707911640980d01d166050b0820442c1400035483c0200d412914014061850354030380c00801c046040c07100460300b400752407101100080c0ea1580c000c145040c466000d0600f1942840c01d071302e40e0b00001c40e0170212019565070019a50f031341c1d45e002d000c016110008084d5101c2d030701d15100c00001c1c00707508214601e00114519542142c070070803021078103000703514107943c43c2417 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 329518902 1250 329517652 329517673
    0x706111513060b010215010906050909010513031b0f061b11033907060e03120414010509090907140f0f04110d02040303021c09050904080702031507080a0f060602 71
    0x40040c841d0280f21070642c400c5e140c1009007942141d0320140201b81e03005000030340034a45000c2c48500b00c0c00921180060b4509010041c821f04043e105d0a04a038051a240ca034002c005610590000e181020180c4400d64405031141040500d81000180780035040207200f620500610a54404e010044003d040f50418000030f00d8485001c00e4001210700210450710181c0c1c0d603550080150484606462155040300b134040c0b00e225001803030500d000030143c0c010084049000c507000c06c0c80c0a03034001c0413000500407842070b034607038891415a802d071040240b1100250904113a401d5803158a03105001032903400000032407161412040c042035118004e0304c242c0003024460200001400c9400c028400075105003c03807001c07030200b40302500155100c0e400030040c011860707840045c0d600c2e05a241d078040240001c0c4c1413220b80c541c005400c0e003040d8070041d8140c98403184d05c002800c001c0341b154040c1201d44120104007060b5402145c5034094902500100101500750205a040d0340c294081c0101583c880030324030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 329520152 1250 329518902 329518913
    0xa05250909210201020703110303010b07061503050321010501051201260118052b0c110301050a091103150712020702090106081b0301050d0b04020409050706111513 72
    0x103078103003403080c501000c01000c411075104035040c458400c040180c0d404a05001015009421100302003050801103003990f00d401021600c500c00d00d007000304030071b890795540e0840003410390008005d542d0000c203481d2540c05002500c42a69041c1c070200480d0100030300001400d500581c100e42c43c82a60f0742540420741e0900110302c0751001c41e40e138009200b94107000da4554920081c4a460180250866408894600e50501c2d41c41c049100c1da40240303030009042c0c0001c20f441c50410142c040c0c0440d06081c08000307464206440402c0c1e1b40c0b405203415508143c00c02c1030540240d4004800c892060714402006001c000a0685c0c0e1540340c00c844084107020310104e01014051030084622034100200036141c00c0c41903010859082d03013a40f00c0030220f048801031042c09400c01d08558060719503030f0002810b640c5040c000400a01c480c0801400c02410034003c2425901c0390741198403481d80080448800d80da071600300401003003621381005444d002e442c03104120304801c42d4080d8080d0f40705502d00c0032092001e4992 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 329521402 1250 329520152 329520161
    0x804030206270d020d020f061504050601120f0c031107030f0809030705120405150a0c06091a090705040c0c0b0c1b100912090b0a110f0f0a052509 64
    0x855201d019151211580c42c4040001e40c01e210020313400350464003010380c0042c0c0f5181160b02d118a00380c0140f020405002d003005c5503c0d000307142c2100d02190b2510707168010384401202d200541502414442d12040d50f40b982e80108628901c01c2e50200210180c0c81c0e4603190600484030020001851030712420000c43c41104159000079015098034070303100d9144d80780ca02d44010030750b4132444030b000442c0070015803402c0790300420005401c007680303884c01a10b42e10040040e085810018103c0796a00c00741018443c0f090240ca50820345040d9420050602e004c040340d8840043c441c181c429402d01001484c8a4030459020108540c00f8032070181c141c43c0c414444801e07070002c5e155446185a03241e000b252a01d410400924511098400010354449034140111512041c00c200c5050080850003000b00302c011908455841c446441c2140c4490260283d043c00c1c84598070002c1d00c50b2140585071503031104081094580701b07201ea0700300c0c3d1644141d40040580b903c0901c142c210301d40700c100c0c410840c01c5447c0d0003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 329522652 1250 329521402 329521441
    0x50306010e043f12050609010305030a031107020a030f0b150310050a0902180103050d02030f030c0c07030602042c091213050316032603010902070203070b071b060804030206 76
    0xb90401208a002900c40320364075086820310008502c90084c2c0d01141da01e01c0740542000b000e892007100e0390306544989981e0701c170b2402c03175000b0960344805146039038410341c060351140d65008044000d21962303400c022038500c182050a8820501010100350008102c2c0c0000d1a80301c805805040380c1c84d01c5128400041800600300580d15480b00340c1d1400690740c240c02c0202055100520400c40e5045080c100d1400d00c44000c1c4405551041048541410900c2c051329803042401c0c1d815991034400180407800e1403642d41c0000c0c072a13070010a000c9488019102640224004500e4880d0040103c0c40c181c04c2c01c4006841c2140306030000d15906200c40ca0000c001d1401c08040d0b210420b0b01540c440c042454084403a1000150380142070040c020800c2d0000d0008003940341320f0b9140746041d80000b125595100600c13510032000d0380050b2020443d10103004441c02499101030054403403089051001c91980750360000580c0c8110340c0c4001c50568080c00d545030141e40c1640c010310042d914001c01440031042241d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 329523902 1250 329522652 329522723
    0x19062301050d05090a0c08031204171e0c0c04060e010608060d0507150e030309010206161103160212060c0f09040e0d0309031d010e09040303140c04050306010e04 71
    0x4841c8218900b1030007400c0c0a003404000408040441d070034201003007a03080c3c0000c074450b041002103c00391040c0c82c400a8200b03030000303a0900d0ba403c103080017850502c00e40e58191325525140981c1440380441078050140400480f0940c1d107680e140c034041004032420b0340a01c0c911501d51200500074184030b0403c00d80d00581c054448a40c00d2000d448251410490368040308071600b0301d01c1c42100040d8024040d00c40720100703400031420f00e40e200c00040d441c1d840007442c86c402403600c040e01b1a030142c86220020006103246081d29650040303a1381020511115070400d902070568003c5043c0901d00005000e482860b4040f4181c0c04c082c5548000341241d400002c1c0154880c2e00c03681c540506220601c6988a850030b207450010700c540351440c0242044a9240c040e1001d03409035030300d2103656600080b03100b010b40340c12110111103507581e00c2c0070b030010b280d282e40b503c6c6035080ca2000c028080e010032004005641c0110304441d226072780c44d0020f4039000c0c0200c0d03004007102201400d42039076001407481c0c100110400c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 329525152 1250 329523902 329523907
    0x1709040207022107092306010e040c1106180318010e06030f040c080f07050103110d1b02070e060619020a08180906060405061611181906230105 63
    0x503000036041c1a0b070341080442000443e0020103500c0d01c10041c0b20010840c01c0014440981c50026594280340202040600054004e0016081ea031041d4508155000c1c020400c11411481a50040484120358001704c410701c00e1030041841e648200781901c81ea00f40b0f0700000c52030030010302954482843e000c55014140004404a00b42ca03913601409140300380d0488051000c9817420b410700d61003c40b219404410590801117070f4003480e4034040340700c4090f41c0c420b0802060302071480c0c02c414254414a0011414285031076001c11050100c801b0240d40c003481c650072500c01e283c9602a605c40c041c0c068681d1548aa030800c0700d41e0031003850705800c406500c9940161100d800140d01d403406260301402c10161040144c02c80b4131500c1c0f505182507600008191520360615041201107001c9104030307030003540d032420032800c00c02c1000b05c0060141a4144080e1000398103200f25440d110045400360b40764050303c8100e100702003180030742d48682804c4440d09031001d03214802140841c00ca068507420101c0c10050704 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 329526402 1250 329525152 329525167
    0xf021002030702040c031a0a0608070309030c020d12180f030b04030203130605091207180506150a02100624050318191110090302040209060d090b01050a1217090402 72
    0x13240b00b03074800c8005070740300817501c07101d48181007010707810040340b0a2180210b8a414480b10f580300101650000b0340d41000162201a803c09a42014068078000d42c0003215480d60b20400c0400c182089002c1c245031600345003056041550020718003140a80c0841404201013000418a02c0e200315400500a0059a14100c280321000085030b14079044400414070000e6130391840c2c280040040401d442c4100076002590415100740b280c0d03107245609000d480d489502080719680d410002141001c90121072560718031100f00040d445400b500000044180b500b00d00094002c070800186100d40001806200b0704450404165401c2d000500800040c000060070f102401c1802c11114107262000080f10031000c0107440c1c061016040d0962281c0920390002003607458607000581042038070b41c111005619451040d0114009000d15140345500e14104004e1b803090105004825041e01d0707080e0303484404035403112041621254104001080043e826001134a41d0800d8405881180300041002d450b0825 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 329527652 1250 329526402 329526409
    0x3171207140c030a030e0d0f08010504230907030606050a030b060d05280b090f06160c1505061e1c050712081908071403070e0603091e0a0f021002030702 67
    0x104c40705004240c5c0d400700d50040f890304000e10100c0c4841c1d40340c51408600300800c0203000b40307818440c132401940c0321a100071504000035890700c07204220441092203407800d044282d603251401c0c84113071403091608901081e0342c20440420700984c4d403c05c20410890320b40c403090005124007c401541d241c001d07003050351150810f180301c4003011400b05402046148003030500094080b00038100044c55440001707017444400b00810110b030701002600e2070406150102000759000700c40520010505081480c408082612551042e4058801621b008200e48101040441ca94002075091a031000c0043c803000d0501c00380d5401d0b5002036103e402134403c266a0340d02d00302c802c0d22407041c3c00c8400c8480400c450403408483c0c40814826400c0c0d1070f1000c000e0030002c0e4040d24092040509121304500040050340c40e900980711200c0c0107030041d2001d950381c9451421240c848162024800318080b034440c41f84070072400040d4a41e602900b2104e1440500390035801c024100502c2010341d42507000038010307000581c1d03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 329528902 1250 329527652 329527657
    0x914010e04051306050a0b010f0c170a031b111b040f050106030209030f010c0912140f03040603061a09060c0a0b0f10050603040f0303020c0106050303040b0403171207140c03 76
    0x7500861007041c2d5030032458043e05865004140701b032403c0c54100c68a42617a030149558030842400d040c41103011b400760900003690786003010001990000080c80e010b10700d5060744070444100801c00030304100f601c0e18004451250280d0341c00440b0381d0201505100d00141d02d8151114a2002000050741000031440344059031400d912407400321768081580e1040307040038000c5403450036140f40200300c420300d00200501505020b008040c035460b02a40b6001c04c00a20310030036880100c1c84011601300080600185a4a13800b9000308400a4108000000c2c0070b40102840e65050a401e1002400d1004030000d00103540c100e001400d055201d510610000b1600c00c2240c03034020821030140781c01c0b5141040012078002c00980c4424007402c0d0400400002c40d41e10021002c8196147c0350241c1d44456032018507001d80829004140d060000080005490980380000d0045a02c180d0101c041024558800c09180c090010141c0e103d01e0b02c600000c0381c1920800301c1000780c4040100715424a042106194a141c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 329530152 1250 329528902 329528911
    0x90717010b120601061707080403080402010c020405040b10140603011701092a1505070f023001050603060c070b0604060f09020d051f03020f06041d0f06030c010914010e0405 76
    0x6030420350050003001d9025495a04151b0340e9001c04075503041913a40181035042c02000581081003c0c0d011404581c40b40107068240c1d40c00402c18005401c10342000c150302c0b881518100071006c259400055211981c1000b018060402840141541c1c03a100000102c2030440ca51903925540c1c0b49280000030380c0d006030b11804809840344000c4008c144401c0901c41308040d03005400d100550240800e0000d074031004440a0a9003c41d005c2000804c030320204000444103409200d819100d18403d400d510100450100d01d80100c1c00244015150882815183c03403003590b009000d20001c0010780042a500060b03190020f002420008100390388140c2e100704a841c981141800ca40c001400442c80443c07402082e402ca00a0200310290700c50038140ca081d060b420f444024007900480c82969615610203040d00c0c000d001c8100c000c421051000921055200c003160114040780107400460301c00e040026038540811010785402c2815410200c1c00b80228480d1102d943c100000b00d10124164cc0303071030003580e015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 329531402 1250 329530152 329530189
    0x204230a0f0506100309060605030607020f010f06051008070e0405070e13050c090f0d02040903020a0201091514090f1801051c0503070206091306030308010302100206090717010b 78
    0x5414184100425540c101080e00c001c50300380024020140d46130306222500300202e050010702d44640d0705d020009090254000780c0e16025000130041c0c400d402107488000c8a880304003c0104a050200d00801c54a06005050300304540002c080c407118000d44941ea0850803c3c2000401d42c001500001d0540d0800c6640c080080d0244801c0036503401c00003c602c00382c0d46240e0003804145410800d4024074040c40030400d120b0f0303585600700c041a40f11b10704800c00070703038000c1c006020416041c100695240c120400807030000d03400400001d40804d288445809045d25555001c1040113503805030080343c1c000e10300c3c0780d82c8030f4540703070014070319940d1143c8901d031070300c0384200041c020361519040120310200014440c42118202c03420800158001c03080303c40447e4100d1304a0744034009500858a036184440e5607003410380c90a5808418141c102001074100c9101f120030b6000d41801c00700403a00c40c10195903003000c950040b14140290400099890625100140001138203607516000039940102018455034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 329532652 1250 329531402 329531471
    0x109170307200112020f04030807061401060c20040605090a050106031805071707030b010b0c0706050715050403110d09050f0109030206120417030103030f020c010801061b0204 77
    0x30040140540340c036103100c00d180b100400c48140006410200c1c818000850254001414210140404146c85c0515005843c3c29101d040d01e20b480001046c00070141c01071138041c90000108075104904500401d58043e101030700012002600c54071840e400008294816241e500200d610707182c6d020307458810300c40c9180c0882d4031351500c080a03084a455044032076659403040c00c1d40020071800600141201d01c002000820018101110343c10a201a04002c3c8210719820001501d01a0302014190070603202040c2c03201142d503408142ca03944540400105408181c0b0080b00354095141d1007241d20600a050a0b9105440b80103080c1c10050a43c110901103400103d0902c114282404d0f040340400c002c1c2040c0140d070303095800049030741c041c82b0007480d0043c1c47c0d90700050030040060180c80c0c0c601d0050104503101e503144e19014001c107002c3c5414500510500c0d04280d00f562146040904850300c945a080440203548500048600c0c0004280c0e0041e45a005091100d16001c42c04070001118400d101d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 329533902 1250 329532652 329532667
    0x1061208130504050106020a02011d0904080a09060c0b15031c09090605151b0a051605040c0314070e0d0b0709062d05160606031101110a050c060901091703 68
    0x6461040ea00124000c03484c1c28018854107400145074042203809090a45180c5500441301080102030f19607150050030030700501007046503410103464456400c0d282c107000b09841d0081180e42ca810090007910403101400403680710040c540c02406800409015a0442400310381085028900140c030100040c41c140c0040042ca400352041501401040b59440c5080d40d148050000500518080e103e541820032800501c54008000040768242e00501780d40100c0c000b80010030f0ba004540c407940740207508168030305150601c030348107910b0400001850b095954031000d100f2240807031090132180d0000c1c9207500d084007080c0c400201c18030030035443d41c41140450815a0080a003940750149803c02a01111118034004148064010f4040c0d646401510b42210480b0a10b0f21f050307444002d419103280010100a128031074481c410400d4080e02c503500016518000c4039590704a0304405459078102418012807460010000d00805034140342c15194652501206822055803045503031842e4400034951 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 329535152 1250 329533902 329533927
    0x150d2405100203030c192d08091f020f040b030108070906080d05160f0b0702060f0114031b0a0f080703050d030b0127170615030c030d030e01061208 65
    0xe40c2541d1640c409142141050043c0702d2141c081e11401c8080080760000001c8414464501c01c141d50b180d0001000740c840c035400c40509040080100c0c00b00040301440000e01101c00081c50003040360700001c1c1c840d09a403425aa6a00a40000016840182c8104400a040010000030314060505c610191a00c5460001002e040307440c207a008400b2900704c400000489504402030b2f40c0302007282d40f03a030031440d8144d107458444020790110081c4194030303000c00e0050722640099a1849065801c60b000d407079076268003d00d8000c0841c1003000d58180d00808100c2c41241548018044140001c1c00441c0c1d055110100c1c82c0440441d500444a00e9000d28810403d001080290208000d111304040011040420000307102c0d8540c20040b0342400001003692241c088100c48102c01003180fa4920501440342410311610748070709884039428801407455070710703a0b4a00403400c4426084020000c1200d080c90b01d4043c0c020300a00c0322090040c0d5070310507000036034040722014240101d00c03d1550030354403803090200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 329536402 1250 329535152 329535169
    0x4020d080d11040906140604031506030f1a06030f100b0303090d0f050106120b060d051e2103010807060815151c05070e0f040e150402150306150d2405 66
    0x6d003c1030007045034a1826603c81c8412070b800c2e20b41080000c1c070342c1e00c0d0100020000e0020303940002c051070000c842203000d02500303201014402d0100290946903440d00820075603180008103030348607690400e06201020b0111640071038403180000d82900c1c144841000000d0800300040001d8a420000500e070380c040040a12400c0090054900414422007040e145c0e101c003404000c201c2070060410019810502c2410841c03411000c1a96a2000320035820004090300e42845d032210401c8500c07c05000240102c00d88140da0681e03000e100106041f516150089070350031006003940c000141c3c080c40307081290702c840000c502960501c00d500ca940d04c007071001024680bc140a51981500d203800144160682c0c0100c41c406004401c840a01005600200080080144071491201803180c041703044080b00203410264400c50080f039003800784d00001c40031407109200c03c17200a68027549840c4a11200d01c1ea0302c014003155056014001921102645150403401c00411103160500e4080420403d030301d0000c50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 329537652 1250 329536402 329536409
    0x506010b0f0904020703230a0e061c0c180605040f05242b0e0c0315040807080c01020c0708160807090207050c091e0604090b04020d080d11040906 64
    0x10180d2401c6100304511001e4000c12907018401c580000300702080c03612072071a4a14181a10040311083c085000070429030707174040c100e584042021010b1010062605809132000c2d01d0040500c4100c040c1d52040b03080080030940503000501480004500ca002908603c40e000307803100c0c1e20b0740795a807410907003400004003480d4041da10900c0004500d102c107451a0081e252581c0b0b03c41d403c80d40b91402045107003031f0b2201400c1004098680f800410080ba00c080d0084210a104402a42c02410818043c1621029080b00c0d40319104a4a008600040d17062401403041d903000c1e080c094104503100741100e09aa01c20380c0044400e5115000a0060400c140070b40e4001c146040c2400048901d090900758507070710b041c8a801103895000c24000103021040c0a214000080100104501d1030101d0301600031101c800102c4440400d00800030b0302608180c8150200c0c50782100050400e84c0e41c550030441150950a82200d1016051251403e81960350113074020000c440c1e03159503111410508140200d0740309a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 329538902 1250 329537652 329537669
    0x30f041b2405041505030103020f04051e070c060e1b01180b130801020406120b0d080403110d0611040923041403042102030f0d050a03020702030a02060304060603050601 74
    0x1020040442a0514084040c1c5850032800c1000155081929540980c4d8000d225660307045206003070459101c0b00450503248210b95040b194403003041030100300d90f0200c5045483d007500d02400000f00100c501d95075805421880e14030000c054a94036841951040f0801800c3e6030b0000140b00d61544075102e103042c11690078070f072842d00c0380c05419440da0342d60305600c690319403e04001800d03082c4845800c00c40d0081c2010b030000b50340d40e640c0e07528010310000c0045200c3d00e0f2240750034280130281c641021018226900245a28149820350701c40c401c1c1000b4405286600042ca140f00e41c0020701140103401d0041d44000b0110340380c0d4944003004058400201e10203001c130805010070b101005170001a2904650890210804a00e085c1c802e24954815504200c0909034144200c03800301080000d8204940d2082c0d050b15992000401d156503035a00c41d40345d02e000704a05016000807244203502174918240010125113091000350003040c20703540240c5055948549404041c018007000b00080c900400314030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 329540152 1250 329538902 329538953
    0x3060b011e020c04150509161d090402090606070501110c0d0c1223030a0f0b01030b0d060b0301110d050f070c0c0e07200a050c040908030a110c03030f04 67
    0x9503030094442a0f86003002e07204680d1900c42e41c50007079043c034680c4043e00000d04421810f052070142c50040d401c0e007400d0b60000600501c80f428031104070f00c64101c42514094807801c10390300d0326030030003440c002c0091886401001c14000f21020032024000c60030a9100c0300401d907510b42c100c00d05c0504241954510100784803541110380b001500920b42c18582c4079140c608004018111120110208951081801034110100512008000c9603104411042016008101001c0210010b500361085241066805104401140085080d0b500306c810f60b0301c40200001a4407210261504003500449141089241d840b0108080202e5640c0001e40010481c1418181d0741e4903690b030300316544201c0c0181040705043d0008120304a010300796100e290130045503e144039500d0000065500c002d078803402e46183c0314640c420328142c142403043d808040e400280b06071450f92001c00f282e0103000300c2d44511201e040e0800549030591010304c09540a414550901441c504090034400c56a203070580c4a4038000c03024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 329541402 1250 329540152 329540207
    0xc0501060906180b01030b100815040e0d03050405071806180504023a03050304021813080711030a08210f06130e0f010c02060108030a020d11031303060b01 68
    0x7000f035503160040840b03000c0b071a408904012006132030450b086c1908080d4040c51440f105401040c07603846445a580c2c04040420803504110a803484001d1919094101c0111190382c544203400c11640140600104d0380641e0340c07046140d0040b155001c0d2480100e03a146004c1c0000311403060070100c1d23061206018419820700d600090f0080c041f01d1403031000c203044100c0340302808200b01c10301c481c0404602c400e130f2517000c0f6500b0302400d154000ca070103c0c80764184200903000325083c2c0004500650000c80790110301900365882c103801b68080308095034542240c40c541034050f40d0030002e00744840e04c1034484548952040c0c44030388680140d1000500d0000c00d150030445071680c24098281d000b072007180c0310314400c0b4800750311100610034401112010700482d02aa8007050054206000c500202c2d0f0850380241ea9400500740c490155200d5600103070004c058120000d40718210307500c80e14004034256031504003099a01100c000c002d034812200191203030010152582c00103515100c40582100041442c02c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 329542652 1250 329541402 329541419
    0xe011d060606130902030a0b0f040510051309060501142704020f06070605010b0a09080c0307120302030f0309010f0c05090d0210121806150821070609030c0501060906 73
    0x1001440103010701c50120b40c020f0240d0748890381c0d60092100300800c40d40c0b030a1442888024100d6020950f0040d14144e2403045103047c80e104962040384003442e5001482e08003001c102146030700e40760381c501d0292100030502c00b080e203510035203009101e85000645602030302c0c01440252b0309180140c41d2203145072195036160006100c20769038802d41c11030301d5030517002c071000c00142203000703d0340050030862401c000495500c400d00024000040242c0ba410302c0b581d614040d250f82c40300000b03001609900312490401200d00030000003d038142c8280180c9007444e50080041d0750503041100c0403211603440307600c40314001216114600e02c00d00d82d0b203807413450b01c440c4501003518201c11000007401070134030324100d0720950320411014081800b601002d00c01c04140540c260b10740d03e2820030a5410798a0090b00540040004e45128121a0780401801c18400d251b404445010390362601c2c00860340703007045980300154a80c030882c48038030b100f034071010300740041d5041c641d003121174640140c04a545040c0c0e05215000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 329543902 1250 329542652 329542663
    0x190806181f0519150e06060f07080706141608010f1223030409020310050301061518030807030210060902090a0317120c0d0e0a08090f0a030b0a0e011d 66
    0x30700440c01291948400141d4032244111118034540c85150510b40b4004920600d100800c0f150540c2d104003070f43d01c0d00801c01074107101d201602130401d0020085640003502c4980a010700d14000d042c000f0ba412041d452207662820100c43c015603044c0041e245000f202d0b0805046405092421003c0c100c250510a8211780d01c480b039080a0b00700e80000c00807190b10075070b40560302c084040d520152600c540da81c11503200650001c0d14514000b040c00c0e540852281414414101150b260794810041754020b500b09881e80c1ca80800600c111740a6a4400b00208815030001c0200500c2036009103c043c100c0b1600e24101c80407600a8081c00740100728515103a1768030860360342901d0300643c040354680c116421040e0030348540b481c4910b54203c0602040300c14842030000d85402c1a00c12000d109007134412440644940c0102c80092080c0c005101003e45803c2250804160301005006003003056129158880250000c451503c1c0003030f12101c11b54440c1c3d1007801480788100908002051078180720015580740c0c07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 329545152 1250 329543902 329543953
    0x919020a110f0a0c060507060e01111c0b0a0608040c0503030a0c1e0201020606010f05090418051207150903110a06050115020303060915010210020d142a0919080618 72
    0x140c04501c100c01d0009a034003a0008200ca40003c120204145d00d0750b40bd9500140410140d4a01032902d00b0381c10b000070b00905030f06490081104091321709200d0140c034211000f42c801d0369800401200401c1d40c1d00c3c01c200a000e48692621559030403404c42c80d2004848010303528071200048645440c07001031740c000410320b80020090030810300b102081d0900b03caa6019940c2c0d1142d215003400e0346142460442600360441741d01881c161000c6100313080509080f403090560050101c0107114049403205502d074082d1410030311a26004295100e1009190f00d0b0940c00710040c2e668941d20401004036484c84a80c40220703901701d002860070b40ca444000180304a10040400341008001207000c007203a842804600c003900c452450441d1101d01030810f2500520700982804074028606006c210710180809042d6400740a4403141d824a40840702c8000898120302c031025040486c146036001d02009861042000e005000010310582c900440c0300c0c001c0c00b01c01e003a0078400c0d070441c03110101440f201c0b54049451 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 329546402 1250 329545152 329545157
    0x10020a0b0f0613020c0c0f121905120406080a0b04060306022701170a0c02070b13060e010504050d1103010f111306030e061803070c06020f21090919020a110f0a0c06 72
    0x4000b0300c1011501d101000e0005c1c10702c40c0603408a44a082710040494041907020742c003154098880c640101c8440d12a5004150109103440e0004c1c80001c40303a0040868614043c0c0089035480d034981d1040240e070418841d451418004081c0840c846c8800d03c0c1010b0405000d2a1507100007054a80d14090700038007800c0742801540700e00100c0e00c1c150081082100a100744030030155039010044040c04565100d014110002d00500d0a240c1290700c00d0081c2c41c20b1700d2004040a21170030641da00d0184882162141c1a0195201c03001e905079650a4820342140000a081d9180d407128180001c80100c0c80710341118040c0740c5014110308000f40c0025030240c3c410000c21180300074902c501d490501d507005443c0018800d0714109008521140c1c0450300407192690003046940015011903044104041d41c01c980c0301c3c030807041c007150301c4528209400c0ca400c152181c0603494019082c1c886c40b0f040ea4032403001140850030440640c04040010064410301904280141090b808a907903a15500010351113941c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 329547652 1250 329546402 329546419
    0x21603300e0717150109110a200d0207050f0d0305070825140c030f0d0f03092009180604030e180a06140105030405060610020a0b0f0613020c0c 63
    0x946508200e030b2005440fa400e54000e40d060b5007180103079246810789512910a6010000040402041c02000e4440301d10b8020355007041c6c0a06400c07a03592560083c0c5400151f080f03140d210008409100441d00e02016501030704005041009000c5c2000f61050036a00441148030b40c0c1011940c481c0c2601c82203580f10115503130701c241c581442641e480080c40d818a81d46184c084130000c110800d0980b00301c42c000e900644440c40c040d40704060315030030400c00b00e02c41a000514091016031160104825100c2141800034003003010303441d0410007400d10700002054900c43c100b00c001514056461035800300883c49202810311150a0564a88001070002002e005500e04c20780d541c0c0c0e888a091001030848005d904441349050f13540300015080303510440c00244c81c45801e1500c20751283c01200e1055800c40c00510b43c03501d0700400d108800c42c5890110382140901e2031284002854000a1401517050517409201414400108050f90320481e46100c903c80c030405c2000e9120f000880c8800410600300c51410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 329548902 1250 329547652 329547671
    0x303030a1119030501090e0604111023041706131704030b040c090606030902030307020f06070203030d14100627080106030f060509070f030b06010203070602160330 72
    0x31600d0051440b050303003141550115030207071503040d4866130480f540700c031042c0b00ba08180c3d40e03416168070060b50050800045542c000f0300c2070601007807000c100d100780e00d01290340f007103030100c102e45084000c00c07510f0310b6a0f400542004a46a01d501d160400079460018180604101902003807102c100900181303005040300300c40001074030060035a001150415a024000c2c0350a2402c5502c00c050f070b000f1221803500e8440042016803003881440200d95028004510b014819000c205004040c140c00d90b0b80308030b0400400e0300603103040c0050800031110020100e90b140c2c0313101441028090041515002110064040081d030b0350000c90700b20328404a04250403000d6501c030000b440559581c01c00076056092003000001c1011042490b0200c0740182c104201b96207650340313410b0310b5005d644610744100b0140c503428004580d94002e100d07080003050049034a4070b0001d0b80d4040c00c0ea08241002807103064040c8214043c583c21520302283c3e801071140700040001c9104a06041000104c60f08541503a0348a00304c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 329550152 1250 329548902 329548931
    0xe01090c031119020706020316020d1707030c03020708150f1005120a0515060604050907030f060e04052e090201020102040b180a09020c0703020103020f093003090303030a 75
    0x20081405a00009a0f60740d200a1129440000c2050764001072048140c00105540b02005503940203070703400d00e1800156011b03000c100040700c0c140d9081d6240560110000c1070103221038000c0a60360721070344800c0d00044040c240a802c1001d01d034000d8a01d904003a03850301014a044904943c04840b010001d10300780c8401558501900d4980c01164100f04030054003408a40001060070f4664030030001c48440044909081011080c00e50356143c002c0310a0006019610300310380b80711b40c40302c44ca29000445203405c00c0c0340d03000d1321601d0340500e0010668100303100c2401020310181e01c020090880003003000c015050103c00401045282d001d035165142580811a8400e40486004140b00c5240d26210440042030555200403a203005e841800c41c044005000d01701402503c0c0d41321390703000250040b5403079034005401035030080710850901c20041128480c1c41e036414009403009000103280160780c90703c1c0d109840d400d01c0b01190350046a88103100d40c01c19941c00000b1030f030f404504104086099100b80304034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 329551402 1250 329550152 329550161
    0xb03010e060d0311070303091701091104090314070605010521060601142206020c030d08040204020306060d021306020c0a0e0c09031501240806010c062d0504050607090e01090c03 78
    0x8004c2140540340b000000d15502181c1703401500d803030142000c042c07040041e0141c205c40d0f80020040003201140060602803400d5404110f20a00a007000580280007022a504550104034116801a618001841282003519801e548400c26a0104050340524003481e907640c50000c10540c100004649204510036081d0f06660041646040e4445980783d14140010790b64940e015040c0184540a400c0495103000284544040b105403203025a03600c0342c0d0240006544010240b68000790100300c0c1c0312000200f03100400c0c2c8101585001210700d810114001e00b0300309010312207881680ba11900303011850006201ca6000018003030400d03074030030080700400d0030004070051004100c0c074490000102c0040f01c14603110640d603620314038182d03446550b100381c0d90800168bc0042c00282042040700014106901006a055102101c03030340364203011140c180030000d441c42004145844405010410004010750398002505003480034045090001e00b400c250340510035020002d45480c0d81551043c0a42d01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 329552652 1250 329551402 329551427
    0xd020a0503161508060a0623070b0a14011a070204090204051e07030c05040e060301090b01180f020a140f120708010509090d0f030e07090c03150b03010e060d03 70
    0x1900c4150100404040c4841414850b90140785004246024400d1013124100c1c801c40005103d00c0140c1d0038403408070b60204076000c0c0d299884095032400340f045142200034141c424840c10303000c079092520590b0002513600782d02d807066030102c414005124072a407103034400c0204c0300d200361500d45480d0701c1d000084c042e00340f0300c034069005403925041c8103940002c1c0c0c2008041c2c1d503400d160255541c585100440031545100c101c0c0300010002d00040c80001083c045c615000503004001003400d61103521842c5041c81301381d000c0031301d14070444582904200c00380035207440094005402c40c20f004007850301803e40048210f250140c4900081c5044912140109035070559a001c901c2802500d00100c01604a80d400e0040600c033f41c0102c0009280003070002036100c40e205455503103a5270080104c009a015140005030700c90a8002c091020070408440d114200d01e000070760340c010403c503d00d554140c41003880c5400c00558024204018001c0b041c04400f129000748041c3c940d01c404082c50305040754080c80710340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 329553902 1250 329552652 329552659
    0x70503030a110a0c0e090d0f05040510020f1209040f06050f0108040c08061e16270b0c06010f06020d0801050d110d0f02010306060201090f081b030f07060b0405060f0d020a05 76
    0x324042148440b038040203121b8103020003101d50402840400b41c2c0d40120350520f85d40000e00401c41880581001007090b2151091401214482034010082c1401c24a415104c11f00101c0c0c0800c110700c0e603103064010301792016044e910800c080d5040102007807000707215400c02d40c10711154601240820a210242200500326071080c1c43c90b07410442c062400014003c50184403902c03042c00869000c0d0801001c40b802450301c0c0d281e0351009015001c0540080000c0c038910305691410350300c006044a0284000e010009059010b0311035917043c40e0308106c1d900c0c070350f0300040110742c8019040c161554218640c1410345804840380303c90030841e490840d120340c803012422600140000c24003000c0100c000f020070b9942c0d101344c070700b4085075450300790032800c0341c0f8841c0703016011911842449003c2007d072002446071010b0300b12005503000007100030502d960f10000880c820320b10002a80c000340300f441d10590040c01d00444061280f418090f00040c003039007882030401d20504900c0c40f0309085603200080c0790020321014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 329555152 1250 329553902 329553923
    0xc170c030c03041505091c06020f160212010c0f1d0402040801050a0509241005091009150501050403021c1e14070302061218062502070503030a110a 65
    0x1941e07480350003a204260422034000100200300c0c2c014410384024001c0a4071845c01d400341c034001400c0d000c1400c10140e960035820480a0034105010004040d95a040c1d84503a080710b0662041c40703018000d03031000d0040c691500300140c1050760701091151090b40c070f41c509080c0c87e81800030407402845088c101c2560080c400640024001c42c103400552165110038401c121640d907100b2966250261608a0742c0d41c0420551800b0703c0c0e90000c01281c0d00120307103000c040c1065450b240880c0700720340181c440300b60b180c24003001000201e4480c0602e02c40815866112074100e80b4000001e03041d4016404024401c8500d420520b01c2ea1950800e260324046e002040c09980b40780f03080c43c14001444100d81592261881c101050740118001200c3c401c80b1350290406141050b41e0298040c22407020301518002440e4803e54034030b000c020032800e40202e0105640ca203100e0a800d0040191242c1c4074000c40564102e46000c11060350007000341d8650410500789618034007000d030042030901201e032100500d030716140b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 329556402 1250 329555152 329555167
    0x2090705090d0b010e0a090b060103021e0d020301150306030c330e04060605030f01030f051609020a0809010c02070e0a02040f08010605180c030a180602030a0f0605100c170c03 77
    0x45220f2812240c03901640d9069032502071103042070b2141150701030002d011030b0010821552199005041d19040501480d004080e408011103042d0310a03c941014190040018040300b0345504825038030201c2d03400d007001940c0c9107544c0c400c0310b030300750b84203812001c5407040c0042c00380c131242c00b110080d003410742410314080b1409290203410f2020b021031190140346008000b1900602800880e8020713941c018a5000750380c84c5913030305080e0084001c000c40e200e004082e00449420308840f19000500b10851016880b01010741000b085400002c1841c10907030305000002da107241d0041800d0090361500b005201155444281c180040d205a0740707d03d100450b41c0360001074509040d440003080d548211a1542481803600082d20301c00f4083d2103003d002c6104101281015255a010384603050350342002d000b43c086261104412a00111900c640b503e40301c5940b0710b2004024410741c13002d00012140c0d00b00c201a001e00013003451007100b4000348905845d5010594023014601a40e19180b84403080340e584501c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 329557652 1250 329556402 329556413
    0x6040f0f0e0d1b0302030d0506010201061a1206040c050d0b011112040503060a0204050306131109040f020906010306180b0d0807031211030105060a03021c18020319080702090705090d 80
    0x1800344100e0008a07100d400040c0300402d0a104095140c140d4003e44c101001e0b81f202c00002e040107411581590360340c11001a5080081028404200c00305100944528072401d5102c4225001015548038034640040710003461b800c0015180302142030100082c3c01060000184c0c1d0042030b81003050394078030402080a5500030b0b000010b02c10f403031041c1d05542d007503180c00040c0020390041c0d0203200d0341a00081c000840c0316405810b0030410502804c0310803d802d1000300444d456a005880c1952844041100c0c0402e42c00c02600142e002007081c601040315920300903103030700c54001c041740f800d14031615a0010851030341d50613900c41d00f6a80082c6100d036074005d20f01e8040c0130403a40c8001100201e003130408004030380d0850410741c2d048641c061300c1d103440c01e620300d50128002c0d0f125003041c3c5200500d0320402680615584192907110400380350445903c10580100351405401c81204200c1760401c1d948035000440207810781d011581d05550038006601c40403402d841a00580d60390641001d10400d020082c0708 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 329558902 1250 329557652 329557663
    0x501141020070f0602011a030c0108100e0a0207060b0d03020d121407020f0708010915020c030c070f08010b0904080f0c030c01090c1502030a08010b1602060f180a080606040f0f0e 78
    0x4c545070000c000e994120980d652080c0c09103002c01d81e068008800e840481d50246035000e5020741c002c03081d401201d8544607010100001910340c8901e085e070128800741001011310510701a03000443e480c9101d0001a03034000d40d01d014010400b400c0005030549041d480800713030048801205000907030038052030800c0e00207503103003036821400303201c2c0c03180000014035064107104081c00c2c19004200e2501394040403121030b01035401800c500d0751500c02005021031450041c049a8050680f00600c84103403490903019031309403500062502d00c030303506140a10000522900458122400a61040da1600d083c1c0421600b140580c81602809500300ba01d06001c100080c4003c805175a1443c1610740f50b00581007003282e90340a4018100007150341d1705c0c014040c03484c002016001c075030142c414000344401258080703001500440303d40300002c1c00100d60b0001e18560342c41444060101076400c40e00b1946059901d507602d51001d0806802030395112251000c072101d540200f070302c800000d0014031034501d0314181156a00d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 329560152 1250 329558902 329558909
    0x80303150a03030503130f0b0f04030305011406031f03080a0801080706110c09060f030a1a07030b060a0c050c06030c0901091e1e050d03120501141020070f 68
    0x20462820054490700c0d00c1e4640d00c0075260140e40ea0381c159034550790b10901c041003108080d14601c0080b40b8400001da40064842d21400300c00c4208029400c06150103010340300182c00408907110001413004450311850142d84e8854148480e024482c01c21540c6003141c14696000588a84400104480e0b500e8010714400e040310001030845120715a101c03012078030b074514070020752556080919490070f6450881001900b00100400045191210900103454066140c908131056007001041c00c1c0c11035001c0c2020350b0712403002c2c2401e124081403040003c540d03200d44080300302030200700c0c81c0034814824104480d07660988040c202c0d554a087c80070300741c440ca4100d490240d00080c5640e0011030405a8030645508040e0914010310756641881400b2082c84d840526250300702800b80340000b0284d969910501100f0b00a88034805005a40b0b20680b09544d0141c00c052250b125003020511241c5a054000503642e000d45010101501c1c20090108002d031203001001440c07082d0540400e0b071011158010089 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 329561402 1250 329560152 329560171
    0x50f01140f0d0b06030f0d020129010806060a09050d1a071403010b0a0507020405040602030601110f121b010e010f1d1903110307030332010501120603020406080303 72
    0x1540d00e240304200000d210598041e42155071480e066002a00803207490303811941c000d080d10340400207040300e94134110400b9002c10050f9126028046074036040b450b1780700c0d105010221a072032102c000002030000c0f44042c0c2140d0082c0c4000820342c003090b200302d20ba44083c08009044880d03514190038220492001d0000c05001c48612170003051095000350529080485042c3e20746041da8a403d800c503a140d0031480048041c00020802c5100507903486c407580d81310349e2148400603140d00700034000501010b007441d605da200340d100144005a0000000f240c2c40d03003040518500380d81e0409002c4082c1510807030b1101d07002c1c03076091031240c10b002c0b4810341040c12a0142c030f0350704009003a92203182003892095032040c0c2c80560013000250400e40240d810384c01c0524028200380401032510740c001442c0da03010580540020350f8580d0040c00e4900604c1500d90171250b030808054010f00da5a180015070035040c850f003418007009c503164404407001a0450b400540c2c0040040002c150389000207904e0b42e004803503401c80f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 329562652 1250 329561402 329561429
    0xa0b0103050a030f08101403030c0601030f05060906010305030d1d0610140d150903020a08070f030915080a05180a031e020102040b07110f0d03020c090a02190c060f050f01 75
    0x1000c4d88158440c51140608070711000702c0c103180200100d40f0134010a40c3c1c94040c00b04000642212a04100c0d4a00031880350b4940b540c00419401c2290904002601c81001e94004000410104100100380c1c2d00c44500b1410000b0380c1c580340310304201c0c0c050b1250303e682071a004180c20003565800d00180301d42201d068450403440d520503002008401040c1110042113081103000b102520b0380ba90b40001184c920900407600504841c0d121455140c1148408844246402107480300705035100000b4030007001c1a1104d40100482c2910141c00c00c8030081684000e6940c1701c2c0040c101e242a20110004050803109481255025081c01000e2440d508070555a5170503000701c400b0b07030300e105200b150122008840050300b0710185996440701a60114121030740814103154400b160b50313400104030b036024840c0d0010f01c2e0160360f203028400d107900e00800200c0c0b203520520005811840703070300245030401c03030b68902005090503a140000c000c0500445d8400b4803072400c4100101c0d040120030b1141030700d68001c80c512 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 329563902 1250 329562652 329562677
    0x507020102011406011403040501020408061303021908030f04231b09042d15090b0708010e06012006091f15090506040b041b0917120306030a0b0103050a03 68
    0x10000f1800e48400f40060b0408014421346810040519082449040090b142c076507100802450400141d51540c1e4000d4402c00500400d90101306180d0381070340160002504403499110351005002c018840910060301c41d00250400c4280c50701c41101c0380c0801c1c070444400c03212524035984e80741034211005c055441b1170503039840340c608840310b148600c0d400040e8100320400c0041120148440c155150301d00d02c2c80800581c009030f03440383c0c0014044030002000501d81900c0c246800138100c090856424020007078014440700c0c0b000c01c401a400304003800d081c2050000744007040c0c0000085080620640260f03401d100701c83c00e0200e00310468a01e0080c104440081d81100d0100303d80745c07961083c244480241c0200f00c1d104980d0031017644020000d00000c3e540c0c00000c08101500c0c90303c9403881d01904003c40f05003071399410182407800340041e2000404000c0341c0d442096500c80540c0d9a4140e1220b000c00024042e550402907102850380c07280714440107503901d180650751040074540880c00b02e00c0400c4d600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 329565152 1250 329563902 329563931
    0x70c06080a1109030a0201181505030411100f0813060f020306030c03060906070e120307050c03010615090504050619170d0e18040c080106120c1203052203060c050702010201 76
    0x1c520f01c02009015000814240c0d005692101000400b8440b00408000005400101003400c1485a240d61074603070b501d240c03d1405540ca4150040f0191103425401030481c504c0d41d00110104604245040c146d102c3e07100c5141d0f42940a004002c0100054140b0b001c1c00e100c80c5564002d140039200540c101c0b071840d00907a00f016200c000444004016520103c00160503521400d00b4406200d400740122080804000742c150455000101c00e984aa210400d0f500f41401c00740718160080400218406903108808001071051202e1b02c641c52242e5102d001140d0659600758880b05040d0b4518111000b0a654034100c0380340f02c990004010030f500130750180400181c0219440340c4d00c088020080060511000300c911041107002d0026160740703810701008648040700f441030001034184901200b0240500b80f03040c403454207050b044050302080840500340000d402509842040b1a030300c59102c10421500c2424407a081c0c0ca520180045051103808142d0b81d0300a001002014002e83c001d112010b85c21185 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 329566402 1250 329565152 329565157
    0xf0f030c06090c1323040f02010e030609250b12090c06090d08030a0f02030108010b150c3a09090b0901050f0f0103090501110903061b09060f070c06080a11 68
    0x10a4000049403041c0c041e0b0300440d480b0030362003010300d00c03401e40b4400c45d650b80400c41d03070040304c0840f808070b000122a400e40d82c2003c3c051482800440c0240707181d2800c20300c03842d26858800b036140700b0940c0d0190507001c0380f186180e0000c080c0c0110101c0d00e841d25456845891041c07816506d0380c00d680120070b0304420031304100048070060742d8040d010028101d9503903108007455000420700d441003070f40d4003c290b40030340b07031400114002c0040e0400800c1c0368a114007088900d800080282c20910000c1002d480b031502d001c0303a07801da00e0b0741200c0702d5206100200000f0310f00d50003600306294034496801001a030b858001d040c1c0743c01d17240780c1001004208140014808184001c0c06103980c02090342c0c95001302440e01c0113404001c22010f02d00491040003507940c060079111201410348020b5000301e5118003d040402c941c0d5031001407400c0c11100040013109004462040810380c501075140021220782c1000100100d5598950141810300c90342e90341d50000300040340030360f40901c4503410101052043c5030390034103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 329567652 1250 329566402 329566423
    0xb04030201052b0f0f060b090f09040f0b0c1804020901082a0408010c1107030f030c0201140d050115111e19030302180405130f050f0f030c0609 63
    0x1900391500c106032800b20408001c00c03046243c020003240984104076018044c502c202507681070007283c03218401003d603041d18082d40003030745120404d1010000036500d40c0c070000c8256005031001c5400351604d00f40b900c040c400c154805881c850a542c103116101d41a04020000a00744801651280c181002000183d01c9403208050014145a020171011a0012590100b010b07001c2c03000715005c50301d00c100e4007168100d0f80c004000307655548003038581550000d544104401844005c0c1000500710f54513060f82c84001d084c05410050310710311400441e4040c101c0f0b0100f10b604946420707110311144d032211015006c24025061700b00d00700c5001c010725a00640b80c28160300300c0c620292a001466002d0f0241e890514003080d031241c46180f55040401d10b1a140c003001c2c85019540142c0c2d1040d0031004448074800d0861117501079441c040030803100308180c000c020b010507406248448403440d1030605501d048a800340c1480207000340d00d5111942c900c008000c005000c8010161003080d03032000300b100c0d11070121a4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 329568902 1250 329567652 329567657
    0x70e090106080f06030f1b0301050f06030d030b06160b041205191209080301260a0c0302040203130b0117010f0c0806130f06060e090a09110d0f02120303100b04030201 73
    0x1c08180c4402420b4843d541c008805811141401c0345200c150340b5140c0d0303403841450030041410301d4502a050a01903d0381c0000f080e40c0c18001f9040003004280c1d03501c000d40d4210f01309a5581103601555803141c0842d5101c21580b21491552012420310401460042d103084410803004c4074030b0040d41d80110243c2d004031004c69401c28001c4007010080e9504030f040042182d0b419521041a000a80508040c501800320005440e00b0b243c13500c3e0014035400c410606080983e4054952240000e0480302110252a4160f90140c0c9941381e180102070030400300c5000821401e2104000304001149008079000307000d0380c0b030003440040c02608010044501c2c0006120000c0c001500145182c10240c54080014050440005441000d141328404803482c036002000024030012140c0001c0c035080071440e03000b00e90008200034080160791034074156480740b003001b405000e00034814020301c107164102a50031900034100040c503061051080d40c90754411141c290031710f4038410000c0341c9055500151426207a041c1c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 329570152 1250 329568902 329568917
    0x60809061501030c02070302091e0702030f16062c0d1d0d030915050a0e040209010f0e120102030f0906010e01030b0415020d0e0c0a050618090a0b18070e090106 70
    0x10070044003c0d102001d1070b0015071284003000001600c035808941d100d410078103404920404c0b0001b481d8211103018100e0011540107001c40119200c1141c1214551040c0c0d9045c460302001c00e2510b80d01614032080d40b00c851504165402d00d140c80c0701c00e04052907505620640d403089840241c140c68500d8038407100d40901061100c06012414150783c007104032802803d0180c1d001e5031724508030864070841d49140000403c0801d1244c1c0d903540156888055402c202c03019420032419800081403010460300200c2005101d5a400d80540c580b101c0c001a40440100207550301d1401508140003614181c85034074940c803420000040c40c8040740c000c50b0690b980802185203907115519607055008030000c9903a0000d500f0400150700d070069104400620f0000c502411307020300e030302040100c08600c0d40e03c140e003c0e40c0c0802a00a011051040841c0c00b004100c41566640e00d9a180c43c60003411030a2880350003132a00b07880f1010f042005017440d84145021707540c0641c40c00190051000b0003400f84690350100700d08 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 329571402 1250 329570152 329570191
    0xb100c08070209070c12020c011211031f0b070606031b030206030703020a0e0405070206070207090b0607020d080f070b04060e07030f0f02040e0d0c0b010506091f020a020409060606080906 82
    0x6005402d400ca40245808501031780075803220545940c84c004503901583c4224200780ea10350300a0401d424031960340c182088030041030100790000c0c3c0300040403c00401c90701400046101074840340d01c000351014001c400d807180140d1903c18024401c6010641c5d03461410101c040280e00400c00e183d0039254040c0007142180c0303c500b001d502a400c03020b518002d109810418207081c6d201c911841d8401c94080d40140668102150b01074140401c42e0441032040c2e0900b120a070103519542c1c04c44510650685504401c01110304000d6007030702031071482000b0890005004824041c4040b1140d00850081c80b040103000c010700085d0799103115902c4014081001c6428400c085040c2011030b1309154005400454060207401405041242000304140070031b110b581c5402c148503200e000300c2d015200c1500e43e24a011050f800084100c80604d000b41d00c00d6840c10740a1142a1090054400580d40500700b03000c105002d140c55000390803d4060031380000c1410380000c404400018801c1d0041101c4416101203090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 329572652 1250 329571402 329571409
    0xf120e09010803070c33032a020715051b010c0f02011406010302180406030b091b0f0405070203360907080402040507020703020306090705031e0709020913020c010b100c080702 77
    0x202403110841b409440d0791481d2a941d020282c0502e03100c11980d0005030341d400c00031400907004841030070464826031500340081543c0c000903140d060381c0c0c003980340c082040351290b421610f501c0351002c00780d1841c608501414000405400941451182d41c55010303a0f43d0000300100d00301c0d92810160308035400c1d40c0010404a501960051a41e550314200e400b10380910070f404142612001d0f401100c4100450b82000800141486076280c03840f2803a55441419079540005007a070400079512511455031000420183e500800c2100c15161044000c1e0140c076001420a0002031340c00c20703038070810300c0e005503041c907180c81c000d10301c0c3d88030305001e0701c071600c0d181c03607075024080240b00017010001580f0500e04007102587c0e00300030380c520840b040001012110b00740400d25003403000300d42a4041d00c00000d80c0000a50901240039401d0b41c85040d001a21401d0a1000420140154102d003100da840020001c0160701c040d0042e42018000b644c403a056079128020880d45058400806000300398144001c0d0014034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 329573902 1250 329572652 329572679
    0x2030d0b040e0604051b0303040806041415070207060906030c020604030c060e151605070f080304051603030f09061803022205010e15010e09010608040f120e09010803070c 75
    0x180500006118542c14440300d1038500203a030706070790790b41c49210700c0d440003882d81d907040104101c01c5d805981041d14180500c1d940b64006080200001c0142c0180700303121100f040a504034140154408046044c41400039407600524081c0c4400500840404a000d6000c1d019003c5030f04860380c0144420754031610100d6064452074000c07a04943c50754514407103514100903c80c440e0a5110010409061000500001d400c0d03803010300c1d007801030030300205000c122440440314030b09400c007610a030303641d4440c9001810b00a803035143d040b030700030b4244010043c154031501041d1460442d495005c0940e440340001ea5140c0b00400c101407801c5003050301070005091a04c42c41c0307600c20200448841c0c1c4100c140e00b0000ba12000d800500600801400b04403032441e80040561140ca800c0c01d100d0a030b0b45240c40460b0940e20140104c1b0103200701040440c2c100b041842c2403158880c0c020407044200c0c201b0000046c40145244010751089080800200c2c55940220484034003d60114641c3c0441d842c1c9041c0c03082c00d6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 329575152 1250 329573902 329573921
    0x30f01060c230d03061208071b0305010f0e060f04150c030204050603131e0c1203050c1509010605060405060a0e03030c1006051c0c17100f09050607020a0302030d 71
    0x2503100b14000b00160491100903042c284000c0d01410070107000760001800c544480d803000b048040b40f152000701054030302048076011a0403900801c0c0c4806100038082c0218035540c4010700750b40c6850300081d03001e0884c1d80481031075041c41c0107a6409403104589800f0280c410345001d071a00c60300d0003008251000992108203500a141009801e065603000083c031150011542c94958428208501d010440381001001d64075121140203a00d0005a8a1341d8481284c0c0d401411a004c0d8125150024140500700780c601c6034600208a070000b000718540b4802d0050280d036140700c81c0d070900c4404251440c1c15015542a00c3c0c001d804c0606100d585101150545940344070950135000810440c500b1036028404142c104a0108012407010f1401c0c1c10b10549519031600282c101180210040005071a0071240c012584410280c50b9808600f950140c2841d03010b0580010040ca0205545202c885030307080500c00901610583e1003aa8581d0400e903200c00d03540314010b0058204020400a07003085a000c503046 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 329576402 1250 329575152 329575163
    0x30f030106022b0f2a08040801060b030f0415020d1a10050708030a021803070e090d0507120c06020405040f0b0a0603140f100b030108010b100f0509090a0b0301060303091a030f01060c 80
    0x4005c0f1030b0070741500103007242c0e00b0f44003504001400c0c02041c90074080d04005001e14400c003465880c1442d4091030701e00d4090002001303d08401e00700465a6150f4055459a920011003000782c0b2140d1503480308190702c1408502c2c0103041074440c8461190150041e600103a820144203444c1d6520380702540001d40c00700e250f505616140340060801074508100e40c4000c0d25030040c4030041d0f400c0510a503860200c80b404c4020800c4410011040001e24003240e50205020a0505c030514101d80c0c0b41041c003a000e550481c9410514090920b0441e14140c1c100045c0b400b03080d0346d000080768a58a0860680d0715562054100a60b9280031803420280320440f6544105c40e003400040003511078442e4403841e40203910511490b13465103103848043c9007229460940e2665400d14030f440245222024049000d800302c001d202d040a00001043c5011907008110b9112000340200045c0391a860058131314201c40c014610204420003402c003680c001c1070101e901074031350000f030310115a2901c00308554a0404100482e00d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 329577652 1250 329576402 329576447
    0x7030e0d05030c0a060b0405010f0909170c1006050901030c1a04080d0504140f090a0209010c0c03120801170303041e020a060306061b0c0b070203030f030106022b0f 72
    0xca0300c14000f400d02c4038000c10140800c0e450904000742520514900342d4811803410004020b11806019401d044805074039021400c02060b080070303141d00d0314450000480c0000050320350030494000c941d0050b216200e50081101603107802c14000d0b5000309000003004a040c4000a01c094840b40341c4030003c03c041d5403c0245050b4880105a0a100b906088200890000f141c03d010388400e980e64249059001e84184011801203400503115050240004003034540c00159210907922450912080e00d401002448146941e0700c0d16007982c040c0f886850380041c980f44008118070b080550796642031200c4400950031921035480c0e007000103050f14604031181340800c0b807031001615a5101c60000302210b4900054203840d000c0003400d903880d1200400c0000d007114084600050302c0d4103180c01500c508200c082c4d1642d209101082c0b440c41810b02e0b014160601100000b621b9034000f03035409149104000d42400d0000310f140300e00c5c0c40b0702801c0030180071481e04003c4000041c424803045200f003068004848 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 329578902 1250 329577652 329577679
    0x1110f1009060b0108040506060603062707030501060c212f0601060f05071b0e010311011b0302061308160302030d0b0306090a03110102120108010b1002010b030307030e 74
    0x2403400654556a0022544903600e400a00c04144036001005500303003088100d40c030701551100d80f00c580040680f4455140440410b0700c6e5180d940345c1003500e040d02420803e000350200b080840f40c1c042203d040000074208000841d00300d2080c8101542d507540150004d100d640c004403d4040d148031840b01108200340c9400000030021083c075080b0503200710200da55034045c0400011400c1405c160024014460885d03d840e2655a0180072240e030240c010ba28001d19800c4d03c0103140f40408240d00134407010f00e84000100038030564003210780e561202600c990700075072040d1080100314040000003402581080c0e002a0800e07500540c180c03a428841c0700742514041c00c500010703d00858101007540180d1002c62040c0080b100c9100c0d10501c9241207000704030600d003030000c0c03c2d59080d15010060400044a50080b078504003501034038900c4a292603030030f03400c2da141c1412038020303c1840c08041c8102181106509840e0061168100f08500a0003543c03034072685840a85026011440c5550010f030014a4030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 329580152 1250 329578902 329578933
    0x303030507022a010801141503060607120f080f0c0711030a0206040b04060801050604080303042003010504060902030c0d0302030409110912010b1215011703072325050111 75
    0x28603984110070310283c08001800050100d0b1051308800c42080003411645810f80d40d8980601e10352602500d00f640e640d44400110b61907008126004000310060f007180034005402070ba0b0301010350703425519481155101c8100d241c0180c400d480c5030325900c504100354404106c0f12011140100e02c00f408640114590703501048840e40942d210004465000c2000c0c40303056070100079030b4014102120000d00307060030160121380302d10004d44002c102100768488050700140044e003407054807600400030803840c038081c1030400103070501c0207040703109028100d5248428a400714480004680540c001d41c02c1c1401c2c0660f51000b81203400c08090311003014003000740250368a411800400324513070008544403450005120500710030249090158000e407248025214050f01001d045691000004602030492844241144034021014060b00380c00c00c4030511546040d1150800401010b040740d04120100c0c0c64202c261710301036415010750b44d00d04400c202940c411811402e028908105440d00e0518001d0341 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 329581402 1250 329580152 329580193
    0x90118050615060304021c230303070809030a0e270414070602030c0a030302030615070c080c040606140c0f07060e040f02030606070b04110301090f0c091104030303050702 75
    0x40310320307a00c1441004109140e20101d240088003d480150444c10690f0006100d54005692a04002421030304c51003400301d0701500110540c0c46031500c03100e4103100640181c03654401c690f50b4010480031000301d042c11314004121200e0a419030b4a8002c4006450b04020000d0014890040d10000c0f0301803d1109880482d14940550303c112028603a01e80c03500c00690404020ba844130b02550401c2c00301d0403511b48080b840150441d0b140c500180d8a0356000d001a002d58100c01e404180c0040209022040007410000c00e0250740064084030900800d440800042d50301c580180c800185c206020a01c0f040300500140000e40c1032003060720348805891804900d085803503804a130001e61800000241800c00c2c0c410310039241c80402c004d600d540780440110362180302e100c0d402000c19a40c1800038040c0518a0144220324400800900400040d405c018200345c0381010140c0e84007801e00c00000c1c5400040c4070782488141c0c000245070420740380d03442c1a00104002030840f0158003602c6179110710440c040c0007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 329582652 1250 329581402 329581451
    0x610060e041515050909010501090806040b06041d0105090c040608070e1902072405040b060105160203100903030b0603070915111207050d080708010b0c0c0415050306130209070302030901 82
    0x140c0c4e0340c40780100c9040102080041c1c0c001814002040e1003802503880100b500e591180d0040304030811030300e07500082002440020341c84100c0070452000305c1100941904441c3c003d0f0460002c0b140743c1c0c5248004c010032284607101d190703003650000c542001a0304140700b00d260301074101c0c2084500c5e000d5405040c000e0742e0006004440003070318180a10041a80c0e080c40e62808442c030242001246002c1e0f544010900300070348040d0501c80007180355101c1c68004804000c2059025054407204420f108030003001c3c21005100300c0c003290400c0d49401042c01c110081d6441540340c0e0ba6076803582d920740751040f20b415187c4440f4200700134000211007503100d4200500e1a04503290f61066a9400441c1403890070480c40c411000e0422030400140300710664413030780c00c60564141d0f840c2035580381c1e040d20280e860001035104c2a42c100b17080c410441f82c106d081d11880d6046407416810b54185903119840c00e0800c141924000b54080341c25004039011074841d0780a0b540c004044000080c0c07034600034810301c3c0035581d00c16 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 329583902 1250 329582652 329582657
    0xf0103150905130201022503060e031303050106141f0c020d05030c0705010806040c080f0c0705010f0203100b040f0b070f20013002180a06050702030610060e041515 72
    0x45030411564104104000c004007240c80003229100300030303031f004000f60510014008903110345c0c00c1c8034425028412907043c200441d480b1805903a480c60300d68040c1546103c1c4d038004510500030b02103181451162840320200351204c0502c140410707103054914080404050780c1159070041d4040014404000501101d01407200030032205280100050480764000d1a031801141000c01c40d46145800400c0b042d040107022428100075540c98001e002d19000b2110301800e65802c0905030005c04a07a44e0046015417608025400c00b1034a400b5400071038403a9120782122098030003010010758054501400c5e00300e1264010744031a8101d0349800d08140a030f0341d0f8410050510103c1505590b82005843e0000c82250440313440c40342c1a1121440c040d10060345200d130302500021005090751141c80c050b040158010000d08016031038400c01403c17500850300c101e010740315660110f050031501344116011918280c2d2a00700314141a011711015040c006140d03074900200e14404240104641d1001e010b400d00c5c0d0307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 329585152 1250 329583902 329583931
    0x60f060203130605040503060612033006060a0807030c02030418020d06140a03060f020405040c020a03030c0203030f04111f03020d1104050d1202070b07150c0e0f0103150905 76
    0x4400c02c0d01500a610503018407408200410164501042047d8041c0046481c144146d00380400ea600718810301c140000c10310842d8400d8900c1c19200d41501480c905031040c0320312296503000034003800d8880c80e5071308000f00b140000040c0c6010700c43d800c201e95118103403041d6400e1941d103d0703101e020b9171300b6684844400c3d9000700e0110820301c030b107100b25001000c2802d09407055200d50750104102174001d00014260603224001c1c4089410107804880080030050410007008c20070600094450100c8541180007a083c11a80c55480b80300005680c095a040249042280c48a945056030b04d00d000302400e0304070002442e041a00c102002c000c11030403a464402694401e41201d146045450001050000d02014041800140c0b42c441814000d690700c60b0351254610107181c4260714240722035101e48400d04000512030200b003880c0d0800401c003074580905002601a03100d09403a0340c08083c109507008a480c85600d9610740c400d4002000c050b89490032031051a03110075601d0140d03441214500a61210b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 329586402 1250 329585152 329585167
    0xc060f09030609010b100509010c0507060807080a06050f01081f090e1608070605090a0806091006170a2009160207050a030b0103060504060e030313121103041503060f060203 76
    0x340034256210001c84000c0103005c018030b000905036000e010f101420040f0229025020b0b07401070052805031900001100d10443d924440113000207002c40340803000800002c0400d013070341820301400c025903030000c0c990642c3d20b20703100044908000041c03808001c0a10045030040d089040c0480402a0071103d2003c10020b8046101c40c0c6840f82011100b400240440b00402845501107401010746440740740c06591216031000140303001340c1540242d4464001c02041c81104600068103400c00e42e07100030b013480320946c0c440c0e20001c01c03581c0340c000c2c2139650002c92070480050f0440c00761400f1030400d00b2280141905810121702d40140484030010a40845d002d04a10700750104440c03002070004480c03e00340c036412340d0703200011703807406210041001340c807513000ca410061503802c41030421240b04100e80d00e91400c0c0d1046050302c0d0030381078140c5003ca901e00740b2503044c6104082a5080443e070030011031a040c580000b4400100240e00e0042c200341d038512010503e07811024180e801400203600642d241c100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 329587652 1250 329586402 329586409
    0x603100509070f090513060803130315020f0a080c0d1103040611030112200d0602030a11090d021c051609050601080103030c0201050c0a0605180c0405040803180c060f09 74
    0x181070a002e202c12801880961540480c1c10130035200140e45101a0340e0f0031680e00f0b000ba104540088101c0e000210f0112102c0180780c11500450f40940312005041d40d08030810301c00c81c4601c070345142e08100c0400040d032038035001d2030003207070007103184c00e030030340c601100f542c0c0b0441154481c0702541480341c0004103000c1400711501400c1c1c414514001c0652865141c0301003160381e28090344004140b80812542d4801c1100260ba201c0c04084003d003454481ca401072a226000354000c948a05440345030029481e8501c95100980300500f07009403c450005409808100040c1c1c8100d0560004984005801c00011014003000ba0800018a40305e04210b05182080e420303101c00070040d80c104001c40c1700400c0803d40c001c4054880980a007050b5543c0d011004e095820400c2510740a40450b0400b000d0040b0f03003608032131445c10b550703c10b42075a011000d070008020aa0f6800d4402514100060000c1000031600034000a50460041c08490403486924080742203500401940b40e030001d00890351840504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 329588902 1250 329587652 329587669
    0x1501140d0b040e010c09061103040e010b0c100c0509060d2003040b0a090b0a1d0d02160b0306060304230a0804050405070c0506180118050c03070e1b090f06031005 71
    0x70000000d02105c410000000c084c404244251010000440b0f010fa02c0c08a060081381d0290060080440040d80c503200d40340c2c010391000001010718450f94103130300343d20b045900c1806564034482da502841c20001008010480e0051403034610640c0d650310030082d4008824079640c00a411842c50780c1d03100d1030035080000060b240141001d14a50814001000207100c905480380d00c000b40000c001a4000700a4003065020003e9013130003510b00c100c000161802e40c00042d07403201031219400c070340c1d0895210b40c25101c01d13003c155801034101400748045400601c94401a01100300030740c000642490003005400d05d4220305980644682e00009024401400e0900a1651010003401d0000b0032000503600d00740c0d510707402171032100d0400302c1d5030b9034281903042900310f25180240c10005461a4080f8240f440c3c861091801a40c403038483c44400058880e02003402c18072034031030760381d440e00f8220030903140549950120302000e611054420512901c0d548840c05140035a580c5003032003420900b090244aa0700 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 329590152 1250 329588902 329588921
    0xf03030b0604080d0503040804212a0b0904020c06010e061801080c0904030e0d0305121003020102030d0b1302040815010911041707030204021902100902091501140d0b04 74
    0x148402c220601c46880c000802003002d400f076151041c0e0701e6a640c2054002c034000d980010000700a09072200d03038002d4050404088681c0246195001c400f812070308043c000120715550500c1b16040401080b00d262000d028026100300038201614080782c4520700350810400340c00c00c1113100340500074400c3c1e90600404615a240c0c2c0324807004555414440d82c2959440d00b408444e02c40d10302c420001d0205407003401504e01c00fa00192030b8006051341d030329020b05250040010201c0b0314082e40d00007803104c1c400c080710004894040c0c0140d4905002206543c0241c042480d125400a214000d046610070161000703000400d0a5005030401009000c03801315051010391140f52420700b40303450100f100ca440720031942100d0125803407220210682200c0390412100d41d00195200d4408110680c140701c003046851000d0105a094030440c03034136001500c044070741c1e0300c8020b500f00b10710303100140100460700b90340d4040c42014142140c0b00f600305440c041603a400700ca541c0070010740310308105d1682d050502403038505 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 329591402 1250 329590152 329590159
    0xc050109050108010e060f0a06030c03050a1109010f09080d17060901030206040b09150c0c011e080a0f0f0c0324030803040f0206070c030f11030609100b011205040f03030b 75
    0x1d00d0503000810600c41806851035030200140820210307615101a14540080034002c40d00301a91440c010300100034580083d000300e800d000000d15071800c14803135003a101e25984102c2c1d0400011200444280805a40020911855140c0400c0300d99081200c0c401c3d441285d81c2c0c0c242c065809440070110004060300e071034042c4c04400010301c01a642c442c01d41d002d5428216040e5102c84410380098040042e010042182040c0003404c01c0003000c0104694183ca0741c00e0322410800109003001004084070110100d0000c4c270031602103244c03141e442c0c00092000100800105040c40444a800c04403942c1c81108400300c0d50711403100c03a98980c6c640300c008010105042a688075803450711100002d1200510082a000310700140307000f15500c00e0b090f07510b440d0f02b00b042010495202d2a08000200684000359890304011040f4525407a00042d941e2040c24810050103000e0b4600385c006001d05502c001c4203042c0301c8090394051114070340c1d104151085000320008500c085450602908035490401810701 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 329592652 1250 329591402 329591417
    0x608030a021f0f091b170309010302070606030b090a0501060918020907140d0c080c0901021c0e10050310050d2006090402161203052403070801050709030c0501 70
    0x2500d8000c034400380c08041400c5028001408241d41d0002440314000c100260392130154210188485203952005580e001403c250129407102c1110b40c440d10492008031840c0d0007004540d11a502c80e4000c0c1a4140c4180c2c0c0119240b61690b803458246031040b528030300150312482c2030100b842424000c0f440146138200c002c100700014890400d00c144007110f0043d0240141c1000700300810310400c8075a4511590020b072035280c0a42e03c0d0001b01810210403c480004c0c05440810552040715040b01c4464005130003c10205428040c58a100387c9020414018050907680f101066200d01c80e406198805036602d07a907a900d0f01c0c03001107039241d040ba0011406481d50101da800003c1103801c8440d10380c12048540d01500b403801c0001080d42c407404400a4015001003418503543c4544007542590502c50340e031519100f201e103c01102180c00880702005520442900c0540c54840c000c0010008240038050340c102c0d40d03c40030350304c1c02c1d00d80a84902d8005110000104240403007035072944041d0a0074a0030a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 329593902 1250 329592652 329592667
    0x3030c050d08150904050f2b03060506041403100f02121008031e0d110403021008040804121b030b06090f04210c0c06120f14070f180810060803 63
    0x11821240f0321006405125081c000c602440000c224000d0b03d080900c0480b00e007011038000d9040101e51003414140400c3c902103c12030214000c0c09000141d91000e00310300d040928012501c001040794040c00c5805010358442c078100c40e40203001e9003440c3d4440070009a07a0b0340004001c1a607203007000308125045010306100b4440540c012080340c04210480c0491380321600d4102d140c030420302c2500e4000014614140700c0b807034005403502c090403c0f240211040c111040c40c8200179502001300300c40041051904200c00e01030050004942d60805001c9c01c1021161000c1003070b820301c46000c6800540b9426100010002c0701e20740b5140482d40321310040e40c503030030354181650b40107060f030301413804881c0d45c000b07100e00d8003480ca104d025100030341908046d600098607a601005007807c90301c0c030031568110303003050780643c05100c1d1800340c8490f843c01c59403415200e54801c1001c0780c04010403105641000b4a42c80e240d10b039241d1080e0480094024440034200c00444003443e6800c03079a1650000040b86c01c1440000f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 329595152 1250 329593902 329593921
    0xa1110030e0d050c070f0f17010519051f0807080613110103110702180f060a060905060a090e0414010c0f231920031201091109060403030c050d08 64
    0x140c400e1020b82c10581d84816881c2c41850405505800a8000c81086400041d07000301d0440c40400b1111001c0800042039109642282a510102c501d42d4034117002e50824120504143d12580e440f9109058000c6200400004068100c41c2903100403100e9000c42c0044c041c5a2050040c1500714400c040381030b62150081d515214100c4014482c0d40c18150744200702c0042c40a0003045445155004143c00303074072440c1480d0040092016242c010403040824002001400c1a501c044103403100ca4948900036441c003c00c000035540014540d0042014038ec0b0005400358050580500552041070341c1103c05100800d0300f03084440100012080104403860300d16540e42001d0294440c0f0010329080c0d00e046000700400e101441501015090040c9942c103c40ca41c1717911480480035580c10160300c0307102d5403d10026990301d0141c0892250b40703450100040140c401742e036100e02c01f501000e182c014200801760740002c02d203402550042d00821202411141004010b201d2041521154240010a030030b005424 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 329596402 1250 329595152 329595163
    0x306021306030c09120309030b16080f060607060b041104080604050c150a03051e01080f0705090705030601050a091e06230d020c031902031b1216020609030a1110030e 73
    0x82c4000c081034543c00406047c450a1100041c54000b00d0040a5081c84d4401c0c1005c800d4980d0b4030000202c0300004106921034450b941030007028000c001034200078040c0c4035031008004858140354030641c0c0f40e2849109150080260004003603e40103409071b40380c542025030821000000c0c441c4519844603840d5000c0d8070132810b51340060f0103480c0010b07440c0d83d00e0702d8950782800c070000112031034096203000080207038002480310b000d03144900c04d403400300e5039442c00e00510300700541d204804a00240300041e040d512900141603151070074584500060b544481d01c8034100d110318a40045440525404d01c240c94100001020b02d085502c08400f00200d0b40c1c10180d0702d401402a20a0326540024800d00c0c055410000d0392110b04018220603110349040b040a5640d601140c1988a850a10b001207040b800010620180720a000c0601d10b15140010480740e08000ca11801268001405e0041c1c20260b10204503000410784a00365495844400c041080a01c510390a011020913082001391040c102c0c02062 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 329597652 1250 329596402 329596409
    0xf05101e05040201033c020c030301061b060e0c01110a0b190603080d1b0c03140a0507060c11100608100b150a050d15030b040320070306021306030c09 66
    0x14000707441c1d11503100490140c1101c890a1808851104411003880080e240710a042c42d04202248411103408002d002640a800500e5060b504217000401c0b06d24002c0402d40d00c080f00100c400000945650303030f03002c00c442881179001ca46a2107001d00c5005960000000595822030f0b0005025480c1d50341c0d80c10b140c08100402d01010b11201100f4260b105005407c143d0145501008054569482c100307408000c0c091040e07822008416445c8100203680194114104d090f0995035600341c90b803100c1c4035441d565020014400c10400f08000d00c1e0003050240c070800d0041c920320b40c1c0700a441507040100a19148001d01c40350515450000c0800c02140001403462001c0c0c0b1403100800c0384403007500010203550141d145100b4040d0000f6401d10a41c0d4080c00424045203880380030022035800c1d8050b04801c403020301004180e00440b00104000c60700508440d031910f01d0305a5010a000b0410710518241000e540c0203d8486030042101c00c8003260714002d440140540e4607042102844440c4d00130003a0b030310f030311 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 329598902 1250 329597652 329597711
    0x31809042321030406051015110c060d0903020c0a0803040e0408070c06020a0c080a030e090a0e0d0f0206090609071802040b03010605032212031d0a0f0510 68
    0x141103103040708007801042a00141c0124151001041091410a0b40d20880b0b044800c50f01d8600020b800400c10006030050340d0001d10b5408111a421074281c40303000f0300c0004890b0a1288800c0d010080d500d12001f8400403140076004030f004805858007902d080c0c0190390852041c401c800050101240c008262011030303141040362032a036262030030001207621030000c1c0074010301880388000c00c407141c00260080c50b0921415030303181c0c0307103a58030b251540701e40d0030b034000800141854001c02c0881c0380c0203c00b1504a2032008001034200d81c0c000501d45000e043c504080040b030481041007802d1501070150030390254a24001d002c8a00d09070501d1521984140500e4403400c01c41c003800d08580030541c0c1660080d284039000d062b583c0d40c4410f406003194001302c0d6543d010103041d2108500e524170340c100344440564002c0c48549100031010301900134200000b84d0754a1511108403c2010300800c203c0d072130303909003e0f2a44150114203403c207241401e0040100802050a250180c240d01844102d89211031094a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 329600152 1250 329598902 329598953
    0x1120b0d050105010306021909140f01110f0d110606182508010f051002061902070804030f050f0a08030720010203100608010503070b1b0304051203180904 68
    0x1600000c040a85600000e40950b1900d40003000300640c80d40100400010120b0052100c003084074102d50240c5103018880502e1440ca04400c0c050811546c10f500f6020141801110072600040305440c00b6255580380310356070300c94130484007010b41198800e401d15008502426851525002090208000305055441c2c444140000713400444108515000e851030303480b80503229250707070030014030120080c003490701142919600010545400308910082251640240c155952002c2041d40800b0003201c00e90000d68007040110001100e040080c000307940300b031940e044880c20a00300146040741024460449911500c0e1760000301c2d1269080d694400e0702442c02c00c081c0603902d0209055402200c010315032a600210078041d4040c1c880d03500d001900c210342c0d01d0310116a620410560740c2c0050744618540014104016144101c99044180b015201c060459261599a10129116100013403c1034055080443c110268050b80390b09403100083c200c95034100c034140b584665040c41c01e101c0c9246001c42c900c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 329601402 1250 329600152 329600171
    0x40b12120d0e03070f02090112030e1003021908010f0905070207031b26060a021e130302060403140c03070e0a1d100218150f030406091509060513020112 67
    0x102d4006400c2c008034542a6915038540d0f00c0c002c1c4481403070345000c900c642d00c000700101b40c06074401840149103406070755240250060005111a80d105c5040c514101502007050300b040340d0740c3d07201803090b81c2d030580e507000308a614050320340c0710b02511038010a6042d810201880310382c5a0006140d01038903008900c0c42043e43e010390701e03400c001e01264009030ba40540c0494030000120040a00d01480c01240150307240345e96501c80003000c920540200e00f143c0e003541d4081c0050f0510513400340044960348401643e1660702c9800240f07498102d0f078021960200001c1e110009100b0900c445842484180c0080c10317601d0910b041041e81c00f40c02001a48101e1b6100c03150309840c442c100ca42c0e0001c04144c0306890600504040640c06940480c0c0b04600d001521444c0614506144141d140d0721070642001c40d0400c403403840455415031002c1c1c02660b5554031503544002198040001c0e60001c01c45c0701d800200c518040c5400010b464008244405080344031440c003015076007200b240079841580f0140007400404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 329602652 1250 329601402 329601427
    0x70b1905120106080103142e09060f020310090b061804021b0c03010c0206061309080c0f0a030e1008010306020d1113050103060e01081218060a030605040b1212 70
    0x5000350301c1201d141c40100000d21039030071900d00c030b050321f000304080e031800022540760301c0e41d5042e108039620b09685c80481c40303008030030b46c01d20003181c04100702d1005c6a69061a1112419240c44c019105c43c2164000280b041100d401c016820003400004001c2c1700c1d800010001400d1030254181d014003251621010000725900d45c5d0456801c401c05451102c03484242101d0283d6a0742c0b258482c1e4001d601c1e03c1c0a43c0ca4881c00040c0c1c2510a00f4000d020000000312000400050048000101c0761942c00b408684244801840786441d030b02c140c100201401034450030018011601941454020b008100144031415480440c281c152600705001503940c01d8006443d800400c0342141c2c0081c91070001c21110b1200d5142241c100c200c8400f40e03000d00200f03881d07021041100a0a1140610340c0c0e20403c6000030003905100a8103120f501d5824200d9000744640200320300c0c1c4e004401e0700f030000369141c00c28000c0389014820b008511500ba944440090302c018006a83c40c03828010840d40840040340e28000d850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 329603902 1250 329602652 329602657
    0x207020109080f06040204060f03150207050c090106020c031209010e012a0f02030c0a0e0a09031412070908030405100302070611120403080a27050708030415090503070b1905 76
    0x78150b0126202e140d680c0600d00d07214074090318100d02c2681481c10009070484000c0c110420f4a41040d214032001c0d222080e600000c0d480316a044416008044200e0a160369400c0c0307090003080d10b81c01403d244c0322420201800d040c00000d02c0040070005110007509a41d000584050300c4900382403019945d1041c0a50b00552001c4030701c0d940741c88203d40c0d81841000720b1034249502d0360348254200d5003503440400401c80c1d108a5030281c0b02821201c00300140d4202036582000003168082e0070540f89248101a0012040d4481100e407400c4511950500a070b0302e60280d0420010101600514181070401b000100c0d41081032562604154001c42c0f0b003800d2000907800100300700d0111020360340c0c4400300c45007103410460803076060780400c080300c00054000da00360054201110040b246180990016905d0207802c20050303406803a0780c401c0034004100d0900400080010b000c1d107843c503480a4074500c0c00240003401d5a048240203801000c01045000490070588110621030349409a04249a402c21034160 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 329605152 1250 329603902 329603909
    0x314060c0a0c141e0c0f0a06140711090f060111120307050a110712050708060103151a031006080d0203070b070503130609030504030213140f060301020d02071211070f06030207020109 80
    0x104c82003401200f5001e0008911007104030544200e5140c40400d003c01c051002c0c1c1e8443d03040420440c202c85403922000c000101a00c7e0720a07100481ca50300000c0115044420031241441007210360b40501905607005040c005013400090001c1c00d41e548407160f01d807407a0002814020501502091a41301c0d03600505580c030b5164680001c07556665500e10003103c0e2007007240070540b810b020351034022801d410003007121416240c114004220039991040108010405101640d0410040800080d010740d03040c4400504100450b10118001e800c00001c41d0408800c11021025540108000c80009400300b16141d0f000c02c0600b0015100e58071000315080c40c00c4400d00003880d251404088400b09034000c0c025105990080d01c1c0800c8511180066a04550401c00c00700d1018800b00b000a442c100c000310442c0d4030440190025042c05244004401a138001006c01c658901400c0380038404c2560026032040510b40b00f600a1000c0d80c0340c410030b9200401940030700c20806130000b41a1040d64040c14006000717 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 329606402 1250 329605152 329605183
    0x20304090908030109110a021b01030603020301140933040c0b0c3007020d0302160b1c02030f01060c03020c1f0e24071b0314060c0a0c14 60
    0x2001c1203403418480b158003d000e48090f6070720f09260046105002d600380c0b20310700b09540040491801880400c0401001411403030304040e1038110110060303d0078061184048040391114200e41806c00703c00c0c1c1800071741e99100d4090250000b042c200e140001c40f25400038080908000310302d80315401d1085000075290058111440c1c00100501900d000003880140c03101103035140c0649290b000c920100c0004001900c00c88044280103035130251402c0b52484e05160312038011606102007130220710365007407141d0340701ca80c8041d004150450364403196500d01003103c0700b000c4214510720b40301841d015040018028041007204561a0300201402040044406440180051a030300042a14614019460b207110780000d4a9100f06c00980d04260381c2074445070b04060300d44003000c0daa8007204d01d403c1e0850300e01034440c25101e920380e4500d04994100100503500401c000c00f0840c003041c41e141d1500c00e028202d803c80a8040200000c1c1e194400d001105890b0301007166902460090142e07854845004110f4030b5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 329607652 1250 329606402 329606411
    0x80708070302061b04090f060806010609080606061201180b06131d04051e01061502030309151009020a110f0105070f020f10020a12020408030306090c1806090102030409 74
    0x600220801800358a480307903080340c145540d1a402000344003031102c00075106800900041c46410615000160a01001600007940555540d042031800100382c0c0480c003c251010020300c5803a038248072603076002d1000e07aa82490200035100000701d40310141b00c1c3c100100e42143c1559102482c070340002e0b42402004154a80b90300419500030091102482640c0d85c0001400c18402d91400c903000d51b62082d43c0050140503071a402d814071101a41c0510b000c095107559801d07010401c00b40d01c41000c81046001d40c029516483c0c002c1d0785501c2c0100303c01d03008007585528000c00407402d60118000040d150640400350f1607040454068070604480d01c2201303803c0c0160000307e48001c0c0c0561107540b2412035641c5480c0c0d01c11050000740e0b215220a0f030440403680004d000c203d8840780503001016402128605034454a03c003110f004c080b03800a800c140d4140d0400070500c03400d440d03d502c600b50031640c4011820b142c1220b404001d101c921b207007405c940c05044041081013440e0f000b801a02c00400c0801418007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 329608902 1250 329607652 329607667
    0x1b02010f090e070509040506010305070f030b0109080a0f060b06031009020d0f0203040609060605190e06190308040503010f1b08060a0f1805090a0b070c0c03140307061a01170a0908 79
    0x340035170420080180101c1ca0540050000d601c24042c05010f6086500c0c0c0400c1140030903802c4000d0540c040b801414400c2000c8009008941004003007002030040042d251090040c1c90881d00755159400030300e00c40d803028414000c48410040c1e12208550b400d010059070f500080902101801c10010300701403680c808003c010a100141c2c105201082c454403042002903115020070131090b20f001c0002c0340882240105200100d102891036411181c01000f010041410744409222503104c0e0b001142d0003030b0003043c01c11103400c00740602c035440c4089000500c000c8100d206060f002170700a030710140401c0200800b00c0c549494094403080609408003500d0074085d1144050b05100c00703141c0170148014640000214542c0c0c0c0864015081a03002c0c0c46100f603502c42080868200b103041c201a58081481170b000000030748984001d45807103190001664491101c3d0500070212a0510911144080040340c00481c036a440021108044051380b411581912410407100052403d8800145049400100c15 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 329610152 1250 329608902 329608907
    0x9090911030c0301060605180d0204092009040f033e070506191101110d0b030c121e03070512070b0c04050612070e0a03031e1b02010f090e07 62
    0x30100c00d14141d0403225820002410b00d03088460728070512001a80c24002c0d025010b0440b0041450740000508601c0803041640014089a2001400300c840340c440c8035600b90344480170501e20058210440340140301d8613007500e40c142d00440c3c209005080042c114007114078100e0801681c954500c210240d42ca80f903500d1414452503410005446d2498420514001058070303103c000c40704d004042c695400c42d41c039a1401d0a03140601408410b0007203548940820180e003032014003929681c904035201041c400d203c0350038981425500c0d82d0090240e1140c1070802c44071200002c03890048214865108450070900380d00c94154000d45030024414052040241001c0c54400301600310b0340d0280307900103413503120114410880c0c410380c4549074020300107200107044010044419540302115060000140c01702c140001d00510160308101c01085a030754045803d98103080c00c1c214101c00380e0600c02c80203500400500500004848000d0411220486400b146446003040c0001081007003030000c140d09102102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 329611402 1250 329610152 329610173
    0x1b06030204060e030309030d0f0210050f0103141b151c050f0c040f0306090f02130f0c02010b0102150604090c12030e06070308040f1112060604180804090507090909 72
    0x40c00001a00601100c00611300401116900c000c0200100f4185014003819540c006004aa86042d402001c030300d210380520034000c0610404032520650000e41c1189409441c0300302080c4040d40c0b07a8080c1c0c09000e403001c541c4510283c00c0b0401c8544820600f40d0040c0d0501ca4850783d0079641c40034840b0305000c4a0101a074022a000b0110741d402034503181d40ba842c1c40402401a031040c9610003490020800220303d0390ba020408d29400760003200c5006680b5008610401d01c038411103411240c1d901e890f41e214105a01ca0350381c0143d064030003070004d00c03e5940002c0d542d404800c05204030542e04404548d2550700c5a0241c02c02c554098080391440d80d80380d1034031b0340e5095801801c1e4085174000180310b6103440e00008a40c41c0030b42c9a290510306481d01d0701c0d00c840c60000c070314044500b00d84070b2a08215550f1548644a402820000240a0381c50008103200070f952001000000783c242002140b00001d1a04040d502600d0391b880001500d55125a8112444170740f40d40858012441d10620340b0a02410740388 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 329612652 1250 329611402 329611409
    0xa17010b0a120209041518030507020f120c01031d0609060f07050316051605030c03221d0705280305070810050d080c010c0903140307020f040203041b06030204 70
    0x180300e00070300c2d61400691091407003a20001d61240c1d84400040010b1007041c031040040f074a031200001c0910494081c025018290003007030300400c402149160840c60b00047c2c0380301340c0600703940f000100300d041c040c0680d852100018581c103043e2942c10591000401203c510401d04102045881d64188003078031a03292103064841100d0a0160360003d08028001c804aa000307220007405c40c03411614417a805c4840f5008203080a5810155000d03500c046a401c00150011500c0d80020b95074072241401c00340d41510301e400c98003c40341c500000401010b401c20400300c0d0b0701640306080c0081c0b5684d5040441e26882003610340107409000039001000740041404480d80d123007985d2410800d40d25414022f87e60500c0c00c51b1256080440000144040d00f0500482c4400c54410102d030740c1032000708480e080c03d5a454810031000940e408008105000c10b50025a6444001038087c5107030540d41c2d0040f80c030900341d0110b054040d64000011400b00040402581e058034220104080000d0301e425005010754450310 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 329613902 1250 329612652 329612659
    0x14091516120c020a06080c090315060307060201060e220515160302131a130e04050706390227100509040b07050910030c03060906050105030a0b0a17010b 67
    0x408240346140078442d001d4441e03400920440c44513140070821640c1c81e50040940c4583e5030180000d0704140c4040019203955020340103204078900e058802c1c5403400713502d07510400031603041c0341c41000400342081540750466545600581032806140541d04c00c140c003010014018414061490b0200e10300302d21b0701d4040c6490a008000746240c4940482c00c1e40100180002084130404007007240d0011402ca072041e040068411310309180c5c80a0b85842c08101e264411a0600d00c4202008100041444610040c11050074003514140f01c20174044040024144400d40070414a81105000c00c04e520424403043d6000f06843d419a80034941944170001949044040c6601c60011412840f41040c0b454141c07503000c2c241e40c01a50b03e41d2691100c0c10300240900052050801c005101d5454110084640768a9134801080c0c24061034401801c0781c1182d8802c914092504d00180401c1c0c0e40202201e0b00583d02c04008200604050300088141103164815120034100d0000c468401c0da06400010320320000720f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 329615152 1250 329613902 329613923
    0x2030a1109090f0a0b061b0f1c0e031c0507031722020402070b0903070b070503010b1602360a0b1503070e03070e04050c1014091516 58
    0x140100240360003000c040c07903404480c020001d000c030034000000584c808070283c4046490800c1101043c0c907030303000c07039114042100d00300c0b2400801d0030200130407070743c0d80201070041501c1c495100103a5803c84220600504000da20024080c45070350410043e02c40070030860740c408002c055050060000c0d406440c00300c001c54030b5640040341030344001000c180310b482c072120032017107088613008900604401c1d00c4049a115070300381311071008162080400b0b4441c6020800944e81c1da601403c0501e02c841c401414030042160030401030060003003800503501407504601014081402d1403000892200100d40c0300c000d40c0441212050600002c4580a030822030440e4417141039445003a180c0003901e45501d289030300701c201d00d52810030b540c03030810003182e000c0c1c01482d00c035041c200a040000d05000c1283c2c0002140c8078210180001e010341070042c004d42039402c030351441c01080301c180094095115200b01c44c0600d0804a03003000c05440360b5001610b54182c8005807607580c19944500d2070f460119010507a481c6620303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 329616402 1250 329615152 329615171
    0x1150501020c191505040e010e061f020a02012001050a0f0b0a0f05090402031614010905030a2402120907080606030a0b060d060902030a030c0302010c210e19030302030a 74
    0x840c0300a009101803e4000c0f80fa82016180100c4220b546030400030030504205c00150440f44c1c110300750203040c04a280440c5403c043d401c00c4001c000d1113441100c081203209660341220740008004107000c3c1c1c2800c10700045440d400c030a081d0034541d0b40c510f250950819003044000c5805034040c41c40c0e0143e0f41e900700310100303c0005004101c030b0030f8001c0a2401c488103800f030001c0d107011226a0b03170191000b000c680001810403411125501b0a9006500d908060036601c9819038102d082440680416001000c04c00401d403030721104618080c00034010b40820402802e80d031000c54046030076601864204200d03604000f032541e07940f4240c0d440b80300914041d40d0082041850042103502c075990704000e80a00c252506030030815041a07003a41100c902d5554615440180c40501c07011007200e00030340b1100042621814080e00b07488844502c0000c00400300c0c00c0014071303800080e84191b070305001500001d4044c0e003807524034944a00314170304008811391010000201541600114494917104000b40408502d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 329617652 1250 329616402 329616409
    0x10271b0f090f0e01050904020d080a09032f010f030f09030203040302030f0d0c11060423040605060307120207060b0603010b040306061202012c040e07090e061005010f050c01150501020c 81
    0x580d010f110015404400100142d1412041d05904140028000c00b048070855803100440c1e44112940c0c0f021070542401002444101c0301d924034540c48888900d02c1c1d401e201c18041c3d22890341e40314458181308090a020070300d0f910030303030210788404004030007003000124900b0065525002031104a00c40e10400c1d61010003000c001c5142c1d45220780f40c0c0c40303250001c00720303039907242c424504000a140c1140040c48002000121040040024100c49421000700b2450740c051100b45c5a0980019000b20000c10500401030740c041c4100711010070301000143ca805892405c0b001801300c01c00c101da0300c0000030001040c00c1114100a004503417017994100035180d130341d4100d100a06054680680498180e00003001903804406420200c04040c2c00c1903002c2d84901c0b40040d04a032020a42c000341a0720540040c80b110449100700400c402c0c09100a003041d140060b03a07a00120303164007890f410000f0140c0101d001c2809072041c1c0c0d03e80e10304603000340108908601c0303036200d0408070f20486c1d00503c600d54480c070142c01d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 329618902 1250 329617652 329617679
    0x403030203042a03230d140d060906091401060516080904020d05060118060f11010e070b09030f01060320010912050a1e0b01090203060303041a0a020610271b0f09 71
    0x81c1030300060300001c2c002c80c0d002c0c2d0703c1c8802e07d014601715110400400304a030503c2e01c0364001170000c2c1403000480906003000c0301c003101da203201c554907103101503070050101c9078008054400caa60240b0701800580058034020f961170040240303840c2c201b400403414440c1500d081c1c004603c05e113002c0e82c0b070040c4e05681001000002180f482008041a103c0700580302443c4604200d003000310010340007150311070701e2040d00e82c902040b5600c05404c902c004200c070345151409004000550030800001d003c05811f60315616002c426800b0070b00300c8540000e03c1400142d000d110382d40700078400c0f406200c0400c4d00504242d511400340c8001259403908804802c0c078003400c10f020038041e82e60813000400ca16824801e001c4001d51018140d0b40c1e1500c4203000008030400080c5031468001c014103009a01c4070840d400107460020007030021040310a04a40c148101c15003c0703240c01d207142c0300848241c500d580e400207c000921084442c0400005802140c180b8503070000301c10282c203040781c1e48803841140d55454a044d02c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 329620152 1250 329618902 329618963
    0x30414060408040e04020d051c0306090c0203040b180307170601060c111905060d140703020901021f27140303100608041401051e0c04030305030403030203042a03 71
    0x500d003804107202e03641c10300c9400c070b9100784064030f4201f0082460315218070b04004152940461302c4500c24005405616002d050014081d00390144404010080003a4a0b800349000701320356040b0105102603600301184d40c0035001c21000e004c2c0d98602c6c1d244c00d8096102110284029140d2166800008409100300c4503104040e0300f0203210704480c6205400c10146001d83c40621040707103c9100042055078602008190b0304c0c074402c10004e091001d06181601c0703058018a4013061620600c5050002e907004038079401610100c4004404450070354200d4402406445010407044030f08950000480b1a0400749000d0180111b21840310b40c4a00810b6070354a100c111060750045070410b0f01084003070301a40380207030010300c01e41401e9242005102541c2c2100d0045502c01f075581003203807840099461002805070000300020030f071803a241c02c540303002d0700307520010308010308141c0d0000004007803000601420683c9900010706411012107618204c43c241d440d804203840d42c046055501d145650300440680c41c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 329621402 1250 329620152 329620163
    0x60e0c030103150905030f1c0e0705060703120f06060201151404020c030f030c09150309151801141009050105091302030f060a051504020c1513050f030304140604 71
    0x85030b0071075a03141401c000d20305520034803940392081140003030014405040441d04200000e5111403080312049086401091100046464004a0902041c0100d01c803803e50340e00b0748100350303680c030319103400c030b0751031b15000c0041c54940d10740104140c6403030b07182c3c0003541111b026a00038403105000c982c20140500e000d00c100300c81d4200c0011b408000d4182070f000380c036008d0300c0d44c02500d040a40460814560382e10440710500c83c21000a6255001d251015510b03440010a40d811410342c40c16450041d030b1540c0d49000150522000c80014901c1c910002c100d8104100040082c0228000682c0503c0c03000c80c11ba44150380000310080c00f01e01c043c1c0500ca658101c2d6801020307030360a62111490b42400000703440e0280c1e01400b540b0511010076070100b1106008409001c400160f030326002c1c0c42c10350002d4800404922441c01004514003087d80081c030001e00c41c1301c50003c02500d44401001c00c4403d400702100400e607011f48600407100d660007002035441540203074142c902c06600c0c00d40d03003502c903401214004c08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 329622652 1250 329621402 329621407
    0x60b04060327060b04021309090b1e04030513080a050f010f0e0709020f090627010c050c1207150215070e0607170403020d080304110604050a030305030915070f03060e0c 74
    0x11a0990300f020b01c141002810041c030780600b824034071f08a104c2a801902141d42c45600f841c007001a40301c031051b48108422204000c006102440041e00d500141015007000404a000e40c6500d9885200000a184400840fa0100410310340551200750254196015520b40384040c00002040e010b81024218110041c08500f414480090b0094200f1282059024800d101c40e5020307032982002400d000b01c01d1860385080b0818484c4004ca2214085429410011000d850380c1c00160300044542d18400111001110a542048010301c0d050041e442000d1400c031404100d40101c0d004241081d0100c2c00000c604401e5494107002d6541003c200c0100b60440010002107010400d49521500e491182e003c0d40e07840e10303950360002000d1203103440701510070810000502c402c02903040c1c1e0411035001e080c0d900c10b050528003c00180805403e12019050050002c0010705082050003d600c01b0821203217080f4032410424401081900c0ba2103900003c05c1c03a00d50040395078800140e40c1c510407001c5414891 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 329623902 1250 329622652 329622731
    0x1150320040909050c0d14060c0702060702042a03020901080f093414090604151401030902060a0f08090a15020c0c0d030f030b0f0f10050d060b040603 66
    0x3c064010056405006440c0d40c14095510940990710141c001c0d070220701402504070040f4107144020b085010360010801c8545c006883d400f0540b40c0c00340d011900014400c200622030881c01d0342011103940c0c007600f0280340e00b120310b4159001d40715141080c0d039200026039540f94507030303003413481580c20310344c103901002d0011321400300240403410a51004d002c01040340d8049003100007804075608000e001055441082e2042e0801100c010740c0300308115010b11000a0050b20356840700101c4c021960094604103040705070380d02a810060000b079000c1c0c00365548140101d80100844442c40c0c0040020f981c000c042811001c1c0000c00114403900403242801d4880b228002ca002540f2101254040d80070f0340000703020a648135180c0d00c0e402030180c1c81c2c2c40d075052007500001703048910302c8920602c24650030f5201d4446032210100165a0803080d02d00d910001180c01081d20640230300701650306540e0400740081a2800700704083c01c120754840c0c800f84000e4204a170703a51a451185016424442c86100d200d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 329625152 1250 329623902 329623919
    0x904020a020f2d0d0c140703020901030f0b061215040c170601050f06070804050d0602090307080d120209011b17041e0803030103020901060e180115032004 68
    0xc00d642a40350044620807000da81d0003038108a120500030004410b80760151441218482c41a4049620741c000340503101c644074005441040300e40b85c05000c00420140d40c80400c0710400005000e542c00600345406980e40346004039242c2c60102c03040307844244140200300340c1e003031071544d040c006651f4801514400101d81010b500d20a0004d1083e22000f100620000700e10004501d0700c0b050b00f00300e0f80608000d40c10322083c8040080304120039409003804000303040c041844071381581c0a070b440445820401c442a410450060b02500c100107a041c0200c0c4800070b03000318000f075550b8500200d034403943d441c0c11890351544224042c3c0003046001c21203280c0104550840d81124044140c851445852030340c10120301e110307071074003c0e81004010840e008107130115004e11403042e40040074043c0c002c514660541c0d011071484c070810720070380080c0141d00e01281c4460381c0c4d452002100b00000b10302c0170b102c1e40e9215004000320800385668000700341b6151059620f04001c00d4920801100d03020503524091401605 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 329626402 1250 329625152 329625157
    0x6040f1a070b04030c060501240305060d080c071503060e06091806011d1602030f030c0d1505130e0304050f01030603060e150703061202040e1005250c08090402 70
    0x11082200c420032110000810451016001d903020795915066008603150000c215181038100650304160007400611200b0640d540a0301801e00c3d150104e5591600c00204a892480346001460324402041000a40c00000340c813030f00300c4030304540a46100700744035000d41c100c4040e800f8440c000440e41000505a0030500c0702240c0002c9040219001654101c0d038803030401100f0381101e00044103601404031b00003240c9031240d40100c81c80c0002207402c060110040c0d0781e88a1940e18200ca0300f4080001222031810b40c00b0343d2460010410f05000b1000000503c0076880f50b14002c10340314600c003c40442e0f02081c54403500c5524500803008528040c100701c104191740c16410140c0e03040503200c220100004145000703005c070a401040040109800b000e5000481c0c1800030003080401d450105d08010254148603403140241d0141c0300010041c40301003096050602d04401701c45610700305414000a1545028004400b500303640d1451101d4008160448450111640285c14120240140800d03880d25600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 329627652 1250 329626402 329626439
    0x60f012414090414160201020c060402090912030403120522020103051f080109060506120604030c080f0a0e040b01021203041b081506010305010f120308040302010f0207050f0c06040f 80
    0x151a00301051600000d050340c540042440344c8a01d0001808050325001217050300d005400e000039401c01c0440c0050030b942e10070062020740309261400220b10074a406114074400750a401c49002c0d0380b45407074100908609101111781c0600c528000005a140b000b8041a1003034001c0011201c089640540046010f4440a02100542c0090407014102c43c1c2c00a41540010041e440010400031041c4c24030000300c030f40c01485140582400303400f402c156080410229030056240c18108800a007070f04090105000724800c220705c140300010311030302c155000f501c01c0c4d074005011542030119070100c200490b00d07100998001c0480850500124001841d9a40341540400d081526419156642c0c038500745401030500710040e004101905120301941d040c081c1a000d0105081c0d21141a03291a8070010300300c0c10540058108070701580420f04142c403e41040091444040040d5107600940c01d0154661031540c5800d0014400e107114008141010400d890865114022441c00d40b4684081c24086500050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 329628902 1250 329627652 329627687
    0x610030c0306080a060f11030108120a051c0e0709020f04170c030109080d050109110d0213051e01031d0616021212010e0a060b0901050c011409060f0124 67
    0x1040400e15201c00c00c00b20300078502884022802c0d038829074004088400210603411f9000741003005104001d8002a03242a60640c0b5040c999107200c000e00842c0e09020f254514410796401c0000a4220403494020100540300d07041502c56080c0c1d924402403ca02c14002c045082e550144000c002d080c1e136510000c0c07840e180d00c1050342c180080c0d0000013401c50746e40040484240c0720114000561500c036100702c6004d00009003080040c03842c5450203d580d4002c2e01705400c0d0941e000540455010110b407681070091101501c40103418019541c1a000741c800c03410385900003841c0103048031515280f41511301041d9407610140c2010f488549002408002d5804018154070421034103140ca2003a040003807100800407034001e4465410f1000803d00c0f034001038070504100742018000c1c00140100f40849525000c01d0030f01d03966070030706483c0d07150240649a140d034842c0b90a04040106120000c0389182c402d010205c01c4002036230b221025115201c004035440314440b44000b50f407142080c020201d10b4200701010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 329630152 1250 329628902 329628911
    0x625090b0712080709060914040e16060e0f09010e06010c080a0201060504060e0709140d05060411040b0a060504030615090213080c0a0e0406020306061b03040e0601080610030c03 78
    0x94105000c0d69001a00490300e54410b0b038202107407a640609400d030846420315218083c3c1d0700d0407400a10742d4002e40070304000b03035410b00e68030082503507558040103c0500781c0301603030121020842000c0340c0140301e12481c0b002c186501000755883c600304000722000f8030010721034031b1581d0a1164a44101c50018515410b01c00b82c41901004100d009000c1c2c001c441c819800410443d00380800d00098442e190b01c00c68500407140140a40c040d0003a07522410360b191031068810100c008000103443c1d0b8208800540345e405414140824021080c0302807503080c030b05a0b0144040caa59406004440d4110310402c40012014030040c00044d200f44c11482000a400c000d041e2420748660740141203910050f6521001030307250b581046101028407080300d0480c02220380d8000741e8501005041000b40080001780116070010004104d5500c005c1990f840610040c3c030003001881441019070750740d00038024103400180d08400107500b50b04c90701c9441e108107409420322150202000065029040c2c2c100100c2c10305454 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 329631402 1250 329630152 329630159
    0xc0304020d0c030f0c0e040b1302220204140f0a09051003170c0105090705030c0111010905030f0705010f1803030c0c080a17370204030213060e09062509 67
    0x4540c501e0000c0c2d40500c013040303100100703032619000c00080743d884140e026401c0010000441c82c020001a8840c54840b000003420840e0b2001a10000401d1070403440e841a05942e990011520380c040e00c19541054500648501c001c1e0810854502c0304442c9540900828428401d03440f541d00401d4000c0307000030580600c16105d41d0b50f0600d0b41d0345200d0103480d0700320225182e203040d0703070901071160070108040107003420f14101404252540c0d44880f03000d052000e03c02c1c0902802800b5409410201e0300710040d40e0702c91507011000380d0507510110080e079080d801c0519000031000d8a11a0100c1600c0031201c0e00800c0da81c9035002e401404a402c0c0d220180502c0c00f040c040443c455500518040c40c550362903c48040c00244030750300e0300340050400b088030041c280304005108100c051f05160ba01400301c22061022200001c44040e100d20b800082d081300c0e01980000b0110f84c070b40c114109851425240c0c81076651203202042d0303140c0781194008c100d002c20b40005e240720142c8016580c2e0459041c6400e0751420344 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 329632652 1250 329631402 329631413
    0x706230406050307021005091b031e0604020a090c0e0409020609090a050a0e06010803031305100921031a0603181209010912080d0c0c0515040215120c0304020d 70
    0x100740d0101c0007251000041010040e41030085600c081107141c42046039050020345542d80d040c0e002100c0c001b5152001440800d030b0b604001310b41c140050981008810004400b00c035032205800d8030102e000342c1b0321400110b43c0c09110f0084d01c0030303100c456a41ca444513051604203c054460288240d810910030001c2a60684070f1a000f1403007103082510201d01400c2c0307045544103d8110306074201042c2c21040041c0003828010044030b400400104601075401200d08005060400400042c000f8505c1c110b200c10812030782d0114094002000b01800c0c0901d1044031003030b02900c003840311714914480d0354120f100c2c1038640000950b0304825080206004a20981d80d52807510780480d4000508981c00b003500c030310640e44000c1050151001c2c9604a25100c0c5594031500107024610354140070329152061100c2c00b43c81041d80741616030f003000c11265211184000c074210070005580076030080d401c0c60911650b5590380030440d1a0208882247d09240d030b03c0c6801c0794000e80014000300d82c0030340081c2c900004204c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 329633902 1250 329632652 329632657
    0x70302040312090314120720030f1006061b030f020f0d1110090201051903150e1006050408070e0627010603050a09030e2701060f02070b0c070623 64
    0x84030340343c40c0e100ca0b04506240a2002d595078807a29590302110306210302070301110030785011542c4a02091070000480610011005000c6132880d01440b0300310309240a40e2001030a050494000e0034200600c0d522004202e4000c1d4014202002c1d0100100107040040d01c544881000300714030784180c611824204005904000117540780c030000928065640c0c001c04000c1c001800450103801c1d007003201c0e65080e40040c01c10300998821001001e0001000c543c014069081165651034030050307041b003a0f807904182d00c00e0144c00c4d039980c251003403c42d001150090080707041b2410703103c001c001084d0036443c0c00210800c09100401154000300081c4001d80312000c05030b0a403d81840c116080645903041c02c60040860744014020103031075060400380ca0219401c4001e96500c1e40c01a07038800582801d40850380409240080e0350281d51000500018115501c070006032241801c0e030382640c60303160762a003070f544d603500911824100c5600070900c204141802445410b600301981301e400c903154540030089906a4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 329635152 1250 329633902 329633933
    0xd020a0b0f0a0e0f220914030901110d0c0816020307030602120a060810020a030608190b0a06050d1203140403030606030e0303010812031801020a0201020904061e060e04090203160e0f04050c01080703020403 90
    0x40c0d0011271403405640c1c02884071150402260010480c405214074004c100c01e42c50800506072030400a8203a5002c03d00d01c0d007235008581c02504644049580389003900c0251301841d0002c0383c0410782d00110349102900c1c010581200c41820040448148141000000303610116102c01455030f190400980703c4001c0c4588094600007040151407407085042030302603801e009140e00121031601400340110303515001c220f220150040f150101c2c1c1c10b08808140c0027419161000d00b1285022402c00c001c150f8113030402e000390751040e6414440041c4000d0340039501e000a008902d044c1e04181d060515143c1844080c0d54401121841410f182e2440380b40d00e400c80e440840708000607500015116200c0c2031031b02503e0014081c0e0300ca00510742012a40b100d41c85203c41c080c80042204840c4500f213182d0f165003003000020380042c1950060002403000080e2003066100c1c0c1910b2200e0f60000034510004642514465500000070702251106d010044549480040508060550a00c400f0000c92101041312854 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 329636402 1250 329635152 329635193
    0x60d0312240306060b12070f030e010f090c080c01120b010c0f0803150a0503031215040608010b03010c020c011d03100203010320030304080c0d020a0b0f0a0e0f2209 72
    0xa940c02c50401105441c001d802803000e40d002040b4051101200c103000d203030702c03104a107041e03000001c0e003841c00c40c06004407405402c1c0c6582490110401d0303525961155480b00c0c0b15486552805944000c040d40310174042d00e0190200301320f840007541840c020b422415510782c0514040d80b00750496950f0303501c4181240d80c19154402d02000f004002c4201c1101540c400b07070101c903e0440d8500d4540065504e205440000f10040c8038000455621a401c14410803a4180100280441c81d1203880d214020541042d155211b5803c140c89801000e001189121401c0d2040c2d4030035012800061625105040b007039005500340c8a143c0745440041c0d11440518081c41c491000341c490b404541c0d01c500340744408103011b68401e030030402c01003140d180d0016210101e00030940b0720b00e2854036039000040c01c0c1e2007142d2150010000000d03a001ca1003160390011b08501e074840e01e4900d00d10200c2d400384005089002c0c62290005000183c0e83e5110300745510481c02c0c3c0320030003804920040c05649624401e5801c0c43d9071110f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 329637652 1250 329636402 329636471
    0x70f030e120403050d2a1b090c050d11071110020f15090607020c221e142401030504050a21090803120f0c040801060b07140303060d0312 60
    0xc072194040310002c03804425a030314140120308010300300d949100702103004041352091407e5456001c00c813a900c100900e50000100002d800c0680054101d034021001440854a01102c2600310702d19001510070703c54002c4141c00d082d020309800c0c40041c01d9105100c1c1d055200b0003000d2481560100503960006075100b00b601c22909140b4031492a02e50050302110540d00702160f80c0c40d480d11007450140d5004c0e0000b02d11103c0c3d10328100c00380020506003104c910b0416010b00c54540c0c5030400d400280000d081452044d10f540e41c0d00b0308040c0c1c003003008082406100325840e2500f01a42c441d811084c2c00070300038000d4071071050306682d0741740040740a0790f0000d602d00704440c060060660031083c1880103206640295251a041c000034007008900103294401821302c00000c030701e101e9121800c2e90090700c1820700810650341c41c1d00c09507040342c1001d0030031140c01c0c07030501d4204210030303002c02602e000310009400c0e0f001c880c0c1c4680d8140c90300040b00c0c52503505255a0b0b144420020440c40d110413010302083c00107003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 329638902 1250 329637652 329637673
    0xc090f030606140f0f0603100305070e070806010206041509021c0f021c050304050d0503040e0c0d0501060e0d03140c0a0605150103150b070305040b0a02010c0215070f030e12040305 79
    0x1102e40620082040c03260400300d00300004c0b80c480c6401001080c40450b840c1e90f0f170b981e07541144120640140c1024205100700c00000c600d48400201c1540070300c5140c1c41d040c1d0907940e01c1004a1381c811040b03038014004010790000300c00c1e990444d0045420b0340d200800003100950405900c60300150000c001b542d009080d0300e4802c05508291120640c009115043c1003e03805140d1500d903a81d00c82d51040501802842400b081030150a10958009e401c60349840345040c10716414034400390704030101d50568640307018000111680140d4000030000c0303000c0c1c00403d0900680c0c03000c1c1c5416481d440c5900368080c04205c1e2540050301480501c860502c20b410024490800355000a140b400840d059411f03d0700d07122140200c00d240a425008a0f0707011350015540f44081d01d0100d0310390181d58882610b000003c07e07032104003601174100d0301100320300307030300300c07812140c20102ca2681c52009507045004110a6aa540030941c82900405070341810302e800c5800008607000012902d6000f9402a1459084207130501c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 329640152 1250 329638902 329638919
    0xe07030b150301121e1b09052d0a09140f06100522020c070303080405061312030207080906040803090a0807060f0e011806050306010f02011a040c090f030606 69
    0x4504001284102c0c1158108140b00e08003411164000e025162210800021540118004c0b0001e0f40c1c0f045180d501c113160303848000111186406940b1803a0b00300000140074119120030302c00140d1403030030304040c0503070807117601c0c880c0c0300014000f020580d486804c140b0118620141c000705044212008088201307018684504003200900f446a10300000407040011750b480c14528281c08046501030080404080b032a0b00c000d104203068041d40e802249000802c2c1500605207a01c40e5001e203050f500207540d8450518a20a8608002020007444600050b5014443e5018003100e601c03c5e140c5625004500000070310039005607001520a03071000913425140d081c444a410010300382c000003411000d0502d80b01a1a900441c01c04404002020b00c030502079a10403805400c08289a20442c0b4802d03403a440d00400c913500c215213007404240d00704100c111480c814402c005a004448460724104200d920400000c2d10703030715014a08104442c9004030b407031004525440000e500c03a044c000358213880c00415 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 329641402 1250 329640152 329640169
    0x4200c100b0a06031107140c01090602010504021305060f0a090203071b0c030623070f1404050d0f020303070503180a090501060509040e0102040b0f070203010f0507020a1b0e07030b 79
    0x104189080c8001042103031680b1540c5400ea03056814080b40d58a1950340102c054014410040c1c17419000c4040300310040d80200780305003541e5003aa548240715859440590984909490003908200400c80300c151404960744501e4210800405811200700c0b24000035510303040c5600701f040c28503400030a00c074900f03400010ae8032240c042f400b0b00d441e0707449198a92429420031840301905030743e2984100a02c03580a0300c41016080d44045061405007400c070310080543e0b00c10507020001c2140481d8200301d4032505c4042d2005c98800400d5540852a656189405e5900e0624100d80620081c848003000420a001602e42208003030200b0841303414a000b0010a40d0b2291b0207192124548001404031941c040111412803000384d4010800303c0c484010340f402840b0b9a401030900030000b0580c800c8d0840240024045a40224000d020b0500c2d14050b81d02294419103400e40581d20800ca0500000c0c5948110315480c030708502c000030099a10700520302d84d6881200c021001075070710802210f881c60080e00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 329642652 1250 329641402 329641423
    0x1020f2503080a022215030c140a1d0301051f050105031b09010903020a09090b060907020d0f0207081501170d020303060d0203030913020c0729030604200c 68
    0x28003111500340d200685908030161185080c103800150440102101c0800c126140d0350300e503ca115804d5480d174040e4003140c10074000742c00003800c0001840c02548540c2d10303118210000c0f01103600d0302d00540d000b55030030803905c4031011810041750b1090314a540e0030700c5014400e00342d09400205032580240c241600d16010b0300700506022040c4240160022000700d01000074000c0302d00c481da500003400041e940714205074402940060484004100300149801000c1014425101ca44140c1c03034003001c001c103160b411221b810048e40802031400d01a803041c42d89a00c0d24606d0f0041d10241500e440026050607180d90b0a012007480c80302c01005082000c0b480000c0400301d107405441c00c614000c400946a1201814207481141c103003840c002990350074000c5482102008241c8181c001103800c00401a40052900090f18007070340300d00140940d00070045191001080c4140c00940304042009031440e0000380000c0d8010740d6800030868200704c0c1400041d1841e21182c070303842d2192108a002d924050307103002c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 329643902 1250 329642652 329642707
    0x60203120a09020f0a0305010218010207151b0614070816141b0105090d090609030305030601140c0a050a020f010c05030d0e03190905010f030b09041209050301020f 72
    0x21142002a49103140e45420000c0108041414002400000c1c4124a003881d0a0f41c043c4c004880081000b40c1540205a0030f25068400780d10107980400580c0c03100124400e46901c41000c0b111003051a21440080c84010b401030004821602d260b160241181d247d00c4107481a00406020b00c14800c0d00b00c1140d80e48041074460f043e98841030f0381c1008000b00407103001803070a41404240b01090480094071000c0480300c480080125143c40c4007015600e0015501e071002140300c0d00700c04038034107204d01c6d0f540c010740740c2544440d850358a03031000444800070740e0700c21050380e400103000f090500d071014028080314030b00500060288400d1030040001c46c010123545181480703200c1c020f000004d0000700a40e54110507125001525a8281009a042d44503c0c00d000040c80d10701101424400c0d0402c808906541081e6115480f0303624601e0181c2c102c5014840245c1d10954080001e000196820791000d4107144070315208000542d06c20110303099800003494034844400100e90025201505400014030708880c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 329645152 1250 329643902 329643907
    0x807050909100905010f0e0c0f060406020607110102070c060314061014070c0f0308041e0f090b0102010b0907200c010c030804060b130c18050a05010f03060b1201080601060203 77
    0x107119582c0c0e95040d10a011006503c81c2290001d0000039072141500340c035070010610840301d070007420f5a154000034600c280700302e03455611503045003402e60583d03060315802c0c5c000780307145e445001044c2c031181c101d408403c0b01c940d003c0203c040015040c0000c04010b041e281c0300820301c480f803040585110100285100d0050304107210700ea041590100603c0b00110f82d11494a44e03032a800c0c241080d4041040d08081014540d41800008100084000384200c0307600142114440c0c02c1c40c1c031034503034041d040e104840070300c560010144403883c1168000c00109005000014072100780350b021500101c400c44040b4049901074484485010515010400d5401d1020107455400b41820000c2c1c48100144000740c2041980c400007410000d03164010000c034203006160390048421032507482c01800d00c04034054005901e115803a07e14a41035100001920002030810354500e013040c004450081884211030101600c4400c000360202c401e1008000101e41c4031681c5180e503041951071494a0010703404481150f204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 329646402 1250 329645152 329645161
    0x90a080703033e07030908010504140d05031005131401080705031005010302030d110a170706060611100c0210020301090903030e15010b1c0203100609050a03020603010311270108070509 81
    0xd20700080c04140d2030640f29031a0700307050074100c40300010368011030f0080d03107480306010511103120444001c0d995080200c7c1c4c40c2581407541121640000e49039042c0d50011444107104a00e0074034015003c4290000b0005065096403c07004c0880e03100380e0007000b40340c014a8007400141801e12522002c07911144003844a5451540400d640b10810480e00e010415820070b1b48902100c14818503401540195400c8105685219022000e601860084840a1030101300090241c044c0003881e2a4201302d02c0a02110a0158091070180c047c0d00c070f24004500681203c56103041091020f58040c14035100300149200c1149806412280281c100580039404108005408c3c80c490301c0c854150380d1441040c1d40c803940d010304425000d85000c01c1d803200c001d002108201c02c606244030510121506a51004800c5560300c0502011460750702003e9040310042006201044001283d20b1461402410f595011081a10011801501c4100c508070b0601404010000c0e03400c108080005840c084600d403485040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 329647652 1250 329646402 329646491
    0x90c0506070c0b09010e12070f050405010303050702090c090d08070218010f03170d05010b1306030c0509011b050f0d0e031f050405010b040509070513050601020d08090a08070303 78
    0x8181c0f140c050300100001e410085a481500c8005141c0720151034006003580303e1420070703114421401010522511aa40000c9038a002e010701c81c100ca800d62521460480160244011f20340d005100410118040041e00102d4681e18007070f55850b030081c1c2500341c8403426441044050760180041c0520140c400b80140300450220081c1d82c01c80f50311141d60030003100e07211201e802c03d0180d02d01c01c3c403c140c03401e0000500c2a80c814010315030102800c001c4c035001912a10b0903400c0b1480c444800c00068024041c400c0f03654000c0c1402c0d00000085410003c030608280d0382d50f0310700050062010010b401601450748003682090715100f078984114090030f8032031281301000380c40741625105001d1aa032100c020a00b030280a6100e00207580c0060400d1105161440109540d400d152249034040d42c1c040d0000600e810341e81c894107002d128160b000d40310b1040c0342c980464003020040c0c1212402c0c09110704c440d0010b80600001c04074207109480109030120300c42d408941038180a00401c4442c02c034001120070703144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 329648902 1250 329647652 329647673
    0x30c090a05060c014a070b18030d020a0b150a0503120c070e07050f0a0e03060702010b03070902270a121a070c0c09050702070b04080312240d02180a090c050607 70
    0x170b040300d07950103019080e840c3c403901e4520785500110b0040f1000814200c1d100071503003541ea581c2819400c50391594940d1000700e070b5422003568040c0410075904007082c220080240500d030380400042c50392680e01d845400003410320f403c00b5000c008030440042c1c04078102c0c500f481040010940c8920104c228038203054058240e100e00d1700c024101d0100000c0d8000164000c001d08030400a0107001c44d5058030780080068001c00c40c01090358424414104002240c072410f008a0707e1030400702442074010a04101c0d1201b040507002c01c484e81c028041c0c0300116003500b100b0082044940258480601c1901450f12070141d0040030303082da010400a40750000c0072441e954058003c841e01c02000140c0b0b603468042c12401c01030070390007070705202c1f10010700000d01030000030180050808040c5480003d4454000c8905905410701a401035601100c0c140c40c4030b4035040350200c81081c0041d01803030a5850084080203114401c4600450f283c0d0b407050004203024140c0402400703010b06940341c501d03103d407d4a4035402c1c0c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 329650152 1250 329648902 329649011
    0x109110d051b040e39010903020d050c030613060c05030105010c0b07031506080a060b03011d10030206120a1a13051b07081902010b06030c090a05060c01 67
    0xb00d400500c03610329511150301c0200d091281c031082e0b58444e030014620002c00e000042c1464505c10030304900c520840f40000500d400f020058440315405403941d42886568000d8540c00c0e5250302828000042a8400703000585c8541002000184406814584902120f02031038000c0c0400a09000600c03a03070360440507540d000ba400040c035502541c0e82c80300c200c000d068114507180c0040d081d80c0000030300e1a04040590700825000d00e09001ca66244c0115942d140001d100b0601190780e01101240e001c0103210b0019002403000d28422a0300d40c60b500032600c15405802d02e03901d445c055808104003841503102d03031455151003401c20782060b41e00300000340f020860202e02508186c0d5842c080703407900d454102c56440f403407010741c40941c4420b454100007030250804816100460b45070085001c40c20310600c103042135020010805821500c9081c0300b01050742182207001c0e00803402042c041003ea50741c801605030b410141c8004249170100c0c00b228241462446a00806049003091101200c41881c9003804035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 329651402 1250 329650152 329650183
    0x1b02010f0302030405160914060306070503042a03080a122a0504050d0b040516030f1401090c09020405030c040b060304020123040602010b0108010e04031403091e0109110d05 76
    0x484c0c030707182000d60910304020200d4049444514000a49030465004500a0544442c020405131740c1d07042403649030130b42180c1a40c0014402c20025000441d209140600212410143c0e03440000014101c01e40004a800075101c41c1c8001c0703816100d107a4410042d1811550b02a0207008410322541082c0300a407418905000300001c2c6003022403c0c1e8451000e0310014070004282d0300644040e400d102040300006e80d0300303607078601860000d000d8149030000c0b00c60480750320a80c906044070150702c8551030440c083d803510f2841c0d500c0b820a10042118024044050150706900680d21441c2c40200341c41c0030a904c4040740102d05081603084036541d0801a6644142c0a00304488140d0742c0d07410380307070b00c4440d008050000c10f14003040c003180c2036034154086039640b0b0003a01c9002003641c0310320604c400208111130040000b0900c0115a1902c80204061508501100c0442e0500000100381c6c1c0c00c42d0b44a000042c0241c1c1d564051181402441c1250342e201c02c0041e524001000e400740c540545814031103144004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 329652652 1250 329651402 329651407
    0xb03100e0a15061e06020a020d11030f070602060a0e12031b03090309010201050106050c03190e0604030605060a0518160c1a06030115060e0111070807080703031b02010f0302 76
    0xc54400c00e100169100750300091044400820040040060400c4d020700e081d0014040c11281d2010001c450140540f1095002404050103907400c000c452000ca020880d8001070074801090310b03031410403001640050500140c6070450801d03030000d00e0004001e1040700c80c1c5062804010390014003140403581202011038442da26512241000e0f03002d405294404064880002041444003021003d000000d40981c000e0042d42d907142c508070b496001e0101c11440c950030401c6040e554a2650714810a50704040c108420b412255070000368684d0003a91056032110348440801c15145040c151440141008031030b207585801600503002d440c054005d10281d581003150742884030709400f50111040385603001c1d80e00c2c1680f14070800d560f00d01940664010340650300305081e00b4200c4001c00110800d44040343c1e03501442d1f0104100445950103480d50044030341c0510007010504001c14091840a007050303000500110340741d0b16004007090981030b00b10b0085c820907682c000c01030ba841f160201c0d03a01c449180158 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 329653902 1250 329652652 329652671
    0x90d0501020408160e0c04030b06130b041b090b03010e07110a02061c0b180a09020415060e0112050408030f04031101090c180207020306070f1701030c180b0310 70
    0x20300a110301d420640c0710340320b02e031a04c0c0d0f0907180503070712441520850380000e00162900790800c4210b004500004003040c0984001402d5070400714265024841c40c0200410b03c00101004a022600400d041c1c07075142041030403042140703400c5014100200307059040300d445c66140c5100390340e0607007001c0d12038420030086000001030150304001c0d000403160010504c1d680c400342c40082c203940702e441300c5904160300d040c4007400741c981c50285e1600d000e814413051980d280350f03260000100100010703071003280c1c42640d980c3c1201c90b13041d0300780020b40a0400c50725109000a0304130000760140c0c0064050300c0c4903508080030000011440c0040d260410a90314842d003040d146c41c07a0642d003104280030940c40640c80c0c40004014071030b0110a140480d00554001c42c4400200c84402c0140d02c100070000e50554450070201d1070343c5224541a21444a007858401ca94070610b103545000107800380c3c000c0da4410081802403103c11074281504070f1859000308200040c1142c4004251200070110490540075600d80d0510b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 329655152 1250 329653902 329653913
    0xe040e03160f1a090114060603060a0501080a02160b090c0913110105040306020d0b010930030e0a0306050105030c090721021c06030c0b040302030a111801090b030d14090d 75
    0x800c090108025000b03c40d14084480c02d00901c4c0a0100e800c04000100100e01c82c0d00740f4004480c003c03440585a0880c241c142001500c1ca088040c4c45064160350820074240225a140b50144402d441144164201d08204400b42d18001c2040d00f4588210404014004402c90f818424182640d100341d02c81c00d1038551320300580d01750080d5030010b0700e142d00003c4c41207101d445990120b02400d000340c90780351040da2505c0c0c1801031000f106850102090801098010b440e441c4481d0742a4075109280100070a99180c01060543d400342d40201c540a440d500180164501408013a413004801e56400050340b505560003007085034030038012190030328995101016502141c0444019202082d800740c4e4050014a03a840100f000f840190ba0745a0b40000215018000004650480350000c0082c1710a10b22a00c803405265a184901c07980f244207080000840038032002114001c100a07100052141040c0e01811b090407081c900c000100061201900f50403201d8100b614401002500d9182580b1220b2900 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 329656402 1250 329655152 329655173
    0x50306330d051006060503190b060d180302070e1003020f011103031e0618070503090304080706121505010801140d140a051506090103060b0607060504030e040e03160f 73
    0x554001c65210318103028001c000a181241d040041c408003d4140c0d03510040b1100c1c002034404807161030750f2003c44140141241c020040c050b0300141100d1804141d101c0a00413560303110046062024051051014560144040070003404500d4410134940307891088981c0540107800028440d5212062860302a4868020b00002c44400401c0b2a5207040000b04001d1200070840c0e0051103105140005015040081d50229100c0756280c80724103e8944e00400c0e15650402010b000341da1006220004a0303210270402c200061602e901c400c40310300513281010b0140c0d41e8210050030f02002c240020007240e41c1c40070b0044d046411403109a81e81e18940d000207a200000f04501400c1110308141c4e10b08488400305600d440307640f0070402c860603054822800010030b1011203045510a070500c0c01000400c945400c42107811100400e401d01e0302d111075443d24201d980649050740014860010945681400e12a601240c0c900c07100450030003a000000480288403128010311401e0000c40403c200140c5101c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 329657652 1250 329656402 329656501
    0x90f03141501080f0706020f30030f01090c050c0c15070f050f2401120201030603080d05061507110616020303040303030507030605090405060727030309030c050306 72
    0x42465540e44289199594490305000d94503405061170018034240006801126100c0e20300113403a105048070140fa01080801081640644888400723804071268280158070407001c5420094455041c01520700854502c2101c14091010400141845050018004001c901c0c00c403030240d800007510b21604914040c00c00020188651801c0f0304040040108440140100560440c2c55010010030504c1c1e5003914480c840c9001c0949030010300c600c00d524101c0141e906c1c010b040100c0e20595070b039254000340c0d00c160b540440950707541e000d105051404c0416800f00f207005409807400c040d0940c0b41d0743c044d944c0080d1380510034080050000021409904908a941d8000781543e885070f98904015001d00310031030b11240000c2c5488804521442c01d01c00c3c10f0300030f0b50841c004203042d40d0b54440540c5d803003000254541098ac41d842c0985100c02840b055031015500c66035402400e41d01d580380c140d03c0d502e11030b0440b5100741c100e80d040221445040d41942d0341204802c902900c20500d0381d5100921044508 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 329658902 1250 329657652 329657683
    0x5190e0604090506090f010b07080f12070806030d0f1704020301090c030f1703040b01030201080702070504230c0313031407020a030c17060606030604090c0b03010312020607090f0314 80
    0x103070015424090f03500c8948901010350384540a6665514180008a403d02940846072003c0c070045010078032100140c03860002c070580700c40c40e02c0d0080224a250036411544d01c3d0010700300b0303800c124140c01d041c098442480c4081c184403480c058091405010b01c00d40b222400c48160003100010150f540c250008044035070080c42520110741c03641842e00130800448000c0c0c43c00030550100a1075465880c0490b0301c1503400001d0584541d003190300448103500b0150511085114001022513195640e2064403a100301c00900701e00c4884407080c031140304090003810390510000c140100034200a960b490f01e01030707560500d0120340705100044210080e000b145006500100d90410110802001002c040180d495040c6000d0f5428000142c41781e81d00c00841d002900418244040f401506068100c028a184104d9140030019242c1500401c7d9410907801174543c16070010a528400b60140301c419000107181ca89110031504210100300315404070304c80100403400415113102448001d00003c40f580310242c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 329660152 1250 329658902 329658907
    0x13090308061e1207060207080327060d0e010b040c0c1106070515090a140a0f03030b1302030a021b07080c011404090e0a02010801080309090406051e0a15050d0305190e06 74
    0x1200182d075880131340c02183d0244c46100c102081615002080e29000d440180790700c1c2001c0500b9800812100300c00b010540c03c40030501020310695190701030004a682404000211103500f01d041005645070201c00000b4411404115008a404621219511001503400036903407000c900e0102c0c03402654241b03100c0310fa4021001c2c08011000401c0150034039012340f40c03002e40b142c11070111589528180c03100500c60050041c003040028000d03008005424001010005500d150a200c001130760700c21038542410950004112034403402c9080e40c690852142402840c43e00d0400e81007039691b009400007541400400c0310141c9482d1501c00844000d800d005009221500e516040103a4510420804034007080e4800b0000c584880000180c0704c0300b40001b811755901d0345490b180c401c010007003e0020803000c1030b02c1107144199001030f5402d5000d08883d580000d8000030078560b03600d1984650b00541c2c42615a01d0031000400e5000058036900c440c40315030351210180c4040c080d0f48040c40340b402c5a8000502 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 329661402 1250 329660152 329660179
    0x6180904050d09170d0305091204030b180106051806130951020d090b090601091b08060a0f1205060a271b09020913090308061e 56
    0x2160b001c41e056940d88076210a036031103000c141d0b041005841c11141c2036218007070000c441071282d044a40c0002200c41501c2986c1e071030008402d92980709410984e1400000b800303100d010440b408180d24089035513002000f040d401c00c030000b0380149910a102c045484000080350749503803628000f4441c10b480440c100b04c1c0302214545206e1681e020180e141214507140c1402c10f0300466070001960b503d01450700e1000c442e9144101782146000c910017080e0065090282c2c51a0b100310384070305404180580d040d10100c2c501500480c0c5445016006000f0080c00d002002100200540300559005501e0a0111441d5200b10110b594200350782c1c42a8000b0292110004400c4540b00c040000c66000d1070990700c080d500d0f00c061030240c0750403244428840044422600902d05c00e420384640301440307682a001034007014010068101c086070040480b203a80002d05808174034115400d85d0700100d6000003848205c50b030b61009088058010000d600680d03d603107001072854450845500f450b44010a0b4a030340b40003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 329662652 1250 329661402 329661413
    0xc08090907031b03090302060c0d020d06170f0a03091a1603081005011d010f020f010204090b040b100c0204020c0a020607080304110d200a030f20010e0306010506180904 74
    0x20309503c80c94102484149194910b4401c0c0520143d40d40c01d50001c014680703e21032409002d62046070b00e03240d07042c2d0902c08100010003178000c003001422094100c04e208107245180c103003042c04080c507500031940141e01c16000031340c100d8030b20302c2103810b41815003800001c0000c5020b4207200b21540ca50b1b1005090b0030307080416800c208502d004020701e082e941f4201c4d0300da4005465280c080410b4500007442081002c200e98480e8450081000451041e0750070501d2800d10b160076070b003040c0c02c444203564449881c1607650416102d5100c034500c0803a100d40d5600401d80c406403071815401400303409030703400094804c10403104020181400f64007a1645580314203900b00140c03160025141110340722014010164146040c4804c440c010b508901610001d407018905a100c00314400c421a81141c2c07840d00c004003207030300c032030010100341e005500d0503040308582c005048140c01d083c3c4865052000c848506400b94038001a45419903a080d41e039a541c80c805190000c00c400f100380300155200e903000d01040b04104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 329663902 1250 329662652 329662661
    0x105100e03151f060e04050705040e0405030904110a1e0203040b0f07020907020721021f030f0f0203100e2a0a030c020307020607030804031e0512061503070c0809090703 74
    0x10f9038000030307000b0983c103850100c10750202d9124030800101c0c107441914070762400d0f900c2550412142d04040f0300d025964000075031528402c413000d844c25000840c03502050b041c640910308032914204611842c112402c1005001c6810703082e00c90003c1e008980241020b0383c020421500030701215009581c07220407554441100d83e2002e007040b401241030901042d42240001581026510244c009003141403c0c05001404010300c250140d910a240003079401c1e4520912004101680f600c3e607000c54444c2080703d841040c0c0e507040325040805403041003007000c2d80141c00b40f11800d880062406205c141c80380906010040d151414403840d074039113082080c010220320300c0103102c0c59070261800e0141c080c0d0803906980724080d201000e0340040081015400091260721070550103403290a001c4010300c421500417003a101c04180c050f012031000078096040c0320901141d694420000c8986083d01100303410f41c840c417070002500f0315061003080c0301c08808000a4406841c2c5182001d0000e02d200c1c038040701d00a0242 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 329665152 1250 329663902 329663911
    0x2a0615090e0304030203120d02040302130c18080601051504150f02160f03080313050f060921040b0a1e0201020a1704020904230109050c01260105100e0315 68
    0x5514104011001c000301100342c3e411a900100940700e038031a020a5602c06034000801c1d00100e59007040080016990f8180c1ca080c001d0600c1c00001d0710f0035003501c003d00078071648921441d4540507034408201102c000540325041d1442030b50865882030710401a180d042c001e036046a102c503000380540d01c1e8000d42c0302016105a0805608a03801d25400491200c544c510500510507140c131100d00600108410500840d0440030000341601c0c05169621003500b080031506d420000703600000c041c001050010030854242c040504003030344002d50001c1e00c1021b6441184208070404201042c05288640134190a1007000300ca2003c550000c190b50304024000d52202c0b07441e00110f0500c0d0800411001d103111560721541c0d01a2446c0196110b5031110321040c030300d4110350b4ac4120301e0507000c030b00c103035400f8007844072034030f2142009211112702840090b01c040382c84c43c88801528109030104a40c01e02c1c07001c8540c110742c0180c072a455003141010b4121110704420750300c0e60b0148241c04003440110544040d09100c1d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 329666402 1250 329665152 329665169
    0xc030d12151e0b0c0a031b080d0506030d020309061c1b09091d10050c0d020f030103050106050108061309050c04050103030f020106050a0b0a0305130609080c06162a0615 74
    0x65210200080d0f1809403070160380659202100e6440041d004015904900c0131552460011507400d0340d8070401030b4000c54017000c1040d1a1024003000d400c082000ea400c20342203001039400c0101580100b5918020100002d06d0a0701c404048400082c1e2035004108031803042c5c0172030880407038400c1d005e04100440e12440b00348501c0c0580a00221040198400104c40b07428040e00103012214403d10103800e011707160b00040441000910034600711803000f8020703050045010741c0c0300d6140d824840d003140e0f00c4e5800141405200d4042040315035409583c505880740f841c4000840c8885400c09900d04509058929041854a0000f1040c1900708040d450b500d01654020310481d030322142440300c01c0249120755038010354144200b846042c007940096038401c03903074106000c4001c501d03100c150030366600e1942034401000004081210044c01c2c002d055000c501041d202080c2100944000c080a80c3d00288189680002040022403101c2c0340c246425203070442030500005150303403600d00d1160110b1250152 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 329667652 1250 329666402 329666459
    0x130513050609010504021503100503030c0106060207140906130603020402070311010b01020705031c11030f1306090e01030201030e03120a0e15150d020a08030a02031b0c030d1215 78
    0x900c1d10341401307840c0c8115405040c282c6540c1d80c0040d0306100c2e4002074415412200d5400c0040340303a40f4200041e140300c07a07090340040b9600380707041c00c0330342400701640018110203c08a00361100e911292001c0b1341040c2c00343d0300c4000214542d04903400030441500000d5102d40001008070a01d503101160100c5085103500070880081984010390392010700d4440c1076015007040324030304920034100310708280400f4141094040302d641602c4050455201e076240c464120ed010582d00e030520160210000a86100c0c00c1103415103040c4a81e114500005200017410036071240c90070120b5100a10580b080008801e1480d011418850944070103010303403221080790b51003540302d001c094100c1d5208c80d60280c0402e403006050180c0000030311036051500d01c07003a40c0180220b02d000840c00390030030040801098941c042c60711501c0600442108100d013248001c0700f41e003c010849a240d9011800590584140c03c0480f0015051845500605055602e0400d40340850100207108100554039059080340088032340bd = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 329668902 1250 329667652 329667661
    0x231224090105090607051605060109060321230d020c0a030e0d03091e080601060f0e01140327070608060405070305010602070608060d060501080309150a1b021305130506 74
    0x107003240c004a52850181d40504081455140140300030000c144610070145c080010b40d488061a015081e4007010b8415501c880800900c644440420035618020a400075000c1e001800280300e00100d60000350984080c255204040e48080300301e44000480c9a800c2d51900c00e5462556111640c1e0501a00420b00450801d8446e2a02e10514520907505844020425040001c0d0301070341d02e00c3c4407084811035211a000300e20b402041140500a0000782d07247c8802254150b1f005043c03210440501c0d040c0f00c0400303040c03189030a02c0c2050340da002911160144903030b45550705e081c1220b0704007809007034140202440400c044d03a226120610485007034a0030300254803108001c5040b07a2091107400e0068000d52030901846101d0115141c000070700414000e1011029190041114000e0b8002071041e44001007418090902030520072000036000c045a04040280c2d0000c2c0510050102081d50f9284c001ea925085555800004c0c00900b074003a420840c03490200303154001c0c841241d1080d1441e11035100000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 329670152 1250 329668902 329668921
    0x1d0a06090f0e060c0906040b0d18150c021218012a050105061206060105030405030705150103051c09090c1b08130b03060d02060f07060c080a15231224 66
    0x22135011001a01b01071415141c540b14000d242c01c40350410088a4880a407100148000206202c20764000c1c1840095960088400d03000c403090403030540d041d5040100f411422009100c113030380b0141c030311614881d0074120980c0100c134004500d483c854500410882c1040e0340003034800d15114107a1145008009548030300e4100150410320034840d003401e80c03108000514652080e40650381043c400d008482c1002450764a82d8142204c0400c1200054401d40042003031000c00c0183c00000c01c0b901030b03e28907a15400100915601c0c103070241e24201c0b80c403480444a264400c4401c030764842c00b4481c41c01003900079440e2030030341c07503110003102141c2403210384012a80014920403240078200081064100164640c20702485070000400c920107407209020310800314072140108d00b100d014566415040d0714050258074101e0700c180160359515480500300b8422903d4040c440303140701c1e8a089000d40f4034203103440050300a800c40d00595034a4050105540d99010314101c98600410004030300300303180d0b40c03440b801 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 329671402 1250 329670152 329670157
    0x90207050d0c020d290a0b0a090c110106091a0303040602100f02040b0a0207052d1c050712060f09030206040f02030102090a06020303100603061d0a06090f0e060c 71
    0x103086500548961030103103001d0010000700c24805401400741c820380b0b864440d00300c04051300c0e620210740e5a048074100b0b440c00c008003d50110380010b040010f070105402050035181300e07004a2035410b6603030841200300c40c00352070b00c0c100814040c8001c2c05900c0c0c44403000c4c0060700d261440c88507056a11145040b00e03142c04800c1c3c0303040c2c902681c000c000b4681c00c030950002801c011848004c0a40c2d0801c80030036142c48a1000701401040740d002000340a10382410301294884607501c0004140c0700c007441214024210750701000d46031049821007501c0000e9010f10305410300c40d4030010704500c540f040004000120010b805500380c0118020072410b40200788040558518200050041e00700704005000107208611541c00b1900180c001410070040c080400d0710340500d40c01c0580540e0000c01080304e1200107614890241c400c1f407409001c141d1502c001c685021440d016200c04203039500000604c09800b41c0e0000c4010040c9a909211510104102200504d100400354090340211000208483d491804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 329672652 1250 329671402 329671417
    0x1c1812020105250f060b15030112020105091903121115010501030510030204050c0913020403030203040e070c0c0e0412170105010e01180b0c0712150203090c030a030503100902 77
    0x12800c1c0b60080300104019000611946400c610000f64140800b05030405180384145208400014103641039100f08124201d0101075900e2a000410050281002256802001d1030342030a28a803a01c01c1d100c005000308101c220f2550754070406840000a00480b41000301ca4180703581c0721901040603440c081ba46035070f905920108148144c2e801000755500c00d41c0600e5008071130b880b10030003003a1a84d001400b42c51003501c08070b03461203011851190500c0c04030052071100c1c201c000c08605d403514580e4042e484e4010b40c403a851002c00d6020000d6140d034090621206080d5100d1400ca9620780c0b610400307800b241042d203080ea0300b0f01c28a0780302c11a00e03014258025458200b109442990b070b1a204c01102c0d80d44a004006040060708005d80b049180e051000c480500103038400d041d1605034150340c5600e0041c039544400703094025014148040303641c08983c070074194510500540e695840400044c80d0100c2c03001500d40605c1001c828405069100014500413520442c035101d4482e80c03100c07a8801d9024101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 329673902 1250 329672652 329672657
    0x3070e13171303141f06080c0f0310110c03030108071706130803100e0f0103022b02013b0102070501210903030e0307050709050c120a0c021c18120201 66
    0x92000c0b4078503072910304000510408480d9613800f00700e0640501324100300c05c0100c2a894840a0110b05400d11079820b590106480d00c0101c42840e1000030707a15044122340391080ea550346550310003441c11400312211304602c081201d64a507540d00034982c1d104814413989285601e50031040222290205899005542d84800d500340301d402d0382c956108130b0340042c04512903130180d80000140207640007241885602c0a0610400561541c0103020244040408044c0f40c04480e50003c0e00c1d55a403400000d07004d60302072030219285c1c5500d803604a00309010101800010310001204400c0060b4900c8405803080c007a400d41c0e010a0b80c0d2070041d502ca681712000c0d0f684001190260118a084a40c8000350003402031402080304240b0050b92401c5600c400010350f03081d0016481844011741e80d000b290b400c0070704001d02c0307031400001d44076001e07080401400350010740d43c441e03c200420502c200301c1900e207103603a020300030400e0303804c0e0030007408089482d44035a9020260100020b44603d078800c1c1c0c2010a03130180c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 329675152 1250 329673902 329673937
    0x1107050a050c01090302061b1e150703270f020d05032106060d09110405010b0c0f0c0f040c020a0b07050c01050105040c020a0305070c03151a0901032003070e1317 71
    0x231041055001009507101c003984500300034040c2d40480720000410074072490740640791003811132035002d1901100034805e00a05040040c120040ca03860410300100700e2110000781c200d5403043ca40007000380000740c07000e0740c001ca180d0102402e002000c4014642c4824103410f1440d01008400080580d1034201e50303440e4010b40600c101c0c3c2d54a8020b404c18040b42c3e11641c140c1020301c824200107001c07100d01ba00003101904022030035501d81141000440281180140281550b0358032000256204604480450249440d0110142868000c000030041d042c0d20504c001464a00010000c21035049543c2c2442c00d9800c01c0e00020340c5045c0361059407100042503014007001e90154030152400c1d403013000b0495030f41c00006c0d800408554200301c40103200c41d81d00c1c400f096030719040c03c2c15412115120030b45480f426000d001000080e500a0400c904e00c119162030880e0a01c07083d0000f420280141d211103106111001007184840c03440c84604070309032282e004400d144030001c684c00751a0060100070300440507178 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 329676258 1106 329675152 329675167
    0x180a0902032e1206020c07090b01030c050c0703020103020304141212090d0906181815120b040204020318010f0b01091505041403011107050a050c0109030206 69
    0x100000340620341d6801c07400381010050382c400c060307080044080c41c1c41000001d4042e2421b101b0702005403160303503680c0d15200d005040b031052a540080e10701103800003224003540c1640d109900000042c80c8860540d40158025440038005075004140f03d024051444400c012080c42e03804103000040e19000d144102540000c0701a0900e9019009225505a1964801d040700708850741071500119a088100807035050740d11035002203004600f610380200516280345c01c40d0700d11462403200401e10f142e640c0c104401450100d540100480e40141c040380252409070050358012586400346000015800c04990844070300d0085081555201e0151a0847da0006040300042822640a03249401020002411031095002d4482d11305940c90b00b00751203403425880300c0c0503504c0416030b03e5552102820450340d21078600004450f18802ca07520030315503520540380d42c030031642d002d0803690a0019 = true := by decide +kernel

theorem cover : BRFrame.Cov 329496402 329676258 := by
  have h0 := BRFrame.cov_init 329496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 329496402 ≤ n) (h2 : n < 329676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
