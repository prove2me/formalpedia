-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2483
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:50:30.194055+00:00
-- url     : https://prove2.me/submissions/59f5da3f-0cca-4f7c-9501-4a64af8de2d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 446402877 ≤ n < 446582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 446404127 1250 446402877 446402893
    0xa0c080a060501020d2d0203071401020901140c0304210b0703110906070c05150c12090d03030203130c0b09040516090510090302030106030305120a06030b010909030c080403050102030405 82
    0x10a80701d240122081030300900010901440112190812000c82c02d4011001d1a00310b028070000c1c2d880101510000e4004654408a504185a04841207000d1650700da0040005030030300d90340700f0b4049804020403003243e51280880072100f81035005940022a201504661482903804003990018001b4080d10104940340c50301e40c000c5080d1107901c030903502c010f182041040310a080520042c030740070380038982ca01c076030944810001d1070118440101c0a5229004682c0c00d2505500303100080900c0140415140742585c1400441c0309940c2401000c1e0a0560220005d054412008400e80b0490391101c0c5402c00300d40c991000c09400e070401c004141c041e0745800700003140e0610000c1e070072655034041e80340d05145034501420000b1000000e040d0204008407000c0c00001a20309000d104080c62190b154203855202030b0030101c0c1740940003082019000d0500c031080000c074132810711203415a00e080304c01290381281420181d911200d85c990003411014000341c00810300006502840c0264032590595141e8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 446405377 1250 446404127 446404141
    0x91e0709091d030412080c0d1817070303080405030d05011502070506040b09061c020304200d020918240a06050d08090f0f03010c0201150503030703021209030309090a0c08 75
    0x3088941c208080d698402c01041c4840740b030405c40c10b40258070484841d46010640520341e820f14150340f09400201d8456021803025106100c0d0680244c00c0907000010181c0e1404683c0d6503851082c13001909100c3d1160202e014858140202e400040000300d090201c0d5955400058810042c200203000500070f81e00b020131a444c120046400702c451800754141070040300b004229183d8451074484040f10303c40d200b10180b051550024601c1a40540300310826240701c16441c0d00d400c41c0769900070303201d481c4440741a0010307540c80f100c0c80c0d0885c3e8100346140100081c6151286020991070307004002c1070b5031a60303031803c1400c0001c030b8074814626a42e091000c0c0b81d641080c451715035403a810080090409100251107414071303091560040d540104500104800d880109007110420382450005035180c00080d5080c659034142480140429401103240942c2c40d18001d440d401d03004800d010075100060540c0c1a0344c0c08209481c14140000d120741e60900304900580c0c0200380750380078080403c42d0300c4006241 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 446406627 1250 446405377 446405411
    0x613050105010b16020f18010b1e0c1507020f160f0b07021509030705040f090b090c0d03030b0312030115030506010c1113090501020c0109060b06040311091e070909 72
    0x240c00c0021030130031501d00c819403c00440e400e03d000b0032600045000c0071484c01600684c501c60007802c0900304169107100c00b91700c07004245821601d06400c0ca0040007500c584860005109841c00c1403040d805070182c581550483c201003070050800e402d841509108203480325001c00900442c3c0041859480d44d0343e903002241050b000e040006903200542d41c1c08030750114581d00080110355002003d039a03246450306c0004040719001c0c0b030828442ea540340b02600800c05180012600801d02c54000c1c540301c041280015100350030340d90010304050b00da6842e05c645480401000254003119040b040c2c480da19034070f40b00c001d009410b0ba5000041e0501c0c002c12410350203003800c10351141d00318901142c0b055212007805880d1400d50300303200c90300b507442c01d001010680a101802c4508103290000c1401240340c20404195141c08801c280700d000b00700000c00000c1d042262003c440442507c1400c0e00780e451400d1080700c41520b21009100100702020410183e5000600609a5074944d5040080f4030b500260303086 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 446407877 1250 446406627 446406637
    0x10603050604080711100c140109021c0c0504020309010212071701150c0c030b15041406010c0305070b071806030510210501020d1d0d05040b0d0e0613050105010b 71
    0x305a800080116020580c09002040540d000f003d082d0301e0440d50382d01040f03032090040c0c04031000410700242042080076600d00042800d074000000d000b0001a17800060004030300c00126070030b096201d2002402c03c54002490002060f00a10440d100d01e011582d0501039444505071186022070b070000201580c3c010f6060403080709407440c10444503800c0c249c405801e5034060bc030340e60a1010450354680014641e03500900514480c4c0c016184a041032528040c116100c0a02148150b00340803401d18a002541d1100d98044801d20f000700c22020729080949407803040040151003c0f0740031040160464001c2030061074400d05010100c962503860504404035a01910100c00d4101115002c1101404045050f00c03110361a0b44c1c02c4007080b800395500f508983c804202c02c051030303844400d1701c00d6a035195081c03c0c004e0442440900420039001100501074840d501907560004404148407102c0c0840c0e070701c101c80c80b000e030390200c403c10f0514076010b049a0a03034060032a90f540c03c110001c50f1413140755069507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 446409127 1250 446407877 446407883
    0x30124060c0b0f07090509130c170a0b100b0d050f06010c0b04020f0a0b120f01090c020a0b0c0906040b0c1b150306031203010612060f03020112090c03050304090209040608010603 78
    0xd85522480c0320f48141160240401c4204409a640410313140d5640400600030182003404000c1c0420510b000d92400c01c0ba5405000000e5028000045210000c038000b07440c554000351401040d5101401c0c0c2e007101c0c000380c03c50390035a40c01003a020703207684950b40000e018030354031078880103940e840d2801129407910091005203d11110b4001c580107090610305001d242000411031303c4407546548200c051500480f42000b824140482032120150246600c08d01402d0240c030305014029181c40040d6480301c80001c01010f4a0092000405040c4c0c030718240c900c98413008203400d0766656910b000900c07a07081640c11400300d004403902d0301300078843c0049104a40d4009402000b41104070b2000c02d4503604000d04050300340c000c1c507884d00c0f0100c0d007440095010705040d403210b10810050003080c00c00c59040d03401102c1c548221070030500150ba0804942e4194042e418402300b9040550b1902a913403165950008103207110210700440d100c1300c550003070403e802c82500d08000b1b075a610203099080e41c80901c005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 446410377 1250 446409127 446409143
    0xe0102040506071506051e04140408041503020c030a050c0d0c050c040906150e040c1d0f061801030510140103020a151707120c0e030d0f020a02030124060c 68
    0x8000010204803130385a0080300100c0002e0819607400110f400c3c501c00360408004052081c8034034402d440d09100e991441115890b026559181a641c0c0700080d20644c0500e41015951842e940c4940c0c4c880e404845107003107a102238a89a00040401814a81008203030b40c202d4002c0503010041140724500e042031064010009200d4500f9000038840101410501900d41d107031501503c9101380d501c04824802404032000301492450141002458452140c000c1340c3e0784062503c0360030314015608003040d080500d40700254072549a41000580420131034004c0d00c500c2d222000000705209011541d07880c619540701050110090788036a08070b03aa042400f009501101c880742c284003108030b110b49040c14a2013410203003800700c001383c0c0c0f0250050b000c49001c1c00045203042103008044440c002c4400f54599800c1a0f124a0f07030301c01c0042c0d11401d46103a1401001b0b146c4942c415164800c000e168178507a00640200016102120180040500186429040c0702c2026000490303a02c0307200200012500b002807 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 446411627 1250 446410377 446410387
    0x906050f161b02041803080c0304030203041e170c0f030a05060a0906060314010b01020d052107021e010b0a060206040f030518130207020f0103050105060412081b0d030e0102040506 79
    0x4203440207000071042c00703181140c203002c007001a200d07803241c2050701c1d207400034100304422a03282c000e141090003000c15030307200350520074000041d400009840990b10300c031084a2078001d1201c3c81c1e46445e956980f1062003c005441c10b0184000c001c201005034050643c0e515030362941240038181e0790b01240b60000c190350700c501c00086038a100356001c0180140f140c0008a891503490302c56410f5a041d88000c281039964440180c1d11a42c2c0410000c650f1400300c1c02d15600340b035a0b90012003074032007207110250004451003001a203858401c0c80302d00130300c540c2145208003000700f51110500038402800340c507001d440c691501060f80760002801e94455030b44050b001c1541d0b202da9a0455a81e0000c8603900011651050140340c076030340c4e00c403000c00e1407519071000507251400c500400440c03071070b20a016418103280c03000600441c1c1302e510480e026a01fa00c2c666032108662854590f010703100c0d40c02100c1220784004511b605448000c1840100416580d0f000e01c4540d0741e44d00c0070b1b4201e01c00d5102d92640104100300d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 446412877 1250 446411627 446411671
    0x30f0203030115110717150a0b0d03030905010f0203011202010e0a2d0518070e0409110607030c1a01171f090201020c1509040e0c090601030b120f010906050f 69
    0x300b00403114244c0c04c2035a0241e50381c0d42508103641c1e0691402c81d0160450640348103040d1003841c2c07442c0c2c00b243e10319080c8403801c060401b2412000c42d800002d010161a8480300d4180002504582c807a220340364421580c03582c4d43e9402c0710010700345100481c000342841031070b0440c07840c082100700306489203c9502c01f100b0f400600b03c1050b240047d1407101904d04400400202952403805d080540c4280c4004c07140607161410300101100503041507240f2661401c00c094001c698408043c1035650015581240d8034920381c1002d9920104038903004003821880b0b541342c5c00740b9500800e010304a40b20072542484052918404544404c000c40c603280d94010768080924510391980c00c1084458010300580312081814008110a450b0880007551404070008401c0e015007000d1040402150140e40503040a5100b00f00249040201a0080e4101034031244141d900d6914440d61810808500040f02c9106a4580029002e01100c850a607003007403500300018040342c0310702000d600c210704440c6107403d0318416107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 446414127 1250 446412877 446412887
    0x51c020a050409031112280e19180b0102060924040c08030c0109050705040e030d02180603070c060507090302010c0f03030e010e160501050a080a090203011b0c030f0203030115 77
    0x24402c4d001c00048a00e9a0042d07441800808200f810130f001113951605140c00005040741e038604030030300384103201e012422030507402440104094000c4600e5205280441ca0110b40046160458107108030404124910f54486174008002d6150a0302a10000c0d42c0e001015511150801c548002041546050442e107a52030010a03600c00d02c207003000f140e5203440756642495a04441700145440c0e40d1000d0010501504014000060100312800e02c002c0507281c0b03146499005000882201c150041108605801114662070298502402168681c5822070004110f150101c5050f14000d00d0306c0c02040b0500d00c00c6041506072038060b12a4a000d0406541e01c0c4129148040142c0400d0b90b545500b8100e0303c428090814608130541c01401000d0355a054000802520f6001906001d01048a5400f058001d610039500110805001400308024004240900501c2d0320310000403044c003440040a540040c0403a01e070074040d6441c2071021212500580e500e20080c05900d42d03218408000b0002c03d8891 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 446415377 1250 446414127 446414141
    0x10510081306051905011415040b0f070501180515090601030803060d020a0801180201120b090c0d0f0915050601090e220c090c1b0c06030c0225051c020a0504 69
    0xc1303d012184418494104422602c00b0f800c4141000d10400e1103408525080742070a00e013101050490345400c0c505074054010784a41d080c0e48401c034102203850001d02500b9400428201a00f46407134441e000349103017994035202010b94450382c052455001c10300100c40017642c58107032540040360501e9901d5100401c56400d032070b00800c907841054154041203107003081c01962040c0030702c00c40e200503c95503840050003000000d055a84614900003130358405e0f59a01e070a040e005003255520136580d12081000704041e0414074171000c040e40c00d08602d002002074005103d03522000741e1b5010851034803254011142d01e4058841c0c094500f207458003043d001d05401c601d25040040d44000000c15626903a9082c0034482c0d42d521010703d076a070390044150300705d403c401c119040c85800c84c04080c030b01804d5a075000032100700c1c5c040d20041550b50742c846d0507001d008000035070404c15004601d200440c030b00d00038a102c8800d80e026540c0245500c00542d080c20440031224042250f00801c502c41042c100b90a0000038144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 446416627 1250 446415377 446415391
    0x7060207080c070b032418090f011103060a05010c0c0b1605060c0702010e031504030c080f030406151e03080c030f070b01050a061e031a060f0301051008130605 70
    0x4100704a0042c204201c404010b0000d030301e50755241d01e042415000d5151030b0083c0210031001e019200c0c1241d542d410824442500c85488800c81919540d60482c682840d020311f50100c1d610b4103804081420030800070310310428088032800c1680c0d07110b000444140e81031b260001c0490180190a2002d0000031026100d601c86441c0c071516046400e03103a11f45489030558a40c0c0c1d4030407000890800b5964820342c514102034099005002c1180d118240241121000f000582000904000c4078104052142229035429207100c0c1070f034407030410f4203108008050350b01000c84000700e05540007401c04c0300c101c0040c8041000740351081483d803464179030100340d9111040c1104c480c08100b255120000f80d280181c454140030b0f00203080310350f041c0000e12940e021150400f03c14000c0a62081c0c41860440c541c00382100498500400d410b407503252711191081468440707561022020840c40a0040c0e6a00618100c90b811142900308401c3c42c00b0581e105941030f5035844441500d00408404512550002900214 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 446417877 1250 446416627 446416643
    0x1d1f0309020f10030605090115020303040f020d0b07020f070e070c02121005010e150301060308031f0e07020d0e0607031b03021504201806101b060b09180307060207 72
    0x1c00b00001440115000d502e040200b0ba489030140b2803424080340c0d281c0903006020044000e82c607080006542c84c040108010004801107110304210744680b1403913013075554001c20707110082c2000200079440703030115244c900091251410024910402510260041c0c00ea0786584110610640900021000ba600241c0c0580300c1d1a8600c1d13510070151040341d0080082c120220b609041c5504802d840e190b0840c1c9143c070982c1000814008134042c203044030f8024090a0740801e0341c510b960311660801c189a80400d81a80510081210743c6401289840c0840010b958903040c0115a108000560080c0c2002400041031070040984950f00032149040842c040d004540203407071880c940c080031240031103084568144c001004600e1a401c000c3c070150303400c0211505125802206007074000124000c10b01c41c441c0f801d102d09030300002e000b40000030031354090b02000b00814a00341405401f40036240300e03503030048245c440000c01706605502103a0340c0c07070505405107207828030031380f54800650401c51050318448 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 446419127 1250 446417877 446417899
    0xf020102130e04050f0d09091e050702030901020f0114072003280201053c10030201080601081902030c040b18010815090f0c13061d1f030902 62
    0x480060700014400604a42d0703140c5400d244c2142018011513101c0c0c00ba50081c802540042d801c030b1004415074094120004105445500503090b40702c1818a00b2101443d18003406032859001c8020135080d4401e030229400301044030301103801c0314140c0d0300b0182c82080c04c6011580c4d00d4440e08000d0340070500c2803c42c3d020b00d03142c042031a0856020030107d1100c000e04455490034070842041500d60080f1074002007243e0700d05140c1c100c8070310405071160450381c0e2121400c002c0258108070004a0304084070b442070030b6858120802000b030b2030a0701040e40440c1e204c0c0c00113102c961050f100140310b0f0b0101d20b4011045101415030300040c0d003014010022500080c4004100484040c006d4850590442410b58410303203448005043d10710054500119128580d4441c80c1c1c54559190054110715440d00e0720100d651407514062042c05a80703450a0034000c103140020b81d01307504c0b5880c0303010002d81400c8185801c0c101401c1040402114407000340f5201c0c4a0007452003240a984000009030015040b40951 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 446420377 1250 446419127 446419147
    0x30d180c08030405010906090620390405010b07030c0c030b0f1b13120c0509010f03060506040524121c030608010207050c0d030c05010515010305071e0f020102 70
    0x6240c15030001001a0300110302082103607405039400d0000c080354107001d8815802d003000100080d40000600100d40c0d40200c0c8001101010072516010f00c0104070048019015140f1003644841c0202c2d084074088a11303100510300b4902441680e04072660a084a403030b02200d80d50942e08012a503c00f0354070b0b00300000e800030100b40110205072140e0400c0021542034a003140300f01c0094040001095040141031024000b01c1c10100344410503103079040101c0e50f408540b4a42001ca00c0b107a038101d00e0b0030500080000603810500002001681d1240317805000d655528000d01048030000c0380d56040031a442d5042000d4000440b21384010800060311103084a42c01c0c400c514500310308030003c030059500ea6054404641e0380b52141c6005000448001e5203407241540300c03540d5820202a165100f540d280c51000c080600903020301d584030354000c0007030105140c44003040306502802e00486000c0b900300000590036622410690714030003101070f104503851701c690300300b12074460b9440190700c1559400c1281c0889 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 446421627 1250 446420377 446420393
    0xe0f0a0803040608181509100e1f0605040207060b09070c0209010e04060b030105040503130e040c03140a060609051608240409050a0c1409070f05071a040309030b0c040503030d18 78
    0x40c10307010f14401c805801d05e000028500700041719070700303107027850815081c1e49000302289030903402010507640250f402c0d2460100340107000590155900920004400382008426005003c0f040b030121980d1700c2503580c03281c05407010165000025840480300340103121b88204007130619000340c0aa20001000c0f40b0306404a42147d2007a034007911281c0c13001c175051100c40e408140b048003a0009a542c5542410241d03244030380e0b0360b45800001d0400106100c0101d42800030002c2d51041500040c05020190362260803200030401550740203040c0d80030b03a25180c0d1a50103401402e018441c030f41c030103c0d40d00309001d036800c2c00d014480404a90103500c0d00b0403100880d00410401d8905401014210070640c90522503540007c00741c400c16008200c0c0c5810440050b801c124168460170f42c1b23040640e9640350900e06581c8482e02103140f500f8150482c8140010315500200d003c003920321842d0500c20b9503c8040f0344e07001c0c078000d500c10150b25510401a400602c14990030000049680d001c481541040703661b50344079 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 446422877 1250 446421627 446421643
    0xf020607051c060e0709050a05010302040503030d02031506031f17150402060906040815090604080a030c1e02060a0e030c03090609131b021501230d080a0e0f0a080304060818 76
    0x102150411f10040c5400c2c0090801080c0c01d080851a2a1411000c80e0f228050b030101502c1090340400002d0508410501c0444201c4000340101d99038500491001242c1c400f54441541c961584100450130001102d25144110740450041200c2e14900d4a121980540100b040360010b00a0024104945829015001030a088400b5001c1141c44003191070099000900890701a07000c0d1041c0000f154440c0c048540003000ca18011a0303d01089900340d0b5403035041028810554291429820b100381c0c042141c41c06111141000d00034864072030412035903400b030040c1c840c0890b041017164085501d880801080c0c19100501600981d03a2000065000c890010340341480c0e00d0034507580944007a80c10302120b0300e8071902034000c0156505080ea66108207543d00002014244d013021011031a5a1740215120714130380c41001241e54895603c002008440d07027128450080607160320100191070081e00d24070555040900039418a440d08100311094800502409240f100c540313110094503800b440011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 446424127 1250 446422877 446422891
    0x3020f040e010f022d040321020c150a0e090106090b0c010b040608060403081b04060f050c0d03060f060206011d07050f030112020f060901020615041d0c010f020607051c060e 76
    0x170140300b00c0303100030690980700c140460703c0d010403040c000110108050401211410117840004881c003100780c0c50445d148940c550301140d903c0280c1c0402c1000c8000b00b0a0700d5590b500c40305229a00b000340305411a00380240c030701003500d2840510080440c140581f940d0110a000032400005010100d0102d071b80942182022740c00550801c0207240d04141a1600104e0b05038210402c8000f07809180707418016406404104002096942c2c2240d1182050301c0640c050b10045d220682d440c07081c080e000f00418815a071599201d40800100da60010403603c1c125140710b0010b8072204641142c0c6000b4400007010320051280034802c007032080b004480130314060501e54508128000c001d0040142042814203054411f40c41040b0001c283d0f40d02085064010b403802d880340c418244100e0000c0d024104590300c500d0440095001461000381c0000d150304031200c01e0302d4004618000b000100e071290300844001c004140c00700980c0c500500d50380402810781d4900790000030000d40b9594159858001a2418 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 446425377 1250 446424127 446424157
    0xf180b07050d020115150e041113030c080c090a050c0f0307020303010f0b041d100b071511120f06030a0b0906060114031b030a0906021207030f0603020f040e010f02 72
    0xc00050f40900c0741a2100034a040c03020074691501c030a0004026643e070703501080054070390a034250358485c0d41203a640e080e0203e68243c1c0700e456282c02e0307401400c001c1c8030544414201010000709000089031000042e10b020b050005c1d59900c0000e80d001601d4050100000b5920401c942102c9604040146005047e242d01440c0c2d80d501d08264107000310595000400307251010003040010880b2210700e030141c05081143d11404c1e50f98440c000034500240d520148001074001552010080f00c00f04c52070301036a0041080110001b490f5500c0ca250092901c105401c3c030690000c40e9220a004c150703564440801800c8404c985a10307664004103a006a440d4011944484203201c030668000c4c10317403030b29800c0c02d01701e0f00d0644c5403c484001400b80c090120b102c0c004400808140030f0406604203101540d0017020555840b0034051500e10012000c8444800007450110a07200725000350088000b01e9800410200c07003000f1404c00c00c0000c040300024100190740e2a03808000b4014280050080306480d1014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 446426627 1250 446425377 446425393
    0x40b0c0f010c0203160605150a0b0406090e100e04060209032d1c0e0d0212060414010506010e011d04060602031309020f160201020304030b0a0504020f060a0f180b0705 73
    0x400d082d0366110160100307541051218091480309070f441000380b103030840c00200b07a80e290030180301c100c9170f225180d150300003100c0c42c40825207120700300c010800c9490564480110350b944140c0142c10b003005503625842900ea01c0000c03c20f415200100c99041802403078010710340301e403200009140041c05801560505550715454100c49500d480c41660155141d0107460b0144140061801d010801452507083c01100000110a42c940c0302d1700041c1c199014002c140c803003101407003065540c00204d0741200c600010b4026045040d40c1801220300903501a10784200002d41c9a00541c3c6620110010348903060240003090034a940e103004681c006c0c0b2554014569882242d1030b0241880b0842d0842d0140310b0040200301000340002d8110340140f02141b581c942100e40c6440100e05600c42e0380d001610003440d440034482c201d40b90754015401584201d81c0c11940d000c0110900031140940504007011462074a42402210300038000e004401c0001c0c1c15281042d6220000800c150308140825102980140700b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 446427877 1250 446426627 446426653
    0x1017010603020f0d0b011a0904110c12160201031a0303070f0201030c030c02070b0a020307080d0c0315051c0c090906050901050702071a0c01020d020403060e0d0f120908040b0c 77
    0x1180424250007a21031444c2507110b5116504a010103204403560340881044034030584030140255460407400600902440c080650b50300200e4114070f40c46010341c011400c14884061082c4206e03010f282c00c80c001c94603401c00b2134006400600b104484507171450b60600310070140ba81c00740020b1107a90321a0108000c1104507000041c115400c2d001d0f64002d152030520840b841540005051041ba014031410aa031444840b00c203d0a60181100042290901082001000020740c100341f621010a640c2000070304010303c41c02c0301d4114280305403600b0a1703613030584050040c241c00442502e03030300030109a10000d0350b070200d240403541d07454801c1e07401a9941050000c0391000380203a5401106a1009104050410a111602c40007200078100a03a0001808074070501c0e003034050361081c0b00380800864a85940f403e01102078080300c4028080b81c01002c0d010304610340200303c504ea049401d0f65442044040900c150030082c60b140c3c1081c1c0b06002e051100103a13441d004402001032010340070281c129568000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 446429127 1250 446427877 446427889
    0x9040c1205060910090f0b0a081c0f051c11030c040501080f01050105030f09010603050d0926120d02040302030a21030203160e1c030f0f2303101701060302 68
    0xe80010700c240f52100a0111100c2c2c2d19074613506550040d6000601000e1681402004084048000750010300340d100004210b840030a04000c1c140100b045004140c100150446000846a1203640070070342c107020050403000300c4c542440f42c03c895032100040c2c001c00300c0c0d001c41c1a50402c560002610034005002c0c07180303580c80503c850308100d517480d00a51550510f4006000c6000c010803810103201c040e40080c013440b209420940c01150804203480710580c01140003861021240154104c10407000516000a60800f400c0540d040c451005048484100c003100d00c0564859142c0301100e507001d01010001d40e4041c0501c03601144141540301c40e0710207130414581c169403074200c500185403062040080007058610312050003086031a000c1c01904810001a983d2140c03ca103402d031000b04403004c070041607004200402c84085540346e148400642070001ca441402d40c00800c3c002001403200340c00100d02050217581c1050901c281882d940f612150351100d1b8005100001d10280e46444080083d4203200c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 446430377 1250 446429127 446429131
    0x4142716030b041a01140103060603180303020708120702071d040b06090a02131202030c010f0f120615031a0d0302070b030c0c0d0504090501050a061706150d1a18041709040c1205 78
    0x2608080c8400040344034033040b5030800480c0602850b800140510030090201c046480e00700411071064031f24100a80001d42d00c8500e4021182107040c1210b0b2400307842c0e030100c09035204551044050015030380d80c4045c094900806800b041c2040d80910005079003009140b04400030b001c0300d00b002c003000c2c0c050b40100343c03a1600c042002414041968034090007130b030b805400200f56800500300703400b2880f20380c002d800081c01c0561040e81d20442c03038203c00f40110b9050f00101c150889800c807130300d041030a450800400341901140100580d1040c1c1c4108140c104103406150b01c596128044c03803c2c01d801c26419424a0f8203191100005900020184220505482a20301400c002c0d900c0f08249803e004015040d800c1e441c00a41c43c1c641c0d5000014250780d5445994150201c92001c126180d403584005070015000c840c0c5030b8180b4102e00c000000d59401c1c40c1801d01e42c03407030f40748400c6a455148c0352103001221004507110360807c6420040d42005032114015036903040c0039a95000c0c814221142411304880300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 446431627 1250 446430377 446430389
    0xa0605060a050103050f13081b03030640020702030a0506180c060a05090a050406260c100c0309080312070206100f090b04142716030b041a0114010306 66
    0x40c28086c0013402034514203507540109540c2d030303d6540da160b030b042c07180c0c050161a000014040384064100320701c10010000d18007450080e15a07107182409a007a40c0c49404184425142c1c185000360102c07584811070034081880c442041c00103207080401d0700401e041842500c000c0d5074990080302844100300c1040004400c0c0710f17030394001e01454626103000a91602c03c889042017040004a0303614110b60794804070000404005000300300b01552107005100310800410401c0076114140408490718402080c62014198010b0064070030b0b409030403003554080240003050b0100070802c200480e10764003c000410004892841c110454500303080700903e0f281c0000c203950983c1e130b91490200200c0503003410b6407013030380e1a0707103408240c80e1403000c04900141241072205142d8000300701440501c050b6180c014001c0710041000400d00170488548581d02e8154125654000700102001c102244980c205140c00a05c01d07a0010000c42011120407800402030704001e42d0340c418084182110760b010301c00c00700103081d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 446432877 1250 446431627 446431631
    0x307030503271509150f0105040b011e0825021e0a0b0117122a0d170a09050a0b09060106090302011d0a03050a0c0e0112050604020d03020f0a0605060a050103 69
    0x48014080362189140c500c0f000503031062802050128206004400b181c401e600b074006558a001312480c402c1d61428031406000300e24100b5032681a5100d50120024401c24043c051803611410004852504000380380d810740080c0c5040441460800550449000540c0e40c01000c0d40a980e128001d40500d030b009268085034442040301700024004580c5904680030071000e401240b104900d81810b20303118100b440c210610015003141e00701c503400c0c0e19600700d14600b400c00001051507007055660345030960200e804110340070380212031f5141052483d0760000d016070011603181d40580e100c9140c08008401220081c454204015010300d04020311801041c4c68905603c40d585103400107445408044050000c000120540010949850021200540d80300007140e001003e0380c1003100c4409100c0c000d00300c3d00e0200000010322080d00405504074039030003d02916040d11240d0070070240291581c011000d50080c105003280c0100d0520580f204240503140200300d0f4a000700401024881540020f4141341c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 446434127 1250 446432877 446432941
    0x1501080a05040f03180911040e07030e03031914010905040b0a0225020301110f0c0105010b0901050f0a090e1905090a030215070210090c060809072106020c0307030503 73
    0x40c41c451540f500681c040c00c15049001031a07620050081698024400040c01c0c400c0380b4051216a40040c002c680c0a81500c480c0764076100022029034030401c0400106500c01c1c07002c1400361a080d550302e83c42921580e00001d0941400100c0c52417040b0076400415040d50b642c00b044144a040800280d01900d00c24003141b50030481d0381c040c865003a8908c001c03141018034240040464609610000440349003425564503011040900042a8002a000280c2d0b501b42800080d0641d00401603614108050719481e08003a0003089200440d000102d404080100780100015a5a523690340b040c00307142c4c1e40f0061508400c50111a405551002d441924035600008c0c240010990200780603415000350f03410401c1030f459542c802c0b0324200d001040000514030701004d2004000458518400b1201151a019202d540720041140c450070144240150400d100040c8181901115a094101403040c4801070a02a909001501e150084c1000f140070402c00001e010104d10882c0d03680101c000c82440502c050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 446435377 1250 446434127 446434133
    0x14030f01050930160311010c05031605120a0b10020606091f030b100e0c0702030a030e030f030c0706090b04240c05030a0f2304170111031501080a0504 66
    0x83d0740c80d800c03101007140400d0001600058040084449518084900740d00c0301d50000d04a04800d6a00c1c8049001ca84c10380c40c1e81c0f020722418007402e0b80c2002c2a0300ca040c110758584140341211091246103000b008030030440b903006400700d066114011851a80001101e510005c00e10000b00307001c42102c1d0940d444039080061030750b14411700e10b030b20910b040c12184142c070146101e56188101900020007030014541000100903c1280c0b0307600711580045480e1032921080341010a9210318000603400d504418080c40109001e807603548841d060140c1100c81020f510000b860075500802607855458000900400c142d5038810800c030050102c407010649410300e0300030407480703c1580c44d0135200c0284050082c89080c60051240b1810380d41c0107800d4a54890a0000c01030503646005001c402064855001c00c41d406407038900040444500700030f0070b180c6401c100200c40041110040015259210211b02142148500185001d25a0b40c001080c50008550000d00302d01030041002e00043e180000300004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 446436627 1250 446435377 446435383
    0x3010c080103052a0d0f0f0803091e1b01021903050d050f0919050102040911030405010c050f040e3c090a080307030b0f040e030c01050604020307090324050114030f010509 75
    0x900d1304201c0d40100071685520b403000c0d040c002088050b0078004d109040320144020200114402c9000c5001d42e0300303030001a0300590383c4603005070024049901c41c043c2080b40e1550100749501c0640e0500440c1c0703010081c000130030100c96182c40b08400250020a03505813000300c9004254000099103905000d1345080d07444541c0d250301c81c8480500032140d84039542c0520030203604590107051300315000d024000c2104201e42d0aa481900d0440b030b00d62070051303188010740c802d100ba01c014020402544c0d1a261515200c40d1003404003418a2a42d84405080240e00c40000229884400110041814100100c8000c3da087c030500500c186000d400071032213a000990045d040b40d6010319141000500e9480e00404a00b141507418522a007048ca0015809000003000000d000030300603e00003070041d03544680910080e40400d50340705020400004c0c5c05d100182c0510288480001000c1c0240801080d80c81408240c50303081e41f182c10314840346124040241000d00c10a902e60a01c0d4000f80700311b040c44000b02c0e40e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 446437877 1250 446436627 446436703
    0x80d0e1b030a150f1109120a0c051e101106010e01050d060203181516050c0a140f010c09030c08061b0306011803080d0b0910030308130203010c08010305 67
    0x184110155048030024242c2c807078441006030601c2003060300000591002582d10220206d84a888610408020710100082600043e0ba00002000d122440c0c0420300140030b04808a004c404080401160240d440c0c6204d003111003c1140d4502140d0000c1d0398110b424510103030850500b210080d4014000d58952195003200c0c160300020040c0e50340d0314080d0900d0155411b00d00f0280e5401035030140d00c5d49000f1402401d0081d0b101d0300244101c20f0700100291918440c0d6205140b580d0000007810000c143d404244004204c1b1400940c0c0a44142e0402d04c0d0865203100488404512403a03001e10601685c01000e002920500b0f0041051b42410300940c4005401c1444148480e00f0010005019903c61022145403401e40008070780160348030700d041c046680060b809629900d00d000c2c515541480c1100d000d601607007a60300c0082180d07045490484181b00004c0010b003a0001031040080140c400b44146200040259254483c0b5410743c903059080c101c4100d60340c00c0b400701401c8081c580c0b20302980d400b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 446439127 1250 446437877 446437883
    0x10e06011d06160b090f061f030807030905211e031602060d02040b0d1b05030109180b07020d1806141b03031311061801031503080d0e1b030a 62
    0x5a102d07003d010304501100f6200000801194501d0107101d1001c400003441030400d000380b400e136001e90350340c2c0c42c5240c00c5d046158000594651028410804501c044000f841502d00038038203a4412501c1d800400e8032a02d00200c080c00c0c1e030703400c2440b810030030b4000d00941d1085807000b945613160388050f44c0d003140e0f20b0140c0949040d414a8800c58541196140821542e40b808510000d40d01c9540d242006955074001001882a89080c0f0198600004119121081c3c01341180c440c00e0559013081c2c41d0400030819003082140201d120001080403902a9071120f1040c0c07140c1d801860880c0301c804008001020302d134003059913003a44100900455030041000c0e400d60004001041d1140703003112003442c14103824083d1007514000001846050600d9968000301c9a0258001983d0701000d14203001644c410008002440d20f842c41d00c482c6c840d0310a41041c0740c03d8001c10494a0191b4a0b9218880365600c00d903142c11001d640e035554220b24000601c07100d19103180c0c0580b003c00700000c403130129442e042c400c0001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 446440377 1250 446439127 446439139
    0x60c0e0f040228180509100e071214090d030e030d0903020312010e0609100605030109020d0f05090303150f0a0303050a1803030905011d01091505120a0203010e06011d 73
    0x8402080c0d4405010800494034400d040700c00b49940001d05080c40340016884d0510400102052034200028002c1c0141488001c0507140f5150500d1440d404401616600800c28407d0404003440b240d0700903a80121030002112506062403900d040c03524030070700024800d25080894200c22484040180c2c0e5111003c0381010410394030a03d0100e055214505030031071031f04e03460300002c00c180800c0034610344181c80507542d8680743c0d103503140b0103814050940301c0e01c000984d0401c0140722407070851300038001121401101103001074161050308240e402c1103410410320b80c00401041544500da80001c40c1200d01903e51281d900c40703200c081240c940e075a00001d4103000d4001383c50341c480c40c41000490362034010351a90241035034891400034501540761207424006600d501072804cd8482d00c90039500e034050161180c0720514a008900c005c0c20300a031043e030b028803d00780401400d20702101485449616400801a0b5940c18a01c107a644403001600207410400444c1e4201c4041c607a01b14904000c160880785 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 446441627 1250 446440377 446440387
    0x160e03010f020c0a060509060405101a040c0e01140c0312040f1e03031505031c03110409091703070c03050310180e06010905100e181207060c0e0f0402 66
    0x11a014006403448a08a9072002540d180c0003c00407803a00741c07080c0318003401e200c0341e11030347c900540d186400c3d5400b503e0340d0414401d00d8259061035001c42c182014003406620101809000181242c41f4403403c403000c10001c550380200e40da403200341081912036100d4401e00345440100900c1e52801210410b01102c010030001c1428004501c00110010b540310541d040d00d00c0145c440c070305900c04500c0701140407030304081017101545c10104030081528800340061841d20b8500255200120940d02c00c0d605042d590078440c1010510400100003400210078046107054051500d10222505030b500030510b00001c0c002d03c5072803a400200c04400c6605460002c1c0c481d140c40120299400c407a80c800e8600b41622945448150752640200c00349c500c0e03590a44440383e90303c68005068030070031184142466000a000e012032014110000e4000d80e0b20021103041c1005180700303515018495000c02c4c0d500e07202140141c100202070080d071404016500d0074140c81d40446002c10300420104c804d140c4a503402082c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 446442877 1250 446441627 446441629
    0x5091b1c0b09010204030f050a12030203040209060d0f0203030d0c02060109050c0306010f030e010f0b091005030303160302071e020a0812040512010905070f1d010503030f03091203010305071d160e 86
    0x117481c05103401c20903200d2050024500a50b65400c209421501a01ca10302107040c490300920070b891145030013030034196442e5a000100120201310300e4085030286102c61410f00540c500300b026050800c6403402c00148041c42e400041d01d03049059112908607424102009039003440c02042d42c0c0c02940a08018200c02100117080e00500f180d035540340103541c608021f80c9103607031b80b44d0017801c111042900d0041940e00c2d40c0705600001d80b0740e40a40760b01503100700b02088110342484010400846c1910700142400010703591a004a408650030100c3d941c0c20480300d40562401410300030041044500403c505e5241050f030f1000e500442c441d0a110b000d8001001000700703020b400c21070900d5031220a542e10305031501c1c40c45a440100340584000c241003030348000e4001c8405000745060301c030024000c5003084100070481100750b00050030000ea034041c04a0000071441e83e00c024601039441000900811401c0003001d09114001c442034988104074038050040032804107000342000010b038034000b544441160 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 446444127 1250 446442877 446442881
    0x20c030619050c0d090b060108060d02010921080301080705040b090f0112020a15020a150c020c0904020604050a08030a020114010605070209151908010b0a032003010f05091b1c0b0901 80
    0x841122a139082c02444010440e40029940c4220303026210018142c4030201032014100c1b181000a01040f03004406102440d00c21a40341d600f0b01d204a070417410300303040760ba502100b40c0080e84006c03050350180c43e007800300340303024000e81245120948030300e425490800304940101c041807040c200e403001015040420b544604041c0d60140c921101d204442c0840301070001c0d5904c0442d00180ea2180380d4020800c00140f20380100401900f10340c2c024a40407100004203c05013a0141040b030740320404001c0024251106030144004009030030103103403640440f5a004c0d00751003000382050b41402050005001c19900036044d42c001c25010703902c1e5019a80c1d1102a0320b000030300c3c050798603409000b440e110700c0c07804480541071096580d020000d02841d81c00d081400310080ca1400014642c45402c01c1205205504500313031071000c0001000481d03014034041050381129002e6a411802d81c2080c40041d0540b80f03100d0380a40c0480003508d0f48450880206002c0ca0303005c103071000080c0708049400120310020070075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 446445377 1250 446444127 446444137
    0x60b07331802010e030f1e0703060c020a03110303160e2d01020f06090307021324050f0906100c020a1508040b0a110915130b0406020c030619050c 64
    0xd40801203952501141d14100314810001ca000846201a40049003808614105210804401451000d2003001641c0c40a0b03a9080c5065046c4203030300000020824900903d10740e0141d80c0c01400701c0c10094140241419204880d0710025403040050000000405040b10440030300f501c1c1c14003160041c0000540404040ca104051a10f6800885069081c0d50640c2e000300283c00d8080303409030010600407540b03a85045580f12600e400c1030003204094181050752100701041c02d4400161b49d15404042000012003160440007818542e40c180102e040c014851018034400304d494090500c1c014001404103840c0040302020081c0c07142070300302151165403a0102814642261041c16040300e42c0003441a02c0c200c500342c40c501e10301404900d08060740d10504800408040300c203480c100644e024000c04a03241844414242c10400900d521020802448009840ca5000003a565841c0560003840c000c07003c0903062107500050300303000d4998420406200281030000d004519a80c9040c2440158018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 446446627 1250 446445377 446445473
    0xd080726070306060f03140615071208060a1403060c0d02040b040305160f030f020d0309090f0c0f0e13090f23070b0a020d0809030f0a080a060b07 64
    0x210381840310031901600403000361203150340c402a042e500448100c040c0d40380b08030003a840000c0580030070001c0c1050441041021602102c1503c1d003c1181c0e510701c0b03140208141030300050b03603900510140d85041d10b5450001d040d0401c00c100a84a00800039403141e50190014802c0440044c0803080c0c105550141c41c02400d0100f891900c1c3c50f0389090094942920341d214481d80011120003150b680c5190100c4801d5a03080100c1c2d488051856080c0950110900e0055080c00403010000903058554020301c2c0b1030303502d2100301050580c0d00c010060030903003000e0503030001e2103140080030a541e1180181000003030901c000210383c1000e54100340d0034008000802601050100c106490264541a12001e00c01c051404940c0038942d91803a808160048958500060700301d1803110b03080c18810800140c00c5071041c1d00350307890410741810840c000d03403114288402045540040000240d690310031a0300614044500c103142c81ca06680c2c030b018003803485860081d072000c8622100d41d0744428022204001e0a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 446447877 1250 446446627 446446697
    0x1e19050c04060b03040b010f08030a030b0102032a150610030b40060303050702040902211005010911040506031f030f050f01150909080f03010902030708090d0807 71
    0x103243c00b0300d0f02e4254000c0f5402c0e24082145000001c00c9410881000c0844240c080512b0604281e8a001ca011f0582c110400381180b006004c08600010a000b0801920308241d819003502e4410242460504442d00c1202c2c60701b2200b0800c0249580b20080050003141d0f05103000500c0c040707003000142240341440540da41c00500c0760003801b60b0120800c000c00b044c116600d0840c5058240b03401d40c2c130960f5054040100000c0003408420700604254012525051000348a69440c0c0d040c120201c041d00401d00d02c0c52800e6010482030203404500f442214050301c4000d509110b5010108590030343d074411341c420a0b001d07240000024980086d0244100c1d41c01e20520b015501d656038a081500114904240c03d40d81e50042003088680507c05204c0d9060f2101d584510014507890081d60070010680c107102560007139001c01c1480090700e1820002c6000c0c03c0034050050716424081c1c80242104401401001d80f680007590300f591141d00324a00d2135200c042803a004c0d5480c0a00c10450b0314013090203840000d100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 446449127 1250 446447877 446447879
    0xc01020d120f180c080705010210050c0d0e061005010318080a17090d27030605060a08060405030408010c020303011802090607020d11010810050d08160209070f021e19050c0406 77
    0x300c0070070f028020280c041c400318040140c50b101d0454882c0400d200d5580035074040f4004a01808103504403e601a40c00302a16081058100d84041901d240801850300c540104080044116200314410040c10303081c6000c01109000c03c42a2400c46441d12000d000d03070f0340224075031203081d104400030f114075001d40132110301034102030f688142d441c0c80d4012218041400038000030138602e126420100000960500401e03030300c2c40c58451710001c1c10041c11554120000b660007040c1010200440c0d40201e200b04019a030b200d01e450b00c4c0e40d00b11000128180e0454008000400400701c803000c44010598001200580e80d58400e4001080d038440c0440080d003141ca076201030b2041c0300c07094107400c450755000e80743c5601d03696401c40840044070413030045a5001606500403404200418080c01c0c0c08108800304804c4840d2580000383c030031408881c0d400c001500c0c0a11180c5503507042c08562407074200c0c0d0001700242444260381d1600c0d0403060400048400c4070045c08002d215040180c101c50b0740d00a0302c1003201d9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 446450377 1250 446449127 446449151
    0xd02040b10020703061a030322080307080414030c030604060c03060f08030d0506010305190e07093608030105120a0602030106031a0f031507121503020f030c01020d120f 74
    0x41050340b00c1030b14003518042c114880420707110040303880417000402442c030b010f004a8600341d040c40c50a0182d80009d00d4910041a1100100001d00704075010b940c1c0981c45d280b510701d40340c07106103250b80d01ca80641c0010303107030361559140010304581040e404000801e200c0c51421044004082562002c0390741112010300040100c1d010001345005801e01c20280721603503c1714010b50998806a8985403201c0c04101c050040d4105580f05a50140e161000d0392007565070307007041100703075036070620807007000c3e01d103100003651801d481003030711040c03851410180d86801c40e00d0b01d4841c2c03180070500c9154020542c0c4c3c038203114001750900ca0301102950000d000c54895841c0d001c010010880309010000c1490030344401d031524588030503220000704004004000c22040682c0807100104054501c405001316081c00e0301751074400303004110389401681d121101e228598010040700071604683d150082d0480c030002960359902194550707000b0540d00302440d030071101d804404010110384010240c0c05140031164451 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 446451627 1250 446450377 446450383
    0x120106030507120c050307050f09060307110706030605010e04021c0e060a0b061e1b0a030807080a02091e01050d0608010b121203060108131b031b06020303060d02040b1002 75
    0x10782610b503600c490101a890f1100219150030b03003640c0120313401b840000c807a01c0c0728038000c1c4105080700c039440342000346c1d5102103006e82c5c00584060010030600100039100c2c4800308070920040c4051710f4248601442c4c01c0000c3c2c54441140d4840740070b990005010b1070a0410210141c1c40d00300d031900c00f0888482c00341c8100d52200429207080d03160b141081c0003001c0500d026002d640e40c0d8030501c1003034091110320214827003040d400030400b0344404e03001140c0066260014400c08101034069156000c042c03501080060200000400d46420a441031148400070744409403c0e4494425620000818540c00c1c030040e6250700420030382031003080c2044c1002c52400c4064000e82d904020607903542c80d4001e02200c01c50344a054141540701c003001d048c000140309604c00d4940f07071b4201207140300c840c039141403d48545403d074041c05012404821101402c100b0003028900305a282c2c0c11022040c0301850801400035202d1002500907813155007130040103020340d0b44a41c40142044002014a111640f40d040040c0d2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 446452877 1250 446451627 446451631
    0xa0e1003200901080a020309011b05030103050c01111507020313140901170303040f0c090f020c10020408070315060503010212090c040b0927030c0a0c0801020412080f1201060305 78
    0x1008426407034421407800606030595001010507107840509a0300d01000b0002500001c001008642d2206941081c20002100c180010102c40d80c40e10340d65819828000d1401d046045107604010505401c24a08070009c0350f241c0c02c0d404101d40410183e2a0480100d1841c0a885210501c3e2070300c0ca000000c0304040d2a40d070702d01541c07050b07279030845a03a40c0780403084290414050b2203034590020800500002c44074002004054840c290a08244c0e44130042c040407601030358a8403403a15800620f240e8202801c20000080340c200850940c5010300304846152a01d00d103100040c03c0e0303010030703241c011032400a80001000d000054000c40d1940310095600c0040300c010b503401c04182c0942100c83e02c25003000d0140003520300014040901c0c0391a8421445a040c01100d03248040c812600c801d00b902810900080040c0303414480140380c010f1759814a034043c0c905170b51200c2c01c160302c108401c1069015410800300c40580102e40325450340101300c00300045109270080b43c4212205440041003658055000d54 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 446454127 1250 446452877 446452901
    0x110708010917032215020a05030a1b050d021303150203060a06081006111009050705131a150403050601090c1214190b0a031a1e0103080a0e1003 63
    0x4001031010b00c0d11103881d03210660300c0d00b0480c0401c454801c0c6203401d908004240a2103910005c12500c1c00c4004c03401260000491000066400414024064100e000f100708a105070f0b40c603821202e5100700302801a2250117038031a0b8013900482c0010b60300100303449104c01180c2212a1100701d07418810742c440254411140b41344100310b03524021810a02c20201584510000c05110012500344601554042c071140400041481640d01c0030021a48030701860301568400c000420041d810102003089001103000079051f958070703251020804002c460b94101c040303042031310750155155400c3c14840345445207030000f0349a44030715800003a1200541d400b40c40c56480c5907035902400450380c1600340a90f210728440c00100807054001c240414860b296013901c00c800d80500041d0440c4d003002050303030f600320380d881601d8110b000c00c2842e030014882403107142c0c06442c0010040c0001e200c4100540200c00c18040601000300216109842a01036441d00d0304c0507400500c0c21701130003140c1d007006010700a100e101c0d07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 446455377 1250 446454127 446454143
    0xe0109090c0602070602121312050d0306051e0f0a03230c0a05010c0213180c03120801030f0809180a0b0109090b011d13060303020d0f0215040f031107080109 69
    0x150b41440807808006507625a4050100e6042841043e400754001a014600c1d500b040b56000a4618460301c1036020a40304501810b080d4490344006011035a140d1710560060040000d404100c100350704424034880740481e0000c40507078107500410208008c3d504000c010031a01540c4c0c4451b18803a5440442c0300e4203010071541e0707110000042c00010300c6036101e01800300e0960a130400040ca0071070202070f5298407410f00050780c0e40c2d10422142c4650240013050b1144102854180b0078001201c090592241c010704007210254555550710040000e07040c1e001e0b0403890041344a181e01d66440000c1c1d00d805022842c9101e4500706514881c00805014409901041124000080760700c058010700030310407416129030709544840300603212b1070032003810036503031050b1000500000d0882900c20080907500a034018008007880d050040c2424041e03400c01401e640c01034800d25040004440e5940e8415444030401040000310300d829141040060701d0606280100380d0003184812055020340c244034010801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 446456627 1250 446455377 446455379
    0x8160206030c131217031b19120213180207050109030e0f0103090b070c060b04050a0b01140313030e06070203060c0a140306030615010210090c0e07020609060a150e0109090c 76
    0x4650b0805507011401800d1145c900004d101d4080c000c0701456101000c4050017940f481145030b02c10b040d87c01a803d14515041d4042d80250a80d8420b94008103a01000d40440c036041964410071070403059072081004103a00c0c000103401d428590b405481085500c4402417009450510b006080c50104604240c001c1f0312001d503261003584240182d648994120341c40d01010b03202d6840480390311350700e664150785480d15114140142c0d22603200325481441803410005441c9800e10005010760034280d40409543e9090061004506000c949101010b030b15040c0020380d1860200455150b00030f61502940c540164420072011545820041000901f40e54410200f1038142803d64080e010580704181c0580c440000075120b55024240183c90403030500407a03c0485180d10610b082c0c0c2c2140d003080712038059100d03081212005013110150009040e0014111903c1c1c180104c960b1980001c1401c00c0f102e40320403242c03495841e103140b054050814082110340c06c0da100c3c02408080d00f03d10404803107070116840 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 446457877 1250 446456627 446456639
    0xb040b010f0c0308090a020a0e06030c0a060807260a0605090604150302090601051201060f021605010806040b060f040905160801080304031b0906030302010b04060f050d08160206030c13 81
    0x1074054841091034682420308103503a00c04a9465100034910703030480c07103103007202000f6039200c2000200030300d0203880c245110b00e05075051606102400c8016800b850150400303014164011000c1a030061042c0b919804068214282820100010441c00c1c481a07000d403d120030032100b0b40020069520568400003a030319041c050100700e4400c20082c500d00a848001030006182c2402090b40004051600c00d0030100c03001d00041130b40100f03a103d480442e40c41911003c50b95010300042c90754401d00d2f8260041a40740c8030002e820204014011032099a03a02c3c4800b6241e41c3d0201a1040400c1700803070360b034649440344046001030400ba01d03000707040403c055401201500c0352901c40c2c141e41034400074609040c80c65a4907681c00403c8907520400548070040814034409510810004601036400828184050400d21048820581000d00120700c000c1e028002740e12407141842d01c95502a620981d200d1441c4800a840d45801d10000e602480010900c418100001d014196080e00d42c0203001e1640c1d038500d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 446459127 1250 446457877 446457887
    0x30506060c0312090109020306072303010b040b03040c0816211a040629040c02010e1b04110d0902120307441b16090e07180b040b01 58
    0x141401c503664020004028044030000486810051390000400c10114030750010b800c240c03085981c2c4000400f1580e05103002100f040d082e007610341070146c18a180d5410000f40d0300360b500c80c500410741e0411000012500f00903500400340002c0c80018281d598401002c02030141c051070038410ba440014844040c0324030800342c0680c0300c00460f0b00c010030511984044c58250341e010001001501e09582e5250395030019509107600c04410304040440003032603880041000222200e01103880d04580c58962111000040014a09005642c00b07250407aa0314001c000940038101c1040c5080f04420045090009440c0e2600002c0c2024400c41d01c04c0409900400481e03030324001d100014259801e4030845200b80a01082c60101c19504848030030070708005d0304128640350898602d114980b0038000303400503000d4000040201c840110001501c030134500c0184c2c1c005280582e0240c07004060351546582042074040000308000c04510714003424641808c203944006041041416003da420056448010340c421 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 446460377 1250 446459127 446459137
    0x10060e01260601030f02010c080408030901030c0e03121308030d0912020a0302060f100e07020a03020f0f0c04020a021f0c1211071101050903010e0609010c0809030316030f090501050703050606 84
    0xa500510060780313107460b0800d0b4600410342c280e0500c0100649500403a00005c000c00241000c00c00a41c0d03207010810004040326404207144c1c1c00c110030049640025078021844400e071000000f41d5a85070200403002c3d00000d00303d607202c01114030000078a4101c40c18503070449d00b0240c3c000e0a50301c1e02d036909610280d1322a800080010010b0300800000341010309540c0b81d0507040241000606540d5441e44410301d800b140560750300700540c3c0803031070081c10940d04200c0c210390590250041e200750464000b142d80e6640c9072541d4140718503004514418003920800542c0982035510030341110440307a812104006010800d00100042d10758050300c803581c03110780200f51204102c0d03800c1c80c0c6440c40d6a00c0b5003900555007441103041210401c50351955607024010701d0b084407034101c0a0708150401c1080203084606952020081c84088000c20091030000300c140ca030311606c2c5260882e0780c040d503101c00714000d00140c850020240d1501420f0340610105501c07a078404c0405840030042ea07100e400c1088024011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 446461627 1250 446460377 446460449
    0x91918020724090609030e130204120b06030f011503060e03040f031b0e010902130812030408030709081203070f030b03100b010215090a0b01060c030804031110060e01 73
    0xc054882d015014822880300441864000c0000ca400765a039030340d011341c0e66030007060303000900c0c100c1410003e2910091101050b03000b98421454a071800c0400c0303500d06004074022304020f44842c005035081c2c070113000700c4140640400c001c10144d4008c1079100c84424481c00155040c03441c00f60b03034204840002040307409560b600c158010390380c0c0c65580c440300008171044100f03480c0d4840010028824034040c2c2e420f400b910380d000001d80c0700da900d440c07484030312503080e031282c032a65004a0340407100210100840380c0041e003001040f42c1e80c0d902d029055541c2c40545d48901c809204a0418030444101c179006980101c40c40d603602c1481e45140c410485c01e85150051090b4143c00c64003809403050500d900c10514210107005540e81d006403204240340c0c2180880799035a454000b101090100b181d0703850094054800e5041901207a00c113614014403020008000600b8400c0c1150f45984800007000184042c00000b2028000300d0b44808a1a10f4071800f071043c0c450800c0150b1000d920b81c108801102c2d12514 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 446462877 1250 446461627 446461643
    0x20105010303091a1903020a180302060906030402030a12020c0f1909051b0301090c0311030403140706020903030d09050708073503040f0e0609040f0b04080919180207 73
    0x41001c800f21044c4c0d4204140110745041081010030410540b00c03a0740d0040515140180c0302d00d090540507000040c1445045901d8052640620050351501c051358044c0c0d03005d5810688035603070307440483c1c5040c4078210702406440c02c00d042845026030029102d9980c0b01d0586490842c03040751003c0c0a0404044481c1e1120341040724400d0012180907030107240e000d00303031072550051400c20703a0078411607074400c0c3c000a9007643c440c0d65440c01c00b6018003e0300b80104601c4c2001e480e40c509503d000f002d19061006207400d06500090941c00d100302c0740c0646403101c04c0101600d03607402c8889166801805030b1181110b4500801c0c800291245000c20048115080c020440010680c465990440b0781c2050708564041c4c0c0c903c04549101040420107800138203e005041e0803400e00b4840550084003004000500c90132801082000084000c0200344420f81d2008408801c5c0d103551030000360381d001d1520700e1600560450646201d40050002d074004450507540184440f601c104040c1c1c05030b00c2020070251100f4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 446464127 1250 446462877 446462879
    0x601020a0b090304050a030b1006050408061609180b0a0b0906090423010b0a0219081c0f0e07030201091703030612030405060d0501060e03010624050c07170d02010501030309 76
    0x70156104140d1145402c030540b0b180075114400903400b010a60410f5820100301c82c01c01c071031000310708000d00c040c000c1ca0815a0810749820b480390340d43c0c0300040000c2c14052240d109902c8080c0610303000300240c00c046803001c00e80007540701c1c00d8005108900015105612004000440b500c035442180e040c0d1b03101031304c1caa141444030300c1404003a01a0140c02d03500c020780703001100320600d40407440a01802c41160344650320801d0000007443c01b202e84031148020010007001100207541a0210759054241d5040101d451003410b07203940003410500e4401c403141d8140600102241c40100700f503010399100b6251042c801e40c40300d00f003e19410440da01d400081d80104007003003a500c1c0a0321600034100d00001101e1409444902040d8250003614450310800e86440c01442816081503003040d9610090340200040c900e8650742030204601102034513240c40188542803207d07403090003150524000d407002c6610007a43c48403251030455844601100354010b07600c40d40340715072040c0a40e504a0f501075441e02849 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 446465377 1250 446464127 446464133
    0x30d090807061d0a03052406060307110118081b0a0f0807080706180201030e030306030607050903070504020c07050420040b0307051b0601150c08030a0f020403020d0c0f09050601020a 80
    0x2045410060040c1d050300b00304580310f590741e2801d01c1010314032800c058801424151485030b0b1b946810250b80c03006036510401c10000c0e072620303004d580d888011442e05007284200c4010483c0140002404070a42100c0040074205005404c4001d1034101c000170202040c842042d2203040c0c40c1d4050030001444229104100c1c0085480d010292000ba40915492481c05e01c035a50799a080741c284005403400d20740b01040c910b05640c0c041c414607801201c00c80c09185103203000c4000a8a503003000300200305101d400325a201841c5c500700036107005000050070855499040b81030300e580d501c1040c410184100c2c2481d01e0500d222440c6103000c1003080740d1071813203400c0509207461240786800060010080000c180990450094004500d110b17220551000d07000c5941411440080c9010311411001440741680f40007000500034012203520680500c0002900c21040711018064031030355101031351001d1406105000c1c010350342402d2044403103000090910641c1c1d81e1440e420356000f2030b1503a0160f00010303002008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 446466627 1250 446465377 446465387
    0xb040902072a03060b0604030209181903050318070305150c121f061b0b06060405090906070306080a03050d093305060402074d030d09080706 62
    0x50544a140c61014507904940d542c08402d511104880c104030940c50100280708061080a9449405413040d503c2e150550f00891403909014103454180107086083c04000385080c0000f90260503113031440d99000405040081040c1c0058034402200030080c480081c0307201e00001c5a8046950080182c142080c00d203015202c181c00040c0007180c0814100310301c1c4400103c4a50891090401d9650748544c00d09440b103210002c1c44603007241d014000c030030014410720345444c0301c0c01c00c0140d1b0020140000f40d65880201d891400b0342d13404540c106000c1da003440003102c0d004c14103d02c81c041c10750b401c2200740d40d01d4080303070b54070307000000e01402041d400c00c01c0000000d44c40d00941c682c18040c00c4071510000c407515000c852100b10300d18112503031003001d01c9614050028020b075a000708003101c0a50400351251504000011480b10080382d01c0400d04516076045001880613801d90f5000440c0c1d4000c1071010442c241c03140c4072a4a0921038084d0304901d100307481c00303059418181e4500000030127201d41040c1d01592 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 446467877 1250 446466627 446466637
    0x2030d14120a0204140409020a17070b07050c010809030f1218150726130f050109050c0a0915090c09090612020405100e070c0206211f0b040902 63
    0x484000c1004041c0c0301c03200c503004603800349940380c2005030741d1403402c8900004007080203100c070b1259060900280141c1e1724189040d00352074141540340d61018190003541d00d040c2c09980041c000e40800b181c1c1c0002d0100204424841c0d50342070300d64000c1592414100c07502c0b40728480e0700801d0840107001e0b00480e5600b94102d035600948035000d10401c910000d4809207421920900681400f030840c00300050580d1011010f8a028000030841041000c0001202c01c0400300030949040c1c29202c802803000c2c41076204084003803541100003000340c4455820280d440f0b03c41d1301819401440d0a08001618000e0341c410380203100e180364070005035181041480030140c00c0040d007840400040a10100b150085881010b0082113401a803110488162041c0000d640005000180c3d1030744070001084007410a11078154081844d02d4840751050a91000480740c0c0030350700380034101d2042d55004001002e0504132050242002e001c0c5110051700001e030300c000d101024010110402404d00040280d8041348c0c000e45 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 446469127 1250 446467877 446467907
    0x20d0503040c0503030d05010f060207030f020402030702010207140304060e101b14010e0c040c05250c09050c03240307050d020409081c0f02072d050616080604060302030d 75
    0x1c24543c3d1240003e2454000400320705a03265a607004006451900156000a10740c5001801c80325103580c46400c4aa416100040d01464001000850301c5100b0740c11600304030790002850443c860700e04181d40d581d81042c0143c0c800b081c1650309811007031034a841c921040700615580c1035041160005041c45040401d48215805444614100d40305042070050140050703a050090400e0407a400401c41510035081c800d00030f0001c108460041414514400d941c1040380e10001103054450780b44c04081400c450b448034500a10385010f100d60720300d000703000718010441d10707242c90480045201841c80704c42c2c0f46888030740e140d402204100414100482442d60b21800200f00003902215510341c15040e134006c02c4081e603041e880000d440c421035007030b210302c05044039803203000c600b824242d5031524000a1407119080302081281104030303440d148900c00b045025401020f41d0f2490130150b80581c3c459100c1181070010900c40c500184a40c207003481010304aa400070700034020700c080650250703000d4104222003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 446470377 1250 446469127 446469143
    0x10e130c0201090b0c0702041107050706052b09121713050a05060708061003053102190f0b0309030403120504080a050c15032a0913050412050703020d050304 69
    0x8011680d4203084034802c0c1c611071045c035543d80316032040100704d030b05c0540c034120302d42d10912507080403c400103900d07000e0740c41a00300190382c1c2003e880001c0600b9018a48071900c1215900c2c01c041d081c030980c205100d0340703100305900565680007100580e215500035000000000380744001450050b110190010494010019100a0207040c0c4075a814402d085641c1000301d1064401d0264600704010b41e0703035a601e1685002c1110341840c5080c2d0744d09420195401c401240d0060490201912545000d0700705a4000c3c031013075441403492148a0f69008600c900082c0400204c0c0001d400740da600300b128464400c0001030f5107003604642d10307a00d070745c5500e03004034080000a1001044082d4204080c5a105000f0743c008e10341e09006004003c03500511500401c0c0d0040c00703100703000403413510300201043d10051143c1e4400d200455000c840950090150b01035021241c0848036901c11910b5001501a6001d02c0300f6030b1f4502d401380c0c8140c13810b2092a50040c010384c0400c1e400f05091348108042e6811034810450 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 446471627 1250 446470377 446470391
    0x13080102310f0305030a09120b0f0709081006230114030c040512010609050a1a0f242104020a0902090f060a0305090d08011a03040804050a0315050105010e130c0201 72
    0x1c0740b4440400d500b00311180c2d070000502204594001e0030600091403021188002c0414540c1c44642403c0d020380943c16050148010030310307890181306400003800c0260201c903c0c151002c10720202904103482498a18601102000b200c8400800e811400c4001030b110300142087d14510b0b0364181c4c2c002402000340c107005000100302daa5a07403007208181c400070300c004506941040c0c4030104540025100c0d0016503c2c0c05d40c0409050544ca155440e0400222240c682c1c0011a0000c0b1741e1509070003d021014001409002012030481c5000d844c00612000d103091022641111015041005840180d80300800f000204118200c070340007410041d0015001d54528034049012603001d41002060002081c1c0761004c00c000c0c6482008440350b44800c600e000c1c801d65260400140310709505080200b139044c03000000506000c0e08400716002004050281c40b03050380da0f4240700528100075181c3c0e0100c03d0034100001078542c828050a110b150b40281203103074141d0318554520052000c005400150b540700c1e80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 446472877 1250 446471627 446471639
    0x6050a1a01090308090f0604061e23030405010b040f0c02060c07030206010b0d0e03040b09042316020106030c0f08060106020f0d030209011806120b032107050a1401021308010231 78
    0x2008c1c1009280710b49409401d01c2e0905d01c0b80c041002040418810003510600c3c0300241c0c080340d6039110003c00340050b6942d49031a02e003403190140503824035a40e0810704004141528460a601c01e2031001120707402e0b1000d50312155070104051099400290050740041c00610940c42d1400042038181e01c811400039410407451007060458000394800003407020089034030415420b140c054006444155a850388089130810200b5501d40409000303000d01d110b075500c0c8110801d00035070040d409141c10000c4800016501c60300e44881040c0360145d440306000b1840001a00c500004642c2c0b0b08007450005000c0302815684210000d42004940310b041000c2d1001000f03c60b401d100c0d4040203854590303100307040b214009039003005841003281118000d42c48990f803028000e9485580c90007142507490707080d60380c01e580d040240c5809004203021b01800344a84003014254015070050a2400c594010580440da44444003070817030003581e0f2000f1074034860002e0943d109031021502120030a4100002415540342c0d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 446474127 1250 446472877 446472889
    0xb1b0105041115130f0e1305060406110708030c0403030f020d1d060403060507030903020705060403081b012904150323160f1a0306060409020703020c090406050a1a01090308090f 78
    0x40e00c491117444100100b44030350083c0e030782c84c140c0c043c80c030a00c0c000c824045640c0d0300d5504c0d02c000f0b2015203181e0342c407140d04d034950084104403108503411400054403400c110392200c803164003074803003203000c10144004280c40600201d014141746940d034541310095414040641c0d2818034406031683d010400308000f1000405512440d07000d2103107540c002aa991251a01134035003a055005944a030005000c00c10003c1c40c0002211114106006c480754560703078486104c0d0241401c2c2c202d4060403401040e000501552070224500f03001d0b4104c6061008004503201e0341340320700b0540805043d81d09522845034020014514142e8903ca001c0112440d100c80c03800302d44200c1c0313480d40000240c4400510204881c1c5040c1ca900e880d0a08007444461a601704a4001541c03407080d8820b180c1001e8000ca00c902c02e15009100d114071180f000b03000580b06240510b0103000074881103641941d91407401019801001045001c10111070040e118840101e046403961400364001c00e08850780030035281e204c9805902c0300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 446475377 1250 446474127 446474129
    0x1507080f07330e030a1202040f0308070c05040b0109120f17091905092418160201060311011206050a0915090207030207030609030507020a0b1b010504111513 69
    0x4480080680401080e200110514040b00c455402e800d0040c50f1a55901c040304458a40015042c400303046d0300e0400d0450041d02032540040004040d070072000040c400c1d00c400a100d0030384102496031045440f0700c100320465418000041c0040d01848040c4042004100d8003101c4600400e04480311022580d51038034189085e07490109a0794010642041d01c3c00c1c90310a00c1d03000b212016407c01d00604060100d040d2040041c002111158140c80542c00c08c4151121002c0301c040241044524039034003c1509070445e000e84000d143e80100381c4501c070031203206104100a480d40000b20f1100010582e004442c0b40c010b4819481ca400d0b038560000900750381d402c1a89000704400d60004c00c02e0340742c0400c900d2000c3c00e1580400c0300030b0b004000c1d07640029808120003003501d600c010300048440c200d01301100c1c140036000009410004150010414003044d401400c0814607000c40f4070740b80c0c038040500c41d080c1c03201034400801c900801d5140c07011a19051070b000d08604554082107060040742c501c00c001c80411 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 446476627 1250 446475377 446475413
    0x70f0f141c0606060f050909070c0f06290306091b03010f3603090b0717030a06050901050312072013020a140301030f1211010c0801080c1507080f07 65
    0x60b030b4004012460b00101e041245c80c0a82c10924106131a20010940608000707040104012046c04000200580500c0e1100b90f0780d00500104020710b0240569044608002a541d104026424030300304207160004031988920140b034013034400c245c42004981c4e450001a88030700c0e459503c545210060a9807846042c001100c00c6060260380d0b54604d25240c05142202041005003101065200100e501700028008039050740b00d4141c0d1700d12150410380c0d60b180d108001a80c0c140ca0010900c1602c0b0819044842500c200300e036801610b907600c20403d551001c1826260b90202824490500401d00360700114669a42d2400a005101c007002e00095032175043c41c16001c2c1450b40071508500c0c0030340c040520f80c000150390008901c0e42d419030b1030b29803180941c42c1c8010034003c050342024036400d21800290104400700b10082c0655101010701420100702406800c50301e1007440b001c6a42450300c0d01204408800200503035181c0300e41c5403108101ca9100c40c0200294070403c0161000045480d1180d501c0545 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 446477877 1250 446476627 446476631
    0x309031722060b030102131806211e05031308010c0e330304110a0b0711010c0804170f030702010e0d0f02130207200f01110703021011070f0f141c06 65
    0xc12300b2440d1410f004201d0381d03105407a1030a0420302a6900d02c81000c04482c800b0201c1500003105031402007215525424150042e000000c0c4140400600101902541c600450700b210b41d00d84a1107098200c0d50b01c4130345a0002a201980c201560400c00b01600309480c07050501c10a0610502c0c03c0604042c600c0c4048020324400410070080c428003207107550824104454816586107844c60f1110940110350f0080c0c409841900c540020b40e004244007141c0e44e92101c561500c0d15039501040c1c103110a84031250826004010710f504691101004840c27481d5416198492601d61003810301030780c8404e01d0402c0791542c82e14215840541d0b030740e00280306442007030341002d80d50320900d10303190b0054804c2d2451a040320030100680e5070a56140303204210101801e01c0c1420340042d44001e40d519011755a80081d4004480301c0c41c1d1000260f00000c7d0506050100c0c0031900344599411071082004c415220f40103110035001001d0105d0b103200403544000100003820b0518014544072030f020b6003c02c04000701d540c9070b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 446479127 1250 446477877 446477879
    0x60906010602160303020c0411090a030b07030c030b0a060807090b161203050f0414210d0b0105040303020d0305180f0705040501060512010e040302120301060309031722060b03010213 80
    0x280c2c1000043e00300c5407010b41c0480710603d10baa02955840d4404c81c1e49214984034040c0b00020706811043d41c0000400400c4024040c2d0b890034540441c50003a1401030000f824007e450310054000c0c0542819803e029107502c082d68039007007085541030b4000e000c0604000a070240020f0040e1580040c0c42c0541d00701e1042003108906240c0a00f03407030001c0e4008014942014100b00140f21a1100d40340c0c05500540c081250220100c0307000c2c2030640054203441a5200d6031440c040450301c5401505413050840b01c100b11002c9440d0040d1402d0260b41701c000e0050b4800328951510714801d030485600000f0b005461445d41c68001a0a42000424809031686a1100300c0070009403910380240b600600e1681045450300e1240c103070442064038140a0740404002c504045800c0620811000c00300c0d092050700140c031395841c0c4600401411280c0030550018140c1b00c500d204c02480c0140d4240954031100401000c3c07407011714440c031310325411030082d10070341e54035030520304c4070b40307081c0000c0c035860014a0308a4005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 446480377 1250 446479127 446479139
    0x21c02030423242a10050f070e0d081603030506010503010501020d030509101514090609070c031103040b0d0609110306090c0408070905010e07020a200307030506090601 74
    0x440d02109080791800140d40745200075403200040d000010002c0c410030010820750400e0b110f407078882c08100d1a804401d10300801240009122a9405104d8400039203907246641080380080d44d00513a00d42c941d2070940b40c00b00d0900d60240c200040246405001b17441c559103240c94104841e04603a20a00c8500e01c0e08144104143d03045c4500b96001d202420160f045504010001f076880141c0011141415a944003145441d00104200c1c11100c90300340090104140380321450003440914842d480e2501c0c1101d100c0b1000d0f1800b07101042c41508090074911190791812421a03540c440b054003036090050200c407904030038a0510041000d40310021200c2d5413213414245032400c41e21158040b0300c09038034081c0c0c150a195a00005c480c0c10520031507003040b0a40391101642c20a10030390340710064610400d03000103005489600024100d5980d85c0e03210480340d56291041e619140000002402ca50b512036a005081e1901294030750355400c041c0071a160592250b442d24035140d016a445c0115500c403000401c82 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 446481627 1250 446480377 446480399
    0x2033d0e010c081b3117071a0a0c0203010e0f0c011e08220b04031b02151b010e210408100b0103110711280302040c021c020304 56
    0x140011034900200e0501c2c4c00018103040c14488081456a81d070000780c1601031942c0800c0f0f141a0311904540e4600c1c0b25544880d00880301590301c03c03103c0014426925544180011a810049850320b0440703c001441c0310080314a9503010300c10f810305201c032403247d403000340e1000d12a202c902921000185450b0780f088001074074060707190300c59904100140c107450001022030b00360b1447c001c06038100500ea80d00e544401101c1e403808100c1d40710700040d01003485001d000c008000c041c003d50080e150440503400380080c0c0002c507030081c203000c1d401510380c2d00310390280d68840e03005003118100e1034016110800d000c0d03061400d542c4404074905160b4400c0410b107410350360ce011002201c16400b00c20328980392800741243e441c1d01d442c1c0501c0c1003045d514101c88175203034025003019007800c10b000d0001da0786004900c1c1c504240300e00003800500034100108510180c1c40501d2004029180003456540d1407480e41d402c12001d03280711003a4404600034403070040d540521000818102c1e0426402071034440c0c1c105403203054 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 446482877 1250 446481627 446481641
    0xb0405060d08070f030c0b160e151e1e0715020a080406200c0d08061507020d0f0b040b0a0510031e02150301060e031902033d0e01 57
    0x1204807610041c03640010000d40c100c60b801c55110001c514003601c5401d003030f510030594480103800304802504020300d1450007905a4051001e5480701d00c40074130701d4014481031300518403400a41c1241001800c5c1e00f02d142d01d0f01e100b8a00050740e00b13036190400303104515804903044821004544000705008003000f113410340221038204506011030408410030401000701c0030281c4007405855a0341e0303c00310f040841c0841130102511042d030041d6928503a0298640c0c48201203032550028011501203079061404071141e00c1036028242d0340c903042900c15020082d603006d001d0310403100d094098161100040b08070040520541c018401c8045610308941240243e0308020320b0f80201107190501440044d02400c806c0700001007001c03080410741c4031840410440c1008000031075030740d00b021000081e425406060360300900d0043e42550084149200426507007120480f00a5264001c55481068544980c0c3d1400805e0f034016010820b40903000c010a122108170f0401103651034480c08080c285020900a01c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 446484127 1250 446482877 446482879
    0x9092a18020a080c1305270c0705010507020f030d0c0c0c032d05030a030209130504060b01141903110d05010b030a1d07060f020c090f01080f0d050307030b1c060b040506 74
    0x5c2c039090300c40e03103e074900c410240100f43c07290341081900207484170162141940504c40c1406d11109050558000741d40740c02c900e0f03045405c3d60070040040c050b10310108844d0f40f140c00e800c0055081002c8245250003030040140310804100001c915200810710004803d4011801001c0714581c4103184508016040701c0c1900d40382c0260780503402c10740092000821034008402c2c0780341c0103842d00031900005c0c0041001016805546081c0418001030050340c0d4844221a8003d80b6a000312a0040c03596490034019100361003c440700c079410140c90ba5000380c1003040804841d12484e4686120201d40100312070007a0803440b01650f000c01001141d0003039108441d44036411442200350304038851105aa40c0a40380102c90030403550510250205008101800003030070010300c0e009191801d03d8100f8140700f809d1150388981d2007a000c141c0c0c0300001c0440c0c28082c00b46030303a40e0146140e07a921004d4021f801c080035816044481e07000c0e2003040d070101140f546510b80c452803010400c0e0380414100000d80390081c1100b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 446485377 1250 446484127 446484151
    0xb270709030c062f01050f0702010e07140a0803030103080c0d0905100c06150305100c080f0c16061802040c1409040f020c03030c03090709092a18020a08 67
    0x40c004642e00c01a000c045401c00d00c0c4c94404008001c024034901c0d8010304060194140c4013001d07401580d8103401080c8a10440444020070b5076030a0780c06c030700f40d8241181d145100d41284100380322002c03004003058016100035000075480396a44003e5032a540c026070050314203003004151000d5542d8240000c8420103000c0c0b62a031501c2e400c100000f16004c8600c00d03600e05100311102c41504012954208904100d1621000e0107540d603a070070300d41d441e4030050a8000501d441e01502006c00c1c1d0180080901401180c2c03d80c5d01280c0d1114002d045039072003c0311900a0311a6104080c0003d00d0502921048160b8000d0040c45c0203182e00c10f00007510060102c0505106d80c00701a4050310703940b00203039526964110740200b20007070200040b0000307101d01800c0310014040003003082010013105000714000d60456040300e110555614110084406038000240540982801c4210740d0541c4001000c2051114000b0141c3e03643d01c3d0031440c09469a4551029900d802003006500260004519540800c410f101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 446486627 1250 446485377 446485379
    0x60405060f06220902030d0e030115030c06270303090e13080d2007050a2d08030702030c150709170a170f040303030605040f090f11040b270709 63
    0x21094200c2008054820b0b504183d410301410240d00503014483d006010b540700190088001080c10340c1c1d040c10640a9801c100314070b81c1c1001e0000721241200c1d00048841c0c2c9140c10700008458491062854a82c008007031500304d0495a648004074008511a0320748102440c60305c03ca0f11040180140000b25000703525a1440100384410115981c140501200080f1125009204840b5246001075501c2050001c5004c0080000010302d40f40220701445078550606a02c1e10000b2080b0721291514160040d07001d24007000031031020145400c0f1100d40180d0741440c03403044105141880014000d8455850384051249041d0001c0469002d4207140202c1c0320500c1c14510307016603556072000010400d81a400c0ea10150b003c0ea0802d8074004a43c5040160b0b6641c0d603400c0040180043d03014044c825880d110210440e1040c91040c0c40c0c0c0c4540c4020803000a4075151103000700521082c04244c0c0090715104614074650340e802d0300165010500300c3e6042e0004130360140901c0813400400202c280205444 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 446487877 1250 446486627 446486629
    0x1a0306091015120516050316060c031b050d0f0f020a0b1815040203070603052701020408030706090b15060d1505090103060b040b0105032a0705060405060405060f06 72
    0x34800121004810080740005100e880564802401d6000064910b083c0440d0000c000010503a400e1070761003580700720007140e140c1e000c0540710500d030780ea080c8402c0800c03d420012140030f00440345880d4001e0811500013000c00d04011109800c5040848081e00700e08203201c00300e07030420101d803410341c41840c00c0d010307503210181e0103513584500f5500a0705a9222500090810505111158401442d1003d4400d000920116103018040c1034030200c3c440c0c00340390000f055071803091145070321480d20b036850401e9040ea02501180410803103d00312495540030040031400720400c000078110a4841d100008088142c2c2c2040d420343c00c0702130701c80f8400414000340f030320b41c036038607902515503000040e680002c3c4000141c080e84a0050135610103030700980c05200000500042c0d61140d41c090005803070610020300d010380110381c81e10003112400c0c24500d14225a80340801e4141300400e00d014084c90341403070004d15480ea03c3c41c0c0181110201c90580c030640c20481041024442e480d002001c9000b1040f160034224 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 446489127 1250 446487877 446487883
    0x80606040303050c120c0607020601120b130f06050c07030e06041406130302220c0905010503011814040f050d0302070f120219200303030603070b0702010210020d1a030609 75
    0xc4030141c02c000010a0030710083c0c0d4248600305c0c0e11220000c40030396407410302145a4480000316050000350003248000100e51601c100300b0f50b1801da119030458115901c3c009420b8048107200302c02c1c0d170350a040c400301000148071481094040c4a880c000c880d00d4420900c1c00401000208441c1c034042c030824001044030350300400c003c556082048900c907403903541e0030003a0170b0701113115480a9486036403441d68480d9100c404d01403034440d00d11007105200410500800795502400303442031070700058040004120b8140b0750951056100c15050006c02c128001c24001e6054803800d0702d040d150410410540010400d04124800b61800c03603040650920400d40c45070036076007203010800f8280d11008554859018030a10250005081c841c8402c2448052820003034000c550943ca101d4031401c080d1036071100c40c84e0020075070b8851440180107208140c10540145034580044004a0552284101404044009002030842c60600c0b10001500c9484202d6001070380b404000b896010b40c100714288050a2004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 446490377 1250 446489127 446489129
    0x10b0109080712261b0114060909120d0c0905010207080706200105090a02012a0602130e010303030207020f04020a0503150109080f070e010f0503030d0f0f020c0a050d08060604 77
    0x40d807401c4611a4034104441c1c040c50110820030041d44110300201d8419800001d0005040c100b210314a8640da41c1e04950300700c0b1406404c845d904c1004400048d003070310301500207031760041401c0261000c803c411540644140c000040c04001c07145c80742c3d031501c107c942c002c20326001000c00f44000c00c070692500c08095120401401000204951400e4007449180320400c108881c45a42008200c0c61408046a54541015083c100d001800c2ca40e003040e04030b03140d014800040c000b041d08610030750510381e803042c0007513014103030320f01b0800c456183c000b405408000c032941c004c1d030194401607a20b00091040102c640c81502c8201d124620512003680070507403080913030b9405403100070f800110006c0c8100503074440c82503030700c24420f41c4603000d074452140e030000c140ca01c00c403142c07400620b0150741c803003441c1c0c110000c981c00f8a80c1c00d54424419610170301c0b40e82d00504000b61090324005203102340c02c12114140d03400340c009805541c0c4403050b0207040100400503910006c6c0145001030b02401d103a40011424412 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 446491627 1250 446490377 446490389
    0xe0c070b1602150109021201080c010e012f030a1710030201050a11010612050f010615050d450206180f06040e1e0c070201140c0604050f010b01090807 66
    0x118100803244030307008120b00360f51403403040c1907003115694800301c9001a51003203041520040f0054000a2525400540440380c800f0584421202410180045036508004000508500ea160450802d2084c10a00b07217886d500f4840007840c5d55800104020344103042c0074031b841c00b2018040d002c014802c90584501c1064950918109550f45c00c0b14808039030031401c02c1101403555180890000388407890450200c502846041a2203c91148a001c1400c031200d61080304a07058052001031810341c803c100404e00541c14607000507240c3c440034140d40c0c1c1c000c00c60180e40301c211000d2001641c44a99800c50b01020314884000d000800055808645030340a007110a040d01066201300d1742e603a60b0b4001c90690032000182003070b0703100c650390050002e41040036501c61914041140600b031220001c56201c501c140b0180e143c841c40c04c0417130f500440344c1480d2041516008102885655a82c18007442000e002d60700a200070220000c040ac2c0803802c4540d01e50189040c00040d100c100719490002c910308040300d034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 446492877 1250 446491627 446491651
    0xe160f05070302030c010c0918021206010c0f1a0a18020d14120304050307060b010c030c08090105040b0d150503030405030715020109120807081003150905250e0c070b 73
    0x241d150503881d602581c0c01c0303607040b5400c10034008000c60740515204c8c100c2d9201113901e203101502400e030744200d1007100c607000c18142d070802c0010380650081109000c0c052040c0070440015440b0748540175418084842d42c01c01e122001d0a100f010046409250407404031030342c2980c403112640d80002d84000388040c0052605d0200000b24010010520040c00ea09800001895492400e407800d20f8596004c00021103c123032410a1704001c0c1c1d4403400c120421640c5c140ca52001c1011503031601a80c40c2c004070b81d0641000010080443c981c03034400042d05c0111081507001c21001030269500b0013802058008900a5200703000c10091540d00140002c119482980e90101500304001c04a0151840c07140141103d100c00907a03808140d80040706a100e004940d9501c5250b40740d45900e5007102142d440040c220469203030300c10780d441200341d1011600c40e100c0c1d81100c3e0003800f0f1421380310061259200d0300005031041c02040200a403400300050340040c445440c0c503d03001c65035a602c1038401e8060060440c1d15 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 446494127 1250 446492877 446492887
    0x21e0d0201030c050412081b030408190f0c0618081c08090c060a020609060c0a0e060a020c130b04050619030326190b010c080319021b070e160f05 64
    0x40e0149080b100074013030a81d206c24002115040c0310109034042a84c00c65800660300c560340d00d40e04044180c405440702c01d0003809201031038010702e060940724440c09550327040300008031800184006560400810036900c851030280e0074905030b00d10031100c81c1d124000d80c0d0410b9007941d2400c00c40702c0b07074050072880b981040da066464070101c8518bc6440d00c099140c02c41c1c0002801d08000f9000180f0b07034881c98000086032095502c0b411000c09502908140c500030400383c0815001030302c0c0c540c0141c441c000c810b1040b1407444540c0000101060000f1900c0745009646816042c032a041034000c150703103d00103a82e40d813040d4400782c4129000d20503511000d81040f0082c9040c000e020b074044010490464441e00c10b180b40c2c1041c8542203880b05140020000c541c0c5003c181c90059402221403921254014001da82103994141c10138915411401c1c01c084d120ba4200200003640302821001102d05001e0402014054281041c0c002440d1010b802c848055000b464040d4000c0e600510380c0c039600c0003d16005480b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 446495377 1250 446494127 446494151
    0x10f08090c0607060608060405010b1306080705060a0509031f0e1209090c1209150112170d02090307090204030317010e0406090609080c16091a100e0604060903021e0d020103 76
    0x20440e1b034002c6407507030107400c0500040c44415000107400c0241200ca03600d002c01102e40c40d9003203d00c548103c2c5410b400041e401c22aa00c0c0140141c8907040c03543c100700c4e1030302e15501c1c002418145501148940701c000d459240740d01d441c1754802c000640045000800740d5044000703495081e0700a43d0304140c407540007070300064800c0c1d0003142550b42c01c05640307200304568201103046907155508841041c035000074100002034150348085006d200607401c920007116441402d01074a00c10b6004403104048550200b10900c010b40301080036000402d40c6841c01601d590951500a00401d64598440200700011005000409903c400507400540c0907000042603203991070048081c240560700900031f0301001c07580c2c1034000000300b54068051400780040701000d4866844004682203c2e0390f1000c01d40c40070062158504040c0b01c4050303100e40c18101894a4031025000404940c481d40080c0300042d0031030f00420860804450f1110b00c88080c0c41c8510f900c0e49642c0c00301c2c0015a241304040c2c10562a45004072032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 446496627 1250 446495377 446495381
    0xe031e0a09080312061003050c090d060e070f080c0a0b16030e0d05030918091b30010b01090b07081803030a1d06070224130f05010f08090c060706 64
    0x100034140540f44c4410894030f5030341c03034260300b102d25a0013550700a0109803042d04c64441d040c440d0b0b1a28a1007030611642200b405500341034074404460040d079620384040c03842c104100c040d0080032410080110503003410704175030800c074031145060300401440605001440610007a5040d406c84000240404500c43c00d0031a002800220b00d50380044046180c201030100102c01800a90020340316840d641c0e10454804024502c1207c0041e6240c00003149010341c00394068071418808401840d0b00160a40c1001c1002c01130702c01c5940c05505074000201e810850390a006050b95048242800700b8a04e1500c0c031150500d20803040b0003001c9400001d03c540c800800c1c2d0408186544000c0c04603030300d52001c2038003d04000320341e0681c4544200704002080081c80c001089a040c6036001e4000e41840f51422600141a101a201c04401d4001440416501c420748544040180000b82d00c1c40e1007280341ca00003425619003080a4001c0005c418204030700d07602d0008074504a8030003910b0b656540d4416060541c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 446497877 1250 446496627 446496629
    0x1403030a05030c04051309050d0f0e19090c0302090a0e13030806131a03011103010f09020f0c100b0f01081005060f04090f02120603060f01060e0a051906030e031e0a09 73
    0x6e801500301c00061200e640507403202d031040d440b07101264550480b140b0f0030380d1605081030070342c0002400582d940d1261705100080c0d04251418481d1848825114000c040c161181c03040c2c0500029404960b5003e9481c06052001c018843c24a41c420b940c104072100002241c1d151034050148072032a4042070043d10f4070301340d00a002400140810211550817140000403070705250091181d801c048408010301c200a04480c100e40075048400009464107060b0b402075005204008402c180501200303418100a00c200740d00188000000a120f44a58080100742841303101346a041111810810984101c81e41c03441c4152842111503a4a4400502103035450b4420f80e0401070600b0b09007092003a41d540c482d005402e07040708802100020307503a00420b0640d510402c80da40740c02407940787c00401607680264038030464280040c1003840a182c6403804140041a00c071300401c0da00b034550301e0070800503070f1511643c0c044600c1603000d1842c0105005e0804070a03070055045550305980054048000c900901001c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 446499127 1250 446497877 446497879
    0x3171005030a05070906080c1c0302010605121f02070308072d0302041a0c100b0609040203090a05060a02030105031f0f15030303230a05180715091403030a05030c0405 73
    0x91040c6040d8a0095244c001a20850101c20b06010003c140310f040416a030508050103441002800b541151262140c402e40c5425010f55590304400715640c0c55125500e500c4481ea04014542d06180900910f042c03407038441c0070b07202a03105102c4000041d82c85144990410071364a082c0803d01c00901682e901c00c2c0341c0601384105d110001c0c544a95054141e0040e1048840c4102d600c0b209118040d07415080c1c3c401d00143e480310f5009890000010601a48403450600780a4101c60424024101041c200d07030007a10340c00c502da40102500810401d0400c0115800200c1c59025410340d403401c000b2950710070000030020b2488e50780300ea441054a81036848842d041301580028001a16101002d00384460780740010750000342488440c0da4540151100700c0340507900200c03641c0c03940d034400c8144c0000300310245c02c83c110001d0003019005a15020421400549004100c800340302100c02c2c0080c3c0140210341c8610b18184542c0c4114030155000310940e02d001c006405c059580782d4850141e6001480360740c00003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 446500377 1250 446499127 446499133
    0x100605181e090a05010b100c1202030408010f060e0a090c0b0702150307030603120f1403070c0203060115030e0c061803190f03030c08240a0302130b04060e040317100503 74
    0x20081c402d0000f04030326150301400c0208442d09008041c4400314580040c0c3d20007099400b030107603001980824420880c41d02c1841075a082c561180007441c29114808458800f072074450030706010300207000440300d40001c03802c202000803010f240e032500f04201c2c0030b2007000d0440d40003050f40000c0d5194456004102d0540c0b0b4600356681c548a2406001400306010a440680c811b03010a0030040c06401c00c00c174a1354207616624042114440e650101d81d0005061030b0400001051050050314200660f90190984000c040b8032502083c400408071500d80308032101c1540843c040400c15111700b82200c0204aa4500074007118a580380420705c0d01c04c1401030b500c1d503441200400710a02c0034042d180304085200f80d5040c00700f6031400c0c00031107900740c2c140c90820006aa4582d648440780c02ca180d000c03413002020309000300d22550383c1c0000340302e0490b03140c000004544510b0030617003500d071600c542400380000300500d0049050070b80b8024140c203403905040b019141c043c000b14141180b410245001030400a0807 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 446501627 1250 446500377 446500381
    0x40b031c0c1401050702280b040f080d1e020a12050705160b1605030402100f031b020601090b06030408040315060302100c140616031a090414100605181e 67
    0x207441e0083c40704072140303001070268003080071070a1018001c0316000c6840f06422180d2640c08d4903400c009100180046640803015440d490000703480c00050081703240c00c110005640720b100184100301403400c0e00145880c1e4410014070250b240c000c0c0d5032440c540e202c0f03000040d4940d82c00105488a20905503445940e0a1130042e0208011034000d4a61150001c81d01c1e04400b8a42c800041d100ea0209136030080d4006501c0b008568400e20603607a607200c0006a02d404203d810390403000354444c1c5404a80140107800640c0180250705450041100008090320101c1c507520b01501d40407128055804010564481000314440341d0301d180d007290780a55002840d603c00f01c4e81d40a009002ea0400f000126180226071191000c07124010030142c0c070a40d88240c803140350680f114812001088480d03c007a500c1e8a11403801070f4180c0700d188500388610312410003211880240ea1005107400c0d040030003015601e061440134005611142c4002008a0254128050f2500d40f050655214001005602419441001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 446502877 1250 446501627 446501663
    0xc25091b02070f1505070f08040f030c0e0c16060603021c060e0c010203031305010207211107050a1a0909070e0a05090c0306240d0207060605040b031c0c 67
    0x400321440404035022682416500c0f202d070325103800300c0e11032244428031400104e0a480c2c010b000400140c2d00c50128203090b84155912019650810b401070740800381c80d21401d008001c0301a0001d00601010b0705010f46074545002501610300c9140c582110381c201c4002d1290400c0b010341c010501a5500a001e11a6501c2205403e503d018800409039000f60800804444500000c149101c070381c00306038042d40c6596105070300201d188540d15011940d542d4200421004030321804242e007045203502d07007820040e0060b981d001348040803a241424403600070003c100302c1d9a940030072403000c40c0c000c10807042482001d40a1213042c1c1c00784075007540c1c001c900041044080c990040c050341c6401c00499510702c565881d03034144140341d2411a442d580360781040001c92024030f0030310310601410f00319408010506000710b0306200c883d0007040c00840e0240d0041141e20070072460b4001d1002400d010b4030104841942c000000e03565110000b403040d4100d094400e503201e05441190381406040d0444038070010034080d02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 446504127 1250 446502877 446502911
    0x5210f010b01081e06040b180c0301300b06061210230d0204020c0c0d060e0118050c0d03030e010c05190306030818210607080603030c2509 61
    0x400124002000344000a2201e804d211402d60300040c0101650560f039603410a000040280c1d05581d5401fa00d000302080303020702c81c0f002280c42142d1080010361a0751401c54494680088102c0403214800d0307a410041041c6a2980d910103500d8000701c002c8078644139800814500d02c40c0e0443c081e40880d40f1800c119131814112848011140848903403900c01007a400000308110018090315402903d0313400410140c03506030060403d520203c4191000600c400000440140c03480508560003519900c40c1b444000e42880b94007540c0e500703e140400d140d101640d03041e44503020307484ca0603c0b0308001006038041c10710030b03030040544110040081042102d544000303012a00411032110002c82e0900b0f0a1030501c0c413038040c000460b80d0084507241000042c0c501c03800f81c00c5984031620b1704080301002c041030324072a0403848180b00120300050645414000c4000346503480050110740254130411480b0080c101c0000c0c4110307601701455101d2070016104810a803840426840700f4841814410007c400682c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 446505377 1250 446504127 446504141
    0x3030201090b010503010c0f030228020d0305090c0913050a0b0c270a060c0528330902030f150906011a070305030405030d0e07090c020109050705210f01 67
    0x580c441442c182e0380c1d101014240c40309092120700044000a0719801a406a0042c000b8050580300a6151007905a075400310707843d0011004006074007400a5613051038252023040d4200003001c010b4018100b5001c04141192405017510307100038408500c020511205011010b1a41d0380101d0034101418004000e03151500402c031100404150751020030b201011450703801d1a114005007203250120315041c8161258050380d0000e40d5140110442d032102c00c2444203000480941412602c80c1c040032900704101320b110f0301050030004801511404200c42042c8003001400340b1007480108000c220361021034180f00003031403006118419084205080054242132900c24204030044582c00c7c1c0c0e0f203046005d0500f11361a1250f4503210104a0700c0f001c24401d4005591050254040b41d2500304400311101c01c5030600c44c6d0904035034000040900c40401b0074040c8211a41b4076100034851a001c0d51201c50f2110b0040c454548222050f8240703050f0040f0880b443c0e501c04003240241c612070b007100c4242c1406400300b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 446506627 1250 446505377 446505383
    0x4090302060711010608151306020f0d11070209010e09121606050609040b060603040314180f01051c090f020316080c0d1a1b130e06011103031303180303020109 70
    0x152030f000403e0504148074800403180302100920861042c1010100d502d030003d803030b4440130f82d101000180480c41d240028a01c510b01401c08513a034820403070401048603442200401d10140800902002d6618844501c1c19182280001c01080c1c441002c207500d0720034604406100d400010400076442100e800d620b8100310300902040c042070b600c8508001e6030410445000f00b04a00c2c03007000c100941002c0001c1c5a000d88242441090b001241c600084507070003070f0040c40a44011410415110304002181c1e9028000a003002414800060506031004408821350220290f1b51f044202c2802544620200d00036009401e454128a800200384042409401f031078145100c0c2607070a00c1542412501400d070075800034810400c0c03403120040400c4040c800fa025984000c0c120881101c2d140b4050010040011450014080c00386004500082c071000209114188020a0303600c0300d52010110450f0390100800350100c040900300d103010340303803440300a606410b01b1400c281c01100b059015030000c50000c0c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 446507877 1250 446506627 446506637
    0x110c070f1a030708010e040201020709060b1b0309101202040e190b030a02011403060118080706021603050316030c061e0b040b0a060c0317070315060c02090c18040903020607 76
    0x11118200e01810b21080da9038000094204004000c00900036050a4020784144180c40240365900001300c03d070b85040c0c008020503680002c0c64003002801207141d020b46042c06000c1c40c20550890b001a100c140c0891200092064103100e03501c0200b0203604072009402d203264481103d08140002c850403850824110300c0982c07030190101014a4001013441e0800d5050b9078200c0600070700290b029054001034051342c140410307140c800d00e61980c4920804003602c0756600401601c0d181000091a100c0b4040050308140f400c0724080c000f02d2008401c0320714948507940c050700070440c0c5103021101044a420064206817501001c40d030240c5038030b070504201090202c800e01c411000a0200300840d000c107103800303502125000b410008d0714080e10141c041e460003810400e400045030355004402100441c1c0c00f000199880305604040184004d1002c041c18051414503800045540800da450f2b0700600380d00701d41c800c0030584441d004400c184a4941502c041e00900050140703182c0659600800c0d295800418 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 446509127 1250 446507877 446507909
    0x9030311030f04060309060f24050a1212140a030f0f0203100e1005031203040203010c080103080703050f0c01020c0a03090506070b040f031b0b09060127110c070f 71
    0x10000180d82000d4600b20300180391070b18001d030550042603440401c40e803890700e42007081c080d11824801c01c50310001051100d1200710a1303e40750440844240c001521a940e4018144800050000f4481816078041400344103a41d9000060343c0100f0b00c0902400e0104c40010340503a881e601d60080c1603140c00902050046800111030b5a060b0b0000319148031250b1400b40c820002c81d038201e1200c4d6088864450382c4211135480b0000700e0b00341a000000345002120000c03d0104500b400d11543d00c5000c620310304007000c1d5040d81e0325800310344034200d0003504000001c41c0b807a9001c11180304072900b212200008561b034440601202d6112844030b50180c002c038022405c00035940c10500100e441640d8040d001060700d9035541e44404080c1d000d402c0540401c0b0075a04c400344c0c07400301e0f0040c20200134090303040c0b440e4501d040c0e210145040d00c140c1000d611100d503d58000c0074400291a022200030041c600071401521490300d0180c1c2d8003035281c102d04144103408000039200401034101065507034000038001d5038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 446510377 1250 446509127 446509157
    0x30a0801090b010206071d0607080310080d120507090f06022d0d0c11090f040c240f0c060609060f080f07030222060e01180506010905010e03011b090303 67
    0x50714007622940c01340c0c22150006804a20035944400d081c0f182144500c070b2131555002103102a00421800c0b115440f0000601100000142c5020001c00846c07000342010b00c10501c0041c0300342d6034185415015505c0701702041d00c02e40a001c0385809000c25031030f498400c6a42d01d900030764030f1881e00b46500c000c01508558601807020814004103803403c030001002c45d0082c8080465409000300c50558080e14211040b1190382d545802d8103014071500a241e012074285420400f04004d0940d0000e0200d002114480c0b00d0002d03c41400c0c0011001c07401c0001d004501c1e0034054500e02c80300c2c5402464149040e0700490740140350351000050701c0c0d6103028060f016482e0038859549022014003d0341660021908000500c0c004840e6403c1c08521030307035035070f0b007124010b02001a10425040040f20005030310040c030420910074440150210308000600c0f4904220002070316220160045904004840c1c44e030440c0f039182504030301d180c051074100310072100509640040c0500c05a010480004080340910108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 446511627 1250 446510377 446510381
    0xc0a02090a240e0105130213030501060314160909020d15051e011811070615050108060105070c0501050904090b0a09030807021c0305040312090516091a0904061409030a080109 77
    0x82c0d84104030002042d0b400d060811551200d17011b001d050a540030030001e00c804582c40c6407100210f1254001240c001d007140b4041411004603035006485134001c0c00d4003140c000146050f074040352940b02000840104a00220f010340c6103008001e88400790030340b51210540025840b0300e01c12100c00d10048050320080582c3c40e4048000c0c0300f03a2062040e41f54550b6811800e56010940742010459200e103000344543d00c1e1000c0e00c1c11810b2002c2480030394fc004005a503080021943d104200346403443c500b46c0550b465100c003281d40c2c0541410007402144c042c07204d48595010045082d00030b040c1042625112000d0f03009058a0101140011000c0700442c8403a40002013091f0403070300c3e240c01240442c0e0100011401090002c000313804215072440c1084200340c145c4030388403500b40140050001d82e440ea11000d95045107075440054090f2801c1aa07130f20040102000b144940310071256000c0d40d48071410601c014000806800030004455000e1103c2d001000004140307844603602e4010940c1e0b40d07000e109d41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 446512877 1250 446511627 446511629
    0x60f01151704060f0b0d05011509020c190204110d09050c0105030c160c030f110a060e010504030206030415020f0a020d081b0306121f14010303140c0a02090a24 70
    0x6a01c0d0850002c82e00085241d00700c0c501c1c8060030440001c07001c0c00440080c003000559030040e1110307591070341c0d0f034503c4201e01d50310640a801d4000d07042d440e04401d0b906490340d0368200c2400c0c0042c00700c0101250110340e12900410708030b0707003c240e8542c0c81d100c25894041c020603030240c046441d445184400c5195500810a0b01e00c02d0200603c01400c1410070100910025910101180c040c590004040006070321100075909050290075a005410f81c014284101308045400100920a500052242e960791001c00c4030141c070380c1a2078858403078550f864900c0e03600c0c0c001140070441c0c0f40042403020785184940007801031900158222010341420341c0c0203a880e5a4103544a0503030b101034a03106100c011001c002503400003c00b40800007141c8060000724180002c010a010203030300d206107044112103090081c1150f464103020f01507415407650750007503d00b401116a01d0342000000c00c41440490051044100c41034002d44410101e00e0700d449020020000d2130101400c650b201208113000d448031201d400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 446514127 1250 446512877 446512907
    0xc090f0618070908120d05090a0c060e0409080a1701060c020d0609020f180106020c01110d1413080a020a08010207030e06030a0204090615030c181a0c060f0115 70
    0x110403650307545141a40d40c4001403102e001d00240c0d00f0300240d007050400504c01103094100080d92074440d8102c500c000c0e241f005c2c0c11094503601100009001c50f4200700a5400c60b08141013040d07090b0042004030300948081a00508480404501c400c40c0d1030308000c0400700d10f4655800c03956141e0303c5480076070b400b1619010103034000c3d18200c00000040d58550000080500003004919420305100010384000311050b10040c601088500410013a601044507a28990090a04160560141130044d40d01d001c03801e01101080308509032180035100e03504c2203a00340950030361420440c5807a00c1c480380d540c201405081380506051140010184410300c03d81c1c941e00c0c9c0c9a60f40286821101d820003403517400280010940302e03420480003c00c2c1c0720a102e000010500300c0807080c101c800743e100141c1140c000320401000c0c40044846050b60000441850b4140c400203400c003c1017004d43c0210000b2409021580c41d01c038801c550034400c0b428641d06001d0304a401d49e400150404803024001c803800d0310700d0400c207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 446515377 1250 446514127 446514139
    0x10503090a03120209120106030311030a0c021e0a030503090a06110c2b150f02030730290301180204021e0f0a09090506060403060905010b040c020c090f06 68
    0x101c1e0000380300d1036100640d4400100701608001e040300015503603e84500d1601e0701030b0354400c000c00405400000594501646902035402d043e40d02d07802800c85c0d011200700034031070f404240200059440703400c00e10110b00405000c410140c5d44030b152440d507992005d11031500c070b03100203813001803854883c5101d80c5007103000790003800940c0c902d07400340036158100107406c421b1100c00c0c000404002c150180a80071181c00385c1500d40398101046074803c12a1101603000c0e40303440c0100100106507420282c1d07030b0812945020045020b003071405001c3e00341400c44840381403850a00302d1440b13862005406a501804c152076158000c4800385d800c160880c0c5040e841c6a458034140920300e409440c00e41e014085030b9400103100c2105e4980c82d11910a207070b10500d001003004401082582d00694052200c00141c603080c0c5c010441800c1900015800d4062440003d010685507028207081060a410032404001d01800c148410408c4210207901d0308041d60b8031b14001ea114000040543d220000154001c05001c1c000e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 446516627 1250 446515377 446515393
    0xf0f1410050a1505180310060617010b0913020c0316030f020106140d050709060f0614040f03060b1807111b0d030309081201030602070c080303041106131a0c0c01050309 74
    0x13520180c0041c82e5051403039240f9080b214068405000c02a1800312110380040c10604044024101d512000c1d0258001c0d140d0200501a20255200304c50900200302c036900415040280441c1c040c1c800c0c801080140c1c040071a942c0c07070035001f01e600c40c0d4810703100340c46d4502c1403205e80030200d003250864801d41c10b01c0224076000b0b030103501f410001d110030f80d0b0260095811182d120140b100958400343c0c4026250b041c100403c021482e402500c2c100c0c00c40710513080038502854003016511401d07182c04040c000355514018602c1c103941d00c650141000c0071401e2004a10f20f85a040030b4080300000444800ca070040040c880941c1d27042c02451003500070024100040316010752002c5006000501d0304552040e0104240071204062200c154007c43c0300c1c8070301699801051601086841d030316407025103160300910030700c800a411025011414101078907100c0d25241800d03119240403a030360b40140020442c1c42003081c03019010100a14080f22003000325140d000c81c175801140c003848208e07499000da41107815 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 446517877 1250 446516627 446516669
    0x2a0105060307051c06060e090105011a19170708010603051303021203090f060a1e020c0318060d020406121a011209051606020307051b130f0f1410050a 66
    0x4201101310343c0071030070760b40c520420ba5a200c2120803d40016042ea84007200f04070304034109000301800f414102e420b12242043e210361802403070003208a203c4c0c881d0360300d2003a0300740c0300c0c40743c4607400c0941d81e00c050180c0c3c40c1c20001000303004050280221400a41050009940401c1c2d0714078551b4100d0f4183e00424007581000c5035100640c0002d03101150f030703010348080d0034082001040300c0d030f0080d1100d450005d54144801e000c99001076009000c400350f41e00502c4040040301020081c0c403080c6c070b000e0711050040c514010004000c0d204005041000b01e202060201d00c0c66071051204000c0390307043c0c100300494580c076801c0c4e4100304144101d144c00603042c44001c864414103a001032600310721030001c030340c400d45d600c00444040c5c1c40740350008401a8004190384040c0f1008006075150800600c0c0400c8039846804089060704a07202c019a4403182c940044048030b455541c000140400c12920070001c003540300b8415241d11100340e96142e040b00104c40042005d00e0700240050441c0c65180c5442600c0060701 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 446519127 1250 446517877 446517889
    0x301050f06070512270a0303090504020a1106090c1207050d020105070303061d090616050d0b0604050d0c030b070509030c040b04090f050d110304080a02242a010506030705 75
    0x4002200d5600412a0005241d0300090280000510b031441d03c20b0020500c030345c00d180e80d13004000543c0c07081226000c10000300b41c200c4151005d031141030301c0150f5075003902c1d0025140814041c01c01d500501c60031081040030f14010842c4421120101c601820307100240c030316166540b0710bd0092581c8918885d40b42401580104010f0a4852107810b0101d800b0303030381e24401c86680304030409211a0301c0c2c00c10100f18190307105000d0a5880302941c0290341a084805c94010240e000f1400d8205445a0700d040a01d001da441c5000d890041c100184061040c02442c9021800e03817507903200403101000f500e00805c0d400c50180c1c0130365820000c0a030080c489007030100c0800018184201015030040c0d074600c240c0003c5103220000a14140c0507900a0540d001410802008160926100041c0341c01c01c4c8024440803101050060781c5a8040702d02501c0d1201c1d503139056058907e4411804031000001440012401c40c14900d01ca00d0403030020100540c0d02e00b904128281ca0013254a1541908000341c140700c0740ca850 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 446520377 1250 446519127 446519137
    0x30c0414060d0c080f0c09090604050604022101060801020a09080304270f0f0c0207061103040e090c0603090f1c210b030a060b09070512010b03070309020a09050403080a020301050f06 80
    0x10f03a2807071040c59030b900519042190103d078100341600b090b0b0b0b658200d410080c0d19660040510f40c018460f40c907060301c0300da13280d00014100900c01c0c0d802c00103480703022040741300d2154980031410003001843e5545640c01d0013944001c204c807020800004000803500001b1058500b01c41c03d000d000510054491107042c40300b0300c01604c000d500c9079204810060a1854172524003e04030f490f0000550a402e03000207868030035075a000100304078150b00e400c0340462020040e0340440710340490b6032400d41c80b040f50817410940200c10f035a4000e00003000700900d0410008208491051803070617140d0100c004001c8102e410b983c050b0324004200d200c07107898a41d04512011291060141d4800600000f03410000390800136015015903c00d6202d42100e41189414560150440c0c40b40c00e01e14174010b80000306e52041c040c1481402c41000c40400042e400501941001d80010350003020503410300d407280036000007043c0c1039906074001240d00c0001a842c0a01b442200c0c141c840041c58603620201301e0040009641c05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 446521627 1250 446520377 446520383
    0xb090a031e03060e070f120509250911120a02090607021201060801060f0e0c12060d05010605090c190206040302070b09150d092108160c0b15030c0414060d 68
    0x19820b070015402c0c0040d148a4005c1c501e50340c944408054960000f040e001c3c110490307001151404e801d0119980000400c0700c00312035809031415181c4864a02d000c503525075030b844076441d1414105100c85005822006013016000c840c03001c0f0b6076455003880c0700300b02c1c01148032054200340e04200c9400585000385490083c44000380011500d217803544401804c0d28030315400440d4001e40c416013440107140c185401c03039000d02d50120450034842000750240d130036070000e01464054140e00b0321103014041e003034000d071018150103800c805042c28080c00c0100345601424901d4080310300b200843e10041d00c0400c0c002c7c0035030b4141e0700070402d441c01c2c5188043c0b0f541c88003440c240e20040017006088100c1c034140203000950100c3c4800a81e618041c14030380b1300580440c0709445c11004c008010315285030001e55103074014035010605108001c006c80305444100c895000a008a00030b0020021400d40c4054100b0f04c0c1c210a030140c0707034850b200000388000d036008815900300100611000550500707000690343d9a00f80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 446522877 1250 446521627 446521631
    0xc010e03010e611a03040b0105030d09060809010f09060c020c03070308070f020d0807051606090e160c0f05010203160c080d0b031f090b090a031e03 65
    0xa5881a1a86007010814031540240c0d88010b50f00401c004104503050240a10300c14040303d0003c51640c0720409002010f1400ca0508200103100c0440740c104082d4041c02001095959001e444520222150012582100c0305103030750300086010709001c60742443d00200d68450b0a01d1a090084c142e0b07290728010720080b81d541d41e5403e0201c8801c1107001d40300010340500710000300301036080d0000303040c0803003520418001e500c1508200002007078041104e000f2604008104c414466610020b404800204402340544401059080c00e1040120302006403420b400440324941d651008140c03801042c2d4450304a40c144040005103c014003034504403400d203200c1c5004529000c1035a02c809900318603000945103031798040200407003600e030404c0c00e0581407a50f00b08001a40760070703600d0b0103251140b80c0c042c89140d91640000c42c000d0700c0c00c10861203081e080b070207442c2980c0c00350b402050081603007400c2078a00ba2481e9001c503e03009004500d08009907010740e5030f403810300b4084004640d1001e40301001401c0503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 446524127 1250 446522877 446522891
    0xb060313150c0905040e0706020a060911090c0310090b030337170a0207020f04090203120f09030606040e031e0c010203070917011e180506010e01081902030c010e0301 73
    0x100c0d4070b200ea60081c01e0542c4840c6000d0b0300b06801d0004450388107400000c42c0e4040c0c00305005181c2c000443c440e541e03501150104000d441480c0a86070603c4600a44d9005202c040c2032015100310800698851011840849029070ba56102002030b80c0c00240302c02e425800c10000b030996149030703280b90f60301e040910380140450310100d952030380310821490f0004005507610170b28a00311314403072a0084c0c0000380400c1c290308044007074000a114800314402c40748225a1002d085085407814009030709151030482d1401c1d2104008051500c0503448070450911070b000e19400120180b42034070503a250101e04500840c203220054008400503204540c4050031264244443e80c903c29090005500c5210b41d695000340345440c12185c0a6000e0b001e003811045a41041140300f182c040c1018078034442403944c80089010000300b0510008801085000f4082c5c0c0540800070403007020a01d4414100d4410800711344059491601c000300c5001007440c004e50503008001c641ca0a98450342615024550083c00090a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 446525377 1250 446524127 446524163
    0x1110403060209091003170307020f012d1e0504031112070606150c2303040e010503070b0c071401140a0c0506010506130b0a090e0c031005040b060313 66
    0x590425801220440e400003240000303401c20000050b0000eaa48005c0b0300c0e40e50543d510b60041039544409000c140c200440002c0415100700543c0c1c0b4007940f180001c00c1038540040c81040500b0300000103e103c28030b144900d280084061007660242e1200b00b42c24100c030040410b03420043e01001e40700342c040180030750b01a04088002d001d01741e2550b0a090900e40c0e21002407800006856080e031120410000c0000f40202e2140c004000c035003d142d01404414410a8840180f403078911a02d0350b0815030b100104001c5400c1c0700d04a0041e058440072411955199900c0d603110f5050300c500c000303119458000480c10013845240200000e860a414105050380225000c00160070741c0091640c000081c0000c02c070441480011b0120b607002d0401a11520302d00955000f00355050035032480744508030030340003801100c403600c126000c00180150216054960600c50400000c1d07420689440b1f030190651000082c19280c0380c4100050401c01406041c15540d40d9031444805089540c8191840800b41c110007042c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 446526627 1250 446525377 446525411
    0x3090b0109090b0f090c01082806030b01090c0903030806040b130b0a141c050a050601060504170a020f01050706090204020c1e06130834020102010c02010908090d0501 73
    0x1820240a00058038000790034810840f901c040c05100400c1c0f0740300180600c50070082030380000c000c000c4c00c050030940c40702a0a0303210180341034401140189404440028004903400190440340a03030201c1d02d859807142500000c803804041c42c00c012459012007000064010001d039540894001d0000071400b10740c1000c10420341548500100c0e030380c0c0d200442c082c82e15010500d40003034006018940124102c0002190b0001f2008090510f00000c2d8503a036010018200000f0500c158480141d43c41540d6400d4058880c0e0082c1c007071840d0684100415070b130100400030f005075440b5002043d0144814001e001500c660341310410941d42c01b503c1c1c07040d0502580342d80c0000e10390303210050000d10a6801c0342444c400ca01590300c0d035002c841d030460300520516a6810b81c103946096013080b1041c3e62072480c1e03560041519100a44040b0710410701460407244009010300024140c001e030020710591b003040c0c2049089030f00e80d6000800c5820140b001c4040d50a11801c91424a80704000000d5009450411150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 446527877 1250 446526627 446526629
    0x3210708011a0d0204150f030b28080a0302030405120a03021209190803090406120f02011b060f05010e09030316030f02040e09010506040b0607080a05090a031202160816140103090b01 80
    0x20f0201e407001c52070310955407100031401d11a107103103400c10896278500005082188800780200e0328440040d0000402904404284020b140607801c813003141005d8540a5140e401ca071049074483c01482520906512000c964448002d605502511009402c10001071094000b02d030000d41000b084000c403580f02d003411540c503016081c1341000f10b131a1361603101000181c5000d81c00034440029031038003d0300000c100702d907441c2d1703c517a0900300b4030705200300501c40451030421514050702c018180f20520f60003005991215042c0c41c040502a03101b07a03a505845652444261940008070100248562895100b0b500c0616001c480b030b000545040d565120702c41c02c81d80103031030030001c44e507684c4280242c500d001e02c01c00e03018103829580603042004a4450201c0c40c0a00c1a601e030500c2800500ca00c03d40d40c1c2c1e144441c02070340d0302c24003c442d0b212050720001d6540e4144c1342101c1e124880d0a1020400c102d002914182104080001038051800c01d0245012101c900701583d040c0f41e29890604002400720040c1c0d8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 446529127 1250 446527877 446527889
    0x122104030201060e10050a0e040602070206030c0c0118050d08090313090501180606080103151407020a060c0801080a080c0114190c18050910051203210708011a0d0204 73
    0x70a44a0802c2030000c400da001511500440b13945e243c0400441e00c4030181601100e10744034230004681ea541c00c003071020348100400203602060001c10050341c0003144015100c6100118002c000c900e0b25445001c0100000d10005802a070201e8251841c6a00c1070042c181d00100801c284c03814409489004454040c40c0e030400c0300141c0d1150700600c800031a40c0807200e20311181103003e105251804902500168042c003000c0c0c004006044111a81300203134000c011880307003001c10517900c1c1c649004004c0d141c101075001260300c1c60500b4405a200751080c1c0300641a28510000b406110b069582c4455880c0d000c1d16000d0083d54a580034600000850401c01d44030b0030545441100b081007006003d01241e10168a06040c42071131b14403203500a560303c00c581d003901d4095814505685079400611510b49d07156022580c400000d42d40702c401800c000c800f4011484052110b820044045500c80a02c1003007203500340005207440c40104003448a11021017160904840340340d140c49204000d2005903800340c2c010b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 446530377 1250 446529127 446529131
    0x50a1e050f120318010216060c030f0b03030901030f0905030d05010303120501180c0e030f01060501030b0d110d151a0112150510050c01020d0f140702122104030201 72
    0x44080c888180103540c8054082405000e440b5461150b410031808090941d8004030741c1d0320740c2d10085075025070413241c0c03990300704c20b05071860b0005150030b102800748104031600081c01c141640c0b085020f58001c046400200802940c10641041d0046000b400c0d01280402c2442c0c6400020f8003048050008104000d103071240410190704508010707040312049600d6824136854007004100800150705010300c03070b110803440818403101622048441114080d000c5078035020f041d0441890303040540c09442100c0b400c1e281071100408100c00c000401c5034860002d000c1c4014a11003d419190000c03d1408492040c15204400001c1e540300c03a0880f0f4040c400aa00303220310340c6242100b582c002d80844051800381d038040c0105200c0e1152000085650300c1901d00811782044510f22041c0608140d42c0007000b054000c45d2130302032940481020301851521415028034000301507110301214544103101e0340c8260001c1c071034158040f10803002c541c81880c101c5c4030080a90711036029041780202d0140114041e40c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 446531627 1250 446530377 446530433
    0x10050103050a0b0112080304020f01210c0f020102090307050409030c05030403030c1502190804081e07060b04090302030f0c0c130212010509010f0608090f0a03090614030606040b0304050a 82
    0x200c0181500f040c1c011204410806130000c0c000381c401c104a0354015419035101082c94051001603d90303280303041654bc14803081103690903050a8507402039030885400e44d150320101a92400a078201c1c0b280502c1c140d0144c01c1818144030b141015042442c1042c401d04d40000400030580301d503402d503081504210005a5141d140c80240a141900000151205c0c3c004503d402e03e00380701c2c0720424408040ca0002d009640d0005028001150262240c1d50b4100124080d000b10b0308028018991083e04201c0d150f9240c607500300e40c141814450800040da043d00198900441c103280c00c805030f00604d0300c3c200705201d400c4044000d500c48098109d40c070081f1a4001d601c4440070004200c030810140c0000d80a900e600004004540c1c414041000701c038980c0c1018205519014545800c0c415039000d2142e061182c2051207040550011401085135061796030189099804021820310744000d41d4070301d51290042c84140302d041607a04c01113801511520460300ea8516641d80c1008000f85200800321956007420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 446532877 1250 446531627 446531633
    0x5070302010b0901120308070c020307090c1103030c0f0d0906090305030a050a0b010203180406170c0901090c02060a020c0a020d0803010915180b0d051f110310031410050103050a 78
    0x944901100c2107030390f0750b615818020300d000b04061701030300a420006850007055480f801900070165454025081e5902c058039000508054100d4049400010300c121610b11500d5401005581c00341c2507202e20503141070002c3c0c50040203604a20503ca4038540c0c1d0340d40d100000351286c0b01c1c4800742072007034650342d440c1e1421100203803c403840100340701c0183d400c1c081d01c00d04983c1d0100440708a01015902141c038000c651003c240100541d0300259502c000c0801030542c08200081d03400781032078040f1040700946ea01e070f04031042503840a0310781c04e0246c0d01c0180032440c50b4805401406440880d203007200c50300401c503000505100142c903012b030744450000005100e80a52406081074960304e080c15250710510380840010b07090b10041c8110b5000d80d03180303401451543ca04c20107808940c1c00c00c04075075081c000030485200340c100341020360b011142351a80a4580c10711017415a84544c9005030400105803035502d4004030301540420032a09070281100c0e400c0008280d101e4140071314000c00041401141e545 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 446534127 1250 446532877 446532881
    0x1c02030d091a01082103070c0206040f05040c050c190212190212010908120c190302190815090406060b070804030605090601050d060c05092106060901151b0507060507030201 76
    0x207040141c13580c1184045545290900d00704800d41c42140b40702950b41d540e002c0c411504e0080c41c00000798440300c0001c0025610405034000c109a800c01c0310b04100c0200c5411041d107040c481d0b05c0602b030103a0018400382ca1a102421070229820340090700d0403a01a250300640360803c001e034481c18010401510307a25081d030601120606142040100030070408a060b00c1e86c040500070a00d4054111031402c1c00110304484000558400ea66041c1d00c038140388480d004c0281c0690042c0d20304513a900e001e0721103080317902e10032280e143c010f0400d1264110052026001d011901100800031707988651591400184000c000d0000d2034158001c09690b030711141146011400e440018101145a90007440103202c16503d554a92500c55401203000a001180f110151000d0064003040c960040c0d1400d0385840b0303120803540030328441550509440850340e420301006100403080c081c80703400c200310010012200780a01c005003080c1403121601c2002e13200320391300da5140c80d0391600100300051010030070500f015024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 446535377 1250 446534127 446534129
    0x70305100b0a0e0d060f02040626010f1404090219050109140105090607030c12051b0a030e010518060f120c04030807060f02070c080304261c02030d091a01 68
    0x300007864a0020038110003405601c8121240e40325241d91407903081004210b030b1018a100f0314441e401d644880d92550b0180c00c20105a1980c0904843ca41503110148400300203241a02d44120181801c4d5081601d0440382848079407134242c100340d4841000c00542c0e101d041a800b00704080780700015070340c2007400040c80c482d065030065941c041d400f410310314203070381140945071054416250030781c0300c1d0507a0030212910009014040c200000c040382001c0808c1d44880101440c1c2100c10000b01c1c0b04900c1403081e0740d0f0302c1003500040c0004800200c10300c420761080d0018403105050072440e09104403c04001040d9a00c282451100c844000036075a041100c00f4203456401810500c2c00c9080c586140c60b1206a8440c81400600c159074841e212140614183d05848500340c01c01081c04816485841c00c540d250310600580d1080710034900700d940030001200044407e07140003005004001d103031002681541391744410a43c02e50001b8003020482c61007520400e00c5003801035840000c0030210511002d540501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 446536627 1250 446535377 446535389
    0x5071404140f0a0b0a0203030a0b0108090a0b09070e090d0e03070b121b0a02010e060a06030c03060c0504030503031302180402060304030e030c19140a15230307030510 73
    0x400e0104200d000314a40c06460701903426144041c4403880000010701c0749001e500007003003c02c8082080c1d20354a500001544c07080e03214041c10008001080015030380c4401c11a0110941d900a80800d4006aa003880705608800d60b0310884020302d4440c11003c070798280c11185401541e01105003089025488885000000300607030140c10080c0c18442da0300c80611416541c1007030034050380e0114038401c02a100c151700c1d41183d4400c09440d1041e1810090107403482c2d12020329184107001c0422502c104621806080741d901001c214451031440ea91903002e0000c055903641804801e00001010075420300c0110701c0340140000c503d0700084030384108400000030449007a000c000410403c00143c03541403c581e08075400d4180782810010820010749041034038019540c001481d03041d070310750507420b05030324100741c420681c165004103040605000c050f2502d442001c00907001100707020503003406410280f4074880071440c0300c071040880a1025080e0350042e2800750022356108100150051850301c0700028010f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 446537877 1250 446536627 446536667
    0x7080f0a06060e1608040201020304050405130302010c0e0d030c260c010606231308190501140c0405060c012901030515100e0118030303140106050403032f100507 71
    0x818284041e0036081350003403401803080d904041030540e8020401ea400402008100780103514001001d404540e40303002c8220055800c01031540c113164054611001e1054016082d0b0164121648081340c41c4040d204040e600c0b4001e002061008401340040c040c03003040d1070a10a42e0761034248440307600f1202a54840b100300078515560f03046803213411010300c6041040300c03145034503807100107462104404290301551036132251349045110585103528004905020f140208841c0c0c0a20410114180044413000241d00082000707012074508400a0450417001d1b100004182412418804442c086000016000e5144c10499080f540e41401000d0f032084220700c3c500c0d4040460390205105000400010b01030011081c000e08403a4821500490740c0040c08460924580d52030401400414000741c10b41e61a66040d0000b1603014000d0b02168201e0b0341c55036445802a130540f0119001e007102c2e0144a145508102864a610000700200c0715420300751000040c075814118400f80c4020560300403091005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 446539127 1250 446537877 446537881
    0x302120702031e0f041205010b1e130908032d07030f230105040507030e0a08031f060503010b0f040b0a0f0305061c120c0f0605010e01061106070f0207080f0a06060e 72
    0x801854145d404481082e0400c81312840607151403400742034040c2045170441005046035400d0724001440080820058900d04420314541d81d001050300c400c02000390903c0e504101060500c2422007140f08030788100c04104914810042140008106c141d40502c002501c0d02c0e030942414035070303100d10356040b40c1004030300c0707000c140030000c200a0305014840d0a01c596074680010300380da030090304101000005c1e001039410b44011443c044400f50001c0d15041d106038800520480c4900142c144103040d1929074030b0b1a42140c1c42c000f19251b0540c018207810304141414040081d85a541b030015000b01803c03502d905280101c10440182203450060206215136041c200c100b400d607041c0c00c08021069080111210071f010340b01020b64100d522030b480140b181840360403a00c20711004c1d81c01241680c03005514124541d80c0c60008a40c04811400c0d141202e420003000300b6005402256000030400003070042d19840d0b035943d0b0f11282040c1030380064051035040244101e04010b240d1061001a1000c0212900c140c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 446540377 1250 446539127 446539147
    0x40c1e060801060f0e01121107080c0c030109170c011107050619021c020304020a0e130303050a05040b0a0b0d02120304090506033d0218010206072309010302120702031e 74
    0x59000c07105c4141c18040070f168074446000d01508040030ba26860030205a46000c2d914001405e50302414040000e03000b0311500a8080c641030007480711441d0403131941000119184040921644100e0704040550351302d4a0740040c50030140d0203400d20034081c1d07000e002d440c0b40c030322041c01c40308020f05040f0034054810805034041e01c4134168a440c0010702d02100603100d90700d91020402a0080750806480e607191002006101c0d00c26140c095180740c800c3d81d0502454440f9000c54081d0b90054400610840b00d07100010102c07100c591180c90302660041030400b021205402140200d140340f81c040056410019080c800309017503000301d6802c040103400405e541c81740215414108101410414140d4803018100e840c1c80051100c18100d0007502070741151f03071b8130204004bd0148088001c80c1c0e03016001e0600052748940c09801c44c0034030840c10303248c5c001c0341c011680000b1035103a202c0050030f4141503092142c000403034158800a4410b441540045075642078130200140311802c951702c43c0c09d044908000203005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 446541627 1250 446540377 446540387
    0xb030f1003031e02100f15080307030507020f0f0907031b080112060e031b0706030f020c07060516080301090903171005150904090b0402040e0d05070b040c1e060801060f 74
    0x280e5030300c2c0e00b4a2643c0e00c1d510081281410760140e03aa1a500e42005800352aa4104d40d00c6000c000d00c490b801c29414aa032900e0007601e9005240c0e020300405e109109880141c10048120000c3c0d4000a00c803442c0c0c55800300006584100680d00300b00041c1d504c1050710300b03803407005a1440c4241c4540c01c14114a61604a01801c1f48501da0001880b0580711070280202001c00c105072203039441c0a40c8403400002030140c125650321000e108a0000034140003520310150740b144229144c05030703090040c201c030a06040c400c0c0c4080d4811b0b41d0007000d0b121000810b80c003240380640558040c01c6122030105119100d4103004250a40207040c4020082c40241400740030802c4005181c01c590342968211070a419810740c5400301d004001d8240d4100d4100074501081103200c10610b0712680c070031242000030280b402c1e020303a42e075042c0c1140c10022940c10481035001c1003641c040303680e1061160740b9094646440d410b0100350346280c950440c4060002d200c1c1442825080152035014210703902c0c086090b80354290000708 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 446542877 1250 446541627 446541647
    0x1050907020703021324030605040b06060f09040509030d020d0b090a0b0303070f02192904051806040f06060903110103050f06010f02010603080c072603070b0903090a0b030f100303 79
    0x400a9610070318030501b1114070320740d107584054000307061400e56aa820030101402040f2000c4a455240c1400260185040c00640f40c07203101c290003041c01d00e410705051200500c0702070b00e441030621041c0410741c20384425000401c055503180d0408030307605020f00240114004040c21501c0043e0901004008030740700003050f5800f1a81020115140003010700201d9030214070314440c0428550800da0214400c4030401190f94401640a051102d0010041c0c0b171a41c180a24096258804d0030340c40300c1c0c1d1000e02e018880580001006000280e5941c0380054130044600342c0c1d10510114006000402c284a000c2d050000365010a00b0148118600306603034050b04800101134505200040700e9204043d4800d503c110003465219103090381d078822440b02e451b82c0c0c3d1003030b100300741032032128100b061601640500c1c1075440780e070303180001c50816070300d562440c400c00b1004000704030b40d10017480031006641d5000d44000c010800d019540d42d0700e0506540c030241c4401c004007210041881c041d010070009a100d50104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 446544127 1250 446542877 446542909
    0x901060501140d020c0109030306060e0d0c1701020f0a08010e010f03080a1d041a0a0f080c010c0812010e0105091602060609150a080312010f150516060f050105090702070302 76
    0xc3d0396141007082d0000240a00300466605601c1c3c40d00708002c140e015800398060f9407060f19202c41089500082140343d143d5044000c1803201c074601c0400814400e101100030b04103c0c500050700307100044001c4801a0005944d110004807000c00401031a4502050107008d481940d2040c880386003162242011880343e686901f0400c105524a001c0050280c40c4c031205110b8000c0003849041c03050f0b07403564440382e00f40e50720714418103c48400084112800340038000301c602140245c500404448010f41d6101c030a504159124070b0100040e4250b02e201408090280a0040ca020340239410030301402040da2000700103101c000380e40d5104460054001441e00d60204040745c1c0345020741e60f03807194910b10b0444140102c0c0c01c00680c040204440a0100280480049011040009aa8035030788900f942d080e130b00c94184035491150030b03882517078811002850011040701c2110740d14041e07551980304079078080300940d82080d6a200180050b1801e03004040c0c00c110a440202055811500054504241711a200f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 446545377 1250 446544127 446544167
    0x60801050109030f08070204020909090106050a0603020c0c2404060914010e01020604121101290f09010605030705040e0c0c0705010513180912020f190b01030602070c150e03060901060501 82
    0x81b0131903456070119000fa110140040d4410306004000c0b50181000b406264421264440041007061085c420b5510711005d042c001e110704000401404400108581c40d180c00807403100080440f6034a0310000e0000303020b1036481185a600d0030542030a42807405200c035040050034101600c541c0c2c0d0009020740c00c03a030881d418060981400c2c0040d5610340c500c1e03080840035400c0c120310382030780400544661450382c00140340302e20040502c407c000b40c03222070340340060b0710910031001070140c940f041019560258050508614141d06c0308900c840c650000c50f1a41c644240001c1e50114190341804440700911080c20000d00b4403040c0a003502200d12107005162810040b41803441d684851a0801245107410070341100c07210188031002510340380c3c0146080603900c90070f010b40c800b0000711070800d02c9458005500100d0f42e401c50352520041d50080e14182e859188407000418002c1190303502c450340382980d4907003c0da0414050700307241c10100010107402069240580420940c1d800060030040100510780d5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 446546627 1250 446545377 446545387
    0x1050901120e100c020f0601090b09010303140c0a140c011706012304030602121006020703030804060b030601150201060603050f061005040b0f0403060f0506031c020c090907060801050109030f08 85
    0x15a103410b0510b0300038009107041002d001c4c506070300801c1588203040204282d8039580c5c2c84030081410f441e4200803554012505200400100e0720401c844028001c15034a01807034003031204502d51900240303500648121100e03220010310030030204401028414207081900c07003084403c0b0381c0024124004c2c6118144044000040c10401146240c07001c0c0a0f2000c2d00c06441d00d841e41000700082d04103090388141a1004008590741c0702c21a03441400301e4505a0043c0841415541c084805150241c800c40b492502c80c840c00d0f01c2c69078140480b030301074008103881c4481d081c2d49a00003401e584c010350000c414540f6003000d1041c52170030444501d9000d0b60948001750f0f07c0318030820882d401e108541c0440480f8a001c514000303071100c0d45c4c00030700440303000310400d004c29107080f0b5442c0200ca4069989640c5903019140a2983c0f2640d1300000c0006002c90040c1d848583d5201c010450000c4221400542034125178002e1000540041c8030901510080c42c1440c1b58038150b60340c1c1600e501e01d1390380c05055a600411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 446547877 1250 446546627 446546651
    0x10e030c030307140609072301090518040b0c070c050d02210d17060904020f06160b101707030305030c04091e0b01050901140c0304150c05010b0105090112 68
    0x668040300805012a0742e140d0207414907110004021080c0c01070303070007110b0104202940010b0200c095814122005d824403440510900381c004c00c003007265050110b1100300003a9580c0700e0280d00c1e01107140031010f264500d0315203055800840c0c020b10300891a401403101c140410414642542a03401c25116a0a40020b81c000038086600c1241030091801c202100e4214100700401e90304007007801c03074594101403c14110381071100e820496000390400d400c8000500540b6110105d116010009446c46140c601486140343c1003082d111030981c1c400c40203509206000f82c44200d5603000b00071742050440401100c46007551214400d200203001c2082c04404200140d4072034084800414026200300b0154801c5808101c0208074101140b007540d00d4101d50b44c40030750145003160200c010503924024075451f0214100c603186c0000c114204944018840031070300e00800342c085865294161104036038445c86280c60750a4a0300c0e2040c0604005040c0710b514002c1c0d800480481c540049a200443d030104110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 446549127 1250 446547877 446547883
    0xb0423090c060703020d0f0807050d050619320303071403040e070c06140705220305060406050133030c0c17180f0a121e060b011205070e010e03 63
    0x1c1a010740c4254006181c00806030005209194a0100d441d0651009560302081e07446040031144000032800070044800403020702e038456a4482c000512800c2c401540755132142c0d100c000340d001042e041d0440442940703100703154881e1102d00c900110100d04030000c1003010030f0f120700410400401d00000a10035000008081c82690058000d0200151651a1940d802071444a8441c4c00f03035005480c051016a4800d84041190f11034452512010302c0d01115842120700020310483c00300720844450750110001d9014041140903d00418021845504003240c3c0d0442c0e000f4207088808695100745666009100321910b003018248070b06002500b564400c0041c0e601008110006000d0b5080800c0e540100d0181005404011401da2540c2580050803007030084009410a0841c0d10800d000010807a0307640c1000600c8800c0d00c907a846800c076000003501214103014002c4100e542640707401072070a10b0b50f03000300c0540001c4104002840f0604003a0006001c2c800c088480e070b41001440c10121100351020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 446550377 1250 446549127 446549143
    0x1a040c030f03090e06010c0209011701020f12010f0f0e010302060d0212070201050405011a09061e0901060224061807031e020d05070203070317060f1e040b042309 71
    0x200c00003801d11500e80c030b40185101c050780500f1030000d07602008500303d94800c0f200951004d501414140c0780303909180060446c4080a00980e040359000c010300c2d4007002a08000c2c01841030a41000c07655541000c9420b140c204071078204041d50328040d90100504458000098112034065440c165255000b0305004080c0c40752604110070403082d6812b0003030159055000510480c05400200a0001c40c054201d8215440014407644000010080359071490008409500a030303002e810505000266804106502e030300740d0100026070030010041d401810b403241c000e401100180e50001c2e403442d19100040745ca00c0b046407281d100405903000180f9050007075020030a803010100a80c4030780c0144d40c0700b10700a58003064141d503007075081c500400c07580c45c00003040d104115459210300b068030101c11013003800c01400516047e400385128100170500e40304c01801c000c03003039a2204901407010b4250f00340801c0c0c3d214915a036000c1e501d001e20801d2100c1c241002000140070640054151351103c0708014608031003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 446551627 1250 446550377 446550383
    0xf170601090f030b0a05060f030703080d0b09040305120108013806130906080f06071209021c051603020f0103090303061a13090c05030109091b170c0a031a040c03 71
    0x6994408800c0c0404c20300064401c0f041c4403000d01180e5130b0310080c48585000d1078840b503010340c0281f005000040c0c2d000047c0c400c2102c0800c0018119883c034000414920080d10181c0225200003200c0480d484056107039405444540c0092000150f000701181c0c60554501013900301b4600c0301c2e0094480341142c1c0f20282c4007000102402e80b207100c5d2540203910350102d413260302e81d50ba1030b003840003440140c0030075450044030300c90000d00800c0ea2100c5c010b03240280031501e107401300e56031440881c0059039500300d40b4103083c0399000152440310103403400c103151441c081c000b494205084c0c0e0081005070703544070b04144044401c0c42d010a943c10755180036406040c00360085c0c116024400c610f040c4262000d005007410038445601a241c04c0c0d9982c10301c00c1141d201102c00300014100b003005000001068121344603c031301c22028070030f441101d104108410360247c0c1040342e80203003620b60a6401c1004002001d82404100c900060340c03490b5a030340a941d8000b402400c50f0801ca01c80001d014008621805070045030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 446552877 1250 446551627 446551649
    0x109170d09060e030d0614180903070b07050a0e01030e0c120c0d08071e0f0215070602030906040b090f0714010302091005030703060609080606010e06090a090b0306070f17060109 78
    0x3c6543c9264883d00048034a5120b04c0c501203000500450403502c0148044001e000d001c40f1500f40311000b0901e450041041e8464401040544006030807511404d1040030282e840c2901c3c0d800d1618010024145502840e0406003800c901200319200401d41e406440c608803100848605500c08050800501140c200e070300001c409580424801041c0050030b10612540540c0448818110540c03943c200d0500003400030a940b86541006003081c1e42d02c1d031400e500f404251420301c245541d0308005d0f644111007140356900130a052204000d0051040c40c2c00c0034040000c0c0440303c2241600540e2108940319005031351401020020141e40a41e044515880c2c025200c4109c2c1d40003008058600d41c419942c00b800603240010025181d44520014420b071022503001d81940e03183c0c0c80046894440358207400b58000ba00300611401507641c0030342e22004101c6102e010030039980c260100350500030000e202105011084140c3e8403525172000301c04101b0110028906a42d0701c40e500100e440b440307180c00c15030400c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 446554127 1250 446552877 446552891
    0x10807110f03030a0e0106060206070c05070f061806110c0105090409210807030c0e0d0501060b16020a170a020108040c050405010b0c10110405010f030e0d030e0f0109170d0906 77
    0x1c400400114480c502000040c0041400d00d50101e080728118443c41006801010118820310700c40c00143d100c140c041c2007251485500c45484540400841d404440400c550075501c002004130244114024516414901031000b07026040e1601c81031080709a83c104140014424059070b503a521a025281c0c01040f40702104504a40c1215902424070344240440c140d5000111078a100e402140030380380259607940414415081480305110200c80111015501d5000c00711317580703443c00c01400d40000462124100281c07a8014001a00d0721a000035001c11000e0f003601c400000001061004c50794286040d060790380c5c80d42009056100150081c41c0d2180c281800002d2003001080580005044002592003801d5808004812a54103440462181d00c082c0000c01c00c0350701a42c0c00a20703140e601d06000c10680c0f5170111203402c01d40c6120000740460b80d564846070540c041042016500004100204680442500c0e900d40e035409059900320340303c400003840c181301c5203d038000000c3c1c0340e44004140441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 446555377 1250 446554127 446554153
    0x303040e0103050a03110c1c11030d0207290304110d06090b010504050c0901021c030f1b02060c040f140d150e06060303040b1605120f130906030503030601080711 71
    0x1162130030300590002d200c141c40007808071000310750030f101030320010944a42004040301088854100c400e043d128001042821040785d101481060344490072540501440e50031320125116102426a501140d54100303049403001004030f0f802c980c0c00a412404182d54800040000740d0517000e80d850040c1414242081c0a04018078a0022416640c1c01c8400388066550140115900d02648079028016480003815403c012440c2035540e041000310714002c15101d03a5a001e0780d041d13a074000c00d402e01c08031101e40b00c668080d84c18414503802041d8403032454986864280c0c1c100840c42c85000300e02341d44a600103249019510340040ca202264050800010003002c0c0d00110020610740e5413400090043d00b000901910303021003154152a000000700d414160503481c02000d040c02010704a549106403918042c100e030008015002ca1114000115034884400c07002ca20705110b140c0c041e40b500341c1051010701c00240c1c00300599078026400e2801c5500351340c07228801c65140d81c070311804580034003440b00c1c61204 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 446556627 1250 446555377 446555383
    0xf05061b19051c0c1b150206340302030702031605060421050d050c090301060e0a0b0409200d02060f07060e190f03020307080d0204050f0a03020a0b090303040e010305 73
    0xa1a024200b61101d4107140403194141c403c90400a50008040070031034400241103042c03c80303040711540110019991180001000d070395161040b58090f0707100701d0820900f100418590f80e240d9204160900003c0740070080408180008854503061540100c00502100e10800c02c1c1e602d00d41050300d0381d01c01103000d1b0070182d454038420b50741074402d0304542c580382400b141640313142c10341950765a48141c07a190070070342200d00610010b004030794540420007440034070795400d002e07004c042c200c4140c41c900a810301800e031f0380c1160040340501c1c0c040c07820000c80402180308035400f90420704840b100030b90046800000200c400c040030130000e52000f00403900810b02c940c18070142c01e41910803402045002c0d00022400d039100846038004c407001d00f58060000000c1c510f010f5100b20745d4442c1c0101e13410311600b0307a074034922500041861020340e079020608100900c1c100d070062a440f80b0a03203002041504603004038070301342c81a005070142d01e0000205082d460b2802c01c110b8004162a0040410950b100d141aa403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 446557877 1250 446556627 446556673
    0x1e04090b04050a05040b0105060c0705041b081b030c09030a0f0b01080c0a0e0103020f060d230105100f0302160b01080a110a0803031b070203010c20070f05061b 70
    0x1c0194a41000035961001c6441110700540d001110900b45a2804080100d42e074802c2c3c88240c00c07130061070b5000415496501400c034480b0401c5d00300c0340c00b003170600d039000f44050001092100810720503d98080e00c2400b140441e40c1201c0e611000aa448000034040b070b14294550800030102c00300b54207103005101582d00002d0584802c60291048144c1480030050001d10a00502c28608c00c2040100018a8007569004810780d000e0902410140c440034800200c1d0f443c40309218411145151514039080c0403103016024000407074440780015281400104440d500072851001c0c19400600458030450075200b4846030749d482403000d88a985c50b40300d140c0d03d82d0328000d801c031044202d15a2072140e5261060704032040d20542801141503a640f8260010310070010802c00003840c008004110250f1003e028100691580b92500d050016107160400fa000ca0b111041c0e04464001507418092203009041c0c07041114412903005485954440c02c8551034407900351030006e40e21808404c0ca48245503610b90b55 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 446559127 1250 446557877 446557879
    0x5010602010507020f03180f09010306090308061f08100f06020c120c0603040b06041e051e060d0f151b090b04261006090209040f0b0609061e04090b 65
    0x800b440c0c94403002a40d4582c801408200190410321100004041c0d07412602d812000003071100e0045860040881c10b08a002c0c2c00a171990b0385c440c141d040c141604150802d270000300c00d40714080300385030f1000702c1a0700003d40000c41e0100544100480c5140f01ca0041c0c5c40094030405034101c020550b0354601139a10424000468010111030f01c00e156407403804a05000011800380c903080c070710f60319507071144040c400042456a1060752100d8030740c0300511040e841c906405009200054030f00301840d8030580840c1091120414810701004c000507600c2d10503441c080140c1c4040002007144441c034201e00320540402c481184da41c60700c1d4030448800300101415110062035120030529030348a40700c02c3e40c00c0c40342d07004268600c041e090710800400c985102c100690380019043d80c0180e6030350300400e02550300b1640041c92241e00454072149518207441480e41500215004001c5a4044c601003190781c020100d02c41c0c407582005c034441c948002083e07a550140b07103030720024039503c40c5c84d600310000a0601010f85 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 446560377 1250 446559127 446559131
    0x250c09022101140a060503090f030a0f1d1309080708070c050a060503040506070c060b0d080414370915030c0801020306010207090b0f090c0711010c03050d05060a030b0a0501060201 79
    0x1801d807000b2401c3d42003036540505080007044c14401d05075000d90002e8044030591107203041501000381c0600c090519034916569051818962500080c04448860b88104245031180034000700e65554808403500c41c2007580c0040360805190038202100e000e60740000d014400c0c0081c052080180c181108029100101c49805280b5252201201c1600080f20002c005601100200310003070701505042280e03078418400030030348c0502200852800c848151088862081c089800e1041c2d0885001480c0c5543e0300742c80f00f50910340100755071440c00d011261804e42c4848006810342c540c4080403007460140441a5091224003d00c0715102c5220740310f84020307a090f4550000120380e0381010b0003100d0103244164000d100140c20555504010718120001a606ca034100001a02035241c0c07000d824460030501469035200e2881e410581c02500c041800c036170401112202c0200060b401c00291036011524a0001646a440748080be40c50344c81d6400240c0850500c0082006080c00f6400c4541030380c03515802 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 446561627 1250 446560377 446560379
    0x9090c130606021c0c0609210e0909150103020f06040e090304030219122406091b0f0801032603090d0216060905240f0c12250c09022101 60
    0x2920413140f014060010020316000c0d00340d4041081900b00039a07071801502042480c01000b50a07491300c18100341e40101095090210080e13500d095a00300354400e070500301070b00d0441455850b075001007505010007032040345a00c40c0010740ba01c502c400c1d900a000070740c90f050070900740002c450303640303400c0352108920074460203180711590744e10300600404892071403400d100009c4550b03a03420400c40c0c240342d080000003154150702080c201c4500510303008004038080001c0e038107400c0741c0304420070284401200c240030401410f503a81e941d00224150442790028981c20100c0c0315482040b4081d61024122104804040207120030968040388640d0511030301e400301c0d4010750302180c0c0d0a2040c0b185100f080f01046008904002900700752010030501c4880c1c801c0d00001200200105145170410003400c00032600101d0001c0791080108001e4035402d0750291309a0500c023035581d400c045e509100c58640e1103079180302800010052100c0b55000641122041952910f00c203082400c4d41c0c18070f1030a81d02c510800c000c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 446562877 1250 446561627 446561653
    0x40630060e0405010b041125050d0e011115070f0905060a031406121e070509090a12030203160f0c06051906090905030906070515010b0406090b031509090c13060602 72
    0x301d0640c003052000c002904012607480c2d010f190641c1354401d40c811103540301d60940000c1c0300f44040d660522b19911600d83c15106400014a26800310707107080003039070064040c03030700030340d034814500354402c05c1c03807501c408005000802203a0080090780150f8200c90082202499603406812050a461004e107481507250354070b500b00400702c4a0030001644030341090150182c4011345200c84008200c1a50440e81c0300c80d070b20404200e00c1070088a849150f50403a0008c0c1040103140104030701c07501c08a02c2c0c00c0d811801c203810009a9907403101c018a00740f140c00700092014070f00401c9141010741d04034000300414034101b603c60320b001d0b6429980c070316a6441c000c0c0108646c8643d220340b9242603000402907080c00740810a0103599444103406445520886c802e0369100c01043c50094083c044090406d5141c0d40303061000f400494032508106020403082c41006403011025560142614084038101082d881e400aa2410010703442c1c0d0303031900011511012800748149411640c203c2d0b180f5070880f0b41d8100000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 446564127 1250 446562877 446562881
    0x1150c020109030206090a0302030307061d070608061c06020d1515080109020f0c0706020109050c10050d410702031215040f090609021005040630060e0405010b04 71
    0x2500a02182c0345100030700245c18524040c01c11103802a00c207104a40c0c5039000241b0f19082100120380c980d44480940d41411030f4130f8806044001d02400a140c4a1f0402d00d01828007031300201624014401c0f0207014601403c180520034100d40c100c14111b54074510611140040c05242840b81c400e5403018100080b800305c42400d42100c000c50750b507a01c4181c0d003840035a070080d50010303c0d03412440c002800340c1212020140590f00003000e030b64000080e0711100d850458108503414040522a5103103100d11a50385410008032440c000c100b100020f0842c10003800368290305e111030342c002180048800c58005031a0f16032000c0e0078480c221200c5850f03d03518464100d0fa0392145182000c5981800740114102401c00ca030700b81b0074000001c1c0003190350340000103a0b41c11200b9201c800e44809841310303100010740c00c10443e10441d41815140c01032620303040c000050411525648459104044411841c41c0f1080c000903040113010402c200344901d41d5901c1003441043d0040d9801e94855290130081c12480c6854 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 446565377 1250 446564127 446564147
    0x20918041b0f050913020901060810080706050702060a03150f03170f090613030501150e06030c010f18050d060207050f0705010e1c060906021c1428050405060115 71
    0x148900040c2e800c000502071001001741240d040010100c00d001e0059888802443c0a427281e69640a800c4c585694500c000c90029803005007690001101030228540c00b4007128009501907564507521203c10230214024030401030708c0800b403404500041140c0c0c04a000110890703004400408400788400e03400d01c094824802484140b40d020403540309603046c8940074060300d07204801550355003a03072030321002d0a51300c10031076210902c01031700b030103000d42c01803014000d40244046d0010300c02d0a1807140007801e10340910101000380140c00501210702c0ea07152034800042c7c04080c0c0400d0b802c0845240c00f90181d0400c0d00100d83d24050a405a460301500080313090440d030050b07444101e00d440510602c42104080b0554410110403488800c1c0418114003a00b21350300d20800c00180d5420101031400701035815108800c40d82c0b8140f00140640d05144c0d407110740c00c50b00c1c142102081c40f8114282c03051105606042ca0321031402c000800040c4100400d0b4203040b22440c055410080103d03400440d2040305d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 446566627 1250 446565377 446565389
    0x1b0714100b0a0f0527090d09080f070303230c03180312030f0a0e0102180a140105030f0709030209070905030c0d0b04060c0201060914091b10050a03020918041b 70
    0x5120f104201902e098621010466828a091038070b42420b000900d0004c2c1c070407140c5486c9503010082c0801c405500c40d608000411b400c5000c6c2032900541c4c04e07000d8454150344000307010071050128000201d4840494400030206c0305070081d0b03441c1c400c0c051032522134214501d018200002507640c44031078103000c21110500e01c80884101d03e103541e0041d07020240c40d4040e05c030514550340c1d582641d221070404d2004200c00b4261a031140d800c00140802c0003c1051103070810480c02c04040c07034010306a6080380c2034035000751640380b0017516a038450804030340e80e134603691010794011069414041c00682110482c000d81c0c40990603a0030000040c0140700202e440c0e0301004010310010400600070800e581e2000300303d0380c0107200104101c0e503940c032240c060b18044000e00400751103420602540d40c3c010007406240f2181c02c404007108024500001e21401f10800c0c1000a1142c0001c01d0780540d03110358115002550004c1180038100c0380d81d5880d01254000b19411aa031954400c9440c00c3c012120101800f1a05 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 446567877 1250 446566627 446566649
    0xf0d020310050c0409090f0203060a201b06042d031b0c081e010515030a08030426070218041509080c120a1d0303031b0714100b0a 57
    0x3100e868200100b60041000c03004040910004c1500f80090241490003401100f04510920150041504050000d4008a0b0180c50103411794603a420700d810708801c4800c444400c0340c0303d000c5c2c21810075a01040b540c14081a00484007008100300000d031460310320f654001750118203200080e42004140c803800d1409004690042102c00034540c3c000b4620403014850541807800607a60481036113840b401054404282801c0700700c2c0c00020900b482380070b600084c501001300701c4d241c01c400801c4d1107800450b4060803681c400000201130120386002c910524801840c8040500803510464400343c00c91b0108074499850b903854400040903c01d60b40b4045d58000e04c6603c0706c0042000d65070002d02c910b02040711101ca040c490b4030b281758414806000b0b4202c5106066640b05041c19005110401c445842d044040390b81090655a46001056035801b01c1545c0150048014100b2031031058015880024210352021282c540030307501c0440c19140c00c1c001d03d00b0030700008644204200641000740500400d8403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 446569127 1250 446567877 446567893
    0x5070909050709020f19120b0108040b010603020304081209010f0e160e070c02030102130807060206010b030a1e0905010b0f04020708070209040f080c070f15051c020d0603110f0d0203 80
    0xd0f91580201482045014428604040306905400c507860301088000825000c000241c5405002d0044402d0b40809180400d445e24050b40c03050400441070140004042d80130000904010180c3c040b0740e03441c01c5046014190340303800c4400f240a0700c183c6038002c41d03a900b0503921500325200050503024134107105400b88185410b003100d00b041160010312900400101a1881c4050780303017840100140403500902d105081c0c180031303045181003032590140c8210360000004005c40f803c1102540d411074048200492078100940c25200d0b250180d0f2041c66485103442407540400205620103050b4030019a4200a0480c00100308170483c06105409006031a0400c100c07401860107110080d8070510480100386010381c5030300c030070030290441492840f042d07001c01d80502104006c000c0c0310740142661081d94a0034111242c0003442405610b800312580000c4e03072002e060810751f40c1c041d21100c1501d41c41c2080040d41d17900742a60811030000269014804a111007200c3d07050040f1401c1d89250003a008000c10b03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 446570377 1250 446569127 446569139
    0xe0708160906120314040f03060f0513031d0d02060c0610060203040b0405130612120305010503060c0702040504020307030b1005240307121b03050114181302040207050316050709090507 81
    0x311584101751005c0200720110b4505004480500994041c0900241007180a441031040741c0003c0c00e00c0090320500341c0c9040000303a2081d11010440c0d95404c51f6401e61800c80c01044c59171102c800000d40c410b0020404401c004000154240700ba51049a00c1d414213a86220682c0c6034800c502850306070b03003001c01c024049400d0014640101c41c41204002440300c0d40c4451001043c0c3c121740d030485030041504081e50586605025080c090700c1c040b40900a82e050a410902d8580f081200c001d001c2c90711a4006020365030103200240045811914450f1507180007500406611034a000d081e02c01c88111054014038417100700081c01550064031010701e980c4980d1415140d04907041c00d2003d00c1d03074071543c940100b4482c0c5032051049002c03a413408201941094542100500103011103405145a0030042004503014071203250880b807240e5580c0d10980c010300110300a8400c1d04009851031100042105000c01e410401d04211400f0350259001180c0f508001019104c5400016203141e03c04181032000b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 446571627 1250 446570377 446570387
    0x81c060503062a04030305090910140f010512091c0e030a11061b010209130203042103380312030a050703020702030f06070e04062402010e07081609061203 68
    0x41038000b02c0034405400104400f405658031980088001600c0403d9007003507800c19042641e0441008944611190b0620800d0303a070940c031502c2013901c99810542c00304143e0340550f0864440400f820300081080ca8001c03441c9030f45c0c0c01c0c50074801e05403540c3d010500382024400c2c000e8021602009002d883c084116032112400c038180c154502ea446041002101c56281031508400e11400c948400036866114507010459030b800c960031008019801041000300260390038000b0fa840c18410011022700421502e001c900034030444143c1d4100c0044003091001c0060b040c20403040c1d909940502a105480150238180c4414030701e07000c60103000c4244045076102203942c102580c002340920b001400d14425400080c54881042150340251300b0800910011a600c62040340c1c48100540d170620400341b07809013200c2d01041d0343c030380c0c0d44d42418840e810f0701c2482d00c02e4000b03003035032000d1300e0490340004d031104155522050003100d1920003003003040700055407840038090007080750200c010400300c500301d0b0741f0b0a980b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 446572877 1250 446571627 446571661
    0x4020d02030111030f0a140606070212030f070807060c1b060b010c0206070b0a060b0a0c020f1c08042d12021908010b041812110106090504081c06050306 67
    0x1034155280c107940000d420b44040a10301c0342040d500400c5c006d04100c4071020441d41c00c17180414030011a04100718072901c1d0700088a049550540781d9503080d0114421705420341c007840e9640d9070b002d403002030f50070b0500c86150043c041c0140604010400c0d011020303001d644c02d400714070b400284003141440c5500402d405900004441506042c007400380740f1207a0020300154030044086484a030844140140d00800b407060708003405194400c1c1c4d2510354114000703001d000448000030f00c0f52a64551f2201a520340d5003506502e40e02c94456943d980165242c0451181c0040c021100c50080c0300202d444941e070100880304e514840d15100d00002d03414079120030080c000d411401c1c1d0300016030340c8418510b5820002800c0060486070000036000c0503040400084e00c440340107940500c100240351f14041601205444a02c1c466414001100f408a01c04580500525800705024034980001c2005101d40c43c401400d030305110140c00a0041580f0103540103c55084c050741c0e80540c0040006601c911038440c44030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 446574127 1250 446572877 446572879
    0x6020f0304030b181c08070e030a081c021e03010e0c040b0405011115180d0c0b0f060a030f05010204060314041109090304051509031c0221160317090f0604020d02 71
    0x181d54020082041d01050240c0c245c0f801c0099070314030030000c051341d001048061100b001c0b005420030502c182c03105070540c0584103c0c244004d190002c098403050050f4101e5800908900040800b00380701d001440341a0024400e03d035040300c1e2140007410410b80d0908407019907403020f1409042170308003001101c00360071403011640513110ba5205000040038030038140c0e2160714030f03040d501400107201c00c101d4145504a000d6500740020321f492070b0b0014025807006644203c94500072140e5965038000a030072401c072070b480601449500c0024806114040d00148107a80303198406011000d12581c00d09840e680464001d040031010503c1c90020346003852125401c50301d00412241081e032100f0004001095070074040c1540e0000058040003410180a4000328811304003d40100c4090b926020307440781c0c0f110b04114024145890700d10092080f24090301c805aa418940030456142031501800a00f44050341d40c0ea052704500029418200000d02003216605180151005442d103a080c0010651242422 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 446575377 1250 446574127 446574133
    0x15071404060c030509150c0109141b10051201060305100f030b0609070302130b030405100c0f1115070509030709020915480c01050f130905070906020f0304030b18 71
    0x20365031b5138581c88007520043c110304000040c09206840d041e0a082100c0ca0410020b400110441e07120781e01d00300b12401360300300c19103100310f41540050044640c2d21030803202c444900b160310b002154142c0d059000612888124000e2102c841c0ca440188140305003622000b80140030b024000380103814454039054000065080140c00e20803200d840300030704007050300702282a0310007200300720074030a04004034a205060440104402403002c04014010800c0f030400c034041c05440311074000504c50070042441d100c501310036101400d09048800402552028106500c64855141c012079628100d02c02c5551600004184c3c0010800484280e00660850b484d50003550302814803441d100020103800c0101e000305600420702c0000c050410000ca42a0129018040c0d8400b04c075402c0b0326604a01161544003584503442c1d126040c43c076803503030156016000f0138405810181480040d40c0c000749518140c400680039525180c0b04251016a81e0045201c0070b850030140e50045031107000b0100078054442000415 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 446576627 1250 446575377 446575399
    0x60a0509030f030c0a03170603070b0c10181101031a01030e072409140108041113060308130e061f050c151b0712030203060a0815071404060c030509 65
    0xd5086800c10b521041da03d41005410100b0103900c200041e504040782040087c1505040d408640c1d158400e00030349649078400101c20240d060100454400342c07951b070310140302c8803020256004241c5a403640c00c8540404555040805600900842180381e00c444000d10b00e04441100440c05010001c40100d228001c0740340200d12b5950b0001c0000c540c14049070a08a44551410014000c1d8000d520040c804401c0c4002c0c0d44c40760f80c1c0030603915082608114040e404508400016006c0351242610185d03c51803c1c0002040000c0c02d00a00b1000010504602c6200d656000d01d07400114103d9441ea03201c600402d00300040d000040380b1003108030061030f0050401d40c103041e81d00d280014003036102030b4462a0320100252080000210002050300403003080c18002155620b648102041a1080504d50040700040c103540700c08103107000a180200440d2940c0d0070701d020304443e294054904d00009070187c54036911812030882110700311185692080605911707902e04807103039005039104503401020451 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 446577877 1250 446576627 446576653
    0x1030c0831080417250506030c270405060a06020a17040e010e100b0c030306150c070e0f07020606102a1a090c13110f0a09030309080705060a050903 65
    0x3014201520183c0d5407422413143c1095400d141c2410300003801040c040300031034070b20b9010713114404000315001580c0080d200d072960405050305004103002c0d10207030021140c2076070301c0400b4405200c869030401d031400c0009844031014009581c071180280d00c00750f030015001000054082c1d10b49005030048100305030500d91120380303002030000b0031392018454000341c20034410f425151241800050491b8210103241030411a000f644900000744902e201e0300b0900d1440110640107405c4036241413844007a035209548540401c4051442943c1640c2070500c440c0c00a050346d030000aa26000740070041c84000f5902c01a401141d603864041e038458020f03020741741540d082c482c0d4060081c032a00d1068412045108420f1b1505d00300309001407400c06941d121594091290729000140c04070344414582c007140d171071b440c900c0400c0740f40311750b80e0840350096001841c408116840020b00055a1080e51004462540c94141ea0780d56100d070300070a54801302c00c0140486480c0a41c0003044650405010744410540f070740 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 446579127 1250 446577877 446577893
    0x50c0f031306062c1009050a0b1504030b06030106030302071a07050a0f02030d0216090b0d08030a090b0c03040206030601030203060f0d0309090608060103051b01140c030901030c0831 80
    0x50300c100949003110045484131550050688100508424891901d19246183c4000c8940c00d22900510690b203401041c0b501c0c546402080d820707080074105100100304041e03100d00039841f5201c181d80209000c40443d20310300c1e041c0079400850340c1580c010135100b07084c001d04070f2814032901e61002c4801410020100024814811300b1300032409241642260724190042c1403e100b00391078180215000301091402d8035800391844029540d6038040011024800800700303d0340ea900007800ba1200300d01004110041800360401f00f40305100d002c403080c0715146e03099000c80c1ca000c20b403070007507000340180002241c03540310b907000c0c2d54050070040550390081c0340c100104142407007001c4250001203154100b8010f4184d58003070503008018000090415600d9500c07480d880d000d20260b41000c4a07038800d92450560b2240c240070411024440c0303129a1403242c2d2418664070f83c0801c12540c0428242071100b15018000d0014605c1180503d0030200321000e00006504c2482001c2180a00d85e540349203010301051800d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 446580377 1250 446579127 446579129
    0x31528090606030204050703020c1e120c1b0105030405060103150221060108131703100b0f0a0206070c0308040b06031e03040504060806070c060b0a090207030507020112050c0f03130606 81
    0x41c180020024118010301058070360040031501418010421260440c00c0003586119403062050000c100c4010038028a003001c0050601241500020500400040020074402c4003092752030301014000a40c1c600645a5010442c0c001d03040b504400b00400200350203070200d90384c1c00c901741c00040c90034aa03111010304039000558000340c05600941048510b503001940580c201440b01c60740013041c401a03961445013012030904c40c10340107010012072050310607036041c07030098a60b00b480300d500c0b0010109004000d801010b0300000500c00c20010a60389030050000c4861035415070707600c51160745c0d1a00c903181200805040350390948100e0a181a4000200885a821240b000c0246640320300c2d1200b00320584a9070307000450b041d004401031140954002040011f050303801200403446026031000a10b161060b58030501900d40001405020580d2060040c02c4092003601c0b08482192643c00d40e408a80085503014010641049000082d07488000650350000030508201c1248005650f823100355081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 446581627 1250 446580377 446580383
    0xc0c06080402010801081b060f070c150f080c0306100905031f0b030304080a030f0905030a060c2007180b1306150e0a03030e0d050a0b060f03152809 65
    0x350505010842da805aa050300400380709000746041440b0411030810719082840103449444c00103055942c8190580a0303880c0107070040c4588201a41c3c80314900540e1008640c10400030340740443d85218680500360440c0a05807064515003996120310074072500f014139500182c28003051060001f9aa581044000b0100488440c180114051480502c00303443c000000a0711940080c40b041c403482c14002815010541c2520f49048400d460030000e44801009422403030300b501810f04d41d00180700c0e942c4c00ca4000d070701441d985c5c1c1405004404030034204a00408560a554002c0782080160412401040306a0303000a64001000d2200100044100c4c0441c28108011a2652410401e03c03034054110f103c0e1240d541000401c2d03040310400240c0c51072150000030184041c0d99070304401078403074022002185a0140c01c4501101c190305200042c12411203005104400051181000f07080100340442c40c400d40c80783c1c0c40300503103402024150000352809021a01845560744040302c147ca40100940280 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 446582733 1106 446581627 446581637
    0x904080403050a08070201081e04080c0114100807061d300a1b060203030a050702010902060a0e10080103150c030b0a03030e030d03060e15010c0c06 65
    0x4030781014110707205001500303040081000003008030a0003600c90300c0483e911a8800316102c0e100350100e6840e0594100407400007903403640540290004000007150141c00c0304c025002c1c41e40222010b910300003004100308035000c0284a20009880a0b2030070359002040e401c07a8011154010800d54081c100801aa208582c00305d008010b05105142c480081d05a01c1030f01b0a81c1e0b89000076090360104040c1c2c41e01000d82c006c50918004a42094014500b5940c558614100030000241840d0070355403a00007507030060752080020402a4078130344600307181224040c02d001c98501440c180505010322000180041100c1e0900c21250740244500890641e8881c481207000d840c410b10b5030740c1c10a001c1600801010341103002ca01031110154102c0300c0384100b00344200c0954041e80303d56110740e02c1a4002c90861011036800904869040c1081c0420b900e9130703036644660940c40c2d802000062 = true := by decide +kernel

theorem cover : BRFrame.Cov 446402877 446582733 := by
  have h0 := BRFrame.cov_init 446402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 446402877 ≤ n) (h2 : n < 446582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
