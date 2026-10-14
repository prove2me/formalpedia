-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2530
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:58:54.570954+00:00
-- url     : https://prove2.me/submissions/108f951e-5d08-4788-bb6a-ec860c73f04b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 454856115 ≤ n < 455035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 454857365 1250 454856115 454856141
    0x2130b030105010305060a0b0415060507140a081207031a12010908180103150303050f091309060c1808060c070f0210020604021507051c120e0c090c04050d06 69
    0x504085000042800d55038243d1003903e00d03410880400007180614060611a590219001c01c41c4101f400d1003501d080c040c90040d20100040850384004010760610340c9100b46000c041140e00340c03002e51070203001642c000341e052024003240c5030128600c1406401807090f544403c40c1d54001140c030200912801000c03d400f081c80643d200d0300f0300c40104040304020416600c0700c02100c035604d4030b110005810784029182404498245200800110358400161b8005c2400c04200071b03950840b1000284d00000d0030305000e42410f00d0b00e40038404000e01030344070b042c05180c203031181030710281c00312943c450500a40c0310303083d119044400000c41d0501c103c401000c5180c07080e04684000700554010820301d958003201d03200941c0c40002800298940900c01085614070141c0145c80c08080380e0743d042d200d60000f2180c403040e80c1c4161807440d0700d03400368400c9107022002010030058003590b0700801355522900001c08bc020300010300400c400c0900307402120705a5002404080115800f580c440d40105032480043c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 454858615 1250 454857365 454857371
    0x3110a120903031107030905040506030a050604060f0b10032301121401150f090e1b010f02070911090f04090804050d0f02190e10030c0611011b03020403030906090b03040213 76
    0x1303072001e4000d1025005050203550f850000b10b0406040c40102e40002c0c0905101e40c0c8400354250024a0000d9101c0d030240d8001c1e4046421070340c101691020308800782210760301603100003e403811140c2c56406103000c5170708051010040040800300c4150450b003070142a5201340703400c140c0c8000c540781c841807048411030180001240c030324000b40c180050802e5045403502c1c50b04420100860106030152620780321141c0060f0400d1111a050310a844c08141c1031030b03050240030b5002c8204a8000e001d608001c100c0c0d00e60a000441c0154400d208a9000e1007416200c6c420309a054400b070300b482c2c86002404c0c0c0e4480d901e14540fa04120810840110540703040307541080e212011001078031121188081810138001d03843c81d040c14000d001c131003480700030720346171414907070550800c0441d000244040c121107440c00c101001035000301c016400340c1140341580b1120040d108000000c02e0f815030060044a010f03a4442580d6501c40104407884110f91260129562040c0301040140ca00024444100e0b0b140482c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 454859865 1250 454858615 454858631
    0xc05030d2409021306020d1d13240e01050303031512030c0d030c030504020307140d05070f0f06090f06030c110a0605010e010801020f03010e060612041203110a12090303 74
    0x41c418500c06820601d0b4880d008500701c20b40840b81240354016124900140114000341540105141c140d8070405180c0414403082010580703d440c10030000c480050303024400400a13a0009505001c008024401c1039108a0f0000d24000740e240b055060315401005146141c995188600c0c0e103e116902e07050b80500b403540201c04082041004096442c001400b07086d110003c1c50020702104c0d2164460000c0c50301348801c0000580c0c001c01c403007003507464078803c054441c612440401c8042280600c0208244210714002c1170700c19030860321104840d52450489402c40d26030200f280c20928034400ca40084100840a201085c007076000081012002e242074160709590b1a0510f01e411800348094451a40e0342c001030000c06900d0704007034090a1070030002d52070800c3c0326aa20301e4501c014410702410059150128540d80c0da50303021158076086a9888001a080a0a00140c0c50030301c9061040864507154003054000c0d2200c0550b1108034454a8442201c0e800800d440040c1c0b1243c0b1040f0704050740c2d4091 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 454861115 1250 454859865 454859921
    0x103060b09122d0c01080411100302091e0405063c04050f090d05041d1905010b0d0b04050403090506091201050112140f120d0605060304030c030806010c05030d 70
    0x1800c1e801040b070f006981002845004002d0a00c03100e62001810451400c1c1000040340c6030100b02d085801040d182d0000f01140c0c21401c900900428100a41c00100030903c019032034441c10b0302e4102e901c000c5408000e1074641104103d1240c5130a0302c986440745403e620a58407580780441e4603110380382851001403138002d00f0001001c5510891320080c42e40005418010388c4c68042001d641c004800341043c03440c040c1010f007a10501300503d2022542c60360000009401c0b8041c522030040010b401c4141800256195100505075400011182010030302c1c10750082610318103400f5040c01560140c482907a014109028465036902c03840805810200c01400407250000034843c01d8001d0070f840340300361a0101c2070300d03000c108c049060b012101c3d603610001a24200010100d2120240b0326100e01712a5203803a241f81c59006060a03500031603028070080f00708814160411911409107102c0e9640200d542e8420006549014401300050140d0f4401e12011042a20075440312888528100481c0185c032107e0032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 454862365 1250 454861115 454861153
    0xf090408160f0c1e0f290c010203341b02030a0b15060f090f0d080d0207110904051203090a140d0f14090d061e05040209060103060b0912 60
    0xc01102e0300d4282150400a0789000c3d13001040b80b0b400001500c0006180200034000d8940901030020505c460000c04000815941503401d0407000c0100301070307111744c980e490b039500170340007290a1010034a100c02842588010307240004003c0302c128400c1402a800c45000319020110302c080060500081c07048800584c1c0d0402c400078a8603c101c00c1940c180c50b040281c1901c03140413089081c040d02c01030210108004585041c4c4080180c15280c02c45045509030000e2031311002030201600060002910307031001c1d43c06400824616001d1018140780c0e0071460240510324004880141c05604041079400c400c03040f4000860300303c4000400ca90b403071000d41d01c4907124104901c80621065028140048105030800c441c80700c0350407241800080051400d00b204101e2064086441c450511880b04030708020b196441804d01540015170120000e14003c0d03403200620058809134411030034000029100c1d80f1074000d40c2c0590b01e00ca40362074200b40d188001c0c00600290703a4101c4a050040030344500b007010900c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 454863615 1250 454862365 454862393
    0x15051306080a061d0723120c0423010905061215010306150203180f0108130606030b0a02070c08030322020d0816062a11070512010e0c0f09040816 64
    0xc1c1e800e090303400c121002411b01e142049405810400e0306065141d140c00600c2034842c0035003502201030042c1d640c02c821141c14132403500540080c1b01020f00700303c41400d484508a10340602070301c42d941c005031107000f04242c0780241c41079000406070b1000042d00380c20180225201b107141c181008185c6a07111680307000c150298903082c4005a10228807540c1d044403480c041c243c14401610343c8006100f16000007003c0040041c802140c4414000040d020406954450b0004540008121600e42001003d80e0b010303601c103403030a070355542c08140c0106510001101300e0340a001c0c2403111503091108103000302d400c0031818209030380c446525079004020942d110700800c074250340c488070200c640c0502e2510404584420860a0520490741c4d60032001d000e03940500003281c019400c10341c24501d040035240d80740035881d40110b0780180100881100094054002018810020040d150543e04943c10301010a021505069101010f003010030042189a0000c0001100b40c03915038003030b00950b442d007803102c0d5644 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 454864865 1250 454863615 454863659
    0x403230a0203121b03040308091002070c080c01030501060906110106080102040308031e010f0501050306060712020c0312120412020f03041206180f06020a110f030415051306080a06 79
    0x501064a90032002900d41c1c841080062140d50203201c07030a03030b50341740401040102400a16008280e0502040000744216281c0c070100b0355603a025840c1680b003003040c51107921100c0c0f1502070586040c2d80139014143c142c1d04c695464908242c54818212541c038549610502107543c0c1d0324010801010070b00007040910b002d8000d2541c0c034100300810b01c0d117000c50203041034440940180103100b807000840c02c020480f0300904c0c22a0301c2e030b103d03d000100144100d00b002460060f0145d5400300c0160040b1b88078541c908200c0030b4800c180c0720607090620500c00e1045030302c100c092250001e40082c15175a800142d003c1244101e07000300e50f00c40526455a4001c0e040514008403158240c420090303039010b2010710180d042410003010200d03035110001102d00c03510080402e0b4021800045091080040c149900e0180040b05e04100e141c50003036841e81c0c814021001d82d10400070807000e61034054030032100c104c81c88207074805446103007540c202e43c110b8000d070060030407985500d40040c559205c1d0881d13403070b03070600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 454866115 1250 454864865 454864867
    0xe04050705010207120503031f09090f060e0a1106030718171e0d03270602120f010501080a0504060209040e010b090108010c0504230d050703030215010b030403230a0203 74
    0x1c10340060f02d84001580484001c0100102001c00280c1c040709998000301800000441c40c43c14a542c5140c29815410090480f0300d80f80500003442450300402c81c07980e00805042110b805115021511900c404602400a09680c00810000d0602c0401581e00660f14507010545031304520108540d179000da4001380c0100d1804101c154083c8017030003a0500004648148070b00341050450a58a42031840b40c1700c1c061595501e40c0d030b0f1840d000d0f10700d0f031500030440301d24148039071805192810080d040f03070441c01c0401d5410b40c00603203042e42d10300c0103905945d0141c55208540d40d074540580e018120003041200e8a81d002c0c03141c000b084d2030f01d01416030719144590010421641d202d017400080407059001e0b1200341e0401c1004054140c04c6001c59041c5d5001c01d000314002c2c0101180f0004400445c5411500104410101002c0c440d001c62001d041d070303229500f44c861900361520140c1c0255420f000c0e41c1c012200410201c2e0004c1d00880800c030007507403e181f055070160362042c0c04e29810f03001580c4038805608 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 454867365 1250 454866115 454866119
    0x6030e2112012304090c2106020a02030406120506010219060603020315010504150506030a022206050c0715020c0f0f030a05030a12051015050d0608031207050c0d0e0a0e040507 77
    0xd0480000000550107850030048091540c580810320480d9200d0202046211500d00d0b105a0711008400b101e1234100600795a00c80b0242002035682d4090303c507840004008500030b02e1205414000e00340240e0b4164001e0a601c400b4480071110100b08000407558243e0b22100007006031000e2020340308103450310a2803003080d071504013031205490f03400c9640e103a00b00c02c0c0710302800a40e03a90015240c011080400041c0c0707456940315001c2d02011060304e503c180012079074001901643c4074004200c144d540310240e40f201070f035034000385110a0340c2012440140e0030400500c1050b080c44c5003402443c110080c21004076421820101e03052a921800c1640c51344c200003860880950020103650040c040020100402d140422a0404081c9c060013003640d042d01d0140c094102a100b40144d880c2003503090f90800c00d869079800074664071390150701040c081100c010000741099000310244c4040c1c11150000e00070150402d1005c40e14559100c0b910381d4040400705021403035610110341d59105034407501c0101303c0c5074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 454868615 1250 454867365 454867409
    0x15160519050a12090f03050c010603080c011a060a0f030203190203132009010b0f040f061d0603071e020f250b0a02070314070b0a050901080106030e211201 68
    0x140ea0f020307400e601d01e05003a5030b107000450340d20721180a56010324007a0345600000c003885024140981c00540300b00400700b0a08007000040d8480c42c0781500c251642c0e42c02007004400c0c0040c5000b83c10548012480d0200902d50f0709010390003d69004021050700c41d072120a04035140101d81007030b1480031010085100540821400aa4210402c0310076002c0076414010343c4000307458040e05004640b0305540200c0e075040c12542c0c800c240e5003e0118540e1040103991a00001407020280010524960f072480d800c1020b54100141180d01804165403246020980c4920956100090351050801c61003090110300c01c1580070f01501d1100107941e140304500741e08402c1c851295802940041c2107840c001c014040560f500001d419040701d5002c40c41c4074071000c0c640600c0303040c120709511000308001c0000c3c4080344540d00c100100003c88007601d5400903039803111411000c64482131000c040641c0140310741d6600341848210225000820511f043c642842e4541107a0001b4081e806504103c441d030542903100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 454869865 1250 454868615 454868627
    0xc0309020a0b090d1118070c0b0a110405270c0c0609030c15040314030708010e07020a0203190f1a04150515040b030321090c0315160519050a 62
    0x8009100100303081c1103041000413510500900d00810310140b0311103094858441a00c3e40c1c403101c80c51400c8020b44e14107c24040c04101160b03004481c508803200c00581802003a1041e44059040403850070306103410070007405200c04444501f2407810900c00c14803c1440000d1507400d1181d15001429901c8480246906140040140c0440d010390024402400001c00000f038404030704414030700c0345041e42c6a0303050590744135118182c030000359180042003000407500000218101e4040030b04100c42a60b40070300c03c03078458104440c003c0d41504201c0001003070311f1a0326a4080e64600610001c3c601d201d4a5032401006100c40004004c68105401040140100b062243d580340c80322010502c450705c0d040044036034100c40c118011f44100d640700c0d031880b1350307442c100141e6010b40075103030049a5140c142498020b03407500440e8450142d00c11500704001d1410003140718540617080105440640e200c6079120342e40780c610900300408200b000e200036440d0138840c1e0a027540e41c0c0611b403540741d41c40c0c003201001055 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 454871115 1250 454869865 454869869
    0x2d020d020105060d0221060f060f090402101404170c1c030c060903031404050723062a03040905011d01030809090a0b03031b0c030703050d051c0c0309020a 68
    0x356490102003001a485031120441d00e80d5046486100d502c800000d0740740740050345241001c2d28400c0c001003024500d43c150030607004620440340240001d42100400c0710305c000460300290042c01444400c00d500703004640251105080121560a25484000c00c4945c1e20b010f00145005600c02800c19940381801c0500303000340c1650f00314082c122041600c1c090711050410400511561f50b903c4020203040c40303640a1400403c50f01410200d0381070074204165544514000c8801c42c4017507100d8000d8403910099840f51000c80980454241710750400b0404d02d401a40b42c042c5032150b0360405c42e40990100780001c04c00f900000030001a10750400b4490500c0305203840f081d400f070b107005100510101c0e00c10402d545c40d6039000c0b60003030859500e02041d50080d00e102000b094051002240c0c10f600307460310a03141c2d5080c44850046829000208080550740c070040e110180142e000a004001e034a44200c0061122011010144071880e5040101e00216140b18880b01e0019940d0b4048208510300000c5480c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 454872365 1250 454871115 454871117
    0x30415020f120919030f020f040e0c040f110c06040308091902040b0310020c0a14010c1b0c050603070305060f010c050601060f09030807050606092d072d020d 69
    0x800022903808036558072030711801c00c61051010815080c190303214410008144020a104e619a03030b600d240c200c13016002c03140101c5c41400c0e82c41009034642024880c400c00b5039060401041c4295185013072200408080c0041400d01da142d001101810b80e1180041c034000c079041d0300a00891406c0c0c103000b440807401426000181e04181180d94222403500c820040c4981c0440780043e04400441c0003c1c80e00d0890300200c40c3c82030021a0309600000040b40c0345d1a6940603000c1070003588503408246080b20000c848000105035202207510f02540c402c0c0d03030401d881e440340203e07031081da440d400000c0042c1c004541e81c1c030000362240100007660400350300d580000102800c100c2c1543c0c81c5a03940c5a2145414080d00c002c000340e10718400521403141c0100320045800006150b031301ca03039031b041c0141c0b1468120307041c50060f01c220740440c08942c0c0a4032182402617035100c281d03100c04108060010440c1e00503101e5020070151603000010b111501022483c203000c3c00c00c60f48d12454000300c0103800d0100c611801c0c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 454873615 1250 454872365 454872373
    0x1b01060b03070807121b08090f011e0b0109050d0f03051b01091a070206010e09240609010501140409020904020c100b10021506060a030207080715110a1d01110a0503041502 75
    0x2452051030b0300c00000c0c6c0c80c10304d410254155500c18081c0c0346401c0e1031030202d510b00c2d070920282c4001c00301440019441070400341c805200e040169001903641480511070703071303800114040c59000410b1f01c00c0d0348907000c24840d00e0000d10b0085100b07809050030f000b0000180050355180441e4080103604114581c0050300d00603003003094503088a029403100e1051003444450144100010345000007400b01242d4094111395200a1506040031900c03016003c45075a03004818010004c5000e600406c0302d4446011420403d500d05814407803190082d402c21582250130913002c1c85071203420b803c00e0100c0c03403800154000000b00c04440c0410021441c4185a4603415500b0101c0080a071140c1c00104680c00107040e43c0c004c0d9030305103005044000307100e024000340c92120041031042c04c114004a60040b00040d1203420b00980b80da240c8560030900c181c01c450008280e001400f4840822408101c4c0200c8005050090700c60740c6108041d4141498a1421240d9400002e401e006c1c9004180e1054128a8188020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 454874865 1250 454873615 454873631
    0x10e01060206040b2a0d05010e06060f0f0d02030a0203040c050114041e0b0703080a0f0b01081909060f0903110a0c0b1b0706030207060e01111b01060b0307080712 71
    0x10703442d01406403024103850700040000300c01e1140707030114020310300141c20350f6820010802a00d1030607411180103451070300e00701000054020500d05141e030003458001c00c854036009005415002941c410920318507500801c3c80203800003240c0c0d00c041e6100c1c01ca111805079407894103203070803101896243c1040e4140062014400b4070007800c0d4040d01d041e6580080701100c0660009090b060340107190b4884483c82c1000685103003096031140f1081e01680c10003405001d12854030007440c1c1500e03618241240000c440c58000b442046002148401c4580e1212000581c07000544486068a818024542800d52600d00315000c041e44413104054610100b0301620520410381c2d25400e48103494800c0421000021071000641c8140e4041c602c000a01001124511552010083c0203900310140607100c0c00e1800c032012908940601a003980148540d4125103007080c548002c06c02085101d440c0380c070307940d6100d1020031221403040003903005000341c0c0c498813036a15001c07500803c8400244e10184015041c4206 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 454876115 1250 454874865 454874867
    0x1e270605040b070602070f050d0807090308072a08010c0212090303070303020304212d0906110f121305030a0b0a02030406020c1e07140f1009050d0c0905010e0106 71
    0x3500d080c0e460040e00566030f1942410404064094084082c00d0303c95035071103880801c1030001d801c00d025000b684072241295100c0c00161003500e40ca200207890140100600c100069408011078400c070603211006c0d180b6040800c0ca44032030f6030150040a5160f548500c8204450340421400301c01c0c10700c82c10382c1031078503841c00c2c0400e48902901600074140340c0c0102c08030b070802c5560005c03010440a650070303006507256400d0004003900d189461618004055154482c01c3c08502d0908200c402001d840f082d4845250000440e0b0f641505405484030340109641c1d202005030901055043c1d008104480303480f1420110081c0120500342e000d107100e0b62101d54030900064a10b9011035001545840050f100d580d40d0038200f01a104407450000c5038002c07921420003909044803180a681030701001c40d1100e503201c3c0035035841003e001d541c0d079501201e0864143d01c64a030031441e554070003099150200d0910380d5000800d030820402c09045030b8107080f40100740b010624034480e9074010a1003a01440441d490100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 454877365 1250 454876115 454876117
    0xc1a0a0c082202040515060f030403080109181403040f0308090405060402040f0e040f0222050a0b01021207020a0b04060503011e0f03020d0c081209120a0c060f1e270605 74
    0x50003400746850f0000100e21b2008030050081c642400744c9420340d51080300703145c062079910461f000c41c08616154000301c0c100003244920b030100480200b2260805403203403914101421030800c1e0400360b2004000100341040480ca03190300030352085c00200e442d04400c4041100ba140014503290090f0b1050108002050280750300d20101ca0078050b03c10030544460030142c0240400341006500546000851145400034003400225140d400c0010801c603242c401c01c01050720a4420b0003030060740701d070140203010390101c8000c00c802480200b0703016159680300101e80c042d030055807085001c500040300420020242445060100c2c2d0706200d1407030604e04110310502c0c440c5c120700005e8000c555960010742040b0012940c2000b07030100008445100525001801c01c0b0f502003050039010f0b1038810800d140040740050041e44003a44001e440d07a8860401d40100c5100390800701d40010001c50003180160215002411141d0000a0362130070049000d10400e1421090312200c0007000c03500d108000c0020503807001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 454878615 1250 454877365 454877431
    0x5160f0e0c031902040b12012102030606060d09060924110f0d09020429040b06030115200303040201112a180c09120d0509010c1a0a0c08 60
    0x11412920b10f005190b8080300074010740d0441e0807407400029500c2c00090840d4401812511503c410105a20780000e456650a400440081d09640b241001c90719519048004d404112a08940010400000d498001c19101c0034401500e001d15000d030524070745243c101c58021040390400301400b102d5404404520140300c1c24016030000080800c042545c0c4402e60002149140c0081c0140003602c40c45031040e413811301350719401d80300644032812201c840c100303402940584c0a00030566420750b841c0c607060101e03400541c03d4031004c00012050a010018040060030031195006c0000e540324a4184009441c15000e40c030f4541007640038140341a02181d1a5a000940403900c0020010207c0e100b004542c000722000f807420030411400080001ca5510000a0711041c10115003c00c0ba00c2e05c2c114415459400c5011054001442040031403010350207503d903009194881d508405201551112407418140103035031524166480d032202000b42c0b680042e00d48e40103500311402c00f201160f00303111000e1181001c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 454879865 1250 454878615 454878631
    0x307170405190201200c13110702040f06030812010e132001021c0809010b120a08090a03020d031d04060f03020405100e04030504031a01050a0b09030a05160f0e0c03 72
    0x65078a0008592140c0068811203215628017840c09100e020031988070f40074404494003448030395950710a1008207000b11034066580b80800c92800c4159000e11000e004641d540008250701c41ca40040001d49403401085101054611490594140344c00801d0348040a0400c0c1444200c110344c1c0000b081d556001413070f84122107035080484540d1000181e04040700207604658080701c200e880b10341160804029442401503a00030444512448104100044d0384000c2c3c80c043e520400545001516000090080f00e00040901d1900c6980e60300141e04844400b908400290741584c142c40d080e50711640010000724119414803a250031300c002040a1444d42c440a8071864076040070800c04200700b0484009000c80120946451900b401c000d800303544648021524542510f0405440c0c4031414140750603030754000c0030903044034a0415440017603049107501a0313040c0145140e140000340c0c2002000701040710307540100c018600c2c8c1520710010b50056030003410000e48001c2084075061903134040700d6010080c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 454881115 1250 454879865 454879903
    0xf06030c0b160206030108010e07050405011d0405071802090112050609160c0209090a031403011511011404150c11030702060c070e04030305010e060607050d0806061e0307170405 78
    0x2214142e072012421240300690050780000020513540c07010b40220311031480d04422280ea0700d43c0c0d4010f0108885003440382d8040c41403283c184501010783c40c17040a41043c0504200d40096846181c148070007540a415120701d103a0003c0d0344012960081d581c41c02e030300c42a0100304001e00d801404a030707805c28000c29005080480c605000c161900844c04080b00e6138020b4281503d03450002c804540d80c00c5a1002500801c000740490014803d40008803130507900f140c0c0505100c0c6904510542d40e426800061040300e54a9440110300d44034140f1485104501440d80b002d410300100b030f4210304441161440d0b0007044046494203000c842c00004403900d044e41540c1040c4d8821103174040c2810580c15422885a90010006001c241035164000d281a901d220404410719110141000480c1c81010001080e0f50481c5019a00e038034020f00300ca0341d2002001d0f0080340303081b16003050640d5001c00f180c0c00c8601014080309110030b0941c003007103108601c0482c542c0440c89080c40e44401d40d80300c5d040c0d8140c80340c2c036407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 454882365 1250 454881115 454881127
    0x216150302070803130515070c0807020103090b0a0f0c0f0e120c21010b1c0b0a0b0409050115050a0b031801020409020a0e01020d09050120010e030708030103060f06030c0b 75
    0x2200e58116001140c00c6655503880c0e00b804d00d0712500300300c00c5800588080c400d02c814968802c101c03000b0180a02c4258a429601c0c034142da13241a0076401c010801e07414155521080030106401c29096413040e5244c5900040060882c8407035821a602d0b01c0c402c004001d1940703804092590031018400e490141258980d443c05002ea150916040441c46110b07000340340e884621000c1d41003513802c400c00074804002400300109090500c24030544030010008881103080c5104089801c0002941e04101070700008070300003c0c0200411300b515240762046407242e654410111101e03826003084c402418040300c0100300380e442e1000d030705c1480c080540f4500c6445803600010f41541425411100208004070095444840d03103030010f00308415201c0c0d0b85000d0300031810200700b840d11502140c404e4a00586894030014070540030781d4100d0315090b0360f500484d96241c0c0307580c00008082001e0842240304800007642d139811890701c002a150b10902c020200c07402d088042c800505441410011707120101140c0380c41d16 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 454883615 1250 454882365 454882367
    0xe09010605030f03040e061c0209060102010e0111040f080601240e13020301080c0102060405060a0b030a0510061509051003051315020c07050303090906220f0b0a0501021615 76
    0x1014035071103107516104003d607441c4105008000742040750205940e0b20910740e00d40091215412030407038140318995465400a0041c85c003c03d0840d045170061000280045c00258002e00f16410441c24000d03801d0702060230081c0da01c4d18140540a800040080d1401d5450118003a44030790072202210f02c0c02e80030710603103a0310500c114030b45c0c4e02c0c00600a021150852110480d24000d40c401e0040c030030940103401080805500018040d402658000d009000e80d40e42d07041c04000502400740400e07894000c00d070380c2201050080080c00c2e2950031642000460703518140546a000c0340c072008070414403040780c004102d00e6a41c16100305001040d4200072860303540c0c01441404d210700c00400109642291008a04261700e02d80c0a05104d100007000c65500646031410142e032401109921580301005000240c460b013000e421410910142c40c0b20104150441101d0505907400400121101c9990b510768a809190030040900184401e0000d0302499100d0215000e4140081c09054400101c070202c4118207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 454884865 1250 454883615 454883621
    0x22020315060607061401030c05030105060306180102130e09070501020f070e04030e04020c1c031107021005160302010c02060c121609050307031406010b09060d050c0f070f02280e0901 80
    0x1160704c0142007180711403000040780300c40d4086c0419100c4051004001c170f21820305100d00c5008240003001005107035615644001d01c0c1642601d2078150f55000e01030014264940c103c0140649080030700c8041514040f00c066140c0300f01640803e04640c4807094151000c1004100c035401c0e42c1810322048650750325400c2c1940c02c40c1d4020441d42e00a40f0009002c25110004164072100140f10388044000c149004001c400b44ea000910103c0d88520402550005260107141d42e1714050050410030f041804910040c8a10307104000c048d03001d81d440d0f00d03502c29aaa81440b500e50f06c0b143c40040307103041c4291070761148e0254030000c242c00c3c1b02c48106011110389600524001e80200001412200c2c2140c80345001d982d03202d5a40601c407083e101c2d10b0004500c403400801039030345c01d41d00a085a410030300070341c0c45d15010b0100605040c682c2070040040c0e40d2407004640045c50001e00455240d03c50009500c180f2600703402d40c0c0c1c107041d110901001c8011b21303c3c95104242048512600d02c40c1015180c0603656801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 454886115 1250 454884865 454884877
    0x120304082212030206010807050f0409060905010603081206011704060b0109051504061b030e0108040c0e010311120604020a1202010509060711130b0105040e0c21220203150606 77
    0x10514a070400064212000c1d44410b958070710075030135194266a50000d1503501c1503035008a607808501002414220b0819a0242490900410010444078007940396079003102c000c1e404c1034075210320016120444200d6040b0664012800307107084012160f45a60010400801910080905817030304518905c50b071140c40028054a801042c071045030005030010103655002d0310403074000c0783c1413800c80b06414506c04040104c0541589400544100080044807400710013801180c0400300e1040100b0103490303e072681800b0b14400c0d01103642c10b130381c3d4004102c140060740400745c40c294014410000141c98080c1b400c4100d8005100e20b040c02c150a10050343c0900075002603d400c41e90105501e018131603c41c2c03a05000e01010b46584a88224001440007503510701c1d1565401b25600b080100b20015000d050160b124141d0304001e07041c82103414400d41e10003d90985049520b10750302c01d100d642200d910203010b1205030101c21007411801940803a40b00e0307007840c0c1500441200400010480d4554400701c40c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 454887365 1250 454886115 454886167
    0xd02060903100c0513170a02061c09031805031908032e050405101a0f0702041404020411160f0201050c06070804210e0d08090607030e1212030408 64
    0x2c0703180440041090b08440c030b05010302c4172848800a1512540c1d0300703020301d0340c051401a28104000d074092190f903074051f0010080188401c2203400c0303003502900c182d00140740729a4a41c503062a840d243c224110320b030703a0001482608050300d10400200c81813202090345a214141544a03540c1d40c0790106925240e400e01080103004c4900d21180746010901c1c40103032401101d003001181c80e504840020b40c10305004078810b030700b07100c200c0c003d007000001c0c00340140d04c58803c2200d00c2c00c88580d0100742030702c00c819100c00a4201841c144802c500e0309000e0200141121615241032400d039084004e1600c0c1c000c2c002a003403003103165848056904c40d000f120001c10150301161158100f00790001e1100d581103400b039036500302501c0c02c0b4407110880c2d04e010b1031050540e50f41052901c0e2500400000d20841101200d1034042009901c0c039940b10000038122950281d1260900d00000c036046c009810120401454150003d2100282c00f0907858240c036006034200c1c501c103131905c900403402501113031010301500c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 454888615 1250 454887365 454887371
    0x9070c0312020f1b19110a03082206020606030c0111030d020c1e1516120c020102130f051f030f052e2409031a06011b020d0206090310 59
    0x103004140f80080811164130300e00143c140101e00801c944441c5010030f542c402c44820005540440c091088001003148006c140d486030507601c2d0390340212076002c81500034041c562003004404103200320062800804c0180090b1131249811000281c4452072140384d1810322a007084204140d10080041e05e40c0001345441c11036542844a0300141e944004170401c64101d101c454800910071030204141103417880304a50403526844000c080801c9881420312801000b52112680e1040803450188220307610300341e00010382c1c400c0103602182c083c000e1600060010150540c1c10041502c4104165800c50700381003149140315000101100135100002c80002610f05181c10310403114a583c440582c4000740b02105c00300000080307a00f1605a00074444c0141c1040e1400070910492913803083ca2501c103589280c9000303040e0300c0303584140700388180c104200b9581d11481e0070059656044448152030541c511a400803607410f503800182940b02c160b8009000b810046803103006a141088801c0301a0002c034024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 454889865 1250 454888615 454888627
    0x8040e01030503071203090305180d05060a150f03020a09050910020d060906060c0b01050103050c090a0306050f09030c120706060512010b240301120f0506010803030915010509070c031202 82
    0x1007943c03a080104284d0b1018200241e002c5100e000380f056449065040c0c6034a814456005000c003c2c100c6924a4260024000c52a00001580031720690f84510500c090000380604040c00441c00803585402241468541c1001403000d60754902e50f90088a080706030100703c0d40d480358050740c1008200c0c404654914004202182c0b0380740c050700000c2c1540c07202c21040100950307030201102d4081002070060409a608001441a94400c0c0c00c0071782e0058068981d01e1030046000c0c00300b010599540d0003541c102d0b9030340061180c581c080790f1080b50040c0d0031400843c01c1c10118030503036840b11124001940c420600252076420032006400c080024807008100003551702d16400100c0c0030f400703c1004680710710b450805508101c10120300f05008114500d40440c11682050940c0407080b000c0705042d01c500c60350380d51b840c00042c801c0010a02820b80c80f0040c6499041012449150103580b00355866940441d1005000c10349461400c01c1d840500b44c504810215400c5c02d065400484192081111b80e0000441d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 454891115 1250 454889865 454889873
    0xd1715030d020f1911090c13090b03010c020a0c06110c0901060f08091605131401122108070c032a170a020606011d0901180e010e1908040e0103 63
    0x102d2203d00f08510a580c0c03021000044008200c040c0ca40007000b0800013580300100b400d054001e154030a0012400c1840d012111110283c00c40307081c0e218206150300e40307480034401c0c20203000d50401000a80002d1210f10000d544541c680056809075504002a584080c0d40b80041000707544412000a01001200e58441c14010810402c4070700c4503002c94851804140e00110004800c180705d070824000713100321403c2030101700300034409800201d4804d0700d51041072a00c0460701c0f070150003032907402c540503031040040c80c007601041c0850807650820802c1c0c80001980d1078000d18039580c4041035191100c031032442c9150907582c84040200090380740d070f4012480e2030003070300c1000740c40001801104000481074401000094500c602810400180c1149005c9140e950150920700c00180f071114034181c401c5800c202141c0070300e10990099024014000c1d6030240c0c5200c03403207010340700c0070424002d010701804816055660000304060801d2000303c0142541030181d080300703442c09005401310146407941c1d2070034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 454892365 1250 454891115 454891123
    0x2580801050f010c0528021804050d03110304060f02070f05160e0114040b031f020d0f0203070e01080a061e0303080f010f1202060403240507020d1715030d02 69
    0x10725401a9500e4000003429070003041100700311640f0000405541440300b240c078032100002900501001d500003000300050783c4081d10002c17928a0f00d0f60582d024039103420b1092610020358081010b00d460000000b9003150641e0450758420340000703002c42d00c0c02401248030024420010064a080d1040150204120700810300008808900319240400b0761109181d0320038a03001e12682c880001c60b150384100d503081c82e810645a030b000007016566400010441d641c5205031360440740f1211640019480c1c2c5400c0c00d03200711110000b00340340460843c60980409402c20202d0818541813290703590004c0c00d910301079048400500226003424900d441001050782648045002c110045040140041c1100054003015030488003124420141280350906100c5682c000c0c00d01a6080303c0704010100100e1502411f06441010b1064664041c6c40c0080d003c2c81103c0c07001c0d04100464001c120ba61070170940c0105000702c840c075041c030f20101c26100c0d1403085040d0b03d82610456054003070035800d4012182c000c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 454893615 1250 454892365 454892369
    0x60f050d0509150a0c050403110319080c0d0c0b04030e13020a0e100314071214090309030c01090803070b090a0506070f03060e1e1504050109090302580801 68
    0x40d448002c6071311411080b0096031075015426000400512040010480501c0d136403080c014090252010500c0c0c1c0254044511001c9070301391b5141100003420040740c0c0d400c210441c2e00c1c00722440c02c8003a0810303a9803820304020001e0000707020400c946183e110159114806440340c0d2240321002c65480c0a00c45000d090040c010802600c50819808044001d9003e402740c0503806d4401c070000b014555820708181d8250001c220312100040d41c403248098124140701c6454080c0c0801c00041d510ba04100c0101480d1901440e01603040000070a4100092038001051300d1055a0140d00305005035195021140741c011185c2028205105034024000c115400945942c8119840c3e40c0c103106407510368026a080c9001038962120003c2d03080035205031007041120403074010446c2d095071a1100241c000050554000b03820103e022541d0f040b001003010780400c80000308003a070303039441c2e040c424150407219100e1142c1c00352000c0d85100d211020710f540c0b5407001d120303140c1d1003076030f4225008112508000344581c10074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 454894865 1250 454893615 454893643
    0x30c0207080321010f12030f05090a030f111210020a031415011205090714060904240819060207030c06050f060f0f09060f120708030703031107030504060f050d0509 72
    0x1400002c00c160703501e00105c2c0140c4003d441d10508540781a81c045a4142411102c1000c00c003040c041c515555075944072107001180200d1481d41c445800307051038042940341d41c0300140703c0c81214048001091001c01c9110884c0e000c000e00688440160102b900a0101c00341a0000c28071030074104040510401040640d240d03007030f41c0307012601150001003000c40d0801d4072000400d40c030140003041405c2c2800c06c103540041011b05420300f41403038000420301f5034103100403c0001c41c0064289158903423070f14002e900107100c031307000410f044079140c030204081c0c1301d002001402e420b40002c4c1e00e005141c003031032411940e6580311204112520b410044190005000d4400502c52540c00d00c81011520700648001c8440c0d000a1000440e5100e07141003003d64060f0301803072508100c8058a200d49020180b1401000300700c0300e0099541c0c0c0d001441e00408507900c201c07546400040500504c07010903400000e8400317448160804520746080711100b65420b004080c000c03000c503800d000070031002c9400070408041490300d03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 454896115 1250 454894865 454894927
    0x10c02030a050105220f200d0b180c011e02011407080105010f0305010b031504060504020706140f090703030c030201023603030421060209032a0a030c06030c02070803 73
    0x102e4090100890301034003801c5111b100300010b01140c0e00c100e24400c2c0c0040c0601c102c1044200f00c000c036260242404007581c10b070311403408000401c0ea03400902486503001a024000504443c80040c02c000314903d1021390040030b50340342a030940c1c001d60091642c941d8480608020340fa040000804a0109004007030020784694043c1c1d41c15402030040720b059030000f0000904503900c01500b42c400512148405c3d0b4044d494080014958503035100802c8420301030500130514240c2194030081d60300c80600100c42c0d400700d480030049003502c041900c5013036079818541003895444504040303001e0f024030031100503a01481100c032110403c8000d2034440141207810b248a440c4030b048101350f1070303001d11312800400c09080c0c0c01d0525440d03481d440c0c54101d184038210040c00c0002200c0402d241210305800794109812982c016490000d83c000c1c4100c0501e01200e60040b1142903644070b1f036056120384100024141c5408141a071240244070b920040d1100404590b01c50790039420703040608252081114070b41c03c2c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 454897365 1250 454896115 454896151
    0x1606141024030b0424060f1805010c051f0f050603031908040602040f0b1215031b061306030b090901090f0201030f0b0d390501080c04030602030901230403020d0e010c02030a050105 79
    0x101651a031150452180f80008e507151134140107480c0d00382042000c81c1e03a4040c840f03540e1300d8110124a40410400d86c0400065070404542035042103400150502e03110342c2c420700c115078411102c0c2070600c11070041c524001d21075449508d4a50040d000340d03000105410000300c03012800880c2c20001d0324000c41003a402211548a40d004147c002c0890f060241e0960403403581d00b201c0311400340980385a110042c0c00070b882d2102c820405041c854880d001240003c3e2110000020b928200c903035a41c2101011001301b140c2c100360fa441400c0f042068800a041c95143c4031000151042d560100c41c0f120710203001044214440e1401c034465505c0341101b08101106040480340c2c541e01a03000c0380100311074005440311142803000544000500425010851208100210000d856800030314050000d4400200d1032043c2551100312440c1000b511309549038000007048046507000031100d1b1058802e082002074070242d10300481e10002d203628013a401d4403940c16844200700b4150302541c0701c0d040344904825051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 454898615 1250 454897365 454897367
    0xf0a0f020702091b0c010e01020403030311030c0703030b06070203030a030509010e0c0307030204051b070f03020d030b13050a0204080f0604110603070c081606141024030b0424060f 79
    0x2000700310020390002c0e0101c000501d03080c3e02891400b0340d85802c1c000107040c8201020240e082d20240d00c0c02095503500401c0c10410540c041c06450407001c02c3d01c45c0d003815443c1958202e00580900300016007055107038142900380b51110002c0b01c0101c1c1d0040d05a0750f0764100c9803400f4010341420750350200603600e04895804d5490f404103ca107003a0030010080e0558528540800010305800340c1000c044120034002d18030001200303401444102d108002c1e0441c5902c107400e0203414282044005001e144c203060070198196150341000912400307030100051103445403d13002009001e070303410102c1c1a10800c60384508441c0c1c0010326900c194800d0500c40c080d0b0350910140301c0c55010560381c0c0404110f80010140c0040c00301c00c050451b0149070320b201b112002c0c4c651a8201928491002da4000d020302801b4000e212114909100140407a408028072800c1709070342c040744201da85071108082681c4c1d101c080000c0c0e174541c0c11111407408062403440809406025045041c80e80740300e66400314940301c0043d0030031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 454899865 1250 454898615 454898617
    0x30a08150d03082a04140a080a141203010b040b1e0a0c060f06030506060108070c0c060f08070f050912100608060105120606090403030905100c03051503070506160215030f0a0f02 78
    0x3090a40f40e8032410117140c0040401c5820350707281b403154044940c1901003548a81080f00c01c5900303029000303c03017881005ea0a114204800895075450106d8104014400c0364810f00c100ca04445400000c5940c039041e07031050003880d03c0d40c01035560404900041c03030265181e100425a00c80c40c0110000c201d1010701c2446001103400d030780310052268119000040041d8001c40c24258070064504041d104841240ea0340110350346030780c01c140042400787c4010141c1075403211001c1e130301c1140303400c16580c403243c800300c00350140c002c21081c20b2003948c41c011885160041030180c02d40043c0c8225040c0002a12281c4080d00d42d14240a03060080050f03050310131040400103402ca000f40c2e07003c0e01940301902da50310f0840141900403000c4d50315100c0c01c1c030403100724041ca1003480c1c4006040d644c0003941e03003015444000c610101c180168825403210100f40200c1e5940005c580d08100320001c1f41c6274619842c4003180031040d0315528131002003004010448201940185035203c1c4114940400030000491144012 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 454901115 1250 454899865 454899931
    0x1505040203060f0103022203051501061704080a0512090c03012f160b0901090308010609030c210804092313200418050d080108030a08150d0308 63
    0xf000b5a02d0b03803041069402035004282804010865951580d40001000d944205070740c02194160700c0b1499040024003400503071809400d441c5001440e1a00302c5545c0c2903e207101034809012208001166003240340900100d40d071056442c0090051442c00c900955111800950360900075400c10405881045062100038200041d428500105096041d4852041e07042801c8204e4160108006031700401e220181d0288502c1528001080d442a1894002c0c5a00320692045042c0050301d182880000c3c801450035080d501204880c10500b095191061218038002a018224440008020600c100036421440011051003609012281b034259040d503908000c59807107601c0d421401c0d641c0b00081e1030300c80180c4644141c00030b03501c4811f0300360700007001c4079441c46c1800307000305142c0d41c40d900b085003e00110928802e6424101d442d51f1400c20300c5900c07482054810b070100402d0b080040c010b0007850707218415981001d004086001418039025014580c10345075000b25140303510403180e460099890f440302d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 454902365 1250 454901115 454901119
    0x120306030303011a16060203090d0305160c0c031e1b06120504051609090c05090402090f04150603060501081606050a05070206091302040302090702060907180e10150504020306 77
    0x4074603031802940610398100e03003444d0b9140160401c10b1714400944074841c40c0a5501a0800581d17138141028001d16009100701000141800d0000700030608400022a041c0c0c81198140051203048514100240002980000b4018a8600303040c9040d03020110311030f06485d11070281c200745803880b10101d0703040401c50f210f58400144182510496020642c00464200341b08100315081b407600241c4811115200e50019042e00d55a024007505201da694030040c0203117010b503058150ba08064021500c41d20780103000042e803080c1a0041010801040c8000a200e41c030703030004100c00b81e201d10b84400502400c0c4541d40080c40784020540c0c2048401001c0400c030b03549515950301e40402319001703a403540c00052042c0e170b004806001e400c549884000c001c00d240c0c80b0001d80160f807607040d0702c100314003120084c10a00840d413100042040e400701c0001e955003507070044029040346031f501c0c82d14040580b2440352011828060850304141d050701c00e801c00380e00c0d103071201d00704032060743c64400f031004074001280c100e5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 454903615 1250 454902365 454902367
    0xf0503030702040c1709030904110403080f070c03120f090501050306090a0f181511070b060d0f02061809010b0a140c03070b090a03170603030a12020d1d1203060303 72
    0x40145003d0303100c0c06131402c5508104500c04c840c503000c1250114101c40021341c83e00000b0300000b032842c0c1485001c21413800f111304c01d07050600b107880701c003254010080307603217851040020010b040c400d20505d030030002c6070301004906500c912480020415848002c841000c00c0d01d0307900c0030420750f0094007074034850307400501070405607554400007002414001c480c4030410744d03688007a045000001c001080c081c900070781e031620300170f06440e6411007241d40c5032185030002d40060007224000b0340d60b51412034102ca004c5070080d4480b401410810a808007880c4002d40c0b014000460b420b8429041d180c00044503002c4815400b140c0e80c604580c07401e4810540001d000031603024641c4248180c0002030320007800900201c9041118655400041100507039081150350f000741d15810806900000901410007400046941030600340e0100740d42c0d0060f003041000317000300d100c0a0718a42c03d040c1c1c141c0d4a160744561080c484120081d145400443d240003095034540156554081d1504401c4122030180c200a4021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 454904865 1250 454903615 454903627
    0x5060304050a060b1504170616120b0406090f05090d030c0507020d080c0604150b010306051302090d121101110405030a0320070902031501020c030d030906020705070e0603070f050303 80
    0xd0001818840f441590000c0e031089441796525200c00a8009040164076007404c035100113070000e1070300038000e01001d0b40206081c402944590311003400181c440b4400c0740800c4c2400c1000006010b001d40380c20100000b450030b10804c003a201c15410640c0101100e6003580c0140260043c200d0694151031807000205404002c800300500307040c43d8106046000358881c034202505d0180c0c49051150588003990717031802c410382c00c0104c100b191150303c80c951801d08040228910f010007091540c01384600141c0300300c6d4040b45683d9241c8444485144841d1b01400c5e14040f6801100003a00508020104803219860a0b800744110030540040f1002d59500400030074080c90150340445026145403202c441e0701c490341e800b407000f00d07200b001454080d0080700005622450030032035003010159121843c2c0d04560044070114010f840210b46201250118603000c100107101d4184500070317105d403140050191007000030004030400c465200c6401508104d003901d0740b61f07546050381201c4028034014030742c0c150010480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 454906115 1250 454904865 454904873
    0x2a0314010506210a06061805090a0f090f081c0209060405090415020a0207031a0f0106080c22030c0b070308060d06090605040b10061d191e090605060304050a 69
    0x5070507601e001c100d1884884440b071031092001c101c140d925550305071700e07914288603054008040c4500c1d42c2810b034400c20391502d00300014014040141c083c2c080e03203075200d82816660020b50841150203410684a1519400d01d217804043c5034418101d2000060359020300c0c0060100c64000c031410541c0080040d0700305030508040107000e00000d0b108917103c42048100d00d084041e540040d04980560350003400c01c042c50b5007040c80001c102a01c100c065081c0d070504004e0030b0010303101030314103407140352419403495941d1181224091140c140d001003114070002012488004040031170041d43d121740c1c0c00c0e041c00340d0791380d00c0e9403118040e210000f00400c800c00c0c00520b160800c40561200c103400b41d200402d0040440d240c00003291710545080e944410f072042005a4a8011080c1900030b1005140c41c0301010a07072860b446030704d50202c0c4200c0c810650101c1945c400c110819040b40035005070020005000d825160402d140d044521408040030b0801b03400107414907080382581d1145130414060680030100d555 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 454907365 1250 454906115 454906117
    0x501020c090c13080a050c06030702101e090b060307060207060c03050711090c1e04120f0c09050702030d06050d03090b071502030c0c0c091509192a0314010506 70
    0x100c2e0005480052006640d91043c00b20184000c0c15080040d00c04500303241031a9050401d9035503a80c1c0103c20410a00101550007d180c0e0290404000002444407070071010b4521841d5100314518150704102c0c0030400d004c07840d0902d6001c0d46046040b5000305990744002e1340c07030f81c0c4276208100114030458a04e80219020740014410360384030b1481c500c00c440d200b50000e4024103054448801152003c0b136a407111154000142106040d00f403c01c43c14245890b0044003010800c6500500d070040e191501000c01c01d6003180d0102801c0d82503414421403401d964000e54a8000541a040b11420000c00240d141000344c5035803000741e0103036185a003603800d00c40c200d4400c0d4024182280c4010b8400d00740312400e141d520285000c1c5004400103641d4680400c60304e0311f4841e0724007501e0311415400050000e5540c44007000382e441c40c02038900b9242a0b0390484080e0064a040000044050400045c0940300c58520000340c0d02c00a540b07180441360001600840480e4103070250103c0f40d803507050051000c0c0c46e001d8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 454908615 1250 454907365 454907371
    0x5010f0f0509040f0509010b12120f0f0d09050610061403070c05100b040e120405010c050a0615061d1014070606030c17120904270b090d090501020c09 66
    0x7081c101e207071103441c001040840b05011a02043c141d550002d1081d41c10307080c0111900b00000722440c071400481c01c90055107426150600c0c1041d40400603030042c1c240c502d2426604c0f0f4049469400c1d0700d0f0b1110f40c12000c003400c0401c00854007406540d0015603940d003492070b400103490747c80d50b1303000c2c138646002c1103605950b0020b09080d040c03003136250350354000802c00c0000024440c034048011441808850601080c1c55403140c0409580d040030701001d002d0210074081d01e0441d0030900e0101990b4616007096420462038080207000c440c10300d14007142c802242c291080c2120702d140d03200c00c0140c90f003142407501c142c0240030050b0711540c41c00c4020003c91041140b04010040400074501d419020b54803001150a01c0d481250680800d50b41081240118002418900880c9000d400903d1400316694610300c10402510b1003941d86401042b005c5e2804a00c505902d00004c60059000300c1c54103003900e08102c04c0b960914544070740d542180502d8443d031002004c650041e0003c0200e84d507410f00b0403c90b00001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 454909865 1250 454908615 454908617
    0xa0f0504030203060a150f0e040807060204080304060206071e0e0d06020f0c0a060e07080d0804050c060309031c111c020909040f030201050c03060a0e06010e19061805010f0f 76
    0x14031001c03001d030380c06100a41c05014401000140c5400c0d01d50001440030481e402217400188003c07040080000b002081c40d4815032103c440c43d6200441d251041c000e0003550070401c4107200120f008035003560001805401002c03603844800007420905103440080c42041e003041c000800720010103c0d0360408100c0d07081e14611541e0050704100b845d40c0d001b0820b40050a14410a5000070300305e01c14425a441101503801d003031000f51414909148440340e030340a240c4130322020030590200280c1440000d12512504900003429142e5031309003861610b599403c4882544001007000180d20840c0005100c2c1c1e0342500116807000b401c01401500c20128032502c01c00003842c517a020003421149a90300030a440c8101d100700c03040101e1a040f400c009003140e00041008100540400500010740d590882d0f600448840c00d201c07403480c1e500d9070012a060b60f180502c154003c941902ca1000c1e03c0002c0031800190340d015560074040d07441c100c841500a6100b482101c1c0030070090365900c0ca403140704074085442d025007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 454911115 1250 454909865 454909867
    0xf03080d022b060f080f0606060c030906070b15040c0801090b120d02071e050105040b07030e040c031b020111030402100c0803011e150f031a0414010303140a050a0f05 73
    0xc030b11030016411407070340000144035a1410144880000f005000c0003a01c0f10300000c050101015040340d5032a0f1300501b00c10f104940c00715140d80602e4040044a40d603c0015020135202c480b01d01e44006e0038901a00c0e84441c500c820f40364819542050b204070b0010048075500c0c640ca99292415079070051500a001341c1e00301d600c0c8200c9254802040000850308d1100d6030007065110314140f4500d01a1401c42800403035002d8000701040581e90200c1541c068038403141c002a43c584282c43c05444007049900a2074000742040441c3d04299050780c0030b0f5a102503504020541e00021280032800c031001c3d1130714a2003101080c0003050140c2003442c2611500340c198100a102e5051030f4481c007400740c209074001e03604042e00340028814010802c1041004084202800b514903111a0300a003900c20000c1c145020545d8a8041c101407802401804819040290080100d000310a0800100d603034240415000700b03412107003a071030012061080780c140da03400743d462505004c40d0500841d61003207405460410014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 454912365 1250 454911115 454911157
    0xb0c0705060307111b09160c02010509181003140a0203060c1b030706022d1c11070c0f051801030b07020a020405070e0405060603010b0421060c090608010f03080d02 72
    0x13004000380300c8040b02982c0d9000d440c0f4441030400c41c001b01c0051444018000d0006010a51a0080100c3c0310342542424001c0d00c542d014001300b680071400462080ca0b8001a00c1449070322a0001007604c04c3d07a02800c000c3d0a8802a500d00607a101c0302c150001b901a40104c00244540b44207002070a0200018006244c01401c040d05a52a60b000791609031840c135070005050804105031003507100000381013901000e0031000900100c41f28025080301004e5095500341401a0b41c00c150b10004965a0b4004002d45401c1141042d0701c030a90070f4007545980c0210020046454600b500108e041028580c503044100d03030a598602c0442c1c40054003c109510825661100680d105c0c0112441030030300e980c1d080a82c02c82103041200b0307250060155800350314100018401a0418001c0360240c8a10113000189002141406041c01d0428000504098942039400407000c2e4054486012299140c0e0ed10302507989850244e4286440da01c00203000050400a40400301d0881e00a000d41c1c00c4c4400307480c03443c42 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 454913615 1250 454912365 454912397
    0x6010609050d1b0b030f010906030201050a03092609010818060105210102210f09030901180b0a02070f0801180201030f090c090608071a2512020c04060b0c0705060307 73
    0x400f0301e4010140c01100441007003141e14021005600404092506000b41c902e150000b903c00c0c42080309a404050300c0303950386070034031095803003c22070b005687c04100104550202030f2221604186809400a92114041144a0f044651003410140d94002805041c0d00c1c010801c1a001c010001904000d0116400c44040030828800361400c20620ae86030000c80755540c00c1c180c19104014a4800744400340010720441c08000010f803280350a082c00c1c0001c40ca10340741082c2071096034542c004040070200240c2d0100055009c43c0d14811540c240300d60500258840b1501c0b426900309070f1500e0200b0b03403007408038000743d803023608110a40760070104000b404021a440e0303000c10751300e01c0d00b18094040d12103204005408007004240000c21000e20049203c007010503100c0824880d8110f146803240490202c0c041c000f8006506c0140c659008114114204100c04040d40710412003484a10a6107410707000113100034001d0454000d10f10b0880502009410801005a91b82014180074100291a01d105010b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 454914865 1250 454913615 454913663
    0x1230a03081207140a0f21090516050a0b030406020f0408011514010c02090c0901030b060310061d10230d0b090705040b0301090f0f1409070806010609050d 68
    0x110030149000080c90002c9004d440c0a182e002c41d801c0042c820012665007503404000c818a0f50b50901d06032004e1b010103207075030701e001004540301640704d40350980840c00c100000980420100c1900f16a50300039503034108100f0107034a141300302c0341c403200200001070014009a0051004c0141094001e00381a19101240d003100d8401e552010900d0103a14180001c036409401640c40780000d186c45480d6a2440c4e010807803a21010301506980c0c1c40204400e4aaa806a003108810319405001207840f49865854500426168410140400c82e00c508198000c101460101d4500350003901d03000c20a0700d021400ca0f41d100e062015450340c00b401101c8500601c0b0b13030380d00811140043c940003007018030510781000380d40130000d0580c0082c040b04100070002d8a0802c0c05580c11a92562400240000100f50a0f40a004600b20601c0a6072070101c0411003c0c20a5401d1401080303035208035035100c0e41710078649544040030b006420200700b450707208018900d40300340381c5000103100e24441044003120010203489 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 454916115 1250 454914865 454914877
    0x150203070f0f02040f0b030304120c03020303030c04030c060801260f03030901020a140c0a0f0f0605040c0305011a0901120c09090311060c1606110c070305030306100801230a0308 78
    0x24104042c03402c0258a01402134015441d8140b808015051110740081e540b841680300b5200301c204000404800d2100c9040f80c0001180c0180507aa920314001041010550250004441c2d881c030300c04000c18034603c1503051a050311284e4600c2000701c1d03030490039401b00d4420b503903541009110f50706011000900a00145018102040c009a110500d400003c0c150b000100c20740c40e10540c041c441b44e60907050014031005020780120303505000000b2810b0041c0c8014209170003410a0f030522050204200c451a070040c02c89005100070804507031107025003060540c1c0c41d0002d80d80107180d94018016200e0030820034522501c542d0b41150925a074244001c240d611442d4140c01040c850781101c00c1224040c80720700da00480c410040e500c2c0c60105c1540c00b4511010710406000c90b9034540d50070040c152a00c0807118070200c1c1f1402c5038449940ea01d03020387d40c0c1d03004840903801626400150f42c2100d01422005058500c009204605002c05d248440820303030b000210755901107074000c03000001c1b414240040c48 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 454917365 1250 454916115 454916123
    0x7050c220e0c0406451b0801080c0f040203090102040503190b0601180918020316060f090e0f07020a1a04050706081509060103020f0409020702120610150203070f 71
    0x1c1000d40301020001181d0442c1d11808024100380003101003500741554036400c400c80d00c68103e5014041840c0d85c44c00701ca21031140c0e50803615198150011007010200030030550301582d0b510b07555a81781d150f015100ca46c0070004980045807540204082e14064015503844000340000508083d034810000703144c5400100350090b2021421114000c0c00699002c0c00c0c2d00010030300340010284962a0035007104013407407080b56459541c070501c000c4031f205c0f440720540c101c68009040703034180d00c00d00103005040c1c0d41072303c20301000c00d800710b00d006040c9019500c22000c90f0071202e2404559501c80c0881e40341c000c0002d015404600406910702c000580311a9480e980c420700002001c4070b07103041e1030004d2400d111504100c041c01090010469003140311500d000c80740205a40600c2c45488120042c2e01a02070151980b40c0390078086000300f400c040941c0940000c134000c80b80c1c160500c3d500710400d91160701c107440c4e2401c6c101c40200305000d1103034040e8004d100010188110707032030840e1607150f80b5001e48844070122 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 454918615 1250 454917365 454917373
    0x10060906080f0105010501050d0b03011d010f0f1802040f060308070f0c1406160f05010e0f0618120f070b25020d08150111060f0414010207050c220e 65
    0x407194641c00c01c0710a03544110b00d4000c0086506240c0080c1441c082c41c5011180c3c945c840c000c1d4006e648082d00060040220744d2102d10a003140660524080d160800c030b0941c2491801441b84d140c0c0040b4043c80076200700c100200d4844124640900000e08803043c0b090408544440d0b00000080c0c090005204030f50250404180c01d20940c50081e0b860b180c25808910768202c07041d081145951040704a6025407a03072402030403d070003786094401c050800c0e20140880d403805001440000002c80e1007400007070001c0075078005544400b8941401508000e00f00f5140d0f04c13a240d5107603446c2ca4100282802d104114555040100c19921108120411102120070748117000701d180040b0340c0b003410b48030780c2c01c10341c00600601c0355010401080c9041c01440e1041e4860340300112110f69000300c403641d0031086800162021840c2c6008150700c1e20300195003c0706d15505030540d40e07803a400107100752040a07a101d00509005a6448100003003540074000b0031900701500395155003804941d10800c01e015001c00090 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 454919865 1250 454918615 454918619
    0xb040504060c020c1f030f060e1317041a07060b0306070305151903060209011211041401030905150a14100e0c030f0f070e0303220506041206020310030512070c0b120a0e10060906 78
    0x424281002f802e95101c026900b031209001e454100d1392001030801c0c1e05021907894411f1410710002800d04031800300c0d003600440e03090007c002c1d4190400d902c54411100421002c2c8015000d108407009094400350f209070001105000084040d0020901840149880000050481003043c00c44050103001c1c00e4460000408000c08090071140510140d030900b002c2000d01c0701e9803035482e150b41c040380c1d0020715010108001201415507900c070050510303460350455100d150030007211a008105000c1c03480c0c450400400640440002c0003280c6c460b4440e0800c4e160300317844008295003030802c040c4c5403005000001203800031544080003d005a02136a26280601003500038000c0c02c151003e4000e40d0241600700401d00407940e000b540d13112150f511080050b507070b0352000040038031310446400040071400307100d000d800b4030304140c4041d2011a010754290350344181d0300c0c01d89010724450007a902ca094500c00c00000c0c4125507030340c00001c010300c40c031040c1c40c0d031503010b20080400c48a2a030040c12000c0d07540c0d541 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 454921115 1250 454919865 454919873
    0x108060a0506060a0c0f0822030618080a0807050d050c130504060518150a180506010f0c140f0102030703150e01060e130b040504060c020c1f030f060e13 67
    0xc1c1e50b000202524000e01d04000490b009001c1d4002500103080040d03400a0201001503c2040300c0641c410014000c81e0b480038840b20900110140c030090720ba46040c20510101128016140401183e11112790342c41d2850146096441a800609203014004180314104225046004581c4207140c00403140ba6606501d0401450907021a040b043c000c51030200280950346608400b03408841160404000c41c4d941c1700304035400a20b517070a20b982c0200380c1e218005103480030300d9034044400400c140d0030710655480c06c0044410036411031a50001440722102071001c92001c0000344150716220050381e114281580c0d402c2c1c203a071b20030746503000002e1f0b991801560181502a0a00c0502101d60102d030303ca5140140c020078466200c410544601c101140e2501c50802e580e0000120900c0a003007804149000e08000b0020061310313411902500440540d03640500e800c0c0401283c40c8204001c502c0b40840c2d44c0421801028140f80301e402c100d554200214501d90440c01c05441110b035541d4004e442c92003860 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 454922365 1250 454921115 454921121
    0x2030405211806070606060f0f0503040c1a070f111c0b010902130807080d090801050f0106110f120c0d0908060a11040b180913031d010e06030108060a 66
    0xc080d050890030768403018042000002218550684070390341c00c1c0301c0d0b201c000c001140c3d40314518004004e940307450000501c250304035102041015450304c0e4040740540340c10f001c1e80d02e44000ca800400700325010718280000062030012a0020006550842c2450050b640e07400c00940c86120581d6000211039110090349048030300442182692442c0c0544170b0119034a2010342c14043c02819010b9401181c0400c40381c84608504000f0014202100c00441e51403107425111050b00301a50700090414001083c0c0100c14021035010328151190303000c840e13283c51812207000400c10090915405484000c0c0024001000141d140c080c06010700d076612070075214101c1c41d1551004180c414003140340300c200300d034401c0866640d030302110006012030000703440c0c3e8480c12103100d10b80140265000102d54105400401001044034a005a44804060b210b080c20710f1440030522200400042494050f031405601240d569041c0f80010705041d40c1c42052000004c0043d04240c2280140b42d0058040015808040c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 454923615 1250 454922365 454922383
    0x3180f030c0a11150f0405040c030212131b03030806130504260d1113060e22230a05010522020714100209011e0c1202030c1002030405 59
    0x2600451a20204003403554030350001d4030000e814440306101ea0010f035141c918401a00040e4064101d039101c009000103080c0390024010140643d103018040d9040c14001e00c00c035a41b4802d02605003107036680742103c0c80742031401c10300e003104d140300400c0c41d619400050507190b4003d50320036110181540341c6074060104c0c0d814884c40c0c0c4a500d90a10040c8004604a120091103081901c22000302c240d00d5404074000c0e9204000e22440514503025180c11180074000140c64802490a98440703c2c1e0342d2603600315050b40c41c881034540d0284040c0c0314040c06100c00d496809d11003007104030100b5141c0e04404290328030344407415030301d295440c98410044122150303c101c0c1e000d040b04903844018203402d08512000201c0107040301c00c4207540095000107100703403490591081107840d000c507102990700c0e038403c1000c0d411050000f404295802d40e0001e00c01e081004004001e180e66031018201c04260321000240c4019807040001e5020403c54481680000d0000d014206d082c880056500d08261030310310b05c2e24602d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 454924865 1250 454923615 454923643
    0x6091404080426030a0f080a0c2705090a0203010501090801020a1715040603150609110a0f18030b1b070201020a060c090512070f0e250302040306020318 67
    0x640400001600200556080d0340d21101503044007912000401d002c14000f01c100041d0b880b010070020384e02a400450400501031a58808a09449040401098900382c10110001c5103840d4690079001062401c8081c14800304410240700954840100302d420f241514820b00d82d5400000602407075822070500c100a2012000851030090303260001485080a0f40481e00440c5064010548124140f0003c454828005100f007080c19968540030074005e40c81d804454543e81000740018030b00410303100704080c40e21190070700741c0b40045003242180d40b400034210310390500007982c127a10300d60303d0082955009544a044800b00b5814010a1940390000c6408149441c0d1400c11a51340141d030301140d40c3c20b40980c00040414021640501600c4110580e0421504113036440000b8011b10030010742d41040301c01d409501e00b603840e250408080a9001100d241d0000c40d80201c0c2001c4411500c0d038503841c0a82c4a00e001410691203a50716002e0340d0060b240712030441102d2004c4c003407103c0c0034440350381c9501e40e03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 454926115 1250 454924865 454924901
    0x7150b090c13060503040c0b1b060901140114061902010507120b0d0f020a090c02060402090703060305060c03250f093503070204092001090317130305030a02010609 72
    0x12510044084105030f00940e0b040050100205080107002c2c00c800002c0c103650981c00c0d031249e1402c00b04200206600c1480e0003248102c0340450b00500f010721610305442401030040703030103070b0030b050205601c182142c150036080401080b6280c0c150310b0f461401e206181c1503600100b440d00f460710004040341040010504803918045048807203995400c40001c59a51203a01c1c01c22005450001682d008495803081003c1410103c9218a0f541d0104800e44220320071215401d1649840104034200e0b01c0c24000246aa401000460551840c40015580c8110b0303520200190613080140309074510a0310038007901164801041042403904441d1003005400042070890a8103010010300b40440d0b0345848d1320040c0300c071a80414000c868144100c4007500c0d000b910600103c641c500d041c03284414085240d40d00c0403000490000a036210f42181d41c100d980004c1c820018010401d800243c560020041079003d0280d03000000000724140702916004800303400024401d480e280191003034500325001800da8640d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 454927365 1250 454926115 454926127
    0xb0613050609130e0d2c011115130201120204080a080c07120809010206070f140c0a02190f32030a0b040b1504020403080f0c1002030c040501030e030c0706030c0507150b090c 76
    0x386d658403001c0d1b400c1c800d20f403d0030400d407003c0c2010309005e9689100003408134800200032410940601441e4034500c06c1e0b035102450a0340701a104100e005900481078650082d009000204801c60094030008402d1000c0d50591640d0b03580031015050304140445805101046083c11f81d0b03010320010382d0051150810803403522449030000c2c250213034255079810b010786c0411280d0380c25208100309032f14a940035001c0140680c03401040d0f07111100030300c11101e88400ea00e4011440b882d5158418125124480d031441d03141840c070429441d403540d88001d19805200382040c0002280951039080c0c02903000c2c0c4014007150070081c5065410a80c031040a6000300c0c0108410000580381030122145011107104803922440305020040c241680da48015000301e00210a002000400c040184212031090700c00300310244500e0340142d1203000c1c1613080500354002d44001c00c1420700907002600013030300302e103040381c40d02140f595881405500103101085040e960744803e071040c1070210841d40c1286894464606040d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 454928615 1250 454927365 454927427
    0x5010e011d06180702240901110f0301030807141b13110706020318060103060e0c04060501080f0903041a0717030c1c1d0d030b0613050609130e0d 64
    0xb801500200403c030444900203008030b4424801400621081d0710700c1e1403009011814040b000b6000d6940203041e500e0900791481488030038003101c88400c94040385a046a10719241c450303541c2c010503000e59420480b00d44102c10103400344000c0001d904601c0d26000f1a400c1c41d003c0c40340c540a106442c05206240c812100d038540300d105c00351500700764010400750341c1b0350b510a81d801240016907402c07003c1c0d215010012040041e5030300715001c200040780488803005c0401c001c1005440c031500c110707404103615030046601c1103207180d403417584422080100c900d07181d5a0300c004003402202e8540098000f40115404080100613000c104940c0140d6040504600302012032206034491290703030b1011362604507131140c20080c0f207400a03210f9000607440102d03d0000c0c8030015888440d4221102c1c006407504501121900e44502a5840c603094100e0320040c01c0e041000b40050b65210b0b214881c1c3c000d04080700500d042050f4082e440750321041b140903219a00ca079050152100150010210000c00031702d840c01015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 454929865 1250 454928615 454928629
    0xf0c200c040f09060c0f1e080106110703230c060f0a05070c080601090608010f06060e0d0f06050a151203020c0108070c0c0807050f01090308031302060d05010e011d06 73
    0x404101d600041d41d080028502005100e09140105524185110298840e4001007202d00441c0c080d10b516514200040d101104810719000b1080450382d8140140015846100070540b520030007001c84103101d0300c0343c4de8002c0070195400e00300b400e0070a540c2c1104003d14240700c60308200134140c90716400c25141032400492801042074060800401087c903c0902c030003801030000800c0c0400645529507100c441c01c8014010a000e02840f0358204054403503820000d21031441120003136907511503c1e440700b03002c02c0103600303080ca0f058400d2132482c401d40300414418032820b400340e1285c020018600800114400140700035070300621400d0901965500440e0300800c42540040007483c0003200c9903100101034900c100c100001800c00c400c00b8502160714080065443e06031103040b04c6070360102c1584401113404081d02d010040120100740041418049034085841c0c0851005180340c1c24103009030380f140100e803004d1740101c000c0c0141100401c45c2c1c51081007000c01511800e00c2d0100f452030100301040d44 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 454931115 1250 454929865 454929883
    0xb1801050d0206040321090e060f21100e010c020703080d270c0905090c0a0b1e0d270222180b0115020708150601050d0f0c20 55
    0x880c070401d165011980c030b00d4121409141c1c0300915401c0c6501c070344501c10b0483c280750180300100d040d112000ca004107049078050b02c5000002c2840405d000d001c030620907c41d400c1075011050004001d21405509010300c05c0201d408025500000c2d15240c004100703081d11000c10420080d90015082400030400c81c40c11211103110401009c200b05180098000010100515020301c941f000b246442c02c112159aa50b03003101c03070784101030203551581050075885d80d4034203074165030003a40d0f280c0811529003d8000b5224403214420607140ea08031060b0402d0141d44415034612905a0328056010185030140d0900700c7d0410700b1124004000056011a00071001c511b800b00c61403201030b400090211a54001d002c01c185043c43e06c82c000f2245285c500300d908000c0c060380105802d00d405028402d40300042c0d0008440003c03009104203034043c02c040d1410940548109d041040400039640d0200e000e01a19001100104000410400940005191010f0110003164880300d0f000c02e04201100003d035a40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 454932365 1250 454931115 454931119
    0x30f02131b111501030614010f05010c1b03291f03080705120c0d08090303040503041214010903050a021b0105030c0a0314040f1e0b0f0a021209100b180105 68
    0x30080020b00c200c07494020381c010b0716581c1614040c000f004112458110400040c8170141c011072a136294151000c000019015a46c005145501504049100316115074041c24595a90300c59040c3c03603446560045188061041a480b058007500300e0f1000012400303130788482044000700101c074281171039600d0113049200180c5500740c049461014080c0c144103044e40070130310144482d640e10070120306e1922440e04140b000c000c101158005116007001004030791189601c50040d514142c00e220071940803408081080e00c10304a44800b2035440c079000d101c0c0c0c05807e4000d4803415115000f07200028641780038441e20200313040c01512099003598215040d20f81001c0721030001521260031080444c010100100c410f24520300715000e02c018014032081c6064210700a1551f04c03400d11719440040e80b29080c81800900d070284001c0001e0024031030b00540b9800c0301040c0000b502d0582000101000e41c801560280103503000300440b187c0d6003581b40300c1d44203801402d580240502400c00d008468124051280c02c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 454933615 1250 454932365 454932377
    0x60a0608070e010c08130821030609012105010906021819290f0301030308071103070f1406090601060e0307080c04111209030d05010906030807030e010315030f02131b 73
    0x48200912182a2000810801c035200e2410307568003103660b0390b01201001d4410400d0304601b40c232000f42c0c1980c2280d102e66030243c00da08180c0d19140c100d10215400c0039110052010b00b40c0c1c0c41c00059402e0140071601e60240c1d1001d610303000c8582280584c031810741040c80c4074000e00300c071400d4203224164591040300d007a455070410400010501202940440d82a000b801e1000a000302d02d410b074081c040d42c143c0340241d40b052a540c0d501d0a0030344030302201d864070948660050199000291329051030780c80c0705110f403111810484a18009c0c5141100c00c0d1000311807504054018080c540e4086d0080b03c06000840003000b0103840d103a1142e89a80d14241c0c40e5004548603600c51500011484c216260100c426944100351f01c0c140341026120340010303650302a582e041000018910b03149018460030740381c10503001441c0150a03a070a4418107a0030f5905418141c4620050101520302c29500e0300450080e1a85a00c4203003910400101010000015120500d06103070028170701144400400d600305142007107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 454934865 1250 454933615 454933637
    0xa060f0c032109060b010201020309100b0a0306020301080105071101020306130b0307150908060702120f0702040b04060803092e050318030d0603200112180605040803060a0608070e01 80
    0xb111200708403010111480d215041c90742d080d4042d5400184114000c3e4001c105011501004900b0b038032040d030b1010b08950105407251400700143d48881085680200441c610503600d03510305050743c009a01008103a59207804100706c013500701c0c448900204e42000210714518103680001e41205084144401150342c42c41d490566480402c0f41401030b21070384034541e068450400e80200544c0150207168054006d10000c2841c0900024000d8158007002c200c15080105000c5001600d4000c41c80599016440b06090340564076548104405818044040d55a41c603004c02031083c0783e46002103d80c524070309001200550034042412500c01c070603918040381d407620b17080c1104200050340404186a804001042041d0960580c800c81c22a0311139038400c8a01008450000b00c1094410801404220982028505000c3c15407001ca44010074019200c030140e01510781c10119241110111b40c041e83c0001404840c0c039000b030180009095500e00342c003440c40c200100501e01ea5000300c1c103a05002411043d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 454936115 1250 454934865 454934867
    0x3060b0409180506090a02210a0b0603240a15140105030c0f030702070f060512010608090106031a040309051905040203070309060e0a06060803042103090308180f0a060f0c03 76
    0x442c40c619801074219440342c100390403000d0300c3c0c48a80d10101d1085540007010040d103c01102c980b01c0c503100b2203000d08502101504d85011202d0700401141d454010082281c81000704c000460b460054816908080382c41c011403814101c0d913910480310f00300d007144c40d802c00c1325850883e5290307600b2400f07203030980c1c0784d8448c4003107868580078601c0508606c850100c1040703885540000c64804407140c5114861009a98500c04d43d2a0702c0381005c8520070b1007401c401030010703501078000c4640001e610000014520758039240c5a446405d0892010030020890083c0404e240c3e000d00c0d284040d04c42160070710700500da043c001c840d40310014803895001d2500440040d20890203a400003480e260031003824080250b18803200c580340d0b18540c508403120340c81d042001c6240d00f070000a4a01341c0d030689400080c1a820070f8071b5006141d40d50941282009001074010000907400380203022100c14084200d8403c800c0c000401c841d0a0014070315500410112108012255001ca501c00c003004c610300740349001c0600c48c20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 454937365 1250 454936115 454936151
    0xa03141203010b0c0705010809030d0507180806010e01080309090f07051306021011130b070203013306080708060f0d140c010e09010303020303010e09030d0504030509040c03060b0409 80
    0xe400c044110200c00001d824107184018203240c082d0070156460991917500550340102e080d640141c2590050181007200360150380080d80040081c01d00001a122520303940400c0e403081d03080014150054801008005101032400317000d40003d2002d14109030300c0d1000304490220080441c0e140d0318000e00428180d6005500b10b400f043d6840002c619a15102e00d006540c848503054820020381c0b8000615103d45c03211415218981340350300c0c0d0141150314003495201d0f541c0050405a138195640c84d00c0019000381c0d0f00c0414411414004112040000303d84007000140803035004506208003181040003566004400c25070214080f40c2c00c040f09503111000c41c48913900340c0070061030782d00304900b05202c940001503011081c0e03400743c0c0e5030513140e9640d00030701000e00c6c428030008000d60b01c1800140140507000101640c0502034404407824403082815000a1394403d99090b0041500042c150f40607080600815002d502d032030900340245c0e031802400d074846110b98420020784a03502d0b40700b024040d100c10303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 454938615 1250 454937365 454937383
    0x1090b030f1f0906171e03030601030903030e0102040807030c060c080313060e1006090608010204150806030f0109080304060606031407030213050a031104060e0106050a031a030313030c050f0a0314 86
    0x40410065680c1714005809040b17a20030b1204541d20416082d50050081003814140750306d200300146003162030350300041d009440803a10850526895070001c9054060920140c401400701c00012b10b1080e1a45c10a045224003d8000e8000c1024000c00301c000305030303da070440703810140c0302001d0010a4442d003404001040750210003415402a1040c038030040c10541c000c2d03010344000c03900c204101540c51021500700d00c039074880c0c0000000c990110140c128007400d01c480d40030401070259209121211003403800c5a410071403c42d161700c004001d010501449102d240c2c041d20300e40c05c2c10030071417101410444100000030b0007081010307000910040000b031503030b2001e0018007005d89005c110070f07141e00e400007840c4408543c40c0d0040d07252000005074080b85103100c078100c660a84070b01c1c2c600308800400724054126044859230408002c200b0700090344041000301900f44c11000c07004d030507909515000444c0e00240d48190301c00c2c14102c41840095803071509441c200c0c0d43c007403140d001c0940c00b101c001d41010002c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 454939865 1250 454938615 454938629
    0x90303090c010c0f0f06050708011e051c120521060d0f02041b020309030c0f0a09020906040b0a02030a03050a0509151510050a020d02030a080a1e020a090501090b030f1f 74
    0x2070000070007002030b21f41109004080c2c607141c62105a0720381880c0e040340101240c0d000b4204000c204108254100b103004e00505111025403c40c00404030703101c90b80f00e0780e8800311202c0014000114540a0744600004950a0380354620a1904d4200b40002803000051081d02034080b550100c50f010466a81ea8410b496660b2042e03c54204400c003d940651203802c1145421b00a000b05400041140f5201111650300380700140510b88080c20000e03400000d400110025410800401000c100c050400c009840e810305268015a40c1c4c42c00307240c1c014151038000c0c00b0710402c2070400050150b43c41c4040b0b014004480c2951802c441ea5440301c400301b216004041d034664201c003203150444141503008008007110400368003220800c64808200706e80d60300c11451420300045046d000310310300041c107800c1108a2611800120805c0a003903c020040368022151440401d041d11400c21195800c01c14103002084c0003180d0b10309600d00000c0c2030001c0180280300000761703500c41d4032481c00c1e0038243b175003034020740070f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 454941115 1250 454939865 454939883
    0xa050607030f11100902091b03010b0307022404020f030109021309020105041d011d0f06041109091512011b2f1609051b03101706070305090303090c010c0f 68
    0x203980d11341e0300420380d0540c10f900498440e40000c540720b209120b0075034141c080c5000d10345160700c0d200c0e601e81142c1014000e03134218019041c62640414400c2100e42144909050505550425104102030301c01d4041d2054002d03410074450300050384d81c00707208007882913050310f0110304201c003480100c40500c982c2d0082c1000304001000003c0301200d000003681a41e042084036500c0642007842900c54800c200d82e208441e00340e20001030b402c0e04140e0450340807440c43e00c030034908049141c0001043c0201c103e410340c0e4500c0e400c80358002949408600c1e03e400780845002008801550000c07603001c0e0740e5100040301840720500035079100d551410040340701143e2070211603070301e0106105420380380c0c034106a01c038244c40c02d07030340e0b02260040f085d20503540036606038210085414110203402c40d00b50401405503002d1990b01400040382d00304202150155850400030703010740d01d80000050b04494001d401c03031030a80e000348108402d4103400502000700c13542c00d0804181800320741c42c2ca4004144070300c40081016403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 454942365 1250 454941115 454941133
    0xe0303090106140316060c140d11190209040609170d0c0f0908030a18051302070b0a02091311190e030c01020c0312033105010b0a050607030f11 63
    0x5010351290b81034540f143e0385100803142040c101aa2583d6900c0200081400210b04001c5036019928145040741b18080305280011004089414403510400000201d06144808284040180316120400450000e000614012900400d840c0d00b0b0052004003a1541e0345040c400303000c072650f4858001c80d44885260303070300c541202d008c0e030150600c40701c03440110300407032104405a40904641000d1b01d005000940c20021070f090121025044900400c8130000601c0380802c0640f00c4a20b801c0007617104280241c1c0c0ca04a0b071034100b680c81d0380148041000c0344144040402a991000f141121054294010842e020449030b4194184900141600c2c0c415080235910b48503504894688102d900071025903a140c01000016600c40300b00301842503140e04655800080b05014901441d080842e0341200d46005900d41501e90401000280074207a600710807040c51b080103824000d06200070f0003618841240b40c981070200c1c18501514400805000ba9641200100e034800c5052251907140e28048504104c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 454943615 1250 454942365 454942381
    0x3020c0a020d0c1e050f1306091104050916050f0c010623030f0703050616030e030a050c060c07030905040e010906060306060609060809060f27010209093301030e0303 73
    0x10006100c4c0103240c0d90160074100343d01d40315200b00c80843d2005450008084e00103400c110301130f1400300e40304d4000b594944000c500c031006881503110054403240040d076100d00384010450911002041180000100742802e007001c1d61000690300f0300100c0300e9070941c940b45031501450141c0599000340507001e08100c1d0100704203c1c403100074401e00310181c0035a03004031440740c8583c0c0c0b140000c0c0009404d03a40403c001c24030035040c031441c9650084640c500060130100710501c05095038004200840028408286504641000c0c4500c03500004000c030480d207008126600501040d05501c601172040da5500345103100b500003074210400580c2c0c0000704104550f1a0f01e041c200402090085030001002c1a0005c01c4280c0200645130240c070200009110540d03400d5100000c2c2038000b01044d03a00e401d0414408082c55080500d0144204030200250715040544203100154034010b00050078000e08050340c0000b48010821100c000520154103034042400c80016809004803c51680c0c840c4800000c000d607030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 454944865 1250 454943615 454943633
    0x190302070c0b210a0207080d05180d0206070309063902010c1e0e120c150313120e0d0c0503060c07021c212006070f03020c0a020d 57
    0x15521034040c442480c0e0b118400901140102d10001d420b002c4410304181d1801690b00381d0342e078021400240589001d0469071044160780100e03212511203078030307001409007190f2000d29040011000318001d0540d8401260025030f510b030040d2044041c181e45880e0141442080d812035070420301c585101e40c000420601c860300c02c410f803400100011100b814007141300a441030180b1002010f8640d1410842c680d178070b075066a60743c0c0030146501070102d00080d002e00e07519502412540031402ca0080c1c055450b020040c05a00c000385803035030006420030000c201001450303401000751603404c81d078030484208500c601030350300c9041551410f0b0304c60130070f6101404101c42803000000707584046e02036440e140c488403401d4805e4081c1c144000d611107540135840349801001c160b0010124050f529600130b800300302003003c02d50032092520400081e42c01d2090364440e00d200600c0b180b0403e101d8020201c3c0c1c50294802041d07040b48e0030110003015000034000500350720401c000c0c3d41d00c81d0010401c1d20048240c1c034042c045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 454946115 1250 454944865 454944877
    0x130c0e04081b0303310c030b040c090209010503070507031716030b030c0d14070b040f06110a0c12151b0212070203150a0905060a02180306010302150a0203190302 71
    0x150380300b1650316080344802000343e074014203120143c00d510022100400301009088140c1040740f85090010740c022850101d00d1200a40c01504c0084603400c050619160b2001550021079105004001682c280c1e68408100c130707845203042c82c065840f20b542e890200c401d20220441c003a8240524028400300d91611b0340d00e24405d45e1152003c04c000c900c03000c245074403805850102c9600200c0600342c24003003169a542a40043c0012050f103541d20340358400c6400c190065004031180030070040c000c0c0040340e001002c49240b50f00241c000c01680f015039558180301c40941c0110707048685e401c80d00380b04001000c02079005000542000384401b01c0c02c1c1c90400141a040600c04006205852002503690400390444400e143c014024001139a01842c1030800042d02403c4218516900c0715508003080003841107078010328080d14050381e00c80c10307401f0807100343c0344400c003d51281e00320100410041e92852590444400c031a2819900c80301101c105038118050a50a03c04031500444480101c5078117038000c0c54 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 454947365 1250 454946115 454946137
    0x50f1b12030406052508070b071b080c0c06180102250e0c0c15062b0b041e050c03100e1b120f0105240108130c0e0408 52
    0x604085424100692040c180d000440240c008000601003076201d4001040f5541c2c4003d03040301e1103086101079403070400c05098142d43c0414042030b0103040041c52850310f600200c180c9032016007000c000c000004208680040205540c900084001109800b0712100f6407034000201141d0300c86e8080281c1005d00c400c441075450060040c0640c02d99880d015040030000d281801c2400c00c000c81c00c04002d0301a07550050164181100d040c45401e004004c200040300b16040000614402401c00c07006000710054181150075020a40400340e4646030b8611503c00100d640040701d41d0f5454445040c000c08039110300320500c0d401c1d502c1d40742c00000d0241c0017440242603d010380403100e170a805c0c080ca42c801c0300d801d0080001d0300e070403580b0400078420507603812240c44074ac01440c840441102c095094134022a081090301c0e5651902c1c1003250456038024088400d0041c0f1046000d40039800c8002480a00002c0c04014802690700c0c03010140080a46400040d10b00b0138148071450400b4117244400390086601c0300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 454948615 1250 454947365 454947403
    0x5011d34050310050d0b070503040302010912050d0b0306011a0706111201030c23041508010c03060501030b0a03020105040e07030b090f0405190b060d0305190c030210050601050703110a050f 83
    0x4841c28464940c0440c0c58000707690340f41b5a26104030407070382c5030310180080e070856482d4840c20340841c0035070035100d070030081d0340c0c44941c0d4420150003103070305580b08007406c01d200e41c2004004200b102c5e000009101c40103480340308980d4600c3c1a2904000038000b030046100407030400700c0d10140b4000b202500301d041c5d030300030b002c1c00d01010340e6200304a2018101c0043e404141404540140c403030305042e000030b09200300d14810145025140c1c0304941c2100c007030a40250029440307400c20000c0f9601446003500524098030420306440c1580c00191480c49039106181c0358800607400510128481d0740708451400f03004260000c2ca04021851010901d0180c4080d203190013030205060034000046000c0c0c84046c2d001a03030300e0035580c50b0402c0100d0300c400d44038107500707000c800c00844845c11203d40c006400405180c4500c024484207040091905905810b04070b1198a07100a00003541c0e080740651350600e6140c035000c074022a6410b0403604105085100030058818598600040e03000810714182c001e004070110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 454949865 1250 454948615 454948619
    0x30c12170415090f051c15090302012021070c1509020f09041a0903070212070608280f0e0a2003010204260309090106050d05011d34050310 61
    0x61402d00c07240c070400d6400400314031102180c80c001d5085411b02030080ca203900e6600d8408613400255903050404800503590740c01c404101d81030174202c140102e8803905017a03043c88035a583c0c00e0101106c1c2d40000c5001c80c000c000207008144514502c10703100d640184000d40746040300180710003030503003020124800c00842a002d051410b000603907510035900300c035000c1c0260462029980d0f40d40c1c4080d0102e42240400c011312800340e1103001105080710441401040320324640351008001d80c102500c089585481116407441d08600694800e002e401c400d0400a40881e01060300d41c0280340544c00e10420340503c2030040b0030700810700b40840413100d01104d0100c50b8020002010708038842d81c007455452500024034041c4512102e841070030f00c3d240c5101100c3c42c05014900003094031409034010340004900043c01e1452113241d0040500404004028101c0100300a0f05c0d0619944020030100c0b01e41c44e0070140900e8011050a401440c980758130398040e02d8822880001c101d070b8800c0391a55210500c140c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 454951115 1250 454949865 454949879
    0x40602060a18060b03031605060603062203030507121103070206060a05010c06150504051003110a050f121002180319020102030702061804050c0c100501030c1217041509 74
    0x4000b004980e54181c210031080c540c3d910002821082141a05032105210650084200c400e100344868002c170010440361074212b0801d440e002d0018213a0702450325000b5000f415601107021400c040c0e515040104595403022030480309640c04070591350216007400201d8024a20300e0004500404443d03096503c1c4d95114400c0c4000038a0501c209800500e01e0b01d045030101d03180b603100001d00740c0210b5450a250b035803840001c0a0b40e40642c0c4075480c54445280400402c04031020007a2244000d4031810003251600f0300280c07030002c040c0b41090242c0c90b0b03030f020003042c50030a110031000c0c0100d4043c21515414860801110f103107600c40f0280c080c0c815000c107d460104603400b00000d00303605070b00940c6417640d42e509104140d0014107800c600950b2203600f0703507013580d00c60280d18800e480740e0796040d880c2d4a00c07100c15403a03d038000f521035810614103030050000c10342502800040d529642d0035036542c2a9140780181c403422000f036034005205404540880c416080016200d04440c942d81c800d421240c403903503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 454952365 1250 454951115 454951121
    0x316021c021c050903030703020c130b060405090606090405040302010b130203090706030b1c030c0b01120201020705120c03070b07030f020d1b060b101701061d0f04110a05040602060a 80
    0x162080150380814102c0c4102001491400c0365400b152405605010115001c01e1071904951400c4015800c158041d203e51701f0040d004100305244d141003407003008141c0000c500d40744240d024480c014514900000c030961071707140440d161f01101070300801c201c0c074142c01e0090081c100410040d00c200c0c43d80341c806290349013a00079a800399a8800190030035920b4040140c0c020411140c041d07801001c10504400030404007000300302c001d4040c2d124060b4100603454811006c000507002000c181280c0561080540d0340010510160b82040e200c0c56014509610501e140030011150187c3c1071141c4400442c0400d40600517103050341c82a11660181c4440b914182c9c2c0b2103a030500540700007001d00900c641e1001100180c0124940a44000078204220f10003069007a000c40300007001195000b030480c844e04001080240c01814589410000012000d151580b0700c0e00007280c0381e1051001c2000c003000d0f0b81c0c6650029122034202c003486035640140c0d0402402c1c0c0d03000740c89124054003481001440d0401140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 454953615 1250 454952365 454952413
    0x15010e061602030c0918060123090406060512030705010e070501230d180311060709090203100f060c060614090402220203010803070b0a0b0607021003090206031602 72
    0x100194280302440803041e140e0600000103070b03454840d18aa0440c2522003040f414040d003115030000045610058450303140c0031040e0300c0030252074003075480e0303014003c06d4a10f0700702c0b400421100350199403110304050015200c01c1d000701340c0c0000000a405916000040140005403140c0c0003805004034004a1503118925803007103074003069182c0d80c0d106000c25020f1640002c0c41d9444403c03070514819481c0142201d44980304041c083d440008090180343c2c2119040a0460b1214002e0819182030540200303506803d11495101759008030100310b5a0200140c4c280c060005103140e036040591310759000700086070290095561514110011130492a000010101c00c80b01814141d643e0311a03600340540a00d50b01450003003112141d40e001c0007010b02d0700003075000b00359440c021610f0300d503141014403030400094071071040e0501d452260b01c180d40b281c40a85007400c0d0100c80440311280400402da014107013240c40298080f00c00002c003d83c0586442d910094113155908032101692200d0040b0740c515688 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 454954865 1250 454953615 454953619
    0x80c04140603061605070606030614061504090b010c0204240806090c060708120412141327180c150806060901020a0b010f080c01020a0c060f0c0f0b15010e 68
    0x8400042e04503000c02c1e480300301e0b1195440c040f480c1c110a621f030781d011203c03030740c000b01e400988948200c8924142c501d90f90740c1003076044490403d201580140f205080c800c034482e24400c3c5c0c0d2108888205607004e60009100e403074000d4030a11011004505d03010005224014501c407030003803401d01007480c2d400002d1306032003441c440c8000c1043c84071400c2040141d80000c80112089041080031007c1c211514903414011131259800f0109042c1441c0094403d142110205201100130700c98460788203040e0801d8802c0303e140c40c03d14000041201a200035040c5a240d41000d51403c0c20b48424020031080041d42109000e031001500c420345509403a00180314040c0c0200001c1d25000c0440c1061074000f00038048840140100c402400440e0f0305c808907028240d110401013028032078104880b4400384006034600718240701a0110969641d1400c1c441c9980d4000d00c81048007100004d0b0800380151010fa20168012101c2c2d42020210300d40280c8101303040780e42c01450b441790541055035500880d1103004041d40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 454956115 1250 454954865 454954873
    0x6071506060906120213031506030b070513180608030316020106060806090403030509010e1b040b01030e0703060203070e0603090a11010f09050d0204090b07050c0d020c0a0e0916080c04140603 84
    0xb41040da80c01941000392054480c40c01c29000000003020303200d4a20023025900130202d14039285052280241800400e408240304040100c90072078480412404240c1e8411101e107802100202003040052030560041c9038284800800d116068080740d441e00d07172028844d802031002d503489002c11541d8500650720580c000c211400800c0019000b504503941c001364500002400c0103210103004e15200701e40c0803800d80c1c842841500c417120704050050714402d410030b08040c020b588401007103994490301440080c0c0001e6010022440303952141d040c45684200c001c099a840c1d0900564550b203031400108200c81100e0345000d414040d501500c00f50b4050740a503260100341d00d10700320602141520002080b1707806540c0341419400144c8091200e4000c1400e581c07119151030188a009181090307040c010801e641c048240b202e26a501d60406c60140c82007001d00480e03940b00c008070783d441e00700c4581d840000302c607165a01107480c000004000f40c04070b0040702e050000c3d410240580d140500180c4100b505900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 454957365 1250 454956115 454956137
    0x20a050d0f05030f06040906060b070c050d11100201090c03080409050906010602030906070302010908120402090a0b130c03140702062a09090c040b12060a08010e0a031d06071506060906 81
    0x10262241310b502007005400403e0502082d56900c0403202e940d0028000c4800c081001418444402001c03c090201a1a0035050311015102c1844800035245c205204030781200d48840e55030301c03c0d001680300551048101c04010b032240362950540d0030a000c0c201a40d03107040001203520f100081d04a0417034003580c01a40c0351a2500040c025540e05c840e6041d8203541d00cbd50200c200003901d00740104010100582c032084142400c1c03041240c10300300901000656814150035000300c0d610303030409161944803140c0c00542170000c00001d801a02a8201c014002980350003003092091b0081111441384a05000801940d161455040706042040300c0b82c0685107014040e0b1150380c141740b200ca64014500400310350501c1da68030800030440e48803014100090013040c4c10311034103062130250400034110a50080c03180740039401381c80d60b55614249001d0108403012502c40132040c42c510b40c442d074480002d45016600d504a0074400a8142000000c042da60b103030141c006410740c481c00c124016103005a482059000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 454958615 1250 454957365 454957381
    0x40513030e01051c020309010608060f271c09050d0c03021e0604120605070302040e0604151707050f060c031b070906080f0c010504181806060303020a050d0f0503 71
    0x2450300740c03081d818000b0802100703408052401c031502c43e425264202503501d103855074002c2c2c00c0d20781940c0310004e180d20070000e0024840f03d01800c0f503072103252441c21060055001055010041c0714006030046070203451164000152404141c100c0ba481686401607030a54a10620407200b030031244c0640602840d00040c401803502038440305480402c2e08140d112000c1940000300f15038805d43c00070461101484040040202c14011554090005d09045003420314060003014040710003031441c0d100e680d07100c0015a840c0113100551000d458103016030f02080094019107603941c4528041c17035118000bc0700c1400041e00e000700448908441c503001542c1801c08503064410b207480e000c0380341012401510008500300e001440b80714010444030f00208101c54000209600f040d0285100303504000082005100d01092841c100701840801030f40040c01402403045080c011030445001000d060400c3d80000605a00241028620f030192042d02d0101000e10400c2c1d88641010211001060041c000a8440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 454959865 1250 454958615 454958627
    0x14183007080a02010c0f0b160915081305010f020a03090c09060617100b070c03030806040504050c0d03090b130302090108030c06010905060118082a0306160903080a0302120604051303 80
    0xc148a0600200740e0803040e5242884000108ca00e008084101c45100d80459840407114000701a05202e40b2800803803d500140030b03110040c0b01d400e990b610941d500080000951041394850a601c60841d118010403400070068048400c050340e000c0c00c0108049800040383c8034150843e031040e00c41e40c100380e0391076517014045900204203080c10030180744000754200020004b040c50300d04c19140501c10034214a40900141d5014020758002c6e49450104030025100207101d40401d01c040f900248030350120704e4100c1d200038854111500a200103e0740c504c245242c09003000c2503d1013195003030303440da880d00c19255490042080c01030351684440d0040114000c950302503900280c040c906000344000d81804c0760048540c0754060012640300891843c0350500c205400f0307900900c0c0d80101e080c15000b641c002503413030402a0840e030b02c4007100c1030503003444d50051038034100030b682c456921616086214006002500403440388440803034a0000a0320618062290324443d55a00b03a0006112542d51800c54207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 454961115 1250 454959865 454959887
    0x1206040b18060c030f09060f01180b0d060902090606031012060603140d0807020a02031b04092a050607081218010e0601030c0b070314183007080a0201 66
    0x220041d081c441200888050080520a900210304540c0c0c80c18055072905400c10020200e0060345c20140600c4280c0b0220401d15044546003614070000d904d100d0305080041035030100040c2e01c26226480d03103081200c20b4001d074620310f008446410046e581d403002d0056078802180d20183d600350f81f160901222100f540d01303c11407170041000007480d640365500c801c00c0c0d0410025010680d80203558001030580c2c84542540d20a500788083d20000c28242d0100b079545100042200c5c4110080000c01802e48445d840b28202c00d070050000c901c6402c501a000300c1c1c84076109040400c004c01c9623000709440c1070000c01c0359400da91003178026107800d050308084e403400c400142c511008015a44dc0801800c403090194210208040000c0c000c0c6500d1860810640070b8240d00ca00403801c41409803c0210b50025014101e00040503010f6036110560440341c0300c800082130504c0d602031086041d4040013000d00c003592070f0319070028200ca800b003074400000030794a0b00303940f0600b0001e80c4100e5010005520481202c81 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 454962365 1250 454961115 454961131
    0x10503010306090305040b2206110a030507110604180c0903020a03081e0408010e0139020f0a080903010c03110306150d05010801020a080f0603070506090d0b010906141206040b 77
    0x801e16446510481162340b104800c0d550404205442c1000c06880242d24401000c003401c29400c0300b5100c1d400aa211040031360003509025000c14100e0602031020101c0c00703813440c010300f841e43d15500c03140120841c069080060800618090006000b0ae00544481054a07001000c15510901d59a101e96481d07110036221000050000c60000501401502500103844140004210745030f10480590071141d001002c61520184c82c1941121408284080054013824805842c00320402c00c105a2500460055905540c400c1c10002800e0001400242c005980200c000380586001d014003101511070049030b81c44045002c1000c2032482c60651013014168042000b52820410540e2854003107603000d074861f92090750002060b60030607600007041e9174003070b8002e9420300c0c1e0760a01402096036100140100c500882c40002e01c005103a81d226850710100f94480d0510b075a41d0f0b1502130b2070015101a00c50403034175285000e850001451700f01d0500e00d030030681d14018400e5a42c2d644a0250091020345540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 454963615 1250 454962365 454962367
    0x21c030302090409030f020c150904050714030a050f061801271b0206070503040f0f11060a0306060807030e150402011e0c150216030e06040f08070e090c010503010306090305 76
    0x514140c0f600d0050350201800398542e02056054984083d0030046200e0003076100341810303d0401820004101a5007400d00c040c1c90000e0ba95030b41040c2921200215010013102c4c0d4408001c00000300d0280d0402e80c03003004000110074843d140c003001d120302100d0041c0c4142034080740c1c100502080b04c050b00006244458800c2c5003644440341c020940c115040e03445a80c201c0c0318010400f50485404000c100d41081a07850014170714549030300c038521a02c0c0c440a004000301015040d80b014000e0004001c52003600040100340d80e403e41e100c0140040c1030070712400b0f0100c1c405900041c0740c0c1380248107100c00b801004024000403544020220b064000046c41281400415169540d030107200e994210031107401900e802d44102c0d802d0402d1100c541c0d00c3c070091102c1900401290014006850640d41d005516050090003c0340707040001e0034501654000d503128031035050001071120750001e803400c1192087c46443e82107485a1044503110300380c114440d030100c0c104100400004101d0740c8102e03082c03402440c01c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 454964865 1250 454963615 454963627
    0x70c0204050a0b0a030c1505040b0a210f0b090106020d0507020103230c25031d120d0203041701050106021509070b1204060b01020c0102060105040f1508031312021c030302 75
    0x50348200035074100352602e8042000a100a03082c181d611f5609510310705105040c00d240400c0203503288038054803c001c0251515a2046a03052801c482c0020f44411000380001910403400034001c2801c0d07003800784106140000007135900d00100b1103090b80c258540d03c2900c3d1201c507400650113002401b028142c00f0740306040820388044039580c4607003c0e60100380160384d0380c080424200031501400e60400f44040e007034a00c2000007a00b2100040c5030a2504500100038404031001602070a24442640c246019000540e900c9942c04401402518040c200d40007204807840fa00d182292002d00510000d030f408000710b1700700403031100f00c5158480103600480e015561100d406803d00d404c09505030528000b84400d0104001550250401c1d0400a20083c8802c08502c1c0000303540da41e042c42064090755803540d0124580d40560070508a040d95803600c00030642c1d85071511940c81d880000010400d03041c2040c0490585414441506115001002d100001e00c103e02c0b1500c20410001084051503820080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 454966115 1250 454964865 454964869
    0x231902271e0603151813020a0e0c04031205070c0924030c0603090510091110170105010e12241f060302090a030219090e0d050d0e0f0a1514070c0204050a0b 68
    0x12988203072141b50700210980220f20520074982682d4100039042007001d0200440400c0b010156011a60440e11010341c1c00ac4a540543e0b040c864580082c100484160011034900c010f600006074080000e440d0012418810040d5030307024000e800001d00724110503001300203080c07003a000b881d22640588242d40c0301d2425511054102c13030500c40c4c00c40391800700f4900c8007c613107003011142003002501e0404c01e040310083d40120070300d00c8050040300d05004081c3d2020640b5100e43c0c8050308149414011034002952400b00480700080720300300c0860114102001a840000c03094612008019210480c420941418402c3d4041c4d0000b44131180c01c082035000000241c2d41e511205c2110504a15028100900f094150000e8031201030009546a1010290ba41600d50200c11140803540c0c03203400041d0240380c80103042c1045040c0c2c0d0002c4562051010990034089840496445407022620410100380195852580c1020846012010442890f02617015040036040a0b0780001d500000103020500600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 454967365 1250 454966115 454966159
    0x50604140a0603170906030f091e03031005042a05071a1f060c1b080304060503070207050d030c201003020c01231902271e060315 57
    0x701071203010740740c1c1410000c2c0718590318800003034000a00c000d8030b40700302140801c2d481e120241550040c2914000054201c04061242e034281111003882d20b4031500c181e000b4241c1e607030415103400000c8904043c0010301417406210b905d03206c0d4402412806403441002c2041e0281440a4810060050822101c0c1c001010390850026125084c0303075103411400c010b078a1944002f485030901c100107260b4001800321a0300403000c11071030755200b542d4600070701d0078410710078111500b40c3c007072516440045408503c030764106028500c1006c5079400c45243d690f850041101d01000410b001e000b181001a9441c08568040c0d6130b00d0000414004c1990503c410724085140d10500c10090340000303a010880910101c001c3c02248969140040c05c11051212285a00c0341d030400a40032010702550309507884000c280540644482c00d03840b001d010703101da2201c1c2e9051480e224010096100e42d60b000740e40303800c50341165001101e069010b070519065035601c6400c6503620a8048000b0740c401c807103070241100250b41e03003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 454968615 1250 454967365 454967371
    0x80c0d150306050a0504050303060f1503090c12070e180f07030605011e0b1b0f01050112231c05070516080d090e040308060103090213150609140405060414 68
    0x4030248510034a10b0034240100c1e0006890103d0070b40c01c080a01000c02e1002040e25003002040b50000305003a0480001141044103181d1020416800320800c1940c910200c0d108460003c117542520404000e5170f082c0391a41c0c070500030302c048030307401c0300c0407030a00580b8441e0902c58440e16000c42c5c41e40e0604c8030b0928036001d0f42c0c0c0c1c07003100c0d180e449800600918048640c042d0030300011107190802d841c208150407007503014140c0b2804011031894401c404251080081e40d5070604900c00803c000e584524250942640066041d9450003042c0300126082c0c0d510795010799040e01c200301625580a0204615543c03011146241e02000700034000f00700862018000890030034100c41c1120110303460206028240465100d200c418480c1c0f0b4078040001607140d40e0b86a9001ea850300c0d200210360f5499005074004c025202d0040d4010001e60f00c804009a150341c04038141001c2241c080341c410742c0d1007004a6128815010b8182e03400120148015542041c0e003005400400041010a54410304480121965130032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 454969865 1250 454968615 454968641
    0x603180c01030b010215150a0608220b15040f0212040c0801050c0a0503091009030e040b0f0319051c052706041e15050a0e03061006080c0d 61
    0x50241052552003004445424042801d003842040707500c10000c0c0d1600245503220079454441000120b100031f544a0380803070454000c22414400361181c10052512008481c602c03105400c566a40d801044c1094048100070344c08044852561749010401002c448094002504245ca9210781c076041c4c4200d0001e0b20944d0003c01684005107081d0030481403401c00e540c00440c02e87d1501d070038484158461001c80d045104d0070b0401725a81d8071f6039145140380490100380320401900e0803505404040c1c0c030a99081e6160011901400400c4028003000400918003203c0d42c0c0c16030042c00c0078001e41c0c0c102c00c40f1850250180c801d407548901040d80f0389614064403a1010002070700010040c0d1041d482c050000070481440c001c90954541d21008180244158000c0c1e0200703c03c0d601c0c49045222084040c00040d0850142906502841c1100540b15400c5442c00300041203881000001c14103001802c10303c201001404507190707514020040c0c076840d8014007000d01c240410030900c1d600d4441070143c540e4030822 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 454971115 1250 454969865 454969891
    0xe0123011403181e0c0d03090f150e030105060a060c05030c0a11031605062a160f080309060f070c0e010e010315290402070212030c06180a11010e0603 66
    0x340f10041400d044881007160880d1980c2c01100032064000190b250640034240c0704c0c0e050400d4a4201a91031400a90090081600143e4042443c2442e4014041143d001c0d40b46e4902c02541a0101803c0e00c504503003642e00156030900400005124010182c50103010f642500d2801d58121030641c1080004201a514856414110340c020b0408000c02d00100c02c481103220701c40c0b420300000074003501c03608440090030500c1401d40511400411301101100c4910401c80d90412040540764010b403c00d4402d01021155a220000d02e0450210454681140041c4440d00d0700841090103012904000d4082d0b6021903601d5010070303003a9401c2d100c103000c1c00c81f0403500d030582d614600c1c180600a494176850524030f8103003c9150320480c3c0c5200300c0036148805401c0c0100c00d03850031021600034003590f400a540001c0401c001c5014040100080c02c56824403410780780c49a03140e04560f504012850307503042d45940041d07080d4006c1103182d80704000f5248145802741801460030300182c4a44c100740e41c501250b4603 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 454972365 1250 454971115 454971151
    0x509040e060609060303042108120f090d0504121b1809060b0f090601140d09030c11010e0a03060b010e0409050c0307150903060e0c0d15060e0123011403 67
    0x2500c4000f00794868000c030011454582030044100d000061404501842000040010108058401610303000d01070100505241d10700314000b500c21002c1a40c1550300ea00a40045407080d0b44240100d605640490000403404000d42d078411780042041070400601c00c110a5010517940036108180900701b102020124410181c0e081100803610380c0d0080c5840b9074500280c541158440108003940640242071411a00d6a1540907030228410b4000500b1464a400a81820540c011240c0207455001b41a50945621740030019201c0ca80281180e560100d55030808100061481d044400350450614062489403152804102594a188000c649580082403250600c0c101089000000c01011420824a003003c210113400944c050101800395600c4400c0581c6080c01000440c0c0c10000240c900c0d0118401824000141c200c0c02003184400b500f00100007409012600da4541600c82522040c4000c070019008440031505503803c5034140b1400b003202c0d40c1c06503104009107208201d07240750303e0b1b0621303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 454973615 1250 454972365 454972369
    0x6090d030b03010605090c090111010507020f0708031e0c0106080d030b10020111091c020d0c0617010b0406121e02040503070b120612030c010203191a010c020103020306010509040e0606 81
    0x1c0000d28040d00984c03400b40100303c0c41d95810700c029044244c04e0220b0341d480d0070f40d10049a80c80c002e107203400c40c01d60070710b428000115400a000f10317400080c1d0f4251024103407980ca0651301c0c1d10503141a40285108680c110200c210620007c00d40d00907198000503100c2d98406a00341080c0e42c0c40b9524000c2941e0300042c11060030300c01c04210408a061000300003076648400c91056a00869a0f128050021004080c1c3c0e0480358444400110390014041080d9564a20300b00c0807000103030045200180e0400c01614002280003103641c1a200005840c500f03103070400b0011121400c0042c0e603400d0998952400c144034403000020070500d10384c110300260b603660805041c545001e00b00d070301c9110340e04010490304003600402d6800c950011000c50b06008410300c011800f5280d0b004003401d03010654070000512040c040210030010840700300580500000e08001c3e010103400582d80c20090102c1e40f00141500158881e42c011540107205040031810315551801240866110201c090400c0d8040d10a100640c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 454974865 1250 454973615 454973621
    0x3190b210f0d021f050f220204090f0210111207031218020a0803072301021e071205070b0a050601030e031305091005060f0c0109060e1b0301020a0203120c0c06090d03 73
    0xb810710a5081c0140c0c102030704120a610302c01861111f00c1d808004050340b612103107a24135604036070010010320119a050a2040444840c42c00480c41503d6407000c4c030324450302030141494100e00183c0070346411150010480c0a581c0109011020419005260304030515244500d646d404d84a0110044100300303407042c0981c0d01500c0c1c00c03078480e660080c004540000c506040b114022190f1101e100e81004059562502a0080b64503030141800140c0e0f00c1104440480082c3c110140124840e4140c0c10400005954510038903034040d003003038240000201c003850303150020b40e0042410300d030015410031400c610030706503000340c0c80d00c000001c10705404000d03515103000c60b01d8204102c40741c07120340b15251900007080c130702c1100c2d14078080640108401c00601400c0d8040c2c000903070400030a200c141004640207455058001070401c90003481e00440d00a03090510a81d001316030b8a80042d07280c6126200043c6aa400062005168610403c02015982d9062082502505042005200f0128100f10180139 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 454976115 1250 454974865 454974913
    0xf0f0603030d09080706060b1602060f09031515040203040f03050309070302030607020f150c12040609021306080d180522020c010b0a061b06180f050303190b210f0d02 73
    0x2803000900a27074407d10362001c010180103a040300c0b070540d684004801c0600764012040c42070380c1402200b0703050401880140d1081d01c0b400188501d0040d0a124504100880c042620041d2203500d000e6080000240140002c6801840d01003c1303c0c000c0e0b5980d80044c0c80c0541c112580001a007007140d031050346510130880d4102520048900103060b161203000b9100d9401051199890700c000310001c102440810b41c84111100d03001f030450250b104410021b003002d400f0b140f0a0800520038402c0f85a241446940c030b11000700185196042814034080030000d2454802075450400c9890380c0c901601c88009200a10380c0c1c0d07a1103000421088580c00070440c0e501314640c0180c041c4030021a4000c08400c80d04501c40d12550310650000d003c10001c0d610400c0340b11202002080d1034100e6444900b0b008000001c0c1d4454444600481d10a80c0b032640c0704001da40d0000222074104c1c051002c4000b0091420640403050044c04080711100c0507115170591401d0070408122003da0864203540c0c0143c1c442c6410340704 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 454977365 1250 454976115 454976129
    0x10609150e060603040219080102070602120c030f0f06010201022b0c08090a032a0f0501270609020324010e180c010305040510060605030604140f0f0603030d0908070606 74
    0x1e031442c10001181480c840203100034412403079807a4191b654040d100c0c980025001c4a402152035111f10301d082070096006034900c400003000034002034841040b01088a2040a4480b5102007540ba4a010f403115580040c2a1905554080c4000c0c07a200c00e041c40e4a00c100c442c00c0c036a01c40b10514401c0003e0454a00074506404c00c1607280c200034010500086400c41e25500d86001030300e42c02304c0041d0340c070240c002c00300c001025a8090202c6080c025805151030140b806034000300010365000002c40a4810250800118498000c40c01c101160301c03035019030013243c0058107442803108410b400080440b50f1241c0c54080c00306c1080148400c200045003076034000c0c05901003242d48170344200d403e0703a1086a4040141050b484000107000c0103414400f481d9200700c2400309004068403088058000e80044600d07502070342c540380c2080d049405150005026180820540f4026226540070702140c51000701601d030584410485809801000d2107640ea49078024001161118894070b0310720140c0f1141e42c0106 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 454978615 1250 454977365 454977389
    0x210210050a0f080601020c0d03020d02010e011a0d05011116030e04020708030103121215091803080708040c032f0f011b14061312050315012001060915 66
    0x18000d80e40102d09649040402e042c40d001c15501e400c0101d140028220710706400c500311384800340c10150002172207410000302d034001780700800085080a007201c03140344188040451040f1580c4507420008444842240140004039a03961005481c112543c081d0035124202000c4014110a25601c800c044400481c00c17201903203420056201c41e030b068001030102404001c3c66800da844603500421212840e0306071607034207001c1c20062041940c88141140b050040180c00c02c00321a42d200300c4508101c03061070b450307118030149403100c00040f9441c4100038821100c000c00c3d614040089050340da8041c10401c0c05440e0300d04141030010450030050f103a510154011540c4625600450380c001200943d0302050000c403003001000b034180420100220100107003180141c4090110103000e184140003058054807000e40c0342d80c04401c044417580b01c21076880181694210781d4002c198030558031003080003030842000b064074442001607821940380e540314240e0295100460140b240303103604400010466a0501 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 454979865 1250 454978615 454978627
    0x904150510180b0318010f050a0608031612021009050313051903110d061a03120705060601120204030b072d020307080a0306031202060f15100e060421021005 69
    0x7101c024600340561400000080300282d82405803001c005d200340b1140c0d000340802042d410140b4000c0209440b00905242428070224203900000300b1161684802c5000e406401c01300d844280c1d40c040030703580083c1103002c2d80481600c005064041c0f49092401000595500c03144050200340f2000c282d40040c0c099510900009100703c000c020800c110f80d005580806d90b08a0480001d40004051000411061070801110a208a0441c08807e030b81130580423980382c10030074454080b10740552000209660300c8040001c069521030301140c40700128103280903003420303200d03503410381241001c481120000d224204c0561564003200742c0300c00544500f88072900ca0815091000351031b0f11803400040d03c882400240c9545e0180f10790711001c01540c004c0c05c3e10704055020540292140016109224007640c02c0d000f007607880900002100d02c0c0074008101c6940410018019910b10048100071603005000348030000d0500103446500c2c0a040070001c00c100004000d204002c1c00d180782c0c039140c2d402c09c0024000303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 454981115 1250 454979865 454979897
    0x60108150117030d09030e06040f0e0901021c1512050f0d110c01180503010204060903030806092e0f0f0501030e060403080609040f020a170606030d0f030f020904150510 74
    0x301c80703070144c844401044d4801c95003002e0760144c120052046e08448002800a66600c0d104400c005850708414200c6142e00e64420150907030003441c3c00343d661072101b154001d030303409030350340c05642c911040241a1490581d1000c01d030340344440d000d605403a150498583c0f8081c43c0c0060000b621100b280c5d0800300c030520741d400e1441da5522511507006040c803c200e0b60100389a1642003404005010003002590340e240c03034001c010b0810003103110840124041d50080381d81c0c0d1408005040c400c036006240da0041c62511305010195001c403402d100c10700808600d02280d500606c514070006444a0b07122041401c0c5020001003c8801030000582c183c1c01040600c80040d40c0040740c2500100200e6006109449905145111015100c0000d501c000d222038005a104440441040c0c800486030a90386980d07115130502d9258491a404400010307070b82081110720500990021f40708002a0b600141000700a0012500f21540c0b003424800c0b4000040b800c000925200c0c0030f02c1b00c00d1001e031905814101c42c0102e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 454982365 1250 454981115 454981117
    0x60b091003050d031104080102040303030b031e060403030b011e08010510110d080402011b051005130b16090e040f05070b120105010f0c0f03210c12150806010815011703 74
    0x10030f0408260b10b8144000a524851003500d0141c50050021503a450352841e014005202c0142403901a000d10f06090b02e41105055503610300f20009409000240d84036034048000f40043c805c601d0610654a09003d8581421010040180c2c02c54881c0798680d4109002c0003420041c0c150b03204204a00402108c28009010402c1d600e60f01550801d0740721902c4610060b035101074001039410000040009580031300100146143c40e5540d4520100003c0e01e07111000d4942e2082504003618041400300418640401d0b00c0e0207124490586c54010b20040d1640e510407101101554155141c0c0d83c80040b4405111081c4003c40003800c1038040b00c1d1800800701c0c41c0400e2521305102e1036062180e8290407403803560165085040c0a54420b10325a014645443c0143c503041055003440c807152a00d04884040046501c2003004132001e03603c4051620320f0308103102c030140520700301e0061382d01072000000400020400c5481c0c082c3c8010300c080c0c40344542d250f203aa443c45d001644030302048c4e0b001d603031041d44c1d0900100c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 454983615 1250 454982365 454982383
    0x302030405040b22050a0c0512060906040e160302130506010c030c020102030403080a050309010c050c03070209060d02040c02150a09170d0b130605190617180a060b09100305 76
    0x1940108483c01104000f4640c2281c89900f040b21454214407251005029840b581c8202c0c4c0702c80041103107a81d8060100c40718001c2d50b1019401c654900003054440c030303011030b810398040740040c4040340d88105001c480781040c400c02d4003030b030001000c40001d00c03c502e0500d0400c09014148101042940303002c000090000c40040c00240c20302c02040e80c0b0780700b5a44240111006590030607400742d5660b58140c0002c02c15842100c007005a54604240c034202d4502c51021980075089040003541840d01c0c076000c0007034000001e000b2940c03040741103c41600585403801151110101500908041004044000119035004101d605160324283c1c001d800103018010903201c010a20010a0301c80d00c8402c0388500070b2261003282603100360203d00811040c3c0e070f1604841e0036101c060352106640c4144110b0206c1c1d0f0034480c050000420011044e4a440c1d15030518003d50140e031300c41c2404020700043c461035041640460702035034001c5d29815003e406041200002d5044142032121445a80c03440d110360b611800c01c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 454984865 1250 454983615 454983619
    0x30c070807061821020f030d11130909030801080105091509150903031b040b09061303061e0b060a0c0b070c050319020c030325020402070602070b01061b0302030405 72
    0x42125002e11000b030b840060803c4062900500c40040b5007003d0303400000449034034801d0039802c04e441039528404109040e211458100560600a081c0010400740038104c440180c0385106100380e2102c030b04042c5200c00102040480001e0102981c10010000e5805821481007a8108020b0000681000641d031903009403c5210240ea174a869103080d051445003014802005010002d0006282c8040300642c025054070310b800020b10b0350a1944511030045100d80c0e5041c08042c800f1151034200030300180308070040f600d00319503d1034499440d0340c11200c14000300c0360380c90006e4024001d0f501c018070401c00c3c0300e07500311081c1c0d05045c00c40030024500040854014004030482c00800c90072801070001d4041541d200f0f040d2516850503060f142e0380b40003546c10440041c4950480a01e032410080115041c500101d05440c1140440003508203440350903202c201d81260f803c2140740041401840a80f00642c441c0c04440000e502d407000052030885504031601c50120606501d100081d000401c8500321042 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 454986115 1250 454984865 454984867
    0x31409061c0e0d030c09120203030c0f071e030503090d02030c10030b03070e0c070f051c0c140d090909020a0b0327030306181503160911030c0708 64
    0x20209120780104005030501e9400100351840030300c40e81d0000005203101c00119041a04511021404d541c000001078010440400d01441103909000300e8010041c006401c03070745096109103425190804000303e80c04141c102c81d100384216280466000810001c000501e041c40d400c1d0b4580075100d21410207114401d80c00d88001030215241403020305078411004002c00b00072040e110010b800740910041041c424000c0031030104150786450142805084601c80d290300f010800d5031a41c4030030f2720100c815540d6200780540345003800d41c15080a81a50507903515040d20292902e044403014203070320200046070b040210065821640002c9032402c031140502c003c2400071060012032040c4016030000c40e401d0400008112110058210107800c02c003d04003035078002d0384040c01d85604c03800250ba5032940403c46805402104e001c036400b65030040d81e00150007001c3d010140021f490070300c40c0405202c1440c0e1300513041101c103000d840340611210310308000610f075260200101e40c45208070301c801410010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 454987365 1250 454986115 454986127
    0x309080d050f0c0c090a060303090509010b0403120512102421090204060e0f010e0103030c03050307030b0a03060c020106050604031713170c090a18060b03100203010e0702060601020a0314 82
    0x104021007101d041015019224601b440b010fa180940281d0006601080c070603c0c0c001018103141249a04941080005500b4581903076501940c840b1407410442c10000140021018000c046075001d01810787c0501d0f005075945030103446058500022a03105134030150f680c001004540004c0740c0404003004007103a50800b994a0180c500800c5902400ba400a141040104600c400602070320301404144000d5000c1da03036a00013400801500740070041c002144100c100000078003c00246400242c10309004c5825681c242c040b031603074400365105890482c0c685051645180d02880b0b890702415041d100d013071516040d500c03000c50b0241030704800014204c000a0181405a42d21b860201611a0000c01301d201942c00d000301e55154600b01041380708030007110204050700094803a10140316000005401200c00b5512014002c01400c1d002a80501860741062003000d0130344029806029080c0d460202c0d400c0191000b85440f00003081d0506540c044850b400100c1d802c1031700b0f11601c455800d05250740780 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 454988615 1250 454987365 454987387
    0x20109140a02181009061403010b150d09020a032901090e06041b18090b070804032106170709050606091305060a0b070f1b051509030f1501030309080d050f 68
    0x444c255000040007464024046081103218080002c0c894080713009020f2003512600f000004044a035102c400e8110410003030100600541081d020b850004110101c0f540e40ca440f1100d8042c0300c0010380f00303000c910290715800c42c000c3c046030a01414484004011807080f6071205c079599000904081d0520355004001c19010416004000141c08412450520035460054030750207800c2c0c03802c04035a400702400003e0425446074280300d01c5a030305583c807101e03017207204820060540541403400c4040341d03da02c0701090851000580100c4407410b00001d16a803403400034000200ca101800b501e2113840100a802c0c82d40c2e4441c1e0710092030855880300040d0741d4443c80001511140c0c44d6001102e200300c082050000c1c4106980301c41c1d841c5001d41032039941d125400d010701d980f420880c0511540004020714032291440e0303490103000500d50103011205248140b061141c54036100600c0300b04802c010100510800d0f5010320204020907a10000b8580000c02c1407001d02180284000524010740218183d00c6036 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 454989865 1250 454988615 454988641
    0x50d09020a08060405060a021206040b12060c09031507050f0c1906060305210a1413240201020903070302220504031812020d2907020109140a0218 64
    0x40d500520000c0c0d01c6a40702d9001d5110360b003c44090300c9a00846000460749480c900803507103c0c48840005100c9130703a5010800000380104001150001819a940d400301a4200009405000b040340381c00d40314840c4404140c90300815039041201d2061000c14000304070f4001c4151000c6564103e82d840e1615280002c25241811940d0184000b50b07000e180da2050246540c0548103a900034020f0740d15440a4100041c01050340420740021010200400706d0a24030400302003010034610074400740342c0f1030703054000070803003607250400c0002d9250b12002490340038070542e100c0354803201c1380025802c0c444500002500e90603107220190250310300c1d4400b44d2036220300180321010b4440c110130401440c24582401030032403000340d4482c251240c00b01c80114001484803180b44117a030b4010180e80c0c01c0b0f003ca45c0c0b5485400b19500104020319180918100401000100c580c811821a800040c0d0480d0740e08040090351680506c050058011281d460090b88a061020307108000c11070381e04c000303903ca41c0036055903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 454991115 1250 454989865 454989881
    0xc07050a050618150a0f0906030509070b0d020409091b0e01030f0f020f030a0312050702070305060c0c1609020706051308031b09031b0f0919051f0b030417090a06050d 73
    0x20031907000404a00c0e01ba00300b43c0c00c0066140c581d03903151031540c540c03800703038202e88040d13611501c294440b181c10031202c84072a0042441d400090000b5082a41d1001584103448040c40c0440380c460780c0b03000144100d040c03044810000c058039010880039501d580c4805000843d001409880704007644000001e54541c42c1c481e440060f4080c089071200a014100148a00c03022400f85000d40e04180205490341c0c800200c0c0c505498009018002030344a94500c0d030840d80c0512403110ba5406680b111100d40004418100c00814680c140540d80303400c07074641380c01280d030000c0444900e01e50341c202040c0400c1102e41500d9118065040c51310b85410368000e550350901032480442d87c92b1150301d003040112000c1140792000700700c09072103d10701c4084e40700821840320701c00c481801220300741c181c0102c190b003203d804c480d400c901e00806510403001485c0c44e074020144107130031410b0414000010704c406c202c8030101c5c01000207020b003001803d204da80400240c0712506c502c2034008200021940d2681d1200580c803880e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 454992365 1250 454991115 454991149
    0xd02070e040609020109180905120a022508071d010f0b071b03080414090c2532061302030c130f0c020a03120203010503070501050714010c050c07050a050618 69
    0x10110390307000c1f5034000e0001c4910071240b038040c00402c160b1600411050781c422040c80d802900d075660740a2002c0404000214110500303822940000500751010b01201025088582c12100c107401c180f115152a848180d10510500c2c03641401044800f62b00e8068403800d0b54480f90241804820710014186441c80781c001074680c260005000075400c2c00320383c04d1f5829050995001d91140d8401c3c0c11081580103100c40044007150003601001d5030010030480da9645842850310002070100c440c41400429240120381480c0e200b642e03070701141c0410030060a6030012085020000b01842c039030110b43c640000914136401002011022481c040b450b400c00401c019092000300001440d03624003d545440c4400140e001c41c200e049a2a0024200d008070380c103a58024006002c1c481c038090044038168032100061310306050703511514407012001e000342d5555564903070b40c09440703414092149041000031b1340305d64800e0902440401c0a81c41e5001a5440c44580300001c0c048602c01e807001c80d00041010080705 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 454993615 1250 454992365 454992389
    0x7110d030507051306031a0603060607060510030b07030203042a090b0d0503071218030809090402063106050c100504031e0929090d14010c0804050d02070e040609020109 74
    0x442c5c1c0e142d05500400c0400c42010042a8078400c000510030144400d5540760380140c82044010301042045d000503410440580361400d0051380e0351101c01d44030070107890050010f40c0020500040c000351b035400c520070034100c00c80500a10303020b28506007807200c54810201010344602c2009016968422040c0075140c01c0001d4a1780c4444030300d0144140410700ca2507030041400280c02c0d648d040310222022065075030090a0034a41a42c80c3e04110000900401c200c0e480301c1d0421104000440a4242c03643c4d11402c51945c0b8a5911071006d14540c41c040e64111804011043c84002c11002c400503d001240340550400a81c0380c0b5a81070031074401ca8035400082e100c540410100f101250b0002100d000c403041102c503101204001d2050395403010050021940c4020f0900c10101245060210412001e00c1810700002940d4540404c0d42920a14400c1c8804101e50104000074860180002e50000c0700c24406840002e04225409605190181c00074042e15960035407001164000e820740c50191004142c61 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 454994865 1250 454993615 454993619
    0x4111c03090f09020c0d050c03070f060f0e0f0d030b0312040608010801110915090f09090c0306090a020d080d090b0f0103031206050f13020906120f07110d0305070513 73
    0x2502808031446100c0300480c0000002910703084904c00c1c0c51446034101d0152581c4c070400102101c440d044500741c0b00b0f4a000810080000400b1003050009007071240740c0208010003141c011904440c2c01c08030b040e00710381020b84000c0344480c0108d5490302032070080c18001038520f9a100409e1a02c01315140c01ca5841000180100d0566006a00a4100d07000b5000074450561410180e1919000340e10f9400c2d0000070450590105c4a000780242080e600050300807104407224000054100b03109542d2414280c020030901616414180019980503c41710300a11905003a030303010074108621a00041c2400c0c00c04030b01180c03403d62642103c0000c03500300051039060706064641d191003080038441140400c0c90b0900c100050111402034100321200102074201e08803000d01442a04810802d5400c03443d41e0802450106603900f8002c1d000350800300d0070300308840c07030322008040014201030b200bd0b0500520ba9505100048009010502400e06160200d01525607103004e641d203000f5071003403d0440b40404e43c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 454996115 1250 454994865 454994867
    0x5011109030f0c0109151b03030e1002030402090f1f031209060807020c040b0102160b0403020a05090108030403081b010e060a050c04050d1b0b0f04091a0904111c03 72
    0x250140100480035a10880388415403580d9810403c44180d000c540907001c01c000d02e040300d2151515042c441d00701222421840d500e1407043d400040702c00ca02190391030010781d612040c00c0105111094503140304518500745034001034181c41005002c22403684c88100002d848101c0880941c004074840041c10f1103454891401c0da48006c1403201c0d020000e40c4226000941c148030b0200d85004038040d8000d4150b003595141032102408a0f0100581980309010b440e40700ca105000554008022551142d81c0365400c43c0304000011080350702c1a8401c010720720052100c884080100e504903540000d20668510b03107200d0340c01d045586200c2c50001c0c0d5190000903d012400400c1a82c42441250000c01581d6141c1f0041d0410340a10f000781ca8120342e8610907200041c1c07105884c0e40301e55003940c2e0b44088103584ca400789500c591001801c2d0959002c0460100700d514050300500909824540661408000002c041000c41c4030080c0042d00d41440030341075803000d45880182401a50b0b4024011100c4c1c1c2c11420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 454997365 1250 454996115 454996117
    0xc0604020108060603041e0c0f0305070503010c020d0801210204050c07033f0905030c0d0f0e0607030e0a0e01120506100806060d11060406090501030c020105270a050111 74
    0x2a0503404103281c0700000d078030303441e003182240e00c2103900525984940c40151024a5260000c09003250740050b00c80001c61078400400c1d591000314820001084640d04040525003583c030707400c5012042d54000c5962003030307080c3c105200d10f0556061840000e201781c1c4d00101c00c904100c4100340a50800c0c50501031201910050008100c024002c0c0c40c1d580080805103a006404050844040807081e0308031100d6001820f070700003180c00340e03000d10004505c0704400c3d101d442c02c59122201c035420303943c8585d585e89031043e04411060220b0307401c3d040a503840c4140202040c2c4501c203c003070060800c042559120032668541d48074002030f01150311845115171b150011801020410901034611317110310400142840c11020f048030031385078000e001d01031544401d021b012074504a10011625200315880d154455241d0101500c0100345590310001b07541c0c9041c002400301c5181d802034000b164180010000781c1d403021031401c4103103914511945d42211040707464074105901c03607a00610550808480e580940c00c120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 454998615 1250 454997365 454997371
    0x10f0f050a14060303040b090d08040f031b0b031521240412050304030903050114100e07090314010b09040812090a050c131d010903020708070b0d020d020f0c06 70
    0x1c01c00c0018201000d42411807071812608607074140d10803c024080325903220094903008070050146940503e003582c40c003490360072036040310f104058004001c00920425007d1410003820140c002c2c581a4100401081c0d07074403004000e440341d00c00d2001031100303a1300c074040034090054419082485003205e1020207034a64821001e0540c002000304084510301503416000c502aa900254402440840ea4802e44054000030700907028814000350010108100703010781c84005111002c00c0c400746c6015103140c502c090305504241a0003008900b0400c87d682c004240c402501c4d013101800e0808403140d120b09026204480b8895000201c21061100308444200030708040c2004162110b070655500b41469640d100ca0340001d002a4843c00d1b500240342001d501c0910b403004800c00c04600c0c14180450315842c0e450104c06101075a540c2c0b901c4009155051110b4030240442c480504040e5180c20401640c40c007441d840381d0702c001d80c001806032907170702ca81e411201080b101c054034545503544030003a036450340412 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 454999865 1250 454998615 454998631
    0xc050d09060c0f090605190315090e1c020c090408040906060233010e04052103040b01050f0105090909151303091202010801090c095909010f0f05 64
    0x90181d12116600820000d42038503021b64401e41800010096010110200d1807034005055480c05152190f0f44003012100141500c00004201003560b030039803d1800041d4040e190680388500b03012035402e6800701e03001604880c211142c180c10f86036820403c010703101d154085400589816000190950080f4956024050b6141e01d2510310440140070704030301100702c465040d0b030341448006003d040d80c101e400a40081c041d5048a01d15990315454660108011910707003011580881040f0801c4200311080c0e000d82003d6405504079004080041c0c0030b40500410580700d07901d01000181e005504104002d07120568444240450904104814074111145000d5001500e55840820200c03a5039041c10140d40d8103a40302d0381260700c0e010400009002c4100c0020070002000400103203141a541c203840c0c02d5a107030340d07040000c9114000301c070031022500f2801c3c2390182d50000038801ca400305402c4911440c3e0106030714903541d40e9004d003090040600c2104900074514207010a2001805940014410010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 455001115 1250 454999865 454999877
    0xd1106032d070905011b05030a0903021207060f050f16110111030414040e010912051c0902030606060a140301030501021903201c090b0a180302100c050d09060c 70
    0x200315501080410440c0d80d0008940f0b146001c2044d54420aa4925800b0200e203e6403050a0b41c1da50b042c3c2194007a0400e900000c10b000010f200307611307010305411281810b0070000c000c850700e4800098a102043e00103401444000b04400b17013086940f01c1250000c0501d181210050449840c0c0412034840307450456000502d800185242c0c4d00c0004129400d0b161600052500842e2010800000e015000d8613070b01c0954031182c582c8001003441d40103507401300c0240c8801c0d031244810040c1c04142d583d41d10507054038074100401400982c801084494100c0d1050350309540c0c49141ea4810342d245104c4016031100440008000800d0160640c060540c0d0700d41d60700100303c40b5112980c05c4007621103842d45843c40100003098035100038100d900522040f094004031014003116059004100c8604c640f064403400b5a440802c010a03490740301b24a0401c003050303151800160b40d901c000f0b507210f03c0b0041610b00321780ea501c10515194000d10980d010486003060501c102d8145142c4680900060f2003da00800c01c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 455002365 1250 455001115 455001181
    0x1e0409020d0b120703170408030a0e240d110702030f0d080a0507120504050f0304170705030d05190525170a210209030706091a0304110d110603 63
    0x80c01c50142c81004410900504d015401c1d030720382d4616074481819900641c2020800098044001d0024181c03480d10b54440c540e41300d44010034480500024010380d16000182031140038042e2600f8159202100310120002d042c0584054444003441100c8020f9814803420002001c0642c1c0015441d02407040c43d0b0f1048040d407242110030040e200c0035268000032401029003a113106642d940409d0b401030041048807124a072008402c0d09583c0160802c11003171400c22104143e20108114103001000700342c1c000c00d100c0030100d1000300640201c100c5e41d5001c071188402e00c0380442c4501e099403140f490094044030f000340021840c1c000e2041c184801c0b102d030751044a40806030703413500d410713034034688c0c900c0e00c1e90000890740908070051104600b544c2c400c807590034402c0c0180ca071070401520340030b0302007900d03144200d905148000c3e10b904d0b00040180712200c410010400001c00e0580d41040700c400c1503e0507144044a89000c1c103025031840380103600040048108030310300d1340d818120640d005104400d100303850 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 455003615 1250 455002365 455002369
    0x1103070605390d02030604060e09071a0c0303010b0a020c030d050910080103050606040f1b020a14010203040201170406090f0b061302030906060f0d0f1112010b10051e0409020d0b 78
    0xe4442d610602102414044102142c40c15002180c3c880c800178400541c4a4407100b02292011041d0f80046071030307101c0310301480811241e8920705e00c020b866403040d50034400100c0b050780e44c920050140032034907a0003140c0ccd0043c85000300100807002070000c003941c0c01800c03030050040158100d14541407180b084071000c07121542c011a40781e0305030398000014261a80c0d80c41d003400060403105440103d49661940000c0340d4504075460750a554020b41d0140c40041c5960410052003850410300c118103074030400c1400b0050780c1003c0d00c010054103510100119a8403410444020b0a0700c440103442e21401c221458100240008402c3c40780504894581c10660340c200c21000704c2c042180c004003964050000314090340323808001242c0c446402801380c0d000b880550b4408050103110741e0115421000c00c10181454606070105441c205c070090000c21503590a400010809504101e04005101700040c1c5048042e400007001c52a48a02412a41da100c0e40ea81095000750f03c41001d04038007034644264076140f4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 455004865 1250 455003615 455003701
    0x15020f07021503041716020d050c0a050a15030f1e0b10020a080304080f162d0f031103040b0c07030209060604030c140301090c090e1507050a1103070605 67
    0x1342e80c2002d6070031190050a0000c11441e486000d0032071002101c98649001691001040c0c0300c0c0ea0710540140c080c0c801c4e143d06000040405030021445800000000d11503031080c8424102d01d10510304d004181d10084403050300082a00002c0718000c280c1009900161503200d0b0011016042c094461a1400741c10340340403030b01d829243c040103003081d0080021070082070300d400c050304000301141070803460050030f8604110780d4003460703c04071100c5040030103011b8050484d030a4a010440e140d600e082c0490850380d2031070440d080500f401018400420301c44008681b003081a600a4448505d1103075441c1220301d5010381d580e0075031000320b20550704a400540d00c0e04005041c0c0d0100c0c3e6000105815090920b012090031034900c0607107079010742d039401015000ca000340124130024050400005504070158513041e06142e05070742c0403010a1b22040c24800290341c000112045e441c4603141c260410b140c445d5903d81948101074004e40342504000a00010402c0a10108501035400425480b0300c0d2243e4051410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 455006115 1250 455004865 455004871
    0x40e0616030b0d06020f190c060c02010513060f0b030f0a050c0a14090c1215044d0304050c03101b0507020f030109060204150801050d030c15020f07021503 68
    0x14401c5250000044080c0c01030141b49040580c0c0301c0c140302e541800b80e00c1c40c84192900b0f20025400c1041d003814050144602551400244024802440d0400715400500b0540c0750042000c4c1d0f4546040c00e4079070f05640240280c58005081d2400304150030308603641e41c0c0c1c0484041ea014050900c40301458076001402e4403c4484588601600e41e80b401d0410a2060008003004540d150401a036281519040c10701031240e285142980042c1700101c003840b0440c5c041109104c038007024030708420a145003610520a188170940f50380d1440404150218194035040c401c0000603801c007205020801c180401d01d606c0c42502641142c4020f00d00ca0741030820355480072288408103d0241541c08520720a10050800d9070019015100d401c004138042404c60b24404c8040c0c901c01e9011405101440e505480030b5810222454040071a5040400084100c204103200a0611080e10400402c00050190b095008031541308210344854100341000540d50250303d00301d00c10f498400380d5400c00104078050300c0c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 455007365 1250 455006115 455006119
    0xf120a020f0105100302061c050c0409050a14061c05061608070c0c0b0d110706050a060b0705100203060f030303040c06090b190f0e03070602070e0c0307022109040e0616030b 76
    0x6080c84c515007e2041c10781c4415501d03a002e07244c0c0400030340c908206020712400380306204c152581c0d95241401c0c01d0110f40c40946041802428032400c400845009007a00390042411541030782d40401041c5640102a240300c4000d04a0107000100240d403440300600390800d500c291111142548c0d0175000300d544140850005100c003280142c05d00a9140000103807852843d17a90380040c0021107980c0c078501c0c6422962040700d401c0d480c0c03020840000103074000c450041ca0148035007070804c1c001d966029140c00d14110300002c403950200c00140955520300c91402e14000140030744e0b075241030034103050700710520f14003a00000c01c1e101c003000a002e50380c1c07030b0880d01e401c7d128154180360040117105c2210010301042e04070042003280d0140754840e0b80c1c24042d980c020103c680040c8031030381c80c0283d003210302d0000420006200310240200283d054001c1038403000c0e050000c3d820044401c0074408402c40c0c2c0112018183c011b8642501030038207000008001c0d0003000303a0042c404404040f0182101543c1c01e0b076034016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 455008615 1250 455007365 455007391
    0xb0108010902030a2619030b10020d0302091c15061e030b1f0f0801110703020304052206060e01120e0705060d09173004140f120a020f0105 61
    0x18001c10313020208008507900703104c041c00241c400714038040030642000c00306c000c036411303981002c000482c0c140c440c450700168140d03644402289001c4c006901d9044030101c020505030002001c2d2143d03507400d428184400104260700346404c440b070524200381c810050303180c4901031402c1000708002d01420300000491001220703a000341401d40d62113041030711000d00600c208011000228075440b1682c808140074004041c440302e2100c0c50040d1560941c2c5e4a000e584008400800030600400c0d80802110b042d548180c94842d21000c0c100c80080441c0303191172401c840680b502102041e82136112a4029002401343e8442806540c00000302c01103680208020010740c0c00354600300f1041c202000034102c5851055030001d44c100c0070303032501c44040003070051744001c800d0f00141c4500d09904030f603c01c03210706085802400c000c410384400507071441c0000e0b20240000c160844a02c5110808208000303c0c00c0141013a00c0180000840300e140a130401c000a03009070060746250f001d0220144113091003048011069 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 455009865 1250 455008615 455008633
    0x32006030c07020f0405040605060a0f0317160c06031509150320030610050102060726040f0602070c14100c110d1209030201030501060e0904031805100503040b010801090203 76
    0x1d1486035006480880c4c000048032542d005503640c620926118600500001c9018605002000343c421500d800440300d01801c07c00900c0820000140e000c400e0400900c01c0e80d8650703240300f00800031210900003c01034941c1c0340011400d1681074000881880306503054803450740d03c850b07898041e141384001403141c114203040c040011a2250400703400c4030012030410401c42d0f0810011030304104085410b40403410841d8820415541e040024035400b103c6442d103080b500d040707510f06000f007802050034900717002500c5021505204102d00400041c0798010001c541c0c1d0450781c0b5002c0704a0000d0711071f0303810b40c0c48851400200750a061019071290000d56695800f500c40c590745604031248189105500201200d88210014040900306401070849032540741d049851403000406450307050300082c00b004014030840740b05840d0007000e2500326906040210130040000b2545840010382c1c0e0010360300c001d40b820000320440d0071a009502460241e007403803c06a0304e40010b035081e51001180250154030000d00d03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 455011115 1250 455009865 455009881
    0x7050a2f040b1311190c020303070f030e040905060a05010f0612020714070636030807020d08030a0207050709060b040b1309060608071205041101230309030403200603 73
    0x1480c1298020500804651507102003c111004100401050100001c0d0020340e5100e0030b00c0c400840c58207103041d1429003810f80c04645c8034014418003d04140c1d40122080800d401650394841a1101a10170840240d4034100959102c134240c078450749040c80e08002042c01003801034030300195070043d15038a5140040001101c002d40c002c1105480354000d090f0301040c02d91003032219070018051560f40c0c0000704220a107662018628211401540785000c00100450445e80002d9003200e0b0840410b0f0388a40442c0080f5890203130031000241400000800c1101640684c0d003d4042503014030200d40d01e80361984041c000f101c281d4040c00f092624184000c000200040b802801c00c124a0f0110050260390349458605a841c150403501c04540c110742041141c0e580700d0780d1001d000f074200d0350912280c1025101c52300030a040c1d81c00d282c1009040c0c04d1103d08002c100f04001680c1030042210b42d500d01d00100c2140d1070790054041140c0c105000703c075546a0414958071100140b0004141500e903071543c85c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 455012365 1250 455011115 455011121
    0xd0b100f021c030912050901080a02031308030402030c10020f07060c1505070225170105070e01030e010e070b0c010e1b010f0c020d030c02190e0a2007050a2f04 70
    0x600301040507114113400000511403130358200c914690343ca400ba22030308070300009002c0090040c10310b811a803060041142d05c69403079001441541d000354600b03a49884600110742443c80207075287d07421480d00304a41c001c0c04d600003401742030180100151207001d0789030081101c50540700c010180003450b0780c0509107101c08065201c1a04588540110390b11a02d05030403c2c0101e03214810b000081da01d02d2081000f81c98200e901c3c021602600f0802040031786400e181c098594101c180541f4105130b560a850083c84c00b00f58445880065404202c4254039039552040c3c07a10780c011003000d09254204546804281000503031024002c1401e500004541703201001101c5640261404c0020807000300303103443c0541c6840300501e070300b035010f0b0b40c48020118950060000b00019070749e44101082c1114400c1003400c2c21101880d03080405403d010403000d45240c0c0001221a01300500c4e11030200024054040210010302c50f009203109403038900034560744080041c0400e810210700c03001c40c04c01c252180d8091030103034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 455013615 1250 455012365 455012413
    0x60f2713020307060e01021c120902060408151f1214070f090c0f0207050109030311030702040e240c03010b360301060e0c160303110d0b100f02 63
    0x44408404540690006843d0400b0355000d400440c205039405000c5590501c0101d0342221002e80c2c1c03903801e142001008000807606440c510f4800d13951040d0380115912038003141e00800f21001150b000f501c04e5858452226802d4407800c0c0031701d01100d04031403c0080c02950034100d500c006030340920b40030680c840140c51800910742001c40d0042000204400381180c0e03611000d04610800010081c5156901a19509582290704150741c84070030204002ea03809107450f4103036039040c43c01d11400c00102e00101e2071070040140007503009050010b481d43c003803000501801c5807400200e1072024a00340481000003150180d8000400e100c04200500101d280c44004001d10162003508095011549803001910703441803003040301700041d8004212061509000c0c0b0809060302009548440c14001c14000c628454003200c00e0000b01d01c6a103002c10305000380d00421640d00314002c0e5650381d1400c0e8015500504034440030b40e00c940054002290f00030300c244013220030100349030010025a04c6410403025004801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 455014865 1250 455013615 455013631
    0xb0c01090609031106130c06140409060303030b0112051b1c050103081c060b090d031103030a0f0522110a0b0d020a092909040603060e06060f27 63
    0x3803910800190152244215681c0283d8481d04007008241805090590103428000c2801800b441d90004c035520642c00d10803940c04c4c0c105410b10819881540c070007802294000e00403070780307000e40c0041415055048130041c04026a504503045440c0021201214402d940e100e1295100000c8100a100b555004050034052400f02039840300c0107833000410340388240c0088800745004a9140306a0205020325031005403a62001e00415080c14582e100c28020401e00d14400c2c0c1c0c0851602c414940541d4503c10390401b400152950380c50302c084014054a222541042442e107801c002400d06041c5c04421040e030600160440d000d090701d5210151402d03000c6a40b03c0d4407403d40ca0317001900e641004024460440207200158448040305000350001c08240e01c1101560402c0000d10007180002107044000144c149146403200040000f080081006400c0285402e20313104240044410006145118030b6045a42c08442c0700c0c00014400003400500340311400c2c0c190b11400e28454040e5112643d880540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 455016115 1250 455014865 455014871
    0x21b120a09140103020f032818170c06010609030302150c090405181f0b0a0501021504050c0901061206050a0b040504051909080c070605030403050d0c121e0506040e03040b0c01 77
    0x186d241455256407095900d0003a4080f000710003142c08040101c5c6c440c0300c2803482020480c0c0114214001440454184c00800140c0300c580c200c0103160313001068901401038035080b2401c941e1202d4015141e50f00718042580036201da43d82c03008046c031060300b00d60310807181400c8086c01c0448020070b0002a1501904070441d01070105525540240c0c1081000007011240200d1340350320b0355030b249078011184941d0149014040301c0a050190b40d07000510550300305400e13603284e1142d5956080c00303030800c075000180d242d02013a0341000280c0341d07901440100c00c2032100c0720104103c690741c004024542d2000d1040320000001401b0410881c030301580020b500c203c9020b0410300441e032444112044039040b000840764500045141410030400f00300c208003810071401e12902d941401e4401514601404841c9101079403a40d0145034028421001c4000d5192130040c00c4c4030980d45480300807903400f014103281d00704038904000030303009241a024116003000c009003d503142c141011144481c03503004c80120000d0f907407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 455017365 1250 455016115 455016127
    0x81f0303020607140f0d0911030f010b0a0807030809061b01090c0905161d03030c031210060302090136080303070311070c060305070203040308030c0403140f061f09021b120a0914010302 81
    0x1000cac80380703600085c3d42c0c1c400001c10342220403c014078490385411110142d806184240f000a1120301119110710301121207540340c004114040c102c05145250110f403e500b498041000c000c0176030076030010f0780d44030384080c05503a13140400e0320b001c000d080140f0400035540d111002e8a60021061466809a015065924156800402914507846404c0307a5001c1b45031202045009103c146210010306150b00e01035140c4148600000c01c1c1c460031300e0709803e036100d1605e001c9a8104981c1449050030a1141800e20000c2e0365041042d00c0742c10464550300824100014030f03000c0e100f52021101c220340c1c01224520440c0c02c100341100100002880c81003944020440480401c4050018512801c010f88817103645509603d4404441c04147c9268100b65100c1200702c0ca2a4902092803a0b00001401041350742c480c0d50321300410444e44a60094100c2d81c800105c407600c1e42c089025000ca804078082c200e4144030b21004081c41c4510440a0130400202907140a00071400c007002001c0c6070340014940941050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 455018615 1250 455017365 455017369
    0x3080402010f020a1704060e0d1a130f050c03011b02060a1104080a080c15190c030204120305040503190b0a05150612091e0d081f0303020607140f0d0911 67
    0x50741c0351700701000541000c0b5040014960003201c5441e54981924010208903980d507550131130042d00c1000001e0b2581c2c1c000055030804030441001441074006940c00030001050411917210b40d94400254060350a000b50314507000107002c004001000c040e13004140d556107140d003090040c00f0044003104034402c02c110000780702c0401c00c441d01d80c3c01d0080b0035032583c1d00c500c001c07080d24041310f04e2401000e01c401c410070403203c518444401148802d003414081486030213180218000e1080f600040704090245429809040c1c2c014081c006841c400d804a85a0026100b400d501d08180038100424404c3d8140c009424500f503a000242c1058003050502403500055000506603009210288140b000c47c004102007c0001c0101048540859403805103048504012544035003856040009120301c00c001300f40a1007007551101e4004070041c841244142d12403030000c1d21031105540c43c400281c2c04000d0024411100000c4841440035040c0f881c1c6494030044030000030f8030071803209448030010090902d2042d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 455019865 1250 455018615 455018633
    0x405041d0604031707020c060316090308030a06230616031806030f0b0a600e01020709050c07060e1e0c060f090607080a02060f070201020703080402010f020a 69
    0x128429207412440410303e03408603114100003480745d000c6500a18a030003185e220300b012640c100034085d4940a06904004041d126816140d000403c0102c0020801070703491060351124080d00c4030b10807601880303401c0650b0007c03101c2c2c00c9140c00346c0c813290412008105024407001900c860344242030406022100080c500a1800942c0c01440441d0301c501c5d001109000c58401d002045004640901c0200d0400c21540041802c0c00d40b04030000c0d10b00c80c0301d00c40301e0982a4a5404c014034100140743c80d01c01e22841802440c1519081e090440c0702e01c07958010050081c0e645401c00501a4010616280752200403c060040640701c0303010203100700a14070105099020b1020011014801442c011411341c00d40000c0054161100515400042e02c3c07101c2c0d03507500c004031407031281c0820000c0d03200c50440740024030a00c07810600038142c4000003180c5511580118840c1e00c182c401d1244000240d4800800783d081c0e11650000800155000001030300660281d129991610001d00c1100c2c00c1d00290f550303c8000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 455021115 1250 455019865 455019871
    0x40806010b131809120f090302240c030d06080303040b16090b0c0a03020c03070308030a0b0102030f040810060f081009170a1716021905122b020408030405041d06 71
    0x85036840e4007004c0b00744480d1a181e6040c6030200d143c9040c0410100c0402082c0051034000203100300000e8032024401c9840c0525804c0c410380c011402555200042002c0f65658028281030000c1420000c0c005603212020003628400d54001c601c2a5595865120030041b00460346481810f0040186010603140e10040c040d00c40c050700c0b8002000e0151150034040d19200c5846040c0c0c1c4603500040040c0002407420b02525008800c0d6103001c1140004100140c3c00c50040c9000039019120100740024280800100c0040480340740703004209a686498060003c840d040c003031985a07511070144005040a070758043d60580e4000c1a8050000100080100141d4021072034207002811440c0f40490700e0744181710040c3c01032401c1d5210b050417001c0380c074081d48900c03808410540c2009000210424410b007402108000c001203c401507485142c030300300070803880b4400418040032104922811445126208403006d0b601004011402e080c40c00c0c04100150996201c1081e174512403910480d5010010888180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 455022365 1250 455021115 455021159
    0x10e1e1014011e1a0d0609060602030d0b1f020703030806010206063105010906180e0607081b0d06180e060a090f050601030303021905070f03050904091407050312040806010b13 77
    0x5a1405403c0400040e501c154018003040c500d484070800040c0d070004101c1c0c0d41c00001728008100a00008000740723b050b041400c0703241c108403002800032220740c0442c40e401600d21a84803e170080d11004012a620141105c0854108441800784044403815040c8040c450b04081c2c0b03181030b404481c52040341501d40c01e920015640342c41c0d1900b48421003200001e400f440c2d950203400c1041418506c05c0e95a106009032414080c07291000c00304c1c406000002c407a23080e002d03c2c881810f640f04450368610300180040c0c0700c0c0e00290f04010300c440e030104900e4081c80b0994860300009004139142c4211200c020244694220343e02072070700301c80d48005003052111a000354060b441c0143c071410440c66215900401140e07041c10490208500d8001400401504003ea41c152a0260700d80d42c5400101340140008080a41400c070700f45a25840301c01c00280610503902c05034199842041c030380f414030303200d80914010b0b103400741c1108006000c20806440600025020103501c507410700e030742d0a1000311034040c40c14031138 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 455023615 1250 455022365 455022367
    0x20c0603070c061b030c0e0102030304080904020708040e0903191b03050901090815010302180c040b03060112090f02131109330d181112010e1e1014011e1a 68
    0x11b1041ea0003407000049010203002540c90740c44c159550540381d1280d1407000e4407840d4041001010300604201ba01c002c0d0052071401202401e041548550380d80101c03e4910304d5441ea02a090490380c480c200a1550f05808169400440065607080c0d499820090116042013840c96000800380f80401c00c0704098140b0308055000d5504500608c0160710001e400300040078800000d002e070300c0715034000311021074800e0040a07489899200048851140c010885114070741403a9070b41061202003c1c40090f801d10846044242c100c030020326400b5560801c0f80c0c091420024400503501b814801540300f0714909018101102c03144007141d0003100c448001d0000d011000200d201e6848984a00c616030030031125081a01d42c1c502c0316542c42c0b01d1504400074076030050148400304035074000d00350007880d0b810a140b419207110b4045c07801e000f81c280a03a1100d11081d80302c0c00c4406043c4812600c00c007280e61044410b500c480781e0825603001c0e8000308041800301c0820094400150010903600040490200302880c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 455024865 1250 455023615 455023631
    0xe0703060f0c0e150c01090c140103141e191104140d110126092104121e050316060b1f0e03011d011407020c0603070c061b03 55
    0x181c001c560080e507151051054002e4807074003698034400c2e550105030425070350640d1145141062409031604400084c0107103600c2001190b03070085182420110704c001ea904001003e001e524040c491032090701c0c60b48881018000e0740d45281903c0c0c00d09030b03112024510f004c0000c0c1114114400b100e031540c00c00420000301090078802d071442812148045c003021240901180350359102c0e082020303608100b41c2c1c10b020307030080c420000c5d044244e001010300c01a003a82603828580500740a031038101551551501c0d81e1080c0e406814600c40c2c005071420759510b802d01c0442044e1a40d40c106050821098071108900d50040d00c10000d64100002c0482e01e400a403500322160b0646407203c1a11400b001c664428405000203580b80d00030380aa04882041601d040520f030b18642010a0051041c0d85003034080d804590300342158488150490f103404000749030418007503910744600301c0c2c8410081d560350b5800281040480d003014450010409101d000344000150400780a0441d44c29492420300352001c60b48032880 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 455026115 1250 455024865 455024891
    0x60f07140f0607090e1f181508120901020307140d0809210f070204050a020901080907061403180a0515100e04140c0603040309051c02011e030e070306 66
    0x5141c6000c40080c00804a034101180083c112100601504400040610020307400e0040c2d02c481c8040720326405220414a9100d0010725201007030b1203181c525060803c8a44162004143c0c1247d08503101c68001e090301480ca0349640460758040c03002141107110a01c42600442c1d94211760140308550070008182c10403041d0000b0b00070180040841e1042c2d000340b08119a10400e242d00c0d60090010556007030313614401c1c1000c2c419240124403029400c1480c0c9000c005500220358018014070400b62640b883c0d540e14841c40c070750f07610381ca4042c1200040448018591002c0c00d28007664000642082c100e071582c1074490280d1a20615a000b521254020152007202c0b075500350300d10f604844d010402002080c2405141d001c20400a000106520420f200c0d240d0307102c4080c40108840b2000500c116607904250800404a2800d40034081c03003075034801010665244c5000c0030301100c03039040c0c541e10b4598502d4180e10160b0740118400005150b100d030f80d650b81c440014810007000d54483c00000400c0c400e2106 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 455027365 1250 455026115 455026123
    0x308131401050a0e0d0309081b042421080a020c01031406150304050f070f0602010b010f090302040b04090606060c05010b0d08040e101a07060e070e060f060f0714 71
    0x340c81414050700304400d8422540c001c40301d041001c004c0d200c148417001e1034134080340c66019550042c0414010301c02408641e031410403403440d10380d000f11824016241500f0a046e50200c01c1180d90b100849030060802111503046005900e010310f5805030079070000c594507410301541c4440d51810041e0007211b441401580c00d8030a072030100000381e4811006e843c0c07000104544038000d40040001d61030100014041080800410b03812082501c244c400196035016480310707101160081d107000d9420503c003d08194802d5142d540010005d43c1c0c0c560000c0d01d15028000180110620746404c41d4680c1d00860100300240600300081c407482d507502c4c0a011031400d2160031112981d02c0d0310307c0703110b590b420302c800729440c401a20240c0314020320300b0810f52244503400d020800705a0109400036440d84010300000d4450000d804c800e80075078001e1003917051a0b40a1a101c035014062008104061400710ba0281001011140d03549003341c54281b901d03000c0300d01c40c61a03800c45241120101c1c03080d24007030101030041c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 455028615 1250 455027365 455027399
    0x91602030403122f071a07080d0605011106070503060f01020a21031d06011e170a02130b03070b0d0b04020334020a080306040605180f0702030711040b030304030813 72
    0x16078001d1405218106a200d54007407244611040b0b4540341030250641410484000c2c42e88500829514270391404811301400d03191084a0229407844c110030400030000c0b5099208900d5a65510310310381d81c1c0c9040211621603000b44d54110b01c01c6150740e400040740c40c0c0d4031007100450415510800c50007000300406070b6540c03840451404d5651010f070a154400019030505483c0400c2d1651460f100c40200d901219907103a01c103200d00c002090000017400c04c0410b8007801d0398020385100c0140040c2c0440c000075600d2440a00d40c05501902c820854006218040d150406801401041d0304c07a410740003030183e81040d585410b00d580c0e1009420064081c07100609808480121744030883d51149c003019484448280d07010307208441c0040099090742d540c1d44071102a250003000c880b9580710006c0d02905200c2c5c00c81e561030748004c1040102d070a560002080c0c4070000c2d80700040c41043d019500a11014092507010507405110a000100014180c84050600341e00d0381030b0403040b41c0340380c0202d000e0244164 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 455029865 1250 455028615 455028677
    0x2d0705070801150305070e040204020c0316110a050f10020106180f06062604020307050d08070b0a060f1a0f0703051c0218220203070203040303091409160203040312 72
    0x10f00420000160017140c1c240c03c03a1200c0c210018243c0e500e0022901a200b44a003c62150100203159584000c220f0070101c0000d00660840b0030803070101c8284029602e042c0038140c1d10900074401160780785000c5036440c940310158800031491a070344048040f1007482d00001da5110315200d98254611103094816640245100e00d003a40221201450540e02c010f80c038504030155074485000101591000c112101c0109406420784282038034906001015800810048904c00d44010214100d0038460150206984441e100c0d100254601043d16081502920000401180a01c18820030030884405001164004c1d1101c5a80d800c0074001060102e01d0041c1020302e0500c107000784501c28800050b1450a0b403400c0e00c2c1c0041041000d84055000400f499280c403006000008025180e5808005401164860b44950038119290170200c04910b03000001540c001200b08001802040d284038659844413040c01134a181584039120185101000700d08440420300c00c1510b19842090003041c98609000303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 455031115 1250 455029865 455029901
    0x604020f03070c0302030c0d0815100801050409020f040c0906090603020c06040305070201021005101409010803030c1e07030f1407020a0b0f0405060409090b06090c2d0705070801 78
    0x440040c10000380005002c2e40104103440d0b05410401d8000c10454030220f0308801103410440d503a2000501611048990007298400080c001200307003024140c5040a200d107072106c000aa0802e003e00004010b103403410ba902007010603404686441c1e5100d80c50704c2d104070f51b5810340d1041c20250040e00351000d55100c0d20405104020181070030714080b5050750442d91520b0204d540311541c2c00100d00d0910034030316401000d0b160209200d84915000403d0303044078000a407002ca510116410000340820074840c1d9081c1e80c2003000003074451030350b48005081108540d0308011841e180180301c0314858101c0d800c1140424002d901c0c0e107180710342010920104840803a0510710f000e07915030101d03003810050303c264010803d000c00e0b0030305a44800c0307041c0d82c040c0401070440d9403640e03500d01c810b202034800214180c44403c01180860761900300b4041e82449401c220384028a03002d40f01c0448516241d100452400b00120703094203840b07105481c0c0003070a400b07000e03000910100c0c0c141442182140d100c03012250741c2c400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 455032365 1250 455031115 455031127
    0x9020903160806160903060f05061003020a021207020a170f1516080a06090207030c020405090106030f240504030305041b05010f03240b1305060301120609022d09060402 74
    0x540000d0150340512200000c40050b006104c00703803061710841d0001820350f81482e8400c2d428641661200344503071001c6132802c80390524100e00f901244910019200140c000e010380040b00340c1103100410055102816004445658840404040507908080c0050b9084814806e510f004104844071400301a01a01907013410f180d51608000540c50b00641d003413004a0000400900340d0781e01510040c20709071401d40d510380c1e0b1468001d10404080c00101d2190b4500400304000e5a0148104006e4951025414038104a580c6039541c2c003460340c41c1d0311a40c04d081120b035a1003c5e683e40c0105030107544a6100803565041519010102a07042c44282003e864280c004003c1680e0001c00c0d004401c056080004000220080c0f2070108100c07100906902250700200184030001140104141803882e503803855041d0719030b020000c282c07100307200e242198002c0c54001c030040380907036210205040c4001c00304079140c40801020f41042d01002420003074480c0a0001400f6414503c0700c003944a00200d4086251072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 455033615 1250 455032365 455032379
    0x9090b06220e13200a18090203010207060506030f011103071b0f030908070801050412030515040509102430060f060605070c0b0a03150902090316 64
    0x10007104600d5415100c40409000c08450010221018102e1011050302910300400c03110b83c03076100c00104a8030b068204a9040485205224001c00c4a00080c030000c941403414411134900c0e140c411a49001964491460005940c2403008043c0b062003640c0200304c0340b421008043c1400300c07280a01c51303141d0410b45c01e0079426414500300c0e58411503034108a8080c4414084101800801c49401031216840341d10320f0041c550000044c004880ca00001c485209803600251800da510903100149401c0b00da44204000324080e404c100c0e400004400b0103058080000006400e6800a880c40707142d64000240c80b29540e9018040c040000000449041101c280413402880411030761054203590704c1a044042c2e84190001c43d8020200000c100500302c4e45114100070340202607400021520505c3d01c003002034101c2c00790301541d600716040b900d003030007262518101058507840360745030030704245d5900c4c003003ca0190507180032400b60060315001030311011001c080c185442c0440d8140700c941010307444204044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 455034865 1250 455033615 455033617
    0x61203090d14070315021b07080715030e03030a140105030d050301121a040c09051b31090b1509030307030c1703090606240d02161a0709090b06 63
    0x11076030101d001c22601112582d203e0408545802c020f00306054405981c54404d0355070041c0c220181481c045401745812192900c1e075032403c0b841840ca030364100210420184205d400b08401d02e02c46414082800401010a00e0555100320f504200440e5140324103007001d00c0c0c0016040c00b41c0020b40013021040000c0c2806052800148035885043d5224a2454104400707120300740c6018180e0012039140303003804c3c50000e01ca501036002c2d011076103140100150003031000580100b200056182c90300c1c6081107072416410a690000900c4180302403d5a500c401c80b00200c8900008008040c3c001400080800c02c0065180042d01c504003080000c0c000d0194658001c0102c460155060918070100681841d00c081c03010404960800411004002c100c681e540205903144035403002c40d100303c0090501101c0c10b28056203580c0611a0070f901b0700111800e04015401030982c1a1103c0c0204030f0301c106690350020350701d810100c030040c0300d4801003408409900482001c0203040040824060350041000ac1202 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 455035971 1106 455034865 455034889
    0x605010f080c091513060b0a090e06041a0108070c150203091c0806010c14060403021c020c010e0f1c0302060114010903020a120302100c0806120309 65
    0x403d01d041050f0511800c0c00e49419a10900100b051003498890a8070302d40c41217954160214002c0c000b0005001010000d0f13865641c900c1c01c2010f01e21264901401c03545c01941001054070300041400045810303c80c00b0b10300700c242139071040740c102c03020754217480050b190800a00300c48150350303425002544541500811119010616039040c210200407040030710008000358003084680d80f0580340841c0f6180100c2541590300c8030030b80300505140c0d054408034090b9100501049520340c400c41441c2080f0b1483c0003905030b0072500310010740601e030f070341512034800c804105840301c55071780d99105e68011040300f114440d040181443c001e541c500e0280206000000c20808204066105017950380c1a01c0c3e015001144c092304c2c10340c0b8407030554280c520460a6004a108039415070318070744141824581160344900340d0341010810300c560480d6034000c0b04c5e566002002980340342e8a5030165014 = true := by decide +kernel

theorem cover : BRFrame.Cov 454856115 455035971 := by
  have h0 := BRFrame.cov_init 454856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 454856115 ≤ n) (h2 : n < 455035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
