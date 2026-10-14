-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2069
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:35:12.297368+00:00
-- url     : https://prove2.me/submissions/81264c40-3882-4da7-897d-5dd9d66b50d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 371942446 ≤ n < 372122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 371943696 1250 371942446 371942471
    0xb0103020d0203150f16050f2b0903021605090408040603091509080306090a060602031b01060902071a01080303070e0609040603021504140603040c120c0911090f1f03 73
    0x324206130f040c0c680a0300034040100d0750580343d004070300568080c0515810b01c421100c04581c980500303002001d4030b0400b0004e120036a00c0c01e0030744003007241c0100041e010400103510f14900300d0300310000640240c0c00c280e014414a12000c2c2ca11000781c04215094a007904080d21400518000d82c080c2c40c0a2503681c880c10f0060211280b00b040214000d00801e1210040c03c3c503000385260001d82d04ad0f40155009404515072010070302a84048d920b440c4e00660500b14880c0010b414142036100200c07240d5650240402e100c2401c2c0028152680594803c6450b00850b4804401000059001042d560414800d1001440c0c0c0240180da0504088421585400d45800000c0041c600342e0300c001e40c4401080240180c0c002800c4c058000c48500d1200084881362410522001e80700c01c581c018000755480c4030900c00d004170f0f050361000c3c0ca03009400004000d0b40350400c410440c0c10754800c40c280741601003002d8032a45424080e0312415802620b096241080714038954a201d03040750410010b041d10b480321702801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 371944946 1250 371943696 371943703
    0x412090b0d06080c01031415060415020c1c0305070807021f021b04060e040b1f0303021b04090f0209071b060905010c050c060f06010905030a14190b0103020d0203 71
    0x34010380852265282010503108008085512402035540030301680d003441907009119408060b1510715100d140d40d91408a4814480c01c4c060145520190a00c800300e50081d43c4da424855000841e0010100c1da080d5038208940c10704007181e28814440032689160001c0d41c44019100000d602200b02521001030f84001031141c9005034011074007910320290910115800a141a0103884100d16004c8042c170307200c03e20080e200d00d4003800040844c0300000c680002d500b6030505030300550072207000500d480d12151644500c19568016001a405910070001c1e1301483c40100205210031181044680c03031aa64003002d031032910f880648507c14038400141c85900800c20f001082c06203c1d0101f0204202d454001300800030754400356600e61810400da00498041e50883c4e000402000c0108038554881d03200d140404002400181003140d04000028a9103041001c03020551165550864545a0a4001d4607000200f048089094040d142c02b07008110610304460550b501034580440e046800e00100b0728 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 371946196 1250 371944946 371944949
    0x909020103020c0105100e01090b090402060f070f050c0306070504151d03070306090c0602010513060e01060e0f180d050d0504020609120703030e0108100e0601020f060c0a030605060f03041209 84
    0x40d401d0004003c0070100091031b10080d038020034a4007c0d140d0700e0b011707004225200c00500075000221100401c0251070010b024004862a541d46a403910134107031344011143d9424981200c80740c0c0000d094103050f15040c06026408440c52421301d08103850071000b01d050000615000d814000e000b82c3e481c3d00c00d031608690444031040581160b444a03034031310b40b0f9001007280c403600740c881010002c001b140080c4103000303031401203a800c00c400d900384074580c0f40c0c00003d1441e0707010625190b5031400c0000d40040c2180030603115510000c40d0950714a48141f21803c60482e08103201d501f074014001e403061094000027035035821945182c00086c0d17603449101003040c03481080c0c80943d120264060b4844092000210b803c1070300d20954414460840d540019903001000b61900c040c421401403042c0403414240300c006d0760040051044482c1922003892035070400c0801d660304890b0410000f5007449698040c01503030004d040c2aa406880c203151110700101600025100403d00301c48185034505051180c1b69410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 371947446 1250 371946196 371946217
    0xb07020a0b130f0902091018120b04030f09053111041a1c0207061404110406080c090a110c0708010506090609060d030e0102240f090a0507090902010302 67
    0x42da20020407940c4030400e00030388920458582c907400e011600491030f0003520940203000d861141001d14052007134504045503807142040025940000900c0560381030440d81c2d10303006520864050625060042c144491441a8000d01882c502c081081d91504507100c091001010403400e04080f1464403c420310783c0500404102d541025901c038004100f40e0000e2040311080c00c404503002114444507019409201404050020a0202c00c540704805800524030680304101c0002c1c55804030442c0701443d81c09585c20707140c2c81c14403920700c81c00c0e0510f4400d0748003a001070b4008041000032040003895040006120103403050302c4001140c400d4400380d051300c0600c1c4040094582094a4509080c020201101c0107807140c110100840e0090802641403400791002410000914085d5102551080740004038541148189420700204200c0001007005100d805903021209080107070114005c42e038003420401742038112000c0c400000f0f800090110450340441d0010458034114001038000380518401076 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 371948696 1250 371947446 371947469
    0x402010e0303210f010e010b2b090303150605040308072a0b031501080108150c04050604030b010314010b030706030b06070609080316020d210b1503190c090b07020a 72
    0x352400740580310320510901138101001490b0782d0b210300c070f240256001e00c64144003034410408030000114002510b012041100c120540d204008a04482203510714041a00041c1d9034401485000340480710240c001c4c0007d180003814141035031581607049c40b03000740080001c003507680c03034003103043c0e0503400c022038260010100c4070380650b20a41c90200707074002c039445010b2105258070011298003411409058890380d07401001301c4018445c81030341160000d0040c80043c0000c0c40300003041e540c1c0f0300040000e18841e40380f007209545503291011401404c0da02001d01641800713940505034400081c900300f2214203113004070b9164540720114180b8403900c5c0007e0710f4641000e0195060040740c40c0103501852401000e8424028030f048103d0715010fa003140f16001508d50040c1105039182030280741c0c0a00825903000900d1480100015180c4400c1c40d2031030842d580100400c41640c9a0780a208400d9088034020700041020000c01080c41107140105500b0701c00105181c0150b48036281280003410007120307103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 371949946 1250 371948696 371948737
    0x7051e0a1205101a0d060f1d0709020f03040221030304060204031208070203030a0b040b190302011205130b0403110a030e190f0501080c0c030f1b060f0402010e0303 72
    0x1640e038454165442600e081c410500d1022a4190740c1c822030000690601d03c4c801401022405c0020950b01c0342c1041c0c50803a1500200c0c10085480e1041c0c81514402580c035071044c0b20010078641c1040050b50110f81e40e140b051003d221589942403c0f40d40c803d03030454002c000113601d0745c0d442c0b24a0f510b50241d40300e240b1011041100300540ca50040042e603014615550f84110590001c80348180103c40402c010307041400418a01c80740c0b034004008945000300003041407042038004c689403984a442d894201c035440c80c0204159600305901022980107083d09111a203003c030a2040a59007650000f132a8407250000a0107152141c0c00000081241e007040c2c42c03c5107440d0a0080201d595040d40c1d612039240c00380040703592001260380c9411038170022510601c0c03904e071000545440070020708002c000f010030820b6040580090004000301c55034400e1441d26491800480100075914440c1c00689038400010b000b81307000c101010380e81c0942d091034110555000c1c0c0011178154040d50710000500e104c3c5142 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 371951196 1250 371949946 371949959
    0x306010915030807030c2d02120a0212010507030c090609050d020d08070b04120302090d0b1b1209011514040f0204050301061706060f011e03271703060307051e0a 71
    0x44845c06c0e1070143c0c0c4082884442140600145422848800c0c0c1074544102c1c0b0000600348100252401c4005a040e284005566000f0071030b00e841015a03034565955500070441c00b2f54062084045c04540c0d0700e0000c040c1303030600001401100d4240030b424801c0401040403c1190b4864505c001c059030700a54458448000d85460244030b10f0648080703c041c03201100b86242c16100344240e80c1c10300c5000342001084403068030359400d10103000e00350190300541365007000005281305009004043d0000754a40b02c0740f410f04405402c44070110024000b116451404006031807003008148550b0004680020300c5850b414003040082c440d07030b0b0010307405508000c80020300c88444c46000c03040307480003802d81c1c0d81d603603460041141d81c4000006840c040f030b8108213488407241c45034000b9031499065040004046910b8690070507018a43c550031001d030320409442d80c040008031081c48801d40210300010741141450f000090304d13100d02d401094001c450179130b0740300c180d2038203d10700c10003140b006403818255503190755 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 371952446 1250 371951196 371951207
    0xc15030c2a01050906070905061b01090803010e0c1318060f1403060c0f040b1602090f090c011119021f0206040c1502060106030b04090506090c031605030601091503080703 75
    0x4401c6101c5518050014070410400300d100e6204021943e258901c0c01d0610f410000c107a0849180e01060b080180000e4003140002d100303120540d4000c3da0901e80380d6140c803640c0c2c1c01c4450b00a0822220210030301a825448441019100c290b62510b00a15004c1003440b030203400400840d44410098200c11000188424800e000d40003000001d0f025a085a9145c1c0c141840c18440c81c040710903850003c120410184201c00301620040c40c0b1070012181490154002605814040e113009860b10a843d003400342c140c1080200c0100001e080c204940c10315825800715444011510513640340da50799054a00c119501e07601c1290b03810480720614400c4081080340250382e244110b40c22140d202d556240841c800343d50034103e050f40611a401010141e007001c1d0101c019041d0003084c180c2041c2c03207010042c00035200388082d0b8403480c00f0200070000e141c2445d08052401801915090407149515403d0106e6180440c020341915110500464070320320000101d209802503901c00360042901060710420154040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 371953696 1250 371952446 371952517
    0x18020a020309061b1c090e06100e010210020c06010e060d0209041113050a06050901120503041503394514040f02160b040c1a030405010e0c15030c 64
    0x594031010107a440d2004d0803100b60041d40c10fa03522244408014009c20f1044685010801041c41a0303413280d04400048010b07a0045880380ea5150002c800510084068420b080d500040840f51000d1a95590b00805d81c0d240d0701400141c90640e21848040c1c0940703403990041005121080c082149141c42c502c0403004000da406071500c5901c14500001e0442d11240d0b2010f18290007802541c80c040c5802513030710344d440c580082c500030b1645440004210419103200e0251380c41c11a10814010058000b10303100c550480514042409009840010042440f04845941307601c0410034044a0803030425800d03092a03d543c0d801b0712261180c40101d000200c011581740b00315400d4809010f802141e0000c90164003940d00a81e4614011b84202004100000341c0c90341c0250142041e0020103031980c40c0088440543d01007080c010200006106c2040310912a600b0700c1240607014102182444000810702c200151405005150220102c2d2101c10035400b200e1078608511142c4440b010510341c00300c02e81d02207 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 371954946 1250 371953696 371953753
    0x4060b011e05030603190302071401121a1005040819080c0601030c06020708030711061803070b090109120201020703021e0d030c14060705160302010e03031018020a020309061b 77
    0x30300d000c5a80c00c02c002206c0d21290307075064003e028001c1c201800510f036542d847c040c0504100890401400049403480340c9800703450001c1d0240c0c0581c258209004959060f0302c102001c21100b0031080004039400b0070144103020300c00c6070703800710001c460070b000c4040d01544d40c801d0b2580c01698000000c12520410000032600711303409032032410755104551500c074060900060115242148540a6032078101c00600583c1c40301441c03040c20b0740d41c0c400071a2800502c0d4021030700d0f0b0301002840701980d40c0c014021200801c2c08161301c01d8160000e500003074503880144030081c05060f0900200b103880340c0400800303902080c0984038501e4018141001401000c2c200d42c2540c071400c15400c002a800c4010030094881c0c20207840d90f600e40410b50084418003a003c0c202501107568800300c20b411144203000642c06000440510280316040407410070b00d41e4001c40e48940424810040e0300c61454020040c0d500480301120526144c0c54000d01203544540d40c0040c01c0441e0044aa0100c2e05030803810000c0c111014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 371956196 1250 371954946 371954953
    0x1f0506030f010209010903030323070809190f0201031808070501020307170402100f031e0c0e0315071b120309060b01030b010503010b07051e070303032304060b011e05030603 76
    0x203070700c40e81c10b00300e01c0340704c88030fa0002d0300704017040c00803e0007030300400c0720003038440f40300120030b0b4180f411994818800d036100400224410184515441d04000181d00c1c200300d00c42900c0c0f900c030507070350b000d441400e03015000707041c59194540d01000300c0c500c509881490f9001031006a9034141850400e000b5802160120082510ba604024440f251560070620035a4040e04004800c015024240c41e0900420104400c15072104c03d010f103c0340340340c0e80c0d10100004590002c14500c1400402074000c60781450035034060f5104405840c462411110030070303000802c1e41000c450848085604100e1390802c180041d1000b542084c118405550544c001c2043c140160303410401080c56100440660b02d01c1c03210705000410910040c007400b101c0e00020185180302d42c007100e0342c920a4211340c551121084140740e03180c0d00610070400c14075806010f48001c0c01e110000c0c03024403080c100c66802141001400180c541c1d941c1d0780c00411240d010701101c141c40408031b50b04c01941101039000400703c0e442128114020300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 371957446 1250 371956196 371956213
    0x907031b18050405030d200c01091a04050d0e01030212010e0a06152a05060408030f0a02030f0103030e15041e080d020312070e091006020d0c050c121f050603 69
    0x5072841000d000b19880b101030340c07512000b604140060102c1c0804005655075511108003000c003907400030402e01d04120300101d501d9191742032581c9070000c03000b90300001d90b00300010440003840100302103842c01403609101052810000040f4000d0180803640005181d2200012505203010310180784501e100361024407500d611660081d800c090061001d1010fe080d91000c429280070404100d2140d060100a050fa01c48042d00d81c0d0b0301d0140281c40c141c4d000303003002081c840e51500f03141a86a02a40100e41585103044c039000c90f1800410510014041205d411244080c0b681c0e44807034003c03a06000200303207450f149c407901d4a41c0108810709800070440410400043d01e00404101d104802016801442c01c01241c0422020450001407018040040081c4035003090b03601d400c000d0b40140ca403940d00c1c003d0f41d800d0040192030074450001400c280003010144200240e070009102d803030000141d40141d5800c3c05001036914010a0544004488084503a807034484090383d4005442f41500710122403161 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 371958696 1250 371957446 371957489
    0x2040603020301080105090f031801110709060501170603070b0a0201022109100b030304030305090a121505150f10090b030108010c02010501120314030c04050306070e15090112050907031b 82
    0x640c07088400780823940092210038021221a01034a06502e8181000103515952280941c00c22001d500240c030501eaa03034000303100e0741d6800001d5040e08140100e0060712410450002680d41c601c80c4505004c3c8100000c582403032601c00e4042d66030400c0801070a074424501d1040d4012a91421a0003020601c1803a162003400c845501854511010140c0614501411503c044500c2c0d40002c840682100d8011000a02c6c003d01c507049040b050701038002606404010038961041d102c0c003802c003210000c80446e00c00642c3e0745000c158540c1c918100c40000012a102009861110240e809188034041c08000058000703019000044900304070b034000c1206030780b03540098144014403100034000943c1e4a841d62804518100110340103001d0007079242c2800c0c1e0385c43c0024a0103501701c0e140800242c1090380792110303052403103c000c41d102e01004510b040c00c1550000801000d118400f000f001c0b40c0f620007103010039100b88940009542c20444114012105140f04080a00548108160001c00380c2174a442c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 371959946 1250 371958696 371958703
    0x807110307030905060a05090d0803010914090322081504020a060206011505071e0812010b251b0305031801050418090507091a01030e0c012a060204060302030108010509 74
    0x65640b40e00c0d1981040c3c1480c003030003120742103840c545050200c20000d00200e40c0e03174054140c0b800d510480301642c2c0d941c1010580700c1505c1c580c24100c221400602e0134000610f00c003005441d00c100c2103003492110901d046940030858541503200d2409406401c800300050320300500e105109a00944903000c00e42c2d51a0b4049031b8a400034071508928908008144400620400c010701000740540000242c1c4400c00c00444000c00c1d18140440f00b0000016440e541d600314a101c480c01030014810041c01c00e8071030031000310490303a0880607050000000c0d800390704104c0c14070f80300c0c14001400c0600800403074403460181d540e50320070510810b03100d0410b004000e1961141007243c099800e0345208088000c2c109210001030005000d0407600c9007d01d03a00400e41c103040e4481c0c003000c1c2054560402c507242c15000007404407021180fa40c44660080c1d445c0c140d950760080c0924003140d46143e03054203901f415030203103a81c2550032072000301014000100002d01690507006507040e20700d084020081911002e04d00c3c1d0b40e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 371961196 1250 371959946 371959957
    0x21020115050919090b011212030501180905011e050f0a18140f0105090d090906031e03091502010b010906020f0615040906090f170c030f1605030a08071103 68
    0xb4050300d104000742001a10042c81059001084004581c0600e00c0e9104581c003d404d8101040003880c2d4030702001070103447c440844104c5900d08081009504005040c00d0215411900c80102500c0b000340c80c081200961091a0001f011114402404100da6003403000d004103403008626000c40c14042080302e24140f01d070300601000d020001800c14459540c0c28086008401c4419181c0100c503048061141c083c05814406c03000840030b070141c0b4400c80c101400a8849401c1486403c0c0342010a00014503400300e6540303610001302e5000c0090b000744c50121003c1c04030f900903811401031740c02403401a680540003010968426200c2181e500e4070340108a960f444070310707034480040e40110003040c842e09841c14489603030100504003040140454031130201351028030200302c0380c02c40c10824607028014051986011005d50741443d9103015400f40d40c455a900035a941d0028105000907845001807440044c0c5a51035071040a50761501409034001c0c100400c00c070303500004580c121424682c0c0d01c1004c0704440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 371962446 1250 371961196 371961199
    0x60c0307020d150903020a0203011b0c1e0f0b041e03050702010f2015010618140a0f1401020105220308040c03060603052104050607020910032102011505 67
    0x103052903415001c20140e0228800c0c10707107188603024a8016544024007508000e44e00a030001c14510115205040c212880c50410270b000985215810003907a501041d10040160800540c64050000f80c1012a080905000041c40d0100b000c18500410402c0400544124005d224104200340401140c000006e030156004001800c10060030005600800070340490314002e00e4030814200752640d5002d441e42134149120b03440e6110189041000d4410400140500103600d010511804c12811242902010b8002c1c44031100300317400d0301050390302d4000200c402006081c91605440359909150911040c4055400b0700650908001906c90900c00200e0b480c01d2a84504a00d0040c0c0c858400704c07500c9d00041d1084904006004c0e0010105c0d01074001d11025601400180409811500201007480052102007a942c01c06020411140c0d0740c0f14103907920150107440300c401c5550707500b500c01c0000880360001401c018100b40c00c40c2c10700d040071075000100084ca80007080841101c01c50710000804a04c01d55 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 371963696 1250 371962446 371962453
    0x1202060c07061a03031b010b040e120a12020a0531050d03200303010627170a0c0f0501140909010b09011218151418031b0c0906060c 58
    0x900010843c1d031140c10390200700541040300440e6080005d00315448152410f007089040b20341031280880c01c2c45901d070055070031070f410840788070001d000c5138482503981141c0c071000c1008540301d0300960040502c161007000d00b1908641d40c6914003005419904598800100149000b00fa25084240010082d20a00e041c003103511485203807000b0010058103201342201000ba103040002490766416403020400c441b0b60000c0c5442e9810004024841c550501c0078034001c1000319a4111040fa20810039001d030b85e000e000c1030010314291584a0710340407210000901c91038260070005501c0c20701128140564100341d03907000084900140708416809100001396000502e0341c01002264640c00045c0f04c0801d0604104208006040505045450104480c2c00c4540211408000c1007030355592481e4000f1451020072410701403a10b10020494001c14070260a00500c0300c0801c021410001d81d4040803883c1c80001d05480304c04901500c0d824003401c0340d406521b4000125000380b40c01401d0700c0090107000000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 371964946 1250 371963696 371963707
    0x2212031b1e050405030a0b0a0b0d08090d030c050d0f020601120213050603070e0a1401060f1d030f0d110105060103061d060a0504020706050f07020601141512070c1202060c 75
    0x280e0481c0304610051080c08000c00c0001000e860500410010314041e0b8101d90261500c00c5d00b4000742c41d454011984a9858030b5050070000f884130050340c20b10001a111444407140516050b20502503484014003640302e80c2d4000d4001c5c03540b08007201c220301d045609480c016640c0f1003842c54034080320000250300c52121880c810211010383e000a0f4000401000c943c015640d443c7d0000c0c01040c00d4a2000d54070740c8881c9045104000c0842c600e004000510301080302c4d50554070002e008051100070b05040d030300c810b6000c4174260b0701045480200d40707070302040e52410440c071078003d4895811a0300721401c42d402c0000080f42580688541c804450b498010b1403003804201c100c03d0b01c071100c01001d20f5402074010001140f10f4851348040d25106109160002d15420010f1101c80e01c088000c8c034503800c6500c03e02c01401203940b1104000703514401a90040411440703da00c4682c0382c065005640f010700c141c54200300300303160300010a42c5a940503000710713040040c0c41d0302c04984038001101c800011410130842c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 371966196 1250 371964946 371964977
    0x20703060908041707080d0203090901140a0b0d32070809010f09030c02010e2e03110a080103150501150c06021204050102130b0304020a0302092212031b 67
    0x601c40302881120001e01e800c1e01c802600c05011409141240a076000200c1485000400c00c140c405000c01f50008505081d008000a0910340050064045600c0c07882d4a1503c1501d980c1b1170760010388010b0002c162560300f1003105070002c1107940412820150341c0345442c445c050a48003802c4100403c0003812009070750f29001030307800c2040901100040e41d61824502101c002c0c500c07951240c64417955a03c001000f8a000042c501010724690f6481111a00079503055008810b10f50344035500c902d00740460304080d00d41c06900400c4100002224001e00003804000241d0260480381680e01c661070b080d0702c21140340c040b84100e032000d0096440072118041030b13081e091701985042e201c50380b1404000d443e003141012001240f20b0255000c49640e9000708038454a140300900c400084c201c0c4980d82400c601c2d05800150120743c0501c8040d02403039040010500c1d00c05105401800c2d10343c100d1102d031a805461401d4401080382d00020b40c0000d14150502d000080102c0c0e036000341c13664540e9007094000c2100c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 371967446 1250 371966196 371966201
    0xd0e060d0c02120a03060e0c03100303030c03181103010c02030f03010909080408011b03050a0e0a0b0705090a0303120507050306030a1211070f091a060409020708040906090b03150702070306 83
    0x7050551140c10500c1030940c00c010018081c808882e6408207040745081c956140902c0081c0800b4600b200920812114514400138070301120b4140c42d0200d41c518041d50240c0c014101ca00e5291048542400004280a40459195100039041d0300800003889404c00482e181c4c081d48801d03c80e004402c00c0108020407007500f202120b64010481645040c3d41d03608528215020081d0b6035006c003401d0300700c070b2a846403d07201c2c060b44002590320a001240802c0c600b242c03030301e04c0807000800200c000740118800901c200262544c050b8054102015140c403820040d204440c50404644490705150000f46800d205071305503400b074100038000300f900700303030540d80c03001c019001c0f128000412480002051400304208500c4004004805080040f07030b00340480c0c541903c42516924174510318440c0001c6071038903142c00b11404c4800d01c000050701c03201c140c0741c01c2c82d042c45254002a080c1c0d06254000c00c40d0506507025400781d042c2201142c400114a104005014108580703800241c0c002000030404241c02d40c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 371968696 1250 371967446 371967461
    0x20718020f0f131701050601020f0729090a0f03050705191809020405011e05061e0c0106030503070b010513140109020901090504050106080906151c0203010e011d0d0e060d 75
    0x40b12550291246076030b030410360740350100131143c2e9102c070240401540c040c095910f4a801b504081e00c0784600780024140d8040300050451010700403000041c0d5503449460544000c3c1100401c08032400d0fa4500790301008002d9400141d403140240180001d6074600b0028100d03034241c901c11111025807800c200561000f64000c0c0c411131003903c1c2c40c02400145d075180302d40b501034882c04582c0c10700d5480c5d040d41f194541e12550000c50249000300400c002034070000107011440d100300000a0350b61060040300b035014003500d60006103544008696082042074180b07070981603620a680c01d03554400c9034103a1707200f55881440b00c14032070300c1d91100600c030114440d00203240151041c1043c181990351440400d003241c200364040c40c00900890b00344001d0040600072a50402c94444a1900c070442078000602d03106d00221311030000601d00c0b812501113450a4100852125114008010a426441401c0d1200c50124110f20490003880b0401c007405004400c0c3c20355801c0f0181845091912024500005002c6d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 371969946 1250 371968696 371968717
    0x70215150f012714040212010509130609061407020a030e04050604062301020607021501061803140c13090c09052505120a061d0a0209030d020718020f0f 67
    0x1210352034100c0d40c00d1860004440460012040390082c030380701002c08900c1c0030302138040c030440c010821a01740003c1d690450b8151241119080b0301d03500d5003007003107a00303100f4800300800c000d050528441c280312096104007020010b0221200e010340d40c111040381c035410f81240c002c0200d900e41035035900904140c0e0120341c0c0550f015100042403510340c810701040c2d40c075808400c14500e211140603942540d041c00340c160401e1050000b00000c1d0401588031f03142c10014014001044000141c031030100b4400700031400256003041280d00030a0403a400d0355203e0340b07003000b4940560103699114150035040d1050401054000b2030303442000303040081c0000580300c05840400c80c07400c03103a5803030b060b00b1900c88401e002000c1926140d6640c10702402ca0f000400c0700420040b00306241040401a511400c0000d1003c0440c1d045c420b90640d440d507031024000e002d0002282e80522404d8191130700c00d0b0f0005008016a806260342c0421403012019820691142480450310101c080c00700c501107002260280c4101c030034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 371971196 1250 371969946 371969957
    0xa0c030f020c0a110409050703060b03010b06220509070909020f071b0608090c0a0902070c030c1715010f170111030f0412440a05070215150f01 63
    0x21a60a40c241c1e00048010141500043c80c550200088034111405842c02a50305010700b0850340c0301c150316000180300142160343c5a0b043d24003556420750005c2c41c420701c0104010b49503800c0c2d078518030802a0042109443c910444800b02d031500c0c08000d00e40c8200c40c10340e22040340780d0619000c080650042100b0061051003480b1100000b80312080090f0b92158152a00e40d00b5450720760000c05d100d00c007500d000c0294115801401081e11000c84010a9500c0c100000d80c3c0c442e01e80ca0070704074810782da0f40050304100c01504003003400310804000c030403041c00b80e03000c0340c1e4224481e60314050350503000c1c0b04e1600b0412504804000c0c0e080140707200c903584044c0500009960404000c03490095004540c410141c220a904000c1005035461606900c807200341b4041030710702c4041e0b84034041d07400d41051550003c48410504440c2002000030800c0c106942e11108850741400f0309500d000d031a01f640c58902601078141035805003d10461540e110f007841c405a5284031680c2c40c01d00c51a407809002c440c2c104807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 371972446 1250 371971196 371971211
    0x61e2407080307170c070512093f07080705090c0403050f060105120a03090501050c070302300616261003021002070b07060216020909010e0c0105070302060a0c03 71
    0x40400c4041d43c480d0400c0d8461915040320b002e1038903200c1800030f20f082000c81d010310508012800001d203508a5600340c030401e60b502c02c1c83c040000d0344400c40c605c8440712071080c42c0501c017a1007000d00400100f58041441c85102d40240007101d602c0f0415402070340307a00d60084604007ca032504040d81600b10782c000c0901c078070307107520303600c4050034092550341c0044076500c02e4004101d41c2c1071408034130100401c183c0c05400c80d094166401000d1640c544140c0c6d04002c0007140985a0f25014000d000003142c0c020012140e002c42244d01400040142c00c1049040403609a00c00b588000850910300c0351070381d038244501c3d00301da6090a403a040c2030091000001c1b880080303542c07000a0000e400e10701540500890b008100d2441c4100881094001030300030440d007255004012405045058a80c515408500036841c0c41e8030368001005e411940c5400381d88458035401f4480241819400088044203a8040d61459a004070055600740f0070100f0040050344114006180515140e100c0742031100356107000b0412a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 371973696 1250 371972446 371972453
    0xa1a03100903120c05090f011101020a0314010806100b0f04030209180f01020c0c0d0203210301031407050f01051605030307090e0901050c0f03070323061e2407 70
    0x400c861000e515a59a00c00c801c05068200300c00450308030320000140300000a410303006045000d00325185020340c01004924260b43e002d116010b01c3c0d041020001c54841204042c0200a4a4070920b44400846407034000318042101207100e6202e02c128801c0100c03094a00108002039601580c403000c1e072850280000300050391404451401031f802807240c140714416031142d50303080418000d60310803e6841000389003a070803004109805030340421241402e02c15005e0010074244440c49564500354030590b003c4d010302003001b40265040e03e00450b60b107032402c49030808460340c0c0e81c0c075801016031005002100304925840380005011071004151040550b64a503a078030b504d075400a544501c04500325035002c0c0040c917900b0728401d07808008100244054200300000d0015032003404550985d01c40c0010020382d00b10300030740010301d007814000880e00780940e6031000014600070a0311038521908007000d5240c00244046000410b0034000ad200c5201d621006c0320031050001c481c502e88196a005002e1980403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 371974946 1250 371973696 371973703
    0x20d0303022b0b1206190e030f0307090b03011a0f12090309030c0301050105090703200a090608010503010c090509100b160302070f0b040e0712020712030b0111060a1a03 74
    0x100b50010440c07080e00c03003a10805000c1d1840f1003201e60180c2c0d0b4480c812004214001031840d00031184d2854001000d0440c00000007400600395007001c1c03880001070751548001c2c0c1e00002c1d4401c00582d80c2d507031070a41c1c072812030740c4591000b031043c1c00510110031040c0085003941402004205103d01c061450000c1403280b0300f14107141218840e01da078101194407402c070300b07060040ca0000740c0100e000b000300b503060900144400d800504000109682d072201840c0f1340b070351000166144403401c0070b01512400e000c0f1000300b203c2040c3c011100040c1040c0300001e04d0b8201405519980b994503207841f400541032105004540900400d02c0030003507402c500006400c003031a40109108020201c030400c11500a0038041d00e0200386078441118900c01510411803a03160340159270603954000241d2803142c0359090200d4103800040202402184001030410400500001492405086450501c08200b040c1d00640700d2200c0001d00050b03035000040001c40c0d20249911012a5441c8115080044000d12000c28076 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 371976196 1250 371974946 371974987
    0x30605090f0f061921050f060105151204020f03010b060d140906010810051509070305090709020a090603090c1d01081504110108060a1a04050405180307020d030302 72
    0x9001202400e10890042c0d200c0041e40c01002a50030708115a1500081c0814000c0c5101d540d48120f1110500d16010040f60040681c50750004102d51800803607401071030f1194000e00c980342c0308041c02c5401500104001e80ad40301c1c6103191359081e07270465a49400b88020080304040d907035459540d812040446a45100c040c1550ac20441d40c0060716100c0c960300f140c2201c0b406005102d440d84024010410380c100000c5803101420002c0001c40c1c60348490b00d0003080782e0030760307884e8a5110300f508080041e0103506610041c800e5200c00100c2e0202a500d000200403441078804107000203c5001c414000035010741c00c41b0b15040d12032012226840d03600c40c1d0071541c4e14541a2a540c460070800d00420108004100c4210315100160308d01c6201d0606690f4100c040c600d07480c80d00e040c018181d00003a400d6880305035207801005c02100e200b00141c01010f0f94449a407041c001d8922031850070000c6400b1000c0c1503420b5810780c0d4500c000b1454425507800f0814400002031003101050340801200c4c1340d0b002485030180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 371977446 1250 371976196 371976211
    0x6131a0c0c090906010b070609050703080a02010506180115050c0106030305041509470d11122e09020406030c0e130e0102070605040f0b160504060e0103060509 70
    0x5894040c8461214102140c9101e903030320070440b82d4140841590003054450446040b810810340e90b078070624200f009000c20000107013190113601d00000074404514014880b1810302d038000c104554078241040354840300c074107100003102c0044006000511010721404610461401c00303a00f825409a8480d080d264107070400c600144010804100c1441c2c000d030554102d030740310700740b950160b41460882000610144809256605a400f00c00c194541a10001c00c0803003e00c145d04604030300c41c000003901503020780007190880341350080e4900308071441c5040e9584508801610a001d45440420080a0001e81d01c902a549403069141411160303840030400144249000903844030702c6c2c01000750486461051b608140310201034401510350f0703400000e03021550280c03c001a50241c02d2038803802801742c064000c00c000d182006210500584210001426100d4800480141e545244446d10355948482071b40126a0034081802114010700303128002010600d0001140d1340d40b18001040b00030141e034101c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 371978696 1250 371977446 371977499
    0x70608180a29270f030703050a0519080f0610121a030f01150b0705030910030f020f07140c0901060804030c0b010e07020106170d1b020a180b0f0f0613 66
    0xc6a104210b0201c500043d03200c005441103943c0e1001142d180d20800100408101c40015145561030040007500d608191100b0468114001c044000d04100400c0d40c110410281c02000580e0f10b141031525461000c03655550b82d02650b82420070900500700d40520810400001c43d14070701603480c10030405414403401800440c0c44004107000380c00341c1100b40c121240202e400c00540000ca81700000301d40d200c00c01070301d80204603954400101c004000011803008494000903580d8080014040542062801244800411012055480d41d12031818110540000900c0c004000d0140a0142c65501c03034000d08000b98951515980d200d0513031402d810980d01160810f05000c1c440d40d092140f503024184811482c00242c0c510078140c0c0c0d81e1300b00d4041440070440203c0381611404a004920441594040c0c03401030105d032940d03c0c03080f0f880041c1e121640c00d580b400420b040107143c491030f0030417418405031910110255401c00c1c086964401c01565065002501001945034005a100300c41042d024084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 371979946 1250 371978696 371978731
    0x61709030f072f060a0f120e100b0913020904031209060204090c0e09011412010e03030f07081306024504061a2505070608180a29 57
    0xe03401c40140c0382400e9001e581d180d60740c4283c075183c0104642001e8007604101c0d980041004c000c46d2114820030816014908081e200c0c3c00680002030078560680c0701c210240412040c81080c8210004200c60909820030341c01c1302c400140c2840054190440c0c002d142951800784070b182c0d060190352500c54101c40050b4000341c100f110041602c14102c95401c180382c90303621050981e00080c480c0f001801003440b032403032550381241e41d50340340c8411451600500e0300070f2000301e41803581503440e5001100d0741041c0880c18070005040511a1130043d2248281c0100120a40103e45842c0020b4006030344403401c0400c0c1301c418200b154004802c20101b1302a144415503d88245a600003104d014103040c1d6004c0c900b00701e030500c0402070700702006100480210b00e8a44842188041203403050304600f4000c442000f1501c10b0042c4580461043c095407901e884062064450140403082241100345044040c0c0103500340034005080c0c2490309400c0c1821850340d80c036030010200701284190050f1038103a001d1805070034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 371981196 1250 371979946 371979983
    0x17150c0403061a010c12110f01051509091513080c0604021507021f09051302090f0a060c020f0f0a08010203041208040f0b0c0d02121906061709030f07 66
    0x10b0b4004002d01030f5012620748090300c0000e0300c0c280424100910300480718040c904210700c0b801d1103c0a02c226281100c85514500c5c9000d4001c1200351850f80242000e030500b040b2078141810301900502c0c00400412031041c0700200d220504070b024203e25540c2c082d101c251404100302c00d000d003030040c030300d10f01401150800744100140d0724540f20100480b8001404600007594600d804011944800000c2c84c990051105048603145469002143c0c4140441429121041c4030b902801d003120043e11740c0c0005404060030071018019500c1a000095180c000d50001410300c1d488031101168041e10025441c1c0c800000a100c015082c0c00c40307031250b903001c0100010302c035429210000c804c0c500d080c80792260400b600c41d07401c11000362001a00721910340d4007107002000d401d02124100744003440304644030000c50410402c40e00d07054842c43d0140c101c2c508051902400c510906e001c407015a260800004c1d220800e000650400a054003820700003804100c1484d0700040003412000c3c481d40309030507090140390 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 371982446 1250 371981196 371981201
    0x409050d080a0519020c1213061d0607030e3105010e160c1502071101020c1504060f09030b0103033c0311070c06090810020c0717150c040306 62
    0x40c0074030740b40b505002c188a002c492140008490007541c40001d40d440f8035000c4000d1401200c80354240c000280002e20703c4815401e10803440a8480319659100e0110440214001090320209825881141001038400090048800c8408008058207281c41800d104185404e40040e030b000818007490210f944174000d86180c8241405821109804c5600c0e003014a2402c2c5803107120308100301030003009a040000d00021007954003c0d0000c0b68410765480341e40340380c10544901070404060241c032030b00c50000f5041c0b030510f44c40c100310007080b403816060a1038001c044940c0c50b00c460740301081c0034080d040400451040e0745414082c1d8025141c01100d01034840e00b000c803541000308045004c00d40401c0340d10300900301e030308200b800381c003180740114081d0f81503102051544511440188003031104d4600042c001d4219104d10700f00c503d8030707007075515004c0d00d00c4505060f0720a0700c45c2200c00b40c018503028401d06005040c004500202d810032500e0300a1075080d2001c0b04035049c1c03480c00500300c0c042000c004109450 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 371983696 1250 371982446 371982451
    0x50a021906022b030e070f030f020f0405132004050406150506180609060d020c07081e060115140a0305060f04020c0a0b0a02210402120105070912110409050d08 70
    0x4000c0101c0200c030744030710b0080c0b11052035501d002c242c2c580106500c001000c03c820000303400787c0300000e4080c82c0d8130300d07101946226111040303001307802219021805160503c5400c1c440d00b15146c21303401c1002165240902451070f94888048036034020642001625284549849203225000025a00c1c91703080d506403030340310142e000c9803045604100501c070094824040116080080d41c1d09516220f449001900724020030170700c942030510101c0c00000d80000010301804444250044d581c00c010000c03070310034200301c403400414010b600c181c0042103410354182d91503046003020310b00110200344c4684c40408a501981032503002980790805e000547c40c00c140c095031601300c03c132001c40c039000c2c5414496403103c1c240500980b60402c20400545a000160100d50010300322885500008090b4903400040f40070035601a801181001440780700800148103981c0141700c143c032564031651802e641da621011100c0303406c40da90304d02c0100e42d060f107484a0140c0030040c1e2085000d0141022810001071510350700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 371984946 1250 371983696 371983723
    0xf160e090604150e01271a06060412170a09030515010e0703020702130509010f05160503160c020d030c12140406050a0c0c0905010e0a0902061204050a02190602 70
    0x1c5000d100000300074480c0402007455001000c00d2a400e00100d40f0300510f0040350048800c0940c41d4015409100400301807076285c41801c0740704110540401c064107038402100e4140d001030f800c0000740852210810b10fa29554491200c010407440c529140012580201400d080070a030341c0e200600c1002400c0c8840300b0300c0f11042e0f000b15565850150a00d42500004c3d0107041410360004600c2c041d0f480c0c2080d041c4004c00b2419041c81036007010100f85009107000c1e030206041c030f4904000b04030b1500d800c944817074140085a403010705588903007008802d010300861030f08080c0111842d800005844031890211450b010351143d0360029035900309403880101030101441001300c604400c0341c103007202406490a6520340d203041b41c3c590b90308003000d60708448030903070103810004450300c0083c9146182e00210705880d40244600e40545401403c4020745101d0303076000b944071100340003890040200c2c21030141d20600410840b00304001503004182c0b504103042d00110000c07140704007400440c3c0c04001c82c0c0c040301e66 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 371986196 1250 371984946 371984953
    0x41401080f030c19031b08030603010c03090b040605060a08101b0c030207261c02010c0206010315110403020907080603061e0a15080303160315120609050f160e09 71
    0x200c0000135151141c80042c2640321000009141c01e1601c1020314910b40298200400c0d440400707414461919001290703028425801c0041030b014980c0309029003213890b80c0c400c225403c1c9894503601c03840607040003080c0c00c0e000310350310b40001884081081004410002d030b40740024240401080c402c506100c5078082000d0203507100c1c410000a130b00007244400c0300d45100c028a42042d84000720280502510b48000b050721914048031800940b40b841c88406000c250002c2101d801d6864040c7d0b15103009200103030084000d50740340100c003400342e000720720800c500c200361174907003500ea60000761a903400703460120009070103108000050404000d0681c0000710084220589015081c480d04500313001404807140503207819012a00d642c41800d034101402c1c03900d003980d890303151444c107112030b1200c10304400c0c0009040c0140f0f8504c9148048060741580c2c02c0e006a400c0742c40c103c1c1c0f102d802400580c41c0480d4207114044500c80c0704681030114902603a0074047d4540c0061402400140c100005409213100c2d41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 371987446 1250 371986196 371986207
    0x60c0504120209150415150f120c02010212010602061503010605060d020d201c02040509040816020901060509090a020405031903170106080f091b040b040b041401080f03 74
    0x104a490304a1526504440c0903006540312856902a0712804c030300c3c0d40d00517007800c0310303850208140e00e961400e403002030f2650a0402d11400c0203c5002c4d0100040340e010510721038400c41301c90495001240d0551f043d000151031b00003000c840700c100340c03400d070311200058000c0003e0100806045002101541c000c400074401e041c01c100000c3d82d03034800c120203004010350008545090740c103150011150103110501001554480e0700e4020101d0380019040501656807441c6802c0404030341c429a000c0d50720140c40c40d0400c1d42c4030b81c0d032082c040e80714020780b848101c44420302d58010303500c1300300e5140a0700c203540d2070b0340e110700c030074010300c0720034100648049480c9005101c1400162800185c04240380c480220f000350003501030500740c50100d1014100005000d12000100d8016041100d46004140c400445202d9540744040700d51200038900075007003020814002c50b00c0914150f001850f071240020000142c1c00f41203000542181e044040d2039007a8013440b40100101c8100340020300403600404061842c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 371988696 1250 371987446 371987459
    0x206090106050307060e221407030c0c02010e03030d05160905091b130f06020102130512100203191a0102011404080f0a0309080d060305060601020a0b010b09240304060c0504 76
    0x201030b540a00c00c00c00007246c6400b0026541c01e1040405032440e04403140c180e500401550700070f031561005000404840c030002c00d40e842d12038481d07030203012419038400015604d20b0b401182c942203c010300607414402441558207000c030318450140140c0981c08080c0e9114260b0030040d00b00322603544170900c10035641c001c00159141d06218480c9440d0102d4940d0750711584117001c101500a903405c011072002205201066064055000308145002540300c144141e030794000700314800d1205ca03800c0c4019000358488404000054000c0c0da0401c002e00039030042030541e2207000045031210078480f8551510b4080100031940c080c801c0806004500300c0c01403043c035298071248554845c08101d6500f510b000105108614401e9104001441e4813034107242c0c0e41d4124668070005844a0702040c3c69074014007001c11842e600029411200c55800908000030340c2c03928200a0203a00044042030700442586e4420300c99046620b003a0101800030401c0d5a00c07800c0c01e0800000311444004013200303010080000b4002c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 371989946 1250 371988696 371988703
    0x2160e010e13150203070306050a050609040509030c0a0803040c14150901030f02030a02030f1501140711060a05070c0806070c14150c0406030509031201030f030c0f060c02060901060503 81
    0x190755101080070040c0d12085a10344008050480181902d690058003452142494000b940540e000e640d00b8000303a070301c80c81040311400151280c0303940002d00300003041c21401c0503002280d000c0d076200e0960782090400100d150500044038411610400b000040100f0012001e28800181071201451104001d550010a0350590340320700040100c034001c222240140c0c482d81040d081c2e4051801c0039900c03424414ad042000e9042903400710030800c1d000c8006000140032100380390106005035500003660801c41c20b6000c6c00d5114610669142202c0c26003107645489200c0241080031560703440f40e03580c5e07005040038081d904058009505d190890018440c1c85a404481100350175001012000024135505107640f804141c001d102400d0401601000944180d04c4044c0085a449480a10440d03a030f00302519220300c075411050004440c2c600040c000f2586c1040c602041e61f00c241003010203501d0b01d03121540003180703030401112220384484007540c24a50610591f80c108401c0c0307009000c59030602e00002c1d20b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 371991196 1250 371989946 371989949
    0x30f07061401030c12210e0f19090b2d0307060c0507092307030b03070906030c0306090c0e090304050a0e16050a1b0c0807061404030221060703050702160e01 69
    0x50141c1c50b403c0d5482403000788541044e50044038003107190407185084024003121241c1f01c05600c6040c8103c1440c2c10b80c103000940240201140f020060660300705003080c030040110b00d08031070f0010240114095a03080d0141c10b8101011040c1a00700b0400000d41094504004c03500801c041201c000c0b4290006200000c1c54820f90307050310000f107801300600c288582044100310034140c01d12094024000c91540503130040d03400c61030540640711066280d0450400343ca40130f100080c2604170382801000800c8207a4402d0540310700c6012a60b45a9942c3d9880b1083e41e60b06645030209034000040c01c01c06403030b145403080004c00082940c0d146078a40401050a071240b00040c0c00240301000400c140002d1188484da03800000d50844401f0841c82e505208003081c01318080c510030352003000d402181940c0210103400720b0780a0b61404902d4903056500740310306914080c94983d81e41c201c0309104e8a100d04140b0455214007000e80c0e00060918090500034584102c074088500f040700c142e001413120203145000c2d0360 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 371992446 1250 371991196 371991209
    0x230709183c031b0c09150e0c0d0612060b0405060906011205060f0613140307030f03050a0e060c010903020105061c02010305060f04020a120b04060b030708060d05030f07061401030c 79
    0x1600309145080c10303035407800c002a41c580d83d200580d41401c20409800100d80965070844000c00c150b0100002c00e0742d4001c0d460080d1a19800c4210006401101d010000c0022410360780000c141c0903501c801e070f1200d90004050490700d440e11221824000d08003481805e034415400c507025145414004000303041100c981103654042901c50000409a481d0083c0c209002e44001e4041581d403202e200b080740000000340154592100001024440c078580095054107880c0c21000d42e440305000c540d01a0343c00c0c1d012814400c280001d2101c110459622075001d4003184260500102c0d2030640751800071b0031030300001c12442c0301e03980c1685060b1038194561083e0718032580c2070078005520b440341d0300004e02c491803041d6031a501600003d01410f0a035130015903046410751120052140518031801c001c180c2e000d60041401d4021700b803002401080c41003039811381104020b004030640300300b01e44443d8290380c0007420080580400144010405c580c40c8225400345c040716003001195411035135614031004203031003480c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 371993696 1250 371992446 371992553
    0x609010c020d050f030702030c0306060109050919052d190e010209040c050a0206090c0102060f0c0d090b150a0308032703030708040c05010c23070918 66
    0x2204648624140810302900401104c00490080070040c0ea40d50140f14102c0c00790042403505c0d2042d00b4001aaa80555416156811242c0c01c00007400000030004024494030150800704d0f043e220f85501c00c55004a55031450781c85000358407061505900140340000c40f401101d40700700000c1c040d9100d04480200c081030310105210600b440c2c02d03806406407903005c641c0300d0310b403031102082d2035000002030050030015025149e81e0b0341c5600c8041d032030b80c02c000c50306400768001c08002400705c40107205103a4441401c4003080d0600015480c91011108401021650f0b40144024000040b450000d420765000d800c542003040c0e1800c50303482c103045e4007016000000701209007180400d0070381c0e42102d52014003c2081265142d1803c107800518081d800d90b000e480780c0c5803404002c5103a502c150401c00c0a2030300b01e4100c1140511706045920172041403204100d00f401581000300d10b003003941c01296459800441038a0120b00c1500b4a1300040c0d4200e07403c0810300300110301c0e540c1b07184d1004d0440c1210b00b4002d801c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 371994946 1250 371993696 371993717
    0xc1e0306121b150c010f02040e0105100e090402122e0209031902032e0516050318030c0d0e130b31020406050c010f060501090b0d1d2a060901 62
    0x301c1043c020510204d400b542801481e9600c2004c55000d0700494284200512050340c0e9103040c0604400b01403000b000060100c042c0440c0760030681c29036904948060050060701c0c0329903200500346500012008072201d040c05910050203011901c01100341940c0404514042042002a50b07950308a0f440d02103083c0c80d9a510010365405000405585900002c0044100b01c200310b00404010a0440c1c416090b19041c0400c07080020840d2000f80081c05841d22171840d00d0340c8456010b2401850045101880204100002a02d040c0030f28241c980c042d441d40315000c02250104032000c2003034910076045c50324060018410342d0b107081c14441a00c805255a1500091251700e0340f00f02c61408400e510392600000e000600c440d030100043c6242c000c20002081200c1c0907103540d806a071881d00c82d15000600c41507043c4000002c42c00200040790718840001400012902c048111a5030800c00100c5600240d581c00f8203000c806030b9521100401d4181c03a15017000031400501c65025000c03050b810000f00c20348 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 371996196 1250 371994946 371994979
    0x1020106060c0b150301020a0210110f180a051003060303021203090a0803090304050a15020d0e0307050f040b04090f0c0807180c030e0a0c21050607080c1e0306121b 72
    0x4e0206400e04003400940d5510b103851006903580c002002003051a604c1c000e10071070440c800905440500b1140c845040c0f0b408090110018428002035069a001c0c00742100040e803a030303460100003d005880e49021428a245040280c1040e41003880c42c14141020810400c080c2c1001c1080c045056018503480d889440d00b22017075146002c1c94000903048490301c00040b40e40c040e2100380401d155015800c8802c50b84502d0422980b038180101035075013552102c5014082d070700e40103501c5185000090400215032500e03074006410340c1ca15400c00d0321039011000c0c00c0014441910510805010210014030300e281c40d15480c19200c080300206e95503d1540c81283c03c0c0050b11030f40025032000015412900c0c17440650814013145141845195a1010710107003013114020f07800000c0c2c01494120029003a5903072803c00a5400a4008246441c02e543c10003c071601d021421108800300d80032451010f403646000028054002080500c0440552009070050311b00f0a6448160810351802d80d010b005c148503c5a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 371997446 1250 371996196 371996221
    0xa0503040c1a03012103020a030509030a0c18230402041a040c0e040e010608060a0213080f0f1204051f021006080115050901081902030c040e01090302070501020106060c0b 75
    0x801141c1c100c0b801c0400c05400050303010183d8140c2e910301c1443c0a01110745100300040307021824000f40560080f08034600403e01400103022161800380680d01c5403851303a500c900d0040d1346a08040569000400700140041c120311500c41e090b503211400c2a00462400000301e0ba004006000a2050751509421400c4100800c0c4611205401402c240042d0946113005480c0c4d4550fa00c155000f54078104030340e00c02400c14000c5100311900080900000d40320f65240030b000c1d40c000004031241a01d140000503c1c194100302100c0c40020300c0b805400520b44000e6003a042941000c01c0d03441e00d03102030100b444660748101040e90f000034403040610080c2111107040e4140b4480040907280c1c54984030001451490640001e00742201440c1100381c1c40f5145c804204190b2001c0c02040300e1503005034220b5004511018400450900086c00c550341c3e02c1c03111001070243c40e072041c10f00181d0b9454004c545d0405404201c02000307000240002c0c40690f0803d40e008155008a2130040c0614140710080343c040c00030403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 371998696 1250 371997446 371997449
    0x50a0e07021005150f03061b030606040302030a0b040b01090203011404020a020f0609070302031e061f03081c0f0603110103021c0e030c07080c0f060d1401090b0312030c0a0503040c 79
    0x2d100034485490891034070309250310031551290150340350101c05201458086a03a51081082c10301417028040084041112a000184080d410000805c00030000d60341c1000385001840c800c0c8800c003683c0c6800e2400d41072840040c0c2c80200442e00510060003403d5905800e40e2280d2000d860050b12400002802c034500300c06566080194040c150501458240100d40001501d0094044130704001642e49049505107003115600c0030b0740c210b400821090142603003142e244441d0807556184258598403200c0d002d512000030742e00e4400c5903400c9480319060a020f01c24132042c00c0b28003085550f26548540c0c0d8028030b8009040d040590001d090241416110b183c0340f44162a4041013060100c20b00880c2d50301c2e0f102c4c0044030320f544144072000410300c1e00040e030400b0201014040e12061245001800f00e6078014202400480d500c031111640b4401611000354000c203e842e402045c3c0d00c3c8400c01785802c01600d00040c00096804004014050f20504100c580c003060a280182d42d0342d4590130318a000b80107a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 371999946 1250 371998696 371998723
    0xb0c0c0a090501080c0d02030304170715030c08090c0d0210121503021f02190c08060708070e060703200102070c1518081509030c01020a05180a050a0e0702 68
    0x2900003040903107003603009505807003116084a8070903004000b080b00075007218100a6042c0d000708001d0103c5c0c0c4004044026808140045407a51500c2d0748071030401103107080341c0900280e07640c0d690741c2b074182d03001100942020341d44002c0d100040320800400c608012444d0080c0c064242e54006900c0d241c8103445600c1e0725816500100100940959122408480c51009900c40c5441040307490580141d0000908400c5041d0000c08002030154000c4c07803200e0400740706443e615098003000918000504c00b403440385c0101d039034000051500e504080c0010b6584001c5901840b07081c0103220000381c2005160080800c94000038201c41e214203d500e0183c440c06170001d05880e01c2c4a0001100151210303141c2c80d088160310b0710540b00d060344450f150788842c14030135200c103076100617460a0701d009105441a08030702d40034180d9180000c2003660342c0c2a43c0c08181507000060300007540c00c5980311400c1e00103540200441c0c400c59201d1400f800915039610300d02907030501004d0302004c9403030b1a00030040c000342c2514 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 372001196 1250 371999946 371999959
    0x105180603032a062d0604020d0608010b0a0e161116080307140c0a05040b0109030b100305011a030d120917120601021c0e03010908040e010f0e100b0c0c 67
    0x20901400385603049400d0703102c0410b210b808041400176105900d1043e101d518140700b1180a802d103180c01140d04000340100350880c1d401c0001002d42c1c501801100094000c113000070446003e154244500090183d00031300c0c66120035010f10880001801958140305080d180a10421401807152420705049041c4000020a09034000404c00c1d000300241c600d841c003560b00342d9805005645125141c6101e0000c481d800822031405008514007a44a10007544040c901800180d880b503807070003249030041d10544165259044100108002401619a4509915644d600c001c5044010079070341c452902c403e80c1405042003125240c81043c0e803080e81c0154004001501c031500c00d24030a003c580c098000000320303540910028040d5400042c6111040b4041c803114074400001000072680110810980755042d500d500300600440c0444010f4000752000600710072055162646550201006034422002e001306030040117042c1e07107060000411680e090012076a81c900480d103c5051002d82180b075a80541c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 372002446 1250 372001196 372001237
    0xf0509030d090f0f030201080c0a1b0b0912070c03031b06021204031202030f061c060908030703150e0a0504110d051510030b0a022104050a1a010518060303 68
    0xb0741c0044481c0883d1100d0f8058645551110408079650f10320b8040030b800f16401502040d41d480703403140203059482482c40c00304c4000b14a1030b40003030a035440f400309440700203650303041c480400818041000c1c068150103072103245c401290340b5035844400e18400075090102500004520b000e04150000344a0b40c8504d01f103555101d00c414543c001c2d4019102580000c40103590716400d05210b100701c1e40590045080d018180d41c1d980100001e04030b40c00407466000fa44403242da40010010b01402d50117900c00e37100300b0380340d10340110b00400b120341154404100341d8240e00c04000c0d01000c0300e505504940300400124032a40d6a01b0091340d60840980c440d60401070346007400d8103010000c0350340c0380310340504100600c160f01c807461314822500b4140000b5104000c00c002261003040c003035000309803005c440b0248140e40160b03100300003c4c80c0030443c0d040e0b50310340100c58400d0401080c140d102d821250f510103030340165410f20004c0f400080400300c640745605090000f2402c580d07010015500b1202000010000f8403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 372003696 1250 372002446 372002473
    0x24060705030c03031f0609060203030a0906060b040f090e0105010b04060c230a030206010603050606180d0506010b070507271503020a090f06050609010c03050d0f0212010501020c0906100f050903 85
    0x205400107800410302c1c0405c0c80410290310589600d803c88016900460460300e0f201e840b80003c0a002c1008c8510744e41d0703807000103814400134000e08000c02c05c016460040300e1074102880c040c1c500b0b110355600c060f490030005000e81c40c1603005640949940746004003001c1524a08118030310207204110031075098200c540341c8100e2002400c40c0c0444c1c800c1c4c1c01e403031035a43d17103200640a44005843c203640c846010b1040700341542c1c40303c001d01001c100c010440441c490041d02c030141400310a8010301110070300024040b050100801400000344080300b180800c00010300da070644030180740107a800304540c0305d010144070804801c0c0c1100c0615001018040311650b52003200008014003900290319038201840001d40d440d020040d65031945040e150707804e1005055404940940c8076580140d00c542d500c850117034070046244050305225800001d03c69a65060400192510040107152441800320000b08540341e00c0305150600400c0450410000407141010203550707038025101c507a40c05200b50380140000303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 372004946 1250 372003696 372003721
    0x40605070e010c02100c06060b0d0902270606030606090306010803030a150b0f0c1903031a0303340618022806050a0306030f0b06040524060705030c0303 67
    0x41015894040040218000650341d44000c00f80c060741c000044940740180314011020b01000354400c190015069441d07010100081d0080300ea0042220794400052007141032040002d0042006960030810741010394041e42c12800e4001c2405018900c003101007030003500c1d803201b40c524114004040e10f02540c1c50750605a41c942086079a03010303050400702007626480485000c0c1e01603d2401448902d041d01111403100c2a501134410b0540c0c0388500030820307540c0c41c51a143c1c025024482ea40110710040e005008030840d03c1060b1032913200750010000203194919000b141121420360b00000300c040380b5503c50000a58202c09400f030003450500200c0d10180c800110108012882103450036024082000e4901d0020407203965800794556100080c04458020000381032450403614020907120740700d40d00d8402c0c00c0d40103523003101d0300e612031804d00c51640b4113401502d40c061301004407514400385c030307808a803104d40d0740e512441d000300c1c400034000d003d00005008030740020020200712030780d0742401d030740c06482e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 372006196 1250 372004946 372004951
    0xd030b0a12020105040515120c09040c050c06040201111609050f090705010f03150512060f0604051b070c090e0601080d020a0305091c20090109110a081b03040605 71
    0x45440d58080214142014032004284550103030360f51070506003408280620301106040101c0720003010720201040b1185100307100d200f80001d90405448142c6030051000b9102000000010f004080c0450401c540d80001c0103a44141c09180c203819440a4600c02070920710184032010400d060344002003420040c541010380100131032802c103003065450a000e01d0b114100e07806090f000556000300600c51342d00ca81c009036008600c20704e02c6207001b13a0303c0e000654120308018102074160014410814642d01a41d030160b4880005d070f505105502d0f1030ba80c0004001184420740c2d0000801040c0001408400420f05e4003600028a0420066200c06980e1313907680d909202e09002803181602003400a8404203c8075020365140e16210b00f005461420025452030a040304c0000c803d0f010b0540001c500962410002c80c1466100340c135007284164140944014140c1105010600300300000a01d61a03200840d20840306500d05105251152110495030108040d1a14907940002c0240024001507030312050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 372007446 1250 372006196 372006199
    0x140106020c010908012c4b2508010c0903150204050f04110d1e0b06030103050a110102030d060605090901051210020c1905010603170705030a140c0d030b 67
    0x8602d548139405403e0752405204500c11440c1400542080c0e203045520b40700719a4030030186d034443c881c280031081e60108501241100d200d1b8031840c04d039444c3d50f000400e50700c01e0170001030724800c42d130801c446a64a03101031914514000b031441d03001d0300c0d50248900c21006406078000030311419181e220010f04501e441e0000342c8000f00100309a004500d628401c0303400300c900161402103080d080e0400c00004040e03420840c0c0c0c0c0e07c0000c0022803220440c0b40704042003107c020583c05034010160b12800c0c106c0e0303e6400c500b406054208014030114000003181c251030303079102458441601c40e81004174110b0003521701050046081c260003040607038110006c1c1440c0e68003910f001c022a030380e9204004160032060000d407019044149010608034250300184000f800c913104a1b400e11890041d00421b03000b9120b0151420795441c02c00380b041108613800c0d5148810051026400d040117074a84a80701c0c40345215400c140881d00007d5580c8210807802d41e06444502c0040c0c510403000c0c01c1c0090007403e551030145 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 372008696 1250 372007446 372007457
    0x50a03050d081806010b0a090803121807060c02100306030206070c1505030c09010c0302070b070813061103041707150f020105060111070509060d080301030f060e03121603140106020c01 81
    0x2900d00008201215070071003843c000b000c0030391030400200324542c000001e41c030800c0540500451941c101304028007034072044444d00b1319a80344c20102150000c000203003c04035900100c0c004c003c0c440d84900c5991020703070101d640c0e0900514414040c3c00410059000941110300814a03c0601004110150403902d0b1035180e01040705010008640911003290030000d04001400200a1544203e041000c0c0b40d109004039290985c4134000032074ad940004000700c41681000071081d2400c1301d1012144010491780c00c1440c1c806500351149500c90003940284254840d604074080291101000150004d21201403040d0180c200001d0003030500311151205000b641c20080858440d52040d0f0304054020401d1002d899020f0800041249140b0080e010b664040d40385070044010a40c0d01c1c000358000c500c108c0c941200c010403890040140c0715009684016500309103c090800c1441e1492554002040098000e040c0700f82c1000f9002040c10a20025000d03000d9000031540f260001072440d500c1e0401d0300c03038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 372009946 1250 372008696 372008701
    0x20a060c0c121a040c05031f0e340e0f0702011401060f0509060706020c0a0201090902030f040f050307050708010b1203031603090812190e010905070b0d0204050a03050d08 75
    0x115402d440c031a210003410a4680301e48500e494610728140354101e0710480c104951144c0c1d03400000e06d0413007160b2810302c0d503c03450707a0300d0882d41d0828401d4142d1200d21a0180c404603000348600110620341180b40e05529608500040c511501d00400e80301401100400082504100c80c0c052282c007000c0360380da0007644c40c000c102c0c0800044641100c0c1201c074030741d070303000140c514490003240d83e0707000756050750380000050100360006942400a030450006d004000c00c00106540001404198581c2c401d640040c810400c0c00001c2c540391034100c0c2e100b03800604d2040c803403065180c1940756102d2074001424600030889c000ca81503006400845001408403201054200e01c124260344901c422384000c413614205c002c00079082e5000e500268a20740c0a01491400c0118024050f201c0c0082140d00b880c0c0b4403c145d08042e003000d0a4402c1e04110032244008010803403065690f02c0d0341d032040740070724040a000454043c2c03200c2d40302d404845c0030b040084c00740416240c0c0d03860420342d038070944498600070a104c17500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 372011196 1250 372009946 372009959
    0x30f0319030b132315270601050a020f060f070207060c03020c4b0316090e070f090e0118030507060b120a0305120a020c0703030c03050d0e0307050f2e09020a060c0c 72
    0x1074148a81c0800b1b503110391a45449006581592140a1000a501441e079685e4032a000c113000481c0314010145881034107180c100e40082c10070f28039401a40c14001c1c005103a02c0800d90019001800c8031050716480c99100081d09010442005414200d4a42200340510904815100301b032410a03844900349109540c110400c00d601c0d42c2c08141c07014a54480707100204400e1250b07400c0740e1703030640c8031006840010f40c40d1400d044e0448802d41000c24495200d1030381941201d000d214802d9052400c003006400711802d0340e0001d10342d21404402600c0c2503100c0001e101d0f65620754205c1c0101007030040481d6001c02c51441d0140c1a6041f01010f020140c0d1000f0016907241c07594001c41d0144540c2e03070013401c640c9003596000d4a0900354040c040e001c103c414082826024000d110300100001610001c41c1c80d1082850090b103411031705030b5050459007200c0c2545000b8442d01c0314a00800c400d1840c0440390901d6280888001d00e86001d010794402c03154040003400700d1300702d0160800c1500420b05444540d4031800c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 372012446 1250 372011196 372011239
    0x418020904140106050904021809070c050c031203070503090708330c190201020f03040308010e160f03020a020f0601031a1005150d0902030f0319030b132315 69
    0x1150602150003040340722284d2409a00500c09c01803a03002c203081c1d120144002c0703a000c55003100c0c0d010200300d444001c00148401003000d1f0a50800440c01813440c010302107601881d0380800342c45c0038148040440421a0020b0512000011f451041c003240d00282400354a001c1d02e0b840381c5003201d1580f1040e42500d00c88011015402d1240143d02032a514011f24481028544e2003001d4401c411035500740101071054440d00019402680207540300311a55040550008100c0c502600d0380f901c410404000c1c80200350890b000c0741c0c0c0312205090050b20f03460010003d81c2008002092404103000d80c0c0000300c00c00140450035422017492403094101c81d5140c0d41650326400c441c0c099140d020040c021400342c11020784000780030f45098000d011800e041e00f54082441c15150070410111600701194048089141d03070f4040c041c5541c5450244420801500071403615101a1204c90450b40c0f1240503112360b00625017903004204084520021600d843d1860b00d000d102042c0c503142c45a40c411028055039106003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 372013696 1250 372012446 372012449
    0x20a1410061a04060c03020304230a080606090126070b03070e03030c07090906110309010b011107240201140c0301031a04081b071a0c011805060f090304180209041401 73
    0x29100d441d113400c00d6810399604208800840c110b210420001c0b86800303000e101142c10b1005840340700c0d80b4062240c200a4041e116400601065008104100d402d0780e6a0700b816044450240c6000c049081030019021600075090461019226115000802030742110045224007840e0b82c60401d0980c6050405441e071048412000c1103600c0302c5010b1007044203982c4a166403910a16000548058410010340f44d9002141c40502996580c0c82c0e0003d9940c101c504412540d105001800b540d034180600610a81c40c401a042071a03242c01407110f403c54001d511140c140c4000b41810009840c040c410560643e00900089940b000810120350300040e10182150159600684050900042070003410403122050f801608620a0302000034924440c010040101200c40c11040d40d180841031541d402d45440f00340300c41c41680e51034812030118101141d499040411804450035680320440c040d0b24501403074100c061800d0b1001c20308150103c00f613000b820603103800d4406000054400a5a40808809 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 372014946 1250 372013696 372013739
    0x618010501050301031506030f03080601021e1e010221090c031203070305060a030209090c0114040305120c03040905070807030c18120c15030b15090312070201020a141006 75
    0x40c0011700028454074480401e246008200003103190783d0b502c03408004130b003011041d404161004140012540d050240340360502d414100d8070389950b48918003550380e40c84001c000c202083e0141003100c0843c400c0d0121008001202c90700b04843d5041e020449c103c540c00e4980034020700c82c2041580c4c8a09003c00e015484243d1050043d05590360405e00384d000c2c100003042c1a5120b25a00380110040ea156101c03170b070064010f4801420b9900c4040d0015081080340420700c840140d05000c00c000252001400d0043c0240000d40c040d1244c071f0311390200e803031801940c103c50451402c000810280592009010b44030700002c1d039003407000701d8200005480b2002003411a901001000c0e405100304002c6a0160003691b11034000c0115003039540764081c00c10402d100741c0d280020b0306c40248442c50b00e0291401344403d81c100c0401c0d8031780010080081d50b6035004450941500c0d0001c50a075055a00078801d50f20313685d40140f070b284080d1008182e000e0b1100c0c40c03d403400381a145030a401003891140c401640c8503104a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 372016196 1250 372014946 372014957
    0x708160c020d1103070b09040b01020a0c031e06050721090f1704090f0615020d08040204051503010216061b0e12073609030503160306120503030618010501 68
    0x3541d4003400405a00c44106440700300140c0d40c0e840450714204400f80080848080240d00c1e2500d00c0c08000c20340d50211961811075010310710030004035480600300400c407a440088011042d141c0315202588400c99200a1b01291524080010300d94025516004642d030b11240290784021810071807040f00c080c540041c0019003c0705030640011101900c141c40c00700c100c2c031880e08207a5030300c071400261999903500c00380071900d541c010001028280c25120030805140054480952060b074003d0070000300601c06413140c7d0f102c20225604500a000c003507210350010700203543d03410310888400030820f43e120b411a8004e14080019070b680304107a1b182203400c0c1943d83d4582603144080f08208114448000b6650b403400b4004002070492000d581c06001040b103005130101c0b00f1001d400243d41590309e0021341f0401c0742005142c0c2c0000358810100c80c0c0c03103901d40d01411a60030f00307200202c00620841e0406180317000400b002800348100000503620510701100c00000d00804c4100c20720b1503c0080c8105030100d007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 372017446 1250 372016196 372016217
    0x5040b0601113c03031e0a1404120914010c0204110d0606081b0406050d2f0d0e0a1e03210f05060a0302011b051e06070816 54
    0x40c070802d01d00240002c0c0408996040001d4000c01100e100c02d070083e03840c07041074409422550b070b2250f03440c1042c00d005800910f0075482d19010342d0050b03004035800901441c10000001c0e0641d81e90798032000000078440441005442d240c5480300080c50741c00001000b1405d4845d000500303280d40101a201000107a5822056468aa0030701001e04040e04420b6000725040c00003a01d20012403141100809450742c9482143c104040f40a03081c0807a1b030708007883c5003010441804500c0c1c004045425601100c80006034102100e06a646040d081d02840d140d0000c980300c01c92400407081016191081600d0801c0041110012000307582e4080a540200b00d18684944d24500b4054000009407080c02400c019040000c04004035080e0905807601241c0141d1341c20b00200e0160031441071980c4800113071218001541103030006071051200c20b030071080d2684101410401c011050114400c040b00d580c1e281e40b0310600c20182191182001c45d01c03480081c41600008030b55851000300c0e4513940c2c81c29280c826451 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 372018696 1250 372017446 372017449
    0x605031b120a0b060114043b0109060f0b030105210f03030115030506091b130f03081e04030b0c0708070506160305060d0819032c01050105010305040b06 67
    0x158085805154401c0c40c400140884075020300890780000c1c402d540c0031286140070300000d407070544c0c00c41d0704110b1510f00780001c1c00200c0700b40b400034680d01c0e8411480d800d4101e5032504d1300044803800c5c1440c0452198031300001350580c0b1036005001030328003144001e084507440d0b15844816000910039030394000d00610075500341a4903802c00b84494582e07802980d546404149540746554002ea001030340303401d041021120f98903450f2003501e0700000100e440452502b844160003c15500041d1120982d07e400546482d000c607442e05803000400d00400644002eaa0f00c1c1001e201c0c03600003140782501d050581c4240c1c2401042e000441e4143ca42c845030044e000d441d20381c0d480b0410382140004440d281c03c01c205a0000c0f9100308400c40c8208070142c1c0b40c496000e2460710050648401500c014000c1032898050300000340e07400e041ea84020044000001c11001030b2a00310043c0101100741586040000c10705a0043e507400392a002c490400030083c03049903a240d00440407103008403006800031500c48040b4000703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 372019946 1250 372018696 372018733
    0x905060108010908180409020d030e04150803070210020309030a0f0b10080d0e0f06040e160e181e0c030108250909030c061a041a0d0b090703120809060a060503 70
    0x141402902c0040c82074003523030126110032050344054011690503c6150400d2405002c0d41c941c4010724080041c01c5843e002d402c0b596801082802813054400c13940b0003803035a1080041e1003080340c000703044890204940c1890082c0c9804441c06a558440f0b40000074543c1010104160495191200034111640030320700446104443e00881588110170301c50001041c0d5909014001901c500f900d452840e00b008100d40b9004900c01c0e00e4201400180c0045501d80d948040640d6a0542c83d90040030740c3c1d03a6100010302c3d80d680280002c6000305482c20500090f500c2070b01c0914143d54080701240e20007100e82c10141c52100d010348a00c0036a9003489000d00003032140360080400c0520904102c0911550380c0c1e640d0064400103030b140b4090043e040708468030740c989401044030442c00444030b11100184038020814404071880b010700100b18080219980110400c0480d0081d40c201c9194002a15003a0300100541803d0301c0702403da120b540b01040c00940244074034412030340000d00818425400103407038140d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 372021196 1250 372019946 372019987
    0x21c05120c061b04081c030f060b04090b03010f230703110a050d1409010b011413050f01090306020d0b121c08070917010f110304050c060f0d020d0905060108010908 72
    0xd00a10001450300020003407140b000600007401e944030006e40038000e0071986907410b0301803010f0400301c1c101300c803c0c403c408075002e54664902c00303e00004803002285c0949240f40600c0c142c4d0340b40c00030081400c903000035a00c6642c80c0e40740b03111500d600c44000c11000e40d010b40c06101e0580b2820010841128001ca00034480b40300b080e1804107a6000480a2180c1003604895000c0b0342d035104d102c001c2c140e42c0d03c008211101040307455401d042c00300758100c540040c03c1c81e01402e8015051101e656a117130b8040c0c40701c10011644100d00f590b0380c0400d01d90010292118144e1140910349891000c10485d5001ca030094003c02840034595403070300002c0d800c454018001c1c0c410001d128281c00d01050881c3c41c4100c0c004c001c00c2e040000709d81900e945200c481110214070340d19085290910900c80007030b902152112211404443c007680307d10704a038520001d880b901c28154401d900c0090b00818940003170700200551400b038010341c1d5990303903591482e500741c0d045090010703d030b09000c100c40d507014000400d0900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 372022446 1250 372021196 372021241
    0x11190b0306280f09020a022505030d030911010e0d20030d0206010314010e0d0302030703021b06040212010c020c0405040f060905150606040605071e021c05120c06 71
    0x800c21206400c0030a092090102d1844603148881001c3c40000c8403e81c0c00d0f00146621803045240100d81c003c0203440b40c1e080b46d4403016052129003403040d8520303c280380c900903000060607a585d0400b050b20240c000c2100700d00407074079102c01c86442403e41d03004424810f840c1e103001d0b26440a25006958424883c2e0041d8050000c52308040035031105514104501c031840301e0150000c00044d4198140350040042c0820121101c0e81010b840360411800440d080b90701d24080d08000d0b0b201c1e11610000e80190050b01000420f0080d5203254011840c000030b034450041c0d000b502c1c0c4035407001200c42e482e8261104000d006c400360740510b09602072400c00d41c0c071142e440750051700c0c406182240c17691a071056912208051311183d0005480c0f4940000d00d01500e9001501180d11501d0503152031005002da0050100207400000031660020705c4942d40d10a41181c540c0c003c2c5010f0f580302d8000d80701c0e1508615814191104c1c80382481b40000ba1080c441203a21550b441030080142d980c48610040b808041c14aa10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 372023696 1250 372022446 372022459
    0x19020f06070f1e0b010f050d081b1009030f020601061e0e09041a0c030f07110307170a020c01170c030c0d14072606010f0e0a09020711190b0306 63
    0x2400401c9500b0400c0a111599a0040b021009903041004c0141010b03000503020381c2c41908100070700d594001d20f140c601c60f803003405aa101e41c4200c021031200d076089144c0d00c4084c001c0c2440742070300c40560303032000030703014840d495520740905442c1c412681d6003003d019080200d515a26841075070340b08036259104490052034600b03105211000426141030341510100c1d404040800d1b00c0e8001c1c001c0d10000c036481844845038504500e07203201400c1400d0400b40c8800240104c40d001e00501030781c1803040341c1e0000c1d081500b80d80c3c802880708411880354401d107108401405000e943e1032044d03124085000350601d640f1110941c58a40032040041a4005403403440160300400000410448901808041aa41c6022129149811240078180c001032102110450003103900005a0100703000300310340c11640a00c1e100f40000324240c8280c90450300c0d61499a030082d0581030000740140310303030010700e490f41c0708901c00c1080c9007619060040c07540329901180781c10a200d84d800d205400308400038603800140103000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 372024946 1250 372023696 372023723
    0x306130f0906060902120610020303060103050714031312030905100f021b01020703020106150210110405130501050301060618030807060f0504030507052a01050c0f011503030219020f0607 82
    0x2040c08883c2140d10041c50f42d60080b0b207994004424142217079020b10241c2d4000d00c0c4818040c4000c0d164403000f031896040c03650b0f0320003280c90f1038842c64804410340e01115546907241040b400711118543c85840482e12402051604411507100b0b001b12202039612000502c4001d0f996032400005c1c0c80262017004c000c80c0d00f4000007403109103056050443c1202c9070300042c0d0390401d90038000c3c00d42c0d64903001500c1d074503a009040c071005070340010000002801c0c040c00154503100c0c2031400120713120f240e005039400040001d00c05410400c270743c4900d04940c0b00320b00030402a507072500107988510001c441c040c01c03403808941c00c0002c280241c0041c02060702c1102c0010303e02e28a040d401d001c0311030903141580002c1c1c02240890412034100b08016150444a00141143c5140717582c00c0c1e54091207010150400402140c4640b941c07800300940105011084000d10181c0e0407a00c00c1141050544015001485903c008110098030709c025072008507000752001550803058400e025656001b45402c90b005c9900120 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 372026196 1250 372024946 372024953
    0x512030c06010b040e06041127130b0102160807060807020a1514070903080f090d050105010303030507090905040b011208191d03010608030306040b032a13020306130f09 74
    0x45280a403d8403000d5a4079941070510145268400130511030041c0d1400032030450103040c11041c1c4421100340305c140d100b81003008003950b0209490034009500008904521003020540343c02412414a003a42101ca100a0011800c5900f401ca841907007030b240c0058400380070441c443c200b0543c0c4940e890040383c5241046541e105019844020703c07013407003a0303240c04003460303e03204111098014070b180c80d0040c40141503865001c5240b00d40080e1007283c41c0700042c01e0100303480302c03c022452950000020406076030759040103400307424220382000000d042d40901140002c240d124140c002c5401107070904150b801e00e030669000001401c0103484100b024003c2401a0f840c01412007024000c0d665040b40c451900289000318201c0004840d11a13410722200b03000c00ea50000c141ca0f44030604a034003180750f0b125540441d05001600550f030f0820842d0440004031207041a5014141480550360b04a084a0b0410340e04101c2c00b00b0f0b42c00c20ba00045851303080b01c10207c1d40e0440016120f048500244010041c1d5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 372027446 1250 372026196 372026203
    0x80d090b160c0f0b0a030c0f1e120f09030806150d11040909030f0905030a0503090405070e100519050a020a1103100624181a040b040305060405071406040512030c 71
    0x74400400c50b1400034003510301d16494000c0400011f4181040e080f5001814409070523011203030000c800f000b041c000d0000419102d0001e841e108002204104072101000c0100c10141c04480029004145103c7c0810020b050141e1030018000218040300e081882c2e41916102400c040c580b006c000000034000842e41804501c01c0030401c0b4880d49034505101c1620780d01400740c410300d6029038400c0d004407070214042540402100c0011204071000190395861500540306c205841c0e1107243c00c811001c25104505803c01300403c400c17800300113098201503024504450b1071190000c801c0040c1c001c40c41c580000388114141508600008090741c84e0620441a51001c42d900b40c0d100c1070768082c1d044415017440b8406c5442a101c4845464034031601d8016070700751200c1041300c1c070803203801050f00010f0141c035800381b00075500a0140f400c1526641c680d207046c0780369285803c0d00c09075140d02075024001a44c245d110301c10154200003400d0303e4207162422040050814001909001074042000010700d100c0051 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 372028696 1250 372027446 372027449
    0xa0810230a02030703290a1a040311030a060204080303070801120807063801080c0c030a08090f011503062a030b0a150207030506070f0518030c030d0306080d090b160c0f 74
    0x30000c41981c40c10500300502e131f4400d07034801c003000903a1010903203a019860085806036504243d10003240900c010100f0328000481c0ea020300440c0c40440d000c1407144001c40150301400103640d85500690b2168075080c003060944000a0000c2e208122040000b51160007100c0c1080c90f2817005c601c60740906914031900c0c0c001e0010803405110a00c504c1001e90703044120250004010003885003030551031015a0794a10880c14500c052000c191f00003074402004000301c04d184040b5070021322011848050201c4150204e00007154403600702280021505691526450000c409110070204180803117400e500400c040c0b41002c1e0040a0640d01144104c890f00c0c60003440ca00030360040c0707042451410160305105016043c41c2c20400b03040688542c0903840001c0c0c84450b08010849030f5038016030f03000245841580c0d00016007601510152301078054040e840b000448192400380d030581c0c4106002258451a5405202075201041c0107480c208141c0145080303005204d40c000040c060f442e08814003c0c40d046 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 372029946 1250 372028696 372028751
    0x60d060e0309011b0c14060c011e18150203150a0e0609090303010e0f070908060703051504020a0804062304050a0c050409032c0a0810230a02030703 65
    0x9480c2d000c55910400c800560b41c00e40032000181c58107a6a8030b516910a4450042803000a200c406010340c1d80104070380c3c100900e24001c222045400400e1510400618584600f103403502e00900114481c06a41150701c507409031140c001804044400c9000350009010b807080340b08114454101c544420390094040c1045006440c002d2516030300300102c0c2c07a801404c03e810354109000421600c44500756823a00a4054007451000f03039545c41007103130082072aa119041c0c034401c0074203002c2c8141d01a803085026003845031341014281e11417003d0009a229030b400b40800240743e003002401207016607000c0800d141c50200705003081c02d01440f10680307e10095806a40c5070300324280c0c0c1410080486090700c001c100940f4144500030032078038094030000341e10521542da1080546030b0440401d0401e481900480c00801c0c0c4105152a80c46503543ca0310b003030302100100d0f8130301581c0000040804e03240d2481c800210f40380c01c14a994000000c1c005c1c1d04050030345018151684480140800e1089409915045 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 372031196 1250 372029946 372029953
    0x7030f06091104031b050a030b060303120103140c121203040620030106090807030c030b0a0b1011120c12210103140613050d03090218011203080705160308060d060e 72
    0x1542000d030160000c0034907000740b070815011708104903240c5000801c101c2e0380040042d10207649001c0800e00354401c90f00100715034103804002208005216810501c2c803080c050031200b544038a0820322190b0408041030440a81c0207205404107d1401001158424425030001c5030428485c5640d45442d400000e044090b00b00100061180a5100442c00c00804000700101025841d503114422a114035020241506010000291000165030010201464080d0031200018400d010041020001a424030301500480c884090340c10314040684159102c00005000160ba07d29940030299001141e80100c102030341c032101c2030f8040c6510780a4000c502640f00e07011125544800e590804a000703010300400d800c22041c5402003140003070f0421806440b41000510070b0464000508550081198094010b0a120020a8150102c0c27031443c4161f100c0c0d1281c0075103498113a000c0d2411300030445000754910100c0e1f12600403e10895000e9000b0310041c00400e114012078990809851a04070f003480c813a071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 372032446 1250 372031196 372031199
    0x1051021020406170d03061202011202070c081c03090c1224200a200c090a0c0806011e030504030905041d121608030c0c1c032307030f06091104 63
    0x24081c8003402d03110006146c1000054140044400d14483c03041e4007134100101100a080454603950403148026001145482c207907950b407103070f59590305880c55889290304410005682c1d41d4081d018101c1810303807240c4003d0880d410400044800c14158009948121884400c4010b51102005000c05900300080204613020148030745514410140c603070b100000c20400201c1c0d074640e402a49600304000c4d102c085140e0007a800c0ea03140c94541c1d250700455001c0c1a21040c0196150b05610000c4890b5007a02c5980550303a03082d0040d41c4041101c11b0042250500101240350107100394455030340940310b07060145490741c9440100b000c80c2d500300221021210368083c00d80301c00000700900012500c01c0250360b8903003141101c41d203904408640e0b005100315004800300d01008400c00684505086600c01c0b108a05000048050000715600e812008039140c00b0498440d82440300b065001d804100c8140c2c0116228003200310002c0001100d1010300c41c1e82da01c004511280603005441c684480e0fa00c5068403103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 372033696 1250 372032446 372032489
    0x2071506060905060c0c0f010504090f02070213050408070609061b022a0604170102040305011e15051f0c0203190c09050405071206020f070f050c010201051021020406 73
    0x46100d43c101030f04c40e1000f4494440c00603c000b6103440b107014190741c003042c482c003044010b03100c82c0982e03004105201c0c01c09407201402202640503200490003201e0740c0f0ac60b80164a2041304031081034a0146c1101c0d4100500b2000c03890941210220610941000030807034035040b110002065100c48040050b0440c6030203c0d840c3c191410303001c02866801341d4504a0541c49030000351140710701e01c50110501e0304a0100c0440d01c1003036040d90019a0001c00034000382c9908010440c100c2c0c1c10300d4150b0b003280c0c500240d4111804403808007400f640c001401c45561010070300c00180a994480b0203c208105140103014010303203080c0203503a2491032408941017808010b244c0302c1511034054000743c150b01d140c0400c02c4042140040c1c02d80031100d0342440807010f9607150410101900c2030036000c0026890006a0008119610f10f0401d0704a004000380d80e5141d10b078600480c2aa03c081d1031810300e01918000600c012900d031134011050030007401418025000c3e030740c045016911640d0080107182c9a212402811 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 372034946 1250 372033696 372033707
    0x101d0105090906060120070b0d02030106090905040515040203010b030109031206060e030d050703021504050d090518011404061205060f01050d03050a0e0d140723060403080c010207150606 82
    0x2d005140503240e075141034030000f48440c000b80ea02007280581241d0708010036005014103c00780041c04142c0365a0541d0301c0d0180007170360080c420303180094403602d0001180401842118000e542c0000a044050101c0c00400f000d80d2000d001070341d05540e80c40d00e5410300e40d024413071020660b1203511070050303040c6210f0300d00c0c00b26045a4040c400707200340300003e0720140c3d502140c9c0e038039512841c0c00c00c00d881d1441740c00d0480c94071049210200c00840310000380300520500242d03804414000d170782c50355440784c1c583c2c05002c0c004c0d4161031015407000d45040107008108241c0c07a441c3c08540702910000d095a6034104250800910030f0007550701d904083c0038002c01e1400020365902504051b11b40b08020041560010854451491041c0c100701800e00c00b602d807a0f03038500950549a4104443c4407201c1191107903180c854545100d00c0180c1c205c11080b550940e00130a03503541060600506243c1058990f0302c6042040d80100180c00213954200200e20010b01220501101c001c3c4e08040061010304110001c0c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 372036196 1250 372034946 372034951
    0x306050d0f020f060a0e0904030c1205070209070912062403061d010b090403030b0f090705031e190e010612140d0503190c020c03100c0206060a1508101d010509 70
    0x8207420421450080e0300810340c1e00c0611415194a08a80d44500302201c041c5401c0301d002f001d4071200c0b0f140f006401da00030040c0ca04580204c1c7d0402668a80b280c0c01daa0310f1a541c1f06600711078200050880208030507910001c0140d1140961120440048a80c00c01d50130740c0f908119002680d920240d240390108400042c0a0050038008029908151000454941c0010002010552600315140c910380340d00740303e290300040c05081da64040c1010b21002e03000f130304221901e40420103020400c079007134014910b0441c0500c1445501c1d0301c0e800b1422120f240940320050710380007150740ba00350008640c0d00b000814428280501142c0d0700b031041c01400a41000024907500040001c280184506d03c020f8070300c017a5982510a800042c8841c40f00300507410701da811060390b1303850b00403d80440e5840703d0070341000103070854a40c00da420941c4c4078004c00c07c3d0b1901c00c0c081e4640b400d4502456001540c004c080306030300508098188081641e41e60b000d145c4001d605030038030140c9040c210040016003403400c912754 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 372037446 1250 372036196 372036199
    0x2030d0b0603060a0b0c1219080a0c051c020f0c0717010b0f120a0b0f0a0c180303050f04080a060b01090605030f0c0927063a02010306050d0f020f 64
    0x1455403c140e000620085941e000e0004445030005546540207003c11620b90601d102d501003945030201c00c8210201891000c000e000426503000018469429510072074070311466a440300360030300b00206043c0141007412014004019420040604012805c0002e085071801400040624030305182ea100c961014400014032540e0405241360300c956503102c01c10116010903030341030303441280741c07400117240640b014006021b004071601404070340010364280070f100e445210414050801c40b00340440d0321801c48074a8910310100404203000080c0310b0760040400a04588041e414540c90304001c03410410340070310403180282c6d1041151465604800d08000038116404d2080c11031901515600e10303520b00810fa8580020300150650865640300100d9511300001d00c0078004008000c040b5402180c2c054070514440c400251103486003003641c040001888144019a1048031480501500c0ca4000314208038140744c2c44050114060702c034050707c512031901807402280d03020900c6c0144807001d000c0b4a07015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 372038696 1250 372037446 372037459
    0x9021210140702120904020702090a06090e12030f1005060d0501090f050403020c010c080d09080705060c1306140d0f020306120331080a0f05060a0c1d01110d02030d0b 73
    0x1001c62600803880107135a003900c0c445655a80c6025000400034894000f00a600c1004035043c0800e5026079401601a9501603004000034603003000c0f901c0d40c0e800e0074a24161b00310002c00000300e40c281c41c1506c1682201300d4120a104540d03d4000040c6a5000180c12015155690004116940039070048007080208803c003040107042030f440094481c101c0758103840c14003400d007100c14204a1030303404503802175a584004000940542c030389180c003a44642015100d80c4140c4000c1400000c00c0001c4640040c7d0b1041d100382494a0080c060354403544000c508039001c5400d210000a000c039902424400103043c200050780e03803030004200080e8207040f8100f5201544113210764030000b42800260400d0080d4001404a10b41040c00f201c3c2c080450b40e00308078524040c1c000074070108401c0703d0342d4044c031900c41c03025180299141e000c42c20444881c403100708002400c0140c0118072600b103c41444070b400d410f02d003848032100442421441c28940b400d40c840181d0000904005001075881007402d03020088951 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 372039946 1250 372038696 372038701
    0x417010b0f060f1804050907050111060c090d1e0b01030b090a080307050d0209041407090902030f0103030e030a1b1503050103200d050a0506150607240902121014 71
    0x104841d030040300f80110308064000b0380e0803a000295075a415a800f0010402c0c009442c1c1642c0007501ca9410f403042c203001c1102030010b039640f01004a0214408c04210b254103042c141e041040180782c0000d83c00659107032200450030074255210400000c5005d001d400c2140c800e5240d80b03465051000000c14042c0c964101c0841c0d900017840303800460360010140d180a0303445006003481d90707001b4840c1505903588940b03403000150503103024044c0300748189015194a00e04c02e075564204030a0380f00841e4000c3e0b1020403400140b000a016407681eaa1409004d011a070382982d5946d2a5032004101510141d00b41e80305801c204802d209109074141810402c0c50240400d5255a4a40c0c0d04e151011383c0b80500e241001c2054015034444201034419150408100c924540903070034455111071055032508010002d0f48020000c60500c0c1c0129010340742d0160804040c402007112080c0540c0210a0028480ea2901026000341c2c2c1e8a40c0d41c0d1071100201c00c00ba182203100105c1540481d191743c000c9400e4100c0507001c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 372041196 1250 372039946 372039949
    0x1080102120f060a0806090a050105160906211a0a09090201080609250503070e0d080d09170d02030f060a03030212070606030c14190803090111120417010b0f 69
    0x31a82c1241c8000b00300307a941d0700d8000003d10070040301d4110364031a00c129404c0004165000601d81d0000c1e000340e0007005036460328885220f45030b0b81a81e000e4080340300d06408019892154401030391141c9254030400e000320a10686400755801c4109104108000602101452170014202801400807110801401c8079950019120344801803001c0d210307040e1007002840001101002e401860345246c0b030005034116540303010345180c0050381c80d40c00003900300490302c072700c2c1c00c041c0d0280c280300f070b04081c2807400d0650441d8910040c00000400700d07089451080b140ca0104a410f01900c840040b031140941c4902e440707002c82a40c0003004107140d10445080700c04002081e0007042d44c068180d18403826030b0b5588680e0401000ac0e120756031000300035a400c01c0c2c0c002208070883c2c6030301003035040c100c48440400885500c00040c40307009014600d403540080080010640c0070700300d02d00309041d5900c00e407a40c0c2904450000480c3d000750f400f500383e540840300f810032080020300c281030f51180d040b9101c00ca039180303100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 372042446 1250 372041196 372041227
    0xb130903020c37120311011128021e07090f09020603061c05030714100c0e0123071119180b011209080a11120a0c0f0807080301030b01080102 62
    0x4a425040d900a560003103009502c048824083c018000c1c1031300440d110740c44c0041c040382c00b04003e54515483c002002c103100c5102c8040b030b4041d0280080c0b041000040103004080f60396203101c00019032040c3d072945228904452105100c41d0b9002c4003030302040d0b107412595000e4840e84032000900d42c0c6001004801a92aa4240c0745c00000599480320001846580410744a10103203010f0418480801d90404000e24000c0e0702002e9001c401c295401074062290035416100781c080b18101081a00034944483e51103a1109122400364006105801c1d0012540301040da12680c0255071307881854001c3c0c0102d00305985804200030310b01100300790982c40c0519040f19041550010700340540c0700c6803044c2141c1e2140014191041282c5010040c808040c58150300c40e82c406040507001c42d02c2111054140c0402040c10404002c02c40009854600309030340c221406039070240d00325081184800030f00041240e20020b800080c3c42020b005a44c1c0d41141885055100141d2105c442070f030040040c4190b00104d40d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 372043696 1250 372042446 372042499
    0x40305071509090e0a030e030f060a0c120e0706020c030319030f0e03120a0b01090e1801060f0e0a0b060901020309041a12011b02010903021507030b130903020c 70
    0x10050918002007034101201e10310507503806041c800e0b08082c0b0001c2c51000c080340185081c0d200f40c4602d050000114141500d45844144194040c1c006000281c2d400d0440d4204a003034503c149400c18003103698808680031103561403455261503104903414440150100031525100800300c00850500b00102180c0380c030b450035006030384100364a030301e079803008200300c0d802001d10b096400b8240e80e04c0d08402d2294010007070048030380004a40c2000b0840001c4d50048403010181c070040c840356041e40d42d03403041c04201c80451000b02030f5190359079880000c0f110142c80700b200103002c18080c40f038100d050400c040000c2d01d13103522165105d40410010010700c0da0f000022135002000070382d400b01e07004820b00b40b0011080c3c00781342080d8102100101502201c181940300d4100c0c801c01810030b07044204020b000301d00701c0d1a00388000b80940d0210740c40011119503200d00c1d07540b1150900d4041100300261340803d80f0040102c903554406c41d21410792804140c1c06011041c1d0708002901d201e00b0b09104101c100c0c000d80d510 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 372044946 1250 372043696 372043709
    0xf03060f1803030506090a180f050a020d140606030102250c0302060a030b09180307020603101a03070f110601140307080706050301030b0106110c01050a0216090c030c020304030507 79
    0x485035588204122600505034403000200c0d888140c4065003006000f501c0c085070010721072801c07840040e1203102d09108290f485080f0100c50310b00c4016698407000700070340200041d103451051030040c200507942c000c800900f4600c607100040070512010625403814802070b201502c00d90042c008901c040811960018080e00c0380c038000d07400c41d12503003008042c00d11142c1000e034111000140d4a920141c01d0b030410482141d06443e603120f0380c1c1d507040e86d410050280d11020304058100b0802000503182200203150066622161183d800381c0d10816000d2003031a401880001e0303100402040f02d9960049032111000d0b01c94180000c3c1c0300e5005490b80d840b80700c1406100030321030542e02c031110b85450400114001d00000412100349a840e0701d4080c00940007480200c40c55141d0000100715a44600c600100102d403030001010000800b03001501c45410a1901a045202d41c0d90380b0204110341000c898028200d500c8001084c011a00d070080c2555140140402550310802007000000e20002c1d034501194403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 372046196 1250 372044946 372044951
    0x3050304030c0201170a020c0c010e090a092f040e010b01080f090f0f06010906081609050c0910080402030105090109031403100b0403030302040f14010c0b0406020f131406040f0306 79
    0x142c51005032280750480f00c40506151080081141c007002d1a4014102c0c29082d60843c0c242d9604000115813a007003002c0032a401130301c03c03c081110038096070061078590b4410784000c50982005404103011030807403001d0f0481e001e00360b41c0485042c01c0c103201e05c02c107144501000703014200c1400300181154002500103070341d01d50700070300051086100344031455202070707160203a59001ca00001400d988900078007034000c0c4503144c40c00000780c480700056040700c011502040f070503c9600c0d00c1c00550081a0007400d100f80d51358204141503082e900c02c1205082c41985494010072800c040c0141030071200d00401c40005603150040382400301e03400c03c81c2c180c0d002c00604030302030307072507690b042c4003180722015074130410030290080341c00300405415030007500c1074540148801c0c1d9500d0f0b6903c00001940b4280d15075a0101d282a8140c0c004150800545507000340a410301616084c94501207135840c0d4402413407160500c24106083c081c21209100c0243c65810031a1280d0801c0d013841ea01c202c42c440244070042180e603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 372047446 1250 372046196 372046217
    0x1030206071716140d05030f0711010b1f03050c0a020703232b050f0f0a02160f08010e01090b0613060806040f11030a03050414010513090e070b070305030403 69
    0x400ba1040710440e200d5540d5031008098249018442c1c2903290200a00c0d81c004c5445900559114105480c4220500c200c0d10040303440c0c0c0c84c0191102c2880b0890030803a5500c6605400e12621100841c885078885101b41000c414591140101200c07805003034090f84400130000750200e5030340000c1e0401031325000010315490401401842c00d001c0a0070068000d18000c0b0315112011800c4d0100c4406000000c240c416814200001c04071a64460f2102110240c08103100d01e07441d04407250081d007007800c43d40c0102c96560360a01031060b1014002e60080d144610740000038022200280148042104004000e2203181d0141e640d1040e00d00c0002d1003980500100f042e03400c4d1216145d00550024500001039031054109070803c0300103641c0c1142c0c10b456a00f007403c080c06240c20000741b0100300e580c041da40e0a041900380a654800c0f815242c5000307040080c28040000f02210070714180c0001d0401c2c100005100303502020b003600f414210340c08050200400c1c0440c3c4c0109820000b202d5020b0752625000d00ca09 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 372048696 1250 372047446 372047483
    0xc0405011b030e04112203020102100b220f0e06010501021005040f03030504020a0e010b070201031b020604140c0a0b04080c0604030309270509010603050f0c0d060209010c05161d0103020607 83
    0x10301600c0c0c0c41c485441c0c0c1460345251003507805807094060720300032b03400c0e00c082030030308840c0609854080326015080340c01e0500d958048490442d0754180d1502c086404524860715081d1181a50322030301d451409500f180c4010880381d0380411580c00c15400310b66040c07195141c03507240c0d0240148418000340a00d61144002021561001041c03005418000c42e00c0185585030581d41e86150402202240400d241030035030289050b0540040c00b00480c540d004090035610750b500c0c4280f07040075612480b428451904804142e0345da1483c0600078080c03006d9820f0302c4600d411600c0b0324001c1c00002280c040d4000b04020310100358013a555000366a10600941038401007480d84800c9842d100b0001051145040b0a0242d000d006401000880c2c4c040d0084407055400b014200e622410a081e69941c01a04045000f002403099005440030b40b605040c22000720020381c499500f4001c0c0f1400740403021406d80000c2c00800110310b80a44441241881c101e00e960460380031815500c41c2010107440c003180a0341c26040d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 372049946 1250 372048696 372048731
    0x40b010e01090e102003131a040506190608011107061a060a03150306050a020d0e0c061204050f0a0302060403080106020a080409020c1204090903030b0d0c1a120c0405011b030e04 78
    0x140008809026070384d00c5c00051540a1f69041d4800320f640c408950034000b00700710017121203401542c111000d40040d45a07541c284900c00001e049080310a0f07124240094840800e1140c0706141d94030014550f81c0eaa02c030310b407030030071203070a000c00c0070060f81a1412000310b910f03280190b845441850800007000700e62800a601c2d0150b407a8801081c85060000b0801e181c04150084c0c600000b03910f40034006640c1d144030b0981c4405482c00d486070414000d0140002c041914202d46401c680184195042c0c4036011400381c1c18801040800d0740903902a00510007010f51080200b4010318541c409080d2004450780c031f0341c0b0700f449141700b02101e190f0042240a0380f000188504800881400025691640d031054504094403502005a011034030309642c1c10003e090001104c80c15070703400150581450b080111816040c00c070248105028402071001d40d001c1c001d207041c418060a148541c0540303032031910000500c205000e800c4038000080c440f15000001c0d41000c0c0d084600003080310b01003025042c0407865845c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 372051196 1250 372049946 372049991
    0x601050d0c03060f020c011506020c01030f06030501020c0c010801090b0a0506070302160305010b03010b030712062003190b01020f10180c03120e0a0b0f090f09040b010e01090e10 78
    0x6420300d803503c802114481e40d8000c2419946d070708028232201c0c9165214040c12507081c898000581c000700f1145201c0c1d80310740d02ca0b10105916a0000407007035105e860305070881e008120510038a5100c95403c904540c0c20801c114010300c440301d8140603c07a603960110308020140d208060282001082900805009000808462074080808a5000c0c0d0f6414424064244800030f14081d501c1c100f00d4926608010940e6026100510f410300e580c00034680c0c40c80000c00701d00f130a4101e800401880388030300f05242d100450042a200c400044420046086402111044503c641c15503211900c4c8480d64000403541c6800404101400581d00a0b0300003107690780390701418004c242711008480807041090740703009500c2e00307841c990b1703803884101d1444240304110360b1902036071a04d0b070410b0180010b0603c0c0c0c04010101d4446c00343c0280783c1d01440c80085a62040107a4003264108800e00042c0071500c8188a918010304508000340070b00b40a50300030326110740d1071068440c48642c0b1845114410801d0002115 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 372052446 1250 372051196 372051203
    0x60715050f0402120d080402100c0210080103023c0114070311010608030304080f0c0304090f360b040f1a010e0c040302011416050f071403060106020601050d0c03 71
    0x12518114603154801c5070215422407103054001d8038106507040025812401c0c510a4403440e2003034449408106c04030810b58840410820003041810040c0c80ea040140c0d007445668445071304030f50661040105001011404e0120514020f280b1140515229010820800491070241140040000480e2820b0303e200352103208020014402042640c012440044050180000c2040546814906469100a45014100b40d1062001d040500b450314003c084849030b80b01102d2401d99100301c0c0ca03090300d149003480c4010356911070182c1d902c52600004a6040400c24014101c2c003400c2809403a000c0400310006480e0090f000009002c0080800b010b0103202e811100c6900c2c44001c2c1240060042001d005240c41c210f035100200710522802c001b0b44041e26416114101b080c1c0c412035110805411a09095124120690502020480902541a2a55480016040d12800d02e034240c28009180428180290321103801005507582c041586070642c1c80413640e10680c4002418000314140b0980c0029 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 372053696 1250 372052446 372052451
    0x50906030a1d031b0109051e0304050a0b071203050124050f0c0601060f0c020307030602030603160b0a0905150d0903050f0c0a03080903070b0c2110050924060715 71
    0xb840e05400c0040075018480300440007100801c520303446282654a0008010220b1b40f00c103490004103480004141031019000e0704072414a0ba444002401d0b41791a44e202c0c01c01c202c800101c10090201800c005d0b51303080e83c82e0905021a51406424040e1203620035104501381d0301c403103a90080e85104000f1120260080c0a0840d101d8900031425502c1d86400e00c200c0000c20381541d218010140903441200303905400a011307000091540d26850040e600007400c1c0c0b51305020700f0324200d40000c0020b4400001d42601c582c1301c0c1d04d4200929001c0d00440c0b4580125104401490000344014462400c41d01e050303030090000300d100c45182c41e0994590180386c0f100142c0b04800700d410442480005000742c6018060752b20f02000d40c41d0034680c1c0c3c1d10717071145403806401d49101400081e503000d501001000c8116010158170501d40541104040d040429a12007194036108441000345103050400c05070000200c08145c6c1022034040380c0001c5601c180013087c0c4c000d82010034040e05005051910000c0c1c01c501700780c03e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 372054946 1250 372053696 372053741
    0x20d0207051b030f06040302030306100e0303130906091e020c070302060d0c0206012c09070b0f090a090c120906200304060f0b0a051504081c091401050906030a 70
    0x71030001c22040000c00d4041c0c42584160000584c0c0003c0460050f80c0580195203141c55900522010900300541c00341802a070810030107041d213040004200e16a6280c008101c100d08012091066920950045461906040088000d61a140e80048501710703a12030040c2c0d513800d000101410b0800030390000c0c0d40401d0108001c00040840c6c1c1145403181c40d00e42c02c0d918280c1c4c8841520701004005000b0540040038500c45101005490030340030340000202d000c481005903a4000b0840d154804145c00d241004040741c0d404007401d013400728a0150800060070b01c02070288040081040d00084041220a5118200d1405000090340490707003044010400220682c031451100c10164130540701166a603141000c41d01764110544102d035007160004281780d941511301800c10a458540001c0c40141d410100800a00902d0420134070102c0d8102c03c0c0240d02d8680100b0000d01544895406000c42d501103103000c030f080342c0c0d000d81150003d140449001c0c2c0c1340c0c1c0b64031080000a02c0f400d050b007046140402407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 372056196 1250 372054946 372054973
    0x312100f03081207022b17180708062505190309020f0406050a120305190f1103030103050706030504030e1801090b15070f2901060801060e030c04020d020705 69
    0x4081c1e40f4500c8410300c415484078007003203903211483c0c0443c0c908001400c0c803000040a0880d03c0d4195154146000005c1504641203094845401d40d0040202504054824a11601406108010304145000e01050b280c00d05400f000360141341c5120a160b01c0612000c0009030047c0c0554607603034404c0307401c03152202c07030200064020841c2240513803080664400076070031490540920b8041c1d51002d0560301e0307481c0c9084001017031824079000032401c1c84000c8c0044510144a07248103401c0c0701250340d0792540c41c42c40d07031000742408108417484401608100018008107000103085d81c1201c000b0f1030002020340d40c500b0300b10381031000840c0d055407100c24805400303103e92000031554180c4046450030440b0303110b21030402207020b0443d11002c6555605000d00c0b004168000b4006242070f018000e03010010f00d40321500c480c6100d15030f0030140000f0101005110300d69205e480d0f2030140c07a16081c00341c0b144c43c4a40019654550320940302e481213400080201840303a5540503030315150307402021111030748075000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 372057446 1250 372056196 372056213
    0x91903080a06050f0d020105130306050a091202060c0403110f030f0f0715091514030906070e010c021807090b0c031b060609010909020303040b03070c03020c01020f0312100f03 77
    0x860040c00725040140c04102450311444042091600900d01400c81c0d1140d4010343c0d617a000356041a2465006000001c0441c00c940103040c407030800304400161021061820200c20084480c0c03040455010500b04840c0b400f4005c01c45003520f40107007141e000c01504a0000742c1401c0d071034840342d030035001303011070051145000540050900010800c1e00c5140d03455000710f000d503d090083c0d8000244100ea010043c20ba10306221000076451480c002004e070982d0000c040c2250300a42e81450385074041c40070054401d51080040d00740000910346803800700d030075030001020082c0d915192281d066002e40070919090040780b01c41c000b004c20310582d0340c594480d10000390301d90f005900f034030850300d8031440a680f80c0f840116800c1d2203140c0003091a005a420065503200902111001300c1e09840100808140550840040c44c072840f12652000c2410500e850000e040c5040740280034191346c0701c441480f451700e0000c01a294000070592a040d4242d940c96400c220015050f8000340311403070fa910011040c8030700f52 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 372058696 1250 372057446 372057451
    0x7091d0105060303090d03030b06160804030c06080c040603020c0a051902090c04030314220f1805060f0f0406030c1e0b25140111030603011d030a0809190308 69
    0x10001c0103075035914410f0546901c61026403d80c0540c95210340800680281d01c603c0e480b0002810140c10161040f0711801040e035840f00c00c0d19000320124042003085800000807019214510709081c0c281003001c6000d94070b0040c1d00034841810740119042141281c10842c0b00215904603084400700d6603c0054910560f40d41c1109900840c011000100140c0c10b2100300c07800c50381d16944442d980e80f41d040506000b50410321740380010000b440c1034038565800701c060041c05058130741c0c49411070701d14180002e100f030b420341c00000401e03608000030803c2c50303501c0c0e0210320314000003545d020b0301101100c00024000c1a081c3c000034880114094085040c040100c81244204c01062445119940700c0580080318000c103a810180c50310424881301a80d105a078041c10300c10f00c108101d050307000900100034255090351198046400000c401c108091402740110346401c01f5103d400c40d030307000302101143c1d1a8820105840103006040300840c00340f840c200180048082c0c4070340c0009250b030f42446d00806c8108103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 372059946 1250 372058696 372058751
    0xa020307390f050f0d02190308030f0a0b03010b0d1b080109060c020d0503040f0213110d05091612110a17010207020924150c0703080c010c0203070b0f0402030709 71
    0x1908808102d6051144d126141c1840042c000c1c0c03804180d550030070901c540500e06410070044048000070000b914900510b014440c10409140386203000344038403045624404280b0310036070500020050076203ca070989039001e6005070b8112040100716080c004500340c1607102d01c1440d07280c05c018205001c82c1b5404084504120340c2941c8040d00043c1040b1f400740015907000d090404a03000c120010310b800c290704030303080c1c0c50b0040110795034044c0d034400005900103080c0b100c05292104100501200140510300c1d011081605816219081001688000c1118100204000142012100c1683d10524040c006010780c60500c01d030030400c012118003035008480c040303019000d210041007404a40c005150701c144441607498903c2d20b0010108101c154a29141401561081029044c6140b040c000c01d40078500540d42c032507845d94042d81c03803821a81103120403000c54009000340d0000803020000c564000b82100da1302c900b01c0d02e80340001f82c1030400540c0240c0e0200c0c90400c28030340b003c0440302030501403a003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 372061196 1250 372059946 372059969
    0x50303070819050f0a111005041a01081b0411090607120e0301020703050712030e0f0312011d010302011206050603071d0a15050a0201181b06050a02030739 68
    0x4050007541c0d14041c40300c000405400c1807000c502201e1007600101d00310349034a411116100410b031040c0040310308c00d0301c00356101000d12010700740c0d40b40224400d42c010b00c2c0340c07001440400050b015103004d0841100b9810b1007980c8515505940780341d00420b8908420004090030b540740568a0641e40e01c1103c2d0401101003680401d800010b0b02e81071080e100303065010780310a840c0903070581e9013240808800000406240e40d5142010480100308881480000200001d554507100d440c1c0040c410103050340054006001c08600c18042c54800e00d04a0460354282488030080c0c03080d00b0b82a005d81029004190070180101c100701e074042e480307500204038140c1a40030100d1035440200380180c6822b035010f0345100740307401d00c0a036041520980040c840c5006510000400507812442e01407400101401500c0303550040742c522a490034281078000003051182882440c160442001944a0041c104041c103113281d4090041030282e04901288654400b80c0401e0070900b100c600f010b1802c070124024100c02c0d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 372062446 1250 372061196 372061237
    0x20307030c15120908040b0f0d060905071202070f02010e01050f0f0a11010b15030c070b0108060f01230613050d120f0e0a05211e0d090617060a0503030708 68
    0x383c3c0744140f0400a800008151900c1e00b065060f81035a0300101e00214142010003024004440e80c0c45240040c00005401088038201130200a251220085901212a00c1007103c203001440c444030600980c1e90a0074000d0107800041c0042c0e4450040c58841080004001956000c84400c9401040e20500c103441c0c540e51181100219400c90f00f4500d01160040c0a410702c03880b0494030900556400800b10b50100d10f0004644e540401600007030b440405180e0001040c0400205901601405403480e0391240250b50b50840000100c81600c1040d9805001c00103070070311105000c1c0c84101c001d0300000e080844d11910381d141800b10000c20900d1240040d06410300314224501c1102c5070540148000d0450708030302d040c80c0c2000b08003243c2071100e0740281e08840710890040002e00203d0405111002681c030116080c420080c02c102c11140f841003007200c562424414150851142c0d03501c07245c0080d80614644d03405011900c0e031656500100d07407510020500e02d040000300c0703006005201250780c0240c0002e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 372063696 1250 372062446 372062477
    0x1903080a050106050a12060f0f0f0e04020d080903100c05070201020706020d020d0e030709090c03060c0c0210050904150b13080712080c03041d160f0e0d020307030c15 73
    0x1100700380120400200204080e14903140302c0c082010761821280d00024000d5611454a0440703d0160310075150380200400401140e810250150010702e48405c814000d0b1030a540040d60140e1b060b40010030760711020991290544003006004140b0303464410801c403140003000b02600940207207100304e00610403801c0201c0c5040c408540034180300c48540040440f03402d0b04000b960006401e110558040c80b41c0c980018448075107014000c0b0761805504030004290450400e1410780d22000f80c0b00f011300c8010722010740161941d065140c0341c0300c0c881c640721380c40f42c1a010000380a03000800000c20410340080001c0f802071403480041088029880940b00c0311681c3e1710082d9122281c40c1310307005240a400700c42a000ca038200c0000c1c2184010201038034601078803220b4065129660098100071100340300304200c41c070010349400551004060400d40b02c156410b0038018030111060b40041c0c05500702071001411920108242806035034400760f1200811f0700c540344142c441400e1410000007564244d1241c005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 372064946 1250 372063696 372063701
    0x2a090405060301060f1811040b07020a060801180e0c1519031b0f0909020c0706080f15040b062511060301060203070b0c0c01090308090c1c021e031903080a 68
    0x305c814940d006000c1030301e4a046000d172109480c0500810760f480d5181105400340312401040604075444045072110b134603005000261495400c0107042c088010010300600801201c1c662a400456401041851a544844d82002e6410f10000d82080c075025011204480100c00b8140002c0120301c80c56085600c610120150350302a01099100e1081c1490868114895a001c4001c0c0c9110b00f021400c0740c0d500c1200c10200d034031012503951141c0203000140080c50344052005d422003000711030750085045c000014040d00c00002a030f00c2c4265601d4503500106d403038490941d1038460400710803000d00c21a00c00741da1801500c0d00b2044031603924030b0380031800034a85041500c2c140c035825401503086c40c10f107aa42c001d45080241a80c40e141c1824085207804000074003440780840c1c4a40d5605026050030b4017040d2501c00048141e62003100c0c104500c3c4024001b01455003006a01140c05000007111885c0603003605008400c403903050f014280500c400c103400e0801030b42c00d440c402e545043c030b03c0e80d5042c401c004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 372066196 1250 372064946 372064949
    0x40c0801171f0b0303040e01060504180203070f030915090b1f1d10180228050a050702060706050429040308010501030b03070e27030a02152a09040506030106 69
    0x750810400300c1e031240b080456001e00303003125000c1d0840e40741a884030003482403107409920890024000180034041081c0c08151201901031840c0254114201190041c0c40356510017018001c140d0354446200038401e41d01c040c00c40c500003100c42041071b100b503401d154185c2c4004aa5a10300c80b00f10500c0d10321510001111034003120346034601c11300c160400e8170900d290f4030006491291945121080800d03021400e800100d040042d1840041c0d41d04c40400b2004800c83c00e040744180c00041417a0000900e58200c0c00310b1720519818501103690f0303291380c800202c1c18001c460018000340d18140400c800c00040b00c3d50030034a10718035111000c5581d042c503003445c207a801c1154002c0009450340300402c0345501a40040d184400003d041d01c2c80f4548401d0412001070301210503d5004240c410552a480300311101c0e859000c0000d005180f0b0304c000d20364043c2d6508400c41207501c0c02506c0c4000903d851719042d104000700741c0c41c40c4945a000706054036404240d00309200d1288511320780b00c0411000e141c144242030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 372067446 1250 372066196 372066223
    0x60c1d09010b03130812150f0301110a03023105011b0c050607020621071b0203033703020904050606070507091802040219021c080f100302040c080117 66
    0xa20710ba64541c904100014014002c90303489105003c041b0f1400c0118960500c50701c100c01c0b4001e03100c0c200d001048100740c4504140b0f4060b9260241c121a1100344500300c451030308680c20056968076a0305134070401c56030603004103003000c1c40d0b1000c80301608581c0a4280f0440e00309a80722001034000e4910080c00209404000307194130654002085282001805092924002402c5904100d0b6986030004003103c02c07050988031300e20b1003040001d03041d000120404964540c004d4210700d815075902103641ca2003103401c02c1c40d4008050a08036940702a030ba04500b4103154480d80b00c401c0000d61140540650041c0005922441c10000001c081b418104166540260000c0041040c02c0c0360040c441c006008409900c403110143c0c0c18400b000d0385440c001020a60a1116541d040c228915402030510024003141294500441540600305910031407154000d81300b002d40502035111900c0c003070510003450b84020341240c2080840c0d900b440d04412102d04850300000003001ca0754014425039140d20f240d08206 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 372068696 1250 372067446 372067469
    0x14010806012922122409080f071e150c14120f01080f0a1704090f02090a0f0501051c06090e0d02010b0105190c030c060c1d0901 56
    0x1084004154814441c02042145001590049061070600c0c25071050000c000c5814140400207990302c00244680c0041031001e040004001d540c1ea900341ea119485d482c828251000c240310340400010300c0d03100da40041c1c0d0000304103544040a401c8604590000c4000b0b645110032285010b0300394062040c80104298460100e11400494a01d204c00070407e90401c281004407540003c00b44808045c0182950145908900b036a031401c1c054044500b00c4c140c10800c2c041d08640190f440c204800202101000d070b10140c0c1c80c4c09071054003085052405150701104040381022540e68100e01a5801884089000d82d82c0b460aa40c481c040b0459117102d44c480c90b0f002600401080d8284010000c500c8048000c550011990640c0c0d8042c5c0d400b501d241030780221543c0c04c0507100a02e00c80d024450194400c07402e080850400c10300c002051204a0443e6801040c0020b103040d5004140c40f900011000399441142080510000c040c010034420369000d1641143d010174000594900d04021064121201581e45 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 372069946 1250 372068696 372068699
    0x306060d020907091809020a090c1e1b0803090105060a0e070e0301090f060203070906090e06040b030307050115080d0c050c0d23030909011d010510110f0607031401080601 75
    0x1d1100190380100f0f01070404c1140d038404a1101441d90074040710012108001c00e00150314010011151040d0b80100041c51034120328440041d00700802c00c00c03050081748030030701001e102501959002406107600400181200d510740c01c03c843c11019501071102d00008220700d58422051080d8503040b80145108002100300241046100320b090141440020340007007000700060791429114034244100f143e0b800d4022080110882e408890072001300501e00d882c0d00518604509150030301e5025001c24015602c07810090b880da10304100301e03500c10364004000c0103c04030340c181410750f060050240e49554021290781c02caa40d4420700281c101c213078010020b0201030000c90204000c90400a004941d4100040d04443d000307040268107610300c950040145541d00071400422246180c1608020080d45030b0451451007030410b010500c0c15601c2c140c41c1e408600c0e22041056801441d404903041d018841c8407200c0b1a0b41001084580c0940043d031400d0105000c00403000c22080c409001d048002c0e03105d80c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 372071196 1250 372069946 372069949
    0x2805090606040f0e0f01020403030305060114042c150103050603030c06130c03020303040e06040b01050a0804030c02040e010f0e010b040203091c1701080d0e030303100b2101080604060b0306060d02 86
    0x440070b0155110703c001882252011591300340b100003600b50074503950120b020001d150309401020303808402440c080d00043d0840d6481c00039070080317001d064840c148401d610f206141d00d0281400d0f0304c820340605840d0ba80b0306901c410f005110030010460000f4141070104882e0b040010980300c04010480280c4119a01c1c0c0004101194035903400750764007100e0040003c0507883c10300061025180d550295140c0d40f414406100582d18000292410010304110085106a002410f0b9810507814500040f0803011400010050010010592015440c2520541c182e14096004401c2d20302c12a000b0f01009618404000c200c1c002250072520300d13000041c03660600c070700f0f00d010890814601d0401d4680e402082c0b0321440d02000c2604502c1080c1c0c854100e030208140c00100c1490712000440c000c0d442c600d450040360903400c40520980340c40b08400304640d0f0f98040004161140829008003400e819039451005503034a0704155403d44460b45001e5140c0c0081c140401d00703610038a40540481241c010650 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 372072446 1250 372071196 372071201
    0xc040308030c0708031e010e010302090c030702120d09020301050c070f23030a0e0f2e020307060e060402150306010c2d12090605130b21280509060604 66
    0x1d1182c00c4a10b020000707500062050302c00307540203100c000390750100403120030001ea0f500c00301038001c403c4440c0c0c08001080140c1d1040c410b903610600d14131500c3c3c4c49440c0c40005a1424554112226030b540011407040d4070200ba560000c0c401d107008500034000c41d160400d00824178425918003825219038854040041401419281030060300d04190490b0400d66608450458114000c0180011418080d00340549801c90304031959840031507515104404a101c103840402480c82d00041c00325a203101019200d00900694131000e0300200305004520001e1a02c1da1a02c408031000c0380309100c0584299501821102601d20880381030316840c0f50800b40c0d8481c04080c010755802c0b02c0003150000044400d42d10001041004103129429004407461400400741120305541c02001c1009010300110f80d600c1e501310800f904541218040c5613603502d00384001c20808034002d07141d0854100c0d850600101e400c560440c03884d040c010196007212007005143d481c081e11416525000140d2100703011036464070b01a03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 372073696 1250 372072446 372072451
    0x3100c0215040507030201031b1e0c0f0516080d1209080d0e07180c140d11030106051801030908030411060c0f010b100e011704081b030c0c0105030c04030803 69
    0x3801100c54403859a0001200c03164111411a1560003550b410411942c141c042c001001e03a061500744440401102e000301070b075040c01640e5045e100c1405400c001d01c0d019043c4000002d401c0b2500000c042030340d00300b0569414890721403031251003828030002019280071a4154560f031041d80c0d04622442c0740d00078280a40042a01650218030800030280d00304590b00c2460100c41924020301603040c54541484241c40c200580f0000b05401d20801504082d4003d5a45030b03d51501d50312070362a480c9020500303005042d200110508000000000b0510503040030191440c4404210781c10200c4540704011003da6900700070040c0380807401c0c400b00307002640f4010101240c01d8044c0c09079041c40e0700b0362141840e0000c01340d910605a595610003501034109030003500c0d01c407605410301c10550205840028840301e0403951900350020740d000403608212180c0c00b02c400400401480c82c513184214224641c695100c0070740c018880c40348092619595020743c1c1900d115a02040850381082c1c5140c0320701c509035100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 372074946 1250 372073696 372073721
    0x307120203042606071404210f03110709060e0109050a150f1712122d240303090d0c0e0a020405150f0d020702011803081e0304020310 59
    0x2404041051004111a160083c24040c2500c844110f549400f038200700c1c000e040d500c20812201010b5100006103070445003118501c80d1002c1015400156a109039005114001c0031209180b2206080c980d1120304641558024401c1e00e81e070350703510031106003240c50501c6010080780b0008010821407100b5800036621038419840862900700d01842c1101c20381c07482d041440458444841401148054031035103005450755401000280c1d400001002c1c01e0191442c0c1c00303068a00d9000040b0941454200701030300e803152544032072105e02c0554450281001c00c440c000c511850300e86505642403041821001c030400041d000d0b40c984900102880101040040e0a44038501250701c002400c03c89030301014031410722a4001030310303141081c040090a51120103a209144014015000e40c414244100c3d801500c21080c0140d44880610040c0d0303c018490081c0f4840c00d140071000814010060020311180c0143c0241480d480c00c40381c1c040740b543c0000d0701c1c0a90554007160250702400101c1e4080c8c41c001302e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 372076196 1250 372074946 372074953
    0x1030b0105120403021c05270a0308032d040c0612090c0e06030d050a0210090f050d0305040302070815010510030e0318030111030606070210030f020c24010803071202 73
    0x1c0c04100e02d15408181e9080300164000c20b403a0702650940401d6507150b903203a15269190022010000406d1140100f40d421641d00036400511181c0e164444c5500840d44818403540700e00d880040902944100107411080407444200c1090740c1c100840d19504c100ea00010f0a1003160814100301c1c0c000d003040904105a9a4030b403100400700c0c500c1c194290003054040c503080070b90f141c0141814100082c101c1140107000302400407801c02c42c1c011542d1a2003051740300c40007070a60313118100710014403203002d1b02500c180100140d00721013582c036800c40c7e8403440c029002c0300c0d42c02d941c80b0318142d6154020500c80b11405001c0b001171045180601003000340107540d11380412404405a41c040c01c40c3d014405841c08000c000f40c043c285030400780140125203a20796180e43c00c6251040100701640324241c0c00901c40d004211440e11154081d0307000b2221000d0741c0c50215100d0700141e0015950328142c0248840d01a810000c40940301c92005885060710001c0020b1070134140c0c0c40c1d9030b0b003000078100d1114109500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 372077446 1250 372076196 372076207
    0x503031614071202030d0504061b03031503030309030e1009030201030203132102070f0f05121f0f0e0307080702010810030b1915031106090103020d15050a060c03080601030b0105 78
    0x1a030801800c4040c3c0340b501500e201840c031902c1014071309611003410b0014010240001c02c2001d80040d40c00b07040c0c51140c5070510026000d440c08800801c2d14442c42d0b240c14610001c0442415815444040243d11a46610007804002c0c03081264000c2040e00e4403001a070510030500045d4440d801550300985a030b1401c0007404000c1d6543c40c0007504000403100740a000203041d40040d9410044080200b200b200d030760310181d0502440d6400304080d8005c0c3e50103540d5101c8800300b5034004000343d072100314001c120000d41710041e40b00b8201070201c090000b1341031800c144400c03102182c0801142c1c1000d5010b90100e01c2c2150fa540103440c110030013010302e0000c00d0601d0000021903054044036100300d00c0041e03030600642a0001c800d0403070715038211601000402180500c0010265510000060030481e603d646440c3c0c041c00403004ac0c0314103010080c0503420022410791103414840007038240d0710b04449100c007a5407285000c0300c090020605c0034000070380c00000f241641d4026402290300d10b0040c03600d1840c00d07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 372078696 1250 372077446 372077483
    0x40b06041205061b04060206010506160b0c03010f0501110601090b1302030406020d0501090b0d1416030f02011103030c0336060f010b16060b03010204080a260405030316 74
    0x12541070105031495048103007000310560312141c0d0b6038840c000c2860054101810020020360b501c205008540c000d0324005900c1c0e142c04010144260120b5100341120198a401e840d0f000a40c1c20a219600310a0b41d24900403400b90300407040594400080ba00801c0b15170301e4901010050316103840e040340c1018510008801104490008501c0782d401194056507407264000b00404a50050b40004e0103d0318241c828991a644e001c0a0b02c0e1643c2c10014001c800303504400b400e41040300c0031585290b03401000f0000001c00551904219855000340c0340d000800c1092500e031602c901c801c0301d050000100810004032101c1c00750301800444100c4150f10b00c00b180c00f41007000003062400c03c40202075408901003103281c12040c52607070701400c2c8071064281808448090b61400c030548480040c45152187c45481301ea850940c10340300200150802c0301c4100a00303080004101c08400741c0318030700011040480103001a1541120211103014009515015503450090740e0281100310403030708100020700d6a02078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 372079946 1250 372078696 372078719
    0x1e0d020c030705031213030c0b190c02060a0f06060f03020c010b0604031a160e011209050a12030c091805040204140a0b0a090b06030115051201030c051002011a040b0604 74
    0x52030f10507401181d84581c0300d113403000381c244000c0c01d80d440700606004100029030b00503440701100f54040d141000e56103810550700c090040e0200ca4090f03032403034100074100e1550300040d4603005036692202049094100c04245d01a070b14640680004200d0b885100e5071018441e07802840700d1917108000040d01c4030460001880c95210350300c00e64504909a480c005c00d810300d06501500109901c07621204004034020183c00380600c1c9120368188103250b108440c0518032500940303035480c0e0060a0326000075042c90f103408503245030451900001c0c82c1001035880d00f0b000380b0300841503820310b818905043c0c0e07003801039102811000740126003142d190203004540000385450365006003440d902c0814400000c0081c09030362242c9908c850b2401c0d0030400148269150b1000301e1741950581d003580309450b10306250585d154401c207850b00000b0001840000b00b841514000d41c001d0715001c40b15450240314002d8201d00b81c0340c12034600d06400c0034100d950205803034254040c90701c0078000380c400d038103165903172190012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 372081196 1250 372079946 372079957
    0x80409051302030d02011a060c03120c0a090807060c061e06080c01111513030c050d0503010302090903071205220b0a02063102130c09030302060c1e0d020c03 69
    0x76504180e4184085203030a0292442010191000b04106004118014068010101e640b800741c072002a070300e240e41d20706108603090721035041d01503a42410400b9684460b0340c0410040c00c00a05007503c0800c0c0e508011a40c841140c445640348020a0000c0d00d44030028241c1088050350f00103018802c0c90005407900506008240140180c880440c1200000d0542d13414072088554603009001c120b001e000340200a00c0d01322031601d07402c088260f00d41c40c054a102400c4038015205108542c8112600c591000c000c50580c0d00c292812040ca4480d820129541e000e130303e20040c038078010004100e901600c07520260141c1400c03a0400c0200034000030101402d2071107070b040030003102d40000e000e900040e010040f0700d8100110752a00c803544010044400512015401042d01c203c1c280c100c01c10a40d0742d0100250340c1503031230a0341001420103e51002c3c0000e441c91001b1405070060070001980701008105840c552841c4030440d000c000c1849a500d401c50b072100c030990b0b071013660903c405450480204060034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 372082446 1250 372081196 372081211
    0x180f09020307050d2309120711030c19031a0103050604020f042403050c0312070308270303060427030305101e09150513020304030309050d030c030e01020702180408040905 75
    0x380105e08071351400d0a04c040081600c0c0f010381c4410805410070b04880c0885000ca50410181d02c071084407440001c0c00e1200c4e56542c1a800422008401100c4001660300c80840c4d100740c207880c500c28107240020440d070303000b440054215005180094050706210b0b040402000005100040c00d1104c42ea110903425010012020305552024081c410007804120041d0340d02c9c0206d00800091440d0008403c0b035100349440102040507601c0440d00382c6401c030124200e0092a603480440c02c50060349807a95980007100c3e054812410407421151566280c40c1d402c0240c4000310703403e03407007480984040e0041c280190281d0300f50380000340c00198072000b0b55070b04120120200c07030004140f454138000a054480c8501d40107400000c0c140304120540e05c20540b191107031859078002d0b80b20f90303d500701a4000c010001018140340904005042059410303031001c4907030b02c5c80d5102004910a9030080d0380c05c0380518030340203400095214144824201c0a010141d0107071040c403003146801e440759030f184280c40068030900b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 372083696 1250 372082446 372082481
    0x1050909370e070f0312090b0708180d08041203091a091f0915020c1201060801112502030f0d08100b0c06011e032001180f09020307050d 60
    0x4400c2001c5000b0000c40144034401049a035040401143c01c18089220040c038138002c101502c0070300d6000d444c808001b08807034210261144214100180298442100d104600303411320121482880c02400c036450329600590b210741018100321000c1c100342031541c000e42c00e12015444c0001c940b0711703a20402e01000e902200054031594030300184a503091125003580c5030ba80c00d04e02040c49560b8008090700c22207032101c0f50384601c1c00713134800203906003480e1510a40e088942c40032203085201054201804880d808002040750000481001480f401200d541342044d000001210a0000480d4000c90900380000c4c1526050b009080b0304510342601c2420350b001085d03084081001810020880c440100f800310361007440c0440a0411549500050007548210355269654401d0b030080441c00d00050340d80b103042242d08410300000c0c02d01c601c0440915600003008440660682c82000c00c40008441c265030800740312134105041c003406500010009410030109100f0440d0070aa203010701740d120f00461452 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 372084946 1250 372083696 372083791
    0x17090d1104060e0f04020f040908270d050c120102130306090302060c030f1803090a0f09050a0917091311091219020f0604080d08090c030c01050909 65
    0x5010603120b40380d014115403c0e414041007002401c0d04011a4080d604603925420b04d00d061000400400804401400b03043d40403071a00c00d000041c2c0e030294404c1c0a50241001f008907170808101004180440c0141140c00003200844d9a003000540c4030005034601001508000c1001003515400700c059106507000c0380c440900707030245501440590b4009841003136084c99450702d569200002c82020b488034003202200c03c3d610308485414030694400b284001c1107a440595505054005000c031070181d5a00e2920300070101d52041c1e814031803101640e600c030030f4621420180b2441040c11390090501240c01410545005801c204144104001a0101d1088645400e45a420702046a05142c08008558015074151502d60030707619400d001d071641220000e18604e0603070042a2140210780c071040c41d074400da0100460507604604158899104101190031840a840825588820084200740401c2040210b01c525050032342100e03610a448036020354010311200e002c11031410800f1040010b03200c80484 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 372086196 1250 372084946 372084949
    0x6151e0a020a0309080304062f0d05070204110c0a080a03060f03082110090b04020c0303090d120c050a03091a0405010c031505060f07050f07080a0b09011817090d11 72
    0x3950000d050171000842c03d1a0401801030300007007103d05e00e0100b000564060110340b035600501c2c0782e9103031141011782c2c00e80b02c20300b01301a1a54104680480c480c5060102000d202040c0c4020346149802d008000d00c4200031503290b004041e80914110b5040540b070740f0000c070b0040380c2c2d4503403031000303503c9140140e54030350350349000c01e80d40d000e003c1c082c0003146198003c0c0001658440d02120a507948c07071200080d148101c4002400910581100b180140004000c12074440300114400c01140e2554580340e0401102031150b4040720000d181c0840480c2c014084483c15038403a40c44146482d102d8031b2041000464806026080761044600b04d44680d101c00407a141203a05004801030003c51030f0402d625982082c00103140c5004150000d103030280045010000d000c8100700460003c0300702015940c805031501c0e030898a0309803c42c410741c0d450b44501c012542440c0144503901c114101b45a2200105c0c50940e26043c20110714412106614004e00c900f103204d40e00c0401c03a924442c072601841c100da1b02c4040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 372087446 1250 372086196 372086207
    0x40f020a1d07110a030c08090607141c110304090507140d0b011d03100504030c0803070512071b140f0f0c130606020601033309150506151e0a020a03 65
    0x22180f10f01e42c114855443c0065009900702180641c01134056880b606084d011409a02070150050100c010540c0c003003801520100744008096804c0e10181c0588600e031800380e4554403050501065540204401c01c0442640e80c0125081030880c030301400821003103400b100007500401002c1c0f888a03902e000e10300842d80c000003104050f445031a45260405083c10001c0e440d14120480740c91403076110000101054481c90b02c040311240d0000000b070706c0307080107800101300340c00c02e4410820001c610700210b80b0041c0185031024100a540e0200c28030303003449540e22611100d420031110070500c140380941c0841c43c02480b4a4401c01501401080c00f000c0c0441009440703c10803418810007403404030140144c0b0390210f513050650b03806c914075080003040410b8951581050501c407400c4144624007400e1010740c0d80e00807042540c0114541c405004400000000301c90007940c18651115600821040600f045805001111325502c1d4114409900e114180e03100e034000c100000068210305240c40c101038104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 372088696 1250 372087446 372087467
    0xe0109080606030a060203090313080f010c0e130911040c11060a0c1704150f0506210d110c0d14100203010b0706020c030715052d040f020a1d07 63
    0xc1004024608000010a03240c1074615800b508040e0004002035908000300b04a40750803600d40401c1807140d40c0d03102420b488005030405601e00b942010340d4281c0140c400d07483e581150100a020703c1015882c090070310000e00310400103d64010301410480c00607552442104400c11094982035001c4a005075018100040100070401051606070304400340c6500000107400c500c0801d004400540303883c1410041003004103489040e007410819041088550340d08014000c160a46a000d040038480b091990450350440c02c2074003581c082c0c0ca108502c3c510406400102064182c1070340e04c4c82e8502c1002c616501c141d83c0f0182d401e40c8e42c04039101d00c01581084415090403410300c0440c02c65050801c21070040c440d2150107451560041040720a041081c02100c4010f5071202500c041d6050f0f401d1400058a0704503a8043c0d481506130301145145440c01407185142d5022101c2102545c450340c41c50000f00d0740e42c20507a00148000000b0460045078007035988406d5910004960a01d08042d000b1f000e480038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 372089946 1250 372088696 372088709
    0x30901020f030708040e04031202040f060908030c060a1d0f030406020c01020a12050304150e060601031808030406090f021302180a060503060405093a0813140c100e0109 74
    0x104030f18404100c40005403000c1c1c40c45150090b006031628201254003071100368112015602c005400950064241040011100f0648451046c0366a41800d95101e0281c0441801d80e50404400184822100e0b404004112004501450101c20000b00e8900c2c0c81d1604c560a880d0f0780c0001000d00c038560b010402408101424802016100001d41d81c007070326040d0300e180d10010f021012011404000c0048448903a45020b202c00f04100070050b0303070040d41e402040d1081400719103400390fa01e000c0c1e5a03000c03110341c001ea04110800e14640b07455880c600140322510313042d03e540c0041003006005075110940300306201460320025842d1303042c005030200d140400300c0c01d1034400d0b200380d0b204002d0b0729040002daa07406141281c0c002041d5942c8100c540c149820070342040104141c855125100f4030304030406601c0d403002c06c072040f1000c1d1201a0151806601541c1001e00494420880d1002560501b000f400c008000015154444001004105141c440038402008502c4a520b0b40e10346590240d00c0d440240318 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 372091196 1250 372089946 372089953
    0xa05150903250605090604030e09070212160602030702060a0609021201260708030a080108150412030902040603061b080105060d020901090f170f060103050706260108030901020f 78
    0x20032195040d500d20440035440048105102021409240ca40b519a5416000141488075140c0f01403039644070385044504602241e104825070105051407001c07240b00d50f041c0c1d0002e08600d00c44105070b4216800c04882c0c1c5801c520203900e02800100d40d8005140076001680081405050450b0828281d69464100c00c90130b40c81441214200d0101c544014111495075594419644d0501185000501e204000840c680315241c0001603c120002c001d00001e01c4542d21001c459884e40c0303045403078028424030390050015090100340810345800020404400c2c90600203150780e010790200c0c040c0d8950760702c1520204e55a104520301c44c009115640400985450304031013560600c1d000443c0c501030030039010300e0180c0c0032441c0042a40101203030405007030010491200c141d40c940668016007409824101d803400b491402e0081520005610343c16240d20502800b419801e000080701d149800840c5101407441d2210180d20011840385558007a14103100034690740e203800d41c00649032882100829100b40e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 372092446 1250 372091196 372091201
    0x507231c0807080318010e0705030d0206090d0f090f0602010c030b061e0c07090203010b0c0106050306090d0f1b031205070905150304021f270b031b0c030c0a0515 71
    0x408040c101c40b1510703881144103484c5e481d60400c04841e10b0058114400c4ea41c6091280c640394800002c454003228400c0702162481032154100720b85030386080d6a1031030260700c8040304e00000c0d4003582c100310354000380b458014500ba07522501e05a1800b220f0b0300410150350b5130141c2244080d8907000d035113a0356400340d540610f41002d200d403911141ca0303046101255428085800141c0000a103ca1f50040044607002d5450b03503114560f004a650110b0030700d03041586029000146070501007601449000c1741c0d0003400600c001c445003910000a081203110400c48030301c000c403007186c500c4104195150300030796490300724040703412801044890141c00f0100348080701d07100300655035a12405030003643d1407203c11038480d2503e1010031441e600041c850184820000880e102c85940400400301c80c941c45c0c4400c801c050380b05001c000760f004040c05142d01c808420400540c140604400980040b0b00700021079280031a0b0100403030558001e18000704080c2c02040c1c580f000d00404000499103500245a6032000f030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 372093696 1250 372092446 372092453
    0x70c0614121812220504090206040b090103060e01030302030a0212090f01030e010605090403050c070b0304021011280c0f05061e090405010f03150e060604090507231c 73
    0x64000414120410031101508030040000f401207100d50440c1c6510203480f00d68105803103050a200040c1526010000e0000103024907080c041d10181a030060a05407800b0309104030981d00e0340c8001905818591a00f2001441c018217640701402540a64003070f40c1c480c599074070700a0511050340603854074020107000314041995800d8810060800900380011410740c400300745405010700c0d40c8801d0740000340070700300030030b254000c4002c3c0300c3c1341910001e4580940e10791008000a000689001c0e404c480101c1000c9509400f40380380501000040d400c403160581d503480c0c9c00344480d41c1103495400c01d401c80341c0c400040006442018015020b2603401180d030b14207240206180e4080c422040c8801d21101001903d28046403003159400240507006100c1582c503039220035280582c51204451400c03440e40e01e04451811f40c8100400640e00300085c1400351581e508100141610120503680760003510300004001c0c000c03400ca0683c18040c44486800d81c3c405030b041252007440d00b08045003001080c2e008a001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 372094946 1250 372093696 372093727
    0x18180b0618100510111207140a03171510031b021f020f040909060218010f080a0b010504120c03050610031203110c0a050105151203180d0206070c0614 66
    0x607950282c622560301e04100000b2240074600445e201e225004203003464010504d2a0002d000e003d018400240210b040c035480740d40c0e52020064041d001580f1044007002514103d140c103034203c1d801c200d02c080c113111910b000070010540c80345408003003076882e40d0913078500000342c0b10f542908d60b03540040d040200001c198225212000350421007115030000b4143c0c0c0004010707050310080d003034001003005066150b29140000b58080c1e5880b1442c1080807000303010945c443c04410b2120343c26641c07850400d4a60b80100405060341180b06c0e07040c0101440080b41c801c060702d600040481c02005440b500c1032441c20881c1c00c110f03024103680282200c7c501d040c0003103011070080d203114002c1c614000034081d03905d1007405418042c6c17078015103444c026028920309001054022034080c81c014040c032400000c4500403c05607604406c0f6941035604180f10180a13030404400b1900c820324080d048514520580c1c0c0014525403001d00210390203004ca01091010030741c40301c040202d00c0c00c6004210b00c0c004403038420401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 372096196 1250 372094946 372094949
    0x603032003030f060d0b0903090307230d1103160f06050c0d080919050616030209010f0c1104020708030411010503130f050c0901060e01020c03030405090118180b061810 74
    0x181143c1220214201c1e03142d0f61814100507400909104541c1003083c1400d03103d80c03205000d1032080c03060800200b040e00d440c1c040024110301b03c44421a03c0f2a0ba01d0a202c2c210003d0310b02540c012403078450f080419101880440c041700704c0d4900d004603090802450001005681c0c0045081000c207001c00c080c11000098944060341803403d040c1c640350b071074003e90741c41c2000f400540c00d20034062148540030440000348107400b074042101e4020700000031080403030403401030070b620ba40010a0003507034164640c085d011815415000300c22400c40d1201ca0000b0800342c1c0d1041004480c4003000104000034810001640780c0304542c2464203d28601344940024920600c15001a26240c410709034a420004204500c03801a503010300641140e680d0780002070291103c04400303034094041c440b0340d541d507807038048200da00b51030005080007916420700310a000000c0c3c000106544450b6030f2680f01c24400780724100040100d101300b04800d12490500240040f40c1d040d01c0c55051008140c00501040c80010800b910 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 372097446 1250 372096196 372096211
    0x901050a080a09050a0b0708090d050f0c0f0319080708072307051c02070f0b1b0a0503070f1a0402030606011223070801050a1a0a0302070203060901060303200303 71
    0x8042d031070b41c0c04190024204050020074600c07422402101300701d1241c885500c54072060721070941560b907076540d047c0c0f2130402080d0240000c0040040c080101200c0004d408064140021100454800c0b44680e01c0c42d8403980310640c0b40d21030001c00c4000c0750b41c001c031040d61241c4a803410715800d08000b10302a03c1922184003503a0302c01c440500701e01c02c0e410308405440304903410100f01c400d5860210700e0064001c00054a1500501507110040350790200e42c4031040881d11080070040c0740c9060040c0303096412407421481c0d42d4501440b01010702195040000c0c040950007441030015403200c603d13017814101c1001e455002c800000f0410400581d40c0441c24940c8488203003405801c642c4104491402403400c4814124011450344910228845000c1c50740d1044180f6110910b690340c80c1c41c200040041c1502c074000301d04d01e5100c0745000520140c000740080d50058200942403407030a0340000d0501354100c1e02c5a407181c2d0345000810070316510007614800303840199980d4508544508e00152603100081166 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 372098696 1250 372097446 372097457
    0x140105100f150e0303070606090e0c0d06020a0323010617090a0b0403020717030702120115230d0b06091f030204150b0703020307030807031a010c02030f07080a15020901050a 76
    0x94a41900440403c00072950080c2130380d5441e8032900c3c100004003042d0047c40c101031301e08010000448000034800c1184403005100e00e10f20f01c415525070002e035100b61403200c1056140c20b400d00d2808801c41741c4002030703404085400503560400b0002001c0d004240c550071491210310381402105507000c80c00703050142e0016007042c1c1c07a0f611800e00b0b80c54459598800303004042d0740048800c60070741c0031002d41074540c422200140c44e840d910850b00d00340c800c540040401e1a26105013002250881c03120b1070b11140780030152070082c0c19a68001807042e590b0071001c5d20010400c0041010515001c3c40c4181c0c840c4111081d5440b4800c1200b10307046441c464013000b4001d17507542502070300700148501300a0040601c3d0780d00641e038004500d402512608a484210089040c0102049416000c1e0180b645c00028070111180b8411000b4011182c1d03044441c4240d805024100c011a0781900500c40b040182a00800500050f82140707040300310b90a0880c840b141e46031043c803d0449503a8003004507143e017070280c03429 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 372099946 1250 372098696 372098729
    0x1c0507050702190e0c07150507090e18011401030308092b020109021002010204080706050c0d030203070e03061005010e0103050903030c0705070801090f02040f0b300a140105100f 78
    0x4825540409801030141d130a8200c0c2088003040608004001c610700c5110208084040c0e541a40255032081c2d540c0d1011444400c020f202c00e04220f01d0740d551064480c4444038200c180c4150300360031a43c2c5100400d200d005900c4c01030040c5504200003607040810032008002d15621107690740300308844030904a102405021500c02d01c40d20075080080d02c150010710261040b001c100d0003034002d43c000c1c071130942e00340070340e49000804e20702681c04c0c1c411881c00e1401030404c09d034036240d0032402540020010f5040c0100442131134055242002aa8815002d0710b0b00841c14a0a01d4000741502145285080c101801d0070b0400c014102d021007602d4200341c001c10400e840c1d035141c0c2342c56800c250300c0d900300450179840d00c01424207010034800d090310b4446c000c0d58100318950b00c180c010f0003514100010213400c07035044c0740c00b0000300080380384000115280072540a441b1003071002442c100949050f050b940000302d08080f40c1c1101c028410560001e6185d8010705410303140176000703006454644a03501c4c00182a440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 372101196 1250 372099946 372099979
    0xe0c070c14280816080606090c0708030402040609020d06062c1e090a020d0507090b0306090403090f030b0108100212070804170301060c0c08010c02030706020304050102040f03081c0507050702 84
    0x142c0300050400c18040d030305103040c04aaa1500340d0754a200302c5005101d0780000c00c446007042c0015900410507188803500c2c004003901c034401c0c00d900c040e00498219690f000001200e041ca40b000d001c0220401c2000b1070b00a01d000001402002580b0029001d41542c00b00404804407002d0241c01c180c4099070180007049688480300e02c0080340c01c1010340c01c040184c0c100071700b0121b25402010302c0c88a00404005c42d458014040340c038a411805000460300c000c0010a13040d1400700d042680c018440e15201011036100e02e0701c0094002c01d54412030b046000c440c01800b03025001c1c0701108018424820460801080481c49015410054012024405110702203410300030030307240600009944204403692540e50b03c030300030001d0742143c50648400c081d1100c04501c0c60418014503240c00202d0303004609042143d11a90025403021f081120150b50800c000a512001da09100b4003c500505501d42c0391120341e40030150036814010500403140c80d000400140940003029150784d145c055906020700c040401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 372102446 1250 372101196 372101269
    0x1103070e040905010e060c070b011d040308130501020c010209090606190c05102a030e030d2406050403140c030d080606161209060509060406050a090e0c070c14 70
    0x42517449078000e081c10040c0c1c68604c0d000800c582c52040341202400e81e0390740492810031404486c002c902c10b800302c000c24086849810031a41001d8a80d440c16800100c0da6211030890f4403d001451050350046411030142c588843c041d0b921040984400389032900d080e442d8002d0442022007042171041103450704080c01801c00c8040400358807508100102100003401c10303001200c0850040034001c00b00f0030703114880d219014035104001070310029403c003841c01500c5005001c04205103541381e5205a480b03031030007044010307040c01080c81d41c84040e695805c41c244002d6115043c82e001d0440c0d4801c0c00b003009540c8001816030010320b024582005651510300001e685403140b40d00030303101840c00c510f0034020f0110407203000142d2a03254407211001035446c0340913280d6026040541d0761110381440b041100c1030242004001e64015403a00d8a841d07a00d51510590900003078441c4101c141d000304910f41044520405003028105440004400c00280e03070001c1c4e40c140d10342e08408245e404464100070303501e490342c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 372103696 1250 372102446 372102461
    0xc03062e0513270c03060c02030910031d01060e01061b030203180604090c0f030c09081f060305031314060405060a12060824060909060c0307050f04090f1103070e04090501 75
    0xf10407544181d120b007072681c4240c0b840d000c1a15410b140450002e400c60002007140d001e071202504415072901d0041003a0f00800d2440241442461003840074902128284a07240150031040400b8801d54140303100200020740c800c40c3c007000c02d204030094802107a000402d07111110707040d00584440030212801308505000c2e031740c001d4503c00d081c42c1c642003030181c00400040346c1101c0740c2c0d0100726010141100b00d422403e140b00309101a00001c1c01031103501c0c407801c603540e00401d007004d01240696032079450b00e1859114109220305205001402c0c8820344003000d02c1000150b0494010341040d05200014045109551700f100c1482202c100303545508107582c100800418200303003559195902041d40c696101103020760320021b5041500043c00d1880d01c8440a8040c1500000600711542c900300581e40ca90700140041d411300101744608602c0036034280040020701801900850244080c24100c0160303076000040255041091080144590f0f011040c20003c1303208480105518442e070030402d00600e00b1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 372104946 1250 372103696 372103751
    0x3120c09041812080f010b120408070803070903110103090b06100c12050a090801020301120f03020106150e04143c0a0203040507060306080606060c0c03062e0513 71
    0x1c2d95000e105000c405440b80004440f0f039110700c03c1680c2c8502da01148104240900440090280001410381c0703615007a181d400ba00c02d484c2c0910b8803203070f91074903d040e820864000002860a160920410402404c146074944080c2010b008602c4681c1c0c0d03030704101c100100501e00641c05003800e6121140704070850b04c032454220184100d04032514000034030603808411118007144814100045100052080302d0480b02c4442200b00101c2440c0d8448410101a50007541107648400000c83c2d07520000d0300c0c50b0f0303a1043d50741300e0132071401c41281800143e8480008020b06900810b0410510a038500d0b403120308184072100e11303200403001c0c550308203458034100c4424821681e01d10811031561201d030300450040b4001c9007111174413170750f030b600c00c03400c1d1902c0d80215200b0b038001d0b101150481c185100a40010711a84065030160714101000ca850000708803107080e030b025080000b040c00345000c80c1c01013100003200c0c2c101000c030742d0801001c110b441200c008840e901980e2601e064ad40010181031880884e0342 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 372106196 1250 372104946 372104981
    0x10c060c050a02070b09030309040915020c101103060a03080306040e03040f08071a0703051303020423010906030b161707020d0212090112050603010f0c05180303120c0904 75
    0x30362035401001c50700300c244240090701c500f6501081e150b50720000d0b00c03103559005000b1850000c01b20b06210103040c0c2d80208507140080140500c03180c0c5118006005109a06401080d20301c40800300141560001407002d000443c080003405041e0322031400200541c0d400811040d0b0782e0300c0d8100440d004040c46d404420213404089004170b4010349200000c02140c007040100c4103003588900091500e440442200c49040c2d01c01c006a00009000380045e2007003b82600c101c800003952500840d082d1640c3c1c407508500c500c00410380c25203142140d0086805843d014408000641c2550ba980c20500301c080c0080050308401010200c038540310b00c14010012102ca605008103007003803040603582d141600080c5002d0b0141210309048104000103031000420705a49084482141544c6d003401420090000b5800d0f54039424194030001881c044c2c9446c280080c1c0d00d655684e48410304528032070003a151380c0da2003500b04000c103c1d400d0800f001001d40250b501e40c01c82d59200c407400000f07002414240c950340b910302e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 372107446 1250 372106196 372106211
    0x10b40090c0e01060503010e150607020d0809040f051b0c07080d050703030f0c08041101020f1e010b09130209070c020a030c14040506100e0a050d0b0702210307080402010c06 76
    0xd03250748400100c5106001c10b41450b601c590b4143d406010074010300c22916502c0000400c0c003444c903484480608400743c0210b2402001e80c021a00c0c04400c1b000035200d00b2030000d158030030350030304c1e01c14090846a00642004203082091070780c3c4130391000313000400c801c400204200000305024030240c00101440340440740140a6000081c0c8a9041074030f00750086440c02d4015000c1c80c20303502501511100d03d5503200810f54550781c410320800c0b204c500b1141140300f481090b45038620304001d01000320303c40201c2c10007003504101d640c1c1d003550303002204107014040c02c81c00d10928942148000d5030301c0c3e034121010000c5d42e030b80c01c0040b100b26290300400380d40030303945500000078030400008440070f54040d413079841d81450003d001d001c15103806503007194200200fa81d0301071007240324046d480380c0072100401a400c2c03a50340e400000c0802950f0703001034a080c14210300b40140343d0740400501da007115500b445c481c030003a104207401d0518000100200705002000b80001c04581c40703864486201507001c80d04100310b2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 372108696 1250 372107446 372107453
    0x180b041406100e010e13091536230d05070b0f0f180717030c01180f020f040605030303040b060901060c051b0109030c0602010c02010b4009 61
    0x4100c1696101d0060000c82c50742c22045100c0c1500000e001010b071500c0c0c0040038003205010010039081c401000480c0d446410b800001c1c18840d4140d45503501c101d010902241300922284500c0728100145200c220715080e5408500d214940100d4040e0040000744644000d10310528a000740b00c05400e00d41d0041c1c40642c40070a800c003010384417550091540b500159507210041515900c1070711410314040d9007900080c000c04000203540442e10005c1c058640b8550340300e0400084070040e00300c3d0346007a0804180001ea00c0400d02c10a06d005003000200c0b0300031411030f25840580400b404c00617000701e82d900400e000c50340710b1342c1011009000c0901240e03944c0c40c2c00d0420740703445042510101c1c42002070100004c1e445104407143e030a040d03003000c0501259206c010b4890721054074a606941402003400001020400012010b001850140c0000c554880400310003800c581e403901c0741c1841501101300e03003005a03034054240f40e031812901844001581140042d01001090300000790b01c4207017001c441d01c080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 372109946 1250 372108696 372108731
    0xe0a0b031e1005011505090f060d1e0c02031c020703090f0b030a0b0f0f0402070f020a0b030702010e010c0f080601140c030a0207120b06091e04140c030c0604180b04 72
    0x2d000b00303090401c0aa42c03030f070000305007110351886050005207040c80b0103e06480c5c0200c00310a46440107140a14010101603d0010755101020f030b08200310848040c40481c1c8128007580c0681d81003880510700d02420010f4130206101040a00142240c0c0070480d4010540070300143d1000c1d04088400c80c00701603551038480c030130b5801110802900b43c1800003610cc030382007640c1c080c0350001000b802c43c070f8002d40c0311092100075080f5000036a12443c41700000340150700c42c000b01c0c9014040310000036646c0d103000031000c2d0030344041c1920181241c0c03424216150309544500142c0c20084907145c05041d5440e043e0040f515400c4400c10900e40d0500000c00b44e000b1840040100b0f203a0b00c1c41d4080d503019966070128071150300c10180c000341448801c0b6001030a03034680050455403240000c02c000c4c1d54929040076070040100e0444040716041d02400e02486030140403c40c90701103000c224018480c000541010078a0790080703109034044003802c2c410b0075004255981086003031072000b0740204a451201c034040e198 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 372111196 1250 372109946 372109963
    0x60a0f1a06040b180d0302030a08100e0610171504060603050103080702040c05070501020f0d050105091006030c05070609080d141e06010c020301020c0a0b09070e0a0b031e 75
    0x44051800354503600602100d4525040c020005051509051800d001c0c00354552041800e480d13802165028000d5079612000f82e0342489010707500440d110240700c0c1c009010408060f080b0705407601e03815002c1050f45005101c069024600341d48a0750344000c950070540c1e020042055002ea100104005c204d41281051035526030964211350610000d41d5074182942259401e0001920001003085050091305150308060399130a030618000d80303000c000313440e0f080c220b0704184e00040b61010b0004641500107000d0180601502c000c94059019040018490440c40900c1c4240e1003455103035a40c000c0220301580581d094070350004c10611070682c580c07a01c41020703400b450348010501d1402c150404001e28480d82e0620401c0032030422403501d503001041010221000307200604000250303a007000140c80078000303003100c624054000c100d142c08500d001c44d448000209650800c2d407001004004000030002c196401021016001903151a10300200b800c0041e51383d481813983c240c482c134110421a0000f070964 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 372112446 1250 372111196 372111221
    0x207030e090736170304051306053f070b0706020c0d090f0e0c041d060f01030e071a0702061c05130803010308030a0b040e15100621020c060a 62
    0x8070b0451030343c0d41c014004002c81c15a26800150b08042c00b0025a000e85000c854000804403414940c0e030702c00003101590050301411a45032941010041da00f8244004401e0301c40c4441c14a880014184c800d40c3c41c1c8020301c202c01d4075100100c1c06580d2401c4103205060150041d0802a5580c20280c28840065800300c20802c0032841562000c4401c1c9214400740f40564400b101c07021180c51034540340501b42200540b800c02c2a601c200000034000307152182c201c00d81400c511020070940b40c42020010441000140e49040c5404c24510100403e408103680742941d507001029000e100e060180c00805004040c0001d42219000401c810940554880300b0442501d11700140265a10641c584e8a065004440201840030500041c00001c5890014661003000c4103400601c1e43c010100142c01c0e03c110000750016901b201003100203103440b81d0b0416031f120780d41840c059074407403914a000349613042210340000c2c0e280030034820382540084c9804030380912070501d0480e540f0341808804140100f05604499 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 372113696 1250 372112446 372112487
    0x81f080a1a0105011707031107120e030c1f02011404030e03070803040b0f0c03090a15022407030905031308072409050f010210320108100207030e0907 66
    0x101241d041c54240c0350680d0030694402d440d12108440c120000700010b414481410b0302c540389107808412007005094506d01400241070325039240d03d000352242a80154460003500507880711401d80d10f030098031250a10030802c003c144a643d40c8422401000e52046c0c644001080009220034590f002d4105249020201c3c00d5a1040c1d54941606540e40f01e544144c58040209200c410a9030824501800c0d203110100c0560b440c051000300043d6240b01030b6000310822000130f6080407102641006241c0810015500f4466008200032182c004004011704a40816441b5141281040760500a880d180ba21041c50100025140c00d090750311410240960b00e045004180284116642c44101c80e41c0e402c4143c5035485030b6410300c801c0c40454100c0b400da4070305512802030100c0e80e00581c3e10680e0103a400401a500351200c4007200d407103402106e50300d40f80501c90400d0060249600114907103040c00d02d800e400507076804080c81d0a888803100344003c554088615402c11a155400044c0b0352010003005000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 372114946 1250 372113696 372113723
    0x5091813110a03050606040b010c0f0308160c0203031c02070c171005070e09040809032b05070209070513030c0806090f010204261c050a0f0e06030601081f080a 70
    0x2804502d0080f4031002e0500c0e4017201c0401d110741001d0b481489408010314101a540c0321a407150038000740d104600f100069044400c02490b8407004c0c0e0052543c0920745404c00d40182c2e01d0f00041d944e8000c0a0b03030480c02e80b514138bc2502c43d05450340d0403100700540c000040e00186541e081002800403400e1f1014915000c0c04418000f081000c3c401c491080036140c403995000c424000a10245650041044030350300010000302c009950308000324003604282d0880100490361854103465845140c02d0310b001802424010030f40180d460211855010b0007514000d03450b81d01084001d10401140da0014080320380c10300001c6410b61012a03440e1007100301c0c90454080202c1003003802d080344924032a880800c0307030320740703544000c000c0a420403040401c26104481c1d811469410701803882510b0003000020801c00122020340744d0f000700c01c10b02039510904101484203042c0022803040e21008080b181000061000100703000380080c400070400c0d06000e07800005540b035240c003aa54071702550082d00d4002c6946403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 372116196 1250 372114946 372114949
    0x10324060c0b090706050f130e092103010803041802040b04090204031b0305030409110720030f152205010e070f050a150c051005070906031d0c010509181311 69
    0x109101210081d0b613a07186003400301f0003500c800380c00c900c0f6a10140c0e54407500c0000d03030001060f121409000048054850090a43c403001c40380404420405035280051004004044011056404030ba04850f0720300080da1852054000900c25a0440100001b02190100d07414082d64090000e40b4482c0c01250400c40e50003c0450781160607202c018560392080100784189005038101842c0702441003e007a09000e080d6a40c400e100c002914076065000380e4003920429460704200040300000803030090701e4540e141c40350b40080403100400408410014003500c0d030700c1020a211429683d0307000740003005510750703032000f454440070544610000c40701c207024045010310340007042008842c14580958040e8000c40401d5a41307001c80030059440b4000c00920f605070140038000ca600c55201c0d6601c00c540c0074180b0320b0280c1241d2021108600ca05140940844000c000068030041201c0c00d080080d2940f0382d40e400a0307039249175010031102c0340e1028014444000c209016000485101c1c03101d100a00c1040c0c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 372117446 1250 372116196 372116203
    0x100c05090a060e0f0a03120e011803060c0c050615030c04020c0304031106070b0406020408060703050105031b04110a0302030103060c050a0c031b1a07030509060c09010324060c0b09 79
    0x203503650101ca400c01c1003110702e00a980391502503501400d060b0780f00b84128002005101503500c1030351f001002d645075503601540034904604040c42400c00d10034685002e41c1c0c94000507030301d000052000341d0380c03202c0001660142c40003a039900e41c080101c035854601450b048182c0d85880c0c000502078400c64189200310f02d42402130300d0039500d03590300450816240d134460050001c0750000d01074014404000801c04203032811074451007a4080c0c0800360751107103011102e5107080002000801003610380b4005000c82d170380104408400c2c0324030303051041600d03a45800090003460b81c041c414000440c001505203109030140c01860403240a581e041080c6480b05c2c0c0c09075041c0c815490a10f0000d80c001130a440024042d21096142e08107245a403c1c0009599030b4401091802003000e074007110b070740e9007041003d99041c003440e40c0c4032141c64080c002a003030903040b00b80c1d240280c0c504207041c1912165100d42038004242100c50101201c901c41030000d594103009003440840110035103d151030f01d40003c10022000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 372118696 1250 372117446 372117457
    0x100504110411031e060d021002060708010f03020904080a030b03031813091703071101110d0b2407050c030105040b040212030a0801060c080d11031006110a030804030903050a05100c05 80
    0x2000c0860303a510100c0d02494104c04003d00455000d0007400c0504003584515200c01c400e250250010302c0c0d1030a18140c050501001640000d2403096000e50500040c0c0340e040d0703901d40083e072103491113031210107651066002c4c11400d404e940d01480041850490001000105400528141e8200714408045900c41041e20740d0300c0b02c05050326941050024118054200440e80154280b0704000d1007000c40d00c0460030b540041182c2002030b600403421354043d40c04c0b40710f40314030020115485014540704025454000506940040d40c002000c92031405204090180780351540c0e004000300010b14007442c1407c13032180152016805207020302d0340c1d42d03200e51000007240c000802d1601c60460076031802c1c0085550f11410502141c03414405c0c8829000c01a041c081c0400520108054070303100e00d04a90a40915802c82c0d000e1000c105000000d200340070f0000c07824070b05580e01450008031607900c41c02c054500c00000c0e400100b03a4814078a9070002e008000c29070b501c4042914009200342c4547c00700803612030180 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 372119946 1250 372118696 372118711
    0x3180507090f0513030e120703060213170a060506010c0605100815040b0408030415020d3806030a14010e1501030c0f110c0d060603020f040903080c0c10050411041103 73
    0x280d003055004240514403070300700a00c0042c00031076030840ca114258100423041e80100c079a542c010410030f6039560781c3e20301e80b000f80c08a01c0c84801c51286004150f42d480c505910003900b800d55071008128a640329048043c1e1141e0020801e0115061005084c08000c145100b00c050901903c1c407084030300c0d468592480e0007076420510300116a11a901e618510f40d07c05401102c04d0010580403450200e00350016280040c07490f100028246001d884407240c0381c0c41200f0ba05041c0207014820118548541c224103008001a02c107107480e81d40c1c030304c1407400416505000081c080c07841800015400d021294803446604202c0d005c00c000c4003490015425141914210000311f4000e100340002c003480f802020510400400850340220012004251703d00d40c43e400c151030064455005009600700b14a60381c81d0080281c4040144e4002514014000d03000a041c0709642300c4002138502d40604100100c55030188290010000742c01d00d0f14194203101c203034102c1580140e05101a501a0380c40c0d0005580c400c011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 372121196 1250 372119946 372119971
    0xd05031b2106010c2306060301020f04180b030a12030b0303030f181c26071e030204150806120105010311060a09081203011e050102190303180507090f05 67
    0xc50a110301c0e00400510503810400074845038004203545003d40003410203440381e80003405041c0f20a0f6810000010501d034000d07070041001c0b0034403e020100322021900c10140c526083e550390711001c130180c140c00030840d45c144500c0c001c860074801d41030b0300c4100410060f00c040080d8080c050501d6180d0004035034030001610500005001911018030140070103219109441d00c000c40d9440d140891f401c804107160001300031b4491180341030001d40442c400c4040c0b151103002e107440c1420000701120121521042a0102e0101d80c882c010b00a8041d0b4014003030181c2c01b6100347c41c0f1408010680d5204684e07140c4680345285403085030910601c100d80c107a0740c01144c20680204131405112196121200fa2020403080c40c0c2c0c00180c045050003100c01d030b1400314254903600e514025480203021aa130401c0203285410132010400c903a0001a00c0014801e08401c01608180508054008041c001c031010709411250007401e007040004070b20b60054640780740c07041101c02d03d0101c003142143d1003112041d45800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 372122302 1106 372121196 372121237
    0x90109051e060d030c03180909110405060904020f0a08010906020d0b03150106081902070507030506070c08090402070503041d0a0b0609100f030204080d05031b 70
    0x1e40640005a05080c21400903550f810f007040c1c01010301031829040c0c410107010345490090b010b000b041280c00c3d242ea030703c0ca4a02034911140c08940c0c804041402001e945080c0c0701d80da000300350203052846940d450f0703400c0c06558000034420756404100c2c2d040008402d4002d008030045c0a100c0c11003d40c0301c1c0d100c040c0c280207440c629800b0500c0b0760060b010851086907050f4040d411100545000321030394885d41004065101e4048080744050300005860701403140025612040300c1c85401114266600d0900071141c15180500041c00b00c44200404040c500e0704da009400f02070301440c02d0b6031a05541e90a4881301026000382e40d03100c4a45101081070244a0340f14880345403906a4881e40380c10305420028019585554051051000d1020440b0b0303103501c2981510050446803048a90703072503e40c0c030058210f070812511140c2c6090315480440d041501340b010384881403000c60701e824214 = true := by decide +kernel

theorem cover : BRFrame.Cov 371942446 372122302 := by
  have h0 := BRFrame.cov_init 371942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 371942446 ≤ n) (h2 : n < 372122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
