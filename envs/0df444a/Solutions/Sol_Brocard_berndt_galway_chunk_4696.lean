-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4696
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:26:50.345598+00:00
-- url     : https://prove2.me/submissions/115a8b27-dea8-4f76-b97e-59219779abfb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 844424460 ≤ n < 844604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 844425710 1250 844424460 844424489
    0x10507080901080411031b0102150c0a051e16021c0c050609040f0513052b030f0f090b16080c030402062503090311011e0302030c0903030c07050a 64
    0x280d0385011401094485410026801d00050420503958402888080c0c020704480c804c1400074016010300003c080f00c5401402507426098440c0d2000200074050f0841a24160400001e410f00b00c4454121000400081c9000b040c0b0580c802c804100900e45407200d903a560000d68024014440460000d1020440305401e8401074400310700709011000c1034902c2240d844c0e6480da1500001000340031802c00040c0c24604d40303001d1100b581743c4103038180788070362040c001d41d00c100315034410700215400700304405c40c810007441080208051003640440440d016440002440c0d01440040004540380424100c8144494409001211420b80c02680600c54640781c045040d1038000d2044805000c0078000070b019010125a2a0410310316410301c83d0124441410b8130606162410020801040d80c4002e0f54000d4040d40d00400551049070184207030b400421846582c8000c02e94110002e500003400e09510711070904c0764034410381c0d050004115180100000300780a40c20401009180d040a40c0001650011070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 844426960 1250 844425710 844425713
    0x1a01110d0c14100f06170d020c190315050f01080d05070f050a020d050c1804051e0c040f0e0601090b010212160206030405010906051012022404081b010507 68
    0x446281e49541c2e00114140281c107020b10400e103003502090300410074509004000069500a0b840001151003100c91040d0b40802c48901075220042d142020300146c12400d09000142010080400c2c1c0119003074840c1c80e1155261542e00d849140c00031002c01c01070300c4800388010502c0900780c1c02d000d800c4003c0a003ca107061024040e007548500c0000800b4901c00004440510100340120020290041c29400680f03406262941c2c81d06c0300d0940062007248400707034901d010344440d20200d01c65a4018000c100342e003945001314001940a1480071700c144507003048a4000d803900d00501241f00300e40d01c404107400302440c50301c17410080c0582140c2e00c1d0514000c164070050b80c0c0040d0007024030840c074003d56a200e10030110241146c0d40481d002c1d4008d10700105000c00c0040540c080d030303640c0d809801e040100b500e4035603000306a11598030555134016040c000100262500c50049100b2a141507411890414969402c80b5250015403108003180c00c540e5920701e84484401e1503500c00102407030203d140c000309 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 844428210 1250 844426960 844426967
    0x1090b010f020f1e074101123c0e0604020a03241b17190c120f06170313090b24130f0f0302040203070507061a01110d 52
    0x401c1c040001c0d0302003140881c0e0070402400480041c0c91065031a4a402c03080444d02c010380944c4400035250380000401c02c01c440c1b10a44040f02441c101603445000c1c450055010700d0184c102c80c020b030300441c1c581110303180b8102e1144048042035204a101041446000313807049003281c074005050300e500d07041101040b00590780e84400e80c00317032075200354240707048500a2440c525100500d0f080302c0f0345916003200301c491491440e048a44945861303a50b0407400c0821090001c24078015521b448110100c0c4440018110700c81d00b02d101c2600c407a04d0541c5d000031001042d0810741e894400352629280e82c50009101c44400f800e465260540f0f41c0e4001c40c6495105101c0c940140c000d031040464896540d0390380c00090741c54902c0711014811240b044008120f02c0800b103c0c4650186511110707988081030b0010301031001c4845481141c041d80d000710303001807554003030101961008040d542008000c05c071150000c0c0c20340c81495078100d600c410385000b00c00290005090016451440380d42ca500c4400003070074090f803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 844429460 1250 844428210 844428223
    0xa0c0804020f0904030c05060405030301030c1e05130902150d060806070c030f050909041a1503060406020f0405130204031b140d02010519020102030405010605150720060301090b010f020f 82
    0x2043d03466a2090790350342800c0f940c04140844c02002c0f4011401400b081c4000000914145e90107105201c1d06113035210301c0000710344100d00c0010310b00300941d2801c0040e0305d800c900c15600c1b44900740d0040f80c1c8203e40d034001048441503407410301e4103610100f084100c40c2c44a1140f20040c00c8000000e00c0d090a21640140c00440e500d48003c04000c409003286180601c1503044d151110001f0308485844d00b4a441c203100d00500d803480e21252450340800184641c10032502c580c6580b203028016000da9141c07911840c001e5842190685100c000421002aa548800010700c0518041d5400183c40f01d0542c070b4903800c52903028100403402d2450071014001c10a4581c00319429003401c4078602c2000f04948016100340c022400c44403e94001401340e46081501074000710b2196218000801203d6203c00802808082d0ba401e8803c001c03a080c84510b00145a404542406050341424800c03d00c1c0a800000d4153340240c1103845800d8581118401139600303c190321607100070500150840ca42d5503000b642d0f40d00d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 844430710 1250 844429460 844429489
    0x70f03230312040311010b010503010b0a1805060403030f0801090605090c0c121602090a090b0c0703090b0d0b04050a050408090d0602070f12020f010b030304060c02270a0c080402 78
    0x89404030220800d04000701d030350b54521400424090b15280c100a020b08904454144840d400d00c1d8040d071a5600c60b80489060395402002d00d4101100510101c45c803288688542040601601003c507071a03035840041c00c002d6200390f49400e0a052400d10090840e401030323100d030000c942405824046c0d0782c1d640c0035490f801a115440c00da260055501c81c02d1070111403490403074465400040100c0c803000d0941c018840701e8020382d001c030b06640300c01104008854128001030b21110542d00416010003c80d401451041d0091410803549a11080e44400c0d69100884822240d69156241800760805001d52030b03001000a0042040b4070301a220a0f4083c85000c1c3c07c144a004c0c2900900208551039040d662003582050115040000501d040c1c540b4000d1808188090300c00c0801c108420304e41402501c0d4240405000341d0305062500c8400d581d000030404040ba80305400403007200708122000e0041c04003030050a0f441c0301e07500b060000c403012180e13040c500c81f04010a4604010250f102d14110b0b01408 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 844431960 1250 844430710 844430753
    0x30c06110d08130c24020c03060106030c05040806070315060e090105040c110102070605060f09090c09060a0b13030606060906080415110406021b0a0e041403040b0a030e070f03 77
    0x80d80c410010483c0c08034141e000074004104954003003100130084031180c080c2c00205030400690302901e84242e0b035480180c411140d150784103400601242e48640c00c4907810384c7c014200103007170540300c0e468035081180841e0101c001966810203c071030b888a00c40500010907540c107194050407060404122000c005016581c0525254081c0c088030078400c0c1886422010220300840d20740200d45401400b601040c1e41403803050380c014284131150700e0142d8509004440c3d2200500c01030170402c06218a01c07100401007980204104800140c1410a1008010020001e03400c450300c9400d510700a01120100c2d000f000400000c0c02d01401075507000303040c0e1134025804c01840807050054584402c040e05c0c0070300a22120360b0b40402c0c00501d140d00018000c0340f441c00d00c3c0c1002d104085040521441040034450746080c0302110002c0360204040700e1510500e445445c05032031506844154041c80d0f0b0b400050140006951404201c000a4081c04100301615117444007101440c0745488a40b6545485651513014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 844433210 1250 844431960 844431977
    0x11060f1005030d031415360a090c06021f02131a031b03131104061e051305070e01050d06090c050c15010b181c0c030c06110d 55
    0x82255011103401040014111007698824850040c003410900605201c000351180124400c0c41240d003580c0c455182c00340848001c0b10100c1d20680000a85081c1c404c03242802000a10022402c11a070b24400c0c0844a40499030058616000248550690201c2d0454000b107103030403000854100201c0b60441420b07405070b219018001c0703614401c0c1c11944400800c21000c03142d80941034084001d5407150110f0882c0780d81420a65492510502c800c4a00c8a600c0e10642c03881c4000500704503420240c0da030080c1c00021900d49030540b402c00c15001c03250303801c1c0746642d83c00704200d9854500c00141d074400d0321240c20302960a20300805442c4030245402c25040c07020200300c046800c0c5260740000000d00f1a080180484051540058255400f000703208000740101c1107100d2044a0503441c1c14120307804c05101034544200c4454001640d9040782d990f95014501c0340c0b20380341985c2c040d0007440c2114000c1e607031382d00d40e54030b1403820b452500d41c258051020300c01c0e444000004c81c400803601200000e400d0801c1a038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 844434460 1250 844433210 844433221
    0x141204170c0a141207060c032609011a04020702180408071b051003021215030a1430030601030507110118050c0a031e170c0f0d11060f 59
    0x400e00038440c0700703401c01e418510004104080c044000448181500e0040c26000c60300b402c50348a0100f4080c600200304480b2500002030b1040f480c0280500d030720050200c1c60300c0d500440a410560690301b04445a4681d0118402944010700c0101c48a20460f011850318101e5030128155041ea40708964004d000320000505000d041411a042140e009040384103224414146880e2a0700601a01c0d000d04c25a07019501554013078800c90b50290050070210343e40355103a11403441c80303c00702880d050701343c0075044000c0f000400840c0c103401480345042c0035280d400050740c90b00c10070b400611a159107090450b40031201c04a41241181d401001c2031030042081c1d0f5514205580006111a01041d550b113461401001e0451040410101510071426a04016440000c20101003418000945040f84018003050503c1010070303000e90701442041040b0050202000c0344003a60065170f44a405a0040c01d0880118002401103501042c0b450170f0283e0403074000801b02c1c1d903a42c0c00a2202109241c0f100100350b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 844435710 1250 844434460 844434463
    0x4080705212407170a0b03070801020403061d03250c031406040203011b020c060c0f06070c140303190b01022d010515150a0c0b01030c0314120417 64
    0x748000c0c2a202114032682d64041400156806918050391500041002c00ea045200d107a20002095001c5100e03400c80d1aa042084020902083c15560600c180c101c0060b40042c203002070002540140000201c070010508000a40c01101500443c103400401040d00011500d13020581700c0c01b40e00c001c144503012140791079102d078001e1340c00140c01040c0140e1510038050340001d51500c1240300303a00903c4941a010310401110f403d12000c840980c01c05a010b15041c00d00e28050321a42810908681940038000c40d00d0f0701380b00054406000050000101c0e01c14841002d0180036001055002145035251202c90854040090301c490030300c80780c6030400092268401c12404a0103521400300900182c10342c407506004540b0400e20310119402c00000445400440f8540c0200550103000c10f0012642a0140758450b803002c1c10203010700c8224072145000c200300c0d01e2114043c5120ba04480344a034110708081132040c0403810840c5856220401580100c00c19100340c40172261103410a09440c190f0310300c81e5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 844436960 1250 844435710 844435759
    0x60103030f0e09041101031b02060c0c070f080307030f0203092b0b0a1b09031205030c1612080f070e0906130e031803030307050a050a111c03050a0204080705 69
    0x16512203401d1013030205100d100c082e2003200000980741004200900c2502c0c80408204145900c09038001c440003a50060032400140f181c10320420646e1821500c1d0100318226005581000205910120741d800405400c01454001c0808a0005504040000c800201d800b0075160a0310a044240c2045c85091902c008aa40c60310350f2112a0210301c1c076000340f0041c000e04c4200035050302000380042c1080b5680c010304440c41501e401407800190200da003c810f503040e0b4030140a00503030b100104440c100052080d03590300c1c891071081d0701e0031001c111240340c001c1a9440180c40c00030400da4a00600c83c04541040d511192801c0c00e580c43d41b0523595000028808007120b980070484030f802c00270241d60030717040440100703c001403181180d020010007005155503404110740040200d03104103e1406c0e0f10f80140094500b001803407074161080300100e01002c0c01c10070800401d20f8041c440313480b042803a940500038260300503109002181000e01d032803a05a603851161045500410701c410320600e03400e01d03d42c0c6030f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 844438210 1250 844436960 844436987
    0x1a011d150f0607060c0e040207032712050a03091502190c0f03060501030b07050f03130f140a0302070b2704060b190206060d12030e100c0504090b060c060103030f 71
    0x40f51a481e8508081e0b01501d50f1011610014040d140d605543d880c00b48251340c031168056a4452341ca10001c0d40c60f040c00a03420307203003074140384c10b1007800203003074810f032880f48041e40c0f0400c00b8180c00611407a000c1d002e000c40303400845404071880100c9030301c107500084070200454003800b8210340c48081c4c1052402d1003016041141d070300c858800e01006200040d04414101e920448070b4040307994600c00c0c110343c1c1d030180c00000e1000007000c01c00b0407003d80106000380a000e00a103000d14030b6150b203030f40d61061841540b00e41c00745908000440d005054042c40b03a04010f0542048207440c0c0500ea0552040c0031a840801c038940c180308044140342038460343d0040f00500011600960750b408408502075610b0030005100005106280025541d403d00340b034044001580a403c1c0c3c01c000d94200419000f500013100c0608080c801c14000b0985a4502d005846007241d02c0d446440e83c0301d08040c05034082d0745591540300d006500400405030303128000180c030f504680c0c241c50000c03806c03e5400822200019120340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 844439460 1250 844438210 844438219
    0x2010e010309080f18060405100c1a040b041104050609270111040510050906040e0603031603030f2301030303150f0e010513180b06120106031a011d150f 67
    0x1a00080b0fa00340c400109070510908000c00002100c005c04c0200b0b40c030540c060207410045000085081500648203c2c1d5054442c10b4010548208120064034842040f1400e032400c1c041c607401c2c80107101003c0301c2c0000305c01041d9000c2c0107600c0c1000210300b42c044080c0079035180c1c1c100c28491681204566050003845500784009100f0200b2502040d03120790054043d81d48519441152000380901510444840344400307000e141c14140340c11110140350400600080d01340c042004a6112898191f811508407807003070310f0000380b0b0158441d4039003c440c000f2541003008107156007070340701c03800c034002e41e80341140d9244c580440d6860700c10740200140c03042c6500001389406442c2e404103007a00d000d0200c0b416540f0540350000d132840340c1c03a00ca0707099994000d003108000399102041c202080500c40c485a003d00042c001c5c500c0b403942c1c07001d0542150f8140d40183e8500741110513415802c40303201c000381c0c01016413a04030031480742c015880c10b408500141a40c83c910200310114003290b219510041d2681e50010b1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 844440710 1250 844439460 844439467
    0xb01020c09130221063405040308030a05010e0912190c15050a0b040908160602040b04090b1203070317090a02090f090c01051e070c091b181202010e01030908 69
    0x104140110082c0400844a038001c01001405401002c00f1006c0d0003030000280460151130740c0206441001a03518050800000300130201c045850035001314003601d0b8075100002c01d0b614041c1c103003694403070280200485e6002070700300501284d060360580341190030760f002d0120b03483c5400e402582c90900c400402008409964a03441c2520703074940c00144075410241007441840d00440801c4115026684020b001507414001005100064907441c1c2c4405d100b200014502901c1c0d82c16061590001d41c4010000c0e40c0b01d0461700518180608040c4460001000860038800c141e42c001e06494504048681181c124400150700302d4410040722040d01e8020700294500e0801e030a0665007400225001c1d2072910940090b0f540781d5101e60308840e104c148811003030201c1c8414059000065010142c19034a030341c0311070004110079209101c0c40e042544540e204415111907c43c001c1c00004402d140d0a096900c5110201320b000f40180c1c07000c1940d64246020540002c060005a0044c4043c2002900000010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 844441960 1250 844440710 844440739
    0x15030f2f0915070b0106090303170915010b09040e0d08010b0c0a1205030a0c09150e010c12030501030320030904091b0807060207050301060b040911070605070e130b01020c091302 78
    0x10030041c02c129001380f425071820b81c0ca8a20646500195210080004000181c40703003081c1e06110352140c00001c900141c0318195140b608030030a090003a0000341c04d0441c00205124203151a1048420402c1a0f2026066500c02180050710590052041000702d0300009644515038100744170044247c0c0c0d20041d01700c081c2020801c020920f4108582e4910754074a0841302d0f03980c1e10f0181e0066403c80d084110383d0318928401420499142520320f50765410301290030030302d10010b0000c2c5900441c441c035941e000209513155080051407421a08410810100c41c035103803402084c0044100c030640b070740954001c83d5100702c0b40341c03151600d130f10300b803040a16400740c010101d410040428031800701c0b80540d08807660183c880042500b02e070341c7c500c22120a0101000104041d02c0d5581107801d020b441c21048608001403512950b040d100304403040d00016444a0b205e1806180c031040803000300c14245001c1014500510010755546030305a1020305c00d0300540001905034107080d4062807035660282c01c2103c0540103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 844443210 1250 844441960 844441999
    0x40f05011202060c0f03210c0c0c04020d06030c0e040606060c03170408041701050105211504020f0303070309150e1018050604120209090105040b07141315030f2f09 72
    0x140c02c7c0481d2140d19100400d000400c0d100540e2a4024102d026002d20001c080401c002035012045100100340c0303400e0000082001180d890340200140302508a6a00c0c191808004a0301c0359004081070100d1040c0720300c08264819250010070706005800000e035180c40c01c0c029a680525030046800103075881d040d0b4010103040d00300314102c035404c0c0e07559001d101d00c2c030407001914121080d000c09150b20207a14058030340c1d070000c011078205002801c01103625243d01e000c40c4c21075001900503404202010020044042d01c03101300d40d201c0b030443c0f403c0803010745120001400824807800c200100f001c00004401d43c00064a5110010040106415942e507907461803080880c40c01e11040c1e1091a07890001001c0a0b4103020b400e02c078a902006404c050340c0c41c40400e413142c00c2100b82140804030140b00700c218a4441d05030300d42c040c7c10300440c4c16810100c00d920040c01e444081e06041c03d182c1c1000ba51030300720705544441e03100450600350165000c929012400e0540d0042002c0700b64041100a8030745c220481 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 844444460 1250 844443210 844443247
    0x10f020d0c0e0102010605060717040b03092103010608012304020406020c0301050a0501052d0306040b1501030c021902060c01090f03090f1404051302090103030509040f05011202060c0f03 82
    0x1196160342d404100c801006900300c0d0810300c10316030416010440c2100084151803190744412801590034117040c2c032090544015002111072030400d034005441003401042c030403c6000c4446600824515540c14420010b00359907061090581c03c18181c00d1840b049400e0045950341640050011921a5038503080203540320f460b460464080d5180c40d0200d0401050707801014141d4802400868003680401c0c0c009424080c00c255401c00b2000101c5124ad80d0799041c805075020345d014110401d040c0c28100041c8020541c64580075050514002203e528160003040c0d05404006038002e2100d005880d00114445206001c0c10203035552911900000300b018002450030454041c0c0e4400289039240e003503a0003455018000c61850701541c80d902005450960841d650003801e21400c2800b081c0242e0104180c02c0007070300124007041003c585580e8904240c810007104040000040c080f6524243d01703090070054884000c2e00903c00090f019000350b10402c40704500b00e490600f100d55441e5072203214204403d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 844445710 1250 844444460 844444481
    0x1a190b10050c1f15081b1512040803040c0b07030f110309120312060a03080403060213051e04150e040b07212315010309110d080d0e12040314010f020d 66
    0x1d050120106a031170001400c0340000202c10038400b41480e08000300300714040003035002c00b0500010000c500303980b0202ca100c5401039102d0b100454480c02c0910b0501c0410940340c12169450505000c40ca0120394066001104d1198a081504031540600c0c20241588102130130b4a803c0110b43d0728052404400000820710040c0c4840220200d444600c02c12180108521024051040a120910100c1d401e58004c1410310649403070249415070769404940342c400c8a640c551040d04101e4000581c0342058003036030346890740441491030f6103400c0203080c011415018101600400e400700000d824540290f800405541e000400d844104903244040405407070181500e134105c01c600007601d01c081c081c0107800382c0111701c0d01c291140301002080044004110164003905c0c001e001e10601d8600b0303243c0199101e880340c09001c0495441c070042e99141c0c2075400300c258840442e88200865010302c080c9201380d03002e49500c13070500f0328001c070120710340c1303000d0607000b06082e510910028482c405052164081010303007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 844446960 1250 844445710 844445741
    0x9080a15061406030c09060706060e0f060a15051b01141009020703050307110703080f220b030627100504050a0e06010b070303091a190b10050c1f 64
    0x507600d856094030240002c1e40b00a401600500108042c0490640903189100d1301500d06420400300742c4984d41550241c0d0300c0041405421410700541c00d0401c0c151960040c0181c40c4070708aa8070f42a5050300310107151580030b04001001c1f803800f0101e203822440c528100c541d00c0091007642c020825441030b107402621103002d0308108000004842100b4000d503451103416441d400e040d940c81620a032845c0751100140340950240003404000142014007402600600541082c3c50b020803401242c11500e0b40401c5000c1c0e2090f145003049000090412681d1000c0d096070000c00c11140c449194840100003442c881501c2e01480030040914004402001294000c442c02c0c80140c8810219400f1039030801710700f043c0f07600301e04014884814600001c2c90054400d1900040401e03503a01c0b041650b0700703a14080d0a4140f0308109201d040214000010300440003000108204903030180096107800c0c504a0380c0e014403d01045a0751042c1051060903406a0708518030225440700e00003070360040c0004540d110b900c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 844448210 1250 844446960 844446971
    0x81309020429190c0f0503030108070501090b09060913060e1605034c091b052a031c0e01060f05040f0b0613090b010305071e09080a15 59
    0x3082d90b03503000154a03030300050086161000141941d105544030340807007000d001400442c0300001e00009001414070380144041c0d91a0350410341c005052a0213a0b03c010704025003d1410700610305044100c1300300100c220740c0c582c1e403828200c0200c0d4a602c0c0c1c0300813038000741c0c0c41d0800c00222541d05885051248104001d2113410031081c40d020f49645c00265030b42c54100329926a0648440c00d249030000544550303001000458102d90803aa001030070f40780c00c170034044114800811096440e80110b096a0b4581d840d819441c0c06a450001c01c603006440b0b03000300f00420b41852110040b40984190381c10074102007540e5480c8d04d403602c03c07110340501d04001e5400c3d40c901054101e183c01d040c461070b0700b95200d845007a0781813031034817040101070201070301c42da01201c0c1e1300d025000c002c0d0b98100040c082c121011114031000ca191206810032912812a140d060500303000402640c25440900030610701e5012075044101d1071071030022982c81ea81604205074520954511000303111143c07040347d03070241c10003106200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 844449460 1250 844448210 844448249
    0xa0e0703060e0f0a0c05090409030c050606010309151a040204060314010b0c0a0201120b09040b010e01090204151d0a06051c06120b13020a0905043302070813090204 72
    0x10b0700c2022249201207840300310104800c549190041c166420051604500f0900c06000050403648600400c5000c101151000410804240310440e40715009080400034203002d80c44102c442e8000c1001d01c0f8100c1d41c4d03001007145080c0744051100c02168054002c54403242c4600c00076008001015401c10244594400015182d400d8003c40301e01349442d5014100341800d40d401941d0f1407030702130181c490080d141c00307a0300e9803910b44840d2070344070744c3c0110722411325035252506000308a48180c12240699004200605c0001942d0321900c440d08100c3c9402e2408200b2001404441d608802046a104060702c80c00100e00354400003030080b002d05a01c42c0d40c20401c91454040031a00c60f03104048008045150440c00f01c1c41a403017142c1e01c5084940c920000c0c40e10347c0c4c001151170b03110f504074806041d034603414403040c0000d0501080502d0b1090840d405070004680100c00c0c0b440d04d50a1000381c80f03400207a01010400c4001c240c1c0e10807400302c0c0b10b815041d901c80e2100800394025000d4882940d440b10390000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 844450710 1250 844449460 844449479
    0x5071a0a0f090c1e080a08030f13200607150c2a02210303010603090606060e0a091a060c1c02060c041211030a21180b030a09020a0e070306 61
    0xd40682c80103c0340c80541c58601040d481384d00c3c84890f001ca0b82c51a004c00510050f060002c10040d0707101e009100c0d07aa1600c4900c40b8400c12300500b0348038600804031038090010b00034403c000301ca25040e903200c0d20100c5400c0009100c41c41140401410b41c5020300900d0141141a001070010001e55255103581c4601516016903d05081b07004082c001c100300c0e01d060142c00d2540300c48003011030444c83c0d65074840381004035030301d994801e0740183c001a40e50002d5078140549482400083d0015107017040c00b03104800002804c0c035040f8082c405015641c1e07000070f90350008164032007141007000b81c20152185202010a40c03500142d20141d0b09041540500080e558804200ca130710507191280e04508007803e0034042c1400c2520301e2411900b00341340216529155508224030001d0f01c0c860441c410200b901d02c0796410742c00d81043d084405101540d026071070156007101c0d11106584010200903103e5840d03916003000b40c000000b005c0e4002200001c04120914109011403040071592401c0c45410381d40d48010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 844451960 1250 844450710 844450721
    0xf040906060314031812070f0315050a020703051c021b0a0b160f0e040603060501090b0f100e0105030402030705100f0305011406040b0c01320a0e0303130305071a0a0f 73
    0xb171034056000c810400051a040101c4000d000042044400307181d1200421807107180c45400c256100305105ca1102d05800c510b0240d16445240014154104a0169000b601d24020a0304025510080c524030404150240d410b41d0048940507544e040d805080303c0a15407119804079046d03d07101014800910100c000411040314807500e039651a0800b210b4103001c8441c080d00c2c4804540c03054445a00001040c0300707004d4a4042d1207000f034000303049202082000400e80003a10180c0c0590394030000645001d802402002d41501c2c00c0c20480c1da41ea8036440042d041031404e0f009568401c09803d54150020340c4260060f04070800764a0811540c0d80318502105240001c101c6203610920801041c415111440050180c101030080041020702c407480e4110500c40c148003ca107402c1402010400043c11040811a04a40620701c200304403d2000703c01512403000420201c08040c3d01c2040404061007102180d16094114501034000c0002d0300c019603c00e241601d10f0404281080388040c580002445071f03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 844453210 1250 844451960 844451977
    0x17180f0705090f130b0a0e010e0f06060409020409021e011106160c14071419050a15120f06050109151d010306030c14101b110f04090606031403 63
    0x82200c81d6907400022405800041134a0a405120451400054040716256014480c0b2460114140c40c4020b001c608480e2955a080040d600c2488508100b1030042081070b00944182e8003c01da10480e4000304d00900180c8500035000034014041d0f2503078000010708a80403840982c1e07102e0080103c0343d5005c1e611401030720960300d0300c1d004513208294140507001101440b88542c0c68a944403420700700c02410b004065000c0c00d4103070030314503000440f0319140074150040c100b01f17a00004002d0914011440106541c012020043e484d000c458a46034018040041e00c030030b101405018070345581e52144040e008078883d59012803e00c060204881040c03040a031050102940e030b000c640903c0406100d00100966009414542c0d00d44012001c105040b503040e028080210000044901751301c10b101e510501c00d0007c800b049111500700b960006200120345805030004030701030350a84c02200196048011203a50381d4003500d050000020042d080d0085000c490045610204d911010614107072640304e451070f07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 844454460 1250 844453210 844453219
    0xb121003050319113a08010b070507260601060507030507150e03040306140c0f0a0e0301020d06090e010605010201021c050408120717060f0a0303030203040317180f0705 74
    0x100c1d150070f44010000c088580b07940b038258441901c003400c0904000c40c42d6101c000140e1400d4000c4800c0d46601480d010000012240c2140503070042c038020800403043c0030301e0107034520008902c818041d00300010b80240820300384c40683ea422600828950072508411105540144000001c8250180c1c0036107003025010348400349002602d80c3c55030b0f54400000700151505681e4010143d5900d010800390000d03500c900000644292807161245c031001c0024103441246e002040403403013150114040d140000c0c0325003051020444e41c0b45c0080d02a0041003540f00099140c03500c0040c4100154114503900c0340f07090000c100d4280c076100120309030b224080e00c0090461900120302c0c0800560361050364414020200e442c149002004841d9141006aa0840008041038100e48010149004080e04210200c4100400403210750105100011a01c00503050540c00300001c1d06042c094000803440070541e00640721a840c00c010f401080000d038038041c8010784600c0304424100800007a035030080c0c500060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 844455710 1250 844454460 844454467
    0x10b04061409100305010c050c010b09010b04060507060f0f06180c080c1b03031003021009080d0302220b03150f03030d0c020f030c06060108070203190e0109030209010b1210030503 79
    0x1c240107401c90043c0401011180d0140c2c0000131440030301c100704100103036640b00c83c0c2e124120b030041420741c0c0d802c01081c0d10500c2088010000810030000311400ca0724a4100340740c841ca40342c1080030060290822001038142801d00b00c0107401485d80c03000064610b2040b00a1507111580525812200c3c4060168003203a000000f1650b415540e001410503103011080902c0003903588400c141c00c44d041074410b030045082030301040c0110b05e40600312880070090342c501228110300c0c2c003208903a10a4202509010f0640c0011029020341041000b481e0380b03411440d4202c1c0c801d6079801d12030001d520803100c1c3d036500c9540030003800a174585400c40e100c0051005000b03500b01202c0c2051b03200100000c0407071005503c29100131000c0d81805002605034105100c018100c13a01d003180c00541003050003044130085420170007007020010555500302920003118585080049003c0780181d0b008640c603080a548a1700d0303400002802c405010040904851004011402e0b8a88030409030800901e400000c0040d0420b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 844456960 1250 844455710 844455749
    0xa03020309040f02131a0d1e0c020303130303201209010c0c0c0b03100f090203070305070c150b0a0f09020409060f0609061407060e060f061009170a0c080f010b0406 72
    0x1015109503106d9a551400450f400781c507086034211900343c3d2030380481c0c081038406904288100132983e952030010354a1840c0c07101d150079810050001c0241416641c0c1450404240b00a08060f14a5110342c0b00c25526102c00c3e1107910500c1d01110091746660a160315801058443d00345014440d5020180c10031450401320303061074540004010540009410000166450a5000140c010800b0b080016070360b084c1440001e0548030024a400e083c0041d14900b540003071030395882c18a980c213a03200d00242c8000044d0000d69030305416401001c45454101c1c0116440006e58020801c85500e84e600700115595212841e50442c89d03445400b010a49940741003040c83c0c018110707402c030005030200e070902c0c0c4001c070740d03441c1c0444d8040c80f000c4800c1e6200d5402c01c000c1c4406140c43c140c03c000c2c00c40c1d25840810040c03100820913130003401406810302c065110b00040820401110320210307404260008120384444000d40e0354500415481095030a00d2161610740c00c0034410417041c3d91071244c10500d40850b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 844458210 1250 844456960 844456979
    0x8070506070516060c0302070e061513051201020a030608150f09070f0314010f0b0603130203010225030f030203010b04050f030f060a1d01020430050a03020309040f0213 74
    0x2000240c07814094407042022085100f24142d0191003242c4525074044118200240380c030045801c00c1540e50301040c14040550b0720304908488400d4520141590399000c20044403600c5101c2d880380d0b0300300c0025250800c06a80c1034004d080c0c0c40f401554100142d41d603e03d44155200e81890a07403100001070804212044031002d071440c0e020481c42d048440945e03440d0303942c0c514043c05034004c0d2154003001c0c4015085401c01e02920721100003071041801881404000103c281c80003400b20320f1440340003420301003192429015291212410072001840c400041d82d070140210450340c0c2100024440c0000d60300c198000c0c8241c9061724803440308941854180f07420311040311042a451689403040401c0038017219070803c6154881c2140300c0002c40c0307100151915040f000b103c00340400c1582d0041c0020f100341c41030b40c0517540c080e003800c3d4001e440602d0341c2d907040401c0c0c0007206400f070202d00800c124042856000402449003050644081003280e001700301030001ca000b80c49810a01c0c900e00102000703402403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 844459460 1250 844458210 844458217
    0x8010e1b06070201020f07030303150e1b03060310050405150c252117093403050703060506090f0f0402120322090f0603020307091104090203010602010e070f08070506 73
    0x3c10b00441d0044d903100c1c400c441c5095000e5004500207611148881003c00090703c0740c01c014884212841c0302ca08203114400c11035200135103103580040d07020001070020358042080c03501e40c056070002000181005d062564460383c2400c070340300d96100490046407000a001049814403912240309107500502134100799030710700d01c81c0011750300d03542038115008044899203182c5003044103a840d2000e166008200c01234103484020310700009a0800c2e890900c0c1c0c00c0405400c1d200d0079260301c1070702caa51581400380190102c0701d0342001e005807140500120810016610440c0201f504a41d54003035560345115040c0006412941014920200c1000c40c005080c40070290f54400c0b80c09083d83c0c104901c441042d903200c9040344c07400e02009007280e81040204050311940a16180003c2d0a0160500310b8001c240d03180ca05200301c151150b030721110001204c8161040c1c402400c503032072041d5600d5035105c400a019001c0308484210791f0080c0000010701450000301c0d00c00b25003602014001107890031040007125003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 844460710 1250 844459460 844459463
    0xc060f060314030a03050702070f0b031015120b150d0902150a090609080f030a05070c050301020414120d0f050a02030405040e060f09060f132402030108010e1b0607 72
    0x6488900c08000150256611480740c519003004585500842030300500742c0314050403101c2550042403060107503074a0002004161051482401c0d0399440e088500e008501d070030341c00300110807000000c1302050755028101c03020450a2000c1440011205000c0088950040c0c0c0445014502000015010031a40d040000d0880c001481e5008074802801c1c108229807040301c400c00001c1d00800c085c4100c68002c034444020303180040091200e0303100d076a0091354078414060180d00384000402e4190800c402c0200440240c180500250344443c0c0d52a0508100903030004850721407405103011582c01840010780941040c1580d4074882a12458031060724aa4014051001103000030040801c0c00d84560182d00000302c1c841d03000300b000e481c00002c0303590007800203440c8010320b80001050140242c0c2c1840300035049134160001e0b001c00d450a19146401a404458203003c100350003940b02d07d6000310364055412074407280020320280008440058130f60611801c80501a46590b4001032241041006044207e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 844461960 1250 844460710 844460741
    0x7020d03050904050a0501061d09010302012a081201090c080105041e050405030a0f0c0c060f050c0609070311030d12050408070c0b1909080606151e120601020c010c06 73
    0xb9880c00108003640d000322040080c06407120b004210296001c48240600000003001e030316240c905030006905901d061001038104910740c0141501208000c14694a1428800c40040501c1d501c0c640b4815a800c44040c084400a0716400000c2146e80ca01420310202c0c1035a0341c0700c800f03a00704410440100380424803095042501c1ca0b042c45600365038410070b40290301034001903171201142c00000707000c4020145000d0422180d01c5c500c0c4002001100c000b0196061820814080c1d81000c004807100d0003003646c4d0447d00e100c1d800074001203042c00b040300b105690080440c030345018901c5082c180d03540700d40360342200050040b8012140017105603006981082c0f00e01042031400b00143c84904521400790421200000d002503c200020640126202d418009050000d0b60a2500e41907e44608000305014090100c80080611024848084030034500c0780318541a80e000c100c50502d0490f07004507409000119554021414540c0000f5000210200594400541c401107903954400351000041400b83c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 844463210 1250 844461960 844461967
    0x9130c020f1609050105060909072a030c140102040f0512030705070b181f030218100c0c08010e28060234030e01110c030f010e060a1107020d0305 64
    0x5142090104542580c01d820000c5800b50402181404562042e4041c5214440801005989450304041281e000b44142000118900780344050131100842c0120085008010050701d4205900700003130030207032401188501000da9114503070508170320541c020707000a009030f40000c10040c1791038502c00001c0d402c05000d490900855503250382c6004950b810000c060900400e03c031955842da00d0300001c0660048030010005000f0066040b05202462000c1080540000d1040c580c00c01c40111090000c0001c0e0444d031094004140050010200350780869040c3c0b4807140003d03c804050140c050601d40640141800080200e4002314541c0d045d1402e40c080380c403d2000340d010914600c0130300050091500c2c241c2d48000760b10001180000140140807160507000140c0300400d0b40040a0b41c0c010f202130800e01580c020b901d200300c2c60030700303135160140d031501c14030300321b00741265041d0401c00c01d00000c00115482c0382c8400c07400c0340c25a55180b42a022444d0305102500151620f1445125076a010f0304001d440d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 844464460 1250 844463210 844463233
    0x203071e0306050906090d0c0f022b08180619050304150e10060602160b0306150319051e0c0d06050415031101020c1e011103070318050609130c02 64
    0x2600d008803190105031700700204000b41040d0a02040d0310f00c407490700c3c0030161410b403a0b60f141c802c443c00e50710181c020260068603c500c7d84050306440c402107801c3d821221b91080615000c00c4941c000e004021110070415040020b0703052100540c0d1501b0080d0134003840700620300c2000c64580d00010001d07500b04031240c0c060f10724030015204042c400003400c0040d01000103480d190310180c41c0c05502440031940541c0d103510700c0d106d0b030761140010b580140040c6a901d03110480090321640032120301c0c02c490100041400b0b21302d0800741301908003140803007050100f60f0f941e40940721501c0c000c6000c00c043d041d400e00006d515240032001000000a0780a0014403503440f400410112908414005070412500c04240140700c0c4a103540038071540244014501c1c03000080101c3c4120b003a030b0800070b034090700305510701c1c01681c0500c06103031951240300112510362030786003001010500403158000c5140b030700d401e002c500d40c2061800c03500c04802c0a00440021b1005944040c000c0c2406009001140100010b290 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 844465710 1250 844464460 844464473
    0x61805090a020a14031e0d031e0f0b120102030f07050306010201181406090106061407020604090507120b0a0509071d0303040617060a260109081309180203071e03 71
    0x80c050300440b505101000d050100f8035107030801601b159140c004000301c05000380c25002500c0b0001900343d1030f02240c00f0707180900b08440c10041c0400041030300e0901980c001c0301c580d00d40c4060b601c028100c81c41c10040403044551401c0388803c0e2442017081050b01e0014415601075001180c00c22010710001036601040304c4601144e000c503100c01c8450801c05222418003840070081c0d990000c400308001c1117005e1415902034294000c81607001138000e004681c220070740d5641001d882c010924068113009504c0d0825000f00039001c01401450064074007032904a4034100080018142d5a0143c0a0745580e241c540b0141d44040c010110034040701800b604040840e141400908000c104076282c008908204404103207000307400400150003084690010400340c4061010296149120b02c170210b1040350241800d405012000703005007451000140f881141c5034817850b810101c0e07000c44420002a5000300320f4174070741c07491010040c1d49036002d8542031141e5204030b082c540021030041c032003440c059640c1d502c0304c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 844466960 1250 844465710 844465729
    0x90d0f0309151106060109050a1a0c07080607020f0105040b0f0402040e070620150f0403051e07030e1806191706060a0b0a020307060f021c1b03061805090a02 69
    0x1a00043c1101c0c1c0c0d0203100c10020007485420601c00d0070a00c407400d05001c00701c0c900301d80d54442d0400030040c60b41000190000001112030b051070035404d4420894031501da50760303249000d403400d00051168076103402840c103043c8142c1c1d004070740c40103191805440d09401003e081101400917a4400d64035010412564010006400100131640350f01d50b1a4140885062282d601d100320034020f504024a590100c5045552a43d4400e40f420440000c680395410101d4560103400084428807806a80446240c10481d014018151203a40c075a003819240d4428440703010100d05c9a21700300c3c0c0b481c9002c51514078215084148810f4802c0401ca041c40c0d40c0c0c41d01c8209218008402000d076002503060003064200714040101804611020b14648000020025602d108904018100c85c1d501c5003c1202c1040a0701100d51003251515400e0b41e0981e1910389000a14102030007019010800220322071a0703000b402040111050004c6503507280d52180a80c0d4080d14006102c01a24000c6030444001030352170250761b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 844468210 1250 844466960 844466999
    0x51617030a06050a080102120c07140d051207090501020d031a0d030914091905090a020904150509070807090203220c09060b03060907110c10050a030b06090d0f0309 72
    0xc20700b20716010901948003466040802c0c180d00410000d0000f1910101c110b0f000b02d80c0c50801d554400355803c04410421814462600e140518900740e980168402d016211740f00911409180e41d0302c0f401d00581d0a2001ba10800c0d000d6001044800c2005000764454100c940c083d004c400329074102000001c00d1140c01c40350440208014010900020b03001c03c070000c49030403095a4000d168242603907a052040800c100c58075010b80c40b800040c51604040c003103488030982c05080c0c94000d0400b4a8410340710080ba091100c85185098002540b071040080c0400480b001c0601800c13005041880202c0070b548014900c05618400b1901164810485820340d15075500800030085036900b441c10f03400995071983c2c88001010b206000b403014a50fa4501c2c5c3d55000318460a010300103010b1040c0490801e001107281c1a400f641e00411414031540242c001e1041d01069030b0308118035203c4100f0050b880c00343e120030030f4200022403040341c00600040030a40b8624000d0910042c104d68610070440c040054482 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 844469460 1250 844468210 844468231
    0x7030b0106050a0909060f03080c07150e0f010e0f061b0d111b01050405090703090f0b1503161505071205040504060e0405060604180803090706020c0d0305161703 71
    0x2002c42d8083e03408004d140c040d0500307110503c69985410105040c0e01c401d404050002100062800032060080240c4802450074260b242d04107011503201402101c05003079840e004240150480520350b11401c110303281810001c10540100d05003000348180d5802003480e01c600b1340d5059002d50b40b0010100008109402c869031a030300401d8441d100035003004500440c60820092611184609030380140a03101607034000e90b5001101c1d85c80306401c9001c0d00941d040541240a44041d2405109242e46c50038400d001d8a00d04101c0c46202c0810715a48520034205003201d060310031000e0041005800c85003032454100e00d080c0b420300c001a19045075950b5419034078800300360b00040c200601c0c202070150394000c001041d05200245030588035107031510300040000e445103a4440090f03030f50800b9005100503098100601544074548521501c0d03840c0e1180c0128409446074400c180c14618081c1035804800d649503650070300300740c1c1c56039030b86401e82202c05003100c107140d41c2002e144038040440051446224140d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 844470710 1250 844469460 844469467
    0x6051905030f0613060209010504050418120c030c0f030c0b0c04030506060901292109060903070c230d0503030604050703020f070f11040204080f06060d0209071107030b010605 77
    0x40614004070550600a0b5801280403c00410b02050182d01e000740c1082c40941d9a0341044012542e41c49150480c0364014038000081b0038000000c2440d0b4401481550b41080c03111b1b444106030341074081c410000700080c6040ca130030800034030124441d0751000d00c01e060244000c10a5560115124802c0f207078004140401f0170204144030080050f2900410150380c1010f55506040c80d070401c2203c480c2e90402d10382d07020705030a003125940740c040300c5007002c0c6810070702c201d05550031452480700d1068841400c1e0348250404259401804000c9808069105000c0d07465680b4012410f500840300306110244000861440e8010352113040f0460441031040e8040e594a18042d0200000c0721000f80240042502c144480c22042209804071039045401241c411040c036014582821020646d004194015001090005403200009034441402c01c0c054151900355a40d041030007408500048007075030008000b0045006d00f4081d440c1d40c0c41100343c00041e07072a01a02e035100c0070751030002a03001900013100003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 844471960 1250 844470710 844470719
    0x706050408210403121d1009111806100c05010f29031e01061d0925030f300212040803120903210105010305010806041a0a060519 57
    0x482c88080303200e10382010003142050f89008240c0081c504a0021840c0d9a5000c0300e2010ba640018025254190088820144040343e1680162113107c10031105042e8030050740c00d603450128100c4242c1000c2406a90792961142e08001c150000380040d1824409001d9100001c10800e00518141301f80c4650702164040080004812658080c200040d03542204074040c00c103a074010070110500d41e60321031400303d1040015a01401409542d0000e0000364a00c8401c01c079580c9a80700387c61154081700107840c0da4090301002100402e1059640b03049480c2812000c1c00022120300002582d140286801d580852041c104c084041c484a0fa881c0c462000071580341d005d070750b07042265903c01011000d0711818286001a115a28040c1e00300304603005c920540003a5030743d0010002d44000c00003801d50500889106c0150034a24136081c002d2a00090404001083c88040082e6190041c0da02010480c50307460003015200b980034016082c4400c0c9500e03124001f81c1d90b84d4141000781414100e8080c0a03c06140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 844473210 1250 844471960 844471987
    0x1c020d05060a08010c0c0b090f030705011b020604030f030c0c0614010f1203080a1d0304140109091823150f07030b18041506060503091213050d06020706050408 70
    0x5a03409150f041e03040125007410294001030030303181c0b154445405800358807000c4019003030042d0040740c1840385c840031500e0810301205411003090b0b0401d6150505a200c19502c049071030300c4040710094007160b242c81c038590000d48240d0080d450840e140c90300908039540c076910907040e2088694140d203c071300f440700140710665402c444007000f00018011240484800d58003c0c0200704001c0c00c0c2c0e0607040c1c0d10000701c800e006c18100d5007410300784404103503580d80d606c80b003092100c0d600c10b164860020710800808901200e041c480c0c10347c5055111a84850b2101940d0b9005c005a001c903c501c01d00d02d440b244d00c8012030b03010880d09640e000310104811203031802041140080c1c5004041e801090309005041003551118075032a00c2d10303140c104c40442c0a0783c1c0c03410800c00302824031000505103232400701c00080c4140d10a004d140035103181816982100407004c4100c4160084284840d803071525040c1c10001d9180c101c02c02c1c88820310550002d400c05400c0d1b1141022030b00f00300c034160384980e070020b0052109a076 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 844474460 1250 844473210 844473229
    0xb040506010323250504030c080a022d0307121e0c0308030a020c061005181611010608011401030b090106060e0609010e09090c1005090d03051c020d0506 67
    0x5081c64200400321001883c03080480d14401912180c540520100d29010300c3c100741c074100d81c400303103843c480c464a09080081040d4014801a0b4201000c40c0011405400204046204e1500105140a00807c1424140c1013000004401c00390410305048e2044903182401060010314444242e1442d1740c50364202014403d041c0c44541c116071031480e9460000a0f21140c450341543e4014200e40e07140d81c0c4400ca450024880c80c5c00307444281c42100c0400101c85a95007000c03040c1c5805840300d0034403013071020340075901280a80d40301c00a051000291300f503052052060541d05400c0200100d0250b03502c40c952400c4442041d10010f1860800c4018020f002c40780e007980d86c0290f40600204110352900000412462040990314801c0e140010000b41c280c0c8901903911420314010603071603140c03d00c220300555542c40030701da15000f042c2c05e070400d0b00e60b907000f10141d403442e81000d81022519003556a04807051381c800b102c110402d4400780020300701c006452000d00450040d000c00012070b401c00d0000c002d40c840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 844475710 1250 844474460 844474471
    0x91502060405030a08070203040b040f0609141807050706020705100b01050c060103020d020a03060e10050c0403050c102a030905040b030c0d0c0b210105040c0c03080c0f0d0b0405 78
    0x140000c06200c00940004101c44a0001d43e24203c1e03244d480d040400c0b821440baa43c0400c1201030701141c041902503c0052404c00c41d850b03a2a04c81e08940e0300c0b4000c1004911013101030b944a00c818045248a00100420603403000c81460310b1441c0c10f0865407050101d82240d40c050701d056010301c04c561035241c0b143c03048240700582400c10034100144481800d41c3d40c401400000d006040d507518800c01c5407981c2400d00081c60348100c06001000c168100e1a0390f0f600c604543d088124103000100700d0201e402c7c0c040340c055a03003240c040c103200e0309290248800201090284070400044440a00800c0d45810b0f0301e241145800440901d030b89034a0034014038058541c6c200c82e104a01d0012251055a400244400c88620964007030b6403a8070241032107941202103074000260b040c000280d20031102c2c40801c0220034407002440310095039880e802448211540d01c3e01840c08641c1d581003140100c0e00440307601e544288103940c0b5034030f02590a0185200390304580f000d401c49a0b142c00c80c0c4035892500d402038a500a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 844476960 1250 844475710 844475713
    0xe01020c0c030a0c03240c020109150b030d03051b1603080609010b030f0603010605060a12140105030d320307081f0501050d06030c060c0b09010c0c062406091502 71
    0x103c804c0d01c991580c070b050f80c400200320030362001034800604c042c04980e0325941c11200d01009003070f20021000c2d010700341140b0120f4a003084401454142c001ca44101c0d0846140a002040525400c080903401840e0140140c040e1103c0d1050180d0354005000c002d2500700304520800c0400d04aa01e40540380d0704d00a802184101c000340c00621504c602d400070740394049c0c2c8124030002d031510781c100403e004246607005076802c01350000300541c00c5a007100c1c1c1c0c2580c10503000001c1014640300a91a500a4000e0040f80c0d407640041c0c140b24140c511035040c00c2425000401030344007891900c40c0540c0d141420540040385410b001c01001030840c1c02400e0681e000030401c01189514010003c1701858500c10b00541e418801e01241c08400726549034080406141c0c0b003d550815961181030103019a6407282c4c04542d00e65011002a20301d10040c015080410320f40d84035650030320303115551000030380b2042d062444c1d03188041c2d6000780c0a0341054124002062151216103d03e801e081402000001d214440d030300b035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 844478210 1250 844476960 844476973
    0xf0c080d120c111015050d0c15120203190e030c0c061b030c0c03070b07030e010c080d0c0f020f07121b0b07060213090504080711060d0e01020c0c03 65
    0x800d500704040c54480300100800094100007002d0035149030405403038001041c0300703012188850004c0e65025050364060b46442c00445955001000003070b0140810082c601c041140003000010300011503148030640d24101180061701154030b080898000722504010303202c2e041411084210140f113001c03ca10880d00245191034402a110380d0764801c441c0f4610300452001030b0015072202008141c1a40040301000d5a80c0c560004558a985906c4007416174844d01038084005611040e9000b16101144c1c1501c8412500350040c3c0150b4036208200c41c103456508040284c1c01d044100e501c18203110201c09d44650307260148900d0024a0085d01010748001e580c00b07401c09000c000046040c082d81c59030306c216103503140c0b03205160b146520640c980c01190042030120303001c401c000b8250094500c1c05480d03420307001c00e00d5407220700c01c003690001d03107010706131517000c0083c000450500303000b04800c0e0300042d00c104e1911515410040031108003650040b407031395020401c0320441d18240100d4030114005c0740280ba0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 844479460 1250 844478210 844478233
    0x606031302281e1e150306122f010c060e01230708070206130204090302010b0a091505060702101d0d03030204410f09040f0c08 56
    0x2100c88040a440359810308950400700105803266031621200558880c0007903990500c0d0301d403042c0051040c401d8031090200115203070052100c01c442c6131010301c844504807860113500b08204480501120304044d215400070403213008540184c0302c164802d802c1d803940d5000141c012aa0030705000040050401282d2000000380e03407042c1011856a04424005521a030001c00700c1c0c0100b00581001250361240c0840038094101e0041c40f512032491034444149076911034200301d8442c3c904951440d100c0040e41640c40160916a004c2c04000b4801d00001456041d000001000c0a0139a0b01400300c0380e40b03580e100c110513181d94913034800034401914690300304481540003505a140d495403000400a17015148032401580d146800c000f030034043e140f04d66501040c02d0041c081c2d40306008a030780400c824002c1c071042d5001c0140d2184c5601840410b03031140c2c400d4102c0c15a10700b1000c25a10340c4000000310b0701d41d9a42e00c242155000f00d00c6003000404110f1075140c0366031940e1080e48070f91803642150a4008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 844480710 1250 844479460 844479481
    0x8010501080a09032316030302120a20070501091b05040c0e0d1103150f06090612060408031503011e061e0306020d021209010c020610050607080d0b0d03020a0b060603 73
    0xb00c40110b01031016030540d880c2c5d000800c1600542e00741803202a00f400c0d0039400e058240c0c0c014080c2800c084070030b00d01070f5690880b62064410411034045855500d25002e0501000392015103407503441388001107000040e50720344405002e49045400408141c821080003513240c03611550075802c41ca401c00405025400000444c2071501b01c80262801d0407601801200303980621001c550300040c110505080d003452281749081ca03400310384d0980140d850601140c61031070300c1800800400e207910006d0110f99202d6aa00c10b0035000030380854000c887c140072a190f903507008e029881c6100d213081c00124940b10b00050030800d5400551003000f44202070340d8100050740381a0b2400003681e8100d0b60260313a03540306044c41c400901c03940c8407240d04000300f80d0a21510b90019044419150940c1c0c1c22035245440d141b810901000b0688249035001208100700303030002d840d003030250a80b0f41c481100021400c0845001c07071007d524902d8200c0042e000700380c5500400481c035250980000081c1c51407406c0d440c0c5807451a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 844481960 1250 844480710 844480727
    0x6031406090a02041e030614010b031b09030a260a0909020a1205040f02040b0901320306010b07050f07060e010516210201051f060f020f03070308010501080a0903 71
    0x10390140150000080542c02c1a40440d4000c100d102e400a81c224101081641d40b003070f03d4082194050b007403840c440b03090368016044505071903481080a14503251011004029085074010508035842442216540e40e024040c40c1c0550f80207906000b40d18a00600060f15a0300039203600948240c00c2c01301c84082d5921106202c00e0b200b0301800180d07a0151040e0968403030700c01000454000c2c2c148010003040061048a040ca424804c0d03406000255406040250400c1c00b4000c0f100000000141d2517003a480507074000b403400c01800c0f080c3e02c800f00d114000c241400c8090300300b041e140f50b00040c5103082010411891020540030700142c0616820050004d00048070015071b24100100401c1649500000124003807a469101103c0090b035100009103e0302144c105aa0341c0c05940703018009a040e00703071481c007414030310348000c110905c5034101502500d81c0011010f4040442c422045c400d01c45210070801446803e0281c0c50f0f40c1941d61401000404182009041c1d540d01c50500d03800a0020307400c0b4190 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 844483210 1250 844481960 844481971
    0x1060810060e07120f05070f02011401211415190b0a17032206030b01080f040206160f0c262a1f03051e0106030902040e0d0e0a060314 59
    0x200b049400d104d00b4031801381403080919915540380c2410302a601360082044040088180c00a01ca5a140c400a02e11603403024440c40040040e401160951088030402c070304c50309803254050003212421850302c10320b8000d00c1070006940d107c2c04003d212540c1044610204034500e491024458441003401044613001a0701c03d00042d00c034001c4d50003171029010720036191002c0d0078030306071251402c1243d0154491000c030301c6010042031401a2050942d44075080840c46004c1b08030034441d00e03480700e17400c0c0a02940200b41d80c03400c048005c0184c83c001481d84008010940c014480844400d0501e5540d298402404083c80407002c101820400440c0002c6801e8410701c0d0704032004090110f80385d001080d40500c009080e0b030322840d880e1101142980640f80d1001c80c4d542ca69040119503100c442089004440c2c03205d040c201d01314640104169031190704842240d80c805840031601415040d030541c500b03113884080101050080e0aa1503d40c180700320350000812282c613081c0301d000030000b40d10703960341c070701400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 844484460 1250 844483210 844483217
    0x702010e060315130b10020d110f0c0f1f210212040201270e04120201060b040e1b1b0c0f181e04050f0c01090501050412060608010501060201060810060e07 68
    0x510818511194086920100d002d000c1d44101b00c0b46000007520343c0e240e51000d002080c20001c03500300014000690320030b0802084c1c002c0c014980341400b04860300c0c0201c90ba0301d5019030401d0044100064200e94501d100400352107080481d020800880c00d05501c002d0008007192050040029260740114000d400030340a0900c651aa655448036480042102942d5000c116250100081580120150b07911a50242c1c0c0d4184c0104c281182c1203082e01d0f0310344140c0c41b0b50041131000b40001401041010f4108500110144000c1c4030410f4500081e00202ca80392084115003108280c02442840225151741c1d00311a40b40c40400088001210489103e03c0c03150031100d0b00000440a80400400e01c5030145000b42240c4c4030314191804d25030320000058003500034065880c1401c400d50140c14440d0984405840d41ea0405050220011004a02d44c809450307850b1a01400034a0050a120b214003800c5503900101e90380342404034452508010300b421001585c5046070402c0701858520006801c0b051030b24 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 844485710 1250 844484460 844484479
    0xd0315140a0504110901110a080318010f050c0d050a060605041e1706010609150906030e011503110a0e0121031103120f1609050103020a02010e030f0702010e060315 72
    0x400d414201d15000140c2040c03825844904030340c048405000d40c08002d81e6010741205a540e0116100c100c042c1000340304040910204404442c42c0c0078044542c1004000018070301d0890025034140c0e07070155891214000c0001d180d92780b80a1601840e03a01c96910306040c864249070100040c23251140e0311910021440f0411020407081d901e2070040d004103502d4003410064031040c0c0034907454040a100d81804640396000000e03c3c0f01085840c82c9944415845400100c1c0c50500250003801c0e201c10b01d8019035581d1040824003445041c4000d010f5070080c25204003410629081c0610220b09401c0026815084001004143c240c0c04081100440008080303801a90a00c0e0036551b0311a01d03820800540804603684554140c0340030b0480c80350551410030841a141c61304241030400c0c840b1240300025405100605c0301c3d50094000344032019140c0b0000890880d403131042e07411504181c6950300c0303d1000040c40b8040d580c0c40300d0028050641154454550308081c0c059010120081c02c0d480d01450200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 844486960 1250 844485710 844485749
    0x1a040f120e0d12170c03060a1208070f02041e0507030c110c13090804030f0c0501030c081308040b04080f010501050a1217040f15120203150d15020f0c0d0315 69
    0x7103c044296845012a013005070801808a0b8025001220442c0c080c205011001a044216030896103000340c214400c1e9213004840d868600c0d00e402821426030300b107512a01800d0030511700c0500c01e84c07030f100420300000c0c1c64104100d008065031950748003141003142d0000b1501501c9000f2640e02c0c8480f40840d050035a400d008104400a04400030028080750001310740001407000103882c80600307921032442005000d0303c4e10019001ca4a007031800c5030001e50f07a200040d01d100910391015031068000c0c100c09042941c0c0e60060348960707115030004021504800300345038480e8424013800c0c0c00741200f1214100c600e400c0a1680c0c000c6010810003a003d59a2074003400c00200044d0704a4001d0001e04500c5400940c03204d03a441007460941c0c000b44001254203800d150345814501c02d42e805200000c84c070300403412a800420400344200d400c1900d08030451414240450721500c0100030f42c3c0c21008059440b030079000c43c06800e0401da10100010316050190a5107110306150342c4c3d5095a9600b03e9024000044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 844488210 1250 844486960 844486967
    0x111e09010e10140732100c0c0209040c03140703020312030702150c090d0c080d0801030203060c07171204051212011502010e07090605120c100c1a040f120e0d12 70
    0x140d014008845d850784003108903a4000700b800c081c034a00d0340d0045a020340200503401040b0750944007401d000a400107038501c01858207050640d0024040e203c3e407a4901d4480c3c60f00301420071102d10024480d4803d11080085050502184444054190342076096281000b0080e480c1c20381c03100789401c0c205909002844500300003003500c0c04080c01600b025440d011750b2a0041484e5018015940c1f02d2041840400c4010b100d6410181038030340c090302815980c2c1700c0000c2041d040e00550401c80714041589035486040700c40002618181104421151950600b030409038180740000808000042d41003103091686807005a0040c11243c03100010b640325031485104038018030072090340f01c401d030041500000d1000001d0700100b0903100d0495550190449004143d40e0701c265003c01103402601074018100381c070740602d01004020303010b207500d040c0400c403032400c036281c841d0100c0f01125440c2158003a40c0c14420f25040c0c000b40c4445600313211040100c061700284a034448004014900d107455039160007294030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 844489460 1250 844488210 844488233
    0x1f090201111203071b0c090c03020d0f0501050108132607050f07050a080c01120c050f0309061e07080402121c030e15040f06111e09010e101407 63
    0x2031080545402d468800403849195100707654a900150300f460403440211141e202e040382c00d9910803600178002d0300c7c1c00c2292000d402041c035400d050503400d210b00000300840b405141c5450007080400071b070030f42c10f06c3c0c0090072042d800f91072032030420f040c1e20b02072000070070a04950456210442c2d4244003aa6200300000051007801d01c01465170013841c008040300d00700020210240c0d001103074015650341d2103c0140c1d80d41e400032681300b400645400b81d500c0c6401c0075540300900d82c1c006850300c207150052182080f007065005550300c0505a101d1410400b00c6c9540039070352581012058440300c91820002001008901c01400280c440c541c401549601c8010802c1445010f103e9611148003901d00e0890280080a070045980d415006107040010702e42c0900341c86a1003103600044ac00d44c0402240c940d103005040380b6824507015141004225140802542c24881a000580c0101e96800422000600301c56512100ca0302440500b0300c0800308613007000d840b0070282d416011460711021181050b201542 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 844490710 1250 844489460 844489487
    0x305040e0a091a0f010e130803090c030a0b07081f03030f020a0209180c030f121e0f03180604080d020f0d0504030c17090f061c141005031f090201 64
    0x2124003a002c0c1d80680010f881c44c401c41003801d2a402170b0303076520812071101d0421500c0311b0220001041c8800010000380207590040d000e407084585264009010a14010301d140094400e03036142c2e41003014440d07101d11490b601c6000030b00b04826110340b54504000c080d0041c0001028040c09044a126642c400c10000d034003144c005140044c0d42c03c2035882100c0b00d05010544807100e002d0309820b0001400d002070f030040382c03440e40c0004148e001d20041120596030003407032400360b001903c100c03000d4484108801512610003200101580c90800c0c07600341034081440030a03200290410401c11010a0300e64040d85c001c8150300c040580c1d5882c1c0c610782d0410500c80d44110703a103440d02e0301c030520080c950710200300e2520724031032040b8520b000c1401090210a01032844025441b0000e0f58401c89141080030103008035107130a500310068812940e440c882a603c4110740f81a40e900818200610703440300e584010300a010660190080070010003802540899410000300082d458101107030469120b2a035003000749 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 844491960 1250 844490710 844490723
    0x705030901120b1306140924121014090a11060a0c0807120f08090a0318090507030c12020f070618080c030a0207060e100f0311040611060a05040305040e0a09 69
    0x213415140080540e4003e1070131020050340c0c9010541000b040045c00390f0301c003540384001c224044010380003042e5200300c0c058001252070f01401000c5810801c8640d007840604000c950f610829000c11100080141072058641c0041401c00119800c520b8189400e03d0640d41c190341c490032007000356840c2c14100001001094000351032010f0040b44444c1031100d16583e5181d50350a2041e41c4204d589400640c1c01ca10755400070000000020300070700003003040202165600040c15640c10403401240c00885000010903100d03900c004506a11101c85102d038070030a4002c5040907403032980c211032400b80d21801040b042d0b4445039007003048554508014015409040c0942d100c1419003256101d40203003c410000d48940800403a0607800f0300032b03502901e40060030448600300e01e05011100820180110001d15a58031101d00c11244060020070245c01162220016001c030500c5451801c0c070010101d209461403d018800025070000841e0120384060b0208885900c0e0100c28000801d0340c0758006194 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 844493210 1250 844491960 844491979
    0x140c120601110a060203060a0909171602090106020a150c050d0504060f1e060f15030903270f21260d090203010b0111120c0c1503010f0b0705030901120b 67
    0x4c000543c1c00461240c0c50640c0c0e200c030741c00d6036128013a00740c8107100c000400305042d00981010fa1320500010b480d00784c415042c44040c085840e004150000020b070420b400581010b8078500500001141304400d240543c1810410281280030081960003071102d94003025440340046000c1c0003080d001400f421417002c2003002280541c01e440381001c000d0078103130040b85d810042c00280e4111238416038000c0300c18000c4684006625250b08800615058804034140710148801c41c080511010340d507010844c0c0900301303040c064182810b0845002e69640080c5090100060403409810000c1d00307540c0b115440702100c01d1000001c190300100c0e40c8242d08108001001041c1c04550070303603076008440b0060094008101c4450341c0001114680c40007120500254030440c10b0310010001040203100c0303c42c0302010b0303450700c030f03420000200d000d0401d544084007a400800140224200404890000d080d80784c01c40d490444a0350380ca644074000d00c1c2546047c04642861b401030125140c1180100400c0140071014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 844494460 1250 844493210 844493213
    0x1a0d0203010b090a06020c060d02071a0403080a1802030c0d02010917030910020114010e13020a180e06040b011206060909060c030c0221070302070e07050d140c120601110a 75
    0x2030b50400302c109031113280040c1e40099050700200b800c0e40144805071006260030900c81c081e002170351150310b0807607c00401560201c140d80c40182d1041c00780384070ba65483e0361410b0080d0040180c6981501c54002c960242c8030290060b0b40000c5c605c002498299102100c0a4042c001680c4104417035101e0301c003800594000c4515000302000400030303107508540740300501c500000100d0827101011080000042120010303c02240000095076000e91000c090a445403416804108242c0c00f40d408a40c2c104001940c03e14400d80d10b000e40c1070742c2d4522070020031807442c064075030003a0b44a040c8114442c0c803203d40170303d009111217a040b00c406407410b450b06100f107442d103140c0000103051040780c8030002440c2a805c07105442c4003060640c11464000d0120340a206602054006c581c08070a08400350301c100c0c00c0006074444914030040c070410300d80d10b41c580c584d010252000d06032002190220900700241c020042052405e0090303480d139001401d4500c249a4030300b4010f03150003d44030500b114900c01e2100180 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 844495710 1250 844494460 844494479
    0x10e100501061808030d0506061e070b130b0f130c03050d11032a0c100908121612092714060303040b0310030219050102010c0c0b011a0d020301 63
    0x241202c0c2d040d9514031581860040d52207005900d4010405150401c200c1c00c22140001e42025802c03000c002c060358580302c01020200c41582916030355803400c0002003540010300140741601c5600c8035601c0c00758008508155240f035903076040100034588851581001c14240240d0f13240841c906035100761680c00e4591a81015655000c1d201210400103070999590030200c000801680c7c85000840310302c00c0020040308080c0c48a402c0c00b01d50104520807485007a0305990380b401d0011a01c1c000c2e480352010b4070b08226150313061148215000350314400802c40f84406241c4c03811604000c03600702164418202d40000c0403191052540d02800380103900c901d14146404c6000c00e800000d0354030800c00c20804c085031030612840d00b0304580541e40758100340800c00c01c0c01d4290000750341c04243e000c000d000d201e440c1e0780000c5a420032000d21507464110710f80248503550f024410380841106905061030708204658401800790303814081c41c13440610340300303060016100450503245152441c40066459685641c41c80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 844496960 1250 844495710 844495721
    0x305030705030c121302100c020f011b06020d020a090b09030a2003100515031203060111100f0f0605011b020f040f05090f011b1d010c0f050a0521040e0603010e10 71
    0x5a1280360b0900040140034028a1105c1c0c1c0e644c1d028082c0c420712008800107684003d0307003006c02070307000d0533050f010b80c00900244002d00301c09a09007401600e50300310510003041e0002a41040506800c10844e4200b81e940006036510603d1303002c4440c202000031001c1c050301651081040c2501407282c2c100014600000360400b51191401e038000c81128a014001c0554030a100294855030300d1082010603002d500c940d5501040a40180841d0502c40540e11041c08480d000507105400316901e07101d11001c40098010400109000d203410ba8903040140d1481d0392003100904024800d295803124a242c0d9210798009100d604080c0e041004585050121341d034840d0000c4601241e60351800c1803400013581c105035103c4c00103138256a1020281c0100c03c2006003910300c5103103076041c840030b503c158002400f80001040010b1283c00584840c000c20303e462032414142c94004a5081c0003200a003140396805002e80e400c40300402c2038002a601d0f110003280c0146504451355505010f021007880c00b288041c1c008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 844498210 1250 844496960 844496963
    0x1e1b02061908150d020105030606090612040c031203141524040e0f04050a061a12150744091b04090305040302190e310305030705030c1213 61
    0x94544442c104108401302090b00ca00902098081c00414aa81850700180c15040c1c809090245400c60900b0001c403003a00c2201d080700d107400401424420400da0b142c0b445d18540d11400c050001d104101150355001c000140720260800c0347c40820620356480c036080c5408502580d650101c25060440c1d03034140f40c0e00902501b052038600ca800f06480000d41d01c400d41c0305e10340000c0503140c0c84c0395694030071300070f0f105020304509409414506e44249544041c1c11191520f5841d00030b040e41307440d41e03510419804000300300f4418422901c0c40900c0c00304030701170b006000030458944400c0300a006440b08a072960142d07200d44000f0341075000c00a9a90740010700100c4503d4030145040d01312000c2080005440007404018001007050104000608107003000700008110060502091a00c60b900105450001c8415040c80f50130340010381e5640c500e611544a0300044500ca0a0381781a4544002e0410700c800ba10b8001003010020008202d10340d61030940390344e45549103d4912504004403000340c030390000c0d81c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 844499460 1250 844498210 844498231
    0x3061003030c170d1d0c0117100305010614040e0705130f060b34020f09060d051c110c0a1403030f0a050301051c0f141f0504031e1b02061908 62
    0x5003031725810009248441c00b10141d440849203404085280084500505540700c0d01d101c0020205c0003d60a0203260050310700301100b60300400c00302f410042916684004411181c100010501c071680310303070100f1840482014800314107500d280e80302070024600ea5102e00b4080314003080310062a9030201d000c1c5846410031282180c203c20349000000305000000000358400d6149655180d541050300c1c0040d0701400c02854120700c96903640f141400c0000c01e161203440c941d032007000c0910341908180c154024160080080c160003c020020503031028140c0540d040c071030059100e031089e99604204a510324105000c1c040e031a03a0b900000070703003943c000b03002d102d00c221505180d9206050b05c1028481c01d05403c002000015003c0740c955504010303070740d101c020f1070307000c1e00ca5107800290b581101c601c0d6240c1080d400045c945030504008003d18082c01494044000c10307080f602c1469032003150b00c040e4041c0d178020010921083d10014282e449003200c02c00592050408a82c620b0350498042440799082c841c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 844500710 1250 844499460 844499501
    0x1180f090c150e0d2613060c0609080a0e0307060c08030402040f111606050117101e14090f03030408041e230411040f09150806040f060b03061003030c170d 68
    0x640c03055008006c04510f88641c0c80ca81042001d1041c00300c40c0400d402148005074a0130107444046c05c81d80292a882c022030b251001d05511414100100002003507507107030071450307020300b0b50716942c8a110143c0040d10454507482502c03194030443c1d00c00703902c01031030307541c0942d03188541c0d03e129440100300a025510300e0300e0712000282042d10140c5131442c1503680c0e4040c0a0544d519040c000007420090804000038021099506214450388a00304851100b0402a1100d180881c0198903201450194a02c25002030082c8400604450141c4054407803c450078881c034a0341c1b2a40e500e604451307a2140f0701c0d1155900200c07054901d00e142c1d140d0740741425a002c4c4904070b02c10260369000d125a1040741004105d80c541000007401690100182e04c8048a0002c0c4079950f494002d0301d41801907070243c40e4400076140c208200075151080608a110580281a031443c0c0290800c10358030300b034400030307062154a0b8081c2c1d0070010a20b001d00d81039009212856150080012214000d103946005045010b045c60b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 844501960 1250 844500710 844500773
    0x170105070804030504030b042d020a120209010e0705071a150f030d0f030f06080309032e0203040201020102091201051012082b0501180f090c150e0d 65
    0x12001c0da44141d070182c82c0e0314034240c903642e91402c6114004009a600324081c50040240d40500076001fa1611076179035002d000a4040c0c0104286048542d0201410034807a0362250016103039254990b0468180ad805100c0d2075849060565045c0b185203002040c1c0740380010300c400503040040c1c4203800340d41074807283c00351810079405007d60b14048a488961646c0504540001d040c841c440154090149203008144402005420016140190401034290300003090045590408005240c10700880d00040002072298243e10a804113101200002c0700350000002810759000750121040000d007d040c601054000c400b650b802030506079401511100035400000d200080c0701c03055580d05030405041880c04015405803481c0c20307803040b001002190002c807489101e50721486658000c100b00c0c0c1e142c240c0002c0e5401844101c2d200c001003048164601a800b0340070846158004094500c038513903c1900c03040394a170903504440078003911640b10805501090030001502c15010040120080c52080085c5a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 844503210 1250 844501960 844501967
    0x130b0304151b170a060e040b0403020c010c03171b120901050105010507020109050d03090b040e0a0c0504080606040b040b0d111c03170423010c0915020304050f0609090117010507 78
    0x41c020000711400c80070f08071184000c020700e070085050310300018540e541e1200c022601000711410b64403621800308000502d41c0510089070003413000d00e170a10441d400c82e03402400c3c0c0b24010461128031104180000c800c2613958200050b040c1c0c07518091a126044044100002c0300111781002d055400c003000010554000c0d4255580558140c541842481c00c0200f03200c0b007103624100641c20080341d01030001d410803031b500050010340112118440980380c0503541000340c0c0c100c8410b030403c00400704000c101c100d001080180d0054400c4502081403408400020080e000c034050702c81d40611500056000c2060364195110f010400f5101c0780c00c9101e85141c05404166140400340226426054400c0b440002400d8240e100344242c0200c640000d04114080c02c840d984011020241c2d510b0b0541080a500508008000c1c8203070303510b00115810ba000005e4484c0985e01c15140030310303480001e21955544420030b031100c5582c0609039500f41e69503100405552000c48a5500e90f9518210110302c8131440b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 844504460 1250 844503210 844503251
    0xf070c1407180219180905040c03120f09060804080a030f090221120313080309011e1d0109081c0905030a090614040302032a03060708100b0915130b030415 68
    0x400310305028186c0c074080c07481e0050140244200c89600f2001004400074000261415402c411a59138070010716041d04054a403610a401200030312011504020009420b001220349886c007601d0003040c200301c85003c0e40007030000c55074025032000400c002d04044118401401c540811f031803003101e441c100c51804105051000707880202c9500030b06205840400da541e4001c540120380d02000003180300e91480503942c91940c088500c0b031281e07141d0036180380103504809000030308801031001700000741040c1d84044462007101828980b050011040c80343ea00d4143d805018401e4009054969440130280020f120031124020b0b10301091040303038020316140d2098252401d4aa004d002003040c104581c58a540c20010801400d46503003200c8208001a10140103081c041c80301511a11140d0400420100200070903400c592a01d400a0001c25000e03075502801e84060101c403241c0315030710090303030a084400c6912504840001d0b00000184403c00640441d21942c43d04140410011460703004c80100c580389 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 844505710 1250 844504460 844504487
    0xa0c030e1e1e0d0810030c08060103020f040c0e010e061303051e0d050307050d020403150903110c030a020d0804360209030c012a0501050a050f070c1407180219 70
    0x140040b400d070340f18501855006400c80c0c041060080800d03540e5440902044e078a801a03800b54012800402c00c6041607541004c18400407a011701212140340401000d030b4200d40c0181f41000000035110406480b01d030212080c1c24583d058410f812030f12410410781ea4240d80c000e2048440e102e0303560011410001c265654452003036a00c0c14695107400c14100d9031030704551280d5803082e03403c100000005503900c4010207200480c85010600c4451820081c002464084003400e031500f00721441280ca85d00400ca5503d0700b0741c100c80c12140701805040c4034550b80583d402851104000ca694141e00c55440c0010ba0a041140341000056000305000f03501640610300005415901201034814190b025000701c0440440f50401610711421b0a288100b25454a10341542d5a9555800344070100b01c0c1802901e61115a00041144a04002000802c0610801c00162901407088040b10603070506128000040c00f4400043e04e0035000354034404001d50200115210b40c8200c03010031000d02d03004520028020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 844506960 1250 844505710 844505713
    0x70320030307080309073602090625050a0c0f06020313050f0f0402180114130e0c0c010c05031f050a15050c06040321050402090a0c030e1e1e 62
    0x1010ba80e501c5410340c002800c02d0036903029107140820740f0510000801350311580c03105503200640b4001c494141980030350100ca0307009030040080750410780b106412251b074040716082480c0c0340007035141e03444410040100000e043c1d0140040107014440003070200000d440c003003414102940d645480607070703a1307214000440b510802400030800042c60420008031010001800b01410200340100050403a031002c5030325082412040c0080c5100e507484034031008003402c1000e8242c03820100107550900000544501c44541d0300c0000004c65120310382043c0da1024118034001d121f10001000041c0031500121800210314035540c00c0b400202e6031414032030781202c0d006040b4141c110709100e09645407803100318012091004c2002940902d110030407209200c0c50103a17858160030030041020850703148090040302412030801041c840940d0b00c2d00c400c0d540110a0500014074500d10b900194041c1800c503e10300000c0c080c184030122403082441c52510340360407590503100c8414590150783e100307000200114003a03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 844508210 1250 844506960 844506967
    0x1080d022a12010f0b0103020c12030c0c0d030f0b01021c120908120106020c031c030f06050612101a040909052514040204050d021306050301020c0703200303 69
    0x801c8245040e0a02050a100801540c5100c01040201001c6152a041a0355a01050100410341d21a06405030802d2a082d461301c400300417115038811050348a2200700d040000031400e406000400c40b4040f283e01c03401e854100c000644c01400410b0100818078030706080c614264501e61010075400041114000181c200c0c0d1459041180c0d00c1282864141031150b440c00386c9000701301c0005c043c00700e624014640600310f6044c444001c0c240510096403d00980c0721414240c00348196882600414170075140001e0885500c01403a07015103159030025802680019080c500f054440360b050748075001e03c18041c01455541c0700044441c0304001505690100c051109000c0c40c401c1f40c01200300540264116607001415415a142c1600200140d240305480c0c80303400c11100c60801c03030745c1201c4002240c045081c82e19040c0414550724440c04024030655110040c040381d01c10941c010790103008003500071910781405085482c1e6a03007a5000c159115a801000301107800f03400e048070711034190060091400d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 844509460 1250 844508210 844508233
    0x61015030902130906090510230c13030803071d0a0612150602030d0606020d09270507090e010e04081c09080a0309061808090d05011e1401080d02 64
    0x10031001c030741282e001c91211807200101c01580035412002d8080d9070001004942442c0c5580340070356410742101c590b401e12014503445046005c0d040d140607020000800c2594070041014a644201102c900100009176800f10a01c20b103034014512400c0c0036182d445c080a0b4461414009100003074100350b1188205038107100d0700e84140800c0c0c0c5070a00c02e00c4080f6030340300c28680f0541c4a80c0c6030f801800c0141e2010621070071625550203008000c040d140050802d400781044002c5c03058945025000503000001104c51400641180c006841150380000308030034140020000d02134001482915042d1082e0702c00800c140300a012081c0c02268014815460329281801d10001d8201007041d84070388607594030031800810449001802c02c40030039980001c004802e45004422a200c2c40c640d403500307464212544001400440442d07505c6042101c03400d030440e01514201c2d01400c1d14801c25240440c2c0d1240690b46806903401ca80d484140480c54060030303031f898160301d81d0340308407001c007900041c2e002803843d0740e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 844510710 1250 844509460 844509467
    0x3030301090906021902010b030d030203010e060f1818010c0503010b07061503050d0201090b0a05090604151e060e070221071104021303030f021f05090a051c02061015 73
    0x42c12180300e0301025042c851a03020300c0601548245600700580d440d00640019460f05110880c3d003000581011030943d410074020503c070400007004e2a004040c4031010711b070306035036104196401c103c5603091451103150503c0c81c4485084481d00d850150b44c281160700010502400580741601c000b4100395040c01c000b91a068003400103a010069007070360800001c000306905001c0480500307141d4001113004c01c507519141c0c03ca0366000b0480c4901c1c0d45401c080c81240000480c880f90416048164100f003175080c903c00398001d1441403400c030400c00032205d02044400164108508940e2203d180014541e10194140e0b1115000c40988c458240000c1e000701d600681c090240195a000d50388014071a40b1000204089a103c03158500707008400550400802d0350002e02c0d07029052280c0301030200720000b0b854010351407035000728100301036445170006030752442c00b0000440c0d51a0020115a0700c01c40040c440c00c004101681c001e001805108005095100e200c1003800c2158000300707190140415080049 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 844511960 1250 844510710 844510721
    0x411030f071103041d0f2401030e010c02061603051317070816141b0904141501230f06030402032524080121060524030c0303030109 58
    0xd060000a0882c40300c07254080000e0009041e46050a8018000380400d505070100300034003843e403100b044010441054001150003540c211000e071900d240c0f80690005801178400440358a0301c0c0c0d881c152407a0003850340040c1207401000368014000c00c8070708440c001c509540c0201d410240440004402200282c42c0b51a80500ca480d068400341c00c286456546502c140d02103540004c00401c50b0724420306100801408880c40b0240b880103003007010490301c0f820901c034880115544224000c1c4e000506201034211820b260340303040015101100400d4088004021003809200d0940d400600340d031380750050312051484010030042038000f4000810741004003030f0f84000c20880e09405a408020807242240c4e0207440000725002810743c1090410340c41440208580702c00341c041001201c00c58881c2038000d0482c606442c0d1150302000302a8185d10783d031110b0001e2070001041e00c0d1070102040f044600030107201000f02240f880c8c00c01d031804403608042d601c0c01d000100720b905400400041214410541c8007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 844513210 1250 844511960 844511971
    0x70f050304061b03060314211315110d02070308041a0c0105040804090f0203010e1f030b04030c06061202130b010908120405030c01090e07080c07020d0f110411030f 72
    0x1081c41410010741c051001d03c41c1c007401c800f003a25100d06004214051076814800c0040d04000d00340c614040103500900c001c110010306103d400001c3c02c3c09552140100680940020311101c0080d641d11040102004641e203041d1606004074400b0800391071021600b44110780d000702440342003d0800402c0c002402d000e80600a0140f420003903c925094203001d000d21640c015902107031250320704800340007510345c014240c40105204100501c8800f5464004682150326004c0001402800c00042380c4135815507040904500100001c0004045d805a101c0c3c404500c1258103009a560301c8500710603d20166100a52002c1381c42ca1600d103050b81d43c3d2140140030740515001018960700c11406003440302c02c803030242c15518000303000d0115080c104082c0d002d21800f868420700181c40c05a02c80c8403824058000d0741005030103004100c280f0411000c0c4e5a6041d0001d181985081c001d00e40080088482142103881019560400b501072415114400016000d0154140381d45e4403030030030021902c0020103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 844514460 1250 844513210 844513223
    0x3020d030b1f11060903250302191518020d02040e011832031606140f0f0a0209210f0303010f180c05040b0a231809070f050304 56
    0x31000c001220080150700c0c001d0b495110781a00b00981c041690410304020b115082c075602c1000b501c0c2520100c0d80d005c0c03001500d400c4002d8401a46883c040341030400b0b12100c0c3c04d220610f25405428042c40d0105080c10103654481001144030814502c801078209402c060b51120109015001506068001d04800d0b50400000141402410380484890000726425202d04601c0704128014100c0d081c65080c0440d03a91014454070340c0700c3c103600365803403041240c1803d5104c16518400c2c02c00805800c4142002030f11005290103103030800d60020244d03011204840800ca0902c04280c41702520300c02c03070350f0070700014103841405002200203009400c0340e456528000e2185040e000b11075075042c009140600183d1080843c501e10f000b0756012094080800c03030000e6441c2c604c0707203220141c0280c00c6504640c0c513502800d40301d4200031800e0783d03071390740c0700d030040c9a19209440c102601e80b0120f0b0041500000721501c01080050b14424005c0c200d01c11545c24001c2030340c40d0340081c070841c00703500a141d0042c401e11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 844515710 1250 844514460 844514479
    0x3012607030c05130e06130209060904110d080f1c050f01050a05061e070807021203030708041e02040f0c020d030e0c0603040f05030a0c020a061d0913080408060f0606040303020d030b 80
    0x5c28146400003c464013101703e650020703070504618161100c03d8001d14115003030303000303814036440750030203a100b4a840074030421181400b0020000d120041d01d080341403490580d41c85002084c60000d99924010400c0c0050b0300d060000f66880c44404c910760b058800240c80045c1c41c60402d818005164007246140c00155949000c01010701041801000b55a10840c2655103d482a00c144040c2c581030841d00c02032a007041c01080952540b100d0f00c554002c0d0030481158000030b0340314070a00c0e60503e501010350400c3c00d1211031030700f2401030f4001d01c840d0380c040d074201d40e2145c40e0ba190071000c45024074401c1019401a02900d00c0ca40703045006140c109000300034800d154100c40d45c559103194003000c0800003107048420030340150f24021050750024100703414495401c04001401c50350011413108114450703e086030100c0e12120a49110541007540100c6007941c46440d00303003c45d5140002c940b2030100140c4480080c1c1d003400d2140590702120b074075030020302044109141c2500a051049011600030300c200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 844516960 1250 844515710 844515731
    0x20904020d0608010501230d02040b030f0610050402070f080304030302431a04030e0415140d02060304030302031b0301060f080c04060c08090d050303012607030c0513 73
    0x18802410384010030700c000155245000380c0d490a4400503070140340c080f00f50348024001101c00200110074550f0840f5417202c0b40c45107200240003072004c0c0350499014840c04039001c0d80c56000146142c025404d10350320389902d940d241c00308000c0c1e1003484801003a03081c1c0c522015000540c40b02c00345400a01c03e007009801e106d40d042d00e0803007080705002d289111985840000506215951400e92440100000b0442c96121915407507001000e81101424144c510b80005040c1032041181e45100c00000b07005012084c000004a043c000bc68000c910402061160f424051700c1c2602250201c51740c05008a410741c1c3d202d44090b002904014071a000018a040312080c0403085180151b010341078549a2510580503004000c0404600508035040010100001d001c00fa42007403504010356809041c0c3e659409950300405c80c81d00309075000900324400800040307203146803000ba076031000000300210080d03021100c2115640b08118400505600091081030201e0b0802d842a051506804800130940c1480c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 844518210 1250 844516960 844516969
    0x301050f19200f040603060504020306060f0a0917010603060b100c03080c070203033402030c04090f0b0115021c140904090b1f2709210807080108031911010209 70
    0x580c45543d65240000d070a001c1a605840380300d0150406590850a510f00000498400e2240c600c0266a2001c0499491442886120a000949041c1d40b9000001c081ca038078590180005000449070305052414001150070041c1ca002c07181201d41e507906c6d414083c9a00c05403070603003000c0c003027003203202c020010140580c44c208000c010400c1c1041c0e100d1810140030846006072514040c3c0c240d03400c00c240312200050780d000650008030550840700007420340403501d803924001c0c40c2000e004141d03158100000601c01903011000e10614502d03001d42e0100c07141920007a02201c1d642c608500030400b80c42000c292540f00c1d00107000404e00c0900006442c1e41c46d92280c2d04420021280e004200010300050540403c6110400c4010039104108680050b00600c603241c65190000d0b0185585035548020814024941c403c90450b101d0341b590007150500001004042081c200c1d20400860004400060518400002c507501d00e6580404058602c24611b0200c031005d00c800003a102ca0b6400f0700181c4241d654 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 844519460 1250 844518210 844518217
    0x40209030a0506070f09060c0507060f0309020a0f09060b0a02030a0810032003010c0306050901030b0714030c0d050c03070c0f021203400603020c03041a090301050f1920 74
    0x1e640c3c171409016071a400c0300600c20702d900c0c3c009004101c2081c03800070010f0f500045400a507449030400809038180c0c908210020400382e54080c0d40011000710001d4409030441c9140d05480142c031092128645811189020b4417a458002005a004200e071001d250310030720011b0b0300503041011005030941d807600c880f450625004a0a4802168078440c0700f09031409102c1e03240c6042c41420b00344403a51410340080d0100d00144001740c0900c4504002410b800d01c9004214240e0006602490f12824400a42001d5802165100030300718a48408950008010004e90b482000c150f80c8000e106d64141e902c582031180d4242e0b00301e810501c0c8030960714414400b8005011281e220880d05041000c801c1d80c500b4a807245190018140a4018020310070411100c12080c16030b071183c240565900980d4a003a8030310301c0b45900640c05280d08801ca40100701d00c510090004800440081c022a299904a01079584c0d0070f0b40e80d00d000d00c40d08158840c20030301030b800c41310071070682080075014400310005280b520761 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 844520710 1250 844519460 844519471
    0x40206030f1b071b080609071a040f1203090b03101403150115081003031e21050103030e3c03070f170105070f050903100f1a0102010209030c040209030a0506 69
    0x6010303140c4101e000203c04c8288000e000c10750081c003c6082a01c1d103142c4680050290b86c481c480c648203101c99840244044a00074000310041e00d8507550389520038040c1015240f412400240b41c8080010060b5001c0262401381a16005031450310703242c91080b042c0241d0324011941c25004856001d0042c94960100e64000c01000300c03810090601d01500820060b8020161140843e075081e050011980c86280040002e0785410140100c0c1441c1c0c03801d9072603481824003864455407442c0c0040c100311090300a44c3c1206c4c1f09455000c440c42c846010440c0e4189144511100401c0c25080000030060b580d94002c0010300e0b40c42c00f1046006244040307401c01d600703508240a581103404007000f1308440c0050420400d40000002c00c80ca00b01503a0050004071800c40100030020042219200c0c0c0e9002d2151003143c0058010820071000b0105070940503046d280042480031600b1841050654010300840d04c41c0c0754014060800501341c0b8041000a401013182c00d50076118451885001680812509010f80e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 844521960 1250 844520710 844520723
    0x1b030315080715020a120f1101060b0a110312040312020705010501090501060f1d130204080f0109020103060b090d02060c0102040302100e1009060503040605090f0718050f040206030f1b07 82
    0x40b8200308480181040010f901c80440d03000e880350703a02044e21441c00d0500c241036451710800341c0391006011070329811001e15003a465440c0110000c0c5c1092501e00821681006072100140c2c1328010030381c0c42d05c0c0c3c0540405008581c0460000500181c441c200d00c4581c000300721070050500d8925107855003100d10980280d103241ea5504010b000c0310360409503045001001d4500f040002031440d5482c0140200f9204e41c40c024180c000303400f150500340341c0554011703180039004c0742c103141490103210740a00507400050340805d01c0c001c3c01103801d40c080821950408400341c250504c11034640d003440f1640d401200240303501c2d5030a1101100507a20110b00e0446204695142140341c002a01004540c41407000c20320140401e240c400c0140940180640340d00907041400020b040c1d4070911a14180941c45a500142d4011b038280455440324071480e9100801e2001c2e01002140e6510800c4c1940c55400d1380d02075407082c000d00000320005443c1c0072041d4803074041d2511801e03001800390801c0450b0440581100da0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 844523210 1250 844521960 844521973
    0xb1b011b02014701030f0c020a030e090c0901050d021608070c090515060a03200a03060e010f051c0b0a0e01140c030a0b0a05030303010f17030403031b03031508 70
    0x1055100c00b00d4640c66540382000000c10040c407120002495a08a00b000f5650541880d10301c0701d03030080d8414580500a040180840e40202e0002900d860382c08501300d01003a0000c0c01e05419080c00c40c0d000d88200102c0c0c1400349040c840000540b6550003030400b000d0340b99001c11100070301e41c01103513108082a100d41d10481e2610410301d8120044e042036048414094a05030400405002078110805402c4041d986103580302c000c10b00840c0039007502d644043d52110386658200c102c012035002042e1180d0269070802004e0f0b10307004c0342107010100b88216a44009031440c00c0c801803408006501102c000700c00e91889507c00d0f5607038841500c00490b045026103a440d003c100e440c880a01a5041800f8070844080c182d1514814080c01c0380406440030070702e5555042041c405884080416014050007001c4175184d40e510307281040545041d000c3e200b819a800d20755009103480000c1a201074941c0340c1c8682480d04400c1ca05c25a903c41c4550055040640703420801d004c5050f1801c0d00e402412404001d000c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 844524460 1250 844523210 844523231
    0x20c0102060a0b0906010503061807080a14041106090117090c010e01050a0c2013051e15010f05091f030c02070f050d050705030609071505040b1b011b0201 68
    0x180303100207203841c10b041d0038081980b01c2991801207980d4098005d080c201e40300e45642021919807a181800c441041c040b001c144800c2d10741000c0b005115003134884090104001c4518945601e00c01900c000f889900c00031909081841c004c0c024042c031001c1858103800d004941030407031502c4042950009416004561000750550303000121b4042d5010a00b4a07900d0000c601d2801444050070240140c11041c1c6010750b10030095034042c80d0111240020036940d08a00840d5080303006103010348000307041284070342c0c80c48000070444840c2442000b6040381400045264401990103540900b102c90030003070100032403099984c0307004403060100c0350001d62044006101e0310240445054040d1076042d5800001d04100300341d2403040740e0081c0d40003a91400c1c1680e51520b0b0a070318101c5680c00056242c0120410031041020004580c0304490000380034821400010601740d80c944542d0003164005c031810051420301603c100712110010380840c00004d9a81c1210302c8a1224114482e030600050751151078451 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 844525710 1250 844524460 844524463
    0x60909040309050a0609500406120201021203070e1c06140c1804060b03250302030f070c170d060603050901110a1b0f060c0f140a1b050a03020c0102 65
    0x240900143c4c02c03c0c240c11414160948070384001e030f281c42c40304a5080c600000202e2241c7c80000481003004055490b40d43c01c001c0340d445482c4151442c180076620300b860024000f036101424150081c3c040c0c0141c03c40c030b0401086214240d000130800c00c00d100030390034607840545a00c44da04500840d84a41245584207900e894019030f690700c1010341e02c402c9503c007841522a641c208403841c110b40d0408071101c3c40034840100e800343c0300a500500304180c020080010303441307034a403440c142004148021151f00d91501400d40c202d02041c0c2e03161950800006c00101c241740521000c210550146144100a05005000241c50f07444074820b02010f13612050100291601402050380240d0103500030321100804020440300c0b80074070a0340c0301c00c00807005210303040001e21189901c005c0307402220200c5030107218207141000d0b01d1804c43d40c90002d0580c100c0903c4051203503800651381c0308060ba6461a00307094090440740300104940400301d28a000c500c213000140d0030420321700c1c45803203900034049003075848001a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 844526960 1250 844525710 844525729
    0x213082521050a060b011826011508060615040305070314031b0f16050d020607033614090a0c02030d050f09070f150f1209060e06011a071106090904030905 68
    0x2010140c440180c08d001b25a1a003205101c0c90307542842c41000883c503000801d024002d40f040c071900c400010040071a40100100b00540b1840301070ba90b0303080e01040c6105a4040d84214400a4158ac0002500740001204101601c0d41040b6180442e8103082c581d00158212400c2c541c2c103e501c5a0100c074800c0070910007400024440d11440d40001c0b841ea15040124500341101c2d50000e01c11440001c803202050b00610341500d142280030f000d80001201d01c0072200c64115200b8190001082c966000182104c90600840c0d0a45020f00500c1840d121910f00c0006084485039501c190b020912032001007074114865a0b02c10300300400f05003e80d0070810609410000c03180c0121760310b880c100c6000d0001c282d940102102180311440c0c4050807a2a107041100c5480950700c03440d030803509010580301403008541201c5541c45400003034a1042c1daa5905402101015a22050780322400303020a0003c200520720b41104100c0241001d4507040b1035600041e0b6210086a0440c00b0401038103060040d0704000828 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 844528210 1250 844526960 844526987
    0xa050f0d0f0609060605070813150c020102070e090a1112030a050319090201140901090b03090a1a10050d0809060f030405060c030c041e05040213082521050a060b01 72
    0x42040c4c0e17081c5a4020824810030b00050002038000a0560540540d40c9000c00244020314019808034a03070305000b4030f000d49012082c0d00611420318041941c2c0e841511040c0524014802800c6041150b9619419500032a08556001c0da0050302c14400c441c0501c010034580850b83d40d026600c0c6070181c15400701e2403407292041e409518145440c8010317601302800c481c0100d810001c1544800d0040c0040b540189207400003154418044180403044030700103081800503100c0d20880340d600481c0c008603000c0d05000c540365008130b08400d4082006041c0441188503039400b07400d85600d006030060201c7d003a40d100390592684510004104018800140501070708003181410b520b2850516090440482c0110f000f00142c04007500000b00251801e08000c1c4003c14000d40159220718540030090b44da000a4410000c860041e110b0300311034400c83c0c0760803c0d282c117841d120404e0103908000c4280340e206c101c1c509025030380c1620855040407600c01c11480c401180300f2003002c942880c0c01303000141a80400c0c081c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 844529460 1250 844528210 844528229
    0x24031a211b190627080109080a02010e01050f1311030703050c0909150402040e0a0615051804020306010303140f0c030403030e0607050a021219062c0709020a050f0d0f06 74
    0x1042c4031051380b01500d48001600da503007807031005031035501004d01c0a5055003d24110b40c41d00a02004014048c8041e00c42d41d05260000c00c002d000c11f14040707080c3e4034100d5030f8803580e00110000901508075108810b005e20f0190038189400c400c1c01c804a0320b000038580007940c1503803090003640c11a290400c0742991001d01d4101400d02c011030b81c42066203e18010740b000340304a40356501c0480140381088640310071500110240f114034101000101041e201c2d01a01d401084140081c58042c118040d400780100d6000c1e00a00c480d0380b840d00c045840000b21f02e0f0368401d010b010040c880c07001d11102e02800c15221040d0207180c2e0f4615518000d0448002e55901500500060105001003100400c1210486805865040005010b050031509041d184071807680c146c2c151000718414070840c3d43c80507085956846600031407022903680e040031501410110910355205c103806000d080b1546d0040e1843c031a0a0130310505007584c00840384140e0700290400545196074814080007910280200c1c0010006550f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 844530710 1250 844529460 844529509
    0x1120f180b04061512020411071a06090a0209010e060c070b0304060e0c0d02130c140f030612010539030403030203090c1c0305090d060624031a211b 65
    0x40100b0017001070102078440c60b500d000b00d141c110f00c484200c4900d241e1100080f0100804010110b82881c01911110301400e0a40009002c60205100700e45043c04141c6801d03040b0121001040b40c40c9c0c0c03003100d1001c4d40340070f0200001445c20a81018500481c420032000c0780041100d1141407414030400070b100c1c850303c620254030700561207600211036146d10f00840890fa5021404058480c4961030584a0214500250140e1006401c0c400345010708002c858030b400454405041c02e00341d88060314140f540f074001125909101c103081034a1000003c03070400f09a206400d00030060155002100e0940c0444c1d000002c100c01200244045407064100325000007032003032108020100300411840080a100001444030710b959101e035600c10080b503000c0c40a0014a0b05d800d41c4c0380480d00718215060000121280d190074050103401140c080841e4028010500c00b00d11080010b480e800300c01e040010442c0da02403005d0010144943c407003171042220281030341450001403166106510414480082c4084d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 844531960 1250 844530710 844530719
    0x110a02012304080703030b060c1b032e060b0307030b040c08070906030e0309030102072a0305150429091e100903021f0b0406050f01120f180b040615 65
    0x4542090304942c01c000040d403901011703d4150300900ca0384503696844039003c2150742005038009103101500e4507804525944440e40320505503680d80035071008072461188080d500958a44012201a105c1030840200c0d44a0352280711051550040d01e0310000281c440301c200105007001e02856030305800500c1c101c0700f5172412080041c20090140600300406460b10140440204108240c500e06200140215039944280c906045101d9801080c2c40ca022144210341841b080442e040b80101d0350000060701d0310008012490300d15100080080307a5400080c0328104070307040c00c14458509900c40214110013408c00b407283c5443c1241c0098103041100040041003400c00c8003040680200301c4090001c00c0001c61031401341d04244900c60b8440101c184031909185685681d045061280019107040210315110018803030401840355140b800b2500c00c2c04480785800256000e02d454140d01c0c000080d03030380c000c1c0103500f402042400d8107490041c20729041c0000e10480b4030900303041200600c594400546803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 844533210 1250 844531960 844532021
    0x3021b0c0d0b06040e031207140a05040b0304060f24080a050309090c070b0c030106030501060c082d13170a050613081c020c070504050c1c0f110a0201 66
    0x1651001414082c105010035642c1d10307140c100c10004480482aa07486101d204a0707001d1448080f145c0e90700191549510b41030704c1d41e030f410490f4103007011551114035103802e0100b801c1c102e600203041140c2640d030741c0f100003100300d0300c070311601040fa5090320f80403004c5002220035001849007501700114582100647c01c002070000001c0b6850312105480141d4285d803441c0085126004030302000d000d84400904105030010700c5c0008606a5000b45c801b0486039880c1e00080750404640b036002428100100000712140c2c942d511809215000b01c0c0c803100c282c104260150340241c00207410b560460032004428407149280e03921101c00700c07820800a21070780702c20b9210740d540c0d044050110104801e00c0d41207241808030520482e203406520401c60040c0b9203103541094020340c0003804074413644c000d41d030000c64285428028680140d030409580340c20910031220230302c0580002107241e45c100380e07610381c2140d400c50309015030042601c454030001c1c2c80f100420030180c20341d4494603415403440801c034040341442c0710 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 844534460 1250 844533210 844533229
    0x1609091a042c010507200a08281e050310050a061d06070203030307210c08060306070f0806060a050c07030b06090109051b250503040915080705040b010c0c0603021b0c 73
    0x664107642250040644041e09103d2034a4001c2c004082c0016113403c105050392400d45401d580c111551209c0050340c508442d20b01c200d840f0700c0400300d160082003030b1041c8140c0185400c4610340d0b4606210f56652000a184e40040790302c100c2c003141d0190304c04034580c1da0600600c10101800e8810a10701401940004d48a00c0014004001c3c0070310442d01c0f44405115182c080c01a44c802c200800442158502c050001d6004443d22486841420006210709108021024000115449285403929080208580c50700402c0718041048024000075400481c1000000c1c000c41c002c1e200e50b140780c1084002d01036402d905070060442c1504110034000c0c0907410760b234440054000030070a91781307540800d54041d0a820200e004586d03184d0350101c2c11814044048004d200312262204c040115181d21490000384450f24440c01e802c03a04508420001411b00e030308004000c9605141c120102141e9581d04855400c16410200003c0e0380401c040241140d070024614501004000814003141000e00003107100c0c0f03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 844535710 1250 844534460 844534487
    0xc01030b1003051017060609060f0d02040e21040e0702120a0302032508010602010b1e240d020307030b060c1902060d0c02030904051609091a042c010507 67
    0x50b074030f00000350340c0008440da080140600000002c3c1105040841640e182030658205d88038803940400300d0300038035198007000c0e22a00040c107a4100c000032502004020011100d80445901a2440c1a440d00d180e02c68990354006c001c07240c41e9111800c0044c05065108000c1101c002c0d0341c8200142c1c08400141e005031900201c2c98500540c0c1c80e6290750030303450f410f11440c1000510080242c1c2103c0c0c01034004260034180c50182d8001c110040c150000c100a0f00500750a41d010b644d40341055a009080c50f80c0b00d1680302e450741010b9819000d0594003680550b106101c3c91104543c040184524603503d4040c000d08035108407910703806d000c6410440d41e2501f204802e50110b00c2c1d00d881c00303070046443e42e40603503107031882849042003003510122010b074980d070080d030f1014840d500c0c01c80040c4040484644a00c03010b02d0325a42c2c200b0b102c0c2080440340003841d405410341d0342c1d40090400c2c01505c2d6141e00030440c0c6454901202d010040202140c0ca00910610025650f0b83c1d050000700320074540d002e801158001d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 844536960 1250 844535710 844535717
    0x609010e0a020d090f05150c090d0f051905060403080906010303050306060703090807272304050a061802040f06051e0103020706021815070305090f03160f080c01030b10 74
    0x810310301d04604024030742c640c0d000b81814107030b4000806101b03002c02d000000290340210149182d80d0030b00031101d103110b003040b0940d0254030386203141c02251103004440d2040e8840e42c2115052401d00c000c009014803c5842150103506c11802c0108140d4480302060308164020020901941140e4000e465808001c03c441d0184a0102d90801854850f90305640180310407400c3c0c41c80f09445031100207004464040c815840581d40b0a190340451481c82501b060107042e03030303180601e01805808101c0180700640195160310443c100000814021f10854201010254000098034418030500060350550300009100c180780c44002c008548a030341d01c451081e1010440d526124640d4001030307000340200302000d40b0540c404580c00030710444003800800003040458107819440c0740d42070007004030302c155003000f03001520902248645060042034880729040060980b1101003084401c05100ca0180d40410184015a181000421800c0c410005400c400707290520190703001001143c00c2000020481d01003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 844538210 1250 844536960 844536967
    0x50f0c03062202130204090b060906031612020f0d18030e2101141806010b0904110721110f070533090a27091e050105010e0609010e0a02 60
    0x35215103280d2152543e801041040002c02c103030a080300940003400340d00b0620345404a140180d14100060381c4032844000c2c500307132455440340702d66a40711081030f500c40244120043c0004401c0100d00141c52080f00b00c80308c0710307120745e0480e04040565518a014844040d11003182c030020a911404580304000e0507551a400b80aa0401e10104c150010b40040701c07a52030100000d20003c6810b19140c001c0044400c013860360143c1d0081e02d40c030b0f114280b1440f030f038220701040407800e1410315400015061400c82c01e2981404410345a4445101c404015100c0e001d4401c0840081c250700b20403042c2001d045000203200455040c2d0f0410303074072111405914460400c90307021442c01030b88080c09072150b4208044203810421115004c0000740c2000b40b45e24451404044041980042e441c117189140507024140e41003861065041c80c001d052031002542c8440349044001c0c50345044049090042e40f140000180540c90b24408941e1028090101846182880c00400102e04c45040c441d40000c02a2001685c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 844539460 1250 844538210 844538251
    0x1902010e0f1e060f040602010603120206091005100308030f042a06110705040c05192a030c12090302030c030a02093112080901050601141804060e04050f0c0306 70
    0x2214050541c2544d0100d0000078003040d52076064024804407442019800e41d884e039040000e13601c400040b68055410740c8000008409880b1070317084150010580c40892a25644076141d21069500440300c0c48580f84032070052004200c40d940b940d401d0902000405003004404030142e1000780a40d100301020441c0b24281d49883c0c0d2000d0203d0401820300070810412084000300103801a045034940d200e040d035400700c0045071070f4010303e01000590b1041c1a00943c0e112403138800c11081c0c0da80035082d030404c10150a00f0001615000c05000701061649490851600d10300c1090b161000d100803150080e08050715090060300c030b4040c3e4030b07041903540030400b02f01010084507080e152000801740c999a84000c0c8101c090040c0c240d0a1203c429040e6210302d0a5500d42c0d007960f0a03078100b178036041c0c005511001c0e62401283c0c3d0f0806400101e403017681d11540c1e00c60351000075060714821303040302c10700148070400e10080150400850a0b00461140a041c800c001c1c90006610b44400030b1005407486010400b108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 844540710 1250 844539460 844539469
    0x6010c080c06091f0603020a0302060f0c0706081b07020603151201050a0c110f0c1e0604090606092c07090e040b04060c0c170a050405031902010e0f1e 66
    0x1049120741d01c00b29003140ca070846909035142140c1d0b03074800c541c441c403204001c1d00c1100d501503102929005846549040d185900f03114070740e030010021600500c0300740030003044400203000106c003c050396a200d495034100442c410050400003007902c01c201c0030420450780180c0394002501d500680303d10701960300d000c0307546c003007400c00e41818030000c0e09520744401c020100c0800d41c040c0180403916941c180d030b500400490303156150380e0230348484400d6000c001d0300601490104186503004801c0107286904020210201d01e00384c0040d008030180c00d8030b0f10350510680d03511a12040051084091701c41066065600c0d0a007039482c5000c0149048080c030000072401402004144014010445c05c036000c3d2030141419420f001c42a0340444545003017071f01d41c56000e44a4201c12030080c0d00300c0f441e580c8000c861048c641c05940a03248610074040107010002d6540c0d0140140c44640c100f41442c80040c401e1031000502401003400100d2080d91228203240450303c13040d400102c1e900010501e804022500310000c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 844541960 1250 844540710 844540717
    0x14280303020c12120f06030a0f03030b030703080d0f020a0504061116031104150803180d0b01061709030304030903060e010902060d0204050a12023012042303030306010c08 75
    0x80c0c489100e243c000c00e2014440b10000c20b07041910300404071280d2900c4c83c0c600402c60302038071300c658140d120755032600202c0d81d114504242c1034400c0c10009030402c60040468145a055441030340c6000002c14802c000c0c030300d5409021011907990104600d48000200040c03c07a00031030044600304413550400c9401c908040104904000b0310f0b0900d015841c4d9a403420312845000204035900070385c2405021340a90525403034003000d60b0b040c04040c41c24406408821010341c603a04121540c00010b00fa160004107216111150280540d581c40c0c00740300800301c08130303000400c028081d44450f138400c10422000c6a8001c10f801c0c1604d03400b0078046602c8241d022010702400541e440a07500520000e030f00550080030303034014000c81d4815101000c2640c0d50b410300c060300101903a00690011030510004e08020140c07a1022140304801a210380fa000102d00707814a0b040306000440e40f00000010280007500c0319070010351405034442808010126090082500d03800003038049030601000c40c4441040040080c00e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 844543210 1250 844541960 844541977
    0x30d180306050f0402130b011209061b050a081f090f02120907050109120c0e0702030705161a0c0a0b0a110d090b0105060f030f040f0503161428030302 66
    0x14002424080310034942d40400340c4c1c080b40705400000f80c82d0780084a034001c0000d0351030140c480512040740454000d02400b1118400c594540d80e0701032113102ca00540d070820b800078443ea40c1c1e164448101d0900640001005040c1640e440c0020b11a400c104881c051075105440c1c0f44000425000e0750580c4e8007010b4000d03100031102e003544400400c4134040300020b082044600c00d80c0c2c0c01403640d50b5400421545d0b52540000f600d480321091041c0452545500842c0d0400a20320440b8075001c80f070703224142840300c2074039400e4820100031002c03c11080a81c205814004412041c0b030300c0e10340c524100b0745d95a030f00c103207005000d10100c0e4002842c51440d60300105003500307641001640d804800c40e070140241540c800c200c0d01e00580c0000030030075003005810394100c010352100003451911608043d4040c0d100003801240c8400e170001d2048006201070003d000561804104c0c2c0d50541181c0c03600c42c154413003036140c0c0042c0760b100c11801000d0041c240122008501645111510005142000c0340644140c2c1d59 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 844544460 1250 844543210 844543223
    0xf040306230f1f0e040609020604080303070804060609050106050d050402220509070f0b0f160f050105090f0111041406040902070c06020d091a030709030b07050717030105030d1803 79
    0x10031600085403244188101d129900049003024030500741c00f00c180351400303240c8580c0d1007400010b0001d40180d00c4030140b1400101101d0500c0d45c0c1c0c4d001035166074800c90319000000c5800c010b200422a2900400c0c0241020703000030300940d81007040c01000f501072000c2080340140c4070f402003015521414010034244070383c12049410308121503200303000780c003003518040d5107481000c40c0012039520850901041d56a03906250386407101603014104c0940008200c100d0041c8100340100018014105685500748180000300e95860904242da05006030301007200c643d0390506a120f1400a880011101a00d40200143c03103000080d0300803a10710b0141c2c0d00040c0b48030344001003e40502900009580c01c0354469403c0360b000a0803000c0880345141d01d840340820015450034402c68540c10000510341c4911145081c811040e580d40310782c80208802d442010104200003a200c05100d41c0f004032600c41c0300303883c550328a50f524240100f80e5840c2c0c600c190004000300c0b6845010312590300c0100e140110340225 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 844545710 1250 844544460 844544531
    0x8030a03020c0613050705090403110304030c05010f0e1302070f02100e120d080a0203130f111305041115191e02062a1309090201080c0f040306 63
    0x240050029884510109031600c1544001040508800c0d20140c1859010029115091800051040060010b0b00440600104540c2401136400c01c04c00340000b5070040e070026050915240002d06005c16054070423003006115501c00049868140740105a00e206110050341d0b52154240944601d0a4041c001c1d4000f00f20410525810351181c0140c01100040741c2c080e46506200d958a0740c1d84c0300900e103c1002c506600e0004541d002b0b5035024540c060b0201c1c0e0481c002c01420707039840c03251021000d400c403005041081c09019a007040a4400b0180d203544e2400c106505168454040141d0050405803103201d90040c41d03c611902201a51603642d0400c8070000400034032500a410f040800e603010b840c403441c3d420107400481c800200b090190510401e0f16400a80d809109104007050825180310311408201030003072401c54444000080195010004126603180700040ca4028060800781031400300313021103801884442c04480403a60711a41c00605c03122000e001c81001c3d15411000c0c4090084035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 844546960 1250 844545710 844545727
    0xa09141821040311060a0806040b011103190f0c02060706020c0a080d0c021014040308090304081203061507120c0f0b090c01081f0b07051513060e0309091f0803 70
    0x580508181c904c0b51505040c1d0411072810b226060051020701c40000740755002040007400c041c1c0c014400300d03070185010302c0c080c081c107105585594000d80c1240d007031909000c00d900d59582e00180c8503200f0401e43c581041003156540000381180980003002d006030b90300081011481204000c41183c103a807241d001a104c0040a00440c001c0603004a5000940039a81409540c020a80b01c0e035120264084640d07200341d103686c0c8040b00d12100061001c44984420000400c9031041000006411080382300701d5581c900d03284061123070907000c2626010b4135038002d001c81c500040b0041190781c1410703d0391811071281d1901d030900385504000ba1201030b0051111805211a411703003c2000d2038022001e89031301d0260317100c0d043c010300c001c1c05101c104100208260380510045a500f4003c1c50124000e008460b24108a04680c903000d0f4804d80b01654900c0940341d48108100060040109a01d00700c0095410000c840c00881c1c00b02800620400d00f400c1480d4130140d201c8034096082d40a0142d440469441c4c4860 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 844548210 1250 844546960 844547023
    0x3070203012901080a02220312030605011707020133050d03051c02090a030b041b03171c0204080606010f030501060203030f071b030203130b0f072316050a091418 71
    0x188c0c04180e800c0701c0303070080f186215802401204111041a50707114000ca10130103c5242d840c0300a04060119500c0314a8100440c85c99801100420406062280c0c500b1160703440b001800c1e441d5014a028111810743c15022942110903142c0002c141b141092000070500c0c2c2c0c4000900c14005034a07400b040a10000c400d00c4107200000d0b1090740314014a4410301c0740390003013031300c825003d2100510300440c0c00280c0d9940f1118034090040d0018220b80d10f21034605116084050381c0041e000007110f0752103002004043d61b8003106105001c00a800d0800895061640003503c0e480010080e0700114420700100355414850080428801c107030030400c0700e02c0507152030003e4896000310300e85074405981a85c081110780c100001c5804400a207031599140c05c0380c0341d480384601947d2469100d500007581c0c10002e9500024000c510384111164803210321641001c0801904106542100300e01c61b00c0c244ca1080649480360140c0d40000d10b1482242280c807413009801e103001814007904c14070900e20503840c5000c144 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 844549460 1250 844548210 844548277
    0xa02150f0406241710060b030601090b36090f0912040501080112060e063c06010c05121305040b03150f1f03030203070203012901080a02 60
    0x424102809600200181540429481042030f02c8207081284104584100c0320346015001220760199205040c1c00a40d4901701d0700b180d0b00002c40e0441c0013080200540c0d1242010019011040b4014106030200c04c5072000341c20502020701942034025000c1410300c0c9581c14462090100805c0200d03145403410031684590015105284188074806407044086034171001c2d1420b44506135503412081c0e103400006050941140415200030303648507400c8039090010700443c0e10410f0841c844407041e0720807a00480c00404a040200482904640c880c41e98a6182c00125005482440c2c02d188504043c2800c07030030300782c04120745071110400182c0001b00003840d190b4001190b0048034100b000840c3e45050503115079040c0700401e1180144000241d20403081c8034a82d8021136072600b510035000040c034080c1e0350000c00360026005607001103011411807509001e0360050020303a1403e80880d201c603d081e4988001200001da040c030102a0000e1440b04065069411214014446240a0b2003c000d01d00440e038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 844550710 1250 844549460 844549463
    0x10309080c0a020f0109082a041409060a1b0c170409090201120e1e12121f0303020c0d0201020f0109030801060f1b030c06090203060a0e07090509120a02150f04 70
    0x409113002c0d800540c0141c40100444080002030003421419910805c0f11502d50041080c03419000e500e00c014a480e02e00c00c560a450304004c85002d1400c084945130f00c2c01100070030942e001801d00581070082c1d20300309d0080712004842d08000800314011715051a04e41c0208150020b18080441e00182500c00d40c0c004190480c000e8036489007012240c0d5160054401c031407003019a5500410b030341e00d0742480800c180c0c886070700984140c0e2110030100080b0105a0b004a203050f202800c45c07000c1c0400d82010040c4c07058200501a0700d00e590a00d1503034003035290030040034890b00c9401480369650659000303001d050404090500204030402043c500909404070030700400001410904040c4a068061000b281c1070400e02800f501e24004103503400c8400c0c090002007195025100c0103201c2c0103840810105021701001040890043d080550040c0f6112040d848220054208420b001e071108001c00c40c103000e21100b00340c20faa28140414161324042c40d0101407500a11000e08020807000c070742c0c100c0c0780104d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 844551960 1250 844550710 844550719
    0x2109010302090d170d1d0c0f03031603020c0f0d05070b0a03092325140a080d03240b0f0906070b010305060907090507050a081009022101121a06010309080c0a02 70
    0x40b0700e00071240700c2000c021b10180045601c082842071442c504050710000c0008003d0460b803030804150740c502c0d0b00484400c0d040b0090380c000c9400003942c0c5031516000441080c15100d0041c2d04001e40c4885594504910403030303402c00f2000130851409031182c0c00c01c3ca0780d5034201d24040078211411024400c6070352809101c0000340a00410383d26420214600301030301e6400550580c00d0b10b410603550071045143c1d010150f60286000308000b90128041c00200340480540e1400200307403e40203600e00f841d26080700d0080e40043d0104d0140f01c12898032090307c1c00c061400086c82d8503030540e4004962280b0a06d940504000d00001c000000c02800081c4c0030700c11000c080507100c10701d986042c2d0300c05503a0140c412101044041c420851501e109840842d07200e4410111004402d5a40c41c42c00f08076840a00344900b01c0c260500c0c406100a1050b0a860051016014501103007a568403104000e40941300e481020014020200b0081e80c440c0d0041200c0582241c12035584018640c0c419a617a180303c0e0f0200d006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 844553210 1250 844551960 844551971
    0x190201061721090a09050a02070c241809020c0f07180e03030402010c1410061d09071a0c0c090a06180b06031501020a05030a0804052109010302090d170d 67
    0x2880752000650300c000d44060b141c1c91a103801d00c1580f2000d441b00a14071801c00e607082c0189000710352080c0b41c5800400308000001307a00d5a12084002c03c400056400c0000e00401c15909c1e540701182d01400b40441e05c03450401600d900c0c2401525080074080b2070780c0c0409104096010900045010345030903004800c103010080303400d82074410354803408225400390110f0f1060101c240070440340702500d4640035101066a560b600005000411600e181d0401100701e4490f00001507080c0403a06040d4115620340010a103051070112030008a2940701e02d81c044000300466900d40c4c41c1c0040100401229006240300100d00d003051f030242c010040c03441490704144840b0719807404a001413150241d03600026140340d1640e640d048110140d43c010015142c1188520804c000106009001030481100c190f0f4800d01c0504050030001d21f84103110030b41c2403185080102c034143e0405000700b181e00d040307020300b00540c4913100140064404290b080d4040d220b41060498600344080302c100404c101c014a9104010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 844554460 1250 844553210 844553263
    0x8071d1207260609010b011b11030601140112052502071508040201170f06040e0c1e0a0503060c09190b031905011d0a090203010603020d060608011802061902010617 72
    0x2030306c01d9076070f01a02081070000c000c3c00d1410b5041c000c000307450066080521601c03140740441c6c42c0c41801d0f071110706010070500c1180d0180da4450220140a0740d1390409120604101401003405541c20801181c01d003244610031a00c24000d2105100400c0d0014006c0011a952800900281c40454040340001c910003000d0b14007040c46044207000e094a0702199070b00b980d030003051000400003068070920350320a082103c102c2d0394560001200c0c1c0c1103c280e200b906000c1080c2480451151500b180c1e2103a080001008030036044801568441c820846035035110260490403038007c100e142d00110f485810001c20060f0923140800b07603001070304840104020f01d0784d0361084098080381c2c0071034800c16108111301185001d09990862100b86000400015409a60b03600050001e41d6507030048810b0340d00c40e41c08002848080c820b01055110460124098440c0303580000c07450311650f0b001204100340813100031161803003517200b0006896800010b00340000c0040b20036650b001e000c408070324181c034521041c84 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 844555710 1250 844554460 844554463
    0x30c01050a0e011107051012050c03010302101d0904030507030f0f0c02040209040e010603140c01020118030507050f120d111303030503041506140108071d1207260609 73
    0x7240368a4980c1d50351180c000000044a0030181401c4402141c4601d001c0400c546d540e0000424030281581c40d24140a00c0c2880c6000582e08000c00f0111407a906000400250700c491003190036084031841d1404510a1025032843c4080340b04450f40d4004031043c082204150700240240000b034000e031160000c01d244d001003189c0c00e00298800c1800696021000c030f0060800390082c201402005101052100c8102c00c202d00b103940c140d006a40d08180203294411580040c00840300705802031000b4040040c080e00106010300d440301c4000c042003400141d9800340b00c0700717000900390440e5007001d882c03480400d01d8104410383c010180e907008280c948282d40c01c4450301d01d412074840e2810030481d52045845c5031000d0310241c05c010415074000c5032140303201c02c8003801449901c011303105000301c92a10502c0c0000041003c18010210402d024a000040c01160000b68414030148030403030b010621028603820880c20700100c0d50102c000c07210310303102c064210746c000700c40c4841c00000001240c525945200009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 844556960 1250 844555710 844555717
    0x917041403070f0b091f020d140f12090c18060a08060f0a0914071e0b091e12010509010b030609060426310504021806070f080a0e030c0105 61
    0x100b5824030f441e0010042480000e000d0219a600140548500e11114082400520042003606c00580241c01e0108525070080c444900c2101008042401c2c540c034140c0e001f560f44101e0f00b068607016102d500060038032008016000003010040c00f03002c6c88100303070b04543c2943c0341c007034503001d129015200d0003242101000071024816840d00300ea10001d510741c5030b103020081901c546c05640803804035010850030541005407000410a040001c262501e030000e030f000703d442c80e0760009040c00d0001c00c00410590b80b00c0121000383c2d03840310744c0040e1446c41039001401002850603034070f025508000800100e4281035100d442044000c0d41035a02d40c0d510000700350303242c140071100140072000d0a240c00119150011100f0550400701c0034075858541c4c2e1449610705000e0a0f007640b04008009440006108904402c80c0c00400042d82d056007000c40c481c141400d01c01f05c5055040c000c42d00801d0340701c01e00c4201c1c8545481550030104487c0e80d10011751009080503900c4010b14000d1080091640c825403040c0101e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 844558210 1250 844556960 844556969
    0xc0c2e0b06030f061c0f0312060806041203060812071106090907030903090b120907080705010e0402031b030405030703081509060d0309030c1e05040c0c0f06091704140307 75
    0x291655890f58810b00c5104000b07405107800005503441e00301c4d152144200e02035498010aa48220303c411840c00610110000d0b0844a4031820007004110481c80010389581080c0d211031081190000d008049008082c154802c003503038490418490303905c244860050004901a004204605070f01c2c0d001d01540b403250260240c2c203d980c030800511041c3c03095021011051203890716003000c0741d031603c0d1070203560464428141140c9180e000e0001d080d40c2040300000420340800500981403502c00040c220340b00e242c440500680d000800648640165005082600c19840501ea01c81c281741c1809503584c0c1100310b08071302042c45030010030310003070150900c0391038104001c110b10441d6a40380203000c4650b050440c11000d000c601100070000a15840254010300241b000c02c010014141041440c44400c6900603070180b8508040545d103140c0c0301c904c80080940241389401c3c82080d51030180c00070b1081500160000300300004200d1a500c9010040007150380703120103240c154005d0401c064852029200e03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 844559460 1250 844558210 844558219
    0x1113031a060913110619021e060106031505090c2d09040e010f09080a0e0a0302060a05030709092d0b0d020919020d0e061312080c0c2e0b 60
    0x243e166110103144452032440703501c020b01d140c0b0210001c00e0060f0450198010f1440d5000e400c03007001c55040120a00307061440d074040c0302054200c80041d4603a00e042c00348500305a121042e16010070b14480c65080100000740140d01e81d80b600d003600015a8010b82c0340740011024004003030751001291035502c220b4843c00c003070540c905440303d000c10008005426140e00d036035484061003280e40c0500d20400e01c2d5903009010107079903500c1c107032001002c0c5420051641d100c2c01303034101c0a00c00f42e11078030143c48041e815410102e03a20f07122084140c034403400c03562202202e1401c10424403445460307003403400f406910961180401e00e10b4802c1840c1078039070041259400c89926a5600c01524000d600d282d04141c900d120b02030100c403500d551106030b0307102a124403242921007200c12005641044034a0b80702c841c1c0303000b031800ca6540d41d441c068007016003904001044084004030350024074180c2241c4040c805902154025003811560302d1980e024800c40d0004c0c003101c0d80291000701c9641c0140100d031a070092 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 844560710 1250 844559460 844559479
    0x1704080d14091c080a080f0c1206040c0e090103150c030b0607062d090c240f090f0e0703050907060e0d081209150603071a0309011113031a06 62
    0x303000900c120400f80c000d2010303446410b000416800c0c070041ca651a2a90303104645803801132a5880c5200028050440080080111480d08141da40c4850b800a0307040f10301040503e00707031030110b5070300c110b40c0031407540450f03d58000410019884003c02e850030140c0c6051210341f640c100160110382c1e10100d401d80154042082c413000511603403080d400d00c4003000b004841e0b13089a1071507400e00b0402c041c40784000381d40d0394195424024080c0352100102030080d0f0304021091651030b0b44440343c01d858220340610000340c5030f0016160090300c0071805029040135200c41c840c0c1d124030301c00103401c0a50320000032070b152401240302d4100100d94501520026110318044400700001c2c45140c4003035500584010906010000244000709989030141d4801e4000700081e1800752004011990007130083c5200303034002d00d81001440310060800700104002c4050f65105d03512240c40c1c60251690203054000310100148402008e03038480411030907240901422006103031050300c0032a8100094a00552010b40407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 844561960 1250 844560710 844560727
    0x403080a021005070201060504140411100c20182a040305030403050105090d0e0a050d300923090601021e01061703090d0215071704080d14 61
    0x1008105488403481100d946840c1e0020b4403048907070603210381005035126142000903160500031100c10381182c4503851200e0820f50b403246120980700c0501c034062502c0d01206100180501c0e118010540c22048821011804110001c400c1f841c0e400450310651110105800c401011428030b44150f42080f010741800300c000c801c0041e140d24022148a03680340030040800000d4083c00904003c40c4550004245803c041d64224140007546401c48200006030800d01c9440d44d400c1c917030710103d8030107a0b03901800351aa401c0032a100c1c84184030b880342d441610140c42d21501c0c0070340d03000c01d02c24072241d480185135500c8912620b05030005000700e5802c020f17500c03081c0c038051500d0341255420210500485017019441070340e00400384502001502c0a0355608800c01c50140140d01c040040a130b0400614506030b000341c0040d422071346411010303010380340c04210f01c450707081040102c0e11f1042c1c201106e0046040d00300184035060780300340540f100c213015015560300190300940880c801480b15259450405d61030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 844563210 1250 844561960 844561973
    0x1309060e0906040b09010b12070305071a09061c09050f07061d0f03030c15150103020f0d0f06050a0b1e04062102120106051306111504020312121f0303050403 69
    0x5003107502c00b0356980c0713087c00003070740d80a0080c80140310a1015058052031410560700f0841a41d01103004004401d81113005000c008040321302c1c0490440340795031180c4a200e0140c0324070202005007844213240c6044101803120004802194400400c1103480c2151036207001c69074070034541c0300400a81101c1d440010a450304950030300350000060102ca08164800d000306203018880815010300e080044103001145111154000d0941001c0c2815072404c55400c082c05600d20468141b80b004581d2a5152844d0310403e4000d5001010000d103801a411303100c0160341166400a426220441441413001042c42c50010543c0c04545a03600c0e41c500d00011401d5a004c1c4003010440041515402c1200914028680d4104c0d8060130940e61081e8580380c403040c03041313440c10300b40c1c110f1801d01621a0352a14180400102d4030320740c0038840c030038004a0b01d451010902d00300300000c981c42404004907911011080d0184c0080c400c188060b000d841c0e1011190240502401c14040900000d10400041c408a481c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 844564460 1250 844563210 844563233
    0xa0507021c0b1f14100305060d05011d240705251a0f1006110a0507030b1b0f070212160312020f0601081009080c01021309060e090604 59
    0x5840c0114014400903941c03540106800c43e40420039100700c184000002d140902c410003e04000a042c100800c80600000c16100c80400c1d41001c05480e18002441a11010704642c1803960182c024042c01c0d01103901e01481d00c51411401525104044058081c1b1410070b05141d99240d01d003800c0c10b0a0b89900d0011a03403a0b00030140b851046101c03403040c1d140c540050552110322070080745802110b080075048002d44039006412541c0e0350b00418144031178021850100070854101e420052107403126000950b00309200000003402c00d000c1c407800042070101281c040d5200d5031180f8025a040d50303259801c900c250007225440c07004104280903550040c2002c8540d61048114007003150300748240007040f00c000c4c2540384c0045540c0b01c0508084190300b0b80400104400d0a100d4010f06038940c1002400d60313840e030782c40180c02d6906440782d100005102155007214400c01200c8020b55a40c00040007889190361588038401510b49041400107880844036516800f41640c5006403045441d075444881081c1c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 844565710 1250 844564460 844564489
    0x100806010c080d020301050a090903020c0f0109030c080607080106020a0309141c0f03020c0103061d1b1201031e0218090115030f050705030114070c050115030602070204060b0a050702 80
    0x75420003403001c10241000341010300a00c041c0035035a5070604041c007440202c107134406002c450170981442e0001c0d4021850f008540b00c20b4641000741401c1d480102c41d0041c01b0382c070140c10b40400e040e010640c0580841d04511904c4140c50348000303a40d9034042243d848103c124080c0011342c00050034022030b0400807882c0c0e42d00d0390040408000201301e98601014142c03c010480d5040034500450040540612103821075100c2401c007085011b20f0405d2001201118002c80c5200c401c0c084006160644030b00300c10700e1a241d0b440c1c941c68581803014078600306940c080c00155175003020041446030a9005840507200c0640c060202000f20b00c281e01e00014822024040c0a41552102c040d44400c0b02ca6603100c00003540140c50124014506050003030070301001e0b802850080e41050b0a05214580004000b0b4011826280c402a5510309003411030040143c1c06145409a807000b5001007408480d80146ca0704c14000c440403c8403c2e5a801c8140d128407031000312101040041c4411030151030f0609985804e82c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 844566960 1250 844565710 844565717
    0x406021005190c080a0501170703020402030903070c080a210e040209130f1d010911153708071b11060409140c0a3f230610080601 57
    0x2d614804049090750100961440080c00f0f0104001e80303041c041c05040d0040900c02c01e2141456012901c2030f403190501d0001030301964001010400051003001290205904000c103004099203400b1455181c80700380805032000000350584034180f41c00c000d0001c03c1030300341c1c0d102c1701c4042d00340e4828040650800118582d1007094038074558124038940c080c0c00f0198085000005500d0416854103801e000111090b0f82c590307141c56440340004422451000070144126440210898014901c151034426401c200d054a10381c045030203203450101c00a1450031020b00864400d41c1c80410303003218a490101d40d000300041c8e010a40e5413800a01112810015028509600c1556100c002240040e4401d92007903083d0366484221113410748100c2403003500013030301010103441d100c04503800902014502c1d0640d884020070b0343c503d00100c01c140415280640c840940a0004400000c040c070040c072080c22036005c4205500100749041c110b0708002c500c20031b1b0003080c81c034a03c03440507411281c29100400700c5040c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 844568210 1250 844566960 844566991
    0x1050f040b15150417010b090c07080d181a070c0323031005040606080c09010810031e060e010b060f0a031e0c02010b010507021305070912030306030204060602030406021005 76
    0x2030f218200081650010002d07215611490621110150207400c03441e0341d4681d15141c1c01c20460765030452010780042500404540701c2d9940d0410502e180701c0c3d665001d4005250051004003081400d1460180034000e2101e11040c0b0380780c00201507201004c0714204001002c8400441c0040d02036280385045042200e504003400c8401d496860080d8820350703880d611900d20b458204014906401508080d0401e4a4030341102d00b4000c428031031500074442101e044c000b0000009060804a11001c0c00440e00100c1c1c00400411a15901e074903116084410380f545403d180314011418014000c00e0300940d006040f00345009040784000e00260846041e0104042d1141614402d56405e8420010280030300c0d000026000d40400e00a800c40d4403c5064905210050000001595602c0e200c070034607100031600429642d40302e81088908003080d070401d175080500501d4680516034540d00c004145c910070f90303041266644031001642d8901481c800c810041c6c1c03001460300345480e0783c2d800c0b841d0024180442090b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 844569460 1250 844568210 844568251
    0x1030c03111b161a0703020109020405072c010c020112150620060f0622060902090306010509132006030406092001050f160212030a090801050f040b 65
    0x1001d502c0000008520b40d900b00c4001202c010500c9030700c2940010740401920286050300500342000c08410082040380c01041180a06000b904001609a4020701c10031a03407400402c090302000e041c181512107460f81040801c4c0103034130000600400c1d14161552041e500646d030044030101208030b061900c40344c84881e4500d003d8008000c3c032000c0c1070642c4030341046103001d41c415000581c1c5180b1074505030344080148107140c1c0c00281010781100c0c00755082c4205416403500c0051a00c02c100c4940e1010349001c6d00064000c6055024104161049007a9601a603039402080082c0e80305649a030501d03040d04040c03500180e44091414035051404c00143c804440140c0041d00c140c0007104c01361103239900c0701d0356501006000c40c5035a4400c00b0103403842e1614081c0c000020414001c07844040100b100001e64034090004c3c600b4a000740c694028820801c643c007241c045512a00955400b00204404030f07404505180c040c0a46e6229006081203c0030b42d0b9183d8031003040c110005009203000141e036144961 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 844570710 1250 844569460 844569491
    0x40807120b0c0a0c0f05030c07060201050105010e09040b010e041b09050726040305031f0b0a02010e0303012301090512010501050916020304140a050d03020a05070b09090601030c03 79
    0x2002503448244500d4214240190500310041a01c080c0720700402030505084c2d0004401c1c202240c000c850b0003000074807840e0041c5180b00340207050002d40f0030b0b00000101d1507415044181030318002c0e0784902c0314a066030300b4040131400070364005008042100050240ea51242d821550141c09a04032407500601201034140004607074002ca1401c540f0b810822841d9600000c2c0041015090310103062411402040e01c500000301400080030891b0010209900d80e9a2889203005c02901c61600c424407035881e4520a1142d01225880c0f01650074071402c5140c182011058904942032172929100c2c2d03948058155208400305031085041c01035040c0003040a84403000304650040400000049550401003040002c1600810740100801c0c407806090030250f002c03098404480c4810822404441ca500000e480b10071030fa042990003800b80103c841c11f041e400203c141c403850184054809241d15812906454411030b050b19030440d10b84804146694482c2d0700441200700b030b9240004400c40c15450f0320 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 844571960 1250 844570710 844570723
    0x111e060f12180c010e0111070b07060e010209100f0c06062309010501020d08060a05030d050301031a100b07020310061203031b0807110c1f1e021b060408 67
    0x40d8000080441c0800e00e030840c0303040301500b12084850031109124407102c50781c2d40700c2001c4491810842c588a220420740d0042e194600703600210420344807441c0e11024180f42642001505072001c50419850740c19000042c0f00722014244094010705025029070007e5543c03102c0100307008104100b000c0010085052072003500041c019460200e0302c090354505a032048964640d5a5511a00c203500042201d42e03000541c43e403100340300c1d040407160303030381e0b080000391940d81c1c1d540c015074060040c200b0320b04801c0d90005c0218141c0c0d01c281142068854001c200b0701d96008102c84001e182c540046c428004410004041c10248d4070060850b0114500c004c10041600d240da03004030800702e00c1500000416802d402000e82c1c1d80b5060300e00c2451070500180003007640f40058406c00920a0511000700441c0303041c4032404041d48050890344541c66000001c51031400250344080c001424034640c658628540050a80e40040c640d00070059180c1c040076600c103060140003070b0750703112408200c0003507400000d1024 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 844573210 1250 844571960 844571977
    0x1008041a0708090d0215060f150f070201110606030a06091401060303030e070506160b0c46020a08030a09020d06020c25030803060607020915100903111e06 68
    0xb1444641041c2c1d0720107103000314000e078000554000311080381c0030b00d20f4000341550005007201e0b001c00003e020303004100c50041899602122020000316501e0051028004142c041d00c02e0b691907440034000f4042c6610340c9400d4a40e1a8140c02c01396070b69021807003030341200711828059041e0004050003100300700c0c2103c0c2c80340c0c0201c010a40310302c07000b0030000e41405040014030301501c4071860f203103451003040301c0a464440c0007803103000d80c50080350322404100241c44000701642113072a045030141001c001c2e09140c1902a0140710410011a001d5040442d005109114140c008005543c01340e51480242c0c0c00c000d1070b503170b0315666803541080542d0b1854130226480740201001a030b601d164140035400c01d4034502c003110203804070200d42025200300644507000c403904414803944070744450001404a04c01c840019500c0740716074081c01510404e01d00c3d0b8411004040702c007103403540001c40d070907904104da52202802880308040c0c0ca03146c0d0305001000c50394008143c4401c24032a5400c00000343c2c02d4014060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 844574460 1250 844573210 844573217
    0x61f080d081801020a02120703141b0d0e0d1101020f031209010e0705030714130e03090a0806060a0324090c0603060b04180b0a0302030105010b09090a09021008041a07 73
    0xe00c40011103140032442e0b0b4070036042c000e6180c100c20344006580c8101c0040ca81c0a00c12000a01e0801d151048190400c07039824040000ea4540b8a5000c6e0700c0d9901005a100c80240950f00c1c8100c451801030389004911103000d4600400c4a0040d21500c50b480144510181540650300b25044144401c0c401005400009240000c05041056049084825054242802e580509c40c14400c541e0000341d01800c442407041c117114000c0c10f000104160684644500001c542080702442c0c02010100280c580048155820700301c242c0d5a0044c00e6950400f90350f61a0842c0038490300780046085546e0250190304075903984184501c0151101003152030301f040c280d0302c04140101c24458903501d401041d0003064019a00fa0505080046820a0b15040d00d41d14180f66540e90740c000340340d210442d000e0021074009008100e03540c1e61314a0304615a00c0403c1c3d603403082c140030303001032070040051060228051300905840d07032250720482c00f640d0441001e80180d031041c810100794843d4148010059208444c070f5034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 844575710 1250 844574460 844574477
    0xb190f05180c0907051e040e041a06010314061c08030901050714030103020102120a03150807060323040f0201020a140a02091e0c0a05220f080708061f080d 68
    0x80703200e400d100360801442c2c0b180111a00340100c290b844020344103990700d4440e80001e0b604440c140240c03180304a601c0b600030001824100414054481e410482c0850400100c038016516180110100d40c03041c100c8110f40700942c1c0100d40c00e4201240c101e041262040011165032440e5110310405800484a1050326910b400401404039403105c82c4e2038400a41c140458110f504603030020b526a41000300008540001085032026148130303801c16210302c182c55071410722003902c410030315031561003500034036000c2403c0010b00404141081001c10913024411591002a00c039030350761802c0c600511600340e04521400198401060091581c0c4114104d0b00c80100301004140c4144640007400030010600015500346002d150394101506503800890342d00c09035a11000304206a07118010042c03040300d20030f241e40c84e4144030848002854150354406100800507680c4d505510380d5184280600e0119401c10404a8550001404074101d90b980340c0c2d0800380142d448a40c0549412200b0f0100c0d0009203220 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 844576960 1250 844575710 844575751
    0x5060a02070212150a020d060509161b03020c100c1703040c0e060907111617060a09020604060f0e060a080708180a0308060a031e03030b04020301030b190f05 69
    0x54001d0f00440f00c020160160508a400c0c200003c10001e2140c50141c0d00010548400030496000401800b4000e100c04030504100e251450300c80c01d0500c2c403402007a10f41038500004a0b00c4400921919030680c000e2003800940002c0c131802c00311149000c0140030000c0f98079000600b0b030900003c00f0a034060034660322032070030303050505200c00c40343d000c8022541c04400b402100c2d00d03804913440e401100380c10310b89010503400320414070700f940e40c600c500700c040010300303003c600c41e5455802507190b12500001c03201c080e121000d08004580005100941c403001c10001088070070f024040305c5c01e004683d81400c804070f000580100303100f90300c50f4049034001208142044001d541041c1c00b9900010701810400701008080322555480200382d002401344022200050810b5460741c440001540c0e006c3d640c0701209003403d805482540d80104224046414600384c0945410710b8030a0300d040f41d4000300f40039140d40342d807481121280e400f007001d4820b064a0350f4841a2184880c01020700595088210700c1717090310300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 844578210 1250 844576960 844576969
    0xa09020c213001090513051c0e06030708010611030c070e0f0703090c05010e060910080601170f0a02090102010f050c03011e0506190504030c0305030706050a020a0c0311030705060a020702 82
    0x2c040795905015140800e40c0c5401020030300c51419107810680014094070b61500620406035145002081c0340702c0c110100c21000c1e1840246440240c1c140c40c0e41c040303008540104085404215900340c00150202c004100242c4039090a07102c1810701c905a9142031300c007100c00d90415010341c110b40b000d400840c050006e0b80480e1111560b00c01c1841c038080103040240c0d90b581010b5178462141780e0400c01c402504181d11359802e0f00311010404004e000c0401d132000d0754406001107900700c07802c6020070030541d1035540d0110071441161184542c8051b940303403a40d403c200e5800035044854154110340d0307228648070010029219040c020390342425074644a40c501b00844641c00200040042c149112000070400743e10707054182c640c0410300075019040280c0e0b882040320700740240d50015000183d082d00c00014442c0200080901500541050180c0c1e9513914200b010ba104903500d4100184443e50500c02091060707200f0741da515517207801e4134505071054603054a404802d42e14016036541c00502d2a045150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 844579460 1250 844578210 844578247
    0x1b1b0f21020f0705100314041b080604080306010f050702090f01150f0518040e06040b0601030f0b0f0f01030e120408011802010507060504020409170c06010501020106050a09020c21 79
    0x3041d100408406094440301a203540481c81014050585a039803241c100b40250031400c11079400d801600c425181a00b011081100700c0441412540b0348240040b136a0080420714512071508a0a11841d50300c403040111040c021080344ca204214085c410000165900c12905005845880c0d01d1000d1354104071186880324401c0b071401c001d2000740f035000ea04032500b00041d0317002c0048104441030018609000318019010302c0d94000514040d8104201c20481d5016540d17000381e10a0381d0401140703540030914000c03159210b01c801d0340902605000081441c16503a1490605410301d00420078154030308039685448108844504418000b0400380700d440c1d0248100303007101c0000c0200c0752460b02540c0001e0007912800703102a2000762264002000d54490340c0000e050a40d20403407041c881300300c403035a204050700500051005030044a000040562050140b281550001031800003c0b41c68070f060540250700101c00103007980502c111030409035811781d120407040041c840703403555517100c40c2e2600805204d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 844580710 1250 844579460 844579523
    0x703090b0408070603050c0706110d0c0926121b2a060d14070305010302090a0c0815040603020a060e0a0f0b090616150b040f1b1b0f 58
    0x540c180700410110600045407000c4441d18200010141c4941464020754403801e10058501d5003407100110a04166500130b200054414200708200400400c0403981803000344541d04c0f441c00b1000030980d034011034410040c0908001c104441000107802103c0c61560400e6550816080c040c0c0300d0350160035800d0005014217001e4841505e084117100043e0204045001c414900070200407590032140e01b41680689080521036400000514107214020302600c000d0004a00424620b03022510340e06440c061a04036a00a403181c80803561803000c0c2c0d13150f0a000490721513103d500e9641c00070240c0c94a1040c900941510303070310720619810300b50a000c1c207561107a000000b034001c002c4c41081501204401d8071fa0742c0714200d0f03100ea03031440a1140c80c003c8030f6004034050220b070100d54452080c42100d90100c203c05a0540c0c062040407a01e80c1d00e4001c89148811040b40b100340c801003549481d1060f1a00301140044084c5c1f456822415200e80d00d00680c480000c0b2040401034145081d0318144280301010720 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 844581960 1250 844580710 844580729
    0x151209110a05031609090516080102040f14011d061c0501090507051e03040303061e03110111150a0213140a0f03030e04050a0e012d050420040f020a05070309 69
    0x410007a19044144d0788980b080f020038503600c851400c1000024480c09a40b8180c1680c001c0c01144c0303c5110700d000703500900c20300e213441607031200000b000c84031403c248100d898141c56481d5062609070281c20b0000d0b9200c0015400f92040140300e00c3e06000d41c0180c140040000340000d41e540c1400e880200301c4001800c66018000240b1401c090282416802840c03d000400280d88035151450164060140c9400045500001c2c104000c41c003610307004e40d281180d0151040c2005020030000640b68200315103285060350f00140c2503041f240849406403a00000e07140b500600e009003000d039901100300c00390003040c0c03250241d111048207450070001281c007601110350b403c000d00f0316580d0058070f94407000a02c14080d40d110320020300701281e05d502c800c5140018600902c60f650050114041000e02c90400d0b01d8030045402c860041c244240c400c0c90322485d8481010203007078103101400315800c1c1e2a2088a603200c0d850785543c110040b50b90014000100003503d45c45c0d2030700000c0c540609400427607040500322 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 844583210 1250 844581960 844581973
    0x8100e010b0307062633121b041109060913090f0c05150d0c031b020a0c1a07140f03040906150c051b1212031b070507151209110a0503 59
    0x3441121280602c030750601e99041c08203284000d100405946c0701e100040c0d400072541441285c04800411741106681700400d00e081c40344407600812049035014200b10761401010322151500341000c100030001803100800c030825064601c8000b500b5200021030460300005400c200340100440c1c246880c01400c021148010400b03400341c41c0084034000c0020102c191901c540108900b01e0180d44421203640c0d00554a03003541d0350f182c038080d65030700442c2c104444100c2c0b80c400c000340c00b60115003180c0c1000d84440083d403400318692603040c0496a090803d4255005210010b0502c480400003000203145404000c12601e14049050f070503002e4000080040c841d03440b2250002481c041811007840700d00424503994901c000001c80c207500b10311503184400340309240c0200441140f01d40a10320606c5802154114520240034425040c061311000070300c954002c01d41444180613055415120310b2091500402c90425446000706a645c0c40300148e03106007214840e081c40f418862550344c007408094000740701 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 844584460 1250 844583210 844583221
    0x516111c030207080712020601050111070f06050c030d0606030b10030507140d0b180a0b12030a050d0e010203150a0503010c0c0b06030f0f0705040c0908100e010b03070626 75
    0x102012180346203010158001000f2041000b2841641e580356048815894081141e0b01c010350f94400070300a01e800f042800a83c1c01500c03400161382c1d410f450f140041004041d103000c1e01a1910b41207695200000d00040c445140340007035502c540e01c000d1699036004034080301460b090180c0d54500c01850010503090004000344280c204c0c0a03e0346618101070041d40c7c88005108110082c0200c110080d4001144280509401010300d0803a014241601c8108107108e070401c00c218207030110018100140e0400c3c411030081c140540054442802d004002240c1420010710540c00c80e0300403107044442e14001d0482c103589040c503000c0d542c050f05054000304401001040c01506001c08881c009044400c0d0100091a80d2000c1c4640c45c1c400070310b401100c14800000c1403a0783ca5805500030280118030b42410090094403508400c8200e500d034001034140300e51250710400c00f4080b5400c101c007040d0b407545078540541d10100407043c003c240382c2c0c1d10704c1064160721209400c684e1040c0701540c4400e00345002d028 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 844585710 1250 844584460 844584493
    0xa1406040c0e09190f020717070b040b07090e09031207020d09140621090105070f05030c0901231b03090312130513020a0813050705100c06051611 64
    0x680b20801110030203496981d009074164442c43d0705250100103420001c0450a01506401401100d40314030801414114503560f003241502031140040c140044240208000c96a14900307540c01001d54075040c803c03642c8030244092180c1080c0e8143c013199100040b80c0d48011014400030317030415a580b01500110100150081c504011400341075615802000c0a0215035111b034100e03400040360a0088025040c1c1d00d400c802c12400445010000e9420b02000450b01e034403841001c42e00e00b5080d00c03440d0460f10b8040585000b074004450300703070501000e4101d034030751b21040c100a11300e50107518400340d9070760340101194201c15011104800356940103010180b80d0341d40c04500181d01c0790012071240e44074100300a40c65440c003c1e5034003494001202c40140390038150903400804400840381c54440c2c0700d480e041074000c1e00342c19071b8602501581114100b4031039482e01e840010a0750041d4901682580754907141d0f00b00b11603080e641140b8444501210034011908004114401c941c0c0001a1241906a80441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 844586960 1250 844585710 844585727
    0xb0f160e011d0d051606021903050301380901020d03051506070c1701020d0c05090a0b0d0603021801050108130506072a060c030506151b010209090a1406040c 69
    0x1003500d14000c1c11000700b192910105043c000750004119034a90100191280e00075407180159401030007040700c0a030016003408529814543e00d942c7d01407440c0c0c64810b280341860b180c00624088000c034425001054201002c5410404060818030340d5200c103003400191038680319075035004c00c0c10700b41703c00c200d000012616402819034007651019900c000600d884591340301140c0080c00d4110090101e00d0f80d56078158050151168290f40401c104545560b0944050107a00341080d4410f4044900b803115010310f101030140c12282000204c1c800da00d82d40040c180200803500150741d0302e4844010011517034402c041d10f80100441400051440320340c0c4800b0707101d10001f048907051142203499060b04400070721031001d0041110210b020664050b2511201a003018408000060b0420004c01c0c99890641441c1e0b004081c40ca01241ca0b0200180c00141701085000702200b10395400c1c4807246e55500ca04e200503116000d20b02c0000340b203504400d042001e104025114600a500d0303c00301040c150f070000b940c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 844588210 1250 844586960 844586987
    0x51305070308030601020120030105030106090612062f070b0708160807020705092502070609030b0a02121305060702031c0519020a0207080705030a0804031203090b0f160e01 76
    0x1580e29a1444c0c0142c1c0075007842800340c804400c2000c0007440310440c4801540c182c0d48224001d0010640ea4255807081e9080b500403280c0c1c402520041c000011450380c000c40011a000d10107041001e404441c07102404c8403400b510121200002c4c8c80810042000300460303111146040c0380d261070030700a01c00030030040912400c00c184100b0f040816599402000503000401000704001c4441c509005c4110958000e0003400c2c980c044100c644006490020905501b0341e6420b5945007803161841d29007500044020b000074851070760800000f0004140d14075254070451904503644114003407440e0152504600a0110046400a02c60154010702c1d00d110350404900c50400800ca035181c9517052a400d501d0807404140d81d82c130000c3c401103980d801080840c01c840c8140151500c00340e5407018151251344406000748000820041400001c11800301c4500301c03181071400068104c1c1569802c0d601030015100e4003c84c5215500700711010074429244105401d48e481c2980c8030011000000e0003041c0407504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 844589460 1250 844588210 844588223
    0x2116090b1e130506040b07050c0a03030f180e0702010207020306010602010902180402040b211e061807210c05040213420f0f020d0c170c100513050703 66
    0x21150214000b9151410103410700134100d40d52655078502c05030f440d42c001c200c02c035514015008480b00c540381040603001125055123584001a149003400c0301e0880c0c21743e8803201d00716000c610115648082d120301c0c0c1e01c034080540005035110100c0c01007500e0581d0507800032045a04014102006841c0c0c0b45240192800080007004135803601e20001c0e0181010b216001c1c1c115500992030a1341025550400700001104015104529078100c10700b00a20014400b0390000c0c4d1085001c52004c10200c2ea42e860500b0a41068500481d110400039051040490449100450155404062196400c80c290050000700c4045241a412180b4000c00300828807071403010105400c61889180c1c0308c00c40000e020701458801031804004924450700c07041c944406d038000a02251150404a030049181c20711021082d0020070011750050022540070610b00f82c125030395504280c8110400c0c0612000d00b0b581540000544019500b40410748202c50004152003592040030443d500494000300b03a407400d03660000e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 844590710 1250 844589460 844589467
    0x40518130206161208041b0b03150102070510021c09031a041b0e04050c150d0c090e0f070e0415050411090303040303110c03010902010f052116090b1e 66
    0xc3e19880c003002540d00a0407022031140700d6401c05a0107004280f081d8420540480301c40229840d242100300c00e0300900c0310341041000825601c100d2102050400441403046032003080d11000401c0c61410041c24447c0980e00a4050000880c0c40c190019643c0c1e8051400800c103910b15140d0041801800c6031074213039111a00041001c0c066070801e0085101307840c140c0c51102a90b90f2039403101d0024100c0f03040c0c409010b0b2016041641c070305421100114201c13941141d043c0b00c071500c280c030000d00c0c8209808084c45038250b0009050b200511540348240c2e4000600380e034514090002a21036200416424030407840c11503009011046022118140c804c2902c00050314081340700c1a000f50b100d5a90103651503c80400d0000400d640917085900c80382e080c0083e01c5216009070140350907500c01c1c4c0c0000b800708034088000c85000d40f01300060b0101d07011443c1070740300c43e42d101710404404010589004420411102642c5e03051500006202d00800d1405a1145000070654126075000c2440c0b208041080000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 844591960 1250 844590710 844590727
    0x409030201060e01060504050405090312010b030702030c0a0f020306060a03170d0f0218100507050c01030218040c030c0212031b1c020a0302040603110903060a0b01090812040518130206 81
    0xd500407005803c002d10712401e296103400d0b0113091500301d4807d00740b0170b600f024002100030102105451480e90400d403425080d9083c01c2c1c0b02206900001c1c04002144000d1107110301e03091040000080d0039010b21001c0c6883d0103203006050501e0001000300740038004022080000480542d43c1d9036100035242c03119920341c004228442c019003034510200301514004a905a6070034610a081d90748460224cc01d0007144060703401c161940d000d0588058210b0b003042103060682d501a80003080322131607510802c045600390740001001c4400e001703040c10000c0c2d07594819210f290740400c007110f0384c0090800101c0c110718282c0412804018400c0d45903203034110114140c010f404e0422070a016441412901303645460118200600070340040c032601d40064140f282005204103000102c42036414090003400c850382c1c400215201400d00c14144604010030480700091440013442100408071068280c40c0c1e40e5807914040021004001000b4602018840305100c40703029072407003000113150b050750050b480c1c0304032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 844593210 1250 844591960 844591963
    0x90b0c1803060a02030a0e0619020d0915140a020f0304141207060b0f040629090301020a050712020d0c0f06090c06030b0a0812070b0c0d02041205060702190204090302 73
    0x8000c258162244409118102680d500550b00c82d01080000300f026085188980d40e807104255400c8644d189103800304c580c11180c0d0b8000b004818840c18010500f030703a040d5600007140e034002c0303081c5e6200b90360794440b109521070080003150003500b4003d055091000a108840780e0b07120152005048c0721080c800290407080030b1104002d503035807244a50ba00d841003030a050b8094040040701610480c4010102142850030b0f05c6002c095608112094000500411030a002c101040b401515103000a1000c40820f42e0b007400180082c81c0296501911036180c1e19040c5200c8203109840406e54222084620080741d1001c44515965044014540068140c0c1424001001d0a000c0074000d103400d00750100341c00340c25401c0740040032820340e1740413909030f0760741c88a075216226003050b0b602d034407030400c801c0300070030400344000b50002c1038130000d42d1800d40040d4106040364010341c004a0501c1c545107000303050100610009600004a00203002c0036403820200d80c10070141d4020007032245548041c29801d0510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 844594460 1250 844593210 844593247
    0x31c050a06080d1e0f0f0e1201230a14070503070c06062d1a1b030c0c12010c05042c0106020609070b0415050c030c0a111201090b0c 58
    0x415080e1a203d881c00440186800c418500400c400302081c40d990b6081d500c0f0b044c0a010f0b80c2c2c01076907021200c0c01140400c0324032446802199a0040b4001b2811031542402e204e084821982460171901c0e0441c0f0405030144179500078440018a4549020303246003266a002d0a54407030f1680c580740d80e60fa034613104242d6807a0f80c0000007038044c40c5009004904804103d000d00a8040d904520b4001c0e401035440000c01d203001c1d4056a51000d5000300668201005940a411113031103030402d03c01285040300001d49190410b414001d0360b6401020448084c1c10400c0040342003240b0840280580845008094a24466481030350840d07807180c3d445850b090250000e100b46081c206420b0f00f11540d403400d000795108820398170200c5501880000248902c00c800c2200c0403a00003010181801b074104000741c40a8105a074260703a1404104030340c40074500f0034840000510300c6444541e803106038120a00c1415125000307048421b132f01d00b09009011a601885142e48038503071000c019239401404080b20445103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 844595710 1250 844594460 844594469
    0x1c0b060604090513110402070c0323030d0f1b090303050f091804110d02011d010203132c01080606120c27070f200313150908031c050a06 60
    0xb45040140306402c1c441303070f484541607400761a0341c280708104142000124428128001c00516000b4000c01c00150f41c008a00c02d40cbc41c0d1801c41f080c5410100c02d04509542c00f11101807207060390b50b080000c0301c14203480b86400704080700400700368082c816080508144001d0002509000011880990486186044400001024201114050392041d514207034070020f807000c50344590307041031910345030a242408001c0700c0e0f0140d40f5107002282e4200b100b81110340501d02c442c110b02007044142034060f40e07121100000c1c0b5506c0e480003081104420100c14140206680100c041c20320f100400810100040498000c4821951403685150001c5014541a1703d9190282c010004810160000c1c1c0914421369407000f6540020509540e43c1c08100d5100020100190103c3c0080700900e404445910fa5003003031100303800450386460008103046400d8041a4401c01d815407420032074070080c41e0b11000c900d0003050311400446c1400c2d5134041e0070390b508c0354603100c11000c95070f15400540c0f0403025411210040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 844596960 1250 844595710 844595729
    0x1a0a2112050c0d0503160813020a081f0501033809070f2c131e02030f06060303190903020603070c200619020115081b1c0b060604 57
    0xd10254050120b4100c000785400c580190111080b110f4090b4007282c1c481ca2500c260100e81e0030280c0c000385c4142c40d010308051807151040c0b100341e0058039010300d0342c0064480d42008100014600079041c034229040c400301030030709050500410004040161145520b1a4030340e82c0001d0300c41d000118500390085c400c0710620060104140f06403400082110340941d0451000c3c00413180d03c41d40d2980e4010422480103c501c88c001c2140c200001d8a0788455805c0713501241c41c482d00041c1a20703505240c01000118058150f64a40705000310b19080140540b0501102c01174003c2e45001c40c0040e44a0051254604410309027402c9508494402c1c0001405154010001600c0c0e00703040c00000d050142e90f030401c90f4030036641c030b0394421010006001d0380054a0024415850401c803420310341c088402d4041040c0943d03403110045600e040d6007003070110181c04504020701e4200c0d50038414030122005480d800c2e00510b840c00c0c2d400700150b030100c810201203410060003c995203402c40810503d104651004800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 844598210 1250 844596960 844596983
    0x3030d050c030a0c030204080a0602031306050f010e0a2a02100509101d0a0201180306021206041a0108040b090f060a0c0f0e061c02040801090b0405011a0a21 69
    0x1d0a40040145003e03030104103040004040c41202030381244680c0c041d40b01d0300e42c080e001d034030000340b04d9030021684400d40150741e440c020032982c3e601e01540c40030340d45030025400440060018081c0e17a182d661303000711845000d011040d0001402e034911100d814059420044412090f002c5034000c0001d9840c51007100700c2000545801e0060b10f0300c60341c507103042071080380c180300344041c1111030106250540309480300035114000c060790065603408200010414039260103a00007011440920242000e07401800d0000b582d072902104102c110f841446079006c0044121072404484c0e60301101882d03116a000504841a1700e88001c03461404079000602076842c450402000b01607100303074020100303100490301c07002109020240c0c19100c8000e4458241c0e0807071814041c9d1034001c8541070946000d5102c1d032100610f80360b224000942503581e1860261140c41c00714040c030080120910801020b02c041007400c12041c1c8a08000078a070505c50320030343c0d0701010608105120410510560708040c1e5128104c0b05d807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 844599460 1250 844598210 844598221
    0xb01110f010902150a09060305070909050406141b1210150c06150608041e080f180a0509040f0507081f0c080403021c021603140d03140f0603030d05 65
    0x1910700c180c8100c1c080c00c0e1429101088100c000141c54446100345c076003490b40d604001f4100d0080c0390003030031107040042d183c0000501808078030030307140201e000c6d080129085003801c1c2d8000200c0400740482402088a181c41070005000909484000c44040c86207441903c4098030526401c00503001518010064050b08800e15000b00690075054400c19090000e421031100983d80c0c1070701c0340719002c0803401c40740008000516195030f00d0b64024550000a180d56400e03103030b051043e00720032282c600c1b1040020300d42c0d10030481c046440c116644100d4910308040d04140c0840ca0300c103406000140302050011000c010410248100e2000c1c0100408603820301003008401040a28131160002015182c040b808000d18440c2500c98420350b0036400030603480c4e0f25407034007180b0708910010031002c5029041c1d18800401da0440003c0080d40600b042081007460b81c5105400d00d40300d10601d20906140210039401e00c5c180e40c13200c5031701481320710100d005940c40d400440d0851041000d082c04603440c001c00c001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 844600710 1250 844599460 844599463
    0x60f020c0705100503010302090105010f11070e10240804080c0a0f0b06040b030a140c21010506010906120c030b100309110105070506040b0703020423041406130b01110f 74
    0x10100c2d0303003c032105a1038624508050300d15120030701004c2d4022480000601195000350f240303101140c041d117041c103e02003040c0740070350a040c0d580c0c2040c114081103e041c4a9148042c10b11800a00101001c40e5511801007400328107103030340701c051355050009400003d818005044183c2d210241c1000c02d03614141124501307804694003000e8105c0302107100c0e0b4042540b9090034403403140c82c0d2078013a000b00000f14040d201c403181180d000d0b4000c007082c412940c0c03d584940f1a07a4054481050b918400704011f28506055404d50308000c00081c100070071000104041584071101441c03284415400007461002c41c8000c0700a0448416182e80007030b0380c0020301400d0340d0315070b0012000c01c1c02005000000b0181000440f514420401d01800701c3e440f140c045401710700512042c0340c000e0360038140185020340d5068511001c0002c41204404480e0500c0c60030840e050500841034a0048082580c80780d00d40400000c1c0c0310402d41c452110407031b50301c1c442e00c156030b4050b400d003440d5003082c10121240305110780801d9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 844601960 1250 844600710 844600723
    0x120b040204151214010f0e030405090703020a05180402251b080d1101090f0803040501050109091a0603012a110102030c4e13030504050d060f020c 64
    0xc9000e146000100c0007a525500180c50550300200400040d610441e102c0c81c44504800c4907420941d582d071849852112400e2081c00b41005a200285840b580703400100191244018501da05040c01004440b2146901c1003c41c0d42640144106480b0070080101042c02401601c81c140740c0300b0342000c111340344500700402c0c9601e41442003004031744034040714010701900c0086115550302c6030300c80342000008178003920404c5002c0c4241c00000410060721388030400803900513007080e20700d15000400e01007031000070300400d0702504084a00b03200c4c0400540d690011a100b150310200902107140101d00d041c2c2c0c003034211042007a110100c207000580520780320701020310410001c00100e03902080902c90200d041c020780388070300780c0400c450b41072039030322072800d0b102c0ba4091201034940c40d220000188290003c00003100c5455803960f4105c01161000141c96401c0d1000c2d24808041c24010910b10000358400c0c00ca5080d00c1d8241c505230100e0450746010009044040c580586050011800d2000c0c00c0000500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 844603210 1250 844601960 844601963
    0x9040807051002030c221a090f10030914010509120c0f0604060605130b06070b09190b15010e3a0b090705091b030408070f1b050102012a09120b04 64
    0x3a6070000746000e41e80550191b441c8200703072003030b003000d01844030819007440a04013941001e001c075200490072500141140c51038003400740c0070903a80c0300f6a8051100310050079203503c08030002080340d4100388e00895510380c0030300c100a2101c0c0f0005161100f0860610414910050341c0044803c1804d040c501000901054001c641c06108000540b8025403240d000d241d076401c401522080c03034603160780c0750741c0801c02c00100313421541d00c644502814002d0400c110020701c42c0c01101049620701b420303080108032152510b4510304012038480c0720003207a03880b441460ba06807290424006114155607800544815030041c40e054006800d480c0030903c82c1d83c0784014800c0d0701500130388000d15100c000f0002d00c3c49095071403401100e81900741c0302caa1700144000715041802107021a041c0f14803a0354010b601d06034aa011610542e8240c03d04081b6a001c07120100071f03040900080c09441c0005074400910720100c034149415081d1900511038183c01886a100501100c080100c01c81d241803e01d43c2151200707840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 844604316 1106 844603210 844603237
    0x6060d02070209040b0a1a030327030322060206090a2409050309040615020c0d0212010204080f0705010509010c0b06121608010509010501030209040807051002030c 72
    0x200e504c034522071070583c14a440e0980403041503c030f01c1c00700102070080650320100c141c1d40100584c1d0100c0c00035502d030036486480180305083c1c219080306541e05800001500301940c003040c0c10038040e5102c2082c004203020f0b41c0300703012607440a00b1034611815801c040341c0c10001509008101d69808901e2001605411103030750400e007128800c0d01e00f201c1039800014691010300301400364030014400c002c03170351844a40c1d81e10082d40715801038038554429065007622100f155981300540c420461810b00840d100da440d02182e654981e445901107841d440340f40c030300140943c89001101c44501069480700d144d2403070350780c40310020500508400e5120750f0424074074150100801003070006003100d000611030145010060760843d0070180c00208035034100401480582c948041c0d0640165106010542e41c5c0c1243c1020390400780c2940172450b0701c1703000009110081c0e0703102d0080d04038540c900c0c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 844424460 844604316 := by
  have h0 := BRFrame.cov_init 844424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 844424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 844424460 ≤ n) (h2 : n < 844604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
