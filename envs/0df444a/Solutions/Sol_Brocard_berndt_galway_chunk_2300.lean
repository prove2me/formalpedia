-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2300
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:17:46.036028+00:00
-- url     : https://prove2.me/submissions/ef4b08a3-f68b-426a-8bef-ed51240e2795

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 413489208 ≤ n < 413669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 413490458 1250 413489208 413489213
    0x1603021e0c01020a09080d05073e010e01030b0f041d100207030807050301080d0e0402120a06050f030a11010c0f06110306091f031203060e1008060705030106090504050402120109 78
    0x40e40113001600c01041243c00000745804000c11410442520f41c2d41c1d1500d080e2035540c0720145080b62172154540074500c0c10401d401c50004240244180c001c840050240201d031038001403250000c0d210407070415040150381d5078640c0310000c01c01c02d0031404680120301c42d8130b8090b115248541c07004401d16103105200807042100983d50060580500a40c0d07036296035130310340c0c02c15501d0b0b203c00c0c4550510f60380007040f1000110301c504417003070f031400d0000c0025141c207105a441c0100e45d002961030b08000d036900e220030070580c0b8044614900d6030400740d01410703404003d03459a54007802140407080c1402080c1382d2400c10044010a00c408a56110004109503000749074481070399041110014007812003c0040340368604001d43d04004540a0401d07109624190b45e00c103800780303620b180c1081c103064807088042070200141403d40d1103519003d88444000d407900da030142c903000000e8065001d00508000600002e45d221061500ba01c0040e6004200c1e5160f44c0302041000b9018007040f00103518101c1441c08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 413491708 1250 413490458 413490461
    0x1060e040501060f030b0f0606160302011b020d1407020a08100c08011d060d031e020303190b090a1806060b030901151409090a0b10031502031603021e0c01 68
    0x50380c041c1c8020043c142e115000418401000d01001c0c0282c100c030400a0b0380d481500d001c01e03030b0141000d4981800c1818808103007452180c20b203000c07800360f51295056400e500300b4032469120030350148003c20305071031101000350009000000c000e03c01c8000042407000d541f04e00403800d000f0074070f54080b1565500403094442c01094065003550010320600000201c44010440308680c203420340910842d680c4030402004030003600d0b480101d09005c0c1d003440c034801c5051800010302d21110560091541c920707110b00024a94907d003c0001405407034181c1e04421a164455059408440d079400090340024106800b50403600440d0300412680c102400841c0350840311002d1406840228020701030031190380384d0502c01c0740f01d82c01000c1050421001e0b0502901e000102241c1003100030050340c0d5074102946813a1107003181151103c0f241c035942a030410400030001000b650b00074280300d0031411030414840c120310b20008034000000301500852800c040c20702e0010000d101e068050621503680740c20403d000d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 413492958 1250 413491708 413491711
    0x40213121407150e10080f1e070c06180b1f08070f060215011406090d0f030509100206070903021201021303061a011803080a02030c010207052d0d030c1101060e 70
    0x1c0026104c181c410320036081c5955462181c00c07090321101603a07503803400d410064800051081c0092010018020340c520540042503010314103c0d52010a56542410071105981c2c03809000c5040400712039100d00820340400c04940c01c17481c0034298182c505241d1982075603240440e0000200d034000c205002404449190f2842f048800d01d40989049100282004104240911800b8000c8101d40c11880241c50007800038019007100038203603d040489a202e00e046090f009004502003000043c1c404054a00700000c681c100509100600c13103860141e000500e00303209848000d0058296228500c0c41000a4040e901d1005111842c0ca034015541d060242c0a8040c8110144a51841c01c2d801b1040e5407041d40701c440e1001e003060700c12468510f035641300886030340001d041900314002403061100001081c0020407402c0d00400090100c8031400c1304515401078500c80c2c21040f982c4050b8240d440e603402080c10200c6050505001518400604040d107064607054200c0c0031035441e041012035120491140345 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 413494208 1250 413492958 413492999
    0x150f050103030e1f030c03021c0609112107030605030f0d0f090b031504060e04110f010305010e0f0414030403051e01021e0d150b07060b040213121407 66
    0x91210344041e00138003040e034030000d079032002480d115140c406106002c5c1c1c01440820103030340750040c82d00e0b9601101c941800082d805180541c0e07201c413020072103620180914030079003035200d942030715011310940c0300410006c00480d840e8003442c002c00007504c610b00a6100000030a80602900c070585654220030ba2a144002c0c020760100d58001242001d051003002030350281d03000d943e4098a075071918002e009610305441000b65001b0380300c00c03010500204072001c0c5801544102c07013245200551004001078002e64400d03080c101454040100482110a40103a4006181407100c054644131400c00031101085d142981d402440005000070070003800241000f00150591158150788100c40d121500742c0c03003502e008000d0b00718007011804241c140c0c40c0050101d260103075070015408552a1020406040360342c022200080081100e00601075036000703001c1101000c0340c04610b45041d41100d600e40c0003044c0102262600403d80344400c00c446c0c04000f040da0814030303040f00d0420340d85680b0380c194a0042c4089 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 413495458 1250 413494208 413494217
    0x60f03090a030f0306050a0506131d0a060e0403050702040221150102060114060306210106031a090a1709011101021911070303050307080702030d0606050405041103041707150f05010303 81
    0x3e1100041c400d10902e02a0f6100410300710720310703240c0420407030550000c030b212404113000c40c0030004a035650480d181e2003100365400c1d0744c0442d02e01240ca04049402d00c0d03114031038650342039003000006503116041f2148282e0494005031210101c1011003050401c905500c40d0380c04040c82400783c1010410705944e282e040981c02c4a007160b884088040794100301103411500414284041221403604883e0214414480c0001e03248501e0325070111400c2d100164000c0d80c8285900420164024811070080d51159150000f060602c00e40d94942021258102c01101d00400110382c9440c00d030b100300c900d64a4a030520b0002c4d9101c1c0c90304c8040110106000540102040386081210307444200030441d0001c50b50140c5a603819951183c40640307480d0303c010501400c60004009002c4100074a21944028120507903c20b611142000244000c03900003042c0002031940034030400001582e80003503069522007000030103446900314a0036602907000c030500703800d81e41e06101004600d007400e41d11050403240296034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 413496708 1250 413495458 413495477
    0x60409260301180b0303431a1b09041401090e0115030b0609040c0506070f1203110910170405010902011e0e120c0d1b061b060b060f03090a03 62
    0x20342c00880c4c080e0140d241d0140c20511108102c080300000802046800c00880c100d0f000c81c200f100100d00100f0075051460750110880b21040c8510100300c02010080501c6960301418880401c9921018020309207402c0440000c101080f5102c940084030072080c0c01a00843c2d0b961507007a04005400114070a180c203628000b11201d0404020780100200ca40140c104101ea450340c80500c11210001001900c007503072501c00000d006d40700c01c40103000e0a40034448404000a45180406c550940c0c002841e04140c1029001d048581010b0100e80b5100c40450740c0f14620100c00300190f07982c2c8215581c840b10a040c4004006c01d10006400103010607100340d890742c0b0000c9550040a5080904044002c00159140f0340148541002103803c0c80d1012154100c801500e206400103440109818045400048100800b81d424980c8000c6001820003410021034112103141050360400000b90040c045549940c03aa032280c0d26084c0456010495000549540c1c0c5421a2032540d00c00c5041412030000b00c6800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 413497958 1250 413496708 413496749
    0x60402180c07080903070e090a0201030b0118050d050f06090a11061c2c0d08012c15031e1e030a0f0201020909010608070f020312060409260301 63
    0x1040c40c03090854409840c104400b540714206607030440c40e601034052180702d4020500c1d13540300c004541324011110003445180004c1c4001400d030341352002c20b81d05100b00c81c00742e40c81d04100d0600c480300381c0d9000e031074685c1d0540381410210702e0103040440303981c3d140c001d103824400400f40c041074402c070381401000d502000e00c1d100d4050081da8814000b01103100b41c0400c207210845125034109403144807048465845910110440480307503000750f0200c0f0788070391181440d081c2580c2c0201c0301900410140c46240003020b040da0245100401811001a4000c044000a0310715041803201001e02e060141c01c40e44101c146a060345001000e28001c68464419601c00b01d02d0035003102c556699180c00750026606040c58a40b059542074119450340301555020f006403206030300c800b01145d008000e00da88e62501e50518031405080307400e00320041d10442d00108400c40709072851950f8550414019200064110010308200764440280181024510703501002000c8210306600918180c80389000d88652280c8000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 413499208 1250 413497958 413497999
    0x606090c130512030c0706090f050d08030c0a0918051b0705070e0a06030b0a02041d04080403110d0228050a120f02041103100315020c150a1b02060402 66
    0x12031801c242400e0003200b40240e06001d4446440504024102e0342498182229a030801c6459041400012000030b030400002d4213141c1050000c082c1038401400071481616400300a1200404041c90b0f440000b4038411200e2040041c1c2004090800721021240900540100030301400d5a12445c2d0915240200220301244401c40e02c115034007000804d019440d00045448800b00145880c4416648040000201d68085040d500c00c0070108401a030b0380b424003c400310048140070b00c040b01d150b0800c08200000d001b071030454040d40d4000d40b41c002d03810a00030000380c04440d5008020342021040c03601c449002c9400300c840d510002d00b003481c1c030a000d48500502203000d0581c86211351201011004401107503014a100305180d00250000c14400354400010943c0c0e4820355a2101c1030056041c1001488948500700454016083d81503240c28020801282d841401c04008040b0307002100205e40c1c03c011581c090100c0100c420080790340d01490800194803244101c40981c095032070303540c5440b844c4002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 413500458 1250 413499208 413499217
    0x11090603030702040504060b13020d0c0504062c0607030e03070e10171905070608060409020d0b06040e0f070305150103030206160504180f1d071e0302120606090c 71
    0x2500950030400c0540811002d054003078011f0743c0665669031000322580705c1205401500c1da0411015a888045503042401ca4075480391100c1005418401444001c1d070100c002c0110408051241c1d50804030781c461060791501018001d0b42c4000001200020540c1005c055005040c0440940321450f56819803641b00c11700494080c031965108010a010502c10440c40400da031405074215a000030300441c9140001d1440002903460303034000803003080841ea02c500141e07489032044e02e0501a842250307000c10b00c0301c9101c034001030100340d001c000076549031110782c028403010700d68800f2184036004402e5450345910b003500041e109409090201c04140c2080004203040300d03456401400c80c1d83d110039025190030248400c65040050800c400200a101d0743c003412503100e6440000204c1540d000b1218048a1070b0401c440404e0007200b040710260034000c01d801040341d0b000e810381d00d4007885025045d601031040340c000075803025906800101c02d030800501b05104000640d41134029844105400030503004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 413501708 1250 413500458 413500471
    0x402030d0e090a1d07060203030f131104050702030706060b0a0f08040c060c0f0b010b0d061e0e07030f020c2d06060636040b040b060304110f03191109 66
    0x2e4041940c151641d0b0040d0100d10225a00418456050811a04020007039001d00010780c000300c107121069080503c855007240142c40340d01030f2242c82c0c0c1c0d60b6502510070030046c144650358440000300014024012030303004036803003c1c041000b56110b48640d0b4558001840000015001e034801c1a8000c0c0940307800303400345800100340040c1c6880c1810031220a100c03601708a5043e6454000c0c0000600004061406018030b1107400e034980621041c20070454805038481d14621001b11a1000c0039102a0b082405460f410420030708541d59120b8240c000e07085182d10b0641c45840000e080492217404500700a802461081e00540c4184041603803807400d8030440c4070744854002e00c021850601e4080014401d00505941c80c01013201da0708203508405a154160300b21441c2d008402e5002d42c03a15210701181c0aa040b541000090307141408680c2600000304000c0c41c01c2d4450074404156070300c1e6503120b5601c1e0b5008088400034807150340080c290012040007190001151078098802e031808844044c480c61 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 413502958 1250 413501708 413501719
    0x21002120f06030c060f030603240a0e0f070b04030b010905040b070e010c08030708040b01270f0e0105010b0406030f020f2506060b120a060f0312030e070e0402030d0e 73
    0x4540c0c01c041d07101d03480040c00d030319494801c13845000003940303c0d070014050303542070180d00c283c50f45070220525040100d040d00042d0701140c2d098410061707000744102560440c0d2611400075490810005042c80c200312a195041787e44201080016140c5049009005680c81007101140301c0e61f80742200401d50300705540080c00720001e180000c0308144201703202c50344010145403d00c0516001d48a200a652007500d400c80012091403c01c4240940824041c1c0100300c0c130300191075a01261045004550503c080883c130781912045c10043ca03074115040243c00ca56403800800c03095035501f450900c036911601c20280440c0c02c0c0450a40000320b54400d80300c4c0c140c075448006203050b07034000308030030821041ca0901030040ea40a9040000c11081e229060184c04003980c05a640d0b1400106000303880802800041041e080400a0200b000504005002c490340280320f20303501c1180550640c00b404c40303441d04030420722401c41d0005240510721500c0e4019402074082c7e521003005181d0071201000c4a41c8a0360f00306 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 413504208 1250 413502958 413502961
    0x608160611010b09040c0512060403021b03030702060a0f020f0f030403020d140601090501140603040c1205120309010510050603070f0e1c110a150e062505070602100212 74
    0x9070241080400e0307240740e0400000c5503105640050028081641e0603203856450810a0040381061074650041003e800018420751825903002503680d103082d8840c110141c0c901300d071080c241d1001c02c00d4035406603000f030180d911035000c0100200950503000300e6400511075262413103070020300440e60070807a4003140081e51030141184c003071007001001d00c8000c50708000b068440104c0e140c0c09004c07083c080d0034440c0340810300c3d500d41403043c00034a50301c52080f40310301e50030800e00c0001181c1021800440b80820700300c2e101a4180c2c00c00382d0804031400da090414000000412002050660021340f0907009560b440d820241c5178003c0c4031550104480c00390104086103850780c100e90007420000780040300288403444050418221002c07000c41c6020031a10310202c04520b142070710f003006081019014401d00ca1a600200b1100207120b11545400c240c02907900040362000076010b070f00070544090101c403100b1584da01c1858603d640d20018460500180075050990a8000b010300883d0008032a503403a103c0076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 413505458 1250 413504208 413504219
    0xb040b070809011b060c0f170a0f0b120d080a0204080613021c05011e0b090a020f0702150a02100203091b030304030b0c1803060130080c070306060816 66
    0x50b0350102c1142814803990020301110300c003034400c1d00d203c2c0f80d108450106a00e83d00e181c01804030070940e40315000303214410144801003103925205035031043c9500c00c040b41d9000070850410091000c003660703a4000c2034000c0f000c0c0000400184160203103510741c5c1d440901c1d13a55522a542240118040c1031070b10b410400c0451010030843d81401a658001042a00c1410310070303070402d68101c02e89a04443c2a5117421700040300058580c00c0c070341d0b02d01800ea003d10408000c07030000744900800802100d1142d0340032950b00d426540e4a415a001140d000d411510403c2988100c4a0300d80c100200540c0140725213814510300f40d03500d00a0b20300511256000b890700c0442c01c070142c2150780413000760b00e42511040c040000840e070011441e40c000e09901d010142c2d075040d100b5503c865903440189650081c3d20007001044980e0b0340803480b0907030030341e90b95441c4c802424080000b0341207090058083e01a01001c6504c40c000303840414010212407080804111241e5140e51858403000d11140502004185190800c00e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 413506708 1250 413505458 413505473
    0x1b0b0402040b0112061d060406060512040c0317040e091605010f1106270a030f05030411220609060806010e1012050c270c180306130302070b040b07 65
    0x80b401050409051050303030001c03414121071542d40035000442c604d8403414014013801c5010b40c3c2203003041e10107005aa0402074003502910542c01541c004508502c001014444401c803000e010350b40c820311402d641e0741000000007480c2c1140c050351410f405214081a2561400500034140924551710342c2c801524150040d980c4074035000030041404901c13170190100410502074940700d00b90204c44003002081e03003003030707841d0220007001c0b0b00002d54060b00e00030020075000003012080760701516010796243e0f25850303c8400e61441c0500b55420407180d202007014940b0003142c40e600c038141084100a0303107070350300c18581c10b5800c184944800354110600611801d248901480c2d401000400510340b074030758803000004034243c0c1e8942600d0fa50484034a001440c039000030420300700003101401800395940c0021210400305c010301002c07032071980000c0c0b81100321503040001441c1c1e000101698024078103103285224414901d03030110f0050041902c04074400140f2802c1c1c405560070701044506003030040e6180791 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 413507958 1250 413506708 413506721
    0x1d1009050901020c010203100602060f0702100903140706140615040504020c28031e021c0e03030a05090f01260406180312050f1b03061908030a1b0b040204 68
    0x403070740d502000074580301d803003d0004500400c00344241d40b80c0240303481c1c0000e0030120060100c04c443c0c0102c070240171400b580060140e0f507803090b94800140c00040d41c0360039a0707940388031001140e11030000708851007409801d03400308030190b8a40e010480da5a9aa10401a2400303410701145106c80080c001401641010350250050600d80b01c21101d010076a002d40040d0180501d201009074454420003a0801d0f40c40b0140074048841030020351103406440f40065100c240a070180b118203401180031030550780c483d800b5001488406000d690b561008410000c210790f100340c5000c4d004118451840c107442d4859048521640000d501101070f191000454210802c4003510540342584c8a0f03110b005840b13030384123204440300e10075103c00908503040000b583c1a02c1d0020100746984100d003003085500302c140a007101d120b001555020360789944080004d42d001041090303160118001c80404920400004010074910030036031a6101250b01000210744202021000104a01c075068041001424543c0110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 413509208 1250 413507958 413507971
    0x5011e061b030c170412150b09041e0606060f0e090702070b0c070806012709050309040e01020c011503140c0d0609020103021b011a0117070e060c030a0206011d100905 73
    0xe04c008458100034502580080e0041003180000c0da81c00010080ea00e907014001150ba818107201c101c11031400155521001030001c0c0200c0d03031480d6440c050100d41220001c005a0081c42000100d03100d42005008040d41c461000c080f95120455988074505260b42500c0b81061364010718005040498916050b000034504c000540309a1001007068002800001c1c003800401d5404602080505002c6840303085112002c80d07918903000441c0c01007400402154207000301580c0210310800301c5243c11740207114990079845c0b01e51802c0d021003180c80c0340028407012a4001c015030765009045008150f02d4045009e1010307800000c801902000402c950012113516005040c01410081030b0902e074046403100000da03c1440c0d644c0d00284015121111248011240c2882d1007503040c0050300c070030458168040c10080500417011480d040355541c1c0000c0300c00c0d5008c2c0409407911159240380103961f50b503082c0100d846403494140c0b1000d00701c2103621801e1141c1c1400c0e08104039940340c0021000140b002903c075 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 413510458 1250 413509208 413509223
    0x8071a0901050c0111180414041106040f0e18030a05072018100f05010c02040213080a060c0f030c121121060901050d15050c04050405011e061b030c 65
    0x1042603103082c415025049181c00d85c8030b5551840040c03100c6100d80700c0122500c15441d181c505030020403005443d9078807940c400801c1515924610028051340100d50242420080f40c00e40820003002c4649140c0c0039503c08041d03044c0c59a0780b1007a841e12801416079800015030140545008034030600c003605003544100030928100030f022004a0102d61001e10f6a19000f00300400740000c2160540040000303041490032582c03443e082c5030009111541400b4041d204035000301e265018503411040510080118030101d44060006140c2040909901c1c0c104101090601c0b00c0590124040c0c0120315880c81541d54180d1001c1c0540032030001051070482c0ea042e10302052211030502d110f00020741421842d2481104c02c40c2c5051402c000708081c0c140c20503405604903041071f000080c0c0d880ca108c0540c000642011a0940d01c11004000500a9600180c0d01c42d05110000500e1608800e0340e48041e10600e400030441c1c0d4443d9029100d500c124030268a2000d8a03114501c0400e2140c0760310900284174001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 413511708 1250 413510458 413510467
    0x206160f121803020d18060509032b030e0705060d050403090513090b0c09010804080307030f020307050a020d0903080d020903070f0312021501050307090b1915020708071a090105 78
    0x240a011110304008241d281891501600705064042107000b07545050391610a90f0546408404021b0309000e01c5400700b0702102041d124071700e81d0300784808004008164986400208442642e645003030341c40ca10000481c1c60441291541400810104241c810140c111850318400d030240708001d0000500c1502008044030f004030710795a410401c09500c820980000c6a1031078282025510b02c00c0c00740621030444010015030596980051000e640950012845600d0799901c02040e401752419481d800480c40c4004108180c040e08030000c1d02a00e0001c0d4200c8a51021029041e118542e860001800c068000d01000d40a5400d5170001e01c103070103000e015141386d19990703c04044600030a41084650942c65641039080550421204041c0c0daa0b90b61402402d5260401007520307000c10340a2480055200c81d24a4011b450344541e00041209124250300c01c0360f40c0382c440c0541002204540d500500a146000912841c00a08441030304c40e12500b0f070045090901910089030302c034501c15414400c042c030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 413512958 1250 413511708 413511737
    0x100510020f0f031b0304050a031e0c0617090f061501090e010806070e010c080a0f0323010503010f0c0215040237170307020f0111030a1d010206160f 65
    0x1040100d56003160b4002e603103440074120010700305508501c44480c0c0b0340c02444100700076a1810b4600c021603412600c01c040b041140300011100074070703145019000120750100010710300d0b840288400ca0110301142c0e95540d44941300281e483e00d204000d03207010ac0e801400031950200501c003288040080504003a040c00d40c2d107c00100001078268000b500c0fa40001080005054115410380c400c1c0d903003480d0090400d030b135036074070850a8014002c0c1141040b41506040c0d84160007a8490510b260081c19a40315075581c0c000000c5441c0320074080e1500035400c1c5146180b18082c3d601900360801490307000740803402103403100341080c44002070059a0007040e0f00f00d88954040a0000c0c40211145940714035085201c20040414070211548035041c0b100d80c0d120203031500100441641c5030181cac1150303a2414011f9103001210f180a458250311110b000000e620000380380c00410a01c460241d03040043e9003900c5180044ea00d502c800c440c0d09034602081c6500c0b900c09841881c1400c0b090010741020f090341032400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 413514208 1250 413512958 413512963
    0xb060a0f12020d0f09020f0d030c060507031d0307140102130b13050409080403031d0120010b12010e1b0603010303120e0a0c03020306060d03020d1b150605090f100510020f 75
    0xc0c2c2020130403d5485900c14150306201d10000d48000d002d48400c2034801055800801d400842000584482d94604c046030203948680c1142d074070b150301d44820291800c00ba0903001e469900062003140c1591500c49104081c42042c025200d07590f2404440320b0b030443c60301d0542c0c4c5c043d034003010406484142c80040400c0340c3da69071241040c00c0d4010507280380c4840c10740c5030241c4803205c0814802c08140c205482856180e0317202c044911030f420342d2040004101450350700ca902401c5449141503000d150008010070040741503210072403659488003210803000248046004c402c05211005401030010401840824050300003c0c1d07c10748404c50000d2480c406c0324410b0304040341090100c4094800102c100700398601042000d0704060221111034007064242c0e00a9500e001e070906000a20650343c000ca83c00d141000132103a0a590410406480e082205000d20010039050140c10700c00c80301c84000c00c45803581c60403110301c03132141600d4a001007800c00081041680e90740b202c11085115030016411019400d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 413515458 1250 413514208 413514221
    0xd020904050a1b02030c0a030f030e0609031306051c0504030512010f03020103050105060a170c210907081903050306040b041506020132070504080d02070503010b060a0f12020d 77
    0x40080000d801c1a00107401d041c102941c1c3ca01000c560052119000c2c045021410a810561506201d081c0c0f43c1268800e0380500400c0043d00d01034090002000f81083c0c01000070002d11907202689443e0540b00c0b201a50b0300d00911000ea03c50361222012007400e100c2590104e50094021f04002d4100040e0200c68485139a00360420500420000300c00c004650b0140540c03805000c0071185d45082020149005080680d5203404400c0000984c0101d040000e030790307003120320511034001c44040400072035080500100044c0e801403698820070728009030900700400d001003404841d2001c6148040181c40c03c4070950005009943c0c403664a1418100302d0381c403481100341c00c0c202c01d8009416039142400290844043c05403020b05611061404c03046c1822072007090a80e40742c1d40803c101543c0350b0000c11503440c0a140c01c400c4581c0b0410150082c1c0e6600002d042044a0b8128001d10103040e04106000c2c107802002e03c2072021440c4a14081401402840c04280c041003420006091801d40000002035514 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 413516708 1250 413515458 413515471
    0x8031b0d0b030c0a0302062b0e030c07080c011d010201230601030c080c04030f150c09080c151b28030e09040f080318060103080a03050f0c0f0d02090405 67
    0x9641d211000c00381000d01c0200749954040790b40200c294515004141c1074860b40c1c01008810705401560030242032070000c1041418501641007189011240c0d0040c0d403644219000301c0315106800c00060625400904a280f446041c2c1d11b130031145500308085840b0448600300c00c0c0c10342d500c2d030408581ca03082490709040b0030008013031041481e081000000d411100b20001003401c0100311000c10203c1c8801c80119002c4941c000d03615040c005060601800c1034007900d509810490030012183d034605d500004d640c00b0b0720340400a41e0003010b40a8104a5541c0111aa401410006000001d4031408100c0221051001c1405807020015100350b81c5035902d100b402e00c1000e2800466030403090541c807003000d60800307000f905c2c0c00d0207038109605e60101d19156000024201d8000000165032218560a9a80501000400c40c1e00799616072038940d03070075008405004006850100080c01604800c0d2140b4041c18001145518014001c046400320358090755441c00703015000c0140d020280c445105084c0700f100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 413517958 1250 413516708 413516711
    0x308180307030c1a0103020f060708070b1503060c071a041509050d020706020a0b0c07080403050f010b1003050403090612150b071103030c03030a2003040b04121b08031b0d 75
    0x540302e284c01560142c3c07000c8520140c80d4160300600041c2c03200100715001c0c80d400c44138030391501420300e400d000741c0c0b04d60000207000d0300002c0c00f440300350b840f4000c80e078035040011410764240d41d441169a05090150780d034054951112103240104011400c1980794200d401442c005004c111a403030f40340309550485108950741da0041c40e09104595061186034007400562018144254103a100c0c0f00d6090700252214024a0000445500300f1900800700e900440d07100056071744032010300c14064028003500003030a026280e0401042c10462003840b0f181c2c4516410381312120701a0504400310346903540b000000742e041d50350700c0010036180d152411145c014851110101e544007118a001d824810318000c0c458042d51051100600141c0040152035201c0003203140090591425418210204129405051b12a600109000a0017107040380d444c452809501054400c40200030110303484440864000c950850a480c0940003c40e940011600f0044215000440c20b032214000c03600d030780c840404241e41c3c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 413519208 1250 413517958 413517977
    0x7030605060a0806180f0d05130906080307060c030e030c0c0f0303030103150203100513020a030627090206091c290114040e0d050904050f07020a030818030703 70
    0x5290244950041d002d0b51207800c1d00340350034116640d0314800f600001c012104001c13000801c041c00c100d503010039114401115440d480440c070141035640400b00c919003002d0403820125480740a0301405c02120384020040d0301c0c0c040030785c88190080941c10401401c240e12010400e079454030410280503c3c040040203016509a8401000030011440000500a030002d100420200708801d202c01c80d070011082d405030350f0342d030380b0038007070030002d815400007a4000031080105051040d0769000d8421100641c03010442d541e00c0e680d0300c3c0c0c030000a403020f101021803610848000540a40c0015100604c09003075982440a4040040d0141d42d0390402e00c2c02d0070001d00f064030b0074007082d5030b0561030221580c10010112606244410364644050044002507006091103071429107680c0d02c042c0f00c2100280581e070b010b04007144010003135440189418480c42c2014003103202d90000010050003a92203400601d1009840c4c0e42c16105440c004001400783c403404490a502c00320306100070310300076119589050702c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 413520458 1250 413519208 413519213
    0x100602060a05070516080706060e012d12060f140906070504050117071e080604140c0301050d020d050a030519081b031b04030c1502150a05060a03080c0703 68
    0x2031030002004094481d040c941801185070f00310048407500a101600e2a001800318240186540701d0420018450380c43c10b140010040c0e00041c2e00340c165800c4420b2031a03409440c1004283c602883d0f03014403104510180f081020582140014010f1442120003280c145291540c41048036609418008520488400c002060a062140c0c1d43d00c07400034140141000c1c1040c0000b0120701626039503001904208001c02d00d160300644400000e0342c50a50038201410203150000e0040d001070310042d0040e42040030b45500a4002c900e003a1203001010b18082c00e42e0719007000c01c04c00074000402640c104d5400303645400419001d014a0034800c3c0207480380ca80d240f019030701515003d400c0d021880c0400ca08907044c400d500e141d00d0030312402110302904580d03c3e903d076640d080e54803001c0e00300c4486100e00001400000c101500380e541086031055488aa229481480d040c1d80f100c00f50f0b01400e07041001100004c58451540c2d01981d00000d0180c5400c0c1c0f85e5403296200c1010f54031a8454194a601c1072004004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 413521708 1250 413520458 413520463
    0x90603020906011809020306060d1a01090503210a0309050a030201150e0609040f15180c09050108031b1501031a06030309030309090a1107030c05010b0f100509130203100602 76
    0x4100e40280b070a4080d4400303903040d04e8007000c2c1500030603980a030004081802c1c0e40c0da0f4800c1d56000c9800c190100000009014204001400720040e076021883e0f5820000d1b191801240c4101c61054500f0f045005115a5103500e00c1a44921000c00c01d265440d40003d0100750100001b00d5041d10a400010312001d403000c130b15070030080341d51201c1c1c0c03002c00032001c00c10075455075900b107a0029486007001c58841054600b45442001e54a6003d00480c0f50002050035404c886490006080c01524007411280d1260f8501c3c066a5090180d1a000d078010400c4824401460152101c60303101103041d61303404681d040000401d88020380c07095800e808000320140c8040ea0151909401081c1100118504040840800c2e1a4080d1680751840384162000080800c855500101c609003070b80840180d0b40ca465107070291410203400c01c01d54466282c00038440f21030408203907590325003000910903005a42c02030301c00c07181d40c0d201e0703100750b0303000078044070850b04041d0f290010f1405858404200030755075051510092 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 413522958 1250 413521708 413521711
    0x3040e01061709010204050d0809011116140a0515070303060801050c0711010206070912080d050403020a05100504050a240c1d15071b151205010602030705060c160501060906030209 79
    0x3c10907441044200402c0d035604607001009540650b106450f00c0744240141c1d041c0c00b004030088010f004480100c02c04a1000182c03c0542c6c06011121103030000740800c0c003540d403a03c0e0107115081030304031440c0045030340202d0151062510030b1801041c602d86072120759084d1101602c2c040c21809002c03626070f08101c0500c66002c981d907020f2008088500c3c1850004010f15003902c241755816009100705018400700d2003c442c99102d0190003440b40741071602d0300954a05000d8419511401000b80b40751075001103014140c00703240c006c001418840581c0d00c50060402000b44c0b03010000d08280c61440010754a4024111000e48035100c240180c04040700041040f40d040001c1841409103c5c544c0617140c444c2030a40b46525001104d240d441e5607160465610b03850396400141c0e1403100000701031809540000640d0486400d08020f01490341d841030241ea480c05801c00041168220000145800c40c2040140110490102c0c0c841e440134030b507407101421a416600003ca00a444901c2403096040080c0c401d07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 413524208 1250 413522958 413522971
    0x61006030e120309030708271c0813081b1906021b04150321110a02090916180b270402010e0616020f060913090503040e010617 56
    0x1404008581d10756142c4841c190309462400385000300205043d420104240d0b5509036121105640d1020540036a058150001005d000030190241991256040c00100b080704407401100d25a0b0307008440e03440015580165080e511041b150940010b24504c04016280030300061440300340c1a0320b60340c41031011504c411080704403a00c0c9814400c100959001400080008614034116072510030480094060200203110b0440c0c0070303c0701c1000c0240a81003240080c429015060401c000c0301518040c1d0b4034800b030900c214482e402405800025041c01244298080d140c02c095401062412a0041c0c0740d40b415000803481c0401082c070640c034901d0901c03540047c0c1a0407030311103103191010b80c2c030395030100d0032809070740004a0b081000c40c0c00c41e40110380810313039104000c0c09103484110304030110b401030941c803905900c107140c52040b100342800c0050846900020140c0b280b030b0821355030f09a10000c0d054496007110244020400085c11856003081180079005507981c0003000030110041200e84000074064 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 413525458 1250 413524208 413524211
    0x60b10030e0c010f0c02090a0f1508160303050a030504060f0203090109050c03280303150b2101050108010b0f04080a0b06010206010e24060c1e160b030a020306060d0c0206100603 78
    0x1c1c90702c09810034011708845a045407011025511000d81c04050080080a01400e90605900e11071200041c1080301c10b0725004d0781241c0040004000001c41103442e032001601041080001640b4244282c1085500501901d8003140c507000c1d440d451400c0307034011640240e41d659591107510420030180000e148001084004105115034042c00d40400c910220f40c0c49407081d1001130040405020b0f070411001241d03202c3e89505116514851aa02940024922100c42d003401c07c020f0340c001000544135058402c1a95042c0d02c6030700304204040c0a50100400c6100e40308280300006000d5410440c1c24400e0744580340c940c08038208036002910780300d03040c1c21201950b44030008006803210040b0b9418000350903001060114000d8001044083c0f080c200140054003801d50406160130208040000c46140305003240c0710040c0c810118400c007642405024000701040010482128607038014503049100100400e15200241010208072a0094400405a044441081030708402d401d0480010300751070a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 413526708 1250 413525458 413525477
    0x3030a060509060f0d03090905040339140a021302040509130f0f1106030a0e0601090e03041a04051c02010201061d06040c14070606050901050a0608070804060b10030e0c01 75
    0x4c0030b68980d2a4500c2c0200220200441814411442d100040c40034041c20000c40c1450f00f0000c2c04c08210740440284618241c1c2c00c4461030b02590303070410b0030303481441c2e50240314070b0150b54401c468400c04503007003581c0c82109041000340c0d40c0c1300b82c541c2040c01401780041e903c51905050011801c030040c28000a1020080c20202003401d80314008045a400f0540403001c4034103140107400b2000444c18190891008002c01c40d000700359078400700310400c18a044414680e03942d00600142e40340010030031401d4000380002c108400401520000c2c0e550003614450800351140d01050030703030114940031241c03080c58203100c00039540c083c031500b4040e001007a110780401c030070441c02c0f00080b00081c01080c00740399a00744454100c1c0c4904082e040109044800c1075550341c3c1402c094000d80307891300a9610a00b104d0f0000101480e0614038a01103500c0382d20740240e40d0b6644482903601220042c4240d406075110b2451424aa44400c0b88040401581c2c1300015000c0700001c0703803454480c940840c1070600c4004c0300c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 413527958 1250 413526708 413526721
    0xf0f031908010312140f070629010203041a0d1506170708132102010b041401060903080a110a0b090d0801080601151704030c05100203040803060907051b03030a060509 73
    0x3018549481410506545d402d8509203240c81c0c41540c05060890002203003075403c000b01c03508010030301c2c65401a80721a01c00014003080741d07850020360703490242e0f1040000b01703c1ca01e0104240e50b9601a5405c0c20ba040a5240f406241074695004c034001818500e903e00340440c40d0040310001d907015484041480c02d21b080c0e00003400324007001d00101c1d9281e5109101ea41007100416603107058074504601e6144407020701d000a40a4104035150741e100c1d03130030490948441a40458958121100c87d42da09036000e1558958641039480032401e4800c100342440d1240c0782100410419803094071602d090040b07498070a401a0400c1550050403080000010041040c00b40016075a41500c840c41110100a1a5014103440da200005001e407002e04030300081205040d0054052103215020380190b800080700b800550b01207100458004111342c5041c0080344060400222003540300100782405480d03c112000c1e0001301030200c13001c0750b080b0744c400010005500b0840c00781a00500080e2aa290241001d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 413529208 1250 413527958 413527973
    0x20c0907200a03030605120a080a0c03022e0608010207051e01061706040302013603051b0106210213050a0605120106062a0b0403020f0f0319080103 65
    0x80c16080400c0103903208045444600110410010603003821915080040d180140140c03c0520411b842000500301c602141e1002150320502d0340c0e40140c81d1480c10803288001c0d070310044903030019800c41c0f01d112920032062055040c24a210500312046415003283c840501d0159481c940045041d40d0060043d50001200010800e008000307491202c1402289034a400d0f0042080b40d014251181d609801c0c40c111840111340c641c0106c3c005c0e4001d210041c0f5112040380da401d2149110000d010000c0c071201d52000c85114040d102b0bc2c460724243c2c2c40c003e82d0440d81c1c1c0740480c59481a2a040c1d41d6000100080645c1d0341092010721030403425021400c41940005840c00e1011000004580c1c69a0000b04054080d40c811409054000c10075000891141d6001d402407001c0e01070f9101042201c240d0388040304628215900c48104840412804195681c5006030003402600c100c080d48206c09034098500b0042c00316500784000746004684642c098061342074400d00d45040b103000d0003064001400801d042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 413530458 1250 413529208 413529211
    0x60203094804060303050c0c04061a0a170c0a1707020d05030a090503070510230c0c0c063c04050d080d11090111010b0901090903110106060f020607020c09 68
    0x5100c1d040554061030540840d04030001e10311948985840c0d004020580c00202500603041d0301004c41d8032520380d130b0701400111607082c00b40020b8000100c400d00c0038010b2500040580c03080701e2400a0413004480c0c10000710801c2075076000322000e004208001c50940c0562185646c2c03045946440c198140000080e4848040d10711100402900000003083c9207480d07007111101542c4442280d58074841818a661100f445030700c0324030420b080c03081f0b01160746560b030750280084c1601d8007000d02039203030003441d100e29500802145610340601d071607c0d146603039010050300039942da40303008000e000103c004609948921800180e100b0b00e00324031f110b0841d0100c0741600e040d40e9058450492070304035402c1400c0036002c1d0380c551a0382c0c00d04004034504804071410240c11406c40a81b1404001e5203800703156801e980c000a0351a4200d855400100b1070440b1503004140345e28060304084050b04120789580742500c10310303044040030444004501203200d038100f21495008140f84041e00c209082500000c0f00307040c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 413531708 1250 413530458 413530543
    0xf030b0115021b0d030908100c140708090405190f021305060c03042c0a060e01120b060105210112020f01050705150711010c11070605040f030f1103070306020309 71
    0x5034044140c4c101402008141e01a100e1201104d640b400500c0c101c1c070190011620704400101003210702202c03402d056054031110782d401180f550810070034500b03010003000c0c000d009500381200c0c19980001140c5a00c5484c4962001010160f904c0000d51082c281d8504c140d840700e03006900400a911041102200f43c501340c41d2094046184150050391501160403592064074080341140f00340202c48046038004012507440707401d10a0180e1303a80d00c3c080c0001c96412000b40500356030000040c01903100388001c00d4001012402c20485034086180c0d49024803090b00030303400800c41e028014042d4600074400410180c02403030064070340009a643c80303403a60b40c1412400840c800042c007140440d8011041c418003205007400030041c80c080403000802407c4a110050101e005001000c504240300324121003c0e0f647d0700315124052850b66a410b10581e408200c1a18040a0310011023101d94003402200c1c005c5000d100c0141e03c90030f280d003400f401c001c0403005000b405000e1341a100100410086a03400000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 413532958 1250 413531708 413531719
    0x50108030f04180e030a020102121617070201110d051902090604030b130204022701020105150114040f0312031b0806010c051006080f010e03042d0f030b0115021b 71
    0x903c0b41c90381070080c1c08081490720040c000424520205681540500f00c100c4541038030102903122509100ca203024484040c20004807549208100b00031803007034a64002030b491000043c64500050341d200030f900844481e00425440700180942c40ca004181c103011a1201d0400714500001c10000030b806115520000f89100784100008201d00b0108101d805900e0300503005554850b0310218107805110748051001302d0b07141001483c440795105100c0c1900c01c0720a0f91040781080545d80055803a07a1a440004407440300030007000c15003a001c0d5000c8401140300b00b2450380710001e40c800141c113a81d0303c5690180c00055a80100d5080e6503c6000caa800a000382014110a02181806810043c10800200e400e9090001c0040c0c002c400180c3c207003141140d40002c10409510041c4180c0b01c0c401c52041c0130b0740100c082c03184448498082080890052094400c03402c09607170f280c1f1a1040b030000c0c1d100391000d4941d0001044414100c83d141500c0300041e201030000000020005141d0303056a0310118040d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 413534208 1250 413532958 413532989
    0x7020307120e060325020105040b0a09080708040816060c05070e0a09050a11040b030a0b0c13030b0906060a0e0f2a0f0304031707230904050403090306050108030f04 72
    0x40e0003042d00c845034602c007810b165501e150403220401a5044d020b0f10208800b42c0340d00c00c2d20001c0c03043c85a40c1c00b907940042d00c00d00b00d854401c3c14a01501c21181d090368800010450040080c0600009000030480f8901070014a50070b007a120a13070418591105007031183c42c441200c0050340c0841d0000c03d42d6852105902592a03400f074541c006c1a840078010514403803a0840424816101410086450111024040c1c0b02c001800d01d500c940070b001c401412030240c031012800d800307840c2028054081202c003414401c00e9903034643c1e074108a0203032007040050b007008051100a080003500400a041440194500e0742026414503441c510001c102c1c642c0b01088100790031056003040c00107101c009058000d01e0311074208030003603502c55000741c9003103010811056070800402a00031078148a42031b00e449228a07441441c080404e100e0359421080368141003000014078551707803841640c0c0160b010343d80d42c80d986819413616a08543c0c0607005400d650380148881034080440d0307001c48007600c0051881ca10344 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 413535458 1250 413534208 413534243
    0x61a0406121a030a03020c03010b0616110f0907030905120304050c0d0213150e09070b07110d0f08130e060a06050f07050a0f1a07050a180e09160e07020307 68
    0x24400d1a8182d560b060240d296481c09050f800244c450400000710002c02143c18510300b000458032880100c0301c0c3c00422400c3d070f10080740401d00340c50240d0101030490703c10058210009551141d04541101c0480c0ea594100401d00504200c203006004010380014503508040c0c036141d0780d0740400424544260308006254046440c0c004982101c1a0940c005000c4079140da903d060701103d00340070b111201d029407800902420400105402228958010185040d25a44900c5c140e91504200036810007500881100020142d8203686c602500034441e4035201c03c041c14507200c1c0303404c00d6842034802d08425070902c400d80e0783e10b040c00d400b11415800d00540d1480501e250a007140909031003d80a402100f00139400d1000007448030b0b114900c1100d000d80b0301001010840184001600c1000005200b8000c4c2000c883c0210070441c0b58030791308008422050381d04d13109008850000c803440d11868010301810705261100d4281b0300d02503c00680c0c80380c181e103003040f002552800340701c00140032007107030940a0300c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 413536708 1250 413535458 413535491
    0x702010506010e0d0c320414040f0f050615030c0108070f1b080a0c140102030919050a121d04052e090c17060d020a05121f061a040612 59
    0x10110254410003001406c0c50300b090404091000c0141540c031079817103144602e018403407000078440302c9400b6a400e880d640c0310040343e00d071144400c685019013100b21798003080d020001d2a20038800103000708882c0c4111410706080c0008859500d0501c8080410301003030f55000309201c22811001c1c41d0001c000c00818030b8441100c40411805040e40b0000590f1508a80c0c0c40252070035410b004040503003a042c0521401da080307200841d800d824503005490904085e49440e40115861405101101d040101c2600d807900761407030603100180420031071a8821300148031110001001c44084408005a00d080f22040302ca8003210b10032402e0f00c007001c0d0b414003e0700d10240c20a03c041c010b450800c0010310651a4040c100005004031070814045800c0001c80ca440c1901c2c01d144119805040040841e01e0f0605110b100e10030706035000d44500130f1103008511100c019180c0d00d0303502e19156020510514050855000b96250b00d54092140401c1100b4840d541e04504608003200420000040034800c43c6403419 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 413537958 1250 413536708 413536733
    0x151e0e0a020f040f050a0b250609060f05040204050603030906040e0606070f03020f070b19111234020904030c060b06041d010605040609050f060702150406080702010506010e0d 77
    0x520b600004038002c22603450502c0c00a0640e2410f40f40040c0541c1c40d4400e11049024440100c00300380c103010405160300e07462150400d40a8030514002c0359011032a580c6601355001c54112a0015613100200015450b00c0c0c0901a00160b00764091407808000c007011801920582c0104804145450f01003103494548400f155500343e00300900d09910301240c81e000b900c1d0382c80c101542095100340d02d00410030782c0d031141c1110840c40300c2c0301e064200c9600520080d01c04d01d49195404e40709c0d00801c0607095017810303600b00503c1034110690a41110000d010742544107540540b00d01c00060b44030754806070058a6645410b40c00036014100310b40c1954540c07070a9070150a2410b50560401808600090441c04c401b1014200c000001e1440e0b003107a0320b400084646000d54400c4000140e0707000d00c00c204504055400325030290002d800039182c205240c0100d02e000410740c1d104001e41c1c42c0040c1c10441964041400d41d04000346200a0184d4104440000c0805c00c440d44103074440c01d044803d80040108012540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 413539208 1250 413537958 413537977
    0x70522090302030a03150e04031b0611040f090903020606090903070507031103010b091006030e03190c030f0e01170603030c010e06010501111203010b0c030d090501151e0e0a02 77
    0x14054500c403031034002e4a030b410045409020034205140301c030000302285040420380d40164580c203003070783d2030f524210f400c10b00380e0a41030040310b41d401e03104e80820b245000301401d9002c034903551a03846d854805c1e0001d850916030b010280181ca0410b1800000c0c0c2c0c04030340103410010072103501c0c00e20340703c0b0f8620b68214803843c00010480d101722240002040741ca805080e0724814220000c12982d2100000d03c500110b00310381c20300020f90061014440b19010707074411130a54888800321303400d0240c000218101442e08500c85000f2030142000201010f60086036126403660314507080003400070070800a0403a000400c0031b080c030404000001400390714108107131910052100000d00040601c00119502c40c0428019940010f0100c4100c103048400060b504c004a5107441089142d82c2c41c1c140b981c0b0158004010040c0135000400660282d1000d0380241454203000c0d01c0002480c0102c0c9a491043d182190321520782000503040c51300d401d110b552414800c1316115102c0c40d06c640e980001c3c08000713100c1d02909 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 413540458 1250 413539208 413539211
    0xd020301060216332c0a0611070513020c03072103063803041a0f0405030a030f0609060314060f0610030c1803080d1a03070522 56
    0x50400c0d80091000e00b80150006030702a072035150320a0b10003801c200c002c004840c0e00d80916000c11003100100c2e400c00040645080b02810075404c5d08001c02c00480780c02ca0015007000e142c091a58070b0b1201080e00107091a08000a00f08220a03c081d141d240500c00d09116508038081c0c0c100811258048a1602c03181c202902d55454151524010004059900e002030811100b022844580a0300c500780a4030350310b210740e04045800991580d841c40301d4050741140030115610031100d8403042e0000d5805107200704500001c41c040c0c0d6000e207410070402003981c45e03849003541c02e00c008160040120742c01d0090500c1e001c10000800c0760300030301401c0d01c0e031b004149582ca01540002440340f0005007490074000ea4080d110300340c562016592719079500352035007a0300c41509440021040d001c1d52018001c084681407040000010502d4a09403080f00d50050302d5440000400d02d0700e46a651285e0861104100b40c140c082400c200d003c01e9860a0a00a03a030181040265130003c203e460a00c0200000c0420f20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 413541708 1250 413540458 413540461
    0x3140c0c030f030f04060605040b1516020d0302060f0a06050a0b0a0e0603070315050f06030f1312110118260c010204030503131a0706020304030e0d0506060f030304140d080d0203 78
    0x651825050403a01070b14403919007e404100e61420307025200820a009184000021504e48020003683c440f5040c1d020582c410851000103072201400003207180d020b5000741469160440c0d1924842e01e0052200068918003407052100d1380e40c050040040c0c0d00d8582c2c1013612840d02943c299018142cbc0c4603015406000403040104087c0d06411100441c13034070031000780000d0358403410f01000c00d02622090368400b1b000e200140004503035a42c41d990084240007000da000140e41c8544c482c1c580780c80d00200011b283c080c4c50707145280d03003401480c0c074405005400f00c403940e03007076120044599192503856080040402e90085054901c40a40d035514101c14021940e45640b45030141d603940c01540060341014030a900004c0301000355070f0b1140201c0b6200041484d042c0c80b543c2d0302009600040c822001d202c1c2000c0110880d44a8904089a5030320a100404a500304041000f0b1000d4000342c01504c40e502c108024400c510007102d00300f22608040d00c001c007060500e880c001401c0c2c0204804803c49070f10210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 413542958 1250 413541708 413541721
    0x60c0301050111030301080a110607062301050f101d15030f090706020a03030c17090607030e0a02033c0106150f05090907090902040603020c0d03140c0c030f03 70
    0x40158101c8400741c0302c40100c03421465106440380024810712440b0340142e04d5800101e40c0300400d0040e10540204100c2c0741c8009a80c418044881c1036501e440b207428148045104a104122844c0c05404100d96061002003c500052a26080c10a02c0003c210540018141301c07103802c28150302e036040040a0480480b412018000310380c1088403608094041d60000c10300034400400e808040d14a560302402e00e01c40306413010b0300548840310b4071208015400361021900d00349400c1e040e0151007910054002d5092490004081d0746121010340c2464102c40c0c00c80c0016540000c1000d03207950199417010400d100c1205064400b40a80403c01c0e68100700d0401c0744d02400103522401c1070b03400c0c2e0b802a0704c2041c0e9080302202c0b140405042d0300046401045031032018540000b61036440601c51425000301038440e80c4c5081660070170303840308011a0700801e02208182c000c2c403282d03c181095140030040c211100ca41c564010801400c200030072140003942101c2034005004842030410540c020542d68140343c2d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 413544208 1250 413542958 413542981
    0x4060909350301031709060a0c05060105010f0c0b06041b0f080906040c0b09040b04020a020304080c06120103030c05161401020d0212040b0901020f010908041806060c140f06 76
    0x21008500404100d05508403205141c0501544101c0d51100d40c00c5a086503650884180c00d10041002c0002c1031040d80d4540c0d032030354001c1c80000025611840c411000e403a05616040041e049541488103811444400c07560008801d90f80d40c1c1c00039410300080e11840080760080c1400c8800e00f1600d281440707240b900e142c00100d001c10f4440b503a913070036545070b0b503e400840d240c40c01500c0040480300e00200030003011040e44060203c003580200001070000b505800101240e12248030800941c101040811a5080c1800b5400818205546040c80c208403c0710f42c1c0721003a81404028140441d910021007031000800043c3d1000075400320b02003119882d0348040c1082400c1e0f40a2600510440c05d40c03210180c030201708040b128083d11541401c203030824402c0d048a400c01ca00590451040202070310b4110000d00698490600400f1201d5885003000c8100100f00c104408405085042503020005c46070f0109181c08580d403c034030f09901ca0002000345600707060319aa80300000c0d00c81e10341480700f5810f08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 413545458 1250 413544208 413544233
    0x5180c2803110a06030c0503070804051c111504050a0b0c0f0309150702010b030c210a12030b0a0f0e0a060510020f3a140f03010807060e0d0303090204060909 69
    0x2ca6003010000da03210405c6017a52030f421140400154180041000203000e064095041780c461025102d50361214400c0c04a11551841084005490f40d0009400c0c000140500301000c09050144085441d094440315500c21151000601c002d16680005a03481105001c1d5804540650b0b07603640d03a41800c1c0b40d103a5407070490b0429484015644d0340416151401441600001c240c0074001c2d050401c0303440c0c1000b6006508100041c06100e89144000c50704906201c0050424825a07481c104a01009001812150480c03111805080c10240030701c2040c80781c0c8615000c0300c10102e80040306644d1101034001400950740801d80045410302116039107900880c8000107280300c081102c141620000d0946004c917003840540c542900003140b10507000d06502e06c0313840480d8480c113200e1143c01202001c1c3e08664000000307240e42500100050204c420288a440d0040c0305a151124010b5412000103209002e070120040500da030304c0343c55004648541c2c100308000e140d0b0341410811009a802d089525080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 413546708 1250 413545458 413545493
    0x3020406030506040902010e090a1806020d0e0604020904080313080c030711040506130e0c060703020f06060603040b060405060d02030d0c0b0a0c0503060132040905180c2803 76
    0x1000b00040c51400c2034401d8a6000d0b070142d50340191142c0503800d2200d01480901501070b07443d21410907518a040d140a0f030070b1014450000144d5500130350020b4001c40722100c0940348503800407800d001c0580e840d5080c2c244c1107901f00c86000e940340c60704100c041e0140041c0c500204030070790201d99000d2402021000d0580c0d1402403850b10b85502c109010001114022619680d0240d404411000c00c840317036900030b1a522080b1300854030344018075400158240c200e014100e005a020b1148101e520034103002403600140c00707944150031800c2c1551400110000141450b02239aa034100280e040e59a541460040a4001d0290350110074292002001c182c0b140300c00303945d900004400b0074482c50481c8949600414141c0d01c881c00d50325030000444036001c80100c00300d24080e401e507a07860540c080941301c0d982082004050307039840f441d20444005582004140484a01d810a09445a030301c02094031481101d0849110520302801c5418415140c240d41040821075a610000f108005514090a91941 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 413547958 1250 413546708 413546711
    0x140a030b0a1d09060c2209050114100c03021b0303070b0106081f120b130b190c08060f21190606050a06020a0609020607200103050916050915030304060302040603 71
    0x143c2e0283d8981d0b07145400c0c0d03081c1d0040c036420048101c0d500d07045030f05400e03070344007142c0503038005079851080c01d0544000f078010700300902885242c0300c0640341171440380070012824100881d40c04400c0d207010351038011841d82c00c242c030807801a000b0841d503014030494a010b83c0c003201070f0640f561a01401080700d0004c40d1071300209140d05d40c0100000741c1e20246941150317222203c0b42c2005000e0350701d10306d085902a24068829543e000d6001c0003c00743c40c27046100c0e944a058285840c17102c140c543d403c2d42c0080ea124401c1c01040002e0040f00d442c1c078030400000080c1500d5010006007180703401c130790805515114050a000e080a07546c80d0481c00c83d070140b95107000749401d01500741c40d04d04025a01c0414458900540c0c0176501140000d00311307400181c05240000d00301424854551106110f4240f0203c00d182c4154008030b06011300d60f094400da40e0000003100013061326500c4009050620036040c0501e500c80c180e9500040d01d260101900220011000b509680c1c68560710b42e0098041d400500440703020a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 413549208 1250 413547958 413547961
    0xa0b0d031713150b06130303030b010207050109051008070e0402040e04020f0402131701060506030403020c01030f2c010b040e03030403020f01050c092707091d07140a030b0a1d 77
    0x28400c1e51040d6034000d401c00b0110012001c0200d181009040c101c25117500100280580f9001c200a0b80500e0015030080d10080b810b40001000241014a20b401480c144491203000b40407503100c00c181154a0040d82c1408025a29036001c00d4520080100075139500900005000c10b00d4070182070154000c500c00c1d1059880c48042c40104002ea0244203072000015119030340404c00b0b00b0242d8245903c80418000000c0c00645850100d03001d54000c8078140c0140e23110312041009543d05210f503208405650304200072041c2805190015445020b0040001da40c02c40244a000802035012040c00d4000900420110040000c01a220b400480c0e050703000d4014805000c009860601500380710b0761760359908910386500b82d4208060100e81c8207410b610284203040c202d8480c5188407142d03029102c691a41c4020b107182080102d00d4020704981415152a01c1341031141540e0000320303140071810480030a0341c440c448090214014800e8420700e960240034100001030340d2031404d4007403c0b03c03290028415510b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 413550458 1250 413549208 413549221
    0x14030a090302150603190804051008070e0d05030d0b010e06190824061c0617010e07050a050603130515060a090e1203071205011706071d06030a0b0d0317 67
    0x24001140c490360150806c01ca010402d60655282907100381c0b10b032040a040c2904c950200d00c42220f44000d07440801c40040a1000207908410540c00051040f5078141540c1901d554846e113900903400110903041e00d0389030000d16a03000d8409002c0c0300c6000303403103152030703504050031043c543d800d1000321404511084007056170440000c004440811001050160f084d01c404103000c001d40c050600a02c0e11500c80003105121140703401418024183c10800100f580384071603440f804c40740441c4005050342e11048003001300d9141c0c52040022142c080b140c2d00c0d00c0380c0ea070300300c0300b250b05010490051047c012071118214200701c222215010b40701c00e40e4149034042c0c840c07140c08200d0320828a480b4241d40405045501100c8260042d6488012031800180240c40c01c45070505448080e0050410700c140c4210f00030b460304003041170a030712030745900c3c05050100c2182d00c81c800b1021000b01d0680507034000000604120032a8204081940000d003000c100c100d07941c2001003004101840c001c1481c00d810010850 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 413551708 1250 413550458 413550493
    0x503090705011209050d0f090b0a080a0207050f030d0c09090506030c040b010306050423102315070f060510140405060d02030703080c0d0302160f0314030a090302 71
    0x204001290040004034204401074403980c0080c1040e40b5025200c0107120000390f0140b00102c0c5c00001c0345c6480e45d1003142c03d00c0241c2070319844c0e000300090340004e00040716202da00c40c0c2e41c01d40080c2c4c00750340103a5640c03c0d81401803c010609640c1000c506c40013610f0740364981b0a600424070b003041c5948200320280c40d05c1619044d14420381e0110b03410b5002d01c0c034212462030650f10021140405040001d016692032021405484070081c0c161800014055244044900307400c1d1b565112022240728890f40f424184907810940d00c50880c0c1500c019410b100c0da042c0e4482030000c9294080d007041c219211081884c010314404030000c02240d002e030900010511a00c0603003901800c0d01c001032051011141c206c07040c4001040d00031310391a8412500b90502016031014003c0b14040d40c00f88000d543d441c0b41e148603083c5011a542d01110801d44104650302d145c0b042241c039050300c580e201d0120720214015080c12a0b0071540308024401e01a000400e22621101c03507440440911f11030303000d13500f451095000000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 413552958 1250 413551708 413551711
    0x60a080f0d02101a040b040b04050903070b1005010c03050a05040b03180c0109151d06040b0316090e070323150a060302041a1b0102030a0b04060b0304030c121b060b100503 75
    0x4440d0398450134842242d00e4950000c6208040180c0005902c190610004050321025114181c050f04001510410b100003156800e80c48400c2c1c48407410030500d0640000d03c81c128420024040140c080380c0d17000420710680c200e81c01481440d0199880c1c3c203080c0600840b40c1d003c44200702041c49210951040c650040304a0811225000a010805000c10209903007401c68604541d1351500b289810f0304d02565140007402c0503040843c030007a1a80b4080c0e0041c5c003040e0301e4042c050184031101600700f020410844100f0741c0074200740f5010407001c100c07105031807003409594a000062a044801c0001042d207044030341c0034160040745e1303a401c283d40e5410143c0891146000d032400340c42c4540200c101015400000740380880d1880d103440d0400d4403605844d0f003260010b07940c4826407a210000c008061816000b82d0b0080c3c6055100706285080c1076902a08002900310300911400d100118600c0860003100c0c03000c4a002001098980d040c0745240090080091800c2688503100c1a000b80c022141700c0e900f41d9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 413554208 1250 413552958 413552981
    0x21e0a030c12050f01150513030f1403030412180306140f2809081e07300f0e030f010509010515011b0503070f0803040b010501020d05070605060a080f0d0210 69
    0x1c1c1d442c0e03406c1142c01000744202c2828030062001c100080310004c1c4260451100850007031811001c058132901d000c0ca0f09065a9580200310b50044c0b0600c0f0204038052801050000e10b0f041c403100c204680ea0b8503090038440e9500203403c580c606030180e13401042c050b141034441d0303403a40b030b01501c250b999235441050000010301d2130544c0c504400f0907402511055100c1c0442c0790260459030b05040c01f0702500c80c5005003080103510000008503108e0104011a2070140641c00b4007425080c09003610001642c02d00d01c1c0c1c26640081059180b0f002039503c1c010500b1100200000d004c0d0740d88a4021000b09028113010ba681c660741d90310385000101c40402d1010101c00a030016503804000342d60300e8013100020401c480c800d45140c0010461500010b40c0d02903e2002244900301c2c0d60b88901d8581404140018141c0c030507415134002602c4070490942c84001c444140350302140005054442c20003041d02031500f80c00c00d101503c21001031803019840060688820b540e903034200c599200800228106407241103210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 413555458 1250 413554208 413554231
    0x20a050f0d0c080904090503041e09050712091a1608060904031403040318180e01052205070302040c1e050a210b0d110102070506071203021e0a030c1205 67
    0x66000a0b1020008040c4204002c002188006164643e80d06541c40340c1d00281000030035410ac94900240380b01d601c401040490f00422440c500b40802600c400f031081050100c1507a80c0a0920402500a034903101014147d05141d005140512005d202c6030360846070341000c28852070005d8007038034000b425175200b180e1503603c400c0e00c0040c0c072040c4840c40c0c1000e03104909012482c071a2044100380e000d001d800a00c2502148898031415078842411940c42c02c0900340681d0420b0204004500c005007a501101c65100246c6150880ca08080b030600d044c58000071b60007810803c3c100c0b0900d0f4082c0c0640600041c440303000180224012064645114098001006c1000c040c1100c0000a00c80318003070300718082c105c004c1a0b4090b100c000039000b903032840f0f049440c0001051405e41a50341040248040c1c101514018039080c015229200d81c01d0780da0007078904058002944503456104111022078180480c800aa1100c103c0071010700586003c240c0400018010a05000c07940300d00e001c0c0340d000c0c91a4011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 413556708 1250 413555458 413555477
    0x504080406051b060906060112051b131a0c0106080708060c0901091203080103050c030703050c09070e060f18011409040e070521120a090605071a0106020a050f0d 71
    0x1a40c041d0002080d5001c0d02c101c2c0040b00480f04000d01101d842074030103802416142c9413610002d8050140194008070b40362034613040005103030066026001e219941c5040701d803154042080da01c0108802d401282021408410349901d41c05014050702c0303d119104000d1011940310703001c050781c691551003020140d40c0007101188000031048001d00352040107140c0310b040c943e143d5000104841d200b600031000120300304d00400034081d052003103000400703088000d03008080c40c58545503a42c0c1c0410310b03442c2c440c2000c5e00100d00450b016000c08146a4001f40c2842c0c2c07a55000661b550300c80d0442c0d4040798000010076a280c1d40c9610036418107e00243c030f5081141801c0b160028003000b403070701d1040c440031361140190203d1555100c0c04070000450941040d0210b0424482c40c0c541480d204070303107110310a403050156002250308034111005483d00f170310b000d0780c07114001c1c14102505503402260350102c62302d500c004910307964081842803405008008946981115550031981d0390009841400010b0000b038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 413557958 1250 413556708 413556719
    0x2030702090403120902060a020a1b06020d03270f0302100212150a0306050a0f0e06132a0e0106180302030c01050c010207020604120c090218040905100608010204050a0905040804 78
    0x13040741007000c14a040010f13a096080d404071300d0a0344141400d40c0964010b80030841003203240107004000c212f204541405031464110060341d1050507900d43c9003070584644000d00302040d0070360400c4e01840c2c0c5640c01049081d40341000031110349921820740060148d01912a43c3c14014000c540c1c5100c0141c2c4950317002d5440c070032409108141502619031111030320b41c000000c41d00c1c4d805401d00802c990800010140300c002c0b40101280d00307078005501241c201108002984855291016500307401172908040c060b500140c2c01d50035150795020140641e5001004a86040c840340c034075040c1da5944e107e00304141c00800d04141426240c0c0700c000c0d45a40841070310103403075100340d028180090346540094100980342c0d0004401d41c001c3c1c3c20200d0798140c079502000c240300306c15407050300500c0e510300d0461502d140c0141c913140c00b55003000b000d4080d135100e107445002c1103410005d034842d81350f25643c100003c645030001d09010394000d00c030341441204004000b00c7d031102107200f218020742e440000c0070702d03051914 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 413559208 1250 413557958 413557967
    0x6020c010905060d0e100e101a1026010303120504020a1a130b0306210a0308040f05060a050609010b09060409090c03020a06080103062a0c140f0303010503010c02030702090403 77
    0x102200d44030544031a00c4c605d0281c8100908460b40006200100b8000c400c141e03618031b081d130345c0888a4202d0341880115403c0704005800751001040c2a80c440b5a2001c2e003d40c180d540c050310030000c102030721444001c440786a40c2244110b050341e00c1395884050005095420405031403007902c029500000707628003044001d40c400045040c82d1010071480c0d08000300d4040381010050103500004203034070000100310b024a008161504444020310800200703511000d0150380d10300004500a051207410b40205d01804403494401940503408011241c462a1440000010703010640d40c590040808000100b100c00c00c280584055010145c60303a4141441c00030f8400190240c0001581c0500304000f0100268403891000005400640ca45103102d51552900c2d82c12105664002c0c621420450400c91840401c0841d4186034111031070183c6054240e42880201c06085000d40006881803c1040035040c0010014504a5104a00800115a240340b0581e184c1c8102c00c0000d5200d00c1180002c0c0019004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 413560458 1250 413559208 413559217
    0x5040303230f1008011e05011508130f0f030210110c0d0813060903080115180b0a18150e030a0c05060a0203090a030b2202010207090207021206040c0f06020c01090506 73
    0x11603481005403965680380c00e0031961414124881c0c410100f081251b070303007a50301404d80180b01808094140300d64040c0e0080c40361402030301c003d540c9140341c00d800040c01003160343e451105400503044250a90729140107941c0300c404029110503d410b100d41c0300311420701b520a440e000c03151040a000d840801d01006c0b2800031000742041002011180f209010035581c0c40b8115555109490b404201c0d410040d8a280720500700c2c0004c030030012140704034000c1031780405e0494102c1e0a812038003a22a400c030503040e60043c00c00d001c044080c044030000010a4500c040700301401d04e403d81ca40030b10000800b41407680742c11803140050601c0b01d881c002000303581481e034010f205003042032050300c1c101000840010481501c562040d103846004a05004410f24444044820840403a414036100c2c070003540003039107800883c810715183e40c0c0d000c1001815900c0d4141405d06400c1d048055488030303d82803a103030f00e1740c10481c020218003502c000e1f0041500c034000640c1392240d01c03050716101c60683c981000c000303840c0d11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 413561708 1250 413560458 413560471
    0xf0906091e0f060903030708090f0709050c09090901020d20040303080402031501031101090605070f03080c040b0310080c06132918121b040908090d0605040303230f 72
    0x202d03514a40900c0341402614010800c80020f95079a0600c064000c0131f02c0409040c850f01e980000c00c005c03075804e42c00540202100c0305002c0105003660b03185007000340b9001e4203408503000300c0501e007006110344065000b01800380d0002010001e00148110184004280181040e0740303810400003800864000c1003207640c00f500c018203c0d4010110309460112240082c1d0080720307060f09e09036a80c0c0ca20340e004030015019206c6071034202e04140c00ca4a8403094519204409400d000c00d8a01103000e251458044902828a0b02d00d800c1d90303410f04456444001000344500e60240c05074268804581c0341c60070840d003581031074500400300700c3d04116020845820403040c84d61001c00d461551072181c00018050b11002807098840702141c0061000c3c41000065070310065070580000d0b40d1494150410307032184502020580c2c0010303c800840c90482d0ba00c1c840d01d40d12a42c803980e00c4410b0b004001c0300d0340000e48540d01c03981d003e1140090780c059044041e60a040c101780000d0b04080024000800041095407125 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 413562958 1250 413561708 413561713
    0x1503021e060c0a08090306070c02010c110111120904151d0c09090106030506010e0111070e0c090a03081305030c0904060f0b04050c07030921020d03170f0f0906091e 72
    0x441e849841d0b0314012400703408132058580850312800078582880b141b40d05c8030070f070305125200e81d20301d034002420000300000c02001c10f90300910800060f44100c0807414910310000458081c403c2045101006400c03214800e80b040e4140445000040940c0052404a82c2810001d6900d1009071a102304a00c2004001c2d1000800500942c0d80070390b80c0034107950090106d85c0b00010342d400c040d00010902c014840c0341c6810b0120f0710031402d40c8420005502c5046418180509040342c0b0b48185071021032040c19043c6521441d42c4030048181708128000b426070034000d4800b181410b03130390818142c6410240c46410381c070006900000780451003175006070070360845408000848100d550b00140490303009881c1000100400302d10350007010f03080603240300500404030080c0391151500200b8021803031784880007406003941c00c07003030030405025500b900c1d007104184031006554030302040b0a803806001101c03801c0c00140560080b400e080e101080c0e06004182c0607028000420402e03501140c01800b4400c07200301403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 413564208 1250 413562958 413562967
    0x2010e06070305090a0b0414041103070c02030a12030617071d0705070b1006030c17060d15020a02100b1806091801060b07030207050a121b050907121503021e06 70
    0x280d44085c40c18000e407004040b0140c03550704000000521905604c60540603d01d440c2e07600014100c0007042d243d220708a4a0010b42c02c4405d440400e09260b6a11030080c0000750001c107000e2a60b800d42c0101c015542c60324005074042506c00c003102d60314003180c856041c0c07a8101310003060a1801e195211030303001c5168108a031600c0c0943c0d80301300d0680c0c81100e0130804290204001d02c44154107010b260080400c40c54800040c40007201c1e602c41649010b81144d100d410340d01661020054540190442580d0501046488004443d0041e44803008001d1305202503251062001c0d0600d48640900320010300380c0b41c04102540c400c0c05001a40c0b0001e00045943c40c1074052031480d840c002d0007542c02030400c00d0440c5441d4925842e0180c41c26400d80c101c00e200c0d1034503000c02c2c040301c88004103042c4030a0b0490241243d94a4880ea80044000140c01c9a80c010082c0307420824102e400000c01801501022000c01c54081200341c0c001c03141c03407240802544007003061080c160340e0002205050b0782c0710b002000075140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 413565458 1250 413564208 413564227
    0x120a0b0f032e090b011809051506030607050f0a03150b0d02071a01151b0c1d01060206131403090303070c0e06010507020f010809010b031002040906050d02010e06070305 74
    0x1084580280b04010304402c070100006414032902c42d40700a155020b090004852030f584007240c00794140514058803e0300400340d603c04d1503640010209a405c10192202c1c6491000c01854030142101d0241c040e1146201094174588544101c1c5c4140d00f4003841b03142040c890388030403005015034a419420725a848a000b0400401c0d400c000e2070340c4004001c1c0140d980d01d5518200d45034100d9031400f007440f00c1511004000051442050869940843c90800180c0c50203408203881d43c40c0590b009095000036103404181240e402c10072402d10b508202c00009a6039171003800700e0366581c0c00c0300d103c00d01c12940240740c400580f0727610740d20381c4039040502500d04208a25020900d03641101d5401d07600c1c0d540c10501000185809100a07400910a2a0071444c00c841a00810402e0002400b12810031198200054444c40d0a601203070035100e00405444d0082d0381a41000d001e50064010303000c2403894171100241c44e02d800e040301d0404540c182c58603000c015910f1700b000800c0d0007409054003445401c0008150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 413566708 1250 413565458 413565463
    0x302041a041e0b0d02091609080d0801060305090c031b030a140a031106090304180209040903110f06190507050c0303090a0c060e010c120903020301090b010e060105120a0b0f03 77
    0xc0c250008000360742c00c212041d10020950312412a581c1c05064100c1354640507071501e6200b143d1240003c811030303801c03000c4807000b100e240c0019845105940075104580403840d9000c045c4904840080e941880700c1d0b143c480001d41c80c0c80e0501c45955141e031040c41040302c9282c1038a8010b01f07040c0f0007021303070308044455100d00d10400030600e41c2d103003150801d905c0b08041581000180d94100c0510000306841d207448440306660b4404c90243c00882103201c0c000e1312050b0855012942d80e504003070024044401d0500e00a090b0303030760440c1c1e048a10b0160b00003200d011100010b640344a001010141000101c80362030040003000302401c0841040b00c1041125650707038041000318025552040102900e0819040c1074030400142c1d042a01000886022850681c1e4456400c40201d41c009c10300229000030740c43c098583e0115644000d4155080c00c4141050090000c1c846048441101c18000c00c0c3d03440f1001180c462052102c0c03c03002401d0100880c0880c1c400354059011400041c0260101072401d500003032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 413567958 1250 413566708 413566721
    0x60b13060f1b0b1605030103030f120207060c0806090a02090d1101050702030a0f0605071407141914120c15060d080d0507020c06132c01030c0807050d0c0302041a04 72
    0x4481d0b400203c02d0242c07003020359012580302009840c210341903504542d03000b0615000711150804222800c42c00106920451741114a5030394043c07410450840041c01c05054100d040342c0e000c0c89210302034009900d000c1c0354021100610303401400c4a49040003695890101c0c90342c1038100341048018840b002c01600c04010044410380034800ad220300c0303d414501082a100000d1208003040340e001d9850200c01c0c0000181c0b0700460388500c8010440c10403e42c81072a0841000e07001103000c0b50b4902440900c1082c03401c02c48041c0415040d1484640c9840c11b4080500c640303032440600340c1c08805113611242d0302c2100b4580140b002458004144042d0300d602c60560483c00400080540d10070034050110b404014a600e10041a18880e0800002840e98008000c0605c81c3c06e41e181c010112410360700f54903029090461180603c001a00d507181d003080081d0350391500a1040c90b1185400c0400e180c07520740080c002142d0720480c51284141103a00380405000d85040843c00480b1400a10489035250301445 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 413569208 1250 413567958 413567963
    0xf08010503011b032c070314010204030b06010e130507030614090606040512030d050a0c081b0307050f090613080607080f130f050d030e071212181e0504060b13060f1b 73
    0x814011b401e50a00c962400450021f0948c0b580c070400003000005c10100300160f00110034244032440000c0c0b40041200081d0b1002c5845200d8944410094030303c2d015030165083e03541801c040441200a1170034070080300c60641c2d4940c1d09c40b00911041041c0c4c42c2403501103201001e04000d43c1d0415010300381220950710281e44d4003aa160b2600b2141c90a20703440940070354401d0159401aa904218010540301d603c0b0281400c0200140050301126516585045846550b0050f00c075a07a9400d8040200c00340401302d01446d8054010340000c161850b01c20325019002c1c5448441d0540c051f203550400170701c4100c4050702190340f95461709542010890501000414081070344020401c0045544254201002074106c000401c0300003a4143c08942c5581415103403010f14188080c00c2a103099408140078040e51080340c40300c3e17440e400c1a025050752481e6004440081d01d05002c55520b80100659034001e040046045548080040113603d100d02101441e20f0000c1c2808512800308118002207010507410a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 413570458 1250 413569208 413569213
    0x3080405011106060a090b0105040e0f0f0f1b07060609050f1006050705061603060e09100c030216060c0e0d050a11030a0c1707150f08010503011b032c 66
    0xc100958101d4001c510300305240300038068a107407000003e050703a6124000e04225580c1c071a0080080e034018000ca1707020300703c0e40400c0042c601d010840721110203822107441c180c40005401140120f00e104003500d00401110310800d060341a4498600d040790000c81003a505551100030009401c100d0b8440c041c09080d071046000c425241c003521094a080c0c0307a502c01000c00c241040716801007180840c0303541c1c0015220b0010701c0e50006252003100542030541010729001201001d005840b100042c400d21410003940301031003050750044054089004d11081d24600190740d02010000805c40d5001254100d014140b0000c0c0240324404600c4945605204540315403214414100744445c1d08280d0301108411002004814020303036900604450912806020a400c0982210ba0039010300018000d0402400300104107400d91500034140700e1040c0e0101c0102d001d410003c0b4071400c06010340c0d464082005c011100003030640d08114010301011040c40c41c116002071016404c6030050820700a9221307101d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 413571708 1250 413570458 413570467
    0x21801021b010e0103110408030316090f05090112050f03030112020a050301020a14070303090f2012032b0e03030105031005061c081902160b180f030708070308 70
    0x1a1a01014480204003090400010301590381d01450303c1034046400c5c6800715424203001d8101201d4016500098603c2c0000b1003004400c440707d0040740c0480307604d82d86903603500e5031b00d00420401c003456009050b0000003940061042040c074130012500c0754401c80440700e015012803862070842e0030a811103a045130125401c03170154a490140100031740b04c220001c5151000c260005031408109002400e604640410784009050199010701b00c019003100c140012a2a01c1ca00306650321700d0b408031121001a00201c1d03d040b03017040e032181510041490021480d10340784030b039070240401c0140c0701c4a044003049000508804014001d0590300c1c07681800035901c0f54181802c1505020f5000e2422107101c5ca840204035240d62500e00f01c144894003402546846100e904044003540b06442040180503054084821004e03400144070000c880003440540c0c4607500c82400d1510783c0b00318614110301030048109004035140c02c94810042d840e00500b1190441d0341c40d14040d042000359402070b5a041401f04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 413572958 1250 413571708 413571757
    0x1020d020102030c090d0206120c03040c0918150905030c060711031602100c06050906060103050604090b06101b051506060f0a0f050408031813020712081902 69
    0x10aa404141900080d030461600703c072024010301810408a104510f040125410344d2940c41c22078200300c207010503040c5181360804503003007140c0c0281c0d4121081d0f07a1400c0009110480c0e44520454a030814003041c0d100242a141e40070410440f540b08000c040d5104801c4001840420041c441e0a03450343c00341c03400e40340c503031006080c41d00d0100750341d400c940041040a07001e20342000c800d0700c010340c111901058007800c000120303403862401c3d0005018610340307414005105000180d1920901c1d09030390900c4507540320000e02c800e03900340d84001000d0204c940c000c904185816445040d000d001e91400c90b84910105451130306000c004003094540b40c106032060302200024050180d030060066440500d808404401200d807440703903038024000c00011b54910020903114804850041014404683c4c44801030301d03042c1042c071404101544100345250122003105070600036600b659070488a40441880c050900395444140208410b100c40381e41c000b8009852420b00c00b8007800603080c84401c002d1310126 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 413574208 1250 413572958 413572963
    0x7050a0501060f06021c03060906060302070b060319060203040206070503031306050f1009020315130b090a0e06131b06030902190e0a020d0f0204030503210103030210090521090102 79
    0x150000c0000c0c03044000c0a00c5200d40004802c01d000d5440c40d91b40310184001803045000700050b41243c1401414140c0004003254543c0252004600a0b840d10321141c54880400da541e2000c5e40d001c2d00710040740d50702e10010400f55400307107500070f00250040d80341c6071250b2340349400e503401201c940b14419944c03c40c2c0303001d1044c68401d25901c5240d04080000600301540809010101c0380300745810242c0000000c0d0103100024021441d0f04d00c06424208007145c07171041880a031024081d018080c1040c0000190804807901803205071500c481c02030300b102e8071170107000e20b501f001400302510308400e40e840360244200003138010402481c031030b580062910301a10402840f130f1b1142e045416801c3c15000b040c06036000b00f20015070426142c8800503500e40e21081084090b00c2e49410004500e440458000184007010000300a44500040280c03010200d19161041900e001e0201a005a1000606c0a4004a00d6100010325405042141c1060002c00282a02c400380003e00100b00c3c40080384070403655804 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 413575458 1250 413574208 413574221
    0x302060a0309200618040b0a0b03011403031303121709030306090106051c051902040305030306040510030f08090f03030c070501020c0a06021203070504180b03150106200c040207050a0501 82
    0x201c105107283c000340b00000b00280500c5038800c0c6507000c540039201075075a550b40b000c01049405401c0f888140e82d1107291440507002440342010b407103000300002c13030f40303150100403104150300d1900100e00c181d055840d01d07414402c024060b40140a041c011407a605240e030740e01c2c184540ca20200840d40e03458150248080d03c4010b901590130302c2070a0004152382d01001024840c4140d0300d483c0080c4558804401c11a806102d0070002445840020080309120b00403008611410301660188483d45540d80804c0001c8a184409050030042e070b0015400584480300500104100405007280a16020f000a0940e40024242e42459000010800aa50701440550340d078081c00c560320460103142c00c801a4a840c000003d400e00314000000141d021070080d03042e900980562071b90710110000350b10030800206550380c00c00d031203841240c040c401d40800401c00b507416141a541d48000e207800810400d00d400c1c0541540c0002c82c0100c415800b940d03200c5101070409540240000c18584006040103404c440c2c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 413576708 1250 413575458 413575493
    0xa150203010b1e0f0a0806210d0305091002040e060406053001091b030b061e010e01021002031005090f090d050c0f07151206081b03070302060a0309 65
    0x1400100719140310001540c3d001000388089500660380022640d44a10031810f030007440c1040400c4c010302d5a90301ca001a4420780e02501e03003064201c52601d403040780010813039240c3c1180e4442ea40c8103041c0ca200e504481d40010800045036481c000701000e0406a070400d4119041c2c60100504108980ca03090150070010042034a14801e50b90700c10741c60380d501319014445640320000d0b4034031003d90000254443c034807040c0c01596208034a03049034540301c06503169100648081280d48089960351030102c1d00501a8001494584280810200190b9000220b1000a8154020b081c0f50504d61605400110311a4906000c1900040e0400c020009600d8028108140500c500410480350340300000311041e001200b0f00f050340d100d4107044d44042c680001400414801d000b1813500007418210140114001a0940c6464410002c400311007411540244510a801d5001c0071100f1317003c400183e4103c0750450094103440000b038498000c2400782d840780742180c001913038a1180b0414000c0b00303401a181d000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 413577958 1250 413576708 413576711
    0x60903020c120d051318092d11010c1b0501020f0f0312040f0606030f12081501050c030c0625080405070e0a0902130b0316050a03150b0d050a15 63
    0x5401400c4250f03070b0180740c00154103018000404a00340803040a4680091648684d0240240c142000490181501c041e00710742905c40a4003584403c46618402241100b261800e40995940342c2c0307559101040c10041e00e418080c8298004001c10525010504030400504015103454907000009151101c441109030341038010800c04110144040110398070505000c8445225071114200389003007003035104c8018801ca10300b240000c01c00c500c2d1010f081d000390051403007418100c4075a1f0b0540340304c1002c892104151a860811040560160001c0d00050706840116400c050b038100c40d8900c0d058041e03540ea110340c40e19100103950a080c0d02e82c3c2c42c100b20b12518140d0b049051682d03800755104038078010f0340849009c500000350b2401c6d0b84e610803038100da00100304044203c45840c20000804405040a000b030041300d003055000e1100e00304010481c1d0015260490f100e01c0d6171990341340e4400c0f1072030480015848069003a130030b036990300300d200c061809403014180132046031900e050804010706a003200b15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 413579208 1250 413577958 413577979
    0xc030f03040b0d0b010e1207060210020306032e0c1d060c031602011809150f05010f12091703091506130c091e080c030f0c060c1603060903020c 63
    0x2880d040c0c40340c140f00300c0008260f0040010041e41c0300249841401c0e002486500400b01c0c6501c0080c4100032940070390285c444110048480302c0aa20003204ca0503050382c82041003000803203c104520010110714218250b819410341d03d0700007a0344403058180d00103a2250304c501e440418a08200786400011103440e441c140401c00600c1e103d0041226058414401c20041425640649191203a107040d5041c83c4411a45880003200103111107001c90307203000315004010422138251101142518416150791104a103a21000c50342c0070f1348100842c41c0c0315110303c49540050707004a1400c4d40500801e884603240e161030794080e0b03d004904207580b0041e2003108188129616000000310b10784c1040c0c040403698250040c015a5030f058070b0341c05500030015000300b041580c030210328000181c4915109950318448404105540d500e105444921590000d021040c11850107074000c5c800c28007800245e41d00904000b0282c060150b00e54010b03212a1f03240d1404508040e818003858a13240812175055081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 413580458 1250 413579208 413579219
    0x50721151503230105160f0c030e151204080903100204060c030f021509011b02070b0901030b0d0b01150807032a170406021b06241206090c030f0304 65
    0x18007600e44800b40000c5400c29911a585003041039858010718460002e100c03500300200c0d1a0064403440c8900301c00200f585055165080c07142c10a908865090303600d00c107411050b4410080c0014511119400d61b4204021190340a030140c4c1c0b03101d205a01034103015803284c05003001e060602260394903811080d40304200901c40c82d9004810b5940303054040c5001c984040d0516000c1c2d20b0a4400b017010614100316804004205105400ca000d101c0140008035803207186001050340c1e140500d0003403a00041082c45004545e521962245448480051501c140b00d40a070b100c5144002c004e0704500c15a170b940d1105610b140350004401d40d040341b82ca00d010401807030020400744404204032001082061040e1810804e24401c0c001284041d112810920041c102494424025805a401440c40e5a1654040551003001281003441201c0c8000071451103034080307a0320842a140e51908a9108103501d204417103840c420444544035914080c02042c141c0082e038109440d00c49090861005580108820b225 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 413581708 1250 413580458 413580491
    0x11220e0103060c05090910050f01020d1202030603150106020a02090105102106090e070e070201060e0c0702040204180f140c07060f0b090910060905101205072115 71
    0x440c0c0c1c011034002600c1040783c000322494411880032a81c8202c0d04010b000c2c1c401410300c1f6080c1299811510032820111000040e620f07040c80040b40000b203070343c0c2c02c09201c0c285142c2d0000c540c02600142660460740700c1d06940410300d4003c2c0c001c000141d025611507811400c00102550260104640e0070500e1021040f00804c002c12202148002c3c50489050f80840300c510307004030020345003441052010181141c20070b5562006442540038609052000c5a6050700601c555400c1d1105014481d12a03903800101c90f80304e0303106003401c030b80281c2d00708000640c40746499070744000070120040100e00076042d201d582060340c0e00070700402c8007040b16009010304031030034400321010258040804220b00001c3d0b02000c009006c10a0f0f40f07500300a1001c1000403020020880100003c04035004001068840c0720b00e4086500403074001c00421428107081c072a41c00307041e00406d00c2910400c1214586900c40f407008101d818610820899244000d00c00c20070483d6440005100e010700d13810401244000038080744 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 413582958 1250 413581708 413581711
    0x60515030c130f140103050f0f0c0310030c09050117010c08070e0303070f03030209030d02010b0310020f13030c060e0f0d02120f0a080d05010b0306010903060c0c020411220e 76
    0x8010101c006400951407900c07840100c001c0c8001e4281c0e140c110758404015030751002201209002920f040005004030305201c5946001e0702c0c0d5540700ea40b485d6074400094409602c00b4103004c2c01c901e42104008001444a69202c025250724500842d0952500c5902e00045850303100e0184a03034100007401d21026401107000f5808041842c1c05550400b039500468154401e0740000781055178407950b20014035805800510204c00240c0c1169100070104404900300c581004200c0c0e8147c20151221440580c1764010388020075401c07014614109410b00c003200780300d0144d4400c64070502e5061082040581100310302400c0d00050700c14984140c40c40000600c408061035000344104804200d00700c600b00c007002a004904940b0044034610801414240c1d0150408e04400c0b514504020012900d064804250f03801054183c403030600700c41c215a030f07400140424480c120100644e0890400c0540e503540141124801c0070103030b29550b503044c8034415180d0a8140c981c000c8001a0300c2041014640410707505 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 413584208 1250 413582958 413582971
    0x210801080d0e0616080c03030f010b070803040f0303060801050906090708071410140403030908011d0312070311132603070f030509040e010e010b0102190f0c0504110d06051503 77
    0x4564403803a0000c5012050b078078100142404101150407400c5100020003035010b00380007a49c80980e40c0c0c1c0c030141c0112030f103c0d24034010705441e001d01c040360024805010084040d4803034100403c0c5141c0301ca20040c2141d8048030540d140f9402441480040042404104050599030014254050a0890308034400b4102418507001c0c01101c10240685031261880103404074108540c0765580e0b540c0e082c010101410360003036955652070404440c03181600e07081070f0b03550016504040c500b408013a40b80c14020071780c000c00307400c2415141d0b00051028414003009041c4000c1c031035440b0031307100d003480e2007204120030881d0a040c1511720800c03c01c00e0741800000362542240d114600c0000c216092074110f51a018045039541c106003800c3c86501d18020640000022400c0c140081000442c41c2004994514010300c0c0c0310320f40e494030b0503080e02103240000c1e81c1020600540d51441c1c10361740e9001142c2282d0303a441482090223408203040c8140c07015401b802000304804c0320f8441035401d030f4400551309403201130f005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 413585458 1250 413584208 413584219
    0xb042f010921120c1103031c050603070e091b0f09130819030209010f030c0e210d0314010e07050301060f0e18060a06090b070303020a020a210801080d0e 67
    0x41c088445000350b429015140c0c060a02e040b468a03914000e8800e4007500f200700d49a00c0f0350308402c1c94508000003a580310a407842051080768145032415001400c0213004103415004d1544d0200d03800c000c0481d00303802502c400d40102078114100058421b2501d10102140c400c1104030441500340d611808231640040c07400c6036416510451b860442594403035000e00150b01d11696041e5210503406a01400e60a50283c0303411340d10005421045080303031480c0c0341c100c02044003501e06a0003410a00c400c40641291a00e0100405413110040c514103a21342e9003100010362034100d8070b1041c481380480c4600501d60359600b00000e090019010f8002d000501840d400c2004c0c042102444501c07400c0c0060440c20702900350020039003010111591449d040340c1650041c0421080000c15512501c00e5500f211803000d001e07424a03406641c110040c0d40600c01200c11440340e001441d000c9210f04040700810400c06210741d42d1007000740c070007805801059210721025000264928041500f0000001454808841 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 413586708 1250 413585458 413585489
    0x1804090f02041d0d02062403060a020d09060203040c0f08060106020d0f1b0302070905090307050715090509010b030106080124140d020c070e10030203100c0c0b042f0109 74
    0xe10640296424008a0706131060500010085070003140250180c034841c1104400b09200600c00320407015800461a00355100c400014104c600d5640a048000d4180002040040442d01c1d1038003aa00140d5081c4c908940b401010000340030009040001410060050004c562600002175102c6004001c04011f01940002246946208070354170000c085416560905a020303600b0000d42c0d0764010300800000c14501404556200800415a9010351303100340140005801c0002c200c0c0500303121a80034040c040c10b0100400d06070f80300341100f4003811120407619202c0d0300d021030040c8201e80607404050300c3d0f20400080380d244002d01c4400340c1f003c00c07642000300114480c0d507040d10b054410035056980e00340c80451902e580701400b0810804035400d2100c002d049031248007411000341e0651200950503403000d036502e91206216000303c1e11801046c00c20322800c0900362101c9030203a100303c50803140b403107001c075800e425804051910002c080781d00754440d11740d4a1800010b010a0250b00a40c1c0c10a00d0901 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 413587958 1250 413586708 413586731
    0x405010f0e0423160602011104051e030f24060f0d03170901022206050a1202040503030406080910110a0e0f280902070308070c06021308031804090f0204 67
    0x2403d100300f128040e500c54511548400c00301e034484c0e54460700d201080e13140000000d20184140108002d0111169681c2d141610300320411a607541031258460106c0b071549003810096030140114030b10001118040e01d16000300200c2c041c0c6d103804070107120340c000000303800340041034454858110b5044019580030130741181504080d00c2102c4d000010517206080141007049090040d006001c0b90101891001c90440c0710a440700c1684e0304a01640d800210240201d0340740d5440303a104440d00e41c1b09000010f14180d242d801003411540650030060102d9402c1061040d01a400c2010507150b800040082003182c0011004215a01c40c02514108000340b0504e01825030765003115907070022030020800c2c0340700300c90f02071610305000b05e051124a88203140302d070000300300c0c1640c000c440d8265499a62840c4a60b9a62000d40f5406021001a030304d0703d50030f02200c902c0307000f0b103041c500141080800454682d03440e840e00e403c1d461849185030740107074101a00c1c1000500b618554034085075046501045028000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 413589208 1250 413587958 413587973
    0x209030309030a06060f05041808070f0512040e0105010807020a0b1f030b0612060c160807080304031e020111030a0f150b03150d0b0601080c130605040f050405010f0e04 74
    0x1071035a69458016801c0d03070810041d540c3c0c001000c45d0640844007040c150345008200464a8204d000b004031034188260900064840c0c00401000380b05e06414120f24450351106032401e01c4004002103010030014042c05443c80c840d01c29401881d013440e1000d42c510303220034000d45401d540d0900900e036030301c1400410b2820102044212400d5420301e510043e1590f00d0400d400182c0c400e444003030080b8404451503460147c042502d034131504400702c80341c0c68400c544244440400207103606607803200e130511213100020400b4006600460007a910078500380c04200c8c0e92010440e50320b01c80419a031514241c5100703090a4130a072a44040307801c07000030310b80300e4801e80c60b00035018140044001400041300030a000110300c000e10300508010030942c5d000c070300c6107040c40f0344000c08640241c1890340e1440081d0082d1b1080380302c0d6600640c07811180d404d1405c14130412528030a5a00031401180002c9801d000301400905014020201102c0a1115500d030108800441529000d80c100101440000400344842c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 413590458 1250 413589208 413589217
    0x100e010e0d090f060305040201081602030f07050f0c06041208090a1505070b060105030c03041e120c1a0f0f09010908160201030b041b0c051e0c1008070f0302090303 72
    0xc04064507100c0e5052800104900c0b028007900030000e000740004110613100784101d41c0304550603100d040a6407124940302d905c0f0740b07207901c0c00f0342184000c0080c03202140d0310502030a01184100000c000d290f4031122018201456014a075000e40d000344000c0044045a1010003c00c0c0c0c0c2000205607141940004510300d00100c2d0044074200e00541d413038259156000d0014006c40340980c032010046c0c3c42e010011a014031040d00c400c8000e10742840880e0104020985442a00c4480301d2800143e81035581c405900c040701c0070300f10011443d01300030f010500248190710300300f00c6455420a04680b501e09007000c01910007804540c046000c0c4400580e03486c03403d500144541c0c2e000300580f5150103031075415098518036403104a00090514900d001541014014040c0d8601c18080c2d0f200d0181c40c0b29801c980340886200103491510801825032001d410b4081c044170801407000c060040100c10005001100c100b04060383c0c1049a0001001241c40c3e0006240140344000d14016941c0c9030071000081c6140175 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 413591708 1250 413590458 413590481
    0x14010c11040e012c100501050109090f021608040603180206070b07090803031611030a09030602032a09041103070e0d08121003030f030603020f360604050612100e01 72
    0x580c0314091040032400c441401407207134103012036114642e09541c82c81518400e100c3d190220703502c18014099003919800c5008600e241800042c200b4012000802c0c4c4509510419145048005820b018950707043c000c1040155100e07810900050703240d030101d41103104843d000b40c03101c03820001103441d40340708005500c02040b4a0046a88a0514482003035244603002c0c00070010a541d030b59a900481404001d451101003e52034043c200c501d180c03112400b1794001040d0301200084410404500144113821a220552070300c0c000da1140300d50000c0c0130403910640c01d042e104480c18400c0160b102c0e030000d20000c40040c190b4103a07400e402c007440c140006002d04201550000102000c100030755503607030303918800c4030b01903615010107207449103082c0c04640c03150001940007886003401b0821400c00350803641840e541001414286145c0086540b0913011401800708158043c806005051829008003034220208841108500d682a038078240d4402d0055039151445883d00c0e03600d01c82d8002988508440361 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 413592958 1250 413591708 413591741
    0x607360b0a050c160305060f07050f07080301030b0a0603020a121719020c0a14060c160b04180606080f060a2114120417010e01020a0914010c11040e01 66
    0x31009031025002c3d8210600b40210761240f0404040c941e00c15404941c01c80741c01c035020300280d8441850b4101e00d08002803040c8240001040271000380403900c0020300364240034a4165071a07504500d0990f03000b60000d410441a10b04201c02031015a070b4480c408401c4951442c03110b60080c50a03e400712482d02e00d9005810315000126642c003282d07a00e1698449540495825141c0c0144a10200000c10025005030440c007824000c1a81150030828005c0c2284181d50701200c03e80300c00040540200c0310f0380d410110a10a000c0385c02c0103240d04140d01d211001ca400034041c014241270010082100300002c00428051f0302403c046915038541e0240309014100c1c455144002c030ce06405801c100782c0e48044221120a510b90901d4591100400c025188560160a45d441c00d0310b00000b01086801110140001d55681c090b000e800320024401841c1c0442c480d03d07040b00c858030f804c613060b62910180c82d51905001d040c00802c0001207084607241c00210301141c0003c0d00e040380211b11401801ca0040504003807 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 413594208 1250 413592958 413592967
    0x20a17030609130503180102070803030703060f08010c08070305061c0b06011205091b0112020409062c40050606030d05030f041401050a0605030607360b 67
    0x8400900840c4100825103208880b42ca4071100301032a280c01c0b507800740481c0c0040c01005080d4590b18100d540b4001d0503c125000700703071110401030950f4002e541a0b000309a46210402038840200d07881001020038070020005032806c03c401410144000340000101a41c07200015056605c2d005c0403400b20746050101c140c01c071130900d02903602d104103482260200d191000210b400300514011648154881c5000d046030f0301c4005507034400b02c0304580c04a81800f120b1010001080803d2000e04020f199603800810f01030f1901c0011200440890300c41c100400c1c10226500d0f56481c03101c800c43d0001420040114002c103441034508003c0f030768101c0004204220801560070180c4411800019401030313090314200d03268041050307900c000c040540d00200b0340510010b4800304881404075480ba000ea000c0345c9143c1e440140303c5003101c10440d00c04103143d680300c00a101c6420204a140d910001d58107100d05002d5400008034120000c1584a600282d200407846a03803003240800500106540b10b0000c1c1c45 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 413595458 1250 413594208 413594243
    0x90c0c060c020714191703160b041b080319021c05091306050a03150609050112030809070b040b070f06111e09090c0a090509240d02011e020a 62
    0x2a840e451041109064501c202c04101c1c5c58441668143c901c1e03084070140215203080740129950b4803001040c50340740404e000341100a84030003481e40880d8401c030740c403009510b080c0c50200000c502c9030001e10144507040381d0521000c9000000c88a4594906c91441040d5100c0d18080340703000d1091900300c4092900b1700007580000e401c24080d06034034504684402100c1c1b1466481e00031103000c5e03c101a8801d00c24401080030803901310191544446d40c9001207503540e00c41000f041550001c5c1d00251014540740341020070b15500014203a00030920074046c0c0800e40ca001d07043c62490180c0c2c003444900c03d00c001002010001c030032444a64035540040c0500101c400c0901400464000701041c1c040e8003104c035500c0d6010303100501115000003009003444840e40728130060868542014600c0001d003c3c524001203480c0c0e940038030040c45181030000740c0c00070103000130350680380103010201c0601a0241c3c1d0008801030782c21070031485111004030350823410710388181030072071501581010203000524000c0440e42c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 413596708 1250 413595458 413595463
    0x601110a0c060f1d03030901050706020c0d080108010b09040b150d0b0901020304050f0a03050a0503130204060312090806010b09060c03130b191b060e0a06050901140702031201090c0c060c02 83
    0xc829815154020084c50b082c0301028941103506856a06070410020180f030381d801140035281d13075400382d8401070812049a000318a0118110313848400300e00311400400841009004070b4100c1c1c00c003613880d240d07107041664800d000c42c0800b80107900a1000000100b0321611044c00c1c02050a8002814040c40c0c100f0620300d82c000d50050b03c003910300340100c4128044c40000050914402681aa50b040c03804115150403507054101420982031400000b40e40c0000da0750754010a0003840c05041c4410003a1601100613001e40150741c4107554503004840101301c400a00c8085e90141034040c3c0f2410303074821001500606601ca1036010711120060407002054000d04000a03240440b02126030521072401c5403820303103140d10b450881c9020000c1446401000a8254000303401f110b0204003140c621031525500e80061791011200a81c950795940701a400e4002d0140e12143c121002d40051441c04a20b05c50501c1050f905001c0d88616507100c20b02d0040c0c95100d001c01455541c0c1080d41088842880c1c20003e4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 413597958 1250 413596708 413596727
    0x1051e030313030302060702030c0c04020a0318060b0915010203030103021509031504231009030302190315060903020d0311340602030405010c030809031b0a0b090102070b0601110a0c06 81
    0x11300502c80c0d84001803025000100701e80ea09070b1510b0041002e0a100010400a507110080110806460b801c0714162105e8a0318203001035071003020081406401c08041c4044943c00914002e1100050a040040d9907004000c40341504d4040d5101c65030074a40101805041c4601d81c40f00340c0501c035045840c0d8804103102d01d010302441c40303540c1014500031030554103007030414131081142c5680c01c44803041e801c2d02d03401d51081c1c400034401d040142c00e210f582180b02482140b404040408a509c0e122400038402070403e0003800380c040c0d03060180c0d0050542d000b00d42200400c0d50001c09228050200d110455020801c5903c59442d03000701e85100ca100f18000018492214a004001c07030020b5400b203101800841900d09880041c1c1d00c1e1012500a600c04951400c0060300c09951804100484400340310000004160300b60b07200014041600c2030301d007854a48038002c083d40401c0c0d10500c06040010002c040d96504940c091900031140540e108107541003000300140100200041c2e0b60004005420418a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 413599208 1250 413597958 413597963
    0x1f23040507060f0306050f0118180b010219050a030c0501110f1c090b06100e0a03080a0215150d14010c081e010b0415120c0909060b07020901051e03031303 68
    0xd0702c529560f000c0039800d95595000b00b6500c54828490700d03210b03510668604820711081c06215604540d104031100e03a51500100d00141c031525805440790a580402c90040c021540280f8030740032040310f0f1507258503100c41170380040412044c1754551742441800d40100014401400c1860360700c000018074034215074407100201200800c00b07030800012003018031401d60300c29040645202030b5500c2408000308540c0030780e030000a104602900c00a580c81e000e0000d07000d54400c4040c1d55487e418514003074502905074a01001c1512802c0400003400210401010b84001c140d854000641e59442e16000c01504002c1400ca03940c80e00d40001c43c1c8540c42400c041c0101c0e81140071065000310b01041004480003400b91402c103100401c001c0110303403240604c42c1d9110b1000d2825024001c0800d0003041a240491011000294407510600c000c810038411a0001c09054050900d42800d603800316150000512880f8440c42c054200f250b004c081a980450549000031b007626594036128034248142c01c041c2c00203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 413600458 1250 413599208 413599217
    0x5060901050909060105190801150602150112080703050d140f0c0412080901020a0209010914010902090120070506070507081005101517010801020315031f2304050706 73
    0x1d1141440104140030740100c0700502003682c01d080911030000104022407001c403102d00c00008800b0801e11403100310501c000950015145040c1000340b41c05041c846098891062000411400c5800c0c07100030322159000c81c1e850349030701032402c6c1138506004a05000d501c50782490311389030480039808103603842208500e0040e115529007180ca000b9a0040d8014408200d401c2400310000c140700001809241a051044034001c580e154040350000b0003c2e40042c1e0180e0302d48100b10070904c5120700d0b00d409804d0300300b0110f0a08007842c00090407044109424001290f4081c51000308850501c100c0c00034240142c9015501c03c16072818950307e0200b40714070724940c05000904010780c6039500810f4098030a1424112482d800c0541003100341c10702130940c4091008464091410030094920380d802000943c0005032245884005007a980034941105c48c404c0d0030036503121404040032450994030302c4000400041000d8420180034401c80e2030032505207010104c90401c030402c0000075142054568560b903 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 413601708 1250 413600458 413600461
    0x140609010c02010c020d050d060f0e0f160e04050403020c0a080307021e0f1005070215030f0f09060a15080109120f0e031906090605250519030c090b0a03050609 70
    0x100b00d08a07885030031a42c00507000b034181d103c0c078640304001801c1c0d4040f14800c00914950b4400c000451041a9030003500c041c2c610000f0000b040758807030311250b40304106010800303440b10352120051001c000130384441e02c65543e950108051620070461022a45409000c940f515031f190440c5640d00e80010300128455428a004155100000d0429440c0484003401c41121150303410104a15807544130307040703030400400348004005655030f00f030086c010440c90390034196213042c50075050030f83c1c09005050402c070020740d905100001c82c000980946c4880006ca0001e0f16040ca44170401c480d40e02540034804960800d82c1203428428bc4170212808a20141c40b00540510407074003d8036140111980365a041d000506099400c494000f40c4083c3d00b07105103030000e41c4912654500e02103800030380740004050005107031080e0450f0465545d0402d1303803407414401d003815042c81d200440c042441c80301e0410507840b0300344040d85900640b500b00183c5603002c2e02c0b43e1900f0300c4030300040084c4030481c0c0c03162240103c00f0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 413602958 1250 413601708 413601731
    0x804030c0f0c26030a111c05041503090f1401111b06090d0903020d0807020612060405150901030f02010903150c030f0603020d020f010905060d0e010509010c0801031101050714060901 80
    0x3100c6444102c0f00000f84d07003405440b8005440e01c0740081c1c0e0800b201d008418411718542211002c0301c078007080a8031800d450710304000b1201100840701300c0702401c1c5403034400700b40041010350400320042c40d0b0103d40c400380b0742c80c1c50003140d001d0605086507034568800800c612406c0d20800d12815007510b1343e4030482d81a41c0e242c040c956070b01c040000c6000d0204808440500241c201000342031491030003030fa060761600d400e69002ca001ca03400056018140580c900502c2041d180034018113820500900c510302c0100f10000000d0310401042c0720081000c0c5600d11448116400341810710000c6030094103942003a28001000b8000c0c240c1c43c042c44000034a04a1580e41d010038034814403080e281c020b005241042415824480307040805407111f8180a110600028940d940340700a108548a0000128004c01144020ba0035158040e1250201c0d03410511072100c03940d886204c0c241100e801c40041d0f441645030b01d005035007078822090007a181070b030303c2242d1400040380026103d0081c14100003c011098262 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 413604208 1250 413602958 413603009
    0x827060a030e280b070203160f0201030c020105070518031903110705031f0b011101060f03051b03190305070c030309062304090207020102011b020703150204080d0804030c0f0c 77
    0x9a41c400001c03c1075002c54000314040328034082c0d0180c001d004030380c075049a90954407004000707030130119610000701c1d80c102c0465a140c06142604000b90000781310700c0c05c0160002d071581c0900f070251a060003100740d031014950390030080d0420603d00030048003510b00d19800c0040c21002c0c1d01d1400c0e4101c1c42403e0300001d03a804c0020782c1200400c0b0396061440d00c008445a210702404404950504000084440c54850701082c4190002044142c2110074003910754a0190709004126010354010700d49444095066203000c00c0c1074030180c501c1d12480c030840d49180307070580c1c4a0068050181080218a001000b055084855401965915210b4082c08410409059030702022140c44120800f800c0c4010003404140c1d8001d00b4085105000118038002020154403d00c4070f82c804050042c1d005120030400d00082189045113a480840254034050070083d10342d6440b44040400c5c82082503e000040c2410702c202401050741e41d0040c00c8141c4500607013803d802c0480b9502407a40d2060303104941308400c00c4d12 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 413605458 1250 413604208 413604253
    0x40819050703053c030a150f0506130906030b0402090a0c0e0405190e070501080c0c030328020d0903030b03070302010903170408030a02010603110a030827060a030e 72
    0x1690b5041c9070400300a40c43c4038488800c460400319900c50b5086111801c0d01004c0e1303a070032803120440c0c00e869180800d05c1100740c458071241c0440c0614060003d00c0700061a00744102510010358895551b010020142c100300c0c412580605411880c002001c010401c8040c040c50085008030744603101030301d64910807421683c126440340045248400c1c03a03007c40c01d02d50001c603801f5070248009205403040e220128241d41c0d0740b01c05480c0b00d07002040c05021560300300100c070350000d140060960404100322443d55880c40301406150b0700d103a12001d59050f80036120b5000c0320752803611000b5520346080409090242507405411401f02382003101c02103050034001562807c8035016511074100500d5901c0311a45900c0d9007410159101d010040869080c408000404445002b80e0001411a00d1414260140c0365001001446a40620b500b08041030640050303e80709007007600314090041e40e1204440c04c900c00c030a01550081400f0548040054150b8403002c1c030a04c05205485564580a1381c0240188a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 413606708 1250 413605458 413605463
    0xb07030207090605300f0d030203060301152303030706110a080106030b0a06051b0105090a0c12030504140415060509040609020910050d0902150301051e0604150c06050408190507 78
    0x12025841500074005912660550803a038192070074521300c0302289050203001403020011a07000000e012f02d03030400f4803540c1309030514030420f0301456003085480f501c22400e40041000d18640382e451040c07241d5050044905155005c10704100b030ba2410800d902c3c042e0044038101c0007090340c140000901c60b00900409000035001000d03036400c40c1c104101500ca64204442c80e2254191111070b07035015040034860380d801100080001c1c52880303d0b038a071445400c02260003422400f106d0105840009230448141d5081c1d410108010548001010216004100303420001146062041001a40d240c202d80108021002544c0c2882060344603c0520160310410302c0c0281c1040c4103044065450744500c0c0540302007450b454000c0740148039a000614111a42c4040034210300000004010341d00d030030070310300304030840624132148411300bd44c0000c0c070240039501c030703401d8408032917080e0b4641d0520504541d0041e03175010400308610708050400e084250800d003040002007440c264088440340c060020b88801ca60b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 413607958 1250 413606708 413606749
    0x306310605041b08120703020a0f0c05090a020a090303080c13060f1d0a1412030301060f030e06040c06050927010501090b030910091502120402010806040c050306090405070b07030207090605 83
    0x40d03050120305d00758001807081d011800f440e0040720024004411070400d090040103a800c0aa06040802c051648081c00080c5c40c0d0b803040040120442c0c001413a00d00b00c0343c2508010708036641388980c0f40c020f40f246e12a91111801c4511021500a401c4640004a40f030b9542c0c0e560307914140c40220b411248048000e00754041500e10342080140341d200b180302c002ca903018040c2240c5010680e9102d185400c00e80054012404164003130700b0042e4076100f61505070309000014051790910780c41c0d44d401580c003400b45904121002503800405c3d1a1601d156140326641071207021070584552800203800028040c039400141041400900c2107060342c1500c0c0280c41c800c024121f02129411104001c2100346412107c10070f05804c1d10459191a01c050494a80d040e208030074145014400144441c0d4000c04041c400c61500b000342c1422580300007a00da01030019506001d143d1220b0401c1441c2c40ca5a500070001100001041030805501081400440340d600d002401074603154800c101d01500440441100c03070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 413609208 1250 413607958 413607973
    0x1903150803070807080c07050a0e04030e151204023c04050405070e331918050408090901080307141f18050d05070c0e0103020306310605041b08 63
    0x243d181c002171a1b0400000210f80c1155644c401007045600c8641c8020f0311100124204002e06800400c1895403035812a1034681c640e5209000494178000c440c8901c604a01510004046454034080d101c2494500102c3c074036601201c200c000180d0098200c450300c0551400c004554030b0603e405054015940807018102c03643c00c001c41200c941c50f00138240e00a8001d441590860a415000b09043c013074044620300030201d081e501480400005080c00036510030304420308005290080d0103e204107100000041459140e6042298190098551841e400202c0500014030203900000038654184a943c8030b0380b203803107039501e0940c548030504a4600174013030b070700c244200e80002a807105008520b0340d0705c1101c160310319490300303442c08010b54419404104e00007481428042c007224508001c0000c2c0c00c0303602c00c07076045a010940311440503000c0300c02414682607030400040d01840568070001047d03070745041101e080c200035010344419031741034990740e900005e1a04001881202c0505903510a002803400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 413610458 1250 413609208 413609213
    0x303040c05100507020a0906330c080705011b08150901060c2909070503030f0d051b070b040c0e16052101030614060d0b0105060f1903150803070807 65
    0x2d030101d20118070400c07004001280c0143d89000404c000742145c4440001c446003000a14a075820308907003d00c0b607000d07060305d0004000524002119082e5854584828806420b1814918038010090001d01075401d14508841101c840700c1001385d450050764a00f54991078800c0b840c0d1641c020070b11002d80114103180140311480c000c00c00b90165500c9076000301000c1003e13107440d098145040003501c003414018018000f020404100140c0036000072000b87d45802c0e80e04440500e2403091a4007456196100c0000801e0345290103640c1080c0d000000301c20742d84034503074039000c520f1040c1198102c42584480f0f0000c40c901a058400300d1107101001c450414614003100306441a41180c00300308003810718080f0f0070054024031503405008600c1813a0100d40202e12900d84c40c00b480c00204100e0048003030a003184003052400701681d044501c140e4905950301900c1c19008654403841e20072900001091011094440c0e141d0b02c01d0013480c071001b03030703600b00700303454403411a124451120050403400003403015002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 413611708 1250 413610458 413610469
    0x4030f11010c06020a0c120315050405100b1908010f08192a030c0e06010f0e01030906020711040b0108010803070b060a1509060801081609020a0315090b0a05030303040c05 75
    0xc0105051000e103001c196600c01050742d1040e4448000101c16404a40802840c003091012405160074140408999051514000c4141e4030507144200d1f11030021400c400d8501d403561001d444225505a82c0d440303614501c04d0034019541030400094007a0000184413170034011002d080d0760391040038100810800780100000c011051059480c8507200001d2641c0030100742414a090032020090144031780f4505040c000581240d0050100e61520000c0003926a80f1201c030000580f6907050001c040c480b0702c0d004074004c04c0b01600003401c440c8000f400a06105484250310540082264188410000c850044071885001e21030801558014801c02700020f6201c40b41079071040000d0710b10708900790342d0b40e0b00504906c00c906c003601c04181114014000d50354050545c601403c98400280b10b6540018a80040c03d40b1911550504603408202c001d0700b50311030340184002c03420b00300302c0d42c04044e15215071400410888610030b00c600009040005d46082c044182c900c100d8220404114240c502804c1c4803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 413612958 1250 413611708 413611733
    0x9060105240310090c0e03120c060105100c12120b030114010b0d0e0615031509030d020304030e04151503141503100207060b01030c050313150b0a181104030f 69
    0x41c1c0300c02c6008004120003030716105102a171200da698007000141c181c000c3c0b50408810004c01c294640041240d051458000a00f6904666003078860820038288000c0c111030f40030007948002d02040800141d6502079520500b80400990388603030070800c0c0e801c0742d4101803c036807040100c2c000000d45a0010400000d4840c082c00446000c003901140440300020b02908040e030440d141c000021000701050114102000700717003141c950440c601c1510b410b1400354142d0768001c0301c0c0118140ca03000000581054070408207100d040201034000c3c00b049040c0c0c3c0d1414400d214a0103800d080c61003061410680f03030720034042c014034840c0444103014107884521280001d05145404a42c140c4036407414440840038038801007812a00828000035110380100c0014150780011601c0340c04c100040c010b001500d58400821b04c01c2c10b901c0542d0060601301000240040c040400d445640300c10761000010302240942000e60400700c0c542d5040019405a6442141c580a10701003d05084031440044000450032140d82 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 413614208 1250 413612958 413612971
    0x112109060904020d0914030412060c110a0f021314040f031e111002090105090f0a0f0305070e090109030906080916030807120e060909060d12020303090601052403 71
    0x300d1030010003601040c02d030303800a03441c0302d092640c8403281014000701c1526411480341c1400954074047c43e100c00d030b04c510305503e48090a00742d1784500ca400142d00691110040b0060300080d40d142c044c40d0706200c5800c00030b01400340d0040f52070420704400d5001c075200b0700e00705402001c1035510a844513100c140c0c2001d4802c00131010311090072040c881c070021101d500c02c034040055540c01c0546042150a80c180380d01c8200008250340148000f90950785c02409842c040720050714145010341c10140050f2940c1c89951024280c0e8011940200c00e024012410000741c130024184011141c9030750084508079440040b025000600b80c0005100585c407400102e40c0060078001144c480d0803580000803000800e0740c1c01168501000074190381000317484400e1010400c0306041c00100c0e08013000100f819807080d80d1083d8800d00c103a50015a159447c40009000c0a8100c416051100003124000e0f42d030b90f20540740d1070014460040001414540028004110b0500e1100c0f101c2581c0304c9008803c064101030042d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 413615458 1250 413614208 413614219
    0xa031401060b16030e01050f0a080a09060e0f01060e0f16090b0f09010e0f0a0902070606151808030a05072d06021e130b03041401020d0606112109 64
    0x9008040d08003904080c0701d1541201043c1c4003500d0050807640c0c42c20f03052414000c040c440d15914004100030b440320326941c0d040254550b0798140414000b0a4025401441d0714074003200310325000700c0000c43c6443c1c14229002041125100c4440c01c030010f404407008404101d880000680221a44040d00b6032100300d0704008101a840c0e2b203001c5c7d45904080a10b174182da074082030b07210081d0b0b445401c2c5008000159000302d450f50010011540c81c01c00d41c000d0201c40350f00001c10f02d0401002d588104014840d00d8424001d240135200300428a5195000c000d10115194002040d900d4002c0121102c090b85c0342c880602e480926034405101c810141c0b400011069248029904035071b8214008040511070000180d4a61821301c213040741c08101c40180c2d9500a050140b201028902504082580d49441829482e0303500c51805110100c42e803040c80203554004600d00b221114580c002c3d105030b81c116111440c00c00321810f08103681e5007112648a5044d440b2812040c0034005090040205900103041d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 413616708 1250 413615458 413615471
    0x914010501030f061d0d03110408070b0409140c03060f01140a0f0201060801060b0702041a0a0b030709050904050312041e050304080106092009011b051c0e0a031401 72
    0x1400c54009920545843c0b140c610f101041000c18418000810401442e030345050400e094004d0f83c411070001c0c04024950307030b08078032024400c040e429240200040c0e01240c0c01262140e032041c05540083c0700d184a06030410076a00c110112840c400c41c070a0151405d035905540c3d984080000c12401c03078074064140040340c06442c096103001ca0050a54010b01c0d11030394000c0061203070003401c5904550100748603900d0300b402403080b080c240c012280c00b0390301210041039408091a6660601c58602c3e015030340308020200c0040c81400110266100350380319214411855921010700c8010070049130001d1040c0c0082020b40c00010360219040d4101d40280c201413a1001040304071a400c00c040c40094a4560000c241003220f403c090044402800402ca018042202961901d06c1001d00ba05014050203a000c1641800c070303441801154021840000125400403007070410036122512040c0551454480790440c500c0c0c640698885200450b001d000c01c40c02c149035403180510805049460a1035549031781 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 413617958 1250 413616708 413616743
    0x50a08091503040b16020c0307260d1709010510050409030e03100204031b0806070f02030c070312080a1a0d080d0e0106050a080109051f0e0a030905011701050904020409 74
    0x40142d0b20840c41850004004c2c00c00c0b007080c1814405001c02d000456000d9180203010351000301e9003404a52600140004007426086001c3c2c00101c101031818081c03055041e10600c0c0c41e440b03402d031258040d0103140840107455018985003614400c484070010f03008008020001c50400340e010108540c06403404040131050400041c3c10800d4081d014204690003003800d00a0002e035421005120485069051209150444560f142d0344002d20000500c445010450003503030080c070440702a00d90020544100b55240d2920440b41124110b1141c0040c03000c10016280c05810720622041e0f0042c2c20320088103109800c108405040c0101080f100084103114800401750907010b91042141000004102e007402d010500c000145c080e4000d00d0329a042a800202041004c41c18140e00c4084030001400340d500d91021174060110f010319181c86124054a5100349a4490820810344400f641d6900c8642e41030458228028800e0143c182c1c8050f020000c200180b81c10307444074500900c5800b00c000360310702e440c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 413619208 1250 413617958 413617999
    0x9060e03060411040b040906050a0e010203010510050703170702011a06070f060f090b0f0615070c090b06040302060a020c09060406050312071103060f0702010536100c05090a0e0103050a0809 83
    0x10707d02121142d0f2100140200324003c0d001c1d41d031140b6002e0000714219850040011a6080400200720034020001042c006040c41a9411a000c02040d0100c42803410724043c000c0c005c0001042c406241c0d41c0b58543d1152a1a00b5412244002d4024200341c0e400d20403503d030080103007002d2040700e42e0b0642e1010140c0000d0384000200b40b2a1091419480203882d005051005010320964401080041044454000394161440d441910200c0c00700003203054452000c143c1030310858002a51155010070b1a070702060340001d030b02c0c1e100d81003034801c03519a484890503c0140c0e2401c0c003a0a5150700122910805200c80801421001c1d003e005241010003885000c40d00700481030340c4c44841c4804a504000e400358090049503044410302c100d4421850308078000c0d60b40c404099a071004070441040c5141e80c11a0100a0b101c0861030ba01c900b040b02501300d45019055600c080c0400b4000d81e01c5480c00502c0044800c49d0504a030740040c05000a0300301950344401c00e038043d2070142d51120712004c0103100b01c400c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 413620458 1250 413619208 413619221
    0x62b050106030224040b07030c06050c07050d08060102101509020c030a090e130b090a08030123040608070e3103031515050f0c0a03020d09060e03060411040b04 70
    0x5400014201d070450052104072480c611441252134044000f6140100f240d408980c12a808030b06500d8407103400d46001c4610204c180d0001d4610b0381000f052240400c1580018060b0354407800441b0424584103900b031b9000c0c441103502c1c1c1e0140c3c206068080c0190016006008011401103d03040545d450388010400c980000180c91006c5d4408110714046617002880c490103481120f5001000b4030b0700c4550540c0c0c904803101c005061243d101d000c07820314039040040c03001165200104035120341e1981110107044d503c0c050300071744140c11480c1034015800c052150000f51200c0c03a000e401013078184100c0c07030841240500260100081d0250440140400064101d004006508000750211075810300605030b880000988241c502c42c0d1070f04100846c3d05105071f2480e144141004e81d103c0d803005030801c01c103002d00d00d0406c001d03024404840c0c04050b400300d000702100305240c581c200003a0700d9400465098810b04600b0781c050b0f0000c40804e02041410a11444000b0004c5c400b0a102d6001c0700400c00340da00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 413621708 1250 413620458 413620463
    0x10605030f010f05060d020a0e13020c07050d0c0510021608060613021204030e010903020a14010f0203180d0c261e03090d0203010207020a060206041b030308062b 71
    0x1000320a02403801806400140141091140420301c1c0c0d0511000901d14464600c500a0255001804004850113038031551841e000040103500142c28882540000c0c0d1b00840114220740100840454135140c150701060219400942c100040c0c4c0c01c100502801c02041741043c0b00f03501c40c0950300d400c4840b131104202e01404500018181c80c1c108401805400da040261009680340103021142810f01c0c080304235580300e5010f01e0501e410350503240060314000d10035003000c0c1d080441442c001c02c00230021040d02c4003e55080c0d03140100840c81340300c102d03180d016000ca000092640485000000c0c035110001d640c50501980814200c0c075070700c0300307400411f00b129041c040c96840018a000c0800e13800b40903102e0920383d4030315801200c2e50310084107502c91040445043c419100c1800610964400350f0588104c40d40c00340c01c2c45501c035220b440c065610324040700d0031a4103200500042c0b050345801201041260781c90341300c500f4543c071000d0401c59070b150a15035801056403d5140010b04c02c140782420b03101e060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 413622958 1250 413621708 413621717
    0x4060e0d0606081b030106050108190f0608010603050a12090e18101407021501081e2131030605070c051c170105150f0c0718050f0f070507030311030106 67
    0x61307070305080c542558810750110f81802410400c000300180000781c0500c2e418064000000c039074031a0300300303e0014110340e0031003407056203803003404020020001051181c0c40d01514110218003d40035003200e400c8558000c00000030441c0b00070840f5006d2421aa0070450010300a94102d074040559580c2101c0e84014640c004d144110144044d04d40c041c495140c01c04d09002c42d02500d9810402404c3c0d550f9030b0001c03070103000c81182c4480c20034810213116100080f00c0d099002e450880d00361641c0d0036940c00140104101180d0540071513440c2241d04480300d051945104269209880d58460800801c1c0040c2440103010103103442800003076041c0040c080d01089110211808480d6400c0109004540001d0304a00c0351020014030480e0782b9000440203011200c1307040b60341e40009405004403070156032440200ba00c24540042031812012401c21015640f90b5410082981c071203105080c0c00a082c2d501c0c020106498001c280708600c500b0040c4140c60207030030003003440380340b1050820039680241d01007400035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 413624208 1250 413622958 413623003
    0x130602030a0902040c1d12030d2a1706010c0614070207080c09060a051c14010c1101091106030615030a020c0c0a06120f0e1006170304060e0d060608 65
    0x14070b09441204441c1c0c4140c80c2800c84211003102c1c0039440f13241b56252030320510b10301400d07404076041001100d440708420320082c400e00b54a0203605c8540780054110628444017001c41e001740754802c4801c0036034404c0e01030b08061076484000040d1030f8601c4103007041d1402a119004407106090f01ca110300c0c066000c0d41e005015a501c5d000c2d845040c00051802d045c4192040400d0003515510000c200c01511003c58036000c604100c103c60300c0c0c02c81c20414004111010110f1442c005c80d20650000302c0c4a0707040e46800f040221040806402c1302d1040c000100512141c50702680c090600b079010b99070260000d0003ca02d048004540500290802c032035200e10340750005030500220000303002e01910100241d8201d03800900b0312401070048131003c1e41d61a44a59140300d020f4450180c1d40110000d81e0a840c261070381030300c02d18212005089203000c1c60015141c00d01100c0c80312400002100c040307524035034038410001c001c0f20130050010b44d042000d840080c1ca801010442100a000e121240a036098440c0b100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 413625458 1250 413624208 413624213
    0xe0316020f0d1106090f090403110606090c0d05040203010f0e0a020a0b091e1c080a03060e060d02010e060702060f031f0b07080c0f061306050603190308130602030a09 73
    0x480001c5101d40c041c0340d04a811000082c030700c070400040c4035803c40d843e60b00c41d40100c020911030080c8400301980240d61600b400706050300300d100904a9103510041c1d4040b81d8841041c040076007800d9401040700c080c1040814a406441d034400c07508a0300c003c00205110b0a0003803d101520b41910b4100e03626001019000210f25083c000c2e10300902d80059481e081c009031f8000a100204d1100d200c110290f22842c2d0401181d03104240b4104980203184030100c1c00a45091421031500f101d5500c0e00840d203041b1022907031803002c080c0c191164000074401c10809003e640111080c42444000641010041c045000107950b41c3e00500741c4144d2a40c0440d490b0314014180d8034101c4000721084201640844d001e02550040d0000c1394600f0b50000140303503a803160300340034614141020aa42c840b0b40100300030700c481c0300b01d050f0001b12030a029200a0001ea200e80d020940c84980c040c464400081c03540a8150000e8000e00300b407a402241e0b684080e1500c2c1e09a15004180ea02c00c0354a6000d0650b510404005c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 413626708 1250 413625458 413625469
    0x2030916120305030c0307050d020a17090109200a0308030f0415050702030301120515070201020309010605090603060115020f0f07030201030c03020319020d06030512070c170706080a0e031602 84
    0x50511a00d140500c1c886034034090094807028000c60342c80c400000009000f42d00410446450341d0b40c12008640d28540608000e20401568100210189840c0c0c0442c5540405000b0709040030b4001568038000030600351810b450034215161203410010000000011030031220145200380782d80c3e03802c00d0852500d440d01c2c070708540b00041c204000629100c18085081e40c0003056905403001d10103000c001407502d04080f8900500d0036501055220401d04108003150306401540c007800104000380a1140c9640070890044011110f480c3c00d6401030004000a242d5204132103003d20160042d00e40315000d8044c401d08200100426642c2503001260800440d607040c807424034498042d1408500b1810311340415482145040c0b00c081003541c011650345044407065201c1002554060116950012103081d040010340155905403022400c0000008262550051817042c0c070b50301a0280281c5410308009891303c480107455801682d640d510004040b00c010002400412481e480403400510584100302c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 413627958 1250 413626708 413626753
    0x50112031701030506011e03080711120309030c0603131b150305070c02100e061b0601140d0b0403030b1003240b09060d0906050408070309060503060d121101020309 72
    0xc0c5540d101c1c004001040e4042003490655a08188000d614111150910500d0841d508041c000c030304001a1082041140744e248038101006441c1c5070b00b80454015415100d010390600c03c1c3d05038104200700402d501d4080025a88030500524012050f100d41d1a207a54060350203500c40030811043d8024004d1580080c62101e8165551400f84154681502d00500f010780000000703000c3c10900d440036948a005500c42841e8000140c40b090301c45120800c4102c1841c2e0b030541c4199507002e20b60000c10404c100005026501c00040c08019207000103640360842508024410340070503907200301704070050f61400426503c900c5150f60100d0314100545480741c0d98245802821122000b040f802c0020410000c2a5048200122400c50f10350b5008560080a0000401c00803d080d207494200000c02001a002e0907445000b81d44401640d41c070340805a0301440150380d2a58841d00314044000040c5105080340310070030309446c1c044507050b0348030301a50984c0c00941341c03401c0640000040100e07081203622001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 413629208 1250 413627958 413627987
    0x7260a050d03110301120b04020a0b03150f030d02060403080915070e3d0e060406170c03040201091503021e04090b0f0a0303050a02071805010302010807081605031905011203 76
    0x6914552400d441c10703c21446c000e82c020f04c600030140000d4250365418107000010040c0180307060756854021801c00c1d04100d00007006208865924002600d401c0020f001781140389250004c00d6940c9540c0c0b41030704c015400800d82004c92145c10b000a903403180e40740304107016143c15192042e42025020400040340800c886101c2d40141d00e140840f40c600400c0d0328a44507450409882d0029600284c0848a03890522803450300b00fa8001000100306501411100d80b07484940b5125080d602c0d001d800805520041d5000b90004420b0791081c00501c80800354800360b5444c07810014a400707442c000c110210500c4035084001074a01007810440e4091901445404c2c1f60b04a445104008007140000c2c2c5214031400058100f10000c82c01030f041c540204a181c018142030b9040c02800c1c0342210150001d090240400c0740043c0e515408240031600601d00386006c0c031211010140f11107244d80044919400013000c003940c03410808141c1d80386a41c0e07803203114060207110f56003415805660078050243c01ea00c1c1040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 413630458 1250 413629208 413629241
    0xa1d070e04050411090c090301060b0c071703190e090f060909010c021b03071e060e0d02010f0c0813090504060509030708030703050c0904020d020c070b090307260a050d03 75
    0x4100024020404840041d001200c55174126107800402c29a580500d500c0d0396010b600c0d090000c40c0e1150307d81d010303007040c0c100e44007110b400c0e40c1c4515a002842581c1d109440c83c640c4244002040440200f071484050007041c42d00340d46011404002801f80b200549250401c40d602c60280b041c1814603440456000c1c540c4002803180812540e0029980d01c000403104c02030006e55140c0540656040c032001c070007040700c40e40c2c8002c6080d40000340c111104443c4150380205084408120103828102c1034882d460790141c5132070122402e1400141c0701002c0c00e000451304408100400e240c05d003203a90f2404c001e0a207a540c0082c40745003920b808400c565018004010f981d005000e150009403100301100e40c4142903140c0400c1c0754450030310001c0507014064900758098008501041d20380c4081d409003806c0d041600488412507500e0200c0c92240c890a02c00e20f4050708000e00600120b00b8107502d0050b210101c1a15401640c10000e040d41030104a0f41c007140d054100b604c640701e0707441c3d05001d200c0f054602c0180 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 413631708 1250 413630458 413630461
    0x20f12190e03040501081e190510060e01051e0f0c011104030206041707030803161d03100c0c0501020c070f0603141909060603050f070b030103080301140a1d070e0405 73
    0xe55902a6104e0705040184480009440315003580e10107040701c141600f80d0041d8140103143e0000340c121001d1701d5407641c0c6440001072a200300c91041804036081601c4458515048500444460340401c1682102c01044e040011108070205e000b031002800391402162584440d800540c2500d00f01e9040d041c2842c000e220620141e604c8038121400c4585056091142e011403030041c0307003044200c0e40040c01407400401040070650f003501069400d0402569554032103003031141042c1046140c1200503801d603110030030061324100d4079804403241c00c81c0c5003070189000d0310950354517003640c1c00100c0c041035a8200b660100442d00e40c070840080900b416080038054400000711001c3c0300035004088060700708601552501c59569035200350700c1d20740c10480a014694403400c0c15942c62405010020052162000004806025030305980c16660711248030761650b482c201001500a881c8440142e1000340729000044000340d45019504031030504188160350f18242e5005030100c13281c038102602440c03d010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 413632958 1250 413631708 413631731
    0xf060c0301060509030a06110d0c2c01030b0a18050c0c1213030f0f0c06140909040203030f13080d0f020604032111090316030c06050d020f1219 63
    0x2000e49054030424940180c0314141000080d03e403070512400504100c0c500b001903100489030034002d00c00401c03540424080e0410042003110040c000700309240c00b80700c1604102d4044041e414240141240514021511601c42000111480e030154404902040c1000298500909071301400e5031040b0007900007400c0594040807152100308007190f011517840e001a01034655020703c1100d001640c1c101103450f01400452070417102d0318ec40b1741001d80e9203a0718044000b8505101c0c101209140705000b0070b2030b0400410006014540c00007500481c0d16000c24800c440f0030350002e10107801700745071085541402c3c80c0390000d03050500081400401c10821f13211001078a240d00015041d4019901d45000c070328800099020100c51850006924405400c2840640090030310b03c001c8e100c0b56608074107860101c404008002c04224030b501c03008024041341c101c200512801800589080070703010724094901a0044c0f00c00003583e010303404104240c107a000c1880450040404601c0180d00f90030400c0122080f1007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 413634208 1250 413632958 413632981
    0x80c010c1e031b050a120501120213060b040b0904060503010e060a0b032407091e0303200604031d09161b170d1b23040b04090c02150403050c0f06 64
    0x8880c4442440800254408507510406e400c09500540b60030401c800e50f1180b0000000301c2000105178460104c0d51695000701e0328500c40c0c1801c0310b008055140c50140b41910345146078200040c400d42c410340c1c50034000303519102800b4a550700b90003540035020618020314150110380c80064201d0290380142c0c04208610303001320510280c10081d0381d034610746544000c0111081c0f2159001198200a00003070a02c11a49080d1400b0542b0300c01d0321600c0703500e2035a1b095012581c03c003910584180e40081c010801080c014505800c2c00501c1034042c00c0310000c5030020400b801400e45081c010403e40c008080c040325030011005116100d0001082003001c096155074102054810b03060350f80c05e00000b44607030802c602d58000607035400e0b1201e080c144005600809012000403120606000c0e12a40740c00551003080c2c030440702a02c00c81440c0074101828104820014081e200d00e44040d445070040c40c00404880d0f4240713038403c0740309a40c0c40d80d580500b10a59400d140000c19040c3c51544403000340502201c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 413635458 1250 413634208 413634251
    0xf091302090c0a0804140f07080d020c010c0507050d0203150c0a11061005120a061d06160503150a08011506020c010903170702030307080409021305100e010804080c010c1e03 76
    0x7201e005191207001c0584241010340c0b2016145123032244000c005081080490041400291038080e91401248000107440401e01c080004186030000c0ba014001482c0403482104158009811a002c00f00d940e940700b401d81c5815508804044800b040c02540d895014015140102405000e02080d04001d40c103120717108201c0c01414030803451089a03d00442003000710b540101c2c0c20041c00e105503c2595564100000f01c0b244000850103001c0020750703030310000640c2a00903061a65001d15594500040090130b10403520710729807181d8444000540f000090080140c118604450800c9480c03030008040d00d01580300070514140034021305d00708040765401d0103c031540007241121656a010702e00c00a4254420400c0c002e014a0000c100822154036035409040040d00d0041c40a50300740c1c4460409c1140c00b01c03000aa40012203800e02180c3e1540309042c280d8001384151510340c109120014400d0941d002580c45800180c00c0741c0340d140c0d4001da0701d10800304207403580c1010445000e240300c0700141c41c4403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 413636708 1250 413635458 413635463
    0x6050c1002040e0406050a11070b01031e0503030a050901060b1b060a051b0306040b1008150409111002011b0c0209100f0506070c050a030f0605090c0a050f0f091302090c0a0804 77
    0x5031500081d00034016504140142303204100266941c5416190001c59a0000e00040d0744030f8501c10900042c050204600990807a0000c00450450303503240005009080020204605952607140018054401b50003a0031035602a8640000344006205a03d1400e40c0090601c41591309000074000c0141c803202c008986001030b10007466907170b84c403000810302801000100365046909168684250f5501c401c8003406440040749800c1039071721220411058a40400018000070300c411010741507440d00240340302455000780008181c80f0541c4044c00c0344a40303821314000218120203e0f100840c9803010480f60b00c40fa000c1c4000134240d00b01621103d03d000603002c0c15001c1c0000190340824003880303200e160005d002c01440300c2c00113a264030f01201d84046800d8115241402c1002151011101103203075129101c01812920a082c600780401c2580c003c101201e5800c005c40b244000015100c55040380c2c1f054140d1101c2801003901071050000120000b010300703c00c85020301034025202d03804254142c01c284c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 413637958 1250 413636708 413636711
    0x9010b040603200613080102120106020d050316110f030d0612050304140a030803040c170a0b1f030c152d121d0d20060604150f06050c1002040e0406 65
    0x1c3c0303c140491402c0c81461502e8400281da21000100e01105400500c0c50941c500308100059903168003c0c1e07921184a03401001244090001803081080341800d80f4001160b071a040c06076600e900191070801e800450001c8032904000764443c1012102c1c0141e0000b08100d030203d403020045e5448041c0c8a008a0280403071030600100c6d0020107944624401018507000042199a801c0901d0f001d05120404d204000115110f10389189000c41c001ca0810300054002504203026580c0e0107002c21742e0800901d0b80361a129030f0000c0440171801510302080501280d02c4082d2803262036503009400b000c5405900c41c07205403000b242c2c640c80000080008441011410071104100c0c42690000142625042e5840001700c4120041d884090004410021070074944610780c9500800c1300c040f1152100f808440403e6000401241880c10300d0361041c90807080c4414070b0781c080f90701d40f0514000c0c162158041e000040012500540c1d0480c18040c25140300d041560071880c091400c0a03407104510002d10180485 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 413639208 1250 413637958 413638013
    0x61008070b2b091104050c03040b0402040f0f0905120a021b062106010315080a0b04020a12151b14160501060b0c0705040608150414120309010b040603 66
    0x20030964403506800842c24203034100c0704040c00014000f0000a0390035070f00c040355402c81d42950305252081c0c0d4003480000d2220383c81d55589449513014444090000c9030070564a0058010120042c494240f01030b0403803d0205d2030701c50300c3c2049894080c1440c007045988004220703104080e078002a1090b5a100c0080d807000d02c00b062100010014012059a9070080511020400340f036429000c24034401c0400341c0b03040010020104091703120040074010f40c0b4940c0c2c00344444001040c07815914a5000b4802080601c0040e21015000350701e40c070740d02c022100344200358612b0b565000540142c5614100308141074041080a4000409041d601240c201c05114001a1840a0046220580200d82d005002030080d1a0f0ba490304d0491580030b9035110843e13026401c4041101d10301070041c1c0c030450714108002c0403440003007150070700e1040d00540100e55100084050703000d1110f050100340c0f107903030307882198546034546554283d0135140c1031408a4451894a42c007400020001a199070031006030f0700601d20354 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 413640458 1250 413639208 413639227
    0x30608030f2a1f05090c0604050418080a030902010206091c110a060501060f030c0503160e0a0e04050a0606090b030a060e0c03060a0e010e0607090302090a18030f02061008070b 77
    0x3840b4002d2001805000708140c0c010001c081102c1c09000c0c01e08403070308001d59601d424945442c1c0521a11080c0d00482c104820400b500d000d401c16051282c08d126008c0d03106030301d992000e0003a4004e104660109485498035029580c0504c0210f5121300504003501d104210705032a51440301707003508108280101d42c1c4a114902d142040750400d4240d00c043d0030001540c48010140c424142c0d41d40907030001c0c0c14a203441281c10302c158140d0307011310102c1c0c001c040c0c0c0710016841541c00300c210f00d55032900100c8000c400507219165114860003180500080e020741d10050070450261119500040602800d0411039101600e0000303040d44455041040012003c001440203824071031542c001c81c0e4907200314414040005115030181080003a44402041b10840745080f40f515828115903103001729110344020809414040b8078164080e4891000003554000301044141003100c0325810b0b0009020600307500720264042000c40c1d0000102c407582c0401c0c03460320500c560341d040a8001c0c2203400c00041a01c904 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 413641708 1250 413640458 413640517
    0xf18091d0303040f0c090606120b0f0a0b0d050a060501050a0f0201061a03103c0b03040803041202010e1018020a06120b0d02060d05040222090201030608030f 69
    0x545000410789540342058186440002130141d0260b62520042200050344035292182004440690b00e40c0741e1800114100000240040c840c1e26401103010301068200c3d96a818840004c0d00d40803070010b0b140d4603c10422000ca0394010f007801031062512070144131582c5c0183c00d0303503000704ac14a040512400941000c9014010036400042040400002030f0034215008005c1e5104005101c401044280d490b5800c0381d10014441d1801d900d84880c02c00051a41251904041c07a44080400e040701c40b5900c03801362803507601c122803d540803040030087c4070030800c50740518150185544001d01c80c1c0995100d04170b072030b840407040c200b84ca2640c50800e423042201504203c03800303540080c03541200a507030b144050216403203402003031310b100d1030000c80010504e0103620300405c03a60080c1a03a814440303003c01240003407101074401c0c2e900c1074200c80f02100c4c2c5102d171041005c141401140204495a00d440050141e50303840e08580c006170814031803002aa079004042d80c100412006454541640e40401010f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 413642958 1250 413641708 413641751
    0xc050a150e011b020609014b0f0c060905030f041404110306041d0a03020303090607020a0b0a05180d03020a0e0904150b06070f0602090922060b01020f010911010f1809 73
    0x4203d0010412045010766141c40008403203403c1960161305901052a802014a810340c4232021030700c84444070121350720505195549900c10400010b51803040d8135402e1079900f01191718500114001400d0240718000241d0390010390f13090324180b02507803440c05011440c1c00300400103402103a41f52100e6180780f4010380d81d8142030900d9000c1e9420300806040007501c0794812503245030f09114080104e0451440058190b54007900500c240c2c503983c035155040300190002524030040700c4e040042141c0c030340c4410b11942d5403484d601d450069980200000240030350300b040d02d0092180750600104804200e030001c1c03141100307042040018002c0c0a00000500e0360140d040c014100c451400081410407081d54028284004101c460030340980d60750b607400d826441d41d091545411300c60780b000c480005145402140c030340e001c1401600c0114411752600c40c2181c0340f2110581e02e450b611500b40489582140c4500d4038100180fa140c0460b144241840c1200c1d84035129402001d583c400324422800803810045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 413644208 1250 413642958 413642987
    0x20c0115080307031808030f0d0605120d090f06020601051017150f040506030a02011101110d0915020a050f030406060b0712030e1b010c0c050a150e011b02060901 71
    0x8110840d240c1c03980036502d412641d41240411700c010070800c0e452090110080880740d44400840c5020a00d0b08c4014132500800c5010100948660002c10642d5445d41ca40c1d0090421000404121540790001003031200603a012034071803002c9078401c1c003844d64042074403130540d40151036107044809e90744002c4941c55a001403a440180da00401d008040040810345109910300300c544c02d50100d82c540030001243c1080c4c2c1d546038160311003411b05006500584610354229220030000aa070590034501c0c44a660040d5000717501181c2e56111282001f8480081618108005804509090000030040d0052080c81e180403891500800002c04108031900a900a019804030003038850642d850803805000160702050302181c1002e0304039019100000b13102005e007034420761131421404010010360f407140b10f40c0015180200200c03004074461315803154480c0100754148551001e4460040300610991105904070f042180c031030072030030101c82c1840c000c41010340c04480450f80d48003481d005995241402086 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 413645458 1250 413644208 413644241
    0x9030d1b0b180f0c06030601030e07170a150c0801030f152307021204050f040902090411010809030a02030711121209190503030d090f0c142d04020c01 66
    0x8102041c26480450010440c8000032961042902c00b440d94441ca94031300d040382c10640030310005000703601c241c014a480b402d42030b040d00e0b105910390103081108055040326070760781c0e84514520f078108003102d04804910158000c003013000c10a800b4004002d4281840090a0754a602c1050b1040c401800680600c13100008030030080c0d1a0304484990381e590311110100c82d041e078044009422140045082100d4203c0850130510706400c10040180c05160142c0c1c050f08503a03106440d400580f680c0101c40e01582c0141c2150b03000382c3c1150001003079443c00a01301a4182c1080c42800d4100341c0020944560990200700c1100c14a580c10114031503100c3e40d060103440307200350001c84003603072802c1001b055041c60a50752201c062aa0346120245d5945ca80b10300343d0164402c0040a08041880d8171032040079101c2c1380034a0700394442e51540f290144245d00101d0308003d11841c003000d207182c528814a420740404c14801001d4545010500c07e4810303440d000c6020310f0b000213105000701400e50111651003928903a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 413646708 1250 413645458 413645461
    0x91c02030d06060c0c090203060f120f1506090606040e0c09040b03061612090c09050c0f0c060708060913060915140108100207120c0c030c031202011109030d1b0b 71
    0x10002c0912284c0c00b025181074003858004620440380e802100d11516024003602c10040900080c80308041d010f82423044580a4400e60070807405040c08071054503800d90100d8450307814414100440c54001500a80c0314803001c00040040002c2221040e91040c038090281382c0340c140034004200078180d03000381c042d814010a03080001598100040710700070103c560f5030301200001200701100b1aa0344a4000d00f41800046003080042056082268002800000e090405541141400441c0c000c2d03006c07051079401c00401c021103903a00150707603a40194100d40000076420400e00d1a6400c400c0700c030001c0c20a40d10740d2a00c106000216200007106044001c0801c100b84002d4001003a924013030207501c010340151061a84580c005000307446c603c9411a083e181c005030b905400b507428041c804c001311004040e501000002c40e07494040200114000c0441140a28140700021308482d0b00180d42d8072841d1040c4680b0204d070714000382d560340d0300342d160502414070000600a2114030001e07440007001803c4030350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 413647958 1250 413646708 413646719
    0x9010806070206010602060106020a080c0f032a120906130512010906050612030418060902070f03031508060a0c051b0703050f010c05032d0f01050a0b03091c02030d06 73
    0x10081d208100e55425540680d8031030f40201d8a80000384184001a4007412001c4003140c88640109490500324080712504017482c4815811904182d600801c8034201c18080c06a5040800c21a2102d894401c0600b104900c6c400c0c09507030900a41801a004640108907031110107640d641803406030400134004110000854175642c003030306500d181210800d050034042540c504108809000d582560307809541001e082c2404c40d03032929009071103212607e03290100002c1c208207520040900318002d4103940320311111401e01400b641c1400c001d07041c500108580810005002103180d80e00407082080104410a0144040360305d40140004031840d0000c036010100214400159181120311030001d81d04480c2918036102c0c22a1000325200003c03c1003000001c0300060510401911882040c031980e1030300001145401d96818215081d0400720941d0005000c82c0c641070710810001c100001281d4510f00e4207040c003a48842c00b103004a20b150070640000d0543c14024030075200c40c01d09404040002c0340e03548 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 413649208 1250 413647958 413647963
    0xb04140109020d15051005091906050310120c0501080c0f0c01091703040b060405060105070b0403080a18081204140a030e0108060108060d0f02040e0d020109050705040507080a020d0b090108 83
    0x71201c28220303500e4410310700309400e42006158100e0710003d26408440380c12060541d600d070f000c10302c140c1d8816040310101010280d07281d07209c4013500c00b030340c1c0d415100d00e0720840316402d15205411485803051503123882c8000800601c2c4100950f0300c00e1030420b08540700c41210841500030803489880308280418084d81400d415444821900d0207020f18801703000041034040e6580c40151030103091042c914000802c1400d05400c8950010010714105281400c143c803003c0303081006480440005d402c5005005041a1130300420484406541c030100b84440513076600c0c2094480d0800e501c0c50f01c25144002410b20440061410103025100c0550300940840d2600030901030f075250500e030201c1c4a01000c60f40c10f511503021284a094041e21000b003000b0b403501e400d119080405402c0340d12039180d40c0c050040a809021115034000c0359000400c120015140a0703092400540140d8080c925200800c48580d0b800b1601c56000006500c4c0180c3d01d070314802c2c400700a00039492a80741c104c954440000707441a0f00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 413650458 1250 413649208 413649217
    0x1b1c030f05070f0909110904090b0412050406090e0606160803040b130c0302131527022b062102040e010c020d0e06070c0e060102060c0a0207090b0414010902 69
    0x2080310412450b510200c090310660090710905000a10265042c002d0349001e030301069840d56101d6229050444810006003600c100000494600700704134144410001c0044103522042c00c54103000d1b00340b0b030602c0401450030401c1d214004204803030b18003048007504c400048440c3c40c4124408a14607080307174100b140840d40240c400322012060500000c1980b0031424070004030700e43c05009503003824515000c0150f0b051403041017000169440765100e100f0400f070811b0500030300108001c9841000d80c10300038900c1401e400c56115019004000075075198a003113520b8401d80307000340785c100020040c01140c6002420503821140f41140040401303051060a03880b600303507051085406011480100d00841c0c241c1c2d521000031000f40c0d0001c0c00d260001401612a00716040d801750003a410180d41c0d4032007015960540d4401188034a250b002c1c0320b000c0d68107120745640000c8480020b480e15040550003569013603244038040e180b41d41c60040110968542c5c210b40d284001000c0984420758403001c031a4000d520 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 413651708 1250 413650458 413650481
    0x20103150305010501150306050a06050c10090506060f03011b03110c0f03121509010513090606090504120f020c01080a0f0e0601230a21080f070302211b1c03 69
    0xe8046c00c00780d0501c203024413030545801400344010781c1d26100c025141504010b03820203142c010b69403601ca4802c040e20500341b500703003c0c5004010b036041c00d200f031000545000c20814081e034127000c0080d5004006c003002c14002c0310b480c60000b46001c42001241c1890290050702ca200d8010140000c400003c000003509102e0002c0c5000c240a441e048400d08000d19050a02c030340048140c80100014641000c800c0130444081601080602079076079840200d03007941e00700c104080e55480c00e000903c00442c9178001508145c1c24480480305407494060b560300c4112a0f1103041001c100002400708409401c903c0d0b0800748040c0c1072011880f00140c180d00e40c0400d0050000d10340d0014a011800c14070803018400f50680070707008001ca42d0a00c0301a00a056600c0f05081207550360904d000e000030074400040c210001d10801d215141c40031464000e04059002044a000c611820551360032a14054200d6030b010092002a60745011080065801e05941412000046880240405002c3c4d01604407070403850303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 413652958 1250 413651708 413651729
    0x18020d1a09010b0f01050922200c060705040308071415070201140708070f1209020907052101030b07080406090605070917010c05031906051e0414070516020103150305010501 76
    0x1340c03400e00440c4d5a00542c802e942d840f101c003c042240104460005101c8d2000184021525401e604003a509012a1201030030403040d002445699002d41801300303c2c2c000c0f07800d152840c03170640745071030300c8115010b40034024004000005c0c9040c0020010001800070200c4d482d0308401d81e150408009e40284484d88140c0031040325400001d103481c0c4940009440b41540d6110420355645813041242c001d089945984001591250703600056034809500501c00c90f034036650b5a554849403868070760140401211a514003401d0b000500c00600401d01081e480021441d02000540d40c40c204580034106290010700030358648001d1001e00c030740c06520041230f41c0d8050300034110806412a4a400c07112003026031000150240003242640701940c80d240b100304510000405d86544504c005a50b01c0c0304164001c480454660f00c510850a12340180043c00380b00e000041804e2410b8500075111b88288001014001c4903c99240d0441e802a03001c41020faa0f21080b0207407403074483c94040d009203002e010b001c2815 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 413654208 1250 413652958 413652979
    0x6020c0c031204140609090906010f0911300c0405030d08060d030c0219151412010314010e0307050a0303050108070f09111918080118020d1a09010b 65
    0x24240003a100001c00c10a07040c2c1d62070309141044400710040007050301a441542081102204c1e5a0341c080c0034050042d10018044d10b514000035003118007090b6116406440c01d0580100003004c0344020b8500c7d20003044041111040202c80d8030441d104290383ca040007042e002c0034000c40052210281080d54000c2d011a0381d0050580801c1d94201022652158003410009010300028800d50003500740c90b02c05800004240a90003085003201602c0e040840c418000b429080e0520350b0002c0400500380c002030300385140041828004100d2801400090310070349040d0391017200c0032400d41c44140180402429a0740b1514585401c0380c41d011142416400a03040000110304403102041940884200700381c4061103030320f030807401c10181c1011076038070b48640c40601070141c0014202c1000105442c1d107546407a481501a0005000052143c00480c00c40c0e240c4070842c841e400c18401080085501190407001d031202a28112016034400141118400c0240c011310036040301c150030a810b1041c0480320480c0300c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 413655458 1250 413654208 413654233
    0xf03060918151103010b0a0c05061f0e0405060f100803070f1b080a0b04030903021c030311090a0b0c0106080316120806011b03030905031b07050402030103210905040906020c 76
    0x1610800d0a4003c1d44100800040200c41440d50080a4404d8241030940c00c1407410384a26043c43e8046402c00c0c0361b031804000600030306084c08441009807041907400e032503508180c0c689642c5c4220050070310724003d044001040043d100c1031310000c02002980c0c102c0e5919456468408202540c2d0a011904031a450007203000c040c40c2e4285480a030754a4900401000545854004100740040c00c26000d004074641c2c04000344c2c0320400d0f9083e02580c0814495113000b0145001400ca0b039000311550203182d01404451030303659a499106080751a004001d40e02d500100354498010481c039400025a0300c400200303442299411079150a005000d00c414500e0030030051030546002c0ba048584e0f45c0000c841d83d40126000e00502c03111428540649400550303406540c2c0e88924640c408184113101407d625240c50760001c0c1004024007808d82904e05508652543e500c0c200502c8908003851412007110034036105003489503040e04020407000380144001107241c20598003d41c40113081c04547c1c007441c45014003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 413656708 1250 413655458 413655461
    0xc190911040b12130606122003250b030709180b0607020418051510060c050606010c030516060f060e040b010317040308030f060901060207150f0306091815 68
    0x100c0d121036191600d030100c001d0b1943c0340d1140090030450082440c070491800710f0100d11954014000010f60403280c07450608207100840c0000030401401d03110b114880015813000300307031081c600c100c8036100140440460404203e4042d03942141208141c0032040022059000040608403051a000c04c82c0c622844044402a00c8111442c1074010f10104030320703001414a6805850401c03a05101d915501016542c0c05051401c50002d0410ba0b00301d100502681564208401000b48114204a1010969651542e449000c0204103070f0502c440c2005100034140900200e0b1854030700700a00111000540c40d001000705182c401140c0101c1c50030303601088841d141c012081c015600300f180003003203038a107698054145034030711103242c0d03d40424000040082d51580c0030b580609407503600100c1910f0450140242e05905a00c00003c640c8440c2c0c041101c9071504c60303444520f8a4615090031030b104003907800d5010344110780c4034030503907407070b00340c14007031f070303540400104241a100310200945855451400b10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 413657958 1250 413656708 413656717
    0xa0c1e030b0105010c02060d05070207031103010209093c01030302010f05091009110307030803040506090c010f08060120030c1c09090b040f020c06040b0105220e0c190911 75
    0x6201c014540e005000d40e40c001c00c1504603043c4001c10140c9401041c46104099038016654080568006a002d104020032110101c14030002a402182003012100004c2c0c2030b0007000d813030380aa40114076081c9a450406202c1320925142d44c41e0305400c18074502d410022581c50911055005501c2c046403040d0942060190a02404440c030042a00785200080c080040920000032240c00320461b0310064a920140f11101c010b40c0038030707451034403890607080241c1003030b0740285202041e07002240070610030307a080b034124080103450b4074048500c1c2c3c0e02c51006a403441c1c230407a0962140030395280041000c00c00080149105140d1800740d8640024250100c09403146580700000450303803040c0309004207260382e405202c43c010b00402c00314004e04c416480004980c024055100c5030b41040c4100070600240034a81401014240d41c0740301509140d1017004050f0002100801905454080c042c81100c410840090480030052402403020440d22403038110b20440e20540d880d05040c070f401c1d540c0310401c10082c1d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 413659208 1250 413657958 413657963
    0x90a050306090709141b0a030e070b180604080307150f110711041109060f12070c050f03030103020f060d09050115061709060a180602130f270e030c0a0c1e03 69
    0x1a81446a20354411400d407c610b184108041d90386088000e00c0404121500c000d04500e8541503a4070b00301280c42c0d14251100d00900d0098030100410881c400707000045440040e00120b00b005080040254100600718905418104500301101c0f5030580c41c446c030042c02824030034005c08424440d200240003c0e1503074031008180851003031002903200c0c00c01d14028911511481502c6181c2515141104040e66040c3c1300100010308540315802004070400082c080c800060b03005600b958516030000d000321600c140044d002e00c401040422140380e540e08181c5206601c00001c1c01002c07501c801d42c0102c15110310880c80011494140c0119107100d010300700d80220306c904090310b1383e03a42d401c000d8400740902c00d844c0020310101c4940b0750041707040d503c050001803c51040380e00680e03141800d800300d030300c03200e0300320403035010b544200309600401420641a4107403010b403000c10300040380c068150070360180820160841c010760540c0300410081e180b08038191840000041c2039600800102d81d40d002060100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 413660458 1250 413659208 413659231
    0xb010e041a010f2c03150115050f04081b10030e030d0902180a02030103051c0203070b060a170304080609061924090f0c0e01020d05090a05030609070914 67
    0x22003006500c6101c14409003100c0d030a1036652040d590b8104452240031100426084080610300303d803078981031201b4000c40c0600394a00b40349504190219281245a01c403860a01170001002e1038850030502c1070710020850201511840c0380d10408481f45101b003580101c2c41011a1034074100560700a20800d544001da1300e0055041c03299501c824030042c21600d400381e1740481c0d81041224504402c00903280b20b18142100503840f54518a4101d01d01600c0e00c50a400c0034405130041e400541d400020740310b2690f000b81c004451601c8003004102c0046c0c41e500700002408a02051462105000004004a032210021600d05640b0006803a4440ea4191540d00550040324800c2c0c2440b0070f00d401134110b100c1081d50880300c0c014001070243e20041990300c02c7c054162202102a0001200e200d001c1380a5124102041b01d41301d0600000d403036407140b140000a0200209004e60380d61203100a080203000e001d02194400e05000010036520b08103441008403440c1020040007890344080e006a01a5130b09070b94 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 413661708 1250 413660458 413660501
    0x90705190918051e0601080a020d080d1d0102041a13230d030804020108060108101806050621010b040810020c010b0d0c080f0601031a180a060b010e04 66
    0x20440c002d42288500003503840e034550594008510f040c080f01007803084812a40c104052070300300041c1400016444602d860300107003042000342c1c50310300c6070f0480a0341c09411903036240890030903c4010142d00d2005840f0207110850007080500550081054034181606e40040c6500c1c54080d480071311451040100003d0049002c102c0040c060030360340401900c8100040000c03c050b0003182c8010184841500043c1c2c0d4101400250750700481a9501700c00e0031b01c3c0990080c40d10395038401a48100f44500d17001d05011444030b5800e900fa580c0300502800008120302ea03503c010003800d400c0b016107080340021014042c0c00000741d400b400402c41c0d0844640001810859100384905d400a40100b130303070b0303050654940000688aa541c03850001140c0d00c00e090a02c0d40c24100018149802850304003810964000b00060010422141c4807160441140d564042c0c035644440c103200440300000000030803407041e4240001042002d030403c021144003a81d402040381401401c00094501c0e5041c04c1101d00f11448 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 413662958 1250 413661708 413661719
    0x210111312020d080a03051b07020315070c0b010b0d0c0906021527070602120c280f030806010e0a0b0a0c1103070b0912010606090b0c0709020307050309070519 70
    0xc1060030741c0740010b0a0105403040c50f01c0b5a5800d6004514070400a5550000c001d107100f444d9112880001012040e141000507d03800b09a8808038407040100b0403060400044541344500681070000c0e038071000c202c089581d0340c0407101c80da800c0055186811400c20043c3c0c03c076644140700d40c1d82204c03110340c02404a02d05104243c142440050a0a500c2522100024010502034140d40c1e9041a40000406150b40f4050009040081070f042880c400342c2c04106040c01c14400140b8a5201d000c40380925034209810681c000e1000e0104100500100341c80c4514810f040d040076010303110300c00a8032005040d03404202000080d030240c0c05004200c08040c4608420a4803034185925030302c0c0309820180f801c1d10584d001030b1600c0c00c1a84920701c1d0580005010000d42003100380448668003400c000d001a07414604040c0228626010b42e41c560f14004c103880260140410101c401012000c100315540e0501190081240d172003101c0816043c410054005042e0425420341d04140400b01c0881ca860360400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 413664208 1250 413662958 413662979
    0x30a0b0a150311030607020a021f050f0307020307050714130506060d140f0105010504150518120102070614010302030a02121002030f22050705040e070801020a0c030927020702190602101113 83
    0x7640c42c410010304cc051401000d1155000758010b41c4e881e0002c1d600c40e569840c00310b01c1c20b0b219030040c1c1002c80a1103402c0c80241c46281c8103142c25150024040b40c540d41c3d02c40840c030907028040c1407845003070804440001400c41ca04020b8019584414100c66a07038a42d00151054803e03407040c1d000005c08034485d4400148114090321768030311061480c840195411000130601c4898804400b000e075400201e542c03c120844c400c0c0500e480c01d00e02c17081c2d5590324640002e61500200c3c40044d005850451640100c0382007030206d240c50070001c100031900c0781040641411a1a021660300054a8200d04840388400800f000d41103001d0b4804014205981400244030140c1900003407e8058418034802052003070307080c0060b02c0619010f0350303040c080400c2414001c0941c00d4542c49050000032031401c0f08050800c035500364098a2807100003598075902480403074505240314500e0810b5403585000071402c65030104122405030341200d000d001d048000484c043c0d0910680240d004d02020704030341080303140b010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 413665458 1250 413664208 413664259
    0x100b160201030f140a06093204020102030409110a11012903030f031806330f130b030606180402242b050105030a0b0a150311030607020a02 61
    0x483d4020a110800380d18201007082c051303812492042c0c031010b045c4000903079442461064100790040d4441000c10341d00d00309007a424011207510340c403506000103095900800446000f4890104200404020306214200c00c3c0c001109210016007081c01c0c0c103160f00c0c0c050041001c5c650920f00b41e90594000855101400e00c001600075030940030078403407a11a440403401a5218003125444120040002d203605030800100814200c58126005800441910503d41c03102046c41c1d03078282080020442c13400200240780e541000e9600002c0c5120369070b2100c045030481050640300b030f002c80c1d0840c0c03501d1013000840e08111003129149a190800074015152141c2c04412000c41c43c07103030b258100c95400900a00d540580c030041c0c4a4840c507240c0d00340d604100345500200d02e01c544001c0029504243c00652680110314019110020703c102080d07501400381d004501c0d16403c0c40e0940a195a02d1074161040086d412142d44a40140c40000b8580c500200306524040c0e0700900c0c8294002d5030b608840c892094 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 413666708 1250 413665458 413665481
    0x50118050a06080f030d050c1204150b060a030b011206120209041b0e040308010906030308160905060415090815180309030d0c120e01020327060f03100b16020103 71
    0x329010b00181000b070a018040080801001035691780201c0d0607148180c2d61301402008415a04210320303080d411180c0c60312500180d1110a92a8044c080d000e98130141213400c0c41558840d100043c02c100340e03501035100c045844070a0b260504690b03070707504500c03044480300d100e100030000c1034a401e003005140c0208a1a0b20074130403100340b08814000c0640da400311181d60401310170f200034101400705050f000018140141401e0714144001030459800401c1c1c105c001e4100c2c003031082c4031130000c0440da014030a110302801c40a420141c0703032a500c0ba41d001758128038862030400310b43c08038404a44c6c01c40c00b01e05403500c0750066440f1403082d140d2449089420301d8442c0b400321180010302c40c1610564040c07006091141c890303985c1c03101640c0d43e8149582500b0202d83d1840034407070540794440669030048180c2e0706440d405051708804004055401c404e400c031105445521040c0042c1c000300010700e84d00518050035210980c0d20714a0f071100d060410910415400d41510b01c2480c2c49500117602c03c0c0c002040035071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 413667958 1250 413666708 413666711
    0xc02060105010f210603060e122a0a06050a2f0406050a0c060c02060f16020d0503070207030611030417041d0402060f07031d100801030803100810020913050118050a 72
    0x144d05070041c0048503000d8004544807916182c030301c181580700300f01000b030300c0a01d804a54506840d4411750081407242403090b80f40050300e40c0124803110307030901406541d40d400880900103407034400402d50007060300c11409030b44c841c1c0951140403840040200444800b0302402020f20302410520103840e9500007196100800ca41075044000140140c0100c5c804200182c005110074205074100e5440094010010f0003500c8000213244151a03001803401c5400b03c650800543da90ac1e0340d58201d081c003e0700d03040940540d08141800c0c20020301c506c0250302c45c0d0300481c1c5c070104450403c92010058030691141e1b89080d442407032024502c054403000c45030003905c001c210516180da20b8101d000907812070710007a40403034400404c0316140c03550766944400c0102c00312048944800c8091000d44039190600001d03007101c4c40417000408011908074840d01520000301200d40001d000c1820301d002c0e50060b1301260286040624107101103646001d054182c40c0a9040640641e4032450030400400e0010100e0503441d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 413669064 1106 413667958 413668007
    0x210050702061b0f190c0e0108100e070e07031a0301022505011503051c020c010504120c0b1b01060503150601050703030603020910090c02060105010f 66
    0x540a500e050520030b40c0c01003160303181040111035444548250105813807101083c019600e0340d24818150a51100c7c0c5038011004004400e12901c1455072080a05040c540b03501d070407285480560b941120b640d5651920440c003074810903241a000b00b80e440301215101c41807403210300c1c81c0b0390781a4000e62426001c0b07911003a0319240680d1144851020401a20422100f90000c195807952400e00360081ca881e410069280c2c4061480c160548110080741c503103281c00441c080c1d107a90340584459042031f02c1d140701d90668040703a450071105000d0544021072110385410283c0204625401e031488284480405542140e00680055200f40d1100c0c540c02103010402002c0c5502050030702c1c0441e152001c5140c280c0140803141c10095001d02d844080140302c00d12002104d0441c1d81400b0140310f501c4d1407501c140e0b21134100303014050000b05016000c1e091107005800f0b05140103000c403041744c0e41 = true := by decide +kernel

theorem cover : BRFrame.Cov 413489208 413669064 := by
  have h0 := BRFrame.cov_init 413489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 413489208 ≤ n) (h2 : n < 413669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
