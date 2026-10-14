-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0865
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:15:07.661211+00:00
-- url     : https://prove2.me/submissions/e81c1f55-2db0-491e-a046-d300c54f2278

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 155395683 ≤ n < 155575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 155396933 1250 155395683 155395697
    0x31b010903060912020d050a09030807020301151d010501020109030e060703030b03060115080f01050114070302070902040e07021b13110c07091509060e04020d0f0c0e01090b1e01080403 81
    0x40802d600b80308000501e070042400c0d5814040606000e0725102c400741414042220402a000c0d02c00d40c801071a0702a00c0d40301000c15035640c0349000083c05040315034003030601940029030002e0480c0e04141c16107260382440c10350040c160380e508016400c0718103a060140204215114010703d0b450411300070098035100707090005505a2201c00b0a14100c0260805200000708c2803601040541104169520240110800f5019030404000030440001982d40c100850008034a4100b0540213003c018003500411500315103c603903034800c20501e00c60035030310030016001c1e0280ca0010303805000c2c07145034140d0002d041c03d1150094030f510304000700040700c1c1d00b2a09100620056840300c0302400440000d061b07100d0b011030802035068141c1007146e03e66104040703031443c000080241000d01403005a01c950115a9611800c007a410030800140e517003000204540d0700c0340d9010503003408013415181618811101009000004001d0210401e0300c0182d08000e81080d02065540358030030507540d64440c1c032074074001c0d07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 155398183 1250 155396933 155396939
    0x30909040f0f080a021009021f050f0705071401080f18120c030d0e0a030c06020307050904020721090b04090902010507020a2702030f06190b131d0402031b0109 70
    0x100b1a6012030100301c41c5002c00040c4980000da042001416041c50602c0c1048494065800101c40100380c00c200d5101e083c0c05c2c04041e10440c000d00c10303a21781d4440b01c24440d5803580c10b407600319207172200f5008030141c119004800c603000303510610794140b06000c1a8200065034440d008008050b203a4010802d0180c8240c1c00c6210b11a076220001d40079250501e80115255109032605030291034642c502038542c0d80c001040e03040400e510122545000e80c02460040ea40d48411400f01d6140c1300720307403c00c2d400c50f00006200040140c0d00100c400c41002143c0b0315a07842c05001c00032180c042040c030514072a40d00512060000c00704591181048900c141843d520b0a031b22540030070101c0f4401e81c440004072071200c03140c012142d14003001c280010f03440c407011450b5207815040880c01c0d1001905040c021071050314007070307544042640c114021301442074480b41c848080069210540c2d00a025840780f208007103008100d55216045030a0086500a010b848002d0f841384000da212000d400d015410006156400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 155399433 1250 155398183 155398193
    0x9060a051510030902120118050f0105070c0803040f020a03440903011503050a0c08160312110106080705120c0306010303050a0c060c11011a09070e0301110c070602160602030909040f 80
    0x7085410b001303183d542320386d0290a0560070000e0080340040564100020410300c1540140810192b40e40070760120707143e4581d0b050100c1a5090608003d40180701e4846c0401402442d1a901751107101d48800f00d80c5071051484d004412103500c2200324031984c0300c901c025200440c0c050240000d03100140001446002503045c00507031041982c01a1141d401c40c000080500482404000c0900042c40040190b00010148030300320002c903202c09002070011483c21401e01d803042c002000146480002400850384417480d1a440b00e0041c46001c1c440c2404014a0805040109100c00e61a0009028141c90380c41c54800343c84650101d0b075520200410b81c104c0b08000b03481d81c880d01080402a0341d400c041c2d60b007403112300e80c01c4440c0080c1c1c0301d161441e900c01d91502035954051075588401545401d010b90107071840464007600c107842c925141070314041140b48003d41e0014441c42151955400c40b20382c80c03115040d85440d07001300d003d0b110040c1c008202480b0941883d40055401502c2848103088a442d5901c034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 155400683 1250 155399433 155399441
    0x40f0b06070f1214031602030d0c050a02160e01030803090319030c080f04050c0f0f030105161e0906030b120f160803090913080702030609060a0515100309021201 71
    0x4440122103640200144480a01c240710700b0b0043e42407a40710183c00c6414501140070040072022011760113584410321902c00e200f5640304150305401030207000d4004402920540205203203000501c100140012128201c4490741d0449011000a98090f400c584426034242d200a10b540c04501c0200015181c124041100441d808003d0390002841d0040803402811000040c4c006001c0c1c8095200707110100398042251a5002d2044929048c1d450800000c074205070041e4264a07070552801c2d0410200e000c0d00d018050300402c00c5d40e1108920150b401c0041c21840ca08251a0005203001740107020a0307001c0d51000c031030b601d0018071800d44107070b80e40301c4645445500d0b19040c141e40c008041d21401603105403403017000392540d04040d500345a1104040b0f504070782e0040442643c80c40b110899018404050101c030b0500b5005015202240383c0030f9034650791100d059510300d0b0454035103000030300d00095012680c0502c7c10000c207500c00c4105424000c0b000b07084c910b001079030700c5103904001d450081e9007482 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 155401933 1250 155400683 155400697
    0x8061c050a1202011506021b1c05150604020703081501050906030a0209240a0818010905240708070c05010609021c1407052703010501120b13030e040f0b06 68
    0x119030baa560081d079000900355061310100740807182c034101d41800501d40214080a400c41d40510b081d070190464000075101d41c1e80100000040c45170304840109010300402c1d074145c211a043c030f07502d0382e64840200b448200e20032600040d0002c0c08c508007003035100300d6165140840c060145011810089800000380c9254000d503001d203080c0e580000c01191900f00800304150300a180b00810303409219020440d1000d100c4d200a01003002042c10005100c400001d4281c00141510f100811070f02104d0324189580740594cc02c1013122100c801c1502a803a1000a9000e00c1444103075541e401ca9110b0070700c1652000c0c00001f080741c2c95525080302080855082c80606050001c2c1c03451071580c0740d6400500001c850a140d0303a140001814000c21008540290840703036500b681c08040d403041041d0855030207148540301c0e04039070305500300000040c2c42050b00c6d240b45419800b40c4403a2804c1d444440103126a00070380f5038010701003000a00301001c1450250310500d1000303280c0e4800b141e61080c0c1c6001503240d074044030b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 155403183 1250 155401933 155401943
    0xf020414010e09060103080307050a02010204030602070302010519020c0705061c140105010e03010603051203091005040b0403030b06190e0a0f0b0403050d210209010e0402030a050a0b0f0108061c050a 87
    0x60040006141e00c02c0c1c100c0d00000508081c00041d415500c4110061200030000028032030001103011135141700750b040f50001e40d00b0120840d02d0b50028074000707000e05820345064240502103000400c07030305014401c9510f0b030754420008208092030f10007032141079001019840402410400300540c0c0100902407440f010340601c5242e00c50f0b40c1000c001500d08010030040717038007d80c50102c0074000a5000552000d45880580415440c2e035204103e40c1c1c43c1c8030b041e1122098403800c0c80144400c000300204218011880307900c0c180444103010042c803403140078104001042d005414585022140141200355801601500e5142c1c06621343c1e5400c1c0345808141e02c01c48004100040030001c1c0032013070001050010311468030704424a1003041c0300c6120030119038261500b60b80041c01401c035a00940c0484080c0d00054029900c074680040890000c202c11664220546d060101058440ca4101c10802c0d917010161104196500c1e403506104034100440c6900312083c00585041c00420300c2004204007492041c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 155404433 1250 155403183 155403221
    0x5090f04060507051201090914100b090105060702031506131e0b060a020703031101141311060903150a060b03010323060c040303180b03130201110604110603040f0204 73
    0x525281d021a0001800b91081003410701440003203442002d4440d04440042c18041485822030030001340c292108048900d00e0310900c02120240b4140d500300b0795072010120703800402c0b0780c1e980061004d14414154002e41c980c10681401001d4106211850b41006c0c0140c01d65107258503650b403100440c0c40700da1040000802a89d074109102c2d030f080c0540c464208090750810309040880f0b402a41c0d400c5c1c24000201480f000070611104040300354044651f04040b82d015400324100149410041079162106548410400480304800e061550845050080140043c02d410700150100540ca40e0046d00a41d8615159800020100c031083e02450207113010b006d82c0c1d00c60a00c0e41800c89200060041100d0343d64010004020501114000740c404803505820700000b0064020300c240b50190302904000d4a80c040801800000302205142c5540c09100380c807401d80074a002c4020540d138941c1103400070240d20100244010740e041200103541c009100b850701c030b00b00300d00990004d8181c41c50030051243c40c0403c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 155405683 1250 155404433 155404441
    0xa0e07111b0301060906030b0105100210020d0b010f0c0302030301120c0506041e0f0303090308071b15030c050f1608071a04170702030a120c081210080304060e01120605090f 76
    0xb082c450900180303603044042054914556452081003c1442071030712488214454103980303402401031080c001d51280f000c642d0b803959490720400900007103584500043c0d5103501108250700400c031950303250360140c0040d030550303180040d1145251a102c0c0112540b04032001c00240380d480354000f034000f81600811000f0180d110030403943c111241c5034011050b00310b820901b040469080742c514020760303400045890742d400850905034446005440074a50482c1ca0710000039080c81968210102000256001e000204c0114011516800b90900c224400d0004005007505450008096244103100d036400c181050b1903512010400c14170301c0407c5500e10301c1c4008010421440c0414650361000d5401d0150501003150042541c4000903071009010000c0b08010310103050094014004c0268040c00080e07940c00365079003608016200380e90008648400d040013040e080000b1060368241c1d40a6a68030f0800403811004484608601e03111210780b566500001c00d041d00d41c400342521460030070980403000d0034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 155406933 1250 155405683 155405689
    0x3090105090a030f0e040914070503061e0c030702010603050706030f0c080c070605181905010b030c09070819050702030c0d05160b06040e010207030903050601140a0e07111b 76
    0x280c01070070150325400105650001035003058420032001000d01e050b100d50080000883c0042c0340ea000c2c050140200c42c1042c2070349080000380300e01913a0b41603043c1d842c103072144580100c4240b00803076194030041115000401c00101407000c2c1d6403040081c40040b035015625103556040140c0c40d0007440c0082d40310304c125002a0541d008030075104141e850300d01c0492800400c0c083d0740e0301800074003c00c80368440c40443c000d0300c016088054501210025030b44149000c503a014006002c3e0401103410b9400d240180d40e02d454040f92844804201a160700240e0307031452411100d180008113603551141041060343c1d503807a001c4c03103510311a00080d00110303680e2100d19101c40c43d217a010300d0b510007044801c008503804a00c4151414500907400304200301641c80d5a4005409000c40c124030005942c1f01003410b5050551160068042302d0041d0152420742e41c03120072828031040c20b450721503042500004d003040080d43c440901940a4598a070850203d012030710424140b1070340c442c02c41882140d00140e031242c1c3c9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 155408183 1250 155406933 155406941
    0x303110706080601030905120a0c140c01050301052b0b0712110a03090303060b071a0901061a18030d090609061d01030e0a06021201151815090509010803030901 70
    0x52440010040c0c1480e00350000c041c000d0003803c05040645801884041200c10807072803a005044c109180d8407250540002030155008660a4440104500d4030300100b1101140701001c280c4180d44052a50b801d1030b0034804807114001202303002e241d00c5100c0901080c0c1b80321b54002c0c1c16100b44d034098000d0030190707401003001011110380d103040c91500c801107041e9601881100c3c40b042d26403d01003001180f80c2010340040c54164400303042140c00203400c0081010ba10454075a07079410303042402c2d840d1907451105080340d0060050500c00c149800500c0744e005007840c098400602c05040c418401070f0a000030900f010324964088001c1113444500703000440d004243e40d0042c000a280000c92280d02e1841000c29000c0005900c0c18980c0d140c83d9658062820b0084000e030a4100305c05640e54880554842d103494800d104801e141c010b40323414544441d100da0740d44c0745c2c408818a608140302d8149000011000400d500031400c0c403514540016030383d1a001c0f0901d0003020750b60051601d038a45441164299 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 155409433 1250 155408183 155408207
    0x9010807110703030e060c06010b03011d011802071103030703030522030504030206180306070509100c030e0915041802100f05031906050414040302100612080309010f0e06010303 78
    0x3200c01e0612848000c103000400708120b0f50146008008a41071002188051040307201d50100c40c000e040010079201e4110000358101d49c04030b200e00000c082000c0810320500b000780100c00a541304043c0114140c8034940241100e140a0200040020b0790301c8006440c50307201d5901100401c2d2135408100c41d1008c1d450400740e81401100050454240035540141180b08038000207100d488041452034000b0107064000b15614405400c5074000e04000c2d501822030f41080d4066413188142c9030690802620900080c0c0e902c560644558520a125404000748003000a0885140c002500085002c0f030741e480c02003800c500a84402c098012403580140705d4800301c221505001c1c0b002c60703088099280c0d4400200c0350b000304101050551034a181c020300010300034551040f5406030401003040704958031300c0c0c0c199001e244070f60200da0490a00b220400117648a5106180e500c4e1502c00180000c1040319000f1907012501200008255071001d01e0501252110501030f0789580c0942d0040c810590010728803070324 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 155410683 1250 155409433 155409437
    0x90911040b0f04020c032104050708030a08040204091a13140106210501061d090c011d0103020a091a04030210020f030d0e0c0a0305100617060703020310080a060209010807 75
    0x11040d07070326001c505003540030034407180103c4c2d00003004200210706205480000018150505d20340c0c120301c40e80b02e4000c0080c1d5080d0b9172400b4070f0000055403c00002115284d0600d5220190140c2da03c2d02004014144a142030b00c408071f06030fa04c007540c00c0c548038100f40316140410001a10714202e0400181602c408181419245e1400906002c0d45a0542d040d020200c80d8510000302840039240907400340c015640081c411290321074010b100040390318aa140305005800488440403030b07800045425003480341c445c14024904090464180d4401d030000c0c62052181c0c180401240c0d913590000b50410b900341c4003040d90240100d01402140b03400c0c2c1c40111520a14402000035020980b00a521fa10a403415100000ea4549800101c0e030300600c041c000000c401481007820950b00d0402c41d072516201a00f050045280400c04180100500313490360350b0081480040c10070341c3d80c0700700680c02548003520801e441040b51340300081c401c008200c0082034030300c0b4550258440401500141940f01c0c05800003003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 155411933 1250 155410683 155410691
    0x121d031e0306030622050a0809010e01020613080f0c06130c0f0b0904051017060702010b0a0324020714030c010f060b0a0f030213140a050102060c0f09031609091104 72
    0x51907400081c4903030000c003c0c3c1003000070301ca039420707860715800c0e54500010143c0c0101c647c41c2c0140f001c024080c0117410700c20380b1a45800200c400049880b00b8044a40031034103c004400f10001c10200f1001c0c1195a0340c0d4040301f4900380c6a078500528052048403003000010003580c0000420000c8011800184442140d21309114244556018070303004006806008580d41c400003803d41c030301003501d100140302030001d40c0f4020442d04003041d20740b0303000c0b00e500000d5070a201c0740700189d041540c2031703c04807500403402c444074440e41111950618446154440007540901c01500413503050140503c0b040890300c000c541d1340c0e20008440e420b60320320150030a081071038440c041042c1c03000401142e1417100103107448209407000324420b80080c02000c40380c0c04603402040700802d140c1c43c45070280440c20700440d413405000c2d5461004917550002241c480c58500418400c61000c2c0b058000540741202006040e02c854000d224244008200030f80d0007003c1840d00c0f2070f100810b00083c080f62160100003075900340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 155413183 1250 155411933 155411941
    0x80a061a03070303050d0f091407060e010c060513050613151109131517011a010215090a0b041208150f10030e06010303050702030f0601060f121d031e03 67
    0x30b51140d64500c8003805000340081c02841c2409075a005010010644a04020101c00380c1041310030b280303256180e0a090b01c10844041005801040c0050462405a50b400c0340002240c1d06c00c0301524014205a810540a0000c98002102400414420440308240041b00070042c2030980501d0032102001518614004004120488030b00c119484080141e40c0c81c601c1c800064940c3c00101100c603080c04070040d100c400400c0701e11742860200310034042c0c02d000b0b0000c12040c041e015030140f075181120b03000d80d204002e018409502c00e405242d10000d140143c4100021075151900350b038008a400b110060307407140038907000c50b4011001a40010344490a00034021141d804501d8210351000c984bc0300d80c04d581d54125a240c8070390000d2618298590a4514035692881d001e03001b0303000301074100d100e4000c2901c800106080001c03400d048544c556507440303000b00c03000d00696503010300c1202c2d0880f17151500a28001c0005a6a03400c46030080c145c02181e4503103c1d95254a140c038203240400607100e4040045c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 155414433 1250 155413183 155413189
    0xc01050708180c1e03011506020d050405060712020709020d0c09060f090905090f031303020f09040c030b040609061407020d0f090e060109050a06050301060315030b071116080a061a 79
    0x120402e048144c86803240031400c10707070103c00c03280c420818035031540c20300140c00302a02d01d410a0600303d4440d0b40031590380c001000310565190040303002e25034024100340482c1c40402d240b00303901c9039454414015200e0345a00e071022031013a40d00203508103140e2078403824200700031035120b900c0b08010302403840c0a8480715030442c1c1c01801c44825201d05400c00344c2f540c01044881c4014800d4a2000702d41ca070860b503880403589031000c078040c450700c026445130881e4681149641420000759204a5100c90400c4aa070f0640d41c1e8100c4c0408054004d440041e5954910400034080b440b541c4020302801411851920b040b4100a2500304c03804442001c1160701d451405500350058840c8094a110075240e884c6955002c2c01255911000c2d4803890303200f5030210300011442d80240c0118140d1715143e8003400076150500e05001003480301d21004154075514000a002d581c030a1042524600d041c1c01078030b40071400748504c004048400d81005540b50884840c0b641003003198803800781c4c21200310040400c0e04142c4400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 155415683 1250 155414433 155414443
    0x31006030b090f07020111070b0a0b03070b0f0c0705060f090901060e030d0c17030c0a110d1e0e03100605030c042f04030819031419020c0705060c0105070818 69
    0x80c0ba060b20b2040b000b00c4c030307180d0007074112240c403880c0c040c50907466a0541c200030062090544151001d5803a00c0400380d8142800b14000c0c007507841e8880c115140c0101c4c0c4404580942c01250814500c0c042c9542c049065071301c4138020f00e15034030b0b42c1103210344071801d080400101c0e0030183d003c0030034443c8511070f09038551000308020f01002076030700b010f403441d0301541002603007810b42c0b28000c44c010b0000820402101c4200d005414010b40c0c1e691020080341d91142060b0381c1c1c801242c0420041211200b2030341d40c4068003541d2101c50307641858480701100764074001c80c0c0703031a01400f40c2c490402d0b00c840d002c0c441403d08001e102040071080b035040c441d000102c20b03581a00c1d40c18080089041c1c400c21a0061340c420841c00b181c1c019a030001c58945d0f1094101a102140e22220b00c4420002e42400d080c002403039007000745c282c02040c1c1b1134140d24024620700c00d0000254060900d014041c003c22200150300d0f507a100c0640340c000950780c00440d2906c0c0c2940010f143e0318000b050716040e0440345070520354800e00015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 155416933 1250 155415683 155415691
    0x1020a030e04110405040207050604050607020a020108010b03061315140a050f2704030e100f120b01020709060905060117010e150a030609032706021b0103090c0b031006030b09 77
    0x40c0000d050b0070b6041c0030f004520654200541003400000c0d0901049070009203540b00d180100305a6810b9103a998040b40c07224152800a4000354491006110b2101018002d60700841c000f088850144c85a030303000b40549480e07110741554100c6000c1c0070001442c0380e02203101d4070241200c5440c2c126060000080c1c412001094090240329580200507542d1320040c900c1d102c200c1c240d411100a0302c0d2178a401410101e1208145e40510911050380c00500d010701560248490303152510b03000ca880c01c03100c61000b45604044141141b148000000d40000144200d101a015074400450249841000074192080190b0f081c0f038a600c940004210086002c084550001c035551842d50b08060804005101c3c0840c40d00301402940c5005072840801d50400e41d00e14107080250341890004c3c6202d40b02c800d024109200d80c201507004620b03007014000000d068500d032000c1c14100001c098100c1d0719020043c0209030800074103140000144a41c03650041d610b00c0041181d494284070b5601010041414400094 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 155418183 1250 155416933 155416939
    0x3031101110d0f060b03040c03020a12030206040f1e030504083304080d0e010e0c0913030c05010905032a06100e27010906140f160504050901031202010b01020a030e 72
    0x7040801440b01c0f20340100000703000c4400800d8a0b070030541130080040b001c1c0d2008a2150044500004424200d100b205001c0d0342c064014002d60303a01c0341c0f185241450680306c1240c0c1c05481c070345051395809a400300001082c0c02036881540301e40c20000c41c2842d00008001c480700140181d80640d074a21844c01a680561102c98072070849a1281d24010140d030040c2441c4500f09030074009141c901d0b2005600001c3d80c1c0c4004400c580911080b5424030a9888003030300c08460b964030034204400407034002d084050000c0d2089000003003040c070b40d488060a541094500325002401c5e0015040c0f60060410b543c0380359642040903007002c1c140300320b1242c2442c0d4140324503c40d450109000a024412140f28602d204031121140d1662800e550303031440c001c0c0288801245c1e014901800c0454002d00c2c2d03c0c0f0284070348040480070600d6219098041240c010040521040100400c8003044030340f6102c1c0da1030300070341c80340c40005110785650f0006030a490007100b4160440d44150701c0503000c00c0d48102d982d0f034a62015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 155419433 1250 155418183 155418191
    0x60f0306160315090f0f060305060601030207390e090d0f020c030601030501051f0f0603021b150a0e060601020a140c030115090c050f030a02030a0902030a030903031101110d 76
    0x1180a0700900824034549603100f51803040010051019007110f040d072804802c0c2003001c0c0c0012614501180c10728003002d450b41e40721200040f000d5000307030b0050103810301410b1010580c0089a0002c0624803030700c0300403a107440600c0e100d081100150b2118102400504400580d0703480c002c0445940c03254080d40c1c0c1000c02c8401c91810b42d0460003800640c50034003010741a2003a03903071a1b0a055020340416203215404840d52500d02d490303040551480300954900c2010140101d103091000c50180d000a006206803161815102203801410002c0d460052801c80c1e03000701e1071600c0c11b150f07401c032089440480d102d80c102c0c44c1001046d03079000c11040b119a51120320441d003103040c00c40151800d040f19111036003641c40d006041d00da070091500120221801c07001c0504c452884020111a903000c0c41c240d00d0003500050001c9601001e040d0050741d80851310716030004642e00c41d500040d117000720303a03841940441e4a10105000780340c1c6c44900c0f0700e400300c81c8200900c0406103513003000e02c0521440c0700c01d50081d5a9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 155420683 1250 155419433 155419471
    0xf011103072f0609010c080702010603080d0f02042606070c0b07080907080312060a0603060b12060f04110909070e0609040e0c040e030a030c020d080f0711100c08060f0306 75
    0x2c0c10514400007018401112024a03219800fa030003001c0c81140a00132036401701c0080d04a5105010700000d49521440182c20320010110450203000032098103201030b5000e12003c100d404102c40405c1c142c42a01d00040b031003849144a803818020090b02001c00c10481e11600400700d0110b4000517080f00f0680b9000391039903070704100182403c05076007214a0f14040061111500b143c0340500034004c281c00c0701c40420307495440341e0035021a500740c407401c580c0078001e1050300280d029441c403041d408013010b0050840f462a000c00901100c007403920f07a151002010a28a0f12424015681c035030042248c14505501001c40001030303054040c402801d441a6120004081100410703c050140792101400500158560903c40c0d6266000380030107000207494803801204240c400100b01200031281d0b1914007090b2140030b0b9161f611700d00103050fa42480056408a9400b010800941c008103450b044d00058500e0104c0005020607401381240d403280700d42d0340d481c840f56900460800e410500303c8202540e00c1322 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 155421933 1250 155420683 155420747
    0x60402090d1112031324090b0d091a1e04020f060c07091a100503060a090b0f090103060501080c030319030e3301091a13060f080f01110307 61
    0x9043c800100c0e440c003020420914080880780740c80103580844910b900101c03266400b1041c1d022400f5030031000200c0105c010451506848020482345035400800701e06030145407500d04c0e18000443d24001a43d5480081001c6094110301ca1000402d6141740f049103420150009a440340118a42500c00c030301c0051607846031001046414014010b1756024065400703011403008000d41e20140c124000c2c201036080d080b407607114004483c4920b100426081c1c041d801c00040c40001c0c00c03001d200c42d401880c890f0b59035003a5602d48207201e0082d44201000b0810b9030415249505008103044070074002e41c070500114500481c3c28a240307100e40304070310380020319000040c016454500301c4088441030484000e800344207880e5800143e07510103004500e40803280d90300d00007001111340d680c6610501540c2824860403074a406c510244418142010108443d500c030505003001071580d40c0040c40030781c82030201041c245002e010741d0800f1011001106d0a500e8000000b815005103149445540b03042001d280b04221 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 155423183 1250 155421933 155421949
    0x80705040c031a01080a1404060507200a080901110615040b0303040b4302040b010801060e09040311120d05070801060801031401021c0903020c3715020304060305060402090d11 77
    0x801f0084285800b401c0c40c0c10040e0050001b5221903000600c03000b03900703810a1103000358021410404008000b003880da0740f9030203640d8000c1c180003810020020180d0310808002c0001c903029040c1114802c4450f0a11003c00c030884140500d001c0c000c0e007080c0b004000024030310301691100400d488904074004814810404811000e00c00003441d1591442042d84000074001d600020381e1017500c080000c001040c00540e4010b600744a4407000074020301030a0451708088100310b0b0018800e080c440c2c403010400c008a03003403606041e81da0211035400300340400d5090f100d020325a0095000d041902255040c490700418a05050001421070903080c0e40c00c0b0303600708003581100c484007c03821103200320000e401c00d403101410502c0f40540c014842d60f154500c16280c03e240004050b10990600c1c4d81a411240e00c2c02c1c00500801d072814030084006400140101c06801d0303802d0450442c0e40510340c1c40b410130101600300d07107020302180d01440c418406100e854a42c00c1800c0345840e0004500078800f1420f03800100700c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 155424433 1250 155423183 155423201
    0x801060f060c050a02100f11030f0316090302040c02030915040501020307331b030e0607030b030f030a0206071701030f06090f1b080106120b070e011206080705040c031a01080a 77
    0x1c01000c40d000e41c0f20b80c4691f81003004003403079076049180101c407069207550380a20814000c1006007003010a800443c0c07126605600034150900c12039142e525000502240c41c00c02c0341c01c025030000203034000b040c5810703041c51228400b01c0b0308042c241818140000d59a000b8980300900d4907081544218038102d10f00203a040f20b0221550321740404001000e40c2000e1300000b903203e40030350140003044c030305280079025082609c080fa40003401c1981e12002d0403000361032200b06040e094040c0b020085071844003130004041c603000f00e40040c442c50411540041001b24100ca1640840d0000700051000451860400410710f403c602c000ca43d441f00b500700130148110b0044018100d40c2c68512182c445400c04182c40110303503e0300000c00465540d00d503500c0345000300c404010200c0b406040050042809030110521124040c509041598801d21101085680c03d420140341c981c07040704104039920f0140507a090908041c82c00348480540351001505440b1a07220b40e50520401c10000f4186962a40c410208 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 155425683 1250 155424433 155424439
    0x61009091506030b0603040506060f06090301090f0201020f07060219030e09040c030309080c060306040e150708060301060b0f43200d0f06020d0906150801060f060c050a02 75
    0x120700510040440071101a00c00c4201003410034501149030b2070300105a80c41150071401401e06996003504014050a5000e041513001409029076244c40c0c0f0309100f0302107e180f0800c14103d14149030f000292a21078580d0127484030740e201640900050364041040d0030b541200c1d0410543c0540607107002e81e20f400d403080c0d8468100d000c0204000a02020303914a404690081c0c5441104503213814442d0f4981c1090181150054420008103030b003404c1a9010b070100102d500203582c40840440ba070300d81c800009441000c001a444c000307004d00c9190070701c82d1900801600506510b442c1840c3d03102d24036401116031101c1c4840304041001c500c003050b078034000300310844142610310000c40340590340314080c0342c0301c0151852200c1070120302c4540c0311001e200c0168a8002c02d800c1b11181c150343c99510300d41070600100d0740b01e03030240000700d803540050003689905407050201140703402542078a00c1d400d6072940e101c50416030610072704115004007000d501c03040d1403d510703100303941d00f94500300300340703030107204640290 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 155426933 1250 155425683 155425691
    0x160302031c05010609170a0602040608040b06061e0d06051f090b030103210302040e01030f02011e081302120f010203011802070209190e010e06091203010e06100909 72
    0x1059400300081c21280300903019900c849001ca405081150000d008050214804074414031590000301c9a03929003c40f060304450030304c0c11543ea0041660080ea04c00380210720194107010411141c0110f0304d502040c1941c4050400044031300040e0315280410502c28410f8000502103544196070308120043c03d005041c40031080c04220038039a440242400f14000500310090100d180802c18046034100c03600003840400c071910b15001000c0c0c07588a0b0003a1800e25908200000d01d0b65910b80500340214011506540219204e000240c42401e2603102d9408100d242e03400e2000540d088560590070001c400c0c00a80f482c081440401c00281c0c480020350f2040c0318440f601e0b004000d05400440c1681c0e801d040c040030043d48095000e0590041c5007000b540040d0b0b000005203000100000c0c0e03600071414800100b0600301d10300300e0746e0843d032406161800b59008041040454081003000c000e689198400143c176643c9084040070300701c0b8024010034410790065104500c0c1307500c0398015501801403000100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 155428183 1250 155426933 155426977
    0x80f01230301112203020d03050309071203030b04140709030b15090f0106110a081c02070206280c05030d050612030301091e090302030a030f0f09030306030605010e09120906 76
    0x16040f1200c00300e00039002c4c900612910744450010000c0341d0740035140c43c00011196805451a1b000103240f0802440ba80c0c00008a60341400c1040c064103000e500c0020b40290080c2c1484142c0e02c41300002c6441144c1682800031706c641c010300300e00c2100e41004da0051079413164508180c0305d2460219003907201c400a8244040c40c0c9084403c54100d5285454040d005446880115240e440841010707000764414000b84c1c9400050310714400c1c2050750100014908149070340040c150780c10104100c0b5800d80c4c0512601c1e482031079410075031903420340c030304146200800d03503903466580e48a200c40050550347c488022407a43e8403106038000d080005d88040da42c50b9030315040403000a0192415029a5548032190400903600d1072107440003264040e40039519042031180281c000d0421403039609140d5a84000c00c601076216442080e032002e1090f40e001c101c492560034800309440040c1c01c01d4400404000c00c0c41011500001c8a100703615035401c032662075450484c0041d82034000c0140e012001d1221091030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 155429433 1250 155428183 155428211
    0xc0f241d040f1a0f13090507171609050907030f05010b0405090a0c061404140f06031806180715090506070b0402090a0b0114070804090e010b030706080f01230301 71
    0x790fa610140d100c1d61400c2d400300008102800c0b84135400e050b001003800c91000c501255540083c0150350040d0102c0f03070300b60b6035120788201030078230703086001c030150450301c10628038820140105005206044003400700d402c00d4001c0301e455181520004000910102c0310100b0490203400900703420200070420002e500d000900700c0d40315014140d00f22500500620041000c50145e284001602c084211150500d070521098005801c46031208981c0306121069100241e51040d004502c21104d0454552092401c0c480c078520306003028200c002030000000d02004180300002d18401110700b0f00c1da000e4900d0031028820703583c6ca81d050300043e4000740000b50000500108583c0b00380964400d4440303010560b03400c058001101c0c1541070440c0000c0340005004070154103000074005080c01403000038075090b5143c2c0c0301002c07110441c2202c0302c3c0d40d4403440760700003510f024000311006110310705010003585450300c54104038007414000d04200900c54000207165003108010060444000380c000c0150907451440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 155430683 1250 155429433 155429441
    0x4020d0f150513061206050403051209030c07060c0209040b060a08030f070c1e03061d030d0c091703030601031104031b090608010b03190201020a050a0c0f241d040f 72
    0x1402d03000780f11036100c8188000381c51041c4012112900015015003135a5a02c1340c02901c4050815010080c09119950103001407907007443c0201851001181da5029082d007940c1002601e81c8590b0500c400701d41d42c0000358880f484110744c0560300c00060a40c0380d032103600082c0030b611140c1080800d440040360120f078500c140710040903118020400c03894015a600c100303600c01500d0000d0200c0407509440d0400009540d604807005251160040074060166225a030b86107800c0f1401c1c10250356142c1d9043c0140c40d4202400001424001850188241d0281c1001e5030301e101c094101030404d5500e0007190b5500c00c0c11001da4010f50b43c1f101c0309200b44a40c14404d80b2440006001c0c2901241c50580006502c540502c10ba0040c1600a0003611070f40d9601c044c128404054030070280c0c150f01840f0080000101c00f8419000d41c01d02c00e0007000700c0b0754146141806201c9858005100355542440b030740400002c5030201c840c2c21111403074001c00400014245e280b60a01c414900da80113401d04c0040d1311039402c1900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 155431933 1250 155430683 155430689
    0xf08030408060c0405010c02010807021002070c05240304031b020a03051005090f070b0304020d0c0b0403060b010206010303170a0603080d09060b03190b091204060302090906040c0203040504020d0f15 87
    0x12503005031103c010003002e074400c520aa078003103851200c09400550042d001954400c0032401690344280c0e00203d440c080ea8046c1c3c1040f641e03c110b9107802e01c402e24203461224951024125052012110075626009601c0301601c00340500500320000052414900a54103e55902620110a9658a20700151340c1d42103c6c520110650030107000401c050344c00108008000032420013410204d00d8a035002c80b0a91018100342e800c003c0700c426420110342001000f40040003551a140d698518504040303044441d03912801c0c1c1150007100042021079400380400200503007a2980d00a5a1210707107003040280100c2d440106034543c0410310040860750381c1c2c41403c6442c003c03c1e050101008500415071200c40c05017841000c56030054440c00031880641180f030f80401c0b80e004130790040300da000140c0c10903040381c0d0046000980014500410342003c1d014242c1040c07003078409200003c0e010101a49a006600402d8042c950100da914035601841d04803081d1105040402c0140000b2003071408028980c1d80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 155433183 1250 155431933 155431949
    0x210f0c0810021213020120030415020604120302090904020405060402073c080406050a02030f03090c0112200309031b10061a0702040b0409121701050a12060906060f080304 75
    0x344110551918500107654140e64601c0c0ca8030507445030390487c2c189135000f40024030043c0f0001c80c0c0c82c0da80d411403041c91100c0750010101407901e403900103406e002042c0c010b01014010301085165488491000390055411079011031159a0792000c94020300a1540203014010001148441c03010481803046025101143c4c0703214400366410304620402040000810380704042004108142c41030000d403400007171074810343e850107000c2d00094601e0b41055a01203190f410a246007111980c2201002d100c0308607030142400300d4140d08060400c554170b142d5101c9200a00000022101241442101d2004031107c0a59000306108504103960b00c0031454484401450304a000c5a074682e1b480c14144549040044c0c94541416175084c0000750824003c00c58015445028800c0080d17480b0782c8000c1c610f10260b031080c1c001c4403030059200200d070040e48440e0007140c596800307000711542017040b4400182c00c0365003c80e4200c0181741c00001482e20340e10100e60b41505800101d0b0104011000f071003165010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 155434433 1250 155433183 155433217
    0x8031608070e0906101701060201061806120b040201120207080c06070c050a11030a08040b07060609060602070504090c170303070e100806120f01020301060e030106210f0c081002 78
    0x840415035541c203007110b6481e800600e040014000f031800403070124041000345820f1010401d21030395050402000e8100790090b035140c1e1014068402401c0c980b0905400d520b4082c041da0f45007103980d800c952050318001d0f004051400014040d0b900405164400c580500021903480410341000a00c0743c000c110303114600e00554020a545511852200c490700d40c011010b4055056203550f400b503000000c44403c1e03018003a42d062000030400440242004002c0c0e0701c1e034656501c210749011811a00c8035045091054549001072002560002c2e00300103403001542c000170f000c4841d04107008a9030240d0301042c0c0511012440c403141d480c010028500030480c0c0e4560f5070001d0b9845082204951f06600351000017550207001519504d046200d9204004c1d180c0301795a01003810017402800d990090300b0207170104d4a44c4c118000541401d210b20700081a005101d102c1c800c21207015040d07440c500180182c01c0d1021040101c0900000c1d4100c1d50003021a00101e800a040c5801c05401030342240d1800450301c004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 155435683 1250 155434433 155434441
    0xf030209061e060c0c1c020f09091e0a020402030717010f1a07110a031b0602011b11030c06070309060e0604020d02121203040c08011d0c090a020708031608 68
    0x1c2044220980ca1886501c0581420800103104240e0002d0007010091701c114003d101180d1100340240c070b00c620031804140074040c09401031101d101080ca038200d01a6020808024214002281184180180c0041601c1040d100740a09103400310740d03e0040d500034400400e0104083c2c010400c1d00c4c1904100c180900326a9a564001e55072021611500100c05240d01460317503441c0c0200000c100750391103035502042303440300c0c2404100300d0341d51034004490412020428002e400c91280350700c4d0060504d4402480035104031800400c802124402d070728140300f900740303040c40c400c2001c3c03007030f6031034410088102c8205d842c3c1800024082c00c01814203598043c50030303141448884010031194480c035006895108000400d50034402d880f03207100c0907058107001d40303107201c01540ca6100085020700d0040320204052420103c1040c219010a1000d40c01c28490034605684510045000751448008a035180b00ca070381c1d0b148500700030b485981e10051030f0030000001c03c40d0082c05440217450744100703030f99946204d0355 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 155436933 1250 155435683 155435689
    0x90306070f02030a030b060f0d06060315030f15061e03060c09050102030306011d040c05251203051f081b01030501050a09020f04050306040c0306181220070f03020906 73
    0x201c200824070068004004110950f8000d0308808602d09015144528007051409402070315000800c00414094a4220070483c066045c09078402c1d522500d4032040e0689d19596030109880141c4a0040505e900f546c980c843c0400b440c1e020a00509030010425509244880b428290010300d02080318080e25040e0a00c0300e0b14800e03540c440c152881a002586552948030054401d500366061b5a20b80602d10720021059841d10f02444480e103009481b015100d040800c2c02c1401d000c4406911300c0b80207c100c02c03050202d22a500000103d00c170360b040c00a03194991030001101c80d070080c048101e008200c080006103010300007a40d41102c103124015441385010110044003510020312590754030400011060150f041103a009022980c611228236180640c0c800c0071078188101260142c40200d58064100144600d03802507003016500d580b640089030034036549003405040e0740c0d070303e05080010b069500c203000e012110700c018103d070b00780d4211003040ba40c6a140c0c40074040180002c134003500200c004598242 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 155438183 1250 155436933 155436947
    0xd110102040f0b0306120f280c0b03091501031514070e10120f05010806090d360b0307030e0304050d06050601140403081b0303070e011409031209030607 67
    0x81c104400200b0700620345145026540c0020300150b910521800c00903080c1c1d10200903269402280c1d2020b401149581c4001110300184078014001c413a080c03100510020399181e0b0790406031083d50240796101e1319404031051034810182040c0d0109102c0600100511620b150f01c060020300f206000d21500c0b00c84030f00f070902c0754801d0301c8010115a40118000c02441c04a40300d49181802d4030380440690001c5000000b0399445c9917418145590f6080140000c107020711000340d000000b00d00815200c56041c10042035240b80300719241102d40c4102d0068207010503480008050210b0022800260307855400108450b4400e90300ca0010a10f40101c09c0e0001402100342d6040303440c020074140b0020456100c03a4041c1038014800c078100701810140c4860200140c01410241d4060b843c1540c41e1700c503070300e1000761803072403000f6800e050fa01c103004100c56198402c100b00007036842840d0948828400c85c0c19981d55000301d011895042c010700e0703034840380003031018003034440920100c4c12a1900e84400000766206 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 155439433 1250 155438183 155438189
    0xf0d0203060103112e021c0c03030902060405040203090c0306220b04031e0207030c050a240e1804020906090c030403030c090306060801050a14011203030509030d0203090d11010204 79
    0x541c000600401c042000f03807907100f0031210702a0000030417580c0d003e80807007140c0c1540650b64166841e501c0c1d481c50036904100d100003240c910380b10403015500e1848042c02091143c04010b04040c0c9a0301540d04544030300c41642e0041c000900155128180940c1860b1a0000480360f01c1c082d10640000409500728500e0006134840c0d00001075403901000d84504c400880000c00940902a161461028041e590504820404404d40c00303440558150f14211203211100d034025845451150400e0024031481c0c80e82c1041b90900c0b92200510785030414042d920800c40c0d1a07141da102c440c0c42c518020310303100280c1240c841c46c801c8900a00c07958461302000840e030025500d801c0109014000034000034001d9104c0c002900d40c50808000241d80d0b0380c1c803a400d035049600302c40400e13511036092001c581194000c110511000084d12031140d8140038001c1710742c0204441c05001c254440f0702060250700300780122090f8040002c0159502e151250400340c0d65041c11181c080003075190390f40d00360b4050042c4256019 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 155440683 1250 155439433 155439439
    0x25031b030f120c0509130917040e0a060b090f0a0305060114040e01200a032007050d03060302060a0e18090c0a061b060e03090904031d040e07060507030c0b1003020f0d02 74
    0x100100641885581c491400800001031f5031041d181c808180d4040d003d164000748200c52680c0c0e14200140b0001c004405019615030f641001d1003448035250743c0050b146402c405603060600081e0010008606502642c0b015005014920001c01d500c42445000c5441c12019101031095072824040c65003210300e15004060400200d4030643c4800c003a003c01400c0c0b5585500d0042110717451003401c1f184001c4480b4844100b81000660078003002020f220600e4900c0ca182004c002051035900400c01504c140e0340c048003040714001c0440e84940da00c903110100c42c0504449081c1c507151542c4138560b503601940032507209074100c1d0030008070144103640740442d8030140300078103000c95882d594a402804a21420340f804e03002c180103540c5d051b00c034880b92030301c40c40c003d82d244100c60020000c5c040f03035080c0113035007103000341d040000003400400001440800c9a00c9450b101d9130b0b408490500b01d4800381d4218000f41101d10030404e0010000510b141107060f28021035418200030100b00030000100340c3d601c80250 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 155441933 1250 155440683 155440687
    0xc0c020a0b0306060403080a021b04090b041203060b04140306090a0c0504090807060f09120f1709070305030403030e1507020306042d0b040c06030225031b030f120c05 73
    0xc6045210051500704074058252402d254070395540e41f000307821810300400180c0c01800b515951800108205d01303180002d4034104092482500e401075180c0000f0302c013410b001002c4013001401c51095002c2002007200c1801c2544513034850443d0601f91084030f2055100788944c00120309c0c980404954040b8040d489241c0322251483e2000b4400501041ca00c00c0d110507005004d0000070032200e0140100000ea040ca00240d801e01c186043d202409840d520041000f010320006200f0136001015030340f4000d1034890401701780e80c0b01e0041910b801c40350f4000900b5804040f600008250f002030707a40002141c00c6442c817400018503103014221340903243c400303545036102201240100c2c0c034103805c03d11000d0140800381110000d0801041c030040711124100c401041d0601000709005100c40b10300c019002c0d83c54203501d4400850300c907201c0e60503900e004000b0544110b18070410140102c10400d00307400e120320301c2d440e4800b40f07040262054000f45601808144041580064a011031241d80060311464803130314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 155443183 1250 155441933 155441939
    0x5071704030c050c28061b0323040611060703050c0d0506031608070914060a050108150d0b15150313020604091406010f030218060a0c06050702030a02010c0c020a 71
    0x652462980100341c03600e02581201c0c20203520742c00180000001005a604c00314990403d0702000000b0646c001400c00501c0095800305201851030b0301905509482c18a203002c1c40c8101c05001304005412081030044000b82c0064483e41101d460644980303e0420b030b4200e5980d600c03041c3e0030b0398004c540580c80c9d84410410552504c080b640100c3d08501c01034121150a9070104414880300548c2c1c011100c1c43d400814104a00003442c002e00410001c55150701c3c60350708140000c54100c00321805983c0c10721100c40d000908a900a1a07a08111784008011300c0d1a514603003802c9a41c00130545103100302c24401c2c003a0382d080382401003600c6070540803450322901d16034030342042c8804032074600000c0341c0c880410803002640e10401d00400709214a00100745001d800c1010000d0010030100c190101414014081c680081048000c886025402502c1203952868448070464030b414045400500326807034031051129107039000014101801039030f0020400b10b10080800e0700d40c1580740000030341c0581916828 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 155444433 1250 155443183 155443187
    0x2010e03040510170a1a03120f071502180a0b19030209060f0705010b2701030f081903150803040803030115030e031603090b12060f06040515040503010507170403 71
    0x1210f400350051030f16110540c03420300084c20100d01620040310312074617449001c040025941d0f042204030b030b0450060200000410031010b4900400b01c1120711280042a04000c0c0105c00d04a241da41e0810039045541d148100d00c0204080d82500006004100c40f220104608803a0b100b00c1c0d5083c2c0707503402582554560460114080e5002c00d140d550400c100b4072103120404401c001501100f8442d1001140c2070140d001030041c4400d5480748400d10388103d40502d1074200207825080d040da9009440c0b00d0000c0c1450904214900c654880200050311000581c642c00d58903501503d0300d4001d00504644c02507a0301c1c0789a035039016074007868806070000c0004101c6004280b40440341c1d52410300300440d107000342003c80c2c3d086400c82446140d0145404151400b010b900c10f010b4005807440c82c0ca0783d0b0400404034400c6440002c004d040c9406843c01080c1c0242c0395840c2005d0314010240140040c4002030342c08240320b207503041071296500947c20031010440da0f9000e2800200c03070b800c42044584080c0e135503441c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 155445683 1250 155444433 155444449
    0x1002121807050d030203030f070201090309090e0a0f2001050a09090510030501020c070602061e010303120e0102030c070b060603090a080a030e030f0a020d030e0d0e0f030f010905070602010e030405 86
    0x2605180c41007440004064941c6800620350034000d40107543c4910b007200460407015801420403045901d002c80c0c0d100000c0d0000d006c032055035080080024004c01c1d0003101071401403101c0001d04041c142424040400824550b00c9180c0c5034850b440701d014291880054449000704e14203c2c001c41d41d140000d01210400ba400103038802c000310840800a03940f41c07240d6089a020204900080d0400e010601c0f07a41e4040024940108030000100d82e15080b8400b00c40c07540d901800000c082085480450f1024407043c2c00c2052021f0049000b1540d0303003001c0800380c01b40d80c07280b4400c130b0316085000001540d40c43c1c560141d0744a400c00c2e6010380b580d20300541c0c50000b250300a01c41312061590341c814410140e24100041c0000d090140410f6030b5070034107800301034038200540300014201810141d0405442d0300c003044151031200d490428801152601c4002120100b00050480d09840b5184480c2c080610540009070800d0240c0155403400352a48400ca003a500448558580c0354400c020812003400c1c1007035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 155446933 1250 155445683 155445721
    0x721030e09250912030306081203071d030f0d2c09040222060306050f0609070f0503060a09022718040f1e030c03032301090213150908100212 62
    0x2c0c2c40280c03d62640c2c00802080c01c403440c10b030b00080e13603542c0c188a01075007027000d40c104c5101c0a480904610b081c0c8402040c01610003000d01003040313494035215072910f041202a990070b42072000d484142c0b07114100140742041444010403040c40c07070b8100155a40e180703420000c140c0c1000e007019a540d911a0280300741100c40b141c20050301441c14820581207002482404041c0d0300c124008503072410008078540d03106002402e50303132003050040c00b80100707243c03c00e000000826039801e009440355a840005000c1d0740c0c450744500100c5000140823010844025200b15201c001c4c882d40034090b2108105111941c4d000c1c0c4036441c000150741000c9000b0a42250407601c85910412080741c0450391400c02c0d0740402c482e00c40880c04980c04001c017030101509801082c043c8480d0b118421a0072a07081801001484184240110350743e000a140b450881004104e10240c00704c070038002602014494000c041007060b1117590b5aa005103212589038600301e00890307460010030004903260307444c1c01001d0b040447c3c2e016 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 155448183 1250 155446933 155446937
    0xa0908040b070203190b090705042f0c100f0e150106121503211b02130e0f0604140c0901050118030606170c040e03030708090721030e0925 61
    0x504105603803542140d170015243c80fa107466070352814400d81e800d103000b0f43e84d00b01d54400d40c14440c810846046030400003640826148154a5504c2c2c80349003003905104082d00342400d80680c03c46030143c20203503042030245801c00301d030400440c040810143d442d0b00740303170341890707181001c21004201d5103100e10310202c3c0e452007641c0000360304140b000b416040b00b101d1354411560b501c1c0d510070041520741c903071002e002804071504012071180b440c0307010b1025044610100a05c1041941c131111000002c0e680304019504008044682d401610510559508000c82d811140c0c00040c004401d68294045444d05074003002070415a000e0b42801c005403043c05100001480f0700d00c13440c02c004082051390203090b0007000c6284130b0b0008840040503a9042c003940081d0075019504228450145900001c01c4030f40c0b01100d0b01e040440b945402c21014141546984030306000c070154240340400b91040f010802100c0c2c4207496090300030a00000380002d1003001c96100304d5480244002c080b403c00811500c034403103203c80c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 155449433 1250 155448183 155448193
    0x20a0608091014091006080316110301060602010e060c0f0a121503080904060b0c0604020105090604080601060f08010e070c0201230d020d110403080a030903090315050f0a0908040b070203 82
    0x5250a0045031011899030140146510601410034010701c844480280c0300c20046c000d2504020b5000d13980d01c1169011803051040041c690103010030a100004600c0004001380b055a0340da1b03e00a0291410014403103050003400080707210001c030141265524075208c101d03282060000802952903241846274020aa40c44641d144424011200c005000e1486211043e0b01c0d039101500340411690280c00180c0c0d011410000000b1100002400a40c820b90901e0541e6480d4581030201d0308034022948a03000c0340c0b049900109145070031600c3d0041880c081d956043c0f1580c0d0700d00603602440010366030302000ca4094038842001d94031842a4140e40300d010795100460150300b00d0020640c1d4014100ca00c1030070703800700c0c9440310344003a8054a02c0c403035100710307a0500701400d644501c3e140740320b08002c0300d06055032130301c50f402018028018040116007140f403000e12244640224030150000b110780c066001e1040e030000c2c2507648035110301144030303400840c8241030a01b8021100d1b8580e06c490010b0303a15200d5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 155450683 1250 155449433 155449453
    0x1f0305070909050a0e060603160905040804031401020414181501090825080102090603010b0705010b0d08090102010606030507020c0904140706020f0105060904020904020925050a0801050607020a060809 88
    0xb0f003d41400749002403c0007800381002c0c0703241da0512034068003061094220111414814016030b80c20400da40360743c18009503644840c903056109105075400103294028a00b034440d040c02041d8040c10843e508aa41000302804080c00c00c40e0000c641814008444020408526282a124980030140b001814101407240e183c3c3c031031600e007043d070300c05010034000072138007420f00709519600c2c8070000c0c4050300007541860b00c0480040c0e880d0005004013500380038003103481014820f00750840740c001580989200c407038249506044030640d0001004601560901c100050000c0c80f9100d828854101a0701901049618030100403000c1005041512284919841d07030b5040c0d801403250000424864000f841c10000c0b2304031030707402d564000784224400d103052402c02001d0380798a4400d550043d41129840d640e40d41c0e80407081c0c3d0020103041c03000c1c26544100c0b540306c0101e07000350050050303612503200d59080b07aa885003040001d01c41c48900940000703d40200b000410b000e101260382040b801800d60b41c48100d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 155451933 1250 155450683 155450699
    0x3072c01180506120f0708160b030601081e01140103231308070b070c02031002090f0d030201020c010c050414090108030909220614010e040c050f03030417070905061f03050709 77
    0x44505d6204141d500102d1040280385000c1051102000135090300c0c0103003030b240040050603400020a528184054000004d1030840d0764200d090104d049a0b500c10601c0d50c44004a00c0c004000310381440c0868a800750980320040001e00d5008030164096186072282d9402420350030840b011041141c0e401c0007030081d90000f56058039164420b07401540e03262030503081c90041510300a81d160500740490700c108059043c540350302e15002c00d03001c416038448030544aa0300d4124024450260840e59951031f140005003400d43c04001401114416048409408030010030000c8007002841041c8090380100541c0300e26017000c14000b81d00c41e510300380840e401c40b0905114800d201124404441d0700750f41d14190b2501a4503044864013401405000c1d00300d6240c5540c810301d185c50f03240545441034442d0114a1281d81c6c3c20000c0310090600c000d4004900d148040d00c00c0d5581070f550080e000c02504140010340b407810251503900c030401002c0400c0b40327001d4081170141c00500c0017900c2e40041051040000c94164 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 155453183 1250 155451933 155451943
    0x50601021f1a03030f03040515040c03030f120c080910140a050606130806040302060a05160c060204090608010b09132006070f0305070201020f0c0105070605060f03072c0118050612 79
    0x80e0080085075036450145006400d20420504580b42c0000c42e89c1408042220b60742c15078266035050410700000746040744181c600709030341910183c0300e6007450328a2070404d9021160b075004032508400c803409166405207540503203103c1038441040000020018020300d407140c2141c3d0304000c1c00360845182409a0010030568a11038000d10859440501484109581044403a610140034002000181031aa03e01450301448100280c00c10690340040010b000b11541140d0041104080070012103075070342c4c8028060700840b600c41d881880d419000442442c001c0040752003880c1c2c0190030440030a0307601205002c00000c01081500322005210400000b403481d604540d000d4000d480c0c064407080140300091a000141d480c14043e60807842e10f0182c941d80003801c0c0ea030660390107600880d203559004080340c001e491491142e98148100d5000003160910031400c1c03a510200d40c00c01d40b10030382c0c10280100140c8000c2c800c4034200e06214180c4031322a0302d6680180d4001c0350040c001c10342d403580306030264680 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 155454433 1250 155453183 155453197
    0x50907020d081605070308060f211501050d030f030f05100504150608160c080a09030c0801090507030f0302030d1b0f0201090f030f0909140703050601021f1a0303 71
    0xd64020300000d010240c000b000603070b00124000300f19800000c00d600003000b5014901c1d0003400e02c0801030202c2c1541d903510104420303441019012102040e20000041c888170910848042d1074042c00da10103200702041d99046041e14405018100400200e580031a1f07445100500c10003015642e02104a4000131405540e01500544041003045070400c8100300c111446040c8903d00c50105280800c950398101002643c444085034034004134034010001541c0d41f120141e001020704000080c0c541d07043c1e07002043d0205803401810810358a54641a50b80c1c00c0f6030301500050003503407111340200000350802420b2004944a4410740e8104080040100d00383c9484000304401b104034001c200b8603070760b80310210210740e0000780300911001101740c5458036010031141c405030407c41e1070130300d040005000304291001494100802c001c0c07048500450203010f00c05a5030100044e04040104000358030018810180d070082c42c0c501c0140d00b18071140c0c40d006000c40151030365103e403070b00586038103650184086c1040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 155455683 1250 155454433 155454437
    0x13060c020304150c020310050a111b01060e090303010b03151f021c05030609060d0b04150b010c030f270f0821071502070803041211030f0a05090604050907 68
    0x1a14203111a044903000220f031107008100424081d0030140c0e40000e11480e40c0c00300407a00088130b4861511890141100f4524110f01c040005000b00c1c400100740081800030b80039078000c0003442c1d00d031600c4070800f10040d031b03a15034254010702c010300080007904011500880302c845c08462408000d80810500b4503c1d078840c40b6111015850703d40d03040c0e0148440c500c00854000c0641d4900c100c90b10240180c000901100e0003402007400154507a11a110007007a42070b08501c5142403443e15203000982c003080c00d001e80140720700b8121b2254103540254100607600d07505444e038003406080094116030043d82d014025140403010316118030558191000701018028618002d0041400d04008614040e0350420642032942111014203000c2c000700309403081c85a20a1100e00014811035038031000e400380c00c030094282d80000041c401002085035460014514cda1511300b505030480040c10b0f207074042e00c03440a00c145400c0064000301c6104d080180340c0f50300018041801d0584441c04250780030001c03244440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 155456933 1250 155455683 155455687
    0xd060e0601030e0303191d062d01030b04060903210204030c12030e120304180207022715030304090f020406020f07060507080f0c161502060103020306010e13060c0203 73
    0x2155a00d030040c03d007501c2000e4021840c5051203905070307807109011007258508540e148941008520b00884107035490014900310780c40340c1070800d103600d190380041c5104007074070488801050303500201b400010704036500841c0442c40c507038a60310741754041c045801d8118100005582d80303141000f59942c04484000a0b0103005031141c0c21481c0c00800001103411040c1039000e10b49c8000300083c0d002d1588407040c901940d04550030051520201e01e1402a03402030b480b60400381c003080f446a08241e010b4040c183c0203c5900f00d890240046041001810ba40c0410740401e03c0d50002e070b01c00b03c150903a000745400c084c2c1200c4c501980c4008440440d801018075072559600002c0070011554104078001207040310401520450380f5010000e007080c450000c000342424004114500d030044014140c0fa14291284141c5110300a104880440c12440b03000d001c0301c05040c502e00003501480000c0300c034140d13540603004058590030103030702000c00c00d401081841300045105001000440c580903480e00500242c00550b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 155458183 1250 155456933 155456941
    0x408090d14120d0b04050108060a1509020307030c0e10120e030f071101030608030c03041404020405040903030c0305010f0509040f05010e1501060801050909250801090c03061d0a1401020d060e 84
    0x20f415030f0b20750496148100d003450014019040d01251140d001440c0030030000b01c42400c800114100441030384854403107403000c01049802501a045440d1145441d510301200421207010400d000503030b1f410040000e19202020507004001e0352184004800103030882c2c0c107040140c103000c06503910043d01110340910740c125140c4c0381e503094002c1c20042c11a0502440c240105800e1080d503c0c0601d209014201d4092b0340c0034406070700c03282d04441c0030344405007040c000d555043c2409005407004407032000c0041d241c1000024641034401009060741c10050040059442d03684071441c420003850f8007a500c95617900700c50b102c0c43c80c0820000328001c1c042401c00c2c90719803508170080d20090301680300c11f01400c0c05000f005540000030525100c0c03880e490524800c10604803082c8400750a481e0401c800c2d0b503281c02d00b05014007020040420444c0c0c0704110a101e410040307080c5d0683c115807002c5000b40340e4840912000003d001c08031040110040b10001402c12034081400d8041c0c521541c80b0100a4401c07600340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 155459433 1250 155458183 155458207
    0x2070203060117060a02130b121608070c0821040c0603060803030c0301120f060501080102090901050316150e0d0c05030c0f0f012d08090d080408090d1412 68
    0x100c2d0061540951404503050b505a1aa8032124000d01e51541c1e1a400107203189800100c0c1003030405410860040c030745038001e40c0b0003101c000c00242c42a81240100c840f2400c000e5114065030351141c00c442c0d071042c40314500c2e50341e509000d810000c14130b403060780c07140f59000030072000003040c1303100301e00842140e40018500100034044403c183c00640b007a0f0410000c020540902e401100c0c1140e4004100c5802a181070a055510010151006003064184000020304c0340701500074020503070044601101503681c0303104040c3c0d143e0070b07866819070365034a900c02041568108440d031080061642059184044030800241a0b14000761741203441100c494014401070904100d0201c0001d8140d94101c418407034117000a0b0f15400b0715110038100071000c1e140b15442100f88802c0409640041d0b400d048030003200202a005480032544102c50f48562881801c41c00d01c520402405142c000e000c2c0c07464020740e1820300c522041c0825040c0c03026032424101b51500040ac00c064406840800b1a81d0b0311240d159100c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 155460683 1250 155459433 155459443
    0x9030d03150b0a05070b06030c03100204060e03070f090c050705011806241427090d0203040e011e0e090109060b0406030816050c1008100902040b0a032d02070203 71
    0xc03042c496041401295403941d0400115595150407900b004802c0d039070000003a10b4643d0071f800c42505400380700c2035012442400e030003910668426440e420440b00340d100038103588004910480681c0c402c041d03400c1020300c3c625440000788681901d042441c04540d42c035040d00703456545031100000416540404103000c12442076100320041e01c040d4041d02488001d1018503d10580501031141d0b41600900d04c8954a03a002c10240801c0341c12410305184481c0c0c40004c01140458031010140280c4030110300b22840441110150380503a03c1e00c43d016401e000c0300011040480c81514440307904c0b0540880c602400c119120304c940120030000c24030b85010b1070702d40c0c00c0c1c40350015000c1c0106e007820410300020f100b010030394070702403031800c410800e910445c246146010440c90440760010119000e9006041e030040380f0920a07c1c01145030780e04207a54a213000c08a00c654460341c3e4038044148400303a02503205c0d800c8040501490180ca8040354071030060755216541d69036600d0302d07803176001070414214241404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 155461933 1250 155460683 155460689
    0x607080408010b0d0f030807030f06030503030f0903071e023d02010c0210050606040504110a02010e0c090103030c14070609050a150503270d0806180402032109030d0315 74
    0x703400c030032005445d03407680c3c100402504004c0c180134176100058070030742c0b0030780c0045c195a205a0081c004155241041c40d100c3d882514905213070960080056445903000080301c0321310382c0c400d441542e13a485d50032411802c1401c04404aa00c10380c0706c41880d03500d42400440b41000c8400919521b000104a800b0305200c480300096503055904104003c1e05458000c10304409480110501258664501000071014070450300941e80c403926103a03464115030700c5840079040103d043c0d002040345a55080d0403542d62551000d265074405490001400041d10400c059440b140c0301d4201c803050f10103044900c50030b020352604004001072240604000303504c0c140100400034680c03020303000314000300300c3c000510b94800108180b0304d0b0b94981003942d0703009400100e81c08100c940101680c1002426050041913a241a1502481407e941c4400103444c5060261030380559802002004810302110003000c0c0106c4251040d094904203200d8408941c81c03c2c404825000f9281c0c3d80010140982c07070030310440c2184ca030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 155463183 1250 155461933 155461939
    0x30106030516050a18030c090608070608150d03022416051309050606040f0620010c0903021017090d140315040f1803180501020f03030604020c07050607080408010b 72
    0x10703918828168000c000c0750249846440d000c1503844032003460017491145a40000c040c58052000014011802d50200d030aa03440035050b91a22a0f89036022111484207440803211b4404150b0154100c2c44c0c00c2c03e0180c0310b64860700581d840c02150404580c101320300c060140401000d0700c0b040041c07a46200c05800754400d05401d05a0038407807420405010780c16139000d80d1a000b43e440b408a001030307440c01e0658005116070320341c4a101680f48c0394010324168410340c8192610444032038200403d101801888201c0b2556680e1a00003072840d02000124250540c513030080c421a039079008107480382446170a2283c4446001485070241d0420010a126a2003101c003003001c00602c1030142c95440d000307003003040700400c54010404814103000780006082c401c88000044103010303014400c02d508104140104003281000c0252a5030b03900c016a11486040c1303101d1107a800802c00501c00d0b140a501620b00700000408440c5000e44820104042c2d030f1003100c00380c601401c0440e040010349000d018400e22030b4026 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 155464433 1250 155463183 155463211
    0x7050102060a0c09151803060c030507030207030e04050c0f070b01031202070608010b030415020c10060b030601090320040204030b19060303080610020c030d09030b0c03062b15020301060305 83
    0x101e00f006001d69110701a10300e03a61160f011805401e44503504002c00403180d6454901c400381e5070b00e4454010403002c584500440d00301000515410700070310940e882070350952640c0b40b191441500700001041c0050941100180601c02c0307214660501018240040c030403207501d01d0550441c100443c031000411284070031940100000d01071150312440143c1118240e20710f03143c4035251442d00c50a0352502200701d41d002480465a054841c9000680e180010000c90042103c29262405040c951100b2502540454a110301c10800100354956a810600030f120f001000c1d00440400074050b070f031056005950b01098031040c040f9540b919654003025401240003044520714607a0301412034440200150b2140a035419805030150091004044049004040d83e107204284280508090b62500080d101d0301942000900034001d01421240034450040505030a60340a050007400e4008000c40640d00c285111700310f03800510003400810844522450141e140e60602c8002002c4500080600c0c8031043c4c0703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 155465683 1250 155464433 155464451
    0x5031606062c07021903080601111b1509090a020703120b1f1101110a140414040e0f121804140c180a030c08010c050c030d09111207050102060a 63
    0x90060746211807007400c034003000340d0f40c0c2c0314040c0d0600c81c0111303803d0f4031000003400000030140d000d89641d00ca048240c071895000d0300c1444441da540c1e44a440181000c42d1201ca40c66a2031801000c8103840c01c03031542c8402d1500c010701022a52610082e00e84000c0643c0100b070503410140c000c804181041a5400c00b00702c9546c074080003c145096120801c01103400c2c00c80d4a40340d80d440b86510220304d880c00e02c002d20450703001107140d007a2980100d0850300000c00e079040710303540403000c00101c800300d03a0103a9140e02d040d0101c1c01000010010200310508034440d414504051030820f00a100c0080c00c4903c80c107413640303020021044d4000741d103010746100d86d1504000030a2203800100140c3c100d0406580031b501c507002045080ca840710f003145855400040c69400108208081c00e00c081a40c07441d900a00000400d80000d0302c0311b009985502100390014404c0440503c0542c3c0480035550090030780c0d0070030a02d00c10100360270f48881c020140c80e0340c1210205000558040006541280d5120010030409071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 155466933 1250 155465683 155465729
    0x303160638010503060402120405060a0513170d060e07031a010e0303070f060b0301020705160501090302061b0c0d12110c0a0b0304020406050616060c080c0708160503160606 76
    0x34591141c20306100d00072010421613115541a070340807241c49050307520503040900300680c1d180000c4408104141c00e00000a5912071141e682030000c1340d20425801204c1401c9508401c1a00020245c1ca15a9511040040c2644040514034028600340c1c9000440141d102c03001c0d030308110900a07840c1400300088000a0310307280003049030003642e003042d11a100b29041c0d15001c0058180084510360560011540e10b061000108071381000c10f110341d681e9051170743e5030f40054130780d10300c01d201c00781d0b100d881401150242c03442d01006140030182001691a0b0b44138040025000a080000c00da031515543da5103e94510303081062015480098401442c004640e00c002036503549050055161142010000c1011902c4d84c6d000000038207030003000d0076142d40d049030481c4090f40141c10700b074555034185140550900e00800900e406418850551407502c1654ac40700b03401ca034890700705e40248408104420012078000d102521031000700e500a20000c1000341042001c1d58150b411001c0810524446600004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 155468183 1250 155466933 155467031
    0x1060b0d020307030e030a020c091303020613060b041a010201050f01050307060309030e040c0e090f07080412230309070f120f020d0c08010b10080411090603031606 72
    0x908404005a92540c80c62000c8002e410705e8000101640b001146402202e5004030b209078030781c1c03000e80d030110b0281e8480b00d0040155a0385071000d0003503000301d03021804000c1075001d5000c00600500000c41c80d02d40140114044451001000902003014000d0408642c2d0a004030382d0085450358020b03103154100700029880381003900c107200502d80d50741000410140600d0303c542d41010010000c00c41803500e1600070f0708015000c01d2251107400c0c038100041f0141d2106081e1782c000c02069440c24050ba42d15550f140050b44050074503418424403990203505c89410300d1a0038410903560203429141e040481c0510300e800c680b5040400f080c1c103109414044441903403072804845400c82191405c0540e05d0011400604c0c07054400350a04c0c001003004500940150445202c111080e1001c1e80381030540c4c20304490903403041d94002c0080c400c8401a20b141e24105c4d200070380082d00101641d1800c18807480c074400c0c00c00c80440071515541c683d48a0038041400c0e08007040304070020300a45040100d9610900102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 155469433 1250 155468183 155468197
    0x14010f03140c130e0f0108010b0108010f1a040302061605010e0d1e090b0304050d0e01080c030a1509020c160f261011090301060f0b09040506060c0712120201060b 71
    0x21000401e0400030700440d003e0703d1004080941c1c402480c0d007000002241812824051181b144d0f00b41890005d155109600742c030f040307410301c4001c2d030600c50400c5014011048500007020280400740404400b507580c506c010a802100c81c00c0050ba42d020710300c4c0c800d00b940c500c2c0103400c1041d0008000005e030b446c0c0000c419040c18805c005c10700000030030084240d55000c030a401a042006002c420031082140006070241e014184e9141c9203042c03101c0b100115401d040803204059820310500100702400f400c1c0d00f2444c1c1c10300e185125807500d543c482c0d82103000ca07040301010662690221128801030803e0b0180d442c0030303103c2450700c40071140c18a80c1242d200492901e1249200800d075085200400701880040c0303a245a004042c8601c280c4406000c15039000681d4043c402c0d440d10000207540d40380c000d014404c4850702580c0504001c02c0760100700080400070b2801f9001041003003581748020040c0b10040151617441035801c059641c60a082c0241d881d4a50b4402c156807611005101d200003401c103030f80c11 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 155470683 1250 155469433 155469451
    0x21503010b0f1606150303080f01050f040b0307180603200f060c0f0703060515010201050105010f0302070f0204020c060108100c090521010e0f120403020a0b03130c14010f0314 77
    0x91009860040c600c3c1241c094000b0b03001d1407a14400441e00720b545c03d6032070101c0c3d009070b48840300e0383c035501c840100c400828800c207584014078000010040c01d181d04506140800101601c503500d13a201e4800c6600802d035040a10300c0b17903454005000b04000650300803003a103080c00840006040d542c010070003001c0d020418034803820010954064501003000800540e04100060f103003241c1d0341e460040c010700402e42e002800bd103041c00c417100c80d9501c14450141241c03c1651080340e80c00e04101d05a00035403203401c003aa152960000c2a0300541c85900040694081d4640180b0380cad503150004582c18103e604011780c2450741003200e000c800341c0c0d1140c514004d40d1400c44015041d000703210006039900082d443c600511b0750a10103c02400c000108407402d04c20084001e4850044110b5040c1000d40728a000095020040e40c0c4207000c2d3303100b980d02541d4002d070001c41212100c00c060710b07040092882580101c4000c0b074100003408440d40d00200a85400405060500030384203101c044004001008201c014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 155471933 1250 155470683 155470687
    0x30a03020c071203020d080702060601080106031d0a050a03030c02150415090f1406090304080a080307050c12070210080402030a02040c030f0207030206010f0503071d0a09020a080a021503010b0f 85
    0xd0400c0c0203020402c02882090080d588002044c640a52501122039110020a1640700003801c0c060020500907c03542c016510b00400e68208a015002409000d121345030005020403034800700c04003045004102402500100700c07510140c81c0c004d003a110346064100071500f003d0345995035a03081000c50754015074400c2ca0300003081c2004443d50b004110306203002e480f884401181c10f003071100080c00e4080001c1b2003001c1e02e0f40c1b940c0b00100c443d624491489480c0c110340c420803119004c22010400756802c072410303241031752404040c15681440c2c0382200d0080f1181e110b000070702070b013140342c01c2010580d00e0619061a166514040d00000e4481148000207030003207441d0b8490b11a910311943c070030329501d1f0075104115226060703400c000350785a4090080ca002ca01420b000403407249000608501218403024503200d44030155070240c400c4010141000b5143c03a100c0d11880c005076240a1001c016020a2008000480d00d80c01044480e07a2071811040411804000600003200b00340107e4030101d0780042d00035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 155473183 1250 155471933 155471947
    0x1b030111040e0121061103040506060303030121020a0b07150b0f06040b130506130501020601080109020d0233030703200d02090604030b090f15010509040b19050709050307080708030a0302 82
    0x513000b0601600d001302034602d088400d1a048084a01035800703980200e08486250f6034030010300d03541c1d21080c0501f010000e601d1508215050841c0d4041540714400780a8420741c9554243d060b5594200c01006c449035100d0a828040307015031032041c0d001c2841c080300c80741c0c44c429150021031038600ca113000b14050400c0016004601114000c0c804004180281c581580c0d600f0800d40b400c0318445c1806407a00600851000003800391050007550041c68008050001c0c0c001d01c0d40c01c1100c030300000960900550144141a10401c800c800c01e0121103071000c0642e507507481c010700c00804440c0c0c2548248204444005154003080b0341800b0744501c0240c80c100140d580b41c1880010749039004036440100144184001c010141c070340443c2d90001d28020004417000030220014650138038109009154000000c1e500040100307000f058040c0d0089101c4104035407101c4c8241034401030302c13801c50b52080840c0407254204802c0c141004484001c0920740041c00b2036900b06518140c03288102e40d0604100f58000c40c480e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 155474433 1250 155473183 155473229
    0xe01050c031b1b0306041e0213090609030e100c240216030906170705090607120c0c050315060405040804080706090f09050118050702010209031b030111040e01 70
    0x503001d01ea0702641d080707005203041c1e50203aa00e0402c03d140040511449103111100d00300022298021640450003807100b021403400403120a21105040e41d00295501c160b40348100d0031301c9040c4007e80540f00c08130380316400c2e0074040c00200c0d8041e0194000d098407010050030542c0b0507002500d580d44102007510300105480998168642d403403285c05010700c00201108040034041019030080c0c841c1d11211845680e0301c8060b1020000140c15406c94091b8600203801940320781d0041c020542e008040e10304290550300d4031b40d10390290008000110300300d03081c0704080c010300d2040703440244400c030003c00c20a42c03c003a069602d0b05010300b180e8052901c81000c01e0030042050165805803691800b203401c030f280d5940004018200724400c02d0501107510f50080307070364604c03401018141d425030000318600e483c03a044e40302c1c000c0000909000455500b0321130035409075028000004a0f50300340074880791038001b6004040c00c64861401031039100d5420030040004e20713035141d0403904445031001d40c808098906a00c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 155475683 1250 155474433 155474437
    0x108070e01141204060f06030c06081017030711040b0a1406040b13060f1403040206030a1e0209030f030301030f020108070512070c11190b1606091406090a02010e01050c03 75
    0x10280005001c150350f500c11800c094080e1290b1701030401070090b001c406e00c0c40001c4031a94080030b860800201c005100f1503001d20600b98004649840d403410165689410094400b41001c0c508036a40001450344148003040d1051401c50204407000c01000c01c1407030029602c00301a20800e10205286c0e80c881002d50f6902c004d0320028110350301c0c0aa644c801409410700c51400300e0252102058078440c0c0c0d111442c3c0b1858240003410b10101213545580c44030b800300515504002d050441654442c000c01c1148a1401001d0035240107064016072070311000d80425051170103040c40021240e04c180010070228504401100f42c058080c2410341403034480d07007400c6031103108204501d501003040304203100d9070643c00b049111640d401480e4100c0c4243c61041000490000c941c00500100c0d1208814040000300000411028001c0041081c4100003940e845003615150071003507440481002c0c0c584c00000c0c00b8030203903501010a101030140c000c01da0340040c0c041d1054052080c100040403031240441d807000c01c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 155476933 1250 155475683 155475707
    0xe07050702180c0d0c02120a0323070518040902040614010f0305090303010509061c11150a021e0a02030105010305030d0b03030403120c03050904050906010303270504020f091302040306050609060108070e01 90
    0x141e041d558403620701c0060007800f144d050b500f58080990003100d441c000ad00d5142405082103075100c1d07103000160401850000950303110a98480d03510040500181d50b2881034000503c00020192010320f40c000c005403901c11042c44020a26040c07000300b040040c00402221305603201240c501f5420b0b1690804905600200e000d030380800304000209409028042c06c0000450008132030040120782d03a1500041e150007925000d50242e4462181b0085000550103400c00113400a003ca80c0c404002d500080d003500d50a034401d4407140c0000030034000484540c05801003d075015001107240c01e103540d41c0e0310060005d81c3c13032803001c01c6901c0c002e8808261086003199040d0800a105000b1402e01100c1162640e100b84421004184001c1f0400482c000c108000751a94a240200451080c82c00052202a6022104d409020071f8100010f83c00740e81d4034261902703030f850003202c0140c545041d4039040e01216405480107110780c0c4c080f42001100da0f408580c0303651160f03884c0380c01001001003000603036202241003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 155478183 1250 155476933 155476963
    0x2403021201150e06031b100c051c0801050a0501050a080a0203070c060524040b1810090c020f0c0307120201030209030f01110702090f04020102060c130e07050702180c0d0c02 76
    0x10b540014240d040ca8041406040110300792560080301c0310482e6001c0d05200038440c1c019101d40e541c1c0c3c00590141c18004240340c05001074039025540066101c094120b080c82d01c00104400c2d00043c8110f040c51450480030746001c2c01c01d00d24002d407404010382510002440b00507403613000400282c10501c2017030a146003d621540a01c002c6c00d0072070052100d003021440a240c105450322200005142130b00032003080c0d5401030718081115008414219114200400c0c850700009080030004003c442c510072000d4441d020350103800440040000613051180000a080c800d5101d40024007128900182c09d00603560309090041e6545403c0700400d0a1140340c8521900c1c65103002d01d4182a584250000d00086100b2200304005a64101da1700345203400641e4080d0041e03010900060500300d20000420410100608881d0000c0c2d5940407042109801c6800c100064808039a484c00c6007410f4000f100f200c00061a034200a25016641444500a0450312030100f0307190319110301254000d10100c010383c5028 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 155479433 1250 155478183 155478221
    0x3020105031821070b07090f17150a0501030311150c031f09060518090a080313120e04050a05072c040911030f0f0c090a0615122403021201 61
    0x5501d003c00b09401100c0181d85800800001919807840740802405484100c5400c0185606001d0503403000009000440103a01c511007445402d05000c0060034402e45883c44085070030741c118a4020035003c403010a00c090b80c1c1c0b0442d14000542c04e6130301c0300c0d9445400381c0716440e10f03696110403070002c50040d000c048078013070032501010840d4806600a13409440c0240c0c2c000d140082545503007208140704454003841500090011800070340d850f40110f400c40040101d032001030100b03889060611002d105504042041d504141d9860f00707050007440c1e48190382c0442001315190100c80900500c0274a0703030040102034031001c98900c2c0305003c101079041120207403080102c403845242c1211642ca9081703d031032081c400c1062080d4141c05c00079400000303000b5000903168822030300b001c3c0841a00090190302041d51100404604124444c0551002c528640e49000c01014812004411075120ba09100c01048410f15040e05e031103459211a0205c0b0b078180c0780442c004994400403030040041c0301c1c03030064030201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 155480683 1250 155479433 155479483
    0x20904060b15090a0312050405190e070309050d0c0222090606050a06052209050702010b0a06020606010905120309041d011b0804020418150212010f030201050318 71
    0x20651156112072400d4940b081440950a044869405115001540810108020305c0001d490480580d01c11b0b2082c2041400d00e0384138000901c1201e099201514071141031207081211200c6840440d03044012400d00b0003400c1560303140c0584030b0b5441000c01c2c052100c040800310441d15881140c0316020480665a12858042c3c1e19481c040c113402842910106d0604a0106561504503604005c0322201d490302c5140c08000807440c10341d2844802e200c080d490810305c00140311f0005004480c0303d03041e00c2c0d00015801084004000d42d26401e90815411540301c40200030440c0d801c2002042501c00450350107403540c440103041072440c411004526005130406140b40000c11240b407800c1020440341d0001d000307000008070b8000304840d2403181c0800095400c00440c0c0136091035030002e07440410715500d2044140311516401940d8992881c0401507940c00900e000d0301c100d10002c41405014000c00312b24001e46907400080c42d0780405400c1c8041d02c2d10144492040703003c00c0048201e030b0140342c509a10400300c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 155481933 1250 155480683 155480693
    0x9050f06151503010602070512010908040608040b0a1103012d06051201080f0a030f020c0409031e03020301031502091801030503070c09020703092919020705031603110d020904 77
    0xa50021814010a01c02c821120304842c0441a80d040c2c549540c02000c0c194648400c200054044550200c502d5580c0e44030b12020641d24070092000d40910f07128580c0505051400f0840d84000405508596103001e80940d41300120388116070450b2464640943c864401036000b581c10306d000b0940c1c411309a40d2110001e009508a07001c0c00c0b8007a03203000715100603a6145401c5032259452a202d00071034201c0d00300701300043e004036103400b002030851044410030b0f00c044010030704842194500703401040e03000355140c5407900303070b03c1582c08545507502d0f080d4255495544d444080304000100502e1071500800e41d001e49454a024002902d5050b007442001e559480c02d103591240c0c0329031401e81e1018030160f00420300a14034001c4a904541c5681e03541041361428003980108100c448180b6a82440ca4081d10307031034144a40581941108540c145001002219000e40390403800d6005030302030703002800d16074040b4007500050411a500210020140042280020740100308994000d40c840c007008148800c0c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 155483183 1250 155481933 155481961
    0x1902041e060305060a0e04080a0c080c1c02010213142202030a060f05030a02010f030b06042d0e01090b03011409010e060105030c100e042315060f04060309050f06 71
    0x400c1030310b003009551070b000e01348414008180500c09402c1c3d40380011030001208980180132030802403800c0740b400450f45d92600c0155114058204c400e5001d80480980c010040c00d040c2201c0703501d030000b1132404607120700b11088441603110301c141d0b603041c03601002e106888040b07801c010141c84080349420000860307d140e0007500156043c02026240c540c01080c042000803516007a600014001d1940c40341030303401110084000d01c0d02c00c0c201038503602042c0b01a200c010140c4064200c2d001481000c5040711200705079004019101040041c101c40e00f0013030b0314121369400d41918041c1101203450001d14006c40c3c0034040e264040444a002101000001a019407061003400840015150280d0382c9400701680c0b2111200000d81c001c12155158481600484007a44402c0c405071010031080421190114004070724160400a8a402020800e8138062136035410144c52080311032034208000040c0c84079544c02507004060070f040d0b680d0782880501038100109100c5001220840d03803d45010490f4a10321 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 155484433 1250 155483183 155483189
    0x40f0e090106210c090908030c0d0f0c11010f06121704030807030306180603031d030c100201020c06011e030204111303110111030304051510030c06080601080109020702091902041e 79
    0x322103138100c003182800c91805005982500b29041c0c50564403007008141c040d6001080c5520f4540d600c0140c0ca6244200303016002c2c1d01403e640b103120188001d80a12400c0d140d100e415061018500a000e2020b14998000f081240e50010021050121248251000b80c0b280c0e41000d80300003030210380c3c5400c15605800a6090b9410314060070126101d01c084041501c100d400005c000c60342017110700750701c0425025074034940400101213407000115070000c01d100841c40c1040b0030050350002421f50003030381c1c200402801402120809140c0b4928404101c03408611f40c00024461610341c1ca406c45601001c90079254030005c031114a54465550b458150180844030110382d02049034040403100400020081c1c03442290410054088091858249400000000d010400b030402002010000c102c108080c0c5000d002d179525901c4040c2070080014102c008140c0c4805400c0c0c0c0100900300c0140c6a0101d61500010035541041003080c840140b603001e402103400590309080c0c0d00c2c0703885e040085000c03a20412 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 155485683 1250 155484433 155484443
    0x41d04020406090b010c02040209032d150135060a0f1b05030f100b07080304020103050f09101a0d110f180103080f0702041406030f03040f0e09010621 66
    0x702c0c0b035460108009540e0200030803030124207900140400341c20030350014804540000c041c1d40040081150390905082910620314007101119410b4030200c0007042030003c81505071501b40100e6252407600d90082e030041328500c0c45184200011804030308409000c00050000c1000c0e2016032400101031401031566581580d51141001c0c01e180e04444940c5503020024010b0341c43d28919035880541d00c02114008e00b01e10b03c0303498080800a2f103604484042c01c080c511030303105560b41c0e0405000040581d040a0300e0300c840101716905001e942200000c40381e1040e1681074000c0f40814086002c5140100c0804100750010f013021808030400c4501560400c40c808100c903c2495003800c0c0d000c0c4400b1241d036200e4112071103020001070011070b1082c005007044a103060304161400c0741e0390b030110b010782d0b07402c0c602d0280900d03040051000d0b92505200c040750030b40102008508007445c1a40c45a803188151149181c2d0041c071341d000c501030240a4100c0c0000d4194502c3d580100320440d14042c25180301c220064031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 155486933 1250 155485683 155485691
    0x1020706080705070227190f1a010e0a050a08011d0105010501050406181802032d0604090201020a02090c0406020f0d0906031a030a06060503010b0402030f011703041d040204 76
    0x503105005424541c080c045659805091561a40c28420805c0e0403070304140c000c44420900e400d00c484004c602c948a155504a48511200b0b0b4103244002d84800003020144641410a4a8180b1a02516001c2041c400340303054000c501154003c914203041d660030103500310020041c0425555415005010340c1051164008032501004400303600b01c0300280266400a0703010482007210345d100d0701d03005440002d40c8582c0360f60f4623551081c64012021554070700080c02c0d00801003003070440181540c10600030101d1400115200e075a0100801c2c0c0d0340051041e44101d6460001c10f066901c00c00c420030007194064541c0300c20b4200001d50644a8106202c0c4a00510a050b00c030303c00200b010404000036090350b101e10001905190040d8060200078100450369a01440c00c0070035658204114170301c10380619070009860742000245425181c4000241c0e000e80d0040052101280c525050641100d049140450300c80886104485c214455a031100340141c850024001186607070321115800355208a90401c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 155488183 1250 155486933 155486939
    0x50d0c080702090414100902090a330501090501021605150903010e0a0b0105060c0a03030b130f05071202070209060603070c050d081009050103080d05060406080d02100e0105040b070c0c1a0702010207 87
    0x10b1f50000328000350428074030f0010480007007a513000300802e409841f0342e080c3d845403000780d80b0030000312405203403580c0700d2070300340400c800e503040f51044001d040203101500c600301c2e003024640444883c0d4400c040c0a09081021801c412b01030b00207a440c4400c1c001c0081c010844102a510350326031140006803070130748112000080524100040301d10051000019145032442a141036004004040c0425005000395030a00844601d6200d2007150a04485c03002809060180b8000e0680d40c403041c07801e1000384100140805a61603002e11341e13000c0c60464501c0d540b42c0d00c5003000c9950761b180c110000c4c000e210344120300c0202504902035a03ca6010110010446a900c1f500c1405840c028070000e44140010451507140d2116a00036a80c481c1d005007020400c0350381c4165a83ca00942ca440c100010780200b03040d1828820316000c1c400360710010000901c014201038641c00c8140c000501b102007800300c01301780ca2040045500d407010040c20b4030040840d121100c004001025800268100d005000d800d2003c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 155489433 1250 155488183 155488213
    0x30d0203070512070201090e04061b02060613020f090612010e0906060109050409033605030c01080f13020307030303060501110109030f0e190b07030f0c050d0c080702090414 76
    0x103030728002d41210041080312001210300071150301c0f24034140e0412a5403200440d010a42c1442c1502641c4540000503420b2044070b24440d025601804800454001c0c20501015944000000d050071084103070060343c0e503220481c00042441403045154004801203903490031aa00300140d42e04881100f0315a90407580c59032101916404203e401c140401d07904a428003840c00c4c1580611100343c0f281c24402c483c540101e105c11014540c0f4600362089101884400c400601c3ea2040a801004245c0007003e64002400000c0e0003080700500301009080000300080341703000c007007480d4543c294029007507039102610780c02c00802400140c0601400309510f441884805001442102c20a0790107a80c2c08400f50520304084400e0307410900e9650340100e850044810751402c1e410842d0050500c044407070b50b11911454054103494515803440207020100307407160081100030865a0250549180040c1e441501d480c2082850181c0100079411404010800003000b02c1c208442c0b8a1440c210221550303248032450b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 155490683 1250 155489433 155489437
    0x2c1002010908040e0c0c0a11040e030702030a031b1502040e01050904050d1407060e0f07061805091305061e0109020f0405090c0c0d0c020103060f0503210f0414030d0203 74
    0x800000c800c001c00c22540d5450030b0f40710b800c0240c8080003890404e1b898480b0303107440301669080d190340075492a103444600d00b600c0381074007644c0c41c50095420901079800203619040c8580010341402102e164081c5a4000200320081c4581d200301c4014032508212213480c02074001b4003607240000820707000030800d89041048076105641c86030040407200e24200003181e6030391030102c524114003018031401c0c001079443d000310f606900c000ca004003041c0c403080003c01d14000b4181d20600074800300c08510b503c03003001d01e400072054a800b5289540c09d92500700115184600b900b0001d8550b004050600a030b2498508d104407001e2484001c4174900c0e41c0301d200072000c0348030302e41030171012000c108402c0050b41001c088503a40206001d07801402c003c5005440d6003800c45041c41440044d10600300d00045681510034a80580b0314110720003016420400400e5550900e0703860150742c5021020380c400402c4803601103070682c41141c040030b40c68035551a5582c04121641c144a803090191301c0f0000801440002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 155491933 1250 155490683 155490701
    0x160b070b060402040311040915021602030c0607081207020a080a030c0f030b010c061109030604150c030207020a030f150c05092119051006060816110c102c100201 71
    0x6c001004c0440140410000744903048089400300020b100403002e1300c002c0d1001d445c1031088011003208243c0d2510415051241030112588145814050000811990016180f9140f003a0030780303208984075030b0000e07031a00e80001d00040011a000458071542981500488031814040e11403901c000112201074003034070007640d0b0840c0002c0001038210040313034684d0444205900c405c044c2c01e190031840c1c0f01190030058204c0d02515000c03115401d519041c0405e10461006220034038085042030402d50004885a00900c000703800c6181d642481c0d414403044904111040440b600200700040c603040c4090180d41040e2782040c440d203424030030450a02c40803100410300c54120b0010340345110044d0101c8099540b041002d555601c12040141483c0c1c045118a0019044544610303c00340307441c1810410958421401e00200140d901b03902615000019001c400c526049444501480702c019040300c48403030300310103103441180074800d0b03003035212044e8415202480140c44490490045090a078280c0d80808 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 155493183 1250 155491933 155491943
    0x30c051e06070f050903070303020106061205061e01020c090f060111010203160810120302010203060a0b0a09050f0f041802011e080a0f0612110f01020d0e060a02160b070b0604020403 80
    0x10001442e0b4511482c2a14424502410010306000304000860b01c0d0210580040700980c0d90b900e0180209600014802100000240240514a04040802d4101218003821890f084001c086104182c7c000e012440003110050040000c034506074011001c442c2050b00c041d8046217071a4115a03040300c0600840e1702c103240b2802d80c240402000306048840c2c02005021100d40140d0b080c020404c5d459911811281d070f40207900250b12824500c04008142215501004c081c2000304456054642c1000c40082100c0c41142c031b0754070b80703401c0c2c3c4c020441d80c003855240c840d841703860007080d007018001c0d00c001070200314002e030384480c0081100d608581c020031018688201190038400000c200030001c0c0c21000c0208001400843c103169200d8a005103140d01d40c0f421242c1c0340d42980415098200718013203181c1c1d418244010211400018405032503040e40500b924041c210020381c9004c424000c0020030880c000d08450484081c1e6a002d0b00d2081e078110040407109484944003094051501c0e0007510203607a000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 155494433 1250 155493183 155493193
    0x10080c0105030a0f050a14090c060412030c0b090325050607030c050c01020403030206091002120f0402030114090a1b06050a0c0804170607090806100905150301020d02120906130f0c05030a030c051e 86
    0x1021440b184515820302c10dc1c100206051310704005107102c07052500445198008684483c840307054044005010101e0f4290140c4005203900824800603996030059820b04001420f4440000c0449003482140300c0c160581d800040d0000030180d00040e61f51055000506403641c4003203a0300400140e20517141d00c40305500895020030b00300b05d140d520540c0c010344003c000041015400e48124085a8100e0740e10f4050741015401000307201d021020a00d1101804000c54142c0b0700f481c40140003030081d040b1010070003810351040010000e0450803035000d07006c5504040300692143c003400f6078845049030918001603110800080786000080e4032409102d4108107030030505d007442a0031005041c01800c22840a846952235a00790f1420f100410025100c0f000260f0340d0118210441c81d141c4018101c0d981c2ca9002d0030411800180d4440050180350b408528901d154001c3d0400da006d220075030f040356a0500841c503000e020190043c102c0050148908241c0b5080307101d10300c0e40e980d2240310340c401d01d0030b640003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 155495683 1250 155494433 155494439
    0x6090b03010b04170a021c021306030b18070b03010909140c03070e0a090b01060923060f0702011e09031101032d140103150510080c0105030a0f050a14090c0604 70
    0x401540c9181138240300b00f1913048001d29000030381c0030b924910489010007806c00e010310660500e440207158039502c1410a001d01495640c071592544001030942c01300715108440c0d230606410910003e0000e0421100140d201d5846485260017003280200840b024010008090100c40000c01c0b80081010001c000e040300a01d041c00342c840c03885000b07000b00226542c0ba00c41c500000d645421103800381005680b03806240b81041c002860303000b2170003030015050034540030015166903034030f08540c040685003100540794040b510050b214080e00c0314944002014000e070401200e43d20010410449005525140c40400308074010f504555540007141004910411019411058010821203000503e02e0000d032001030b46220715603005080e00304451007106a0030000d4a000c1e40d0294503040080766840701d40c484d2401040302d590304036005442d4148000030000130700422190b03008a1070340100010034000ca2510051a10040c00c0b24001020013504040c0450b120b04000284401081382c040c00c10703480d142c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 155496933 1250 155495683 155495699
    0x10f0b04030f080d020304030c031d09152b0210080c1b03040f0b07060c0e060a0c0501140a0b0102010c05032701090203031204030816050a050d11040f06090b03010b04 73
    0x400b80c60240c60701c990030000c9401190692001310702c524001c2d81d45403c0540d4074917006001e6100b01c207100d541c0140c00801018035a4400d0301540e0002c0395a00c2480e1400b4030ba0003c10004202c3c6007038454103103803030314030300f034001d01c51410441c0c05501c2101d040342c9101000005443c3e02505580740c0d107900d84103000c4000f41c2d60141541080018410048a050aa0304c0b11385550720109900550303007a8038045001c41c00c20003c3d014030740000c2c485050082c1c1c0c15030014081003031070040a045504100c5203a05003400c2c080290b001200318045404007010f6450940300c9000a400e81c00a12401503281c0364a20003c2d51051041d68080c44190070000c03402c2c0e655884408010540f0501d030426556141c0e84800140e8042000700b025540445044001d85410b08000d888024000d1414010038118003441c01c50030780c400119800e8890b82d0130a56151211090080f00809202c5107100c1c3c110341c009004200d01045181010454002780d50380030000d42c0b9050034030a280401e204684142900303100500c4152 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 155498183 1250 155496933 155496953
    0xf03011b09290703030603052a030312220605070504051e0a0603020a02030d06030f051b0f04020313140105010f0f05100c0305130b04060306050409020109060e0102030408030c0304080105010f0b0403 87
    0x3d03009190103e2900c0c1c894607400e05202e40b991607164001e85141210100c030a540c812a412820203c01440c202085103d4141000100170260036284900b08507005109a1641c514410b642d00440c0800503460041c0e4041d1196009004451040d000f14009850300070004446100340318001e80a10159843d03c601a0040c0d004903e142c0250f02051003203a2007078032148a40b000550040c100102d45415a050441c24861107586616145089145814150f1100c41562103050801d86005942e03079540c82d43d441044421501c014281c4074082c2c0100404001504000d050b5103002c000c1880380340d500c01400101d04903910907282c2040b00c95035111089030203070100113249400390a115141a07425861030600d40700e607800588a402c40804e0500a01d6858407400001d01401d98003080761450303980018110340c18520503002000303214070502c03c0701e920a005980003040d010084a4880e00c12809154407a0806e0003400c05962801e8000945920740d50f510500701c521080c0e0b45480c1606648a0150030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 155499433 1250 155498183 155498197
    0x80d2c010503091e0102090a05120a020108040819021507020c0d0602031b0403150f0c0c020f03030415030506120607051b1c110c0108010b04090207020f03011b0929 72
    0x980501c13106241141180000d5040031807100d000145c1c0e80010a041080c07180040e08401e025045d00388000060b1100050a5038229409080c01c1c0b0042d46d851400500da440780e60807481038000845031440c20301d83c000030901345504101c50442010b60700c44004985d00d04101c00101c2c3e10043c0c01241801182c1203600a540100c03040400040281c1822001110750740954411205501611484601200d0503c039000500e105007a00740002120f0340002842003402c47c02c040d2180414001c11015582c081003140c0c0100b0400785c48010018a00c403025000304400ca03005070262400701c40802150344042902132080003142c907000d051141084250b05401d071900100c0615111b410b02444250903400c91a00030314000382d5808040d080300150b0b40d424402080302d8a410b1080303000062150100f241c0542c1c080d12407a40e40140c56901900001e081c001c21440041c2d00b6500e801010f0994003200c0394050a2459184c441e030ac1990307034861130b038404005851843d100c81880d24004480b240d50000060210f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 155500683 1250 155499433 155499451
    0x30f020409050109030f300209040e060a1d0c031c030e0613050d030903090b07030207031b050306160c0b0c1308010e0106080708060622020301080d2c010503 69
    0xc079205aa400742160385082d000e8010441120050840755840f0804c180c0304011096028541110286981c50f9001c070b0383d50b01000507401040f0b074107458499600840c00c0040300340c111205400c1542c604001049000c1040640700b25290080340034100c0000d0703541c0b030410040c005003030300e15800c58446100c900403075001f001c2540740e400d81d45861600700303e01d5020f0350314036018034400d000720f141851400c10280e03414414581000320388404207800a20700300441d6240d9650942e00d00440c27904a0070003800d07800c000c0000181d0250a910403103440e40030010786074107404448003501c8060714907000d008400300460001e040d224040000842c4054110b810030a010b400c0d50034045c2c50f805007071480c0515085907801e40c0d5601a18000003809000302401401010054220241013504003500c0d848000e003100d004283c400c0380d80b054041c07030300d06d40107886000007030448d1a561180310164941d40404d0200c80000c409800c0101282000c1c3c101c070721082850545030300003449070030065546400c01403007040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 155501933 1250 155500683 155500691
    0x309060c071815090902210709050103080a0206090a08030c0a050c010c020f120901080a02031f030305040303030c0504051305090f0a0b01030b0115080135010f0515010504030f0204 79
    0x40194a03110b040038907000c40700e07020903d410001c038101400040366105aa1081c00e00d403404000d81c03912004040200e490200840c5031035000002685030061a07071000d1907403854440000b040c489030101031300c650000c56081e503410352144488a6036a2019550141444004102080740c800d10107000b4400c0600c0d5040241c142805113009600311000c0f0411f0901607041202e14200b903200501c015840358038400300b03003414007601100080402100500c48020140d00001040c0d00382080d0b50003071b101c02d00030400800c1e065203e1a0050094110b4807041300442c0c2000070344d80d00c3d54010030948090365800303403607455030f085208a80c030041e180c041c00d820803e0050030011003a0504c2801890b040900449052429500d940f400c6e03600e002050744000300c0d020000103600c20280c0e00031240d0381181c00700300d20043c0c8504d001050b00054411008210b442e4411040107604504c01034204981c030b806040b0b410409655204101d1b40cbc04012480b1190020704100010300001c1e44030030300c4415503400a00006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 155503183 1250 155501933 155501939
    0x703111203040509012c0a0b040501270509070b0a09030309060c0f120c0230060403020a031d130e0d0c0b0106210504030302121614070318090e070609080309060c07 72
    0x40000701041c0c88487c015a00d1703400000305070600d4000c440c01042648032103c26a0f6018101001c0c01c52200b0032280696101d0700031031800c0c281009110040c250311300f1131654461b0188809000d038401c0d880210007060304a800000c2c882c1c085c02c1000c00d0070341c00001032400a03031aa40c90b5a00703444040000001c1c429900e44000c05a01c0d00c844800e811405020102c0140484003010320740004403903721a1650b2120081000080d408203d61100903414240f1041260140900c03d02c0000410805904520082c04007444074000f0780060140c844440d050310306031608031b24111070710241c1290203008001c10800403c0850300c10102c1c060221201035090a00d03988410300b00040e254169002e40009070081416410180b001f000d06400410101100c1d407090100d980c060421220b0010707030801150302003924014103004640c403081c0301140d0800351010680369161403004010b440d13010300b01403088042c00705609006140140644500000460806c541101001181d50094800700500d0240700c0c800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 155504433 1250 155503183 155503259
    0x2100c0225140d0809040e10090303020d0b06070b010b030711070807050306010b120f1b0c070609061418060c06070e011e0c020918070311120304050901 67
    0x20450a0401c0916108014502200c42d10b550000a010a01c40e00d603007000c0b203000070b46a41c21207894101c00e680100d810440b00c4400c03401c1941041d0701d04038180c18a5090005c0691550081210b0b1450380401c02501c40107406012150103a01c2e0018030b041002001400511000405180c0c00040c900c1c04440750508030b0000c42c10981a9404801d01d580034900610941c0750510007030b4007410b10245401c0c14074808821090810740040c2505c600e240740c901c04109542007100e603108417400711300700c25a9110101024a641c2d00351610804002035024900400c540b4401c0440000e0750802001c3c00f4100f010502102d5111582c011041c2e51080e820030184812100a0120780d03c10758181d10341c40c1c4562114000503001c08d03220169410b0440c03802420510181d00300c403002000580544000c2c0f940d640390301c003410000c00d0b40c1301d1081080c454494000100000446540040c080a0f41c003001c040310111a580e030743e4050f502625074008900401809054101206d820610700e01585c4503903c0c2008400c9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 155505683 1250 155504433 155504473
    0x708070e04061220040e030f03060d02180702100b01020a11121516020a0b0406090222020d1b0801121703010b0d0b012a0c050301020d1d060702100c02 66
    0x1c0340c004d1045101051190b1110380b01c400d83d80704c199824406002002c0b0711035168400c81c07514a1802d500840030804a07203598031109a2207600ce410380a103138a0364003000340440c03011507840c001441481403034000c0c50760502a02803200410b0b0010318560101d540e64900001181d030070310749c01c040d0702c1d0941d9042d0343c010000d40c0c243c1544040c1c0301d9a1401c1c01805054104990004032095601150044001605c1c0100090380710fa004200040d82c409075200045e0380151041c41a19201d00c2d241a0301e03201803030b6038014a01c140715009c081000c0c0d09202c2c003400340d150b4111001000310388480010040b943c20019151602071188005403000501c00640f12010b800a030406c0c03030328540c0851200c42c000001d110f01a4907031024284100c00c04c0c0b020078104c0d5000c0400b80c0b42c4c0d00600707008200a04104198410314081c0400400035500c50b185400c11000034190650511000703002c210300300100c2c610110704940071f0b16941d4040c15110048404080107084000c1c80c0c04118450390074041d050240c6160 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 155506933 1250 155505683 155505719
    0x2304020f030a0207020a0e0403140c010e0709060f050901050609040506030307140105060108070305041515080703050a0303110a080a090c091d0d0e0d110102070e0a020c070e0708070e0406 82
    0x4006031580d4240c0144000c80445800032040c0c174514406100200e60004400e4050402c1c940d612b40d5a0140403607802d000d00740415404070944505d62010070020760a0300036074292404110341c0100f5607520360030403c548800b880741940210007044040c94604068200c686c2c03001e0080c0440c1d1421510390b031213980314a02c03402100602c0e50340f5400c1c02900d40c1c0c8024515005000c2d407070140084e0030a9140c510461941c0f241e040f4040b60750740d201500160030803c81c00000e04260068945003662410115220a40311504a0010303140001c00d480c2c1400720340598250711801d1b50395007190307a41c1c0340c40701008000030401a81c4a208090000440d00e200340100505542401c800c00d21700c2850184185c5403c15401c40d51051115003a801040c580703c00144034111500401041481800300c00140c0c05c009443d040341c050125000308100c03c0700501e40080c06000790b07540c1181c510310350782c0c40320028001c1d050301c4e01030003e08140b0200c0d1100e44070740054020410300600c00200780e81d0390303282c40240182d054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 155508183 1250 155506933 155506951
    0x90d0b0108010915020a1d031c03061502010c08010e04081213050c030c182a070c050105030f0c0705151504050603121603050903240a062304020f03 65
    0x200503c0400801c1d11441150406181c1c0540c1800c81c0180b0203440d202460b03039101007100000c00010a560340410066034540890504101854001e800c010054040d900980c0301a08440940c1c1d08600d1051140003000b40c9a07940b030001d1039080c0000c0914507080604180d0b07040509203c06c0c0d251940c4226002e000e601c8000d10300d102c3ca8680c0c0340c520700308401820414401e4002c0300d4000603988078510801c0140802c110382d01401d90324080c1d01600205209032564038000b82d01040582504a44002c0004600988019034001e903240011600e520084403450080c22155000c28007070b015180c0581542071040e000c0e910040f402104600b46040b04880030f000c2c00000f03848402c6242010303c01c2e940c102000350090032107041810324002c4603104150400c20200382800f030002c01e05100314260342000c00000c0c2910064000c100c3d00194008079120044201c0c410140842c881802500c604011581002c81019440354515000c16100d103802c20b06a40082d020040c0c3e52912040e0390065200d8800c403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 155509433 1250 155508183 155508191
    0x307120504030c09060e100302100f020a060603030e1507150903110f01052a04031b09140601091401020a080a030207060204030c031b03080f160503030910050709061202090d0b010801 80
    0x103c0c0702c0300d0040320b020f0900c487c41201a0000e00140e2920b03000e0324881c440f50700304101900d030600b10403032800f5895100500200e181c0f910220805503c0010303000110400c540000303202511100360145031280480050051207071804800c0c40b0415500b000c2c1c165402800c0150284202da038171141032070010b8141c4c1c250382e552a070400403092040a550544044a038103141a410b4281a410580e449140070207840611008503440190707400c0e44990b005403150034014882c0803400c00e1104000038082d0396040c085404608003068070400c44d00c0602103648164018620780b8469102da01843e40400110302c1015001c0140e42c02040d101e00007000194480c0f046038401038910b0410449070354002404150404000c2010000315005105803002012000c2d401591550340c10b030803540c080d1121600414501020041188018001c2803403a01004c1070356050046030f40701c180855407000c02d8000d9001042d070903c0c9440b00c80406c0c3d8041c2400a01c050101c294480c80d030f0b210009070310000d910001e09607442d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 155510683 1250 155509433 155509439
    0x3030b0406060c050307060b0a15021b01080609040336030c1208071e021201050405010e010e07090225080a0e01090e01030204050613050c0405210307120504030c0906 73
    0x440c1c4114002003041c0e1920181120096440c0b0342c9074807031498042d00c6031340c6a44043e00d0f9582d070101180000c3c00d4003880e0440300d0340401c04c040d4641104000710f0300103494156190100c0e50040240c1d910444000303007540e04556603690140c0b4500c14002029a88628098000c41c42c1c41c45503000100c110882451484a2031544c64243d40710070441e0041001080801c400c0400510319a09940074194400f030300390714a1390300d8414980180e5403014040c0d488403000c0d0280c00101d006510003401103005600070310400c0c184000990a8031f00896a200281e44090f50402c0704e0403440d809000186504100d191a00e901802c0700e00b030300d25007141c080e40ca142c0d00080380f4040507000502080640300c20b08213020480c5c47e04001030942e03101444080d0080b91141c0c005005030f40c0f07817001f0803000003c6040400c03880c00c011044150319040390242900421000342030f052405843c080740d4028aa0304402075141c030603640d660488500440103141c0900c14280b1000c80001e040301c44800c007a00c5000c07000540185 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 155511933 1250 155510683 155510689
    0xa050105100e060a0602030a2a0c09050a050c27040c0f0f11030304021203090d03050408070509010b0307050c070f0b1306030513060b01020304050913030806180609060609060703030b 80
    0x303003c1c040500c118821078013000017980200030760b07001e51140e040c6454400c00c050084002c41803081041616a140c0790146001c01c045e0381c0350340d03094a24884d801c01c01c079511810401c1c01c0b04c00030b0b5240c05009106001c408230300c803941100d2035034100505040198482c5044040b400f52140740d01454049200482d80030a003d41c07100d801d10090800d803500c070007094000c95500352079110180010340144141c02011540500420840300300c0e6401030320000b5003600b141001002034215005e108454010040c000919161010b0f016040e100c2044005156860b40002a95076030b000c80c40d01c440302e00504400044000480340390b00010800c123501c06a465180130101614107183d900a170082c1480d2205204c8030b540c00307010280c02c01d940070340c00203a547c0e903450050f859170003142c0c010340d84034402204209010140c1904180030520a0f1640c05558440b2000c001d011441d603200d04003421041e100182052030040c840700d41012001d4441890070b042c05003c160a40d002c10010f40c00b00380c0b0780010240c503003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 155513183 1250 155511933 155511959
    0x409021906110d080114011e02010911190909210e10081e07051c020903070905280605120d0801050f0114180d030221041d090a05010510 60
    0xc50680054005100a500f01074581001030080b0f82c109042038050048a90184100281121400c2122280001c0b1040020b018140d03603c41100c010414461841c6d0504140c000c2c034058410181d4030011b91401d01c901d00c001452006000e03a40d500c0d02100c43d2284102c2103034452941019940e55031021800c000c00e10000c810b00c4d081081c10407580808000220b800001c9004545000d144482c80c280c4a6450846080c0140b4401d550b0320354154080e010a00040c0d801043c18400070303410b403150720381e45143d00c504035201100c0d1400b108a04403500c55110300c69040045415401880020302262100042007030941042e044a507540d00c040071380440d082d0429843d43c0181011210013100310315410008148030f01094080e9400140400c1e80f07414945849000652024041c2141e055501581402590788224500985150080e09400b40c43c0000303100403102610284c441c0304e034440401c84d40342814243c000b086600c282c022a0080c40c0003d81c00e018443c000c004010398503080c00e080507403815900c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 155514433 1250 155513183 155513207
    0x12030e060a08220606171605150f0f0301030804030218011503180b07210606090e040816050c0f0103050f06090403020a060c0201060e0901020a1d0409021906 69
    0x20101800180300740350340248250307400940b0092640c580002d03c6148000741000c0e40d4010311007400c10001084801022649102030000c0701c0c11119001d030340010718020410903001d2030b60030070048159a00e07042c4003940100464075801d11400e20b019002144c008d030f0360300281c004580d0340c1e034002010000d524224a140803a0341c000352210401b545464042207c06542020040074107403244d582588082c518018100d48640000700c5006134035000c94010031660011211184c2c030b2303641840f080c1c2c25084901c01c0006541850701c8005007107013481401821810010320031100b180080041c907c075001c0c007003c003501940c460801400411203007401c01c0715036640c948900d410545008100094402420041904240103407583c080580302d07030904034240424548090030590403e150314804032781c158000c20403680d0058034407046444811489090748141c0c001030300001c600310030252440c4900c80341c0d001481727002000010156907542c08035942e02d00c01003190304100d03460801040b155420805074015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 155515683 1250 155514433 155514439
    0x509070906080d0f120b030102040b030a0e07030b0703020f0c0a11040c0203070206030c07030507020603130507060f050717190801080d0c050d050a030207150b0a0f08030f0c03070c12030e 82
    0x310781e241c00500d004120a01c04c01003103040c0e50a00d070886117075400703e200600f003c2e0095540e140c0341c804000c80c507402070315030b060b4441c5003007062032610801080100650344d00a00b0300603d9100e91070300300c0281d0040500e0325070b41442040700da84150410455404041d21500103003d0300c0c50f100081001300d0b0007204010095410411101c8016510002103a51105003501020345840450800b00d549020b00080203420800010034003940c103010a0b10f51000700d00c140104c0d01260b8807240c00720356510001c1d280b040030a200784010710014403a2034294850b802100c01c2242804c9110380300c007442440041c0103101003041040180400c12061001480000d003d0501040c40303117055481c165a10b115400c090b08000e8040f61514506200c0e80440301003e40002c0d841a0940d02c000c03012008113200c184407481010041d40001d04180034600e1203003150741110182d0704041400d040011280d128120184040c0000c001c04000140d04910401c06840b104100e5034007030410340b40107000d560510b0081c501c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 155516933 1250 155515683 155515693
    0x60507180e042003120f0f0a05120106030b010c0308061f031d0f1519020d0204090c111e0a0b07020d08010b0403110d1104060303230c0c0904080d050907090608 70
    0xc1562800100c6607005c034122800660755120fa1a002e14480c055032240440b50f85001a409500c00e62000160803180d2001000b40384a0340d940c40103038221404451041d021562071010440400e0042d01203507400600601403601048100c1a0045464200b40c025800700c0e9880300c40720200402c0d04d000c104e41d206900010981007440c4099207585230107000c0079200d00000707407000854038408a10031550000c808102991908640c00046002e500b050058000c203e2a050aa4401ca0711441d03082004d0b07a007d00250901c0455000c800041121441c0803a242c6d01c10003000c0c0c8002001e004101344074016039801342c600c4002142e0300501350b600607445041c100c0c1081c03200344003240706200200000720301120060300c8801985405900d100410064550091400c0c100106058105004a240c071001c5101c80c9010103100e01185402e01039200314041561250600c25902d040420300a50858003601c5568200340d0811080c0040d14000c641200d0143c00548042011807044c0c000c01003e0700914001d81 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 155518183 1250 155516933 155516993
    0x2508010f0308070302070e01090c030b01051e03130f060905070e04240e010c02060106020106050105071a0402040e0d02010e07050904110d0606050d0c030b0901020406020307060507180e04 82
    0x1008940c4900010340a00700000e03808040500802c111002860708410341c441541e51350305408000c1c40c0b14901c100101e404c06c100041150312a030102c40200486241c00780700d5a40c04040c3c0403840d00700520524541d41001d40041c081051414080100362240901250344003161828909025990f0300a03040303514158203000018624480343c1c202074010360f414510303030155150300b4000382110344c8811000c3c0d460414001400382c0d0220307001e070686003070750024418030b0741c1c034030044409219480000d4603001c81540420400b090300c1c2c0c403094200b80000c1000c69110a622602800c040c0c1001d80c1c100035130b55a071810117407454280889070060000b110701880380d240544400403148101d0f0403448c440c24003600c400e0100300855220001800000e049072420889501d803544544070180020307a0b80d002483d000800c40340050088606a4040da8091030400c01d099403014050300d4003500d85018040c42c241c032990510310203211000202600b038181040c0b42411f00f040e840c0c1e48154162102030040110b488 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 155519433 1250 155518183 155518199
    0x712021801030f0f0c150c05010b031b040e01090b0c030703050105030111030601030e0a08030108010f050a0e190602090603070503040b071d010e010311031018090c0b090414250801 79
    0x740400540100701c12282c8005172070002c04141c0c0a0300964245064800311400d10ba9005103010b100c644185d0080000403040030400d0b40d1108950700002000c6113204507014039081680040000c0c6080100114180c9540d0b6548459018121405410341e0800310800c400c03903a05028407401080241c0080000d942001f101001d50705c001000e0505050300c40c082031900201c00c0082218083d0800c3c8070301d4417541c5901c000d40c042c00007050702e10445820030020070008156441954080760900d00285100b07070002d501203482100791ba0007503075038030ba0034080e030002ca4403400e00441c40307a001683c88a54920701450400b425041c080c0005c010003080e003000ca0165502c1e10007000d010307102401c1105943c3c185a004802501c030440d016045034201200303001900d010701c60700005440389410b0288000d17517400d0441c811141910b4002c3c1414080b00020080d41c40d075000148444c110103030000c41c11708031401c08890420810f80380c0aa440300142122152000100780700c500c18140c42c5480c64081d45880d0710 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 155520683 1250 155519433 155519453
    0x20d020d08040f0204050414011103071d0a030605271011180405060301090f0501090309061419050403020405070c170405150310080601140102120301050904030c0212071202180103 79
    0x3c000d000715510300200c0c007800032081c3c0c00340c010072070b5038000e01507050098808a5290400d0783d0200c04540e007003407440d41d10b0781030104410402e6030180801a15518580302d000140c00090070140c0341c000f0f031100003405080b050a4001205c400200104130f4064106626401c413035070300100c628028800c0c0a18000311044009180480c0011540850180c41e44030002c1c2c01850002030040000b0300a020300420000f064100700c0c0581e010380c851908841da900b0342500c020344c081c02030802e00c91007007142d0b0014032030401c3d1620051026180040c00c003903e950201c1c2c01ca580a83c1c01e100800e00c94000d0b2000c10868800c080b03040a040920303a400d061900d40440ca010400c0740800380c0c000c5000c00007600040c00701d0f050360010407482d0f046032036950f0340720071060b078a460035102d15006000f040034001507001300300c048074103c8002400540c0c1070f039281d4800301e61a04a1503412a0701460354101214030040030013091010704a038400b1001d42c22018030401181041e554038800d000244040104007003681440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 155521933 1250 155520683 155520713
    0x30b03030d09031202250507120507050a09020310060c03180e09010b0303090a0e040204110406090e060a05010906110708100606180521031303030c03030b0306010302060a0c05010605060a020d020d0804 88
    0x8141d9a00c646e4500642080c815400c582021900c003c01c041c2440800100d2804232503054809100854941c025401a0b00c0308489201303083e00e11f84400c10100b4400d840c925a600e001e4a0b00d9030003d2040300d41d003040c8807002c0d40841d01e1000d103042400314540082c8280034a07003a003100114601070f032260210380c068030a4894800c40c022140005020741d01c0e1034200c001211030b0f2841c2542d0307454541c1005072210340207004006d91509200005800303400c08140040c103035030058503410712861400000303c5e40c415682641003500c0c010b4000c0010211410800280e100c41d9134000441d107941040d00c014004041c2c00701c00307030704120611002c000a4803200d03280418104401400b031642840c10843c00d144cc45004410038080d41e01c038100006155104651410091013035030284100d00b42ca0017010754901c0c0070300010394007070002c10507401d41c44e01030394406010320f100d5000404d41998840c0011003941040c034071100540c020590040e01c0300d40c107000150794060141070000c01c500b0305845034084040080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 155523183 1250 155521933 155521987
    0x220509070e0103150b03040b0f04111018140117011a0a020f03160b1501020c041d060f01030b070f05030a09030302040306020a0309050105090307020609090601030b03030d09031202 79
    0x1081d01c1c1c2564400c0d082082e40c0c1d1114248000d642e603891802c02d00f076900807101503494030700b1140403c40074000945043d0003149c101d03a0840700320310101c0421141e94aa03010710818442503030420a0804081e007100c0d4010325010f075038500a403520f40009000803120954009c840542ea80042c04002c4014401000030b0b100d40b0031050319000036a0041e4580001c110f404074440c400400c581101034259411240d50f03600c0380e400003074103461b4a10610090100d2022181c00f503080b101c10902c0c40e04040c2e000b03100001642e681c0f1010a003c1a0000f4184041924401610203030280188140200080000d030031002d549000c41e441801590006c0440c000501510129a15040a582450702c2a01079401030764005400715070b28480f8040280082180c1c04040300c035035003050005a84c4000100540e03602c42e4010b440030b407901d501e81040001c40e1000424003818103a6454980340e094504201034041ca00c240100066502c3c40381c01d014007880220584102c0407801045a410b0b4082c0074460001084842 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 155524433 1250 155523183 155523197
    0x18150909020307030219060e060a1b03180803030405010c0203130e1b04150906050a0c1401060305030a0522050604030b19020307020a0b0a05010b04030206030a0b060f22050907 77
    0x81c40043d0800425034000ba5211080490400009040414803001c417031203900c40c8118000840c1c103100b190300035a01e2210104500d1000c0c3c44a003090300c4000182c442c4030340380003400ca2820140c0f02554464542111070654800300030002082000d1180d607500381c069000550812601c10544002c01c901d40c0a400300160702400403955074400640305101c1c10099035400b94689440ba4207100c601e0751039101b9000010100c1a000034000d01417812940001240e5807044140302c21a2510f8904428400104c401340d96100c1c000000720301e00340701078550380c5c642c0d82d17404c0e55510805000320340b03505d40c000c190100608001c40030040350795250100c0d0110f0358007c41c02700305907440c1c4085401558414003004003141c000400c0004407580030a84000e503611408203003003582c6480d41c4800454400b4000c00300c40c010100400d0001d480c002000d503a00884a0300003103840303412900840d000e1740003030403100003600d0046001942c0c41c40d1603400112400920080000072454180068075011019106405200744 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 155525683 1250 155524433 155524451
    0x303070f020f030703080f0a060803040504020c0c060c0102090108011d070e0409122003030610032d060311090402220e0f0a0512070f030e01050d09050106181509 71
    0xe001c14180c0b50150000d07070f82c5512150030003030301c00c0c04101e50780d65000c00c1403030000b10060441c1c422031007515203080c0118241414082400000c0d8044c518a400394401c05140784c82554071a070003800b02c42c50100001d42c8840b1502d001407c041c4060300100c00119500d14030801543c0240c2a950340011249031000382a581400414000c200c41070018001e0b24410140c10782c0c00c0d8000c01000b0014a0702081d80321201201d915a0392240400e40e40c0c4c907840660042e01c000c03018441d4124161070300c0302a40154003108403003800c0c010500701001d201000d5407501000c00c1400581c2c0100300d65000b0039250364590b0b01d02070b80016601703080d03080c0b1115001183c109801e8013030910762111640700200c004031840d4008202c000307039075041c2082c0c080380d1620a4200c0032002040010a42e481c01d42d001d0070715900c3c0b005a543c2989d00c0f40d41c001070703181040010310000e0940100b038091035812900031400041c41a05110903801d1881000c0c0c0504e1110781801150b1008410480e1484102d400c1c40d907000480b050307 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 155526933 1250 155525683 155525687
    0x40513061e1202060f0405210610030c170115080c040c03020a020a0611090301020d0902130b06030723160c05010e0117040507030503071b0e13060b0d060f060602011109030303070f 79
    0x1d150030140d0080c482200362154610041e5008d01c032011207500710360050380c4480ea07220300c0040030300000305400c0700d6000c10404008403580d01000e40800d80004102115940c0102c00700300841d5111406591040080601500b01441016034100d0146419860a0701400380690758449449005140c1a503804a007031240c5a00000d40e10350000040c0295910065924004050712440342d059110350050b102c1c418a005440c8280c4a4240c0c014281c1ca00f5070b9100102600d4040042a17270028210010142c01031080c018001070281c1086143c5501900d406400c08403a10f07405078000505000b1101d03400e01140c0c0e000882041c0780c080c000003048403980c441c07a10f035041c01c0c2c00b0b5100500902c4041036240410005860400c003582650780940a06d070b40e2903055504c5010150f40c6503030005015040800829055001058035040c00b800c0c404000d14140d80c0d20088513a803000e8036080ba83d03204020b0220340c3e8203001782c525201c0454255410f1418100001b5200d102c0501264103100c0000c004081180c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 155528183 1250 155526933 155526937
    0x712050304060e0f010c030605040605090112050102090a06050a0807030c27050415081006150e04090b0901051501020708070618030b0c07110405040506071103040513061e1202060f 79
    0x800f03107109681c060101c40009501800d03040078180d001c80d0902c9008102c034245403240c901121002004040641d03e460035407403006c0c107040811740f00365400b00710703100e402e450b80a8060020006c950b40c10395140c00300380d401852014094480d80406d41410340d010b42032940140ba03071b8503040c8400c400f006200541018510840c51f0342d44440d070054245103080c3c4808442c1d80903981203074441803d8440d0408119032110458205015100300d8055444998030041d00c1a02c3d504a042009400000c001d51103858807465180203e660b034005a4554003008202001c40c0301650054900f0b000034511141000d074865102c514a0084408010114000604180000324098000c5030030150700c4000d810028010003c55100d0320b016154812550100c54541c1064803503a03219030b4100c0c000e0812601d030740c90201c0b1410032174280c540c1c03148028400402c06d59203030403240a04200c07145c40051004e2803d860b0006412044000c20361880c01003100f00f1003a15124407242140758120f59680c0e441c070090065103814 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 155529433 1250 155528183 155528201
    0x2061311061b030a0201110a09030615051804020301060f0e010e0c0f0a3f09060b2106070206040203370b1b0c0a0204020304020609032b05071205030406 67
    0x1c2c841c1c26200498140d030100003014004d100c3d500074002001c0d8a8080ca050740304244c0d410000821110007000860201d5201c02c02208003041c2c10300c7d08650301c8002034641e120a9070301448949001c002c3c0021450b0901c14800100003941d0783c1800c0711310701701c507661904805220b20f140c01000c100029070003039100000c0307584044070880801d4440300152801080e00003081541603d086500c01040c2c0f6030510004000c1002c0201d0b41c280c4210104800e415020300803648086400d0307504d440079030000d903035140040d28141c00003c280c0a0a0303500c002d105403504001800f00019504078030213200c00742c0c03404100c4003400302521070a01c07802142070088a0502d403101c00c0e54101c418040101104000c0d1441001780030b40000e4200c549101d0401125600c688207000286215600210700c140050900343c01965000c6e000429250030500f9090129007003212003000c02d00ca0032034400d0a10844402001880d5070402d9510340f10742400d6540c1d45410b02844c5d60500300041c84804800107040002c80d402c10190 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 155530683 1250 155529433 155529457
    0x809060403061e140610050d090602030114090a0207080909070e06070b09010506121b0a0e09011b030e030a0c11030d0f020d0509100e0d05010213060f0206131106 71
    0x30001d0212482103880301c440c0030700c10086040c14400d0200139161403281d400f4180003804d4540c02c0d0741180d000d56003580050000200b00e0f4484e00780c040410950710180d802014442d03014048103114004004101c5001403084990314414010203000c40e403440305646004001b40ca5224560b15111703001c2c0d030031000c6a440c2d154030505c00035004003040403900e1120f005088400c001d02c0f06440c0d0808001130a01c110080b094290320200f81c0000700741c580c00c0200040100502080b4219440d00036030500c07c80304540c2001103a4650040c5110354020f1031002580d50030341d24003081001c0328849000c1e00c0c0e110315811401006403400c0d045091002a02c002041c0c0580101121080e0105200142c02075503101403610150080c0b0500c04140c070b02030001c0307400724040280208400c44074520f0503141c0500d03502016411070400280c200003d0005d00c001c140305001045807280107450700e01c00606908083c0251745c00c64001400b4040e84541d04142411001c0d400750300300800300342c17042c0452110b024503140c64070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 155531933 1250 155530683 155530691
    0x71b0905010902121e0601030f0b040f0204051203160b060f0402070f03030e120d0c02030c120910090518040501020d02160b010f0806220b010303080709090e0307080906040306 77
    0x2c08a4207540146110302080118111a6031245d00c146605140c003040700c032007150908001352941d88240e000d000030416002e00010407012901c0403c00701c9a88880c01210168002400c0c0b0040c50942041103801c0c0120700154a8448003842c09103d180103001c004085882ca0004962140e85080400785030f00d0015000319280c1d00c1508001d80040100d12065000c2447e140030b11000c00000b044054411307040540d01403520070241c211000a090200e102000c40c0000d01594052203004d010500c500d00040c900d0a0300da007000c000700300c400f980b034400450034403003a03080402240d1070b01c7d030125031715007400101d00714540e507181003840c064400e4213080711940e840060921507080c034940038440814058880b0302d41036a01c600364100f080e182402050300390341c8100c001070900c2c8400070003040010340c00786210304c00f480181d4658241030f20a8000b1000b041c00402000103640c0e01c88070004c001c0840c14402d0003180c242d02c0b007a50f2a880344d52005003c2d1034000803000c40985482088030700940c7e000100700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 155533183 1250 155531933 155531939
    0x606090524010207080a0807020315010e01060206060904021c062408010f0902060403020d03090513021c0b0105030a1503020603090106080d02010c080708040f1212060509010b071b090501 82
    0x40c0c03840030110350031400707081070105054042d4400035030702c0b00362664600102004001c50300c2e40165600910f01c120783c144201804003403084060035600c0d0003001c20240380030389075042100107070800c0802003209004036000e80810000daa02c0301c160503082045110944600011401c05d90042c00043c01000b01c0e081c403080200c2e49220b9801000d208a03030050000708070902d08030440b1000c2e0b40c04604040d6021380300344001c0c405854962010a0f860f40301e8141a04110b94035008984280c00c0c00350038051203640480c0b00f4144044500c0b01090401141108200096a40d0000382507404045d04164096039909054400780010b2440f84010710b400030f204640303914181c40603e0203880079004d200e0140c01200c07801e550740d600500950418681a03210191240e45072101200c1303920b030003002550758221003880301c0003081c1040c24102008110346d403200030035401810344d581070300e505174861401003090f0720042003000210016540b500740c0c0b05c0203904d01c403086001481641c0629400640403545064000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 155534433 1250 155533183 155533201
    0xc1503020c06180d0c0b0105040b01051c1406010e0108010b0309012306031e030909070e040216110a0803030a0906020403080319060e0108031b070909030e0a080303060d0f06060905 79
    0x100c3c12400a00031200713500c0180800321503012a184000707040d015140e0040c0610b1070b040c0c1120307003080018900641006020f124481e00243d01e01e00c0500000d684891210f03e1703425403400c4540c008002e090040d1030320072010008000e01d0b030502c80c0140700c400c0440407030f031100c0b8290401c1141050354807000c1c00009a0303095694400e1800c0e10241c0c4039200d00100c4e20b1440107a0312841c0750020030031010b50705000141d420f100e03181d4001030a1800708444451800c00380e980c2c03071025010b0030341d61201c1c44000c09524034004a880040c00d0000344030f1110104100080200041260b038081c0302210045800e100ca850100e02a000700e0300700804a12001c003c100102e121b27036450b28101818079406010b883d554100e62403000d5000e01440c0c100d40c20400802c40c600c034102011880d1014003c00315030742140c0c2c403ca908201d90010400f207000580e100e0303d15100b445d00c0c8614030090205040a0352030341c01c10b140010004190900000c0001c4980c0210005110740c1d0741c0044020300300001c041c4420700d026520 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 155535683 1250 155534433 155534461
    0x90d110a0b0a1809180b040203010b150304060501080c03070501031a030a031206090204050f1e04020d090b241009030b0a0203060102010e070602060c0c030f070f0203190c1503020c06 80
    0x10030303078005400600001d50b01c1540c5c0141c50078500c04020740450f0b582e00361209018150002c0c0180c0e05503403580402d0049445118481c4010b64454684540301d0409140c40010750b9010391042006602004610303025543c0890100b0882d0784c2401c00207800c054020b0071201c035100e500e03081a8140107210025081c5608203428400d14543c626040003000d803903411042c00c80c000c5005650300001d04401150141c18402c2c1d4000039016000040480301c4a000000390980e4045000e00840685403205032003003010700d820f9943c0058003804c0c4501d00030714900349542c0c103420007005148103c5114000403d180d010718250009180c07c5040b0802c0ca00d007c4480c040070798010781f90340c2c0c019172800400d0b05030440045000c0041d104164007502142d1501400303400360350480600d04605000401c00142d168142c18010b004c2e941c884c45003001c49498a00425052400e40740e041c1200e180c0b038141140c0003500c0000200306845004e20394050945060004900074090490000c0040c407401c0300780150101c590340d13 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 155536933 1250 155535683 155535707
    0x30403052508070303020a030f060b2a0a03050f0c150103230d0315090e06071407050601050907050910110105151507020d0b100f0b090d110a0b0a 64
    0xa0300711019203440120151844140001034407505081c4040310010348a9002084401c00514001c07801050f00c1520004880c003e5000d51b01000000890803e0b24008070807015402030038054580301e5030a801c401c9038071000080300050030002e0026544050007103003c183c9a50383c440c1000c0310060440a842c600a0050a0005031905c50880703004094070111000d81003203281005020300440341d8034440c1500034194075000d01c005000c06040200c0c0c00b008a218004a84031070500401e600e0070300001c00f13807900304010030a8031801020400c1c407001c201c0002c0c0241c1111420741d08042299280c800844440c0503051040781c0c071000749040c210b8141e520a80000c040e03151b0030002c012a844490440d411041e19401c40c0746c000b895000c1d408803a40840002e4528140045c002801415190344c441610300d6007114281502e03000d501062040074003220100700540011201c0f1441c14540d03800150070720b001e061000b08122551005400b290311156000001010403010707844c0c607603034070f00300191400c03120341 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 155538183 1250 155536933 155536957
    0x2070b0708070210021e03090f0406050604060c031b08090405060603010503070e0405010204080607050307090e100b0304050c030d0e0f09010501090b070c05060304031e0201060302010909021e03040305 88
    0x101020888540050444641a5101000e1440d18000e03900348103d1008691101c0c2c00e40c0910b9071120703031245814002034032141c46078014540d604628001c001044110240082c013803494401e041c406900c0303140c2110180d400300e04252081000c1494104e4031121091741150100c03150030000c03800c200315900a011003003001c23101030146503280010b00c03940380024465260325510902c810040901c0c0d5012198104c4c0c011000589040e880d108420324290003998050006180081003194144c2d004103690f0107040c0a0707196945605001068105240c11070007016070401c800008142040350401190320300c482e0103825204445d10902d0080c020403070b078001c41401044030704031012440c81e0401125040c0c070816182c503a025030810710300445a4114160403102c81c4010940828280da80001031485188640d64840804030380405229100d24540f04d45815a03040070420705c0140e070000e000d58140e65038008010780354103107610410942d807040301c5602c0031b421001040c4014036500000800310f180e066 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 155539433 1250 155538183 155538193
    0x1602011709060c0d0e0d11150c0f180a060509010314093708030414010c0e1306030204020403060b0306060102030414040b01090302190303031b0c0602032208030702 72
    0x218401141650444540c0c00700e40200c800100300001c404050100c2d00d1040700e0000e0018020b004003032404d1442c4621101186180d0b0070400b046008200c400c1c1299040800d4520358104030b44100058000c40104807050300c4007040150090400418002c0200c0000703200d445103130354a41c00a800ca922500169000030f0800c0c90700e000341c0d01039801050241c690354005024030b80c00b00700d03005081d01807521040c0c20400d140050000c088408040070001500031420ba076030383e0074149801104100e4500d403d20059040030941840b83e0341015805410000c02e90f49070400070900c84142c0300401d81904001c0d4402d01c003280c04030500142c0d90120440500030303021500251107400040e6581d0085116606012140709680902d5051980244420f0740317041c100242100c0d1658005100101100103551000302d11080400a143c4e00d4003030518020035a541c4540055038040006041d10001c03070016040d260000042a050000c3d04146003103498015042c042152840c900700b07805500c280d9169005100b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 155540683 1250 155539433 155539457
    0xe101d01030908040b030c0f0f0901030507030c1e120e03180409020901091109041b09050a0f0302190806070918110d0f0603061d060108070807030b1506160201 70
    0x34441d80c0c0c035098100f810f1906061910002103001d9200422030000040248642c0c0c4044502a0207000c0e02d1329000340c0c1e2500c8030344e10740006003218030042c469030400d800d0008006100360024482c503950300021050561003030a004042d62444504015907002c2e0340361070740c1a120b41d003001c8054603e4001822038025146c0c0702e20204000c1c0c600c1040c0c0a0345c8060644010481240950b01015183d60700d40041c1e42000085c07400a001c035000c0709680340d203107402c0d9100142c00305da0140481e40078102c1110515100c41c18100c03012540703011808024014110005840031080015510300c0061920368100e0343e0924120f04010320f503030454030890b401c01c952005101c1183d85503014405110010490550400c00c0d0042c9510281c5282c0802441e540d0355203402201040b0640203010a082c402c91203403816500400c1d4103803805030140e0095205401101c000e000310040031601d0000c407900a15003403130b82c0d203801140505412190010135070101d4001108540f10502c0a0043d07280e9000f40c030799110a001c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 155541933 1250 155540683 155540687
    0xf06090109140f0c190308030a05070e0a0e0106050a0c1e0515070203030a021b0a081e03060f01030518031c0507051303120c0807050303150303070506160e101d01 71
    0xc46400c041103039000355404d42090b007013107000c030401d4245100d46184102e0390380e262000303507070300a460040f021521282000010fa07001035107000041001d0762440e51841c5404c2015504840600890742007003000521850a80d03c50075210a2a6400499802c05100c0b40c5d003000b000314110342c80c2160030740102240c04003500c00c4034074003d00c1102250060f41c40c1d0740d9a1040c1a0080d0b000c0340301101e10720055401e2a038441c608020110842d803103590301e29503e00d50029161034084980f030701d00001d40b07000c02c02c21100d134403100c2c08103000398420b00303010400d51202090421403c0d203010940c1c00e20303c008244003c400390184100075a14003114410042070303c8400d001c4516105945030f81c0c1e2820f14042041002824503000401d00b1407252510510301451a0f540c1400c40e0302c0342c001a6516803000c001c0c80111103004d02c00050304c0108030002d41c0b5040042c0d03079107526410004c12003910389164040030303510070b07000d00c0f1014200b1400030300440790107210300c1004c2c1c10a449690310305000c1088001d101e841354 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 155543183 1250 155541933 155541943
    0x31090506011106070e012f0c03010905030f0904110f03040209010e131203060801020a050702030105150d060b03030904020703030f050c03190b040e010c0504030516030b060603090f0609010914 84
    0x80580006000f070f0b65503040054070052003010b2164100300384001c400c000010070301e03003984030b8025030188000814414440c0c0752506510110707440c40ba0f490074111000151000048690880840c00c02d907840b1003050000030010030006120080301322000a401352200700500082d0321803482228030406c540d0701c4542c184540c5201f2100c1c084035101d03060b9808082090700c0201030810500c1c0ca00800c869480c3e50100d400da80003800450041407001c1280d0085143c28000d0542c03201c1d5101400e201884503000280b9480803c07080508100da0311207829200d902e046c001c07107061201c0584290354a40461800800504007981c41c00e4100c1d240c44085100c2c00100c0007182d004801990100408803101b014040c01801d00c400d5450f80540c0e50907408018023802e000c1d10140040ba82c0341d083d11246182402c2e420000b20881c05144d600350458180002070f425440315400003000c1d50490746a0741c80c601c84900e8164502d9560410303200d031600304003c2030070542007418803170f10440c110503014000507100c40d50b030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 155544433 1250 155543183 155543207
    0xb07030305090105060108060409020d1b0315140c0a090905070e03010c0f05090609030a170415050702010f0c1a090106170a0b040303050403140d0c0e031507053109050601 75
    0x6840320010848c01d1a080c0c01013400c140c0010320100003500980da41d007012a03405000480030f0310390024104240003405d0401e8249500d01d040070300000a46040c40548101c000306026403a40001c154022003501c6414113070098407020200300700c02c0c20404005041c050b00224207070700c03c3d82400c017114075240c8130f0120001401c500341c0720310b4241401041003100c150811440300f40c01d0302c205013000000c21070444040c0d60b00e2030382c21803072035450307040024108078600c0c280c50174002e11608209080041c1d03170211a41070110310501e0450f4068400d480c008076001f907180418600280c070101841401c00040d8040d108a0724010201e909062000c0105500d0700781d1070b6000340100d149a800100448c0c00b980145078024860700d071407512845003450840090f00030590b20454141c0d5480742c55981a0450005400c581085000380396503c40c00025060048006000340c04200e07001c2070b55603103c3c0ea0f09444150008420107480d410304504c1016041c0b4071030a110304811a400c3c44042491540908070042503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 155545683 1250 155544433 155544437
    0x708030a03021801170c030603030c15090c0d080301030f170a030c02010c0c032a080a090302010e3f0106060201050405070e04020d12140403030215011a1602041103010b070303050901050601 83
    0x3176588080000c031660704002e00c51f9815000030003504000100600240c50411118140f0010500380414442d1a1810383c0002d03d016800d11341c1e020b40452008025681145d6020080121141700752502004080c0d41c1c66041d50101300201d40d000e10745806400c01d1171a101305500804c08d0550310801102c004a410b00081e0204004410b101c000d080b07840b480000070b201101a100590f5041d276a49003065012400d908000340f0214420300440d80d001d510180908811100701182c0d01c0050030b8000030004201c0c0c2c00800b06803103085c0d02c041a0300d90355018a0307802030000070420b40d9a60300000c0d028040466045400d030051200220b512949500c0c014011500640350f500c1c40d1215641d0b0801d02044102554140411080220061f030b1b488001400914425400b400c4003806941070010080c406800c5a12400c0081d0302031000e402c10413003903c2da01c02a642c403481011840b4004900180a425860100302d10004004a0003204000040c5a51403095400304091350314201c04078200d41c010707240e182c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 155546933 1250 155545683 155545727
    0x509070509240f0903032a060702240402010c02210f0604030207050111100f0e060f07020c0f0109090903081f03021c0204020d050106020609010f06120b04050708030a03021801 77
    0x3c0360100c207001a24a00c40d018040f2440c1012030010341112a0002c081e14180500801750f48006103424400356802070000c1c001071090014996103000030840700010f050810411034001425607100e01450103030142c01628960149031981c0750185400c0d04c079038490507148100d010100000000151180c0b08681641c09441901e08000c01100d0b001100034140556102e018884222503485d40704030a104028640c00041544000c03410342d0521780c005044c20704114296080051240c0c0100da55418880219070101c8951240300c01030b1072001d1280c004110346864a410340c2c0400d40c010302414003601a02548050740384154012100450007070000075000084421140000c2502e4100520500d03c0144050f081403401c0b1603000031039609034005d0300143c0c814014807003862000c0c0302e10403540d044254184104c03030078207040c64034a455000b002024101540005028404144401e602610344542540c1c1e88104101009020750400c030252000c070380c0350a4080d0580d40c021941d402070800070300c3c0014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 155548183 1250 155546933 155546947
    0xc1520060c030907090c020a03030b0301021201090c0309060e07050109050621130609050d0807050906090f0301020c07030c1406040e0621030f07151e090606050907050924 75
    0x480340741c00c090f00b2400588255800071403a07001d40c3c022680702e401a6402840100120304000f8181d82d04e04d10769070300992040000c9656455230880c403505568141c7c20100d207a042d1020128014880b010021f8200d5150210f101d90001000c141a01151800d98031404031a44840401403e4440c4141c1e40d00010007200140002d00035111465502286d21847c210b0082c0307480d19031600761074079184103c40507004103801000c115080340303100c1d4001d40140f41c0642820726060200c0c0542c400c90218604c40c800710388081021b5a42501143c010843d41c01c2070f690260303901d282076048060240902603800300c0321135042d00713a070400c5c00c142c40031550002542c081680b552428001c001a16610700034000e001d80e83d9101c0300d03020800c010721a001e9103a81090355080c060412000e400c0b02c5034001c2e1101d40c20080340311003004c68200c03100816840c2c80000a103030070321481c21a00403c119404260072010203020804000e4110014002c2030b0010755001010740c50a8200180c1d0f02101c0403400e10010040c0420 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 155549433 1250 155548183 155548201
    0x30b090102160615151206080d09090b1903080c01050901021921110c01180302060103020105130f03030f0f0f1b0303090b0108011e02090306060603090a0c152006 71
    0x108030800075116201c1d6245d1510aa0441c1e0708aa42c07200f008921440d140c480c010b00a80706000092500c0230140c43c0100c01242d0041014a440c881c0106083d101c15a902d190b80e41e26420741c40c41c0241e07a41c0c0003410341e40e038585038440740c00ca045420002e5180000003160350206008440781644104c03024440b40803040000d680081000520030082011105940c020205d01d114a503030100c420480552144c140702201400c5d40c0785c2040c507c1030200e02c00c00600002ea00002e6071410b4a909003130168071405801c2c80c541007202554425001c808844d01c3c00020706400107402031f014003082c0c1d0f502262602900054600342070641d0702c540001c11701c2c1d9143e1400e410581d0350745c003800e01c03c1ca008104203420b07480341d40c118402030700081500d0b5076506213644084582074038000c189221900540c1042c00a400094880701c0040c07016000c1d07500040007030071847c002e2001c1002280c5c010003843d203203078480038020a840040340c3c840d400701c2da00f010381d05000900364604041501c41503008024641d184499 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 155550683 1250 155549433 155549441
    0x80106090e180c030a0804090c0507050a110616030e090a14150301020c0a050d0e0909030412060608010203040c06030b03010b130f1d03091905010206060d020325030b0901021606 78
    0x5142ca40224101602560fa0030710038040c40b2405406e4650722241441c5042c003c49800382c0d4580c0500c1000c0051200141c000301d02c12401d60b4102c2e64441c118080d00000c2111489000412403140e07022020b80030405401890140304a43c0a032012900b60f51010b40c800c04a07440819651051406140041c0800002c442540c0840001400260820913050000c030310340503081a0032a200e40043c2100d90010394080c03401052348004407800480b074201082e09a40301c1c4900d0107000c00b46203030b101441d414012039400a1004110301c800031540c0340382c6803d02400200b01c0f801010002414003003015039a29050054100c00c140c020000e101e03e5403002d12640040041c400400031080e1101c200e032200e04801d100c0c00003800e03d484043e56a0780100020003086003076940c0000b03041940a4402e001c982d9001171503540c44402a00d00b200343c4400d600020780f60441000041402e411001e800e003800342080943c12041340c0c441c1c0c2da0001680c8a504c4102d0a0b4040c011803440040307400d0820001064842d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 155551933 1250 155550683 155550721
    0x70c0605091906020301211a0603120712021b010e041802120a030e04022a011409070315021206060d0f02030a050f0a0501030b1303050d0c0f080106090e 67
    0x104a40008184401d841e0349202d50000598400340e001c0700400c03001d82d071044011010600303280501445505075031540c0208000107000301d003560031180082d2182e02c04000600c01d04080b100031580368001464081d805c091100702484c0103000e2504423552000b22455090107400c41611a005190400800d001c010100542031602c4031000208540260700c890420040a05a540242401141d282405402c002e00d400d943e41c01523204020350712502803a0098138501c5804010b510301c444040c588401e000d055906040e1102c00f480d20240216550002604011248100c090740001e425044c1c890049004102018015640340f0000800c5407620100400301c144981100142d402c0d0110345001c00c80c0c108488105119a0f0384040c00001c0200004007540458054018080d540c150340e240640d40b000507040112504094103a401054060410b40b0020010b4050801440145e00801401c0c4031954030f250000c181c5060010030010300ca4654001a10506403010a294540302104482014030b44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 155553183 1250 155551933 155551951
    0x90c0924020a0c090c080c030606030a0203040320160b180d14010c020114130c0509190e070906060504060c120c05160f29031e0106030905070905070c0605 68
    0x9504640043d110092503005425040e01c0017400c40c1d07036200054880e0074040c2410034028018030401020340e40b0719048a83c04a00010091707200d89840c036003a100e100761100302288610741d81c001040410000a0411440c9010001c00b5152a1340c9101e01c1445100b14800301180400280b500121418100030315000584036800d0f091548510481050171504103015140c0141d4541003002e10f145400808603410040e0340c2144d0031007140540d14410346000512a00d400b640491002580b40d0642c07000803426608010402d00c0080c003500701040e19403007140640011a8601040031510034032a10549050ba0703020f84640344400103548452060702c1401d40c1e0001000081e81c036040016000b40603a07046900c0742851080928108800900200740540028682184070710401080e01c41a11010ba100c1c82048480b036581d480f04a11350300200b1440381941c000c8a40000009900e89e07240e1f1200000602480554900540b81d980c01e80a075002903d80b400040c8258580d00c020070303520391029400c45068 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 155554433 1250 155553183 155553193
    0xf0c0903061508070905010806070f0806090c0c011d06070c0507031416060e13051303081b0c0610090b13021c05070509010305010902040308161103100204090c092402 73
    0xc42d5142d1510703000340c01090075541c80c0c0004001c0d200d02042030320381200490410b9030601141c0b40c4010540384cc020b000e240700d0070000c0045030440d0455000c440706100b07410001d10196261080590400e200d169508409200e000009a19188641e07000100381da4410040c0942030b2440e04c4410300c100d440d590b88031040c01039414040c1401880c407d03010082c2055100c0110b110b001c00f04012070041002401c000b00d50030030b01000464081d42c01c41c505401d074941081501a283d04c1e40c00b01c440b030482901c440408030000348051900301c0000c2e040e445150694030029402c4d44614040061740c243c10240b64002101030b46500c3c0c103980c9500030308035040b0000303141b1500758171215414080d2141030300c0c580301049002a210341903580c180030302405800c1d03400c3e0540c40c040c656a5400002d102c2c61040034921450491306804110b0035903590806a0320040440e20240c2c09940810021351091142c01102440d0401680d03015005100040813200c4150b60040ca6100d8044960150070f012041502107001d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 155555683 1250 155554433 155554439
    0x10e09010335070609020907030501030c050d060902030106140a0b04050603070f0309020d0308160e0f040b0112050c03060a090b0102100c020c0603010f060f0507170702040207150f0f0c09030615 85
    0x6000b014015840c061440400e242e0124014008140c40c0030340a0b000301402d200060010036050002c600490740203a0300102c03841d6050a110001b000c41c0350b40250305500f001030000e40c26402040742401c502044404861042c2e445113843e415103d40e10030303250004002d03c0000c82c0580100d40c01d1440700c0603410081808290365001825154050310100d01180d036442c02d1083d0416084d0f180800c10f416400d00b4206070000d0000150708101ca8440248136540b2003500f050164460105a04081c0c84030300240468100340c900c01841c5c2e04100c80c80d41c094000314400082400840c0601040c0303d0701030f0003408503a00d001e41c900024080310101c1c10258480e05440460f07070b46980000314000d14240c44a8081030b410001c004103802200b002100810400b445040c02054100f8000500f0312404e0b00091354074066072000c40e019002d5503102411000342c2c04c001c00c5100c18140c2100c03a441301221400c11502d10302c840c3d42012100d8440d43c0303c00081d5442400d1000417800e90110080070515a06400b003207175 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 155556933 1250 155555683 155555783
    0x2060906120a11070c26060a020405031207030806040b0a081002091002060c1219050c09100201021305130612081206010e0112050a06030804080c010e090103 69
    0x4408a804541c00309000200200c91501d071140200041e1003040c103520b00f180c2601c40d6180e100541c000e5410740e42102d0100d1002c9142100c034040140c071481c0c00d4901034505070220f24001e41041c81303024002e015103119103501c030302003e0803520f50550644520000e51543c5088c00300802115400701c0e003050041e80003140d175900c00c0100c45025560070700c000d40d9500c404000d04c401c44941100d42425940508240300f031204c280f8003600d241000205203100281d40745441c003001c2c40030043c8810a00f6103440c2c180300c44035616030b004090414007600c11b0784034000c03081000c0b03080348203080142d103442d980060140000d10305889058840c0c1c0c003034240410041d8561441040780d40c0d04140072a0140ca00090f446454842e010300780c0ea2140342401c2040030101c1010001c0c03d1254103004269001d030f503400006001a85660004000d540c210040c1ea44868680341c01c075644203050100300d4042850b04030114503a140412565068a5014103480110f0074050703500704000320b8000ca004440c1c8048030b40102860 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 155558183 1250 155556933 155556937
    0xc020d0b0a06030314040602060103030c08041a031812030106030f0618060503070e16030207050f07030c0812032703300c0702030604170903010908030f01080d0207090902060906 78
    0x40303072441c80001c016240d49400b419400d2800c980d0140d800040c4002c02c03090350082000b60440f505410800b40141a62421b01200d100340d0b0002400403103400c81c800f043c0c01d0083d01451050702081d044200c000d10301d406042c0e6940703801e401110301c050f0810042c003125110b600410310240c2002c1001c10510b40f0340e030f84800e0140f01e4820040300e09581e10010007151404000000041150381c00035115820802c119500007810028030320181500014600d08005042103c28524031030f00c3c05a5003925140d1030175648980c041e1103051074900ca00590b03449041f44480032207001d805082c1034840c0340700c1c1c1035039200380c0d504141030704240500050242c0e2088540e841058100c4e0559415044440d04034030001c1c800072a0042c10110488209000d0900103840000e140c07500f05402c070021400ca2007407100503503801c0c454900d00503095402c19240c00100510b41c0051400780a110202424503a2901a42aa228640150340d0016400360504003c03901c240d9000d00416400038000d1803420808a000c03401d65 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 155559433 1250 155558183 155558191
    0x150d05071401090e04050a03030216020607030315140303030f09030f03071e0c0b0f041716060c080705040b0315120a020a1a0f03090109061d0d0507080a0c020d0b 71
    0x103202540004103960f44409200301038114001c0303a8110341440e803140c40d1342d5001c282e0000c1c1810790001d00c041c086110303400518000c640c01003070603507a03880629004014100a1049401000c01c88401090a454a68140e8410380b0050004d5046640750f5003030b02d40e200c1000c0c1103d0114001040070303240c1400703044010343c0f1404107612608034140120f003503000c40104206003a01048000c039811400a200041099080b242e041503070382540d2264107094500f113894125404d80e001c3d000403401580f039204500d034680103001e04400c01800341000e1040d101c40c4422501c1c0000100208424419450041c02850300103a4070403103601c0c24404040450040f03640e0f09480005076110814080031860070382004000342076491020594442090300510b4a0301817003805907070020f00400000c20340442544a031038500d0300801d05009088422502c4029016201e0800e900b5004a01d488400035015000329840254032907880345c60321030007280444403400040d4080364001040303c8040e0100300071203201401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 155560683 1250 155559433 155559449
    0x190801090b01030506090606010e0103020a090e0a0f0e030301240c051203040b10030c05010f0c0c030803070206010905100501030b030c03060a0203190608060c07021503040303020711030f06150d0507 87
    0x1d950640c00e290f860800010300c6184a60b1081c0d040107143e9900c82885d801180c0c1c04e080243e01c03409980c000355107034101a00310020102c0c1c000100510f40200380c20070f0b180c0c01c240c03400c208855001c0e05501034481c8024003c40b0300d50b02e900311400c0311684078000504118601841c00807602c0c021583e8240c1801c1441000130030079100070080c0400c3c0009035441a070811600380211140300e241d40c0e80c0805810280c801c0d01c2c14481c00c4480f403108a40075002034100707550b00642c01e401d800c2d2039141c4030641e41c005888400040c4904000442c0112041c4039150081014802419080340342c00011400741c018180c6103074141c02911006a01c0b9102009140d01a11880b0009030701c9260015100e80710400c0e00c24100822070400d8000c00c011900840c1da2038009041b02880d6580d11f58034004a4109030582036140c0f1125030000c204028541e041d03000d0071480740301e2485440031000d000d00b010369400c1c500855404c1d1f60400c10124400e166003070303a45c454050000d454a42034a056865403810244180e000c030107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 155561933 1250 155560683 155560703
    0x30702030304060b010314061002120d060f1a0f0904110c1b0a0303210204031202070501021504050d0c02150714100c230708220b030c0919080109 64
    0x2040003480c0c01020501e1300b0078179040228039420407102001c1c0001a14650040b0001040207000038820711548032416090208541d4034014048110000e01c118414200744401d500b001149010003010141075000341d0b000307040c0c14a44254100001648420581940300340c0d2081c00c2c881c040c0008000d0608844860003a2441103441000c01000300e46a244036485101d0034542880043d0308100725501d202d061028640f07040c3c0203031144800911403078201405d848811810f018078039900103402003c1d00d9080e801c0c2c9100028401c0b00d0303940903405642c01030040c2c20a0700441c40f00b51003141180140d0340000c04902d80403415604040980d402108103440041c40d213001f0140c0018104142c1d11000340c0201d0812100300144401040b9044514125000d007594600100e4202103e00c280c032070554200c3c444a6664480c0704101d400d00c41050003504498040c00d400141403801d8801b40e07403059000c0021a8a4a0f402e0401c01076140c910ba100c84500a01d000c0f404103404109201300e841c154440e070002c40e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 155563183 1250 155561933 155561941
    0xc0a120501050603010e0a031b0503030112030923011d04020f0904140702031207021501060302032202010e100c05030a020a14010506010914010c050d03020406031404050d0809120307020303 83
    0x40c02c0d140c0080046002e68101100240004ca00241d40d508080d098500223524002e8010341d0800601801000f50032884084000310b00940600c558942d480e10984a402075555500401642c0807031802004510220aa4000f40d655005600c224180400c60143c41412420300c40090200e030000781c015408801d000c9a020b5144c186449082081c42552482c4070140c948410000c1d528810130040200d48000d20313012820050081201c180110009800f180f02903840e0070f001002504200c401300162000c81585003006840300d520000c80740d0301a544d03100c10b140488144030f95001ea44018808100d040c0040201141003400a81061102a0301800305030080d802c004408015100445000d42d15250612040b6a00704101c1400c5911211042030525041d40040c1c540c1c03010f01c007000d00130740102059004040d60590007003041d604261000c0081c1000000d84156a0b042241e0080c80d681c802c030344c03011456004a141c258409a804c0c1142d01c081c0c0e0800c078018a07504150381c4c200c056880070040c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 155564433 1250 155563183 155563193
    0xf190e01170f0408070c0b0304062703020d0302090102070503070b09030d0504140f0f132708030105040902030102090d0f150c02060411031614090a0204260c0a12 71
    0x340350700801c9040a0007807420090302030815000050001089980001220f40400c0307950901c100081c070b40304565686038541420b00d80f0180c03510404618101c0605030059000014208101d080140c03d64001d04c5113204607141035000354003160205055104208000420356010014034014250f80380000e62581040400e051078181300b0030161052180c20f220900190f0800040c50607103e5081340e61a880340d120102280402013548a900c0e00507603640f00210203401103800200d018200784003054002580b190441e41030303105060b002084143c3c1000100003d01d003507041a03075171900080006140c000d03002c1c00114403580300d10049841c2580354400d4028000009450b656505c0127803400e0040f00780c8a2402511100002e100824500c18003050300d100e5201045075420012501d181c140d03100d5266075017034a8406d007110000d440303103503544005000d00300729000351411180503044044a00c0c51003c407580c4403001e900d10010480c401c1d41508803030740d0348040c907440040c06110350281c140340f058145 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 155565683 1250 155564433 155564447
    0xa0303021804020307050a0302030705041d07020d020105070c140c04240f120204090318090905010b031504030c0312150314010608100902060f0c01020a020d0f0c0303020f190e01 78
    0xc0300b40324a00c14010400c0803504041100d6004499203001039a9956072502552140116001300500300f09490302d2503084402607648070b0084e2519002c84a0144000070101d00740c0c0e01c100c500c0c00001d00e051b014800011980001c01c1703c0409c100302580c3c504107941c00401d0884a030703804e000d10140b921a030010088400d00e0a02e4014006404481c21600c1c1040c021004040380311b88004c2c092640c3c2d040074130604d841031040c800e07401000c0d00007602095403002840d0250407a1641a00c442d40303022a004040d00e0300043d0b041c8a8249580b5070990fa6542d51400d0f04d20840104041c0d040c400204440d40844404c4e102c2c81030722086611034440114158242201a5245043c088815038540182800b0348000080c103c410703d50704601c00b10302c80c0c0c40d41c40810101e010b08001d000d450000410603103002c1c0c40c1900903045c08946542201c1801da885081101c9a000c401c801c440460384c40700c80103002c24480c0e001041c405450f425142e142c90700f0701d0f80742c3ca6064a0798100d880042d140811551a642c2d114103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 155566933 1250 155565683 155565727
    0xe0622033c0801050904150f0c0207150c0b041101020307060623010f140a0e06070b011a070b06190e0f070f0504051e040605090a021905211005030a030302 68
    0x82e0241441d030401001c21781c0260045e10160071040c15407000b03040000250451202c2e0316080b24144000d080d1108040d664608902800c004940e0310068050020720072800f440e8080c0c0c00205030b913180e48881e00d410410703140c8803038858110302003040301c0004540c180c05510b0041950307179540d403094400341245942182c0310035100f904200502c490000321540c0f00510000150000700c0090340e4061141d41900c61280c0600300907084007000c242d1006101e416440181240c0c141111910300c1c100303a4370039602500c1501001844c0000000100303003c0d0030a004a082e554540f5460f0034105502c0d208814403009044030100308040b043c008011a50b070b8804620041c0f0107060600f542000d0801c400144150a1038040c2100c25a0107555040c040d9501e030000c80091202800000241c1843c0140501a5120a040100501d2407411481d2224401c20450311681d50303028042d46803225000d000046100050b042d514040381c00c1c0c0001c12659014040c04940d03074880d48005036100c1841c07111035000380b00d400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 155568183 1250 155566933 155566937
    0x30d050c09130c02031606051005010c03090605031b04091a1c030503190c0519020c0915120303010612060509060603042a17010e0622033c 61
    0x1002520142d20360000c00401d41c80c56500116812a1141040b0704c2c50056005880300481d58961490501144e07603c41409040c04030341441e155500c540041d00c6544891b50002c0c0001e1007401c0400c00c3c94440c90140d40c20604030310340300c810310680108000701608240c0111113030503683e404841c14020b4400403034210300030070380380006a4503005aa60011080c2083c0280600c00000006070540a001401c0320f06422a041c0401c01d0202c2d00c007000380035801c04110440748120000120600ea40001143c2c09148001459401e584d640ca00c0d000310300503004107201c1d8002d40030b95204020005e0a1024601810072a900c01200035080b90003d010307a001640854080c07409407042c40259190401120b602c2508442c101c043c9103d05c940b080120400000f0310092120102d0010684196940c5e000d0000340c1480001c2c800d0018903001c1d2a02d41c0001c0d20b805c0b4046402c04103c4542010550074000070307a0003400c08101804210982c81010503080c64451495400c01018407140a9422041318070300d10740d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 155569433 1250 155568183 155568187
    0x20a240204031520041503020706020d0e121e0a050c01090305090406170a0803040c030609080304031713200307090f0e0a0305070204360b07020f07030b060607080309030d050c 77
    0x600458205d101d40d0150b050002c000e8117100b03640501940480da41241c5c400000c5695100909110004001824a4000354004d0346000d040509044055600000344c1081012200000922a00381c40c2e000300403210500009101042c10042c3c01e22408121314001d40b078140e52070341300c403040000711102a08581708010a000c64011a09000944080c4450340300e0105a039a07121130070512108511913000500907030620380c000e802c105005020f54015442902e0341003200c2080c0c603402245002c11a400b00700b06002080b868081100540d1104040440c4000701420700d40701c0d404a030511136160000c007500d1f601c0d04180c58a00360785210303100c0d02442c210043c211410055400404500c80e1400c042d20483c0c4440e1440030f145010389109150303000042640c0002010f081111444c4249244181c40d00c208940004c1d02050000c1260301d08900c2400c00b4000c030608542d118a43d426015100c10b4201100b40300c0400000d80c0b000055014181100c0256160801203903888260740004203100548142 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 155570683 1250 155569433 155569481
    0x15010503010908160309080a0f021504150e0604090f06080c0402040501020a0b060310020307020d1e020a02010311040b03040311010c031404020909010b0306070908070f06020a2402040315 82
    0x7510300f40d13039595501049115041904e030501301c400306017a80120146014001c141010010b2000b104c00c1d50a100b5034440c0344102c45003d00803c24052031003601c00082c01e6000101d041407046921310300469004000c282400e855a081100315070700b40c00c09549117562030700140884441040040078000c012a0254641400c00c2e00007500c40300200c00040072200f1160102c0c0301d5503010f001c030402c2f00a003002c0440d16860207501c02076070b50644980200100305180120300000b0b4440d1004540b03810190000d01e20310344c195004400070110018028182d071030a21000c141030314801c6c01140140c1c000c0c0c1d6040151580d021841d800c5030595140642810b01e00094a0002c4018442069000790116490b0075582c0c3e440f20f8007400742884001055050148604010030180c1008544080e262035034100c44a180e02c0d100b0941e03100c86280518400b5910106054000031540c282004142ca0016401a404882000070805980040d0011281315000100040c183c90280c401c3c50400f82c000002d110b55008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 155571933 1250 155570683 155570693
    0x90b1f0806101502010605060d06170105070f0c02030a020d03090321020615010c050709020d060b0306030a1b120302010f0b0105130b030a0212010e0604050f0f150d080a02150105030109 81
    0x202c1072145410804003e86400d0b0607034000e6100000600c80a040300da80e484050301d0a800805090040e0002d03a40c605842c214000300500c0380e1031007880c550315500c1c00207100311026218002c081d0403c9030b05201d5603002900507144d251001e204103101c0e40b103081c11181946021500100b61940c140c1074412910a624600c603800140a034220102003150162641a540102c070700c03c0403903002800390711441c280092410903070b0303000300003c02801204000080c2c456a00e0a094401a6a05a0703d60302c04a00100403071101103581c1588450900088400b030786d180da20403554000c4900c00d0380541d55819160406401d83e01a0000a01007441e02c00e1906000843e48030440c0294011a810014080005a1540505d40c1102d0004444201c030400341d60303450b6986540c480f0200c9081d030041c1c0c14030780450392001400318164010305031001000e9441d070b1101141801c0d240344811043e8001001c20307a40700030650480c020010640550301030841c504207003002041501c0c0607801980660300d0184039101140d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 155573183 1250 155571933 155571961
    0xa111606080414030a080907172a03070801090302100e031c020f160c06081b0901030207060e01020703110c0a061b0c080d180e0a0f090b1f0806 63
    0x40e40c0350515072400e8072503080c00e2075080f1184030108600c0c1301c0010b010314020f4220000c21311440340780c07003121000c41e21b07400e07980c154000c4484030030f10310340c0002c848980080d0b00c121030b00c203400307454018034084410072070002c1e207083d075181c0c4821070300d956a20404080c1a4140541c1c50710201904090103068640340515660b88222002e100c42c80503d03454030740d4003029a4046030351b041c00c0566503039240c204032140b9072244c0a8202044819901e400d0b40002ca0300d001d03050300e922401c005d07115400701600402c6016031036800200a1b03030401d642007044200191315403143e440c0d03c60105c8001030304d83d1039910307026101d0001c61039495803039400517014000303d903a5541c03050296035030303807400d1045a041240424403c0151040081c03c400c4031000c0030401200001d01042140042d9403031851700000d08400184420031070040c182242000070014410001e03c1e0031080400100840c0060388260395101c2d0b09218609440c20600c5040c143e2402e0346c1204a4094038000e410704102501c083c0c20222200d0400c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 155574433 1250 155573183 155573189
    0x406050703051b07080c0315090d1b0c170114010e0c0c0a021027060905092805070e041109010c050a0507060207090606050703020c061308010207080a1116 68
    0xb40001d04030030144030b0b80301d1940300c40c400002102c0301a511110710760340719020740c4071440c0641b164441e10036903800c98020082c010b42ca414050b2045054000c0c0845045403480e4100e0385200d0a00030050004540c84030400042035400000030601201600302800d450803103a10400b641c4c44800140050340e4500c018079005044482e1301617554500c100c505d410001179420280d07000201014400100c0d4210020b400b20302e0340002c1c05d00074141c42002544041d07000303020b41303400581107000a1005081211106400032400aa0031807101032400b48104141c04102008190300e4991050004042d003103c0b501a10500c00c94003400b060502d015001c07024041d81e0b03625030410249803000000d1203814040040c00c50f0704001034868694403402c000e551288227210700104940b42085c00a051849030b0203440d041e55250707000d0821980c05000b004640d0308402c0d100e9100d43c0c0b11010000300c140c0244001c2091600c640002c540f18081400080c0c854614640a2055604005c500e40718183c00103018400f6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 155575539 1106 155574433 155574437
    0xf0e0307020906031b040c05090d05070e06060406170c040305060a0b010813050d03050a0b03030a030501030c050d0f030323150306100f0b0d090b0c0403060609020406050703 76
    0x680c0306500c10100d4600241c0c00150414034158104d4101d0647d01d140c543e081c50a08030002c0c0300012032010417104c5170710180d010421030154090041d40500120b030040d040518044000e49450303034014855050140701d10004568055070b205031009940c10108032642450840e0081d0024031060000601244041c00083c0840302142c082d401119803060141001c560042c07001da01800c806461400c0007515154505800e0320100080c00e0150490f41d00419a07525604240c04100266041140502d90180c40c800c04190424003c0f5821079041c036000949005005c41103404040030350a24150780300030000c1c1302050541d0001e400d040f1400300d0031b488060315908903644481265100310a5410b012240c200600801c0030041c048a191180002c5400c1500d40d486824040d02211040102a004501402400101c1c89401d000d00a44941145043c1c100203018001c1d004526004003 = true := by decide +kernel

theorem cover : BRFrame.Cov 155395683 155575539 := by
  have h0 := BRFrame.cov_init 155395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 155395683 ≤ n) (h2 : n < 155575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
