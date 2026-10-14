-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2121
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:42:10.808314+00:00
-- url     : https://prove2.me/submissions/4d370a9d-9bf1-4590-939e-bf984a66c6ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 381294964 ≤ n < 381474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 381296214 1250 381294964 381294997
    0x13061209170403060f0b0112200f0c010f020f070f0f050303240306061c021914150c070e0402011b06050603010b010504030c0306150801090303050105120a0c03120203 73
    0x70944540001030054910910090080140214864042da0408078800e03002c2880e4403c01c85070000c0d25442203010b0641d802849500300d20030700c101c10700d5511003010b11401c00000180840024000d0280d8117200c21103820440c905034000c0f0710341d01c1c01c0c0034a1707000500d00e428010307189050101c03141e00d20306c420b81c005080d40c0c1c1d00d0500c0340c264600561102c52010001c018040e89040d640340105c0e890340700b41c001401183c0f24070526410a448a85134000c12a80185481d041803461201500554050410303c03e0850001d040881004019100510401c0300e0150400000c169000d0200303125080b0340c0800c03c07902d1a500c0314030042e00c404000d0203134031000c0c040c150080381c103001a54010301c1c043e4109500800c8408a007500440d040d02c110701001c0c1c44035000c44c0c0204001015540482c03024200f201c1212501030310b40040901752400c3c40401da0000e40c0301c000500c2a449c08031000d0152143e641c3c01070810780e10136910b08000305010b00c8090441c450700078010704841d0080c421604614901205007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 381297464 1250 381296214 381296243
    0x40b040b0909010509060a05010503190f0c0923130b09070c0204050610080f0c04031203020310060e0f01030c0e03191101020105010e0a050903040306050a020307110313061209 77
    0x440320340c0c000012561244110000001d001c1c10180c00f40b42c0140f0b0080c01c08200c003402c200040d10b0035480603100c108139462141c3c0300800d889040c4200148505040c20100d01d114080c00003c0455526400c0000241c10b044070304000d82121120403403d000060761321211075402444440010100881666046800082041200d65100980911440c401c039000c0125884880500c00c510880b80e40401c0805c1200c000308034481400890303258490b00ca00c5443d0328003a02d075a83d08500b1580340c55990040703600401880545126182c0d6000608000c0c0f5241000e0003220000400c03014081103600e05066032a4400c0000c01c0c030940e401c900814000d0112210500121081c00054454040641d22501041c540100c4c40d0b00c113000b214100c2e048041d0b054410785651145200500740606002d10a00c41004000700140141c060710b4803401048038010780700c0c0b4040700090000191325452058507002041443e45a0081d412503000b82e90701741c504000c0700300c078410881c00102401080600308042d02c5c0031a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 381298714 1250 381297464 381297479
    0x518061e07060e030c0d030e010b0d05030703140f090111010921093819030203070206070903080a05090a180605031c0c0b0603100e010501051903050304030201080408040b04 76
    0x200401e51240800b0082038030340c800740c25280d008003082c04282da04000c0709240301c1442038106107a000b812000008200e1102800103881882c0c0c4d41040395141c0010032048140754001d9041103107501480312140c40c0074180d48101c20346201e041e0b07025040c4126141c5106800200354000281d040c2c2c81141e0804481c21090410892040400081c00003540086c002c18203411b503400c01d04001c1c0545803122204d04407400c8000034080c540070b00450702b2000303206100c03082412842500c0e9040e100d840050362800c01140081c00e10000030104010722203281c50800000b080401111031918141c500b60b901c450008001400f07503c400e0388032894138109042e50422041d19980602c044400841c1156a051170892803c000e40b08450b11400100d007203000244080b40c0b10400c0c2c10340c00b29000301610f291103603182d00f840845882c0b050010140c0c2d035440060006007000c2c0d0b4120303d0030113161428140c161656441c955a4400c50000904120142d00820204480ba03401d9402602c400b42c4070585690f2074110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 381299964 1250 381298714 381298717
    0x140109081c0908040b074704030207090f0204050d05010203060108010522050402120d1808011401090b01050702060406120f05090a0201030b03071e03060609020a0518061e 75
    0x1040c1d512141076011140e2000151180c0c601d0341c1c1d030081045041c50314204102e2695004808103640a800b400c5181410740c0032400900342c00c022010301203d00d5007107041d0103d00718a41d04a052100d12082040c00003094000a003e01201d00c2007902080e410a40c2031600d01a0083d54030858200031054460b03810820190040c511820003a80e440d50140c0c1e0385d10421224420440300c40c000b801d50a0086c8002d00050b0f007000d50300070b002800340c2c140c115203c0c1c4410310300000d840e0b0303c0c40061140c88440c110102c0143c9104020803180000348004544c4043d02d5004540610400450075070b90f40303104d01d00fa4003450a8a540603002800d031038036655245d0018126040300040040c80903d0f184030848100c1c528416180525110b0b0b000b055511401d80c0150014081c90450700d6140c800e20300005101040e20151050a048c0c01c60079400e010f01c2c42c907001c0300740c0d8810b0b00403028460061091800b11a40902030301c0e8200e41c1052707040c0c0c5503081c900c0851010303c111300b1110100e1100684250b0f4890a40c030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 381301214 1250 381299964 381299977
    0x30304061d1e060f071e02070e01030f0b061f110c030a0803010801050703020f2d030a0f111213030302040810020a0e010908120c07080706020a0201020d0e030a03030914010908 77
    0xb0540d12250f45080d16a0a20b080c00c450f46400b00d00c5003080480380d590300c1c0320800400e101c0b134011181c230240c8840009152803000d034421070354140d400301000c08000c9003d04071a00a003094071000101140f1a6125550700084004101000f0340f210254400c02d0003080581c41d60740c000303001c2e140460301d03605010015a000340036030f072070300d60909000c03da11034800e10031542000d0780a00628200141507180e44511034074044070f000c00a08103a00d03201c83c3c401c088002d40c042d8050170030008008510390860b1060351400d8840c0d181c00082400400848000402603030340c4041c507079400201244842c5030a8009000f40d401183c038500c661401c4003000900340e4010611b00d8140e8542c040c1c03c5000d9001104c43c64164041c4008681240342c11100609000f0040c2c00010000020380d40c82a40f038440b21032400c1c09030b500000050b4000400c01c001e5507018404090039285c5403a182c0b0303417400104046552074420400040c10035555000f6001840020f410a09030741366030350000d001c00040350038406010781000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 381302464 1250 381301214 381301273
    0x160803010e090a0302120d0b1305150901050d03050a05120a05100b030403090b0d060306020c0a060b030304060e2115010e180613171c0c050705030304061d 68
    0xc50101c0c00751400040c3c900d038079652690080c281c015041107801090f4010001c05045203841c0c460041180e80c0b25071607804841c1e00010001050714084078006001c99003035900c24021a41d0303030014480740d1203204c40782d107180fa010b0601c96500c0c0582d117030072101032148841d010020711080c001d1150380c05603a0003503400b07034a41d141d018901c5500c82712180d056100656008011507140d200c200000e1440401500e0208002c0400080c015a29251142640d02540301001d0541158020f0000c00c403080c483d090048605038000c50070304d8104000904485405802c0c80c0c41a07210301c124039601e90001d038455004d052038106881203110081c10301c00d0311103801c1c000c42e031240711181e00142c001202e2082507101d40112800510349a122588813126000c81380780c095500b9003010f029407035600075020042040107000d0418040910403400c0e40030461702124000020814104080c0b00458400020340f600720341c00130000540100d414000d1840e4501d0b5004005182c061040c1c0d02800f03258140030589100f004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 381303714 1250 381302464 381302489
    0xd0938040b090a1703070f03020705040603050c0a080102040e0705161203140c0a0f0c021f050408010608032a0724020105090105060102150c09060d06030212010c120e0316080301 78
    0x240c10704c0203102c980384020001c10342d10502000c00801c80c0d44802255046c000e0041d5803003640c0300c03c040707400d94070541c10a031802d44c4049a103e0b81418060701e4807001f09010b00007142490f0904040340b1640d040580840100000406e80012601d07280b1072580c02c40703038801d412250b6410100d001501804004001540100c900c1c00000e44c240c441001300c4526610699654205d6800f0480540b800e8000c090b00b1f90b00181c10010b4482403c6240f01d0040907900151101611146004407071802e40c0c2d0140c0100619030014850b803004201e1a95450344c40d2048004502e00d0702c6010104645030076034552241da080030011520b0300c500555541d100f10494117a500a02c074550b26a81d02900361781060360b015005074011603414280882e861215030b0013800040c072080c90882c48200190440d0041e250300700765a9030f86c0b4410800c61500b81014406401040002d200d4010a044040d002d07035a07040c50245100d88401c0f40d4101d861042c42120303480580300f0100303d840801d42c103102c1d01c1e5800134068108203100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 381304964 1250 381303714 381303719
    0x51f02220e1f05010f020a0602070501090b07020d020d1b0b101d0103020303070209040302160602100e060720100f0902180f0c0a091205010e0d0938040b090a 69
    0x4000c2c0e031a006074051401c1580c600d01c1c100044603110b070303001420b0046024604081c8000785c0e46000802500d401080086111483c0381801c0d20781c0d8101402c09410356102d040d040a0003a0041200c80c0c1401407402c0c10518426042e0003803404840c503070381c02840102c0744820885020380c0132091005942c0e903481030443d5448882c0008102c10020302000c0d50540c410701c144001850071440540c0e11500c2481504c01d810b150340f0780000540d009800c032102503003102101d46c0d0304020398898003205020304030090299090a0b0001b400180515260320300601900c20920350152007000b0b04c0c080300c82c41c9203041001513010780d041030050541440c2203208951000d40306c80c8024a0300f003c24080c00242d00c8404c5941c0707590500b18890360100b0b0070391090154540d00041d0411342400a4458a8000c00010a0520f1490441d03800c00e2403100b080c0f81400f03d403003421301210881003031005003208a88000d0807400e143c00ca914146036000682412090400070380030540b000c51501074003000c00141c9900c3c20154 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 381306214 1250 381304964 381304981
    0x2a0b0702060a0c0516060203042117060906010c0b060a080709090c05010207050a09270f02010e10050919081c02240c09011709010207051603051f02220e 67
    0x1180170726408044100304030302004501c45a00031604a803103403090b1004650442c0803000d0072004a40745d200400c15914280e4066000070f100700340c1c4401d04886550042c5407003000640003100001c2d003e00b000c152600002e6250321401d90740760182071040c0448900301c0d0b5415665000e802481001c440340d00c25140c0025a6500004448060350b5004140030091342c108891500102030000000c02c60390307900980300a400d103a11509030300e030300d00418a10401c2c00c0306000151800c20341c1d04156006050702c08080212540c80000d0b01e2600c0e100710380c2c4481e14803021000c0315000785141c01050307460040701d0324103000754a46d00324511492115001d4030805428013807443c48c3e0003150412000300d0801034000905850440d0001d000e881414144203111159042c800d0102c2c480442d4584000da5000a1036414003100300b025811601922000c08003040c01d50f502c1503191040103103024540b08650020460030134051701540c8034183ea255203002120b9001000c01c080700c855100300108070300300d10040340f0b442 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 381307464 1250 381306214 381306217
    0x20c0406080c011107030b0403080105011b0312110405030708061f05030d03020904140705041706090a030806011b060c0908061b0c0a08030103050d0201110a2a0b0702060a0c05 77
    0x100c031041c1c05001c08101d290015100c01d00e05112040322400742c00d8000c4002900b4211141c000e50080d5131b240c103190304200000d41280707018801e081c1d04107030b610b04038000294800703145100200c03051030128801c9007400200301d05001d6908060341c907025006002c00d50020000301d0a1041c1c100c0000c841140e050003032141a01c0c0581d02850b0340640000d50000c40c1030303000740c00600c80d601c1d0142000500065810041e8035060301039030040001480000c0400030814036135244401c21001401814950510070350450382c82b15846001401e20424000003080c0ba8040c1c07049481e425161201000750254918201d001404008080c1c0c001c01d41161020034031500c0000c400d4410a00742078034403016400040c000e80c003070f00240302a005e1441402d01000003d410b20300614001c5104800a201e980710310803001e400c0d212401c400c01c59808050012820081e4006058a9601e60100c800c212510380020f4800b00251100c001514264030582405110f980c00504184075002120081028102444084455 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 381308714 1250 381307464 381307469
    0x9020919080703020114040e0f0403030f0204060503060f04021303050d18050102030318010f020a0201020c010c0f0822081803010c05030601050a2f06040506010b1201121719020c0406 80
    0x90b640805400d20040d4015400c100d403854080c480181007a60b1103280d0611300c03104858055210251009101c10550507006030003020104600640c00c241c18103400504a02000b030409200307240c2c0f0035854006480390f50484620146040400030381c140c6900381281e40300803d11110b00058209110701e40c522922004110980d60164050341c990340300c4c031941c4128400e410340c441400755600d8031078807003021f03082c8000c0a00c0c03a203a40000d40c4030010384591a0840744407070521028044154040760706168403240303041e8403a01d28215040b46c00c01040c00340002c1c13040030900030f001d040001128010210074a00f8900660320880c000c0c030035481403041c216000c0c0020303501e180c04514140203103080c2038046c07030a0344020784040c80785440140c5101c030301c203d80c2000c150712540030390800f105020500c6024031043d0301400d4081442032812903841c109620802c2d0522814454548210101e000c000e00a41e41409640760142030310744840210100f501415485410380780584280c0311a00014205805100308 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 381309964 1250 381308714 381308729
    0x1308060712150f06090f0b030906010524040303080a05090106060f11011e050702060c09030d0807030b1e0a05030625050d0c0509040606020102070b0c0901110709020919 74
    0x101c0c14820444032019000c80c000e140b400034008140030800311189050701008050a55800306043d20f02a50301c02403102c3c60b003017018011010820407906210020303900b811254181c9494108000200ca41c88600c60a0b00407110409400a000000c2c180d001e0341d540c0c0940c0d20400108500e4030f5940b0f01c142220403902c03e100c04106c0380241000c109000d0700764000030b1603450340082241e21040d0090f4103001d0801850b4103c91b0707500c20501405c280d0401815038424400106240b4080b4000c2c0001da40310700750101e00c4200410000002e440394402d03084044424030103820004d81c03000341c3e9000415148442501402110710030b000151320301c2c0c000754844c001c0100d0703102c0000d1244442c030100706ea68021000402171000801000da5200700700d01c0b903d40800c480d07130b4929440b841c0c490100b100b5901d039540f05004581c01800312002040740e0142d0703e5000b180400c0740e10340c0c640c441c10058500214500030250580184480014540c00940080c0342ca640100d91980202c1100d86078400d030100746024510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 381311214 1250 381309964 381309977
    0x3070f3002090d140f07050a2706150207150c150506041103150a15020616020708030d05100611030406030902040b10020a050c0301110d0504080702030105090313080607 74
    0x1452a0348a41c0200b8080c0c1c4060b0840345a1003440d00c5400340444011411945503000a605560b5024180051000307008100d400c08a19071800720401c91440b0740c1e005900880503499803d910000959100200504880840300c400d1804120084e4444d01c541c40b071155401700520240205610841702404000c0d4014020441b410242d030100e002050010100c98000342d0320114440076020a001940c41002078040b00e0380c07525a40414048611030550080100b0111030b000c0898490300860403e6124142d400c1d00e10340e0358489401285858103a03030013200b040c00000f41e07940c200da482b500075500c2662552014402259100e004650482540d00350f207000307030400d12080c40094401d0b004603440a000910100b044c1c114000017400305076194852501681c88424a4010000140810f0346407010444c0200540c012511400c6601c3c4203910761001c050341d4900c00141040b41280070342e9041500034008019628002010560320b60185032610180f840c0e0301c0c4002864500041c0080c45240c0681c0e628 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 381312464 1250 381311214 381311297
    0x403060b0604030c0b180306061507020d0804090603112e03110d090b0a0506031e030403050714030601091a040b01120e030405010f02010e07060e1503070f 68
    0x25008003001180298071000421000011824402030320014200c4040095a503d40c000d041d0460389000d0b04006000350019000c0100701d54805052680007214011140e9840d0100c3c40004d81101c54100010044540810003103229803da91021082d41d03c01c082c244071901405e001c101c0d011070603a80350700d145a900c94076200600100e204410031907a241c200418980a091400328035034225000c00183c0c1640c40341000148078642c060203401c030780141d0041040d0708112002c00d07158800c001d00f08421031070000380103107420001c00465004540280035203103c144c803a1500178079803070060700c3d07a03101740324030400132401c030304c03688107282d800660310a0011180e00d50070280b0029081030483e030340c14051410142c10f1241d09034080c15540702c1041014503580d50504001518035a00601c644046a01d17000344c0c2c1c03d860400140c0501a1926401d00c1d42c488800c0c800001c2c8141583d0303100c04d4404c0d001106001d4100d070040061a8112040d07220000e0900342240080c04945440d40c403070090100740c0700c80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 381313714 1250 381312464 381312473
    0xa02030705101202040902070c06051c020c0a0b0406050405010e0312010621180c120206090d02031c0c0309170c0906030f01060f090e2a04090f11030f01060b0403 71
    0x20b00080d2050820415403035485840e50100d030469840300c0003c03500084c100b401c00c90303500c3c4140040c0c06c0c0e0b07082041c03c0081020000d04804403503645050141e90000b8020982d540401c6030726030b090380c0300002040324a01031400501405058404483c5582840c5110444440200036039500000c8030154100c560310f4401c0440721540702c05200c180c0c0c10442c801d03211070000580208880d00b04c0100c1d50036140c02452074680d10600302a4400c40c1403103000c00382c09005031350b00c4c0110341952000f1503690305000c8017030000070f04041d940c104020013000035888294102d50044681e81480d402501d402401c19a40c0046002181281c14007520715000000e94001a140c40c4043d03036048803020341184d003000511404c43d8216507035504001002c025510081159464034000c00c1e9200c07010002034100c981081da00b01d581c181200e81c0b42c21313481c05420b14484954440d54032550895400c12000020315100c4e0804403450011244482d00a0040c80029100c8201c14001c800840c2d4820028a2403c1c1c65510b0303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 381314964 1250 381313714 381313729
    0xb030609030406082a0703030c080601030e0304030f081b0d03060b07080a03181b080c030706050a0c030309050601180c0c020901060c0305040b1b0d111504050c04050702010b0a080a02030705 83
    0x300217280c801352100c80819200902c060800e203440380d100090201c0003072002400440000300303a18101802c1c80110300420a000c810b507130489a220040303641548451030115240d00814444400d00040c90321071810049000514040500c145d1b00d0070013103e0340707a215840c070b42d02c17514070007410b003003020000c0d004030612035400010f400010100c0e0311300800c469680c13054003104501d180b0070820717030000d0140300f03400c01448200401c2d94202c00410545d494980040d109002e04107460082c4801a0514000d0501a42002902c0d42e4460150340b0150707140c000c030207403006440d182d8040951804000340c0500d4000c940c0b070a201a0000e10301d01c030316072030034074101e0300240c0101085007081014803001845681c020701401c183d40c148500c0e1000c620824040914081002401804010000c120303a410354401103074000c0c5041c00c40c0804052a903680c107080e444d00b08030041d101c0e003041c9048104000e882e410352002901402c22105c60f4144d550b01c0e45040d17540c1c0751100c000703541034028032800c100500d00021f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 381316214 1250 381314964 381315001
    0x206090906040e120d0606050310330903060b0d050a02062a0a0b06180c03070c050f0c01081602070b090a0302030724080c0723030406030b03060903040608 68
    0x100080f8581d0f580341c2c8450300f041d8511000c48041c440114050742100d00c2c80c0110000b508a074580907082d03141c48602480f08440c144506a03111a101004c9003440c086024100a141e06a40d0000c0402481007070050000c00d5030701c8141c0d202450140c2e1050325142081031582141d40020042c8415001d903020400a60310603100500c0e000700c021901d2050002110002980122220141a51420b6800e10004484004248903c203420703402d0b01e00c0c0d45a0000000030b03009004240c0c91500e0383d9030b07070380280c030010200e0f400a405071060915000400c0f00004020034010020f0b41c4c0d00e64180c5401b4200c80401070900f44203000b40e046a03c050046002441c0945007906008140441860303807600800e042400c1a040701640b0303e000c0790020300c1c0060408401400d003041d890002414a4000000315440c0981c41c001441c840140301c81060f0703049241c404500c1d50785000103032580c40c0c0da0707508007800410051504501900500000484404c1c001c03007900c04845c3c0c50740b60f4030280d40e6011450049a10141e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 381317464 1250 381316214 381316219
    0xf060309021315120b010302040e030304050a030c020d020405090f100e0a29010303020a0308070f080103030513080601060c0203010e01050601020d140f0a0f030506120c1002010f0213030b10030206090906 89
    0x560002618104504113070b401a0301401403005135504600500042e52000c11076480540d10800070320002543c0000c0400c5020381500c2e03d9070211903c2d00c0003400e84401d00c003010754018203190600c09006004680300340d038000304104a401904407540c0900545805104008603030b00013114030000714051920803c0840840c41100700c4c3c84092404001c0c0d400380c285c1050300103a102402d51400c01d5007200c1059000207050400341d0760780039803040c014a00901400010100800460343c0c040c04001256240007804072034083d1440d030b40e124503004040c0100142c050740310398240003074000c0c0c0c41e8042c4602e5001d54010703030180c2114603480b0303010380e86883c602e0380140004400704080c04008000381c02a1050501da07580d95952450440002001c1d0344014155504c0303440002c8959500c480005105800844d0585031b540328154064020380c01007560114106080b4000a07100070300c00928840801a84c0c0300f45001441600c907800e038290070801c41c0c040250030407002c000e880d856150100c00c8580c003c200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 381318714 1250 381317464 381317501
    0x1506040b091f05090a090e0303040818130e0d03021312030504030b0a0504060e0c0a05040f06030f08030f0903120703090609051b041d1b041d070f0603090213 69
    0xc004040100d10003480102c0000b00c000c12140914034142d4500001058200814429091501d40860b00c80c8009403000300050030005550308400122140319501c0f401c001c10484080b5030303012680010740300c1516401d00a0045c8500c08000900900c02e030303803c149c2c1d03c443c04403516060004400b144444c803501501484000c0c8800000508021842441a1407140d4003051900345840d0280550765111943c5030b45811131004e10000d621035040d14011100111004510340c83d90601400040207142c0000c0c1c00114122020000d1050380c130019809035903403c0c290302e0942d031071106590b100c0c042d20b90100c01d0010807402181d00d09100381c208980c1c990190400084550507540d070285081c00394002c1180b04409803001c042c16107480d1142103001c000108a8480769007181211503103c0c81e040003d070b0404400d4014040312511158001c05900c07a80620508030f1014290310302d59100614403803210700c1d6120b4000810018403d000d2607a8007540074182c510384044021140c40a05009102c0c2d01417a40c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 381319964 1250 381318714 381318739
    0x100b0102120d060807051509090c04120b01030506130c0e0c1c0506030d020706020703141002210601030b090103030f170106030e06010515340312051506040b09 70
    0x10340c0010404401003140003d02589803980c1142045103941c0407a100d0f41a070340000072180c4852003203908081c804c0b1200304aa40e100d0341d58040e0f5001e0750300808008010fa8075884100050540040e060b42d0160007100c00b541d0315070f401490800807843c2c00a11400c0c070500c04014a40250190940002e6114255030602c00d008141014412a0f0107001213403540312400c2c400541018010345520005034400f40c9a8182806800703907441181b840010074407121820001c580c03850078040c00c22443c0d1083e50548da107102e9000c511414a07480e0540003042e51280e00400c1080d806031007a22010200681840c910b40e04e56141a5a03404003060b5081c244028504480045920004014081c10b50764400003000950704001c2440d0100580245014815070b041c0c0d030003a8604401540c40f481900b100c0c026660050502004542d040d08070b0784d250422103c8001400c158100005601000c0701240c20410350f92041c21483e41403500c0790780c0c40e401490800c014041e0000b100001c00c000b4001501c1c1d141605d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 381321214 1250 381319964 381319993
    0x32a051201110325020a0803062b050703020a090603050613060207020a060207090f1515090f03030c02120312150a05150309010606020706020309010807030b090a1d0f100b0102 77
    0xa2007104e01c07480b01c00d440d00c44100544240031061200a03500c0c40245071042d00e0380c0e20201d062002800040c41008012076604008400c6c02c40d0030400520341c10340022042c210702e042d0340d58545a0004078800c450075900070555000d0b030703c104804c070b0b60054001c1015481380162002c54980010f4169001b40d020001c400142c1c071175515031002889107a008044882c5089001021640d00d2000d4040d0203040043c40340e0005084402c0c40c040c0d8041c0808a0320b00c101c001c00940c4c2f21074103503210000000e405000001810303000591008c039180295400040d4003080c800180d2280324200c0000003200010001c07500391080b01c002010803210140c16a1821a11000099a40a40da030851707441c0c840000300700074040c1000c2c0220f00042402d07000402106003400e00107512401416130113410024040c0000d400203200780c00c482c0007003001415800c4c0c1401c1c10400c0b40054110000c803211404e15040300e01c029024009082030300d2100c10f002070244440c80540110240450061709411441202040d410340c6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 381322464 1250 381321214 381321217
    0x110109050306131203091a06030109050f010b041a0622050402121008010b010c06020f1309021809060a050d0f06050f071403010308030a0c09080708010204032a05120111 74
    0x240b62040d020071030f882c510f181050020302051103410806003410b015500040350105008040843c10744000d00b643d0b19900420b005000c6481d015106d80320b1002c1031030107032206500180e941c0074181d40a00240c0c00e0400b200c9a0554100e074529080301d000c000300030040754046428880f038140141f6007010203541d000000d080e038100e016070700c00341c00444c0140141c1d4403a020f00f40c001400494001d0084030704040018154900c1540301600160b000030f02850802035440480784c0c02c0003011511203881349c4400e03481c00250040c0240f4060b203105984228481d181050170359200e04802403500010358280020720010300c011120881308061070303030381c054001032090081501c01c801403030080c50180741a1200400070050440006031030b010400040c40071a0034003040301d03400048194042440301c2a00070413211b0b2542070340301100d0b5014142d004240c10006400500c2100e014600e84100b0305003041d8120038141314003100c01c0901400000c07c1043d410510101c04a040e408000014031084900106545 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 381323714 1250 381322464 381322471
    0x510080601060509013903050706061403250501050703020f0d0c050706050703080a020304050a02031507030b030129031f06050a0b0c0604060506060408012a020f0703110109050306 79
    0x86040403d04801075640071a428103408040c1c04110a072403000130301106e40940d02e616003204014001c00e100149401681203920040d8030440400009640c1d2032490151141c00002c14400d0140082581290000c4010b0100b40c02d081800c2d04900b034500001500d15600060044096000c1c07006140e040c0740c001c1c001b1294440e0342d51261080040c861030590300f425111780080060100c1408240b001c203902807a120350041e5001c1c00140c0d2911241000c5d4074210020700d00039410b1007030104401903841502001341c02201a5242440044101803c060903505102c03060031200d50300007106001c0155502c1012031032540030703003507401c170380c3d10210700e5001e440d1034000c4d00780c0894640d5410042030070b0915248004040065406041061819400340c4039030010317001800080c0c88034089003490303a49400300c8004001d100000c1081400803944130a110f91845941090714141c111824000d43c008610455800141405891094199550300c201c05c0300149105040000301c08000c180351302c0c00c0010901 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 381324964 1250 381323714 381323717
    0x207091a0f06040f050d02040f020c0109051e150c160f02090705090d0204050411190f0608190e011122090b0d060e010e0102030412120519051008060106 67
    0x2019030001080c0950460100700c1d0a010303a10400040184004100b0200c00340d1300211013800c1c40b681e0707600000b00030340047c014422001c0c4c40007603407078034015055002c0300c01144940184c0d954010341c000c400200480c10303090400070760000c02d013550f440d407060b41c28103901003aa512000d007840030b07440b4060b0340e4105040046500800c5408508194035254214517403040c0c2034a821807804000c03a02203200c80c0700701f00000340035a4480303010408100164074040d2800d0409030945403c2c5000c1c4a04032207401643c0707e5640401c0003e4008501180f2900589104400c5509d003410b00780c040702d00443c0201345282e0700701c4040d5a11607500c0c4030000400020084540c5205124150714184844000c00800c0d542c00003088074a44920740e0740b9510f0350840c0410360f80d08a1000681c450702d0b1021180540758480408406500c00420003040107968640c0c242241004da44070190814041c4c900422960b046d40e03401d880445140c1481c85544058001c9179201d03070386410340c01203103640d00185403411900780c00060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 381326214 1250 381324964 381325001
    0xe0315040305030925090b0a05030102031f0e0906130f08040b0a0201050702371e03080708060d06090f0c14042904090f0c0803040302040b0d02030c01050a020709 71
    0x44c02c00d401c0140105802d03031103070448000580e021303c0c015108424800e0f800304680302d44c25a10640c1d03405207150300915000c0e0080d580c1c2d14114064056919101c4c40580150605900c0410081c982000851140810714020b104540b660203c11080092100b0200c0380d884010300c80c1e500241100d409000100000c1d602c1c03941b50720711204041d0944000400c0740c005c552048602072a41825014032901101d00513070002861000e0b4644400382200c0b136007000c0c00c03200d001640309014500c040d2001404502075903c101c1c403034071071584c121f4500c0c0c800c0c0c5d4403590002650200c280800d005030b10011101d4405c0004c201e200705079681e000f404010301d40c060300c0c140b03c10041ea20318a09050203100c0b02c460000c64140405214a092079140102e09140d15002e02c2e40c0b01310710010008481d401c00341c0307180c102c600848000c0d501c81c078540c0d0325130041c0803ca00a83c100003202c150340c10403061404070140c0c02005040000380c1100110351607001111032108610503c40d0010720b0411601c24084041c540001c4107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 381327464 1250 381326214 381326221
    0x180307061b0201090f0303020c1516030605010c0308041707021009050108011202060d0209030c03070306050405010b010503040b0708070e0d052d1005040203010906050a0203070806030c100e031504030503 89
    0x456001d2071440c8036081d6410014140006180d071303002601c1c1d80c0e503d4140183c403800c0c2c03415003914081561903003c0c1c2d5510341d141440407020390002e048190400c156402c0c40f0094607040111201d9240940080c04245074030080760004054001d840d03102c2150300100d6082c03010540000307505503100c060410114090150520080d40c1c03000321140506104511320849a0469000c20820301c00c0340c0c4070180081d40400c08409a60b0244058a4404401011101c0c255200d05040004020031b032400c6402d9031816048640c954080e600340d078030540c1c00c465003a03080d42e81c640c007da07104a03004044004103c17040916190f543e03a07028259014500950050103c3d42d0384e030411980c0340a654440754000811303121681090f100008000903400d944030004141501c0760301c082805080c005071300410542c01c001c00c0104050712035010314031456003561801045d80390070040c16110040041c0c5140c1000340182d40308031160148620540000380035089540c0c126082491140c0b030101a641140000c40000c10f2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 381328714 1250 381327464 381327491
    0x110a051e090a12060b0907171003050a1a090606011e03060b041514030c0403030f0905030307030e0102010b1509100e0607062003061c06141626010b0318030706 70
    0x17040c80030034041e2442d140740e007400c0328017500c0b64501078a411807810389000081c501c1c59507080004000d40d400022207103120050b1800d18184030b400507145607600d00d0300c40002c4030b1280015450307008100c1a11095000c2e00d0b10b00716000c803800005480020303d51100740c000341c14511100200010000d0350f0001060a80180006000002481030b01808000500074803c2c0343c0e55090444003142c0e41400c201058217190041030700c1d10481984165403500012030b65105041e007110381c85003590403d0340200b00c1410400100003d004234144150342800052280b80020700308101c0d00d00110005052600c0103407902000950f25600258040703507901d4544040044190000407118403021704070114508618182c40440c00c04000c4d890b6a98824189203080720505c0303150380c003042101ea164640ba420a1404c0011fa28500202179156800901101d840c50035551720b8100d840741c1521816081070070381c1d181c064441c4458002400031003c81d041c40f0300985000c00104028120980308a102140d0031110181 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 381329964 1250 381328714 381328721
    0x1110030225021e180c13120b0414010e01060f031208160f1e090f09140c03311a010501050306130b04090510110a051e090a1206 56
    0x900d44810000038a800c0050742d40c40d08000c10030048603607440009044400262a03403030105804c9035030394002020f01104002e120000d00356690b032140c80080841d83c8286e41140c00200e02c001426a804650100b000604a0300600000011100000c80e002d000c0c0560103085034075a0748038075001d08420350100200104280c88201d403200c3c40c2000326032464070003d140103014262400c01700f0080c480c3c07250755a940c0100300000e8820140320b041c0d1804040180701611541182c0524034000c1000d42c3e0000b80c10005001d8541e100072440c0c0d0b4610340da02c1c2c1c040311600941028150062604103504044e0000300341422200a042031610b178450038041600381208401880d46160054900400040c052030740c0007421a604801c05648801011003034801e1040107090f126407041e803007410071001e00144840000c10441c40c05152a040100304401110760b04644903500801c00800d0041c0702107001046403002c20707484459016607072441d01680f2400940b40002e290406080206c001d4203003801e1210a11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 381331214 1250 381329964 381330007
    0x71d040b0a09021011030f04030605090715272c01060f0c02061c020d02071b0f05060a03020d0f0204080f01090302070b0f041d060907080f010501050711100302 70
    0x80e0400a82203543c011a806000c0307100a001801004200261094010405c44804422403002903890710381741d25240016010640b2511500d00c110140454205416a0f00060180003a182c003107502070041d1441c4613001e21071401d8400d80314003150016074801c000d100031008410b241c001141b007a00b0030305140b0f45030f541070b04088204031445130310a9000e44c200721243e100b60380440701c083d12002e4a18002d1103030a41114150b089034004506d512034500aa006450500c0c41011a002007482114040c11000810b1040c820203540b256800c000310304104000b4156652646409880e003045070014000340e505444d100315200764009000c100014040c0b01a812189122001380601da025480007581c1d0b089900130b505081c500040d1060500b03081808980040074030000b00c00349500d04c100d4403500c10808843c0c40d4000c1c100400044c0b11140304568032441200740764202841c40c1d0810f00115029080003004031610404c204c040031403030390703036400f184000c420070342d409642e45030040140f50002030041c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 381332464 1250 381331214 381331231
    0x8010c20070506120a0e011d07171c2706090902190f0c06050903030109060e0c1e0403210f1d040902030c060f0c240711071d040b 57
    0xe0700140403c0d03030340c1821215000904050a1a5a1175035041c0200030940c40501c00310310b40c64403d0208038a011480150580035444040d2450a9a0369000103000910203c4006090300880c00780e00c104d1030a0040910301103c6450000f510320b03007480400c0b0b0751300484541400700e10314850081103201e07800803000028000251041d81030095103c200401145102e4913403080c0003184000c07002d020300c201030201045070490b50510490400740c1c2100d859500a0040b2540103040440100c0d19035111070b4002c7c003030b1020716070b017a01d8a07802540c4074104000224020207440802c1000202103070740903018001000348440340c07400e10008420007404084810b000d03141404001d81c14041d08440b040c0c2c10b401c10140c2580c011540305007a01c0001d041c207071403140380c079030200340410b4140c000b1030207902405107103c00f04200d071209942e00d17030602d1407000c0f0031440e2100c100c2d070b40002a181a1107002d540c01850565002c4038075203030701c0d07000c45508031407841941c0c0c01c5203000e001000203002e41c8540d120b8001081 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 381333714 1250 381332464 381332473
    0xb01080304150c0b04020d051606080609010603020c3a02011d06060307120503070b10090b0405041e020a03150c081008031207110111070b06030705010504090b0103020408010c20 78
    0x1541c0c3c4c0c1c10808002880603100300006d4005d801030200c10f1246501c5401785c030b001075462a031501005421800d050b5140340c010003c003000480d6040c0030f072003214801e0204100820f83d0000d2421030010302169047c284081e20324101d00c0e0585484c410042001c0300c07500c0e0300007080c4000000d034032140c0f03c1000d0080b05800d1340b01c2c5061004c1c2d502d020a00b2801d071000f03030303049042d48074240c1409891841000401404008803204205a03019038032943d00a4400551050040300030b500100400d5500965002c2d0a03c00141c0e0b0341d0725181c0e0f04030950202184098405c070345003541c1c3e48800c00c5410580c1c161891254540944c54070040d80032007a15880080f20150074800c900304281150341c0c2c02180c03450380120611001089a2034064100300d124421220024011076843c81e2041c091500a40740c12660107000e00d010411514011440005948069444d6130810b49800740e130b0030150050151032418142e00b00070100f0030003c203015002c201c14054540990803514400742400c202c15050400510390031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 381334964 1250 381333714 381333737
    0x40903050406031a130b03011107031806020a05060f18070620060c041203180f0e070e10031a0a0e150a0312052b05090d030204180504050a0b0108030415 67
    0xa441d501181501c0620700002001b42a84001ca401450501c0120f82c01c0240816450201a804508000d20451084124480590341d441c26079580c00d68040040207600300d180003070100300113411030a9104c00c03440207130306503c00c811308860b0820a0a40102000440e030269010360011f0241c688410054008001c0032103141004025000d80154004c600b25005c20380c8442050600c00c0c1507802038404c01847c5448581d90701c00c070201001c10303584290840e03104180001000c5900480c00f2a40081002c3e00007642803c01c404124024801071428044160a211080d10707140c40300d1003603602820035410940442d0070041c640c0008000b0034a4014403131040c0c000305100045c285915040508030768108180c41d440416003a10160410700c40000e000464425400900c0304107030031680c02482c1c01015200314070202c030030072800d91046002d0245046040040a001c420655101952150062040e039904140c1540d550079281c0c401e038042c0000f03520118003401025005541c00c04904801d007010348100c4c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 381336214 1250 381334964 381334969
    0xd09050105180402030a0e07060206011503050609060d2a090b10120b0d080c160e06031911060c0f100501050f040902030f031b0f030304022b02040903050406031a 71
    0x440070b0380150700680d000b00104e02e02e0041d640103002d2100c00c100503291503d4039144000d545980c01d11407235500f418092484001c0724020700c00c103402201c01030032184240d91004144a16420074140c101e510f85079500340042c0003140001c41c0c08078a020030030a24040c5243c650b40c0c0e000e4070000740c00385126803042f592070f101c00d54100072040d4a055500c640854403c1c40d0710700007000030f400c0b41c80150000d000024604484040031030740888004809041d514071b0754903801c80010120044400329010b0344086250790000501580c03c1400c94440c0081e07000e250b019074041106c2e50002c0c0c81d00c00065020010311081c0c100240580504e00c11650010000307589070100161620340502c41040c02155203609000c19920706104070390581100800310b0f0340d151022108150001102924102140a001c22414044078080100c1b40a15002007020888400000f0648041000700b10799482c2900e000c0349036401600c45001d00303a400c0b802a22520303140c40c501413000c0d060300c042c0c030f000b640d2464055411090b40c0e0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 381337464 1250 381336214 381336247
    0x13090201091a1b0a0b100303111506010e030c15030106230304080f0d0c180f08030708090315070203030a0b0906180604060b04030b0703180c121a090d09050105 70
    0x42400c0504060300707a44500040c00c0001300980038002104000800211400004607007013140d10942e203030344011a045600980750080451200d42244618012134003a40c85281c00e851031107401415221122003110008402c00303088400b410014101000400405821030034403011808520101d2050903400741210b0101e00c40100000e001520108030a40d6140e0b4010685030480d40c000030030010030031002e1001c1c0461100d012891040d01c82c41c2d101042407104a9000d60490300312000860601d10b00d5034078030071190410420241c05220f405103c0350340120500c2c40e64010600c6401555903820001010000e4403902583c442c06421080c051040c00c1e02c552820881200545401c142d882d1141800100a0081035000307641d03040012401200340f002c0b584c100c1d40200d01c0d5440c200100003400c141c00030450042c01c0d02500d400032040080001070921483c50340554030580d001d1104a050b0305083c10384034415078001c4070b182c0c081c800040b042c5421a003400080c140c242040790034500901190a01c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 381338714 1250 381337464 381337477
    0x10e010c0806121906111803160e010b070809030a0615090b1305040602270a08010c05180328021516061d010903020a03030b1c030c0f0213090201091a 66
    0x2041007144c1008140401940030a1015100380003185d5141d45c90840040044000c050032842402034129114860981140c450101e60760080c6c0c02c0b5460b80b0700311545003141c010700e02c196051a010441468141d405202d03420300180300e0722000a50030000d61007041e00c2c264642081c19402d1500c2d110502d181d48080c0060055032040c0d002081c0381e5102e16068001c0e0048100f0003946102030700c1000403103a8100000d0ba0030081c29a001c0d4446641d50419500ba0b94040d5a00004500c0c01c00035a0001001040703400c51049016040f20030810010410540754400d4104960000d02c4a100a00443c503041010000001c943c050440c00c0461080d00e030b80700b0f26210100184420380c0c41d01445501d44d01074940302844d0b04490002c02609116040207526203429541c1140000e1424205a41610b4100312581402c0d0162001d00101501a82e00b610304403d499800d96004504150510050740c640c1448a82c0c1d075450200420b00280510001d0081c5805800c4081401000da0b09c0042a00810307013611035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 381339964 1250 381338714 381338743
    0x1a0105071e0b130b150619090e070c050c030609100c0c1a0f010602030406020c2b0c06030606030e0303070c080d050901050f0c090109140111010e010c080612 69
    0x40d845160360556200301c03040e0390001c0c0000e00510400112011a0780110000e40c024440d02e12a599800c0079110410450801c140d40004d0601c00445070140310f102c445088061810040c4503c1c0d16110700b16030751b1101700c0e0301c840016881440b900401034148001003000a0590040c0040c0c104601d115485284c08440e0800780e96a034006503059500c1088150801600a400641d041c0511405e01ca4003580c11590602e04459030700001030103e00c0002203d088480b03550181c1072506403001007003044c0442901d201c1d1a4064040803085942428000a030868800d00140801c0307450000c000d400d41d00c050307009205241c603241c4d03050500c00c40841243e600030040d1500c1404405603103400780d1280200040042414603040422082c00740562045005900c04040310b600b41c0d40781c141001c0144540c103021800a540b60400308003d101200035507041d01c4050500e400001c20707038280c080c2100d142c802250481d03915081c034112000c0d007241400c0c0d0001015100124013204000741c60395190a1600e0086 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 381341214 1250 381339964 381339983
    0x30c09140a150302060c0c0901050109060f050304150c030e060a180f0609080c0106080601050d080d0507022401051018060503060102150a15050a060207090509010902030102040b0406031a010507 85
    0x304000d10031000d90001d55402094a0f885c0e5013007011b072079654009030815600480a04001041d658042d001c1c4030120f98041c4d503503aa82d0483e448044a9640000d40304440007041c0007219411159180510030440710300703070341c002280d403250fa0700b5a1422170040c0032070101c1c03843d10b03d0780b081041d0005600500e4940100d0741c5401c2040620307140d00140010750000d008001e001c941c040b6000c0064118104440c102d20890740241d80340c0041140c0c201501d44010a441001c100751406c44400c1d82250b9844081c50065941c2030410005140e40f41483c001d000f02c91381c000e100140200d00d862603d042002010b890241103420032038403045030540b00d0380940014403502000240c0c882c1c2c8200403001d44924081c0c01c0b50003a003030081070b1001500480500003260f010226003c102030a116240d842207070a140d00429400d0310740f1503201c000b060081c0601c1035554031000340301c0240c1c9003400144001d00412902a98680c0740110040031100c4034103640f108402a1503850700c050703030320000307880596401404e0740 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 381342464 1250 381341214 381341231
    0xa021203040812030103060c0302120a09020f03070b0705060108011b110309060d0e0c090402061605030705060c0a11010614090a0b100519091d0c0c0f07030c09140a 72
    0x9620358000c650100b0440d1050100b500420b102400140d41204d10640042c4502d2213000e4095040e401040c82d100545124040024441ca4260f04401d90090010744641e0061400038046814076540d50420011064009071007410010200040c41c011709442d4000c11000b5003e90784c207038400145080700c0b4200110080d441401c240184100d03101480014181a681c0c1403124507880a000c4d0300409400c40d024000d010310003424583ca01912440d40105840c2c036001d540140314004c2000c0c2c1e0816691403100740300000006400704510f40c0200b10088940f9220302c01c0f00e9000301403012000c2011440e904086041000e10410b424800c40102c0c2200c40900b01c0d60344a86c048018042180c05541c0304501d0011140c0c0d00f50800028000fa240c01800c8880c10b4500030030035030300fa16081c810910752015013101c1111807150700e120710ba0401d04202c410392400d0900e0710040c0c0f600005100b00c9c001500040c04c00c00c00c0003220700907507004110001040c48103501d214000c1d541100028007030340c006034072108007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 381343714 1250 381342464 381342499
    0x8031b030c0102030717160806060a1209050102030a060609300501020d09110a08070e1e0717010e09190201020c04020c240907090b01030902150304060c03060501020a02 74
    0x70341d003003032180340003c44d100d00e0300c1d0300014a904410f40860301c40e142c50001251061945c0590501c40c0e031031039280c3d00301988480040c01035680c0202055410804c98443c80c3d541001c03180a40d2280e02d014100242e10f0b410103c9141c021220290b100710140403c501082046103001e408511081c00c1d82580f14054140c8001ca402854103c680020f241c3d505c002004000c250060b403001c45030502071040800c4202c52102230120420072409452510f60020500300300403110401d080341c1c01210b10b00c48001e044404c00e654176400ac804d607154804a002c017200e00c010075060040741c500610f2400500c2180381040290316884200c2541ca07119440e09034200070003964001c1080442c400c0000d0700c1155100d52203901e5944480384c403039141c0004c05031040107540d0254401021401407406c0c001803c0440e2a083d1500c00a200d003040d00b5040c551a044080d026035558a0f40400e207161810074240c0e00d207440d181c60030442e0114405042410724201003480b45ea6800290034156580c140c0e6811440d1154814 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 381344964 1250 381343714 381343717
    0x90a0209010c0f1a0f010605160804030f051b01031a04181211010b0312030f0411190608090d0206070f02010f060602030406090e13020d0f060f0516030608031b03 71
    0x401514448125540800b04000c0610480c915110420001320300c0c0c845413455655007000780300e600006042445440150f01c0040103008a081c4500506885c01c0d03941e40c0e402445021100017540c007a04031480700020115130480905e130030102464100b02d1000d600c810000c00c945041c1d43c960140e5500c0c020504403064442c411140da45d08100142204e0102900017003e01c0100d0305150b900d5401d0000081ea60308002440d101040481c0a85909680e101c5040024030b10004006031a228003400c0786181c162900c801c4102c20075207155120f0b0400f0305045c0040c00242010300381c80300303503406880303100140d0350702060302d6401000d01e00d400300030381b009000308a0141041001c071500705440c1c0900000d2040c0c0001c003e0085440715101e00e000e182d51a081c08902d100b040710740d080d142d4a140701c3d001c0180b92141c88072056a204d810b200000f006183c2390202150340e008070b140c00d80c660301d00c1800b00010006000c0e1407101c0c840d150900c0a5810300c801c4584901512081c510001030310041198200c20900 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 381346214 1250 381344964 381344987
    0x312020c0a02041b0f18090c0923010f261503070807050907050408030d1107080a0c11060a140a0c051c080c030603030715060f170601050f090a020901 66
    0x41c01444000c24524880c13001003450442c0001080c405428501903501840e12903030110441441c10b01c5c4145000c0c5400090007240310b08000300310205e2804150001c1d0341160086c441c03007241103004000d031190005017031340c0fa42403220003e019080020600602081e0070300c002c181c0d401d00301080305450b50400d0800c42201400165810700034060080356a960004030b240c2140c4088641001584803450140c40070710480c0a007450940041041680035221900540d50318801c04c419945080c01a4032407100c150005c0074401c000641c8108180c050041c0b5101c410030128084415a10300210364801a0207070106a100c041034410120785604498003411882100c82d801c6810764018610100b062410782d46004620300c0441c14540200c0c05d01049101903a208042c054019440c100080c0c0703554030450744c03001040c04070725203442e0701040420722611218010300034400001c03000341c02004468101801600981c5c042c04607a58801803660750840c0c03154006524040061342c8601010040310300c1800407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 381347464 1250 381346214 381346219
    0x306030f060f0b0d0501051b0a08071112040e0703060b04150c1703010e0a050a020403021c06150f030c1202240403080403080c061003080f0f09150915070312020c0a02 73
    0x2a40c1c138052003419001a40710307071401c0703e582c1c080720075040e0164074500442c03081d90000b40380c100010380c05c1d9001d51201440d02c42c0050480e0040d8042525081e0140e105401c541d00b400c480405100d8165058004c10f0060b1400c3d070461820a03051500e402e4840b001c404c441400c00030a4031030342040c42035080d40d04d5148041d51003034a0741c0c0d68480c107004c1406202078608628641c6848005060000700f4420740c1c0540b50300803c00e40d0380202c0c50080d1802d02d01040c80640b05669100580542054454410401420303161460b200c0d40b899820010407035952584452401e801220703502c0016541e0345110035642103005000c041d0029442002040b900071074000074100c120002d00841404460707409040c05440d10001c5500c10782d91136440f054282120b1100a2040e0014810003400f0700c1c01e03a01601c140742070ba548003803e2101410010707814246120340c54a1044000a13001d404e403d01140513181c841202d08580d1802e02c00713580080c220120406000c030169408103e45c146003000f4884140f81e140c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 381348714 1250 381347464 381347479
    0x120f0c010c020304230f010e0103021b01061424071e0302010f0b180c0a270503010c020f030708130e040303050114180c0d18030215070306030f060f0b 66
    0x2410340070b0360742d0b40280142985001c20500411003d80300345c1030300740707007000240460a2000c0300c0c00040d604d0700450700c800343c185070b024440707500314400c02130540c051000ca45c40046803061401304c21001360700e403501c0401d0052920001d40d034542038a00811841c581d0565084590300c02546c1040783c24854140d204a1210310701c8080c90050560541045000c0c1c206c4903004c05c8654040f07001c0066070320320048040d0040c501240000c22542403000540400140d80c141011340140c0800110b14500c1101d10360b840c0ea8000e54001d001a060074450b10004604034001402c5030b01b40e6140c2c0c02c0c1d072401880c00040465000290104400030015102030013812220020000d90810b46000740c0602024051003078164201d02c0112540d01d0480134401a80c10043d4142c2c2c595180c100ba00d285c0d641c06107541c465400e444030103881848154030000309819000b03034090b05204004c00c00161f040b8801915036420113051000c1400400c00c0d00c0740a10900394880ca0016030090200c442401030b0160a5545501045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 381349964 1250 381348714 381348731
    0x26070804060801050406080a02131508010e01050606040303211407020a0201120209060901080c04150c0b0a0506060418110a0c02030f061b0a03020409020711030f0609120f0c01 77
    0x208009801a12002d4650400580e2910140803c0f07a41600c240105503002e4003a00015040155031a13010740007854020604010714030300c48a02c41007650ac0700b21140c0d5229803200d00c800d001e01c600b070380000084403407500d014655180200b104468212684040c40301e8200301c0444551503010152000580c00c40d00241d1400810103522011202800e90100d00c92420351140c0300340c0ca100b194000e41d00184002d0420714070f00d00460300401c0050601140038020071000c584540c110310540003158141c6d6415142d0311107840d002207901300c06403021304264144410300c4107680c1c0d02c00c2130368199004000c51058032007055040002611a076500002c03544000030301d8804507588259400d1109000307504880809000044169507000126400000450084c8403405e02203100d000811004160b440c0160400d03450b60019400c90b0701c010012121400718072030b8440103007000d02c2450040d091041c00780809291508080791141d0427508103c402c220002018050264407900351024001da00000300300e5401c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 381351214 1250 381349964 381349973
    0x9030d090b1501080103030f030b060933040e190f05010b1b0606090705090d0b0c07021804030206041104110c0a03020c15090613030204050906060a08010b09042607 72
    0x1c20580d86801802d200042d164030300c0d4010802c150407a40d04d55203c070501400100c00314000c050740e07050340e90b1111040103080e00303940e200510040c410150283c6a0000e0903c4400e5000f2084042e0007a04003c405010801a00408060075a400300e00c45160003118844031240070000d1401e03a021080e510329000000c030721030070040081c0c0b07164425031803603500c01d41c03034030307840c682d9900003101c0c0d0643c0010610b000400003440f910161640400141860108400da682d07001e1a607003007262203244900300841c03000d041d4900588079000e44802d000114001c1d003410744000751039040040014007445041c192103903098a40da44107a40c510b072a80c2d506611400d4558080d40c84100c01e40c0c090340141b00316400240705180000b01050000c00384c651079841d10300b400c018807000ba00241113601207880307403910000c003507140c5004252041c068100074000f02d24101040082000141c0c001c500c0603071400445001760780722401080c2d080307a040714844a8031508103181c0c01032801103100807507486030007194240030030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 381352464 1250 381351214 381351233
    0x1b0a09150e03070338041208060d0201030b12010c0c0c0807120f05070b0d0b03060709060507080f04091803020f06240d020a0b0c240402060309030d09 66
    0x4989901003500459000802125603000000c1c1d11545608a00802c0000072801140c2c4d00b842e40c00b02c1145041a503512941c54400c210000358643e4414001082104000c000d451801d166003c9062003030060801402041c1205000b000082c14180d030723848480060b568580e070820000720690024040d0f00d2851a0080030800301c008200d814000a140100c0d04190200e01e6009480004940322902062502c940749034945406040c2c0c0c0c1401008004038088804100401440c40700210106500b10310400b45803400c1c0e0024a406d040001c200c00900280da0701000701d4000300c1e000780c100d51300c60349040030000b418480c80e40321580a904d46540c859202c00d109944a0a00c1e00070703008e4544141000c40b520b034a54400701e43c1c040c06429116030b1021002c040042c03152000202810f00c4401250a60200301504410f410070118200d002c5003154207141e00b042400e14615441800d140000400c2090703040d03c02010b4002449004040001481d920040094440d0718400320001d02400469040054a8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 381353714 1250 381352464 381352469
    0x130801020406020d03110c06041509020306011203180602030409020c0f160806070201021207031802031203191b03091e21030212070f0c0209010305010f05090a08121b0a09 75
    0x12038142401c40c48801c0c0200701f0b88840002000c00707041c4603501c0f5035940340140d091a2400d02010b030340b00011000340c0c50810446001c2e01c80904040c00600203810003403d60302c040c01d0140e00000da600320622000d540401600c08890b6090b5002d40c41d40c1911a005003048400c9031004081d00c90243c0a8459504024505044500500035201641c440c020304a00f0303445040301e158414008540420343c0e05210382e100c069480aa240d005d40c100035140d000030b060113841c919001402c1004814003a01011400f00140b00a1400c44100103243d003005424110101c0c8801100a1555810314101405034900502d40c4d954101d0100785500c3d032043c60f10750065901c250655050502c3c0c1000c12070b800703010f4402c032940701d2100c00c841081c03a5900390084548841c0b0600e42ca007003045442d002c0d00140c540249680c0614400c0c0004203414154034031500031254003c00b03c5101d54410300044011556400480704c1805000010502a9482d4002141d41440045855101a0000402000031940080d4401c00e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 381354964 1250 381353714 381353717
    0x1207030b120309270f0f060d020906090a0605030304030609060f0c0806042007080301051e10080a06050a03050d03050f0c270301090302060711031806130801020406020d 74
    0x1016010091084505a4401e941620741c01003091030035500d0000000d40308014a1050001940c1d10444003240b915010744030b640d00701e01d51400f4000c0708090703021941c0d40180103407010a040d0240da00003d4401801801041c056142080800d1800f481038000030b0191001504070b03561140d0341e1409000501101c1c10a6402500e0040f41a1440005000305201055242d1b51707c040303622035030104001000107000c0d2000724900c072891070f608042400e000e04100c9018502c525281d61400b0103020041c2902d030f50a003d40c2010b1611445c913a80c400c182d03054461043d207000100390f540c02c1d400a0080c06c1d140c0095034401600c2c075000080060006001d041102140c0e401e000c1c503180d014480d25040416074400d07001c55800d111005080791401410f8098594010b507880200c8144c0780401c1c00c490015070141c0041c0c2100d8100102160001c041c1d00803c102c002c02036280051340114003e404000000082c464100050400380d0080643c4005001d024039500840d542d079902ca0010703503070b01d012501250 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 381356214 1250 381354964 381354971
    0x5090d0512130c0e012d03150e0105010f090609020c0a08070309050d120e011107050622030b010501140306090f04020d050d0509030706020f100216050105010e0f060405101a040902120703 82
    0x11955096105082d00d02c1d07108800c1c6d44116030650350f4480c508841c07080181503130342e501c2c601203014a00034015140200700f2031290404560403c40301205581540e042145c40c20b00400084d44110790001e51809650303003020885443d158149801ca400c10880e500581c2d00c004103003140d1080c0705101d09408099217168803400800c3d5030800c0151402ca1a0303444048654000302020042801c01d8801000280c2c851000304485072000804103039928020741007681c0b00c2951000521165030000007001c0001d52080f0810306625003640012250000107261800400d2818045000c5480758280c4000c10360b4414252020601c131004010055044841903501c248901440090000c0c000302303180d44400307105005080540202101d0038040c5d4002c0011090240d0f4400401000c1502031141d140604a00c8288a030310342000c42105480d007001401d51441645000305000c156440001004201c5001c2c10b015440341d0720b02d015680b2a40129841510a907000040e041086058006824890039182d02c041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 381357464 1250 381356214 381356249
    0x60501091b0201050601210b090c070506010b0f090f01030908190915140903070f06090f0b03010b03071d040c1e0207030c09020c030904021c05090d0512130c0e01 71
    0xb20f09951050341d00a0100d403840c42510b000b01c20300c60240d24129204640424010709100124640401c212011302500c0004210300b01006800e0003024010aa180c43d450f042c004c01c1e1208204a10404131258072a0744200d082c04080c1c0d000303412442001c2d03000030f100c2d40c8401742050307035044d24038240f142200018141351001c0f407500c401704a4081c2c010301c1542c1e641240607200710030a01d40d5020b1300c2c03039079414070580400003201c42540d052000031b0f0a842da00c1003551031611190005901181c3c0000e00c01c541e0900052003c00861016a81d1000c1ca03441c0c584070604001507419080ca41c1c80c000d00d6040340c02c000f100f9501582004200280b00c1c1c10002800092802210403038580100e40230091800c5100401041100900d03006849003e96220660b46044540c40000381213a120f801c550f502d519280c50b240e0b003001403038403916510001c804042d200144804000520501c9441e0300910700c000441c4c08107043c556185203000090340e00402d8851455110560891450401d00c600206a880e42511 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 381358714 1250 381357464 381357467
    0x6040e030a023304080a030f0b010f0e131a01110109020117070e3a0809190902030907170106030c170a0501050117070503060402030a020913060501091b 67
    0xc41d01148102d030301800940e0004403101c40b001403819140d03140c4103101090b03a4141940048643d010700e00c00d4513001d541d8070b040c00014060744c01480c1540b030003518011300050701742d0b08081301c41038108281c940390032444100c00c0020704040320044d043d00c045242084100703081c400000217901d1100242c0f151144090503144082c01d031450b442d8000d001070082c040c10083d8203030030b514064001d8280e0410700045035101c0d02050861140c0c003851003032030420501c4070058010500005100301b510640241c3c030300b4215200d0f825984103181045010f418800d8400039403a14640c33410010340740c2d41070150341c2c1c1d040c15a1011b03551009402075440c1000054a110780d010414850041225881600c9009142c9401100c0d4010b82c00e000424005028680d000e4001803c28801d8901a090403454002c10844000a062a0020a402603400713944084144000369500080b1802c045604640c040003d5a5000c81a5442061040020101800d14001142c0594203410180301c0814600c00f000c0c641390a02d90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 381359964 1250 381358714 381358717
    0x50a061e18050709080a0308040201090b0c210c19060b010504290c0f07060207050105120a020705010213060f031121070207120c05150a051603021005040b06040e03 72
    0x19000e0141c1424101c440d126450303004203910100900b0080d1030301d135861105c5c07400c144c10943d00b1000241d01008200c00c540c0c101085102901d40c400c04141031203140038441e0740e2652505030f110505290202200f44a01404d4216198000802c0c1541c1f000071000100d40c544007000c99003141c4060612190401c6940301d401550121905000c0e6030030069404403600701c111600e00b0503011080410006c405501c1000c1240b51040694a00109640707850200000d0801c2d000703410450400c4010414424900050025190003090101005942d600c20345482402445802c0b095844040c4d10000001c1d45a00300c41c405140c061380e0f860134407180384240a441040e12400709100038000c1c01049403c138205e00140c4845d4800e0403401124001601c03000010322010f1110000c49504069031130502c11810311100d901c0c1d42890354000e00341048914013015099000340134a4032108a42100f01030149031003004071480d010000c50f0301304103d00307007802d000385030700012107200c0d01031401c040210007000340000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 381361214 1250 381359964 381359969
    0x20310090209130203060a03061a032e0e070306050906010e010911120406090c0906170331030c06110c010206010f14030a0b39030703021c050a061e 65
    0xc0607003070f0124040e44010000d402c007504940d0800c180403070210020302caa10030b0a0692450000792010fa54442e03080500c0e01000b0401910428103450a00b411204a91504d000b0030b115004080340303600c0321140081c43c00003158030192035641020140507085001043c1d245c1a146410b50f5045580c1e03c90f254034041d2002c166203988100d03400c115120230000e00c1310300183c100344248004a07002020342ca0b4038681c000302d600501101640c911040250554100328100c1e510f104002450030040e401e0170701c0c0c00606190140702510b89140075090f800c1d01c030058080d00038680c8000c8421005888001c020410849440200101e104440e1102041d6000244c014102c925492034800a58180960b02e6035039400d0400b92901445411032820003c0c140c80c80041c415200c81040c6500c0580d00c1e2000c04620f00c021400f07008400200c4a50490800184101c039849031050a01507555040c41300c00121403550348208120441c41e104c24048000051f0b00202f01311281c000e0005200b1400002d002048441131 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 381362464 1250 381361214 381361219
    0x206011203020d0f0203070f060606030c0309020a06080910140712140604111b0102032211010804080c0a1109160e04091403030f0a05070804020d0b2503020310090209 73
    0x803001d5030425209411340380c801682807054a0403c90196030351082491000710444805446420500c080d99241c42135500c1c040c8580303824004400160042510183c00d03008980070007440034001015403001b081102c40019048404000603083e40c0d241c2000c0c003005881407800102c0540b030b001c000c003840f400b40700105520300c2c056030700310307116001004000d1008110840350b580c03041c000d40c0350401b8030405000e0589040b0002696a00d80a40607a81903400d100c0c90604080c1c1c3c1e6a401e40124800d0b03010521060000e08003a803840e00c59040c285103501642503038221902c107a000349070422104582c05040414151920481e0f52903803d00040e950005103002c0e80040c54004550045240641100b15182d0040b00783c6440105a40740703107410f5610031111903070746101c4a424081401c04a20680b039100c82c1d00d1510402d507007015800600d6084030b015000e8503074601d1000ac6183c82c0c81142015010718602260049000030349207000e40039410440300c3c00705155039003000041012003030084541d0385000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 381363714 1250 381362464 381362473
    0x150603030901030902011803051b0a06021009021914030c040e0a03140d052a0316050304021201020409270302060105011101140c091c0819031e0b01020601120302 71
    0x800c1c01100101071068050781000101d001c014070301c101c40c006502c090b40c0140c000c3c010701c00c01003d49000b58002104050b02640f1804002c0142641c0420351081200503803070049911b1a0038000900c000115a0310000a480d42c0c410028a40b40c801070a030056950a8043e1410a221041008210f803403a076202c40064100b50a50310020741f0862003401c00201d1512003500700a844405030049540803200d080110385079001c650080d14030390035003c1c1d04403195446c1c1071451602c403418030650310701e0505d008c050040c00320200d011581d07441c0c80080e41c4603a15000315190b503500c0d08100042d0045690014401d041c540f1180e030b103582401090550960550003c0569034a03000c0115590200c48540300040c1d540d070400002b141081c01062401b40d000815160344a510010412000001019481044080d4001d0783d8000a1140007942c1144021540340c28185c0b19400b0143c014040b001031053721400c0c42080419a1141d5501a030088030007a421034660740c2c1c0302c01c1ca004240e210440003030050b921 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 381364964 1250 381363714 381363727
    0x80901153b151302040e0919050318010e030a2607120f120e0604021002010b01081603060902030f01090b060319090f08030a0e0c27040501061d070215060303 69
    0x70b4480c11002070381409082c1c03c1460b03c40e400110120b0b0019002501d042c0d80410a001450300100403a54480d50030074071045d01081c1c0e65456664178441d0810904c210164811900c10981c01103070182c0140c1303400b50940703240381c0083c0f42c0350880900c21004901440040c0710304c15100194802030310349141d84031000d031006411130b2400741c8009241c010b90404102000c031489640280758000c654074103800c40c00400d000d05141c8100000a20403515403811607241602941c10360303030320204164000600010f5401d514003200c13002c502404054020303c40c428000814006e9050541c9001130484072500030400444821030300f04401444140c40d40d2044001030801c2d40c100302000e0b407050301d07800e1180b2041035252105070b4407041c041c0c10860f8a40442d990341d04000315400400e1142e185144011101c07591301040303501d2072078a0307440d41030180710540c411040064200402584541d02502290001103080c40340c00440e0850345200701d402030700600806844504c402500d000389030203050000d000c0d6040c4803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 381366214 1250 381364964 381364981
    0x9060703051e06040b040b0d0807030206061e151308030c0d0809070614090a0902070506060a180f0e03040f0f0807180207230c0901140a06080901153b 66
    0x50607030405900c40c0d6906494400d540c8c0301003007a00301c0c0340700e1040e00d91914240d040290800070014a068064562686c0c1c80201040000c125040c0d0f1504580a4014004010f03004006004100d07920308070010852022440b16000001b60290361044002c40f0741c4044002d5088030051400d0382e40c10401d0740031840074003070309000e006040030001c010200b160800a0100000d00c0c000c030319030b006d1000340b58001501c0092000501c040ba034004001c1c1c50010130305c1d107081242390298901c1041d04100c60b5603510b90700c00300c1e0348642000b04024481000c4a40351900c807580074140369010b100703000f40c040c110719001400d01800700c0c0c00c000312010113414404000719000c030f4401075408400c046450104e040388811000054880401c01c2404680040c0804604001805200c401c1a0020f80c90311340d04400354510f980c0c45a11040c2604c1c1c4600d8441029211000e2040c054942009801512040c15034041603818080d4016060017160620005400c1d0350b4070350716030713000d1542131012004d100c1640001e048003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 381367464 1250 381366214 381366221
    0xc170a02071205010e100f150e010b0702030a0209040c170705030d1d03100e010b030c06070204091403030a0f05010902070231140108010e030a02060a0c050f0309060703051e0604 78
    0x600803030010038041c0d910380403281001000741184400c0f50740c1f4072001c40c40e0300b101e10680d821040e1105240c0415810001d480003071040520030045849000a82441192414810a40355540c003a06414450416260000c036828560240400c01405900d4441e603101000402000f2660040e0281c44c000d440c030303402107402d00501c4c810a80002c041c24100d0f41c4e9030324204100801d0244241000800101c0591400d094810480c44d640c46540401d1001c0121b44d2103008641c60198111030010351064107141624085e10100070340138550001008011650000b50000f41694100c48020805c50303886038072080881c0a000e401a402000071260724180074181031070140d0102030f018002d255442032000200030348a10744a1106401031100040207000d200f4080e590700040e09001660511441401c001d42e00d040080c545a1195100c1d00e2109281d4018011113030242d200180469482ca054260a83d03102070586251300003074508800203d01c0300c11200355410210700c910000103962503050810014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 381368714 1250 381367464 381367499
    0xb0108070f1b0b09160b072414043813060f0608100b0f060d0908090907020309030c0102030408030a050306031219120204030803010312020f010204060c170a0207 71
    0x207200003000030102140d21a07070604c1c031540d845001459402c11040c1c1442190400303138488040380700c0500020001914200b561000c0c1d90031003541c01e4a00e44a81c400c00b01510380d4282d011031001071030050000b03109450b004002c0e0004801d1050880d92000035201749440c100c00794484510000c2c1007c5034060036000c1c2c2c2040800c1c00398070042100e50b010140041112b4103584068180c0e40090050038102c501809182580300049940c3d070410140f0802040c0d20703101e800e034092151903a800b0031100b00118001920b64405003d440340d4002e152040c0c0c042e64035030003410614030912402c0e07034080c0590b100004079816030380d00c0005503060000f004019a010381014042caa072601403c110352400b60461400303401c00340b071326124406c4030080d840805892910881400440a4010401480496010300031681100e500c01c0d09410504800e0000320300b08280314511824950000030001100342d80145241419401500d1004000c0916104070301d240c400e42c01c1d480d0140e00158000c1150700f6813041c0b85800c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 381369964 1250 381368714 381368747
    0x304170a090b071406090f0609010c0504121401180b09010c050a030c02150708041218051302090a08010203070210090b2e060801060f0c0b0402090630010b0108070f 72
    0x1c030b00403113003911030038408104c901d001340e54090114440700c8641044500e401250307241c000c000400c002500103002d0f2203140140c030146082d204040041000742550b404020310064003c004207a0a8412040c0032280b0a5058540442c07072400700703103031100610413500d502000c0e869840c07800c200c071344090300900019880a000d501800c4c0d6600da9134808540101e1103514107030364a510343d260510f030490701441c0e81d01c2100300300014020040d0a08004404090649108681000c00c9038000d151000191280643e500d0704422000030000305030a0540156000b09125001c2d20f100c0348250300248220341d6a0b5030007410012050300401c006007042d5010311200d4451a2400c0320500406402002080240e400500081ca44a004120442d0700ca80d0030100c482e010310345012910344a8079020750800d40078101a2180602c500810150b5403402c0b52207141c200708003c42c1103407040103d141da9126030031070b16102c500d5080c000e42107034561140078503500c28005a116480c4580c1502c0013152840102504a030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 381371214 1250 381369964 381369983
    0xf09061209080318071e0e0c0d0f0905190209041202070509070504030302070b030702030319060f090603021003020c030d0e12070b040309051005090105030421050304170a090b07 78
    0x18003142c26a0300551181c52400c42c0d5134040f2410898861409195900c08030400150b01801000c08220400443c1220034070b07407040d040780e00e40c1c050803c0f9500c0b90924649803c1d25101e10841802019001b8801007070251080c0c89122107011001d00c10035041c008025440200500014001040885280740e200407030f00c1140c822a4840b404100000d200760b5178100440c0000c00c0420070142d04110007005031080b05e1580342581083d2202170b42d0380c08054510a01070b5506d00300100807100a9210900821640c502c45003041c5c2d941c5180401010540002d070f004070660b0078001c030344501030300840c3c0b107402240004603d031083c00c0704d49030001c0020348400707c041e024034100d110b240c2400c080a03110140c0074501070704c0942890b01e000390122400c1c4c0d00960195155100d4505050b401a05a85103080c081c01e00a40d41d036520710b0500c0c01d011071f007103038102c1c0b8a06e19015040c0240d8020081c5104503c50340c2c520800307080b107001420280c01169000800204200b0701070080c641c59034003400481e0701c50b05000c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 381372464 1250 381371214 381371231
    0x403020303070c03050613020f10140f0a03050108071202060307030f060b09040c0f09090b0a030501050c0a0f0509031f0f0905060601020c01030504170306210c01030c0f090612 77
    0x68216441070400351041500d403c0c05105002050006c2900a4203002c40360544242c1a40428070740e100003100c040c070074210040e02100e81ca000b030055500b8004888081c564a00060f040d250070342c2c10082122000038078040011582c4500040c1c01c8060399100c0d84180805030145c2e0801115034001004402099101c103141141e0305094003500c4007500100c1029500e03840d040d02440200d0303c1c142c40c900d0402940112644029410005250030765846510204900511202007000d1541591004190b0341c82d107003c01c103070b400800d00039207802050780e80c0d112890507000e039049529000d1800704a0b0f143c0c00000c040030340b80e10f07080c1076510240b4411101040084420300000120b901c43c000136180c0750000c104204003507905110301d011840090070b0801990074281c403100c2c2d00380340070100b0b040d04003c00400300d2003a9440c1e2280c0e450980d0035503403544680b03100014151b00d660035940050701080c01c0002c1e500f2400d000300c01c0f40700b0041d1a0307916183c20302c0c6040011036000c0f40b81c0e4009028a65681d01c803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 381373714 1250 381372464 381372469
    0xc07090204090906112d071a010515030c04090c030b1806010305100819141009110109030b132420070b010e0901060e070c0c090605010f14040302 64
    0x1074001009500000180d038022400d00748169a001245d000b80b0302000c10006001d08040480e409621503a441809204148640c0c10003036840b40382c0000c1d0046041c500703141d060030b4203c1c2880b41038503010751b0044043c0c80c1403038000c642400705039461100948203000c10f114540160788403955803062440d000c50700082200210340d0300c0c0d808600c2607540c41640c000300f160070750f05401059017000620300f00321025450040c0054070752142c125441c11845044640905001400c1c510703003107860120013654810140081040020b1000090844114518841140301503005070a51401c82c1c0d000000b240d89036803868105580300000c080c04942c00d0340707403c4844500c54849602410344078480d48001512240300e000e00c1c928400b250700429004001000102c0000b101c0c0c045c00c0d4110360700403001c00d8003030f01c0f282002409441c00d80c002e20311840c582802c120341154015030030030a042c0502440f4003000c1e01d40d20103006442c100e0007010702084030240c12510312031140461440c404501c06603982865101da00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 381374964 1250 381373714 381373717
    0x100e2109030c0a05010c1b0e0a0911120a0204090204061d01090605030d0905010c0201120509031c0e030702090a0908391b031501090b0a0605090d08030915010603150e0402060f0c070902 81
    0x1c000b502152ba030381c446000c12480850240a24004a60302200d0410b11004541d40c2d82440400900858956420b032085403500e0f042407001d80181000c1c001040640d04840f000550300b41301c2e2400182c1807a4000402d81004600d14000c0e9415a49030b121403410300f030056440010041007241049101403000444004510031140544c0081e40a55903441c00e912255220103135400031900c0446c40c103480503d61000c000201c8001e60f0341039608a40e1540c508039030900502c42400041d00e1420005500400c000d074a050342a2050384011420000080303680103c00e1800c01212001c00c1c81c0e0021400e01003000c000308604140400040807151006285040c0d04020f40003a07010b01c40098075220f800070316113001c585800c054021841d14608092030b41d00000c000100c0d000340640003003c0000400c1e4102000d01031844101c041c0001c80e450b950751500020f00815940003a448845400302c008105010a299030600440d002010b65003424961010318800e40c2c032031020600f240c45a2400003c250300b40b0f00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 381376214 1250 381374964 381374971
    0xc2e0e0a0b28030203010f0609080a11121506042a030e0a0813060207230105070606030f05060f060301060b072d0302070f090e100e2109030c0a05010c1b0e 68
    0x26005178881d45040484100106660040713000e1040d200350511001400242120506400030200009d54a684d00426007000001060569a01506013030350710b12010031203070300c1c01a1000e5500f04403651000100440101c540072420b42400c901d20030240c00319101e03030000d8109510700300c10380c2e01c08003440c4d40d85061b60340265030040f1140c03882c0b10204001c2c1c0e010300440c8001e01031590640c80040600c40c00324800291180e48505100d0042011028004154040c8000d55880758600b0401103250804580d80d800c1140c407291262928000039819040c1801940100d030f030028180740c00d18820355110a0b050b1180c452802d061840a03402008800b40d060000716114002c1d00500100740c1840305107840003e244d0071403640700c0d003018142503400d58000ba0b03207a056419408000b5609505288940c00c0c1030901000001402c1e841402812401c0c9000080c00001400c404880d601214501071041d03801c100e108140c00b150b9194640e03004541c01d01f403881002009086c803048039540354100741103e01800d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 381377464 1250 381376214 381376217
    0x6091b0e15010804050717190501020c1605130b060c01022a2803090b0c0f01060509010e0c070f060c03051501020604080d020c0c2e0e0a0b28 62
    0xc00511140341d00392299a100c561080c41d1044051400d500d4195a070980351050150b03000b00509000080b10040c86214408034680c400c0340b18003101800c100d40030303402012856401d8051030102e61552240701081c2d004460002d06903c21405a558811000b8011080e0f41c6411023010003255a2248080c030040404180e0100010014800342940070001128844410107035407010322a420301104801e81d20b4002c4c8182c40e520281c0500300d00d030854203055a03500a40704d108000c5044400d2902c0817454030400d600c640300070022281c1d60010000281c1080c0b0940e00e9a0703882d071002c81c040510600007807018030b00401e030503444081540c3e02c5400b1901c030001034000003a5030b4028010401e618141903910030700c0900c000c100c1400c154440d4910b82c0f04a142c070540301940000d00c3d100b11101446401c144850040c08201c0200610314000340f0040200d884041071a140032100c0b40f11030050072005800c800c060407807648181007102d0402d459016400050b030711300800034100c001d581000019000ba041c1da = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 381378714 1250 381377464 381377489
    0x130b04030c030b0a11030a020306040f05040b07261512070906060e030d0906030b0109030204090b0a230402011d030d0c050607050a021203062206030b060105070f06091b 74
    0x390f081c12203103003d014101d000c0e2103040c40c244e07001c08246072040e01e80185407108016560745400c400200148440301c45107a04c641084204400d1000c46035001d4801e00f800d45410301014103000c041c4145a00c0b03400e100008200042c00300b1440703400b46a000314181c07400f90079050118003c10100e4509116540025020350704d4200600850758880000385850740164004c0100c140140d10180003c0c44a000710800c0695a402e8411560300c80c1e8010002160081d204209a00341030502030780400040340c0c4004040e040003440c5c102c2d8682a80314036a400e540d003042a015445136070044900004070b68100701c09400e80c00c60141160703000e2081008201140d01d4036800391000c3e01d412410444d000327080c1c009000007401200e01c46d503008109211003a10f076040081d642d070b40c2c01000452005031441141074943ca07801e0060b030403d815611100540380a0452000c01ea521840111114820f40070f009141114a66200000511f50b42042c40d80610641c1c00280c3c905100c1d107141e0101e1506c3d070105915001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 381379964 1250 381378714 381378719
    0xf080f04030809190803220909080421050604080a030906021209010c0305070c0602090406080726010605010e060703090b0a05070c0f06080f250f0e100212130b04030c 73
    0x1e198040303022600e2115614407013035241030001a10ba000303121003200106510024258442800001040038207101c130006c204500f064184111070381c200740188001020580018000078000c0c810300d2002550000007444070742d455654440280e08401e40f0042450b4481140c1400103016001801240316600d030b04a405d444d2404640d800c0d1401e0b240c907401413500e48814030100e140d100c011400959044000560f5802103403022400410f410740c0008075a001d01d003008110440040c01c07483c1c8420342a03030380640042c2c980c3c446ca401c031051031081a02081510030214280d04104020740311490090520720b41c10303980c84d06561030b01d0f0f00407005400043e200241e120f0400c002a40c03000041c00c6c00e040080829800d0000240089070027422040c0791080040004469100d44240c141c1000c04140400d8401c404107500079204014440109000c42c48a9010901d1410280780408403449140d006220030240c0f81c992900541c003800f2407481e440003a080c003141d400d5040d0014002035100b4a43d0300031251 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 381381214 1250 381379964 381379969
    0x140918090c0405101a07060c0504050a150509040b0609040903090611060147070209090102090f130b1c0303110304051015030209180f0a0804030f080f04030809 70
    0x781d01d440d52203145001d0521400074a551041d00c2130340d4050302201050142e41401d82e4907401950402010b060600c14428103581d4088058801c807032043e140741c52403d84444864202d83d0140100b04005007007842101c600d480d083c0c00203101248064016464004040d0225081d1740300918260080382c2c100f80c04025603940805622011441e00703000c0d03c09035040411031046820f02010214841083d0491101e0010f440c00444135060180c1588071001c5080843c80d05098000d80300a901c60800c03000003c04584040c021100c000b8001084910302241d82010481c448151406548000d80e0b81d56200c0255107455181c44610aa4201e4807081c84640d490003e05885660503101c0d0401001d0042c440000e100140718170b800c109600001c0b918200701508076080440591000e940224101c0501c030140540b048428007201e0501c040c2d400c80a0074050741d6a884814490050015100b00810000300e0305141c4030882c0c49100c0d154040c900003030400c26468940003500305444000c0000f404000c6031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 381382464 1250 381381214 381381223
    0x30a02010b030d020703050c061b0601080a122a08040911030a0e010b0904151b030905070b031e0c0d0507020714010206010f090b01110f011e0e030a14091809 69
    0x3c101c0303100904485040d696400e4030356071a03054180c0601e0010070b8001640e403030500170b580080071100407a50b25694a5200c0c2c0d665440030f02040d2150044001c0d55505c0170700c00ca2503507000082c040c080f242186a801c0c045050a0b00c1c00c041596481c0042c0008154202e89010b0305000100c0f0006a980306d082c42010913045800c042c070300800076894513261010a403102148594000d401078489100690b125202502410340c480c44066220300e002103220040c0c0e00f5900c400c0c140d50003402111075240c0c480741405011b100549186942d40008510740121003090ba00d078591140d204006a814080245164001d070f540c02c2d1040c6000d608034201c10f000b00c071600354034050b544001348000d08a652500c0301d1001e407424a4094a0303090740d210f280c07007505a405000c1750b400710b2150004480e4044040300172680200700a0307142603c1003190308804580c00c1401d010b040301c01c07011240950325003100b2003c00c0c0d13500351500c0d040094640b8207000060080da03484040d542c04c5410410380790700910344590480d041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 381383714 1250 381382464 381382483
    0x9180a021810020a0201050c03070605010605030103030f1701090b0d150b09130b0c090409021302030108070906030203030a1107180f0f0e1c122306061c021b030a02010b03 75
    0x1481c07001c03421426803640012001e242d05e8080c2845650b60742c00095003030842c468402c001d0921410100006030003984900158101d074080d5030f0f03031100400010f4040302c4889111240f4061001c0d1000188109a41c503840075a054200a0044070300c0a403d0303684060344402c5d1700071911520307503e1040318881e0400301040c0e80d020b4490800c01c04c0c0d2480b2a50b5a90546101406051780144042130081058546600800605070014020794003800c080b003d44000c0d44c001d0241380b80c5801882c0c2c000648034690700030317102600e0340200514204642d0a004803540001220000107500c1b80902c002112840c0014800300b001c64020007080222005540b04203458040d490080702ea880d015260303503219004079001526180c488072340218010039100c200c81a041d030f05075071104a890304a0a803841d0501c00309985103903503ea4030b001000d41d1940200445170103031024422003540705800c0c81569050700c0e4011720380c039031528840c1181a2880b8806901d1034006162001c0980c0d07451188440520781040b191300d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 381384964 1250 381383714 381383719
    0x15030b0c25020117011a0d060e090a050705100e13110a120b09061f020c041d0d2c0103090821010e010515030405120a09030c0f0b09010509180a0218 65
    0x842c1d505d0810005042c2c500c06e150f540d0012004203000015038001e411510050107115030382c41e03690814488207615072000c1c140494a40c03041000004107400c1c1900c0811030b440c000d440d03421182d01d0030b205100e04451501a0220a141c1d02c030307076036035007002540f02400000741d0503540d4200800114100c0710031905002d00c40c3e0300c640003003000c01c41240d60350714951039090307032440035150280503040040e4035002400145070750142c14171690b06540f41811843c00c081201a2040781d000d01d16401c01680c0401c0b00d0741482d05013410038140c684c0409000030824a04101c185000114042070342c80f5400c00d07401130110348681507034100c1499942d02030304007524003401d115a9100101e52500c80060030844000f104100b44490100c0003506102003800303003111281c0e584181036611008504010103079819400111507084003140081201824459042c0603107000030b050a15140300c26005407080d030081280710341c1c032296180b4950305d00c4c1041c076a124050700300142c0160315020fa220301001401070048a550 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 381386214 1250 381384964 381385007
    0x60e09010e120405100c020301050c07050c04050408300103080c100c020c150d060801141501020c040902030c10030606030c05090a0504090c0b03040c06030c0315030b0c250201 77
    0x34420350360b04202e03012988210340440903100c43c100700740d8181c1081c4070701030340c95445d00040010b1031a69000500c400c51194080d1001100d00c182000101c41098070302a0010705c00740a483c0a0155001c0200380c006040245080b0301e400c240c0c14107110003002d0300300701d4140c0004134010716038002c00c001d441681810840c091240b4500e09000035622450150118400e0032440039607504540401d0440d000c1c800c2e20700041c064207441d220b20350301a0003542d03101507c0107807507800210840b2050850081c3c00341c051b0302401c3c9001d00d000820000d01312100c42079915001c0d00c08080041d99036150100245111504c02084a9140802c05007c03a14a18950021710004205004450b03641038900010b86e4400c54001500c5010750400d000c10034029081100b2010f0000248824000401031040440b94903580a0280340c2242000700c065441c03600d041410104100010f0000480c003552542e4014400c1c03000904040b111081d000048110250301ca03540c17031140c4003032030955a000c100e0100c1c01a001d800e40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 381387464 1250 381386214 381386233
    0x4060509130b0c0c0f03040e07050304031d0a12060501080d020703080301030602030711030412020f0d020f0d020301180f0c06051e070309030f060f151a0706090501060e09010e 77
    0xe2800340e10040d8000c0c00350b01c05a00081004420340c0c20368031130702500012142d88944111480355264428040ca5480c5410000040c0030310340700e0000c40e0300c00c1da0f05641e480461002911070300041c0d42d10100155004c1c540d80b40100700d0310202070541000501444010070700c2d501d003141c10390505280401034030071904201000e2022030020401c5904490780603400590b2036862038001c955200d42e2001c003060502002400142d03066414a048002c14004c50740300030740c00021010001007156040e0300941010b08584001c0c814a0100700020000340042e00100f8240212940c01c0c42030424a50111307100030642e82c11380c090111080c40031020780b28074144076282115203034410140c80c507041505029440c0001d031910401d8821503802d002941d200d040d603203085174540746c440080c10503050688075040c07410020f16a100610301005003114802180300222005c3c203940171500f6482220155001c50700e510142c0300142c0c1c00d109000041c001e012642040d400d060260354290741005506070280da008603300c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 381388714 1250 381387464 381387481
    0x40b0a0b09060c0a050d02100b0a15030b0315090a0506090f07210204140106020f0a030e010e15030405030415020607140a0c05010e1b090c03040209180102040605070204060509 77
    0x21280141d00c1110865102d0f0040c407107441c5010100c3d00700900c640250181c503100d0b01e400040c079006451052000317000d208401d00900c0300104441c850080001c81511084084a000368020804042e020303055600c02d08900607000d0121200391400c0000d82d202c0d42c0d6080600c0b078288612a040004d0002825055418141d02540c070409809192007850303a0089060312074110f0444030311001d501604c14000e014441405400c1c501c0700344100e10244c05007144000502002151040d00303036915407a0510012868001110448808040590001480e0700184101d0400c20040e505c0703239119400441e9603038140512496501d82030502d050079980310100b03100355190010a070114001c0c01080c1562600e6042c082254080c1b1105805030031940391000180c4024408200781c0a00a40e40f1041038803030403c00140f00581d801150280206101480420018500b0f00d80103a0488030309184240344008418065089a0280e41304d0000301c0c03000a802c40c11401c2c10700940008040448058034585080904c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 381389964 1250 381388714 381388717
    0x1517060d0b07020708060c0304021804200402040302040231140405150607030f08070207030b06120106030b130606122a090e0703050f0105010b0720040c030209040b0a0b 74
    0x800038100c54071500020652442004940700500144089901d40e040201d0511003603481542c09074040e4150005044056800c0c0030090b005507441030f005d0016003420414001d05821002c901580720341c08001c00405640d83d800a050302c03001c0100e42480780c00c42030003204422078846502460f543c00c031072020009100004100c540e400410354000c24190345075480c48003104248100c083d80440042007080c14107034880105610b1203259200da0f0f402da02c40d208107030f0b55118284002010812a03030009541810700c41d0900030003155040001c81d00b140c0386d58a400340c012013200d03404a03111004e1000300a00205006490041c000610030084400726916400040740b0380c0001c500150084031000101c00c00401c0080d0006c0681e13103020801d108181d0340395030b10b071207440c0b005503018071030031503110460401845894101d8186030903507031405095540c0c00d0340060800a400050107203501c0d191100d81c9503400395075400840c42e500142d03510010001c002c1200c0400f4080c40c0104646d4a0600004608c0750 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 381391214 1250 381389964 381389989
    0x105090712030f03020708040f120308060319140a061b0305060a0302090703020724020703030e0c0d02010f05131715010509010605220803091e090705071b151706 71
    0x50050394544050034414103c2c448c036800080754018001c00021200d17455004052401e1080d65100000c0d2111780070195929034007100045804843d00590000941c04400c0314605c8540300c0540e02450055101e1000712000404000040f140200d0f0502046a043c8200340d803000341201c4200300e090945e008a241600300405070b85c1417650000e00302d024810f103c2c2c908030381e09051612928091008552101c007a42208004502090a000c1405c00041c8003049140c0500340142840715040c040c0d40044035504051407140092010421441c100305108010410190050010845011602c8581d00780303003000d0b1000c020000c001c08401400140e5904203900d0440d5500c0c60240c2d1566011009004100c400360070482e98520400800610444080050700003044101c2d000d254110205800c00d80007410054200e40c0810060006030009004a0283c2541402090320100c9502440340600010140e9006900e00a4140100b20862036000c41c00c0c0b800d014200c0e12990050401c0c002041c494601c14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 381392464 1250 381391214 381391217
    0x1807060e0102010207020d050c040f02120609040f0519030801060f0818030c03070605010f0503060708060d21080a05010906080a08090102150f06030c102c0d050105090712030f 77
    0x10800c050268400d405072010346400074043d0034080c0c414a0200e44c2c4900010055000e6400c0c001d0b030942d400180d200f646e019004025405046680d0f6400300801044006e004403524642042031801107001044507140b80800c900303200141c032415080c05440903070144c0c00b010401018a103515000d80e40204a250060b4004400d212000d030641121404d5005100c141c001038400801d081003404080c0d000756040300c10b009d489104817911507050503201c0f0380803200d1001007014540403422508103507660b07007070090080e038a4921010500c049002581c030041100c10004180d0014032031501d4103031040c0c45c0100942e0b441008864640701503940c40c0d20440c0b2000e41080d20100d02c50b102a40240700798104220319205544451a00000c01c07a0302301c8040d40d110f0b0091055000f1074045040c4801c2c40d451072209611906400354160019911803200b440f08070074840c0421818101c251101c0400589942c03041c40080303482e1410308062885c20b0003640c000c1040101d400c40b1800865044074820300b02c101607 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 381393714 1250 381392464 381392477
    0x2030610030506150a02070e18060127020301030506060411250f14070f0f0b03130507030204020a020a030201051605070206030a3801081015121103040b180706 70
    0x2080e000600c181245125100105130000d40c0303420759079004c0b4221040e104085c039504c0341034032100342c08540102003020000a80d404100140664002c94810341a10121001c81e41c48502e08202d1440130ba820a074811145039201c2810f11125241c18020910790048603140d05040604c40c103468003946464400d140c1c11803040e460044144000080c0031201d803504501480c8082c058403443c02c3c3e40c3c0704584070710490342c2c0d100da50100f4005015103080c01120b50714041c031425510780d18910a80011030704130454851046080020050312180041c0407020207507005020105241e04000e03095480c000c14520049840041c900045a00302007507403801ca406585458595580c20071075401072414298080129071001c0d26842c40329402c2c1801425404030840094041d820b8170010745060320243d4001002c10351500b028005812110b4200c007207512145440344244000c90740440480b1701003030720700e11042030000401060110030010960810b40c0c4507000c100c2a41021041519924680a608104800d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 381394964 1250 381393714 381393721
    0x70b0f060a14060c010e0a021c03090603020a27062a0303090312090b0a0c05030906060402130306021c15030b0601080601110f0f07080a0206070807021c05010203010f0504020306100305 81
    0xa810040c4d580316883c0741c00030003c010f4a200800d95411004104034400c040700800c0d8a11750580e800642e480030707495100c01003054145003040e0f0207908440400c2c02000300e4a4419041816124807101c0c6030f131881210350b056941460001081c0098800398034050290a01c03c0030f000700c6d4031b007181d18120758051034002a00400c500d070884100f00c100d091980d1150806881d941400095902e86014591440c1c003001081448a001d84050000b25000f203190f800a1001601605090f001898002ca9080403013020782c0d101e81e5103070220f80200c14409600c1e54104c100443d0131400f0320074100542501c142c0301410340d02d55501d0300349040f00241014100304d50080802c0729a405000c551529031080819100c016251808680c3d40f5128945002640e11600c140050b05c18000f140c2007042c2e07a000391035145061410f84a0f0603860344101c00880c5c202d02801d10342e01a503d441780424154030310910026a0320351420107603030040c240a4111a100701e01c1001802070340d540301c01042d1303620301362420007040070b0340c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 381396214 1250 381394964 381394969
    0x114070305070f0c03021306080d080106020d12061d04050106080102090310020918041104050f010612050c1317060a050f240312040f0b0901090b22030305070b0f060a14 74
    0x141313070b40c0000e421214000006c8810405034120b54181c4000b0012a8407000d030803142107030102004e102d8503000d46c000c41c200c24a41482440104034000c100440071440c030380d0762110501061043d100c904001041d000038417080090a025010042000320000d6081c4140c0c0d80000e5158030b140d00d651030002d0340c00a07802029485000c031607200b034512030f80408070500d45424158100d00781800300c0b520881c0f802d00000c1c0c10103007000c01e030ba0603600310b42d17541c03142c0d12a0115624010300003c1d081002c6060180070030040088000124000392040c60b41c10001c030124210120710303003040503080903070483c244000c20003110308081c143c541c0010106401094030384114003c80c41c1d48000030156402d4041e03884c4110b00000660700910403640d4007090215032710380c0c0d0b1020320303a54051519018001146000208082030410b0301400b00c5201c0c81200d16084032140e28110203a1007154012400321706c01054030014041103d0b000b5a000949201003026441c16000040c040344031805030003003007a50780081c54240e8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 381397464 1250 381396214 381396233
    0x9030509120a051009021f1b0302030705120909070206010e0402061b06070503090f010501080c4c020105071e020c06030c030103113c1e0114070305070f 67
    0x560010280c1d00b00300203840010001c0c103040e0b801640550900e40b40149100c5c00a00c0c20301c7d0103142651002c410440aa01425288849680680442c4020b00c4000c003c10000d12452000c203200d0755803241da0b14194400e00807014001000788065400080041005844010a003540140c0c1210305950304d588010520605a040b013440c04002c0c4906400c012900f904400294000c100d0360741100d0300404454921400c1e68400d0040c018590494001c45c107450400ca03c0103000a410100e1301783d0200346941c40f0399855003c040303080c1040c040540c1c141d1070a843c10040351842c00b049100030b00082c6822074002e0702500c1051101c00884c40310405800320144280710303d40700101d00a04c016075a0a11010141d400d030001e0009950342420801c4550040c80c8c41c030702c00042d05010a0000305e500d44100e940e4030b0396031550300c6592070b040c402241d683c046aa525600b400600041d0013680b0030310b92000c0006088000c0d0940c04040404100710103004250404207036084d803a400040804101014500000c04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 381398714 1250 381397464 381397483
    0x4121b180902040b0d02030a020607080c0a03020c01081b0a0f0203040b0c07090609200a12050a050a050903031308030a091b030b06011b0602030a1e0b010e040903050912 74
    0x9019403080c100c00401515044440e80c00d0080740d0501c42c0702071321000c00030321414821000b0360650001010000604000001d8181d00b4015600740d801c000b01c00ca44141050b02100301100160095006028a5078100488503004000e99203003005980e440c6502e50031034031401440c0c100744070544204a018510030001c80300038004205240c1e844460394405190785800c54020580114201a000300d0a45294400c161506858440000d10701035600180b81040d808004020200500d41d040701881100b01c0c040d46002d80c00c1202d0005192070300d40e07103030412190701404844081d0410024440c0070003c44034400841900800300503540c0e07c5281e0040e0003840c4044004021411940c0711000c03284004004500300c9002c1c030103420712580c501c00115143d0400703018408d56800303040d0b2807001090103940596804958800002039814418452034000d80d00c080000d901152100d11192084d41c0c020001c1043e00d00036102440901140d56001c0c200780102102d250040c01c0030040420200c030108100d544c5d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 381399964 1250 381398714 381398729
    0x20304180e0109122a0b04140703240e060906130609020303030f0a14060120010e1606020f010203100b030a0b042904050f07140f070c150e030d051806030a05061504121b 74
    0xb900d40f4060541f03076180cbd10300314101d50182e14010b50b418a08002140340c070302c940c1c90711001e4907040d5260950464055000a015900540d44811440041e01c0810003140541c2c0c101d00c1e40101450461401d4042e1500143c1201071015020140080f80e6009001010580801e40512540c0d1158104090040c0740c5200c054030580719000c11004803a02c140c0c0a0070580f88107900352551801190740b841e01340d2006450200310301d542180c04000c00d030101005980c2020940d000442c2c1c0000c00c500050030381d0310310203010301200c803011405070a1220785181e4020800064800380410b2800080042007058014845014880d0611030303480141803600455480080041d00341d602c6058909003000f054150b4040c0740e80c1801c00c0d0710307800318650140724000404c0360018014181180440411240b581110101c6a10a4072001c0081c0850f51000e002d14884d01c0800c3c40041c062a005c01000784140503003138803e40c011020401408880c0da0784a400100d00d8200300c09590712410346030219440700780f6902280b03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 381401214 1250 381399964 381399983
    0x901140a05100e040b04080319020a1206060309020d06200a1e050c1b0109090606170f130809130e0606010f020304180e0109122a0b04140703 62
    0xd500300160310440c0160003004100d1000c41e25492074000c0564140c50140400442e41c00180000e00900700035a80002c1500310804081580e81042060b81c00600707060010032240f202ca01d01d0344505100780b50050506290034040c062003a00442c0b03640e070a0b0f90014280c1030310740120040310000d04142642840740c00c03075071503038419001034002c200c2c0f0300701c2c070034424206684000003030381510034400e4503081189000501038110080e8040744810180002090500c024004000382e42e40c514807a100003003040d81c43d0003a01140342610240302c004018110300030b0b288440709110f61141e0a0106d02c840c0c0d9409000700d030361410244002020200034684191009040654007031551340e01003159405414280c0790481d1010740c2c004140d84901442c0105004003158007461640b01545070041820307407800000001d09511641c03a402c14000322010755001244101d000545008100040205a100c00382000c00c03102c034155484040008001e040030b0600c0c400c0b08030880b50300d0011f0002c4401180e216100a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 381402464 1250 381401214 381401221
    0x702030a1209060e030429090609040b0a18020d180c0e07030209040504060f051b0313152d0903020601050d081204050f2b0804080d02130f15090e090114 67
    0x8250b202445003a01510344175030845403c800203000345d48c0542c2000780340d181400d07105401d00005108520f1965403044400200003441031000092100c141000c040240e0b481203ca46d012003510300c100704044100c0d000080e454045005254108103032600e9031003181d0f2071740fa0b0400c1140a80a404155a4050f1501b4240010440a54020245425a02c0080c070095469441020f51120242d5100403507440410024207000f40ca000c80c201c01d280701e000340b958680305a41007103044901c4002c440c814400e00100100480050030034030401502e542c18140180c14403650020748400040c0b2555006120010118040201e81d0090b40c4a4400c400c4a406103490b09041507640c640381d1003550f8005024810380d51100c01c20404850310103d0500c0e244105107906520b00f11f032815402041990981d0007403010300410150f5000400701a110200300000d03081c2890011107070103070f01c2c1d80030300410889041c40f1490150484600001c13141080c00c141c000340d580500581c0503021201c000c1800d00b4050082 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 381403714 1250 381402464 381402479
    0x7090c020307020103050c160605060109170a02040506030a0f0602131805070909090f110301020c060703060806070305160f110d050d0b040203060d121701080f060702030a1209060e0304 81
    0x9401010f0003640c0500603601c0c1c5941e001030521030000604484d102c0b0f07000f040c0210704d15400264110034189030074038070a50f80b100d41070411031045c40645031a800c0000d00c11f0039440d00d401080d801c598110058509a80269541d0000402003031000b400c498000c43e49001311b200000d8170070f00501c0d040c040f03403200d105c0800f80c04000305030803a41180440c601d00c001062000031803081900c03a561006246c002102c41d900c4078010a8000c01d06c0b10f84c5990204401e4507010000d2003003500441c6152000701d803d9040220542c103001c0000d00300c0080500c1c0c64100b00c05440f50721402c091030590b42c01c000f411005044030490f01014071035458250751080e4170203031224560250051010680d141c80c100103624002c400c20041e88070070340328203a02c0740b02c0308441d0000c07030791101150782c2c00851410301c050b5032000c20b9164803040300b00f42e021160581000a0b00154840c00344081e0b5400441440034614242c1d020030050410100b94000b40304555450f04503604100c42d90344120640300401c8112034179140d54a55 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 381404964 1250 381403714 381403717
    0x603080d090b010603061a0c0a0c080703050601060206041101082a0d0525050a0c0c031208091c050901021527030a0203071e1a06040b010e030d080907090c0203 70
    0x1c11203880355900d000043c00d52192180400b51124074000303044014400101144c0c03600501c00d0882940100d41c4001d00280c903076040c500040c400b210143c01000e182d81025410000141c0c00710046d500000104030000c1c203441012900c0640034244040386032107260201110781c10124900c00c004c407002c45118401064a40501509054254140096980c00f021844055150024883c03050b5480c2c0481030310384e004e44c0107494084024a41041d040c903e984460741000710940c0140e644244081d500c0600a5021801a03484107041009200000142041d254100002008842084008241485280e1083c44002c24044c18140300c6050390801c40d030f1600c42c0f02648107500481070440e141c1984041d10100035144c14814540146007003800360780340c1c5410004111416080d80784c582c07c64500103032045402009100403500005d1071f519102080c40100c41c04401020305000d110380006019680014104d526140c151600e03518685541ca1107502c0c0c28283e40090350405e0030903c02c01102c0340d0020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 381406214 1250 381404964 381404981
    0xf0b0c0c0909010f0b010212040603020307181d06040b0f040b0f18090705030715082e182a03021b0c2d0d050c0307030b180f1f0603080d 60
    0x10041005800c17070707030040e41e450300b41c2003ca080c03400d01480200a414060340c0503507405030f05400c20540100c8140701442d1603a00c20340122021540b2000b55a9010440c7c911032948410244c81c20400b0380e03c4480000d40c54400a84124880c98a60050120a46460040d1800010b000d4030840351402c1100c0c04c404416421039518040344240382000407245000240f5800f00c0b0300600c442003070800d22600481d42500010440d482e246441e0101251101c96152580c044500511300c1b0300d2418185448080e402341c00186134008181440e4a42c014100d88005044c81c5000207000c807500203079594070a5003c0d0040200350381c103558400e407002c91058400304203410300040440720300c0c1500240081e148140356000c10112007007142403200701c480d400c08945580001c1e01070401c40c0c43c040e0b0f00c2c0740081c1c60324120b908110742c4884034506001000715400d501002c503a0000000d40b07000c14281c1d144640d91203a4000d0b281046031744541c2c3c0c200a04481d4041d601450700040b100d0340d95a405502200070b4508130 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 381407464 1250 381406214 381406241
    0x1d070911090901151404150206090d020d0c0c09060b041a0301030f0f0201180b0a0e1507240507051903050903030a0f06080106080d11070f0b0c0c090901 67
    0x148850503018046012104210002003800740b03540d00340215a070502031590b240703100784040c0c062000811180c4030007910084c140103200c1415a55000c000030700340500a040300c1440e80c402d4001e0007010360041101403a20742e0700c0c0780044800d081703404e00d08000104c03644090301051500c20f01140c01811180100242d80501740d00820030038002d8915449440240720140000351540c4520380000d03100802c10b081c86005140c040000d4101070325040d420790583d440150001c0c03002400602c402c3e00107c0c941400c100480d6000040100d202070755100d48581207000708000e44100b40c007450150800400100c91654410400c114540600e0190095200181d82000035101e12020506c0503c240201886064840301460554841442d0341025080340110112403e89500000c205c105091195000500d02140103280b14159068041c16055515107132104540003242e040c0700c4023082d1b00ea41c100700d400d80001150342d81c03079446020b810950006d0340940c0c0108002e00344043c41ca0150421030f000e0f40384 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 381408714 1250 381407464 381407471
    0x3040303140c0a08030903130e06030c01110d11030706050106092301020703020603070e030a0b100f080a081305060a091a0c0615010306030209040b041a011206090201031d0709 77
    0x40318122450703402500c00c600403540c08081c1070000181120003a50308610000220380c10070484c1d5142111a1800ea00985419948030040102c1480c08005c10880200c081c01c007405e115030580f00240d102c0c4444103004060003001180c95400c908204100c0c1c001942004080049503140e2700b0040101504d4030807a0314041131500034203900e45001c1007142c0354080c140c00402c1001c3c5190b0a000b0746400c001c041e0424404440c00701d424544090000010f840e104005204180c03500e080109030601542d0002d40e9559450207091102d0301c0c0c00a00710810582000640782c8a0090349070100b00285180c10054000c078000c10144100fa07000020001030701e800800b02040108dc2d101c0c01e800d140100c0004034402e03400b400c00f1a011803a40c5e4000c035691101890081511a00c90700401c500c0c400940781280d05200540130802400050000e07a5404d03004001224541d51411000e04409071600d500a488a0756a1007503404580c0264800c504900d4400d1858111200b00c605c400e4848200d4824020780608 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 381409964 1250 381408714 381408737
    0x6030c0905040b130c4a10080402041b0f020c0108060a050103051807030305030a32090c0a090617150f04060b1806100c150213031403040303 62
    0x1040d006040c0c41007000341c201d2403421104c40c408409003030400c00d141d0605c80c0340c51044050101860b28007021056050140016107040c0d9a0b451000c0903440d850840d040580d04910f000d580e4034900c55588050f18648544580c03207071f0000134024a410a803078030091243c01c240407001900003581d200201e001e9002e5a646000d18070040d101c10804440159024038910b005120542c000d62000750003a132002d50004600384550400c070310300802900141d01048003c0204081308a46000b42c21202481c01d4014414011102c4009903070503a03400200d00540c00700000544414040106040002005041e0701c02c00fa6078515090040400b07000d02100305d00040440d03074401c24001010b00e001c090f0801203030051356a09205212250f801340c811102540c80381d581e25440d696081c06000458031a400000b482d05000c0104201040c1c5103080310188900380d0710701000f0880904c944490300d51520005a602c14542c07075407071021031840c1c01c000c000070840e00c2801c10360180000500140d80c03003a06d031003032401c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 381411214 1250 381409964 381409969
    0x150906060405010e1308070c03060b15070b180c1905040f020408030315011701140a060e090718030b01080d03060e0408160809041811013204030c06030c0905 69
    0x10400d0250b54160255103011455a1420202807400d241c01505031b54248441030ba40c0b24030b003130b61641c410782e0907980b1742c800050103250074440864000c0f06500a2460110941e40740c5c020000002c1c1015160302501820b058120400e1250440c1008000c0000074a50004113401e900c144450040c103014900d0240b00c0a81d4050901c01c582c19034040c43d00450469032585161000207441e40800b504000108001d080c007050f0000940e8083c0210707140707011140d180752040c000d400e20355034400c0c400c21502802d110f0940d2901689544c003c8842e00e0509000c101d140d142189500c1154001001580e902c400002d84800100b440e444860440d80d06001441d600c4070316a951600569001c3c20760b0100704920290707101c1c1110110100391142c03440c1c505040c1d1410000e02190b43c1594141000300019103003008000c0c400c020205081c009003010003a0603d1040f56402d14203140c0c3d07a0f0807503121810903040d09000c846040d40d008641c0010701401c007a440c5d210003000f5003510f00814011038016040403403d031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 381412464 1250 381411214 381411221
    0x7090c02031e0307020a140c030d030203060d0b150a09050a0c0c0c0905072d0e0418060902040b040e101505010f1809020a18090203060906211509060604 67
    0x2022902c03061240d40c4000349011290b4805003864042d0b10500d00d0000003c5d91651104000c400d52030b01501c001140c40d011300d030501c09414045002c02d4810000c0001175176a200564800e550001a007900559a17080725541a400d44400c0d1503000d2100440041c0708603070350704034074410565900f050000d4600f4202c19100309010f070000a00c81d095041c414031a446065005543c42031007407401100301c02048010a428100c0844c03117030807031070007030048440381034110320009100d54084c1c60802001c41f80e014040c2807070b403402000404650320b4011307800655980b900300d41d02e001d000800c10014800d900440c55a2071145003100c030005814010882402d0400c0240c00c0c040341d0040e19814404134144c10100c0c1c682804101da075030801124030700030407000082d20240c42c20407210780390343d131200b00c40070544907021900f40d01c01609a401002001980e40f1614217842e00074806803203000800b12000d40981e0050300c10b4988a000d0f00c00d60001d100b081400780c4a01d4020440c90701504ca07591504070a01059 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 381413714 1250 381412464 381412477
    0xd02032a0901050609010819060b04150806060a1211030f040c090b060a03020307020f0706050307020106210206030405070e0f060108070c02090f0606090910090e1c0806041d07090c0203 81
    0x84c0030320a8440d59405442c146034062669100c0c10240c0340b51100c0301048440c51342003e084010085001d2014940743c100303082d8885640e044c01107072454118005016840f4602d03e90b420009456076280000280e5008004049005840d0f81d8507032809607603401f07413948100e034241e0790f12243c60000503240400c3d10800389c00c3c801c050040c2d0715140c80030300c090b0043e6001816160031403080d11942941801c0600ca804040d00351235031000e1b501e0030010340007401e407520b0307820030090882c83c246062060a1907540c04404c565064841a40382d6582d42007650a204659004c001003000e5101041419001c16500e80c0c46540c00741c0b5030b10700c1e54884c2d14084400c41c81500000b50816002c0d0085188103141d0b008895000700018000d07840c016100000c102c100c4003d41c1c1e041004501500c0c103214411181c000c24504c02a010001e10360800380714022010301440c88600e8092082107c0807503119111600860001d101041192a101c107551003d29924605441005042480c1c0340000346014400b004a407032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 381414964 1250 381413714 381413719
    0x1060e0601020712050703111c03030c0306050a2d05030f030403030207060302030c090d1716120f0c0b070c200a0902041811070b1305060604290d02032a090105 70
    0x41c1d1807c40d0760711002e01e400c0e90314540d4001900170405070485915011940741901c07d0b035001c04d80f0400c0480c003400350b4040d0380121384601c98004040c050f100001510102400c50500555103142ca2000f036001c00d00a250840d503094051000f400c2c0d0100400030041088038481d43c04c0b585259075448049040b070205668420007003000b00551519840e01101d601c02c00c500542030401080080620401c40b81d01455040c0d0104008404d0f1000303000e8960081c8010301290b0510382e00c2d03d02e86060080808034040c500800981d41400070440007031281c040e07010031a80c410101200c04140040207501707100d42140c03032841040850804520381000740290307000c80300345030840074120714407040b968003404800c2040e1064440174000d000c0454091812039010300e0b40000d505c2c0c81e01c80302d41040350400c074004102c41d009506003003c0c000c6414407050303d0001b101a10214407440e07070a0800240e600c59a48102941c50720680a070005c1e500c080043e0408004248150074910010aa0078003c541c08244181d41d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 381416214 1250 381414964 381414973
    0x60e04170a080a1e0c0306240c120e0306010308180301061404020c1203040605010806011401081512060c09010e030a0b01031b03080d022115060c070801060e060102071205 75
    0x200d5034002d42d0805281c44000d10501e0500c102225111000c0385c400010b4400081e481c2d04080002d480005940c44002c59440422424605241c0004c0c1800b80a494007c18889102440001061103100c001600840c000c05595141d41d4038105203884c0d400210a501c000e030941041400b40346070500c91103040f2245c2c08003105001c0d400300100402500711101200e20703401400312203090180380d80015449944960000a900e50600343c40364645101600304410048041007280303a1a038000000f1913120502040c0c446960340210041910b0300001004081140f1840050045984490000d0700c40d8000a0365036040760141c41003056600c080c110303405800041d034100107002050030003129012a504201c10450f543c0d650340d80c0e41c1c1e020f0780002070181700030742e000c5031031210345010a840d40c0e681c3c00810f59070807280c203003140c014101c0c3c04110000d510035007001910500c4410706100e40801400d42c2d42c001c2041760354403d100d0b1106902100c81074010302072203e0100740c0d5440c07c12a2040c441d0000c1c02403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 381417464 1250 381416214 381416221
    0x2150c030a2f0c041a04050a0c08091513080405060a030b24040e0702010b12163003120204030b0609010b070309060503040302120304030e0901210b0c0904060e04170a08 74
    0x210081071a81c880704954440d01703111031480c0c2c4581c0602d0303000d0416200005180d0340e80d00c10090400d1805000c0c80816000680f194005c01d60b980205d075040512012050f82003101480c24140300d1240381d00c0290429408102c0000c2c05816901001d0213540a8403846a6100211b005404040785010070140e16101070009000c044440c4010f00c0e4048540c1c00002220704951000a004001c3d000c00e5000c5984060b010040440100f04103000a052240310903880c4130303d0803411440c1c5030140c42003111990100c0d900e1018907203c0c103006608902d500307030110341da10340381d0400e5030711b00c10115081e0b400b40e81400000507444000c2c000b117800d0030740c241d5508000c1c50f0801504844c5a070000d4010b60452090654102031403d0841c02540580d1007625a00704001c494014000303100016480007a11031032564803061038410103000400d07102d500008068071a5612074410384103010b002000c44c0c01514014010600d4404004c0841c0254055036001c80141e0b10319503014801c2c801c01c01090005249840171 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 381418714 1250 381417464 381417469
    0x9160507060911032508030703090e0403200307030206010e04050604020913051606020f01060f0b0f120403080601140301061b020103021c02040f2102150c030a2f0c 72
    0x600c042c40e1040c082c10b02d81407040000a4034000b55190000b02640780001503001e0705150b1000071004109200185040004986000d0800010380c400d01034002200d0700001d007050311940c1600107a55441a8800810401e81d201030350340c1e04120000c8015100b0740001154203251600803502c40c0e68044000c1c00d42d650b455090255420340a0a050f600050b034040c1c24000079800c2c0602c054584240e0700c009106841c008000380b0f4034508a132078040692400708113110080c081c0555105940351440d01e503699080415502c0b8451090b00a000c6040c52044184030403d523003e41d001c3d01840d001d1b40c40e10700940405000b070322588801e21520020500c0060980c06100e1440c202020107401410010700b0280f074140c0916030f0031601442c00b0041580000d0138403680e20250038a0015101010800c00420702c000300d0400108803c95010b8450a5080d140380b413020000c10444001071224000d407500c843c44040c0150546000101c041c00c054540da0203103051110210800d0000540f001c01002c010300114203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 381419964 1250 381418714 381418721
    0xc11032802030c010509030721141b030d0f0606181a12130b090304031e080f0c07050f180f060111010606050403120905030604060c05070209040803060916050706 71
    0x160056010a0008a848090a2040074032480a01c809941d0b9a0010301d0308129035181d92070061627030302d1290b1558503025486a5035601d01920001c0317043c1d54880d45a00085100705070002e494891000140c8125a0381c00c980000c80c0400d071105090220585409090b1101007020120096050804030300f00004030807524007640c44401c505107a440d01c02060b0908001e03004c110340c079081e8200740c1c0f58014100f2010324105580f01961350301940c10641590384a1950316042c81c9080f0400242c0d400000500800e081250503042510801075500c80007400b00c103071a5112407080b03621030b01c42070810a0f4a4100345400c3c03505191505803010259403807040103920307210045c0905041003100c41110031904424484c010281c0350341c0c4c0360301d80c5883c91858890791625100c11002c041128649003088103840020b005900558001008205d413002540100ea041c000c03010007079032040b040e20902041c401c0c0c4000840c010402502e80000d255290b450102c0c42c04031740810394000400402c24980428490307403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 381421214 1250 381419964 381420037
    0x9020f0d061b0c24111603090602010b0d020d0507090c0207060e010309112e051c06080601030b04050a0510050108010b0405070f0e13050106110607080402030307031d0a0303030c1103 80
    0x6030004154000c100010041d0300000c84003104a001030b06c02c0824140c0040d60107000f0241c0348020f2052a084401007041c107504040001d000300c07000002039081180501a58015101c0c02104101c14051041f000b980c0320000d1041101050342d100d181122075110f80030f090f440c207070002001218106081c0034462014981c09900b580340030400c10060554110608555481d51555652901c60007501c00031140e84414400000e64145081c10401007000046076981c1120707005011014103a50340d00b811030410040c1c5400030004d0017034903c2c0c070311906015404581170314450002000b07100030a00034001100c0c41074a41d000442e0ba66820440e07101c2c17040d07a031440710748405003030b1900100d03158003008291142a0008004604003000300c14480e44204007142e402401e5241000003030410341c0200761070b4802c10501030300704102d1200800441441402d005c00811000d450b081040d5500d083c020300800540000600050340c070004642e42050001c140da52081010b5030320740e4500c81c8d191b4039290264901c2e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 381422464 1250 381421214 381421283
    0x150a141201060608010503071d010e09031c0c0809032704061206051803030103080403020f04090b130201121518060b071506090203010b0d09020f0d061b0c 68
    0x4000c203a48800c42070040748002c164580320903940d035040c48201400c10b259500f050940d00d10710341052640f120f501440904441e07204941c60460384404c95103c0c198410190310b00d001304803910040304010056031015130101c0d000d82c0c44001d02d840b65030885840784107000380c400040c00d81c2800c8400704611805003820701d50004100240d40c0350388070070001c400c0800080c146d60031a511800c10150703011030502d188191001c0c0700135621755070550355801594040c602000c0d00a0941041c40055500ca0f40d2240741034075044811504a441d003032000f80403441d80c103403049000442e5440c0c480d0000c641400307131407900c000c550f0881e850141030048074a049020204040c543d00d48818000400c88022401002c465006104111100000c41c0d08103090310000d038002c590141c030400040041031541c0060300c500007e03c04000c40c002556000081810080d0741310603074031501307000381e80c0c04020745a80301e83c0049507d031500b811013441d401000c2d0780e07041601c8070184c4400301d480d80c98205001401051044643e50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 381423714 1250 381422464 381422479
    0x1509090717010e070b130905060103110c1b06090a03141c02071401081012050f0601140301140702060c2508091c02210f010c17150a14 59
    0x68074958201c0c1900c603001c1941a940d100c0c1c0c10b001c0100280441c0001d4440307406514540758848440c1c2c5480c0425111b0b21072503581c1c407400701e04181c1c86900046020310106072429204c0d15034185441e02d070708050b510314400000c4102c0d040c940d402c016050707a22601000b0503001015166444125801c0c0e40a00264001e005e41c12600290031034015003d086021b02d40d00408080c6e0800030b603034095624203c1c055060150b9074040110742003200b0800801e0350080801005c0c0c0040520705589410100982816a406840008106c0821500c0443c0d288070701140203201415100401c0014190180c2e0301c030006130001800520b00d9080000103145000140284451000709404560404180c42c074081315101d20024038074140d458031002540c80356940c2210480401c016a0006060b101400013074000000004141d0302242e41c01c1c4048254002c050000348042e0034000e80060045650f83c4071682c1c80900c08010565011307100c0c113002d110341005803003d40207604040c655060341001c1c85020340e02000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 381424964 1250 381423714 381423719
    0xf1d0f07030c0c0816020901080f060c09061b03130506040b090d0203150415053904090906060e10080d03050a11070303090525090504020105090901030c08010f020315090907 76
    0x2c1d0744c401000d150100124210030280c0c24410000e084006038490009540203600c02c15100c200812034a070045030440c0034554030340250000c10418011101401106040b44051402000700417004201802d01ca407088040692074508002c018040d5002d401d0709078000744002950360804003150503c0c0b43c00102251120454440ba4642c0001c0c01c48040351b40d140a41821024003100340502c0780c001c0b42c140c03060007a907402c4045800301c60040c000c0040c101d40070440c1c07420000454908413006045c880d036044c0a080071504010020b040c49218035005400550001003040480b14181829960000081c008904a01004070041e00b0040d02418803d6078a040880000f105100184001842614041071707002c00c81c10007a06100540c1418441400c1d69011442110b4912007400156500401c0c0041c0079100c500040b286802001c0d0015040104c140010003408048e4000ba0220749180009008001d05500000164081600d840010841c00600c40c0d001d8030f800720748079030f01029038802c0b0b40c001036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 381426214 1250 381424964 381424973
    0x70b06060921010c3c050408070905150402090d080306030705040203270606150315030d05070605090a0201050405040c1e050405010e060910050c01150f1d0f07030c0c 73
    0x100c4840315000306039584c840700b100c240d80240c40313544400f4402140c0950007001705500c02841010b40200c103000650748103004402ca0007a410b5030064111401220802525072081000030a010340d54030080c403160038101cae4001d00e0b041c0202c802c052005848191559110b50f564403c036007002d448507a05010f80e03840412035807214030181d8401e04001034031180c1481d4800040301611101e03504066507421000c1042030b552204140381c6000c4c410210f549030307682d942e031885034030a801601295a05000d0980349404095000001d07114650044104103c01e44480499a982d0f82210000901180040c8410002c1c0d25090380180d00c40d44280c02c0c11103040000041d14860313103154411000c007103072002c00c091040e56408545002200c005480c1607140050078000a0aa259201c980004108000a6909484100b03422890300c21b028035001c0c591198690180e0404a121409003710040c030740c42d21507401150325000340e801481d107180d000505884561045000d030042420802c03c1c401c5488600c2c0c0000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 381427464 1250 381426214 381426259
    0x608041401020a050406030f0902010504120302010b0d0c05100503060a05010c03030e0618010b03071a030402011e02030a082202190f0312080c0307050d051513050f07020102070b060609 81
    0x1040640c0c4da055603030b802c00c0c82c05811134003c126040c0d5100d140100c0a80141d0f04030003102c050b50461450151786025510b0f04034050403840f82400d4100c5d0500c0c1700d480c104110281e045095075000c98980155600702c440c2100e06000c101c1f0415070220556108000d0340d40248021005280246008a0580c060060861070100161024030490000c1145078107541000e200e5000b81c031320304030f001c2e1050a1034900c124488801d0304c5012118114008045411a0702440e0480385035280b901c0c3c01940b0b1081c40d007010b9100e4104516103408901c1e401d0000f5100b228440b100d000790088800d0075049410b0fa9001d00801c402130381e00c02c95030300307902e0720300400c2420011900000941c400c80b420040340e601ea480041110740050403041d0069810301c240001d450304075003941c0d042040f03a1400282c0359503224038120704e002141c2e90a40c00c000e145558140c002c2880d0842c81c4205a030305070411058032025000c0b4200d208010000c1e0060f00c000d03020625900c0e0410041540503002021020415900700041036003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 381428714 1250 381427464 381427477
    0x3021b0f0d020f0a200a1805010f0303320c01091202010b090f0a110d0e06060a1a0c03041a0408010b0405010506040e070c1416090213060804140102 65
    0x6960242200100009040002461140261019000000d0032000182e580e00920070024807110610610f01e00e182606507410704603020052015111594030350340220b40d00303002c54810714580c1c207100c00400c6200c6250301020840e0782c90350b41c0300148800030f8511040c0071401100d8076520100c0a150240318008032020b441ea00c1301040c00062492000d14021000e02c014004440959042842101c01c0781e994a1520b90300c088c00e01425195551007541442c010804492200b01c244004551000c992000e540142c2c500e25505007150f01700c1c0c440380c0030421444031a11803058000c001e01d1540310003581585c040d08440c2c1100b402c880c1055120300e00304030015a2480181c4a40002050800c2001402d024410f0604070668040140d5418400801d001d4425401001000c0c1890400b044d0283d00c5040400f02c41a040f881c81400400640030440d180c0c60b5001001690148004012911150070710031a04019051801d40500130720308a010307114420001d0060b9298080c1801d80364510900307000500da03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 381429964 1250 381428714 381428767
    0x703020a08150a0c05041511030f031e1605091203040330020304030f020f090907090e15060d0309030b010e07090b18060912010f020307031b140a0302 66
    0x1040c050b801e0281c0034080052919002d9030821183c0220160004101c906444280c810919007100e180c40988481d8001c3c06880007a1000003003511248c9502070246015030980280680c14102d2040400b803446420b440c0000500d8422042d562828050001081c0e11440584141d0204d50766045540c01c1d608550300660300d64401114071182da651780410402d0070f060124080030f0060980000a60324011404002e12001054054006640e180083c0250612009180c0900d500d4601507498644030203110340b1030b00b40e00f802c12249880d1130104050400d240310454404a95469504200b4000d908440a500303000804a01202040d0748409850181500c80d182c5540e60800c0c0d040180400c0c080e5002c20b9040c0b1060007800600074000643c0b20340c04008541241d152003259002540c001d41c01c0341942090b620b032550500e9040700b80c0d00958401c2580e41c80801c40e0800c51901c41c2c2c02007841c10706820005100c2c100d1070306400d4512001e01040491403a0041c01c241800058a1140414105004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 381431214 1250 381429964 381429973
    0xe090c0d1a160905010507060612061406030a081e04170a051615030f0b060406090302040b0d0209040327090b03060c130501081e01030807030809010209100c050703020a08 75
    0x8074040d00c0c200e4040c0d0000c411210042120380402e80051200140c1e015241c10401c00103980420b001c4150044000303040981c81c00e040c244058541400107120061140d100c503c030840c002080b03840d0115170302c8040e5420003100d5160282080078103280085141c0e0790f4100c140c0c20711000c00c0c54081c03050000504105640184030054640c2441c030714280343c075007046050064040c0107001440c802c1e05042088440703824007040b645d804011400c0a01038400c3c119030080000f083c0001c1309035000895034120780c0291010480c0c860310109010110b5010300303020350003162410204000900c1050340c0c01c02d02c4021041010440c2a40c0600c82c43c0510b1540a0020702d03890b030b03444ca181c900d030911036280c21542940403585810059034400c429401346101e844d050041d00000036680421a205079113402d040583c080d2210b42e10303490300c21500d03003104d101900081da1503c002008603205100f1205070382c0c0014010300070980d03000402ca07400e104181c012034550140400002c01a102c1840503806850034034040c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 381432464 1250 381431214 381431243
    0x4030c0801020f0f0a020a050f10050c0705030a0f030207080d14131e05070905010807080d020f0a02040504030e1207081515240a050d060b0901090e090c0d 68
    0x2184155419000320045900c1004442c070480e04140444111007142040c0a803101c0c0c21001c00c0e42030031841100640140a140c5c0f0144040201048101144d07090030820403103511205200c0200d030052000040c407580c402c00691001500072141c07031000303c810385000340c500714841e40c0d07a400e41e401c04004000442d46500c01c020111080e8910190700120031000302c0b14010030380c0c4030450000848003581428070007082d441e8080c0300d0280400d20150003400c1090105503900d0b00f42d541c2d500f205101e8040039000c0e0240b00441d00c0c0c070105a80d18150904001003040046603000c0000510002d003040702400302c00301e9400307400c1c2c0f50060a901d1060750356010384451843d2001c507130b0504484803c07140030000b000d01080f448003160b400550180c681a60031045024203044846100c456451004114010118220440e243e00000070540d00718980414044166120580c01503409803207040703030215000d0035060001801c0803101c01d500456540031560024042000300d220940007110640e01c0103511080c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 381433714 1250 381432464 381432473
    0x30b0c16060b090708070905040b04090618020a080a0302073c060f030905030313060b090a060f06111e1c080123031506030106050a0b0a02010609050106052506050c0403 74
    0x58962000301030910a03100d00d81003038020070440988c09614440c60b5a807401c42c0039078655601c203941041c7e00c09020032075190084040d90030000821403c0313128401c01c04003c5a006800b04203540306c10343c16001403040720306000d2196a400c2d080f00703142c1e102400d4402c4514058600440244c024855214071000890420200400e5030451000800038142843d08010000ea03001080f03961040d040d40d1050403d001614113800078011420005501690010074001aa007865118500300d030b2403208015130103503030b500c0142c68035640318102e101c594210710011480703280c2c15182400e424540794103a07414107403017203940203000c0640d1888400040c520340043c405003a01c6140107005001c403441d40c4081180d0303c4000381e50354404d541101d00340309080340492031a480940102c0c0185c8001080a21420748508441003680c0011200c03034010b41c208400000d602c400307031080b541a94041c0c0d881904c2c000e0341d00000c03181d0740d900d0020410102d0700003c050300441c405103e110b005070036107488655540e18500b030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 381434964 1250 381433714 381433729
    0x1204030f060f020c03070f02060702120f01050108010504020603060f0f0405070f03061a041214010203010605121006090605070201140c2a060d0e1e030a02101104030b0c16060b 77
    0x82c00050a1040001040c165000419200141c1c2c0c450404000301d44244046a00c80c01103000082d00f0924403c1e05655907540461181a00d0805000801c4581e0b604c2203018207071782090b82c010350024400c20203c0c5850500025203140982c01404504c001c0310801e000c50211201101c03900e00041011141c060165410301a4400600c5000c240c020100c56000142c0303518840c0f889203007400c030708100091081110000c96a42d0340e040a0000719100e6a40348000b030712a505c001591040144494002019048001e00300c0301a00c20f503a80c4c00c01c07140e040031802e86d190740c000c900690620038070505144c010141c0200030700801e24030350080d000445894403005c00e1703004444000c5584006030030184419445100035280c40c1220b002c030200e10710844242e01424078071101001c41c410722022a0301f22103c0000802400d100c41d00e5400ca942003c501d0b0201c00c00c60f80f00204282c03000d8400c02003000400d4194a06c00d8110903492511850002c10318010703800d00110290850321146c541c1076200480c40d0108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 381436214 1250 381434964 381434981
    0x2a020315060114030105151b0102070507090b01210c1215050312031b03061c0b07180501090302130219080901060b09031e2a0a060201060510080601021204030f06 71
    0x91040e8195410710000640c5c0b20204503451200c8040402c010005ca00088c00002400018000855903480c1c03500f412034845100f400343c10303001ca04080f209001035102d014003008840e140070172105041c080285460142450703424440400c00c45045085040c0d0303052082d40d0405612040c485480c1e480c250034542004124004508d0348542442040007100303102c4544181c10200c403402540c0c980e1490b002403810020300c00d56042c80e441d40701c1400e040144011000380160f2a41e1500098071004140d003240400481c007a03e40010604c0000304014189520180c0341c08082d10400741c1014511103c030300304107e101100c1000100407600b0300c609804280715650190684034180c2d46010000e41c08265034516154691a00110340d103507551090900740b00744004003940e144410072401d181064080301c00303009003142d403040440150000302280140304a80c11142c01038000006604046410b44050a004080c2030560065401d800410085000100003951145121117640240390a06000b250b0485 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 381437464 1250 381436214 381436247
    0x6050a0c050a0e0d0605040503030f0c0922020403120c300e010903051221130f0809060d020d05061516060e1b1f2a0203150601 56
    0x180c0e90800055004084540c1840c0d54106201104074900c042550700f03105480c05449a8a41003d100070010007100460143c01c1e46d030f0b038500441e121304484051764402c40c0d00d040da010801d6100e5400c1c12080e0404c04004502500c0f005040907a41e442c1e2428684d5428001400103034070768240c1040013007181600002c918440d2024000c40d5007030491124050001d074000003481074034084184543c1c0300d080344501650303110f400d840005540301c2c100340d402c2c1c200b9a802400f03035881303504124090a2144200e840f0f24035104d00d02074a41f6044e1140c1441c0c00040c0c03420703107181804012800c8162a16401040190b246600050741c03480c4415601048440141c2014030420880d140f10003400030002c01d603a0038142c4680310407000102494041c2c0206000c46485106025071002030561407641078103407000b40020b0f22011a0540c506c031440d001c00058400030303008503100062045000d03284508590598034610f044000c000c07540c2e0000703864003100b10025112505c111003041900d5034080440011701056 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 381438714 1250 381437464 381437471
    0x180f04020724021e091c050d020f120a0c080712020d090905060d0210021501030b06010801080d210b2e09060c0f050c0d03030507080c0403030512040203010f110706050a 74
    0x546280301300101c1d003108440703080280412805c0f015590a02103200d000c2010301018080c102d1440c2840d01d6901540301c0070058081d40d0143c2c203800c0c10101342c403010807036131600c003600d080000e60742982c0c1685240425030700c40310305008020026011542505503400307142c0081081152841c03004012007916001000341c50708110500020740c0310041d542580e03070303070490f4818414072005000b2440c00c0d00320003d0b84440c0d440034000106004110b0a07042c05884280c2e04c00c8450380c2c03900040c5640b0b8001c00705a0b80001c50f40b8400144d160351955000c3c1091200b0b48022411082140000d11070008000c03840100444040d1b402041e441459100c04501c62241066039841e80f90290140851148042c00740c13017000000340020420501b404201c40354400104860b1062080d07080c014010301045441e03401260491000c101c403038026105a5080769410307130305c041c60141c1e40d110001e000040030744105d82540d01c8841c00c60403100b1a004038182402c01320562916151903041801c29108054050400d1918 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 381439964 1250 381438714 381438727
    0x9050114010815010311040b1801020c0307121a0a0b01091a0912010e030714070905040230120a03050c030103020a030807170f03040b07080903180f0402072402 70
    0x204196a581d12004100300e401080e0000e00045e0080c022040d02008415000200820719a4040001d0304102c45405c45102a07074160a00590360b810360440350316499404640c0400c540d0106c071880380b659501c9914184c10423280b851081c4060b003c240e800368000b984660140580b544d00800240c001c28880f039135402075105c6250301c020b442c80b032001d55500130013036014000d0347d18102b500321500b03001c0ea001c00c5a503901ca10b410000003070301c095403294085000722800040d40c171003d0b029150080760003e04006241c16521103040e0740b8110000001e0550030124241c0007086024044407600c000c0c03c0011a5544948440080454000800080e81080b0600c0180701680710b00070f080c0152a84145074542d507a80a040455000802c201e84400103000040c950ba00c0300700c660061030090340b0810f2024455212088269903143e42218164210342c4244080801034214015034500c540018203441c0c840e54890020500386da10004003945c2e62040c01c81c20310454450030280c07009076a00300d8011803c045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 381441214 1250 381439964 381439967
    0x250503011518060302030f0a0e030f03040f02150a0f08011203180f06030f0608210a0309080f1206030d12020a03110304050a050607050703020a0f0f0c0801060905011401 74
    0x1060040740001c0c6050405500158040c1881c0e1250003444085040725030b555000060207540100c40140000c0d0320440400c00c1d5000c1d501507040260f5030301d8061414081820f107455a01d0b0802003040d551400b075444407001503100ca400d044281c2090040140d5202c0d5451000340401042c6582082045801e01c01081509500d0952800d4035500d0720780106048a1182c2d00040c2d1070a94105648001c42c042c00060b1094056002c600e2004076488240002513884400e00e4503800e404c00030036100704c5081000040075040c00000e080340480c908001406043c06d032944400c2c2e0b085281150388041002460b038444240d000011544400214010605903104007001041d8006030f101c2424980d4000c601010113501035080b0b00200c8a445101c6601d1780341034182a996801d0701c220940f00c0340541008114007a2043c41220405500340d00181002c484a90710800790b003080d10390075101200040d9208001610b8044030340000c041d101d0021a9036410020744204945060303228015020804009c0340499 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 381442464 1250 381441214 381441217
    0x2802010c0e01021b01030212070206011a030103050a0303051008100b12120d09330b03010b0f0d020d0f0c081c0c0312060911042d030f080c030d052505 66
    0x42c08039050302c20303107060132005030041d0142c41c54110801100c0000c0140495001074424100c031540341b150841c0c5680c000c01e00d82a44401e0101901030b400c540710140120740240c02c10307030b0406c0310a80d0f034985150750b40d003c05003012024084058110384581c404c4542d8540150180c8401d15440050030100c1070b00044844030348184007001c14002d0301da40719201402000b5841040c410800503001c83d4000090704185a014051f40b040c00c8038900d81300800c00281814801c2141c0d410020389440c46100c1c2c1c84c0c0800541810103e0120381c48441d5004403030000b000c06c0c0c014a80e0714440e9001d11040750610307500d94100413600021100e0788126080006903da271080c07640f41602d405080401c0c0d40041c41222401030b0016410001116080407100c022000044005000b121400561216419a409900480446262000d810f0b00d1511242130011a001c81021000103102d20615841c0c1443c81d0841c6041d070700038601e40103101c1e685d0030401030b5503101e0521550030762a00205030040d44d007c03101c02410a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 381443714 1250 381442464 381442483
    0x4030606141008090f0a1109100807260a0f0b090303040201050706020a0c1202060a0608011a1c06180209010602010203090a030305180615042703142802010c0e0102 72
    0x1007007451000b24910302c40602c54001045c10702020390382100380f1030801c04c480203103007040c00740680f43c040005030007040c400100341b042d1000240030700b19803464a0510071034030b00e02c481c0f81500a80003030441ca4110710100807140c045031080d4203125100589080001d01c5030001008006650002c00c2080010707a0b101e0106c886055000800585511700c048088840903a030200003003030030500003403482c140c2d83c001072954802c0309061350030f00004c1e40342c010041c02d07202c00700d54180903914080b01c120018030305083d0040440840b084012030710f02803500d0f0013042c0c46820018000c003400400d81402542011041e00e0f000d40068002540b4604103194a540e0b90b441145015080550351000b054200340414888401683c00700100d074421304100304940d1040c1420941684101c2c500100e40100313680c40641d00c200c40030004a025010701e00e50b02d095174148440061042c0310a400c1041c01c1e00184d0b60401c07444454611203a40b80c211110313120103800c4900d102104014001301c3d003601c1c105a82d0001f282040c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 381444964 1250 381443714 381443717
    0x5040f05060d020d0203071206090b13020c0c060708040e1605071407120b0a1401030213050c0904020c0607021002090604091e06150f2105090f060a02040306061410 72
    0x1620b0306200000002402008046140e660000044c8560561302c105583c03c108000781e800c02440f581c401c2120101d8200465654000038880b0b051040b010256029020314200c1000369040c0d040220b000a4580d404a00d0484d155240030074140850b0317501d980300c1580071513510414170a0401903413024100d0b005400c4020451a52144220030419062198500400c5020801d8614010611745461768035001c0303440c0340980345070500e4501c560151980041c1200d4001d000c05607040c11010390880039100c0200304460160081050180381d840360700c0106030016507040500501c0c18441030003401c1c0541d0b200a01c40703135401400318003060f03a40c1008132000c80307603089000602c400c1041c050303500c11080b50003072882e071610f0200006203043c24407245046501c4950f032101d003441070380307002555807500211850002c40703031000c0d81c407503642c0090b80600d40194240084420510300500a035240c04400c6400702405500490300304100407690180354050036107a500d40c8825000b240200d058900740111800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 381446214 1250 381444964 381444967
    0x1060e0409060608060c0403050c100509100c02031515010206240a0506031003020102060a020c0709180b07030f0b0d020907140c07030606060e030a0f0b0a02280f05040f0506 76
    0x404100b0907030b0100004040072400c0d5540b40c03034140d1100920350020700c01500d0501a14101c0314032454181da0500d0303410b2894441500340040c0c101070102454508a09006100d255400d100140c1d83c200404000b0601555420b203842c5003007043c43d2040213180c0501815075010f5010701c0140c0d18000d4070000c0312001c5801015407002d01000040b514003a5038807860b0004800024004901d10026400e4140ea00030703000c450491705d0300700b012022842052000324542e0051902071008a505e07420800000070f2240c590104060a0345842c040c00500b660044081307035a0350074104290303a45000c0c1207410340c01252403c000c44856004a400c440d0002c10340010486000d510302d40001e00b16003a14544030064040700c1c03855407245072610007070846000f40b1010504141e11032400d8540000c01d00b0820382d20840241f04050a650b07104030382031019103403143c1c0b01c3d001e20024041c078102102055030090f144a002c0301d16052030201511020340c0700c0c0200200320003080b085c01040c64540402d800c961040d5400d6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 381447464 1250 381446214 381446231
    0x60109020c120f0705010b061809061f030f050c070f0b0604060f150201060509090a120e06130302180903160305120702030904060e090a020d0f0c0312080f01060e04 72
    0x38100302c807a290420301c142c80401c803110741c0b5074014040c1c000c07540314000801c207c4402604000d903d0042001821110703100382010202801c00007011030b0090300252040000d8132240e6101d545c41522416620002551240c203c186400350340078194108005040b95440c00f41c09482e507080240c0256405040400440045000c6413515800640180802080400995116030001c031444502d410b54600642c04c107840801d00b032400840e0540203041a200410b0211515034a10b18502c0045c04100203021425541c00403548400c40140689075030b40d002d590a6a01b140304010000310101c0360f01174400010b40030841207d000104884610130b000107050382c20074240c9011070302341c400c00082035112160b44050221054001028003c80902260140702c8603446004034181c0500c2221092456031290103440f0150034070250f2200071600807040b80c0780246554a800e640da0141e688200c1c0e08100751811070b026190303c00c2226030007040c2001d903003240b940f4041e4000c0070001180b07580c6100d180d590010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 381448714 1250 381447464 381447487
    0x2a150c0507060b0325080c0118030b0714040803042102061213020607030801063231080d0207030209060f0d060c030b03010b010302040b03010b031b0706022a06010902 73
    0x242c8500c541c2c3d21202804d07656070100c0070901c84018031400c0c003980300c7c1c21290b1000d5800361801e100c5030f40103807020a11241c070f503450318010290040d00810a02440c1c4400d155400c03c0f01004001811400d8021966a40307013000c805e91000200b0040740e414140000c2d25401030341e46004441004003071900c2d40400780c444503401e0020b41d49140000f5445080024a102010780000030b482c12600c0e240c990f552100070300c00b415213003588544030780820340b201e40300301c40c400c080600003800004580010780003200506a01101006011b03802d80240040c0c038900412155000f006128103a095038800f400303d49145a01050804030041e1813280300307031710709500c050564442034044800c2c1500484148241d0040d288080c0003004041907081c025400e0000d5500c1c154000e00894086820841e00e50745560310705803081c02560005041030124005403d481b0300180314040280100502400c001a52082c6000c0b424000c140040c1d070354852060f125468041d01032011400e20b04461038004056031391080c0b5180e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 381449964 1250 381448714 381448723
    0x6050702060d09031214100602030901080718080f01150b0f122e030c050303040f0e070c050f1005060423040c0f080a021008060a090b012a150c0507060b03 68
    0x83c0317003024540001641c0039022000030500600d205071402c1c07986501c0c0c02c0c041f62240700340b00314180881c0e405400328000c3c40c82342e242d034400c0e012100110103c00c0d4545030400d05140700304828955584d103500c03c4000050014800c02c0c014540d90003a1031500700401e00000543c05103501c03010469040b40700141c60300c4483c683c07101203510711440b00c030380c0e8840c10025482000560b001c00d8480d180248004100c0e070400000710ba040d107031400d0102c032041d890005070100541d001403501080100000909000880400030f00c1052071280c0c01604500c080200ca100803a41c0081a540c0700380d00381445c007030440040d51800780c41c501210702000466561820200310f403041317030f03032003182895100d45000800c00c0380802c000729024030841d22034081c8842c0e90300845907150142c40c0107034417a042400c00c01c541e0010360710450940070b060401c1d1300407e41600d014281c0160002004d4031040714081c080342041116a0020422030302c64404000c0c002d03000d14020803600441c94001c00b969691a0414903540c1d0421 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 381451214 1250 381449964 381449987
    0x30602030712110a020705091320190812160305090a0b13081902031c0908060a0f0b220902040204050603010b0a020714061c0f0501150906050702060d0903 68
    0x142440042183d900d01251580144490401401019008a09840c1c01c20600e4042c0e81d0920441000ea1915101c140000c0c8100c022a0003c030843d00d00301d0f1107511012060601c5241030300803040518640039401303091150180c2c14000c0d80108000304030340240045070030608a40c2514010743c80c1e03030180c004280d03a6030b410b801540f5130000208190f04d820482c94088000d03100c18a00f031b208104800c5503c2d42d030f548450a00290b150304410718000d0b1240c0c1c4610040052130640c0b92103207545075100b00c1c0ba400e01209660a41155031190200c14024005004101c04208143c41140c485540340d414002c0300007030b04040380c514580300c0ea0091700395039a54050ba001740200401c0307195a941c0d20110083c0300d51148001c44054020380d100007808803110310b4040c01003100502080d2824144103000210b0b180e03100c14046550342d658031242c2007104103101e01c0317000c1c1c24480c1035200c050309200c001170600041031784000c04209003045020010b07104c820540720b508580c0d440206010303849280544040f107042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 381452464 1250 381451214 381451247
    0x1e021e030d140105030d0e0d060509100603030309030807020f0c0609041d030a0e0307030f0b0c07060e06040c0b0f040506070203190303090b0604110703111c050309160303090306020307 81
    0x3400c82c050052035030564100e0b10101c040b01d00705101603000381c81c3d680b00100d045512a040300c0008000c40c9994020b80d5006401c00207456004140001440c100c0d44550002d6000a0b59108814200350300309954607040300c0180020404000c198515940c0d41002400c06030103102c020511991645554000780e0f00a0420304a8841c541c101d188216540d8200c00c42000c0000d050407001ca10702e080c046a0032059903000519001d036641d03107448400040d070300540f540384082c90400c404008102e007440b503140300c3c58014000c3c1070642806d003000c4202d926290000c15175903808014006100600c20201d8044484c107658131501e880050000a003081215520720b01d40b0401d120780b0f081010b60591142c680e40b41b041313200c0c41c0145c540000380412101d441001c041036110030401c64001c603000341c1030b40c07441034620000c03070345010400208070f408154800e880b107011500120034844900420300c000046141c40d00f42030090646140c4004250f09417610003c2c114942c00001f1a02c002d202e80882d00a18890 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 381453714 1250 381452464 381452471
    0x10f14181c050322120c081608180102010e0712061b051b01060311090a060b0d0b0f030a021c080906040f05010e040c051c020712020109031e021e030d 66
    0x46481c082d0040d0320849103d21824141440314804c01225404901e60a402a0280000b0850408151782c0c02495840a80d10b88030240715100c0d4500d0700e417134406070092003242c442d0349800c44000603aa8000c072080c84903040d64184550491000c02c00100082191107015088031058942d0400750010001261001e0045280c0307002c4903402c981140c01003107503525100c2035201802c10071021a00300c800f1400001c2889002d02a0000240380410b82160090502940064404da030341d9400480780c1d2044402e40456a00c2d842c1d50801458203c4003001d1001050340a8000c01842c0c1d400030781c0207001d0000c620340c0800d1291942080c0b01001d41590030b03800c006007055643c0c0703459914590312200c203441094000f4148580c1e000b164200340c05070403d00021916000d06040300701c15942c2562640c0050112015070074010400411410f000074034889039150000500030000c0c2c100105080d41c0c000c0b03109841c0710082c404c400101e42c00100d8890650798403e0402c401614844e0403411407007070724190302e01c1509 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 381454964 1250 381453714 381453763
    0x10391d0613030b09150726010e150409050c040c09081506040f0b0d031d0303030a02030a05130f0f0201030b06030a0c0e0d050c0402070f0c140102010f1418 68
    0x303a14210010780f40200703400030190343c0d0941a03e43d2502440584100c1400500201c0c55032406000802080340c00c014000c01c0c011668500c1c1e15480c1000da2152000071401010b004000948103c1d607024004140d4060145c601d25072109662030250041540c0601d40e1020300d01c8a0500c18410040a40707580c00a03100c0318400c04146001500c000d844040c0b04514201c0c0c0031104074a030f4883c16176214405488040c0380c12050b141070392141030700c41e030352808030312141c01d007420380c0e40c0a000862007150ba4000041c1c0301d06100d001c0c0800c0300c100030b1120804e24038141c1140045203021080819965110079062400380c0e462004a02800b00444203603007114010051020081c03c0303410410808e0141d540f00b80008218504010032540d0721500904250007a26601c6001d040c070f40c00a0660b2800f9041c0042429147c2d03440040d1102658400c0403020660f0305460059a820b0041407421301018601340440d414491b8204001c1802602046480010000d062000c88045c0900340ca0b8200c1c5410351f02e00c245 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 381456214 1250 381454964 381454987
    0xb1003150903020d0512070e060f0a03020310050904020a1205070f0b0d0e0601120f051203090a0b100b030f070c05011a040b0604060503041b0810391d06 67
    0x7070812405801a4840802030a101e007064503295180c0501c00d4195854090b42545d1030903180b141c0f2074215000f0008c00c62a4108a80201410f01ca15900144d49142c898490009000760b500302c54031513046c900501015903121000c20741540c0c07106164000c1c08000386021460074180e68803030007001103002000204410f590024104010240605114940501c0d00039907c034042402851950440300f01307498081503a489850900600c13920445c0c40b104142068040242c02c222a240403039400204140200545014480d8004054041c810030160800c9070030344090000070215008004a040002d01c0c0c02c3c8641e800d41a8250030100800101552600f20744c0e8030004411403a002d9420045002d0140c140042110111001642e5040c15a00c0329607514107620f0030101651a590800c2c500030440e40410b00107481c441c00b0319180010008115000c0c134626510001c0402c42ca500919080302513034070b210354007800000d00c3e0714040d20202592001c40408500302d032000c2e50003072000b04548643c003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 381457464 1250 381456214 381456221
    0x30d271e031406040330050907180c23120a060f0e0c0a030c090e0702150601080402130c2105040507120503180a12050c1203160b100315 60
    0x200d00440c0b0110a2056004407140d48000550700240046c00342c0b240700c4002d03910240300100385e00500303d038200380084107055036040c0ca5040d41c042066400202c2c00300808280c2200302050107884201c24018034403040c0b0040c04000c2900414252031480a55a00005285008072400d50380700d00501030321414000403c40040013140a002400c0d00c5040c40454010222481d5074424070b45151404e152280c4c0c1c040840c0508042c0c01d268051001c46480452030031464007085104203800d5000b00104a62144110214240902402d05221640b000e100243e01d84200301e45c61484104004503028641400894249900411026400e0020705850007481c6141d00294051800340049506042d120342001188140c003071401045540100300c0c40c0003003c5040b0350b20030728040060440000d00e07a03640210300480c85480e022101034101049090281c070700516000c803040c101d04011410020175108213944001222006000d40781002d0000307044e101e82c420040090750b88a00300700c2415030740040c0b54015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 381458714 1250 381457464 381457469
    0x703060317042105010b09010b0909060d0201230d090c080d0e01120c05070213020d1506090b030a0f0e0f150c091e060c0a0b06030d271e 60
    0x4400c4506003800c803071020750155425103401900b0740c200710060400d03210b41000c1a40703080703480d95220f200c0d44850f95518002c0074000d124210b100341c0d860150208202c08800024199480744011441710405070340e114440340c1c80024a4207107a02d100d261045c01c06c94500411616040207410a0440400c106080c0c42d600c049805a9003203a800b01413040c0141e0b1072a039448002070000b003070b000f001002c9000c560000700f10003841e4146949007030819000b041030f0b14007100b00f8000c16a000a8400c2c006103072846100120710300f5030b8160540c0d50400000038030400051140703000100703010010412044d000d501c030100e1000c00000070050724406d07000b0030313482c1c8031121a0319401c0e0007070680b4103c0b0340f1181505548212640b40c002841c0444010402c0284000c180c1110700312400914604d41d5a01ca80700107100f1400c00d4002072a0142d41e41c580321903a0500103005900a8100e01d041c5a40c2c140c000f400803401055110f0125901e071072803180c40c2c0d01800b499002401084d40210540500b0900301e803034806 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 381459964 1250 381458714 381458723
    0x603061a0a0f0302160b090c0102150610091e0819111003020d06142b0b1b0f0306010e0d020109050609120123060306010f0312110607030603 62
    0x1696440d0064404031018000a0000c14820490a81a184503400c805034000c0e1500f401170030302240308860761245030307805c0f400c6031611070041c24481c06040030400c040200e04248000c0100000c0310700311a1403900054441c6004200300850402180c2c0a541c0010140c80380c200078006d050b500009024442919102d2245180a0181c842d02c200c001c468030904225004511121035044043c203116060041201540416500b449461458481d07030161000030004c800614206419007170812107040b80b0041001e070207502d0140008040310300100420a055004040f01c44203544034009200c11008951060201743c200159419400e4074480280d40569030070790b0f81010484002c024485000350300711002e804145440000c00261521100401035003e01805030650007400b041000d0079601004201d01c0221249181202100b2004118550101049000700815450f202c802d0020000c01d000141c00070001c400007890442c080c0141902c40751018046030352034a0f24100003001031585000484 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 381461214 1250 381459964 381459971
    0x1703071e0503131e05070510030632031501030303052215110d050615120103031101090209090616030c020d121113181802010e0f09100603 61
    0x9a0841460451030460803007500e49501d50b0700c0c3c820302070b51100120081200c0e8110300c05865040c002100f50183c1640384605c0c001d100703540c200004c00044022050180040519141c0d040021119a801d40200b13100164884034001001240c9529002c0301006001d4240c8942da004010100719568243d0407031340603503010030043d10340260f00e2a6050380494150306124018620700045034a60300c0d444020130400030001804441492500c00c6a0000900201510340e148100102030600c01c4070111602800084646071500300e205013404658103000c007804000d491041c6200340282544024440c580040081101d4540300e1105a81d980342196004130050701000b84500701d50090082d040b090246801070711301018001400c650300603501c00410000c030348403c0d40b4955450340d980203210006d203600029107418101440c2a40d60280001403440c008d141088483d400013000c000241c4050382441d081103100c54107000104400b280724035595105003800c0500c005480301c9890202121010788090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 381462464 1250 381461214 381461237
    0xc0503090612010f0603140411120f010608011107032010090b04060b03150109110403320c010503070f12050106020c032521120203040906080109050d1209170307 71
    0xb1000c0d10352590900c047c3c0e169850215000910600030146420b0019050702074119418140303902e805036060315400c40d40d41d03500090204e03050030300528042d80c0c00044d400c2d26041d19035130004e0801c20588400801c10a1502e9280c00d411014056400030700300b008001d120322051424041d0085c1b4094034111040c900d0810000c905080108542d13260f803500d55110300d0982c0c60054084081d080b003200d0344000d18030400020000450b08080c0c4402441d4148031a215100c1d2000d035400d000003500100e40e81a405840a0705aa1703030300004a9034400b2141c03612609884d80c118080d00d0940d0b0071f20b4803040b12814500089080d550001c0c00d5842050b0490444440703035090402d2485044c3e800705100c4107002912024044655034100c04109400e41010a05446005444083c03619117984102001a080042d040100070080c0c05001c0145c810a0020404144280c1d141540c41052030540e03014405540800a404002ca40c84840c03016082072203041c0a15610400c0e87d0513038001c60702e04011440002e8030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 381463714 1250 381462464 381462467
    0x1e09020d0c110115090c0207030b040c0305010b01230a090b07031205070c050c0405070e280b0406020c010e03010b03010c090302040e06040b22140309032a010c0503090612010f06 78
    0x20700d12000f11080815400034146170081018006401c0e001c0190700c603007940000010b8060042d0340c4100c3c041d078800e01d07416095240403070a599001170b2072810010301031100b01080603072503044900818826107555446c41804402d03203a2402c42d5120490000003c1424424141c1204206070f40704e41d414402c00c143d580e82a026550403120003030140841d884003c03841d0715418180c2c00107802c01c00d80d01700010004490310000b890b03c03000741506600c0c0b40e950b001400b0500d45e00c507100c20251150b20602d07401c00d4117181000756503080b4540350604210350f0b6038904040351800c0d40300c0061104050020302620000082c02342c0b240704a480100d01492610300c8144010702c003ca1b89070b020740d40c440d041e00101d4845185c403007001c8161b00032050820441030710403130001c0c80f001c4899503591007480141d600c0701c80610400d41058202031490141c100301c500e81e400c0030300340b0f100460481a800d0034504510310140c141603265009010f100c54120000003810a00040181e801c03038122003004a4884005448510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 381464964 1250 381463714 381463721
    0x1f150f0216140d240c030515040c0903170903121306050f090303070b06040b0301050423030403081303140106050306040206070206120a020d0c09030c1e09020d0c1101 73
    0x8440c5110300003403030500501d400079031501c2c500440104140a0320380f80e61940340e004500c0c034203411030380c04500e003141c0a1207000740a041203116003818100420700c1e00003015500300101381c60035846141d640310000000e5010716120009140c12006240e402c0c070003102681d005a000c1d0481c40d00c01c0c4264411a081454540d00b141c070346800004000c28028a044000e490541000703034880110380051007180700c0c54600f00082c1c00040d000d2003081c14141840700500c4212950802c6846c0642d04080c1000003040303081070a6a4044003019031249589a803803102400c50007580c000802102c1c000036024040311200e07800714203030b9000784042c0c82c40751125a1403a00b00c0b6028842d03250117401c100002009407400401404c00c40e8009800a0719180c0c0f407401c0041441c10803510541d66035404203081051070715501c40ca00c40c88001c0d05101d101c9500703607120700ca00050b061141d18030a62207004d00b00c842103003c13841c6100810460034103545030003c81d60400041d01c15551584001803a48082520b110320501 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 381466214 1250 381464964 381464983
    0x504060e04020a06030b15130906060c051507050d18110117060409080d020304050a0b0a02090607060f181110141b0118030306030c0b1c051f150f02 65
    0x2080c410051340740500950245c68a0350590303500c0300d600350094191501410050a1761155011510707601405d000e041c108444068000c0d02c100202054072100140000070210700c094102407812100340d480e2801106c5900c51066512350442c10503512500420300407a1a51070f8603c60701c2120142c8070864011a4224011109403030300e0040c000120b002800c056115100407400355520a2901c51800c3c500d0317042c1d902c142c40031100e40c1d10081d660420700412000e50b81e00110780c2c1c24207600d001200d5000030810702603848064002e5542d008510f5180d2010f40c0900000c01c144561038099500c64180f81c80488203810580d4000c00700484444c00d403522800c180b140d80d60304403903a10b041602008a40c03940f0300501c1c0020401350360312440c0440120304802001d00c40c62081d0780204065055252035490201e8a41c010101901c1c01d02251040540c0c4060303550451340c1c40c3c000003d503982d036081c11a450503042c280c1d0001a030144880407901c040645010403250000d17840d9031601e4804040e0880c0e541030200c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 381467464 1250 381466214 381466219
    0x3010617280305030a0921020d1103090d0809061b032101150806122a0402070201080c070804091b021c0f11010f0509031b0a03091a0705010c020303010504060e0402 72
    0x100006441091550b01485038603000e14143d0540008044003404811003991401f405a0b000800c41117400da4026808089a07002c2e1020314202618180402d400b0102580c00800b000c030701149228030390310f03010192494038450f01c2c1281d0300103012016041d00c80d4040250540034a5520341262003051140c54228100d4148040018500200c24001c8a00200c041c0c03000d80d004081d80034454145108202e03a0218403112901d2204030f039160391050380c0410f1038039500e5010300d0041c015140580e800c140d00c0ca1380041c588050a548810318a0091154071a942140390b500385408100c1a00e001503c0394040084d509400320f070340da083c4110b4840c030b05a00101080000614440300c07418514820301d00c003054000c441c000880c580080c5900d42003039540848182403280d1000c0b0b01c0e4080030042c2c44041c004c1c0c18908019104600305a1402004030015018070b030358801d02c405e000c96104058404503203450740c102c002006a0300030010025100d500a12929119905107034020542ca402e50580e00d000701d500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 381468714 1250 381467464 381467467
    0x913020c150115140706150f0f030c150c0c030809120307050a0809040f06080a050d0908030904021312030c060b1203030a09031403010909030f050306010f0c0203010617280305 77
    0x440f0044032812085441d10301e94607418000c920000e64035016000b01001c0c2040c3d080b04250421070724170b03022030303540d84460b1384131080e610104040b420b0314441605a8100e00441200c000c101d62080d206010b805070300034003100698400005011104002d440e082004075486140c03099003400301c660f00c1c0030780400070309150460301ca150001400040185801400504046103100c0b044407550202c801c03940c000807031078000c034440904008040c00024102c00650078a0f20350030741002241941c2e0700900d1417060060b50b000401841340500448400d0080c01440c105d00201d04192900426170300d8000f200712546402e00a507500c040c0703004215a05400002c0009605596036001110040c1142807010340c248456010403042d601d40b1100258003a0001c404045582c4015181c024001490074248404104051040c010f03180c2c1d1040100c1c209042a1410a10820302400000e00501080d444408d940741d22103800c1c1000304011817414043d40022022001000d441140011440714248004001520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 381469964 1250 381468714 381468749
    0x60807050d020907030c11010f090b0604151202040906020f0a090b190c0c0305010518150601050d0509151608010504020708031801090818030607020c10030b0301020913020c1501 78
    0x1182e406260241100c0c070740400526008540d031f43c2192017105441c1000c41d00c40640001344411489480d81014081d0f9007045055030b000612a0703071100714003615602e100a0b0820710f0941d91a5040700e02c5d959000b11085680e14491b02d4481d210364843d10140000c1580b407030700007507484411000d54179000d0408004803411215114100c84898440c5822103065010b880c020010540c00d1044d24890000c00d41045000600000c0380342c07500c0640c2d90030124410400d03041000303a9070b00909491140c3d141d89000328080c1c4901e1000c1e800c0040d11051500013002c0d00c0d04203e11961f803d0050022000140c0761800d180c0d072030f481480164860304001500c3e8900400225900604801900101c100303114000500d015407503032400b00a034080e618002001804890140e403914043c060f02c0c0c1c12030744500041c403c00b43c0c1d2902080890144c6581402495510170001c1416102901160440a002030000140e101c607400c0800094009000d08005c5100d81202c07202c03040f001484c0d19040e03d104446850782c981 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 381471214 1250 381469964 381469967
    0x60f011502030403060c05040e102301050c0109150c1806050f0c0102071a090105091b03012c0c1e1512042103090320070506040801060807050d020907 66
    0x40e601a0602184810003000001c50f9061244000c003c4003a50307903903038171031903d1030307000c00040080e001102081e0107150401444010f80c0c00e9460038220010040001200c060040c0e43c03501486210130002d5080002c031400700844404a0b2020301c4035414100b1218480b0802250641d4903000901e00140d08100c3c28059580074074041d04044010000044c5000d642d510f2860a90300300369800c07030742d5040f045044820fa0050315012584010000000c002c0c920704060481d0b943d01c00c00800000031a100012100681c80a41150390024482c800010380c0c1144240c06010101c0d6107290b00540e4040d441041030325180c48950010302101e400008140c02c001e03481003050190303482c10f074120300321001c20001d0121909890003078401c40c0124001510240c0d0148030741c400b8600d00c52844c0806240c119410000794211001c003401241d04230407070200c210407031009803501d00b03150007040e844880440d00180d051415042030b070650f1940001d840c80e843c1d81d0001d004034800300303446c025841003003c800903803046d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 381472464 1250 381471214 381471239
    0x606020712020d080f0301030215030603100509030d02120a0c0c02150d0b04050103030309050607052d040e040f060c02060106080c030723130f03021c08070804120212060f01 76
    0x1c40c001815030f0240d034144d0340c13074108540c0410340007007031101d01000400c29450301c00c1c404004041c00e8040d8600d98580300000030f45032000c03c034210170b0207951600030800c10700c0d040040c0e402c12203910380304561305c0c06064400070804601f11400100b11b07044c072440c016420302c40c2c000d6154071980a8030310810402100c01c04140b513081880038040c420366032640f44507656100d002d0f140c001c5000c2d40300002c0e80d030305c5820158102030f001011501845420020106c01e8441d2048c4141c402846451003180c3c42e140750a808840d114a6000c11007010111042c041444440c07809081c0c200c2c8900c00801821011100a0f62174540c02d10950380456202000100b14600078002158810150714010700c030312151030700c03007004517030100c0100340f104602003800d500d01c80603451220040c018070188406d10500d19400189102603482c0124040c0788181d041a0400141d0b00a4032561a44800780c251140d0b107508984e1031290081c0d03000da10483c10b5000722440c040c80850124044c141415000401e80e08102200584 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 381473714 1250 381472464 381472499
    0x3040308070f060f050708040b090708060601030e0102070c0b211e04022101152106150f0306091a06090f19020301080d0e12030a030c03090b04050616020106060207 72
    0xa81e5190703035135076240648610072140306424a0721404591f04150400c10043c0d0801000c045982d0f0040c1c40030320092900052499004800346030100d0080c0039014140d0290142c10001400111841c00c003007101c40945c0040c101e00201c1002d45000038020034a6003005a0068817031903080401030008840300c0c200c11498075841800030340341c00d441d150002c1481c0b01d03243c01b8040f800401d0359500b11000c215007041c000301000340040c415200d0501c2e02c15410741100b00702c400004150555660f0068402c19404003118010140c041c812504d00d03503a8280400a080e400030126050ba550309008805564042141c0d40150782c05880c0d030600d541d07007010740700e403180010f48034031058104451fa00006102d1400194049d25000002c0d03c8508400b46d8042c5c102060002220f101d000302182a040c078103070010980d9484076691070b02180c0b5003107801043c0d0060030600c00183c0040920b1042000384000003e09074090910075020071075404620708100d00302c0e1a075004a0005070094602000001114a0380010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 381474820 1106 381473714 381473723
    0x20d1b06090e0a0c020c030f0f071d1311030f030c06010b07122109050d14031035060f0108030f04120c03021314010803040308070f 58
    0xb1468001045070880d56550900c0212041c803c2080b01402e80d00a81541e103100f8255003500c0d20743c86049030902c3e50784074548000800501e10303002600b600580039403070011912903100301241c015202009842c000c6040001440171b81e0705001010301c64000d01e0086503201011a801c81c20104142d002a9120310240142000b148214500350404035051070310480c1d482441d45006140c13048059042c1c1c56a2601020008100000a5040302820740d0785806441c00034142ca041d000780310841d1101011442c1d01001c2010000b03136401410300600072100582152001c1c408a450092112482d0845038854810310220703007902214a0f0142400c070025606d0b21858252401c0b07144240c0c4589650080245111410300c00c1451001010f10342c01041e0501c84001c81006101811008581c2d5450140341d80001410120010032941100c0d4005005410414940c42e81440a0600c800943c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 381294964 381474820 := by
  have h0 := BRFrame.cov_init 381294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 381294964 ≤ n) (h2 : n < 381474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
