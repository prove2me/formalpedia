-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1463
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:06:43.185977+00:00
-- url     : https://prove2.me/submissions/a9c3c30d-7a89-4da8-a67a-1510e6632a27

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 262949640 ≤ n < 263129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 262950890 1250 262949640 262949651
    0x80d090f0f0615091803030f0f0c08040c060207210f020607060b0a090605060a031a030610060e15071e02120c1804080301050108090307020a06050a1b02360901 70
    0x107440f40400240000c100280781403026150a502e003003800e14000c10300506040e103804002c07540c9481c0390040181495205000c00505030402c4008080312420745040e0f404261003200031840345d1000c81c806084d188904a2410601e120304044c1307ca40402c000d050f540c020f5a00403c200596541c1c5c003d2950500414002c5800d40b02141000b980101c0b960084524602c0c00100f082280c503544151b851106d11410002901042c5900c084009010244110b606025030410040b219004500c518240e54040c3d03101060f0514041c203000e4078402c80111210021828060b1000113030064081001050111041c3c116000d21a0702107803549200710300601e01034102c110000070900f458480d1024650344036800d4030407030400e5101c0403524441801064100301c10200050b405100800032100d100b0b50291001b0001c039628600180507030410301380d0a00180007d4546c5210400c440804480305400510300c4180078004841910080e1180c4059124098030009501400f100106103520540713260002003007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 262952140 1250 262950890 262950911
    0xa0909110306030c040507020706052508070c140102060a05091c0504080f01060317090a0e0f06100503060108161103130302010f0c050607030c030e03070f02030709020403080d090f0f06 81
    0x84c11042000c00740641d240104220b01968005000c108a4203207080041d5100f02d0340392000130703a4920360395030354860f00c1040c0c84404025143c0c0c000d1400c40e0040c01d1350303108a1b41341c5008808030003039441920300690140340425010003e84c1c3c00306804c403c03504202e034a0403184804081d070070031103c64882d000c00c201003010400000140b0000321410404c0000b00b0241b800c590354407000158007070085000d90004244000e00786c58540101018240c0500403000c10b14082c0207040e000403084400500400c03101d080c2100c0c0301e0254080d6405494161504a210f6880354280141e0314100380b03c0340200501e0308803e0090100074802407003002250307544e1226090640c000580f46506070302011040141404002e804a84046a115000081445e0224080e00c04180440c05000141d24180700c5d400005407030010004d050310300c920345034825016074101075546c03111f0308200d0146220162008200b0804d00884200b15800720050300e100795074101e840403070303615803808140380e0f0032049540f203540e0980c510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 262953390 1250 262952140 262952143
    0x40b0108011d120d06181a01050306030a060903140d0905060603070b1c0221060f060f04030308220c0618140105030a060905070e15090306010b0a090911030603 70
    0x38814942e005070421020300b000034240d40351149400004141e00101c3c10902e8400c0701c2c0c004900811040504801510440042030010320340c40c1c60040410711048016141c2d54019010703030b403168200501400306812603031105c50140148400c11410040620071002101e5a1140a4101050445000258018181742c079901d0100050f08040c820350000c1800c0000318ac000d011580742c8603110104009500e2000040e82c017078010311000f1743d540c0d4071500b9001c5030201c03440e81c030920411045030f04030070305d16000e02170040c0c601c580306084040180030401407010030b000d000c3c85604003400c10019808109910b202c038010400c5c1e00022520481180302c200903090b030140e03900700070141e16507450802a18112400304205030080049052010100c0045c3d080301e0150710a80c0203028020040c00305180201c0010848481000300e01e22802280b9640320390b0300302c0f540903175401c0c0710050020201642400154912078000003411410802209000328410241e80070b02e44a10402c049131039141d007071200406 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 262954640 1250 262953390 262953401
    0x61502060603011a0607170f0d05062b030c0215040f0f06050d0c021e0102090103060906030b01060507050f0f0106030c0512060a050915010e15090c22030605040b010801 74
    0x500c240e041c004e401042c414589130900c514402211280c2e0f48805d203280400c02108002c40442c460880841c01038402c00c64000217003080280403104000c02c1e5900070410040b003a19a001c0b11000041040c0f008005040f80001a107440c040c0c180030700300c844503a001400d04000403c40211810f00441e04200f51142e400300342c0040d003040c542c000d88160070018010041e004000e0888415a140c00411403414000e100c4124404034001404034003100c01c0410314081e61040440f40d0019203031889c00100030358a8428082581d0740214800440c2e4a0840202e406411105080d2024010381107003910242c010440c00d0400f40d902000416254507604006185070083d82c091801200300f81e09080894201180580d84018900e130001044c1d00c815a00510f0005103540e82402640800004141001094003080c03042c200300d0300c001d481d0090041800403e640a54111152240501c441d0000744070505080a18015401944030706607900e41b1600c00350b507030035142030305c524000310014001550280a034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 262955890 1250 262954640 262954651
    0x409060605210612030304030c0c0f03030e0609010e0a09150b070302061b0d0606030203010905010f030803012306030a0b040506062106130509100b030d05090103180606150206 77
    0x32400e00c0203103116480141c2000b00c2d00720030154208001541d40e60740d440824002c0c403a1200312500c0c3d14240c607015000c44040d10043c0d50000d8081c0001070b41c8a2030b968003030140d0780d25580c0c0651100d030501c280201c035005200d0381d0b4103119107000d010134152034100c0b00307400801c0300c0ca8011170710302d1958070341d6619035070a031304141c59034a0100b1021000c40c0d0001040f076007284010502e550708407440758080c0c0c105c1c000e00400705881420003c1c000b9226902d5000b07141a604030702d108000c2a42e0f506410042c504962100925030501407004000203901c541d032151400c107030b0034001200d082c16000040d1895000300c03400e0b0041a510100c0354028103007840b91541c0454162001131600e000d02282115040865100354203c075a1000007511a44038903024882c294000003061040d4203280021302c0e11040704200c4021303400d2500c081e05245140c0041c0400e0301c249182c81d0a480c01030b0440044000e06a00c1028403013070406c00d440130300050824418000100015081e0755107008420000a0404201520 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 262957140 1250 262955890 262955897
    0x7050304020d08030402030f100906050903090307030b070203090d06050a0c21021e070501050601021603030f050a020a050718140c030105091003050f0705090901140109020d0b090a0204090606 84
    0x400c0010386070340411018680d0043d240940f0707030b80d451001901d050361505000b119402850a0f492004807140c01c201e0616100d52000d0005641c4d019080d84e9a004101d00c466259206400400105419541032070700003a080c81920f02d0103600c13001181d030310032458008403140b59581041010054a5102c0c0c084002824039180740300300c151503480f4803141c400c41e68009000b640080d1091a03070507010341e41c2001c11000001c0686801c1d0314140300740201800c80707245026024a14662110112401c0349100386d9034192205000004090300841d642d402a01e0020254440d0046820124104210210080030b020301050b4200c443c604004007620249a5100b00f044010030501c40c2c04031030781054034191401039917620020381e9890044c0d12811096403014125004880544c40c201401041c0c41c01601c0342926107100d0740d01c1e20f0300700c2400c8800e41442c04000070601001480400c0c500e80003000040320006c400300382d54402c0c0e40041d0701c0d004280ca000e480943c1c0040c0400c0055654000c00000708410700f07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 262958390 1250 262957140 262957147
    0x91807081f0e0d030c020109021e0a0501020d0c0b040804120b1b070b1501030207020a12030315060e090702030417070f060809190f060e0109110a15082707030b0705 72
    0x60b01c1c0b55440711129000ca05140c0c966413011500c61003580020080c640007040420145da0042004000018100300300740100c13034030b68001c190340d400050502c5001c101d40d51103442c1014513840e484500b2101810444070260304000c000703502c6102940240c001809420f8075940707410101c078807080700030b804c80e0b407003503100818400b80010440120350203500c01000744401490808800040b0024494560003d60101380c00c0404a10710203580140380f0903510035202004406550b9140902c13000c00c91180100217004002c40d0ec0da90b0500c501520342110060040f40c0c2015110703900c07509000070b07119100d80e180e44610420041d0074200303591500100240d0030107080c81e042c551070942c1c54189880c8400540b0140c00b00b004100161080c0d60084150084410040040031600c518040c0c100088203440498079000c840d40c03203142c4070590004803182400342981e1704080c40e00c20385440100524220101d0032040703980103194118552810140e01c0f280162031414250b29080f40c0b02c01024104030100074090 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 262959640 1250 262958390 262958411
    0x150a110c0d080c1006030c03051b06090f011e0c020123040b0703050d02070c0311120705040f06080f03030f010e06010c081b010606031e090b06091807081f 68
    0x78076000355810603a801d43d1900d1208070765180c04501075400e003010b4a00380c40041400700e614054003c2e00c0c8250156402c810b00802c401c1035004a003101070340d0002040100d00101e02c2c00f5643c0c1c04240c0c1041c1000e810ba00c1c40300364010024004030464001003900084010119a4003c9234483c403441500944140101c00740305c45816409a40038004c0246e07000076100041c9030180d42134980400d070070b0a066545000720b10300302000c2c041900c0100d4403600701d213a40451902e0305180564801e00500010100586040b003000094945c14064805c803503542c12010500319028401c0b501e000c5c01d2000210303941d0400c100300725250541603005009230ba07202410b1140710780e80302c011140c52941181c44c564031504400c0c0c00714103404e00140c01c0001c81d840c06100141168054100e52403002504d015481c1d00580003000100b85d03000130b80c008282010082c00540c440c0703400004150404200c0c0c090703040300640b11104605c1c0002d5500a0000c65201084103101080852150b088070101c0d440c0601c0f02044c1c2c3c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 262960890 1250 262959640 262959649
    0x2040609080316030f0203040308030709051005180105091c0602090108180c131b091707030320030f0a11100b010804060f0b03100f050604060e0408030411150a110c 72
    0x203800080c20020140c4007040c5d854400c0050301e01550704001d0241c0c3e241001c03403010700b0b001010b11501c0e01451015525041950042064030f40f020002041079404d440200011601984480d50359640507450070108011a0f0701c2d41d0301c2035080c500c01e15006903a02c520f20005014240d00500c010181040c0040303c2000010100d18001d03008010381c1d14240b016680d1b1004409000210203040c00e4001000c07015400c2c650100304c140031180854520700e038080c103020503140c5501480c000940441c2c09803408c2960135004410311b4a44580d040280c0341080e5000c038244280c2e0340f26200103000541c035401c02c0c420601040c45039284d0911440c5003040003884620018001510040000d0012a95541100741100e11074000b840c110740001c2c04d4462919007207820380d0080030b6262010740111b10b81800610fa5040620600c4292560080305803181e42d11949d52400700d9000610803524481c980203416041c1e190b182610411450401604c0e4540c0d0040f0401000100036000543da16800b40020040d44c1c4c0b503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 262962140 1250 262960890 262960927
    0xe031c030b041d100218060c06100b030903040501120207170a18030209070309022b0b01080d05030c1602030105070c110f131802060304060c180302100516060f020406090803 76
    0x6129001d41c5034042c6511042010846d00221900100c0001d42c03003544d90004501c15209044232281080c00781c0c0c680420300200d020842d410001d5620400042c0105d41c02071900005202454030094500700c1d060b52005000302d4441003013624a03801046e02002e641d08491311501b80030f0304c01d1404072007030714540003e103060341c005d03058038140340e51805081c00b507449100e1000460b90b402d8040382960f03034840714406401c0048100030343d00c01c01040008a404400820303d0041c41281d035a03030078219116228035200580c084c1020340751185590175028016102130003190700c5241d0a0b1900c4080004038240200283d1103c1030003072189502540200095030344510303d450000d0080c2c2d000540d1540307860f54090070805020003950000d4040200000c00a040e0084821580596103001c0e482c80038446204a090035800700075446411800c0d1205440c0c480c101401031072143c074a04003018001601c824086515004000c2c0e00e10b030300000e007401216003001d03001000b409400015484e007121a49407254208 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 262963390 1250 262962140 262962163
    0x100309031b080d15060f030516110a06061401030f2f130b0c160b0f0d0f181205071106030402030a050d0e04050112030c030e031c030b041d 61
    0x55030340c0c01400074003090300250f89070b1200510b010000c4518079048030070120b00b00d12a00d0b00060307000440d0314001c2d1185c01903034043c407100381346450008002802540c845052030b10680d0b8922904203000f001c6021070243e90014500c5d54404011503884400040c242d0f20091800341051781414048940c02ca20541021110414402044808005502c81d80424400c00008094224100f040803170034005100c02464405038110840384a8620081d030380800c104240b1627038440c460140140d031802800c14006103011281d106001850622101489084500c440c8072070064485201c008802c00c06007400590040c11141000750502c1442d5840780030890131a00082d02078034011000ca011507c0400c0b10002841d0b00800b90303188104003c1008102c098940b59a034404c0d800d00b800000d440d54505640d11400b501581c4034800c045107910255640b1125814803905445046502c2004081508045a0f103000c140c0d40810084030f034104000944800640343d503039084104c18030424085000034400341e01c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 262964640 1250 262963390 262963427
    0x3090318040615021005011a03040615121101090602030c1b030a1211060112031d011707050d05010e09070e090a02060d020714010515041509060603050610030903 71
    0x1600400200700503204950211501107850381c6031542d9103030040740360400c40f480344000304440d030790751515902d8600350140d000300724650400c0890007152040c1c2160340118496000120005d5641503c0c0080c0e0341c202e038084d214803e42c103035003030f0003580c0c000300060040c81d00e480154244220161100d4031494040034400c450751100e05031140540f800d016807010181c000c400c6400c845040c2101401088903c50314403424010b42001040c0c8000520010006a4059481444d051a0101403005d196201a01c441c18840002901c1004500c0070701d0303481c4108031603030300c1548461908a0318001d4400c1a001300544251003000c002850000244880c100d968180320f400040d00d030b1404090814025050181d00500c00046ca58003011603500100086417081c8182041004004081e0f82203540548242d90b20107048030907210207141c0340e0000201405028074601206d6540d0002e04103c60203030340f018001c00d481d20100f0143e403030300c1d0301c1d03648811070503050a10030b40b000750740d0003444ac110803084031500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 262965890 1250 262964640 262964677
    0x7090e07050a0908030f0a022112060414090c01020c012a14030c0309130b0d02130f090b06100c0305030109021317150612060a0908071e0c0b030903 65
    0x24180300303c03001401040b100302a41c0d503865a040003421070340e02404102001d40300e0b036070542d00100310f41c40c1c491400c07070310341103004d82401c001918000c2c2109020382102d5102da100c980f01c640c003a95208115000703245a00044c82d50302d1904002904186d1100b01840c1840500c1e04c852070305aa021040f10070200d40d10b100b18500000500e4545810491103140c0082c612000c2030384400ca000002c02030040e28011a0f00306401e242d42c04200054070041409290045101e11503079005003041240490041c001030700c042010004104180c01707c409000b13040e03401e00b68582c02c0c01024104024400882c103003c2c60100b814081175200034080b4441032180d2a801503000400d05d5517200e0035802c08000c1e06c024000c3d4034454240c11004c40e0303039401c0d00b10718800010401020038054075024000200190029000d80f41c0c5607601c066190003041c1c80c00c0c0a031034100f801c100b00300c0040c02c0c8100300d40c51504050001c44156070142805a412800750300620301000c01001840714100300041584d03c0131241c44100081d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 262967140 1250 262965890 262965907
    0x80d020901200d090f0b0a0309151404021002070b0703080a110a0c0c0603021309020f0f0c0312010e040209060f01140a02010b09150a0b03040c0803190807090e0705 72
    0x5003024030602e04041c0610300e92003038041a10104080e4440412a0344c0d4189440d10340813039400d4000c0c21711601c98000e204100c910f100f070b40240c100c5982980101c0001c0140750360701140f41d040e070340c40c040c00509456880b01040114901b200d10341e4051500e40c4010480140ed000c200304142c4901c0703401034103008000001510b000b0f00c45d00840d125065103a0350940310021b0600150a0102403201103948450450021842520910940300341c02e40c04d2541003140d0f0310380703000c12000f075020a000102194003040700079072800a20300142031064085004650310a100c06070644403581c1a00640d00301001c480900c170159540000307640d00400200e40f180075005d00140141c0c4c4125038510f80011080e00400d000201580650180303484003403d60750200305d643c03500b8426189010881030039900c9081c80c4418043c2502903c043d41d4014442c8000a5071643c4030301d40329255030041c0c1550f90b4417030762103003c3c50003e560011035680c101800b814100c043c50f061040794880c0400c001c14603010000c001c01c0104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 262968390 1250 262967140 262967147
    0x117091018140609060c0a0203040b18010207140a030809030114040606050f030309101b051203100e04150b2e08010b030910020304060b0919060f03080d020901 70
    0x4502040e41040207001810100e4080e2440d0454040e1010400c0d04060000300b14049901e5126250030700142c070156485122165017904040b029008522040c040810042d050710001c11030310ba510464909004070500009251041c039410200c00d100504440341d9190b00d41400c440e00341d99104010544038180302c3c0110380101840066050440041002e00c0248452580064141c3c2e2098807003000e2101888149a42da1080c1100ca580000c3e01301d20740c5901c1c902c552401d5048117201503a02180310203980391603281000d15002c00d000c4071000014000d0010301000e01c0c800516101604c000d00707191540b1407540e111018410000310544840c1c00e2034441e03031218030117032214900d05200c84424820316021200503059000740030210f0403900001c40e2581600303064034450042c400003410b42ea8100100000a9000500704466032501c1e1801c11410f991007000782840f4000e08014000700c2e030022140c02c0152641070b0310000d03803851500c40610124040104071420034040d5503015a54014600049 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 262969640 1250 262968390 262968403
    0x1061d010302090411210c070b04021201110c01020c0601090c051c020913230f1329090106050109050d0305071e120f05040608040318090509010e15010302011709 71
    0x548000c10004001046c0210080ca65941081410000029544114a03c1ca081c42220005090080c4840c0002c0041c0b8003100c040058010880c00400c1080c2004415480341d00000b500200e1079401003070020810108000d0360b401020603210070300c04000c200202501038070465400e81086103000044284e03059858040301c0d0007840241904d0340a45012140000070042e405c601d110f05e069503130840c00d400d424840a140101000c0c54408480c1c1c0740c4805403c04440840b100321541d0070a02d8a400440013010042ca4072000442c0800340c0d0343c90120716903421070b030042d00958103101d4a05020300280e160327086001c4410381d050030700303c0e5100c2c8a41820303130040d903000e81c07000a045064500e0700704101c1d040360300356100c3c5042d442d510341891254200303550901a9002ea0000581e6400010303000c24880d966548808800300802e070780f2135407901c801c48243d600880d11011641e442e000300c4004070b5400c118490084100303403900c003150350455000810344c010002d40d40c1011502c0344040b035035444092010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 262970890 1250 262969640 262969661
    0x7020705040e0102120c0d15050f012d020f0105010e0c091201060302040c0c0201020c100f030b06070203120403020108070c0f061e0507021c0504080601090c05160b150414010e090f16050901061d0103020904 90
    0x12628440d1550500940d6010b058071653b4165084c100000f44803c0302d00c400c00e01422030700c0451030600c0047c2c030601468003e825111001c0e5902c510001000d84c85034803900300d580d011030303842d80600c0e29207000192230420612940303405000301c0c11035813071820381c400c0151141200500d408a1000e0082d0f00140c4603004104c0c001e9418043c5280401703800c51010000c01c22203100fa22107075115940c1e09400d5400100c1b100d00a0302c41504002c1d500b000072030303c2d03012550441c520f019034054601c0354101c940484c0c07c06c8a002000da480071705c4016100036001c9541c5409030a6182080c601401e00c0a0240c4a12061007224032858459400e03681352400b59040d500d41a15030034407101d52020300c0c00c2ca02884541a00c019401602498211580707080a0241884940303106601d00126441c00800e8000540003e09010741405240c2ea11020000d050190701c01c00d035182803001d4911070504040084400d01a40a1810f000720805495418500ca090045609009003001a00c0746621404a07001e811740000c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 262972140 1250 262970890 262970957
    0x1512030409050109060501050301151b0f0b040b13020619020f0a060c09090608030a1805100215131a06011205010b031008010507020705040e0102120c0d15050f01 71
    0x40124000d078150344100d04a44a0940901c8415a42c83c01500d035848207019144402c04c005071100c0009011b41c4030030b000c101a00301140060040c0e40c6920f9884207000900725610b0705100140420300c0400030f240c1d50030001c0800e104c07032004684d500156451099001404003039281c0000b08101e24001e01c40d40b402c2000355801e954965840385000300003008843c00250110380f401d0004917003583d1510929064503c400025881c0000c0e00d101502d501c41507040ca06060341081c04086400c7d16101300503049104103800620300c65244900e507011018000b8507203040107070b0b001070b00000b06032030380707082440c546040c0d07400d026648039440121809aa469402500c05003840d00002c0e0b0280707500e000b14444e01400c443c1004203a144e0404500749c0d0000e50703103000180e2102a00703200c946441c0e4810030703a0510003c0010302c0e240604c014150010030407a0221248200840d0101c0d000103503000f144c0c0c921146248121f4414242000038200e101c1540049040240045001a02248150028522018420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 262973390 1250 262972140 262972147
    0x91b230a0b0a1e140a110a120207050114030c03010b03070e2710060203180a0e09061b03060303030a09260903150903071101021513020901050f0306151203 68
    0x1070240011820b000040c3c84210101503e030421807280b29000c4441100c6403940e49003100d022030454803107994000040107805481141c4000501c0340c190f5240004403034018003145031a00001400803007001a41001c8071000308100300105424104990541c1c14800426440f51140716040b00c1c83c0c0103240c0e07116001464030640030307100783c0003104e00010039030003103412a0b00d6600d8488188000f20944101e01c0943d000b400810036101d41c0f5448550204e90280034031007840e40d0707104020004002600c0161070364220600703101b0300300c81084072041010840c65500f442c60502c0800310343e483c440109040344056640041c0c6040011010105856014103084814210407000148005074060300ba414803a10890100705060355040408a00c110070200c091800c0c100b0301d8545014111440c0111411030040018010945000e81980c0d170150071000c2452080020764414407401c4401030708a04d1090f41c0c0a041314aa596001031301075442030b10311200e280405600c1012684840c25110340000900022 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 262974640 1250 262973390 262973407
    0x40c09021c02070b0f1f06030e031c0204050406050303190c02310b100c021c05060a06060201140c0703211416030b01050a0503100902030109091b230a0b 67
    0x20062980a01c3d25465950310a40fa0358561a11025a0040300d1544151b07031103003009024060b50044039054048802d881c45c01407043c2040d09500355400342415107960114007030026007001d22410000e043c080d070007985800c2c06420648038a080c0994500304100480101500b1919480703200d00301e22000d48052905804500074441d100401000d21080291518030507004500d000c0504443c242a15151240300b40c20540905c800c0240c040e841100a402401051000441c10402c407482440e500344002406801c000c6c00900707546002c2c032074116041204040c0207018a4840880e00d0340c03945410040741e024000c0204c0760300780d144020429419481c1030242190b02c0a5180c0051040c8024050a24904128101a4115015500540d000030310502810035018069401035030001d204071a9044c1565031407540105aa200360032454602c0e803110046c408000396405035440d03966009043c00c402500380241807011040318400c0414603102a4070101c21905e40c810480081d000006047c1d80d01c40b82c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 262975890 1250 262974640 262974653
    0x90a02090f0a14090601390503040f030302060c030709060c03020c03060903071104140112030504030203010615120e030d0b12070906030c06030b030309090603010b030715030f05040c09021c0207 85
    0xc041068004c01900c00011203661082100b07602040c0d1407100d807440e5201000d40c0700807140c100a00c083c400402088000b01096003040500000e2100d003840039409419490300174208000540341c3c140031601030007440701310790300002c1d041c0c2075075120303d0301c44100c0003141030803850035102c001203503050b010b0701c0306020030808084001c1c00307018015141c07100c1c01c008020501045440038548007807848a03c000601c41c0591700050480003602030300e0b0050400740c42342c000900b1078100e40c1c0300e140c6156041014903a850740006a02203049864001001101c10300c40c2c2c8987c80c4d00c10b802417802c0c0e4950311680003025075554070312001038696600403206120b451300c10401c020019404250f440340c1c100c04000402c1da00c00c0c0075800a00300c0180245040a1055082c08071a0340301400007549552a0418003850380c804111038002000d4400303003a802a2021400a41111103c1c1c0b290306055041008100c080750841c803181080760040240140e480b05072007009000d031000040307140259800000c030902030040c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 262977140 1250 262975890 262975919
    0x3230f06190b040303050f0d020408031e090a05060a03090501060806070201060e242101140601030e060f0a06170a03020118031e03180311060c0306090a02090f0a 71
    0x391160900948441a00101c040c000d2040d00d206a100300010f000017407144d0050a03070340c0786007440981848107490380c4030141d0708180c1201c0c01541c000725144c0000c2c0c5210050034142032203500e185181c01c2c60130f00030845004681c002e450082c800007400095092281c1e0020b200c40b50040300030000079403a12481d5864000a0302c140c00151300b800804540d00e21090610781c083c1e00040707410680d0140c2003c108046848400341c1540c0902e0408a0030040c15041e030100000b00035940c000140008140b244001d2041c0281800cbd040500c4c080c0c1c03180020314000b4100e5000125400101d8040d40c600504202808071904071084c9070146940080d880b444c001140500070341b080d00248100311139981550355407040500007600080c0340c442001c180e002e0115102000c3d180518011840d5a01c3c183d1002204154100442c000303100c0c2440c105c10450309002d541c1e0860302c0e030074244c1d20b141000c1d000185d2683d00500302c1400d960340020608000c0c1d54120001c14101c0c40541480da8031580d96560050041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 262978390 1250 262977140 262977151
    0xf010c0c0c050103110406080901020d02030106030c14040f0911091908100203060a05060a1e0c020306010e010803070b130b10081c021902060417030702032104050103230f 75
    0x2041140080344640c040d00494100110f190101703400d241c07030b2407821100000003902d44c200655003041054501c5140b4002140030340120b84002c01c6a8419400003020204d00d42c01042394000184420f00030343c20b800c039031401100e90f061404a03d10b1080c0403040c245119901c0402d0b440b501400c0e81072000480740f41d4a40480d11044107032481002c0905030036042c0c0c4812500c1070b0b0300012a5000b40080d03e024406014031040528102d40c3d12200d250a08404a0000c06007001140c1d08180d0041103143c10451640505000b0111000319451f00d01c8241d5a40569800200103004480000ea12001e045d20f450258a402280360030b92030801c51750414071001c45001c0c0712002e009401d101c1101610302c201030303050b421a0f03a0081440c0f00c5030340c1c880407459200c4030040780c1c819004c004c00154030b00102c4c143d10040c01c1c000c01655580d80c1c0d1b44101454008054448200740d14088480e10344801c021003518200c60003800c1c0410741c54010580103081c2180c0002c4005110714182c2401074228001403014402c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 262979640 1250 262978390 262978403
    0x804051807080a0b010804080c0f06101703250807080a03020307090905040c050907030b0301020d06050301050108070f140d0b040f05010b010219080c0106120f02030c060304230f010c0c 81
    0xa80f140ea00341c1003643e542001e42400b148090000c9000249120000c10110a040c0d081d00c0301414444e07252402c000d001c0c1c0b1420540d0740002c000348040340c15100c4540140700544000c5160862214152070444040e11040c20220090f0003102c041c0240da608541416601c1034000b44e58420f10f0303501400a41095801d0000180d000c68040b40815440c40340f980125000380c001204240350608108031064010011010552100c42c4003d0704e4a0900180c0384880c0c52034000300e085403e000900d403c50368141d01007005584002e90801865a2200ca0041030312030901c1179191a04004010445924007036400400c1ea80c01d101c2000103000700c0505142a00313114100912034131034090012640c079604045005104918295010001050030b0000d0994080820000c90344a6a40c000300000200c50403081e2a8080781c40f141004511381440712040c03010003202c6141c10350810fa12140c01141c201082c002c4096200100c0c85085a01004814480c086050082c030200032100e000400800381c52408581e030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 262980890 1250 262979640 262979657
    0xb032103150a0602060f0a0e01061202120601050a0603020702030a1707020a0b0c0d051e0f1e070309031e0c0803090301140403020606090408090405070509100c05030a0c0804051807 79
    0x80c6420003002c030440e0520703802130a450302e4008458440341005015200c3e4903a0300c801c8244551000e000d220300500c800082111514841d005011841c90700c1a81a0515049900140b2656031070403a4034007640d04500c5c0c01626a00d440c03001c6462705540c000e000d844521002c6038100c1c1c85120000400c1103910980e40c01a015030354084030451401040c500c0d44003504202d8205080a102d030002c1d002c80c0195076031500110301c00303510360f00300e95114111045414000240041d003145150300110404061603c80c140b03030000c0ca49006203400c0d01c0d400001c0a00005d40c503480c070a407050608003100310b50007220f45410141c1c0c07540003d5880e803100c000c0798082d5003400000c40160000310005e0384101d4154003c0d0510740c4e142da0030048907070001132007100c00f68001d03c600700a0b07464510a03241700d1700c000d0315070f1507039038034031004110428800340840401c00001c1c41c0d0500020780044203440c500980c50038190300c3d000d22850301d00c216000300e40005420101012445445444161503030340640420344540d5203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 262982140 1250 262980890 262980931
    0x4110409020901231c0b010806060f150d0e03091009050d020d020607121805030d09061404050303160c0b190f120c08040b061002060a0b032103 63
    0x280c460340d400103507110020000420500700c44901600982c0032001c04500c580e16460f00081210750340d17203803119803102250721001c01c100e02e41d2240e90241104138010b0000f8580701c00014965180102128060482c403c141a44165203805448451190f030b4000e1000f28643d4040969a400c003107003051280c00c41ea0784140710b403801104c828058130005008501500c010b9024001c00070102d103001ca0700300c0c4d81040090046400c0c80b014507a0644d04d0b5460450b0007220b0090100500c185400031440390f085082c400566070b8001000408542136410b102440042c03039024005640215400990140000910308120b50f4001c1c500740c60152150101e85819501d6940e110198020200101011a501802c40505a000d814245840446480c00704150307034000e10f03100152054026410003181d101c1c070038401000380e0030903045d40c08103040d1a0146c880540e50002507440344054809030303025584985421203074034140031000540c0d00e00340c0030581e111008a00034046600407141c0006002681401c030741c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 262983390 1250 262982140 262982149
    0x1120515031011190e09010b0403060507080601120506120307050604170a050d0207080904060e150415031709030a05070e0907030c0303051c1506020606091006140c03030f0411 77
    0x940380402068001d0903e8202d9080d201036202048952092024090011500d40d1b0b034902d6141c0a403034040182c1d030302c80385145400000d07550081c16940a1040540400007140d0b40b09000031403413184a05e01083c01e03140e61020984108628404003d240000604041400400103015000e1072241c40c404402000b0744888030098090380100b200051030030040302c0604480d54014001890140300c8403407514562200080071034009500141810300910200b100c00410303102c14440000003a03c09221030505090b0020402d0214000104810003030125080f2102105060300d002c80400f40864414032102d080c4583d03915100c1c443c0e80000401d00d40083c0780c00802042d40021a40e108104a4640b4215a0259903e400005040d401c1407a41903c0001c2030480f070089032603016514000d0700f9024101000241481f40007807205004081640500c021392540e4032811003265007a00e406c0b0941c0910300c41ca851907104006e031a01d501c0c4004002d21443d450700b291803500413880b4910090310380d0034050500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 262984640 1250 262983390 262983401
    0xa120507080403050711040504060c0f030c12150305030307110f0705010c080f071a1b0903060402040504031b0c330e01020703050f0102030601030e06090705040209011205150310 78
    0xd4000a038100301103800680240050101c40380305100990303a014200340030804550040b40d0945103141c0b110340c100c0605030041d58114525545107410b001c120341140c005410320f4004c07026070040a540301001c1294140103661000034591000079a0b03620300b03103103c0040803d101920b41c41e14a00800c503201c4020200090103070112601a100c8000260041d1140ca10940040860f02e007200020000840081e0a040750100f0100010b5602c0019050100c400390601004003881c421127070080280801035940007510765849503040302c01017a40d80d51303844d081760b524000c4080846468101420301d0700300a4081000345c241c60303919102212010040f29160989007455002402c4c0701902ca02c030880d40c41c0305610030381d207065041c012900c6113a40c81c1d440e82d10b0400020041c01082e507001c41803240703030340e850300458554081c800e000b0542c6045c520505a12182130744245032092381c0c0006c178422242d0007800d508808400c0014200003030303e0010900400300307072009802d0b4424020b00346140750441051044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 262985890 1250 262984640 262984651
    0x606020102570f070e0703020313080d090309090e0a0b07090b07060507030b010c110d0503041e05100905010906030b0f0402030f0f0603031318151205010b011d01082a0a1205 76
    0x80d80003901c46c0741c0158020760025104c0c1c440040d08202c0c0c03a01040c00e040c0103041124140c1d074005905440c5050080000703c0540100b141241041d203c42100e0000181c008400313600021101c0c5652103007203083c0c1d10f89055a000d01d0f0761080c0070600030140318250f48050f103d1445074900f07014491079480116052004203000500c4002210103d010030304040c0f10f10450a0b200780e08032840e0a84074203041e00c8d5900801e0f10040b0001100c8814881800e0042a43d406211107042c801e003080d04100020b440103001e8042c1804240d500e80960a07643d80d031103011146102d0240086581341448022540680340c112039030003069880002050035400e001040300c0b6400c115203141e0110904001d0340012151690400421007500c5004519030070348192044401403a03918886040320002d46445820340e15600d084906010b040d00c9551111a41040d16080c8203809282050840e6107001d00d50754921480c0c9400c000000458104143e031101030802000c0d200740545501c55071090303c040001c00d0720b904540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 262987140 1250 262985890 262985909
    0x1030c0905040f02130608011b020718091e05061506030c18060c06040b0a11040b2802030a0e060c1c17040c0501030606020102570f07 59
    0x30000c812840d440540c00c248500409461040c0c81e40024014400c2102481035141d43c54404010b0071209100711100030048940003ca40e5052802c080d4860700c0610400200b41c504055400000d0110f50107100c0c4d00d0b610802007407001106540706803108107000c1040710307a80300700e070082403c0141c0c0583c800c0345e229000b89510301e141d90706002030941c0e0b00984662200020f0321350070800c065441c4400350803005c00c1c0c4c000800d010b00e81410400c1c10020050908410b180c0b41440c0160a10701810441d0305075040c8840080d65480750311641c4052088459211503814140315a81850581c080000c01045903a650f45040c1102102d0401995200300750002286138803051002410b98040d000c01d800c50b4009061119080c07080070346d140b02c8030341c084604483c840c0c0314040501c11580c1620543c0d014284c9072008500b807a181c0c0c0c5030700e558590041320740580f14409609035902e0a94007500c059402c040ca51410000d09280c00485c000c08615041e00d0b00c4e075000d02441580896400903184089400d080c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 262988390 1250 262987140 262987163
    0x3170a0305060d11061c0e060a0c0f0512250201050109050a06051f0c1205041805040b1317120108210703030b2e080f09030405130605040603080706060e0103 69
    0x4c0400240d5444040d40050304400c00e0950080c40c6c0d01c910901608220445c0a00281e143c070401705011501c03407240c05010f00014400c003000c0b480d442802d40d48031075000680004651560407282e20000c10740610100d41408071b007840310701a5810340009040300c101d84004d010545912480364103444c5980641504407400f02065118101401c8504041c400c9600300710b205099170b0307115041100031240300341c07000c141d00180410a200050b60752000754001044108500c0c1416603a058000340094010035012018a0081080c0038110f42d42c0e1003c5489800c1d0542c0e180d20902000c0c042c54000d214442141c0152104219100e0244024903201160396841030700d03090696400b90001c000810400e0b8110802c280054140c20148030300403964802c10360100c0000303000200040001034014000c94940c0005001d02c0415034000042d503058907800c80324403103007482c0f190700328000300480d03401154008d060160000c00d0000080081110303501a40c4240b0505032110b4401140d0042884000c089400e01c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 262989640 1250 262988390 262988423
    0x10052d010b07080f0f04080d090608010f0e04020f060c0a02150a0f1101111303060b03070810091b0b040e010b0c060103080a0323010512070e040b04020a03170a0305060d 74
    0x50707004002941c80c2c5007070942058054070170408642c109030055007043c0e101c1c182c81d1107580c0d0003134107507401480c1030300e0a00c8980d030400c800780d61400f409100c0d04108410a1004c42c0856503042c6050440200c00f80200c0d0b1a1500c0307044841c1d44400705071003070b40a04110003a07040551441412a07280403281d072101d5600c03101d42c41044030212182120014595070b15061004401101001810710740d803010718002c41d460444c14984100c401526040d84a50f000030ba0400c0303e050045005100c007040a040081c03c500f00e400c2004016079000c00051040403214000309584603c3e4003d403080c4c0d8805041c00034a07a886511110f024400c4020004955000e800100002013401c0c1c0202651000e520f000314000360310039060310b0b09000507070700c5512505440e0014403490510000004094031090018601545002c004031503040c4003800181034103441c07030300090a5403126175145d03000315404040140062401003004215400503010200024200004244149080c1c4070700a05550815420700c142c1405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 262990890 1250 262989640 262989653
    0x20f0909070305070b03150103022803020403050102070b15010f08010e130b090a2105030f151e011725022d060f0c0d0506010210052d010b07 62
    0x4100203840d00c5964008000074106104140051010344491500c0e81412500c1c0040e010f4440b5950741054414052121240c111010254045060701c0f0103106400200000720040d200d56040a0090f6000003180810400c504840c2ca101e00003182c588030030f251000c0011105816081e20140001c0e08107401886903c400b1401581c00104a80b2101c1800c500c1f5503441001c0d88044402a02075000000d070340043c080034052040c2c500910762250314140d440b40901400350f0201600b0140243d0384103000882820301c0c003000d5420204010001190907581d09140c10060300f22000c840c0c0040c0c40942c8040100003e415042e024400c20a00000e410185014240710004000c8040086100d08810900c04140c2c1000920750501ea10003201400110403a44918100000e070201d0038080c0c05504015484c07280c9402c0c0d4604040c0d0308404511a03c41a00403440c0124441c10011082d2030308003403143c503c805010b140111110180d4414107850181c5149400aa0034802c4001e041410080040003802 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 262992140 1250 262990890 262990909
    0x20901090b03011b0e01020f01020a0f1803020d0f1403070b0c0702030c040c020c01020f0f06181c05090f040902010f05392a01080a0915020a0912020f 66
    0x1d010b000000c1d0000c0c408124038034800b0204030340c40031036468244040c581d6814045008854000c01c0258644001c5542c01800701303518000c0d036000c00491000d000d20212a954065000b0340e0004d043d110248054201600010702105044070b6024240c40440000d5401000759408150882c00701c02d403990720124120490751080300c08aa1501809100c0900340d0f030386103d60046911260b004051000044001a1a004c00400c04101c0340d404400c00c0d1515280004000e907001151030784032800346081c0c0c002e203450212139070b0700d1100403c002000365420300d034000b0140030780100440da007031006444034041c04111081d821010307001500300c8085650a0f4043e50080c9841820780141c030f15655043c000c440768030b1000c084085040e190544111046000800c501c0e080003500c101d0000452414801046034402c0c0e94038142e0502c000d800c0021f0000d0410380c070280200c2e40000303042d006030481c542c20000a40c03103008004c01062018002003280c0300114a541c50140c0e000d49440d0001c4400310400c51040b2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 262993390 1250 262992140 262992161
    0x71e020a0b06120105040305030115020c240417010b040c080601020d030e0705091906080d0816052b0e01020f07061d0d091d070c03030507120c05131202090109 70
    0x929030407400f4003e02442200d110780e0080c2ea4054480d4102020b480d09e960300e030b0b0f864034115448015103c00d144e41d40e4103080c0901e40b00e142003040d0085007001001190103140d21541700c080da000000114480e040d007000c3c06413202100d04000b060b0990809444240c0c0540707403240140d00c101b41280f4080d0186c0d01082c1d01000c10812100f22070764400000d01107840481d9207243d52015041c04908101580c01207a0103042e809001e0306954048940c01049050000c0000e110b2046100302c140c03481d4011801c0368134028442140b0388490203414044106103000000c01a40700c2d20381070090b1400f01042c801c4d107241508000c041894003047d615000c001c3c000c0c1c6026900080b901d00101980414204000c2c0c8448a00351030745180945031886040d0146004400d490b2692040010406819441820210354590600340040c0725102c440080f80c609411100d18502146400d109400107900324000e04460910800c6c100506038895440b1886021141c2d002908412403c0060040046540240100302d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 262994640 1250 262993390 262993399
    0x504060f0c0203130b0c060f06040f0912020601060504141e04060303080a060e010e06010305040c0e0c04030c0f050d02151c02210708070c1502030c03071e020a0b06 72
    0x9500001600807140d246461501690000450b915482c00c0011090300034554003074101e040c40c0000c054035440d0900141345140d10141c001c00105a03544581c0b010030411540d000c20009400d85281c036409583d00c80c0007010162143c0d5000003003017849007040b6020b6480035105200c0048040041c0400d81c031250902a0500c0d5000c241d80f44076841e14811040154042d94841145003404542c0100b01c405a40080c54407121000051061848181a052b0800028a030020743d0b0b9a5600306000c640340745402400389503440000340400035900c00c1c0500162805072074020340003640c50308014070001e0180701d02600080819400300143c80e0010480e50224200050640743c94100f040700181c5071a51030040010650120341c1806010120b64034024180c0c4e0134104941d41d00703181102a00c24070000b420700c0c0400c05640c403207500300b00400d0b0300d010890b40041030070f544074140351202d0402e07030704122a15800102c941e545000054800c4206402030020343c0c0103072440d1241511648500480186410b400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 262995890 1250 262994640 262994651
    0x115050901050705060a0914070b07081605010603030305062803080c0708060c1819030204180204090c0504380103020c0a0c050a120c09020d0e07030f0c060c030e04050406 75
    0x403030424401281b26600d480c80008003030306186000300c0341d0504903100b201581e10400090250465420841d1082c13500b01342807540302c0c8a8080001041d0700075850013080c80d42030a03400010550540c02c810301689040701e419440182018418401071103044000400e02c04440d801c1010501c01c2008200d0600350800341c070405074885050034684001034a5803004c08a0001d1132020382c0c40c202c0710b404500d4004540c0ca86114581d103d4003a60b0795447d0001070701c5159100c00e5420103d12202d0b1001d28642d0180c03083c00115550f050110300c59109118841c012420082008041506011000f500070700d4a000301040701c4441c01c08807801c4101d0b198071814558208401c0074114030401541d00250310601e4103421503410407050208051444e4030402d800c05030858a40d0019403407080780d82c16103070503410060300c41851a581c42c01070800403444d0350f0079009269020042c4150614090120b50240c1c3c070b01030005a407504112000b8041d5a009000624140c1c107003a407918094002a0300140580c4000c0391 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 262997140 1250 262995890 262995893
    0x2060906090414072c09160509041103040b07110d0c0c03080c030a0e01020706020a030809011d0706171501030b181801051f03020d06020d060b09041401150509010507 73
    0x2d5400b91001c84c0410200a42501209050105001c0c104010b07007103d5035000e4020086101d0720006010b4101170b40250f56200420740c40b90f0300384c40e1000342c02001800004000030701200e9981c8140e5082e11507605020006aa0138010070b01e8200c3c0c0400140200314510090f4811510114224001ca400300c0b2603007400004500250091321980003d0030140d540d410803000301134040101c03c0c440394155007008108005183d0040b0b00c1481043d01814900000d5861040c4140103010601c51007403240c503609003a81c238204000a03544251041511000103207441c1d0080050500b0081758501e11125a240355120503501c80d0304000b404200240c040d000ea980810102415840c1c215506442c200b00891603401c40300c000d00030250010101c0080b480114545140b07c6040562400081e0040040000b0fa0041085a904030340401c01402e500b00321075a214504a0665844840d80911850070100d1120090480c41c01840c101e0f600c0300310040c0c140611030400e40303081e00408403050610006109920 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 262998390 1250 262997140 262997171
    0xc06020d02030711100506010905040c110706021606081320090a0e010b15031605040305010c03020a0905010305150103180f05070611031215060c030c1b0607020609060904 75
    0x10b014100760b80b2044c40042c1c0e81c240c071354035045002802006817800c000034809180d03003140a8005403201646c02083c02070f99031f03409a07040314406503508013520500d0300000d0039550115000d48082d55040d1114101070760b03040d0840d0720000544e9007001000b90381d1418000030345d480400d070110010000758641892a010009421030900310742000409807620503100c3c40c1c030820b100711401068100d070b51004014210000e01268080141691070202143c0c0c185843c2d0760181c03042c0c0c0c000313607880b000902c4041161403005029410103028503000c03807604c0801040b10360080c010944103000115880c0909541e81c030044026050124001c0d04101040d2410004100080380c0c084085004070000c3c40524900440181365002021030039003660410b21010852113443c5d194141c20148290500c150017070100002001489002c0d102d0609100c00203545e4011352002c82c80030512076191806440070740b540010b014107440b0f01c06000350f0048007000700d4251442c010700079210401003e04005904c100140880 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 262999640 1250 262998390 262998397
    0x7060503241c06090b090d14090316031202010b0f010c030807230301150203030708010303110c0a0306050f060618090c13300b060108091f060609050301060302030c010c06020d02 78
    0x152a41d075110f013204000d202d540301000340c208021034000c4c01c2c00040c40000030400182c911503408008000103520206076802c01540300d00759440c030300003d45980d40740b0b008140049403103280409942400b00e4140280383c85080f04000c50b030107850f14047c078a120394080700e0301c0000034980c101740444620f260700e80e0a06100018900720310403003101da80f5414a510710110001d6884410b007154004c1080108c2035501107203041c1140e0341410950880400700f11000e003440c4918044036000f00303917aa8000180440c64101600840f1a10550140c94440300e0a22403144140c2030300c0001c6000d240e9100c0c0150410548065000d01c180d0340403814139075440106030680700b09078844c42d0070412114003d000000e44409031145501444040a64100b01da980e00030b5004009101ca07050090100008100607403c1c4038414001c010b606513001c580c407282d44400c0003070845000e24400100070766008201404c0501c10002629002001404403180e40c2004540890203107908844e85a0248a40b549511090014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 263000890 1250 262999640 262999643
    0x2120301090c090e04111002010b040c0807030b10020d0e01021905011b09050a0521010903110d0302040e0c0304020a1503050a0b060702090a1104050312070507060503241c 75
    0x480d10700400c2c240142049855000192038041c03901c24000045d24600c2c1940c805070742503414098040c502c1e90143c2c0100500705103250054200806015030784e030700107000c1d4032800040c0c17030800801d102d41b030030702905c0c0c031400b42e41d080036a01c01070015071410f025404440b2034800510464246044024a440d414006100c044946030b458440c3c1810f81c51000d100d000050b1060314258142070300e400001500030806d0300c2814000d03400c0402c0c000d0004d00304802c89141c05240c400030f100390b1882e4540101040030300b0000d081940546248115507a2080c02101d044541d0f10a188803140c030b42502240c0035900150041b0380c492541c010001d00daa00c40c5810346003640c1141c4002965140500e504402e4442001c44e003885038108000441c0160b40c1c3e402140d41000c4282400603811800b0705000c0740500c201d40205a05118001d11413468264a4008014492040c0288d620790303952900b065841e400280d65010742c01c01307040e49a00034501c1001103007021000041c400501d000b09512801200d4501110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 263002140 1250 263000890 263000909
    0xa0f051b01021c0c0305120906092a09130c0b040f090b0315060f12010f0b03030c070b0706020409020d0b030d0f091a04051804141f0c02120301 63
    0x820310035000000c40c40e94500982030010709032550321030031100940c8004080d03e0007809003190803101410300c80c0c020342c0c040e2840d1403108032550038007031900e568403141281c80151a110302400c0103600307080410500741c4190081600d80b40507003e5030410000c5403000307044640114004840c0800720b03425010a400500840410660340c03030400d40c42c031680d98160b82085801e2418010264000d13200000d07007140c0307999501e04138001a280c80740012201a92015910352201c184204001c0d5508107521080003513410705000c101c0203102205068a900030891114515005014100083c8a1050040c48500d04c25100140381c19110180801203800200300b802080b44e6841490032642000c010760818641d142c10305104001941600034a00b6090380206005118580898966502d00034183d801901000740b03800403200c01040503101160085030151070018030142241810400070400308010f1307160070b01c1086000c9010120b800030303201c0c611500c4214800d6000d12140102c940b00510f019112851 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 263003390 1250 263002140 263002153
    0x1b060f0a0e03130e070306050a08030408370305071b03052e1505040606020a0c0f0311040207020105090306040507060f05030c0703140d2307020c090a0e0a0f05 70
    0xc102204403454041580c007030354010016540420700c20300000741102d004018000141d5100e500890241899600140e048580520003080394603000c005001a118648101c4801200850ba4840091005108509080d002c212001d0244c0303450100828041d00030f080c144d15180550b544c50b501c0400d0191501d208403907185080c0304115040c8595411090140c03001603a0106040c18001861620410810502e584020308801040407128010080100030310400040d41d69160181d100e40c00740c54210b40304992030102003542041d90001c2410342c2c0d081200507140644001c1444020350141f00103905200e424403e244072035404111041c8214070400107070041601e46640030b072240f5542c00d11007046c00390510403c0400e181c2d01c0c082d00c800b80d805280400e60a0449030700d400251080c240248280313410499203000ba580046902d94444071207504460282d03582200480c1c40e01580c407901c60744000c6d0040800c51b802195000710380c01704001c0c03041d60100301d0555985818806200c80445940c0c0050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 263004640 1250 263003390 263003401
    0x20703171006200607030b0f04020f0d0605120d050702010c05012d02090d0b1314030a021b0904030c05120406120b150d0c02070b0a020115080d0e061b060f 68
    0x12100b11400310f51454592020440d000940c41d00c2e00203010008150b07032051190441c0d0342e0040200040c1c1000f500841d562405a41041c080340c0c010712034444011b0406c4000501b6041081d503403280e000c03842e00984040c41c02200215056440404141d04010110306104040707002803055000844426003083d0040c1c001380105143d00c9000a96403c41c00d20500040b030494031143c01403404182c4c01a1007042c950381d1080c0a042d50715001303201504210600c0c070450708032000000240300c07190054003141c0d400c11200d01210401141d040040c0d404c0070311600802c0003c0d0040c165449480d110310f080d0317802d040301d0026827802e54015501c1100020141400134100c1140da11500c00d01c02d20584102c404620740d210300a1441c8151908604859075840d490310714071748284040c2018040d104003c40d0781e1a10918000c2c0078180803120801030f003512000c005201d003000144a4200d40c90743d2640c0f000000c280b4108280754100c90014156012180800c02c09944140b29403407245000d600340c0002c42c2800b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 263005890 1250 263004640 263004647
    0x170c150901021011090105030a020f0c1f05070f050a020709020a1d0a060203041502251d1b1b032a0a05100923030414010819020703171006 61
    0x40180f2102a881d040000711141c801000729000301c0002e00709240d07070b40c90f0110080000d1051244180f807005003c545100c410901080b074503984100c5400f50400300a103880864221041901c0003000b288400520034071060013a805405c001134180152200c00340d4600640041c1e03402480c0744000141c1c40a110129032040c641a00c04582c42076034010141414a00080e41d42e20a901460019820211000c207006100b00b100340c01d100c2081d4850200301703510b001d02c0510411140610b000700d48106405805400416884502c18030005181c088400151030651800b80d01008005203101000500d5080f40002040241011b501c025034100d0384003041c20046d405c048006946000a4002e000c0d21170204000188860f0003c1c40038600180c1034040b442d0201860042d1640841e49507400c2d156001000780110151044850000e404250048600d00441d0402c0d000c03104500c0c8007804d0605036010660940c0034184081c46030401d60780c0e8441e4800698a9a001124941c0001c402010305011480d070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 263007140 1250 263005890 263005903
    0x603152d18030903030919030501060306020409050a29060d06080604030f0519120b04050a05040b010510050f0c07050307081c0503040b06100e0d060203040204150b0301170c15090102 80
    0x40c160255041c00388983c00640c0781c1c8030362408039102d0a40d461210f50724040503900d01d402180c0c81802000840e0317aa1500c9400394002d80710f030322010703468400065014171450003031401c024411452101b10003428043c407454003c002400341d4000d00140300036503503002988030740c00180441500404041c981440c00030544488201e148040103018000041000078214603580707180c0c42e5040620700c54a008905d1802440c40c0c0c00e083d03030b01c41c0c00d02060000d140115803101e400b89000712a1009240c3e22042800924016a40c0940010700100314140342c48010030301608c40710070100c05aa01c21640e80d000203140600540003004250440030f000030000c140441e541100104034108203081d4074007502e41408202c1c00900303141c041c1410300080c1c022948503d42ca02d9140d2402014449883c8290500300c0c0250421107049024914158502c16211540b4604ea070483e80000261451a03003442c8542c00c4040c110590302c6038610a116100540d95502101800c001540200305512440c2c0400020710304017 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 263008390 1250 263007140 263007181
    0x60302040b04210c0e040308060301020f0904020c0a051609050f010609031203060806180106050a080a140705090a091e0519240617060603152d 63
    0x184100400c008101111096030100c400f0748100389100c05a142d0001d038503031551040189414481d00c0042000107003086002d02544c040d54079914160346040606080740325101300f110b008481403203210458030b01500101030a14501c019144c0d41c000310354a441c0f80c845420001d180c190781105003803110789254412160300c032040c00c40b80d5040d5407514002400124403400701401d540411a8500400fa000f500007070001c1100800300c45562500b0900e550205001c484001260350071b01d2000106842c1241a0710292105c200107800c02c01069510840d1030124030480b00454041c4041c000780c155a4001007078881c15044502180024071454803886840b60889407150440030048214041800021a012042c0e01124034003861412800c0001d60390b11040850407000d8020803441101007501d801031001c99017010840315500d12500215622200100c03441905036020904070f0001001c046070444d0020108044111441080c052040790200101103101e150058102480300402c210390710521801d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 263009640 1250 263008390 263008397
    0x60c0207031a070e0909032a0f0703200a0e070e090a05040c03060c0905060d0b040b090f1501090518071803020108040b060307080307030309150501080a061d030d0e0706 74
    0x28940303d20060001600c01ea03a490090700c0030700000d410107804004a81c088407a624402074402c58600040002030060312446089000d41100303070800c124005400341c10789900211081e185980c4442d800d180fa800107110642c403001d04600029014110000700d13004812540d2406042da041c06c061103202c0402070141d004140c545020000401e00600e146800c7c1d95000c0d4011075100b40c1c001044596070082d411842d4484000228006100501e50020000703c1c03050b5418000342541030304011001c1ca084416402d000c040f100000c0e80d800b03009112000e40d00c0c05040401c2c105859030045100e803100056196442c1c0340d142c0901060075008210700751a20441e001c4204180e046a0009215460181006103030809500200302a031380c0c00c1c00040c2c0503203548030840b40c442502c8d04000f0302034102120103584540111008a1003c100e502641c1d050380c04031001800c0312440c555407038006000c289036041c02c140342c0c400340f0f50340002d040c001008000b0419402183d03414881c03e010741003040c02c0e80310f030060 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 263010890 1250 263009640 263009693
    0xb0a0f060519030b031b0306010602030307050403030c020420090906060315040f060e040c090c0c12081b0d02090901050d020108070c080c16060e0103090b130807060c020703 76
    0x1496400310864800a0114203402a02c010521007503018050206544d94540503000c03000529000340c031160088003800b103049601590ba56a4280e80324441900c00f4030010700c1c1008284042070107802d0310704825102500005041c410700c07241c22078030103241c20961200c080000f940704d00d902d000d100c20740d0010b07000c60780b0503d1800e00182101c01560030801050180780c95003090f0801c683c0550240300141241180800070b0b142901d030803c6004000d006210207603240130681081144901440c03900303180d10002c809081e0403000d80507641c0c071a0040c4002d50040b40d00c030070002201c1c90803024003051000b181015882e110744104002c0c40304c405030000c50161000d18140340c050707a4070000703061304607513a4107220703120051b90304229405d44110030401c0018410104c03000301254421600304126005a0340721a80c1d648144011001d40320620b001922503090080807e8071040746a0050001074841c01000e403400485945c0d9100741c0d41e480920320056000490104184940c24070707499800180000d03455036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 263012140 1250 263010890 263010899
    0x1203020f0705060d0f0603020d121b0209060402030c0d060311010f020c130b032802040e030a1d061c0608010b06120403030506040f0f0605100212030c090a050904060b0a0f 75
    0x250b0082e84c42d04030741c5035126012109420002e61203030018580152890041c0d60396401d101e5004199469108005a0000303c040d11600da030026168405900500941040c1c66480402000c0c0d00050200014407100300280710032002580310700710080d84506413064819104000240c105015405001d007590456046e05465690f400e5000302e100a00300000581003640d503002c645801c080010203d884110f005000540c01591260841d50a00c01c40d0280024400707116140d8580c01001d80000220314001d01448401152200340400503401408581c01c203901c664040343d007800f514500410090fa164000c0c410b030142070003030780025041070301c900746010314503590861440f1703008002904140e55100401d46503a1940c0041c29001e4a092003440090040c03c514402006a4840e4a104080c038015a480b603d00108056010404400e01b03503082d030343e54a010a040c1e0f440900420b80c000c6c00580b001c100703a942d2000c1d140c000d44c059080000c195083c4002c0c45900b400507080140a014890320422 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 263013390 1250 263012140 263012149
    0x804021201110f0f120705030a0c03020705031b0c1804050c03030712030b0303070c0e0f010e06010c0b04020d02060309030d0f14041101090302090a020c0111190804050a05071203020f0705 82
    0x8500c52219040f0b2a9211002d04c010038040c010752144182010462081c800400ea20030090b5004604c0b0203030030000c1ca481c503041a822840782c0c882c000c096800a104400c40340c503c10340048500420b0f90140e13800384550380300040100294680300e2604440000500060040c2080a8844c80c40d003500207510344400c0d40c0398844103903a80042c1380304064a50300517031081c4c0c405100f520301c21a88400f150820988525900341e9440003140c0d40c02401001500000d050100e040c138150090106844050020000343c68580582c5401003042c3c0e0003100a4015900580f650401180316210301000f442c0c5905250380d10009481b0640100503c1604202410159081002885410691043c288803929012000513a44542d8990020303500041280030481802e070103400420820406100030055000c60f42415181c42c010741908032960081c610440800f180110080c0d030300140180c040f43c075884c00c1c6580e114503003200b03900049583d410b925140c1042680410000d03129900140142134141e08000108 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 263014640 1250 263013390 263013397
    0x3023129041107120e09010306091103060f0118020408030a0e150a2a061406040b1f0507031b120f08191805030f04030201081003030e041505040903080402120111 71
    0x703000181c403909400d0189010f81e6081545c1031010b04075000715030752400c1000c02854183c00903507104076204e0b05d00f0000d14020038001e10420000c0c0101045900f4030800c44440d900031000e50b1422a403c12004c60216410005007054034015542d48070010105401d110002d1003aa410142044083c49440d6040d0381010703416501030031941c0e076989504120100e103040514183c8000d0551458980184500304072105020704c540000c0d942801400d46079400e04c00710901034141d00f000704a000d400020194801c030014079409009140101c0000b0403004401a5035002e80700483c1c2200e40d900d9100006500030954210b2001a410078011600c0c16003001c0d0401e000c41c00300403200035035480742d080716040d81e00d10710721030300741c010046949400d0307641c00310300695120740410f07400b00c0d035400000f41904000d6018502500c0c0d1647c0c90602200c070000074000501111504645980300c0343d40e021603181c80e0351048501090199903820050f003454018004012521f004003149a4144103c003203800c01c10390205c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 263015890 1250 263014640 263014643
    0x403140f060f070f090b160302010c0207030c090c091d0712090302030910090b04060e0307080a170d0f020705010f0c02010209100c05030705031b1603023129041107 72
    0x20f965040a41002c64941070207401006c0300704808104001401c0a2541e000040c91081e002040501c04484c2d090b0380d2000c20740710051003a4000c14003449280e0158210742051661400e0483d269600c9942e04591801040000a1444008030401c01c910307611903c2c10302d070002d68480c1004404d210b501c0080d26803244d154001d0103600c4021610f14001d128940003402030588203080c54030782d61148001001498584042071003481480f20203c0e85000c0460320150896129007189a00c4540340725503400e90300444105618181d96048044032000c5900090065920900c000070711202088400310450745000505000c6a01c180400849521288001d605007441420240040c2480b45070113481c40c803410070014400d010215003d481040b1103048070030522001e000340e541c004034481501c1260061488040d500c441c9600303030b0221001152000c0070010303c0541029104000034222417050302d4424499030181640c190440d009002c010a141c004680101c60502100301d282c0818881c60184010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 263017140 1250 263015890 263015897
    0x5070f060e0f1f021e0d080708090a021306090c0801050f0d020303130906150f020303010510030e0a030905011710140109080a0302060402090f060a0b0a0c02060403140f060f07 77
    0xd500000e56100c80e0700340c245406102d030b59801403c1c2020025140c0049080c02030642c04035140758403a80e01d01190b9180315240580d80c1000707581e43c00401300c034141d40141204e0b520b070040014110250f1105580c520b58001104004101c0310314018041d0700719080704c503c480070005408014080f940d5907160030980c1c80c1045031502001c0b442400020f0641c0b040d40501151282c000a00150030b66060700180700302c8200401a102c403070303004041038910b0610300381a100140c02c200014002031610100516466030540750000d1000844040d031440c091000d0300950105d83d813403008110644e88810300480c5001182c00194550070000d20f204c00d1140079018070040c05061158440749a4401e40c0300038014041f5404541442c40b2038100039444503c2030301c003640908940c2c40000c0d001802041105e02070300020306640d503840e2414221440315000b072800f2104000005203001d016945000c0039001441c0288541005852030315075030780c0792148201004205401217405c00c0400c43e102c10043c0d900000c03608 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 263018390 1250 263017140 263017159
    0x150207030e040f060b07050703030813050a060504030e0409062901080415020c0a060b10030911090a0e030a0305100501140a0503040c0b0d0b042a0518061605070f060e 73
    0x1141c28001e0000c070742080c17045a101041c09411b0150001c2e002e0210f1380241c0b503000c0d1544640c101d51085220121010f055903010340b06010000703e1607809158464060b07c0d00111652105001405079405c000050343d26a07200c1255400c60100021030f18110341090034448041c1440c0703800607181e244002d1000c0e0516003e10f03800f001218090b0112403400b007081c819140414200d19090b4001c110658140d4000e407600c04c2e41d945442c2c041d1160605454120750000c2d0000e003610704020076500014001000b407074451188851131001040944604901071301d0110340c0d85044c0c0e1100021980e070f03501c6103041103500400c8a0200400004940302c0409600d0072940c3d964950801d201e800600e5801130100da600007602580c85012903201c800c04c2c0100b16028040301c2d82d0792007496650303401003010600c40c0100c02c0b240345865002d48010100074040d1681003c64180c0000002c0840e04003401800180c03113250400d604100050041101038208071160070b01c800e007880b40081031004150000c600404824 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 263019640 1250 263018390 263018411
    0x402090709080a110a03060e03120109090c0b0a11030301061115040c0506070c0e01030308071e080a09050115030c0503100e03090f040212010902130b04140420030106030207150207030e04 82
    0x14901707240510380000341400303070680c1ca9200e10340c0e07540841c042d4440c0c2c3c8098000403400710820700a0581039a049225250181e00b0228001005c0e0300c821085010b002010001e001c1100c001e001541c000d2a483d100c00400d220703011038481c28101c14a0f040101c8808400030403000540380d600500a9410071b60f891a00c44440d4a0110601c04040c1c0180f00c82d100d03042d000004255102241c4d900c220860741d11031203494032084040c0e0701c002d00c10a5100105000100040e9025172b1980100b80d0700d4041c00010a140900b0202c0700d0061145800542d4a4607a41c502804142010040161091084002001141c80030641942c0780d0041c070700624031074900e041c0030742960b5540b070701594940090208411002e50303440c01000c0c025403002040b848544801500001c90790400d40a507400c0350241005480c40301d00c18400c1000522526030b02c0704481c1e65030b8100d80040340c27980007e103028180c16100166a428141415400b8101d4464a910b00714010024000042da01c4003440e081d121058602045d0f86908 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 263020890 1250 263019640 263019649
    0x3070e04081303050106060912020d02060319020423060a17190c0c061d060c0f040b0414210307021002010204080d03060f0905060d0b100e0f0402090709080a11 70
    0xc2c0c00080c000e07800b05150101c01c4c0041903000a0803181c081e2903205096a40e580e080c9031064035803a0103544072803402402030143c2003c1000319807020409080d08560b20504541d0742c104d80190300008910210140b41c1c41850943d07500f40d00180b401160b8007410000202001804c00c80c890742c8201a580d00030b0041000c802c0e08043e0101d0615003140180940d40030108010005010b00e0416a010f504000729600800800713182c4500803042a00907081c5551000d2122280d40d0202951040748402080000f50054412015101410500c03800b960078018940410264011907030b90384a10320303540032508480040c004101c1d000581d0559401c100e0700304501c4141c1c0280960b030b0149880d40100f00c0c800903104d50680c40001624800809807075041c3c0c8030070780442125411100303660050864012a4049900d0b22003281e404029099441c02003071300c0d428014a84801503420051b44c80341e00007807208503e40320312920340c80b24a9140c140c0e44c80340f506106039070f1b6400d81c000c00b820b0784000038182c41d02c81d00c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 263022140 1250 263020890 263020897
    0x40506180310061d0a02040b0d0914060702070603061a03041509061802031605010206191803080105040e06040b070f0306210c0f05060906030a0b12010e0111070203070e0408 76
    0xb40441c00c000761941c5196454213a1003003042e04549100c5440002c640303071420320a0b03d05a5010f5542c050400c00b03d0101080140035002040d03403402609690503465840c20014288625082d601070071142c0c1c0740100143c2910800d410280040058200725a440003072401600e6000ea0010720b10f000c218560400000142000c4034040c010074104849800041500010504e100d803081c0d0840b8400c000505003001c015400c2d0282c58010b0704444007165a013041042a10405541000300040110618001d0020403603046030490100d082030f40100308a140c10310800c060958250b0240240d80740c40d5980d482104402881941400a1112803e0315103100fa0720003805450204d0240c6204034601c41494010562184103c41b01c00d15640003041c0038040300000d008441c8040d000f64144a100401c009441e040240701c4c00303101c0d030384025203c038655940b000b180544540380000030301c3d011481c510034255140171a800560403420800c0c0001038400244000c00c0300c0f000702c141d55168484c1c0c0b604221510 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 263023390 1250 263022140 263022163
    0xc08060124032403030201050105031207020d0201211a100503040f0305030a09060216020909120316030b100309030908010603030912031e09060f080601020d0815060408010b150405061803 82
    0x203c64200220030503405500182c142c07102107048560603494480f0003241481200380003500880c40300c8001c40154060303c40301d413000d414260038030280103010070844200d0340642c2020080e4580d8104840380e50804844001100400e49841803541c900354031a00ca0a5002050003030400c0700010005007071034199031100f08000d40c0700343d0035551070300354400b182e048000c1038030207070310513205c0801040c402c3c04c00049400e0b80000c0860060304541c1d0303114210ba890300300d083e005420b050302d41b031026640d42d4801c0810030710702e001a00c0c00a07580c10b00f0304000b008940360341c002040e00d80c509003040c000329410400007011034008880000090f201440c0c200c98451844940e448030541024650031b10300d0704440305909031003496468482d0070318079040c00c80300f0726800e0303c04501580100181c223802c0c0d0b01c20a002c40c0d1260312440c080b81c401f8401400f084940d402503101c10460395580c030a01e004c0c1e16240c842543c40083c202e8203903050604100c00a0740500c43c030b00408250031513080f2641d0700c98a09002968211 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 263024640 1250 263023390 263023451
    0x2509050a060504052119031704050a0302070b03010f1226030f0c07030e04090c0305120a021209010f210906050603060a110d0c020a06090c0806012403 66
    0x281d6141c0e00034081e50000e0141d00d210f1549505d0184011480714201c902d004501e000411280060900b00b10440408000541c204100040b81c1c1100e082c7c40041c9a014034864001407460303400d6414000c0c01c0c101140c0248441c094100f004100e5401000c640c0804e80c0d1404000d880000d0151812203806002010000404030004803001e11f80100c290203184609a401c118611544c2e4052200e280c1d44600b82004010846030301c004021410950b0050061a20446000707a00545946840345825000b1590a080c11b10010303502c100d495060011201588000a59a0408038030340c0021700f202000040c144100807600c43d011180020303480d0503c0c2d080400f0075041151500b14200308000e04402c90f201402489000e01040d52800c440c800d0750940d0172401e83e0241010b15200025014141c010300c1c1a086101304649000850340d140308560041d0301c07445500d0f90140c90f15032801e0500300140d004140ba0030910203001081c0310320411310f0540329028a00005e00c044606a6079840d007032030020300e4044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 263025890 1250 263024640 263024659
    0x1902130b030103030f0503130809030309030709021308300f0c0a030f020a0f11030a0209090307120504270615020d140f0906070503160b010e0708250905 67
    0xe52850004606882c002d540700164241c41c4001600c40e80b006440b000182d441c074030842008030350f4030340140c07184160090640b4070348131880c00004c0c03400c20142c2049584603400190104a00c0841c8842401099244054410060b030b00c2c194507641440203200c0311145210070041e11448106008580c44003400030003280c0c454242c2d51009035160400001140841c070403c000a041034000550010001e034401d2820035428202d03524900c4215841d060b480c0c043c424080306d0380040e6101100c0074440c684030b000854451040e4200070f00500c140a40040c20302408000510144916005030320400040c11007004a44074074035991030040c1b4156000103001e010b000ca082920580c0401e68650b030035500d070349000c101108043c8410081c400c505075400d1403c402c1002e421181041d030060f240035805070056a0408a8580b110301c074000c412402240e1107201ea0b0300610040b00c1c00d8001e5a001021440d1001c070700e16003070140311454070000520070924217254448240795445991144080c000c0079055007403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 263027140 1250 263025890 263025899
    0x729070206060306180c010c0201050d1404110a030519050a020a090f05070e060403020f0d060e06070f0f27030c151103090102070612110414090906040b190213 70
    0x100c1d81c0e41681c1942c401c0c0928008911968100f0300c41c5110b82421101520700007405000540d5180792000d0200d06004040c411400d8003156445046070701115805140e10b82d1800741391035500c0441030010a44582e003042000d001040d40020340341c851403e41100c404500b2801c2c00c206280200030600290311010036000810900e00c0c503000002d441c080c1d0758003030050b0344440320151801c80700e0000280d04202c3c140300420140c600b80301c44400700740c1e001c1c1906400810701e440f40e00a031074801c4941e07815941f100041c001107a030f00003e540d000184515180396865142d480040400403a003103415201400c8803429581a18000780f45001940c0c4403040281e131503075402141200d0030b0000c00c480c1c04250045040d03c61380102104960400394160f024141250070290203a50381c0d03041c495045145c0e030359442a564080d110314003d1019000000a0070701c0043d16a0402038400c2c40144030b181107801101c244000a80000c50341604000b4804940c0340241c814840400280a81d03800da40100004000008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 263028390 1250 263027140 263027143
    0x16020603130209102d0b0705033109020c1f050114090f161110050103060506060723160e010501110a050c01030f06150327030507290702 60
    0x122202d01c266a402e460341e0383c80361a01d00705013072407060030504800600e0442d010307845450040c0d180103c1081402d80c5544840a1240c10740028408581d540d000213241040c2c80c00d24503886aa00c0710300c012003501c000104d102e1014090091180644031138002c158403140c01014814079003100440e45150300861860301250f40903080a100350925805207901c81d02030703414031030102c030300c20000403000144c6500c42e0200d030b21460b20032903031110070882081610000180f09001d2446c1d03241a9a0010526505600b0314204803000544030920803d82005450006610f00503c01041e02c6080000640500e00c59581414004032421111341c600c90501e02103500d000d201c91080c10f0f40d10070b986040007a215600715035500c1c000e0103005441a8480d07500984550310a400101d0081c0d103007a8046001540c031079010b10740240609001d00403d40b41c2007091300d03030140d600c204501e01e4209050742c06010f486031805042881100c00c00392000d001103c007084e00e24601e10a00100c0764500710610914902044000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 263029640 1250 263028390 263028421
    0x123f0903051501170705061819230a06020c1002030405040608060a0609090510051e0702010e0607180b03180a030903030206090304050a0e07200c0109090c080c16020603 74
    0xc450380a0100141c44a8130300020b40605449010300094981904e542c40d1100c1080c41c060b0b0154082da8006c100e5214034203082c44a03000b004480003c19508808a0000c9042d0311110451809440c0700a8104010399000500300004c902c10303551901c604020910803070452081d900003a81150070500c0002d1052400243c41c1d120301a0b01c4001c006494481c42000f064510741400604030741e002d85d0160b60000f0180d840079401401009007100d841d01803407020140214204d60040160750349008174103030f0b410140003950b4845d01d035140814440e0b58440c451400000c580c0540e2248040102c00074a1520741c6c108880e100039506411212121500e141c001c1c400a00c2e40421001401604007040362444004180d506440000b803e44181c039081c40110310309094001c0c900c0c0108540e00e0300404000462100352002e8501a0b0040c0c10252040000507014881c01d60003a00782901c3c1c600c0311000700342e00a50440c0c001810001c52a580c0780d40300e0141d138031030342c003228007035071004001090000e46c60b4015141e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 263030890 1250 263029640 263029649
    0x2070521070308010f0b0f130e040f050f06010303080c0d0609090b0405160e010501080a0f0f1d4312170c0606090a02040f123f0903051501 61
    0x2110f0881c0e072113580321640d010180c45100c00c0ca131030134015000c644200c81c0c05001044015002e000e0401d9460f124040e02c039030700355829a10f00751110076003014000103100014004a440004010552656a00a20040d401011031004400c00704002e5082c803a40e401034401482044400c0c40814581e01301b0311445030040d42c017141c491148542004c18050204002004c882e114010000182e10340001500c920f08000c01e078072210b030340c0d4a50316014441c03584500e01004050b26800140048014888503561641c0340c4400d0250380483d004001e00c000034400d1114154403072001d402c405030104080c81c00c82c0c0042481002d40e406c105800b09400d503400c490114100c0c095184842581c2000b48850b8162140105a40064200c980010020b040a9803110380140008030018070301030b43d070b91031030200303544a402107643c240300e03c035880c002e02002665203040c007900010300e084d92443c015280071450003114aa041050350003042c0c050002d0040c1c004400554104040d1802c4801f42c1681c5141c01100f40513 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 263032140 1250 263030890 263030897
    0x20c190b010f061107030f020a05061207090803090d200306040b070f1707140c1506130216030f020304180509070905090709020913060b03070807030c0f03020705210703 74
    0x2400641c2c1ea2080d5104d00c2404002d0000e0064039045440e1710241004600042e03802c10000f00d0b0005581e01c80300700802812141048460050a1031b50380280007040079030080340380754800d03c55400c0b96600c08101c5640c0661001c0317011141c070503500314690000e00f000d2100e90f05014950400003408980b102e2144142425a22484020041d0000307407442800c401100700c00485000000d50320701e01900c034817080920080316241c10049030002c20342c500344402a10803d0b0000b20320600c1403038200f0100c0001c106800590a40c10854281e51891b005071200e04068200304038240c44445041c024011035025001082c4000e000c204a40c0300e42000d030070203488c90302c02480341d006c0000f0825a0780c42028054100768003d492482d1909203484042d4022100c41d5a01207011018201c0481c047c0c0b0542d002032561809913912454011000360100f03800410742424181000b010030041a40039082d05120100c81c02c0041e26903ca03414554540310140c441c0744d020030b40ba00742000e24400382030050481c0c68400d58 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 263033390 1250 263032140 263032169
    0x913060c0203030106033918062a02061207050705010525031e090201020f03030718120503040e09100c020f010c02070e150102100213090c0302030712020c190b01 71
    0x401f8140401100c1882da9160ba4040d036407071140c0303405122545e880c5400c1c98020500c50f5000c20341c0d804001d1aa0042000c204090441c008000c4408190007400940156007940000545c010461324410700c07004403580c0d9005800244510300440544010b02d8000300200154038103115003404c001203e0445405280ca0a03042003400c0e403081c0600621030321240c002c03c065040000180300030382030070320b81241507009242c583e000080d01040038611a981071381c0d40b081a40c1e8522040c1660704020f412001c42c052a0b07409039030104900100703c3d811169880025115556080141c50600025003466010507013401038900300c0950000341d201d94240c0c0c000007082920140300050707940c0c01c203d00c5508e4a44100c100003a4a42d12210340a9422480600550b100f00ca0050444070482c0d1209d03014100c1000b0b42007007801500344500c20b0341208003007420214510701300311001802d0000c0d81b540d04110b2a030002040c00000c6030a1040f8119101c40b100c907901d1084242c545070202c9002402021030300300e0240e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 263034640 1250 263033390 263033411
    0xf1b060402120c0f0103151e050f030a03080f0c0f03102d0302090a11030f0a0605010804150f18030e040509010605060a2706020109060b0406050f0913060c020303010603 74
    0x100f000c800c1c40300700038000240c0044910040d0090011075010000d02140740100180788002c80e40d10311060090f450002d940c25003407000700003490000049890080c0d004015410000b6040840c4540207072103041c52130340c950342c0d0030f2200c81380c0d100c0d80350740742234030346010080c807402006803000907050b181b8151400015040340d030a002c0d04200c3c00ca000355060801544c04001600340307032003519004030300144040b41313140d502d184a500e1507100345c1d004110720150700b08000c24200d051040801030a02403804960500341074030f0b125a044201030100c1e0306107a843c0d2035254844907030740c02080400702c00a1860300040c0300f400d02400f0001000703140740c0102e003400c001840c48401071081c0760a603440144214200b108241044a0704c008800c1080d8030118803210800c480712400f4000d00083c00c0d558008240316005150070802e60340f0315402113000f141031134400d1005594000070220411400d07107451140d5914080c0d00410a100090042c051524218074584000c3c0c0c0400254181c4000352014007607075081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 263035890 1250 263034640 263034643
    0x1f0b0d080c0607300b06130303080a110d050601230703090806010b0703050d020d1404060c020f070b090402070b130b01081506040c0e0a0f0807060507050705060f1b06040212 76
    0x1c0829514130300854860804065410400020142c0c400c03001640c41400c002003406030b80030411000d40030750351000400800d5031102817660310040d041410300140c0203102442c0850b000d500c80e4602496160340010360b69921412001603801d244421545610b45441100201075200d000d060300040c805030b074040344c1c12400146650480d078241044618208144c1ca04581d00e0700042c40c0c04c003010b0780030080d110401c1c55500885030010610741030101103083ca841d16000702c074160780400701035400140e14094013880100300072040750400c2d000b03150f9481d1140000b034000c3c402c92078004d0450350440b041c0a000400090380e604818407449071010f0326600c80c03100701c2e81c2b660040202c00e8880464000a0201d050a801591041800342000940512798500043c201c0400d42c01c000c4410078419420094640c0400400c0000c02182c100145000d401d030b2101034030f86c030480c080d2ba80a42c8000030701c4280c8102d00c83c00c0714814059244c009110440c1c0c1000d80361241420b403803d0388039241d0b504102112080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 263037140 1250 263035890 263035907
    0x3060f0d0507030b1003060603150f14160c0501050c0703090608090a06020d0b06181011061f0b030a090c0905010b0d0b060d0911030106080703051f0b0d080c0607 71
    0x1008801448032030f2a40da114403401400030040c83c001c040210000000903428002c04e070140d44290151519a40078800c0041100c400c0c07085020f1031420100d8442806400c103840e11340040b02c071480d5054a84542e0016a0b05940d010030041c041e40c600000c2020040d81070000c0d0030014402c0e554405000c1e6240012220000700341d6585100d9046030040780002503da0b4000d199400c0401808110040703080d00041141e040003402c40002182c1c102002030728500313807105802e032000c1410441280d0710b40914495480034001e00740c1d20030841090303501e80c482a140454000814603242d64580d41e1620305d460101030864108100e64011452201145106071030003464141e412081d101414292880880300140c407800034941c1e00180100510b042810b958040d000c3d0090003074021100c02ca010302c0616084900591102070103030007862060000500209507981c00e4035140d0b002d0030320000d451500e08003c100203042d456010821014020030030140c0809095a81c0354101542d5603a52580000d4030030f01e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 263038390 1250 263037140 263037143
    0x1506081510021005060a031e140f070e0a02070b010305031308030901080a020d06030804060c0b091209091f060306080d080c090d03030207291303021515030a030503060f0d 75
    0x20824000040703d032449904c203540c40140105042c0c1780e60307626101c11001c20a2140c1e171543c05042d00e070005050003540d130380e80d11303880c50b0703500040c8090110220003035111881030040d400c11490200209410300450b07019954100e0300b0000300710707045d40d42e46440355a96003d080b2022a03807250520001d0203000c04030a94044080c10703102e003d20341c5d440225081c001d40c040c404000c0e11036074a81c40030003c6103290020f0710141581e0746070401d0140301d030304008404200040500300d00d80d101c8046190005001015a481c10750306031a094020788410b6420b2180340040e010500508200b071600003015a0725800400803614500251281004038040450f99502c04480b440075034030042000c00514244600100b00343c6019181c010f04103095a81d0b461070600f846500d0b101100b0080e014030b19007d140024a680042207500000b410303100c590740c0651605402a00b49034030303044000002da0000c0341c1c03d440301d460001c000d0948400030410f2a000d0100e410a6420134003989a04000d031b010f1307091180c92440c116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 263039640 1250 263038390 263038393
    0x50301030c03030503070c0605151203090a14030f03030f040311010b10050a11072d030f060902010905130525140c0f070806040506060405061c02010201150608151002 73
    0x40c2c1942c80544059202800810030051070142d0f08010600d50310a05000d14010402c1c0c2500c03010920412180c1c9003150040d079aa230b00f04101510741a6601c03000d000488500500c000040c07813035140028104464240131790302c140400001c0010719880c0528941c070652281c0c03a405407440e0320b80255422140c1030901103400502007820310820600031405404401c0342460004403011000c1d440b203090441f9584801440c050190031110302d51440d060400c10030752182074401c4146c0c995168846540d10b0341c031000d0100c1c5d64549001c03065900c60304007540580000b03484c7c21a00b10040020000030a0111440300000d41c070001c11054001450307040c818140c61954036074072100140705281c0a150f2201384a1001d610407018181030145052046200914680c0042c110601c3c0030304209013800802809544070328031301030070014242d480440c0c8410800489101c86070111341440141d006040e8494800c00002c0116800958561302020040c45030101c003494111218481d818008958981d6401e840075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 263040890 1250 263039640 263039663
    0xf1b130216020111010e0703050a0b1b0403060c05040f0e190b032a12031c0219030b0301090b10170d0e10020c1f080618070c020f13140705030103 64
    0x90341c1320310380000e0007040d10000001d100b0f11014820745001c41d1644202d905822451012042c0040d40c10303c107510458040d202d140ca00d80b40382e0840b509219a000040000b0b07501d150710f0a8180c440c8041e940901403580312101d041e9180c502c100c415250859103104504120406080303a640355000382185494040c2c002d084100140c14100ca14400721101c1e417101e100e0844000d001962600d8011401c1e40c00305c0050f55483e4500d086c0c03143c00108a1103004100d5004003d86202e605250700112201182d030301d00051a80f0004000034050008500c018051030300038014085201100e10fa8001214088050154448004440b29407200c4d0f011000170f000c6070190004c141641480c030f440c1c240302d002030b205031101c642040c1d0020344a030004814044503a5a440c00340d0320000d410045868010b00201c0c3c00c4500700540c84080c200c400700041c0312404100b0104040001c46d150f101e82403ea0500c000c041d05801e40310310380d40d00014098a051200201110700205460710b0203041203034103032900505d0341e420 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 263042140 1250 263040890 263040893
    0x3060e0d090614090a0605090901060906020709021b070303050d200702042f07140a120e0607060207050109050d08040f020d08070524061207050f030f1b130216 70
    0x2000c00c3c60784043d070020075040008681c10f960b018070481c05050781c0c3e1a4980c50b80510018081e020030143c004405115854900340304080d00000c1900854001c43c90245c0d940800d084c0740c401c5807210320045030f01803054990200c105500103000e0841d440c40107504120f541c15001c0390700800548a1004022502d04200d2000907042a0b04100400240040c044a0340b040b8050024144540790752455509079000c24480200002140340b843c07030b20400c1000342200c4c1c1c10b82d03d4420710105143c007080f040c0031800c0084580d40d00e62074251071a003600001c04540300c0006050180c060158444102c80c680544204150064041c0120900a6070494060314081c400f650a01c200c0709580242691149018030402002490800c245d081f66810010840e011392094100d07603c0844000e01140d104042100d030301021480c0c0003914008855046034424050304101d00428108424000c94078118051080c0c50f20f080d0140c41581d401c40b00c1d098600c0807100c1e0100704400300328041c68403d40e000000402c560030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 263043390 1250 263042140 263042147
    0xe070317040608151f050d1107050c0d14031c0606110714060f1606050106030b010e044a03160204150b0310060e06030103030f261003060e0d0906 64
    0x3899000043c00445c80c402c400d41c440840501d001514000141c0c0009550600400c07501840d0284401208180c0c1020010364031a901c0d00501441035010300116140340d82809074000300d4510f0107051406403540c03000c2c20513076000c02840b181400d0b04441d041c940c0008800340304110300024442c9520140c0b50310390400301c0c3c240c0d26419200134194403102c1444450003072002c103401007802c1b02d201c035100a02840d25141c0b4200b9204143d102005144c5413445203490760740c11004151400c40100c50005008100c0c851803003402014044410350300d445481c02c80044403044051082c0c100c01c41c1c1e0a998000b030031442d0301d652031003500300105001e01050744003401400c0c01d07007040301e00c00c8080ca04c20410341d858100c080c4080e041103a03100840b900180c800c2100076000080443c0045040e00c4c80303451507065032800340100c10780c0c62004040101c0703c1808010f41889110fa840440b400660101d8a03003011480c04088801b02d01007501ca692038800c03c012090790014a8000d1510591903481c103152821005a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 263044640 1250 263043390 263043421
    0x5061b0a0f110616031505011e020a120206040b0f1905060d0f030f03060b030103262107121a090603010e0102030f040b18030403080714010e070317040608 68
    0x1409110105038202d16a207414030000b449000001c0780003040c240c44280041c103581164a41d206071645140082c0500d0b41e01a4820203916030301c4201442120001d4022881c2905005014051001070186070440c0c0d079011800501447c040c400240103512414602081e9103400e4910091810340d12001940600c0c06411080d84448001c01a031209151394031a12144150000120006103a4500b0801003e405110305005882a843d5480c119070665031a129000540d09654000380340c03004240c0682200c030421220500c80c01c1c000300b0802400185c103008950001d666820100764019241c0c2d20752401d6200320900624090b001c1c02c80f8000308014130072402400703440700c0d4055480b1514818804000d00096001e0585d080440c4081e1901d81403510350102c010b40482c490442c0e01c002142ca401d4000261070a40f070f0000e1806587d404d45140c070015414645c05d03840d00c0c950824040040d05040407034400704480c0120a181c0182040703000d00d00152066000d0000400c6116003c0752480040b100340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 263045890 1250 263044640 263044667
    0x2010c031709010504050115030c03020402030408041e05010e011106070e0112061403060a020a05121f0305031c0b15030628080f0109030e06031003060c030905061b0a 73
    0x10807510740c40c0915030300c1003202124030848607034440040c030080000c01d02c680c161705226461040385103420740d981d0a06824031448064403c607004004a014032103030108980040001e0000310340400c14107506050a01624030801c0d01003490650900143c0d401060580002e42114001d81210307550384000340c40078050300c00c2550401c1104c0400e190604001d00c5040c000e01b01c0b084903e00110694001c06140041c014142002e1074014029001425004029251103010300c511303141c2d1603620816813108445c04c3d0119000c0481c0640c1000060100120082c10803520520007030086004076440d00c2c0030f40352640c848941042c1042040c288540003080650b0f0480c0c00240b12243c0041d62030b9900ca03c00420030300d40301d84410b08070b004102c0e00740c0c01c0040045074860f0b00c00a220051103614050b15090078601002d009440001c005001240150004005540d204a0411900ba0181801401040a807a0032201480b600000c03072001000c00c0341d0700c140c0c0000f44001c90b1800c1c005890807189071500078130 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 263047140 1250 263045890 263045897
    0x7031e030b090c040e01120308010e070c0501290a080c0d14070303170f0c0f0307050c0601060201060f08010e0c0103090804030b070c21020a11060c010906150e1302010c03 75
    0x1d61455950306524103005400801402e612203081003901480d0b2035041e40321840c0402e20006020000790004140b50441d00716048034001903490350010b030b443c0d0358640300060880d403030890181c0c00c11701c1a02c910100340300c00881c1d20341e07a001d44400380808442280200340c140da01403c144125072400c406803120340342c4282c4510150404401140c3c0c80c202c4180c00480100d409595a895031550601813030f58040030000641c60715007405a05c018146c8207201c0d0301030450300004000f42c01680607408489100b0208000c459486da0359400c020700030f14590061490100c4107080018041d00140100904030812102510b070405d0300300015001031600d1001229041000c3c040000880c12007c1002d2081406072101141c020192801d000c106030a0a00004c43c1d851418812202e0399002845403813850b0300290792000d002c5500000340040c02000c0f44402e072582011240f10801401c0d4200400c0ca202109030388a40a171680c22000204100701c444403520210709110038059032191100c1c00810340a4203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 263048390 1250 263047140 263047151
    0x2a05091e04050f011b090509061203031911040806010e130f030f0206070302040e04020d0c0906121103030408060a05040c1203051b01050c0f0c01020d0e0703030905040207031e03 78
    0x24000061040071102503034960032041441c91054402c0c0075100010090051001c0d2060300c1c0c3d480601a01043d005580c001e1301121700141258444143e81c418101e00d2900301c030384038030348418548245a96010840f05c0d00b03041c0b00c0010744104000094600b507800e80d0700500840da08001186242860003490f4945d89a018a4024080740342c040319045000e0003507a0340e004c1c0d910703812000703468007201078405000c0600c1003004110714012031310041e802aa040340c2085002e007403805d2100303001d40c803500b01d00813071447c00d4030009085201803c11000d5520660b6000b9107030140c5000c143d264066845181c850783c00610005a0f00311241d440554060320a62400d40c1d4151580301810317810b07026070012000308500081c04100000f0005d03100c424924500300a03c0185020850b4514600901000d050200408074068022101c20f4042c0c44455000900401c20034500d194101c0e030f2790201c5d110540106e040e40c0710100742410103000b00d4100031382680b00c0c0104403443d560201d03007882d6000c107108201a541c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 263049640 1250 263048390 263048431
    0x3091e0330110c0f0f010c0201030908131a040e0c0a03110403081b0a0c1406040806070215070914010c020303210a0614360f01032a0509 60
    0x107205007144480e030340d8071060100c0da140304502c2c00d101c0446040c0f144c0700354034681086545204032802d9504d020710740b08500e548144010f0b400b925884100820088001c82c2c2c88080070b80151704082140c1075034407420340e14042803400151078415402280c0941100c0c60000715001c40300c000502c0f100700300e031500003054681c1182c44022500603800c100e40040700010103c04242c0e4900d00c44811401003001b401c1405201c0d5110008400c9074842e01c004002030403a00040c0b07036241c1084da00249036650070342c1c00c58501400001d450f596466942c0710310f000f0803400b24610798850804802615054030000320381360022030040d500300c00a110101d0b49803004225884594500502d4000210480e0f110b07a070031030900314108800d0790488d4201401061500c0c40c400001d41d502d40c40070800549240c5540c00e4a4458030881c0c441c800b035501c54507140f000f840180300401028948a50403070b4003580001b0340480c45805048140f5210b0048410000360b6900188524a0420021078016100880a0f800407101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 263050890 1250 263049640 263049713
    0x20d1106070f120f020f0714120708010e0f070f12061b080103051009020307030b06030316030c0c050a0e0a05090f0f0106050f09040b190605060d0903091e03 69
    0x150104840030000c0c07003d618260354029588120400d00790000d403807088091607410365110752034442c004100e070300001d0f078440c0e03500c4072660b0101b01607051040e0b41c04280c543e501a40604100c0144070428410520b10131000030000c1585000e81e039148034040c402a01d424020321680c500c080701030381d0700e9641d545c85152103640303000c1103840610701d40c40d1440c0075032550a02a00303108001c400c03200c029040400700e20041e41c1c00310f540000e595000300b00015680781c00004c2460360203092108001a0411f80300c1c5001d142d0000412003801c0c1c400c130b038a03c4483c3d0301c5000b0300c404071420380700390228040e1480104090780b4041e00107981c000141011207a45600740f080292030602c003c4400c102c6a5550070f4140290b00304070955040b40c03041501c061145050540d1080b0851400030640c01b0070088240d00c480c040311158002d90000d2400520107502c42495600800c02025440002c601094030788500103010840c24a010a902c54010041e00c606495615180c00901942c1c44105201d8016018010034111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 263052140 1250 263050890 263050913
    0x403260a0806030d02071a03040c03020a23040207020a0303051b061f0807060504170703120806120708030f07020f060409050103031103090604061b17030a0f09020d110607 75
    0x3815075072004142003000a040c01c104080030074400f1504150070074400c0c07041c0c00b80c500d401040250320144ea6980c0b40c1c100880c699142d40c000a620800048000079040d044042040300b0068440380d038103034030130500704120481c07141d050001d4101c0c03900030003003001c28080c1c80030b0300000c80c00305140c00c40d44410748030450628100704c55520a26000f080185403004020781c10710098015600103046103800e100b0b000c0c0c018002c600c11081c1c0c96072140551982480140081070041d988401c2d10342500d405088081d124150455240d801038100c620f151491600c00034008007221214005540b80c1903005d0050701843d0b1007100240e8108190100f01c5d030301c40e1212001400107100c1c819000960f541180f80040c0403503642074004125500a000c00c40d62555a501102c080359602e041c903100034043c0205003603407094a80405000d44d20b442c0c5201c1c0881c02204011031103450200c1c002c000c4840d807000804121500900041d40000a80d821314002030009080301110550080c54241018001c1d50b60034413414 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 263053390 1250 263052140 263052157
    0x40f0c060801090c09080c0609030f03031510020c010e120a0506040b0708060d0b0621010c0c050c06040605041401020c1201020c01150510032a021605010311040326 72
    0x80764000100540b04040c491032044402c03030b20703003042c00e40d02e0f04030415a14488810018494040040c940865540400ca801006140c40040c0ca480e4035242400104006502c0d58144c06044c00f0b508009000d0310200700c0784400e034030585400c0b607921a01014400c01c820000862502481250000808160704200a5204030701c43c0301c9527180c0c0e00c0c19070300c028012540600070600400164a403d0009006203100590000c400c1c0c1c0c14881c642d01041da03101d85a59180c1d59520745502e42100b0031794031540401c0c10320005000c0c404441e55a0340010a00549100d2441040c000030400c0c001413001511100e84203440c0c40d014070403a880c44140d2000185810140006038009039400128078620850a0080304400105601c122180a10b088081b410301d039040e5003000201a6181181e014440c40b081080800d203060145c441240f810201020f50741c0c0d4040296000c0320b050303041c00010a584240540141d0494400c81c61b810185075540f107051040300046e510b03070880420303504200c000d00208094000b09 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 263054640 1250 263053390 263053397
    0x1209030903071e0803040506070609060b0a15110f0c040b0402090a1d060306040f0201080402010311210a0e030a05070f0f08040905250c1110020106080607031e05040f0c06 75
    0xf25000d1104480c40f607a0001600390824001008a03580310000e07251360541004010400442c1403070010010240c8880c05907001540315004222460545004880011140c981311041c4080c100040c0d0f907000280301c018202d030300942c0c0d81c6169062503000041c0d160350181015040564031000595840c05940020302684100d8800e80c6044420a802503040081070f005814a410140c5503101014017042004c0e05011441001c6002c40e41300c2d80c00350700801580782500c3d440340300400034140d00301c1d200e0b4920107c015070800400e400409502c01d420300355072201300a52502084171002e54181d08049401e9544803003603003071840890040390004039180c0c03050a500b075855081c2003074441180c0001c1d0960116991400204540000540b03003440c4a07500c41c21f111404014a02e081d64004d0322142599800c020410b075001b4140e43c05420031016516408142d914a98440c00d0480845002d1103641c50b800c0740125130525168400c2d40407d8209004207000b82c3d18a0582d1260750f0201410303408170001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 263055890 1250 263054640 263054669
    0x91f080601020d05070c03020418050d0e030c030705030a0303090c08030f0706062102040b03010e0f0d0306080d050a20010c0e01080703090f120302160c1e0308120903090307 76
    0x10341c2e060024464000c00380c1045401d1000c241c0705e07610541c0c2c8a02009004650721003d20071800300e0801040b2030140e0002c101c810a400b5400014107652400d081c0320300a11909009842518000c1010019280040c00800b40662191001c40c0030b441101710a4440048100d808180c07030609200804140b480807485594607141498002c0440700d0075030000289204800d40d01d8400d90076151440c100c03540455011922175540c10009004052200341071081c1e2040307890800100c1808100011526455213040140035a11074041d52101d44900c145400079500b009031003060760151107003040042030b03907001d100c440c03410380d4409085404200c3c00401140002e401b0750601c1d03034003508103039010b2450f140c148000d450302d035501c452384c0032810300052030300c44494072105400340f20740c0c10b54904e945264401079141d4240c0c14030300c0b1030481d58001c503006e00c11100520121b4010416164040300d9211000d41d107407114103420100c0c103c07000f0f010a609400b04115000060b43e0030464a4040e0000a101118 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 263057140 1250 263055890 263055901
    0x40c021b1804141b0d060f0204181d0106081203091612050105090d0e0609240a0210110301030b04020a0305160f0f0b090918070b07050f0f0c06091f08 66
    0x645401581c0300d44031300c0d11a008103031003034490343c0c044204668400300204a2111130309900019002e91f4204840c039071500c48001c26102030503044000c807c40b01100f0608584600100b4600742d402034080d81445600c9201c64600402e17449000350b51141c9042c0980d10a404410082c0031204410b81c0400425028111040c0601100b881203d42100e0310728018007400c002002e011389a00b2504c40d90702c1c442c00011401d07000b0f6444540d1160290381c0b00020707820b203907604100039660703680103803c40c3d00041c4542030354580c044000380300340c50040b401d80e845241168a036030b480c059075071801002281c0120325440c00000240c0c04120440092848007231421805c1e040050108588034654042074a80301030701c03000c10454055000b2126206406d0315918801d60300d00443c40988400044000c0b803030301c9564000141c00c40304030041c000c2940704500351038820300d000c0021036075030810406131740403074110383d11704981031610400400000d10007400c0340003a4924030864410340250581107201082c210342c03c000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 263058390 1250 263057140 263057143
    0x60209040911100c0b13050c0415030b01090501061d0102240105040e061312051c02120a0209090601080604090204180b0105030730020904060603030e040c021b180414 73
    0x800680c1c901c3c140341001c2140d1505c0c000341d207015040064641c001c801760414404240079001c0100e401800911020301e0040c521400040c8922055a00c0a01140041648a40c0f405001d0403244a070b40d0722200c20f00800034501829814000503410743c45018001c0d6040398103a170b069001200241522843c0d58584014002034a8000b10640656081842000210741e4140b03129041c40d42c11035001c0e444c140003200152564070420291394103802c000200050780c075206400a01e9420003821000c2d08a465030001e007070980c014111415402a11840001c40c02d501c00c00e41e240d44500010004686140d503500402e08a03000342c07922070944030140100030103204000042c84c1c010034091300180b02403464400c5a61381510326031030b509241000004802019400e4003181c1e41a950010041c001c1402c051030310000800c4584030850104645c513042d8400c52400b442540118480b51700a8a030540d407041c0c1c0c03140040c040450b135030392110b1400c038a590024080580e49100f94031483d00c1250a03100c403141103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 263059640 1250 263058390 263058409
    0x190602090a05040c031b210902030a0206030c030703061a180312070c03020306070215040609030c12030e06070302090105041e03060203160210150b0a030e0f160f05060301030f060209040911 83
    0x621000c3c115154a010490031f00100c0c000307030790000249083d603510011f400c0ca480503801941c0501c01101740041080410019070007418207072810400d05641e10425000a200d1450060903920300b072052080004140c840030034111001409d0f1a0b03000f0382c03020a41e00a410244081da03100044030b500380118201040680d4220205000030051f00300c1d00340d1760a810040c001d00003060380381c40704009010940034003c2c00001d180c2c0901804a01043d0550040007080058203010b07140c8a050f01280c1550f019108480e407241060303413411300c2c0034200300620302da400d4006401d4a1504d40150000007007450342c0b01850040c4449132020040800b8030400030b280c8110717655040230352450140d01c0041c02602c0e00d03a40d000c84100b0f160140d1582507042d000d074000c141d680b036074443c00d0064081c8a41e04890210340c10990700420b6a40c00001c41d12110211002010344c090150048010401070010841040307000e84003a116080c00752400c4245004039007030310030315407040380c4034961038501c00d2091038140100c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 263060890 1250 263059640 263059691
    0xd020a031b020a0224070f0302070510030c0806180c0a11031305010f03050c070f0515040b0106021e07090506120f0307031e0917070f03080903010c02190602090a05040c03 75
    0xc4109041c0b041242c1180d4451b400c401041681c040c41c503002014000c0c4501c00091800810f407280c0214410805809030203d44002d030001156080001c0ca10300e048103142203103008074426090b05542e0714050940c164080080482840459124124020b2040004001495641d801d0704412890840054041140d200d0b0a86c1818140f03401c2200c085807103002d44e800541c020f50000302100560500d01c0c00c10450440c0b5081c120002d40401080c09103a4502c141290350560888241e410074501c081c0c00b00d8581150b402050700455000c101700080764200c80d4211a005040300201300b66160030030300d810308445494001d03030004928101859000356500f45080660054548022000c41e0024496602c60080d03060001c1c4401403404011810091756010f0065081c07100c0205440741445250b5810015440d4032941c20510300b030001034404900049011038812882c0c0040640b650780708041d4000120068100ea001c2c10000f92581d601c2c02615560344141c1c80001d01d0380411003881c9a6409080071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 263062140 1250 263060890 263060929
    0x90a3e07050f07080d1d010c0204090b0105010912211e02070602010506041803120b12150a1404110315181002030c0702150d05041b0602070b0d020a031b020a02 70
    0xd5803070025000b00ba408003410100b840c100546d20003100584107c00750040280d0814034043c03241d400c00805580c0141a41da00340c8075050a141e0341c000d007076a40d074403050000f0000725000307864054070500d280724040840d0300d0b81804101c1c410304455441b0071049481001340143c1c880300c01044080d07020302c51950400c0c000d46041c00070b5100d064034504000303400400281000710a40c6291030f00d08039548800040c0e80d00030018000c98409071000c0341c3d81d811170700710a05109602008260348110741e10030841419568076001d00d5a0340d4944a80f281703c82c0358010f50381c144c00b03800f0400303400404030b2000500c58030b5455241004a001c0c4801a441c000020603016507052042003031003841c10800d802e03200c010394100c4440b20b0a4000b07003507071a00e90242d016200038070360914082c07104010f00c0307041c200c05250819000a2529070f41d140201e0383d4851318800e081075900100507200e5550810380003042d0f00965400e02003082c4446075684070700011300c0342000d80144c100c8000082142341164143d90703104000003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 263063390 1250 263062140 263062153
    0x6120f090d09030809031c090923010527071e031103280e0705090a200a0c05070803271309030903080a030506090a3e07050f0708 57
    0xc0c0c0302c02e07803600010b480300502040104450358200428001859203400341200300100810140c540e182c103020f541c010505052a050440300b924103e40f00c441103d0000040c02e9181106002500321001204001880403400c01e01001102e01007203401010030b0f80d25000700d8511b41041440a107501d2500c00e04060a120707a000b40c403a121419240c200c40f8221120410504205100a14401054015170345a091031106030b8100700100e044402c0b03c038240d420b0071b01c50362020300709001c8804803942219600044000c2840e8220701c00b014241010080c20510701c51003182d00d50301d240150551101e0182d03880011402d0030382000102d646188002c51000c1a103014180c0300141c04600804141100b49a4a010300c01c107040c400e0800600554004503901d0742c80e005040001c002e8107044941c280905424000318246000e6481105100160340400d452300c82c00580e000204c0e00c02001c0280c52051610070b5200b01c9492160007070101c0740c03040008040200020351850304022066000450a80019 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 263064640 1250 263063390 263063413
    0x140121020d020108070c050a200303040b0d0b0f030313060f05090109030b060105040312080603070b070f0b090304051e0f0a060f1110020409020d0e01111b03070206120f09 75
    0x8a2400301c550350909116240b940c9000084071007201c04031000d0054420b8a03140014490000c508811002d00550346810b4402c0351424181c0c0d900c1070344550048444104800590100e81d6030200c41038070310003402c0c80001c03190782c0c0001c1d14641225041d001c14054446d000c00400380c128038202c0c4841c04a06119052001c20310020b000f072800751101a2190002ca000580c89030311440c212006580e100301c030000c810344001c100400c26001105d4081c0244650000130590800f0700040d00c04455124110072080f0b16a40c0e1045801ca82c00307000f80040b840140310210f0b040c0e460b05d50405107540b00c103002210122030764080100000c29920628002c0c1515001409000d0744520b41d10301c1015182403880d20050b000f980d051410030042402c08940b840070074041488107064009042150a00000780101c101d90000c481c00c0f103813500a0b0341010402041a031502202e0410807480000c6a4020341e030a082294022a00759408803030300040c01075130642000702da803a900403505c0c1c0084004004000042d05c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 263065890 1250 263064640 263064649
    0xf1302040c032f04060c1a180c0a0b040506070609170901180b090d08072301050f01060519090503070e10080102030c0d020919091a06030402100e0303040914012102 72
    0x1640a8501041011041034050107030301c0c00e010503403c081c803448403108c1ca012020500b900402c030f02601b405015500440201e468502c80300e8040e105000911443c0c5460201008039a91041204507500364903070451b6404284503d812045004448542d0781d41d503030481000404081020300000ea90340c03140003003480a00e4a203015109003440941d0150001c10741401d18580b58010b40030020441d035500c0e408601050f410f035a0240032080e0300c400034845a218880800c042080900803c00011400c1c003544103146030500e1500d4401c031450409501040c0c07a00042414440c06d504146a044481414000b90341045504d40f0000c01c1d03014021030540c1080b984002c030901c60034541804c0340b0340214011130b00d680c403060f24210003221600c280440c103941c1d405007401f410028010b008003071454180c10f0044d080c02401c0741c1c0b0450f40101440d900092a00c400d91303007468002c02264140c03000788000310305101d451044200d0400300388a5243d0302c1d03262101c1d240d58645940800000b000c280c200540c0182c0701c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 263067140 1250 263065890 263065897
    0xc041109090402130204180f0513170c0f0c0f0604030b01090902181611070e0402061b0f0304080601060c1a15060a0509091b030f1302040c032f 63
    0x40031a00e150160325680000344440b84a000c0f081366581c4001800100200807181a0415600800050180b42c01c154442c41c02c40b10200d85801840001032140300005402e408420041c484d0803229600f42a450502e0072b00d0f200c4072482c0d5021030761000c949060940780020070b40c00c401d54104c0d001032402e419a680e1881e403140621422011036141c042d21011580c4000c210811040404403900103071400c1c9040d0680030040c1210000400d00e40c80014020200215115042c0c880c18080c07006e4603211a1300748030245d440551108200800c003070940f001e0100900994000e42403900040d0f46550030002030504248043e84074109000b100fa00b5200055215541c002c00140708004441c8180c1d01e40c030800420305101540580d000e10005a440e48868000024000310081681c608c02160b407805480340c550310340940c0b0650002803d000007280001c07881140c0740c1c8408100d22961481030315601017000d40712012284404240c881d1090981084160041042c010039819040501e01030208151018130 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 263068390 1250 263067140 263067157
    0x21f05070f0c050a0f051014010b04170114040f03030c02010c090b09010c0c0f0806090c030a14070816030605060a0b0406140405060415110a031e020c04060b0301080c0411 75
    0xc092964406003c0c0901c03080300a141c0050083d0000c20461500c961035042c4030501d151060b00e48200c1800c003414405025041c5c6a580c140ba52405051024041c0c4880740261010b04039074035540c0b01e41856044c02d1445004500c04c16802e80c540b0400c2c0350140549294140b103108580c0b414614400b26940903170840111041c00c0c440d50340d103030021340040390342c2100c0340e10140c03007030380c2d10300c03001950300b000d040040304682c007900654556450310201540c68541d0203030095490b0b0b2005104401240a0501c0c81a2030f00780d501c11208000e5a4011a41c18480804e5500d140c00e42c40c01020414040e4601403c1d9000001f211010140c5060500d030148a0065000310410429003a0070f281d1041c041310200d40141034010292030320395503500801282d564080040400180044403e148c0c915800217200e003480740d15498802d001e5540d4403080d0424090801d129003188208114640b0980391480303520041c00c40300c1034603540c940c1440e0241e49842030308030715a0301807071605001c80a440344040c1501d4801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 263069640 1250 263068390 263068397
    0x30911090a0207060c11010f0506030312190f0c120c080126031b0c01080c0d200a02070311030c060d02030606040b0408011b0905090402040b01031b021f05070f 70
    0x544500041c440240500f4100408091405c40c81001040d008081001441400310007400030303803070860403001607441c15150241c0540c011310454040c2202c00030104c0e0300042c45007a482e02112403110790b0f0161941c82c8000d50045940d541560191648100400504600b001003840021540000101600414440d6941350414091139070002e080c8131000410040da5202101e0315040e04020079a9403c40c180c005400e1449070300d805030255400740c940306221303400413101207081004050503070000c0c00d00f03001644d514004071008411400c070802c002e00315038003550b4024121181140340c060014142c60441501c0783e0301144113199656105e4040340c0c0743e1030107000003580700d443c0c150110f180c0d4011b07a00034081c0844003080100307811038154048800d90040356000180c0840c90b0005032500b035028094540c004103618009009410039400c032074060401031600281065556440e9a42500b0300c140302d0005800440a51075554209440d0600300003c995040019040c00d800c0601107503c88a045401e1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 263070890 1250 263069640 263069659
    0x323040b0a150f051915050c01061a03062b03110a0c17060f01060c0f050c0901080706030509010e030301210503070309060810030302030a030f020903030a0201020910030911 76
    0x80050680080640040d14250000c600f900c503060950b188466000301c0d03004140c450110285070b00964a80740484003007400d540034290b00d03240c040340d49502c2650007103071940d03c0340000204282c852510140260342078444c00d81700d060031000c0000c440007002600c06000e01c1501c1c6140e5200d0b1180104520550600b020300710078254212450510f800c8242c064240d4104c50f100242d102c641c00d00500880344100d081e24459603070b00d0660b89100d4804c0c0928000625604510000107080c100040d8100f801402150510050f0000040920900740c02c00320a03a00718810400500343c240c0180c80c3c001605100034406400805501590381c041441100c07144525010580080c000030300c0c102860359009000c0d40d03946c078070030708002d0000d4245c0d20940e0002192a80042d11905003190060705a81d03160b80910301e40011400c048000e0617100c007081c0b100c16802c00440c00e9a0f0b50400060548152580001d42c684c0c1d030040400600020140200e800e00d800e00c84141c00040720700c0c8100c1440307482112aa040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 263072140 1250 263070890 263070901
    0xe0a0f050609030703120c0b011703120403020c040e010e2e050601050c030a0915020d0801090506151306030b06031005010c1e030e09011502100c050f0a0309030323040b 74
    0x180000b1940090098044115070446d0b050380090030725011400341000144590b83c901224440b0a40786503110400c0e001840071410103285010709a41150092040700c2146440400060841d00f4078124003440e42c4d595111050450414090f015561042c8403ca00301c004000e40e941c5803000b11107003042211a55040020a03503800740080c0d40580d004001200c0e181c240f0144003429100c854003640504c00c40344008a17140e03620010303411901403041c1d130f40c42c00664600110140030f40780180030190302c01c80d201004c0c1510f92462001d00100190705400441031407400c42d0140c00c45980308038050040404104001c03081c0207502d08001101e400b841d084581c2c400c6030910000c140412082540c0f40c6d005078004c003040c941d210f02d015070b091070200c0d000404e0366a580031880821500c60611400b50b080380b04c0e26030f001c6240b80d00c813100540d824101249442d1660304025195402801100003003030303403001500b0515900d4481c031440c00001d2491a40707520004140a400028001d200404c260060f07400a40c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 263073390 1250 263072140 263072143
    0x102120d200301050301050a0e0a0b040201030b030f010609050c130311180112050c0301151202130203092514040f0e030c0a03021612020909071a03010302010e0a0f05060903 76
    0x88120141d080a0120001c480000456600c01e101d494400e608180210b1009046ca03c141808008003d0080543c005156103a1300c84085c014402d0381810365640c030702c80803510b040c02151079080e8024000240309040080c00c00498402404244003801c090002001c1c1e0400d0300070590030b4035040418080c84107451000981d074030342100808019140c28400000343c088100342803c0500d4440d2041e02c0c074600304c5d002071500701d0310240c0310040f0b5000d241901300324009100010064050014040000118036050b2040a0340e01c00d860040282d4070042403280d817401140c100c55121203401a948800340d140a1110014020515100c2d01c19569207841000b000271503804405181004400d4035201e1201a110a844283d02c04064002d40030389459810110034024281041d03d000700d40d00b10716010503400b07000808900900c400414441c8900200b000000c510b021940808507000b019503960461000411714506106150f0140050b1842401103041441110095074020b0716016102c66074100000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 263074640 1250 263073390 263073401
    0x1204051606030b01030507020c090a110d021917071d060c0a0804060f08040c032307090b011e020d080c040b040326040b09040209040603060e1606030b0102120d 70
    0x15003801012440016000e4268000c0d0300d5440007601c0c01c2100c1d03079078100166110403d1840c80303680f0070011000508180c00c1544030001d10940c3c840002c0c14101d010b100282242d011501900c1c403407040508014513103600190420320704844a00001103400e180310098400c00d0350900c0d04d260561400e0301448603032610804d603105070301000225880c20481c2e08202c03c4030341c0315001d840002a8500c584a654a0080c00083c0c003075030b8807503410842646552650090240004100000303594002e0403c2c0d02c1c1d000801c100c1d0054100ba80f000102e510f900b4001400c0c52510b840d520030464172805503024a2038021640f00104c3c41207050a040301c0c1e4881c00c00040c0780c89544c0001c4004078005c5000f00c244803406010701c03201c0300d42e440194070688100180110600a91142e084641010404001c0da400c1c00d8015000c2c0c81c3d00608003161240d140d40d00c1ea4140c07140f070300d101d0b280b41e4040111801184c2c10074000800030b01007400c08100c50350002c00000d444800071044640321503400141c1c01c3d054801ca42c0301 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 263075890 1250 263074640 263074663
    0x705120307020609042a09060504060207170102120c0a0f080f0a0c120207061409010608060a0c140a021005070302270607051c0f020c0a03031209020303030a02070201020105011a120405 81
    0x281c42429401b00a00144184504c00780c000109140c10114800f402841114181d561035001091020314020303041ca101e8248543d01000b40d5000c0c41144141d0301701041050041903084440c030380b50418200e0040a6071054080041044441414006103913039000c541e6802c000000300100d060411010283c940007049455589000d100084040900029900c02510140d50312011801c0740c9030040c1180c20313200700707004031440d68002d0008150f421100d40c0c400b00081c40c2c5424071146c0040c03408010f05040e0400c5011f8000360300030038601540c4004500c109039024169090850601001070700d960782400c60644c4001003d5402040c020050b9110016101c0c0305600000301e0309580b0304405601900e0381d441c8c074400007007910040d101e40303050300200381c214420802408003090303107207142c40449640b441804221507c40d982c0d107440c009610248000c610070b0280a801581d2070007075100084c01c580c2c0503407108041c00c034200c4d12041a040c07550102c0b83c0b907204064a0807070980751400c0450501071a0242c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 263077140 1250 263075890 263075921
    0x4051903051204140d0201050f0309010615210603111002010f050a0c090803040608150f04090302010c090503010605030703020607020a1d0412170a020c030409020f0408070512030702060904 83
    0x4088440040a0008105541a001191540c00c0344042441170801e40d180e802408a803003800640e02d035803460005564000c0052001103942d41e6178041d043c04030301c1c40d040c2110028003d908007289400403c454103d545001c0300c0104510f52850f15841d0f55500000d0009108100c12440210213070b100750031211300f41009503030800c21403c1c0a0000d00040504600d03c07c0861003581c000201410040b05840442e80700e900d5012990b42d58002d6800b0605084090035400030030125101a079480d0b92040c0611244a600000340200040401030421040c90380003e20a038106002031201d0340340420a101100c4e4107442d0f15844141a20025244044a401c40c030205119900f079120f865218031426030089005d010507260040f8064011100310586109140c8139494040c00300f880c041e0700360b00034096411054162030510381c8501046042e0b901403100e100e006003000c10280300d243d805010700c0c0001c0c20304488020b01084844e002940342d000710f0300080e01c60007000c244d010070703916581c0044800195964 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 263078390 1250 263077140 263077153
    0x105090f06190207060c030f0e1305090d0305130c030b0714030708041e350a03060503070914040803040203030d05011203120b010c06050a14040f050111040b0405190305 74
    0x2d860750050000403050010b1007071300000030b12a80903c0f44c241c0341e560941c0d6200c09410040030240d5401c1440c024450f0040b00c0c4081d0b02d001c0500703d12030180121070040203801a18440b500003425140f020b86250103102c0c10480100010f0101c400e200210707a44088842c03a996255402075911414600180c40b45d10000003c1100561780f0a41a600c5144210f541c0e4400d01c0b201400c0d81c0c900040441e0003020f0034401d540c8044071001c01030003c6805c401041d40010064039440e20708000390440c068481c08a41c07034400500061500b8040c82000d071816000c20000380d80c03816010220084040c1c800b92030780354000701107800d5440a00440d80340d101150018006965034490206907210442819000200105203c0007807069a009890380c0c010141d4889404a0243c0c4440d0004e02015060201041d62415090030842003200001d118500902c1e45022910309800d0403420b41e4000040184081c4c0304204c1805601e40641c1580d0503908180d509100040c0250290f42110680c0d80005e070040c40341c00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 263079640 1250 263078390 263078407
    0x180906010f1b02100801031502040e150d020a090b40060515040e06040c050d11041203020a0c0605040e0703020c0f070b090a060203120c0306011b050d031116020105090f06 75
    0x18081724100e9100b4660141007460402d0f00304100d001c0c0d8019040440f1852000c41c182801c006010181d12500a20003542c442c1c0c141c0c006605185268444140710f525450b1041c410310344032040c00803281c1e110881d03141d40103100180140b0310001d11700d040710203440b00c40440010005940608080d00300074218031541c8009200180b82d5800c14400c01c1005030a01c0f00180311414680140c1041d082c01e601c2e030030f041c100e0215040020f4000c000c845480c0f00340900c80011b08064003031005030b0b002e010390041c1c01034081c03504040310081c56641244060007000c0104000c0d01e8261685542e00003283e10300103031584281001d003410207080c10300c0c0c7c80700c070311613408080390440603440241070880c0300b1110042c0c1942d5951085ea200d000b180e24506c1a82c111034000340402828a0041d54002014940084101c8090341200320441c0c0001c020f681c2c47c0c0c0324403040841c1c150580702d40c1c2c450b0700d040b607001400c03c1d48403048078960035843c02001f03041110100e19a0010744507d4043c2c0c2c66540300400301c03a102c0c801e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 263080890 1250 263079640 263079647
    0x6050403030f0e0f060105060307050f0f03010e06010c0302060103030806040207060c030e01060603060e0a0902030705150c190503070f0309080718050a0b0a09050426180906010f1b0210 81
    0x900800c85440c0340b414801c40c400f40070020b04450380036240341c040c2106a180900b00012a04000c1c1140d05101c01000a005a510100d00901880c190940c1140d10b950528004090f42d940c02015607052001c04007107500131075000159681140c4c0d1614000301c0c0c95541c540400d000e40910140241890309002501007100c1d01600502840a0000004c00ca55032b81c80c482141500d02501c1400012041e0703d0204520790016040400414000340c211418907a83d50003143c5075184907982e1000003600441c0c0d0b00504403040c400c0d00f064442d42040144074500b243c440036168411040001c100103d080c08100815000f400400300030701c4000141c44089554020301040c0c000f0301156078200502d8200060801081b5125068046501070840503205080007840802000701500c261005220b04c122842c0003404446a00694407415030016212584074403516818507803140f00304d01c964403510400407540d074407280585a860451501500c0240303c09000c0d65550b906490113500980100741603e4801d80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 263082140 1250 263080890 263080901
    0xa110a0309032312040206070206070b0414030715020714070602030706110c0c0114070203070f08160605160318060201051f0f03020105030402060904060906081203090d14070605040303 81
    0x703480300750102a285201448884483d01e144410003c10f105011001c1343c1c4002107503000b0f01c003a16541ca00074941d0002001d540045e107003111100050410401084042c552103592201c0f01801107060080da0341d5080d080302c80e44120300804981c042105010301402c084a050300c10248402e45240680b1210003c1d03e96220340801d0300c440b403d00181640d2015000211100d08001002614078101400c1c01101c00f002c500b0080d443c154410700c040c401503601444541c00510032804d00164440c44d0520072070a00c41c01021030345011010990801407070743c005048840703a41d03141105050507195440c0035552260303500d1403049034101122003c40c0c01501540007e0150713a000c076040006000c142c0403040c9c4a2900c0c0038103111059845420070041d4002e40186800520081000d0704100240002c101100c41c80d60101d6a040c3c1c81d008200030528040c0446005040c007000018510725054401641e0341c0f00c030008802c2040070b22103071101b0141c40b010685a8281c0d210380144154140381c00d00601408 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 263083390 1250 263082140 263082143
    0xb15010e120d230307020c1309020310021b01090803060a080601060504060f03021209010606090602012f0408060708040203070b090d030e030c0a03060e1209060706050a110a0309 78
    0x32030803400c10050345028002500142150002003080102900c811a40508200480a06140061810307034010800801451080300c0d194001c6c01d0030000d210410805584010350a03900a10b003450750030144c6c50104100200d41c501801c05a13440164000440f4011b840e03d500c030089510740f0080d00c00b04200e11000303501490084506040a6846803034180c0c9404003841000f000c140100002c000003030041d09011101045ea0a00505100385121601e0703901100b1074900300709035940c01041c44425000300d80c0d4400303004a0f1000f00040480c008840703d40c1d60340c07503484800d1441c10501400c0c42c0c01000d0206d50140c44c1d400d0541d0080d0614a4000d0601c800640c0c040b4481c4c0100c0ba0089050036214042c0d4040746030050580450941f80d48082d5103810080d01030355018020b0380449003058541814100055201e0200042e070b000c40c17100c005050001d0b00a04400103001005004402c1d5510402d1315003094100f040000e4588071343c00010001d0140700d034040e00041000c6811000640c06910645619 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 263084640 1250 263083390 263083397
    0x6040605060a0b030a05090c0a030b07022104140a080118050601060e0d02060703031130090a1401060504060b0301090f0e2e050c0c12041a0f070b1501 66
    0x240c6500c0c08214042d10345008490350014240005148051150000c1f80c004010000f1b0340c1000d4800303004501e100466400c260358a44100d01401100d550400ca59802c8c0d01d44c0030894440c1e070988031140d0034544218407072440074030201610529070341c1d0b07017000410043c480700700200f111914490484445041000050703d4501804000050a500a10300618006001402200b044001d907003000406d8120010560825944080791030300c2c4038000c8018054502081402d0203902c88101c5903c001084184141d0700b949880c0c024450309039400211154040c0e880844070101c241d40d144001e0040c42c46503c501d41c494204507000440004070741c0194143c4210b0041401495607031800802503881d0f110400b403503a8031000e5095455403503c1d001111104041c881342c09009a481382040c152072080d1100c9500340000204003640410421030f014540501116030390510b860455000302000c15003583c24042003000458a04000c0302c00200e030800745e4003810110107810b00e0120035041c00901441c0c035010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 263085890 1250 263084640 263084651
    0x110f0c010f0512040618050f011509150b1b0102030106030218011b020405090709090b0105030c0901241e0c0b0a02070215160203071401140a05031311040e060406 71
    0x2584500200c03900800c20f0040411503484503507810b40142003620480c1203811500301118001803041c01484800c291890001c124118081010020300d6019400005460300d80a9071840345240070540700f045070300d01e8480c140c903054480b0040403540750a080340d00c12544000000304c1c6140d0194060403084008500f1b048000c00f82c031005507503490f01081c080c3c0001105102c80001403074160001c0da80008104e054526030395030341680b813041e00d81c4040308031000c2c070300c0000600081c1020040c011003a40e048410a065514240b41203802102040007036001001d039400c01401c84c2e001c2d4444e00705011140030031851002103000001c003030b103811a10841e1041e05038408214000464000d032002d16400505042400036090310044441e8001080c850320070703100004200250740d0078880d010041c1111050540490034000c00140b819010201c0d03808503007000c0c016120080d60040c240c0340e00c01e9400c0c2a0000042641c10007240b40c001c6d101d070554ac428200103810f4070403080400c4003400707a0311a840c14480c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 263087140 1250 263085890 263085917
    0x30d0203030f160210091e03080105121203131b03050a201c061826030408030a15080f07060908010c050702150c030d0e06090601030506010510110f0c01 67
    0x3201d01c880c103003c40040e485102c10f4551085a540000c401038800c2281e051019420144242c4241043d002500414a03c500400440c14000c40f9140104d40000241c04e41d000216910151408054200340c2e00001101250041246050f03040740c101d0500000c0c184140d03070360301e000c0b5520141c80408803007400c01c041082c01e08464003407400c0f542c00c90050220041494000c04807640d0a00540103031940c13030b220180d072100c110301c0d24152a00d45001d41c4c0400c00d600440741d034030210700c1605460128103020401c204004681c11000f5287c00ca107000f440802c0002c0c552480300740e942c00319005072405001c0d2000d6641d12010010300c0004483c1c245e100c41211070354030043d0a00703c8a0a14616000c80c0080005000500e030882030058400d41420780f041c140b142c00c81c141c07490f68003c60341c0074440039568294600300001c2040700a83c0a041400280010f604668480783c807440c043c0f180d40d0150800f0040c0c1c60b2a28042c141a5002c6298881141e0003950041c4582d039544100d0070b2140d01007440d0408000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 263088390 1250 263087140 263087161
    0x60902010e041e090302150a060816031a0a0219020f010e071d06010207090609140a0e1507020c03101b0503040b010b030601050c030c0d120b0d020d0201030b030d0203030f 75
    0x2103540e9034076006600700c0300343c08080794003510380d41200f2011401040a0b11031142e481501740d038040e00d28883c00207901414007481070b2814481c0300e14400b81880c060000c1000484805a007280390002c810300100f40d44800c550080a8020081010041d01c001043d4040040e4000340641e040f1034070310004c0c071888032440249500c4404070302a40d120445100310b000561017414900c203400100600c100c1c0c16180d80c5050b01800c42c1c090f5000500c2913610f800040c2ca0002c40b40310030541020b1581e4042150502d00710840b0745d6407014251801d00d050010300024032581c0240104d00c080750380030b000d0320090380d403610f8072400510001000100a04080b0201180380744030b170041d0b03841a540400701030a03503424403d2446940c0c0005003402c0c10494204869410000c00f88007a10074640300e1001090200035400d8081c0501c03c0590316100000d00d070980310b1003c0d07541e0160100714540c0507200400c01e080c01e03000403005401048107598243c4103405032001d140c0e40c00801180704212007420100746881e442c0c684e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 263089640 1250 263088390 263088401
    0x1b06050403020306130c08060c07030806090712050406060b0c0f010501080109050307030c08070807060506090703021303200904030c030e09010302010804081b010501090c0e0607021c050316060902010e04 89
    0xa500f50b4029070000d814185103035005c90156000d005504110f66030344480c07500e4031204443d90880700c0d00215861080580000d4140d8001204454514842c41c0c004401420364454190306500e0366203910116080c05003590001c0701501e401d40f0200c3d42e46103202100c6698400d58a500e41140d0710700400007403a800180302b940605a84a0302031407805a140c2c0302110f500c030b2500c2d416980b2032810450000020300046c000c03c0d40380d00c01c0f480421a881c09404104203003000400f0101031600401221881000113801002960303880f040e40c82c1c11054611003414000c10104c581c41e00050104207000c00d150300030010b41204c900c207513504002c042e90300090040740c85003840000e020801e4200031a0000c0c005d04045c1450b0015810b071492401500c000c1c403400d680080e4449001d1039070312294024030940c00301c030380b50f240320040c0c400314075056007a80403038070250801401143d03600644001404003c2e003801143d00d00203500070070101d003030a541071000041c80486802c074041005114903c1300d0303040a0185 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 263090890 1250 263089640 263089643
    0xc0305031503161d040b04081b03031303030b0a0303050301210f060b131b050c16030b1005031f0203040f0c08030d1805060a0e010f060b34030c11030a1b06050403 71
    0x191b401521565100d1025411089072020091085150f00080d54010400755204007200c10b0064602c2e415402c0240480e010010840c0c00384020b0710703041c8040307034221044a04440410401c0360728040040310340d1141304541c5800800e1002c2c50000700d0180300150b000071a011000b2540350040d90b4600c052082120346c0c41205855812441740034100e81401640a05000fa13840e0060740c0c18071012a5101ca0001455041250581d1280c2c0c20710140141700c150340800f9000540040c50b4489a4442d00f0200041f00c49400c5002ca8000000030208062520b40118040d4030105010320300e1780310514181c80f6001b92940c20291894034119020620852003d0300d10590800301600041c2c641007603c0d800351448480b140720b103640b5168074070640c90171441490001c2074107002c0143c80e014a030300001001d804c615080a850000d418040d00000c04031402e00b1850f66040c24094040c100710b107841e0004e245a07050495142c0034010148060203540d00e14000012250340503100c4564440740140d50310b0003203000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 263092140 1250 263090890 263090903
    0xc080f0106090b0a0909090b0103060b011409090402010509100302030a230f2d0406150302180702070b041707090513110604090e031c0504030c0305031503161d04 71
    0x30100f1810800078004d0910721090b2070212080f945a071881740940300501011a180c00d201801041402440e218440304104c0929103000c0d507400307460b8a81b541e4000e181c061442030320b880d0003280843e80100f04a420758031018044149448800070301400039001101d040311001c3c24406602c01d041010b91403007040c1d0442c180b039178409407602e8400720a203141c010481013024441c03108151540101c0d018080c520b4030810070500d007074030302443d1071000e031098803a0031b40c502005c1c41c0041c40107079141e00e2224131584000007503051a68039a00b0881c0703030108580c4901404080020045012003c1c6c00310300205e18208400c54290564a07000c00b1b0441d0001c90711440011401218200001c10000d134103092003400421150030152650304a100b120302d00c1e41c0714403841d400000e184414196045146603280c80d804810049407405403030260172085005001002c124002001614007802907500070700844019003140d4000c00420700781c2600071110302502e20800a03940c040841c141c0f800110904c210b6111a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 263093390 1250 263092140 263092157
    0x809070605030a0e07030219090b041a0d05030706050106030e16080d0315030b0a0506011706010206150402070c0e1b090f01030902061909031101170402010e150d0c080f0106 76
    0x40c21001440e0701c45542c4214002c1c8400000541d641110f002071034240c07094000740d4527190100041c01c891514402500582c240400c50003200e400689019480400380c51464100f00c003031901038210b00c00c11400401d62840c02002040c82c9506034031040c00034549030200c50003103a046407408248a01c41c49501081c1d4081c4800c1d4940307900c01c1d002600e130060010f0038500c4040e20b903610481c00510848100b4200c82d070396010080c41e5070b440780d5038042c100840c048503641c0d0308103140001d496040042a10210b043c0c800b00071b100a41300d43d4100e9991580000b09404c415407075165901c1491800e550302e00304a42c4003100e1907442d100c0702049928045004100388542d03602e40005401034a2903150990b4400c40a019011905031008080c2440300388523560261403500b140390408110300e8140459041054062000074801000102540c00a409080c414100424000014407030703481c07640f100000040204003e18540802d42103000f103810303541c42e1844955034681520b060002d091149900207600380 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 263094640 1250 263093390 263093401
    0x30108060f01062d2c0102010c0c110120030a1d0307050d0213140108030a0318020906040e030904110712021906020a02072301090e0c04091812020d080907060503 71
    0x3030391010f031107652803c0800421905d15220511405100344d10804850011240b520300e41e828802e0038008061420564800619a215021554801c0d2001414401c8140c5064407529006045071061041c54003204d9480c1105080186495520b13002d03218840e4002c001d0707003a640f0340030404106859000d03101d8100d0442c01d400b04078041e010086800d5800e0360728058000c01e100585211806040010b004507070304d242080b0010100c0301008218030301d450b26a24002c0069032440803132500407404403030118880032010841415071041501d541e0b849840d2140070050325079110040e0804a0094141070800c4801c00c07000c0c0e07150628480c0c0c0c1d0f81c9182c5001001e40c0002c00d15070190001c2c402910444a5498440c0d010040f50441702528985481c1c80c801051324940c0d101c400314000c0c0c004c0c0c1c04158041d003850384071030a4038010341c081d403c22070351608100c0e10303405406a00400c01980090508042c601c0811000e03482d03081503035000000460031000640c81d000000f40d81004c41f481980d900d89035a494 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 263095890 1250 263094640 263094707
    0x60c040503100203061201090c0e010f0609060e0406050406090b040506060f0a08190c0c0204051b04060c02031903170c07020105030c09040e160f090905151308030108060f0106 77
    0xc044946c0000c000d608415039600912132604840e101d030f0000402c0c1814407c1781d03040848142d1000c440a481d0000034050740c2d610602c003908850603404c1c214942003500001034080c103419002240c01c18581500010781c1b502540000b0400a0255400c0140c0d4072030740240f00591150300340680802c4810400031b02e440b4400d10100345e00c00110121041410b0303880d032000d8241d503130080c8210000790103500d195041d4501032050a4012040b500d8090107050b001c042400c05001d144101410300c200b02000c00d065480034060071142690541c02801900c030607203005480035070051a800703c0c1e61550313800201c06004800441b21156016141c050650f9607003241c03940380703501040420390401d40300d50b0000b15186080147c0d045015070800f1001c003280c1800c21030188240c040c0e001041c0c1c203041103201c20210b00c0111b5003583c00c036001040c1007801c0e5a0480166003850320580300901c401ca0002c00003a40718008150207005104100059007030fa640c0c0c0c18110b80540c00329003401c0000c80b0703070b6075409100d414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 263097140 1250 263095890 263095897
    0x411070305070f0606080102190309030f0f02070b0d1a01110705060f0d0e0a03030e0c06030a09051c0e030c010f0e090a0f11120105060a0903030f120e030a02060c0405031002 76
    0xf05401404918002d980c660040d15180d510000c0d143c2c0d00840c2010000c100c040002d0301382560789c42d04000881a5071030045c01c1c15002d181171800c2c85100c4624400045c03007403081c000078044101d03045549080fa8600b4070010491810081410301070407c00128a40c401e4040380710681d034070b034010054141041c0801100381e000d03480f0501e00410402c6103410721b18403401103580480100010f40002c600a060181c01e440320807440c138003d500212405520383e910075042d80c0d04407a0340240040c1d0401c0903c0d219140504040811001710240110320020ba940f10303200d106c0c41030090b17007901c1c021200800152040030342e06200c58081031001c40c01c42030904000143c03d03031000c61039070301182ca00007940b100811628407403108001a140000d0700c41d41c044015100030700501054591625002d00f40000403d018a20700005003080135160350300c543c040c0f10b51094038503d480d10008000307103130110040a60b02e500008052015006403400180307009130100a4804450019000d4140c420100e5000c10003980b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 263098390 1250 263097140 263097143
    0x21030109020a030b0a0e060a050603090706030207050309090103080c0d0905060a0c030315060c110d03020a0b13080307080103050f010e100c02071e051201051504050c1b031305041107030507 83
    0x15611800ca030760940e9540102c030010000006c6107030290500c501071042d004000e0b00080d000380010010312005000014810085440718940141ca40426140c01811413003100001355028100000110030302c541e0900a084a0710b035242112620712603070b401940d00f100544201940810140040030070305001301c540c43c2a192207407030009282a02d220400f0508040d507006440040d030302c41285400c114003007900c13490309042207079140b52060080e40c009550b412304440061200b0782c100d001c10b0f098101d61400c040c0c072507030000140b6200c2c58000070080020400340700c103940c40d1285110640ac07040d0b043c0f042e04500a1420084d040c0341c882112103034040d003621190700086206140700007036500016035401000c4540c0030300c0341a60610705000c11203c44100420380d1880e9140005100031161080d51204904009450100c0c83c0c0d9540c01d8801900c1c00361440c409400c081107074441c20b0901012000300701c1c018541c124201915200c1c0144400c4444000b0200c5110800300184004a03009402511016 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 263099640 1250 263098390 263098397
    0x50d03110d0e0a0e090d140f0304050a02040b240a11070902070210080f040627050c0405100518090a150203040303050612061612140921030109020a 65
    0x40111608440c5041c544500150000710782c106129a98900a041c0d807000300401c05482034a030400801c4551540034a00c0540f0500031844030041a844000c0c00391a04802d501c5151901c9242c28108151a1203460170704078420b074035005e104445490081c41320340300c180032003004030031080015491400310390202240105020f6003038a0404003401c1080480090164208003688030b42071441480070400c03000c01e03100c0038001c100e820448044000070300c4640c041e401020114001d2015001d01e9402d150b4202c0304140c1c007c01501103000c0c04800138030011451403d88080013030f80d8485603508405a203501a80b80e0001c6100c90200c48440704942d0550401c2604095500051456888210400501c0008481d164000c01040b0038181c15100e01c81c1d0214040c0c4103c4200c5841006464036518003c1800305c4200340304846240303d41c402d00036a000c034803a00307008000c07515402c1c02503416003d0031204441240b02d4031010510035036000d9820400c1c50b030100005810342e400c00100318040d4010020780402c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 263100890 1250 263099640 263099657
    0x3020412050715030605010f0509060909010b0304050c0102032a0f0f0a1a0606041710110d0b18010312180f050f03011a0409150c050919050307050d03 66
    0x11008035014108269209030010205545020209890303001411032060505260040410550742c003c50542004151890140c2c0d41d4148600041c00381c2c01110003aa401004803000842c1c80345402c8021030145002d40210b5025200b00e0380120f98a100d280b00d0541070344200348844000340e00c007440e8400c5103c84803003a10540710310211454a05115401c20f036000e5480f559404044c041ca03800000e014044111204040d890174001207040c6124038416484c810160311305c5007000031030500c844120035035482c9007440980c0c500e2150141c1070300300c007400c92030491402c01c0400c038900c2c2200c500003031040740c4440f0345004d0f031954643d62100a403080821060009100c10071981d0401441c038203001e403101c6001000000d08080038800301102e421030050280c0e01d86005c0c485010500190000d80540c100c5002c14040c19070700e06080011000c5c20002280781c01c0c4510303aa400380e04400a014012001d503030b030081501260050310100e0100388175898041d0030011083c041d034144148400d4aa900a040c541403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 263102140 1250 263100890 263100899
    0x4020f040b030705070c090b090103030c110d060f0b010c02090c0309030418140f090a120306050402040801051e011206050a1b0206060a0602030703140a0306080303040b010f0522050601030204 84
    0x40c070790b0044800c800002c600040c15410000a9064400601a20042048614401404100c1058060101a00f404540201c0030108031424003101408480903010182240582c909040500495140f201c4c3d00c5090048a00d9507521960785104590b8005002d1201d540399041c008000f9031002d0700c04603040c001040017068003c0140c0031100c1c0a004d210001901c100c1c21099602d11000203460040300303000d0380302031000011002850f00b0311240c21201000390b0750017138202500140036992142e40c01a001040c005a08041940003611403100005800c4032042070001000c10701c4824024116032800b403070006400b160340c1d41d1020b9071060344403100103220800588141000c2c1c3c0c800000e0001070788648100551418450810b00052420303000a5081c03180e15a409040340042c5810951160341c04150592428403031b030003c10007441d0391000c0d80e40d40e04190070021a419824010044d0440c1081e0000450f400c00888a60b40c2c0c0b0102005000e040d032850700300e030004e0b24028110b10b0425800348800705 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 263103390 1250 263102140 263102159
    0x14070503030a210626010b1201090b090c0d0308070320030403021b061803252d050d02240a170f01121a010b251104020f04 54
    0x600c4002c035031519402146004039914081014454551220703081920030006108952440000c02e0664010006010324482c1d102d40140700721038982e940042c1c140b036003a0204034194800d00c01103000d8081540c03682d8450036680d50b03e007445c0080c6170300085880300900110f031144000302d800021610380801c54800140c246490901102ca136075000d48000002d00003055010000c007110203000d4440301c680210f542001400703500401d0303881385c401301551020302c8141e50305000c0d02428405140d80080c0b841090740401d01070710070b80e000742044c11484d08080f001032503920700c0d001800010481a0903589080c03005102e003900d14068102d0700250444298140701107169254425014800607803038030f034108c2c1040104060112008104c164644106000252a04501031419110f80711081181c509080ca40406001d14482c0d6144000320610004201030b04550000d0001401c002c1c200041c02807101245124090850001010024400d240c0075081c00d041e0043d18601164000d468200740d80c0750341a0b17 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 263104640 1250 263103390 263103397
    0x40911040806060f0609060702040209040504081306080f04032f06090106050d1a130b042117160207050402071203050f091f180308070908010209010c1407050303 71
    0x684910002040901c61618104074580d4850f0040750388450380780303080b0045110b9109082990b4002c0a00195010a5403a260100c0e110801d01810802143c42c3c541401c200580145000c3c2d140068420800502d5601ca60f89031401481c8840074485107031610f80d000d50f01111040680e8054480e8a01c00c082c801e031400720500c00d00151107014080900d44038000d2400c407685a0452842080611181c0700840d246065104041c100c0169001203504e45000207103910b00000401422071148104100c100504104041c048551035140300701c00540d2a1010303a03030300d101540742216100d41c480008440701400d001c410b04090090041d144150388480208091303900580c411f881d0440031084000c25580c0c18481c4603408540541d004806040480d900354441d804540f0103107802c00404800d516018a0b540852050003843d0392113480791816107005003041130121140e0001c56402d00c00000ca40074103000700c03048510305940714603284546a8130041c1182003004020614800e0b01000308090302c041000303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 263105890 1250 263104640 263104661
    0x50d0c1739071703070b090c0918100504021504080f19030512150604060e09090f0c060d150e04060f0204050f060d0e01020a110c030a08040e0901020409 67
    0x10345011078160807800ca85045491107980c41240d41c4040e903005840104004060303480d502c50598a401c020650949103001d1418043c00031070000082c007554800008990321410340550b058200c5d07a4604480c11000b07605a0719088040d044030b403c56604807040d902c480d6000344014000161800070281154407900590001c2055901c2251050f0401d80100a840494060f02c03840100800300b640c0d00511034041c1e1801040c0c5403040401080d003001080f60094030b1003030060030707403912296a60401002c100c2d1260095014075070f4580450b00070312001c29130400c2903919200811034401aa014000254081c21418440c3c6503100c0d080c0908480003040d80e8010801120310302d080d410310381420001c0b1810a01c0c05201903104020030055500c0e440d41c011240351049612a484642040281015010001c0c1a4256510000b24201525008110161210080012034000d0303203140e002c0c91b40c3c8617000314002d401403800703001c1000300b4181403101c19846240e00c4009410706580312554020349501952 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 263107140 1250 263105890 263105917
    0x15141b030a090f1e150903020d030305160804170705010f020301141011060c0a030b0a080d030e0606090a020703120c21021201030231020c120304050d0c17 68
    0x104030720031602c0301c0e0341c0103040140303060030074803620441c0548900c0140c82540240c070105c180c19265140039405c000025600034240da2107104507464020f0081804581d0b1b130031901003804128020501c10a01680300f030ba44049551848840558018256045124100d5440d0b403240e900040240702c03400614000d0480c4c01000c1e12000803041080711600c02001c040d42084500c500070710b2440d00004030b26401c071403041c81803680c1e0618000120042d00c4081fa41c3c90300446040b800181fa0703040052141400f4410303544c02c000158a5460303e60f03c8140580b221548400410041600d90700141d00030f06040348281444261151118100001e94415001c0c81010400320421030701062811040c18540141c03202086151500c2c145100780103640601000c1d00600b40310300e041c00600d201040c540d210300d11844c81608103000c1208401c01030750281078201c01d640a03081c10f55540c6007540041e00d0140f40e10201809001c8a2000e04551480b0499016282903940c4050303840140400b07030041a02405902 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 263108390 1250 263107140 263107157
    0x20c010b060a0207050d231005010902120c0a0309050604050a0210030501061b080d1517030a0206150409062306090903120c0c0102031006080115141b030a 68
    0x14116421901a0105240102020404040103550110714081a600304880e0088092103070b080503000790340c0900c001c15031199410180c011108000404c40342c0d00d00c00e150180050303030321416031400340d010380442d240c001e00c06a008508601d0041c1701412800120303160000d030702d94540d121549030817005d403410788040d0002c1518009504103030b8560201c00b0401d040900095150074402885801c0c0c140c030a0024640b94085242001007140c00c603a504100c1705000e0001041a69054812043c2403289020700e0440072001840d41e840030050b03d0520100d50090070403a0380e1140004c1480700c0100d000c56000355105442c0c0c0004030240310724000004005503812510300c01c00c004001602c0050300c0d0301d200c0d201c03800820031a401c00004941d00003004500344002622401030300540360140c21100907013075001200308000309410709400000c50701640e443c3d0215907a10704540060708443d18501e0002400d01601814100c171040090080c41180c0c4000b440001403d6003070741c2960006d940160000d00721b007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 263109640 1250 263108390 263108407
    0x9030d090825030201030f0f0203090f0f0114061003150e010e240d0507080d05070c090614010525030e10080112111906020607090e0403020c060d02040906080102 71
    0x40107044141100d203545010720381a609070402da11070583c4030090405459000030a00c6142e15000083d54901d01c40c0251f4036824190300d4581c440b80c2000c04034009114140c0301c00380c0c50704e05005079410401c5001003400c1c152105400e101101c90564a03c106142d1034080b1766041c02c00c00c10031800140388603a5084169418031500168407840640001101c0690200d0981038010786910f040c9007400441d5071034041c0e4407070315041c1e090a4184e03002e80660b0007280c070074008075034008004110003840303251030440c41c0b9100e100c41e008440560088c0f000d1a06425462011940a04020400f1a034203d541100d510241c004052409520302d10403400601942d01d402514100603102814001c03090404225544c10416002c0034441d00c20340207428800a404500d103e91251240780301c136100211001c8001c81d8580c14003a40d10101601c5400000358002000560320407a11841c900a544c10707406003010103001801c11926411514540f0001076080000240c01c8140d4460807000300b49400001d600c40381e81c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 263110890 1250 263109640 263109643
    0x8100b04060b1e031021120c030206150d3002031e0304140a050c0a0f030b06120c030307051006080a020d060e030910050909010b0a0f1409030d0908 65
    0x2a880103100100c02c1c0b00890310b0100c400030283d0010260346540f5160303074030380103410200c0005601901c5407010046203494404440d02002074020702851070b4524184d5203050465810000020280058111001241ea4108001100c8480c08402070540c1c040940d40d48403500d10f4428106400780703040e44d401d580e11003002c420b03a41e09a800340314006142080c01c07810f09004994003030b0f207626028510000020f07040000b8804202503d54025003116550340c014580b0369031b1b480d9200a240c0c450703035031002e0000350000d5401c20081500e601100281031134903408188541a03481c05d118079205d000300146910181c07010006402c4540c017a4000742070400d6400da950044401c25088808240c00c009000400740c1c40c0c805680c40481c1e0310643c0010b4151400d090b1505500680d844035030712203011100250140e6208000d00702e0140700f211100b401b0390341d41003c51840c0c41750310003420100b08800070004206008464820004040880300c9103445440b4000070b061002d860a06c2002c07504580061054400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 263112140 1250 263110890 263110901
    0x201020d0305010807050d02180106121a01050d05040303060312090905091b0105161b1509180b0102070302030d03050403180513090201051b0714010806060315060408100b04 76
    0x856003002c01c15541000d540984904041c0111402036050080940464807600311091000482202d629440d5840790030080002101c00d0007034010b9820580d503c8210340d821210203140c0d80058540a1408164012a4020300301c0144144c082c903030303107000c00004225000044a030f40b510340d981e841c16007800c2144c11012540060300840482d484444010500c2c44440750701107140c0320074200300da1102954601c1e040f030b520040c04001d11014901300309142c6070001580d00030a03210f01d1600c02c080c4c8400840f040314581114801c0165200520009010900143e482450f00f5501807042d03034041910f0740c012900e0514521001070010381c1d00d6042205066001002e11850082400d03030030841460b020006800d1810003400c154084c2e07540500000b10380c01681190b081e08091040040c40ca100c4e030303440d039842d20044e1003058012072110401c0d4804c1c2d8445c000180c801c0c24018012070541c2c60b03407540305401c264000c40480e013040c0c080001158441041104e141c1d400040800840d0300058001440705454 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 263113390 1250 263112140 263112163
    0x60602072606060f030307061407170708070e0a030c120c08210a030216050c010806031603120509030f010501150e10030c120f0f3801020a1a04020102 66
    0x240d8688001000002003485500003c0c1159070900324219030000900314411524000c08192a040c803500d080c80d1030140c442c0c810075460b00c071f05007003d40c1052820494034046a03081c00040c203580c0040d0800b401041941203640c1e0283c40029401d07100d680f00100d01c41030340c11150808003695659010800d058120001402481010300b410410114100304d03402c02c03246482840c0f0101185405000b803080d8150b58a0943e08401c00c0217465070340c100541ca03803020328500b80c00258210b00059042c2000921000034901000380322001c0c9295844800c6000f02420f02c1e001000020041200d481e0b03810000040790044c40f030000071701c0e0b51604008104581c088884e040c2802010b42481e0f401d0b030740f080d0740c40d5070840d9a42070100e080411090211741c1c15901e004a004503615001451420f103c1d580d00c0001c2d0000c03801d400b04108901228148070011004007924090108005c001c003010300d0341040c401c41c8140600490307210f4541559000180041008190702c5601d034401004150341e03040100b040d203038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 263114640 1250 263113390 263113439
    0x120417030c03040603020a0e0405010b090301050f0115031104030506010e090c0d082a030a050703020f0304050a05010f05160f0605070c020f0409140a03020606191203200106060207 79
    0x410390311641c0b80e00070f078801c0005140d408102c118103035010704800700030403e00400070400c83d038480c4812507481d000018068000e618150002d240e2180105c13011703041e180500241400040740ba102240034111350352480c03c00100c1030000100180b002c10499000e41020210749420f4905050f00380e142185200841e48542e048200c6007011030380c108211045d41954203941100900e0f502171180c4402001c0740000c1c01407000007038040c8020ba1090252403c01d10070360980b810064104080c03643c83c01503000c3c465002c200300208000d550f00070000c1a44c1e0520307a047c0b41e03040c403005180400400410180a542488a2038018000c0000900c6401c2c1d00c841c40f41080b141000b07058003c21001e5050038296809250340351444070071321499111419400040c001110943c00aa19000307450742d4050729428000ca01c2407661038201e401076110329090301c440075409200d0001075141100c10260140c6035406800d22142070175400705080c05240003600310390300140790892410702c040c82e5081c1c2100c640f035100e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 263115890 1250 263114640 263114647
    0x100c33020a05120a092a05010207210309150306150f0828050c0409061d0403030209040209120607080c0721030b10020109170c03120a0b0312041703 65
    0x150050107648012030b00c14500c3d1510340d12284130000410403820b002d01200180c60801c03140703003070030a84030740604904628131400d65694801a41d42c0d14444c081d030308603900c04140b0781500f40c13070503108860748500901d086d0108070b030b035142c084400c81d60700c04100001035102c070f03424802d044130b01d07090b100646081e00d050000b00c0f0307100c00c00034202100a010440c035044d04000408009a035811000034020a37440100702905141c414510b80c0d50040c0f01c2c2c00d85050401c9800110b44003204001c11004504181d080826500c6d95000c4000754440e1480030380c010707030134404000b0315103e43c4907484140c000381c00102054142018054610b5500500210030000200403c00014a55070303192504c110a881010074060f41e00d450540151140d01481c070b401404d414402c580444d81500800300c401d000d14211045c1e041d030180010081d00c07a04a141407a0343c020440b031008090342000d44d0750b01415420001070460104000a401d1a0350a54180c0281d00085000e00000072a40d01409410106d40015481d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 263117140 1250 263115890 263115907
    0x15050f10051e040504140c07030e060c011d01050109110d0e190f060b090c042106020309030310140d0209090f010204060e27010501050717071415010f05100c3302 71
    0x61620501c08c00070108a82030190652544403c0143c03069011150000d200c10054120040c04612001036100510360803d0000151600180700702202c1e004048869072a1003140100c4070090b1810303042241240c030680903000301001512202c504010722594203c000c071102410604c007990841c1d016584180c40c0340040c0050751b022481200c04450368202d003003103881d42e6070510302d0082a070a0000303410f1500000c20801c0318800030000394480d1411000441046444115001609035200116504206e140da01e8001502c4e1140500c1e0b070100786036088400001c100108242641c10a500900109416080e08291440c0080160324009441c08802100300e0000760b0200c2c10201c117204240c18010006046030078042d0340c0c0b8405409042c00b105099032000030b032420199030340000c11100302c14011034480f400b00c408114599812941000203450030a804c14007002044101d880c0603209000d11214420300040c515140d00c003203140080d1030310700c01b0f0f848200700c60705c082009840303880c5140c41040324a030b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 263118390 1250 263117140 263117161
    0x1180e01090c030b041401060311040e070302090901090902090606031302030a08210907030b0711030a090f23060a05090306010311010f02060103150908042715050f10051e04050414 79
    0x3811903aa500c0c1c0801d944a412400ad5003a2241c4d030808081140448100001030780c064004240345502500c00707201c0d583c0c1c1c034840001112403105000b5401480700020070b00c60b02e04000619041090450600a034081c540c0c0064038145540200f200d10080c041400304541251001d0451951141c0603c01b0841c038200307002e217884c2c19440c00005c020324445804904428855281505412100c404132552181e0244000d05651610711032500400782d41040806d18018200e070301502441c085c0e540b0681d0004c442e0421860350080c0740d812003003200600280ca01c03030750100440b034001c2d8040c42c41c0361480c0c124500010b220082c0d0070f00110940d4030280040000998400c641c982c001ea1200000400c0c0d0355924010207948196405084080e050005480d040316010b60f004007041c042010401180c18413982281d0040c0c002c0c070a80d0b6014802c400102401d0402813a0b05004000c1d500d0290300e403525444024010300c524040c81116800c2c0810144101c1c02c06105140e4103a65941002400e487c0c9800b13001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 263119640 1250 263118390 263118431
    0xa05060a1d06120c0a11060a05190b060711030c040f0b030f010e0303041709120607030605031b2206120524130303060e01141906090501180e01090c030b04 68
    0x70130200000100c410f940c1e44145205108600e0940954510f803c0040281020302015603000c0f851950f00d40000e0b000059610404450341405425241420940e44910210740745203202d468050007080081580d50703a45103e03880b1081100d4100060314640001494a00740740c40100e00d1240c0e150414000c1000000025240c2c03051b0b01c5130902040c00c1e00314050b00518050940900c0d000100c5a5031012040300c0803070a180703d041c09581c2048095030316010581e0740c2c600380148250402c81d02d8074440090034101403150120501b100561110a0600301c2c81c402c40741258030042054011001c03800801038280940724102c1c92201c3c1c410841c1c84c2c0c0c00b07884440400060240f0a540c516082d0300001c050081c0c0110004092444611079150796a44c50b001c5a4078481035800e226103400c0d2200412001807400c5c0201751941ca03070300d2611043c101401501d895014980c4190894901100001d190b003105400c5406020f444001007040910780101809a07103000c1c6032030f881035040c04450380810b411300801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 263120890 1250 263119640 263119651
    0x30717060f1017010912110c0a030b0a0f02090d0b270303070e19091b090f09020c0a06020a020304050406091e0c03020403050604050601030201020f060f01090b0a05060a1d0612 77
    0x2032960100ca1601203c4c010030084a004119202803c282a12540c10519164507800510700b80c9030b09460820030000c1100c1e00e808010002ca5050000c1207440d60306a0003c1048100d000005241641c0c00f0000b07027026400310021103145000100300305000e843e14049403a482402c0c0c01425064800c080310507164000141800b040003135000c500d4200350f82d980c0580090f1104519000111070b00c07000e0410107800702465004590f081024086169845103840310201c0302c003003440c2c00c40700c0c2c04c003400c1102039401007100d00f034a4410b811072100030034014801800002c440d5001107075150301e403030b081c0020707a00e030755010240709440e000b05501600c0841480019011081d14000344c07415054038150024001c40c1c01c0035005100e40d0003000208000002c1080c10707603000742c00306e400e1904c501003803a60707640d0708442c6c10340060f94480c0104880304c4103800207800042c000b0808069541c84170b02040a68000c0220500058000151020b0810480d02311140110043d110649000d420700c1014029520107080d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 263122140 1250 263120890 263120909
    0xc090a030b090304061116050f1516030e0d03020c040903020c060d0c0e150901080a020c0a0507030203151015020a0803090604031706010507030c060615120e01090c060c05010b030717060f10 83
    0x8009d0144c2c0d540c441c600058007060050716444243c401c80001080007810021004101d1011418055190800c9440220f41d0b140d80288252002001800041d14000c90201c05600c03800803d0003042e507031400600929035040200040b0301c0c54025002344000440e240281c00384110340030740002c441d40300040b00d00c485028280104141c4400c41010b00030720404205900310300852011408005001c01d511080f24000ca04550300410f2104110000441c10b90341e001f00c1e40031800080089054450000c4545802c0d401514444c1d01a0b44500c000d070b03401200c010b8450380146c0e08000c10990402064140c04901c104044054944200060114402c0c8070000e81806001101242005066001080540402804920001540302001e00741c030310310a00981005090100041003c141441141481da03007141ca040c0c01c0c0c038a0f008041d600d04000281c1a100c0b952280e108460079102040303020001d00c0048a04e0003080e010b072082c9403c101000c0c2012080f900e2503010300c004034040d40b80d02d000766120f940 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 263123390 1250 263122140 263122159
    0x50705100804060507090f180f0509030304030c15360803061c0503040605120109020a050d0903030b09040b06131a0402301006050307080c090a030b09030406111605 72
    0x1010b40f00000c1c13660041c8809500800007040780c4813050700c2301e580740b40b13160414001420300e0080c4e00c09441c02101c01a1455000f40300003804280700d101401c6515018400c0015145244204001a07954000c61060507001c03400403484800345820413159204c400b4040d00d00f080246030380e11017052001508140c461010264100034014610f64450b0b400782d408021a030307807166210350140c13660300b00285002003085d05400000c4d00315154000c8030300705440c65480c42d1070f140c045015940204048441501056990745d80400d80b512416035443c0079501031000c07102d03680740c54070421600c90342952500d840b0758241001e1598030342c0b0000303884900c124100c1e4003680b40c84400c140d103503107074900c01c03042d0a160b100c844c40c403a100c0c001041964021242a558942c200d0b40310001030b540ba01c42551101c00142460000440303481101000e400d41040061031910030030307942d4841c000d00b84020740341034101e5080003400300f2202d50000000385040d041c440207440100b440560440301c2c01510310a0900400c02407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 263124640 1250 263123390 263123401
    0x20102150907050604090c030501120c03030309030c020301021c0b190510230703020715021908041a1801080c120c0f04090c020c061e0904091208040507051008040605 73
    0x7840b181001d88009000c0d0f0361219600c122100240c40303020701c4000420301e00341c001300b1030011080310060410313009040350080d83d1035036508800400040038250204010303560204010f0340c003070005146111040c0c1b211681500d802c07002c00102c81a40b01058070072504030700701c0d4500c12980d1040e28200c900c01c4412003280f9030300e21004e440b1030300740e03900c46420111035007140c2e03a1641080000d807008074000d03400c443c10340c4c0d02c40c07120516902c0300940702c1e40980c0c868000032039403e0078201440a9148101680b5040681e900c100710001080302c42105007124005c5001c0340c0342c4800c2d6449012911007403a0440050802146401d420f2150070044a10350401c40001000a0012030072680702c04520b2007615078507540c07070204000422000c1640d41c0140100c1e4845481460003e0503940c280040140001c0d0000440c0048560790744000c3e030b260b401c603480d04070b13100200742408104034400c90582c449180360310700b03441d04c54241481c2d604064451440040b1269146520104003035000e42e01810004d115100c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 263125890 1250 263124640 263124643
    0x51c030804021908060f09030f0412060b10020d03050901140f04050106051c02030f1c05070c03150e0601080f0607050d0902090a060f06051c1e0f06030209060d0201021509 75
    0x102d8541d019007500440005029280000c506200d0752691411b01da10b42c07a42c0803810345072300c0341c5e405180004109220500009a100c07031008040d603c02c0e000024062030810205190100c050200030150f040a0780c0c030100306415000d41c640c0100400c00030002c10000141d0317511900000303407d035654201204000780c2000401d42c411303070141000a00306040103440c120900001888060120301a0198030483c40041c1c00c0000c020f4092008994600714030780d41d000040300e040d0880841a1443d400b01913001010801c01c03011002c005900e5100441c0010b25a032480385404d01c180d1040e0080e43c41215400d45155020603100c3c0c011405180060f80c0c4c0151314003080103882c590368041e50280c03607041840306c0307406240e01c844220345010341111030325070341d44400340c40394000c0700104280400c1a41d21207008109a80c411603925a40b1041101c030320011801c840e08540b521282c811042e581c07002c0510651070311401c82a84504210b9044050302602d500007903e030b60491003a002103441980116840303000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 263127140 1250 263125890 263125909
    0x51902090904110a1a0403121805130f0510210804030204020d020715050a05070c030207050603091c020c03060a09020d1106090303180f0604031a0907050409110406051c03080402 78
    0xf2120702c0c14000850039072421121b9100740b10490341c02203a0000c20201d00c0c02024016051402114001c0000e4900010300c01b180d03007840385140c3d100d551501030261000862244501515100c400e41d00c90a003441e00c03200100070b40c4454415040e10070035842c0700042500b011501aa641a90056120080201901c0c068015840000d08680d03007000072550940d07560b4420340c440c91800d6014441c81c0c8403a0003e650080300c001001c0c0042c2c001c400203003e0b07408d00c10025500442d25400f04d41140d05620008905203501d0216140140c0084580c00403038507013003240301d0700415410360070084c80c407440c0c2c001144003001d048010900040e2a28400380b07540d4000964956260140c1500d540395407039501c100500d1000215035105142007620143c0900f4500c0680e41500d502c945c8002c030405400c9030040d4052001070036600544900040818140c543e40a80c2c805148525901e4204152481c1080305550381a04114005c80905c0100144002c190003d19009034040c10804656265800812144003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 263128390 1250 263127140 263127149
    0x11d09070909060f02192a03050c150403020a0b072d14040b0d150302090609130f030908060f0403090b090303040e01030c05030d0c020607060e0312040303051902090904110a 76
    0x2172000c2600b0701c05106005c0e10010011b1590b60701d45d10b0f180f050380c4001402200c58290a80f807615502d2280c0000c1c002c81c001c01000d0303086001c0703a041c90710a0660f0499500100d41c110010b80101c441c0c0030402c40c04d0100300f60815102d0030103081c044480352880002c600d4250040484666541c1c2c1071000c03c0c05055003803032045c140038107550788680324215240c6a5001d111070300321951400d01c00300051004095104107a9500a0024905855007000c00c08010400740c052540012051290400505900b1101341031a2081d16941021440d1100e403504103d40200a0305245030540e04003c0000c1e4415080c60561b040c0724481619580000080b034035500540e0007411000c03a00200210620002101c0c180466604600301c034242c0c1c5011408650f0050a0350000f500140184900c4000807100c1e080005412001c40c00c60b130810002c1e665110b0140302c1900d060f008079540b001406041d080e500d13180c82c0f000d01d440d20154500024032000c14800d0308018030140c19000704910350a0141e40e0301070250000c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 263129496 1106 263128390 263128421
    0x3090d03110d2c06060a060f0210020f04050405100f051008011224050103020a080309030a140703020307141305190c0e0315011d0907090906 62
    0x41c480303100301c00941c000307500402140081d0f80b126001075074014030003042681172010920050313560a13002901000940d5034111000c0360000b54038203040c5c0119400695801040c0d8120200b4011600210751080c240b40a000d0070743c00c0710b14403105030343c0c24441007032166507228100046940450000008a6404030041050744400441c55204500404100d8240d085c101d20303002650b00201644002c941c1e032a0014000d42c2004862360014080788070085107040428000659156503101d00207019a0700e000441030644020710604c8011940542201d00c4a0746940500303000c007200c420790f00e0003805005211118500940038a5024160280301d41c1d008156101c140c1000e0280000000d081c041030035000d22040d00c04000c520900c59a424003092654100100305221242401040071071086a0050103030100b004900802221070b0302d02c0010341e013900f030f2400d4005440c0e81640e00b200c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 262949640 263129496 := by
  have h0 := BRFrame.cov_init 262949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 262949640 ≤ n) (h2 : n < 263129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
