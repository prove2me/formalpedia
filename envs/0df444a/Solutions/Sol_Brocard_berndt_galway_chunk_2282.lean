-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2282
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:14:00.407426+00:00
-- url     : https://prove2.me/submissions/4a9277d7-d4f2-48e9-9cad-56d13bc65d13

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 410251798 ≤ n < 410431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 410253048 1250 410251798 410251817
    0xf181b050901271b02160803040803120402010302130915090504022110020a03021e0f19170f1b270d0516090b040b10030e1f0903 57
    0x5141c00700d003540c12543c10a007100034010b03584681c26880c005149041d032046541d484800c043c10054044003000c6035043e8007400ea150740c180da203078445420507000240194005e00007407001410010445a001c8009000100150741e07901c01200a48503410044c10020414540025609295004603c80e50b08010541c0c0e1495101c00c8070204451003220042d40c008550380142440b01d28800040f1260340b1194107460703400c4a141110005d0782e0140603d4030019500083c01e40c080c3d07241c0a4001c00756104040198a8554120740100039401000f0000f400c0720700c0940001d80903400792080745260082001c11f0070303280c505004030b100501022520350310301044059075402c2900341c25048074802c12610b000100004144c00760030301c50800a442c440d401c00c00c8008a81c010590811211051820403c0106d01180c00d0240440507104042c120310301032418a1460a0b0310b0380c580541c1d551089a0303280c0082c3d6480030040b180d00c0c1080580d0b10070320070302c48407201108482c10340d04142c102c46e0103500d40074541c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 410254298 1250 410253048 410253059
    0x9030903260f16170c190c031403040f03110108060103060f06031d2e050408030109020a0c14060105120c0303070209041a0739060f181b 60
    0x210540d0110590303032481c00c005085202441c0d101820b182d1480b11045101041c40b40c0d25802810410320369a0031a0b0804200014442c10800003600074017401d028041d25140295600707000300c02507010040220940e00d20361980d280041003903c00070b00340f031601c24400c66500e0500c0000f40d22800400c43c009202c4c20300055030b5500038090385085032517403070022042d545040700460040124803100d181c50703140c0c007503000c080140800450b02030300f0b42d8034002d440207200e901d0000900c80350f008140c1c80160401040101084510080d681100e001820250365054469021030340b281500800900c1e0920380034440b41c0c840760010322281680e000303032948204401d8412b5083e9440d06881f0301c966142c0e1040000c900107090620486400c00d2081c00c0884e244c2011503088461114101c1d050f00001e050f4608a0095401d00066a10150183c0c0350076540205404203840003010300e0803000d000241c940c0020208807560343e11070510805000039404a0800c140340c22071a07442c4441c80d201ca11800038201140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 410255548 1250 410254298 410254343
    0x6060611150601140c100605180609040f060903080601020601120203070302042406031a090103050a02010809101a0a050301050c16230d12110f0c1009030903 69
    0x84100d8440300030040c08071140c000350421880100501d040245400040307080894000241c444400c121024000e00b00501900d50210350650f4007941c8a02420842c03c104ea904101c1200c0c1c0100068440074407072f544a040c03101d291a41c0c0301c40204480e02e003151034024591300144850191100742d00340c40c01d99a0b0f40364080244c1070070b50f1001e503168100701c404100601d4158081041440080f0800d120000c0381708030741c00181c40070b610000110780c0b1000001e14851007030441782d4040d11304403100555541543c0703549940b80c0883c43c0003818801e17500c4c0440c8401ca01048440d8031030700c00d00c1092161516115000c4a800030404200e8024a120440405e4500d0107004113032040000484143c10a070b207002058504c3c40007000196a104002480c040b06070b20b03440507000c20400000000c02d0400000ca000400390010110524002c0d4070b48910500002d070284125a65076042c6202d2070f0b1201244841140ac2180c00e841d8000305514050701942015000000b90040700d005800d1894000c551620103030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 410256798 1250 410255548 410255567
    0x711120c03040b161e05010c090b03220c1202120a0b16030b13230402060414030c04060f03050609010b01050403061107050a080d0e07030203060a0c1701060903060606 73
    0x1d410070b20041c000ba2001c00003415811000e144190108030b00c40e00d41c025203205d2a01d019080c28032816448040c880c09015042c0c20060038a00341b000e4a2404140031030304d000140c603445c203e07001d0b445000b1b060000034419805075500100c0c107144040d0380741d40d00c00105d112118109d00030302d10018429030070400440c0d07144490381c1000c083d451a9440c00b0003081c002c400a1071540078550341e94070f120141d44846d504005000300f420b00010f815042c00c2e150580c60f0145201841d10840b1100401005803615800d41d0200c0c1c03002c1d070b440820640000006814032010000180d04140390941c00100761480e410303080200c0340548196200c40d1202105142640d8040d040c0c00c0c0400c80400081001071455031228424005211045080403010750f1410b00b080348600040da010000428030048031040c1e4030591506210000007000401d2071540403e440b99030080103c585030b5a01c0b803050716020b001e100302842051004001c0030956841d100d0103014944280001c0d1501da14000b80807c0d0907000f602c03001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 410258048 1250 410256798 410256817
    0x9060806010e1e31090c030f0506010e090d0210050c0403140c01030e07140112020403051608100b090c03270a060c080903030a0f0b0d030201020d0c05041a130e071112 73
    0x26030f00d0135600300080060301d1044400c86805600d030f0400000304240c0d08c014200b0b03500c1403001d041c0035494880d0360700c07046d28041e0100445030400c084080700141c000807034010000c0c080d2804100c81c0c0d00c1c1c80d80c2c14258051540080c1403c01902c2ca08050a0740c003207281001e1103401d890800a075054186411b035680c07228010b00c01d4600482481800c00e40c0640c002c40a400c80081d03016103440d0712542c1e600e050040c810403103070f00403110134814010f50300144000b4403003000b0084100710681c542c1c4005600920060090407a401000001c039440c84072042e90303441d56016040d846a07a40341e01307880c500d03070350b074007030103040e1011032404598580d014401c4103030900030070401c8000d5080d5200c0c020180010410104c4124295507140040d040d03944a070440c0e000e82600179000141c0351030004030a8001d440540d4107450412400b00001d0010b111800c2c9038183c072881c0c3e82c2142d40c41d096107078000914028140c112050918008080004080e8030000b140e90610110b000c3d1020720f0540d080549a5009000c3ca0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 410259298 1250 410258048 410258119
    0x60207050d08010810020c0307080711090703020a0212131205060a0f090f060c030603020a120b0c041a0f0c0a0605041103062502011b0f081609060806010e1e 69
    0xb51700c0d102c01960054a42d410f0486c1c00d4070b161a000c0da507900c2c0d075503214801c1220240c0c600382e01030400d07241441c116136001740c2904056181600340c480003034803401c1481c0781e514220000310740c81d4840a441d1b4008005022501760114547d81907050050b903d8400b21039075a0580d04010302c0040e426480d0240c145c6d000e5120024100703c000c0c9954140c080c0449400000c2003641d038820000150362072081190081481c00148403c41d441400c1c2101303c040020f0101c0d0031000c007040b04005220b460010781c40c240c50041c0e010343d203d11094103d0b009030310407401c0401003403288039044030a000e0b0f20751189008600c240604a118080d0000f415100c00c03040324209103118a00422122403a0114804524800e46200003d00800c1c0301416202c940007030036007000050300ea201c25080b07043d04240038540044181100c014811500c803402003500e8814090710b001c001000011800e203900580081011b940001c02029100319000800365000c0101d40d03100b48981c0380300a0003040081d40c2c502c060b020380c641011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 410260548 1250 410259298 410259313
    0x51e060106030908180d06050c0c010c180b07080c0f010213050d03170a02090409110f1c020d0611070501270f11060909070c1205040501021c0912060207050d080108 72
    0x429441040705c161506410081d408210b00001780213105180c803500e4003012260b220b078450080d460848002c0d07160041404060300c002c1c3e0000e4254501c0204403111035004a544100394905003c4030b0240d016a4940c80c824030240c100346900640180c9036800040716106c440b00d65403002c200b04407001d0000900810707040100114800e2101c201d00d039001141850141c0341c10070200214044075118071081d034580c84141c8501a0354500300782c0840505900f2a46110030030505482084180b000c074030000d10402082e1908410010160000c4d846207401c0300c00300c1e4a640a508015000c2d00020f00c07000e500c0200d21080d02070700c00849010880041d0440806c0d01c0c04005641e030100b501e0500d00d00d650f80301009002c0d142d00fa540e6060352902c5103085507103c001041091400c24205290036403000c0c1031100a00050003242d0b400030311083d2100c14048490308a10082005580c0300115070401700c10344510101d01c0c0305100c840d80003810501e01c0742084940e043c84409003158042c0d8203005503e841d400000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 410261798 1250 410260548 410260567
    0x60d051f0b030a1a0a18050a0527071a070b090714240412050f03070305030411010c05060718150c15061809060b01170a18051e060106030908 62
    0xa111030b0007200c0404248013900100782c0021407000c10b0342d0090092110300c40b801d09040d00b070760103165044001c56009104a080c0010207841c1d0742c0610070300b0719848917a80303c0280110010403028000342804004130340c0d00702000c6120360450b4400e100c140d840d080f4000100d856540700058420881d600d03010912041c000d01010490b420251508a03a54104405120005104008002c1c001084108001e034180701c107601d006410640c015040040300d07003003071040e400440e811a04603039100ea40a4281651224445c0042e1003d504440000d007803841000104242142c20900501102500f5180101110740d070743c403c681591406c286200024103640308010000e00c2d8072840c601c0041c4101c1b004144c05807070348001181480480c60540304c8039265400711080c07050300d200d60381131064280391020f54182496403003100c02d14041c25102419646001841c000b00d001c05400c560f0503409030986507c0700c009940b0f040340321040b2a080000e4090240000b8400740280b040650042e80910310307905002808 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 410263048 1250 410261798 410261801
    0x2010c09082104090e0607020d0c050706081e07110714061e040e07090306051531020f04060305160c030e12010c0305090d05091c050309060d051f0b030a 67
    0x80c4602c0d00750080c8070108038960140500d816600c86400208224908001c00900d4500c2504074803081c031140d0440080032a00c085482c80a0761003a080c16402d646410700a503038104115050b0301d00d4142018240310149910242040c0c2c1403209130116541c450311001c9415901c00c070950071a40c007190030481c0c1d10f08504815140c00b020b0980c1341800c0e007419a00c1128130700c03150341114014009049880107004204180c41500c0d00200142950081301031003074045a04420003144803001e440030040c07600d500d03d1207030068800695001109540703480c4030000c082451341090150700c0105e4104070003d454141c040c081d610500c50f15568403064629140c40c141d1741c42c00d00d400130340c0d00020012200100d450090194101c1440305540004061074280620380c100b04180342103c0400c02d0800180c070b025030f1a800ca0f5020384162480041e000c039090315000f0b02e94030840700081d4121002288200030003401e6407166110b1004e1841c071040c2e950b110824641d258a850084500007107003031000c10b015044a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 410264298 1250 410263048 410263093
    0x6040606020c0925020f01051620070807030b041202010902030a0b0703090f1506050603070f05030903120c1b1f0b01020c090a0c090b1806071a0709030302010c0908 72
    0x30060f11070000038181d540040c0181c00c403070400c4c050703401811341800043c024820a940503201071280d213101da0441e800285259000c000c8078103c1c40e030001110100c110b05100c0000140300740e00071242840e0f40c0b03243c00031031001c0440f41a00c0c510140164803107800c0c018018070840d694010060700a42203e540c4e6440c0d0303041e000d02410101599022480300041c480c0401c6c60701e050050040308441034800c94010180d40142e0082c6000d40703014010b000556800a803400d144000b80d0400720380781c0e691401d859145000b032004a0140446000501c500c2d8203e9100420423416154030000240480c40c3d1010341d02c1502081440c40514042d104e1030210070306510241c10480140b0680d9481d4141c0d00000340c840c00241c0380d4004056031b50b14120001034100d449540102038803010281450300b40c048044a4510303011115000703017000241e1908000952981010a140c0700750103540380c1c103001900070000c0751140802c0b4059840e002e503055855003c1c500042c12140d800c4014220b0030056506841c48607503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 410265548 1250 410264298 410264311
    0x1407060f11011b050306120a0c05120309060409020a08010602030a080a09030c0204140a0c02190803090a0c0602010b040c0509090622051501170108030d05101d0f06040606020c09 78
    0x140d0380d0034140110515500c41d80ca42101e660713400d849052000401a228007007844102c90769210550310000201841c00440c1100c07070032210395149800702c4040d0f40c191300c81c0300c00c103d5001c2c42c0013a01141e01300007603020303008440165580795000d0303803250fa06a90701d10a00d01d1200110344140d0028411502d15007050f00303014031a1524070008030540c7d002c01d0035240002d00c0d042c1c4181c4124200829540e140c8151610559244002c02503046800c60001c100c20681c2d00141043c0000000107141d0314007000611601648a9a02c055250b40d8181c001d00900c0c030042c0880c07156041800b043d440c00d101c0d40070303200c035400300602e1460a51195410031000c507e408185030000d00710394000365542141f87c881d40c2d2162000047c19801c54440c0c2000520014400351041e10401841e001803003002e200001b1b407070b03103802c0c1c10b240013845403a1211944214211940003000706241456840c1c036000702d00c2103040c02160011403180f01d60301d03650104404e076003217405030a0059100301a042c2d040d01e004040c1c40d40003203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 410266798 1250 410265548 410265551
    0x10050906071b0303110d140604020901050d0506030c03120301030c0b25020a09060801020c01050606160303150b0a020d110d12090c0902072604060e0105092b1407060f1101 75
    0x1c5c94142100015080140b01c003140540e41c06030451041400103085500c98000c80c0d0031841c224421002902c140203c8240b258015035a0303000a6064804001c0c409808070003e040f22080c45641c030315020aa4000d0100319181210b4940016210381102d0a42d0f03c2191510014510745902c94103541e051449103800ba6400071100100151004051080c2c2d805003071000001b503540d01040c20010b095810240106000720300800603000804c014803149842160b0501d8080f41100701039060004a0915420049041d400040c0351000c4540005401044221a460741c80138148078400c01e948884420725400c010407250465070300c070141598048100a8405d020a550090303c4a00c26012a00300b420200d0b1244003600c0da03206010b00c0e0182154116682c03816092401d070030200000e1000028800e56818000d000c201d03081c80da03403602154400b909810309411920442040b55284842060000b9211907642a81030744040e9400302d4400180d55090b1124403803207056440c110b940c4640041115a40d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 410268048 1250 410266798 410266811
    0x20190303050a0e21060c03060603010e1801020a0924080c2506091a1005040218030a050106060906050f090d0f05010c09030c050402030403020c090703020705010e10050906071b0303 79
    0x6949907120801c050341901c0148602c0d0b44c443c0162803602ca0085c140b04a103401c1401003000c42e0341c0e04801c9905460010b100c0b201e251320755400c4546141060010046503500200d0101d2100c1e5000c05418120b522012402103214205000c0903100f240f040c06007400141804005200106888020492800342a8108074580c200003105100c806040600320766150316560a9414030034500d4002c55402d1403c010050a801c041f02c03180c8980c1d210b032051901554000c038418611310300404204104840c0541034480d040380c01d24041d4003c05103809158045078a100000c140c1ca44a0026175081b9017507144c80c249440b0303004041141e00040b507902251000c8081501c4c3e40000d00a002c1c0908580c0e06803102659681186080070040c1240d4101c14021072040c0204004641d001840b2076072554180e400700011348503002c0440103841340302005001582090701900d20501c0000f43c03401060003d0408014a4550300300c801d4488006698502c0020f024061640d4040d220520380b880451184c200010007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 410269298 1250 410268048 410268077
    0x120f0e191a0d0b10021005060f0402030f0708131527050d02011811190f080a050c01020c030d081f150e01050a020a17130320190303050a 60
    0x10405076a441c50407210340810002c0d0310034414003920942d0403040342c602c1200c080c8804025a241075455032502e0a903100c0780400c480f61244074241407030980241c0b0035562894000343c141244001038542500060900b800140200d0319240d1491605c1d07800501d018181140781480000f030320040c45000250341e0013110000381004000102501c10303103da4082c046482102c1000303400c48110260181800c081203901c04002a0058440d4800ca04121140300c0e825052000c5200c0d540343e660005201c4002e06800850140c200052b4040543d2041e03040ba215184140c1c01240c031000c0309075415030580d03c069801003109008000060380801d04002042d85210040500381c42d08605601c000c240b03440c5030141b1000ba03640a400c4008141003802c24070702c3e0904000009595441201000d40700700307045200d5148641011044600820300e581200070166280c0c10680500c0c0c10380c6030104900c02105000364644d052584c2070440e440c441c003c9030705d46503246403000e43d481c0d0700171101c840c05c0040d41c07148080c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 410270548 1250 410269298 410269319
    0x6012102120102070f0605100b04061809110706050c0c030405151c090312110910030e070b04171212130210020c03070801050c040603090302030c030a0804120f0e19 72
    0x11441c00380401045c0c0e846903080c202c04a0b10041e0803041c81d0b0b42d20032014071000d00b90300e049404603085450a5100c611550300038102c2da1000381c0015283c02d082001c8400c55400403c040c0a8150084004020b0760f01d640344140c4080c40313245102c040030703041404200020f00c0c1c800000208002025400341c42c1900101803044480701c025914031810b540c512800050645c400d000010b841012032003040108062a1021034900505036442d1180c9520320001310651310a0700316200050080702100c414be502c0b0b01c0012203a40013405a03035066a060038202032010340004103448001d1480035460f142c030f49100c00d581d021000081c040c42900521045100040c0c0b900740c10078224186940c045c01c0c4046c555420942801110380c0035508503030600051001981c0359030b08840454074281400a0804c615140990550141c0d50380d2104a001c04202400096000009188154410001400d544690882c10f5070110090181000054610b03035a4841e40d0615500c103518201002d49244500340e41c0715100320 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 410271798 1250 410270548 410270557
    0x60a020a0c080a031d030604020907120614030c01090e010509070306150306150e010207050d020a0806010608060f06040b031b0c0109061a040c02100903140318060906012102120102 79
    0x121a8800d01603d820b15501016211007100714908416181540c4030010342d072440c003d00042e22881011000c6130100b8080c0c0b00204c9040406c02050101d503170b41d18848034105151407041c5000313006610007403c5941c0701d01a1076080e24045441200c540c3d0805081c400c00d440001e02c2403051503940c4002080003240744c20080600c810795034010422034240100700c0e13039118159481d0b00900c525280c0c1c0b02c1c0141e8000c03d4220036500103440c4900395242500000c3c40200f2a580101c465010300d00c0082002584210860300c50981500c1080610409006100d1980f0851040200b0783c502480820948460720505030300340c2c4488d900450510001a801c1800c40d0040c4408640235560350840003550726826000002004089408000308840c45c40060346429420035556080c81c1e0f1524028100f42c00781c0a010300c0001d0002d6002d032603261224850a5049480004946c50700c18030b00040c0e01480c0008900d4145c03603024038810b0000807110140c032515030303640030100d030311a0040001c0031082e402480900f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 410273048 1250 410271798 410271809
    0x2010b0a0e0402010f0806030c0d1b17121c05060f040e03041e03020105031f0306060e19060f0b07111e150901020d050309011b09091811060a020a0c 65
    0x14441ca06040c030024002501c00c01030700c01030103101400c001080e540480c0d200d50442054132a801c1810041c40c0200c000402d61401d10b482d044046004aa807404181101c280780100504958001450100360919801100304c402061800070f1080b01814101d0b0300041d4000c40040c00c14171402c0c3c44000040c00751198211000c103190b0001c1020081c1d26251070040800104404e1200810780c00c6800007411848000c0c20070074403c6c110100c4004a9083c2e4924000864001004200064580000c661400d400707882c8410703008c1100703203948901c40240c400e10003200c04084400e0030391854013a0104164009172420754420b10180f280c0d07445900d5248006810400c04948075120101c440c003003003003902041207152612001031203040980e0b6000103215078082c520342040354880d030701c028070706014005505680d00815407000100c0c901c40c0d007080e0000245c42c140c0030b0a00c05a10004054402d482c00d00c24090310300042e12841082c5410007400810301c94441d13105603290524039407109801d010b480e6108 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 410274298 1250 410273048 410273069
    0x611100e0f07061e05070f060e011d011a10020f0303180706180e04020f0d05010b010207120230030304050a1109190b040b0d0c090605150703030c02010b0a 68
    0x90042804090060030b016141d04d007002a00d08101812501a6803850079007803080c4800004c45500707102d8020840c90800d41d00c0f800070f01c4075082055003240a0641c0740d584040d55018171005502e0000180230b110405840360381d204031546071a604210311000b080d204030041d4040d0005400682c0b0003403000310b1049489050000003080101085c516060312584441c1c200001800c0001080e01420340b014225013440c1c142000700e489500000c0c0d40100c2140c00d07aa8003e012110311360130003106407c144c101d00826001e44250554401a011250b441618025444140300c5444038003002c2102d01541ea80344241c0b04414080000d203606403441c4e20a8400741c0f941c2e40f000c1d203e40100243c514840403a100161558811810141c0404820b0200c60060616684d11050081401d07100c66000400380900180b154440c140e460031700104840003070003202d004074140b480106503401c0c9401c48000b410480161180750030069201140201528902c3d0030071035403170394028082c1c0d90307076100100701030050b1611 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 410275548 1250 410274298 410274313
    0x1140606121906271b230712180f060309060e060702060a2702060a030b030d090e0108031e0c010b062b05061e0a03060e06060112090c0611100e 63
    0xc185240d9210002c2034101908114203203c829109988201030b11285060a851b00d034561040d200c50300d03040c0d480c4422004000703d018401e002000b000016040066150380010103c1c1c1610040300d0002802084e403207041d5000c0c100f0605120b43d07c50705905014190006000e4005c0c6035141c28100c09681c0c50005a1180061000e802458450b0752290071910340d8030601c284081e170515036802c110f0308d002791041101203103c003001e500030f0300000c40007407004094500030b030300049000e0b08400d800e01940b60111445000440d01150020849003042c0b1008083d410310003680000c0c02950b84800d01c0c2003075954984580304c6082d00c0e4003000c0c1245901c0c0e2640c18130944401c490340395444960095480d1100d007800d0a000c0a91140c0c000301c524002d0a84119003100d24000105035603403119440208002d04d01746016024000c00b02d81540203400076070715460415828040036003910001c101c007410003024242c08101d440d01501c42e400d6101c24490540301840004110700044403071959822100e0f81050a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 410276798 1250 410275548 410275589
    0xa0b1e120411150304051b01030905010f0c030b0a0503030f0717040b070b06012d022104030c0f030317180a03030504020103050702120d1503020a061101140606121906 73
    0x424102d1000c0c180e42d01500f145000c2d00d8559076248071f410b041c0c4460400712801c0c9030300d074400e030480299150080700a105004506142000030f144194511b0002403a1400d60320751464500e5840e42182c90040056043c20360305d90015a00d0f500c00365044500841040c4040400d013442d401510040003103a25582d04d41c01141026410420002e14040c1000340c80301d04020480510725880110383c03810314440b0302c0b04418440c01c1c0d180500c01107280c001003d01002e4004c09451000c014015244640f682c82c50040d0b0b00c4149000c003100302e0000901140003180089441c1800032407c45d4441b01c05001051030b00da032140228240b1030860700980000352103804000039941c15025540d0440220303c0240624038600c070321103c190040d200d00d0007501c0e40314042c0201c0d540c0b020b6018000307941c0040001c81c08a65540c00076040d0090200040e03695400c5c1040e216000107018006441488007501c9646080344442010707030b10650040110b9440c090030030b8103031400e80700b0307100c0c03d0003802011050404516921 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 410278048 1250 410276798 410276809
    0x90a06051c0803160e1206010302190b0a0c240203181b1c02030609070305060604020a050a030e070e160305130f0212031c0b0108060a0b1e120411 64
    0x90040200120301c0018401c0041d40c0e16040b01d82c050301c07034000282688202101283c02c0d14007482c0e003503842000009a020700b82c4d00415a68100c1c0d10803601d00884122081e920800281a40304042054600740915030100340968258000c061141da9051701e00da01403651003242010845001c00125801f00803c030741140c2000b0301b214052480b80090a00344e962400392141c110081c100c4a01461200402200303c186401840b8200350b40101642c0c0d0798940956480e80e5a100c91000f03650503c60b1030046041414248200c1d1964129035030380915254501e801a0040c2408a0908020744075206000641d007280506160251810034514400c1309480312005066a00c09404422089600e28aa100144c911b240344440340383d041c1c40d080814074040380500c1c1580510310340b00d010260000d03421507011b43d6680c0412100102600c0316007040c0c032841d040c03081d450381c00e0044010b800002c10070120007200740c0d1300c074a603205903000b0318912304512040794503050b04041c0d130100ca41408000749104180780c038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 410279298 1250 410278048 410278069
    0x170709180e0c0d150c050333040507180605090f031f0902011b0804051e0d08090a050310140c0304050303040807061107110f0d0809130b090a0605 64
    0x1041418414030805151854485a80b0240c02d80304075264080c2908104800894110485048004004001c52110080c0c03496000720350f0300002140000c10710607007095541c50039600c0b896002c02502c081c10104244002050090b1071a02407040340303802d90340a544184944000340c441d954489484816000c188030001103400c2c0d015120f038001c03210340c11607280c04e040000140b005550b8013065031007072400142c81c0c210042c94580d200d0f58000800302c007403002d03000c000c0003118001e580c200100d5403008940c2154106002d0078076401780709056040302046501e0058030035214020100d40f90a40d4900000b40b80100b5103410207542a1542525030711140b111000c50380c4403010190951031481d103692466103a100051000b0a43c1b8004550314052010310b80c0408000c41c0c4d0003010071390b03964017414042d02a10a07030240d244506901d074122401810300b00540814035500000583c01c0c510020104108002c2030340402003050350314204069070f5940c4100700d41c000e4803113100c0042e40a0a04040c002500790 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 410280548 1250 410279298 410279339
    0xf0903190510060602100c03180605060901050105030c030609090f1905060a060501051b031201080609120c0d03051f15030b030c0901140f10020c01031b0c02060a170709 74
    0x14105082160759000305420200e006a800001440b1005540c258000d05086040d41c507100c903002027201c00c02c40d42d41d018034003030101140c81000f660b0340d800045541c0e100441c0e00c046019000e002082c100c0c01c1c071102c41a0042c0e2402c00741c1d01850790081c0510301d01a555500540710341c3d0b100442000744202409641d8120759040800c5c0510360400300080d24510440050000f40b4260144a04803400c052094500034000c104e054007103035035151324a0b5038455040d200b1241c2801800c90000002003890204d40286002c600500f02d18040d4480640050500074100c649042c04070400d0500d120307140c0b401c00c004d040c0c2611711307992804162030004d0894440e1002540698045a80b19859680781250141107911010f03440c4c442c80c81340750104038122081d9111640000301102c8c4000c040340c0104400380c81c04000c0c0c1c0c0800180368040c201014440c0701c0c181c0071000c07417805200c0a001d420300c48004c0082d000e0314100703400d000306040c1c0c10160703012080b079207040043d00c0010144582c80440505070407120 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 410281798 1250 410280548 410280551
    0x90c0a050a06080f071803080d0b031f020a0905060c070f080309090a0b06090d120311070803010512120d060e0a09030906030e010902031005060a05031f020f0903190510 74
    0x60500c02c0180a402000d8070041c1214903100018400c0c9102e0241d80c10718400c0034a8007030601c0d5803490f0940081c6c001d22000783c05a410f14400142030304000603200c0402207004200c2402c410404101d80080d4003142079101003283d11480400c05403a40c0c07004001e4045110020421203160842e40c1c1d0464080d5041b929881e0020007030364030382c0d54506803001e4201c0305ca0a4002401e4581100144140c41404e4070316822411200d10304043c4001c403089a41700c034610380c40c28031a07141411a0707103e66206000e402030400d1003d2005021030304180d4a03003038450415000301c0750f00001c451440314080d00101c5101000645460050150184402015810032000e131030a11100e001c56030080c10500c49806400e08050342c8182c0c486a00d1750940001983c50703000390070f441d80840c19240400151000700c3c0c203540a00348104c4001010306000681011071082000b201031b90030504811503010b54416050401402018448442c042d80d00340300c40710781244180ad0b410481080d61822500b8855001028400607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 410283048 1250 410281798 410281819
    0x207030b0606032212110c01090308090d0c1502120a1d01021f050f090a020604060e3d0315060507020619090612090218060315090c0a05 60
    0x120556005900803030211041e64603a0795203801000c0d4021001030038210304222003218401c1c031a640e01780c0b44000d00d9941d1000400720a16a51507600c1784420000d50000341424420400b00351000050100810000e08110206440b0345600e01007000a40020040000d140380c14042e994042100036000c0a818003820f08000d61401d0140200380c07842507883c03200040c058600401e03842032122812754038594101c10010403080c4030081c021300080315244d41010080c800728482c04400955800221343c0200028682410510101c41d10f1020080d44c5c0e4002d00700300d04080e030101c00858050000b5a42d1a40c200c00c103a000841609210100201c0c0d01c240f61500c01400c00f0340c1480d0705080151496030038180d54500045c8003141107481090344813809085040c040f1180b036030b8400020710031110581d07240f81824924a0b0b0700d90441e92a406c00035072110001c0b404841042c210480f290f40300310001e0544a800900c00140d010803001103a581c00c050b041805c5d440007919259400401030081580c094020307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 410284298 1250 410283048 410283053
    0x15151d0307030f140a05010507030609060e090a080c0f030403110f0f0a121e03080f0c18040504060e06090c1e0a03020909100c3501090b010c06060f090507020703 71
    0x280e0710f03c2a000380442150948100d400d000c00c1211915560b17002c4020015454600b4009000b0040d5000e0000524140a00010b03c030aa080c642030042c202d4001605284440e40d484980c107074032000e090301c0c1501400c03c075115029420300240c401907000d1600a006141001c00b081803400721101c4052140c0d03465860380758261994009901030f504d103110301e404082e280e81003a805600070442c0300c40b02e05100c4010b076010154842161030084120226003816601e070140c505105001754055400780e01d01b40c5001e2460351401d600600e8215021300e82c00074905181e51003076030a00504135000d00e001d5026407981b0f1402e081282c0860034446211411040e8040e41c3e034006100d008051001070700c07900303581012900d146814800100b4040c02d9410800035403040000c0a030218658034640111600208003100c2000c402403090040041601c11400c42a070911012074000c05a9182c19410004050300f8500010058856400500840020000ca0030b2400101c0300540f04000c01d01400c540044a04200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 410285548 1250 410284298 410284313
    0xb070f031b090608091e030c2820060315130b0102060a0518060702150f04020315040c080f101505060409111201151d031015151d030703 60
    0x9a4083c0d20b03100545444800c003c514080240b0152940d041d40ca104144ca8400000002c002d11032041c800d40d00c856000f8256040700119100705803c0344183d864401c80020030f1800720210440b281e400c0042c2c01400d503000b09400e074000712400b603600e01303003c0c0d80060030340f410b01880640000729030b400b0310205c203d0000007901c1e41c502030900c2e215540c603400030803180b8500d45101148800007008030f074442c0c607101c14002d41e20304511421088203003100b4045400c510501c4486441160050020100c00e1000301400d40081c200601c2900c0c2041c0312580412209800d01c018a01052114020510301800c5101d01d821680201c801d1700c80b504400c1c1c070402440d20784005440403250080400103c85102c5402c58030140f007103c5c41003080c600d541d8004140540340444a141c7d04250390b0b20382400303d50400301004000c0715211920340c180d0013003100c504c00c03500d0354001c020a04e00341c001c24960503685244424403030740c54580800c0410154604000c659200e114540c000400807001807031101c2c0385440b04103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 410286798 1250 410285548 410285567
    0x50124050c0a020414070801061e0c03020a05060106030e0f0106360207081b1b060f0c2e06050d0618150209041112060402070f0b070f031b 61
    0x106000c80031800903803141d41401020150354020f0820300151501c0e4203143c50070b4400311041d50209911700008a141071003800c2d1042d041908002d0321000e2545031406441ea640445800c40442c440c0390100b6001440500089008101c2c03030b1008608031000201c0b09080c11080080d12540c4da14140080114044000f10707141d0a402c1d072003031010724010101440761075071f03241c0750340428081c000a1440100001040280444034500740c40c0e50403803a11310035641e103030124110441b4840300f00c200c0705240d502d400030040201800c021825480d2407001c1841d5414010705002e141d00c2c81c8420081c0e41c2b0081040380402c812220034490420a0905050008003454031001c0d002d0b284039500e10100c0990104d5010800c203854000303800740340504c4880c0d00c0741e0203941314500c824062400c0c20b0040141c801c021040d50401402412034003208c0d40d803203052000940080f1130564031a022020074501082804064901480c0159900d044204071480d019050b203400d07101c09000240d510403980d241c140d0005c8a01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 410288048 1250 410286798 410286869
    0xc0e06070308060a170601060e0301150b2a01061716060e151209070b0c0709020d092001031512031101060b130801060b03100b0307051902100501 64
    0x182c2150300c4400215102d000c0c0d40d04400e41203001d40d42042100703c000141c0f98106c482c1075444c10065074040b81854242e8a01800c003030780c5040d00b040c0c20b200011011000d445261004c2e00a5001d00c00c22456a040718030300480380344c82076590340c817003405003d8588102d403c0d0140c403840144942202444c590314080c600b84207441c1007050031601002d00d0b940e1b11208400c2c9040080c1004d03207403c22084080c100010a40e0280494841d981c0000b44000b03000090382d0b5080c0c801070181450b1071816100358082e522000051b2101175444120710005012010715a4202103080c00d1a40000349880024044030368040c0c030700348070030701c000c408110083d5100c0081000c240c0c189000d1540e000b095104034007414032504214a042c03c04141d4448500c070302e00050040705c0418000380280b95444100a42d903100c1130320400e20700100c000b4107000030b81c2484021900310340b491811070720b080b0203010384181400400a0501c010b03005010805218003c9004140c09042c051328041448107000c014114408408400c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 410289298 1250 410288048 410288057
    0x50f030d120b0a1706070206151c05060103031805060f04050d21051e0c071505040f0e060f03011a0111070b0408031c050403020307031b150f0c0e060703 67
    0x8514401d541c00200002e88043d01060180780c40320440c40b210700d442031501009226040001301d00620015070203019a10801d030980b8100c5583c02800400b40c0521103003000100d0300d1651360001801081018003c600941d12540c0000b24112020724080d1150b0066115010a00c102c00e40b00a200c801c86049820031101144203148a04d0401006d5445031300614074010030040c207071003541c2c00100826a182089004451500c203a400c94031650040380c07400c03220346d84000014002c070300c00b034120740c101411103041c9507081039a40c000c0050069101d40222182c05400310030310900e41400310121150001c1140284120840300ea001241c0c05520095941080745032007111105443c01c3c0070480107004d0240d04250b8075916810011758941c08030100c040711415101020490270454800c080c05140e02d98051440c107070480c0c80440302c03010506106103800300c810b5403c2d4002200c403003610240d04450700d030200745010380b41d100500312403481001a0a00c0280007110001395103542c1200d4115501d42007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 410290548 1250 410289298 410289317
    0x41d0f090d120911040e060615041a070c17010605040f0203070e060912010921110c06071104020705010e0c03031219021204030503040b07140a11010b03030a0503040507050f030d 78
    0x80c20a00800355013280c94101d480c21050804601c0040b49403071050109541c0f20710094620000b0605510540c07142d61170010340700d0006012001403e00600200c1d02035200210140e8550b0200c8004004041c411441a07544007010826030070607000d045004010050b046045140480c3e0281c1a0108101464841e61000880140554401c4910030070903030044001c010004240c54841d0355609107903841d61b07a101080d1010b10120348620400015001c9040181c000d00f5559414028160002d41d001c5800c1610f440300720115840c0c51000d4503d140c00f0300004601c004080c1105400c3c041c2105c45103000c0e41040080a1160b02d00d40d03982a00000803a5039000749103038620318580280109009240301d0790011081c0003d141e4818040c40c003540c081c80d00a1441d8903104e0060722003610447c0303110a00b8100303000c80e42d9194010200e00c11403040b40000410310401c0280040e04507400214060301180000c002c0c0414400c08200c10005041c2c03d691020358050b0500000c0d6880c000030304130108120745c024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 410291798 1250 410290548 410290553
    0x30203090318041e1517030a08060a120b100f0b180f0319060c0504050907030c180609031502030408160f0204060f06110622020105041d0f090d1209 65
    0x602c0700725402514040492a00701c0d0007000e4001e0454400c5d4110074124214012405000c0c1c07030200000402e10384029440c3c500b00e10750075070b00c1e8503004101c283c0c003540070000022020202c002c0140380911601e0482d81c945440b0000305070b02050717900311402c08020040d040c048042c81004840781003d807441948200414003000038070b0b0b510300c07418194050207202489010a100d0300d0b14a05402d00c01e100034080914510f5044441f8002c40c0300d0b40b0b034064226004144094001d9026003800411889c02a03115a240c81d40c0146d1091140d11107000900025000c10a02203103c0803810007445c600d10540c40e50506441d44c6105014501c00e214038440f8040484007007000941d42d81c09425070103041805400e07070310b80b0100b00d4664244600400326807680341030b082a810104210b4459070700d842d00902440c05c1c602000701d0403443c00d9401c07410712504200116a100a10003141190800c00201038030300e01d4103092884103404040c240504603400500781c84e04445d08031095402c9844100c90000361100b950 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 410293048 1250 410291798 410291801
    0x60f01110a0606080705100e06030f09010212070216060201050609041211010c05090a05040504020915150f04050301060e04170a03060914061c020d021201020906040e040209060103020309031804 85
    0x4000140074620b0318000042040012802004540041f03c09140c500001141580d1520080e18403651040c3d00b040015640c54003d10000d8010b2100b400060401a01041c0345c00c40303036025620351001d64070001500303807085030a00c040e80c00f41c00316100034409420080f022600000e0302404c0241000a0308124000310342c410141c07049030811000003408104980790000c1d00c65401441d082c0d0044d90030000106060425005041c003581c6c0c042c1001120380e8500c8140c03c00000d00e082e0042d070150400100050300100d100242144041421103d5a80c0c0d01e01400c25085a0700d0390312004c1c40301c801c1c43c1000086060480409995100711480c541e4442d170484080b002040e0580007580c10a2a1030704d5440b103070300311032001c0d40f24000585120105408900a0560090008500950111040d0440001414940545042c11850b01c0c005420a04102c00243e05030b0001d801200508138110208015840d114a0807900b00c202800e04500d9030030b10080507070b1203100310201d06801801031038000d880c0c1e0316079 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 410294298 1250 410293048 410293063
    0x70f150605040501150c1202030c06130614090a150213031b08060106050f030703110c030c390604260d031503140c10020c0126040b0a02160c080d0305060f0111 70
    0x7000036a0418030b88010307004c40300030400f10b054dd0894580b009003001d0080b0030800030701a001110003014082d805580e0f0300131382c240c040440d0740d0441d004c7c00b110348201c00c83d25540c0042c6106080280c1e007600710002c4014030700800c1d07015080b90780c0700c1001005026000801c559204a4482817540d4944e50200c1c1074024080740142c4081d855000902500c0c1c101c40400a464101020403d4a40229403c0d000700c10b900d030001c4010240a2080035a00552603d0f9020790500a0010341020f00340790741c416084401402d038882e5101c030180c1d0000400065a014890226040c45a08080042d0300f5400881c03400050507000003001d8800c0a00310100403802003011042401c00142140c01d4009050301c001c0d210003000719550301060100900c04201d80c1c8003038030002c0c400381000043e65265205e44403003800c0300c8050b0122020f2503080215480341a00c001420000a0183c0e0076122554604002d941c907201c2d02c0d0000a040525200600c070302d0350342d40c03004514030800034600148041070314000740307007031506 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 410295548 1250 410294298 410294317
    0x304020117090a0b040609030e040c080c0d06051011162303030706290105070209040b060a030f03090f06230f0f03010306060302010212031902070f150605040501150c120203 76
    0x8010308200400c030740c6d41c000245040c8603668006501700301c2c1060000f41c50b900508030010070041000100e08030789150250035080640800480c43c0703a03450001c504181c07420011003000980e421150305036400104003840312040d03040c2e8100a102e00c0d2889401c40c07558010000c410f19401d91106440c3d968080050f80c445c0754009104201050117516160039290f038540d0b40c09200000c01e00c8811040d8045d20a581c0c0c1c164000e4020305c1d85903100c1c0d99180b03201034018610750380715001c01c1c030100210711140500d100f86031003030726801d0b5981c3c2009811555070781c0552018080001c0b8a2201240925444101c0c21b0314003140c41958031340c01414000c003224000d95043e040004008000001807100c2e0707030001001c69000381c091795190b504c1c81c02c2d000800c3c44100c0b0340011504005070706004174100d641c000c29105004a0807208e203448603640b203080352050740c41107041d051b440e00c070140301034031b006d12640307004104400d6040341009203040c003d0001030f541d41014003084034011038468a0f41c000e0080b15140031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 410296798 1250 410295548 410295563
    0x3050f040806070c02030705030703050a0b0907081218150d0e1212061203070b0117070306020304200303040518061503010e150d020a0b0a090305070b0406020c060304020117090a 78
    0x14200f07800034280661140164820310074640001520b00b0f001c2050030669070841302411100e01c4a8803840901d14004d00703103481e144249500040e4850040c00543e000d42d49042400d5525000d48e001c2082c0055200303000e511948001c50202d40b0718001d032003100c42c20b0407034803004a8032040c0042d100e41011300a210110b00000e00051806d10354002e00303034052240c0802c07291805402040003d0742d0341c1c1d0165040007018903890000501c003510103c46005001001d080441d40f1450f26681c4003000d0340c20a48044400c04041d0a0309100c0848680382100c201800380c0045040c0392808000908804030410103c41300b4030071501040558448010b0034822643c9103000c0395895039510254200030504a0b10b01d069030b90b045400780720510f48006045c0680c0c1c1c00800301e0712021f0070852041d00d1540801c100c5014002c4140300000002d9040c0180c5004007c0e144a82d501c0b10700d081e00283c01c100498008920880d420010440180e030807002b206c1c207444443e001c8480a41d10f00c8443d0f40743c00b0b9028009030506 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 410298048 1250 410296798 410296801
    0xd03052518060507020a090501060e06030a0f0f0506010e100816021c1106010911040e060402071202010e0c190b07081c29010e01030f270201030c0215010303050f040806 74
    0x890f007040007411610f1007950500c1d103942c0da40024004603030302801080c00284800c1a0201c680c07401801454000d007103600002a8510090a02d40846203000c2c0c00b402010b4445003001361968101d10f420f807030480c0544d001d0750609034a40307001741442c02c0181958080c4d035410701d40488652003081100150781342080315542400d16040040c0c03440c800c5400c100080d10070b010012948031154080c4844440d03460721042d040c82c3c100241008041001407440e5040741c0c0c00d10544000c20641183c034010100c203500001030946201c6240f82c00c100000d05654001e20f008891140008461600001294220f10303201c3d0700c0345030505c0c0004072072240c5000c00c4116403480341100e400042e1036002c030401080d04011240600a41c00120740c480c0b0845400b03a010581042040b44554000d421058032039201c4140020340005000405829100741d800300281440b02e12500300440d605407040100750b400c640000c040369407140d4403001e10703003405000040c00c106000ca40c801c06000c252068030040c043c8102030710400d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 410299298 1250 410298048 410298059
    0x50306090304291c0221010e160203070f030c0c06050408010524040b0402041a04230a14010215130611090a090b0609120a03020d03052518 61
    0x40c0e0b045805000505140780103c1c05514000202101588140c2400c01d8101964a041c0c000c104040c0d42100400503020000031a459042c4000398a50307100c01c00529600d9414550020550071004080d000394540181036211016000016200c03e1944014400c01c003401c5403508490010710448000d014518108000c00d0258008015100b99031225008011540d00d0340b0f0020070b0000300303074500f25910284c0c15071005507090940000065000240c03015180039510352080e023002142003002c4c902c0843c0402d00b401030030302d070340108070005040b440e9110201e0321907030000d15610100d03c80e800e15800218101ea48590080c48800411300020713007401c41ca850300100b03603825844441011540d451400601a0134121075a05030761000d28050442840035040008200041806490465011600340421821581c401c1d140099684c0c030b100207404155078038540a46081129125801410304080401c10190440101101e5002002011911a5002040948a11420087d0401d1400050790040b80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 410300548 1250 410299298 410299303
    0x19050a200d0f021f09030308060f0907030506011e0203070201081f0521013209070504021b030c1e030f0708160506040b1f080c060a05040801020a1805090f06130605030609 75
    0x840e4040c0d22820700c8c540e910000c200500501c00f0300e0303c0d400019440070032034481c8241c0c00b1581c8284117040681400300b06010700585941a110000010f0344005410400c5581c005c0103190860340758961840803050076012072403c503c031030044c80d0007403907a01058903218165403000030600154800802240d0900120500303415101003201d13440051100c80f030350b502442c8550103449442e02c0c0b070180000c80e0a010820000c0e6120122001d0708a503054400581c1c0c0506000030480c084095005005007a20040c991801d070182c4800e104a9400500c0348100701440c01c0308956496030700040b0a513a070030382d0365030b80c120544100401901c03038480c0404100030040c1200e0018080c1e060b081c1ca512062803001c60f21300c0c009510b402820b03250380040c180c40543d401c140b0013400c032050050420900341a100e600ca10700f240c019064a000041c07034141880c104400000d40c0e14098182a620130500d85803c0510a840010261a541c081e44250320101c3e881c40080d44204040c2c50300501ba43d409040145000e130303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 410301798 1250 410300548 410300567
    0xf0308030403051b100e0f060a05060607020301050a050a0b01090311010f1b060902030c0a0f12080f0f090a1401080411120106030506040606090e070603020a0219050a200d0f021f 78
    0x81d0000d15000907a08650f200040484251f405040245465030b01d80c01103c3c0a4000500302c0c6030010741c113101341da0059800b030150364400e1403900c20008207403802c040444242c43c80c4044603411711642d52014070205405d010b00b030565481c00e00342903440703103d22601150340d440b105c00c00140300011a811401004602c2e00108001402202110100f880301004c0022880c003a1207900414503543d04100240b20b2030442041d00d0500691043d4184007c1c00f1583c0030542c0b00784015a031181e8000f81940715486d05059040281002c0c10000d00300030301d04030019155080143c0087c220501201c1082000e507a03400c0c00d4000d60010b44000e101d203d54038034105170f4454040e101141d03200e081100110380c991152040c8810400100002c3c82007034500720081d0025030101c1007490441c043c884d40340d00e20850355589101e0041c4200010100d01b0b91906000d0340d0000c000040038800c00180381c5601540e511407000c0824607402c182101e021500902c000744048807c61005101000c1050140044170340014900 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 410303048 1250 410301798 410301823
    0xa05070c0b0a020705062115040903171e07110c0619140f07170c060f0915280609090b010e1b1204111521010f0308030403051b 56
    0x13a032085450710104030150040074110a0700050362204500104803021301c00c5c0c0c22002d503030003a020003062480440c056961200096002c40c009580c1c060f1049000b107803030399006030900741c100e40610182082d5101618007a1103002000400322120845143c140424070103000010300c125900c1c1d400d800814140004d8150b0100480c140000c03825152000c1c6003101c907070904103d0364500e050450703070768000c078800700c01e032125004001031002101c2e0080c1044228099043d0001401d0b0a2a005013120301d0f007078050200c0c00c0301c1841c1100f8000380d0100210b0407544040100984010f444203102c0040043c8082d41c802288a410304401e2020b103c8940042816a8888119400e0075900e00d00644107008000d03100d204a00020042605686441c00030301c2d40143c42a0801c01c0d060140f074001505003d1018101d007070340000058007801b803540c000c00d0b41c0300b003500c0e0b944095242d6140090854545409100260000c14000300050403d0700c2801162480120304031391003012086003c0e2250b4410810549 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 410304298 1250 410303048 410303053
    0x3030c0e01020106080c1c0606080601140301020c070b0a02010f060f14030d050708070f060203040b0a05070f0903080a020c0604080c010228020d051207050a1704030c09020a05070c0b0a02 82
    0x845907502c1802580180e0311202e0042800c501d290050000d01c81406070040c2090341c01c440d407400098070b24014400100042402058654104501d000c0e051001868486c0710b130f841004001c807030a20202d0054100c0d10940030641e103808003100142e0250140ea10b0420a082c030f028000300b00c22140d24050001d4548200d0010b030301a403070b00245555415042c0001010540c2480300400182400d801440e400c0c0c440d180319440d41c1c14a0751814140d0b041a84c00b110040982420041700c02068400c0e10b51205242c5007107101c03040c4191001d41000c000d8040980250b500060800086008100c010071104014000c02d907116641e0810640354501080020b005003d8881d0703100000e03105803030b05c3c000f000465450701c0c0001215070800078140e03121007040307a29001d00d4640b00380000f000009850030b1802400a0584d004080c0340c0341d03403909400410310f609014140f200b8004102000802030036178550b40310061355110b400005a89600030424014404643e074200490411440ea0150031510416000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 410305548 1250 410304298 410304317
    0x38010504021201090e030f071a150105040506210c0c1002040b0d090201030b040c0509040b1f110f100207050c0925031d03040302030d110a02092203030c 67
    0x1048141d1280990b080c00118403600180001c4545500c40700390380c1d040d41d003203030724024070b1450800c0c0035081044107a1360652600c9060504c540403559241d82b1018405901c854902440300281c4280134034007030503004800119150007000c81c04480406074001c084800d9001d850401140040c48d404440024094006c640b04010a60040d00a4900381c0704840d118a06122810344000f00500801d24164105601c40340c080700507032202d2103016208105030340c0b004e41c1d440c0030b0002d000694015071760150088558960300c458083e1400c1ca09000b02c486460200f5060001002c03503403501395880e84820807802102d0b0801d6600320343e9402044841d03c42c1d8255006101c426081140c40fa100721064002510001ca150901d1500c00804402ca404581800500791a51007648482c0406140026509a000140600c00d600c1d0070171034000704503000d103040106030000c100c0381a05d800583c0c0c0005c3c021441c80c2c001c9940030891400c3d0545e0101c0c20b4a485040407441e00707006000e0f00b00c248a68002c01c20148 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 410306798 1250 410305548 410305559
    0x10b07020f040603050c03160f050d02060d0f0509070e04151104150e09090a05100f0f022d032214030307030c110f03190504030203030c010c021b090f043801 69
    0x2423404100c801c40700c605450140b8120601c2140c24400008a911820822001c1c01c0c030201403040a1803d509004001118500a14403901e0030186801c510041c0886004010000da12106100c80c40010181c001c0341102c0c00000c03c0e2800d01a54001c1c0c16801c1e1100c061090f490b9010048d5514100211201c049503100c201d100f649540000c000030b09180c010f04150b80d030458003504010f01c1e680103050009101601072110004a03002180c624000708128040d9514810302c20031203560701c00250007464550300380030b100404d0503c004141c0d00040b10b45100520f0520481000101d5011010300c142c0f50b4034689864014000c01012645002180c4c0340c0120041c940c400040300d07451300c50104025454250424490f8500da1502c075050410000100130200060320b090014204401c02800040f0780700c00c12007000790814843e05c0c4c40318a072607410070790301038030742d40b00c1c580a600100c0782c00d003a184603203560600220100ca0741111038105030710170707480400300401c04460025501180360307540c0c0242d80300c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 410308048 1250 410306798 410306833
    0x15020a02100c06050604021809070210140406150501020706140706140414071802131a0310060216030204090314031801140601020a0209072303010608070f020303010b07020f040603050c03 82
    0x1002c0b0724000712304500200d0b031410204101a00702c1c143c1d004541c003101004040d0015542c101010400400811050104104290282940a10181011410070f43c14040002e40e02c0906205035420401c00c82089400108034030100d4508a8010000380042103509000d40803012096500312001c40144141106070b0402249100c140c650b640f05001c0b41100d1902e00381c020b5003012070075009906410a0001d101051540d000b51005d42d1882c4180d02c911707003084d4015840b0f05a6001006541090244110902c180c080384000d49904503070010701c4010f0b41c1801c5a0701e0450b5001b9031a161400424402000075680000511810b000020300608603507101c41d40071204151802c0d0b002d44d01040d5104010710740403000640c04241c616000d071412100e0074150070101850b0800403200280040103001440d480707590310b1341c0444541040f10841e030030018006c2d074030700c014400c2085845000c0b66207011595008004115888014401d20605031241445510f5580406249202c0c0c890040654191400c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 410309298 1250 410308048 410308057
    0xf140c060a0e1e070504020906040e07030e0f01110703030528061403030906190c15050604050f10270212060406050108090d1d1002010c1101020f0415020a02100c0605060402 76
    0x401e0060b01c1403505d07010a2201035004030680ea588130704203102c00b18585100e04a428491303510b030390b00400c01c0c500f002c440740d00f400860310034032040b40d040410746d6420740c3c03483d4102e40000b07900d440c0025003590390241c00154200c0b0002d01701100100340710140240c040c030790407640603206503060450541c074800c01010356a00c60b2012490300000705200c0000d0080001c0001c1c04403010364142140c0c194503d40e80c6010b20102c0481510000356a942400247d04180c4078407a401480742642105c2c500307020b10550050101446005d89076038103000045140e41c4c2030702d008440f082001c0001d45d1a407003446807400003140202d4126008500e0f00f40002120740c801c80c000307170007129404003900c000e0b420b56070f04132940b00c4140c011440004015001c000142c9807000d890550483d40c0e80001080d11140200402300ca1360402001026070050080310388001000046400702c5100740c00d010181e01071800b040e030501c900c1e410069401003000d402060425000324480f28007900c03c850030012607441d0010442240034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 410310548 1250 410309298 410309353
    0x3071b0b1e09042406090f0e131b120b0a050f0604090303061203021b060702060a18030b0408070330050907030203070f0906051009050607060b040e0f011b0f140c060a0e 74
    0x1031201240b081302000020036080c6000d1449030341070306081c985040303c0045980c024455072020590bc2418040b443c0b03000b5400c0404000148001d00300600d0280c50741c600a0000c1c1c1c810350340e0f14200310806000303a00c09001840041035403100e0704240c0c2170194950049692080c469520501d00c42c00c00d00c2d0290407500d189900030845400c0c0089a14100c0308001e0f041408100e41c001404080003081518aa543c80b0701e1140030b83d01c2d603030a001d1400402500c061080960030720000c0e020400166510080402110440794002a0315070303c01c000549459805d030b00103900341c0100e02c004507446003041040f1095403c1d4a00a02c40d06545500340241100b54003680000284804024080c07894450b00402200f40031350004180c001900d80040c04a42501d1b0041c0705e0303540a03035401c1401e18001c2c02052a040c4030ba00e44680c1d04150002c002d40ba2003503a624071000c20400140503191441800d05032100f11140e9022a880e41c40d10200803c0206070b60b01201c071017803060103120800844940d440c1800c151 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 410311798 1250 410310548 410310569
    0x10608010b0d0b040207150b0a03080d090f0b09071e050307030303050a0b100504180b03030909071202040e041406040515060f0303071b0b1e09042406090f 68
    0xc1c680340c04070465801c003114034407259485000c004200d40e110b00280c00107600541c11000c3c44401d5942d10411614000c010302d0150211100410118100e8400e444501c1ca002c00c2c007091040a41c0f500c1c404055807207034010b00001310041031010b4480006440d0040c0c841c80f8145d4030f411209800d646038007501d1352081d16850307808a030042c80024801d81005400c11490035020a22288a00c0045c4400d100d0110100000e00c01240c00c002d41408100b02d51415240400100107540c0d440020a84910503807802600404000e0080b40b450752103450b12145401402c5411502c90340c81c1d203036103c2c00c03010a46042d43c50440c00070540604001c0410242d014982c02001000c443c0c1d07601c0b81c01003210300d0083c500c03075000511000801a5407010300007080400d10400703224100140c018151120140d080e0402c141c0008180500414118584a01c01601610402503038981e10301c9400180502074211104420711065600c02504e09119031000e01603c0345512020b5a082d1501104070314420603126000c02c46 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 410313048 1250 410311798 410311801
    0x30f0705010606140d0f141e06061602060f070c0f03030e010e030d0c08090a06080a0c0f020d0c02150a0e0f010206160e031c050c010b010c0c030201111513050114010608 74
    0x500ca86c2c1e00c40c1110844040c0701007154000403c50100904080b104c0c84500c0541c0c900c0841c1c00040c441461360703c0001224494200380041240080b0307943d000310003d006010001d01c0c60060740d03811040e141c4e00c1313070302c6181d001d0060b0700c43c180f40402e010144402c602164051030210f00b19070041e0316111043c80003400511a43c101c4640c1111003043c0304c5e006072a40041004801403e0700d0724007242c4e026050b184c658101505142969200310340341024880c1c10000c805081041c41e541c0400c491050303201c545854026410640001103400e01c0c080d41526000e80c0024410034825001002c9500d4444100c2d8941c2d01c10354076000598071500200c5522a203851640d040b541800c0c000c034011a035446001d81124120791a11514912601d44084280003140303002c50440b41d914004d003d4200603240a20b85a041606582e540c0034040040f808028180701401c0003054200c01e080141803051050710441e190241132040c1030503200528520140c400303500313100c42d400c110300b142030116040722020782c1c501c81c05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 410314298 1250 410313048 410313067
    0x4022715031504110d02130806040f120306080d0c1b05130c050d0f15080106150f0314041b050402090f01080403110a0b060109091802060c0708030f070501060614 71
    0x4090b09080581c0c0c041e584030381c0d9010720b0740200041c00c2c02c051042001650707484c2d445040020b4504a50003401240c6c03142040100140301403076813a07500da61106444000180241d400d6002d030001c1c0d089a01e40d407103602d94090f001a842031040350103901841103070348030314030040c0720454072a502c0c040c9a8000750400b04065025160380e000b440402c01c1c1c1d162440c1000102900c1009503417404c0740120f4541d85492640c0c000402114402c8000d00014000308039151600e40115101006180f1120620030b200b6100b01d060b5000380c100b441e00a540500d12581454030340380c030190110541d0543e00b540c0d2001640845d00b414180700725184a14020a50b000e10980000111082d16000708203c00b00701401c201c20a940c1d400700854640f80d441003290001901c2c00300001000d1410b940c0c050502d1601307203d1268440e900e00258180100d4045c0c0b40e4aa4805080341341c2413410501c0c0e408a101032000050b0320b2201e84101c0060140284260b0083c40002d039a0803041b00d803007900c1402e04602c000c0c100302c040c40307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 410315548 1250 410314298 410314321
    0x130b090402090402190e091012032f0606010512041101090e0108030304150c0815211b030309090106030b03071a07050c031204030b04110402271503 65
    0x25458020405450610b560010500366082161481503c90503070354001e80c016040780b8075404804090785e525105180540800030000894421000c01d240211901814103225110b0326103140c5d141c100c1c450b841001070500f40c00c6070200102e014518000d09000c21010b40c4290110f4005034480405a1200d440d1038850071107104600d00c103903042c0300b0402c03000030b20540a9481d890007008034001840d242d2902c0d04001c0019665008400d030001d1904110842e0f103908000c000c0d8100d800d14041ea1030034404ca81c0414001d400241c580c0d034142034048900100d0300e0f00020b128400214040603101c03210203641c1407582d17a0148209042d84102d0200040c4544d500c40d80c0802c2031040003c04496540e6a42d0500044403240e0071000501003000103001c1c800c0c00020001030090180c05e41c010040d002005801d103016004501008000382a5280802d040c45224601041c040c40d00600c110741e82e0f61480c0c1c80c1015180b007240b002c0941c12441a01504a12340705170343c0c0c0310740c034002c1d90160314580d40c0100320386 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 410316798 1250 410315548 410315557
    0x10210b22090f0f1416060311090a0b0c0d080f01060c170d1e0515120102040308040b0901030e07150c020f09011212021912050c010f0506040f050903090609010224010f060203130b 78
    0x41c00822710800200c0c2d55501d019000414007109a141e8079031310788510600700341145400d17005014062041c820750f01404071001e411685589005408030700ba510304406801c5d84c4400010850501040180c1000c060740d018016030f1040c2d0032203402c1000e44d01c510342d0030740344110b4009851950700c5418500754104200081c1c10500703030400040c5032648a0b9202d5140380c01607000080c0780100850340903403558144c821b00c100f20b8180d800401a252409400106003000350442030100b104662440c800c6441e501150816010020b100f0a15583c4801c1d000718800c00550081d51050580e04560440030300100700c00124020118248200c05400c3e115140b07071a540c900306038200300041001064106080c4a204e00188070f401c2d02066a04201c2c04001c1502d400c02448115145010305102d8842030000440307070240f0382511850b88070916000140e05003241c0707810030f4243c080311124015030082c00321b42181c1a18240d500e0a654991a00400c0380d0340d020301d40611040046400c0f0a2008407421005003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 410318048 1250 410316798 410316821
    0x6051c05161215141210020301091107020f100302090301060308030604110a0206150a031e120509090f06060412030203070309090506030606040e030910210b22090f0f14160603 77
    0x640007044c0445c2e416203800c80210380444c0c4aa4040010300c44100c841c0110020341b4041840d490800c6a6600041c9114501d00300c49413040ca00c40c80814502e6000b601942c0380f8a030000d00800c002542c030304158240e5401115030501c110300c1d00b080750304582103280903503144010b1507008007540e03a140d042c02d8800084200313200d540f000600e1800000500004031242d064141c4264040004489150480902d026003502005000082c4030184c2181c41d2203180310b900455040924846460300360210314280701d01d0304000c6512744064807050078160004001d0201621980c0d40340c4900369900c455400b202c000340d981e00e5158120b8008030b007a0741b51940054a2100212040e00e15200da2400020b82e1146040801c0012401c0340032044049440c103000ea0310010700342e20b0244024060400024441200d000c4040310f0b440d030503644982200b01c82d9012031021a8010000040070000781450f0050200a100443e0340011101103841001400310310b03420300301d00b8440700003411414414164094940c5202c007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 410319298 1250 410318048 410318059
    0xd031e0209030114150901050a1d040f0503030103081b06070e060a181701050f090a1704030c1d09070303080a0b0d08070309030c080a050706051c0516121514 69
    0x90071400e141d442c0000b40100c1d4412a0b200d6140000305c01d110328148142e22051091070216400c000d4100310188504c100d81403220101c509070f0b00c03423a10000c1803440e01c50180c41d86c480480040304104008004010074280d0807200782c02802c9520481750b66420403505180010240305c14600c0310b042c400050302c1c42044a00300a10700001ca001d040d9240c018503444504031521840000c1d4415800784032b50f6401854140741d00403285811080c141d92610080001031481d40e020412403c2031074194140d8019503408018118029a90480c88550350b0a41441c9040d15051001048031400c0c00500380080385e9064442d035120703a0f6030000c600d005001c401c0129810507542c8118800064900d00200b460900c40c1d01c5441d1501d040d400c00540034000c0c2c0d04191400e610030340c00c0c08040303000099800101c0d00145003080d91510b003607400d0340309403600820031807040c0d003000c0912460011509001145c0c10140d580c1c00c019110a45040e4141c070603545e003e0300305c2c1888034810300035282441601d01d8400c2c0003800c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 410320548 1250 410319298 410319311
    0x110405040602220501110601050904020f01050d050f0a0b04021603110a0f06090b0108060405070e070e03060702010c0e06040e1b0c1603030207050105070210030e0c061305030d031e02090301 83
    0x280b022041c00e02600240f100e040d03044140315a41c0c01901c0788a108801c403005050a42c10040400c80705100a0b002078881d00c3c60402542c400d0307101c0c05c202c0e50128100001880f19003025916040d040c00203032254003116080c00210030392414244256103c80701c0d40003030622110308079101603032144020903440050340288001503011520100c065a03459114080000b507800d400d041101048006030001c280c1d80d0070000500c4041a00042c0720340a40c2d107103540141e0b42e500c81c0390041d200d400c18000010b4060054408010f001034043d845441c44118030349072485000c0c16682000118455401500030503016840411550000c006000d5082c40e10f0856440ca00071541c1c80715840d002403516001c01c482e0f003070001402015414444200200f500303003001c0d030400c607203940010310849004042808055442c0341100102604000401c00380b040989520b541d0100c04000b092800c56502645003c0c0c0f2907200102400e92080c0703e0200c1e40500002c07220b244010b848c0d00813019508c000c2c0400d516648401c8c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 410321798 1250 410320548 410320567
    0x60507150c12060b030f01150207090507020a0b010b0c010c030c1b05010e011d0d09030201080f0a09080301061215051c11060f04090b010e010210090c15020f1207110405040602 77
    0x883c40c1d02811800900c641c0300c2c41c015141d03d40300103050301320740910403039540090503041d000200e14003640c04180b004907583da100c0c00100d181c01c2d00004054070842080c0f00025420340c0700307402000e00f01605002030080b00800701054054804a030704c0d04000510280840d2940903030102041c496a100380b0010400c00f6030f0705036079403d4549030b1030a840d030720512001c1c1d1781d4590b4080114101c007070680d00344200c1051554002801c01c20008010142c12540780001489100d103661224650540c040b0000b510b0356165a40103114500c1e2800700011a07152001c4044424003d04050044800052040c2c42060355080000c4416002d40301c204c5021941c2000018240e441401074400c980c03559490a4469281103020340942c0c2525070314905110700d0100701181079a001c20900c2c01614419000f00b140703002450481c4418001d03502c140c00030320354021a400e1960340422501e0141002000f194680480c0d11030a1b000c0340314070b0780c00810110390000c54045030300f00346c1c1207a54414040d40006091000da803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 410323048 1250 410321798 410321801
    0x5010609051512120d020c011503050c0a14030a021516030e0901090c08010b0c0a05030708030601030605191e05041d01050c0c070b03310b01060507150c12 68
    0x1551065500b56241525a03003904007030301040c0b0b2043c1e02c04000e210040c1c102c0c41c01c00c201d1040201801c0c00c5500003903050a001400d420000d03038400c62030881d04a1175503d0074801d844482842d9070911500c070b034034030001d407690324001901c0e0142c100801034886c083d45030b82001480c10380d015240d40404410300114050a4106114007151806a00d804c003c80341f02408105240c0c0058115400c039503d00b0020b403200680c40000c0a064582000b01c032951648220b400030300c0c040f119074000300b5078800041c0140800540c58041d50103120280c809120303d0303071a0000c001c0d5103201a40d01d81e40d00e5500380c0081020182c503013091155030350001c2031180304e50380300c401117819180c1d0010144401c10884000799800682481001c1d481304040e0764140c18540d00c1c0c0c540030303222203162281903079036140800411441088040b80101d00024811180400540c2d0100d81c0c442550a050550b1810f4184000240c0703940268200c400595128a00583c181d40300c591110060000b8030281c010401d815415107101c0c03e46 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 410324298 1250 410323048 410323051
    0x1030b041a1e0a0303091d2806050409082a0a06021e0c150703150347010e06060406031e110c010b060405090708040f05060403030507080708090d0c0501060905 70
    0x6a6600111b007401c10b0300000e15050021044680ea4414104000b08526842060301238000402100d203080034811400002401498000c01ea0007072908000c01d0400418600811010300f9410035a80404e005d503511000740d202074490030720340313802072700c01900020419070007000b0483c1c4503200405401c907407419088480c2c00c00c0a850606038443d1012429410304106456031003101c518090100c2045e01d241c0c0c292000c200d200c01486043c5051104d085035000b0903103c10950243c64501040110700c40040302403a11a03910f2190490300a40049043c08035001c5040c1b1800e0040d0545180c00e207011400c40040681901a03021340401c100940002c140078005c280d00300c10072031207003038444014401190842d494100aa4480d600400040210780c54545120b54000040c0c01c10041c1ea5030359041c803400c00200100024018001c0c0c40400c410590944d2140d8050701d015500c10702142d581c00e009954900007070380c80703070400d610007207480b01320b90b2081030705601d1144560004200e01e56a82032940c241d540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 410325548 1250 410324298 410324303
    0x4030f0602030a0e1209040c050f0d06150201050f010b1b0610080d0504030c060f14070303020409060e0609190b0909060f06031501050d11120c01030b041a1e0a03 71
    0x80010601c00c0b0740103d400703051580b01c00e4030080e09071aa0000c030761014070f125640480f0b000380d44a00b601f00810f4003072000d440388408410f20080d9100070303a490440c0100058020030b04140c803620107241c0030b50f01c1440381e50300c510510110f802440e42003240b0003400760446200b041e00c0a41e4049009040c0c5428410179002d5030418908070f205070304004e40b003410608003064036810094140003c1001c1f64200e10581d04803401801c1c41500c0070a071460031518a90b80aa01c0f4103900400100002010390590040044540411081041c0c645400c0c400c8800a030a54405500016480224100c1000c460400ba45808044400614103c004020170084101222a0307445504980e08200c210300e08400b2181e40700604a004c3c040341c0e0020742c400d540e0300c0010b00a543c0100d404e83c1c0c015003000242041702d010402e0040000301c600019907800c0b075490240000c120b0010b42080404009820b1601400c4601480181d11203080744100040c020700141161201c00c0c20041c803a2021116228200703440d000d10f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 410326798 1250 410325548 410325551
    0x609080720100215060301090b04140606010305092505190302040501120507061d06030c18060f1204020a05060406081b04060903020f0a03050601090614040903020d08090304030f06 79
    0x103491101080d070341002031522030241296040200038150b012441085208008840115035110030010a0040268102c003c0000301880240410302c994131062001402800c0c0407907045960b44801182502c0c4141c1c0c41d1a40c660058109500041c0019a11401c2c03106400c071500d1060355a50000324011401d64000c80005405c54051055051900a89014125450301c2e444a46030a584160351800e051040504005d004619041c4c60100c0001000f840c140050803640c403800d0143c1c070680c555210001a20010900e440e90601c5806c094091b1824620f07401d81d164107052070543d581060000c014002ca902500d41c0030045025a078880152018040a60b1018598074202c0c061722898042841d45141c5810305000400c80309034030640e10801c1e00d074140c500140100041d00820341440a5420081c114090a0001b1034032224581c070010444040605c48019941e44c501800304030b82084a018006811850246401c3ca01403115030350040d0304602100d01d031564a480e14200c40900300c4c000c44095 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 410328048 1250 410326798 410326823
    0xa030e030412020f0402130e070201020c1606020c010e150a0e03030d0615050304170702030a0212010e0706031a041805060a0b130506100305060409060501080c0306010f0803030c0706090807 83
    0x60604100710003001300140e80c01c614111085001c00464003280c803d6a210b14403800004075524402c0d01550b64103480c00045400341c2c8401c2918031100c40b030030b00842005110b1040302c942e0030341c03203000d030030201200207408030a048100540058196010b0030400c0e090191104901d807290300c00304000d00c80031000f4400000c1040c1041e404400c50f000143c040c0040240030302c14000812030085840ea009500000351554503203030b40c40401d04021001e200650300106a0b40700724191007040d0060a003880d50641130358202900d600050b412180c0e0a81c1a45080380b10740c032941c0e041d09066001405828916002c150759860540d01d040c0f5241003120101c00d03150310b03081210900d0805d1340b00da0b08441c0401f1024845490701c4404900e10040f07480580c0c0c2016103403000305a00380ca40d98490b0b50003d411400a0000d50f8440b00101e944038041209140139200c1c51000040c072091300c140800603500c01d84007461640c0c4520b42c1c210301a400c03189040c1c0d40c059803800312800050216000304101032007050900b080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 410329298 1250 410328048 410328053
    0x40501050f060306092a042406181a071506050a06030b0f040507090b040603050118090506012d14041b0e09040606050a030b0907060c170a030e030412 66
    0x5141c40500800c0c000e40c812814003558070710118200074605002280001c3c0301ca1922041010038080c2280603422520b40300c0307041850394015000741e1004000890a02d00507585580494600d040b405885507001d01105080c403c64084004a0300303100c4082900e141860560f484150940f00c0864250240c15035542d0308204900340203490100800081c20204600702c0400007240362800c003111146d00c900d03903481c0051101d074080c402580150208981c49074440f0f0b00c402010300141402c3c050540580e6401e01e0703174602103900d400b6016025074084081e10541e4130b08500840900502c60411a06880142503480b01d410303000449001440031068001c1c480c07520800380800c4443c503080008281103003070220500182c2100c1180710740101602c1c0000340d5071b2103007401002803616070440342c1c3c040c181700c5000090000d1003040500401148059801d440d6544109482d40d407410640100900f60b00361001c0d094602050103041c5e942c50906000c20842a0010b0881c10342d03025411580e011300380c4c4442c5070306 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 410330548 1250 410329298 410329321
    0x11160302060106050301060815010903051c121512031214070f0804051c12110406140306030a0b060102012c01111e1c090807120302070b0402060c0c0904050105 70
    0x620f22810024995414480000d04070300c4024002e0b10700366203030300c1c2888151b407080e5811350065400500740c80b0304205a00d06100c41042d034246034000122401c00c0000000780343c0c0304441c208002c10f0700103a0503a141c002134001980c4105801d80a01c03c500c0083d191848081c003919501139210410035000b882c0880300a007854030b28611003001c0102c1c2104000c00608009400d0036511030208202022010f20941111118500d41c000007000e030514511003078210400c0003800a0b079000c0d031140d0040306011014003515000440b0981d0341503002094960204204101075034000da0180300110302006c07800c10014001400c152081041044006164a4400b0a01c0390804824030f2100c0c0c2d51030030110f0081c603280c280c0701050b034195180000580480c035141441440320751041550341400a104d031350400c2005a003100708182c4030784500703011200c049486403088801055002c4160640d039103842c1c0900c6065042415456650b06ca5503607140308540d15409000c0c482c610400000ca07103460014032840 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 410331798 1250 410330548 410330551
    0x1b060501120611070209010317070c0f0906061706040519140a0c0e010e06030723030103150605031f0e011113170304090c0318050c04050609060a05060306041116030206 74
    0x2440c0070b0b028040b1000507900d446c4000c0c1100c0d0401d802044949488450f10002d109001c001402e10119800001e41884500c40080840d001404200005555440d041d511143e0034000155428400b00c002403282c502076201582000082d01d03100d1044ae000003520044030310031040b440b00c00728007001f00810030380c0c14000e411040d203a0307241890200940a0002c3c241140035413156100c0c91020000a115a05c03403118061040c4620288095880c0b4050a0140540c001c0c0001d0354004480c0f42d1141003c86d650252100301d902c058024000c24044403148030310000404a040516515081b03400c100610901030642c1071080e0301c2420f542c1d00c200714000700d651400c0768001a4a012000340f80c07034200601105175001c88415800200c0d40e1152500c00303c0c014800b2200035103000d4102041e072003d01031f0014908150721400e5608101e1030711004200b00e40c8980c03c40d01554006013025003485a401c02030003840d048400548041284403405e43c114bd00d40d007151142c00c009181114518085c1541000181d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 410333048 1250 410331798 410331821
    0x120b09030f0417160f050f0f0306040b07170c042112021605120a021005040911071a09060c13030f2a21030c050a03020f0f0115061b0605011206 63
    0x103404e511701d40040c04250001504c541032055100301100c03549038403030015440c54200700500f691458074040c0f40440001e1429102e5600040c40b0000a26802d02c101020300d0065480030034032818035140c05070256840c800c81c2c16052081020300280c50003d202100c003c0651405500504180c913141407540d9450070465010904c01c004144151140c3c00010850b0b141c0543c0580e810300e10011190811343d554400d660002049515250074199410b164401600096104141c15201e15800c0140001e5814003904c4c034100540110001c114180c9241c00107190619070020070b00c6d022507881e21203046c40078010741c09071035400d480c46500b050502400e20012010104000440d281d07030030f14000d01c882030302c00c9031007030110b0307802104150616000762114450250721504940c941096889c00944803d040d404e242c41600c03440c0050700c2c8110f07040c0124491440b241c4212071840703151501c00c44828194509174407401052007601004100103006860107488400c600088036001c610380081180c2c0b400010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 410334298 1250 410333048 410333083
    0x60c0509040b0f0a061404210204140f0c2208010603210c020607080c060a0b030c01090506120c1314010207050901050906040c031e050f0105060301120b09030f0417 72
    0x2081c0c180e580440c01004d5030301511b410315001407980c24240d1544500c0e0040304101304201c0e852241406000b04008200348251010700880d4040740541000000980707a10030000744c52400550a902104081c00c1c2148200e5400d40680c0707400440700418413502d070051000c59440b4901441030084800c13064100002514040703020720360030380c802417056211041c020311815000600302c080c80f03081001da961100c2410191904e9050480101f402482e2420056001e0700681013510229801201100100c0b100903082030300e00819a030001617400300040403402131074014001840c11001d0407005501a044003852040c0091440c800a46414515032045114441000051005461b8000410303041030003a580420b18542e0701b03005034080d20021028100c0c60051034062045135600d038201c5400b940b80a40d00800c26600e484c10300583c1d20090184082d070b056011404000070f209940269400302d8800292400d14070b0f080641c061a0707101b58440010901a0300d14601c418000740072101c0700ca08000c10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 410335548 1250 410334298 410334319
    0xd03021e0d08150f04021207030608060c09130609090803040515061003021b0111040f080312040818030703240b0310020a0302040b0f03041401050402030a060e0a060c0509040b 77
    0xa1a0000080100d40c10500d403801100f034035240c0000c12803541c2c100030400c1d911640d800d0b0b11040410421107a00340082e08010b0300281c00c94001c6602d60091402010040c0b400e400102401007080701c1042c1019034070340d90040000e50000c5c62003548403040c802c02d103407692804c1908015240200321065640da1071006414800759550340c006807200c3c02c000303041c05a11402c004002d01e229a04c80740720502e03a942014046068000e10300000c0040d1241740c1d24045541e5183c0c0c4016a8a002e50741840001d4000e440216010840d1079010b403112000d10380080000242c20400703e4104140c5900441d042007029440480030850b418800d040460001e50801c000c2c040d840000350740f51b2100e050840c03119400544140321038401d804840c007603c00903041325645d8000c11242000c560003264143ca0306802003000028140040c01068056a0010000e00141c3c1450b110307040200550448d01d049445140903503070019816010780c10310300101e5140c0d02d8035100ca0300140416180c0c42c1d040e01780b08182565 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 410336798 1250 410335548 410335573
    0x7140405010905131b0f14070c12020a0906080a12030b010e04111b0c0a0b0406140a050c0f07050306010f0501020a1202010e0a0f170403050606100e0d03021e 69
    0x10a604100d0303000b140e01d4074400d00c04800ca00000c1c554071860719a8110040c0d0b0820817140c0202031100d481034580d44030000701e200e11108070202e00880100500300201248100003180e0281d51103414640003c00d0107070015034441200040360002c1c0d001c0c40c42508080b04203020b007d12402684500b4100d42010302c41c1520b5040000e2803611400c00043c825070f500e102d0700b01c010100105aa507562440d0581280901c944075650356034807610a010352003945403100c04070715284e500d0700752412a4030760707103c100d074048024845400301c3d00701c03c2e4808100700301071081690402e410040036004401e040d01404080303090006040c10f102c0160001e40740e026042c00100007590307001800f400c03d0742e080b0b10300d084408168041203015020440b2000c103940706204040003440303005924180068850300a0082c3c045400c0400d603014022403102400d01e4000703800085440c1026590a203680c2c080d482c107000c0410050f4001241007070712150550050740720380b0082d000c600603100c040900202e0580104429402d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 410338048 1250 410336798 410336807
    0x9090c050f0d1716140f0f0a03031808030c090a060f1205041a0103030f03050106030b0a050f0102120d0606110c030309011416111c03440714040501 65
    0x114401010418041010701244128005130781481c00800003900030315106040090081140b424000c095016420310100000b000059081c1110f90324000350091a40586094004002a07542020958980c00345480054125030065108210464400c2c1d16508460140269400381b038100c1d81c140134088810142e1240c009407e999507030001c20713002c0703519510703490b1003800036a01220740c441d8040420008420980c000c0c0fa0840309410301d5504004980c0e0742e00044040e50311040031907411100307040c024415800c0c450078138007e0980c1030045070482c40c00b00d00d07800c1e406c1c2d00ca2030810f03420a43d1000180f08241d03108418805400e8848010315942c4945c01c0080e81700e100c1c10140d10b06000c0c00d002110105900e205c15983d40003d00851500f10301aa810700710605a0083e6500b445208403403c2c5841e81c2045031407902005030540c0d200c00d51a0621088601101c10031801c00290b0319820403030f10304180071741c691014035424401039144242040c1601801010303030001101043c6005100500460b60720 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 410339298 1250 410338048 410338069
    0x40b041d0f180f01050a05061003060303050301050111012019050f0f130b0d15060f0206011701020d0911040b0a030503070b04080d0203090a020906030307051207020301140109090c050f 81
    0x1d01006541105400d440f89880c010a00401c059400d040411007030b0401a803204e48510002c0d900d40c03612607003115044084403854000200424018001071155502c40c2010341c0341407009000010b1140074920302c001d060034142c47c004504050004205800c0028024510f140c0410b0717041090800040c854610246d025124005a00b41004203400c20140d0040c0a0480240b1803c00c0c01c0399224000d403c00e00c0648990340c086005040200380005950388100e00000d01c9000b5503000e00926403d0442c000904c40c1c055100719495074003444007066181d03940c403d070176090741724808030140d0340c54031418801941c00c0c160300341d0300c1050400c0c82000800c4c07000c4211150103a21403078100047d940c07443c1400160040050140b8158400320400c00f02003c0003400603281402118018019900d040070180c1d01d01c2f408a00403d0343d08a101d401c4802d903121006454840d00c001c0000c5100c0d1404001440e110800368880505282c0303404940c0284902c2d41c2c22800505029078011328403030750703100119120000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 410340548 1250 410339298 410339311
    0x3050d2102070516090501080615010c020f0316090204031103030c1908040e0c030a050c0a051803030706020a120e073006060b041d1012030c08040b041d0f 68
    0x70001041c004202d014041541c13041001030100d0184c5440300300da1401007009025024480c819540490380903941300d000711804c01016940c0e41c050034119420321a0400c034001445406100e0701f0165082e16002254040c0a07202c0a000140c1b01c0740303107040c03400c0248001c01140780280c00400c000c0d818810040346000c1000c55412811051014a1500d0600c520a81e4044200702c14030506104521400500560083c1d11a50080c00340c5c1d00c409244800c1c82c42145412004141c04001c00402e00916040480041c4402001c0d2030608101e80c42c3c20082e07038070000000700091020781c402e04120120380706d4640e0101400c802000c20f24240320706186a0709849501c500d01205060003101e16032100341a005c0071550001c070901c0001d070346064a4800d0380090007078003485001105242d0803a14600400b510900340c3c40341d680f00c060b19000c5c40c580001c1c9001d01c15020460803090040104040c0001070009090720210241d865160100e22400000314003080b0041644050520000d11066591250000d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 410341798 1250 410340548 410340551
    0xc030609050408031b04091b0e032d0a0f03080426030712020903070312021002090a090b0607050304140a060f1e030b03060f0106030b03030a090909062403050d21 71
    0x1280601c2c88481406151f1004082906000585c2e504048484103402c1d8084140c84044888107544d0805031651201c003600d1508000c002c0189000654486030645041c4c03c21054403100c0312603803a10b02098174241d00c00d170049540f900c240020810547c0032265056210720006240b8205000c1c009130034400640840c0402c81d0b07644021a0b80380f9603504840c0310010080444a00b242d90345040f40754071800501071005070017912010301d600c451034001c464010790020080400181409850b400401c000c00040e6040b00d0240005400151300b04010070240242c040071500443d0507000300061026150045410029828040d9403c150440480401050380e182d4090003903880204c100d0041c80f00c041c58940c580f1500e03051240703508100c13200d14181c2d100c071343d01400407020b024185581d030312403081010005030203100100030207041c0d0b6000c20940b44c4980c1c40070a86041951400350f11020380c0a4401c0c3d09400d18a08004000080103414003407031581c1800d0481d9115600300d0744144403e00c0040781d115 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 410343048 1250 410341798 410341831
    0x706150509070509040b0a0b1c0c0513120c0b0708030f010603021801300e0f010b24040302100302031f14150f0a020d02101b03021605100c03060905040803 68
    0x31f40d1055404030180c01030884142d180c2c191002040030007441d1500002101d85480c80550616201c0c00c00c0b01c2c8120b44100c112480326140030003070300c0e0003c0c20300016038020700074407000302e41480c0840c01003640b41d0051814a4503406c04203c0038200543c10b0740180c00b8188100302190b01d070b2480340544000b891007401c01c40d1829400700d0651b200c2080d01d890a80102e0042c0190306914000340c0d02c9055090038160480b41a6a07400c0c88650803a600d40100c1da40c80303200d07150b00449450300d80d58a803207800d4450340d08a0404d40d580e40441e000c80c40344105440842e8000c0104408130000f490308411801900844402c3d15141485d442c0c0b007420103da8150054455004808040e40c0318411503801d00c5486d550542d480011020094403020340d048000b005005201051403085c1490040e000090681102c070048401c00c15002c9d0000e5200d180d0104006040481e850007040c4103110195292000c00c00209624001c0d007001000c44900390050b040b42031808043c8404075407504296a0300a0542805113100d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 410344298 1250 410343048 410343071
    0x110603060f040227030f07271404060f05103f1403030103030215091e01020409200f03062107060f020309100e0103060b070615050907050904 62
    0x118100300107801e811600026140d0003040300e84d0321094840080ca0b00f01d100d02c50801041689440603100e004019a118813424002400b6184c4c41084d940120b00404003070350f15507010035003a120068544900840034104000500c01c0b0b60083d058040d104050801603131400300031141d031019150041d1000b944950303550403011800c103804050302ca01d4541c08541c2e0b0b181c0c03e00e010b00003540459421581500300082e58183c600300003003501d040c0c0341d00d1340207012240403090203145124001095031240d440341008020717065a201c40e0f001800d407400d00c00940e9032070030f004081d001e48070254104038140e2101005841c1c10820342080c0c41010a4003440280d0741c0c0c4801c07001a9510214451120071a10561444954480c00160740c908403142e13030b192424080c042581c140c3e140d010b08d00805401241020950034030511840d0300c4002d0703400504000a0f03140e200e00715070b407150708010b6003202c41e40c1d03656003c2d5503030301c03c7e10703840d503008010071900703034000389000d040041080c01070744d05290082d600d0725600c0c0c09 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 410345548 1250 410344298 410344309
    0xb01030b0901090c09050616060b0a0e090106060206010b3105150414040506090f0703020d020406020a060e030306010f080a090209070201050403090512070308310905070c11060306 79
    0x4100c04010034010065842c0d011910092910070110004150907100000d03135070804c681602d0000d0000d0002c004403a040381c50b24809400c80d106c407190300a00450000c214a644079110321300032003400c0700011790b0030b00303100000e480c11206030090140312a0501082c418180100e138030000840116842512441c800d8010202c44985500301070340c041c5a04100041c1a0078840c0508111240043c5184140e12004103200440c0d1003541c8e4950000140300001e4107003020b5441d466005805441c0c01031810325910112012600181c0148006810030031108007406010302944080c0d2000f030011310325504210f0300191028040c00742020a0105c0d02d070004251402680c0811440c0390042e004001c54545050000d000303100c00c072012804504c511b00003107280e0400703e0740005c0d0044c2c96802011006e042d502c681038150055400410380a80050000341d456100342464a0311001401c81a00c001341004080400d50700e004010408000081180b82d000c213580c100141d40c0101c007030751500c0d0b507919140040344 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 410346798 1250 410345548 410345561
    0x9010501090f17070b0a081509040f080331020f09070512040305040302090a14090a050309010513090c0519020105070207030807151d0d020c210708060f070f050a120b0103 75
    0x30745c90600400d00600c22904400c1c103034451164000c0d81c0520407100c6003000f408200039a0091304441800d4450800141c8070801582c005000100700003100380300081c8038821411100030422000d801c8120340c42181059801038030340203000c4415845900d040c0c540203013140a40303d0000c103508103400100382454002c034112006503801410310162480c203080400c0182a00140000c1e05160039070024806113400300b2520802c44d44080070394542801e080c01100c4541000001d040c546480c1000007030300e85210300c1070703280a01c80d41c0c03a006c0e2a01d1405007401c840c03111b00c001c0315081d64101800c002d4950f6012403040b050740c1e4405000ca4995a007401d255032100c6100c9001000b144c500f45103101c41c1d441d910b400440c811840c42c111000c08085050403601c4000c4a082250444609405d041d8002c420310044100707a081c813012111900d40d00c075211403811105480c4075550400c50014051146d90240d04000802c009051151500c1122503000780079503d00c0c5201455540e5074a041d0308542e1007900001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 410348048 1250 410346798 410346809
    0xb090903091c0c03061a031b040209060d060e06090709060c0308130803270d0c021309120c030e0103061d090f01090c0e160c0b10090203090c09010501090f1707 70
    0x3140070726142c0c9801801006c901d22040760900d0180003d484a1600154003880a80fa10104805090a4205010294014142c4180c6c80007040c409100300070b55610400c0024850707000f828249060501c280401c00034050a10010032000e01001d0201076000701c50b00006c242e051620300b1440d171307500b00082000207a843c1d00400e003200002c2030000c1041c9900c0444142d50424100354002d18201c40c0c66540c4580341d194410110721080c0e91400585085000040c3c1504c4241002c00d00d20741c141c0d01c20782d2404000800c0004600184030308402d05610032282d0740440300030300b8200111800d041a00301e910790802c020596814031400050303c000000e002e81c40007064254002d0021035080d2421519540f0207014908069202e030002460340103040050007021800e64035001c004a2070303070701c60a031514402050381520103200c10000039540114402144140600700181120003400001c02000540680c0024100910300d10107105034510340203c002190b075020101c0d00e51110f1052920b05040d1150702c074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 410349298 1250 410348048 410348063
    0xc0609110a050306092104080a1208060414220c0b120a020405010e01110307080307200a051c02010603080a0f111c0e06070c08100b090903091c 63
    0x81808002280094101450040307800d1000350752142d0034581d640030111803440c00b039800741420301a1321400000406030750b54841c076850725068440c401c4038604400c441d000c0b201ca45080c030160440940c441502500710000300c409100c0b40300800c101c1c3d80c0342000136000c9007101c00006070000d030500d018108524102e900c4400701c02e2030b558035400e01c00ea50b00710b0241c512185000c6e800144203909203100710b40c180d0300d050712070204941e101d10045070749025903200001c803407200300494004200c00e440503600c80e41a6680d0000b82d0103826600c2d0715400880074100d1f60551201e408180010310100382c801c1d0308070f010603503a0304508400004078090012903101a040c03610006010b105598840032040c5011190740320312000c2e401880c84079546250501c44480401840e42c0025002ca02c01c41040441c071000600741030414030180c54910b01c60309154001412644902c0d04082030012602820040e49000c48000c0b20b0741c6443c00c0d0940d100e100b5216014460025032070111140100947c80503038468002c0718 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 410350548 1250 410349298 410349311
    0x90109051906030b0a0f0603050726030d150918020f060906031305070e0708010e040c05090a0b010807090302090606030702010608100c0e0a2d050d05011b0903080f07030c06 76
    0x2460b182c5603c0c155610001c044c06c0c0a0302c1c2c0b1108000c0c0c0102c80840b6406030060404501d85409400d101c4c8a40585142c44c144642c01c0c100b085004101400b4002030103000080c1c80c40300403c2425413208580d200d0a00340e420088607903141c030f00c401d07006210290140c90741d65070401010001141849200c424540c444000700c24002c030803107600c3c0e810340c076648290112020113484140e02201004112030204c001820040140200324000c6c1c24207030810310441d036041c85152140006000081300700c2d07140c02616521038240c00c282d82c0c0301020a812022904101200a0440d004103a8400b00107007058000c01000001c20344442c802d5200301d0040c4101c1040d6555800716002442c0940069203003080041c0d01c403000b0742d401d1f01d40720500304111011301b2442c00b2101c0c2c48041019000c003035076040d19001c6003030040001d515260001e211000d140700304000201244020303c099000145414401e04109446409100040da001d084505400100c40e8054a59000c0c0c030b4204c42c0d08001a100400d140c2c140072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 410351798 1250 410350548 410350553
    0xc12010506210307030e0a0504060303080405011401081b0a12210f0e0f01170c0421231002120103050c010809061308070606080c1002010b09010905190603 68
    0x148880d001d0003084402d0748141c5000070071803800b810704000c0b851164108211107000240507100c10384003118050440516290385000160480b0541c2d031058011034072800c10003040000a00c294010a00040f1204c0c41075410a905030b65104135111101c41c11483d20051030026a0390078a030300f801000d1031100041c1c43c20749032404179480c040303004100d03500010500b110300003a80a001a90700c2c000c00799640b000c1d86201081004580e04181c5800c0f41070201d0102c92419034008100343d544030740d5100c5121640c880c9481d1a2824100008250001700c861b20780b8280001740c0c000b03a00c03014034910b0380c0056481c0d0b400c102c0d8032400c040c419161203035618400148000c98005184131039040701d0040c800d80f80c8100c50305005541e2880304950428203500660700180324440c0d524220506680111407107030400070310740c1e500421a01d040c0c01001450b44038820074525880c02e180e07510b40341c020030701c02404800115030114404040c18060820b1503500c0320000707020701d03d4185847c0280360101e0000d0091503502d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 410353048 1250 410351798 410351801
    0xd030c023a0f0f080c031b1b161403030d020a1725080f0105060a090302091305190f0312021909061b1a0603010b062232030c1201 57
    0x500b41c01d000f0514107120b5a6225003d0a01c0912505145200f14610b030f035000706240044400d01c035445400c4c0b0007405404120000c07031903803403910040d490080010316400c00322503040c4101c40e444180c843ca2544070401103500d011003a40c1d030b01113048030301586070150103509461007811440c034003640304802c20400400da080045c094140f550041402c8450b00c401c0c0100303c0f01b401e4100c0307036031000240c960010880b0b81402c10040c02080d4451603c1480d40c2e440c1e43c00100d103041c050728122800c11500c12060140f2000303000440c241c1000079100c00d614500341c2e5601610084845020b014080b15142039034040ca140d030102c4a0000d2020341980001c0304552001e046441940181000217558580308ac000701003400c02801c10582000c2d600c20090301c000952078010100a1405801d5503e0386080001c940b20540036125003084c0f548a05062281c04002084400d00b03a0f00a441102051960403043e02c4090511441c02540001200103400c540c1c001c00c1c64003c0702d841203608481104100700c5100c0d0103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 410354298 1250 410353048 410353067
    0xe0306070507021503061c0804050a0e04060b01030e0d180f06030c080901050105010c0f05150118050618060f01090e07030b09130201140a111b030d030c023a 69
    0x3100e10005410950138122801e010445801d90811042c101c8848220302480c8110629489031039110329054840010400201c4207902c84400c0541020501007040501c0c0191040b40d6001e10701040b03517882c0c00c0150340e0b40b040c0101100050140390148000c442d40d4510904005c0c2c0071110041e45002c2d55048010002c1071801c1c502000a035020000c102600c02c18002d00c3d040f6201696601c0003130ba41521400c4510155000454203481042d124085d501c064000b1107000740420301c11241049a044514404d840b0002d0406102e202111004000700041e640d019810600a4640310300c081442c00c01a00c1034a2250010440d441082c010001c400354141c00c50751104009890000c00ca855001c000ca80043c1070040090110720100f200760400d005100103800e01c1e171040c0c03424511a16941010300d042c401b2010410b0080b1140b0240a400b908080000c2c0c0780401552404004400300000c0094485c051100001030350464200c003202d00c510340e40300c0505d5840f40d1202d0240d04900320100540044003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 410355548 1250 410354298 410354303
    0xc0f020a180e070b192007030203070905060d0609030e0925140706020f0d06030302060a06061d12010f020d06080c091006030c05160308070305092b0e0306070507 71
    0xc10a02d1080c00324007141d0901114001c400c140e050140a400201480308484400d0080000c40ca180d0041544c0110090802c5c0303030a003001d42101d03411030060606140013a00441e1480b0b0424040c00441d803180c81200c40819000300c00042c0380320b403518040710845400c4042c564810148000d06c014403406814081d50681c09184148940040354003c0d06e6010600e08007900c681c04c240080c0f000300340325070000c040803c0400c00745031500030407015080440c1c55980050f40164040810064842481d10540300603148a00f00241340540c0400040051170070b40030480d02600c0f040d12003d03501d00094100e92204646480255120302040710760000901a5124190080c0f06031204201c003403c0858000d4011002034143d001d109042401c00e8014040400740c420811030100000c4003902d420700d10142d8014481c0da0b6040141c14100b00c0102540d00c00340c00503115030450300b4048545241d950000c0b144c2e00707001094030b0030b072080c83d10b0994034941006d142c036405020340c404001500e83d01034000c00343c451 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 410356798 1250 410355548 410355551
    0x603070e0a06030b0609060d06030209010b03100e0121080d020c030d060603090812040302160815091c270e010801151d092a15030c03070c0f020a18 65
    0x10742e200ca040702950000e00a194001c0b104000907146410500d0040c007841d4060301011030019642d40c0840c0f048a0241d024111198020003808540710301c40c20558002c0c4070003001c1481950600c03c0c422500c642d004018200009001c0c844003c0101c85016180b0003118220119129100640b0b1251294030082d8250034940c40c112000c41d0710340c0644150034116400c1000141081113000d100c19008402801c00d80540c459100e001c20700790310380390404e00640301c3d1070003400615120324459003d004000e400400d440d0070013070076900d442451005031000003846150499900e000c01c1561850720003401e40c081d070042c0c5200300228030038260322007282c104c2c3c0d00c0740c00070024524224400100b03070b1014001c0e444401c010b4801001d00d82564003080e50407848803005d41d03002800030700800710030b84480c3d640b00f00c00b100c400326081214030380700704003540b441d502d841302502c0c41c41c00c0d111803409840010f05020030b00c51072241a100303000403034140380f60f907035030241004100360b0711002c62140e54480d061725001d405 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 410358048 1250 410356798 410356819
    0x170a020717150103120c02030d03020702120a0b190b0d05010203040201120603210302130e19060e0601140d14101706150f031b040e0d09060c030c020603070e 69
    0x1060008411904401c46080b480050742199034030b82401d0300400c0700204000c0804002c0000d40e44c144410640c01e079040d10016078031081441806602c0040107489010382e00020100008900c511045a03030000140010301d0905034400c080800414503200c0c00c43e00b00ba481079060342000015401140558000d88404004400d0841c0040507200c450000602103009403025840d043c448600c0610314503618140941441048408402c40008650200c1d1b84e02c640b0704188411845c4103036070b14403400c4075488180041e60411004e04000c02002c0d01d200c2c1044100000700c0c0d500c0f0070712002e0720080c00c0100c4007481800c0b5214002c04114401340c0380c40e560b00704d602c503000940b041c81c24201c1e948010304c20082d0240703946a1600300050324031142200e801c1f40003070682c240240c0c1c1c14464000c4441c44402c2c0402d0f480c41a001348421180c0070150000c2642c00160034a410340d800800d01c0040710010b150a1610180900d0200c0701503527505002508a40c3c04000c0c011070f9a0043c11144c0b00c2c01041d500030031603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 410359298 1250 410358048 410358089
    0x60f040c170c0607030e04020d0b10050a020303010311030f030a080106030c170624120f070206071e0201020f030109020c0d180306020c0a02150307030506040603020913170a0207 78
    0x81a0014061405030b11428030003106041c010b002d8922240030b8282602c000700d140011030142da00c070500620b240e5a4850001e01d0b5450f24180821141c10300d403a020b400d148094602964038030043c0000b40c011070078414940541e503000c0088121030000344066a880b501900c41c09800c855081c040e003030200b4144a8000011885204544955110861036403801c2d11200c080c840070034414007800c400d0720000d16040740e0310f00801c0014070f84500549644c101601d0305407400c4000327040c00340540086401034000c4c4015650320100403858000343c01c50090804145001c1a0700a10a020260030411804000011100340f2039010304080c032000c80c291009203491580441e01c0d08508021203003400d90401c4280089159a400b810300342c004030044a01d2a02ea03500001c410b9002240c5c00d071041200081003210072030b40740c054990096070a5070103200c501c0c01d549c00110f0310103008144541650448002d202401002c150410007540f2580860b0740e14016035000031344420b00d0b800b54014000844e01c98640 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 410360548 1250 410359298 410359319
    0x2060703060b0306100503090c060408160905012718060603031106010605030c0a050708030f06240a110c120c040e03040e0402040b0a0e0a05180d0c02040b03010e060f040c 75
    0x1c20076000340850411710400900342e400c0c0d04044c0040856200e101c0040046854610043c001f074090103009112010042034402c9140d00e10390011101581004010030013052060308a0982e04960f542d2014540340707160007a402000c03641024001000343d410340710140401544a03d05880c00390b910704000c3c1e00b142c0c0000b907580800b0b06c502c200007281000024a81c0c61040060484501a441c0c01490b01d4801d88801e0305c3d541050314121a125101010300c00b543c5010b0707011220006400442480d1666440f0b004246805500d071001c052280c0604100d00742c8800b406078074031402c030040c0041100940115055a190701366244d0601680ca0010070300310189000059034110b50202001d601036a4407942030002030441e0112007a00400c000402041201441403400d21031030a0710300014252030700b0300c13150350401c40d8402d5080c1c071034129006404050b82c0c007808a0303034160380582e40490741424a20119004104102a448690094005000d486e580141200c0d008038001d480071000d4a072100c10035071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 410361798 1250 410360548 410360551
    0x20406150e01030b0a1205010605120a03090603020310030b04140f1b131409030304030e0105040e15191202090702060c030a090302150403050d06060503130204021806070302060703060b03 82
    0x140072805600c0c54086562080c1c12000c0d40701d01c0a49002d040303d517168425080350714100e1b070445660b51980e809101904024142d00d000c170b140744006045140d96510080c0220b040343c010076080540001c00518607103041f4414900946d44a1121509031625041c01c804901c55541e51080c1c601911044540c0841c002402050030b0249025800c5e0f51030a110801c0b40d0841c1403000844940c5c3c50300800251980d010050b03600c6500301102465aa207000d1600034100c8144550729414400d0910062140c454641c100581c004007008000c441d02e0084400140f400850041500c04949440380205054551103101c400d054800d031489019038640b0360090362500400c0b9102002c0b5041440010328142c0103400403d20300c1e0190040d50307210482c1c04500ca0141c03030129003e401198000500c0300583d90315100304030040c5400d10b00301e4250b04050030700c1402c0040501010744595000304404c60749011900510000400003000035541c0c81242c640a0746510342100c0c03c0c1c0200c1d1a01e80c000074007801c0b090469 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 410363048 1250 410361798 410361839
    0x1b140a030306090e0c0f130903020a0314041805040f1407050a08060601020a03080a060503071203020d021c11100903090f080a0503070303020a0e15030a0b0f0d060207031b0f020406 79
    0x1052125175810502c85032005100d01d0710707884520320104e0580300c0030500c502c031601030003076000d8034008441e828054100c107141c008814440710700300400c00000c0707000700b9480c034030103000e0030302007490707200c41c100034015828098001e01003c0c0c56004660356000d000a520703040b00c0007592101c40a6940e880096102c54045510b03d001d60045240000040d00c0340205a034004210940040d441d031b1101f011a1030002c081e001044544009c444150506404001c0a458201c29200621044078544010b0003000c042411751030901c21401c4880c11a00400c0c05900d142c44101c070020454504113040003044a035480c030034140807803503080021070003090104d610090150800d0054ac81d200e00790f58100c00070b40c0112111010030000b1244a100780e500e0b1006400317000725a0f80003d4580c05d000f04100210380b0501800c52240d920152042c259403600b2141d5407400c0e411020058807081039050649024903d006a01c4034000d42d18029010401d54a1040e40716074003c0c1c908100c80342d12601044500a00304106 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 410364298 1250 410363048 410363053
    0x1415030601030b06070c181805070308030603010f1e0c050c0a0b10030203010e06150a0609090f06080604080414060a170402030c0d080301090e1204061b140a030306090e 74
    0x18006502070f810015211101420305468150242c8a140c1c642e403a030780103110b07508000508122040d2090060074180d03204070491808003509907070340e55540c0780580700003401c40d10080001140780e5000e520094941c02c11704810b01c0340c0082d600010b61054000542e44100514069110407054424400e0350103c5107001c0c000d10103c402a04c036600c9138140245583e24001d0701800c0030005890a004a0051501c001d000f402a800e207007a130041030526517020070f409800c4003442080300c6644080120112000011300260502006043c207000e082c042e04402030314803030304c0203220400020200400031180703600a00d042480e0f900c01000100e128003000400062001c1c407501260032240f0402d1600280300404844032026000d012804440c164030003602c3d00d240200040040001a0041400d20f04514000e0024200800c245004501480c0252001c103e6440030443c442407411070307410040ca800800c0580204d0100d80003a0341d50090003c1200000c0c10103800043c6209540a0b600340300111001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 410365548 1250 410364298 410364301
    0x1009030c06030905190803060123070f0c12030f09091401140a050a170c090c0307230d0603060c0e0a060f0507170405090f0c0301030201210606020304141503 69
    0x600700c010f07128003942650940210049510003501189140c0a220320584d021512031401200141c00744440a580b1f40c000b030074a4800084d5801c01d0300c201c0d189541d0105840416500354100624440703800d40000ea0b4908801c11a4400d050308501e01d25002000b503902c0f1400240c80782020010380d049445290340b10120341005000c10034040d40502030040000d055426402e940c2e400082c1e80c00c02580c40642c2d110b60801034043d203540d06006a9101c014259003086280c24508004612480020300740300c01c01040e08101c2180502e603c001034601c6804450301615907203c1e42e650300007440b45200c1256158586480075071854019890310f04000f200414500b80e41c1e1a0900a55003410b06003042000c1000412610001608113580f1100880600320ba4a07203540c104028403503003031006000389100d0f07183e907410132040c50019003c03241500d03420b00e01219540c1c8507021082d09641c0007040800410304201000c9003e550000c090801c44840107000d8060603a401c2c180511041507186801c0d03107100410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 410366798 1250 410365548 410365559
    0x1180b0a0c090311030a05120a0e09102c04110f04090b01060302130f090608070503060f04120509031f1b05030c03100b0406170a0e0c09191a1009030c 66
    0x13101501c100f080902680da201800759211400c2a5410301481c1c040a03000c07400503440c03940a24039070340004095801c50051b013003903100c042e03003850b1034401c00c81c90440c002450051200440c42e1941109e07280e15940055007807900c0d0010001403902d25103801900f412124038580d2920f4010941c0054110300c0c580007a0b420110700700d020b076000c030038500c40003402104000b82242c06002500b004100d010030000d01c0d2820074440a08020240d4001813181c2e008070148280d40d000c00300c85a401c5075004580090702c00070202c041d140c0340106900709a0501902020541c0030361144501d00e80f0b1110003004100010050404400d80b0f82c901c140385002580900c009032254500d00011a0000c020541d400000c0b59650382c0300c683355000b608108001480c00c8203030b555000d0200c508907040220141c0c140138020f02500d03410740e6403c40c2c0050b18800e0a2400208102b00003288813808149121481408080a445081c0140d1404130359010301070011a42d10049140c41503074204280d903070001030031060a107442c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 410368048 1250 410366798 410366813
    0xc080f0403050c0706021617070b0c070302060703110d08090a08031509010b3a0504020a2114010c0e010c11090411011d01020613080c01180b0a0c0903 66
    0xd00403001e01800b008101c0d020942044120000e014590040c000300c1d03505030780c00904004541c480342500e5500005905042400f00381c42c804d4a015113046a15004000345251406103182d0019421042c00150801071550000049041003050720444107d0b0500c040d08890104c8129500f0b441074021040c0c4034001640203000f9604641524158030345800d00000140c1c404c1820383c040841d0712400500d11030030228100340d00c1d084404588850302c5202034076409903240382c40c0311010703402c084d40c441c001000c558600da03d02026107007101c881281400c100c10316144814100e50241c0f0710340942422034625900500543d8040300080c0d035020f4260407003100545800c10301074000c07290403442c80705241958440c0040984214050001b80140ca200c801c0094501c0c005a48a94840c2083d01d0481c1c030303d640c000580f982c02c2928880044040741440c10f0010050246011900083d42080b42401d410744500c080444403034080c0074040b14903140c482c000400c4130031010700d5102168100710104040b9070031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 410369298 1250 410368048 410368051
    0xc03020901111c110f010e010510060f14030919110102010b1c060e2104061b0507150e0a0801020a080c04030510020915130807060306030b0604020a02030f04030f030806040c080f 78
    0x264201c2d0310585c626010b06081d22031068200d0466035403481000800d441d0b500b40c001c0100000d040040e08100c080700c00811004020140e02207211001002c2260403000b0001036518544040080c140400b040c680f8400d40880b4503181c030300660900e0401e41d0103107010080e81c4c08805054501503625801540c50078007a258031046003026000c0c8401c444000c401403655501c1e02800b0044903035845080c454043e00c80414182e4080200e04a01586000030794000780e41780517210300f034400003081000c0e04421100740054841c5c1a03009074043c80005a283c4054019200c40c0c10603850b1400280d0b600c1d5200615401284005000b40e40308054440450045500502c0c840b40c0c040e00c3d074003500a00740c0c2c0c60002c1c0d074051030b0030824409548204000005050011030003408075443c0a1081d146140c8410040d00d401904d10b45c0324950014015030110f008004903091030100840d400d440750b0b0341e41409462072490340c60580c0031581600000307115140c07501c0b40c03400203681901d076102c0c00e0f21406184221100d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 410370548 1250 410369298 410369327
    0x70e07050733141f08191703010303023c0a0501060812070f1a040f060c0503090a021c020904030f080a060608011806170c03010f0c0e100306090c03020901111c 70
    0xd81c11320100d10b803c01881610890030000c8044040070005103080c1051a0841e004020712040a00060000903400728446407a0325601000d40201c410042d004411842c480d02401341d0b80004c121121403050010903516000e030301442c02003082daa40c0b07000103600c55124010041412100300054130011380f640440021040c09505e8000038500441204e5032076000075141038806040c00d480c040304014850103180d0a801e45071400318118180071746881e43e80c0c440001d009106e40d1504001c802d091030401e49600da000d070001d2400d102030a0034180503200c800010130500c0000d542e000000ca260740c0303500a5008803070160707075507a00907031901400d00041d0550440c40791300e85440307c0001039080d401d05014410700031080302406115060100b0075084401001da14400c81d801e11000e80c0d03101381c1040f022031800c034081d01c1e9408140440c8408600806083d000140d880746443c00c03905d0442d42c15405000506001c2e01ca2404484d058540150f4410303103178552011084001842008080c42410701041262 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 410371798 1250 410370548 410370601
    0x106062007080d0e03100605060405061b03030406060f06090303020601030b09010209040e07050a140d02090403120903020c01080604093201050408090a05060705070e0705073314 78
    0x980b2018030504140c05078101d800016041441c1150500c0c007804045401d480e0b00001b0415030307140c40041211802180b02d03c41c030500c804282140c40c08a480300a101c111540d0081e25079030302c0c141c0340c91030003050b00d40903038440040c4102c0049040d0340600b211505503134140d00145900ea10316922004000f10040156449540a0162460b9519580616000c03d9001c0019260403800c00c41070000103840e81d0701651225070103c00691090300d40f06008241c040c3c05440f0f01810350345605084c1d411114403c015100140350260200a1541c04601002100703030999030b00520b81c403410100401d99480b0400600104500c403801183c0c14441c40803418020102d0010284841c01d0110041c00c503801220305031403a0078001144d82030382c03805020800150104030380890400308217448070350355403a0301d000d00e05000006001107075149000344240d03410b040d0302000881c04e44244036001c903607070b140c40c2180d401c103080742107551410031506001d000d41c0ca40111301038000a03a1000c0d5000840d90401c9807100118 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 410373048 1250 410371798 410371813
    0x121c05150d0f03020c1c060b180a09033c0e0303040305070812120a0203060103110c0109210f050f1e0301031403030114190b0a030905010e01060620 65
    0x40d110368000000540c0200c0d030300034580b0160308000c0d0800e0180b401c514881c030544d4044600c02a803031040003200a41220001030480b0300c900220300300100b01345404035126a14010040009800c0c1c11040200e0f1090b44c940b0010a481c6110300c158020001802d28114905000d19040355070510083c8040103903880c04240411403080401c3c2198000d40080c6c0306600b0109060110150404c041c4881c0c1042d401001d00d441c4c80d0b164040e002100180c61036035000e4000001c01e203207a03c030f60808240107007103490403a51341130344240e941e00802c2451400c4400680c03090140402d810305030340b03140580c0016103174007c4611080c0320440b81c55100031044581c00b4130a009a50300101a090300c082c0c103a2649580550700e5055041003451340100c041d001b01e0307a601c00c1005108a900c40700900441340f9051f00c00045202602c03c510715003205580000110b40004905620760076413603040381d140e841c001c1000708000c25800b90700c00e080e00c5007805400c012405031242c1420300010440b03145c005958182c01d49242 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 410374298 1250 410373048 410373091
    0xc0703020913030908062701060f14010807110c04020d02120709180507020d080402040f0e010b0a05030a02060909041a0903090109080c0d030509030703080403060e121c05 75
    0x841c241501da0700d508000544404081540001c5900c1c013030200000140000c1ca403600002900c01c04c040d00c080109010101d1410100d5007d400070303400b030440f00860f80f03c41d940724042606090802a40d0600058181001c901031301c0c09050b8000030030320200041d0080020306406c0c0000b0b90301101813951120b40c200b00d02e1030304c1086070027202d0240340d43c0d58510fa802c91600c05540103000658462031505c91804042c4982903800041000f18504282070081039961039000180c000e142e001c00c100042820440e030002014019400742c441064102d4034140240e444105141e0384114541000350494403c00c0782d1135041c50494081540113208002e03ca280d030807440e03204850341c5010b50b41e41c0040d90020640d80744540e0400310800103010f040c0000e0100f00041c5001404880b4103034005010702100050b51580d81e00e0a002940145410802d220b580b941da80c40d01c100100034506140c0018000c400100d0041122a01210fa1014022285107034900c03103400043c1c005d11016044440480d400d0b000e00c0e00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 410375548 1250 410374298 410374309
    0x20705011b1a040623060907090e040c0810061a07060908070f0209070c0506070f140c030301050a09090218060301180317070e0a09020304060b1c0c08071a0c070302 72
    0x1100400800c0c0a403142010725114041e45c0d41e0213202d0f080e0016085000300c83d40c444030303a80d40c0e11102c120381c251459100c81c44152040090354128810002000c2e04120a020808804034102c4610400301e58035201364181940403900280140381c002d00c01503d100c0c0c080856603020f080350501800c0001000c801c00c0d9103000307041d404200e00304c0d02905000d2a800c15440c1c50301795694426203d003840100a04581c0d202e640341c12008110b4818880c081e9407110a080c4200000000f21181d4117510b07984454050031a603594100b4815207205485c600004200c2204030302402c00044ea02a109864000754102c0401040c0340082103250599a150071790710300c0e0b103040032810360b40074043d03213038107801c04921200004070042c01032250081c0203a0b401d803440c00c0c1d1030b003112400c111100110300503100d480314a0160301800e88d07a143d056000c091001e003c2c030503100c002d842d80e03181c0348626205800b05549240541e10740100b44a0342c40e10310305503065150088804401081c0c214160801e491805480703500150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 410376798 1250 410375548 410375573
    0xb0a1d041d0604120c0b010603051e10080f1b010804030e04020d061d040b0610050702090108031c060b040b07150606120e0601180c1106091005070c03020705011b 71
    0x5641c1d91006003400240200c00580301840b18061920314280c0609407142070071020188546400c00d40d942000408072190003040e05a07460140c1800344aa0800140e48440c18aa0340104d046500840401c003e00a10025801740d510038600421524800890019a842c3e04000d100303501703212a403907400400390349910041550301c0c054080020441c0c242403005410921032030040a19181040600c8040346404010941c40041152003000c0001c460342c040fa80b0340100c1d000290458120800451014000b0000d40340000d880e03041392201084c1d05039203100303840662094a009403420002070003070704a4540140031030340c083e4001d8028409900d28140880c2c0c036541c454000200d04030300c00c01d080d04140c054400450602e030300510030340d4145032109200b10030061080058580c1c5d48202c5070f03028010543c9007491524441501c540e803500b0a10f16480342c403607002801480e8a410300096541d8082c071450118a034040d4010450301d03003000c0c01950030f0382c485025030122000f0103180307034006100e680508 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 410378048 1250 410376798 410376851
    0x903100905100c050f0408031c020a270504020f030615120c1b101b0311030604020702030c100507050706031119050f0a090e0709030b0c2a010b09010b0a1d04 69
    0x4592741c009829600385c03000710060802c500c883c0100454202c00e54042034001408180300540c559900c0420001d02c1200303015030001d90000c1c00455280300102008020714400c1c281136441d01c64080c0e030102058424800e10044ca5107001d558404141d2550780c21020b040308403202e170814094041e02c00780e11858a110700c0d005018258842d50304040c6580310310050000ea6070141001d0120769214007a40a103800002c180d43c3c019580840d0020556400700309007414490040c200e500b5900150400030000d521036601650760340b04030500095210300ca441140500941c000c1400d0905020203005c4184048002020040110170f1201d03400c503050500040482503030740d8440e000201d180001410310070200411b18010701c01c1500081002c95a160f0f105e651050070810740a82d01c603420100702c0d07480005240c2c0090300c640c41c1891001003000552140c00c405404980c9405907a07030744c0594402c00c0c8549500c3c1070002d100b803401e440188000c180705040001006001040300a840c00d00182d40f41c1c80032140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 410379298 1250 410378048 410378053
    0x1409130b030c01080c0a030209030c04090f060522060b0d0501060b040501121a060a0309060204060809100501081207020a0b07080a090803030103030c080a021e01020903100905100c050f0408 83
    0x2403003152804108814400c0001c0c24049414601100c940e1010300840ca8440c003030607000030304420965014800b0032080e2200030710420224446041c55080000c2442d0202e513203d144c2008556016103020000742441d00e002528408111241c0ea03610151210340301d1907800528980340c0c1c0d00022003e02076040540300c03802d005a10303903107800700050103000204114200c0901d0805200d030320920b44071020380303842e2003512010f5131071010660850051207032390340140c0b51610104001c07404075032040c035140c0250f0140088400c040c8070301466200b195028496080264400c100c030442e03081c0c9080151a0040c0020f001090302c41c0d60309524141c0790b01c414401c50b4030502c001040e43c459900a000d01002e010700d44000c50a560441d9000382600204540180480c000400d002c200103108014180200c8410321244100106070380782c07030f8040d40281074440d00c280562500c815010189214020b0f0681e0400001c00424003c90314490080c00701c02c8103482044401c015602c1d038060807000600c01415030000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 410380548 1250 410379298 410379311
    0x70f06020c0d051218070e0f0a06090b0d02040f0f02040902030402010906020601060903170c030d09060e0c1302031302030f0a051506131113030506010e07080f07140913 74
    0x42500b0400b076520084280842446115000132030300c0001648034184601e40c0d940600d0340b83d01c43c0d1400303a01d47e10002610103d00d08001c070000d00c10f500c0e18041c245805040c000d04e503d80200301c0070346041e15561b0b0380251280d000c1e64090f15041d080650b07003c0030003100103010082d5040003010b90b44942c0219102c1d40c2c0002c06d00045590000801c401030401e440034006a5042c444010b02d9130000e488068421601000031840c0e110042040720750104512046980d0317000d503e07900030080e001100c0243c890310b242c030b800d0503040349012a00c1109080c00404002c5010a400d0300c00009400142c00b11403c110346145480058508101d03030ba03800d01c1d1310340040c080701c2c405240031440c0150200c0c0d0b01d03003100343c00710a0001c551505040015150301c03a400c04100800e0751042e0b09014000c1c1c40001460b9114058001709000001c24414142c403003c4283c2c0d0388654512100781c0c0c540d03e0548120041c0c0d01c03120005600d682c461404e8000744004070018624040300c4000060403008441c010711642581e405 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 410381798 1250 410380548 410380567
    0x70c02040b04060e180a020102060112110405090a0203161413060f0e0f010b1204081e210108070311190302090c040e130c090e0a060207030206180106080a060c05070f0602 75
    0x11718200c0905946001014491401d40c0000e40f55907042c1319200c800380700c00480804100c800920002c620070090030401c16858000012543d0340d0f41c00c0c0c000e07030090040316000c1c101c43e214180c440701600e11803400030540a000f1000d00c443d64000c5112500060781d0303500c02240c03c01e95076480400500241032204010f0420382c48911844406034042e150716a000c00150103601c01400d4410b61054108180c15110317030800080f4500104900d010940410001031110b421000b103c49020742109842d01c02e00c52607803107403480d80da81e0070540800340540854480320952450402400b42c2003901c44508441d03e10351b0b035408101020350503207628011800c017060070f0001407410000c065200382c0b0512040c20904507501e500d052950240944020b050b211441000c504904010740e010a50703000700b00b19510002407c009450308019a0083c82d883d0010b0095403551105003c1c21080c2c0703400c0c10191494400541d50303800104140640c1d9400d202c3d040c0700da08041152481038051042c060301c0c01607601c91400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 410383048 1250 410381798 410381821
    0x8010e07030c150f030207021c0302062a030103080c03190906030f0209150a050f300103150c09050d06050a0609090b06040b04020c0a0501140f0c03070c02040b04060e 73
    0x1c0d00400d840c200382041c40c001c120340c40704c00068121158240140d60300c0484c0007041c0c2c40c140c1070b01402050500240d0f0201059400260103116401c0c010700003106c074102c406002c241880981580001500600050010031114402080c03c0b0a035070040b2458004082000403816103060041004a40005d40c00c119107030309801591001c580c03107c030440c42c2c80030300350000e480c124045c01540f00103e03000c04c11803001c500032401c0f18488015402400e03150f004411800c1d00c0448100424502d4400b00c29003c2e00070959140b403541030720351014850102207900301c100307401804403520120400021348400202a100d482d042e90007d402608013084074075080150005903001940040301041c40e02d141d44000c01c102010396500104102c0703021626011080004000c2d00600d81c4410650003042c042904020f0154007050005003003560588180d03440100300101400111a11115070008000103011300740300d0000070043d00e10007403000610400903030109080710125000b0500200d1254188050f4080300d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 410384298 1250 410383048 410383073
    0xd050403020a17210f0403080c3a1403040f0b01150909020d0f0513050607050306130e150702100605030336030a120e101b03020708010e0703 62
    0x83d0035001100e201e00d0652903503192169001c13004080114069442502800d044800528100c0b248580711070b202d0508034040e0f8081000ca50281c855550714000d00c100f1402903001c0c840c01c1805901604404101c0c142c1030304040c01c14203040000164410318118004005580140d004030401b00000260380340110314100180c1002402c031486030b00111741150720014000a440342414056142c9060750559406400b41c00c49560342c041c00c03c010400030060004843c1d00d440c2c0190101c90081d101c54805959610082c4c41041e0045e5026907040c3c042610394000c051070f013060a0848070420985403070404c4210f426105100182c210061b000c1d0900700900a041c080e0004402552400031154088608400031201012034558030409506a42c600005041c103644006000e8840f804072615040304541030345140c03000030480e5001c100344182072401c40340f0505609a242c0313901c1140180b101c042e0003007461400701c0c00c41c410700d9802301e02e00b102802784012401d0b58400401940d8210714282080c05072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 410385548 1250 410384298 410384309
    0x30316080709140d140712022d1e0d0303150506030906220c030305090a091802040e01020c010e300405010c032601030c0812031503030c0d050403020a 66
    0x40b040c80501c0340c03018954140f080c0b030100315006007107100180340603112411000d280349581c1c080d207100020400128280c0c1940c040c8200c405285040e030001c0000c17044880d10b10148a1541659054038250400300004100740303030402405140d548561000400b840480d050442c00a0380340c0e000480e84414a030034000c05400203d9005041d45084100a03554110040c14080c008181c415080d10940a1035484800c00e078000340040100307612800e003c0c0590f4400c0c50224025040100c0000702d50215205441e401c4220b85484c0c1d503005165000c11019145005207079040795420055181001307c00d2150701c0c180e50204c03015042c504140101543c0340d080b50400303407562145001c443c514490140c0120743c15940c090074094482481130a08840380c1800c010000c000b00c280c1e018041082c4544402d00307049902c214100a03441b61651480d43e2140d50700c00550415510500c049422611035078000107100f140901200d003031500c1c1c65131a03803812107000070354008240c000034140700f582080d0a14001400c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 410386798 1250 410385548 410385557
    0x304060c0206090d02060a0f0906030207030c030c030e19030203010b0306220807060204060e0916120b060c0a03080103150902102709020c010f0c020a030804080c0303160807 76
    0x18a0500054006240014028414000090a1a000ea480c4a00c2400454020b0720641e01d4440c0041d020300004403480000b400315030064000100144240211030089605580d010042c0e241c40e83d09881091000c90104c09100051110041c60340307802e0410404001071141c070b41011440c500600d421501c04800d10380c0a50843c1080007446400d001c405055507030010760202d812902820842da43e0702810200074821800041c0c00183d1a5005000424040341122034401070b03100c100d680071220a03015007840106a981d1040390301064250300c0400b00d035202802c030903e4442c1c0d2031072240c03c00901e440304074007040c00e810043c014018a0341034485844010201084010300750b80002e159201c460010800300801c0d5024002c00700d0b40707080030b0070141e910200c641400c1c580b1903070100046d40000359080e40a40c41c00042009111250003401c140020540290082a00c1c580741204c003103000038020b0720381c0402001006540314040009600c40c84400c907120340c10000041c0d00400c085009070a01c02000b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 410388048 1250 410386798 410386807
    0xc0709050f0709150512040b1f080d030b0d020d05011e02090d0602210103060c0e01050717070201090308030a1d0123090c0910030203071d1b07050d1101060803 70
    0x42c0d00304192070107031042c0341c10304000d444c948602212141310303403640c41100840c01d0080c0000c0001100042c1c0c010075010700e174032400c9101da06502002500761b11035043c07c5e502c40c1d504640200e000354071013054250301401140d41815031340c001c2000346400c0d07101264569501d881000c0d072040e043c14258040704000505625160040000548000d5056000f82c040b5a0024449050310803203c034210481c0d21704145180f044d0b80d00e0401e00e004003102c084081c04290384480d54105036218904039911503600076000f01d0419046078000300207401ca030728201d043c440245004408104103601940c841c04100a0201e15025912002070041e41c6075401d100081c1c2c100b07644501c400184040404400100080c0004140d46590400e4540b00000f1903441c1c020702140180200d41000c140c4050540780242c0c1110b181c20703a90302010440341c80c07010180090b01c1c0b0356400f04003002c2014502c1c3c0450340b82100e80b0340c101605a281d040c144090918070070080350300020981c0768000d0070b0003040300a000320000355041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 410389298 1250 410388048 410388061
    0xf010506072112050f090d0e010503150d021e1f020303040b060f0415140108040203070b070303020f18010e040501080c06070203070305061f05100f0507170c0709050f 73
    0x161528181005522940b41d1000c446242c810f5032568101d00b055241405282080c8043c2c4203a10810b83d002546d41c0100250307200500d0268603440304040d030682d140c510710380c0d0b10017050444106004d03145038070060b55608600960f807161100e103030348000d841c0e6000c40c50110200f000440342101040340400302c28110306801e07654020050300d60041d0070141100300c9688010000e0784411003600c040e030748580780000d0040643e40711881030054840883c4070351002070070a801510b21100488000b075056000d80e0052000810401c00744c000303941b00342000342c00c1090480405d5240d800801810030512440001c01c01d03d5a0300c004102c1d1f8040e801d4500300000d50403e111142c49034110a4103e01070030000800d041191820000040210303004001c2d8dd015080074039000f84070f9800c49101020065200f100403031f06142144408406070303401d465060014146078015600c540045100744e5644d10814041120814620300605200084201400300a03041440040c201c400c00381400c11801c00b0401041700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 410390548 1250 410389298 410389313
    0x8090705030d0f08070c05070914010b28020c130519050906011203020f1006030b0a0216020108060418211d0f1201110403021c050c01030507020f07030503030f01050607 74
    0x69002c40f5213444807240c0d950220550700198803640051080c4103402c00043c0e0003e051340040d206a80409040c0502c0c0d03a02c442c801900d018030f494003820032080c0b01c521f01c14040d9800031480c4d0308510340151800004450006804036150a8406070013070f44a00403c000704a061002c1a1583c1e40d0203000c000c142460b808065175858140504030203100c0c0c1c0c0d0f058000340b60003000000c10f80030350f000859000d00030a030000c001420341488100c820203d0900400c05692150082c0e560b1640c2c50741c9a145d8aa00c2c0b90011940003c0281c102030b04a0307910700b1200c1200201e101201d50341400381c20034070f4100404030243d83d4105000000f100c00c01081c0c6c403460b1101c1410100ca0b00d07054800300c680c101c08a03425070000321210540300220406602e00f10900b205e07000c5550161003100c1c02260726000e00905c90090b000400c0465000828642241c000151998043e5008641003d0144125070f03a480c010310f0003600e02a600e410070340e215840441001007a8040c0c000b03090250a003910603e040c0401692500b2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 410391798 1250 410390548 410390567
    0xa090504051b031608010c0f020304030807020405060f0d030807020c010e0307050d060e0d021014060d0f1e03080603071205070608040510050c12101d0604180308090705030d 76
    0x410394100312180405035010400082c07141134101c2140304065440c03845030b00a1031501050400320f4001142594214004420b440490b50031007801850107105908100082c10000c10b0b440d400180d00b01d8001d0a41c4a4181c1681400d10a8541c050941000d840207480c0c080c1c422070b194100032500c031044000380c401203426004c4074002e59800c0403680d6240791a0000c1d11414260306440e01c59401110301070341c0d0000342c2c14a541070181c400c101d40c0800705100030a001d01100c0030364010070300f18070071800500c203030120403900ca0160843e641d5281d42800c8112030030b485180c09500080b441381c2840310a00c2c0600036080103007850600101c041410355036481e00e0300d035144640c0060010150001d82800401d02c031106070b08007070080810980c40c0c001811416034000d10525401481104000340845180f4100481a10708c004400000410302907081d0321000002092150007940301d00c003100c070b0300b0310301c100f48505240300c0c0d1608200e620f807501e1060310b4104541d0120b031099102c01610300c0e400d81c01405a4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 410393048 1250 410391798 410391823
    0x60c08240607020607060216120c0c2c0106030b0405090303101502070e040f0302150f06060702121006290307110a120807121109010c26090a09050405 66
    0x3940c070b4900c24000502ca40c01800c40141c03850b03000144540070722030240c8100768000c2c8038005821170700490680446024000300d82c010b045500350784040c4210017031020038102c010310365003640d1900c80170410001580542a03009101082e142e0425401620701401000c1d4040e070004000c40c11441c0192007003a0000052140b8100b81d140034406d0000248240007a801a102e003096030f142d1800c051170001a403d01c0000141c00501810151049189401c04005d0107410520324081c6d160f00c2d00e5003000b6169200d004100c5c0c1c810a149000480c0e000f0030310507047e6044a4202c005066490030b0f08290301c0000503410800e08100c00175100317031510f14030000d5a820486518103101c0c0c10f0035074144149003110404026019443c094900000c6552040c00170348034803e25900e04017240c2d40c0c3c00500c8141e82d07a00000c4000001d0074410014203511410f183c010150250006c4981c150f0075240500c039088000d000320000c03440000780204181803003800a0b004184110080000d89030075203c80340c45180f4101c08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 410394298 1250 410393048 410393059
    0x90c03090c0e1812120903090a182315030307030f0c0f2301240e31020102060615030f0402061b030d0c0512010324020403060c0824 58
    0x40b0340440707590340003140f8848602049800c6040c1d81c0d8040b00c041d40000004a01d1940181e000500100c0040151103640030f0180081000303074103006500400d1080700020b0841a9900c11100ca07282d00c1040d005050401a04d0151540c0d08ac007105500341d0b405a0900c4600a600030084100040c0d40104403002d0006107103416050020f071480c1641a40c010500b003c0c2c915a03802d068415204034916203220702e01c508500800016003070301c01d2000f803041011000c1e0001010b184040008510710503800d60700c8103004424584a104a4036804a0149810513410000101001030710855030100f04140c0c1204048400940d1412034018218003840001c102c00000c1e40306001143c11910740c3c20603500201c211410400f8852119a62190342c0d802200001c040b641c00c10895283c0c40303003c0d10480c0d9403020b001321401481e80c00c64071580e08890b0210080410041d2403080001c00460500c090310185100e40e0011591514600008100c01009485500000c1c1482050540207034885848940700000351342 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 410395548 1250 410394298 410394301
    0x5060a0f060f0e10320d05150103060c081003020d0311030a050d0f090b06060a020f03280e01092d0f06080702030304030f1d0a03030801090c03090c0e 66
    0x21648060012940107005000b100a0045020201c550240c3d1182d280382c004100415602c40c0e041c01d0781c0000700da98541410403800a00c07081100300c02854044100940014404482599200c2c45c2c08100106282c5403c03011005000b0820540a6400d907690207240040241c101508085104502c621000384164402c1c0350000415008040300d003a502c3c1c2da002902d80760703010000301911a40c08140074920072843c0c8082542c08211612070180040c1d000b805001c580c0d039440d014040140e00004440c401c1d0700c00d007330503c0e080741c004100514088400c0490b203905148031100d104101c040748000b10080c04480817030540142d0303010001a0031070f83d4400030306003044001c80c8150743c0d0810f08851030000a2003000d0206922000006d0704003103071000c0d950014141e641500c00c90300d0b4002501c00a0000c0ea03602d0035040c80c2841341c04000701002113440345040240d85040043c41444e165801180440e60040040107008214815280240c0042c1024000300070907982d2500110b4241c003442802012020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 410396798 1250 410395548 410395571
    0x6140a1713121d091b031003081c180f0201030c050405041b080112031d0a05041a090c16170c030408010b031605030309090a0209061303051905060a 65
    0x142041055034110081c280c640b1407003030300240391007550040350f000402c100300601d1103070500d10360b0140318044511502d1185c442848070b160b8190b0000d01415800c00b0b411700301001003503001e4001d08002c040c00d56401c1a0000d812408800c4d40c1100c12207003950200e550103900804c8119085251690342441e000548010341082518180615002550094030b0145007502d903600001c8400414005902c80400983e0390790708035102110b0041d401030005200d074801d07649100c214840800c030030720001c04a02c00346031910045400c07506405100300c003aa0340212010001e007802d91605401c0a40d5000d014a020002048101400380c8181c0050032400120300d0f80c2030304913001c402c0d01c80c040340280980342e035199039000c0103000c0e059000d00c1c14824014009441d4411600414400884a0240141d414a8200d80400042003c006c100d5003050790204005d5400c1da840000408040c5d404032a00251242941450782c58616840980c07400c80549101d41000700e1000100340f5400074007101c1c0401c4221140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 410398048 1250 410396798 410396821
    0x50714251e0c0806181f060b0a0302030a0c0f170a2a090801021e0702031f020d0b10080103020d0507090908030708150f04090f080703050406140a17 65
    0x81c2101d072a000d098410304100101c5199101c00c03118030404903045621552565000c00000d1290300c24079a0028141c4010346c4661500899528013a40000480310343d101804611607000140007000281c1c0082040b07a41c140c2071061010b8040d0760f181c1f43c0703680c00480c43c019100131440c031070b070030b510100360b0703001403100c44007604207542c88908039046030000d200e031000d4081151000c4800001203054004003080c1c1960520989100c41500c0703641045442200c100c2e29000e9000d88410390701400f450f0b407014015203000102c0c8c52124442c10300140c3d20035140744550b0454001041070742c41600c5000803200c20a078000c4010381980e030129030340034040c0350f2440e089141c000d40b544122078444c1484208000c0c0f2044102442c031032000d5031182209527039000e00001d40440415040c0b9401407486c4520b050504044c1d0001590f00c0c4900020414464240c030b8500980e00107400490001c1c3e0006400d003d9140c0c003003a1f43c0104118080414141076150b0006400503d0300d0380d01003642c100020020742070b400ba1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 410399298 1250 410398048 410398073
    0xf171305030c0f0c011d0105030c030939010c020904080a020a0b0f07140703020a120203041d01050307060504080c0609150a17090313120819020105071425 68
    0x70081103440c0d000643c01c2107034072401e842c852207021030114080d44d0000038120b0445141b0040594400d451a598803800f080385400c0a400081d00380305090100300d2000c0b90305a400807200c000e051101005103401101550034028681490410254119150050300d440f0512900503520144a640f100058801240b07070040c3c1807c06041c0c800c801007804400110721004901444042c0d076090840c14414041f068580705084000300164046140040814a0000e40d0b4543d04003c1c810340e40707000ea9818010f6000381610080c03940300c50f00000100190f1408000ca0b10041100303041035420985044107146e01c80307000018a601900300002e40c41529a10780c00200c44064101903140c1d00d4400707805000700341100a00711000200802c0300800c903c10000015502024202b0403500b683c903013003101002d50660191000c940341c00e0148140741382482001085000300d200c5600003d0381d451701d8540188020540e140e540b01c144010482428901c03d00a01c103441c0c480100100140385129107005800c0c2d508 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 410400548 1250 410399298 410399317
    0x109031401021c02040504060b0c060601120e0f061905010b0a050702030102120c090405061c02011827110a050a080717010801331a040f06030c0f17130503 68
    0x1140910205075440d84e0280090700c0013a00e0400070180c8468605619100301410f141042d4480800110198803a5800c0d40d01c002d40d030300c0080b507801c25032282140380214000d501400b5030400810007140130310403400a8071103001c580c4180040c0d403400040640901c189012001000800036004055460940460700380076408110045149030000031100603030031003600c0c40e00c2a400d1101246561800c843c0344a049056003010028850b503640c010f40b600c07441e68140120341c1c1c402c1c80c00000c108400305100b040403641090a159104481200202150b010000c2e204500105208810441c0d900506540d11142d05052405107501c4488041c0c5030b80082c0c588a6084d04c508000215960354103400501180201c8420900031000200107100041240303010401001030b002410400246107032504540d4010741c1051074a020307240d52028a4138621034001a0109454003000f030086603008205040c415294607084501c1c5440b00d914010024010b080c00817076002c0c004011003800000e0048030048403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 410401798 1250 410400548 410400577
    0x1503060112120c0803010b1305060d020306150703090e06010e030f03180a0311011b060203040b15041401090209152a07120303180203010513020915010903140102 71
    0x1030395060111201c0000c1101100e442c0c1d00e2070410614140601d10420007258480d42550071617080000228041e000790141501e00302a00d00c2c0011301c0d4039a02d000f804180120000965a40351a0782400307500310700481e1103145151700b0001140031030360105c1d203001540c2100d562132155454000041b42d12a1504541c01d0b898004e0b402c0300451184000014645a80381c02d800e6400f501c161010004911454480641101317134030441802150702ca03001c220190800391284400f140040d464050807070304115400c94454654005000e0501da88256083c020f5900300e80a1282c0000c80c0700a181c03199040c032507644a65008102850656152001c260001d41084c0b600c40d103074121104074602c0c41000c1058601800030b2013062403124980400d0440a035090210200d1000d02195004c80003028130700300c4044d0186564640d02c0042c0e8080c010180901e03611205051440060700401502ca0006403130b04510811014950707100d030760411004800c0326000041590100f05083c0803a0292150b40008000d16 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 410403048 1250 410401798 410401801
    0x38060313121806050702150d1503050307061b17060102100905070e090f0a1e08030a0507020c010302040f030311070305010507020304030309120c2702040b3f150306 72
    0x5642c800c00181d44408411001c00103556249402c4d143c610a102c0041d410151000084103403a010388024080000c22510004200d006850b11813600c88080e00304480903040001e040017800403d000703c0000022075089100031403002c1038090282d040d001400740d2416800c10002e16075030300a02103001da442e0241d00c24443e01c0c0d5146080c0c1d885203058010303003054000c401e012a01465000450840708440c2e40700808550000340c440ca9007030407541840c054070324883d5100c000041c240c80091401003840150108080c2091a0041e05024181c210941090f01c18002001444d201d1803000040320707010b0928195215803664074504100f0303113070009002582400305010304558000020002c4901a0740e800d40007688400d07241400190910001d460100c0307201c01807080800e00002081d40002c003100f4117604604a009040130ba0f0000e60042c00e034090045034000c0f0f15a2103d610280507a010180c414901009001c00c903034a52110784d92081c0710140310009000c0f11074403001d03030034104401011210386 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 410404298 1250 410403048 410403083
    0xb0d02041b0206090706230904060b0d0506180c090d0803040317070807090501051c0501060206011a2104050304091506030c0e0306150301090602030a38060313 70
    0x41412030074a007001445050b00141d106280072070040c06403195541c9400c50b800842885035040e0071024054440703007504002d1841c0e1907540784140c3c001011603150440d20b52403041502021104002c0105004089202515000780051280c43d5485900545156201c401910100d01d4012a204c00100f180c02c002013400240b40d040f0100c2d01560891142014165455003012605105d041d200306004c01c0b411081440740b9030140c0040c2c02c080030304501549500320f00300050f4040d10420391211000d600010018411100c5101e590401c00800c4d400c814070b091800b84280a400000502150407103040c840807034100903052003154000c10b4448001c2c09218000c1d28102aa80f105214034808a031500400041c104d01030102c0152502d0010080e200981d00ca4103a0003460203003e861591555036891844d00003020382c809140a502d030031030001800001f1081150008150b2414819101000051080700101035490649100c80940702030f600d13521352540c075035107460014400a01c0c0f902d826128035031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 410405548 1250 410404298 410404331
    0x103060b030705012d171807050409030c06021305090a02090906010e0d1401061503020403020f0a030203061815010303050901090e0c09040534020d030513060b0d0204 73
    0xe0300c80c044042e1604143da82c1c0040d240c0d044105614904640707003041c114141c040d4103114242490071070814040280c42c05009044a04c0e00300d400b0248082440600107580c0000c00071500a01415a0100039000c1c403501d011f00001e080700001040580c00182d0b43c400b0b8503c0500380d600500f809840e0300800c2c01c00c070355603101035044030881d1400b4008241c00542c0c158418601c0b540102c4000d091421311282030b071903410014100c2c40700c1400ca50340340d42000403510202091481100013680c0c0c0140c84905503c1003100c031410100002d032249032401c0050015a40129207543c0020344090300c0400c03040481842810b00100c22030102180480320000818150000010944020240c1c0c441c01d4054a90138415156101690032181440c0300780122812803d02c0c1d44584d4100800c80303000b00600c1e110895034036140c44009201c6e00e03038840c00c2125241c101d4041102c4850303584207050900c058602080d100b00d60002d83c810180046440d1040c0f0f41543d118500000c01c0c09402800511003009101c40108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 410406798 1250 410405548 410405561
    0x1c14091c050d0318081603030b10030605030c060304030215070e040504030827120c0f01050412080f010812070212150108070b0702030604060c14070606090e1c08090304030b010306 79
    0x40100c1d080c84ca5034440c0380e101d42d03416808a0f40c0700000d50308003030800c91343d080c483c070008008a050655a8101c04a035588816900701d0541055030f0101d11503090009050034203100303041c240d00450b02401413000103030700403420b44a981c1201e246801d00340d030b0b46001150103599051042e900945004180418135078403204092041c00c1400e08600031210f440c0450680d11291800c01c0c03002e41003034040d082618007140040c949024500e0440312400c04d205c61003070071500c065400f101c0ca00543c04624505a800c40320480d80680407404103071481d850000425214a540040341e40d5406e00098040c00310740d034440500c0c000d544100100e400c14074420b000080c0e211020b0107111070701c0c452009c0000f43c0f40284001c9540aa901a016102c25290381ea144005041540c910300280010056207400800c01000a80340c20360103481b0201e6580c2c5030802490468600300e044840c960400710000ca04d607644030090004054841c606061f07241d5460044904501a6800040c00464444000003e000d1550803c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 410408048 1250 410406798 410406823
    0x60b040501031112040201080718170f0a030e09101e06030e0c0a030b060301090b04050318010c1a0403020304090c050403060609020406091e090212091c14091c05 71
    0x108420841c010f0324510342c2c0a400004000c0f140e8540c0040c0c0107512403540c098105400f801c085110003040c0311074613a081040e030041c4c03401100c1c00d0820401810101301c0b0600c89184074015161101080e103004001003101b614407409208002c0c08614681d00202c0c3c01c100030000c8015604421200345000d4184001c03e1040100090406450303050640340400d078201d04400040030150a41c4c550303601d450300060001c00b031540c195651506000480c4098034000d11441c42007001d165500d480303500c1e4000480c1c000031070700e0402520140100c0024050118a070749128400454601c3c0d584070300c0c0807461072140e50814220a804c00740041c2c103140d044030140c003e4903c9a40705020312611040700508a02403846000000340092a00300810762480041032842400a43d2005d00551200210700c00d1343e2040d010006102c0f880c004006030400c040c0603141c0303100d649400c0d051414204c518014024045010900350004000468541d140e49119842011099070720200c0820b40e1281041a107885036001e00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 410409298 1250 410408048 410408051
    0x60601020d0206160e040b0306131709150306120d021e0105070e1e06030408190914130b0d030215070203070c06030e030d0f0606090909021c0f06060b04050103 70
    0x10070719807030021a2461103410a0880c0c0f8514120358070040380c00d01080b0802e29042690344044140360740b81406114450800700c01c041c1d8003402d8074986042061400e0b4032101d41c40c4e0b004d02a002c103130351f1510103030320a2003001c0350b5194480d1510b500084d06440300103000e035014841e040c501d05020360007203808840c0001c501031480f05240c044400318241c0b0300c01c4075080c0c00150031122106031803521461007000071180701d0107005c00b007562101144c03056105903000d0710840340101e1041c01ca03540b00721a55055503031920b004100c040c44c0c10302180944102514491140c44072107400c2e5a1210300d5400050040303001070644a541105d4100651500100040b0950041c0200001400300b40004200ca203a99400080c0214092802c08214000e10000305450341c1400100019800e000041c00f030079141c252201d20003e0168500b40c0c000c3d00107003035130303000b12000c908102400015a890030b2000b95460400d6080100c0280a89822030002a00030002010b240c5051804a5a2502c400280058490a0701c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 410410548 1250 410409298 410409313
    0x904182603010f0303051c0f091104180b060d08390c01050a0e0d1b120f0f020f060d0c0306060903150c0917010e06070c380906060102 59
    0xd0194103120902495420104400303042000a00c01c20081050140345005041c10554106046081d10b1b1704002004610761900203071824004405102200080111303010000118018074854502c548613001038289111103002400300e4030703000107003001250300003013041c1c0d204032108140e100c40b05403165010401e00c0b01c10303006041c0308920721141d400c8000240140703821040d40004403560f600484100302040305000d0100c4054403008000d05401d4801c8039503601955501c2e6110003601c00d503070b01c0045810440c0081201092001c40074016154000072001d20105860000c501d00085688406400c12000500c1102c030b85070320fa01200e4944100e550500025941e14012106a141404044c2c030903104c446980070819815409020030310810304210014640e80c0050703400700c1081011070002a5121104c00ca41030406105940d80b24022b400c008a01c14415100c400b0340c0740c402c281c116003210300b20b481c058030185500102c0e81003502c00c91b88060a4682426030b00d480c0c260541e101c80c094400d0a0703 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 410411798 1250 410410548 410410613
    0x2011e0507170a1b080402010f050412030311071e1a071409030106030b010b1e0c030702011209081305130c022508030310050a06030603020d08090418 66
    0x250900448940e9034100d034040304803803030555580c400b80825000070b41c4c072410701c42106040ba0310b0405108060300e0301302451406000143c03603200500ba06108104c1d0401040c0008040715204a400b1601481c002070710b92606940b00a19200c0d03004080d0074121100003950110b05130303c490441f07452040c00d00d580401165480c10400c41002d43d2410042580b0088048001110101600c2a0b500050000c1130f410399984030087d41078405c2e001100107801c0002e00d04030403c2c482076903264021544001c00c0c50a0441c0402c00d450340240c5500904120341d80c0455080d400d400d4002c4a0f4082d08540080c0e51a0081d51034a201c00c1e5031441454040e07035805005820b1036880e803107403200d4032500c0c1d0043c21651041a400d1440c0306946a14403900100640011880d030008101451207585502c1025001508103000c0240048159003d581054200703030b000e00058540503a030703081031540104041c1d15003c4402c0018054031140c1060080d028040340002c00344898101e00c11020300440340784444268904 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 410413048 1250 410411798 410411801
    0xa09050d0503060f04110717090103060501080405150c13060f1707212307080f0903070605061203180108060f1804030e060a02010c17010303020d0e040e01020a02011e 73
    0x898180da13100d0401081c51100741026000300c1d602c45a40b0407503525191056940c01c00501c4075140e2030074a0030000c9401006560144540005001e003402e00e034a41d860b0941d1400c0da038100d1003e0341e00100e00e064022400390745030801602c1615162104016915494601c024101c2409088001c0058000b41e10400710309940364400303004552070350300c034441c810190018926040400d5030101318180da0703100800c0ba5280c0340c824241014101c000c0c0d101340d07092008004244c0b1002401c020b42c0780d8507020a205407800004100c80c0c1144d030254001c103840d41c681002800714007410303d01c4480d03400001400c0b110111b010110554a030f4090b200d086aa0304c65205101c0c25100540d007840c0c1010440703000712200c80316001c1c50b0394054403030700d1708030300030f444603004210203410a01841c0d000d41c0d11082c0a0301d4581d00140c400745c2d42020150140d446615507203000b50f40e80301c140416414071940390b0110500c1d8885070030201651038814025940e42d480028000e008050300080d607100034031500c0d000004c52141c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 410414298 1250 410413048 410413051
    0x3070b030f01150f180b130e1e2a03070c031202031e19110301090609140a090302070503060c0406080934050a03200103091e03020a050102030a09050d0503 68
    0x15030340d6483d0030816113102911030102540b0030584100001c103000400e54100001030850300320202d400c485061401c20300741440200a031506500220140d803108a00a00710140d0340c0c010b0000f46004040e007100c078042c810180c061001092000000000c010740d41d45c010a2000a69202f40e603261081d6400b108114101d006c02e4907209400c0004503618104414008401f50f00140300d02c2a8203001d040084200045a414a21404030010040010090300c0c03c140302320b400502201c0c1c0d0a2000038202e003800c0590101c000e29503092207540b05020014144200440405420064112030315800d018813801e4141e0083c0c440c400000e607440c000502c01410110725032114918203548110744049a00c0c0991560b01d03080310501606400d580c0005540d43e4000c10180154040c154240852402c601c11200415141140c181810f04003484980001c0d00941c007214400301e120078680410760140740072800c0c15203850000d41a5030000c001d2001c011411f51010000c1c0b4410000c66203d448002e106842a020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 410415548 1250 410414298 410414339
    0x10e01201b0f0f030706110309030102041530020318010c180614030115020a0f03080f07110705010302161407060207080a0b0a050604110d050601110705030604020d030302040503070b030f01 83
    0x7005c0b0040100347d0251603104650301000058a041000304800320742213030010380c170110720484c440050120003a00404158242e10200f00b0303165800c58401d8100c4034100d04807103800003181d80000043c40301d200c150f500d6240000c1c002e00a110540c2c09582c0100381c40c40301e1402d041c0740c0100b50000030340c10340035040c00340300c9042400c03849055a19082c0203101d00c0d00c81101ea4070075802030711140000100c2c041c0c50115064403d0306d40001a007408281941c0c1c001d00241f48100380701c0c070380d1a40c0c4410070000070504101e076030902c0c0160741c5100710701e12103080f442c0004000381024001c0301c82689030702c004a1448241d807503541c00c80340403d5595010965446e80c00c04007030030714400040418407601c0c2640015600a001420200b120030036040c2401903917003e05054035000e07540ea8140406585d1100e00243d10407079100051080c90305000004c0d0b15400090300092040030280d41e000e04041c02901502d00410b4024141c0341301580c0d81400c1030981e070044071150705908101b40045000c24406014910540 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 410416798 1250 410415548 410415553
    0x331905040213090f2a03140c0a0306060e060909070302250204050c0708041203020a120e041508030a030504020d080304030207031101170402090402040608161403010b010e01201b0f0f03 81
    0x101c001e0107420141506003510170400d61074103105c4902d2011080914000c803280d581d103641e580c8209034010229003090300700304c08006162902c00c07005e41c1d0320429900b00b07541c01c41d034414190325041c3c002c0c0e00074403a400c030056040c0b40640604400540e880742c1c109007035000366800e200f01e507114025001c1c188141c00e001849800140001e00c1001001c0744ca8040541c8280100c44110545850765068040011140d0001a6404018001c40d0405010700048030300c68a85501e082403c05560688078019103d95a0800d951000041c065581c0c40740e100108582084141c2d0b601c0c01d01d07050003510f88031140415510705030400d412105039482800c940c030700c1c142c4a002c00c0c1041c0c1c460750f0070080e44210151059078080d80307951010030b80c08001d120180302c140c01030825801c014a0000c1142d002c88500710304606c40e903d000107a0b0500d0f608503001142107002442d012081042c060803001045c00a4501c40e4203a00c5a410852049201602c121306a14000c60f1200207140401e0100720001000a41154064 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 410418048 1250 410416798 410416841
    0x2503050c2e0e040203181b0603240a0902190e060406110c0306150f030f0309061b010513060b030c150a050d05040b331905040213090f 59
    0x3200c01c4010140c0010a0b162003070301c07400008000380036a0000d840340c684861030f2007000d80c1d00c03c0d420400010216011031a40607100d5075240000c2e00c9000003002d01103044141c4424640400f01d408003207281c10001442216019102c6440d08002d400c00c1910000070038041344080384150007004001c1c05043d008201911741070800703000b11000c07100325a10000900c901c9214200c00d87d000e2007490703c01c50088000100351400719080015020784003034610700030780200460954843c4044100c0b0000e103000c7d5101a034402c00300c103028402e03100720940b55145500e84818459900403a0032040001c500034281402120f5480c010952210385a0903805d03030041d540740c182c1c04a0010030f000303030140800e03a003040b6007051400039108080d50412241101e03502490010031404a440d4196416404488030b151100f541035108035441405d010300540d071040140c0d000c900c1c86000042c24101c042d160260080d51140d2004003500f1021816010f200015800c16290400451082c0725006141e8407403000600c20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 410419298 1250 410418048 410418109
    0x807180b060d021623060103020f030a02091801060f150c02120f06010315020403032a06110901031a0d0b10030204020a050307031503080a030c022503050c 68
    0x400400e060190050340612411400000c0382c400351000d039020b04d02c071000794032541c034250b21004038003807880b120b81c0c0d07420706282845031000070703158150380e0306503000320700400030703078000b9141000341a0000c0d4401e03c002c0c10130003c0504202034410300042800248101602c4883c0d003400c00e4880c1c01485030f52800140b5101030359101e030314000d40c40c42c009482d0b0000c0d102030038406403e0a2450340d1205840e800500100100003603210755102410707100c0d50840c00e0908699009121034001081c1c9104400c9072a844500803003108100d03182a03501c8541041440464124401d0035001680c090340030901e4030054130010300f41001c9880c03108400503c055902001e983d00d10164180240903001030803034044c404001a101c0384002d06941d1042c1c0c41c0caa0310b80ca04848000c0039100801d2015543c844c40313180030800200c4e9941501c01800042c2808600f041c0c1940c0102d1a080c100780c0c0c980f81c40b088182c84c0061194104000d081035a015a080e42d10512041c0c0522048448201040c7c5200800c01c058048 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 410420548 1250 410419298 410419301
    0x403080f13050708070501080a0b1507142d0d02031c11070305031009060f14060712110d03020f0a030c11031206090f060f04271407080718 61
    0x50009501010700c11422040d2107503440c0908079001080c5684c0400c8080c00f95603040100036078800d4210710203000e5a6140c40102d104444860b507a1010504d000c07900c2c2d030400c1410901c05903801c404904513802c41030084281c1c8601d901c04c0c4d03130621081c3c1030b0402c01c03054a0f0020400e0b540c40005034000394640050b100748681d500c01d6a404d040c00440da04c0e5070342a43c41d4010402030480d2402907a40c25101c0c00c2c0100d40600740211076000717100b01860501300708509001d07019104200c6a00c60313a840720003100c03440424850301c224880100100303070b60301c003020b142c540280f2018006801c1c00210740007120050b0054040f446002e42c0460000428804c0361010b9100c1d4021100196841c80c000c008440d00062481c1343d50411364185400001c10340c00c01070982400700400d070344900301d444000c81a003800c00104003a41400300000c0c0c099078407072007068071905080180c20704079200c40d00340e00e603840c155040c000c8071444c49005170f88560140c0400000e00300c03c0003c0c01c1e005c0e0703030a00c0c00b00501901c0f0000c1640 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 410421798 1250 410420548 410420551
    0xa06031a15070b010b030f012108070303061e0311120606100512070e04180807020d0c0f060c150c090902030a0b060304120e0102030322080702190303090803030403080f 74
    0x3030080d4070412803100018048450b0303038024624a21025200c1c10446402030071a001600041940c1018400040c005c20031400f8900b0115046101c11b0354a05281c1800c401402c42c58001e224041003140c44a240d141040060b4400c0b0703030003035000c03642e083d0703e003410400300108030101c0880b158003078400318000e0b2a0040c01e23401c0132989400d281e071400e14510810310400c801240d0040110300107a400081e40d04141c082c8003566000b61040e0700016100d9690100140607070b4102038000c981c40c95480003000800700c0c840c07000c1c1516040b082c009030380e6500001c01c410552001268100d50603c1e200c402c80c1c4243c0200da07041c49441e00c1d4422001c2c102070141d0000d40004140704040c54071284402c40e00e494940045011f030340a41b1820204a24408000e0580b4400c62841c074119441001048001169268000b1306d011051a035480c01c0039076820603068502075440081d600400841034250680381c0c141c0c2400461f84640c5030070484940d6403c409813a4041100d010f0082150f580c00215142e21142e11039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 410423048 1250 410421798 410421829
    0x3020c030f03090f01240905040c09150b0c0307031106010609180219080109050f0118020d09060c080f0f010b0304032f01051f0302030a030e0319110a06031a 69
    0xa59131aa450301a0030b0a5a28443c1010708640560303a14483d5049054074283c040c240f04601403019050a64031090260f51318492003030819030311518401d04911801c80080103040b2500260f4030742c2403151980c1e489500011048001c90110404216003000200302c0314100e910750b413200c1c91454682182ca941c60b00208164100e074039402c01050907c81880765105900000c20350721034125604207260351040711005008600181901401041040708048001302280713000c250260300c074564100c540700a0072501e00000d201c00c0c180300f840e10312164494021b5100c0d07403000e1004125900c804855030140b017400c1c0100061500b040000030041390080309545500340c4907034150780310f05040c0c602000c0180781a91400c000c84c2d46030402c1c0030b40014113440d407040c1004c00341c0b0100f105504d9580081c1d03685601910003018003042100044007540c060281c081c040024426921110080385008041d000e42c200c0000c3c41031102900100f003c40c1700e480384c15240403c1048503005202140100a0310320b042d508a0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 410424298 1250 410423048 410423053
    0x1110307050307120203090c0f09160f03060306051914040503030615040b03070201050a06080c030c10031b02010c0f03060e13060608030705161401020703080f0f0403030806010f03020c030f0309 85
    0x4800c10395400f1720003540305100e8030780030703100320504001000130620031106018421500d0780b081c0041c500d11746d0303002c906d500c04500300314a015003074840540140400d94405411035107014208089062810780080071850000010050140c024003481001c03042507a02403c15401400000c546003400740c460400040841080c90800d83e6a440e07030002a0310885244005075150014882c400081c0c0c0100005012028068400e00c403401010a0792850122070180c45050021a0003500c10701a61141046801c1e03c407034800e59101c0008068080c080040c3c105000525421580000603ca40309100598a098000300c54548441300c504079100c0f0080001e03115542d03104e0001a0356a401c00084c8100d500c51000f80c0300500081e014807200340c1c2c50b40c1c09883d0750000c03010b100c7c41582e408170f00360050f2540308010545400200038240b0144c040d64142e0580090006004400c5c5a0415070307041c401d190990302c0207a005d02994044090f8001c40a02c3d06082d40300388200e48000d0828130240d503110150108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 410425548 1250 410424298 410424317
    0x6060702040501080a0b251b061b0206010602060c18180a1e1407050d150609230303160f0803010b0319050903042310080105030f01110307050307 64
    0x2400b25007003a030002d480c07170f80006290f80400c013074848440c4d88a0707045211043c11441840741c4201000380d400011003008a414940c10400e541e156001e4107043d00004200304224040498407c5c9580c040d50340d01c054450720000040c41d501c00580c0900c01c4111440542c1001e4882c1c1040c9039250440c0342d0b055001d804000441d01491039040054400d03060204040b43c4000c51071740507036004418a0f28162218204502e0440c494508800c20741c01841928203c2c1d5036820b08034080c0000c001511200c004103260b2240050f030903620041d541c041d40d1101440e10001d154403403203000035103010703046150103400520690341a03000340800144107601503603214000801c26030320030380c1c2940242c00001030340b800403007445190b50f010b500d48040c950b841074041005003001c91800f0341d03d002e14071524441c1c014101c03095010400c0598030b4500c821000e042c2c618101003864015007890b03402d0103468080e110f0303800d440c2e10301e0005026504020703121424452540c3c841e480101d415500080141c418820b2000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 410426798 1250 410425548 410425553
    0xa03020c0d080105040b01050903030327030403060b0907031a240d09060e03130b0901050d020307080103060e0304050a03060c0905030f010501060305060111030a2007030302151003080a030203060607 87
    0x70381c0c10101456454024a6040500300011100b0040d20f01d0304000c02408280042d03100001242e4019600c5490342e0003020356480c05803ea20f400b8401b43c5814040070078000f08010032900820700c040e000312844000e954914004030110380130003c403500c4e856036003048002141084d440303032885180000f42d071040841c0510780721440740e40421005204180d0726040c400034860302c2e11074101d0310318103940514170b0b0903d400032800b44410107004400400c41300046200c200da01544c215154100e580d4010754a0f072030074590103880c800091106694190414071043c0503214040b048501303035100100300f40c9015080d84c940728000c0522809a9013441045500441c413a0381c00c00c803030060b801c1c0710700000c03807a0340c10404010240c801c0544414144a502d802c10071040002000303135001001e0519000d070540c0c2d0001040b0480300620f410f42a842c0c0a00302008c8241940480c8003140d103180a800c3d41e03d10748500103040310300a914803015201001c2844000c500910070b400a41d00541e0080c40c983c100f600c40e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 410428048 1250 410426798 410426803
    0xb0310090c12050601090c030212010b0c03091e0907020d0507061808040f03140d090b0702030a170d0b0f030c10020a020301140702010b0102071a0a0c0f12170601140a03020c 76
    0x5841a6484e9103c0e600400c0942002c2c00798490541c03984c40c0030350428030405840d06142c0d1040c001c1102e0b10364080303000e2031118003c0041c0da4040c40c00400c0080c41602000d0741c92180c44210800500640e50940003c0c8414000039201003007400d695122490003556031146401001034485011f0b018003d800742001289448010b04041d00454141210f914558a087c0c1d10b80c015001130791242d500a000710490f610740021a40080b501d0940300c6640c5ca5005100080c205001228001c0c0064892900c0340d82d28035904018003890100d1002c00c1042444c00c80800944032070411400c1c0c3e05500652078410542040742d07a9028079070017401180d9003540c465000a0a50b030304482d41c51035400207081084002a03090140c0e21061400303002410142d4141040c14100440e24290350100c0180010848181845103040c1c4580d141c00ca40341ea034100e800c601d4200c0401d0300d4100d0b0400000e240890003040e051550301100c1c080c541c16186e03242030b645c10500c210b40c6038000342c0056040c540c1c00c0c041c55041c200203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 410429298 1250 410428048 410428079
    0x6040807080c09070f090627060e0a060c0b041e0b040812070e030a1103030c0a0503032e0323060901060501180807051c02060d05040b01090b0310090c 66
    0x590203001ea20b20b000050141d1420002c0009080013102803481071010f070408005015240c81c0c0c90030f07100c086110025120300d0201e4801c04480b640040d200050866481407244009010442e07825030195510f01c402c540b24500c98002400d00246400031900203900c40d109224a620b02d2810a00080c00e00d46841c20141d9041382c080d540c440000880348a4001e40d184075980c0b0202c6800c00c125502d451501190361141d8468006000c030010380354001e1300d568100b040c1d070456183c600481e8994011450001d40340d410a803007054100416007005200f0342c01c201500b0010099287c428800c0618585404032600020682d108004c0143c500015400802f80910b43c401d041040c00421000d1515000404400b0108000816000f039a04280b0140901240c0c1208840c0102d50074081c031080b508164900c50316001d0001c2d88030100141c0c0c50b050600d1500542e2103140903040051b03543c0c0e45c0c0c103520819110f9100c011031b45a0080c1040c00034101c45a4060300203940100d600321860b07611101c507401d02002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 410430548 1250 410429298 410429309
    0x10e0d0306090c0504240e1c0c050301050402131109060301140111010203070504030f050309061b010506010507110913020301020a050405090a1b0c0501090602040902091f09090b06040807 82
    0x11100818050080039010f9140800b000c0d241c460310303103850701ca4285c4c80115250503503035404032403ea002c54075a100d5071030700c145400700030443d03980906400c2c2d40c1031081011000c01c40768602c400c2d000040c945818030580b84240c0e000742400c00c2481201125500411807030181d942ea5900c20b11004030340c0c0d100d4001540c0030f040440c01c108407202070080058110210b08008102c0c0f80e004000700320b43d0310342c840c080c2ca0840b5031110200180c11a41c0c0741c070354111300410401c9a085440401c80c0e005030340c00203241030b54008840703008001e9a00c89000445061041c044044c04140c50300c41410307440d003841803080c1d602100b03a400c00741884c0103076400079003643d0018a034000080d0021030140700034608840900c0e000408484100490b5400c010031700c000d40c0d015103510040c404070a5084050103004c5d0071184600354081d0045603600e407149501d100941000342894094820b0343c1a55208181c0380b41d05903504001d5844921445180199040240c00b24941440d000f0360300384000101d016040284602500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 410431654 1106 410430548 410430551
    0x303050405150c34080d080702010b03070e01060e06030912030705070605090109030908030a120c2d170f04030f0516050c030708010608100b03010e0d03 67
    0x41c58003d15150007950660088000c0c0711101402100b08850405164080d2500e10700c15001c4500584455510084032059142d0203504499807003180c034400810b1109204000c03c0c00d22000351b10084030001c02600500651750403e0315a25401410782d14141585000007086645514884943d000d4000010119460fa03216400320761801d038003c407051049041c000d00320b0303000300b0300c000c011380002d03101c2440031807070260120071079072550010f5031040b08540c0c820004400503d0041c405909003c452010400c2c054506880080126220389200d40d5a03414008080c003031180c48010740508260001c1002810030103680e5443d0020b41604d4000280019201c064900c0c1c42400005070300b80755400271800411400049502c0540310076000d54094550310001d841c203030f0342d007405070221507040340940300c01030711995000382c0741060700500100e1404284001c040c1013140880c2c440300000d = true := by decide +kernel

theorem cover : BRFrame.Cov 410251798 410431654 := by
  have h0 := BRFrame.cov_init 410251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 410251798 ≤ n) (h2 : n < 410431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
