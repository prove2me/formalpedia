-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3180
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:53:47.627651+00:00
-- url     : https://prove2.me/submissions/34148728-447d-49c9-a0ab-4c0a4c46c98f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 571762589 ≤ n < 571942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 571763839 1250 571762589 571762603
    0x501030e1204080c10080717070c02040e0a1a040803011503180c09060506040b09060d0e06040309030b0604290f0a090f050c03061c0305041730220e0c0705 68
    0x6d21001900b0041c02030b034400c02e07507004100020716a000c662070f1030100342c2d40c001484500a61080c00c0201d41c0341c0b051400106040c4d014010120082c420b5140555980e4203a4183e80103002c500d0b0400040c85040900c1620080c0101c85244c0001d0240308010098a40700c03103940211084d48407258200402c03147e50203a14080d200440d0030340e291602d464038103a1a4032840d00d14a000e00c0c0e000c0740040c00206e15a011098a0740603c05803101490540b400502118840c00100e03401d02854002c182d0312305080c80341c01e48000c514410f22443c04072034184003401991031201103511080280801c9101c2d110300842c01e004016200010401034004000b810a5880040c040d00c003180302807081000984c0c60209060031401019540c03201100360381000c4940e48a150400c48100e0128040400310720000a01c0412503005502480011180400300680c981c20040f000905214180007501c0c2206034540b0301e82a070b6400c0f10310090b110355900700fa4550000d00300c1d0310000b41c6101240ca0790902ca0180541 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 571765089 1250 571763839 571763869
    0x90501150617040c030f050a05010c03020304030c110a0504110a081305060609132001180303200f0f030306191503050a0902030703061b0e06040501030e1204080c 71
    0xd420a0303401c21a004210a82e64501814a004220085010b01c00300701c5146010310303002032480e40c6008003030070b006941c1c0100303520440e0f4561820a15810082c400d1080d24011640340c0e90305480c0c001507407504403030f4490360413030707640e00a081540014260b540c0b48142481d81c0c03140b000356500c4400b405009000e00f60b0007441c2d0f40300701d400e0000300700000b500882c1c916401101220850f404d45c0b43c045c0f05200c00c10307104400601d202d050780d10100001059002c4820f03800000d90341e0002541c0c50070b0042010460390300c00100499000040d107103403112040d001d00d6100007444100d402c80914140800c1c0703802440460b09450703810000038040c0c82c0c1031900012040006c040301000005141c0b52031703c0c500c606510000d40406a5440100301016081e400030750b8501c1d0010101c640702038980c102403000b0540c051000d03414a240b24000c6030030ba0302580840740400d10040240e81031038501401034010708900f400c2c03000e41e030007084a440f0409000d40701800c058181000103020214804050001042d400d90308 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 571766339 1250 571765089 571765121
    0x20f210901150e011505041d060a120c060f05251103030406140f070203030712080a0c08010311040608060f040210050c100b06091302090a0e01051507030c08070501090501 75
    0xc03c1c0840c1004405680c11510700c0901c1102c03550b91010115820302903a000032210038000000c0d0888482484100d5004032012074911425541c1c440d00308526900101004240c240c04013010440346028400d8901b0406481c10110b06d04800642c1182c0720250708422100700442c1844420288070041044500745601680110710b81800d00303c010304540c0340038100740021100010001d15800100081d1842c440c0e0240440c0d44644c4a03180c5072403280540503002c0d000480800004a035100079028503900c0340420348414406900f991102c0d1000d10003a100d142d0026114800054208010080203110300390001c00314185050500c100400d5544030214182000001d000703032000c1d08808104601030085481d800500d149070306001c100f1600400352007a41c0203c184010650f10413040d002000c501000f2260100c219890310340a0519900c28010540c20071100448002c00030010030090018038040e00340480a8a0103598002859100038400c4640380d45611410080000c00d0040074600c12184070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 571767589 1250 571766339 571766381
    0x60501051801030b0411130e210715060e010e150414011503060b0c01020403060b060f030c0c030d0204060f030c020c060904020d0e0102030c090a0e1504020f210901 72
    0x3418040401c0103010140502240c1300104003001041890351442c3c00c000f8080310000651108043c00504005e42002c02c1030241000d0110261001503000c0f000202e01020707103082c082c00788c0302c3c10003c05040314000c0710a560b5030000300e6a0035140d03201c18002c0402c0301c4a10749910301017050131050420491120301847c1041d003075480d0707009646150303410764804600d01c01c2000150601107000d80714560000c200540002080c003070400c0d06400500940f4060300040c0440c2d20240b00b0701c2083d00c50940e081110310411b0001c41d509148440017844118010402c0324140001d10007000100da1140e403245000c108001c80c18400181c142c003400b0b500da802070020340b013090079900204489100b1000214496540040c102035200707030691185809811990007103403281f078480030000da00e5001c4469180300301c0301c40304005542c00424510314495000000f10111401114007448065000b00510f030144510070710100e20513030141c00d84290300d004207511001082c10441c3c80e050850b5a480007180c2100e18081c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 571768839 1250 571767589 571767619
    0x162d020f010804020d1a010503070f0e0a0b06042412020307170613110a030e0303011a070f0f0f0b06011106040206130b12150a140f03032506050105 65
    0x40d00e10341052080c200340106654030b20014890038030b9450000c0011103655206104045a407031a50705030340007902100e0050352910310065451625100350729000c001d09000529990607500500c040c1d10020302590300b4103450309194a07240b0006450445040c02259441b0013950348071b20000307124061b0390340440c40c1d8104800c000303000720000030700005003900300c10201d4119203544030011000302d100320080002c1000015140c0e070b1036011600c4900024104036004616000c084100ca0480e815503041c41028006610310b0341d0241c100b40004c0d00e92503021800c810202c3c1c010b102c1c0d03c000c940b2410f16414405d81c070b454184203820ac090f180b5810010301e4040c00703021001c00100b481c0c1054045401a45641c1808217402c10312940b500300f101d414002141c1141c1d0b1010300840c0078003c2074a40c0902d0103030a510800e0085000d41485048160b0001a0120ba024100030545031510b001c0a01941c0ca00a80c4110003980c8100b00c2c48505039056980022500780310031441303010701510040f10700e101040000c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 571770089 1250 571768839 571768849
    0xc070b1e0c0a230706030504060b0118060f0c140c0301060b0c0c06180d080c0709110a031a1903020108090111190c0b13030f020a081806162d02 63
    0x120b20000d0070100710b0800d040806500c800c51040d0b2041d904111040301c3c1d112400180505802e40b021a45a030810341313001c01c250300441c1e885800d02c940740c0c000f0501d00d241c00c200702d6000c168000d005040c040402c003020007007012105140310b902141c0004084c914408401d242c21600150b1090340700d000306110b0b20201020110341d041d6041c01c111a01034840b24401c032100501c2d002c1e40f42c4d40d82c1c45400b00b17800704100f182e46005000012030f1031003540c0400d03984548440c2510150b15542c1c1d005a010815480010302039804900303513070803603005005118100800700d002e91122207244c00341c0142c418010400c560b0702003440e40e40090b840c0300074442907441c07950f84260760003018401c1000301c8002400c161402d10600700841c601da000b010820a82c200540428903081d903201d400c0e070008190604031380340640009000e82241d40c0c011880303460800c2c482c003403034003ca00006005030300c03179401c000349001c044850344243c1d41d80303000b818015032910007180384051540d820700f408060107000c4801d00c00035a4503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 571771339 1250 571770089 571770103
    0x30b010314010603111207090e210405030604030f030b1206010801201b0a0b04030c0c05030d1e0908060a0501062c0d1505160e010302070b0a110c070b1e0c 68
    0x4c3e220711b1034454501600a080c8070341d58201c40c080c18500554008686c40c002a0318030720011125101248584020340380c0d1440c40781d030282e150141d000c040442d0007e8400c1e05400c080f6031842c0b40005a66040000048080580842c1c08032503920040042c071040000b07210b6010030039a024002c01d64203071007400a0700d0a0003944500c000d0702d0a00c4440b01c8001c941400709401e1a40d02860480c41407400d468041d01005160f0410b40d1400c088034004901d9040000b51803058211a4844401d80d928400d520711100d250110260104450300100041c207000800c00240100b0010701c2c081850360500d08005d00c1c003101d03c01c0e401603402582901503025164100c80300b658080c281d9007400340820500300b4250841140d001004504d28100400160100390300e80400d55000660300c100358944688011410790017a4403010b4009402007011901c01c087d42d91000300d0b200032640c4800c0c28890551502410044542d00c091030601e40001d804208001000d4101540440c1002d05403c02c1700c0c009000c1e0b640c000e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 571772589 1250 571771339 571771373
    0xc0609030718020421050c0904112e020102090906191806050a080d02060a15050d02030c100f08100312110124060201050a06080a12050d0204030b010314010603 70
    0x401d0303808410700b10109404440140515034a8560b800100c2c00c448114a41001000d50715809a00700118030f074500384840c20b0140c0e0b004a40350038014910000c11652801111600c00b00c140038400c40c000d03034903500d070319006280c1c100e4000680700c2e0051002d1114885008254a1240c001c00b0b49035051040103c21303480c162000d0bda02c5e00c0708298480040e02c014211a01721550110000c00d00198040700003c546110492a03400d0314440d40300c140800c41034131a1842145194140c2140600c0300f42020406410501d000504440c107008015002c1403400c84a00360000001e80310700130005040c0c3d084000340340c1204404a071100420701e50345450001005801600c010010f070401441c107004002d4001601c0941503072138045040d0121486410303407000a110f81300c0554240400203010380c1d40d5200d080e0864000300d020300034119156884000103032a0140000c14000144040382d00d003c107500c00350020318450080641c0e1541142441e40070003017124042011070381000014000070300b01c4030102c50108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 571773839 1250 571772589 571772609
    0xa0e01030b130c05190315290301021210030507171c230a090b09030a0f0c090603051501140307060f0c0b041511070305120601090819050c06090307 65
    0x802d40f41070116501181c0c026648004100400b02c10107000d10700c001d04407403051525010118400100c641640d040003840341040c001c2c101d0000c18a0f012151813880c40d60f000b00010b150060350081070300c40240c16103040b02c003046140b1042c000c00c507041204034044d180140116112140c1d90340a20399507070125a0001c09000320450a0150310700801d41006c5041403144040070303000c418007032105a074011a00210014007030290002d0362040703180403242d03024405005041807601c00e455444d006170044400301da121028040000704a0480d12440c4003542c4160042c1c452401e204500000b90b45060b08044000c1c600070452614030303980000d0202c03c0301c000c0c2c1010a0022080101a00d150103d0103014010400c200100001c01100440c040130b21a03162000300140300d01e00d200300c03215002e407a1001f00070900810a05002903090060aa807001051410001854440c0f283c2d5040c0540401c41c095a2050b010b0300204010f0140b1400411800035600e030f9083c5107145000a076507202e144106482c01c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 571775089 1250 571773839 571773871
    0x4110d24090614101d010b0c0705090118060b040e0a090302010605040c2c06030408090a090608030a0906032702040f1d0d090303090608100906060903020a0e01030b 72
    0xa5041d400c2881d1858201d841001080d8191a001009801c02c98041c03240903880070000c2039002076080401035a943d00c2110b41c80740e81c00c0c1280c107a01c9511132054203205108102000405648540840d0b01a040d0a804940d035102440c4480c3c040d1802e60f000a0700e513203001e00c002e1200703104174500d041e400107000201080c040342d203080903801070013250003c0d81c10604181000c41c5003601304403080440a200803c05030407006800c3e00304600d64842c014658001000c0010a01190591020b06a01c0078028028204540e65044100485a65030705c81000e9400202e20542d02c285c000760003000522480c01c0501000460580412410002c0600b4080b60758500c40c061040d5101c540c04104050102d41381007008404c60062420262808064001540b103120303010120588544030180440c0d906803500b0000760700780681601c00407401420448803070041c5500040d400b609000e804018446038440e0101203082d03005010b010340c4150000801050f002d001000095440c040442d0b0224200409481e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 571776339 1250 571775089 571775153
    0x833060907030c0c060507091d0c0702240d0903020d021f02071704080309031b011b02270a0b0103091218030605010303031406030c030c13020714010504110d 69
    0x5410007000031708101c0c9001d04000359940c0202041e419605109804900c41301000d0380b502208008903010b000c4490144285001820620500c062024020400340da5821a10444010b00d4100c002c2040042703444103006814140c05100d0714000703110304c1c4046c00203070004440d80c48a100521340b80d540f80355030000b003010501c00c0003203010002c815000305c0c00307a5490790780000036500d4005d559058440d0140c1c0f041300403010030750032113405580740684070503400c0094014403c420030340004060303070407000880e031450342a00c82c00d40d40c0361030b15240784080300241080e403010310884040c5031010b414903141c5a43c0f600440c2c2045c10009a40100e0315003501c2d840422451040c0e0002c01e0340c0000e002e11b0915002004058064010182420080b160300703c040d61208201580c4100100c42944c054100d19a614443d0400040702070700d000100c800989001d001d6980d102c4400d0708814408250f954900501003000000501050391305400c59420b0304c0504240c80d00642e4071102c00300688244003107003416071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 571777589 1250 571776339 571776347
    0xb0906010818030d02071b0819080f04080f0a060c09050a1412100c08070509130906021c150503070f060e030a0213021b03040f1403070833060907030c 66
    0xc001301070038030641d140c1c5198a0300c07098030520080139010100c07030342e02d000c0760009001640609044801e0403809281c00d003502c40755203540c0160704803042080c08200101d401e04082000300c1c54040c0701d500600c090169410100211200400c40d1020400e03042c03070030015952400501c0d001e403800450b80b15043c401c00c1d000603000b10301e880280e05480c010300b0705500074440f040d48441d0920206440300b40d4a941c0d00b95080783c4502c100d000c06a407062041c5000c0740003060030741c070401c100342c41484014548100403007111f840490900c1c0c4e0f62004d80e21000c4040b400600103881d000141001d4004000c260305028100242600302d00070b080400803000c07060355450b03408000d8506099005003a90031862002c0d1292406544440361031250b803480068407403480040003044030115040700c42407980351030600944602e0312855810b100d5040c86000c0012500c04418403510000c80b0690086070b0106221150b880b92054404540c0b030310406c9103608004c500c1d200d2044040d0310040c4c82c940000c04084c0c25a003a6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 571778839 1250 571777589 571777597
    0x220b1c03050d090b0f070207090c05040303050a020a060f230f180a12050301153207080a0905100c170c1c080711031321081c0b090601081803 62
    0x5013444424009004100b448058800e0080c0219425500c0031a111641141600d464a407000300240c01040308001203441080507044801040c03040e10344800305905c40009071030215030038100482e902c6072100c44002809102500165011504960515100001a82c18200240180c2c8008103008078058840001d0000f4419585d203c241a0b05091440b40c0060141d002400f03641c0329804404840c484071409003800200c81d484000312a42c55040110f07103000040102001c3c03a0500303605000c0340c40029010300140400e0001c60341c03070080722854201000b01103000300504000703200311044604080b520104010a0044401541030380c0c441c81602050700d0810149005110011001401c9100c00d80c0200018015003103540c440841d4140340380e000d1b40340e100c1c04400c1e0301c9680c20000c0c104814030848200c40500d0704d481c0411a94903000e41c9807a1107035400342c8a03560422061200c0b5516a010520503c60700d41410341d11030340545400c0001130f08030b034000340141c030982407103075a61400759804000321 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 571780089 1250 571778839 571778843
    0xa03140a05030a03091122021602130b03190f030f1202070f0308010b0408190501140c031905040323040807030f15021201090c020c220b1c03050d09 65
    0x1030b5070780d4415a100038020680100b046602405400c06d024240c6002d404d032155800d01c0817100c1c150301c010141200b00a511000c40702c0f0542c12102c6d00c400260303031441500f401d2018807901c0803038454105000c250801d24200c0300c4504404004003844041000341040c0600244e140c105000d00c104011410f85580d0b44101c2400d00c003038000200d400420151131500070809210fa00c0e90002641c80d040c4150440c00f0710300501d2469030100c0c401000c01107a0382410105140240000501140451403194513118100c5050725010000005e0140c16131a00c0000703500480351a008000074140303541d0081035000699140300b94030300d40101d1100c00d02040c008880007080c1c001f049074522581c178680500207040b040825200a441c3c0184140c0ca003209008541400007070541c84d2040ba0f00302281c1c84018406204800e013184140032a03080613840310241c1c45156914502044013a1202002e1201507076022a5002e0191076240e01c254017040711100410442030b0306d0f08105440310309280b0360300e000f01050480 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 571781339 1250 571780089 571780093
    0x50c04051c05010609051501180902030f15010c0b070503070e042f030105010905190b270406140409060b060d02070212011404061a030a0516060e0a03140a05 69
    0x108411825041c10781d04550703101d60028802030343d4880d01e001c1203d100301c03070007034103003050460141c0303558813800806a04105808420b05202e489142d07401c05c982045481c200b54140d620107020f100c003052101780307081e00c0c400d2032700e8112141c6580e0351407148000503018006024001c00401d0390303240981b070881c3c10090041e00400c4018a040c1e002040c203503014a410f080e80790b007486000141d2880c41d00301c906071441030b107030117090750303d0902800f440740d2512082640004c1d502002241107610200200900c4c3c4814261640b50882ca100d4514085004500075108a00c3c004080001c062003c920040a42080b07900096100c01420140050702d2000b51161303000400044000d03080c4a241c1c040e0001a00907176100040404025183e0301300c90321101c41d5810840070400207400078645402004283c4086061420381e030446001113450300c12160b608607180e421880303181030210348102c181030050105103005090380a214000c501540188d000c0500025000d079501fa0482d0020414003441c5603000781 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 571782589 1250 571781339 571781359
    0x100515040c03020a030c09140607170a0f1e021b1c05061e1b0307120510051e0d1106070f0311100506091512070810110c0a06050c0405 59
    0x1c0100254401c0d5080400700c1d02c0d1050510541d4440c2080c032098031494800741e00080d6010f400c020b110b030040c0c001211148800626240241ca218015003050200e0341c075515812011844040d000860506442c40c0d0070051055491015600051040e120002800000010000c04000c200480480c6060501c0c1c00d4030b88840318108031001601c148200d00a00d40c2c043c130003039400d00e900c030802000c0c0c4a00003000640c01c008a0403621080046802c0b0b66242400740b10030f0b1159040e40d007642d008a4000d899058008410040d5080001c0d01f069400098100810a91004400211107081e58040604003d1a060a814191311403000301c802c2c041d00601f00c07004407001e6242c0148401d40d455240ca0031030040c07038004640064540a40c5014000c020109201e0795501c51403020310000c561016a402903614040e901d1510081c00745102420410001d006c3c4000c1c0d118034075003511590540104170010820140d10842808910384194a5000c4c102091a4031250100e26150045410881c5d01c042e2081f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 571783839 1250 571782589 571782611
    0x405030726010c0f030b180106080603010b04020a021207020d05150108010605090615090316090903021b1026010f061b0803191b05130e0910051504 65
    0x260398540001c1c1c4008000c0710a1500c8541909031a00300400701c0100d40c0d0403240a405034040c2e00807103901c1078090f050041c00c05170116001e00f050006c0e405080402d000d1003d10509040a0103415001c2350140d0b001c2d450196603501c000d5840d0b04201404075a94801714260003150307991400c0303100b4030b904a8100c0d0010301405d030504807151020b01c1615115031034100000303803a0400b00b405520034600100505541c210107030b040440c80d88001003a035811b0143c4400b14007910301e0b00e1003850140800240005004603a841c020749403484803040c02901d1012450b2840013945c5602075800c54512500d05000e0b4603405014400b07441a00d42e84c0e514020195030001300d611440415154122408c035925000700303081040c1e041040c002c01410140030401300f000008c00303028070350325038001e0550070340c90000d1060341034001c46003100107066550002a0340001c0740c0d02d0061314800b11501a120024010324241407a09004d503031004903800c0c02c1e40d80b5480740002040c010441e00d0016404001803c00c2c00514584 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 571785089 1250 571783839 571783859
    0x80108010515150a021006150906020d17040206070b150a09050103020f042a0824090c0f0d110d0c14070f061b021510030302030706050a0b0d0b07030513080904090804050307 76
    0x23903050000149144900040aa20010b1000c822101a456001c1c46d03d42070400b03a0520807005009907004181004540c00080840c20194071801c00351003501554003141d82008594056640180155030070180140302595030381e4115400108101c5000841160b54503100000c2d0403c2c2c40c2640400c0e0441034640038454003c4203461065a0003a546030b0700240001005072a900829444d941050302440002e0300c0b00e00e140010a500c45404c0280c5081c4145200b03014262001200880c04074800030542d070f14540014010409076880c10b040c00140c0d40695240292030b0b01810002074080c01c0a00360345001d00405610010209407207815018400c158450003a60b91036407a00c1a070111260040010025400308524030141c03a419405546054400d4840034082c25024189407903c2c0c0d528a10b00e0840d81e80c55914103031031449001001882e251000024048450003803c00006007802c0501c2030000d52810110f55048030304450018020890382404003180c000c80d08103a0b010310551701c0104030111a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 571786339 1250 571785089 571785119
    0xf0b0706050f0f060910080f03090f010c15021c0f05090d090b07320d11011e15170f071208040b180d03080108010515150a021006 57
    0x141030144074039100e0240c042c0e620403080312401092800300c1d01084581c81d00d40c510740c0e0804154552418100e855039030040c03c0622208814046a20000c2c600e50350741001410100d00c0202400d0007510079845840b0050403c0c1c6615043d1180760307002441e4072030040c0c684981f00c1c2c00315143c2c00c03c21011100c034030034500904060742c0030a440e10442d5080c0350000e00c5103020307005507034001102c5405e10b42c2d01d60b114521160260414440250070004210401482100ca40079513903030035000f4000c0e4007140e0706c040c21503d045440c61000307905000c0ca12450920210340000c000d070224400184200c20700d04400341ca00c900c0e4110341003030700b50100d28201e13111001900e5840003000b03030151411f03d81d460002c2c07004035209220003010030301e00b80010494009081d0181c0b030707055030401049440c2654032000500f130000c0d11104501044c0f83c18014007100c03409100c0d080c3c0c0114004030060b03503105044002070000141006480a00c0c0d00040c1c1051043d02c2072001c40140600444213120003034a0746044210812 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 571787589 1250 571786339 571786343
    0x2211040612050c090607050a0b07020c0a0f050a03140102090d0b1902180d032105010e090f100b0a090203100312081e13050307060b010201060506131e0f0b07 69
    0x9081c801c85909441c280c4181800b07090441c8426141c001d01c2070600001d90040e540640e054000c500140c0c01080c959541030b440340015074050001d4603030a00030402940b000d41c00645460302260014041925030800c50016240c0040b00c6011000101211601a105010880d5000310710b03c50304000704507201200303902448140c00000307000005603031a0030480c00307404011540303160340070030aa41600707200c2000250b1601070728110907a40248644190206028148026050307a24030040151602c500d2102d50404807031800b0b04040c0e001d17501220340c0c520070145001601595140c1d0710500b65103102020008002d00b0b2000c0d0340b01d19012494880340307038040c481900c1115007000d0080e40144180f80107480307040100c1c85000c80240094080c00d40510080c0400300e2505510f1036500032507000c00c054074026104000200c1c02c95410400242501d9440d07002c18016103040c01001c030425165412001665100000803074202a00100f012000c1c026500035820400c03141c4001c02e5461007000200740040c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 571788839 1250 571787589 571787597
    0x51c020606062b1b021518010b0303121006030506090f1005030d05040302040b03010908030115030b0d0803040c0803030112031103070c030b0a0507170402100201090602210f1522110406 81
    0x184c2c072401c0580e02c0700300c054202104007400c080010780d140d50181c601070101c1606d400000d007940103200444c1c9190704ca0903519041016400c2000144404e07605000050600e0380342c00e00c410b05088003c602b03c6c032405014220403003c04800a01000d04c849128001000c005044031480500700c8800b500c15401808140c0c007403420322140107900e050502803040c0641e40202024078580ca0414072040242410380c440c010540c4a001e045829900d0102c40f0054070301402407145e8034201840d1070000110360f5403107000341c1d400902c0100f25540e411100b4583d51070705401d089000d02c900d404080d046100e01d0030001d00d40f9010316004028090751412240c42505050020070143d152000156858100441441500ca041400160060030416840c0c204101503000200c5d500e1441e40c0d88034282d805c510045c4110050407030380041040811080250451400c0d600c1501c117051081c104002910806c000340d000b14a100ca03907200442000d003542c488003441e801c080251170007080c4200201e9200781301e804009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 571790089 1250 571788839 571788881
    0x12061503050a061a07031b0312050609070203180a030b16080c031315150905101403060105010e0a080a08090915240d02040b07051c020606062b 63
    0x42c031038840c950948400400307000c0a4000c1d403000325856801580f00f1001c02050b03940104c4605280d51846100d940b280d191481d400d026050b5040c00c84c3c0300106010720401280052020058003c8111a07035000881e904072802140003000c40c4031140550700040410b0700b8002000605055200005003022041da00c1c044161030390728010290b400305840c00c8003520425441c9e0400102c0e80c403520750031041104404144010f0802c00e8030f60780d910740c2c0c0c03010f12465119810819585803100c0c60602a00c10700c5040781d540c1902d0340c0401d0f600d60b030500a042c180210013070091010f5a03a16090b00042002074125510291149000c600390b41040015501031355112020460300000900b640741e0001d0b001d0688109d0004035440c1d88070950099003190082c00d0108072114030017025000610180c048203110980e20031541ca0800d20b002d408980915041ca01d0350428020b07954042181074003d001210140d407070305800c031400d845007141100c000d4071a4025003d4404092003940025002c44a034007003d000c9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 571791339 1250 571790089 571790101
    0x140303040c080d0f030510080a0606080d03060b04090507050c19170306010f0e010302310b030f01062604060c090603021e070c08060103030917150a09031206150305 72
    0x290f40e41c0d840200003c1481c801e03400e140148242d02c120b5000340c0d800d21050319a076881c101035090030200001920340507140c85051084460801a82060f16031601c0d00308815450480649044d028901407400005d46440109401a1017174090320882c10305c19059400c0c0a09110700742d0400c0c1e19032003049454a501182c0194041403400903240318030030607164040014401c0300d0844490b8440b143e16418507900384113026001d0340949a503001100012071444124903101000744009841d58071520610000300100054003002e2102c2d1411940705013002c0fa0000c0151100803580714152104010140000c0d080000340b100c03a421a18580c00c468468030341045d25080e0843c240d120b458568010381c1c6015101c040314214410045c4210ba0190000307203205074540c10202e09140003039205500150f01c0850030711812645801021481041030020307c00310007c0b548440b41c85400030140012147c0d10090320080c0340c02120405941001d82c042044000c0c3ca83c840003101e80b14000b60a40000e1601c00000e00d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 571792589 1250 571791339 571791343
    0x60606090f01050c010e0f01020d0e0d02151e040b060f030a0803060d0804172a030c06030c09090108100e0109050604020609010504030b151503070905130207140303040c08 75
    0x441210003501c01841e2088a40064800c2d40c407403036400100e5075a0b000300010098051214400d8451100000f40e030350b540e025030a00903600d4485091a090b004406800d8580303800046c4507504a00e9046a0301607070362000820381800f884124030000b0704429004100422100340000c81c450300040b00e01110201624043c580d6843c15920001c1035440100081101440d006000b500301d41d01c030701c8555141c5920b400b4125a46080e00c0b800451035800802d0040e0b01041580c04402489000f503ca00d03441c05d0710a00203503640c02d0600c1c00c03c1c00340c0350002c041032500c15103508640e01300d2000b0740b100c2e915580d203c824940d104203803d503100405140c10304240c0c03071481c1070181105054110700104141c0d15282c00b080103561205170f8503410300c00100070000c00104d485d200c2601ca42e00030701c00490300030320507424004c03507040300c85044c1d0074200100304200c0d07640d402130582800da034016514001c0c541800d0945000030720407540e02070f00c2028040d642514a890020040d885244036050720300010ba80d5403400da0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 571793839 1250 571792589 571792597
    0x20a1707081503030f0d06050307080a210e0301140f0a020c060f0c160605092407110115080703060612020312090307150e030d021b0402070f08040605040305060606 72
    0x1400a07026101140304240721070322006080000400380c1e403a0020b620107103582684440110a01103803111410003880c5401e01c0640700410b20070300039100440c0c540c1d40d8014241c400600341a4a25510151010164850358901141400240c020840020000349580b10310340c040300e10b222548600701c00079500b4075040c004e85503000081002020103446098040d5180b800c010f0190350303051400d011802c0034100f46202002e0307090060100180300d003407096005041c180f100361079420604101a0000002c00c2d44c0b60702c1c1d85e2000592428880031008402c40f9800b43c20040407030344d0490503881c2c0c04070b9640000b080680c05c1324404d02c010010345a5800120a0141c80943d029526400000c0c41207025080c003c0200300d80c04008068504107030311481c1c09036961070744504003000500c8594110840307040030001c8a02c581d6682c002891104464094611140d044408142c000c0d50082580b504000c2c0f0340380e117480748907808400f00d80c40d5038840c00000c0c00c4d504140f0007070302e591190001144242c10038800302d03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 571795089 1250 571793839 571793851
    0x80c1b15040512031e0a0e01180306051504022b06080c0603070e0d060605090601030e0d0c0204020c06090c0102120a09032406030308070207050406081c11060703020a17 74
    0x100341028902402c20a0002c0c0b43c0c2c2c420001070004116001000b04c440301808011080180714580b5181000c1c4000c104503000907071a41480300c01c402000304160580840f030200c03a40003101045682e43c403600c2049400c1c0c0ba0301e180380c000c6c0c0041601c0007500003a403107442c941d00345040e1104203e909440740c2d005662441c032a410b406d802031590794845003065002181e1080300360805450243c022004152070260b0004142c408543e11801845203180c20131045411503400d00e0140309445803003102c16140c411015141003885050384440c82103480d40c0e0103448104030701800740d9100740f4103000500e403240800d198250060003601e041228080940003520581c0d288ac0d0744204115082d582d030302c403031001c04411500c2004021602194040701a01418015500c242c0c0c81500c0c0e400d010340041e00e49200c030340046114a0034200140000103000607000009a418065002d41d98080e050a5540342210603030104035001d00b108014442c3e401d41c0040c00d5180b42135564080c0c0b518002c2c103041503004242c41c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 571796339 1250 571795089 571795129
    0x402031e09032226120a05031617070305150d06050601080c070b072105130b010f080c04090c1703070c0e0c090d060608012a05070f0b070903080c1b 65
    0x248078483e0640744960090220f000311900b9045c0c2490500c0305400000c2c01300c00003040002003180e82a00038029a041b40005d0030a11800e080c80300030b0010841004187c0303400c2503500c90024014540e100c2148035030160103820303200103880504000015150480e6010301107014200401c04420800c001c80700c44980000a05045840f0744608aa150200e2540001c5080f4140d41006c41d540582c4201801000031990b0b00c464007040d032909550800e030507440840020400c250410000350081041c0b42d60748021500010000d6241c54080b40703038540364020503d89100001001c4421300c0000081203e140940500c18641e55210078000c04440d0860320105c2d5040280405265400d00c554404c3e2618400c2001240031915000f0300390840e80550400d210044005035a0341020407a619800030703800141c038110f441c10140f52a0242554002c520040a8402d11800100e03420701c1140381c84003030341d4003c0d2030039030fa0302c82c13940c80c1640e07070503031146150600100c80120010b62400140c00c03c5440103400c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 571797589 1250 571796339 571796369
    0x1050d02060a030902190e07021b0d0803040620030703050c070c03120903080d0605040f0213061107080601170105091c180b0a050403140106030f020402031e090322 72
    0x10880240020080403a0000031038900c09460600d22048030303000e00b00d1087e100d00d85181910009150441d88110211003081c41018012a9111a02041801500000e0b001d54980b110b2500200401941c0d4116100045451209400c0c805510040d4000c0c402c60b58107100c0c5484102400e012403051a1000f001c15124607001c00008969401c0ca841000c00b5050031511381d40e83c0e44030041c0940c0084640702c1042d94a6106200c603180510901d10380c107058080843c1042148000303401391800a004201c01c0c40240e9885441c030f604100100e070090440d1406660055a481044a00c0d01d412170102e84802d508100003c0c17600318002500d1148035802000314000e540c100d00058604c86200c0319003503903038051a50080740a5484800503d03a1540540d24181d440c0d280d0304044d11504184407000c02c40c2d90502804001150322000d8484419804a9005030380c2d4843c0c4e480d084003440c008a01d003003481210b40801214400100c0030300b0518410715034011214035804510920104180111910030310494 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 571798839 1250 571797589 571797607
    0xe031308060f2809020609120607090605040e06010c21030903030b120a030e0315040f0203070b030903071b03021009170102271504030f030f0503091e0c220501050d0206 74
    0x40c01240449001504092400c87c44001203010034a00c030150313070307080d0b031103c024000c40f180d000300000000d00c290b1a03c46c1c200303800d042411003120f9000d0001d50400000c03004c1107091085101811008a0000c0c10701054030940c044050061b00039054180d002c646000d0000c5020b0520105d04031000820b2030240200300c001c2e9a0591320480d5204215070944601d4002c40f804c5031440140c28040c0b03020304607801c01e55520380704152030200c454010348003014080c0180518040000203907109694403c404415030b00f0b80b0001c0000110366a80013951003650200303080900d9801c005000141c842c1103c500300c82c0140c0c1e42c0a0740c240d101d010300182040003074410034000f02050318180c12840000074034401c100308644101480ca500541c009443c4410044402070426800c4526046106003e062080c290b00d480c180298807810700402c207031841e40b03810754000b0030500180901100150001e180a1740802142500701c954020300f80084c60041c680070010460f80342c60440c10103003590080401d032525500b5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 571800089 1250 571798839 571798841
    0xb361920030426040902041818030e030109060c0c020a06030506010c080d060509071e1d010f1e0302090319082703062518090e031308060f28 62
    0x2e4043d02c0125010002a002c8001001800203110300800540c4460410b10440c2119403120110b4014070b1a010824044540c0c201380e00e0220764150400b0316a16401e8000310f409800319003401003030700e450b245400f2810368000345a0b0503002d00035643c2181250320392000350308481090ba0b45c00d000c106c500822100291140c80100710b0001001e00100b4040d41d40d902207203900d141501c0c0c88002c56222913a14450307002c1000d0840307403c215850320000c004240683d8403030030090030000c1c504110040c409002d802e8061046000d6000702c0c070049074265541618014000d41228007007034864042c02d4010041404d0041c0c1d40c60405800180f06445c1111070310900001503a40c01e50345000466041c42001d5560f0140440743c41016681180000c001d00301c0044600c0103e06a031010600c404842011400e0145e0b0480c0720503190050000255002c807203599070b103140901d40180003211621113000c0340030760000c00c182c0c0c001d002d620103d03403240c2c44500c13a14254110010b90480e00c0118000144105225 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 571801339 1250 571800089 571800113
    0x12110d031e0908010c052d070605091911120c090601111c120f02030435040f080d0219030c1109040c0312030b3619200304 54
    0x1d801c0407507541c0d82d103018480c00c0d82c1d0300164080110700c2c0801c58243d41064181d101c9005001f80e04907526204200708006410f0080384005080b0340d907203200103910315404111401c8144c0a1492500390202d541c507000302d2a510301c0712128069091460300c603801c410000340c180c1cac0f0840d0042044d401c0c1c0d61000011a003005107070301500d08a225000000803940e51a01281c54400c0881d030300e202808085d00c101c0310560341103400040072244100100008540f2a00c10b245031413100744800c1c143d0090129246000340c00b8a004014201e1b1b00040c0020098038140d206401c40c1c4184003619810780c0d5403001a40c40e00c1e4030f03089003d10b07501145551000a0300c40c1e500110014800c1e11044824202907000c60302d01d540441d42110010310301070040c410710000002c040038202d0b0920f4140816542d0b41d0128035041148a0f0102c0d41c0444049107601c4c16904407055000380c81c5108031070003913207807001c90100340c90b83e070101011646150404d41c1c40742c1103480100300e01c1046c810300fa2614607101c9994031104410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 571802589 1250 571801339 571801397
    0x607060626070b2d0d1104050102030a030b0307090e0a060507090810020c07180c030b0406060e0d050a060c050712022b1206060c0309050f090c2212110d03 68
    0x641140018550315036030070700c404403108a030718162905400d50f0a1006c480c1d03003110304034003203c00740700c2001141ea0010132510031000514020502031f100d00b010034a0700b10603400c10219181400d0036490014000a03500741054000c180c28442c94403003010540d41d40606001d042c4803500030380002c00010925400070480642000300f110641c0756035100f00120780c00145482d01d001a100d0040d44a03c540c940900a1050000c0791b04001403132528102038032500304001b440d806031000440c0402408400c0c031042d0768264009400f4407c0c3c640008009207a0303801004115002c81030100355101e12480021100d100744469142d425040380b200341c6c0c16034090b0648c505002080a102e0102021358a40d02601005041c1910781c101c1d074001e14035002c2c044074a42d0300f0440c052000d07110442603958905613800d400c4402c0d1079038140e40d01910792521405c110390604594010310611070000d04d40a000c094105032900515420710b42c8121041008060940c074007001d0300180030a80e02c509042c98028041c02c40d21 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 571803839 1250 571802589 571802617
    0xd020d08030c041a09040f0b2211040909051903051b0a0f0303200306181b07050d030e0a030c03110a0203070305010c020637020403020607060626070b 66
    0xc0d682d44185600100344480b42c0b44c0544080b0350881c0034140303405400940e020310300040c1301348002500821204030358840f041100c85040700f03642c500c10710540d0000001c090700c40300c000e07a526110122070001d448144000c0300e86220b080401c10008050004259086915507900c1d4500804860b201d82441ea20240c0c441890040290800029400e2550359074898403e44001c101161425000c1c2c0b450554041c200344082c030100100b2640d03589018903140d0000307151382005030b5a101c1c0300c900c5040d1032041d5420300c0880301c00161042404800119607840c03444698040c008100d441c09699203456070360b440200031401c00029440060300500c20103100c042c194040b1a8107080c56000245015200e9100340c4042c0d649091802c0301607410701110794081e460b101842d0629800603c402041044441e01048011202240d031000e60110780440300155001007000342c94034024105070b801030065118807404840700d405a00c520002034549542c2d00600e140c0981001440c101e90700c042d90b4407111034424a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 571805089 1250 571803839 571803847
    0x80f1204080714060f07050105071e090e090c100c0c060504180b1201020d0b0a0b040f090e0307060f0209041413030e0f03010204080601031214030a0207140d030b0f0d020d08030c 78
    0x3645c50141210300e010b1000802c15082031000982258185519043c1401442e80400e00d15500414004211802200300b8bd80ac2e6940d0340314a41856602d01d2603e510046035800c0b00491035010341c5540344280184680e14006940e02030a5a5030303c0b42d44144c03250a85020801c4414200d6070384000c81c00c5070054000f01410f400d90f40d0035400c80c0d10460141a007a80e071501803010178104031901801030140d1704080c503d0107050a8081d1040b6003a031258440081c4c458180004c102c50600c281e4820310b500c664180a101a03400341c040c080d4211075001801223191401018201718610041c1d8041c0007c0b0402003411021500c00702e49109181c02c819401404444240300c1d44d8400340b00400c010144000a010254110328017613000d048840280c01c00c10400413415241482403c044030703040580c110006998200b503141c20b524240413400800010302844c048410000e030107400803840041e044071001103011402c01000760941c4c00e0f102c0070350803100383c2110400240b614001160015800d002003800c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 571806339 1250 571805089 571805107
    0xc032714191718100306050303120703050a09150c020307080301090b011706060a0e0d021207080c0a0305060103030309080d02030403031a030102121b07050601080f120408071406 78
    0x18000a03484504082460038080704140700704900405003800030500c01074588189040500c1e001d8501c034240d2440303894040413070142680a0351000006080c00350541ea02c0d01304030a01451210303c02c441c100c0121f8188000180d225410b4420030105075481001d42c3e1203518103041000082803010b80714401c0d0321003001400e001c200b1030406540200002c100c04101140f2040004020324809201c910344620100140a22035940c5020344440d20524545480c188a051001030740001000708082e40110807403c200e6006100405c120302511018000c072920b40c0ba500f014401c06050b10701c4050b1858101c2d000500020740320b034000d50a107500504000d0b080851114214040b40e1003504d08401107075a0b00f04418084c00300c0d07000da13a10010101d00850071b041050103402c2031a04020800198080c10300d491200022180c0140c0300e407a0b4008084801644c0c481d40d03855a200425824410320f07206030904601803c0941007211700742c503564009414490b20308404a404200724030852580b181e000d21071080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 571807589 1250 571806339 571806343
    0x60b0a0e01082715010902070203010b1c0f021305190b030f0709020f0f0d050618060d0b190903090305071520010609050c0901091a040b091c080c010c032714 69
    0x13000e0031b2444d90040c0e41300402e01c101400c441402101038000c00540c09100ca100d00840c10784076109070041400403950794248000781c409804079038040400c515000c1401004501076207007400050a508082000a00e60070415640300327010601400f003940031010500c40d02c9407a8015049001245081506109000c03a0306810341d0401160040c22940e142c0401802e40b034400302c440c10290001010001505140300850a89440c1c0c9002901e120740c40750204014003002e42d2001001f0900c40c2080044003007924000b4807090302c500c4181c030903119040022070306d01c8a25039000c4240041e030b06e03001110300802450700b917044038811a0031059566080009101506030150301d120f814000300c0340e5910300400c3c3c000741507443c180e0000c42c3c44100459986002d207208008032001e075800c103002691150490703030009000308005541c10072072624042d9031004204015002e8401c00d01d61400038440b10242d007100300c2c200c032a01501c5015821811045c0b0003804407111303252002c240503034440c055450042e201d40f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 571808839 1250 571807589 571807591
    0x3070f12060c0305100608100b030a0911030111030403081e0a020d200a0c0204021306020a030f0c0f0215210106020f010b090103060b03030409060b0a0e01082715 71
    0x124486012400031010040d840c071038091aa146400c00300440d080800c801400d08845001d481c05016041021400c6100b240400000901400141c2641c0345028030514000d4901c0b02802c540d194403c0b4048540c07850107001d0110642c0424140c0b80c03d550320354400b00d036210005042002c00000d081700303c502005464052503c110110000540d484c0c9003c05035030112042400340840c174012480c464440d41e1706000c215509088985070520004070b00c0d00005000344200e039004850040381d03600000301b0540204070074844a00031f494852201e0216401030b40c1d1400544001040c081c2922758060041c80c0c40f161030140410110b01850a0030382d0030143d41e50700b07840903d2000300c0c01c55840041040c0c42c2e0401200c00c842c441013009110031134840000c541d0402c0180002880d007512070742d0310340075903d080040d41e00410310500241b14442e44d03011043d4582e84044c1082d40081d1044000304d02c00e50041c00c04500a10742803022442c0305c00030101403680d54000c0300c5c1000090207172a03264001042202c90030303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 571810089 1250 571808839 571808849
    0x53f040302060f36090c0702031c05040f0306050108010c080907090218030a050a05060901060602030d0b060f03010b09010306090c0e0f0a08010c020726030301030f06060902160210020f030f0903070f 87
    0x139803080043d2804001c0742040042c07a83c88404410462080142c4001c10f58400d4042c00c80704041d075041d0f603207900755800d02440d00300002c2500020000400d001c0a030f04298101e0305840001c1050390105001141c0c107000c00c0b500001e0740d500c501d00030004d001d142d60007001c40c080c0400c58424080e00d003c0c0024140850340c02c3c281c81c190301c0b07860180c3c1401428420341e500401808001c02200d4070b010343c0070b1f4803400380309103580d0306d90399400c075076007683d19180c0844040700b0130119216504c0d80c407000804c500d034020200890000346070407000f2503500d45600c14403178106502d4480b01907100703001c2d080162941d0003500460b003001e800400011021000d0054852145a41d005070001a0601100d440100c00c1c01c1c002c000804160003a201c1092004400c60b03042d43c0d0480d81c2007140b9070782030a056000d8030040d40030840c0301e84000f8212303503900341c0c680300500900d01c2250b1001c1580707005c9000326956100882017454582040001410515011000b45004540501030300d00749035075540300c00003c400382c3c4c0c82 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 571811339 1250 571810089 571810177
    0xa0606030b04060501150e040e070905010602071503020403020f0402070204061806061404060f0f030e0303070305010303171b18040e060f070309050601050409053f040302060f 77
    0x180403c200c10f90044502500c0110000b540c07190f8024401814100044d030001d00560780d500402800c013a050001c0000340c200341d0020300c01c95948500c025500c40091058110031030f142c00c00306910703038440e000f114116a0000e00005204401c0c804003c002d503c0100c003240c1c0319030794070800621010840d03880c901c5444003010001c1c5d11031914001614591140c04040d0100d9004c01040c024a40c0000810440e94040d113000042e8040080c02500141085000101341d0b110210400c010f03294503800c80741c1070340d109030f44102120704a0b00d2204456001556040c018030103442c0702c0e8055201580245c40d0045a0310480c00000410324041340032245c03113240c009180d411040410511100000810f07420142c680390810483c00161102612400103006103481243c0b07400c041010b00c1740030071204001074040c5075001c9014040c0450066842a094044025408029003220b180f0360050141c3d422290054510b520304440d09403841c80507031007200c040c001e280703080002d401182d0780c004601900c0100030b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 571812589 1250 571811339 571811341
    0x9050109080901180510030b031516090905160806190f090e060f16050408190b0108121903060b0f180d020102190201022103150301020f040311030a0606030b 69
    0x43c040340c0140400014803684c02d50801c40f40d185c1910f01c0e07940521600d030020310300e2101c40003c1c1c03d208041110095200c84001408600d541c480070b079102811181d100c203c0610390342e480e1081600d50440f9041030f1304e40340c202c40c000d420340103000d035607032000d0010144224102d40d8200742404207080d41120010400329001030010200e9071050109140c5550000c01c1d80b454902c048245c510001030400090444407142420341034001c3c0c4c160380160040100340d40451000203c06000c91085102c240d41c480150800020711721004100c400a00100010162400200000f8076402403004601c038010142d540b0300000d81d801c0990003408925591024499449114003000c03003812010300260303031040c202c928402c40184c0c2c0000b0100c481c00c0281500c5040145603000503801e004409000351a02c0d0358401c4ea5034a0036500000540c491401020300c2c0d416400400c00f031500301c0c0240ba0485514502c2008144003041c103242e244184100010300f00c40c9440426610141564225842181d03c2c04070342c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 571813839 1250 571812589 571812607
    0x90c0504080105330a090614031020220b040f050108060105040603090c030b070c02090f01080c090a020405030a080901030c0309031b08070614040302060f0c071101030905010908 78
    0x806001c0d00034259007240304161002c84c0440c1c40e5031000d41403803079240c06080c54011180e11461810801001030440c1000f100303640b4410310410408240609110b4040c0d4004134091802600ca41c4e14520050089004101d400607100c2405a01003004d0941507071b0080b080c42d4000100c8080310740903142801d20291110700d084651440341c0e03080e0704480d0610104500304209030f44c0c400d0a40702141c60901c0c010804c62428205003180409030b0f08050201c2d141c1c41e0030040d0154000c500c01c0700e031920a4840b924241e84085254400d40401e01900007507030008215501d01780360400d032031500100424001481d10b0b5403480001d04d01a40c610307045a1489011400885030740e09445920381d07107407943c00c050185094681c0c0087c003554800c00c94031941c1003402860300911407a20301360703a09941c1c071241c100190ba0010075200c400d568121421401441000d00062040017060040c90180d013000744001d003001415035a0355801e001020145040540d03030300c40b5101050003401800b500343d000b110b4842d5606150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 571815089 1250 571813839 571813841
    0x109180f1d1f1407051c0608160e0f07050c0f0d200c0109090e0a0611070b060d1106092704050d0c03051602061e130509070206061504090c05040801 65
    0x401c031042d05281c8260745980900c1400c042d540040326151250340d40b81904541c0a0441c170300d41d14001458a003440215030641d000482c485094039030b144650249a480d100c0c1880144101c5110700a0000480484c500728040da0103031100748a41c405603005411560724661504200c20401400280603036008000000410360720900840c030007000e0700c803041e031400028040c6001e900c202c8000c6680c4220310501d2103001d00c00c582c4041e60001c000d010440b030134180c03060f4030381048806031084103d100c0890320901d0800c0d015610240d00807000005540c4031030421507142c020001203138000811910404258520640c6403804002c000d400d03841b00c0c146414100d28014200b0981003e0010030070700080440d402c402640c034015100f50a114108800b840810278038000c204020411540f003281610b4040c00b24409019000160403100050503902d02c100051035809807210009a00700d400420f50b01d00b0039105002d100f0414020040c074055960988204607171107603400000082020030144008074003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 571816339 1250 571815089 571815133
    0x210c0d0b1008040f02060c01020a0302090f0a12080d021b1e1f050c09101110090f0f0201020c090c04050102190305042303010c050c010b0109180f1d 65
    0xd8a60314a070700760740d035005420701c40c000e04007411040d6030740e0b282421540c450003143e00740c0d14018000d40d194009954007901039044a0390491103031015800e20915410074516032811210042c00100030540a61140c1da59035005000c030420301a0200710800070002600c002948512a180c01070160007540c00c8181103030100803400d0b0459401c100004080c00c0200d10144000d20644407001405450f00105603c25205030121036411940d9a10418582c50b0410661400c0c1030030b0b0010780e407951030480b003c0303030444006000040c542c181e40d000c14004510040d50300c481c403610600441c1c0f1b8050358240000c4400741c0c11a100155000001028800c40d607050201d112060036400f1081c4426005a80180840c051070241101585c00259041e8400f4040c4100800d4404040d000308000741c00f41000802e00c0c0e0104445100039820100008881d5102e0107160040790038921440f04024100310003d000381c400c1440c2201c0ba252103241c90086885076168004820424500030420a90b0194640d812988 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 571817589 1250 571816339 571816361
    0xf080a0e2e020307091815170f150f011403030403030c060e060f100902090d0f0c031502040303031b02070513140f0906240108040f051005060a05120c06210c0d 70
    0x41049002101451f86140d10800d554511240c0e10303184440e1155945040812140c08410344518162902d041801c13804460054205140303640550381c85010b00200d03021031301a42c0340c01d80c0c0104810000f00c0c0c4599100300c2c3c068418240400e031002e074150214038200c0282e1305050101748080c03e00c0f0030a10391001e0324005080d013070310031b6061104003400241c1d0b681e900400641700000c60380710003042052020581020319406101310310103103510790f0744000940041c0022400b2a2414180103007a503e4484811014406a4010088181468140540e08448401020031540c9604000c61700001601015101c1e4070100c0c0c60400b1440c1ca00c04051605001900768010b84400d40d4900540d071011031443d4208038820708105125450300d150124807003c1c03461010b88640a005c0580d508500c040c0c008502400c002c43e1410003094980082040380c07800d0748103ca03120740c841008e894841c14260060400254840c510590b10b542050000e540d81808480c560f40d02540094031000c0d16240744105c0c89011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 571818839 1250 571817589 571817591
    0xc020c03070902160b04030206091624200a050d140f030c04030b04030c050d05031014130204030302030d051510110a120f080a0e2e0203070918 63
    0x188510042a1614214001d45540540000d1601420b2100941c594541c0b03510030342d0010a40707000c0c01e00035207414007500c1c0308400d80103410548101040c0e03604507600351440c02546207034104196024021003106014290207000ca40f1055000302c806070495801e0350440139001d40107452a07868000c0c2044440340344c0c2c006000140502c0402010444251480310400100d99580ea44555541c0d413014055540010700b9036601500300820540e000d03200006180c401c40498080100d0303420f003a42c090100300d0b0603e031500054003042002c600410b10b011038410001e0980500203030300811507800d83c1d01540040c0e015030f00010300c40e410502d181c4500b03984661b4a20000d1586012075000668a55a0190b000f08100c000e040c544200701d424052203240b26402503441060145203100a00490201092000401d070b009000032040910b902494010310301c000050100c82180c6040c01c05051002c01e0348c07282c2c00d001c890311907070601e0381440194010340d00340d01c0d488613080c9810030850300c00502000390702c022 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 571820089 1250 571818839 571818853
    0x1f09080f03040506070f080a030906050a0e06060d110907030c080a1107060203040204140a0605120111070308040c030818090a181e05071202090f041212140711010c02 73
    0x5040c08000e440c2034600c12104c80e581c4140317074101406041907001c8081c100820001d82c403640309030103a0082c0d605911500c814401551045080000c07141c460b40a600d076a04030300001403851a10b584070710000c0c1e120b43c1c03191b00d1015001000c1200700070116500c00200e9510051488001c1c0c2284115610405001e418400b8540c190218101d60265800c020461900400810304541c0c40785c00c441030032900007940300010314040b140380b40030b40347c10f104050045407030307040e801400903060041050549000000a29069403540c0c01c807000d4800400940b440032000c500400001c0000c2c005103450104840400c0c0c94440d1a01001080c0c000900b4154480e403400a02c1703178003a00418000000d15030041d4901c0782c13021004800d84070100c407501c8000e000d802401310109495650a424500b598007d40e8134070140c1e605c100c102024040141d070098126445030704422505403117009800504003070b00402050041010075250301c00c1c1400c4e40d400c40411008208588404824403404501030310b144000c15075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 571821339 1250 571820089 571820113
    0x23030d09110909120a090905040309150c020906090702070b0304050606040641030106080102130501030209061c020906034206070501090f030c11030c090601031a1f0908 74
    0x16500084c91a00c5410001098404419000e10110f00c0200a9940c0c00c3c4441e141c80c0c64010032004640c01210f682d030049034001014148100d880486207a406401c0e890280c072140d0030003d542000070544411403082000200d8a10711020265005511903030013410f4900b0441c0412080d52620f8010101122117411203840040c2a45c01c0c1c003c901b42100c59100383c0392425415900580030b0005e005070507600b841000a000c200560091481c40c0440006600f40c0f44c4500044044c2d200707602c1280d07440841403280078181c002d081400b600c01e0207550300061074001e0040218015400c222020441c5482c0d010030b1035900e41440b0a0b180406000c4001040d122196a0031005103620b1041500d00901000c9501b0040080950120700083c1d005205042240582d1800900f02c1030341c0b14003141c018032151403101c2c05007800141070709845001810bca030f9683d60071004400606003402e4140d194825420b5146081e00c40400c0c3d040300d803045012900d84009401d43c0036203000c1955220340c56681c4840c14480c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 571822589 1250 571821339 571821343
    0x303120c051608030402011707020307061401030c05270c07051506130b060d090606080d020706080105011b0b040303050106030b090105030a0305130b030c03180a0201090323030d09110909 82
    0x80b1503580a2052512503c442c00100c41c074000c441a40e044a0329680c0c01d00c000503030000003401019100d500107108500c0c0c134000c0308070304110a1000410710f4501d42d009000b40c0c44c081888210f03005016405200200c0c40d0381c0000d0038080144e45d50410f003c0d00041c3d460911405100c80c007501d202100003101d040c140400030542e07820158503414281d99854030600d825686400c22038800c01e000c500240260070308d03418100b005141e1341c441c166042c499503145411083c00800d861048601c65110590707030768600b1005407524294407403c5210b043d0504282c0c0e001441d440310180c0118065503000940350b040080107003c84400d0b40e4000c0c8034002200c01000315950000b084012240e01d40740c03aa448280110307400b2100b01e8640c00c0ac4000003c04410440003103c01d401035440307a4030454003904c0d0790041c4800e81752105071800000e030014605081c2800454680aa103500100c5141c0300f200c038080001c4151821074100f420347c040c4403a07c9600c030300d00b48008002c01031a004400c59522496013000040c441e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 571823839 1250 571822589 571822627
    0x6020c090a0b010c02060d0b1c03270506120f0a0204081905120c010b090a0912080c09040e071d01060c030e03160e0f0903250204020d02040303120c05 66
    0x7039041900d60001c001143d10400e4110b0072564003420060300c0c1c0e0fa4010421000d0405880c3c030358040c592103070503404540e0b41d80d9096240f030f80d00340c2c8808094001c40f0510403112880c91039180300f0300102540000707140c0c4407400104880c50b500d1042100505041c100c3c000e043d48003424902d10350340180b00074841da00012400000f92106050040380681140c0b070f050303051411210507000e407a140403851300d16013401074110011802c0c04076050000380d40c0716440c1c2c00c1122074210700600800350f080e40308600c2d64082e4440315002102e0425090602040d2400102901c01031421421141c01000d03040100000c003c20091207160074003d494610b41c100940100240030400c0301400b00683c100d9180f030951400e000781c0c000d130301c5856070741800130340c4881000a010000707030b8030801000780e00c80025030404008001d5480800e0a040d481203d03400f20b03681d40a2000120209aa02c281d081028010441c1030f84014002113100e074036942c079400c22038041d820840300340b041c61300c05000c410841c800c02002c10110750 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 571825089 1250 571823839 571823851
    0x207031806021005090a0c1d0604091e020f09010b0c01060b04030b04151b090e07030c02071418091c02160905130b0a0b100c0506131a1f06020c09 64
    0xb4032617440700b000c01d1034240071400142c2034078030031803000c01d803010300307500000d5217401c41c415413003042e00e40c00c042c08116407110f0b6018000307043c2c2c4e00b541d14404610440c650031701c1d4002441082040c0c81c804c00144013507002e82c81600c4842c0001000e100d40303135007802108010700038620030606251540d211150701d50001400108044603101c8007200c000e07115400400d43c1c1c0403004050903041c0440102030200362040c0230300c00301044440001140c451290150810598090380582080e501d8030844203103070114502419408281c0d00319109010f1031840050b4411301d4072400401650f201c000b82c070398000b042c081000e8219000300c958078007040c458140500886464150005040e528000c41000d03010780d0000007403015112005100510203070b50482d0610380b9045402514110002d00250307080c80180700014010f1b04030303500092a28214045c0c0c008005e000d0b24040d0004c14050041c4101404116510300e00c43c1c813444e0710300390180180041c100240c41076000804141c18000005080e510009250f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 571826339 1250 571825089 571825091
    0x180303030c0909020a050301140d020d020402030c0f0d1416090e0406090f030305060f0604240c0c030804030302070e010e064c050f0d0504060902090a02070318060210 73
    0x400341d4070902d102c000034409000115207692030164000c003640d02c28410005003d003102e1070075607586000c00d00314108660092076021801da0350f03405c0c440039402c014080140110180b101010b0100b400000344490303021100006080c0c0a440c401804070000a442c0103803c440d02c80e03600710540d400c000000107a07440c8290011070b5985a1401c0000b40c102741400900b00010b0203122410103805410550007107004a030b459503045c54640c1880068080d0744618103076144008207006158111062402185070140f9010f050242140c40c1e100ea0b038001a0f000700c8001d5000502001807650500030031000c0c003400b011894481d4036004000d40c010001030007880c072400d034480e480d011a80401c40b06425410040c55064481a10090040e00301907601e48191228a4500b01056001c0c1c41401118814108210054104a01ca181c2c6000410700108121401551010060050790318400c2d030510801e0402d50160351030031640350040001caa910308114201814400074046039070081041901c292080744 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 571827589 1250 571826339 571826351
    0x8010c03050613090821061002012304060e0613110139061811060c06070c0f1a041b0b0405060c070e04050f071a0d0203060f10030501050a0618030303 66
    0x400700d01620850314080192101684030300700d4580c140d607421f0b124403400c941400300001706000031b83c2640c3d00461104400e0760f1b2603c00c50f03450030400d036138250030174001d1a000508103103041d0001c0c5001415108440450021004001000f45203c03455003118420b07c1d009880340d122101050000d403004281c1e241c0502c81c00c4c1a5441102403202d08842c0507000801442001c400d44615074549517507410680e00c0c150919032903113107410910111800078000c00c00411903603076112422620141500e008840010450040c200418414010702c1c0341d5800c00043c0c1c0380c4038205494005a034103000c1110070000302d030703501d01001442a54000d90381100c1c3d040e81c010317560b80c407541c81071802c1008a81200441903040024801400000180c070384101c280c58041703a40040c2c441d0003a40c240b1b00c0e511003101d41c030715081000ca800d4110f10f4000c0c40d040301c0d000c4c080c1d10076914600c0c001081c5600c03102e4070200081d070360b0740100028600040d1110080c0410700341000b44007125020146282100c1c00080d0605480b60 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 571828839 1250 571827589 571827593
    0x206090909011506110c0402041503020f0d050109053102060315120f060c0f0703030b040906090b0f010f0b121302061204030306171c0e060409020408010c0305061309 73
    0x908601842008a0a03280e0b5075910b404014084400e040143d546a01c00d1b5100041541030501c222030980d000b0788c11000d03d07c0202e200441c069800410410700400e0305216041105c00c4034018103028142460000c203107481c200b641040c0710040e61420016070107007441956540e40c03005085800d000d4040d601e26903241d403544248050031010140d095040f01d141c0c0c521182e00b04000c56070a40415428050301c01c42d40710304507084c1e894080c2850000110300b04101e4140000d0080c1d22156590401600104564105458490440700c200d00140e48020a501c2000700d016002078445004d080c0d50560120941d00701a0b1146003401581c070442c141d1001d4030041540680c0c004296215983d00511095031140002d0b940e0074003403000d560440100703040081c04202803245084603403144112800629950003010075600e83c0c80d414512400c140301c10702075581e4003a00c41038010000343c80d04100259071645000025400c44510b544000201031400003071200e0b913614118041d56090070bc2c080454007140074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 571830089 1250 571828839 571828841
    0xf010804060f060b07060b03010b0103151503090c060806010e0402031e0414012c0607080606070311060109060e0c0702150a03020d0c0f181a0c0705040f0522020609090901 75
    0x3e5040410f0b1014045444410000f45e6006405c405400364000d10180801034015011f0742d031482d004941c1d042141605100c802e0074260003241442d03540c40c0c045007a242a40341c0354046d41c05a08035000141000d02000001d58014410103002c810170b4608510714a4642c4c0381c0c240349040803680c200f92425440201c0c041c1300038a64201811034644000300101040b142c00e20703141000c0340050143e1500d540f041091170b6070000c1010b5100c1c0b04907480b459050ba4400003003112960044104505000c408030002603040010080f41d806015002c0c400107030359040c45100c0b140f02c040203003540701c1d0079001c0080600585401142c03da031441c0da45480c070340340c82100300241c000e030041900380c2003607500e00510102400d0b402000d8203500075298650b030790055147d249c0300c0309a04640c050300308079410600c5071a90b809892030007085c0c551516001c1c0c070041ca8981001a00b6071340c20000407400c082d124405c0c450810500304c42003032a11000410482e1204c100e6004c03510900400482610648400380091218042 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 571831339 1250 571830089 571830101
    0xf01060527060a080118020a20030c01090308060117090c0d0206070b0a02030f01050303090102121303020306090706170106020a0609030903060216150e0318010207080601061d0f010804060f 83
    0x2c00706030700d03801c2000d0018520030003441801c0e0760121450209440c079030103200307d952111903a51005400310910740c02c01038510348074a000800e88420040291146400e10070a242c40c0c0c42561800d0403418079100040200300749158600100c0c2940090152506000840b408910030569852420721028000500c1c0c40c09144030203080754010b28104404104503900031442081d01500010340c50340c90700c00380340d501e003c0c9192407070251780a82c4282059045110140c003140c0ca84180340c2003801e84036408a4108402681c07111a191321840c0144040f9030840c103024401808045c04604542c036000000b075481040000c090240350385c9810141c141446800c0c24030145030092025582c560303031204142c41c3d1243c00d08064444a01f180070210b80c10806d4003501d2420344842c8004c505101841d07088015000c030284416065200c0c039800001c11110511852b030003494a511441d85090b00c405450b0740015803584618859005c0b8a14080241c0c1c10048480d00183c11440000b403441400c0412001450 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 571832589 1250 571831339 571831417
    0x61815060904141b0114040602151504020d0b0301050109090209010315020d0e0307020907030b0a09050907050d03050415232a071d040809011112030703140f010605 72
    0x101c20360b8440007400b490000c0c4c2000c10a030b84000e00607449580000c1140141d00804005810440e02d03482c4e4183c1d18440580c0110b201200d0381e545050100c00541280e00c9a6a0020325a44030b08085440749402e100d080d005140baa030003402268000d074005031141d401400300a10512220300b06001401c0c1580c16541c1060f0781100c1004404600d085581d5281c005040491094132030400041e849072083c064444410405440860218200030300c41c4042c04001700351480038407420a00140e81c0d940e1000c0ca40825000b034880c690b80b00c5c1090b2103103030203050000c2941c0c2800444440a1500c5140c541c00008000d0002c11050312070340e448416040d05022032151201400c044034402901d41c00206404c0101c1d00740c60b5081680701c5503055855000e420440300a01088001d00000f590b81d40514007410242c204031701551020300b0340040756806900141c4d40b8600003542c50000004c0d960320580f4082e040070b0841d218500c40c2d80b4141c001041403003201010044000801840f603000b09089052841c050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 571833839 1250 571832589 571832593
    0xd1205160305190201110d1805030a0903051b06090f03010b131e0b0a2c090a0201090611100e0c090c0901090515031b0c0a0506181506090414 62
    0x51510304009100e0307002440f88007001d964000b00e44145500502c1140c0d01d081d0320030300c144d08050306c424811009101c40350401501000e14500e01c00050303018402412404401d895140100d421802d20914060440d40340c40c906030404400c20080b0790f1148250350280c0c100700c805010310303071048000c60702401c449070300c15420007010402060700800907000f2450031000c0e201451a0612040012019618000c210359007154003c0003d10001c24800390039903444000d414a20b40030089109400c4501a044500490940014100404540c1d10640b6000148010703c0c01d0700401d41c0001c1c0d01c81e1910f40c006041d0794819910507204100100900c41da942c40303100200801411710384078203041e00941c005140d00380040d00002004c02d8502d400d5607000000341440c031070242140c0d03c502c0000b461403002c80552800c2c0b10140200018107804001569406204001903d201c1c108840b1515079484c1c24039001915805c554a0000701000c030180060381318008072600c0b0b80d29160b500303210545c0351071025048031324 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 571835089 1250 571833839 571833877
    0x40b060a0c02040b0a050901030602030a0b10050c160b19020c03120c0c030d02060c0307020a171801050301080307030e0d05010608070e070309080d0b011e030605130504020d1205 78
    0x3079003052044000c64001d0783c051000440040c10884c580849001c0c190748110414018000b14000c1d9000e15405044050005a10a003640c0050340c078406000004001030000034940561040500c42d14000006d4808402003e5041c0012001140100341c503c60389140c0c1d60501d030340400d100300301904001401070180c4440e0211404024081c0d800f8076415031944c480c00501808609001440c844c2e500328650107407016841d860051000e6501c06404803007141b19034a448004916016016490451241a01c503a00c582c3d545003000444011b20466040c0041403004000d603200110841d00019030510307151483e40b58400008400100040300138000350310340540802d0130140014004181d4040020500d290b540341a02201072310146c8030300078441c1905000c6000d80358055004104600b00504100c3d0307441c0c080e0101c41c064401c1070a8003200294403413030100240c1c240385000c8681d542041c1c0e41880710b482c058002c110020101c02000b441c1e20640100140d61902c500c0c1598559203400040d070300340e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 571836339 1250 571835089 571835107
    0x1e050627040f0f060e010b1204030c0519030e01031a011b140609070902130303111f020310170c010c1a010303120b010810060e04020f040f080f16030b06040b06 70
    0x2010386481c20542285084e0000c00c44200d01a050b60480360501c60302ca01d032000010b02c0c0004481c000c0c100700c041c44405444940014014441051406401c052a8801c20742c075050007001c82c00c07224038842c14076160030202c8050031200040425000001e00303201171454040c1300c00c0075a400400c2030281444860700040c01070703000045803250060b2981c1c0d04a030380b044d440351301d810101e02c1110242c40545650710800c00000740904018142e505461050366241c00345940c080e0300d015050f15803d003840f54000708006102911403002e102070901d01402e031403100324101005990311400f154180c18004008203490821407010181071242c500000710050a50390307460064000c042042d101c058032802c1500400865118529440c815580b080610021915040c401e40795000c02d20102c40d009130f020007001015104010040c0300400010611810152074a0740c12402d01d8910180b0700b40607042078165a1420409568000c2074036040000e0314800d46450b00010018542c0d42020b60b000038000c40e01000e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 571837589 1250 571836339 571836341
    0x11010c0b01030605072a06050f2a0d0e070603050c090102100b0a03080406030501030302190506040212010b0a120c06090f0e0a151503050606041802070602090301151e050627040f 78
    0x241547c030500b0140081e8030f403180c400d40014012180307200d81c080752200b514025000070801386280c08000300300c545071a240c40365101c151130b0142450310855014800420655500d449110341c4105103040c4103044c1110703c0c000030b44420400710341c2215103442d00c0c1e010b03145565000604004503801048142c1e150360700d880140240609110035009030113001041c801003242da061001c0b0880d8443e010340010354a81d800c0040110f03013826540344643d6038010000485c1c982c6400385021308903100000304101490718140c44050f000e9007008003049a04c0b9820030000e02c03050b5600341030340d2460901130260356840c0449402002c40d01c15040500c102039600080e40ca110790002817000c0103070745d414402d03540c0d80001c1c40154451441050041e24804070400c591840990190004502c0707007001514002e1218002800e5400c801507035940c011805508010100c0e240c8145040b0003404505141d50340d01d40000103089000c0e00d4411340d0a0000c2d10858503d9200b42c15050340351410080082001010b1b684000c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 571838839 1250 571837589 571837667
    0x50618160201050106090609030210020a020405150a150806100e19060e0d0503030615040b031e09060f060d03030f060b040510050903070603110409020f030411010c0b0103060507 78
    0x401552803c40041030140c800c04e89031090314000d0702e07040912451603007071050b080380041c1241c00f1400303554400c000503961400340031b0240c1440d04040c1c131401c0c86030082040329480c0f0752040d000000c1c04030900200d00d030098441d07980301400b21541040e0303601d442c0d801d4824020101c0c1480e17220b20030041c2110001401074100040c1c5d41180e8914860408400c240b004500075400301408541c01840002c50529150b0300d440c5502140d102c1c8141801c1d61840c1c4152190810703112550403481065080001c4419200b034185d01c451100f000706120b0414881d59003030706002800181c022030305018040b06042c000d030820003012075a03007404c1094030380d200b0b0044d40e160000d0094600c07841c0d00d001c840d00e61a100f40c040d00c000403c010041c001e0389242c0142030f0001d20052010384107001e010300c00001d8403c400d102400c2d500300b8060f00c495483c1b4007458a801022103521080c3d050150042d11000070540080d040d5066a60000000506455002c0e040e2003010f1041a841440074001584c07a07050a8030a800c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 571840089 1250 571838839 571838881
    0x40218180a0f061a2407050a0503041e15030b18100602240c1e0c0a020901091406010e06250c090b100311040506120f0c040b0a03050618 60
    0x1c001c4d07882000714040c002c807003600e0416440203000382e481c1076040c000944880d841031030040c05407a0048599480d800d0183c43c11303050342c40d5040070a04124260044568840303945214101154080c04e000c40c10361650f40310714615080560b214084282a192095145080c0c0d01000540c003c91415101c03108c11017031315000c0ca00050080b0720140e10b0f8800304405028000300c040f5a54107082c2e80340c10074060181c000c1049240d2640c1c800142500c5681d181005040da003141c3c1001e0724024201e80103220b000141a070005e00c5151401ca0034610138001440d50701e410090900c2c10316a110024000149603000310100719405040002c15500c4010751258120341c0184604010401c0581c0e604640d4100d542c451211030304000704a01c0b04010610a6204460b1160410003450074151101c001c58203030380002c0c0160a082c00c2c4542801540041010400c0e484003002034110319040c1001d80e0b411a500031410303080145034a5002081140d911603000b00d044908445090080c2d251004103450311600300802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 571841339 1250 571840089 571840091
    0x406080a1109060a030209041104090302061008030909190902031b031608060711070f120203190201090b070f0506040f0b0a0506030a03080405010e0a050d02070e040218180a0f06 78
    0x1107040103003001000d151140c00b00034102c1900910315001d02c041440c3c0203104660205203610b41110a50360b600c01d22071414081e0307009041c20314194100d80e44490454012868581c001d00202907955580c1c0c040544c8640d9040c200452032800c200a28041d124021000b5818040c0441c80d000e9040b2441120302165011003c0b070740385000f1502c103121051414001d645890b085140054a110f014110b4051544804011100603903900e00c14021022099001200c003d41900048415440c01b0440c51a14008103150f207202c420440d400640400424070034100c150380040f4107070341801521581034181c56006000d580c6146070078686015401356642c000c8410714580400f05136010002c1c8102c0348901710142c014a11980c15407000e44800000030001c03a550b40d00e0b8605200042c50900c00e0200c180c5c41813009050102482501034202015038018942030b41e01d4030108000b590703c5400c0c116058202040c0e0050940b20481d02c0502e1541e80c4440071158815007241604000542079051000717801142c1c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 571842589 1250 571841339 571841363
    0x11010e0f0c06030912091c06050601080703020c0c012a0503070b16050702130b040c0e10030b090a150b041215090b040b071b0b0a150302130207030207050406080a 71
    0x70402845020590f2507941c1c6500040c0d018117000c4288000f8035401030010300d0208102c0c220101c00241e580c01100449560343c68100b485990350f007103a03e1a0b00174451341020b43c10040d4240201d551802c0c0644280d0400c801040350b08100248065030f078490b600500d41a0000300c00500741710f5030303980c051103045a0142d9a0340c0061800c122a090f1409a10801d07501c07149402c000d0340820421401e10381c4c40c0744501e55260100e0a0543d07807840744034550100b9443c1d007500090041c1c1006188060f00e51683c05050404855640c2907a602c1e406640c0a02d400707900141c10747e54038125001711401504a04440040018007203010142c0300500b0b82140e1152101840301c3c1c2107164004240c6903240c0f4003c200c00080e00105e00054003440c95140d001c441c80c80d04800c44070980c40040c910400d44035040ea4a0315a42081c0f00c014940c501621000e038080003003040481b40755038041078141c83c4580000c0e10140c1e000c2020b108140c420f006100041100030010321025848071035a030307103c0d02203a004075000c0804403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 571843839 1250 571842589 571842613
    0x3040807050d17030a0b0a14041b140c160602030301210305042309010909020915010906050c031309060512300c0604350f0a11010e0f 59
    0xc003142842c10342c0024a0701021070003811080750313508080c265054080d00e50103200425103401ca8000e0051800c1c000084c10482004d05000c100d030b55101c0c100010300d0048040640e49604505d070040d4030305d401142e10360b41d0b4404e100c009091168050490248038910040003030040d5000000d14140d900340e03900c210200380c032000981a0246d4498004000c0356041c00100503100070100700b00c461003d14103401d8207512142c0009860941c0981000c801281e546d4414415030134860301503640400c07e507051128004070400081c04140241c458907040117000110516082410300649100c1c154403a03901c16155110384100d07010341140e02900340100982e1001300c9d20840300180034000200c03403030082e11088204000d60307100c582c00081c89000b030080070407514200100070070000384a68001c10040c028502425051b1500001e201609480991050b00d0030221040e400c0c12a4442c4800c0b042c081d44e50144c9003001e95a03c0f00c1c030401c100055180041c1304104034004070b080204c11141d83c05860302c1078550 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 571845089 1250 571843839 571843849
    0x90d17040f051c030206190e101a0607020604050d0206280f031503030e2b0c05060406021b0a12030903170a05040504050405010b090a0c030f0c020d0804110607050304080705 76
    0x1005010300142d001b100440d1030a400d0014244261005010129943c5681a0b00b145080c48d0014104030b91559091071110f141e01001d08000007a4007115400c3c0b809000d500020184e01036406018030030f8241c01007502c00c65551001b1100700206d9800c50250003900200c03844a508400034804020550002200000c00d1180c42005400091004040130007030658070200e03070820b412414079030445a2035403e1000301c0589920280d05901080352803000b0211446d1a2901029603880030f0b000f484148024011640c000c030320380324090241c080c0394072007101550014100c031416034058450b0701c04a1071400241a400200c0e442624000d105a4a04204c80b039035a074024402c20238580001501400f0a100e1440d02c0c0d000550807900640011070744500d000001381005400f942c007400d0f140d0380c409440c28000c0d00f5010302003544504440400202c4040381000e501c1c2ca00742c1d210030040201c0c400014003041004c0e0f01c181039008010348955200c0d001ca25140ba0750b940907020f40c101ca40314001c0d00040610f00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 571846339 1250 571845089 571845139
    0x7080106170601020a122c030c1203070f06150b0a0201051005010e1e0319060e01090201090b1c0507030e01060f0308040605132c06090c090d17040f05 66
    0xc10384c000c02844c1d0a035100c0c2a000c0c0500d180b07a40400500e01007000c003d0610316901c000d40e040142c01020049118420940782241d06060305009030844c44454208002c08000d44907101c0c1c012a031104078458514203240240341e100c6140b007240034180c00120700548140090b203041006a0000c00c130039192a61000c0a102030361150030f000600d211802d0781d403030600700c083e00b50380107000e2016110b01165000090414850305600d4001e02a40060507050080318001e91240b85c003110700070000700c42c080c3c0009210054501544c1eaa40d007001960a81070141380462480d0440c600c01c0801070383c1031070784000f400761902082000302582083c01c040b03200d030a14100281207960001c07000f890a071405609035240d0700000e000700003a0511200005004610500480c120481030302220303080311061702c408090030405060103028104040c01c01c20f2020204c81251075902c81201d80816400051404d40000b4003102c0d0b0b01e641c0ea0901007070000e010403c00d100c200542c0c20860320174114000c2c07030300d0810205413 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 571847589 1250 571846339 571846351
    0x61c05030a1206150f020607080108190201121d070506030115442a0c0a0c23010507051b0f04020310050a080c06040513060305060708010617 62
    0x4010448485009050009545040440110380b455413622144010744560038408042074940307140d40543e942c144162540103820703040c4000b503035041000e0329641d078011190904000701d03d808010156070281c1422483d02e00b0302d0314144071071003c0705841c1403610b0801062940343e1180700000f282e00e2038820180c9069034120041f80300490707450042103c0c0182001c1401c80540314030299600c607a50b0b00d518501c201c035940d05010078241000c070075603001c204008043c02844203444040100c06241c0c910310340c81600421a120340c43e40c1d501c0c90385e1410501101c6000700482001035001840b01c83c950418006000c0e82109060b00c02c098000540d40c03480340e82001081500811a24a242d1195845074260303020040c3c180b102050100b0082412648195442c00c0b403900102400c000519100389a100607210b05000b80050704404404110309000f603000e1240f00d658614a60302e082c00b010380c0054010340c1c0040880702507060408026020441c02c0c02000000f1b041c030321084980605500069004003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 571848839 1250 571847589 571847593
    0x501051804091e0501050f06010e09060420270303040b030f0406060302090903221d06060f0721140706050403201e010504080306010503040c050301060e061c05 70
    0x4a414410000103010501003141c001480108403d400c1c64031440040031507100d03100020312801c00303400c030300c80c4900000c1c00d2a0411404024241280d10382e24115500000156030215200720012020b000c00e00480e10206a000008074400080c19048030340c0844c5001000e01d201d075401100c20030b140d241d00c100e014860b41600d081002c2000d010886103c3d45e84240561070000c1c103151a907000602e84c40040c9c520702280d91000c10134114140c400c2c81e024034002c0c403880c0521091403420b250b80300140a5030050710480c40003c0e00042442d103501d8101c17107482c50014061030343e4099524183da100000c0703070008441075009000c107a02b40e5004c0c07560740080740c2401000c1c40c00c24125955070000340c600100100c0811101c612018000c90058032316000400290000d0030748203000140981045160650752a140d070f0500040c44080384540041b03a8019000380307840ca07642d645608080400c44610f5001527015880d00c0d00025080080a070064080d010464001c1101b103501e280010003814007000c0a0700341d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 571850089 1250 571848839 571848877
    0xe090f0307021002070915170606010210020c01060806310c1a0d11041715063003190e03060118060506040f03021807080c0307050f1909050105 63
    0x545040e141900f24030384203104643e074031a00d03008880d013a5207000710300110501c0140d005110081504e0f14244102220300300410702c62510360b0000b950b65522090781044182d000481c080a01001c0d00803c4c00741410108035402400c003030300560f481c0c1c640441c0408034a1102c40c0c1c5004116a51581c034007855420042c0242690306001d15201c2100d8181110b00d118a820800580f1944141c000d800c20813800004d11a1603d1501c11790541c00d1114448140041d0451390101040ba07000e5824107400c0f200c255500012824140310f070441c0416800c00703e0842c40c072040300f03108000724004028090556141644079800c40302110680e01d1014000801c0e5150308694010b01802c8441807035030306079401d03c8201162a40e0b641021903040d5200760401502c10720204814411f5041141c041408120203800a00903031402400041c050070001c0c180da0507103200000071816107032044040d20b0304d0742c0c00003414956a2840054410754041c0c2210f0031808503c0801002030b0f00d40c000e6091fa02c4144544694003c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 571851339 1250 571850089 571850093
    0x50705060d06080d0c060c092d0e040b09010b180f0a0f150806060f09150f0a06030504140f0712050a0b04050d0e0901180e0120040e090f0307 62
    0x90340e0412145601180c0d500c0344001480303441000100d01c41c06041d164641089403e080c6141981c2c0c500f9088800d215061000b000381074600c0890101542007103a4085880d03c0050303050051030382d00d621040c1420250414030042c001a00c01c018050304e0b500c0020001d80d003d25041c8000340c4401e04d16490345030101400141011400358000340e000e07420081c005240e0704103411b070b00c0c00c450440705090300e45013000c3d1003400301807002c201c40c64106038201c0f207001c154800c0e00300052807440000d1454501d82151502002561140c0040002c109802082e503426207465440080c01010221025200a6000a5010301c01040403891451a000d410090200b840c00d0041c000c00c48076516400301c42d548110610a40410700310022280118490741c040c000003920144028100b034440c50240d8800c0c03411400400002d110125a40c071020b40082d400300741c0c48074415060b070040400201505d102c200c031400a482c264031003801003003a6040100b00802e19115288000e07a00c03c0d540d00700c405503500401030140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 571852589 1250 571851339 571851349
    0x5280504031e0207050a0b07051605030a17040506300702060703110c0304060302030118021206130b150a0216030b010509040203030705030406180e06221103130201030612050705 78
    0x14105109004603651545e0b50300208041c4005c903400003003021004100e007001c114040c800702030088488a500310740c4904000029071940c030601401040d0300900034a001070151940305031401407000404142d11403428020100c41d01c40c0403103000103015103004000c510251800500c1c0d01880c9264010501c541d01c0950540040141c2100d10040d10b0301400024004ca500700300410140101e0f603005a102d501d800401c0c0d200c0c1c4001301000140f140103020030003c0110140e4099800380c800c4905034594255559420300500c0610b40994019403410391060503040410000c16079400a54222001044800c5164442e140076002c028000188840100440d10f0450a06501315000400352441c11710f42e030792001e245501951108001c124070b0a0440c428041c0242c0b00f42c01072540c011802e00e1072801354002027004120b00c40c1c28480c02c9040c42005201180d0354082c0c07442c07081014955030740741400d401e03c3d03190382d00a0108900183c00d082c40412001808408402e24030703402001880030781d04040802c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 571853839 1250 571852589 571852637
    0x1605010f170c0306181905090703120305220606050915030c060703021e010b0a06050a02060601080c13030309170312040f0201020c28141c060902040528050403 70
    0x43d13408001c5d0080c0c0c8280244200da150b0280078080224120201c3c1c0f031500d0020341c2ca0081201010381c04c0041d04101103003604812261200303161900040e41d5a5510345880780e5107280c20000b46103512920320318100010380e0b2005081d15402c0700c070301e0000d5840283c11281c41000485441d050340014006640754101840a0110240309005986500c205107440080300005007840003202ea4440700c03c426907041c4002200050282c0d4504585802c000c0035002c0d6940b0400b030601d604000c0c0c4030b00041e0f0f00d2101c00c001c1e0742034a0300203001c00710165900c1c00c008005104d113000d19401e200f501c069105a0b08400400c0340c4113108003880d9490255141d17101d803000d80003500c1080e419070103001050f5885540e4400d01141d0464510301e51330f007000c40307400288400c3e000381e005080f00c11014100c903040f83e6100550445686c01c45c0c64007260781c0c0da207460000003400ca1800c0c02904641018140f0001080f044141d0688001c20101c2503106429050b608040d0b4400740c8010300868a100e03c03031902c0400c242c0d207503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 571855089 1250 571853839 571853851
    0x3070608060a0e0f0f1b190c02090a020c010b030a020d03051803060403050301061808120d0e0d050702130c0c0b0a09121805090c0405041d1605010f170c03 68
    0x3094a540c0c0c0302d0081c0807100702111801c403480e204000300205d008603c4c1045030000030903503143c140158000c5044010f031041115212024140c0c0e0030710114180306108a022050f4060680fa030305040c408843c401075001024240312a50808200580d5820000b03030806015400512840580c0c0d0607031410b59460744041030402d515a00901c2185141c0c904220040c0a1351180c0d40340c1e5038940c0351080003002c0800c0c4014401031401040001c20004000207001c01d00e850302466015910880b03501d899000300450740d0b240d55140034bd0200582c00c60b8101d030284c01032746e0007610700444d040400034201c002c80d072200a11001040fa042500710228040e48034050744140c6000c4005041c82c00303a00d4100440720819050f200180b5000d429000740340c114040701006000130f542c0c90b07103c0c2c00c08a68014403801540075890080e941ea00804036080f03521002c1710800c0c8a02010755540c14132284510317144008030b019007030100300c0f0015000c8001e0701c144003172280031104003181021901d030030902d4882c40d800075101c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 571856339 1250 571855089 571855099
    0x1207090b0a0b0a1e0c11130207061a210d0807052b0e0f0307060e0a0209010e0108071a09011805060d02030402040c020109170c01110a2304050307060806 67
    0x10100d4401840c1c4014080040f20b5111026070003480c00c180c0c0707010110306031101c00b0400c1c038107030000020304940c1590902c131904803030506c0e90380d400c5800000207000350180075180600709501240d4202101b07600710601003054075415040e1040803803a021046600a4800f03840c1d0000f098800001e12886030150002c045140082ca000d1008404011103000070030380c01071015000038401c0c656060b61058943c5440040064251103449030059600c900170204007800301d0303840c1c0051001101c020b008403008943c1c014030001041d6150010000c00100034060907001e4403075840701280749210201d0b1602e0011000b041d180ca024210b6004403a1248400000c041c00040860701103016694400580341c000b1125500688901d0180104004e0360b107640120025645842c0030f00d03000c900c0307283d034159444091140711541c4640105240d0300401c0406008141d800000c1842045a80d01c22142804075001c1d4035a0040986400f2441d04c1c0f51160344529541a4494401004414060100d055000c100141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 571857589 1250 571856339 571856359
    0x24081014161e050c0105101215021b0303150102010212010513090804141f092d17010515030601090c05090a03060209010210050408090603040f050f0d0e1207090b 71
    0x160b40990285000701000862800b0500c913100c80703000d10070f075a80b01c035a04000c1e2a130710385400c40d034038454800550050320982080408080700000c82e0121400c0556041140c0340312070701c0021107074032908103894000e2420082c3d6051090780d8414020b841903511940081003199181c801000102e012a4202d200000d84030303000d10f40441d0902c1c014200500d4407400381c60300d50031005c04000c141c4901e140707030821a80e0502400c206441c0c2c032051281c10b81e403081c2c0c81040383d861248201620443c00c1d0303280080300080ca442c0821540601000c1108103030400e0024002900ca01c55404800300d0b080c0102a0140c1c01a03004003d2440190804d0509030b0f00740c00e11515004a02d404180044400d40040c1c03645500010889150750b0f0400203049070840380581008071f0304099468140e203104001040f84100030100101d0203000c490301102c00125401801c076041d20103800f84c9a51104590351500e80410040d8000181d1410300c010340844a103c500c014104441c00c1004c0d80b00149030b0a43c0302a00288003138 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 571858839 1250 571857589 571857617
    0x70c120e0d050f1605030f070603050402120a050705010e030d020604021c0b0c03040b0f07020d0e0a0b0a0806190e040807050c030f07090b0409021309062408101416 72
    0x310050702d58442e06400340003003044c0c180c1441902e000a91060f03010b07500c01210318440c550042149010346a4514001c03403d0780311400040c2c0c2200281d044d10543d40a003651207010000c0015a903000c558003a00c551405080c89000c15895841d40044030026030801000500145030000c44030003191402c0b150111813820382d4982c01441002111909201c0f00b0000130b110a1000074034509502401c0e030300a1007428a0885402511a4110251503082c0040c0e00b81c41e20560380c901051001401840a50507210034902200401c4124103444190141d20011591110602510200400e030f8402c1c811050550300c0756951032045501c5207a0a8030b4038014580c0d900d82c9039500344418050180200e00030a2498100413000c4c044035480c1d8540c41c4036a00c0d1080c10700040c1c68552800910300240c00000411012038101400075055400d91200450141e00c407905e0340e060705a20070703815265074100321801201d6007184c940490300e4600040c2400d2800b840021214645c00300c61f002031510520b0650301c580c40403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 571860089 1250 571858839 571858843
    0xc030a03200f03161b0503030a05090a033c0309022e050f1b06070e01080631051003030305060603010e0408072105180a180e07080d020c09070c120e0d05 67
    0x605e50484140d00000300781f1003403203400e024140e041241a00540a09049641d02618081d90948800c0480200e80c4294a041c051060746c03862220480c82407202c22600d40400400414519004078031441d0303052041d0503404189140000c0c4030b81080c00c101802144c112090720181c004110000e01e14800b040202106040120707039485801c0240000c2c2003e00300310300050460301030042018100304401080254a64030b40503142280ba00305480540b040c0303914400d51400409241045813402d080900303001c1901c0e030440d0b40c142168000c1d90100103503100d02040040601c42803144003950840030000c1008103548038014044c075440707a41e03000c504444602010449001038140c06001c90000700c1c00c0c88131000400004107425804488021304181400d411117200010700036224440c87d960801d010040404020b4803010b01208011555042c0081800035540d405000085000b5005a4040389400d80a03030044030103240e000c10b200000c41141401107030703084590306c1a1030b4051810720404000ca803003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 571861339 1250 571860089 571860137
    0xb0f040b0a020102120a050f010b030705070b010b03091e070603020c07090501030b010f06020a0203100506030708100e0f0a030e06090103110d0b03070506070f11060c030a03200f0316 80
    0x10741c1c0025843d00e0400070a58480300000b417a9034045070610040289110035010a641902e42c1d910f9aa030300d940303c0d11421240c0c0e02075600010058880a8008148582e40c90040e520400c070440807540c5540e6040448c184502c0c0d0001c00c104030394440031041c440c0600036000b074821060030340b04803020256a000d02c642651000c1e4000d603403400d009001444010007200442c3c004e0321041c00181041289940401c0c0d5036044c0b41602d5600c2d070340e03c0001c1403080c0c0d000d1024000500b00541100c250641000b207480041007220510f904078825150000381040010518440042d059103d400b080b01c118401c1c09017507800121058101640c0d26080b00c003c8410201600310079050500010758202c07400c091520f0604640c000b28490355081c440c40c800280140d0b140800c2c40c7e40441d5200401c49482d01190841c007030500341c04064007021450440b000e503d988150060364207445600000300d08030110031024483c40c164030380c4501040000810800101c0724140c0c0f0941ca5241c805082007aa500c604143c080c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 571862589 1250 571861339 571861357
    0x30a0915050a0915021c0e01030c1409010c0c05030d0e040507081303030903050f0c0a0302011a13110c030a050d0b0604030213020903160b040f14030d080c1c090311060c040b0f040b 79
    0x11400e001207543c6c10310404e1146002404c01018007001c051601362f2a003e1200550f04000d00380b0104000c204007141010b0080c040541107a500c540d203104040c100400e0b90f00d103107000b145064002001c1038415643c2d00c3c0540070b80d42c1c0983c19000d407501c0440184c1045e140c20360900a00b0052444840c402c13100030269008250040c140c0c84403140350080c252981044524500d801c0d03448940403d5a0340c02040d0b862600740301c40044c0709820008034400740e0080c803e01c41c500d8000400c0c15181260002c0082500c004031705410080f11030a50100314542c015408080e4001d40007040ca280d58915030b40c020700c00d8031001402c80f001100e02c2d0300c2000c1490f440341c01104c0c07600f101103810001000032040b4540544260002450b10260001c0800d60b1042001000020080380e40007082084a40074101c4200f940d4400c02c1c082120b581d200c0320006840350103c110000b500ea281494010380b40410914010b5100c014400c1c5040d00c0e01c980d858280d00180001203c0c80c0d0100000102103510900074490f440d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 571863839 1250 571862589 571862597
    0xf0b19060c172106190b0a0e01020709050109090c0906080309131d0102040f09051b0313080f032202010c020f0a050402040f0509090a03140714030a0915050a0915021c 73
    0x4544201031081290b0250820f4072030070104201488036035044001c4d50015541f62605200b502140c00c0104e18050180d40844070180c940400031507810325982082c0c1042d4000d049030400c1c3c031343c1e561503a0704072121845004000e0b0000d000351010361030500010b46013400d81540c0801d00000841e00200c5100c01d500c0d101d0305603035000804000322000c40780b0380d2000700b8414000b0045032900000c1c00083c01803906201020400c00400600c4000c10038090f02840c40d000101aa25070300e0305003200c0c1507940191800583c008030f04200d01850321898140da104182d0694a000607004540d081c0040759160343c4080390701c2206000c01190302c2c0c4176440940014100c03030445c000c01502d400c042c412040030140c15004079420890b03c1c03501094100380c6595504940c64580c42d034074082c9080c16515440f1513409c503d1203000c001414401c40368030400b05019100c2800015004614510040e01d0b244500b00e402e4010601814003048200b20100542c2c0d540c4102e80195800d944100c03111074102d90368502a14041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 571865089 1250 571863839 571863841
    0x17060607140f16080111030c0f13030c05090c270a05120604213608030a0210020c071703070803100806060102070b04050418060f0b19060c1721 63
    0xf0302281e0500c000420310000200300307081101219080768403000309000711102002611888880009080303440c0802d032a0409a07002d9202c0c03400920810042c4181407042c11414045110011042d089415030790f0318121000c0f004030f10403516100e904941409279030100100c8000140c40e1102d503148410004001c015103107602d4107103803446c0301440a0758103030841003030b410010803040e421409d22800300c8030641803031203005010880c91054610070080b500d22104a8080003031038000c00405041c0144668003905c0001c0b41200a260480c002c0075110380d141d80c44407204114280100103510390400620044d6403400b0313142d8455171043d500588007203c44800d036440400c4180c8041c4078030f030740154003440a000303402d01d4150004030070702803401042d120310340d15100c0901e00c00445400300038007640b0000520108401800f030200800508944601412081e1b60a8281c03400c0390000c442681e6040e2141c40c1498060f4480302c0c10b050404c001e094604804003c4910482c40080d03c0f000320103400000303540310f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 571866339 1250 571865089 571865113
    0x40b0a18020715050727030812070815060904020d02090607080c1b0d12052a0d020312070507030c0b0c030105010e0f010e060c100518010c17060607140f 67
    0x108020403001c121500c0d01d420b000c5d00d1580b102d110040c1850104410607107641101004001a036181d00080c840034000459400389821102c101d1712400c984d448800341ba03540c038040b071118000c01850f05503100300c1c1080458502d10341540500303901c400b82100141402c80340000309803a07500c052020341d0303003800100fa003103c09039080291050800c0004d9000843c03101c080042904900c00b50340040c40d00b82d0340d40d201c0c0c6406100d00199034010310308907e41d6800a00810440c0e44004082040c3c01c03590040020a04400c2d000204542000803a880200b4072a0755144040701c40d03402404d0214200300c01016083d001c00d09580401d802118804401a580d5240000140969415000c903d000e4910942030004681c1c21550444c0580c4081e0380301a0344075000003a150030f102c05418100c0e07001e80b034030702440501441c1c0500e0b800329901481c000c010700b030740382e100a581c90000781e44205040d0a0402c000b8003582440d201070b0241c031f4456210186851180701010303003003000344455410150300405030710324 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 571867589 1250 571866339 571866353
    0xc15030f18060c230a0e190501020d0f1706040b1503100e04020d1113021216170c1c090803040c05060f0a0c0f060603080301170601060e040b0a180207 66
    0x90010505000160041ca9043d258000004c1000384007413503400f02c1e400000b00d0146183c0032640c1c10041080d400f2000308503183c0e42c40d14581c0207250051180241c1131202d2406602c54190102e840d46502e105007944941d0a00b2940e0020320898206d03840b103080710041e44805c5400041141c86110141d180c0c9001c0003240c00300100c99110f544504601014000580c9a4140300620580c0016002001070754010101301004240c10105204510010300b2641604c0300004c00c038040c01495140392801a05040308446001c4483c0c800450391000a001c0341a91180034024a2500c450044030000054207c409404943c6a468190b0f80310000004100c10488440c034400c02400b011503c84d800c0070b01c1c2c0c00c51102c0e5801002001e5051041c4806d881041c88030380d805401205a01030410320442d0f03240e141201040d00280b0840b400900404d001d01da8901c004502c480c1651a41e94900040559040402c809409804a40c40e0800c0260038041403208840080400c00100101c01503691019464003103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 571868839 1250 571867589 571867601
    0x31206032b18030c0e07030917130515160f02030a03050301051c1e0f061a1003180213090c08031c0608070501030518060103050d0906020a0c15030f1806 67
    0x20b07400c1089080610016465a186006031040754112050715510140103800078843c2d4180138003860510211440000c00d00c0e00280b00c08110b60101c0ca0006941c1c0c0103002d6030001c0100105015541448040c6044d82d081c00c542da15a8083c00081c840c0c5042034010900305111203200381c0008100000500041c18000080000d142902e8000030004501d0345840654100001c00200340e10031600854092014042031a10f400342c20800400540020500030025a8002821580a24081e40d91008554000c0c4221211102809003840382c62a441d400c01012582502c1c08000060345c84c2c2c0c246012071900e20382100076240701e82c001c594030040c07101c0d2161418031881071810a242481c030305210194020404804540c1c00b800c1c00300701d54a425041c2c0c2400444803030100e2091181400020600600003000c6c1d00041ca00d40f00c2c507d49540f00c081c206d80358140d20780e010302500003950042103003070301020000407507103200c0c6400103400201d51818029a42180602e5020300700f1102400207100c0140300e40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 571870089 1250 571868839 571868867
    0x3120f0402040c2d020a051005010905070504030c06080c0f0d0519110f030403020309190302011d010f0f050c0f0a05071d0115090f0e0f0711031206032b 67
    0x81e0114994540040c000c0703081d0604c0c02d4004014403640075800324000c00c600f0b000d16911200740c1c1c904540c0130541c000100b000b4411b103119141424085840680034000326400e070703500015185030460600d034098440f40e4002c0c1c000440210200b000040070001d04c409442c0d0018103030000f1031581040d40b010032100504400380380c40149412341d030310401e980c000200c840c004000401c0d0f82d02d075a900c1c202a4114003034001043d03000380d0071202c0301c0d542da044c401503071040d00d1003601c030321031aa0040201841040ba40b03128460114587c1c00c407240c8014020007903002080600c2c81c029207001c0c01c294003107040040518602d00d0a030b114081000800400b40506000740401c80da944030804458100041380c4581071281c0a0070491040300100700c544901d0b8190040c281c1381d02060034040c1e0307502a01d040403e040380c00950112013500400d0b862803281c0007640b0054080401107080412140298171340c03c0000d0185540751040c1c040e1542010035541d04030346d4002c50b0a40c82c2030206400c03600509090010145 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 571871339 1250 571870089 571870097
    0x70f2004050c09090408070821160c0602091906111c020606060307170112141515130501060507052b08070e040e07050a0b04050d0605040503120f0402040c 68
    0x2c1020406800d03041e950024001c41c0d03041400c0e00c030340c101580720748182c01c0d021309400400280340e070400380709002c428800183c060303180a482d910508610100d2080c04000b0300003d00e074420700d2001c1829500a0710510310010400700f983d1001c844504200c0b00c0c0d40d4010ba0105540514046000c07105100074120f0f8800c0d40003090301c003511010029181ca00040400c1c0c0315039400700104100d60310400011040080c07082c441d0709203503100d520b10f10346085400e10454810480441c0c0601804001c5140b0012007411101907200c4d4a85610400080740c0640300181c10101648003900781902502500707000700683d407a0a6070761040c03400c20606150200c0600e9904000340341850715400c3c000944904040f01c04d15247c0b8260700d600c0c01c00c59444a403031590302c2d0b01c517040504528041c80301240b963300702c071f00844003102569034403003202c65240030342e100c0d159101012400032404030341c5d5600000e61281c40740b0150780c43c1200030100115000c0c41075079a501c03503803079400410085003000c2c483c980781e07071180e814 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 571872589 1250 571871339 571871341
    0x131401020c01030218091807090501030227070503090c0d1101090b0307050405040b010e0d030e0112060e16020321090c01080c0d0b0a0506040b03040605060a08100b0303070f200405 79
    0x44030105c407020303503a2810b00801030130700003c0000b0306201d88101c500e007403041070710f9000e95a900350f007024100a020a0348540e00f0f40100e01400745111400443d0050100c0c5648031540e1070500607201e0741c0006040001c113002d40a50b011469035414071507070a0394440d81603501040104d000041886c412130300004014042001172041030f981003420754003150411100030030710040010040f118464a100071a0300f02501d40005d43c2051b400c0401000303040c000380d82d04500381114504580c251385c194400c21081600120220b4200c070700c10b0300644c800e84a00d00440385012494104240d9007031254074810300f0400c0709014454201000c0c4090001d0301d4007443c10b0405402c0c4852441d03002e101e100b840c002c0c15036441030512075a845864514004120084c039541c1c58545d1192001219030084070129005c9141200044003031401524040580300701c00024100c4100c1d02120000400c40c040015625100a201500015070b0100003e02101d1040310405c680c1e201030b20080615004548001d40315600b090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 571873839 1250 571872589 571872607
    0xa020403170703050f030a0f1406011b02060705060f1e0103020913060e061504062c070908030d0e060a200a03020903030c070501020f030910050a0203131401020c010302 74
    0x2850701e0380030100c0c180c0081e581e4941441d0070313a014420b072059408130404c040f0403c00c0d0340710264059038200785400f40500043d8056460804002400c80b0020301041000703000001c0a010300f1140111644081c00c96441c0841e180c031440c0c40c200c0229038805080103800c040080107158040c0401c3c24544606e070b541050750442c1e00160340540010049540503095059540c18012990445000308041405076089404c002c0081c885c046207002503540501d0070440c0005003285024186804050f22182d01d4140c010180400c06c4014001740c904002c00c0a0380740701141228060000307103407039408084000b60440140c4111802c0480082039071284034642114040417a1050301c0f2103c2031080a80070780d0b5903204d01002a0003c0c00740090b244e8041c0b10209040110a00018404095034401d07001c94525070009034900340e40340300d91170000740c0016101541a1059008070f024000407190750041c0d9081c6621105400070035042503010000c00c2e1084845500e455030140f10380400d03050f081c6010f41c0381240103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 571875089 1250 571873839 571873853
    0x100e1f091205091801030c0519030c05040c0210060b030a060b090904060209060403150204051207060512070c05030d15093e0301030f02040605060a08060d051903080f0a020403 77
    0x382503007010300000040e501401d42d1a0800d0864216496140c0c403810f5840382406c0d07964034164000d182c010301c03640e10b4440e01c3d890310040c1c3d04101c0b41d000303000101d042d040c2401d12016000c075201c4082503100f6003c0c0024035407481c0c01610040c0152a0403591245000c2c0403d000395102544030002d120005c00400e00b45031681c80c0c440b5031240c0c010501594800340000490f9007480755a0001e030035074032100c0181d00c003106641c00400131a1811241192141c011854a60f104c894612a8038045201003000b4010b0b5012800c1c0c0350b6005501d0700f8100344a1880c0c1e00e03030608642c810004000081d50342d4001c0c1000c0481404e401015024070f400070429810906144c089105d641848518410040c0f051000148481c0744100c40c040480b501c0b81f03851303503503c0c5480b05060700b9403d4100c0c1301d0790a0030008a001d040c068240c3c2d076403550a94070682c05403600c00074018029840c01080d00c0a004181c41810000212854206590b00c03954940b0824030b03055032a04444032001e4210036995004000c100041810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 571876339 1250 571875089 571875113
    0x60904030e060d020a0513060f020703150f1a01030516170a0b10090e0f060d0602030414030a0c060e0f060705160c03150f0e120705100e1f09 62
    0x225042082000e000000001d040f0b00030400c620050b41c0c000200c000d01c403035000c07014004400761a025842074a8a6071025a42e06d101c01c400e000069010001c20030104030800c410350140c8040c15000240c04007880c425500f500c244c20800c4103040b0000507a194596414400c80d0740c40014850350700802c18000000410700410140840450360071140421000055a409545032080040000907074901d088030282081c196446005a410400000130b03e10300002c4241d00c1c40b502009001c1c21000c041c0b65071f00b2000350070190055440140507960881070b01402c0000300304480050311029201419840c154081d01d201f03000c10401c5800030180744140c040001855038008642d8142543c485007181640e5070300c03100c00807020f0040703041900c0000074860542002c0d0441400c00a0600408285d568000191025581400d045510041c0c544040b43d150b00041c00400380f01b01c040d500110302880d40041580d0301c114a095064200d80a181000c40a0000c5201b05140c01c400500082c243c030740b00c00d036101341 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 571877589 1250 571876339 571876343
    0x105010e1504170309040c020730080a020f060f100602010b03030304020f0d05062502030315012f030c1e0d08181b0301050901021c0c050909041118060904 68
    0xa1010543d20103403014400e44110301000740c010042c080c120b24000b941e41c00c1c80d00c00c00419041ea90288a40c1006401708180c50501c5d47d003140003000d4941e0355850f01c0d68864508202103003c0d0968030b00301d03510241710203030041e0606003810f03d407410718089900b0081140d41c00102960b151424040180d20b02006480d07115404486419a01d004407021840501014000030524015041000741429580c1545c1407a80c9848041c040b101502c1e02040e07a0fa40720544d81038094001d4800101c54662190b900002c004e07030a20100070155015003090400c0e03a40040d0014002d40002c02d076688070500c108000708104c02e0782403403a4001ba014100442e2030b803004003504420401ca031000036503000703c03c541e84c0e0416220441206d001c000502c551b81c54006e04030f0b080510a50030b000215078510f20500030742d0103d141c010071004c0f583c80740c2c01c80480208122078504090040900c55032041c1d54031011080e02c41d901a03084d203c1d800c1050404c1100d00f416003111000c1c450030000a0040e6500c80744c22096010b5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 571878839 1250 571877589 571877609
    0x2040e04020f030106030c0306020a0915020a0b091002180f010813060b030712050a0506070806060a030f0f0c120609021305130f0c020f15010e0c0d090501090b0105010e1504 76
    0x40b03404000300c1c0c05020b1035000982011251f400010403c02c282d402070584800603918401a01d84825109901d45126141180140d0009002d4000b040781c160301c00380c00040f940304a4040c006901010070981e0031a401945000901d0f90301c41440c0d05081ca95128420300034602100c0d02e10741000d0350052100b0724000030b0951a51070000c0324a42d207007040000e010340003018510400201c01c0c40c0c03c40e078a54000c88101e80038000c0c0004603040702c0c0140701142c0a524000c00c40c03424003100040031030007801d00a402445d155142c01e039410708e0358214801c889940c040c40c0d590340ea0442e48556900c3c00e83e405588200d041604c1007207540e821035075120055054881c112541607404221403403480181c4005544030003030500d040071a419587e0000340e036940b181d00c101c00ba156800c0862184040100c000d11a81c1d0111040c0c07800a1900d0b50944001c000c15101401c0004071680c042d1101804c50340a110129030103030328040107110341c1da084a400709004000316a01145026580d45040c10713030095100d103840034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 571880089 1250 571878839 571878859
    0x17180304061103130f090c02010e1f1103010306050106020d1b1101021005010906060207050904050a0f02060d0203070f0318030e01050a030603020418060e070f0e06060706050703060302120102040e0402 88
    0x1242c2c050003290709003003940210019480d150001e942041e00c00e0312900d88502d10f0010340c4511302c0d0041c011a0b00d290031039405880411010f00803542e20700341808201d02e883e956070005804a61454010794007860040100280541c142100a4a8504916180d209200515002403c1d02c0c200011101c842507210409401200d0043c005030302d403d2640c1d042a00060500001155191041d0321050403648250300321111141e0310390500c44e90180c04e4030041c180b604840100d00100b90a0440e003840b01d0701c040c221078500003100400728120f8109842c074134005140d1083c0100402d615000d0308c03d5034030b0080105642d12009640140001c000743c900b15043c000003003170b000c000c00d000380c0c80305d0015034000d0400e101c2010380700c419850303000e81c03203804035010752511903051582c2c580000c0348000e480903450000c000c40d0400e200c40126210080103143d024200700480e00005895016180c002c5201e07881c0801c0041c2188100701d407291080c3c40f0000c1ca60b00c18002003020f880c0c0b00302c002da00035805684076109 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 571881339 1250 571880089 571880117
    0x140c0a0e0c0d0f020304060902100e061204030905090c09031501060203182202030a11120a0902030c131b020607120902061e030f09060c1b0115061718030406 69
    0xe812102c42e40e0b032401303101208000174032603035410681d031031172003100c032014103444245080d20006407010505400023030911504071404000c1c1001504a40241400035207550745d0784c0061507001c0c2c101d5000d0351001d8041014101400e0410100e00d0b40640b071800c0403001d60407c0402035880c0202041e100f0784001386080707442207440b102440541c80c0001c558a29481c64031211510207075000781d13580f00d1100e1800341101d9090b0040c0058840030091400120f8035a02d600701018068020000c0036603150080346040c5140c1c0e90707020141000c0c070700d540c200801d003030388154015280107040207400780031b40d0040c90400842540c002003640368100c01d4480040d10066074008100c5600a0b400d0310b4400e00d602d4807040360b2004409000e10700c1400080c40014240e952904850f898072002c0d030310b25207110300a000b60881d2011800b1804041d280800c000180d0032074a108181c1b015107035038000000314004480101940c2c2c0f00c1c0c5c0c841a40700f084140c40e80c07032400d0829010303a41ca101c0c038800c110422201e41030307083e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 571882589 1250 571881339 571881341
    0xe0118020a0908070821131e090f09051c050d18050a1406180714040b18150405010f12080c06190e0c010206010b090a080604140c0a0e0c0d 61
    0xf4007407210803106503d40710000a40d41d0420144819604150469508036140545040320705030000c0312103641c4480c1c500b0003150b04410000e008004055900d013408941e2000c0d40c072a81a5503078121002250036002c2c0d00b0018144010f440b03480c0c0c00c0c0300c8035140e240b13070a90700311040318012000200006180c07400054008256001c44900038030b14010020000144010b10350300c14621302e01c0d1400d6607050784031802211042656000f0355445604022030810012030002020207240c03002034000300b80c05040074001a0059410b903e000b500c3c644080c240950030615441c0b500c10401c055030704001e55410000703511314400c100e1041d400f05444a00380b40d800c1010560030341c4c2400e80300c00211415400e02103040081e02c948071844a070755525001c1c415020020014400b140c066068014040303e07401d001c02c041c0c02c2d030f0280c0c2d00030790812280403000030301c8042048068802c900034a400c003481050091042e042c005090b600c02d02c200ba03030032018040006040d080c01d40144040049642d24144101307814 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 571883839 1250 571882589 571882607
    0x40209060928020a0e0102030c060406022a0a050105071b0602030714040e15040614010f02010b0d051510060f0807032318010c0c02060906090301090f05070e0118020a 73
    0x82880d140d00e4024000782c45581c0292515510940f9040e010301030080c01240e40e4002d82599000e19807000f00031030045800c0f503006000401110b4010544c6562508001c0d2040c5030340309001105a11880f00e01d018003100381708180c1c00624034a44484030000b9081400c107051240403014220550004c040340c060b50058003903441c011010401d8544030350340d61031005020304044038491625a191002c40c2c45a103000d1081e881980c90f100411404c1040c807100441d202080e030703400841590b680340c0106026030f60304030b0305500e86d520406c02481030941c1c8803200c0921900181c070103a846100700509011258010045040c03510381e52510040039540d56108030003800301d03149850068488000300210611445900603c9004801046042002c20200c1e042c03ca49840c0100d000050031005030b40c006181c2280107244004006103494141801500020f08461305600203c5400c0c003d0300e01202040024030648c001455828800c0420303600d003c40c100b814481c281141d00c211a0300188291a450041c0039072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 571885089 1250 571883839 571883881
    0xa06030b0c030406050702010207020d0f030908030c0c0f1e09101508090f061b21010b0a09140108131410150f181e0905100b01080402090609 62
    0x1400203030500c00d2a8603400c1d4002d483c151085402c2c40002408039005000300d401c0702c0d5005d0000782856816856280002d01c2e944811820050080c400044e8040c0c104040c00c2001c2c0e49101030604440040c040000806061448500a5406402c120541030b216a0240800082038a8004c1d5681d6038551f40010244503802405500d0440d4451800080d841030340035102d20f00d10b000700d44920140c400801c0d030310342c8210344004420107800010702d80301d240c1c070707019007540410301c039103031001c00c0c240d4030011000c040c2600810144540440d0030500c1603480410000205003e1307406110303002200e400241410001403451041d40c00d00000d102c10000c500410b482caa03243d09040d24040308110100d00040d2078449440050580c80c000040b900f02000000785040b03482ea0400300d265030202c20a80c2010304203001c49100ea00c108055100c80e01180350068001c030b41c0c41240503144254649a03002d08640d81c124219041001d080200801030700e4103e2020b410510445010030555107440140030362403499619 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 571886339 1250 571885089 571885103
    0x18030a080f03010303030b0402030f0105042721090b04090b0d06090b070909022b1b170109141b0d06030c0503070e0c0a180e1807080319080a0603 64
    0x1a00c1e46031a04600954142d911a54060101e02c25580810050340016125440004810380040180b40351551001001d0101c0b00c844030b034030940c90410350300b5810043c4000d0701c03c440010840704644910b5074840381c282520b070901031011814010b81c80c0a502485c000c000d107050361003d00341181d988101e030030100258040014000910746245c160610141504e5881c04039003148008a868501030080e2546040059070340ca8040c04110420441e092101c50350812465a845420a8000044811000588490f2555591113400610384648450140d0101c07850300d04e8490220325900c1005c81c0ba6401401d8005010442021148403020394890b210703240d080240344c194004100003d5080783c01c110f41040301994200c5d80c1e1100d441400308030842b40c1810b6100100b1134a40b03924081c200700c0c80b800c0c03015116000c00d2a15104041d451040c1902c0f011507818445038401c0429404020220140080401450819040a07c41300b00c0b80f1400341c0050a100c140f100148226843d0b1b40a04020351304162 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 571887589 1250 571886339 571886347
    0x70f09090e010b0a050102010b0f0112020f030702031905160f03300b03060606071737020c01050d020a1206151b020f040c120e0102030702012018030a08 67
    0x8aa0080c407504801c0c90103444c0b003440020380e540c018850b4032242000601031040e190410b400446505050856085a2980c07c0c00442c814502e418003840c81603000c0d0300115911046200c90fa00045075424100d0100b0808000d90115845043c0c0e41c6030401e507124218600c0004503103800e0350114010656a00e41314642740c0d54280c00740341051000b011a104140c00c000b43c044100031301d9114102110303001e400c00400c009186c009088568030050030020250180c0c02c1052100d545500c1074584030040c1202c0f42c07050f00c805d0b284400c890b0f2a8200b14602d0008001c288215800a010384c004c0150221030145d000c10b10f0920355014240b9414446007620b001c0114513103ca0b04c07410000d044007603400c0011815408542d08511303180d030844900b50010304540010f1403000800c00078018141001e81004a80c0040c004c070020640510310300310350300301e00240c1c0f00d20f42681c0c02070840c1c00390b200c40c21810400c00a032020b003010007030072034900c050070b41c1d601011082e200c1e02292800c1000c070002410b00500003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 571888839 1250 571887589 571887611
    0x70312090506180106241e02030915160809010903060509030a20060604093809070302010c020f01030b06040b13090209221509020409110f03070f0909 66
    0x4260740d8490300624040201c0f5603103000c1c2c103908850881c000c011842c443e0800520720004c0150301b490f852a4240740040c2030031310b96100d90840c0041d040c403030300150384042269611440d103d09400160702c8600486814914400381c000c0940c402d032403003d0140f90340000c08a141ea4811400c1501030f541100007031059044c80c1a41076a40e030710039200c02000500b02451460714074100e0944050748110034000341865290f510801005004002c011106100c581d01c650910001a244407144607402c908060400b005461007801480002094079410340c002c0142440140e822604480c0c410350190344818100c0d80082c0143d0007001490700e01e80c7d0004003c2070004907815290024041c42e107604140280d01603442d521f540c1a130003980d031800e92010040e080e560b074200c81400c1e0450410818040891150030145000f2003000c05030708941040c5400040510007803006001b80750b0102c0b03818081616110007085900304900010b02400108030a1007400f1100c00c1c8a4102c80e000b92200311000c00c0592964 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 571890089 1250 571888839 571888843
    0x60109051206041713030807060506040612110d0c080c0a080601060f0804080903010914010b0a0b16052505011b020604051201020d18030809150a11040314070f0b0c0a02060703120905 80
    0x16080884000c0d061078001100cbc8d06142c083c880440d0548055260201c10681d5010f0a4207c020003690300300440000410200b00c078410898018a0210302401c2501400700034441c1c0004503420154041d84114010803083d5844014655600018a4010f40365140c1c0e11705000c1034415440415455030a2000d0360052007000c2000c081600012402009000000b000b403122241d450701c9045100d0340c090004086000746010519540791080c4103541d00404044c40d03044400c800401c80c800301c86c0300c042041c0441d50f00111841401c20b1008403510054400d5030000c0d43d02d1090b8040c690054028609181c882c01007501500d0694041000504c0010440c521800c15625604800e0700024085404608214004101c1441d000314440600d0741d41d0342c3d00140d44024000e40040140002002c000000c045010018032910b0040b0117000340001626200c8803601c5649642c1120202030340400460004a100003003e801d02581924941d48a048508054420303d62100464490504005882c4100040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 571891339 1250 571890089 571890097
    0x20a0314070314010801060e01050f03101e060803031b09031c03091101030c0f0f020c0a03060911090705120a020f071b060302091c050f030a080601090512060417130308 74
    0x443c406502a80d136184e105098507410710a0341c102c201454014072441c00d11940c0e90140b810042e04640e565280005850304407003c0d110184092010b080958004020a01a20b4001c0c042d00008504604200300d40070540380504c49548070780100010000e5494a052000006882440c012940900c1150340064094032858104586400d0b130405844d0040d070181c41014108400c5654451804800e482e0030b540c0b010210303109105510400f4605141e51399181643d1014502c500340200b00c10059280000d0411000000c40d8401e807619800c0005d01f030b5000b010fa8803506400c94440443d1744891181c10000d00c9104c00d581c1c0ac486001480a0501945602e8403041901141b070240c00340740d44120813422070041d034861a5200c100e000a4411820600380d0007a10300b40128180ea140486035001030385150f0010920401240c200c10400c03440e9030f00030401d100208416100b40050041c0342d03207001e49407100280000c05061803410b12540d550500000c1c3c943c3e903204156000051611390030030001c9900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 571892589 1250 571891339 571891361
    0x708010506100c030503040b040204020c0f03190801080312040c0e0103050d02210d050c09091003060b0d030807030c530402120111040e0103020f010807050a03020a03140703 76
    0x400c1007900400c00e0f21900716a4049509a5603081c2540c650360b6914000013406042030f40d22540138402d1480152051045a2042e080c040080d503a5038204411104500c1440000d0806d2002030b400403c0b00e0080401280d0707030846091111955640d40e0b10700310005030004d40013400940c202c1c2c0004010040300082001110490f50220b0700450700711852501441105413400b8400071003440100340300841c1d6040590400b01c10f1b00c0c12428640844086070521108451607d400c07402d031a010000c0c804075101e032440d48413050324040042c2c08151000307800c00c00050408410550740c0c26012500c51701c60030304040c02c030f040c1014482003241c3c410104203051103081c50740c0041d01004004981580b440ba404128444140742c00b41d1035035503c0e60204000300b00c02146c80c0303040d5501d030f2960740c00c2e006031640100094041074901070703401d50441c0140007070050484003107810f1140c19414440c1c10b5070400e040d00c01d403d010b8500540e0f2021710900071009414050042e204803003042c0d0038006e8180d01500800c614007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 571893839 1250 571892589 571892599
    0x7082b091a0f061c0524061e061204020f10091a03040c06031e050109020711090f2206060902030106030c1404030305030601090b1204050c102f0708010506 68
    0x510b94610351078225505982c40e0368050b04a8054440d424200300c019045140200c1c142e58080e4445410301d0402c20b81d030108586001c1c5004100425440c01016a00d0504c0404084070442210240482d00a200d4240820740381501170300054215543d5001c0904c880170003814035152013602d03d80c0139000d01e080307002d860100200b054140c681002906c098a1045810075501340c0e0651800800b6801080c801039420603103410301c851a0b142004078040c0b107008004030400166200110304081e1011018030380d44030300c54a0300b00c040c8103480c01c0340242d0716080440c01140308602c13120858020384c5c10886840c010040c030b05204002501c4241617003c3c504031812510700707002000c1e520b9070403280c1c001c0950080e20401e4041c0401e0010906c03c001455000e103042c140912002e0301c64142001d40d03001250391040c003804810800041040600c05c900003007034160f5540940b24021000a890280c2c09101e8028140c2040d580c9008a0142c0d45003041e0004204180e40c48030381c4444584c2d019141c00c945d064055 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 571895089 1250 571893839 571893841
    0x41802040b01030c05040506130b190305060a240e150c12040b0f0306030703021e01030c0806030d05030a090b04050d0207120b28110904050a0207082b091a 68
    0x180d4004e01032100411980d5442d1442e003820b0008015054000b91030080303100c140d00740d01007002440341d4010810b4014088425688242070f62005043d680010304090047c00d00240030800320741202201a450000600c00d6420038414020482d460240784442c1c50b400004107201040106150b03005081003900385d4141c0e00c86450501c800d8403603101e43d20806022207401c005100c50803030716101a5410501c000c05803100700e952038000031503144504001c400c90303299041140b80e056806126142010f0440d0a0020301890f280001940304d030708451404091000000010308100da03540d100e01003555204412060310300345803d000b1380d1031601003402400340c4900300300071410801d0415450000c17039100c1015070155690b0070343c0c000c00110070059404d50220b07a06c2c081880603024090000c0507103449000c103854030303450420842a100050070084410344100300d0240881d06880c102c50b41b81c1e02c04802c402c0007184000d04540000000783c0021656882c09988004201a200c00e04c0202e04081c41000c4803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 571896339 1250 571895089 571895111
    0x3d0509091303020604150905070603020c100b030318030c040204030b061014030105121f021312050a11060f03070201050105010f020105062209080309070501030606090608070e0a0504180204 83
    0x121070007584019015a004800040c00100a2405c2201800b8411000700f86186603607686072a044580d0440d801094000c1040f19642204003d44a81c1c140807901c144181c404910201c0d0b1a0700c600c0c040d01551110310701c9600f035903032410440d1029280703000d00115a070b542c0d6030401003100001a034400d84070303a2400c01c1820f182c52180c490003150b000f08281c150301e5640313010200400000e9217015910b090103443e07078900c580c5944102d01c9141541442c80541c1d201c8026040704501ca02c250444000b030040307000c01c030000c190001901c0038100d0744403001c042c1c070401c0040001e200d40074101e10700460020000c100f082069041d000309040704c0c4280c0314049091170140707081e2b0030b80e40c04461075600540c150250f000c490040385482041120071440020307403a801d640b690a0300758003c40e1110003075400722608100701d59042c400c00300204528909030301c10346c0c00c10f04004c11416020707004404015611072018000e81e0741000c002c0003810b004004200040b040c0b102c0c410143c480d060260702c03d91400b200124 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 571897589 1250 571896339 571896361
    0x12012040e0c07031b17131e03030801260703050307050111070f03030f0f021b07120510270605070e060a0504050103020d0f0501031a01060e3d050909 66
    0x1011542c1034035152040035400100e00303801030401c00281d0708881c00c3c07040c1806d02c11200c0300500340d1408006141014604001d02c0c2111640402001e109070048001c00300086a4030480f4103055880421686410b01c0e84204c0214101d060100c1030840c038092410004200500000100843c5d84540000e00c00c480c0700300015a014010100013905501d541c00050001a01c2603000390791a00407110300003a61129504448120b810007100300750000e0302c00e5240c031100c0c481000910b000b40101c19038440c21080c05e585030b0f600e60440403000c8848c035407580c61181c54a60620310b4405c0302121451058010701050510310040c100c243c0d03102c0003103a008900215181003480448041131810782358145011b00e807200445c0290311040d84076034441d81d41c405264140c403140c0111030095000d40c8841888c200a040c0b4035280c3c0c041a80b00d5401d0019400711501182c0b50008030006c00c030a882c4ca82c0b00d0350302e800d100c031500405030070703a00300005015100c4880340d40c2d8019001d07100003d4159140d0b810f66a5a0418503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 571898839 1250 571897589 571897597
    0x1f0b0604060c02010c030324141e013006090b03070503031c0b040c020102310605090409121d01020c0d060207020a0b0c150703150302012012040e0c 65
    0xc0001d0001070280b80035501032030080c1d070160f1007483e002840940e40c1da615602e001820710380c480f0601e4a9070042000c000494003481e0003440071545248510002e864480d020314403e1480c0e8180403121301060300344002100c03241c45140d8032800704100344014801240050000b4045c10103140e2038048450302508002500d90191480a0b004501e002d1340d01409540700350b01d400ae0081550385840b0003030300a40366402041d5041c0c0542d0009a102c090440c0d0052200b01c11418002d51408520000c280c0c20201c400980c0c100c4402d030600c181e0301c4600d00003003005045181400f600036008000681d600c654030181140e40807400520086100e0002801241ca5114500c4480d03800540061500080340440e402001c0283c0300604142419654010740c1c0390a030803600c084543e41d000098030000d1100010031300f945c4446945410407a10000044241d0b82d000329000182c10012342c06c2043c030902c0505481041c00c50800403c0700c2001100c00101300c1140d00901404e090201044081407038004450165 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 571900089 1250 571898839 571898849
    0x90f040c210606140307061b0f061a1e040203041a0405060f0127020f0415020312010e010303050a0c0c0504090f021014033106020702030f07050f120106081f0b0604 72
    0x20b45006c51030403108903540010120b040070108035100e00e400020b80f800000401c1c45108020100b050b0b181c4280311818400003d5505000e50482d140482c00c984101c0b020700504002180c0050b100d0701c40c1c0c14030700301c1080021161001c10000100780000c2c004001165031240070405140101d9a80300d0101c8406443c009003000da500180a424240f00d00c600d07009014070342e400e8003041c0d0420303a54686403449502e0450000025070000150440e0002c42ca24009001d0008808102407651540c2e07802003181c89003513265010000b0401064041100900c40030004110051060011803d507003400c805001e421501203204031100f050030403146020398080e158001c03181c14144c0c11030ba1105c48043d00840043c00c04039192850030f000f00042c8002e0009190660701802005854550b144141854194400d6015070240d0102908200039030383c441050040c07040503034003411312116515545003d0030041d041814107002c2c2c0d0640060b90740720910f0804000000e42c40074410345a865092043c507101d0f83c020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 571901339 1250 571900089 571900093
    0x903140429090109170c04090b070305010803070215090a0510030204050102010e0604030206010e0c0705061006030e01090c0611030702031903120603030923040507032405090f040c2106061403 84
    0x1001170b00458251700900650160940b214590301800040844507001411500d041c2144140151141d062003098090034020008514060f602e4002450341413101200a0521000043d109000d0f15544660030050002078210001d032408840044c1c00703904a400b03010300561030085c1c10b0124500014003140030f903802d5009400e807039083c03c622600d448002028803000003420080c400020304101300b218851249030000e041d41c2d074100040102614104051b94019038102440304010480c40145081242c0950916180002c5040716080c02c40c0198840030f503060050480c0d80691a050725052010a8440d035581d4182d424041440700c1140d00901001d400280e40c5041849907031151b0006608507000b0114814000c200000001c080d903104580150010b81c0340c8130300084881501c03000c044000e40080361041c41780c6c20040800d01820004010400c0c0700041408182841511000e40c405080300d080700e0305500b201121007903100600c1040454a00b441c0603800642d0001c0884d149078201c6000300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 571902589 1250 571901339 571901357
    0x922140c0a030203071e090315140a0e070803071109011a0d0c0c0506070207170706022805101401210f030207080709140f060105040909031404290901 66
    0x7800702e0080d00020040018000a888013198082e00d84a008800320400e80c0d43c8101d0034254078014604080c0c400c1c02408140c00c0030350000440100805a40c0d000444400015a00322070180043c502400396103e00d200b40000a072800c10310048580c2d4a0200300c090312884180d92f03a0f101400d041c1a00d20071689001141440081510b942e1a04001203480c10340c80d01440c2c0710800d031103c5040c18015140040540d0055901f0009a000301c1c080c504896030020142c24120300e00700c1d01a45503145034100580800350348100c0711030302c208007180c02d0a0701c0c1c11100b00c0e07084d440902c4e0060000d100450003428140b40c0f0b400000341e4854a0700c1e403288600100410f04c02d80d00ba0701c5c0e843c08040c503c010400c40950146600101c0c02d0401007169000901640e2408074501041c0f10f90081040c0029000d401800d01c05010082c0b2a42c1010407942251104d900003d0084a1420f01b160000d40c0d03200c4800b00070500080010b01e00c40120031000f520040401c00e410100d1031600414624412072028a021501c204 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 571903839 1250 571902589 571902607
    0x210609100302100521090d02010b0a0510080a0222061205040f03030f090b0c071b0614030406060806040c0e090106050f2103161a06010c06050c0922140c 67
    0x88007401540100d00d0030120300b5007958143c0541d900007203410700d05e40d5110300f1f402c1c00d000e5424040c05d44c2001d0195084000350b401c200105140b0103546c22250140400c600100d4442c0006034103d46419580300300d0079110f041210000340d100e1801d13114403800602035051503400007516201d110b010320303403143c404002c00d08169010703401703418144000f80c2e0b0640e8503004100450600c0010030300c04c0c032402100e01d80e180b20900c1d012100345400704040e6a500c1c4501d10611246807c440b00340b83d030201c0e014819071607a986107801d1001e8122500540c2c4540030b02000d010810407400021015903040540c014460380e900d490113403c0701d24603c00c4560028030000c0d00a80d5081c8100070310326000001101c40c2100d100003500a00d50341c07105801c0407406144200b80d8090000014401b0300691040c8404c400d02d05010700000c00c00f07131841c0005420300d541c0b603010903800b00041044640324000589001e040c1040b0a1100c100301942c810800c83c51402c00c00d00c07008807001c04c041c951103545152401400c1421503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 571905089 1250 571903839 571903847
    0x708071b02060c0d021e0307050307020d0206161a1f090209030c0d0b0a0c3b09040318080a03120f0b0613090f09051902030321060910030210 62
    0x425081ea0010020401d109144006002400c681d0364203400171322503a0052010601c0c090740b45010b18071190010b11025002941c044201c0c0c52907501154201400749550000402e58480e4481d040b5003004030400382c004100c2510780c1c10110300d0002034881c8a95440301c943c82c00c0c0c0e00285001e0200054041000e00c605003166014154041001c0c0849403a8505400032400300da14410083d51450300f141d04010202e40c0c4d50148400071006441c08040c0868020403048080c8400348a042082c0c0060310400b6040031500815941d401008110b00550b0800d030030054180c2c0f10390202c261081500b20710110300500001210000d07140c0c1665040c08051400c10301030000c00701110600352060702c0e03040c2c000349a59640090224a201313200481e0100b407074480404210303503801d203840c880c0a0810059002042000c2a090111400d041580b0b0301a01184002411445592104003040c02c0c140b07191030110791640c060340d00c182c03010f45255542d61208041c1e0001c8100c0c0d84402036201c000300e2515040213100b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 571906339 1250 571905089 571905137
    0x2010e040e152a19110d0503091c081f05030a08030901180503190306060804020d021201050c040303080609130311190303050403031d0c0d05030f0301060306050108070807 75
    0x310071500d075041800c090a0003242d1416a102102c5240200d40c0d041c1c064500508400d89042178101208003030040080306485903901641d038024403201200080c044c00d0f080c4008504004011804801021420b030003900700002541c1140c0311040b059601e80724800910142000c1d904010000e00091010b40e840da1440e42c8002c0540d02955280c0400d8045038032403640e030f81e20041c8a100515242d0b82002607102500d030b8400100f00070541000c504110301ca411101c0c07207800a80681c1c1c0040c0c1c58100e800440c424440280c1c448080b5880d003800c010030035403180094820ba9200c1c1c2e84030282a107a58080000704502610111400c80391a24034a0000e8014000403052410060540d60000300210403210720b299056070650100e40c071784040004059040c8540440c0041880101001e00ca00c1c1c2403143da80e00051100e580203501010064040c89020000e880764104041d01e2290740350303100c0000402400b9248185c6000c140e6200c08245040d000301100741c455000c0355038400c0721009100c2160540a5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 571907589 1250 571906339 571906351
    0x3180311120a020a080706080f06010c03050903010b0d060501080f070b0307230301030812011712031306050a06081905030703080709030501050a05011a040608040f110907020a02010e040e15 83
    0x8140280d500060b1142260314008045c950094045c2910741034011f01050302c01424012405101010494940c0c4c01401c03100c012a094034180713890b00c910401080c010711981c010241d0003040041004104169600101d050310100303010380e455010010022a41e60302c480c0118a20304805000280b0201d11801041c1010010541c0825510701c420b10b00801c07c3e032080e013080d106000001200b019000c8450245401040304641e02000300102a46141d01c4113411071030340a6420002000c5088419581c00c403004c910b400640400c030508208462078002c1c00544110326040c082c40640300c60603618012060625600b05015615000c00f540c4d040740d100400030300c0d440c140865800007102085003442190310542c00608009450f50411100859555682c84500b0b140030042209225181e07000b03100c0d80c2c00c1580040c003c418001c842c83e0100b200c80d00072090301e030419110f030f00b08801150b00241028500f8000c2e200d0240c0c80381d40c0303030a02c016903130800859600e42d40b01400e210500e106450106078001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 571908839 1250 571907589 571907593
    0x21c081206030a1403072003030d051f090906050603030307050f030603010615170903030910020306150a0f0e09041110020f0102030702010b150304030f0c1b0902070318031112 77
    0xf5242e40d441c01a0312043d01c4034000694004200d4104200703065448220083c8410340c1a104000b005000940d20310550003000942034460001c80e82d548010f03075a1a041d0203086000502c410b44440b000401400c0104c41554614140004240e003401d0110460780182c000d6550f2a18001c0c102940c41c1241e4000f03846c40d42c056581f000001107118003070405241c400c280e55180c180c486481c1c6102e000c0360801511b4034199070810001d0000f0101d00040300254150000b00160300d9a4441c400107614107040780d400004040009110031020b07a11820607071201500d80c0703802800704241c405001d996241114014a110b50701e0144c0310701c0d031030301802000c0b01d03140e11300c100c0e0000640b014005007640c00c01c0c1e0309500580c0d116090f40181c1c0c40c01e1541c143c940300c0111541401c41c0350070b4800500d0380580103020345c1484a660a04400e00c03402545080710310114440c561381c8165160b81100081d444108160300007070104401c601d9484100c5c50503011240c0000c241c480c5020726804010f00d2608c0403a2500b258 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 571910089 1250 571908839 571908853
    0x110708071a1306050f060f0d1b082805070515071a01090b0603191d0304030506180c0d030e04020913090605091c30050103021c08120603 60
    0x10900c07211295100d01000141c403880300032185000f0054410140a00d201101c00e03400708181500c1d403002c0100340840c1220480c4095000c0c2c2030130000c3c542c01900348920160050408202644001242c800c102442890901c175900107904184030b410408034000c000e034100386004c10451500180c110000c3c00d07a50301140c9024010788e540c101c2102c1010340054a000020f00400103078a05110300c001e130500982d80070f851450101c100350740d100894400643c04998522410706061080015040b58440410499607515100c0c201203984020031103101958040c1004102c450210210f40d0300d42c04140544140450021070b03a09841034648400310682056080c0310f1b500340d5a590001542c80262660030004a078001c504103001a1200144018031590219060001488268400710440c0701c0705d02e40b01840c00a0080350b031324200288840b48003648a40310752005c0c0805503510090480388200c40e4010002c05840c0c1d500c80031000580041c09404091045c03200a2400810440d4028402000e440e0f807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 571911339 1250 571910089 571910123
    0xf09160e1906120309050a0b0f040510110d02010b04110a1d04180b190608060a0b0315071701061805040509030d05070c110603060609060901030b031b03070911070807 73
    0xd030341c100000a41c0045c440c140701300000c2c20071861980c09014a240101e162402c1c0068088840c070032407184600805882c05aa02c8640c856104643e10007070000a85007003541c0c1b040024043e018401c1241e10841c9040b000e001e02c107818004984d01c402143d00e806c041c407018052151007001c00c0d001d089030000c1e203680c22140d03040100d0060701d0542d031003607845214508004c030142504040800c01010b905182540601140780c000582d940d02015502001c100302888030007281c14480c600524071512500d902c1032100b1542c114074812132540c00321a00c08026070f41c9510868003000d55800d942c60114503944c0600a49c02c00d60000c0b40d00c101e103042140c1c50403c0c06880b40d011100308541010000e45003245010800c4500e1050400480c0d080750064114204400012090300c208000f15100da82d00154203d5a079009810203401c03402c004050305c808201041c24803901d44074443e10309120f4010b403400818100c10610403412450303582c01155050036450760754247d4a42c04210107499102c009854450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 571912589 1250 571911339 571911359
    0x2040615021005060603010b0f0c030f070602071218230607060606110109120e01030902030d050a1107120336150e03060a05060f090f09160e1906 64
    0x14040820381c0204602e8082c1c6010a08031000074105a00c00c00040004001081d8900241c804122203c19401d5642000c0d019407440c40c4039034050310f080301c18086492010b00a0340e901a208450081440400301c8406c503a00301d9550fa842c2303116840d2030060310001d108280081c1174141e080d0440c00c9159007203003078082c001109908041c2d4215038050310392606002e100d0303009040ca03864110f484d00900030400a0381d208882c040030081303820100444101d11307a600383c0c42500030110281d005015946030f00c2c003460b4000c0c6103601a801072000f20303e220920700890000000c0f5241124440c0c02d4240d40c10520741c8e402c41310318035510310328114213114203502c054604100351650b0b40740350074610807401c0310302d4042840d000c410b2146101e0184000044001c8041c0c4000c180584d100302402c5000445944030000a02500d88000c101c2d9003040044080200212130074070030300d0051030100c08956400d40c03194283c1d5102c581304e010f002030110185010030f0003095425010085078440c1c80011406988580800e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 571913839 1250 571912589 571912619
    0x605161203090512250507030809040902060d0903020607090305030301090b1824040203010315111e030f060d03021c03140c03060a060206070203071506030215071205070b13020406 79
    0x51141c0c002480b44000175845454a076494a4805c45041c01e4441e40b101503c8024510001e00303a4500041e13480c0d01540c036940408085c41d401003555842d82c1240005c0d00040038442d1003200584a00404a0020750203048000116540100254510307800e00007180c000d4860565980d0b004030422510992107915082118481d500504000c0034a103151003168800043c81040940200e10400040c40455403c0700342140700064000003145140320b6240c6c0c2d129510030302c4001c01d00941d24540002d1290003001c0214044e0102d866100b030140c45500400800c085020401405a4800e85450300c1135002542c056035199031500b00042d01d10000c00c01615014000c440b0114204400003c100300c030314004001c0000350640c1c0c4014189458035801c082e41e248940b44020303107140a6041c9a0100d885140c02890245034003410040400c03c540e5216502034021020480d1001d220a01e065122481403041c2e0b1384503a00501c08030ba69441c0c0d006018a4091154000da810984030358012070031500c10348140e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 571915089 1250 571913839 571913863
    0x602030c0c1512130b061f030c0e031b04050a0c0504030b04150612030318120c08280f050c07030204020c01140906071b0b0601050f270a06051612030905 67
    0x4c02403501042c0340c030862061004080c1c03031045d01c004584000b501a41d40c0c24071040c04003424005440a204a0180d03507a943c0b06141c3c65040c07007208142d211259034543c2682e07400e003080e9814040d42c0c403030340300305800d80d081640150001401032000700007183d2008501c40d005030140154205440400e0f4151307060f60199000035011b100d902c07034030341c2c10503905100300c0001c420701d0650b01401d917980d41d507100407080000c40084104901c00d810b10043c0641d080c2194101481e9030030044002d07000340c1c070540d950402600a0f20115205140c4c1d02e00301402070044482c21002c001c040c210321800c550800009400030201180c51759a40c0302820500030102d81510b0144200c07000400d101d00d0040402010301e02da044501c00104004030080000540e9904c0c0b02d0b400000134208140c175401c81c20f0b15040c5c40d000f00902c00d240040c4521100300140740d50107402d40f5101c3d0960300c580181e5121442a1014828042d8001440d2a8000c80c04041141041a510703c00094580464045002d407206441c0c07081480308 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 571916339 1250 571915089 571915111
    0x31107080a180329060d0b06120f030304050a0c0e04150f020f0a020c0f04060b070b0c090907210513030f02010e01020d060509010603090f06020a0905130c090602030c0c1512 76
    0x7040d540c4000d413002254403070411a40d58101c05003590742c0c001f200da0302818040c010b0003582000341007003006000c601c2c005100c11044a88030728181c244503554000e01402552001d03985000812210200e550349407107160807400303254086950601030030051440c2086040c00340c1d400c0c800304481340500d00060600422035801082202140d800b000800320030788003001d1260f03141441c01c10561b00c0403800e03076000c0d80d000103d090443e0303202d607260442d500c02c403115030341e020b800e070010005800d80046130a80f00c26046d11348d00391030600d54009030040700c00075500c0c040c090610f0b46c03540d000244182c403e005000d4040c0f0003c5440074103203102c2804da07000708004109580c4c84407001c0c0500d00b80001c1890040c00310f40f9042c012a1901e0300d8210458138610409403100b5000690404024001c1c0d41c0c941c0100405016070141a40303412605000384410000c10700050305949000540b1b510000c01c3e14240c088800c0500030ba20f10344000c2200380903008a1002525100f401840303134100d200c40c0e1440c814041004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 571917589 1250 571916339 571916393
    0x4031103011b022119050301090e0607080105060a090b030c0901030b04050709031707231005010635090312100e0a1a041b031107080a1803 61
    0x1081509503041050340b038880c21a50750800200d642d0000301000e10a020418010100b1203801d0210014418a07207108203032401c000850380380d40d520200840c125152a50100115a080c01510b40c40719400d6a00d140040c614900500040c648940248201503031810100510756550b040310320780d0b8204070b9141040348400700f107484c1596050b00420102d076004807400c11051501400142c800000781c00094180750080140001c42d9203490101d0b21700b127030808468030554010000440c3c3c1152000300c2c540880c040d15003003c124852074019141078504546131b12002c491480c1c81100403c3c903051060344005528851340c540a8101c00d44640182e00c0c0380041d40d5119400030b801006240094401101d16008540400000050000007a00320260701000b0031742d05011103484803580040341503254420302e03101110881200c1e8980051001e801d0391006c0c8074124103110541706c3c1c0e0140c4000548050b408104004100f40300e000194990158025461a142d449494450b4200e0440c850280604000d103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 571918839 1250 571917589 571917623
    0x20903060f090c1f0503041704030c14031b010f0e04060f05101103030a02211005130e0a060213150804031209050a02040507090b070b060a150f0c15020403 68
    0x40490350060b0b0f0103a8586641c40c00d001c06001c62038810300508410058048007150070056069422644168801310b82500e580e12401c090401d90710a10071850001824281d008403401e010440610311806290b81c05081941c00300195402a03040d413224042064413080218240c3d90340c03040a018014039402c2c201a40d05150610440010354068807040c0b000c403000c01c0070000c5000080701e601842c500405600e40d00740303e15010390380d5100c2c41c10a800c030003841d04100700c600b8103050060454608482e400300c4117010081d500c00701c1d00501da402c06242c2180c41e8180228103107400918a20744c094110380082c5130359050340c4181c510000102e40002c0d5501062000b8150700c01074251a280c801401000381c88010395460342d89035040c0000901854513400000c107414040c22886d00188030701c0c1c9003580e4603212480d006258203000c9507054460941c1000c04121000d42160f5104004c00b541c6032824401d02c40003040d1114880ba26003195040b4030654412030884980c0058002540724030341d4210500e08207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 571920089 1250 571918839 571918843
    0x9150e0106030b0907030b13211206050415090518120c010e0c0603040f0501060e01080a0309090506090c0d0603080a0809210406050a0c0204021809010909150b04020903060f09 77
    0x782101ca40355005a2040c00442c00f640100340c0c2003c0101c01001e030341c040c82d107802540211104a041c9d071421b01032444c1c018054101c1858001e81904440070408103844500b00300403150100200310082c4c6a903c0140714403a0303590300054005070500d0f0040c04040b0112079032854044a000300ca505c04002207042c00100704c0034024001c517500c0c0900500200700409004c2080c40c040184007034291a0307141303421814040e081d8041c8001d00440c07111244250786a0507155030740d9030210f00460004400300da000070a212a482224091503004180380d9294480c0d80902200f9000802c0b0a444c85030b44610020000749201f0051014a4040d02d544c0300502c0e007101d8090a0078854004102c5150700c480703c1601e41207014045405486e8541826912000742100c100c0313240d0140c9000075040361000030114009014041040c2e40e80e5006ca40c102026a2118188429180708283c0100080c0141400030f941c0003082d00034171780399003028000509180390040000e1030640300703070303601000505404188583e03283d003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 571921339 1250 571920089 571920091
    0x40609030914030a030c1e051c03050c0706150801020301030606051507030f0809010e070909050708030c2116060b030c04092a03141b0a06050a0309150e0106030b 71
    0x8102c4520000c007268000ca0f45951310598020b00300701a001d04032007040070390180400c841403502c22401c40035013145401c664520b00d0701c00010f400b01150035102945446070240303612440034164120b00300900c913501c080180c0580750382c00c7e0140c4140034010454900901c00382d4003d500520300441c03131a244c101402500d01c501c0eaa01d55411030f040005101013074000a19554403016447c044a6644d80c1825840c0188410032202189014030100003034040f00c02d420032584213009008ad9001c82e543c588d1441d542c4d2007254005013854001c1904000000e00c90740343d01e0003203c081c0101902c1d224115841c03c0307101c0c0c1030706000c4a04980d500441c420710304040045108a2405813804c00c00c1c0c4e0065144d05420591004620800c80b8003040f03500c500c04145a5032000456102031420b40d10078030a09038544615860300c101200c02d030346801a2407a46448014282100e03115240c652a10042900440c0500700e021819594003640ba8103120030900203209a820090900c0c0000039003501b580f40514150030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 571922589 1250 571921339 571921349
    0x5070e100f0e360d0203090406140d03030e101131180930050310090b030703140f060c0405030c09092a0f10050a0e03150406090309 58
    0xe100003000201103d8100064602030b0f040580c030004800000142458129900100f0140c0940c08550503002d030008081d05101c8821a004d000894488130781200368290304114980c090ba10303800c0c03134011902a0f8822901b01190805880d0040f064481c030205989414503240364040c40041d41004440c0c813508000d0b507921200d270211a42d00740182c00160b502c003590154140501012070340561521300d62b88015140f9a00030807048a088603580048030200e0303503007440c1030392021140300c0c002094822812603100e0700312407190180150030302000d1402422600300070303a09403103800300100219541407d000012520707100204070b0700955450045c01c0520107014074000c1c0000303000500031540c01140024003c802500c0c01c100c10b0741d4001406240038403404070f02500c503c01c00320380480120510280f010321a0700b660100030800f00f0606220b4240d0000040100190080c407005007954820740b10540b9019006040710b0701590310755052040d8000940d02100c802d540c800030b0804058104c1c410340010302c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 571923839 1250 571922589 571922609
    0x110910020111192303060901080f0a14010915020309011512030c1a04050102030f060303180909030705010e010e01050106020f0d18080f010515060903070b0705070e100f 74
    0x101030007005002c00d00840d600045044408401d05250718450070341050b00007988a980c035440c41a10078454141e078001c1c0ca600303000f11200380002c9104240080c031410011072080c01000c2034019620380400d007040c81c1c94814619520385041102042c015441c44030042a5542c0040e070324108550b9190071140f14459426400c00020010400000718035000034060707801d800e040c000340505141a49000c1824242c050241405009020900c0015400f40d8804c81c080d250040080e02e90108046d620302510300c8844c0c0511b0901e0034611207040030f265031034114800504036130070401c0c2c5540701c1d400e44542841055482e036407403801c4104441d0034052035004110600240c080c0c241c0d8520f400e40c03a107801c000380794180b080480a0f046081c200442807801407442600b6a5128502104124003901d410760700b0552441040b65512420b00c0c10000301d4803a4000100141403961070301503081e0706500301480079141c60045140004502c500700303060910554440e00d02d01c0c0c0150811409031030245e110780000c2201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 571925089 1250 571923839 571923851
    0x50105010e03030d050c0f0a110712022d2d0f06040b090307051002010c2a0b040609020405070c05160b12060d08040b1b0a0b01051201020702041109100201 68
    0x140e1008030403181c000300c0500010545d65121403010707407a03100f4441c441a42120001c1c035500ca0962061a0318014281036094900e005e50b681c00180c0000340003000a5400b080440c191081c96030400840c1920883c440049440c450500000a41181c1081404d49444443e002515107041d10f100000441c500304580410340449013001255407809280a034003074041001407100078070b517410802c1030000c0400401400891581c0b141c020301900900c907000c0c01044851010641f040921a10b4103c020440200300c82822000d03180c04000d01030140003036070304664410030500561114040d0034032400301340d150840d00703001c90b15080c1e00d011654404014982841ca0040c480080b00c801102e5440c10200112242c640701d440020301c3c08010040300030301d480c0d070004d8001040003490004c0c1070360240104c040040f0f10400d40e05030752508451080240391084240040c070162400810801d010061040014248510383d4085002c4074910800b16242e400086000d51315442e00040e12418880b0600c000d0100c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 571926339 1250 571925089 571925117
    0xe011b091d250908122101080d0e0103020d05090c01090b0325022a010210060e01050d0c030c1d0702010e071a2a0c090106050703051305091905010501 66
    0x51003850910b00024540e9030341c48401c0052154604001416121080c0d41107002d118014a0140d07000039400b607000d443d00000c0843c00d00b0300358030355812111150064021409607400c1182c0403402501c80d030741415030a004040c001c41580c440c45203da0581e000401c2440410000034042d00d0480d440b00481c000100704020030410301940c1d042c0c40c4880078030104100c0c050403000764280400104400c580010b0071070114040071082107462a83d03102078090780c0503105400c0303c00c0e058841e00d0007207548a101d900e0040159041c00c03000c0c0317070255010b0410b01600b251030707548810400c074080d4045919415038410a0b84000301c019100750700524103000800080c07041d14100794584c40700f84240c0075200721111200303010498010448130f00d86018485000c0c40c801042020108401071140001c80d40701d8040b0540c81d5040c0918100c4c1070341c016031650360501070165800c0303a40380d004290002c030002c0008000034041e11401a00c03030098913050140351521102540d100201e8905a114504002010f100100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 571927589 1250 571926339 571926361
    0xc0f0706021207241b1d1005030f150a0305070302100c1211011d07180c0923040c030902090604061809021c05030c0105010b0a0f030e011b091d 63
    0x2111416100210f0384c1850102c04010042070b07615060a81680340003080c0501d6517201058000a001c01603015080194510034401901018070b800e101140e010004100c56890341081c81e91f00c03a00040158050014083c00b047c103400c0c86506c00c440d00d5110500500440c6414003541180014a01d00403140c00499102e811002e10810341c0070080c022801642e00700984207411666074050121800100d044100c1041a9100441c1c42078291000009801150240050080680c9614181d6402e0110b608242c1c1c1c9400c2032158400d02d0b00301c1403461000c50b8440d1600d001d0245040d26584001403050464014004c54004c020809072040d031602c9003e10190708410100c4403841c500180000341001c0b1072010400c40322883c12030031500891a207002040000010080200380714a000a224270790384c64049144502807900000b001c03848030305840c004c0320b109610421401071420004242003c801d8094000c007a00b035124a0000b0f1040801800f00510450000c45290846001c02d18585081007041d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 571928839 1250 571927589 571927613
    0xf0a02030c0414040902040e03070303060b09031c020f01050c0c101e0b0d080f0408100204031a0a0207170a03060b0403052e06081605040c02060a020a050c0f0706021207 74
    0x140d80c4180c00c0f0341d2110152a164007001c6100d0f400b5000300300340d100c081555030f6283c0164000b200000e0a05101041030040142a606c680001600804c034903015140502c414441c100e10a42c2107126526440d540d4031424010240101a101c00c1d10f40d40c1c290f1480102e041c000000c0005101ea401c20032080203a1030742440d102c4260400d110002501740c8000d00180307650500c0340d4083c140c0c040104501c8002d580c000001c01c122581d034821a00a1030398501e842c0164040c43c48041d04c800701c800c0304812140c66401d40701d42e001464420040c94244603942c0e000840b0152403500d070354140003003499500d40d030300741c8591405020580300c0a41490300d1a6030701d591341c20345042c400da10615400010082a441030f65000a00303880d840060020715290402c1d141d035016045455154001c0f68140014581800d115030052801142e0107444160b441b041203401035889454031030108041000300c22103074007050040c0145010400040c1101520f00f580082c40c0025036499030321000c60420081c8001010042a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 571930089 1250 571928839 571928849
    0xd2304030e041d06161103040b0715091209060203040f0504020a14030406021e12070c050f011e150501050703230a0c0b16020a0803060a0312080f0a02030c04 69
    0x5204507121100031030050401c0100d5080850b07280c0c402000b400070003282c03081c4280b80f00510004419003905040790140f8003000d20005581007004240546440b1600a040f01c500030210811050280c030810807c8410b50041511403000c5a0082042e19034030070203050092140344011800c00c1d041102055040b406886103d100c3c90b8001802d019107800340003c0b0600141c488041c9482c0d25240c100b04000e9441013032601c1103d418100456484402c10040d240051a16010840c40355103c04e010344101a41e400240da81d480758141c404030580c024012280640700034120500d009421076014811fa62036196a036074104115001400380d660311205884000c1c1d014503000c41100306d4003503c83e440303000400680c6982c000021b02409807a811201d030b01c1d00e051086004200e2952507071000c0285460092241006030800c1000c4004583c3c1c0c14059034001c0802401112242e55a5803030b420210b183c25045000b1030800400c224480c01c204000701e6014210400641c5180b5104005c51190f21890041d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 571931339 1250 571930089 571930097
    0x10b0309070e24130501030804181a010f031d0307060e070621060e0a06060e03070602060705180a080a230a020409110907090807140f060705120d020d230403 69
    0x40c14444e40d60855854000c16103080100700a5840e410604480c1c2d1050040043c00044e040d03048401a48600c204004151001e039404040b12045004441c180d10350b085000c209034561a24016954400d1400032030080c2c21002503a450300f03180317010700503102c040000d02055080725604200b100e41004d000211440c95109024000090007840d0b801004250840c40001458008020740045654000400c0e0340725a1900c0c003210343d03008101640c038107107805144016003042c0007046d8014041c0d00a00808010142008450301e118808544059199030050169600c00310100b030600038442e03d056001c50f4009505c8080c00380030101c4e80d5a82c581860000c0c0126075420340b581c00d21012007440c40c950100281054842d040c001401052801d450049113803600035401c1c001041003c0d00f038090304a4802070074000030402107008100c81c0d0f40025001f684c4c507001d01d040380000818000010017001400c010010388802210264908841064021441203120710348006145100d102c10b0380c1c0d1007941494 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 571932589 1250 571931339 571931401
    0x218010c151d0d080f0f100e0c04030204450320010c09060206092a030a05030f04030c09020306010c140c0d050f01050a090f08070f0b010b0309070e 65
    0xd50440c42c008501d4603990b94007034200c2044405522181140c010350074064048056164010744418401d402c0e91444014200001d04014070300c00d0320203641d88540880c1090741440ea4a030041819656942c1c18080c0308041c0d014102c1104109a040403480d10040300030000d0341120340fa000401004011001d804d00905510140c0201b04800740880503811410080c844465425000b900d5a0214001c100c054054000001c040b04000980340341c220141c4c560b00340040752829118a01c40c1c01500000783c2501940b00703c00e01040f400c000400540e4070840389c8965031032440c104442c0410041d009440140d00400c2801034980c0d014940d060010340104c00c29100c020240c6e02c1510b4034100d5401d860300580c8100424061040200e540700300301000c0c0000b40003130350314100180304a801584d00185129a104406e2001c150164090b1030740c28407070305c01070343c40040031740714034414030401d91068048042c00020811019030a0101e00002d003802812031042d800c020035590159000c1e1042c100914070740403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 571933839 1250 571932589 571932611
    0xa0b0103082208210a0c030804020312030106080a0e06131b030606120b0a090201050708070804050a15111b131b08010305070b03060901030305090607150218010c15 72
    0x12030220818403003401c2d051007541c3d4924078141c958480c0c1e444c16925800880810342c0034008107046900714500c503130741c0700032081c040d5406941031400030340141c2c0c052042c0c10700c2051004254008601074902a1504078551500780d03240d2041d2040d100444038941c1085041c4809846c40c20b40d14210140d005080b00ca1100b16000c4031b0362500500d41c00604440d0078000c000403080000c99080e043c80c0d000303459100255568082680569005034002400141708102020105000c0340c05050b5052084e008035261070340d41c00011f0301c65107158102c102e826103a072013089401e9401c50342c90b59807080528090300c0c0082040c20324808038841c01e4400d40c02002154070300202c000706070303221500419400d0900e4071850104040148840306c01d01040398541f01f9070708042902c07500349043e2842104000c3c910090340e82543d50032110398000d611040e403c1101441071704001360009040242c089190180141c40300c05546030749100c0021901003c3c18400300e00da194011034403143c0f20100d002e207500d8002c55105004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 571935089 1250 571933839 571933867
    0x106081902010c02030604060b1801121b12030f030c02011515090902120129030601180302280902090a03110307031a0a050c030f0f060312070308010e090a0b010308 72
    0x3d6000070741c140200000c00c02000700c45da22a5291850a03600e1101101c04801e107074002040138000d0001500c0010810302c0000c0d19140c4038000100088500d00c043d90362035507500c0d81601ca40008038042003441c501b69034560340c144500c1c408a1101d00c0207111404030610050384200040c0512000c0008034540c0e600030500480b1218014007048900710340d118040e880350b00c10400300b07004441c01d2000c4048a880200300281c2921400e844105529240da2240c0c0c00549402541100120b5100103400e000405681e886404c9060324404084807080c0e4200e080d00a14241156000700400e1403040c82001e000707441c5c010706841542da102c144544030b00c0038000042c0c030700703001603100410718558200008a4141014070765409070b50490420b0145440d5030151600703900040710020103600a46001800464082c007403d5006140039040e42d0244a0750a0781424642c0840c03406d40c0460074a000421503c4d07a0032410540c840c0c403c0002d0007085419903588044410188000380c01980041145990700102d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 571936339 1250 571935089 571935107
    0xf0611070f0314041a250302060a02090f0a0b07030f1d010804051203160306050f0609040216082110080304230a2304050610110a0206040e0117010608190201 69
    0x20725095402004d844910110740e84041000c51410000300020402c2075081806896484c7d8140c024166a698080380340000390003105d81d1562080c44903084c3c20f0035441c4c02444c900900f43c04c20f01280d4410050070003410f403100341d40ca114104481c1100302802003400b18500140d0000929000c0c000d9122030074118a4101c2c0c6102a4060610010902600c0e401d2510398221400403a201400969959030070001e8820035640040e0300078104000d12002440d140d4024110303a09041110064502e2a0315002425004249122410024010310000d8010150401640850103400d214001802c101602d0b03142e02071880303004c21040d0030900c46450459410880e045c1154064502c40c002030b035503000e56000b2052141c40e17400f0140c20007402e912070308090040c50700c2185c1c06408072440c0c58005004580c911440d08588108e4007544000d100181d40344001040141407641c3c01055a5042c03196103e0403146030403030916181c0c0740c02c1e010400c0000c04102110300300244078856030f900181e400140c0f80804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 571937589 1250 571936339 571936349
    0x1b1c1b12050406090806010f0b091305010906140f21150a050106030c030b0d021504120f020102120a0e091b120a2f03040602070507030f0611070f031404 67
    0x40410300c1100e0981c44006041120120342d5404a115a510b00b2181c41c0d900c2800b031500496441e100600000c40c20400806a2000c01b8081c04008006403410300100e030802e0308064202034540f0380c100700c4580c4e1030411585150702111590b4500740010b0014400d007503a0715880c1040c1e0000304c0381c0c004204081c88440309080c0184050041c92501d9100d000082a0900400002c03905d080e92100c0c95510a21a0041c064000703008401d021030382d82c08016040741c0703002d10054151070400010405544160146004070f11803144c6003d01e44403031002a040c80c0000356240748a44080c000340c402d82e90f001117000150700c41500c24081e95111240510348500b4000d080720421800058040d80300e41c020b154540c41a1241981000700c5010055504051807450114910710502600c02d214000c68050095801c01d11488005180c40025030350b440c240301c3d0552007940c038404e5682202052001c24010100242a0912500d24103001603035080c4040503440c01c082c003080041c0510076480710030002102c010786 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 571938839 1250 571937589 571937603
    0x3120901020712030506041b1b2103090c0602030f0301090b0f0d03020a11150d33180b060d05070215130c0e041106070302070315021b1c1b 61
    0x9000f2200640030b0841620858001c40c600748000d40c04080071800802c80c15941d685440c45150101b03440c0320740101c00c55083d1010a80720102e0a00c400302545801c41804842d100864005014204007503604e900d0b61000341903400c204040d5003c220080c0489040d03d444080018515882e100410000e621041c1c41c071b504010a500040d0a258001a015205a100c1d0104400105099061046030441d03101c2c0c0c405580c40a011407000468250842c1000748000002c0320714410510352482c598050601c079101d42140000c0c020710104000707142503554200d010300280171848203500420340c6d520411f400c605116503140c010450052013404001001a0511201405400e1048a200840349504421107489403111800101007041e40701d01c078412030304420300e43c1800403820180040d951120303c7c110111b0140c042c000c0300180000304020290410040010b845240084814480480e034005c10f21142c1c0c007195590f204c0707001d0f081030111041420325005210742050340907400d1120031090020504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 571940089 1250 571938839 571938863
    0x8100f05150f0d06031110080a181b0f06030204080319020c0a0902030a0c030e030306040504020604030c060f0806011d1023030f10060e061c0c0809160602031209010207 74
    0x151105070490382c10f036070241b008400d10700004800c00942910a5516401055400300003039003010003036002c401d04000174141068040360554521300380c0c0411944a035091045100305202d200c01003000400904058102189440d04008485690303020b040c010450a05a1850440c4614400d001c0c1110f080e10140100c0c5030f09480d8545200070b0b402c1181e101b4280ba1409c40c000f1151403082c01001000b14203400690300c1d64945105110250a00800a98210404010020000d203c480d0944001c040564441c0b04055420200808044001c0e080c10704004902c8200c240281c445401001101d6044500507405002c01c00d003901c1904400c03214038504c4480754400e0290703200f5040158491401243c1d656000d5560301e400554042076030081c1130008072050b903000818100200102094080400c044c80103d42c54072450003601c038804055000903000506200720085c08008501800301581d442005581c10164001e50701d000f080130f04d03106034601c4004100c400d4001e5044411040c3c000d440301d104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 571941339 1250 571940089 571940107
    0x27090203090f010e1b0f0402090d0308040c0b030c2208010c0c26190c150b0108090d050901030218032406030109020f09090f061608100f05150f 63
    0xc684060480182ca035003071070f8442181e0071001c11103c070320308041e0003070b0443c0c80c4001050200450070800301c0ba4110340e080003081956611802e100f80d102e480790751242a6440d142c907100c0c1010400b0340c080c0c0c84131201441884114900013081da06403251078032070074480b08210308040c1d41c80c200980c82003026510b410316203200503038080381d2840b5040c080d200d0703641d810101c2600702c404081c411107000d00f0080f052211585c04144104614140c000b1072400020f070701e00e284c03030700c1d0814440e820f0748041342aa6459803400950b08541c00b2640602d074803019101d09a044100585103118076480d0b0350405600003007040d02c0c044044a0300081407809411510680d07101000040c10380050103035a1002506070f0002070140c5014012102881d50181c480354140341c207403060060f18000038003403002d6030149814010310302104000392441054010070444007a500d021002d040403a002d4500d2000d56aa00c6003480a8012007001400700e4505481c40301c01d40c501d42d001e18030030b8000c10114041d441400100258 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 571942446 1107 571941339 571941343
    0x150e06132303091e0102100b030606011107030f03030b09010b0403020f0d14160611010525090320150313020906040b0307030f0318062709020309 64
    0x20f05088001c0c000440c1030000b0400484400d001192240c0b096904004400100114081c00c0140340aa000481d885007402080300d418408071207101d45190f141044020000c2da0480c40040e40d0302c105240c0100a066050f1500748510400c100103d101075a0200b220100d0f98000c0c4241010b4401d90b05210141000c0202903c90001c081c240e6400c0d1030060000c0141241400000ba107828240100580100040d030104e004e5a8980000c020b00401e1104080450700b06203029401c00481f0f000044407005107a410080c004c8800b505400c8030080d82d46002103170000c045903028a0110143d140ea2540d0204944406240c01c14400354409030405200306500b058000c1d00c045800000c540200f0300c0d01c0b11035030044440c0c0c0440c00010f024543e2240c14103090703548243c40b0124440c58070f4401086d1780b0011501c4445000c03e10039060401100d4402a002010903000942d00c034986100c80603 = true := by decide +kernel

theorem cover : BRFrame.Cov 571762589 571942446 := by
  have h0 := BRFrame.cov_init 571762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 571762589 ≤ n) (h2 : n < 571942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
