-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3709
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:27:08.008276+00:00
-- url     : https://prove2.me/submissions/5ae58c6b-a3d8-4cbf-94f5-40f689578b52

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 666906474 ≤ n < 667086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 666907724 1250 666906474 666906491
    0x9030f0215120708100501140d231b0a300c0c051608030703030c0210020f0a110607050d11040302100807020d05130323100b030115030b180c0a09 64
    0x1000307404c19410880baa518104043c0c14140040c0400b00d1002020205a50005103204109042e5014600c40c4c0d90000c900c04841c05121081c2035030b070700c0607503104645034444090703244a120410112074003291580c41d1003500380242118200030f030b01c0c40f80308000703100a041c000b0214540e4074400d4050062081c1c8590690b204141417483c40c0074906060078100e426a22401e00c02040e00000b61070840d589841d0118408500400c03c03030070103005042100a0310f0011620f407101304407070005010849016651130800340a0030100340e54513002910743d040401c00810402c80590318541201e450502484a55031400344d40754081111502201d002000060300034040c0003505605200c6001004140d280c4141440d100204406003400a40f00080a8248148044c0c0c03801c5042c590064960300710034195084804001d100c180030301444412248070354a00300d114000300341c1034403544066075001601110140d8030521411050071907008954014803d1012065040e40d8042c0020064060990007150281 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 666908974 1250 666907724 666907727
    0x90204090509060c070b090307120f1701050f1c17030f07020708030a030b030f0a050d090806010b0405090405280b06093c010e0f01080d09030f02151207 67
    0x1100905000c0d01c80d08014107200c190710800c429501c070b442c1c202e041207985072140003500d8a0b61180100040065180d040480cac4129002001410200c1740c9440e900c01840070241e80d0101e200c424082c590341302c450311402d0740081c10034506030320340040d002d03d074492070101c0d903226a2000b0207182d06406803806d002007009500400c10349900d811220742c0c001080041c0c1820542c60300c9002e4003442d41d04040d624007081449580070056481900403520982e9208440d07400c00549130901034405030301160b40c10381c00140c07809002800d42d0481d007040036010701f080d00304020000000b80c080c009680505ca19070b40b440307030030ba04030810401d48914045012000340c524600180303440c0300200031034171a41440d02003095111100c250881d600064103200d030845080322400c40d8140343c7c41a0402220b08941e0000304882c861990701c1c901a41e01c1040c420310980e680e07552076585154504a12001800e2000c08000040f6202400480c0ca48020b00c40000c4c5514010024041d0304141a04441307240103009100005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 666910224 1250 666908974 666908981
    0xe04020d0e07080c0916120908030a09060b0f06042d080c010f1403060904050106081009050115050a0303030209060f0a0e0117091f091208010815070905210709020409 73
    0x1300f100740c6130f0f80c03550318000b00340d5000c1c0780d039062820017031143c010405110507641d980510401a8003040c1d042e128205006440d004200d030f608210f030b0441c40e0031501480f13854a10590050702320001c003840e00d05070500c685080d00d42408001c0014002130320f50150010700500a9040150001c04024141020131100041204c0070040101d03061104541038481003a030703031108480e48243c050f5503178000d40d103d070b291084c010801684620558010580003200707455158210302e80c21406800248041e141e45505e0078098181445015408490194100002030003a00070300003880b002801282040004c416104840c0c1c0413109004c006400b240c00300c041582c0000110300070b0785d00849049040e00d030500b44555603041300c5003901400144c0700d08245c00f442d4542c21802d020b035800580030095040b1058040d168000a001c0c0c9207090045580c6a003540d102c1d55002d600c079000a41c5d46001c400d140c6003d000c40c4600030a941c0f20401e0b4440d810b00c0510780308000c04001090741590050380c49103000800e0007103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 666911474 1250 666910224 666910243
    0x80c060a06060813240e0f0d0c2009010611010e06040309120f170c0d0c110d02010c0b1906050d05120f0c0f100e010203060109060e04020d0e0708 64
    0x50520704241803200b55031150000381c0c0115814a00c46001c851414065000c1c031030419440850702070045000c0b52110304d9001000d9090f031701c800700c42880d0107007058591160030a5110740b0005040a8010780480c03050078004c108e4441d82032011421b8041100070541094003604043c002c6981c959100007800c009100708220851080301620250600343d0707000f40042da040c4290180920744041ca0800e000700c921800070055440b00d050310b000401074aa200c000d40200c003440c40e16010316018065014040d001c11402c0717680c0f00c4030783e0600030403010410004440e00c0c14240c5c100101094007900080c0070010040c01209a800e9140115045100e20300607603585820203401101c1300f10f11000001c1000030304019032000d002496032201d0401c0e2038200140030302c2102c511a0300c201c0d00305225181c0081803100491031030751010302c9070300c1c501c01c080780c281d01c007d5440b240080c85507070040000380d00c1646c04460004c07000300094a010328250400d010765041400054464201440411030b014040090402 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 666912724 1250 666911474 666911491
    0x1305042f090c03070e13060e06030a08040911210103050c03030406020a06021612090806010b040b09011413080c0901052e050405040c020303190204080d0c14060103080c06 75
    0x9150306001191180704050030804101c0c401201044d10b9030300420a846515001501264072243c4810258014251a20070705149500c1e41c000b20f220b909001c11000b40b0250010400e503d014034000d40c45001b030005100807105800d041c85a00e0b070919800800c01c0303802c00106000529941541881810304c80004102c41c400e0703108000c1003048513004120003d4180d002000161241ca072450b418401c05200c02d0000c055003804100c200c0400d81041420f0241d90305102140d1a0360303200c00c180c95a0b0301c190300a140f50382030180070a0a40350b00c641c40f08072503181103000341428409058040c0020758015040344c800758000d401c00c1c42c120b003000c1100900510381201d000c020014840c1302c40c018803170391240051404405a1504000c203024204540080201030410881090a240c2c02512070300261100c0c4270b150842c0601c032200308a18001c0c0c4056914800180c640c0036a5100180c8208003900c1045a9014642c0c1c500300c00003005010700d40c000c60292528541e14800c1c841c4043c28014014101030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 666913974 1250 666912724 666912803
    0x60717120a09151a09090f060403050418050103020607080c07030b0a02070b09060c0a1407020a0e061c0b060d0c0302040f020702100c0f1101050d2a2c130504 69
    0x2504049600940c41821320941c1e100c09903480b007078802814529099252030481c41890700b031100f0160700c84000c108480504c00410000410080000309076a000c0c4006940702400380245c0000c113801c0401048080304000031100d00507501c0c0e81d01e902a2408840d00780607260701140b1017090000050b42301703a001e2901800781a482c0ba090803207040c28000c000300d0200b040b600d00e500d110340070f450707104a44825030002c0c00038102da9500d21481c03d040c44100e075114050144482144420006403600300708660340407079030840c4c0343d0b21602070201c90741e1008001d03180001d100b0070001c0940c4440c41612003a050603034002d666030b420f90040c01a05204044482c2c1044031541c1540007290703400d20b0b03e035186075200c145043c071010444012101d5004510103405981d152681034003030300340020305000501807401928410703000c06c4030040e500c1044070b501c0305200e0f810600440d21f440c61118062118544018212b000c68048210180c2c111041180c0850b81150400744a00c55940d00000030100032146d0030805 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 666915224 1250 666913974 666913991
    0x30f0b06030105090c0c0f0102070c1d071d0103060b12090706140d1d030d0501061808100906150b0a0e04020720010e0d08190509060717120a0915 64
    0x18a0340d0401001031000b21703004101002820400c2c0701b55880c4c02440341c029500d524080c00c100072031800c02c6c4584002c50546210201d44004841180f40c0f2604698494910060040341071810744030400c0c0d2124101a0340301d0010404400c0341c400780c05400626449a0090b18241d0021860216150007110900c4603514181100040704800c035056108104d0000c500d1600326040078525400c4031b2440b081501000c20704c3c2040860903800a81220100e680700c10100810242140000b03100e401503c0f490340041c0705c05442d007801754001c072186620410780062200a1029031035141c0c1102d4005c0140040300080c4911010b034803050213921401d0484085140011a98500c2d6800320303802182030807841e02882400f19030307018028072981c035840036080c0c2c7c450340d0051a2a11880d84440e1903e165a5540c44001c00698451010398800113405041da91070000251500d62030031141c400c1460f083c500070418a44042c0800c030b07106000b484108000b2815000616041ca4a004413605149501d454040705 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 666916474 1250 666915224 666915229
    0x10203070203070308090d080f091509060412050709020f0d060915030b07180b09091006091806031502030a180213020f040308040e06130902060d0509100c030f0b06030105 75
    0xc10440f51700c2502560348949030404035941701148040500406004078a420490075504010300280c030003191900d0442808052001d031502410b0401504006c007840148800d0310202a0202c1060150040701c42e41c550340c01c14203050f03900c40403203a007a54034045006001d000c014052403000c1c00311090140080b04071b4400d08840e1400510010349010032a40c0800c101d10701658030075001101c2d1111003030075aa05d031184841140c0c40440428000c8005100280c0c1e20408e005a002c1515150354402c0d010f1443d00702d1484100800c07106103590310340d8444d0004000b079080e600341c0222203614540540c980ca844030b265421503080d403136120b40d460215100b0300e00581da070301c2c000301c15003208010060315801c0007403003458140595003000780403034000100170900130800c196140c41a4030444070b00c0c2103810740d09a640154ac440e620029009081444241580300e12608411f5101c49102c088502e810070007602d0805a83c101180f07880487d1341c034015500300d10740034007031148021010b40f9007501e5540750101 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 666917724 1250 666916474 666916483
    0xc011106060105030403120e10060f1a0909060310051e0624160204050405070e011d0c090402070b100f0b130306021810030b1f050a03050402211506010203070203 71
    0x400704a070750801000340410b560302008c034540c410000c03031b04000d424011042c010b200d00e024121461581d841f000520300702783c120241403955114002801c00c0800c4c0c00340042c0300300107003171503606014001e000c060000c1c8500c47c1a203d180716007101e500300d4074985e2000c228814040c00c00342c000d07802000e08010450030701c5a80410602440703a81030340d502010034030301c041000c41c410007507100f41420240018040000b4280d015542403082c501d9280e40e03218150342400c07441c0800101c034030140b80c00007040740c0c0c0000064090301e00f01800141c50005d0641d035034418640e04840c1c0700c0c415003a44000340000903554044a0103840489485490801c1c24414440c4420103031000030892030300000d100407107803907020541e000d030700c40540010050040c40c10054094a900313010700d8000c0303060f00d003015040308041d20001d03484503060300c45500e051a000c1048019281c010700030703600551060f540c602003e81141d45014011140310140100c0150801a40c0e819a80548100d0440d8402d110080c0581c3d808034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 666918974 1250 666917724 666917731
    0x60e040c120e150a0b13091e14030403110411090913110409060509060c090f090405010e01060b0d0f0204030b06190e011707050306010302030705010507140607120506030a030e0d020d050f0c01110606010503 90
    0xb10b08c0f0403480540c07400007640c500c90b454984041c00045400820011203013003051842d24100c0b014030500d0035040048000340900c0c81801d9028100c0000304070265084082d070000f15000d010020b4071102404042001d54001d4181242d80301d80c0c0701c0400c00c0c40c0000b4000c00f0781006002c40034030310b46007240e000106a01c01d100c0f01c140c4580c40d00c1011a041160075071010300c1441c0090024030030a640e60201d28015042601040d04440c20034242c10000c5006200711006c3da5031001c40083d1a444140c28001e9007a80302c0d00d0350100c94448000031070301c180040c0c80f0354000d24031101e0000d40c041e4a0002241004182e42c44079019a00c80001800103a03070101c0c50b402a04c00030b00c3d2180e120030f11414013440300c001000c0c0000f51030181205004d0307501d51240d40382da0f81700c81d03060080c00a612400240340c2e50780030301400603000030140d150000040c41c0400c0038105982c0001d00c41c01d0340601e280c5030300781020910240e008840c2d000b8100d121403560405620308900c100d2030080e00451800c1c2c4006001484000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 666920224 1250 666918974 666919013
    0x5010c0806132313020307240e01030f05010b041e0509040206070206041d0f071706010e06090a18110304030c0821070306060e040c120e150a0b1309 65
    0x11228070483c0d40d0300d1003042c03000c07030b007822540300d039500b08188060082848680103a002c2e01580a0204034110f100c040c0908403601615480b540c250200c03011111004070441507030415448422100240d5980d002c0c247c0a0460345940710341d181d02c1e00ba000e4540315040c0b00407440e445a0745408004540d200b5100302c2e40150147e60440d5240460301c0059801d12443c0c020038000308900e02c2503041228103000c254460142c2180c1414503444614081d580d4144480c41101c0f0b01e00064001101ca52107034100030241040a8201801d050484000940d23004103504804580003c0c00c00b8410481d07e1401011030442c1070b00840e07451814503860043c1041031828000d0b100040c0020880c0302010310016020110084042c0c0400c01d04142200a010304041d110700e000040c4900044102443d00b407141014540094541d003140000300c5401c00040c003107071052407001d070050316107100d0790840a00760a4881c1010203000aa03d62200040000c8510022900840b0300c0c500707840c003000500c000c00d4403020103454 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 666921474 1250 666920224 666920231
    0xe07020a0506271c080618060112111b0c0a080304060c0c26010501140a060311220e0901023612071d0f160905060406090305010c080613 60
    0x48101d1078100b801d29220441e0f511800300b0a8419400000003043c8456080d60b400505407100e0f01007011403200001a400000b038a84041501507000b1005040040301140700400c1e24000d0b640340c0350082e0030030201141c640000211a05034135806100c01c82c424402161510805d50601e950719a0b28043d902841007440502a002001e200c00710805100415650030f024420044107100410750b9822142407440c15800c1c00004030b02c03035075001c0842d014a140901107401e071500c1c100080b005000041c0306189980d40c100600c02c185d405610790681c844542c034403402a0315251640009001800801181c010391042c00140c3c016486103011602d0794202540403140d4103c020150880f1524503c4001e0f4403550780c140c061040000840c101c41200d21815546051061000e1080ca18174011502904240c0e004d60024050f00744415002010305424a4400b45e92a00d03a03021610f84d0380b0a801c250f01040000004104002e4240130310003106c03005107050f543c81e00b0480080f48026011070860318030b03180c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 666922724 1250 666921474 666921511
    0xb0609070306080a0f11040605060f0d021201060e09010605030606030403050a2601170304050d0206070c0e04031707020118020411160609020406080a05061f030503130e07020a0506 79
    0x420b411031400342500f0310590b004452a460880e0058003800380c111404030b521402e2505502d414403a001c207c480c040c09040c40c01c05040b1005249912181c003614803107609000030310414610011441c040c10243d00d4080e16841c082d0100007403d94141d106a042000c01c00420800d80c071500e055a4000b545802c0564036100d221070309075850b00d00c11003070394900300d10a82001d00054000f0b02f4076041f502044501b00116a520076459280c0c031032405026000140c80100b80c0040c01e0100040005074010341c2a0b4007015256180c0c0d40400805079001c1d40040d00c1000d042d01c042000601d070741d03003000e01800204042e4803901010307c00e084041350080c2c0300d2540d41d58117003107036103640702203586000e546076075032580300b84034038000004001d684000c1e07028600c1c0c1407012030807280005980e20003e410500619450b901c000745024400c0101c8541c40c8925100b80c0c0000c0000da080010708018201100002c2031345003031000c4204000c10061070a8110361129900f100440c0c00401c000e0b130414851103240100d8603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 666923974 1250 666922724 666922727
    0x3020d140d0524040c0207121e0312180515041425270506010504051302030601020c030d0c171902070806060409020a3302070315090b060907 62
    0x300307034140000506010410600400e41c110300c1601900c0c400c101042d030b40c2900b091104030380042400342c015074800700341400041134140f100308500d403292504041040d1203104600c40c0f19400d40303049010586400000f42c003084940100c14580c50401050320741c0d421243c4805560710345a0413004203003070310f580218080c0450340c507500441c20030312030031601c0941c1400c441c51184e13407100d503030a82d05428143d0081341d0304028664084125112040001b503071a40202200300405024041c581480010800054551a80e440204400416540051302da182c12800681400426441c0354407903009040305041442c0c1184803074004907000f1082c5025216030b16440c1e110342c8510b80c02003003c03190b084403002c4031603800503d6078152040c400076500603468101c180425554aa4402503000580c0e4070140003a1800300d081c5044440e51030031800011102c41601140b4038400e105000060708030340c0084c01485a01c0072500c0c94004c06c440c0c20003240d016501e45454040010b0300461040c402d800103e40c456 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 666925224 1250 666923974 666923977
    0x11030712140106230f0703110a020405190509010c0f051e0325020a02010c030c02010318080a021e0601050d051e03040f05030f0a030302030a1103100305150403020d14 73
    0x4005918a15419615860003074500c4007907149a21041110400c130580ba5151042070b2102821420022800d04101c0e60303040d039110050307141c00e20701440f8844071800035a440d07000d00da004000381f48089102d00d940381c0b4420f0980d1002401c5400d907038101840710a00380d6000354001c8407140b052030300c5a222040385941c44c130111200c0d20301918421740802802a4443e00e011740c50b04402200310001907403c0110801c0e40c0b5103000079806804a907500c0844800f2a020321107103880203105150000b5080f125140624203420724007001d03980c9040c080f4651144c10703010040c0541c0c0c0ca030300d040001c81c2c0c1121156681d0b80d40105010301809580b1903890034040000400c500c501403c1c100102c00c4000b55000318031581d0350031612415504144141d40001d503418046014401070020001a21911842e0b81f4154060342c00038100003101c03643c0b800d40c041a00b00460166025840d22280c20480500d9400d02a01c0e10980d00806026a8640c000388400241c0004406941c0101c50401030000c040960294006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 666926474 1250 666925224 666925241
    0x1403150619180225080304081308030d0b010e010318060f11030c1222060e0c0301020706150e01050901210c030f021305011409060d050706090303090911030712 70
    0x190039581001d102600ea1500505250264025095024a560f2140302543c07544100083c2001008001040102300c2c1d050040c95003803180c1c002016030640d12510645164406089650240c1d61012091181c1d80d00c04801c00c04144246814005035000c250181d020029003100204002d0b41c0303080b901072803c0b0076040764500303164842c000d603100d14050342100d40720b9018000703260f11054030b40d0009424800d0800130005030b000c04821480b0800d0980d69080040c01074480f01d03a1644140003407000166000d00042c80704500c905408280c0e41030140194012403502e410041d4425a10b10040c40a40c03106402c103811511032a1926000c0c9200065069141c1607044001d0016484180084144003078412080c04d10b1f0300c04c5c0c0f843c01c6115501e043e01400c541081c010b8401c014080640041c0390b00d0400202a001718004080442c1c00c5500e6503813614081c8503503c8200840c0401900300185a000141e0034024984928280701c0c0fa0010852040f03203100042c1410300340008211910201a01603016050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 666927724 1250 666926474 666926489
    0x70f020d0b150306072703050303130b06040b2d0603040c050906030f0c01300c080108010b0f0d1b0303051e160b040f0b101403150619 59
    0x94000d441d05107a8100c060445040841c80219000000d540c200040e40300d200d80180d0391003130a0114004d00b0b403416004090300012541c1410700021001c100b0600c01103001b003056950307102c000804d5103489408040c000384941d10861510300003071155220302c00ca502c1e590120414641800340310803001c0980a100b2600e043d000385003c0304001c10005042a43c1040e50304c00c5600304000d03070316030080694034034503c013190354190007511029400b03500400b0384a2102c2c50050399580800303101542500c5076510031717180c000c9003502c904900544cd6086001e0902519040e0024045101c135140400c0c0c9580104289901070142c0c0c103030308000d1140c0b60074800c54400d848007459103078a80c1ca0030000c1068008880b60780c00302c8900b2490310003111800c400c0f20040c00103c95070030002d03030054079004502030005000b40e503092803c04040700065110350130b05204d001c1c11101d04c400030341000601d0b54891009000f890082c1c2c0071800720307081070050a00d12940500d08a822401c18580d1f40c24120001241d5480310742c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 666928974 1250 666927724 666927739
    0xa110a060b040e0d090905132103050702030423010507081306080705070c09020c030f160c05060c10050907050d05010f0f06180e0a0b09030c0105010905010515070f02 73
    0x40030014180c2207000580c004540502c009900e000080c0d495601000000c07020440e0002c040141084c0794100660105101c82d0501040c02d00d0741b00c2c200c000095179640107011000e011200042e682600c107003030304902c0c00c2c8000c501f880d09207030b109042c55450510064190170034002c9081580e219100711906681d1200d14a5110042503d0010301802030b4003a11011641903000241d01e0b42c40303a810b81c0d107000d81000700c042d2201e1030102010020b41c0801c280c442d00380810001501602c2d07100e002862600d0350b011800401b6422410010400c591076000288180410000c245135076038001036405030006402c00008154076039141880c41e00071580d00960300403c95507100014050190301035020309003444810322840201c05440802c03110180034840a00615006500114003164011690f03085141d00f00c0d01200606d88a08120403421078489045a00000304140c10300c40078041d0301c1c01808501e0052115505040000e1042c0d160400360428007500441c5200030b1104800109603465000362010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 666930224 1250 666928974 666928993
    0x18070f03031e030c09092c0d1b0b160c050d02010212060411031f030f0f060b0108011a0f1b0303091e060403110a0b070201020a0f08040c0b0a11 63
    0x9000c1c82a0380030034403000280d01c100d00c5002e50190013059201c1100f0f0381c914642030f0a10003050000d21082c0045001201904900d0000946d4001503001c1c495085c0028a00c040c405540180405516041750041a1000909000241c090103455400a2045564500920b00c00c00e08030782c16803210101820f948595425221000e8047d402041c01d8071003c40c5010099032001c043c4425102d6400070300100352800c20001d1080800da607046a43c0110800c10b0010307055072500c5071040c443e01c0c142c099070410200c26001042140500c98500d2000d000e0030030004540c54400280c1d00b0564868045000f00800540c40000c0310900b411528040044120f1100000994041a41d00e0f003048404002d02d1042c00203811a01615290020002d0340450052503d43d40355941240d0014400c0d2507400300e44100c906101c001404440340e44d02c180c00c107500040c8c07580100440180b002101a4070b10060000304414003001c500d0f042d08030400c0d00c0101c2040e03603a66155000449825400d2640300201d8004c1c0070742c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 666931474 1250 666930224 666930227
    0x1807110d09050301060b03010803073206060f0f1003020912010906060302010807080c0a05070c150f1b05120901022b0206010b0f0a030b120109030305040c060504030b18070f0303 78
    0xc00782c54064008111035911004070004905c001e0094103a69031062100d50700058400014100168400b802d14041d01d07001d501c80c0d03042c01c02140885010380c110500700700352070802c0701301d880780d1100c01c4444090a040010100c0c1040c1e1900c00124201500024a6550303600c1c1d644a10311000c0740c4500800c40d280560030880c0041600b0f0108074001440311002c10f07034162051200c240109050140145023500130b11041e6020ba114030750132240c0142d02180010b50405412001c5032860158444900d0221a5140100081400d405002000071080c03050f10200e80c00141511080758075440d490342d1543c66000503442c10508869102450420150310541d5002e010b0a5409003010703902182d5040e625084002c05601a032016201d1890301800400c60b01c600c6900b04000c0950094002400807214600c41381c01c3d608900d50680110340c842d810b100802c5030b62240003004000ca0710303003141060f0840d500c0e0706c45142e0242024207840604088001c00d044180f002cbc80c014510b030901c420342613681c1c2c0350 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 666932724 1250 666931474 666931487
    0x150d02091b12090607020105040803131104020c010e0729071121010e030306010c1b0806090c0f120705150d05072106030b160201020d0207060608070609051807110d 72
    0x8114200c2c0c0540b0010561446c01400703064041e40d0b21401e12401c41e5034000c200c82c00284030230b070107440540704511004071a45403480140080c0940324000b08000c1c03a070040b440d00e40384c0940d2000e0401c91000415070f07010144842e541c3c6003030b40382d018902e540f1203080c20450750507103070f8000c0d003940601e84007004c0c1120203004501894110102000f441200c10241d51240c0300d0001b118258042842100c21200044808001d00351500403101d412a1280d10341c0c08961500c0d8081301e68054a62040503403110354684410444540007045070746920b4060f204030b5a036140c0703401e0310030f003401111108103100c0b00d03201d9a410340b0108580818100458605000010181800d032505e0540008610490030f5141d4802d008040540703800143c040e000f515002d82c903100c400c42d002c075400d0442d542403003c0c1e0281c000034001058618080c1401161450a00781290f041142662003001480b0b00d13001c0c104019150444030310800000003000100e25035031101c040d205c0c1c40400c0407808140c05900740903e403407030b080030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 666933974 1250 666932724 666932731
    0x30e03130b04181509090203190b1803041d09030f0f09090105060c06010608070c05060c031e01120312110a08040506070f171003050a03090e150d02091b12 68
    0x10300407000f40380315031840422078482c09000c00c8000494203007417064094a0300080d002600c00780480d014841c191a2003801140303010b504845402d405014410078007612088442008800d8014510b0325180140850090403086c10b072000c08000c1400003546120300f40705039008a800310303c00310354500e0700504501c003990181090b00d11464818001042605015042c1e40a0442e4400240141c0c3d007081c2043d180500c004145d8401c0224605c00300000038420701c00e45011758401746c5071a8490501c1d1144072007a0401081d0b003142c20500744010014240641c80e8410402d816003002c5080000c20703c86040030b804421201390002c200000d40501c501d9001c1c100320300c03540c022002d0b6910f6440c0d40d6000c070381c0412103035140e10008000d400c13492440100043c165800400e407103c182d07062541c82e41d0b41814010b50505c1174003c1081010300300f144951a15a0b40d03808090449072400c0354001000088140c145260041e0081c4040800200c0e18082c0344600400700703141e8046940c80e58070403010f040f20f5103000c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 666935224 1250 666933974 666933989
    0x20102030a05131515080d0507110f010914010c1406090708010b0d020f0a09140910090804060f0e090109020a091401090509131a06010e030d050a030e03130b04 70
    0x30000b42d2080e00c620100c00c0f0456104180b40340c00510070340c0c504050001064010900803829800251645041041514007034183e100c0b95101d04071030910100c031313001540b0b69034080d11148402800f1030382d01c0320400b4246c030458020403482001440040380c0d1205004801800102028003d5000d0340000030200c1c4a00411b6049800c02602c4052540c01d0754810350001e03812080c280b0190f4010f140602c1c0004101402a01e44a003c59035003a04500f518203604001c8070200c510760900492440034020310b881a0301a860134881860307942d907494070170b00c01e40c86003c040000140b4a410402d208403051500103074002c2480c052035031164928402136000d030304da00c8041220341c0c1000034202c030303120340700c0e0b424a4058441c0105c00d4541420700842d644010100010031440c17504d020300107601c440e010300c01011000503c8401d45842000500f801c4dc808680c24840d41c400c0c030b91901507540c410100e0710950030624001c941440c035516101e1a501543c44081260344580f5004504100d030300c0083c10032074106 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 666936474 1250 666935224 666935231
    0x907110102040914130b060f040906090b06190f090902180709080123012907080405040501060c020915120709020a08011e05010507020d080313140c09012c0403020102030a 75
    0x45c1d41c480e08114034040d000400307544050000882a2a142c21280f40010010348003140b25241a51100c04840f0062800c44140084c202840420b05001e030001e1401d07002d01561018241c1401d01131019030a01e8032951030314030740364441c610854a03501e1124400030900c1d8500300c8a400c00c080040c10840d0140034401441d882c0c10040c6005650307074400c000d42c6066048100310b5a0342041403c1d070403079030002c1443e0040881d5024070484035a42c0c2c03008020a500403211951140c0c204000c00058030011fa00850800007900c1c442070160746d83c170203800d420400641e0311003074010401c2701284003035854038841051400340103400180d00030a5001080d41e0510303940c035800c3c81d03a202c0c0018440c0203960082d88003021400502400f441d4062801004480d0008002580b140386c81e40d0fa0b02c0043d4002c0b038085003103c072800c071f6120801042c40c041c01074040c001805060781005c55070224006620500c10502d02186041d200342080000c1d6814007200c0801603180c0d00300c1d00d064240a0b020398425596808018613 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 666937724 1250 666936474 666936481
    0x7060501061202160b090a1401050403030b0402030103081b0c1305090c030106061202030406020405120c0109090c170c1e0c0601050d020105041401020c060d09110a0807050907110102040914 83
    0x182c6200300c800a503480d00036149500880c0e19880030102c00202914050312510110001080700d480c08a00301c10803800c00401c3c80c3c40d007843c004041e03a1503440014001e0740140014000103040c10b0550b0900c0313480300101040c041103000c4162400d40021034042e000603401d840701c0b1200e11903402c810311070005c1008580040e40c1ca40d090508030b480340c3c41a00005680707624080e445040d00d40085400a0107041d01504080c0c46400045000d41c286001c106950b000e08404200380d40c001e44407c0080c1303803070041001913000c00c0101a0a4907204102500714030b84540008071403c0219050f241002c240500d08525002c80c100d8045156204d221202a1441084000070311841c02103000541640d06a441e076040900d09060515072515460b42c840c10f40c0114044d1040f6602c845010f80303010307925881d0100300400303c0d040020b012030a1819642c007400da0b810f030600010100060b00d00403250282c03116401591880b00c21512896101fa281c10b942d4000a00028001420782140600c500903901d114483d48 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 666938974 1250 666937724 666937757
    0x110408010204060305250804081e2d0d0e12040b0403150b03030f0a020f1015122d0c0b0a0e04021303021e03030309010606020f0f0604021c02060706050106 68
    0x220b1103800115a030002810071b4500c0340303d4449107800502c150701050401151300004045d614140300890403014020441e91582280c0440040c403504c1c08000b071100301000f2400016803885808600c1c3d00f07013501c03055901e594200800c501d01001c04988145a1200c2d16100d2240311a48948016200b40f0f030700c0d4200d41861802032040c0c0c20f22a42c0100210b2810042c11284015504918503c1065025540d0070346030182062003007030401071500400042141c0500c9544031001c403650085a9101d10380c1b24664001b602d0748070803a007580208070200011150441c2550300c00222400000c021440d0200d00052400c00302c4042e11400c0a10380b200c1d0810001e8005001c2240100c0d00a1801160590b10070400342c00c1c01c504041020080304c203484034218002c00442d00c1c40d441903490741c40d5695240300401060b81d05000e0010803c00c3d2402800048107084e01c2146e8400c8082c0003c0c2c0f1403018490092080c0c0b000d81554813200b40e001d04006e80701d211900b0442c2c001c040910070b50010445400d0580c1580 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 666940224 1250 666938974 666939001
    0x50c070c060504080a1b05060a020c03010606030905030f1b120a090902070b04020907090b0a0e0307060f0210020d06120807060c051c0917070b041406040305031603110408010204060305 81
    0x124042c40c001d00a0136850b40324a041d02c00280e40d101d040840c6d1400121346a110341c802000c481031039400420701400e52501385030844180b580140c08141c41c244030100001d402000b200d0001c08642c032000d0326401c1e480390250200c1420142d003040c070301c104550321080340c00e490701502c03840c00705880308070840d030b910140003043e8821079600400280700c0c031000400514020b607000340c01640b1450070540154070340d0000301155200c0c1081d030001c04c4054112614524040021174050030f03903450660201c0300d07408006550303091380c00c0d4411000c68012407100300f41b856550106c002026018880c440b011141c2c180603407207a01000043c1c1b903e42c1005413410703a0324041d50844120a0114181107800d40d080c2510000802800c5421a80c002c21521580381004218000e400100d0003121503a0043c00c080c0340810a0004503110f003181c81c0c10010030040800d0300081aa07912140d080c82954413008054003c0b0018a840a8440c40d8220041004281030704154090410b842d05502d040044e61103040581e03101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 666941474 1250 666940224 666940229
    0x10f0b04050a091e0f0e0c030d0509100c150507020c011416030504050d11280e09150a0b010f020304050d02041113122904110d06050c070c060504 64
    0x4121030150402c40081184d0042d001c1c600544c442c080c101d014400d00400756180c6a90010856480b14201050020148600e400b04482240100101200d164000d0264012540003520a944506602058038001d1100f43c40b11036101e003006011440003100e020080ca0b0989924005216002040e413180d4011031003451514085141c0741d00303200135050001d200260f00030301202000300078400020036403100e40301805200d10880c1d15a80b4424010248041c002d00584c0c04005008203c81030159566801000c100f65184480c1c40b48003945c8201c00795151040a11502800a4071201002091030f80c541c046049064240da4030b00e100005034000320b80e68003482c0100c607440910341a00c4401840c00703621681159142026143c14000c01e040102146041640f05050f0484182000c50400c83c1104034820b10809180c6001c60803003035002c24030000d8100400c02440300d030b02c0031392540381655a00f0105041652100c000d000b1860050078034220350700601c004850325010300002298450003503054405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 666942724 1250 666941474 666941479
    0x2030a1a090105060d0f0203010b0c0f0a200d020d0f060b0102030427060b0a09080c012c0f280501020109080a03050c120c090117010f050621010e010f0b0405 69
    0x8a6400d00c0c040089a50190070240c0c101707540c414600c01d0900082c00650b00800d0b0941c0b1302910b0f082140001410520515807000c056000b44440000003054035514520510402701110651103075400440c00c803501081011303500000045a00b000c02c12901240d1401521540050082c903004400583e41d030301440c0102108007030014070120b000340e402e04070680c103d468100c0c08150507542c4c0c05039045551000b400390b0002010114140306225003004901d040940a02c3c003150182ea20100ca151700401d15401014140c1c1c08003240c640c90340d9600900300d68244014842817007400a02904e072400f8106140d044d0342d00000400006083d801845020089038100740d031b0328681205000100d0007020014400c420a450900040d91410001c0031828450104610b00a17542c004400002d0510400400001d9030114a8401030040c0700099807039004030750b800e071605521100e6440b1000c2c08008000e50720004a41c0010002a009445150403070407039030500d040c2519541c40c1c05448950340b2a6004854 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 666943974 1250 666942724 666942739
    0x15010e030c06250f0b0606030106050706021305060f0405010207081c0809160b0a1e090b0a05090306090c1201050103050606280b0c01110304110103021608070602030a1a 74
    0x21050b040c107200a1803040d80d60405075810007032555107906100c0001c032060301c070444480030040421808607800754000780300300d40d594150740c07403c0382c0205144161a40104000e4010a207400e00c40d00d0b10b83c001016200c020103035a151031084c880481c1e40d4100e481424014446c1180010341d110000c21507482c030924030100011081c510b55016510701d440a494043c1c0c511504c8a100a280780c50358420010344110b03041036a840448010051001c4001103444101680035450341c5145d44d040341c070300d4040b151001e4040b0344071010118243c485014040496406000340010002c403041e004c5110250b810044907079041030002e5100040c200c031030900000f05079038081e401084141c603105810307010b105541d03007901f16640210040004000314581c42411308541c046103d04c0705840a010300d0344110640c100141c1903140540b6180030518038581491b0515500242d4501c001080d08041500d094221541d0b950350011071170030340d00a51045801c002807601d0010440341c0701e6240007903021803050042408 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 666945224 1250 666943974 666943993
    0xa0e010311070605040302030f0313030e180411060c1f14010312050d0906020711030f21160b0c0706050f1e0907120803060a150906050c010f1415010e03 67
    0x1004060185c8240d080d44002e012804000340d000700194802ea03805a64098040c1c490300c0e000d09a10703004000031f80b01c4d0b0b81100314101ca09101e41700e4035601a4021440030743d80400c01000c1002d9108a050b00a41c81c0a07005680040c50061000030712240d03c0c400f020081d280311500b00134081c0740700303000092055091106480a1f680304601400c2003841d841e000241101c1705944d03400890303100c620203d030440c050446038100782c6070910500c204040c0e1080500b80c02070324035090b1501c02d50500b039089a10b01d400320340f2040a0b0100020809000d50180c42100c0d5030038500098501504840380454410b0305001c005200460100c0e801802071540303c00443c0040c02040d461300c12142c000340400c10501c04c0e500d0014022044200103a0141d000e00300066807800c3c400148259070510741c000c03c1c00706d0301040d100e0b40708981c030540300c4003225032a18105440c0d42d00160603d0141a00e9032500740b40c85d003420000e002014640c00264020034802e4005400001280c006461044181985076455000320880b03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 666946474 1250 666945224 666945233
    0x141e100207060b0405011d0603160504110c0d1d0d0b061e100e0310060e01030b1b04090c03140105011209060209120105222f03070b0a0e01031107 64
    0x1501d082071140c400418031442d9100410308656090b404070701c00381000442000741704e21141c4141d0304088150064201c0425000080c42c0c401084d00c5000d006580e00d44510340040316200030343e040d4811b50b500780c40820400d424010805c2401c81c2815071428848009415186040340c00b10742c00c0b59004420035040c0c1d59400400851020300c02d10b07141c40380c0c940c4000000035520407019400741e84507a20781c6608110701000b4549420304101d188011076103410300c11b0000211072803800d41140d03071040070b800051b540c0c20b0070104240c080c1d0356030316070019000c64040f0f802401034101c5032400c185640c04100341c0714041d108220448d030030302c10310740401d0664000849401464100252040c017400000d0b2606202a000c2500201c0340354848010365510001c1c4004904544144d1284107020074411005480580316050b40300307007000c030341202d40e14a540149104d081e840d8042203008401002d40d6000ca545120480d040c0e0312400c0010005806180c0350f1781a98081c0c4a22101c0b01d00340405a418186581d54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 666947724 1250 666946474 666946477
    0x20d0207060206270a06052205070b1605100b090a09150c0c3206090d0c230c040f02120408070204090804090f060b0f0d0504140307141e1002 62
    0x1504d0311610003e004001034840f0070001c54000714400c0340001421b01d006040380c00e1060a1036a8101e03c075010b0030290002c50130004004080d40c8601d80c542c0c1e610000141e00c001000341c9481c00030214003908808a50756070203580400410342c020341e0301040540d0741d00d42d00c0c0201d1383d0580009103440070340451040201115880407009d86080d04024224440c2c1d900c1d424035458800c2c04640740c0c20000440d6000e10844014802d00c0c441070f900090041e81450465282c5450f00d00c10000100070401d8040300c14840396030783d60f00c1066003645a0880721202641407588a00503d0003142c081c60030040c81a1840301c1c10720032200b1160f4050f10401c00c03500e0b00c2c0c0c1d9801496101072416a84035440d001c000000c28403840041008155003a00092160349401300041503400030f034005140c1040a00503d1811541881100d004151a0600150030381d88d502c0c046034004107a50341c3c1c01c6c2d140304c049814420003031445a440c529003c540101c030540c0c2c0d090540b80c01080350710340802201e90004100248030001e50340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 666948974 1250 666947724 666947761
    0xc02030a0c08041d0a0c0905100e04140106080403020c0a1412100e07080c0a060507150608030d0207050f06090304030209041a0a0902011e0806060c03190807020d0207060206 76
    0x81541c50f050340c6441241904543c01c0e00c1480800304102440081c2c1c1040c0311310702000181d400d180c003006141000003011469051501c8050140b44c002104840c1c0d2654010302075603506190103c603c0d61180b070020210038007120200c001d0710072403580c3c02007443c1000c885e100b240c4a24482d40d104441c0c4030b05000a000802100700520b109040c594220b880190140803040413130500100941c900d000c0c0311904c2c0c154186d81483c01556a403006100c0e0300d600c0822174080c190010480c14481003942e880c00010500d50340301c001c003800b0101d01c00c0e4546403550000e1003030341e00800403a840c0083e01c48095844510a468a0b88207602c10801080181071064483d5800b42c00b6034540c8847e40900b402d038114491013100c0240d12565902c660408544c1c2000c10302200304040701c0c400102105581000d00000000382c41e2a01c030300743c00300b4600c000c1c01e030030000c40d002181d01146005641d0740300341020705028025500000540915903000b41c040e80300003180c104031146030340281070342c0c0c460760000d1105a8500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 666950224 1250 666948974 666948983
    0xd02100c060e0609210f0904021c11041a090603160210060f03030906050a0c060f0e0a0c0807060215060423250e01050f030601050426100c02030a0c 65
    0x42400400c0390070240800c51095658030040c20344066900d164802e0114140050704c1c8041d001d0021b1860030783c040d406d0340d1030450f0682d0016a200c0f4000c0c0d01000210054481c400c4050400d400c1040b84035464000d402220070304406214a104441c10403011801101c0b042c5821400600c005051b20f1301c80001c030300c2e00440a0069900d101e0400c14004180d1714550840c85000c0843c14082040580c800f01c8980100708610f8004e00b0206100401440d0050b0650040e01b9030362a549403241c06000c1d0b40c4200080e07030400044502c10407642c80c0040844586100c0c0c0d41060007101000907034280080b45055581c1c40003035844a0715540d44003000f00404040030008105001c00403629891103004400034000c603442c01c0c609101c2540c8000040d1400c4407824010201320310306942d09116600030055884151800c2000d644a60311040102c3e4140916484208038a010010081e40041d191000c609206112419124050140810501a00c40401101005034030030004020b01a220720710584041d8800d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 666951474 1250 666950224 666950231
    0x806010f02100b0613030b0103021f020618070807061805090108060c0d0b0a03030806041a1c06021e0a080a0b090c0703020106090e01021215030601261506030c0d02100c06 75
    0x1080410905c4180c20844802412030014000d40c50000120104440d00d03000140c0f690100c00300003500d030407019090245508030744e400134240d40018404140074110f8003048800e4569a42c000424444c012819165241115103001c650b0f414181015816181c040c4001c0c0080d46481c4c0c42188e06902450a103001c49070346820f840a281e440c41d90060046000b90350760070090600c241080100c44100402010345818500c152a00c1d03107038070745422a613070010145801d040000d4100712019100e00070850112650048050701c461150320701030700c0005010380d00c5040940c2d51100034000c40f00500d07482d90b4003158600018030302c50008001041404c1c828400410401d40e922542d00540b400e010291081ea50007107501609041c01c60b1100707504c650790f1440c003030101c00c48001081d01c0d0700741801018041120300c50101440304802845a101c0e1100c10112600003c49541c203050140c81a6191446030140700450384040ca4103080c0151050f030002c000011562004506403051440780c07504550164a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 666952724 1250 666951474 666951487
    0x10e030f0d0b03100b120616180f030f0c060f09030210030f05251e0f110624040203040309090c030f060b090a230d020a150e010806010f02100b06 64
    0x1801e0004c0c0c0d1300c2c006580c0303020462030820010400d003174001ea0380f541156400b940c100f20b001d80002c1701c03a281040d070350709003c81c441c00380c500903503a401c1c1c0c43d070001c80881100c5030303001041100314920904240d00031511005d441d91104000c55418680d00c40c02c00002e01191420b0002d4988801604a10001c5017000500c02c2540c000b494140c5104a84400e500c0581140b100340908130f599004440074110701e00b0307440c03002011600304042c9001f10f6000c810001b401c0c00f0f14039060300403e03488400c0e401c414102d98040c0391240402d549009001450320344170302102111f92070307070429000356801075a040d10f5075a081c60a0444d0711000385000c114040426880300c404400c1500075100300301c040e107503001c4170982c5c2d440c0d01d1040c0a0004019401807580341040c54032000d085500d41008500f0320001c407800d5a11010a00008442c522160024141219945618000541c0103c45068040c00a0704c40d2481940c81e04015107e00c200841401e015810221044038111384a80c0b00361500c84005011504051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 666953974 1250 666952724 666952729
    0x152104200d05010e07140f011b060e060412090509040302190303110408151f0312050417030703030c090b07060e0709090c060e0607081206010e280503010e030f0d0b 72
    0x11308100400c201d580140100740410701d402e40c2400d2100c8416519001c41c03c140c00c00080c40101c1041e03182c0148904110100d0800c035481e04907006403031041c2d04031891418070741001401c240091200e1408030303070a00d00001d581d0400c2c003140344c030030f41d0160041c0804c0417420b459981d0841211a0031010036590340c0c501510600d00802400c0070f03040e10030040c42d0f1035603001e044000c030940c007a100c681c407290300101a8441c1b090380d2400c0020350b81d0108000d14840c0c04583c0684440c081d40e0084000641419140380b114000023014000c250b00a550a00001c403080006031065101d070b000320030780d2441c100912000308140390001c0c1078105021044884040d581c000d00402c981800340d0803180701058400400c15540e2101c0c0380c80b0381a1040311218504180c95032041218800c00b2143c11945064200180f9a42e00070107402401c0c1c0400780503c1c4c1c52800003807044144287c0501074a01c0e50340000008602c90905100300301c19803543d003000b18075110611030500901d40000d5a0702c0162502e03510210f0b041d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 666955224 1250 666953974 666953981
    0xa080f03070204050c0414130b06040e06100e13180f03020312090601050f090406140906061302210c0c070801053c07030b152104200d0501 61
    0x2240a2000d15120041e0344108401d0f11406425040040424881030088401882d011948844c04480030410b40d1406d101740000780442156144d80400003190016080e480e000c180d03442420201c3e80c0d18204a40403e0035543e80325510f50958001c1c5a0842022800859601c508151540c92003540d1030035241741c6e1842c40e121000e03901100140c10101e024030640d0700709035480781c11503101c0b0050300701ca60410002c0740c04500aa0941c4d8443d440d020046401d010540e0310a0b1045c1e04802a9540d40d031074005582c550b82c0d4803d4903858000c50059070200046401c510a80c3c080c100107074001400200010b9083c4c031040000343c02d07500c0100c1c0170000340c503801c0c03810003a880040c40600000308283c900501582c5192030500d2040100c20700d01651380d20300c0026000320600480440d0808012500c600c1d4089004284501c3c0c04c1b500806520321406030b202c0782101910a221010385c0709500101c0804094000801c10340d4000e010218102c0b07680d480802d00c48d81c1700300200019100c4d8169101c292940b900b0f5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 666956474 1250 666955224 666955243
    0x403080708070b06100f26130c09020a0504050909070e0a090302010c0c05031207020f0109030513050a1d040503130311030708061504050604020708071b0815070e0a08 73
    0x1240001d00b1002c00201c41d820b00e5110808403003500c034000244001400d00f101c502c0f008020005c55a02c288904006100b11005601c41d0030321160251500720224090244424400d03943c44880000000b1000003c0c000c4a103000419628242817038580001d110911402030075402070384c002c64001003910444445100e00c200742c2e07040701041441c02410302900316804980b28a08000010400c4408550004120381c1640c0e0314400b01140c0c3d03520160704078209145102d41700320380d50820100301e0a0540c07101c003404844d02c2c0c060b81d5050082e0340d4020480d03000e11500c1420032030380010040c0240e6000c0401c0aa0b8000d026500766841c05914000440d6020711a801c2111200b1018840c03a2a5007003c101c10f001401408000f482c950404020444100d82454107052003140c0b04c10000b0701c1d81d02c1341d8041e6824540e005640f1500c4200380d1801c00301032500d4081d03072042313004082d000241e9404001446003104000c030b00848001d444a0004948aa60520040c0d8210074203c00004501c0010401c0c06103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 666957724 1250 666956474 666956483
    0x1050f1602070b1903060513020705011811060706062c0603010b03280609060522080a120e16090b040b030d0e13050a09031b1703090304030807 63
    0x1518603042890300150320401155900719405a1024050414000c08840891844101c000e40e5090210405c5014000316003010703070002c002c030300148501221900500f00a80c41040240608241048000004510740d84050034030410800c02c01c2d82401c010f0020b00c5028000c02010441685841c89103891841c01210761160604901180c1444034203105144d4001400328000d22243c940c07080000e40d981e00d424505544020f940982001080d040d45c0040709495225a0501c4040e200d410007900800c01100d13107240c5e034407032010945450320141c071a920070198403950103414241c608004540c0035041e68441c4449642c2e61081c4500e10070304201201030f00005e4401046010b04107103014090f00d40c001980d9004500702003a81c41c2d9a070380031076415441034240c90714038162510840084c086a4401d8150096945800240700d000603640d0030080c0d411b030280e160100820030050a100c036060303404c0e5002e00034588031880500c1803000b42c1c0085403c540008116800c280d16900c40d900c642d41700840403207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 666958974 1250 666957724 666957751
    0x31d06480409061e091d06040b040201030c020703050304060e061b01050603100b0303040b0f120915010f031a06120106090213150c081c05010b0c1b0d0f020d050105 72
    0x2c0b0031000750140c1005407650440800040b2010a803222540c0198010426803a80b2070314200c9908034911329007060105084102d40180c28a800c00301c7ea040b07810f030340c242e000a040c0313400454201e000240e20703412603500c48010b518151411001311100200c0030340031580400204041c0e8408400c948030105035a403000f00000d418282041058a49081401c00306061420503008032501c0e81d011040e1404c4904400c0c10b10798400d2071002c1036903540724007160351a100c03192509215007a18009420340d400f056001c07001c440c0b41d0f02e0b20304a002001303403880000c3c143c19800b49104018518840c095420600180c8252018541501c000307082d036101e90423200f0307401d0303010909101c0e40d015000800b009220f00d1418000707408000000a10b0040c01510280203030000149032160505805080c00c4c02844ea01400c00c06561101d5412280b6440315040208600c07980c40c054000710124582000c04500c010003a4910000075a1034400c1c045100200385e0380800d203082400c000c17450a009280c80f40780c0342c02006 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 666960224 1250 666958974 666958979
    0x201200114090d0e01031109090a09140d0e0f1018030c17010b04020702011704030c05100b01080f090d0c031403160f0e0306010603020c0a020301060303031d064804 72
    0x7810a111070214170704243c10320395070340301000c1d2580440d030300c84200303440c0741130342d661f844240d4009090340070402040544070008803044140f020820340c828030050350320744204054103410805400030700074485502c0300d0841200c00c0300d00e001d141d802c80000f20b00514050703003aa0365201c1421703160540e8031581040c0070038050320700380b04400c1c403520303401c000200c50071820814140c00080c41111241c0116050194010104051500800c0f410002a501400315400aa072000840000d8540c081c1d4580c04240d0b104041409201e001d04468810500380d070051020800c040c1e4119044030100d4415014042d018101d4544805d5141c0103510400810441da2440c4501d10070040891014400d41800c0100c035900d000250b542c00701c0e049046070210303d000340e19800401034030741c00c01030158030003545036107003240010070180c15030018498103107520300c41c051040b100340c11075480c0e90f030484400280130403034000d02e20102d40300030b4000488541071224103900c2e0783e4000300b0814108000c075440689040403d04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 666961474 1250 666960224 666960227
    0x9010b0406080708030307050a1202040602010f0606080615090409060609061a040308040b0304060b03030307021b030d12021b07081c05040803090f0301020c070905010816030201200114090d 83
    0x944004200c2c20303000b4402d0610b41070980361640005448030041100000d4240d108510501c01440d000300401011036680d0703030703c4030083e00a040000d44255014205040059028080e00502e0300c01c000180c41d105100002d8617030b00c411a800710410550155071858400041210b610441d4090282d10750b001a4050920303941c203000c0c6d440c40c2c007520240c200030070040c40092861002d0320119074038120195140c0c4c03034518119020788030b40b41d255500340c440070080080c203da0004000c0e10080c8008422080760f0110780505403138144031080780c8040b07072800001490f404643e5009054980d84105031074052038031240720504007041d507400514940d010380b0301c8a007003200e60003e000074a540d074141149130603e401441d50b01c0703014464800d0300c034102d6504006101e0f1800e4040342c0c9090401001d41e204942c4401041000380001c2c01004013511a01c5080781c44800700e11201c1003034079016141c0d07008076500340303200407030100c2c02d0800641c0c95500c034843c2c000120525030019007c1c0510501801c104042c8140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 666962724 1250 666961474 666961481
    0xc020d260702030118030c0f031b1208060103020c07060522030305030703050609011d0604111b0709020403020108040b0c07061a010e04090201050d0c030b0d0627152309010b04 77
    0x24909030408030300107a01c000303500f046104024a03880308c800d1843c114075080c00d5409600c3c0b00c101102d0140142d0041d400c12504107442c582c01e0b00c1640b102943d51f00c45200440880c000d01d0300221039a4040030040c040c103070150014081610000c4126843c1002000071009400c0c215401100840c5000c002e200e40c468050007951707131010064440c8000340d8903007450701900c84030046000d102c0c2c4080700040391f02c46d00c5640000d80c0e18500fa40f0565501d001144a2100910100383c00302810b0040304c102060f0300c4514002c59045a030140d40700303601501c4036200c030300041602034511410104104030540004001e405601d2031004420f0701030f01507400b2103002400e240001090305101e90b240c80700010040c3c0e04036040e108480340c400000202100e03007110640003400305c403440303e5000c0400c501d04410420143c2040040001d2144407104940d4000382d02500c094556000410051800d15040004012503200b43d601c800c008401708102050001080ac03c04030a59803010565107401c0c0c841c41c0c40c2005d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 666963974 1250 666962724 666962741
    0xe0303012603030402010809031603090510020303091b030f1b0108060913060b010e031501051002120d091a07030b030f0304142e1814010c020d2607020301 68
    0x8140010705060380c8030315030b140c0c030004100906000b11200170500c00c59081080d10388002800f002810107603407500f0064214070700c51040364460f50345030120f252518804001d585c0a07500200080c14015410000703806101504074086806128080030702060442c00c1141454044c1901c460450030b43c4040001040c01c440107100d01c1c0209071920610480d916145c06030100e01b0b800600005000941c10012603c0c04008211107038944203501100320707401209824a412901c003203420003007882c00007105a071074900342181c61140500900103000000c40c00e0f0854103906116010700c0055858581c2400206003081d14081d0000380d030741c180700c0d0702c42c1400c004400d0151100d20003103040500d001d00380c880080c0048960f80c0685008200542401d1420034950070780315001a500200c1c640d03110004002980414201401c000d0501d40040e5012020111380004003041e9101d18045840e42c003804451005020100c2e442c154841c205405c0a2604810800b82c0030800ca006036503050500415003560040d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 666965224 1250 666963974 666964019
    0x41a0a0515040c1d041d0304050306130507121a071d041104140a03080c0a0323091909060b04170303220f150b1e0108180109060e030301 60
    0x2d1107003102d03134101c203003c0340d07044600c0040e4003040845070200e4068803064843c000e500351442c40782c001503100070000e841521000e5044900c680e0300c00d048041156031503000070300703103802001c0b042c001241d40440792031b041409501101c500507140008011800030803036501c000a2550300e411028145004404d60413140200e500b070040b540da00d02b005003188142d1084003420300c00c01c0c08002c015100c1008550041d50010647c98613401800d005039102c030045001280029000d0090b035028051040c010300c01c407138009040c2d03820b020300307401802000309a040194112407000c03000025010040d002e01c0b00504502803800c0d40766458120354050800060f0130307101080d0001e004002130074502d1140d100300c0b6000c16442c002d0b180000d04009801d01103c075005002d8580603810300f0040340031604900380e00113068400301c03989400140c01d110541801c01c0d0160001e08203001080391404040c0003070308003100050002620007041da8604080f03441c140081401e5810210040262503506150b500c21550803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 666966474 1250 666965224 666965231
    0x23a03020c1801050d0318060c03110a0804030303020a051b0c1201060803090402160b0705040e0f160e19030c0f0602070f030204050c042d080a02090f041a0a051504 72
    0x1a981c00c980c0a00d050080300d01401700605803070281403141030900040c04e2620300085c002c940b100070003480b42a007180141c001c5100540398503100c0500060341325000f50440d0149090a0669800318003951000c001c0760200032061040311042008800b01c0315501c03880d100101a440c0a441c10301405000c225865606645400400c00c0303200000f0046820300e42d0b00300c80047e650349030f00c01130002090900502400110060040000c2c458101d80100141c45100d902a0340716550300c0620442410222a426502800c1003284403205004065a03145c0080080c1488804a02c0403029802c4c0b0110358019901b041c050300040144103803c4100c1005899148080e110341424800014080d02e61840000d000341da60340c00048811104100381d42c0580742d01800154440b0994a6017014003403061180e61100344d049500048078100040c0b20400d40d9030241440b0b074a55500312081ea070244000b0000c0da03445640d00240742c2c480c0d00301900544200c0c20407000081c00c1c2403648880d0341949220715018080d13403a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 666967724 1250 666966474 666966499
    0x150302090c07020a030809010c050f06010f12110d110612040c0e040c030803041b080c090603010b011d040e0319030b010f271823040c03023a03020c 65
    0xc0d03440ca43c2054030741080300c850307607483c1c4400102d89e007100f11400905107004200741480d0465003c909141250f6400c400601d0741364031600d41c0c801c8088a80d500415610511115600340e00b403204045401900448280705502e03020808a100c59009035404050550107000700800c120800360782c1e030007401101005081da40b402d80c2c3c4280c140c0e04240400307090000701100017006c200d01c038003040f243e12021030015510a5035a201c420b40d242d004e4507400d44524000000030308103040521406500341416943c00c0c0c01c11042075180c0764158000b40d403541d00030383c41c1c0002402c031030020001420380380d40c580c3e1081e07107043e012a0300804030760140585038100b00802d40203102ca180d0000d01591594076242d401050035150010346404d41c2595484920f01400007144000c0e0358141d94403100b0440c403c41500c56494072001380449079484111401000c61120300010310160800e810140d00c40105101200624040b072410381a90709542c8440204206002c07581404240d81404108160304094030803418180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 666968974 1250 666967724 666967729
    0x115170303071404050d30020d14040b18090a06080a0201050a110601060807020c03191118040501050403112b12052e06020615060d150302090c0702 65
    0x7101400c0c0008004003451403485004071082140d0040c14020f02d10344038850070b860200c100e11a840da000d50001d03031034141100c0c200d04d2141c40c0407030002c8640c0500a002c0f08000c041d5075200d0000e00c806c94541b1b007840045009402c40c001032104080341d22440380030400003010000108801054400402e0421034200400700c000260240004e48c2400e10a441e41000482100d02c4410b80700702c003105120f884000142e882e08805114090b580310390075a190104c0c14014140ea40e000201e01402400c811442c0c000400c03034000d80c13013807000c02c02880c1601d000000e031902c200150f002c0c0c40560340f50359280c0a0208154202d2010081c0d125000083d00b00b030450111458028882c050038032005075402c42c403a00302d1601c00c1c041c07265415965102008607062200d180c0c0c4074115186003c0b08055160a0140d10980b40010088100d8815500400c9603030b8441c4140403200f000115100c3d042a07040c050b00c6800300c2c00c1e0180c008040e481e2120601c0c0c507031460040150010000e010180182000c116100158 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 666970224 1250 666968974 666968977
    0x160909020316030c030b180303070e0306090c0d150b03030a05091c0807140c0d03020c090f04080f13050d0503030601080f01080c0108040809040509150603070632040801151703 77
    0x140d800070114030381a5210249040c0303445211f00d8031a45800000108446550401e9080104410070f03030442d0380315518009510f84da00500040250b20401c010710030340005000301c10810000c2c102a0300030959407610b5000c80e141d43c02049558000c40c20108040010b8282001584c1035003a441f22038407400c1c202c03920359161920580030040c0402c0d280d2091181310f0802000505100d14018050200313030031040c20000d4444000c001e180344507001500215200f050203008040c007858100074924035101c3c1c0b000c060701240e40240190054103403001c40001c4c16a881503109001c0c0b82c01400595500d24204000401c20751004080c048034003400001408641400201c07140e20190a0030601c02546450400c0d12090080c00e600070360140c00c20041207500c010124568440c3c2c05507044034206038403080300301521b130b402e0380c0a2072000070082c42806210300c0e19135151804031581e02000300b909a140c90300c000c0e802e51046c0c101c80d106a444100c3e4100514103558020028249000c640c484a00398424040d2039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 666971474 1250 666970224 666970229
    0x2010c05120a0e010920040b0906010f230a0306061206080d030e010209090c070c0603020c030d091509030f021204180c05160501060e0a0b01080105060c160909020316030c 75
    0x1d549000b600e6403440254017102d08141c2041e61046001800e68040c43d51000c032410141c0900d0030120310106a042c06002d5a001c1c110584401e011708542c00e02c12100a007404043c00026a680084020308a102c42d000b841000d00b03994020501e50704065016003801d03103040604800524162040051a40c0442c01c18841803461401048282c0300c0041c070360281c01a401c01d140d1014071103042c46103401a9000802c2283e1007290000034094ac0d43d40190120f004103030b1960308542081281400a40244d401300403035a2050070101c006588404000c0107c5105038003c40105070760440390900c13650100060308050200c009564542814401e03015040650002d10100d0303103441e0705001e402d0070701842c15034006104124600100c4207990034003078003130b00082c4980d01007102100017146600c907550041d0030200c08103842e807240e00d0b441c08080c410660322000080c80640074190502d082c03690500e10b64002400104030102c5c04842c00d00400d400c00c0990540c08481d10f804078170410001d04480440b004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 666972724 1250 666971474 666971491
    0xf0305030a020f0309011d0601060503191d0a06061e15020c0d03085e0b252a0c0e0a0b06040b0f0c0c1f02010c0512 51
    0x2201d8980d510880041e004025400704589400f00c100224000154880c41850325004804000300c41d82e12200c44d01c401c000c0c0039440004204000203a003039a00221890800505c0300e800041c0d21a040a4240004504003120951900320201143c04c0c07040c01d0040e98050183d08680001410381500d15003040c0101d0f204103035034194104021010a4020b01c60403407441c070064054112a11286070080003900c04458249040c8001d41e020400c14900c50f206d800700d001312940c00712548104154080f0400c00743e00c00b6900713149000b01215589400d540013101c55500c00c203074100460608480c0c843c00031280044e20704214100c6c101c550350156002801100002001541040600144202ca001e05900400240c03024078184000507c100e420f50090b445a80d851104005035a2440104503103841540b10350501c4a4040c00f0407042000100002d1040d81488003c45000d200f03400017081f00b0f0030100d4411041c00360b0141680f0480f603020301038042d50200c5407500501d0291540010354404602406000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 666973974 1250 666972724 666972727
    0x90506010e01180b04030f0b0109061404090501150f03030305130b06010804110a0f141e060d0207050f0309090711191a0109020406110604050d050919090207060605010c0f0305 77
    0xf0b080320f071030700c0d4450260500c945269680d5840b8188180700900300b45085175600d506800000d80c800c43ca01c9180140c031980822105200c03055010040a08a400016160382d503035126528002110307031451034020700501ca840002e0030300d9800e0143c21590010291540d5207952048080000c4e54a2001c0e50700c00c009003400449600c0d1818201000300740c1e0b04480b904001010b1020a00420340780034201280c1141081850082c00642405122088200ba264407d030803c5111a002d152040c054031190f59541001810319a00d610356514082e41c0c1c1c0c080c3c4005400014142c0700c42d08040d01e21680c40202c0f814904000913052011660325403401c014801100e899140141c20480f400040ca10030040c2680c04115551b151000c050003035109104070f002003a140c140c500324a0f0000b18189110795000030203414280c41524080e6540c0d80078244455100d100d40010784c0540040411820180c00302c0c07800182c64000703501e000001c40340240c0249040c03242c01d000440006020032100508079501d442c005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 666975224 1250 666973974 666973997
    0x30111041502120315150702010c2423060105070b1605070b070906090641030906040314041503110c0f0c0a09020901140a05040f0306090c090506010e01 67
    0x40f4146804020381004002e0300005226035220059505040c1510440700f040d4010191070f052440e40c420048001d0115228508200104100318640940514090403135035291000401e500100c82d00183ca000c0003440ba03038200c06060650000302944941c003802e01078980b038240d850791104035400030010100f500d41000f4080856100d082a507903040d0f0711690010541c00d0181000c1d000709054000d280000d90310801c0059a58415100040c0c02c416040f00c5007000c038803541e068561000d22054500e16101d0800c40d0ba0000f0f00c04c3c4004500c20a808009405113050614008005a400da44490790b604010710060240c940076001c0442c000d6418180050803900404a2005038011640441400d0280500e114001c240128203a05507070b10403101a82104c3d2206082012802080102800a555000351403001080c400003810b0008290800d1401d0654444038030420341003039042183d410340c072099910100002000404043c02c05145c0901c56464407d000902e400c0c000d0100c41d04000059900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 666976474 1250 666975224 666975227
    0x3070818061204060c020c0f0906030312071815080105040203040c0905070e13020301083003011503200f22031b06030902030604080f09040501090c09050301110415 72
    0x4000c2a25000d40030a03181c4594218490b080c401c1110b056030641e0a01ca035070a140e5101040342080c0c1500140388060800521042c4203140b00300030700c400e030140b01c200030580d81507414000700742c8115141d03501c0318a4200b1420101880e65403c0e8003800c80180c90802900c070a607040345c0c842d415120207840068882c3da40d800c014144005a500c2390010300c0c941018003845a1340080c66520004040d00c0600840018020030700403031009200303148641d0000504040300c0b50346800c501d0f01b28841500d075421105856001318080c0d900070380c002c020741110701806007542070309405820108440c4000c902d40b09903890507800700d05d1294508580f107030000080c1e101c3d85050303800081e80341d0703a403940381d4500101d4507890312510070081f1000440190700d0300c1c3c40008003a8440e008689000d40d024001c3d24040c0c840e0342d29801280c00024001c07400500500014a203500c80340301d243e000340420726000c200c0700701c882e00240c442e02c900c2c2c00c00350081c0d0606842c45858283d0000315800c440c21110510381b10301c0c0f641d10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 666977724 1250 666976474 666976507
    0xa03050606090d0b01060e1c0602030403182405031b0a03060b12040303060e1302010518040c091e0e1b070f030e090a23091606030603060b040207020102030708 70
    0x12495020040c03c0b04102071005110b00941030303a100b034461601e032646400410010f0820a00700b202406400406400007074801c0e0051a040ba100b4200b9006100d01e0703002c02c000202c403e810a40c0008a01c044c03c0020040009402c0d0b4042c0b29820000e19500740074128106142c2c6060303440034981d40020362504201c1c42944210000e0498000240c1c440e44058000004004143c5003540020300703003080400d43d01d6059061a000c0c440c0d0b4ad507031412909565005541d5500034a00c004284504a0a00e861071389540c064520840350b90b03a2146409801d00070f2501d500146020f8a10400010078410b018140c0c884104a07002041a503072032828850001d00305a0b1403182c0c000082c20120400490020182c00440000006908171030b2400d07940d440c1c040c480c0c1194014408032664901c00090f4808001c8d604a01540194010080d551a40038221075004001c503aa8070a03c0040c3e65403804006000c002e01ca10040c0300b004440c29441c3c541140c0000350f680c000d174900500004000101d241c840c651441 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 666978974 1250 666977724 666977737
    0x40b0a0207050612060d02010e120f120c030d0f090c06080601030c020303090d05030901200a1d0f0d020d0c080a0b06030c0108060118050301050c04080c040b060414030a05060408040f08070b0a03050606 88
    0x1072007244101d841030103050715240080402807061041203c6695188339800c180e0704007511070030080d4201070481035070501401404c5124100580d582030202c010800400d1804007800c981d89909100e8100754000608407070203d4103d4045400600038070401480201e01d01e90f071840507284c0162240c840c012900e004001c0e010004429202d003668024000c071a42024002548130b13a00d40c101c03c51041c8030040c502c0403d000000ea0320011080c014212441c0c000342c40c0302d02c1400906011000880343c0e0f10782c06018071580041c480b40d8096031610040044005126900103000d6001e001c0e040000c0740085c10402024149905008122661900d402020940000103000041c000c3c4400e082105600300b40742d12078001d80c24180940e880307080c1d4604150181d20f10910019098510b064600a0980c803030100b000358103640341c0610107410f00451000c0003898000c1740203984259646141010303012039080258400b44894221000811a000d04282524031003010390034081340307550f103550008480c0d10408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 666980224 1250 666978974 666978979
    0x210904020c1e0a02190b0405120a0b04050120070206040302010f0c051915050f060609060c070902090f011d090a060312030e0118050703080c070308040b0a0207050612060d02010e 78
    0x14560145102c000100000c00c2c07402a1002d1501140318020002d0214080c00740a0185800f0001000f01e801c04403000103544c00c2202c2500d20010f0180d070b40981608050740c09640580d1202203107500c1c551078003075240001d60b260031315529080595020403100d010300c1c800070b030510540001403181180680d0803503162a07481810748040c80c2c0e00038030801c00044502c40a45401c0c5101c2202d07120070b9403d210715030042d00320074100480d9513a44800c01180f41e0280c14540e40056050003907500050040141c98050030b05c0074000740e111009841072102203130b418010181004110040d441e4a420680307003c03514180700382c400454540d5942901c074080c0095a000520109550600c50003c99141c0c0c02003c0481d0782034001c0c40b04400c11a0390301c40d80e01a0b004050010340080d082080081c3c918030041200892110a58a00d180d03603403100d011682080d82719903110300c1d0008013075802075414440100600303001c0f160903003403c604440511a265009010318007136000c070381da81c0b429a8000c3d0b000d0444c1c0d9030300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 666981474 1250 666980224 666980263
    0x9011a1303080d0f230a020c0709050103051b0d06090609020d080909010e100e190203040f05070b072102010b091608060a0e040b070e0a0303030c02210904020c 70
    0x76454511526407050b603403081d10614040b03034410075031064003420404410580d00400310000c2c929246402c84405840844040c2c0c1c2000703850740c565005d10140c4011b0911a10005043d031542c1842070070001c0444442120985040d420746403640d4035001c83c9101e03608904001102c00003458600b00506c0b01c0c0d40007a42c00b109a01e241e008100ca41401458a00d0701580d0030081a6a58080c55020140568050716441d0808030144803c4007582d03c991703404500e00c0068103211504908032070490380107440c15180503020480c01410312404100c0e0000800801007174074600000c40c0c0722004114440c3c0d100e0411091440b001c660120f100350460103810100400810040c1062800c001c0c0011440340604045808100003c05c81d14000204000f201e0f001d0404030b403695101e135100f00582c1070080c4140d05224440080c01250b4460590320f40c003031442610f0005a80391715440107882c184441025100c100e032543d104014105448046e02d20484c0143c0b000740c2c0b24004c1c001228100144080ba04804122 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 666982724 1250 666981474 666981479
    0x130b03180106090b0112051b090604051804021005090a051c051b040c08011206150b2b0216170f0f0a0e01020f03030402010c17030a050109060807030209011a13 70
    0xb0568030111003100309890306d440000556038001c06855040311030943e641c15040750390140002038002040c6542004102c503160079103c4002418035a040c01d0400768000a03c01004118101380c06401600e54060911508005c0010001000500a0300980b40526201891641380c3c0310a001d41c081c159030b1007800d503610402483c642504a18540043c54811801d1480401890340203540181c140c4e8040d1000c401c2e00d5031941c0311000078001000300008140e2555030f000684010440240c460140b60f1543d81e400d1080c204880d84c041c44540344802c28071481001264100d8406803402c000d025803240f078a02030320010180101c00c50062410b13059880c0c1c00010350310200000341c070041c009040152034820081900800480c0e582c00c9030f603504117099008001040142d030040040b00c056510585242032124281d000c04042031704181c07800f100d440d45510040c015109240200000b5050400041c40103070319540001d00c0040c41072150b00407000d404e1030072003032524440d800c40b0740348200b00604010607039 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 666983974 1250 666982724 666982739
    0x1203200d020d0207060f05120402030f06042f030303061e0d05010b090108010b010804111f05091002160308031306020a0908100204050904023c011202130b03180106 72
    0x1c01100c40302c0c014010b1510100c2e4150068514114401183d030b500c90030a516030b82507040d00c4102800581e410f124100e6250b00c0080104503852003148160116841840542280180020850704a5213058401408140d954030008103032035202d00212008800d4100d00e40c2d581144103800c841854016020301c02503401d04c0030540100720041c03020703921070361980c1ea1186164200c4004600b540d001030380078800304010800c07041138110078002c020700c5e4005440040da6000311001c1196500c0c400b241300880d000b8142d00c1d0490390100c8031030060000c1e000307042911840c021494028000104480000300c041285900c02c1c94254500c1540f16004540d10300c800c0701c2c00f6101000740e2148041a22846031040c503050203a0099604a03003002e402c410054440b51700f049060011501c1d070013542d00428075800c055002c2030750b00380d84410f0714240441100f540b0400050100750303d8284000c00360300411468503d1034140e500802124406071042d501da450314181542201e0508403041207643c01c041d030104142 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 666985224 1250 666983974 666983983
    0x15010c17090328020114090d060e15010b031807050303160b0c0f0f0a0e09010f060201140c0406030b0102070f0801060906080a0308160c0b0f0406151203200d02 70
    0x1080c044084034071148850008910f07910ba45104210f0100c4069998001075006801409802a142500e1403c040400d03011a8136680098030507900d480d01c0b030314040300c8a03105110130500c6d2842840014901e604010740c0304554800070703050b18002410007018040500e41800107901800008050f26030b604e458011070200054006000d81705502e01c800031424030300036207040302c1c403c0f1043c0d001182804600f04180e03206822140e080401e0011045200310960b071440c1c02c0901030804950805115814110001e003110100c140300f2056602ca1001d114010940d030090f90211111813a010030110a4900104c2c20f0030382c2d036441041c240b0244d49021030004410340200065481841c0700708105aa0f82c0b0b14641e4508a180c03000d800306070154081940d0f00700746120003000c0007540c1082410b040305a601c510403040200e40b010003068490007448108034490141c07510f50001000652089420401841c856061a5074002c080c030480c1742041c980441010f81c10040c44100e6030a9440b482d0b4100e4000e0340310f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 666986474 1250 666985224 666985237
    0x1b030b0103060f0e07080d080a0e0109050f0c03010c0507020411040e0a090203161503050a0204080318090703062402011401090b01170106120f0b10090f0807030b15010c17 75
    0x1050601c5007908031136000096080841702c41d0001002c03020440b18094401c003101a01c907480450712209058541e107004d00072808840d105400400249010404080c1000341d0040c070640f099050031940100c00b5071013810303900da864049a00242007125502c40b5417242c4229442080c2c0700d10070f5401c003c038400c3c0d617a0142d50114000d4003544e00c52020998402000d442038000d0b402d8480c1e11205e603001d410710a9210941c03200501100514142c2ca4080032481d43d00905107221044503555000f50751400c00e20710158009410b402c00340403250401c5038017001d40c111500003c0303404644400c15840c2c03503c01d41200441c04000640c40090b1b50b11412070320040c140c4d0b101190b011903001c4120204550b07000d00701c603040740d8a65a0300b000340d883c0d00300000040c10b00c8008180c3c90b1600c4911780150b960b100490020142c0704ca8407140304451808400c403421900a0344070b0000b07074011040c01c10100e42c0841a070703548007900100780c074000f4840c0d90050340d980726084d102812010140720001500101031004000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 666987724 1250 666986474 666986501
    0xf0418031d0603010b0f160203100213170c010807020309190303020105070c0201200a06021306140703090510050c010e0c0f0d02030706052a06160c0506041b030b010306 74
    0x340700c0390074451588803e1241d016000410010700c0044d080b102d015002043c00e00f482400d0a07070154001924082c1e00d40354012000f540003507280d800341842403190b00108030350841c110025100d040d41c00c0d00ea080b0940d5590502c484880040c440c14824001c4604034407004101c40844401d25943c40c04400d4a8001100035600e000046820503004901101c2040da05030b5900310017400d10240c0182011140d66a1002d83c400c0602c104005103140c0040c110300b10300c488606034040d28041c0d00030420440744100000403e0300300508004280d02c1241e101c15a641556240c1101120311411030f102d00c2003900c0c80c061035281400c0b11809200100342080c150404403a100310702c100d0340003081a20b1820850003507060340035a4082001c54000c0015003848006c49011540426010401c0b8020341298100c20002d500b05000700800c4c1c040104c400d0312400001d02e00680e0031000c96031210350740c44000d440680081026a04004294500003606001c2d41e0b01c0b1008800302d507541d14001020b0602c00740c0150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 666988974 1250 666987724 666987767
    0x31305010302132106020309150f010f0e0601050403080a030e010f02091c1e0303090317160c080409140a140c0d0504020a0e0708040203060f06010e0f041803 69
    0x1500e6119000340c1d120520805a4501d21900d81030810070160306014040c00c034402545290b20201c4c5951000d14803a240c8000500028400ca620310186003030010007601407204e03c3c0006011404e0b60820503030a0b91a084001c40898607950700586080c0a036900c0140b09410004a0f03540c100d6254004801d220442402806510b281600c87d0099020f4100c01e9034000c01064045186400020404800107004050030305104c12400b0340c0482c0300340c01500c10760200ea1070301d050b0001c01d0392105c1040c402c041c2d2000541c0b15410300590184409612028a1003000b0040c031040303061141810440300200f404001c00c00c207180001c154143c1c500800c4400c010010f01d400da10401c400b042074145449a241100b22a2a003090450302c80010f107409031059030001001a4040780319600400d07820b0050401e6209e115061805104062508000170940d010100480c0e0500c01566004110f40300788d03a400315001e0710f020322041c0101d40141941c00c5001108212400300e903040c9030304040600781c0240720391000c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 666990224 1250 666988974 666988979
    0x10905011103071209060b06040b0406082229090c0a120503070f03030b0a060c1e03081801141302030d05040b030601120f060801020a120522050715020313 68
    0x7014580021145840811020224031104000580c4480d003544d20030840000d001c640c1c0c1000c55241e40240c0c10510502c003001806005050704198801c2d4080346240b840c1c0724001c140c0e01d2001100d1100380000b041c0d4220a4090f06000c0c440140030041c0c801000d246c04000d14003032650540d40c45128039024044d012a10740401d07050013492405505c650040000c2d032610420741c2e1401070320183e0031000d84c101682c41075040e03040c0c2d03109500031000309403e640c1c5040020190034500c555003031110410010446592424001940181d41c046c0d000c4801c03401e031000e118403000d60f540900710800c45221609080700800181e400081c480d860304038020340844201c01072040007901c95110b2030190754688401400050015803040c0d140829a0311a060049804940c0f81110307016a4116000078805035004641d519200e98028600c8040d030500c00b90910180c1841c800c85410301080000c0e003020b02041c08000400c1c400e0400c20400241000c41c50b956140d03110303040c029207035000348003005555820342400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 666991474 1250 666990224 666990251
    0xc0d120e03030103051b010c081606060509130303020c031308011a03030a080c070212010e0c13090f020d081303050a020405070306050102030910031e050405070503120d050a1d01090501 81
    0xb568140d03a8007400600503c40c9104901448544036541c050403c190141c0d07580000e6101c501400140b0f485508001c2e2034030301881d00d0019030300345801250041c02e8120404c4600d540d00c851907070540717405040c01a5562000350b551401e40c410f2240001c80341c0e28603000011407846c154010221303920003950006014855904140d1240b251085c0000041c4146001ca0300c200154402041894801071802080246004d0303070300d0950345840390078091504102d02c401c0722801c0c802001441c02e089000d04000c0c0c94207507694041d130001e0305d050290254400c3c016400410207a64101d80c481c02c03100311000c030525507a15000b6604c48056a040b40201d05000200c3e806600a0103035000b9100149c000e54149000103080c0104c000d0075466031001c2584404481c28604008002d11300202c45020001c2103600d8503041c503c2ca02011036016a020750b20000c0600c80110034034042c0c9028030140100450315403079071004030010b003130000c521880200440c0403005103807005601050300c20307110348020702545410f80c11 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 666992724 1250 666991474 666991477
    0xc0615030a0201021b0303040f180c020309010f0c0c0302030303180d0e0a06120906020a0f020c06040e012313050708072a14060c040609150507080307050c0d120e03 72
    0x20700a025a001100900e4041400071909400d058064201c03400e1580ea1140b9040c0c1890030380c84030865124030130340794101d8280b41c010030013a00c0243c0019440d001c540c0000a00d10074140d41350000304115035040104112074200403000440d0010201c1c0e480b420311040c14040492141c110700190300c2403069840f149405002c03a10312031540185002403203854141c1c15a400e4014030840070307038241e0f140488000500c05201400740125555100c135400c00d061980a890300c56207200b9103114410500c410040080301060241c1515000510450003060181d082084025020051035000c2031080c1c1d40fa9000034207912031449500b0750781d2034280300d44580000b03441c011800c40d070302c0e4a03c503411a006141d85040c203c6488400e07108042203000041020302c00350900c607059031018076618000600b00070300d40c0c0c40b040e0a000381468101c00401442c4040b40504103205810b001046280c000c00064641c5e07000c0e070195a500032524095a106400402c00248402c072544100e0241038a80030043c45000000070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 666993974 1250 666992724 666992743
    0x30801050913022d033f0d230a0f060e07020705060c0a0203070e060a06020f0c150405130501180614040e01110f030109201615020c061503 61
    0x1416504421100313900702c03a0402c001065956244882126000c0a403000c0103140c5982020305207074840d0745082e9507010904040d1210204d044006210614029901c40c41126919207426200198400b0018a80524a0b501c1c0801c030600348210410084612042e8000b080705480d041004c101d616180d180500c101175058401e8401030f40032003c18480b50400c10000c054100000702142c03480031555002901d008202c0d0050700c480c1d00d521083c0911400d0003481900030f04003e00240482c401c00002050792441c81d15840d1388109104014003000998442c1260003604000e0050031040c4049404003026020070720660340d0314200c0c018001d080c40c0c1a80b00d200140e0345044580c0c0140003000301004060040106828040d5588281d04401103501100400406003495403036034580d898a044c50048454074040a070f1040b09814100d11000c20480c1182d4182000040e00b00c1810a94100303006804101c0f4042c0f0501071000851111401b030008025114040307240381d00101d041a141815210308411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 666995224 1250 666993974 666993979
    0x219050118180b1c080c120702033301080105093007020a0b071a0a1a0d0c090e0a0b06030304050105042318151009170a060903080105091302 62
    0x46108007642c0050b078000e80c0401d00014500102040c4035041d84210300d80b6107100f00c0b420000043c03d03800001c000e0040300c04022a101e401070901c012600800d032555680248140d586080081b0b24114210309074200300d0002050203000e409603120301e4201e0080005a03102000e0b840380751039208490880d00180154120b0440403a82c001100b03500d05d460315080008201da0007208050081984a03c003805800340314001d2646020341008a40143c0c4442c101070280403200f404c00c01d201112110000101060501c00c1e504031f1076001c0e0302e00b4510714031101a04030410303036030821448003000c9200295001c0b05074091146a07100b51159410582d0343c0c0308510603c2e000c03610a02082000c00c04c810369801546281381c01031011546141c001400c02d50031031070705041050120061000c55060800c801e946000252405055007664201c0900b001c0300341c0c41500680340406082910b1440306210008a01d0350040701408000e441e071401500e080001d0050714010300c041000603d80202442440b00c0040c1c02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 666996474 1250 666995224 666995249
    0xf0524070b1501300c0e090c070b010b0c060c0d090203120c0706020106080a030c03020f01020a03090c0e060d080307180f03030212130e0a020702061801031d07170a0219050118 77
    0x65410350405800320040817014441203003030802054684200c664450511f004c070f210f03500c840c0b074074140318000010b030060345049400340141401d1780c800045d230075000702c0c060313401548901d20000e045014285451000790103004406080c102680300c08040c190114050301560510390301d40208908036026031280114541c04a100000800c0c000c000742c3d00303041e001b4811303a41e0002a040015003640d10500032807001039981c1c28200140540c0e00d0410000d061010309038489170034090005405812180e43c050030801002000ca0034690091002d9103140d40028000c0720748036034179648a42650381c1c1e8441a805800781202c0311031845c40b2403003150204600040d14040d0f0500b8140214203004c401000d4200160b03003000880c000d640e0b40b1014165a0050345501c0d1000b0481c0000103003a41c1c0b10402002800840071441d182c003081c0030135070b00281c4090030018502c00e03240351019072510716080c01c0030790402a040c0349001c00700403070032034441030700c0082c0c031000340b502c0003071610400e06410342c4208220300c0304 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 666997724 1250 666996474 666996557
    0x10c02061503010237030605010f1d0a03030e03010b01090308040b0c0309090a020910020120031b0a020d02070503060c0304081c0e160f0524070b1501 66
    0x1003441c0c8108115001400041c1417815258005803002062500403042e140142d424901c01001048008085000ca11b41844035a10b0000080c10007003e0345841400d0101c01d1080000341c0b40b8903410003049134030060030740030f0180e07913401c0250000da00101c09600a508110644505502400110044039404150503140918014182010f5003048100c4162130104000280030360350f603940054040c50000c07400507640e1558108102041403007018220079641844035280036200503000300583c4030781080c80c0c590740e66103000341c05150340740080030510340050110741d6200751640040d143e0441d40c120780894074100c1c5c450042503a41c11f02141c00b03505202c800c20010380007c0d01080070340b002002e400c04c0905200c5c030040e45502076400d0040d40f581c20380e00011081287d0803241d00c805005240c1300c0001881c4609180100d20100ba2410f142c0410700d5003c03046070a1100d1043c200e582003a084400300c102810300144400020403446609070004151101c240c0864210320310840c0c0d105442e04c0405030070320 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 666998974 1250 666997724 666997741
    0x60c1a1303120e070e01080d0f050406050a180f080706170601030e01090c0305010c02070504020702060406080907180b120607081f09050c041a040b070f02041b0e030f010c0206 77
    0x38200b19072101425160100721108840400240b009068030501454456042000c0c561810b01c11403060002c014803c503181041541013070803101580d0007450415900d1f8000c1304245d848014540e4512110070340000700043e0701000b040c040c01a1081032055550b03140c0d680380125540400c11780e02c04542c907404400b2410b298040d03480032288104440c00400e049960303455004000907258026203103651600303034041a182e41880010054802142e086040043c1d0303402203000c0d40183c0c0194020300100b031000c03030100d010800000000700800d411000300002d100c1041c6010704140804a4000c0842d03400c0751b4159200820140d10404056541d24080c2e59110050040080001c0d00c0c41c01200040502265000590060520503502c2840040c2d582e440c0a031604078501c203195003140f130b403207081c08180600c0405108442a40d13402440101c641c28642c0001001400c100d05002c402c2500f501420140c04e8110546448860301242940d403148210344410342070340c5001701c1400c0140c00820001e420708 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 667000224 1250 666998974 666998987
    0x1d030f0304110d030f090503071208030703180c06031404030507060b04021905030f0709180f020412150f0216020411070209040f21080a090f020901060c1a1303 70
    0x35009000710031040079034402044081080c07103400c1c0c4c0083c814207070681889411025030700041030140c00900e000d0389420760009420101a00c02810001c00002048a070343c403031340004e2420032149645000c0303041503291510400c0900d2259001190030101d07107075542825003d00d180300b19050740381c4510340300c110380d1000000e000e4032110700d0380144d00740300b00381d1800703501d4404441c4000140c60381540c034100003a0024006100518460130081c00001c02d12810500c070b40000300c155503540340421018604070364030019014503040140281d20320680720b4107004c03c14034000c940c0303265444200005c00c07190300c10100380d1080e0603203a00c411224050401c018100b07640541030b02d42c0c20300c00080c14841194005a00c070303101035400b552401a556812400e020200c00141ca01180140d042a2521000d54002e42008801042e07104525910110801403000b86042c0c6119107a0080c20394a89603100ca4010340810000e0105513088001c4091411300000d43e8103845015420b40096a0800c2c1d2456404940300c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 667001474 1250 667000224 667000231
    0x6040902071b0f080f070b0a051308030a0815030109020303090118091104050907081006080402030a0609080c10090c150c050708100f0513080310030804080d031d030f03 74
    0x2442d0401911096114102c0e0985018000360412907142c549404486460301086010108103608960b504104103030303a140c2100c4a002030f9041541c1c031400d030b81d4056580408103520062240c00000340a42ca455840506944588404029807250741003aa00781422143c50404c025015801041440104c3d80504803410101c0505d45c1410412925500c44c841504c4a654040071011000b0805100a140030701c1c1885d8840d4091800c058140b4002c6100065645241304500a07c000a0040b80542d241071044140c43d98000c0010710030750310685007103059940001441e050070301034204500819541801900c041750340040001e03021605100c1074800d881c0303950040605001024151600140043c402840140742030400380543c000c12038558010380d19140d1100f6405480c00307080040c0c00d46600d60301c1b10b40c1d81d00315103a107440340d60f801c0c030007450710030075402c09890444c0200c2e0002d0383e500d00181807030355104560340c01d10044104441d400d03c3c41043c0341214400d80c206102c0c0703080025114001d55030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 667002724 1250 667001474 667001483
    0x91501032a090902031c0903120c1b06020c060405011709160b120105091611010b21151e0a020f0703030b040e07080304030f0f170712020c0604090207 66
    0x5210804000703080800c801c952100702210f40b1001c12005510303051040d020010300030740465101085000000b00043d595000040c6140860722262540c00e1007038151810280e44090780c010096481c00c024207900c0c6032403141200511400c00740500500741441690102c42c010384560701e055120304448030306100010407000582c8134601c162080040510001c0000b003400042d105d507192440340c00010304c0ca405800c03a90080d00e820003840481e80091401c0782d441d20441ca00010009401d1b4030a074003501840f8611540b007144000c1c2c6241e90342c500b40c80c02c0d10000408041311103004000b0740403501c00104070b0302d41080c400b1584402c8020a040380060f0f522005000e4010b19001900761241c0450f04004001e6001070b035240c0c000702c0350b0b00701849181d00314a01c8400904070a840c02581603078a02c0795000040c00e00d05a01e500c4410401c20026280c14640d000c20001c4a24502e44001002900a0041500c00311002e40c04400510300118041807a4640604814035040c1803200740c4020394058078048a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 667003974 1250 667002724 667002773
    0x1c0f050a0c2318190807050a05130504030c0c0803040e0f070203070210230301050f030a02030d1d03030307030212070f0207030b0c2701021509032b02030106030b0909150103 76
    0x40d1303440c45a0303c00384c0d0400c0200c02e1103e41c100300304145010142d4200e54020484020280019550814200000c2c0e000920205540e0350351302e0100c0f4840562034006045010103000850042d40100280c02540c10282c001d40079540d90403410030144605840980c0941c1040020700051708100e8104162018181440b401d07044082004002c89000140e143c00720b01c00c0440144410f28081c0f0f56000303810011401800030b8010380d000240c0350340c404134012080c00038200604100100c030070461021648001c0641e5228508028058060344c440d4900760300b220030a0340040c01c000c2c000c07000780800320343c0c0c0d6000782502c40c116600c0b5420140c02034542e09031043c1c1030145901d4420f00400d91440360340645842410105c400c40060f281001d01d840d0754144902d20010400c0703441e40041941c440243c00d110140d1229500d0482c0021501c00120000b0964000000420700e907030581c00c03038102c1c80d20039a40301010b13688001250361108071079401490300801a400400120316062203491215540345100c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 667005224 1250 667003974 667004017
    0x3021b190b090a172a031203150409080c010605060f0a050f070501020711090702210a0c0f03080402090f01050303090d0c080d110f0c010503010b1c0f050a0c23 70
    0x10340685400c1d4020300041c3c1c0442d250801d104202100301c0305d5085800048850070408000003912045045ea805000a20100000307560307100c41c40f600f000d51100544200b000000506040d82c2c9540140040c840b25800c160340080d20781002c0c0100c50344540c90042d001d0a184c1c420f4022125039014100815100d9400c2c440365021403401e00c000c00d403091082c074514007200002c038148010504024800e07015500720038030302800310b43e0100e9a000d40c1540e180c2440d070788000030001516919108040540001d44880c000c40c20107422203030039809540215030b500c17000d5a07643c40c00c2e05090024059550990802e01c040302c0359007800e82907403d109104451400043c4e4660002c80d00d000c41041c10318000544a45a040784002c00b400380400d00f041c0b480240910300c0c4401c0001e0014801031003450844080054401a10918a84c01c1d917038031303801c9035420303c01441c6c050f8981c0c0142c441910900f0740d403840e107000304201a000d001c840714505400503606a2a0303600030741d00140c58114101a032100144030340c00c1e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 667006474 1250 667005224 667005239
    0xe131b05060c011a100909050903130303080a2702010f03110d14060303071e0c0b030a0b10020705030705040e1516081f1a130303021b190b090a 63
    0x2400e02e418010000003040f000078101c041c1c0b008101403006028009001500d80000d500464610540b035007540301184646501450510710b1092107800034403402480f101000700b40d484581d40e40039080e1200140825100b00030307400d21000240d0000700c24003c05010314801540240115045401103060000701c1204e005a5554582c4c800059500d4941da90340c8005030030144c00c4002508108160025030528140e96521600316002d913a031143c6007086042810708010145c0d592a0260610b102d445803a410318207890300c060403460150714403440600040a42540c400a0310310110381000300144801c0b0703d840b0900001340390440b036000180c050080b07950300d0407122480c9603000300280f1101d21114140c1840081c0f81010203044c40718070151504480703070345603641c0d9005400d031840d41e0a90204030480441c0640d10784515502e8003c105c40e03091002050580100700e420440d9003815500d03998400c000304001c0703044458100c40c0c0400e25104410321404030003201030032140760007904401d200340d2250315 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 667007724 1250 667006474 667006477
    0x150308090a060507020612132010050703080601140d06030f1b08030f1804090f0615050a0b0c07080601120507060c020105030402190b1c060e131b0506 66
    0x1519080000504000c0504003107107800010225494158101000c41c0c0c005103051086001151400b81c3c804082004002c4042c40102c2c000d40c81540b229504440c03501060a425690722124030802e8580f00350700300d2500490444030099410354414469554040056903120442c0300c1e8029402810700a1491140a602c00c1da00a1800f400b0304d411040907510701000c804d2140000c10300b00740748000d0304200340e00e000415100c0d001c402d150341503240d00c4501c1d020448849001c09540d4002d040c02800d1050129844503000c0090080d08180094880038401d2190400340f849080e8200c00c604104001018419014203040061030041e40d0016903240d01c07041c030b000805e8000301d2880c15440004020800c0402c410700c02003456003020004210a07400203003242c00000e08c068020390a5203810140e1880f00030740000a08507031111280c540540c10703e8038000c408801c004065440c070300300022400d42d40c0d03601060301c54208002d4185441030300d0740da40c14071082d11114140882800d641f011074299107090 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 667008974 1250 667007724 667007729
    0x5151e04020c030c01052a0f090a060302030f090304080705060904020d0e0f10091208190204090c11060108061303110a030e03011407080105040209030a210215060915030115 76
    0x40043d600d8601e0010598211117001c2c1654481909401d80300c440c140c200600007001c11549070019844004507a000c103420f116009081d9441804000049035170b68055028600801b100f01840c030141c0c3c0ca1180180d075074803650180c058190700c05041040546016001031070440006070000d030078055042e0900041c3c494200030103125400070021008003020401040c0a020002407041c0405141c40d00c2d030b15141031503031807090104800e200002d45200345107034140800441c100c8046689a0b80e0702c002c0802000340701c844100240306051940c18250340016030740d040c0c5500402401040d1244511381d0071401d00183c0841c14011501c0340c650810b2010711008100c18001d0322014100321006c0205800c403400344030b20241540941d400c1c4070860347d210708050b040d02c070240e8005a441803580c1c0082c0c9401d034039071002042c1e80403005005080000d82c0d585500b040645400710364a01c6100c0c420f00d8600c4604941d1107401180307120000e07505c001c2e1001458600d8070060000908507581d48111949181d454 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 667010224 1250 667008974 667008997
    0x60f050d1a0a330605030405010213290309060a0203092a04141303120b09150a0503030a0c02040c090e0a0509121c020705011e140a05151e0402 63
    0x8018030841082400203514044614000030714280100c0f100d0651180344502414040100100005041220035412145040c2010b5907884480d81c2d1800d00150441a4441c10002c400c00040c203142d40c0c0942c507003500e00074080078024011396a100040c100003034100070146901072281e02030f01c108542c01040b81d0461481d4801c8621000c203800003d00090300e40c03032214003407081c16240070800d415205006108600341d051800c95013442038504854050418120003544c00403550303090100300319191030507482c4100c0903500110416582d00030180c030f900030100460f0124200140000043c6400d5004503c40022420b14038509901d840c1c0c25007501408980300c4038800e5480050003001001044040500004602140d2501e408501d948041500f01007012486517004140681044020740100d11844100541c180e01c0b04860051b00c07020302018800704001c1c0c4440c00c0403420258441c01094400d180724203661900e009054144072100040201c060b41c964030348616800165614002403005030301d070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 667011474 1250 667010224 667010231
    0x2070609210f09050306040f031e121113211e05070503010c050f0f0d1e0b0f09220203010e0102070204060b0426030403060f050f0a060f050d1a0a 64
    0xe41001502c40c4102c1c1d20104240b1071030440401c25903800081c980e81c060b9200303081c401d481d8854503090340d0403044001e5220482c14409030055075554440107c41c03034040b4405013803112200324994030006226021400b007007400c11007024044005401c1c640010200d10604017a001201ea807203013a00003180c0007550b4810404010140c040c0314080040c00064a8200d000704130180040ca0050031a12541d0803c4032451408200d0704c03d0027640c2c1040d9404403000d0303001404400d0340c400404c6901140f81900c07540641c50034501121500785414005101c00c400741c0040440e44600e10640c542131001d100d94070b01d100701001e107203005807005e0082d0b0152450b010005612402c0e01e104200c2921000e412102004206200c01c00a5000b2054402c4440b03842d000b12240765002c120070709045204680028140c0c60030640070030380441103680468440d85040e404200742d030300c4041040c004d880b8030303100d04081c81007000414401490300f10700c0305201038400c6d014200e40c003485134107100d5014011214200000c1e035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 667012724 1250 667011474 667011533
    0x71a010509060405191517060612011a060c03070501060e15030c060a0e030a0f0506040c23090a0612060204060801120507060e15070507050f121002070609 68
    0x1801d069403500440c00329410300c0a0314182c6144103415001803818091a43ca460150144001d000080070140195440d03403c00c000c0d0002c41e0aa441605980381d5000d603021030030b0806807010610400c6984030b81512422003550400c2c003084400c0d088100041c046010420415001800921411009001c0814202c40358504a40d25007550100d4060180c0290400d95118100d03542d003204507010008941401414804200e0210b41b4090340d502006221540b0148114180200054594802c1d889400160307a07403074450004103c2c0c421250007070040d080010000c0c4a00786000e200550f402428150000b94907036a0760300c5030005e88180c80064403003a500140034031075994408988e50140408501000440000390b8038a55185250710808003045510800c805040d500d00139501d00e560010b0500310340700da9031800e280c0e488640c0b5220303292003002130040d5a8a0b90900c280390f0b803040d0504401602e484009000c0100103540400d071304a486036540c0c0040000580204104001485210a8403103030b002c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 667013974 1250 667012724 667012729
    0x809040f0c0f12020a0e0d0809220506010c0f0b180a060209040b0108060901092a030f1a150c0a02040c05030f0a06050609060a0e04020a0f020c0d050c15071a0105 71
    0x2900102c02d0f03507103280100116203046400038101c80712036806a400060140c0f40f410710102c0c500031140700b554000135a02c40c81c4450021559142c0124800007401c1129031200700040d03402805400000f089580f44407201d60201c0e000001050f8800c00386003040c4456076a0440e202d0030403600c00003c40b4955070200d0307004e0840c107080c461f50362546000e003081005401c007003000986400d0140b00d6503070700d2a10f8501100c00c600c80e10540c10000a03050203a689401c2900c01c010300980000320080d11070038600340e0300340c1d24400070b4252008941c001501055210f40102c035800815880b01d41841900d101d44850f800c0103032901d12502e20a5203582c0d072210344a0170254140b90400c10040c2c8130225140c10207500740b0080c2d07508003c4030a01682102d0665449450f000d080c1c503015003142103143e0061010a41c42ea003250081ea07084500c2c81d02d5801d903404400018100080c02d0748042c0c02401c01c0e070080c038400d20541411782070006c0c3d006a040d03290b81014850f65034030103844006400000d45010040c0108180e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 667015224 1250 667013974 667013987
    0x7050907090306150605070f0f0b010932131a070203070b150310020307030f0501090b0325090c020a080408030a0e030309101404211416030809040f0c0f 67
    0x9202001c2c1c2c4210324179100005000f4003c40354003400d90341e03203180a1404c200a2a800e140c0c1d055210704a8044c82d039441e04c0e070710000c2521311000489070306410b800300301d01c0a051250164460312450401559200c404c140142c2942d07104089403403c25003e0b0800c1c1801884460501c262160390066903101e0340c0d480d09040741031024140174030140c100c800c6180d140e6000320f02c02624020003040140c172603a400c04110040c1c281070071440b0a081c40e047c000b2941c443e06420450a491040e42143c0c0b0210b4210a100c5118840c0801c1c105005603006e03044c844101e140c0c02c0381d03040108910480382d01c0081a02c0ea0006944030350f01501c401d900004515400580004004151080480180d41861050808569948a03141c0d2071810000040401e155003407010742984c0252009942003000400038268000202c100c132401994a170078a4000210340c4000040d010720004080c19120141c0c902d5941e4880094006484480e071054540803454003c0e900c1d403161600c01a80c9541d03814180b860100007400d907 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 667016474 1250 667015224 667015241
    0xd06051501080f0a2007060f270204050604061508040507050603073e0c090a1112130b070f090b0a0e0f0a170304180501030f060e07050907090306 64
    0x18006442d0800030000d00300340e40b160748007440c084042010390078011301803004044c0300c100280079000400c403e000e200155202c5a540132100c1400c200c0f03000306050f40120000003606001010b8000403404e0010700302508245c2c1c00840140c8003045054840c0440c45268012201940018180c44104000d0007000c02103100141820b580712491404c24030070040002d801070416444100100030034840800e5103030072107046034604110954016060f059030940710354074401302610519104011620949081c031034440e0707240207019150300d429080c50588d00e00c020014000347d4540a40c03500800491017101c400f0384250300598409401400f00003010f0000a900e8000b00307400c8905000b03141e42903400c8240028140c3d400c58201410600c044c0000b005091150061201400c5070b824403139504034000064401d845105244642c901c140301074110448009100c0a0b04070100f40d04540d001c60b0703607a44141c074100950030540c4c0b4000e07224400b04e00d07410400d94221000401605080007801040d1160000c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 667017724 1250 667016474 667016477
    0xc061e0606070f0f1406090102180a120f03030b150a021009020907030b06070c080312011a030403030c17090c0f180402010f02160609050a050d030f1107050d06051501 73
    0x502c0001d8a8141c9030280c0b03034600500300c1d050312a0540074041603041d4010b43c00c2c0320b03804079411441c150090328043c0d001324280c000285000403008155142081d0f183c020b651402c4000c001e81c02e010b13210740717103d0800c0070b0040c1c0506039140d143d00c500e40c40d010014080050351109a40d0303500c00c1c021000f4503080f4040d5148071168a4520713110016550003410540004540c40d01044420007140007801d240301c0c0e600010100308450100040100b000310160545070400c5010f000e01380c2c3d882000b40500000210100d480e808204000b4001a002c1c1c9c1c09001412520300d132250580d40031240d00d0301d0344d00d020380d81c0008035404030a0b40a03541c90500902481d402065503a54643c0b201c0c031300d000d4a5030364040d0000781807040309688684142d10800803109600c501004048006643c1d120280c660040c1c1d00409010b0b07400d0318004552803c1c0602504500c3e58507555641700000c0c13050007100c0e1a6503103113090449000341480001d581d620144414240703070182e07100142c5030404264803020041503250706070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 667018974 1250 667017724 667017727
    0x8010801051009020a090e130c060f020a08030703020403050d030b03010c09080703020f010e030714030d300b130f0e07030c0b0d091202030a080901050105031e030c061e0606 76
    0xc0048850140941110f0041d0405030b201c654180007580d0301d1815820102c0080d002c1c00402030528000311040140c280541c40c0300b65225140c14007200e101140c20f500c0c0d80560701002e410b41c0050140e5008640c410706a00d0014201a1240d4030103061103904a0000c00080e200d1102c250710740b4080c462040c1d803074403e08041e4409498144510b803100e41c5403102034800e20050300b031804641d0254804e0701751410010140d41c00d06480c0d1403490700c07a01038040458080e1191114450441c1e004114070012000001c0d10b04801d0540740088801081a6405000440c2e403606000585a101c0302c070320310b0750211000c0010421040c902a0442260f030590b003464101c1d4000700b400c00100d03100b0140c2200352200801401d988a101e1101c01015203c4403200519180d074180c1107400b00c903404000303000c2c440125075907050540c881030b03100d50076560280681e036815000108148801030079032048189090b44001030740c0c108042884101d0400804a480c400103000601c1c3c103c0c0714424445250b03900040c1129007a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 667020224 1250 667018974 667018981
    0x50603060d0305030429010305010c020c0d110f1003020405011b0f08070804080d09050423150a080f0f0f01270609020d062408030a03020a140a0e010801080105 70
    0x1580010003901c0103000d000e00000810140b0a000d440103035075011aa140200311815030030700e521a500e0910060b2140c6d4030381000c849041348080791a41c0300140c01060701a00d0300b615200c07400190503169000c0d902901c05000b403985521035026204020076942c40040c1c44505d8800050030003c9101446030590341001c94003000241d074000e101c40c0258000b00c104c0d40305c0c5d40510700420144219001034440d44a202c12124940d980210144241c44c01a40d00344401161300e1140001c58030504202d0500e82c0d080800520130388a20444120030050080002401580d29590030742024912082c07c0d4081c0c104031840394030040200150400c50200b00c000b048542c890b002003030f803980c203a5044040d1a80c41a0360140510560350440c640c0b9580051142d080300445140c0040104011b0004540745607a82c0322035204452003030402c008640210019524141c1c162208030025848203819600f48415240100d01402441004e01000102c988032011803685c10000506480c0050340180700607030510040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 667021474 1250 667020224 667020229
    0x90f0b061017040311030403050f0703120e03060a0b01050904050a060e09150f0606040e070f11160e0402011701082109100e1215011818031b0b0c0304060605060306 72
    0x3154843d81521700201d412810000590561007036034000392592007075802c221400b00012030a0b0702181d01c51124414015514101501c07401404c01d00c890349508520001040102c0c10f0304010b4001e03005140c01c914080c2c01000050490360b0a44c0c041d2607040c0d0340c0c4000d004000d1100d249581000a03400113028401840041404606000308030a0b50b08042101069103600c5150941e00035104014100703904d0324210b800103004400040d401000915043d2042c0040c60001c2213652010407072074006d14925003040c0c2e598040100c0540128100080300300040c01d401403071400c45019050003c084e081c01c2c02440017007140c2e41f41c0d1340c1c2e2801c2102c60800141009031759507407801a90340710070304200d0004902c56000812407514841491030a010341b850048079103c3c00c0780c00c2410303111070441482c807400a44811400b01c0c2c06580708841040405854500402c2c0501c2c4031601c14582000c60314031b24181950fa244129609a5208070b6010b008818802085028001c0d01d006c2d040c1a01e0b06821032828400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 667022724 1250 667021474 667021517
    0x5070b070c170f0319120203040302010b010228020405220f052a01210e2b050f1303050a0f110306060a0b0711190611160513090f0b0610 60
    0x880c0c490480640341c24515240100b07451030604046ca0b5007191240780504001c0d01800c81017101314018000d080760301c066400c01c94804000380841000354180c0d848940c3c2844020407002d807107401e107003800c01140d00f2010440ca60075a03d1038820b603030ba8202d45035949480c92030301842d02050100400e0000a148075400400d506003141d4000b4a00820400380781582c000010301c1d0801c030030f00c217141400841c1c02945000034041c0380e256490302001d038035949030300a2040b4555400c010000001d0b4100007042d103c80001002d016a008022404c01d00e50f541ea5403068a003010003002101c0b1241c003201050107018100f0300a10006070140d02030009031034010009060b18200b401a0806410302040380428040180a61005d041001e00410411050103124022108891090000190440b101c84010140c00301d24101a83c1001c1440c03102d21341030504100500350015824900c060303403450380f14042180410580e640d41c3c0a100700000600301341d41840040b030340d2400542c00384640b0a062440c04001c039507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 667023974 1250 667022724 667022737
    0xd0c051e10120f1407020712080f09180106020c040b0319120c0204091406250e0f06071b05030a0503030f150a0602030307030f0c050d0905070b070c170f03 68
    0x191041c2c6040e0340d90301d42002440c2c50310103c118103240c461819100300f01c0310b0009001d03154070303000c0b10b04030340d6507541c55a0409100d0038010002442804291184c0f800071025207107000b401003081c056280e10006820446009a0091005074005408103005003054898091440c005501a00059001c01c010628440100000030420382c09101c66042c810301c0740b014070b251950b0041080c049203940e42040050049aa00003182a0040c10003240e03040c51821003100c5a00341384009a04000691203041d0b03080100c64000c250010b82415080d030542e0780e01002020403602c1825503100c4800d14035041c00480e092900240c0c000d40c004041d10011a10020669521840140e0512a2a42d80443c040b038101c02c80c04410f0341204246202044854001c00954411030051780c1c200000030b038410102c000e80d43c550283d10003089003000500300324070103604a10300440c001e6084030303010b03a62039801d40895031041d1426078441c0a04001800f200c0c0c0010f15007403c200c100720082503028030b01010141c480c030800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 667025224 1250 667023974 667023977
    0x40f06080c01230a09050f1813031709010203151005090d0f02040203071d040c050405010f11030d0c0e0307050609060c0a1b151403190204050d0c051e10 67
    0x440103500e0388194110f0003412607140d902d1082d101d000c1c15001401e14840e9000391841114010192503c41c100310488001c1b03039140700341069950b00e13070144003070f040700704030b04140d04101d100340c4040612040d100c5454060100c41c3c0005a8074909560089040d000b8415228031852040140030070403680102960b0300d4420407110550780701d19626012054449074500207400c98008000c00035003039042400b040c45140c000d40700d415500c1d1200d0401085405003001c0d440420310601c404e100f00c0d4030803250910f40d8045d9080c861a81c006e40210249503811100440001b9a21a07800124142c1d021809001c215401c3d0003c001c182c0c180b0340021118001c89400790b01030003000c220040c1c0b030700e002c0001103c9a900a215400d154500a20350101100d65025522918800e0024008128803c0300341602440079800d9113030858880c58600610107400607107a008013502404003151aa403030341c1c004109075228040b800d01303252078034003400071982c1010071016481c20031408010790b58407a0203400510b080c00c0e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 667026474 1250 667025224 667025237
    0x70608010b0c0a0f050c011b0b15010302270111011404030e0d0c090b0901050d0f06050a110c010f0509030403030c02010c0201140d0b040b060702010203040302041802030f0c040f06080c01 82
    0xc8141d540c0c6083e6940d0805007500c5140b0080800b44200454001c103003c4007030340d5121228140880c2c01d0082403640d0070041c450311749400021019070300c581c15003481910501d0054070380f110350582500c42600c0000c03091501018a00381038400d42e0841504208105008000d02584450015520701143c0003000601440200110050b280e0745040e1403008042e40802c41c40f1400391581014001070406400c0d190048048600228041c50203005600c20290320000050005036984c1e02c51007d48005400c1d91481c1e9181d502800d40803038103c000d040d580a6120000560a43d000080d2058075000b0b000548190820803090000c65841010140065020708004c0c415006620048038250160080080e2a00000c1260300030a617060704800c140300400c907401c1c85805802c90800c440c41c4540c140c0203000d64810001000141400d0300021120030b00303403001021050883e000b203418031807000042d5415412070807049542d45814414226004501d45017001134504081c1240c4d5101211000603050022 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 667027724 1250 667026474 667026487
    0x10b01030c1b1412031003022d0409020f13050919020109172a15041809140a050708070b070f1506050a080c090c070c210c060807020f070608010b 64
    0xc00700a1007080ca407880302c13150742d01c2c984811403a052402030700041384250710b0b50200d0900280281e1403165124091080c0307900003012001040002c11a8841c00c98000c1081e00e01d0f100f60782e444822182031108194030204152030126070301428900c09a0038420540c56a03000350015036408904182030325030130a510320403000c5d0100c4085c42c042007408048080a81031402880710a001d40c0303031141115041d680c114298000c40101d4801d40514003400c3c2c034008201821001418035508002d00140c05503900c8814118083c550318107140d03443c8000e40385684070364020048003004111050040001e0603401d0304015040d0b80300c0200e403030f0104010300700b501c1d1b81c82a0030064a90398413407402000d00609400200b962130084c551907101840b00b4920440700c81001030385840c2d40b24111180107610501d0042c2d01400d151100481c424441e01c0328400c0e8a13500c429800240254180001074102d0b0b403a44141490a203200900d401e08402c140c0140f6005a0300400c01c0a80248040c1d0545022114407500e441 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 667028974 1250 667027724 667027763
    0x6030712170403230d020721031115011d010302131a131e09050a03140d02030a020310060c0b0a0e0f0a110312040803040b070212060405010b01030c1b 66
    0xc80d0000307005480049840b4000700303840c1a4440070b10130810143c90558118600990b00c07003407030b072181c0e240c640d001c00036482d9240450071400500310301ca814010f4011900024180c43c061248603c0242000c03150014412020000000c24840d180e81c0702c3c4c0b201c903604660200760b1000840d400b81d124903071075504c0c00001d14240e4403c0c040c1c0c410b018100d0840d060800003840090b0900440001403d6a08007420a81d2001806001d00f61900940100f5000700d260380d04580300071351a0085680c4d0401071103403140508050000754000d4410384400768480c200041030700180c0034517a0218040c0100c0c5952200050108048180d10254000340000c8102c5a200b64605100c65101010b40700c6c0140f5092408002c0400080c0c0c1183c00f0541c100c0b001458101d144c074001d07101e00d0017010221380c001d01c4200410b030140310050201d20301c05001c0c01a4074902440300e81c40c01c04280c5088900365140c0030b200328107580c18841c4800840c0280b414002a84225282400070411410301a10b03c40245040030050b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 667030224 1250 667028974 667028977
    0x30a0e0108060a05092e0605040b0309011e06050108010603182d080c15040b04151b081f210501111306110102030c040e06010201110d02120603071217 66
    0x4000c0503000011601d422245100051100a1403020043c4c06c55803c01c002521b200d421170541c1d01c5619054981820a5403404158000420592596403120017100d5040d0400720361075012650000e010074800d06207000500078060580080d000c051501d0400c03038100c444910300300c1c22580c000d00c600d42401004400c18000031900b600c4030041600d41a2107104001d4000c00814080e035412094544103150044440ca140303a00355009800021040082400b0820958074252511110480051440e201c2e01c0c2e4107003611841c24400010a0b80b01d002c029448950880441c817403803100191420f1a030a04880c1d0b600f000c0501c011090400d440007d540c2040403d501992540c1c0b80400c15580b58200d009030741654003e41c0c0a20800150340d42e52042c80210305009890040082600d22814903040c2040c000d0030b180018416811036480324900100c1001c210000c00d41d050f1040380143e6a90b40d0300880030b550040c0503001e14065444070604224005285100f0b807101e90b884203084a40401002a25016 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 667031474 1250 667030224 667030229
    0x20a050406181a0d080c0a050709061d0912130b040306150b03060307090c05090a06050912030c0c010f0c0501060e220209010506030a151e08030a0e0108060a 69
    0x41d180241c0422000315140b49007805504030032040c0401c20505440349000050b12986541040103003607030000003002d80014101c1c50b0039500031110781c0754050301d880d45462090350116003045d43d918000d20071207025400400b12498503000c168401e0500780241e41d031714101b024840001000c040703003130720188101c1b42c201e500610f05401917a441c0c80d117038186880200b203821204144500c0880c00041c2c0b40c0c0050045e00d120f500000c002d00352a61a0803500f9000e020b1084c1483c0411070204400c42031655100c45000c0541140c1e500d5503102c08581003804036131600c80302408010341c82800440310f1103100054401080c2e50a2038403012180c008901030320524040580101507509189000c51080904c4251520a04503500504400d603140551030312442d400c004080e4028044100602c06410034030004e6800c04401d41000417a0799501820440750340ca150406806041c0c0741c81c061002c4404400e0040c0501042c0c800785150003000400030700106c00e140e05143c184140b0320300266181c1d5580400400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 667032724 1250 667031474 667031479
    0x12a09080f031b0d0507080a0908030d06143115030b070201320601140d05010f05031501181e09030314070207140616030203030405010f0b0901030807020a05 69
    0x288800825481e8a81d084043e941071080181c2c442010318150002d40010004a00c3d1111881e00309143ca800c47c09034404103402c014031105003800035003210304100030f0055031024900000c12908161281c41d00e400000e042500c118855413407203100c0f91540c0c0c8107078103e1944841c00c4081000400094000e040003c12200070300304403500c000180840108000e1141865030b00030800078050b0103005100c4607c10500140c0000c68450a440b80c440684441d87c200c1c405042c2021f041c0110302d0f0142c002d80c859034040340300c0c40d1104010446c0d0000182c603080a070074100c0140c10b49102c00070840010740c0d0140b050a91460041603100d4400c58113a202000301c0240500404002811105400c040c00a05c0400c0703001921700740008600444000d845030003460194090440c0b185001d003c03100c9260300b01100c540c012420050002c0c00e598006005541e14800d8000d0740d02c5c1c0c40c0c181001402c5902d03100c540b0b081e090130011a0140780d61120011819a6445000c85442d10040d00100703585a649412481c2c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 667033974 1250 667032724 667032733
    0x10c020307080d0f0801050303040b040b031017030c10110702011b2f03010e07090c1704050a021002160515190201020c010c0903080f091c060b0909012a0908 69
    0x11900d82c441134200b020402034a4850060342d03100141503482c403131446104640a82840148140c2c0e4038400110f81050700d10700295100758460001c69200070b10350700d8000107544005041c5074806003d1003d00b0745402000000c000710f407580c0d402106c1a1107400c00c006e040251450030b644485c0c552003400e1150300d4200c0c034825043e00c0c8003101e40c080304c0d061412131021182c1c0a03e840c11286414000d4420202d0320002904015207460f4641001d000b070f0102c104180603542c03001e00f40400410301880c1c4228003074402046105001d005220301c540c0340c180c1c0c51086412050119a002c0917045800d422a14151401c0304c000d000d0340c0e840f60a9020309030020f0035200815151501481c0d054010b00919030344c5d20020810b41c01c20b0081070b250f400c4d89100043c0141000c0c008100d800074403030041c02d80b1400290107440305103aa010513080c5a0780d10f40302100c92580d2420800f0403805e18910703c07070344500302c40001c00054003105101e601c40d8400529409081801b0755070390484520481007480249007000c00c54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 667035224 1250 667033974 667033993
    0x3060c090914070e0d05120a110102070f0c170304030f03110d09030506060102011a0402130f0b120a06050f090603070f03050a060507020d0816020a0f110f0603070e010c02030708 78
    0x40b0034a000a80380032000072101c49080d009842d00d00c0d26142c1450f0722000501100d134511803001d030241c004448040c1400140c4030241000310081c002866003d114a45002610748507192071100c0c48155006455103005142058590303040c0041101c0c1a6038000080140001c65413504681e601d2104101c0912801052034050340309070040305080035a131041080d1002c582c2d40301c004a0884911401140700715082d542005614102580148504480d6a0003903003115114801c0300c456030303410351200c60703034070400680352865101c035200c0a0b4110510a01c240400c510b0a80041d000b81d00701c82030a84580c48400115440b95410030000e0000c00c4608503032646aa928100603480e0411b015042d00c0303031800c3c4800264903a2000c641e41007040d4142c0c85d003550503258030002d04050721411000301d040d445200500008900310181820841d80700e856022018400c0105011483c40c05d0200d0034040c05c070034000c0c0000e403500301c000d4060300704083c03801d0301c2030780d0003800040d28080d00360b03200041d47d00926881 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 667036474 1250 667035224 667035251
    0x12020c0115030b06090718030b1803071a1315020306010c150f110a0206190f151d07080a0209061204050c01180b03190b0406091508061003060c0909 65
    0x8640c0709004c1114181074959400130240c640340e141c40300d00c0c50b6034417203503105000103aa8070300c0d8640c10103401800042150341c806820340c69980b0030b00c0261228009402c01c602161040c400055001520207001d1b40e220001c3c1c2c0e28140d494203e04062100d40342c0220020300c660f48100c840b10788241e041082c160b40d2040c1204c80d07034000c0c039040500c022564182440c1441c0c150f512001c40d00d0510307140d8010009a99000001160158916480883c15450314400c003001e0b101c2d8040d01d000014120b000c5010b451030030011038801d85200b615080e882840104000e01e00ba0072048042d07120060030b801596a02803240015000c1c0714041a02841c2d441d0310702400244440010300600041c0700b0380355910b40c01800d42c43c0c20b050900c5882010022002000082c0720a2104040709401101c5c100001c550b020310840002d064810075040300030032a90701d111444100900c0c074030340c000401c0d204003e04003a05164090319843c5000c1c1c000a0200358446c0d1050003000d114400602c01000d080c0c0c420001c0d58100c0d001d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 667037724 1250 667036474 667036493
    0x1107121101230a050403050c010606021b0118051011060a0209011119021c061d011505031002090102120d02070b0a0606050a080604060b040906080106090c12020c011503 74
    0x2000d09035842c1810392014518104920b0718010038440010601d659540c01c40c0014080090045007081010701072500c82e040240240d2000e021690080c041c00d22001d6940e0901d2045d07640c2890401801d1040d48a0142c4048800f8090b1101665501034500301e070301c8141c1e40c50800e4211018a8031035201000b10399041c13640a0001d0b03403030036650800b096105440603642d440741c02209080c140108502c1900501d0b0070030107041d00203102400c82e00214841d44800c003c440e020981c11401c403c8004212800002c02e20580341d03a0084200b00300e001300e05002c0400c1e034444120400d840c030264000740d0313074080341e001300b040b241a00d224041142c1d492409125074000794024200481d00001e5a4002c00e11858860040c0400c0c0d94450390b40030700782a00d090b01111742c0031018040542003943e903003000c6544d80005000344068508a5008118149441886800c4500b16403083c030840c1e1a098100d180c4940c40101310880103449103002d07855068100d08180100b444102c600e0b801e50104d00008100403071440c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 667038974 1250 667037724 667037747
    0x7030f2114010b04081b010e060703050315011b02010e130e101a060703121d010c0908010902010806120c0904060c0210060513090305040b1201051e0a09110712 70
    0x40a881d81030360380300001203250045000714103131500803019000556201d00b407441204181454458084800240490784682c8495020b9000a0000007080003c041501e031098002c602840c022a9103e0100c0150710011810b10b00241080a100d44100d05503548269210340625110020400e042480000325620340301501c52582050402e100910480060f4101d07254154004d8540c40c0340c074182d80e0382100c0b003420001d00d04240070f0303440500c1c1d6011201c03802c03007400d00000351000081803d2131036400342003015581d0010100d60f040103088001030340d0190f01c294000c0d00c00e4a11003054096000c5460410300704084142d0440c5208041200b0f10071103800101d400c00c2c5540a85103410b01005c9100e00343c810390f0007a41c0e009003400b20603000c21140c0da800010254000d03d041d40c01c0c6907d403640d03e0310640c004480030a5a480c00c0b00148201e06d84141c0c0c0d44114240f414100075880240030100700c0d8204580b05104075a03650b8511030202c1c0c05240201c400407030b030141c41c00005428000c000307400c210380c51 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 667040224 1250 667038974 667039001
    0x1f02030c030a03060806130b150d06060b130e090304030b0709030f0b041208070e06091306180b01020307030e1014130e0109021c020f040e010f030201080a1107030f21 73
    0x120082156240019600341503032303412204245a03952038440f24918145034112040c2c12101c210220f101140e014490500070348070200099070741d0740010340582c040900d00e402070141c0010440c10320510440c0001180d0440b603001030050b5460f65150003c1c0c40c07000003a480034000e4803140f00d4900420580030042846940301e1401c2300100000f41c64121107040b030840c0c2201c00b19103842e00d11903603490890043d054004000304002c0140c4038602c041001d803842940102901c4402802078011300c1c056000d041c02d404000e01c02503080c50403a8800409000c0c07007810440c016242c0018200c4140d2094400321519044094529503d030003401c0c582041b600e151090161030b0f02a0f000110300500c16000b21001d0007202915000d01e40170a800c3c1400035400141d80c910b69500810001a5003207540203024000d2622040201c003092440c00090182da00051464030090724100402c8101f0641d0016600b145802d46071910440703114100580f03d0501d100c00cd51207002c00031049500d50f18254101803600c0c21403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 667041474 1250 667040224 667040233
    0x20c060f040317010e19021e03010306112110050a0b1c050c121e0103080a0f080408160c0e090c1212071b091b08070c021f02030c030a030608 62
    0xe105205110102030081802405403c004605421030203803c1006c602c2d00b90078014030300440a0040040754040d00000591104007100420600440b445100b04c1169005a0740c3d2600902c1581c0c1c8104800750412406898103110204d00c880c140c09003031320060302d80540202203050311508104c40d107400144e1440c41e400e403565604003941645029140c0079501c00c482c000d00381541d1940002c07003200d00401180440c1d260010304810b98050414040c001d60003076035132698445d03031040c0041c000c0440050040034000c0ca40c0a120000c1c400000301d5203d102d250404041d03581580c1307042285420103174400ea000421842c1400b41c0303818042100c0400350002c94000701c0c030a20442c0416142c1250038131105001d6000e105140c04100002c110190030034039038070b40d00000c64030b56402204482c1c10982c02251948002004000c41d5049001180c00c410141008094103045600180504811300a1038039540614250303002e80390b0081064504000d100c1040d81d86079050b00c00f005005000d41d00c0307449060700c02c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 667042724 1250 667041474 667041497
    0x80405270105040c2616090b0901110a0512030a0b03011a060a020a05070b1b0105101403070302120c0a0e04110405060a150e01020616020309040b04020c060f0403 71
    0x38803515040181844019204140e840c2c041000002c16242c801902402041051280402d000c07807418507040030001c41851090038009501d075800310f031801115050003144030090101c7c100d040c0a4500d044002d20300381d091505454256410030300043c1008142c1c0c4100000d008200c010103010794814542004100501d03a0904101340c26550030000d2074501282c10258001d240c2032080050405034604c1c01110b2180320700f80c0c0c800d80b81085d0b43c0d0040101c8800420140e40c452450b11002440d110584e000b840181001d081001144041d44100e25150449101c40201506c05021071130007141c0040400b00a56500a00c1d5611562607202d004d20468101202041401581407503500440d0001200c00b442003c610910004003030245c0303071950100c072800c1c0000d03204061003115100700000381e98943c0100c10010000e071421310090115121241c031002d960203059070000a56141c00c10890740480c42c0c40f402001700e0028406c4880d100490f020740c01c100030205000602c0b20340994402e1780c40c40ca003002c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 667043974 1250 667042724 667042759
    0x403020c1503010302060d0608030a0518010c02130c0315080f060a090f0f0f200102010e0c01020a060209042003040c0605030613021b07061d06190507050f0604080405 73
    0x5016010031041d030203041c8014000b5003015000b8004000142c2000034035951142c105500e546c00c10f000020024800003018111030701e100e900141150340a080404035031200b94002012050390000661096980e1801844514465040000c0c403007100c05007001d100c0d40307030248103441c0c883c1c0c0f011420301ca04c0744602140400f60203100780807038035821820300701000d0540c1c0e88283d5281341c030400c00e43e00c032010040c40c0300201d0341c00300b0300400800010340030100700700105002a081d24034944020070581c004030400c5803036980124a84400e0b81d4031000042e0f5811141c0005801041007501c1d1020807540c0d921b03400a4424414003c500980c0680308400c6071650310714049405200850b055a0006051000100f00550680240004020040560441100340380d030492900c0a181e01142c0080d80070314110300502c0c103000e40340f40400c4041d2001071034516058141100007001d86003a00800c040010b0303030014460b05014803403400400805a6a060500d410054a9900315014041c1301c0c4626683d18104e40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 667045224 1250 667043974 667043989
    0x1c0504051203030606090d1106040605040e090a03020d030c0311070503040e090607090b070501090f080319022712060703050105040e0f07032402040f03030f090e0f07030915050403020c 81
    0x50100502451604013501c050200c8241d40c6c103030890b0725861541015039035542711b1001d0701c06407041e0303500c07162954644641a8038007107000d0316045036500303c0e4000b40e010036804660f200041020742070205240300c45032b44c120002d2248503440443c000c00407400b4000c104000c001401105d0000c00c00341c0381d54641c4102d80342c541c0c2003a5550408034004c200100300383d0200038090043c644c010000011100c0458884201208005004480e030303c90001c00c100b40840c0c2003001a5042000031011401c01c2c1201c80007034805210300407445a800d404006403070f06036451314200b0050740100706c10345c5c109060111000e400380c0300c28003629204038100031142280e84000506c1e841e040303202c00020200180b440c1c0702d4090181d01030b42c4a550680744584141c1d1849076500040c00100303d5115900c010528500340244042d4892070000104551841d04202c010764041c2040c0d00170050000c4064643c95001c0160010203110000501ca400c8941428440303c0c1d255015070312840c00b82e000d4480c0040b0b028104806c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 667046474 1250 667045224 667045231
    0x10e060a0f08030d0504060f020c01060e100501140705340608040807151107030e09100b03010b0f0706050702010b0118060f080c0903030309100b031204030308091c050405120303 78
    0x303e902c28041c000031200e154200302c1d00140200000580d01c00360074000c41c00e986c8000450411691900010080381101104003984041120000e144203401c02d00001d201902d084405911940040340c0c00060100030302031003506400110545510018200d44442805500d13043c1d20755214500d000000c0f400d0040303072481d08c92079000c80c095107005d510350755004800074110b041740d076450380e940c150302600d01c0480018003000d80251a60110541480c0812a610381c00416480c81c0c03080780c400400a0150180c182ca0561703104452080e01d070a1140c074103261501a00502400c102d051005200b013239a019401039141d01c40c203030703185107001d001e500360940103100f94820741c0c0005004421a12085103e1413103c2e40181506060501e80a5520000303442c5420a40d0102d4554000b1210018101d09910609828035015400390140a00d100448034440c0941e10019040c410340200103220201d043c06a0b0030400f240c40071110204056080040803500b0a00440d07000e02a41d541403224040004180c034803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 667047724 1250 667046474 667046489
    0x3040c0e1311190308030c0c10181502070218090c1e01030e0309040912080115021522030f020c0a2306041d1041040203010e060a0f 58
    0x900ba9400d1080c0100c51500e640b00300900d880c1d150002c400551520300450160a812008035158203c2d960807905142480180e040c1709482c00080815020368000169225500400e8045e0240b1160501101a10541c03000a50008040c541c6585c54070390000c46600810b400e40c11151240b000c00140078400000080314000c10030b90040043d2036602c80e0304549010b80079241500d040c41450f01c0468180d070150401110440c07040700c6960350711580602203500600f030341049848a0034822602030f403680c01c01d400e0559035101c4500016800c4000e8a1060349144000300100c41c1c4041c00d050050009165980e1307000180207809031500c1920705201c401303050f9052150403400280510381b54444138500c2204403900b20700140000101d0034070a41000307412059205406403a89418000c000ca10380300b54000507280c02d006600d107222443c0d90303140d480008441c1c080224505030300c00619400700070305054045d44070340000000300702000020002070180005035800304481da200ca50340010444507000303084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 667048974 1250 667047724 667047743
    0x607090311030a0201300f091a0135030a0804351612030501030506280c020f07080109140d081f12050d020f010e071202040b040203040c0e13 62
    0x100b81d85c4042e00c190040c40707404030f521b036030301c00008011402d490001154840c100c0d5201440750521841c148040070340c0e4004c0c940c0340d042c1d60404072800d00c0c4050901442517003500b4851088070101aa800489495440308100d07500e41c4107000c3c0040c1818003c5504441c03c8504500c6c074401d01c281d40c105038a101d030420a420b4448044003a80c801e0ba5040b0103105440446a0310101000c40c10449040031000c01654001c105581981449490a00c01904040261002d03a80c0e90381e0000100000b0382ea04245800c0c0440c0d4000b0f200800c903c0c0ca117803000280402d000d007200009180740154440041c0d03a01c240c889120f0340d80000400d03174444066002400114100000049010707800301c48082190078684014034605d602e421580310b0b000b580d80422926948a000c2c0c8211441e010004840b410200c4030003401244141e030f290a46804461080c007107090017050865045503078075040080940c0d0003800c11500e0346420b0500c21074103030307440c468160b4541814010a0714102c0d0382101e070300c0b81c80c0c1009402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 667050224 1250 667048974 667048997
    0x5030705120a06060b0a110604120c020d02130213142808121c05101401021f06031509320604140f010e06040813080607090311030a0201 60
    0x1a50601c000d080c03011401100d0004000921034400e00c4e001c4d01d28080480c2d11080c003000e010380482c011000880160f0f00c07100400002910721500c0c2c10500030a45003200310321041d0f1010928400b40d14070001d502881040d1100116001c030340c00b402d2a8a1030710203010103195580d40321850035114110a540002d0340da403131405580b00f19606405400a0302103414240ba5641c007919007020100d66196221031400a030302c83c080e01078020090502c2168410400003420070b04c0c804160283e03548201c0c000c0544c011007600240c0c0c002e101ca6556881d0143d1404600c0150f21642002000240011100213180c011402e0b2802c7c0544204000c0c40c0d803007449026540031440000c40314001c0301c030959014510b4450003a48103881803203100e0145201e00b440c090500086050903003000090403540403180e140040c50100daa60002e1040d81203500042c00c81c1d81e5022202102d4022007154000c840035101d1041070210301548500008101ca0080c842400054240d00425840b034500c0000680090030a0401c2c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 667051474 1250 667050224 667050229
    0x10b030c0403060905100606030b090105100c0b010e0105090f191a0d030201050a1113090209012709140f150f030709090c0602030903060c09010c0f080a0207060905030705 75
    0x25904035088650140c10640e4030380c3c1d520250b9000c0c0104841c15002400c2c2101e140241e8058800a082581014440c065000780030810b030350014070030703641301d4000c4030002d0040a0242d0351244007103030801810f10b050340c0c50700e8900303540e44c0080c030540c0d0269000c803000600748800180c215014a04003441e60050380071495440010385a080c18090700c250307200d2544205a6140c03820f501883d8420740001c60103143c049200000c03200c1c07800d0712003417038641001400703602c085820502068520450005803580c414000403641d4000300d44104040e241c07020b40e0100e140c5052100781d001c442081c2c006110242003260000000042540d01d41020100c58001c00c5400b910a41240403008000c0c00311b0103116019400070b0303d4002e4950040318011f40d5101c5a00c240310b810101030025050500007141b4003031851001c2503580900906800c1c540c0004606514140e10641e03c0901240d040701503000010340b01d040030001540a00c010201502c0b4060f00010003500640000d011118010007400d40140750100303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 667052724 1250 667051474 667051477
    0xc070611030f1c0b040b0a1e050d0c17010b0117040203011407230306010918182015030a090c091d1005250c20030c060909010b 56
    0x145400306000c10b22203807010899200140080d440508124401e100154112004803820720003007a01071421324142910340d0300c079444206e0403145191049505102d08500c840c40c121a20380080783e106508545a00c180606010f11506444c000600c10908241203d1404d00302c4503604007a88c08100c110281c070040e0311030252400c0d8000e0024002142140c05150036483d058400c448050115a92461205074211a541d4000000e0800c6003107a2860525400280410405106807015510210803d0a03842c883da0080c5171001d400843c40e02001c241c5250145030f0040b900c0740b030840d011030644d040c406403410800200c6140303109140145141c6861074407034040e000d124401d881c1200c0517980042c00c0c500301d01c543c4494001d43c032040b07080400352288060610781243c101d04020307400d00e8113110000d03803440c0e0b20f180c8016071a008a43c007011540d006484d18451080054000c0403c0480c201c00c1c40f4030b005000091300b100310140c071120701d1680e00300b20290085d8500560800001c00052003010301080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 667053974 1250 667052724 667052747
    0x709030f02090408120708010f0b03010e060402070c0e040c0e150112050903090a0f03060c080c03060415031e05060c04080a0b040f0b0907030506071b03082806030c06050c0706 77
    0x20710117240ca0120000c4080c000c03003d440100000d01700380010005074071120300c0c0d036020b4042c00949038515450440000d01e1100091f203060f200719030000300c0701b00b0070582c0140c0e18024001ca490a4040b8a000c0c00c00740f0861000f0721030200f50f040d1020008030721081c40205003422540584500b0903003150f8107006001040b0041c81c10060788820850411a035551044110007410845401d1001600350720302201514030784404003003401450300520011038140f41c1600d500171001c0d40c0000d082a050a011411403140d41e1000c3d1582003856651103400c40d0140c45180d51601450071580c0e95200c82c40c040da4180b00743d00c59500f10b50001c2041030000759280c5030240d0001e0160301140070040142e22429182e08003500d0390103155020102c20002c0000034400c803503000d0003a0401d00203824200034040580950100001c08101d604000190005800c20552001a00c1034500d01452150907107201c2c000c10b402d00083d22801044500007500360700c00c004866200748c41402a19101d480c0c1001911100d2204 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 667055224 1250 667053974 667053983
    0x111009030926010e071d10090e06070905030d050403080c010e2d19022106130c15140a03020f0f0406110d080c0d09050f0607080709030f020904 63
    0x2080002c802564610032001c4896442e2540c01c1442c0a006040c00c503030305140c01400301d812a8004100c0b9103e45c0b1000021040c0b02c1280d002640c0e5070103040040d2044980010259910340101c1c50a001e00005107240300d048980c544001c0e6548071010165070740c80d440842000a00c08000034000640282c005c1e200c0c40d101d100012450071644400c00d41081d0b0350890300c40c0f580074100b840d40007811070415107040c404000320150030720b0100042c94809280151502a000f1030f1b0301d00b0b1300f00c500d5201c66440201d0780e10010949a21781015510080441d41155099404401c0b0540c00b144a8903125401401042e842d21010000c000c0c0070424034035900080342c69024564280422180e104254005140303032452403a00c00c1d601c604103c0c001d04640d1062a261880fa8040300036030200540140c13006030000c1c086005280c445d00c0d1203034440040c01c6000703002081401042d01c0c0c005400720000e10140504e00d10703258031a0954a2180455020000340310103061307010103508081c003500f40f4003081354215024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 667056474 1250 667055224 667055237
    0x405010f02070f0602150a020f0f0a0507050d020f01200315030f01050a0902101d061b0f07030309050108040302100b0d23010e0d05070605060a03050a0b1611100903 72
    0x8800f62198100f186603c5807025070050b00246003080c05007509960301000f540d0045080ca400902401c10354003a0150310070300d400d00000d110010b5401032054070101c0340d100c8103e41d03801407140d40003034a03941c0f895001e004640c00d042800e406001a8102c0050b403a811400c1e2904503501c17610130303206031103000e000c0175014062914685103003c0280526442601c00380c0001c248280d4520600c616181e9910310307403040016098041d04428030910768010300180c1214103940350900f00c90804005001040161480e1103801c10807030315514041525002c0301d0094031040c6980f680c4100548801404440c0100103801108a0310103501c10395109010726036002d070001500e140703d0350b14600391180c1c0d607524801c91780002c1c50f520084e00742409192880000003020303000302c0c05a4040600a03003c6c811008004a895100084142c0c5500440c2001150000100d50718a009400e000d100c100c0144c0381440a6901180c2080c0f10b24000c69138480d4a000c80402012003010b410b1404005040c0c0c0141181000034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 667057724 1250 667056474 667056479
    0xc1d0f0913050d020109020a05060a020c0d020f030a03022a011b260c1002250203030c060f0a0c0c0f06020a020c041b0917070510020102090d0c140103110405010f0207 73
    0x200030403442030441340c00014110009004025044105500c1103229000400500d20015400718102d00c07090010703144d041405085100050354215030803c0d0076018442c8a01c48030074164005608103100084001c00241e1141050a05840700d05601005012450074081d1412040ea9450ba01130811b016031000c4d40d5010420a84402c0001d21001d004101035000c15409125081806184c48044410004605e07000c0c2c01c03c0c207084048440d00d2203c180706210050300056403814012505501c50b800c06440c11454500400c1d040c0d41d000359000c24040c0d26041d00c0840075405003030607690303c1d900804401429111a52501c010390301201c1c0403030844c0901c0d18a0b8003141ca45000d00c54a10303884104800b4098240e810061840d0b0072a07200441c0c0c42818402d800e80785c400824a00c043d030b001070714860030359400034030103034060311644144a810180030361200c030074071004400581c1a40d035005046140c001d035a1004400351038a00c00c01ea5424179041008210341d60048034034581c200c440380140c8a0096 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 667058974 1250 667057724 667057733
    0x605031519030219060207090902130c0320092d13050a0e1906020a090b07080a0f0e09070807170c03160507030c12030e030c010c1d0f0913 61
    0x14418950300d21441c500305014400c61501c0c025004020718600b00d540b1045282ca8402580c40c543c40c450030f00e2103a0743e528410251340310b0310340c103109003014080203000061001301c0090081c0a61507000c144202c44405402140441d0401c488509000908900080e4101220100ca4040081c1d0562481c00751515100d00c0b80c9400a6070b04070140d000100044a24022503594180e450340e81061280b0307003101c00c240038940c101e44060301c62107402110042c1c07a202250426242c9410981191380c100344041104010002902d004004160580d41c4a0801080d0703071000380c411403468940941e100100c940001d10b4588218812580202e4602e00304072050b0140380b0280c8100e60654181c21207450000c20020440003c05175012043c03007030300d81a4079043c12520000d0040751680001808a080c1d4200c40008501c01d400c07291903000e03202d044d29520240c40c4110b60084c00a00c43c00004503d6a440c00c100c503124500c1030b021550000344c100191a811802085404400204040e0a50742c15440c0c040108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 667060224 1250 667058974 667058989
    0x90705042c09010e0106080a0209010905090c09090d0f08012106230405010507051309110d0204170c01030204140d05030c0a2613060804060f020d1d0102070c06050315 73
    0xb03a031600700004960103064941400e48070a40c2203641d8543c0b101c0307013140068442017076443c11154070043c001659120030b81b0b401e0810404a110981c4004c0c04000e101350020003040211100190382ca41c94103d20400c0c80c00d07a0221004d11844440c6c000c50f043c1090941040078890304090b100b01c000040c1c409035080301100782c084400d48540345d0403000c400c000c1000390900ca090340100b0300f03042c16030400203080e8810240c07150b540580c10343c082d00c1d0803a0190742c0b8241000e50300c40001300301007503441daa1900340c0035107001070200d1011001d20a625070f990807540a0310071601502c001030061444554801c0500c1500081c840040342c06101c100560009503034140442440740e4440c003020304200c80607000140c010390340c610136043c109104111081088240c02c4c01c03441143d0103401d142e10f9680d0b440c02c09400074a0700e48040c001007400022041246c0c8413983c000f85900283c0381200f012651602c41e03c0c1e00300d015000e40242004000c141c14000c40780508003559000c8060000c5c42210a00b880104120 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 667061474 1250 667060224 667060231
    0x10050106210b030309060a020a020d0b070f080c09240c010902010f08070f081f0602060709091802010509120304090f0f0c0f0f0c0507080604060b090705042c 69
    0x1c1c0e00c00740400c0120071031051585801c40d088a007403160740d9400000a03100e10030011150304c11400010641c07a00b60081c0940c100b40c940040c00d010a282d20303420301c000078401c22248000090b0300c26125404080c011074455000d120401942030038881523405000f06d803c10055800040c045030802c000011400304011712044618000115140c881440094615000030002509200b8020108a0312950003040e00401c0c40c9903103090f001c2c544420488075426100d6840c1820861001d6001042590300000e94034011030031a9514818140c1d10104402290b0440c1c0700148251002c420b00c13400341d841240038046107000101000541c1e024081d003585907500507445440c03083e4880440c11603414592040c90003440c141402070040c3d038020040100415800403642c400d01c0320f08a088183c080c410b0a682040036400781c11209041e0b200ca458507a102001c440441e509030401c3c0091405040c40d80ca50b50045440307441d031034203081c1048000b00800526110300c0d0082c4061164003000e000c80e00642600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 667062724 1250 667061474 667061477
    0x32a08012312010903091a0f0304020409020d0c05190315240305062421011b0206060a0504021c0203071202042303010501060c0602030903130f09060f051e0310050106 73
    0x711840b05240151403045c1c02d61010180250a4a82c15503100307047c1c0c102c80401c50555141952540c03280b001500809180e00083d400041d11030440d41004840c1342d6060603104200c0b1000d19001001c4001c0346114103e000080201e02040340780380c18502c0540020011000c0480074810318200340e680003840c480036038820780d05648a0814040360115180e501d00c185464a44007840703090740800801c0700c1190401540c90711250000460840a0b4290b010305885410740001880000038000c00135a515820342da91403048824000c0043c0901e030a208540003ca01803080110030307000c0b88050402034100805800c10b0100d0b6888140840b2080c0c0300800c0070f441d0150100103506d030413090740c03001000368103020b500a038500b41c0180042904001e11506941c0c1c400c50159407030303403508043c9007140180d02d800800e10702e41041c04608114003d50000130340c1d1280c641000050350328180345601059034440c1540100d003c146004882e0f02c6e8000307040307903d0341c094215507400318145103280840313109074006030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 667063974 1250 667062724 667062731
    0x30207020d2109060509010e0f0102010b221103090c0904030504080a0305041503110d0f111201170a0c030f05011b090f0602010203090d080910050403032a0801231201 73
    0x540b02d58001c240c84002d4000e618100341004190b60000e000040c0700140325100310f000f81135058032a03100f5040362641c040081c00c402c0300303420758030140311601007200d0150100c2410701501076480d131340110a6070300c244082002416401d40c86014404242800b0340260104031042001140d0a2010004020100e200c0da0340d050761140303815a401400e1843d038a81c1c008041c01d0a030000c0940b10480d090350628424034000080d4240000c1389400100301e6011034241c0c0e4035010a20f00702040c1c004481d14121024011640303900076620042c2c94851010000003032010030b0304103080c004524408080400c05100340000503c001c5149000d19401c02c5540c030580004a0890050082e080c0950f0458021b0031140001d50542c2000381510740c40c1d0800d41e144104000e6504002481100c04000d95a4400302101041102d8202402c0050140c8902e96004c0322017082c01c055440c3c0c01c1c20307000e00000f00c040d03030b552040001e9080c080342c644004104206000d11401c00c06580545a0750038150f600c44031445030000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 667065224 1250 667063974 667064033
    0x30103020a0e061005090402040f08100c1112181f020c0303040b16020103060506040e1b03070e0907270512030405010206131722050306090d030207020d 67
    0x402841d003503402500d8500600ca080c411683c0740d240f542c194125590030090b88a0f507200b40030030300900031640000d40c1141e10712070000313110340003040304e1401c001c4450061042484090b42a9441e145180d620880d80c1c1c001181003a1482402c406042d011000e00e483c4171044041d040010105014000c85150345400e0342c20900b00244c0400166801c132a056000d10300749071078040b00010501500c51601520790031040e4107011a88607a202d40c1c0030f82001040703241c60b41d807110038070030805408a6171613038256644580006803101d0401502c0c8117403401e036140c00c0c0c10355034003040c8580140c02401701c405000c00c0910107071890000b416819041c02030020040140340c941010004038150030700c401001c1c1e410402007400f543c2d0b400704450358401040c95042c20408034504d0300f040700b0b0350426a2580b80800200d00440300c2c1820003a1081550140910030910b07644403420180ca40000780c840c1001684007111130084680030b5009000ca65000030191409107466845000040304000030410080340e5440c4031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 667066474 1250 667065224 667065229
    0x14030607020c0307030201030e0f0a08030f06030a0b011e03051e0105060901120209100e131202010c050a11010b040e010c090f050907081f0801021308060402090609041a040803010302 80
    0x103a00018a100074100c4071080c101194035420b9502000e41010344905000440c3c1e08204010341300541d00c1021103408895506000c1d0150f0800d9a0b00c0042400702c1c0085040d6150000d06440182e403ca034541c040381e40b03003800d00f08108103e801003058003c0c82800010100314103010681c0303520303410b05420010301c1c8810300203070031a0303001012a441642814014040401c0340d000c1c04000d158180d46100b140e445d411b07050340c10122203a2143c407241e400031040109800345e07036210350317411482140c01c0c88800190082c241d0a8138910a460400207900b030007005407851050860444005a5800024a0300120000310b019241841041641c9070746803c1e01580d502c1d84644820000c0c80d59142e00135115060200283e15410003409900c20401038101003003108850440500d00240a00301c40c5810381d41c0d601806010f504081a03041c0002c0064400041c020400319849101e11b90007085401c0690342c4004006038004094001d880c2c2e01241d0040203500c190500c10a8051070040307000f40c1d01c0b589035104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 667067724 1250 667066474 667066483
    0x21e0a02031f1112010b07051c020a0309090203240402040b0c060f0f100513022203120e01270312031a0409441206010201090c230a1403 60
    0x3030001c0f985040080440d05166103046a040d074155a010669414090a1036454000c0c1244000700703100c1d588045041c5035400286001000d4801c0d20398070305240d07070b42d64010101d000440e01c0115403ea04440250000008507417130080600040005003400d0712a01004540d0f0002d84800126600250900644152441005500000c007020001c85850304c010402901203603442268001c0d044014200c2c0c10304c00c035030142c81c52003070400b07882d00c188014400c0171f54202c5c0d4a4071050303e680e0010036090348402d2107100e84419101701038490314662105480700712110315100360714075501113041c8400b100003a60104030f443c2c0244076640c0440c0001c285080000b40c030008428a44c403e601e0680024000b40c00f540d40d0342942c001d0b6981801c4c0000c010f000c80c010807180c0c1e440d50381220301c10041c12a02d664145002e001800c1030a8407091999440e4070040e0308a030302c4800c016200030b800c2441005070540c80359056102815200c0d4810107408541c010403030450240e00b00010313560351040b04d040541400c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 667068974 1250 667067724 667067741
    0xf0f0609160302060a08060a05100201140609011511160b0408010c020a0215160501050702100e0d0c0f060608060705070302010b30070b070b090d020d021e0a02031f 72
    0x40341105100c0c590fa0000c2c28602c24100110203002e0700a00040c7c00e90744015440d8003c21002e0001a8400d403c1c0c40c0080c000c00c601203d090102000f500810b086042416945060f039800311084405c090000c40203880301c44c03115082c25518401c055400380d8401c0c0d0549000020b00000408548039410032041e1829103140c4220401150720102e903d45c056503550485440701c030034150500c1d03030b1547d244128070402d0894140181c090760808040c09001540021000c00d9803c00e150700704600850b498105449a06000103040001c0030b00d0407960204003400c140f035065500c03540000414940d54120b0070b05041c000c40d04003011800204560b8141902800382d1101c0c25001c035504680141e52601040d4803503000d4000b120100d4180f2900303500300008000d80d80182040304652a201d02040ca403000c8000412160030120b0b00079050507409482c000204050030380d9058000d840301185008200c8003100400307005502d50700c225003507080943c800744028011071011620103500040400340003c00d80d00d108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 667070224 1250 667068974 667069003
    0xe0a0b0103050d181203030b030708061005180703020a02151006090e06010c140a1502090a050d1509021804150e030f120c09060c060702071703030a05090f0f0609 71
    0xa451100003002801a54001e4400c050304010b01541c035811b0440081000701038060301885017240100c1c01c083c002441138070030500180507000141c0c0380c0c1d05001c0400060340c41201c44214010100707800714040d1700500200b854a02c12140c01e01207920b40b102c900207081d0ba40725844265038500b0320a26034024800b00103441a1100202c5600b40000001d207100b04490b4003900c002042c030078004481d0402c0c0302c2c03241c02980021050003400c268000010082d800340300c040b4807842e9001e600049a0a01c2a4040341d410b4020708141c036005070589210000e80745034001243e00a400007503000d00c0070b01d4400c0090180340509900c0726031280c3d001c00386007141c000000680c0554030612410a0203c03100d0110f0b86041a8080903171070035110301c11910424055903c082c0c0e80700502260f48a070701900020380324401c004a90844d28180c4e9203645004051049082c5082070390010800900460740e07542120b03402050740421620002d0400b02454101001c1c0f9140081607003149003407203c2c400c0104040f01d90078211 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 667071474 1250 667070224 667070237
    0x170313110901080a0b04142a0f0913060609050f0a3b03040e1825030204020a09171b06030907210f12200d050705010e0a0b0103050d 58
    0x400c600303659100404c050051807020a00001010072861142c43c0002a031901e045640000100401d01205040b081c41001c20141782e03561010307586051030f21100301910240012500e03413119801381e150ba800110055400e2900d400002582900b02d201d00f0740b1615000c8a42c03031450034088503c0017514a8a915014600c199468940000102c0c44082428610960101c4003030001b440805080d40940da00c0482460300007800c01a4941a4601207421010010207403401c1c003404459040070f42d4564202ca0704c0300c000340c036420320050403e42c2c004e04031200503040c015035003a65112880d44000148040c040660040025002129800c459003401404201c400d42d080d4580000310340d903141c189115102540032000103e0503615000040504001c0d00400040810300035400c229651003c03c0d04c102000602c2d0700300d41001e03e0807480c415407010400300042d004540040200b240c80703800c0081c040d00c96550b1400c2c600c100140c01c200f628029449001c50402d00e40c034508200b42090b40700000101804034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 667072724 1250 667071474 667071479
    0x50402120d14210c0c0d02060907051e041e0b040207050a02010507140312010f0e060d0305090103060b0403120f0f090302090712020d0605130621170313110901 70
    0x40007458540d000740c54980c0b198a51001c001481d4042041c440301c5400e8981c11000d0021044004d002442001c0040d811141031580c0c1080490741c0b00c000b114030240320b400c81d80040c0564036082c0001107000c588400107584078003030361000501b251084540d0b2201c1400d091510b0b4100e001d10300401c41c00d0041100e045040c0710a9484880e10341540e104020704100b400500c000c200a1a040310144ca10382520480c1c0c0c449000507004e50700b000c42070180b0100604076003000038042d0112112240f003040064082618000e80d654107442e190440c0300b1140c18180c5400d40032a100c01180c000c0c0000794050b951034226940014000313081406010600710410109000956180707030452441c00450f076042e01d02030302554034180f0848141c6245207016500030300018651000364151341004003500c0c002c40d00d050108904241890488009114051100c600d02007110703420407425004140088c0214149003c0300103044c02c40d42c1c5a8012217400d400c5c149510756a10501c40d510000c07101080050305c09940650 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 667073974 1250 667072724 667072727
    0x40c061701030b04051501120201020705042c010f02220b161e020d060515060a360b07030305010e2401020f330f0c0706140a050402120d 60
    0xc105000c040c0440b10300d0790125080110070800403103103c0420103284087d58440c80c0c20403d100c1001d106034010720802001113028a46407103011080f40088a5608241c0b980600141d000c115905411015540e01e10100c44400c01c1d0303000804440c0d9138503c1052400d290704031008841d0480d50009458090144245514502c0c4004850080c1e50040080c4101d00e001c031620200352822410300a40101c0480500381c1040700d00d802003406070030341d94000c0350720710007507c207100c3d150113100704c2c10700000c144062a00020600c060f42c0e4052240d2018240d0200c4454030103400100303c0707948030f172008880c0050345000f410303030622660303014003181c0b00e4000503801d100100f12a075003c0318110004526480c41240c01d6130703000f0000c0307840c01c90500e4185e680803180740c1a00389000d82416080c0041c18070341888201c041002c010707002e125400d02090300095485040f0f050500e0303000300404585c4c066480c1140300c0050855213501e031194040640102d580c2c605441401007000801042c07425507403190383c01500c1c0b01d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 667075224 1250 667073974 667074017
    0x90112050f070c0c030807080903210313020111060405150108010608030405060c030d050c030108010b0301092d060e070f0b07020d0204020a0912080c01051006021f02120f040c06 78
    0x26240c43c1a05003c4030030b040c002c0c540700b490791006020440004103401040400700c050005407201720243c803640404600b5048000e81c03402e06065110b8801c00c0041e04450f99006000d88080c01890301000100c01c800442e8900303203064070301343d4255001003802e0b09109800303441c89014214010003806a02d02e00b50700c003070f520b0155000e564810500450000d0306d80004205942c1c4c82524440c0034025814000c00310140780c2e100f070188901715402d1410b401c070142014014542035961055440c046040840b1810801013248078034100d5040180c04d95001280c000c0c001c07022505007290103011124070b0304020510103800740d80a8141e5940900494000d0398480840100068060342e002d17039038014111040b2061a9181c0107107250290902400040c00103840140000c801e101b0000c12041e210494409076a945900c0f800d00141e0190109004004e1020111012108060809400c02d044090751095176801151404a132001100400c820720640710703003200092000c0c1c01d0681e01403c50071581c1c2d048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 667076474 1250 667075224 667075231
    0xe180f07091e02030403030603050d05070c0e06030f100203010e060a0501050a030e030d020408010207050c010810060509010e1e030d030c0203160f0b07050d0b040203070801030b040c050a060203090112050f 90
    0xc40c1da40d280b0300c03a6a1000500808050114000856480ca018600a001040b071070100b07071842e224104034103903046d0140040b909081c0d04003000c1d0300c0483c5091811621000002c0a01d80c2500034041e40b172014810400c180300b9101b481c91030160312076041081c00c85082d00c1c01400d89100c0c5024940801583c0d800804845031000e8514000c1910078894240340d02d14410109024511840054001010310b41940036140240c40340c0e054aa00b40c1c2e102004480701071003610020885e0104400822007640182c005001800060500d141d054005200162035004040200c0003045d0800b03214890500c1c00b8402e030761510b452400c1c2008821503454009503640509800d80345100740e804603040c20f200380800b50818460348004c04600074501070700028030325008000850340301c60406409200d1490235000340e80c80385280341d03a00c0100360700c0c640311075040150150041d520740d02a018041000e440c0d96080750094080750f0000c6946881c1c2500060082c140000960140b0b0b14010a2010340320944190641 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 667077724 1250 667076474 667076489
    0x51612030c060b1002010e0601090b06121906030c03120309030e240c0c0a0f0e041709030111030133050703020709020a1d120705190305070e180f07 65
    0x201600a071810b00300030903039210744943c48420001c000380b806505400c0031a040540d40c041d40d025903a036080305415500b040c1c0005a00a1f03040c010a00c0382c808040c0c0441d0300812215031030140d24a8180e80408071200c64009660400c480c4006000f4400c0d083da031109000c030245002c002c400405c0c1c40c001c1c0003174401c0d1441e178890350141e034803c1c1044d0440e1180300f2400305164801951026000100c65031490740480c140e015554600380051289600b040c0501252040c0c150005995102e0f039601580d440700ca030400401d01401d00528500ea102442890b14024070341e852140d513541440004801074447d0400650780c2412800318a41100c407072549250850214286141caa405030b20b010390520f000c42e0005896188041207490a0a61283c000003414800c4d601c00b00310002e9880c14024041c0c889101200581d2107041c040110b820540e050b200300c60b9904118200c040d4890350b5460500c1c500f540426000c10201d0188940074000710301a4400101081c010303c510183c0e5514039031640000d119542 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 667078974 1250 667077724 667077737
    0x103032a4d150d0c2304090c03110c070315090819030209060d0504021525050705060f04031106040806180703060c0c0c060503191107060c0c05161203 66
    0x4110b80c90300c0601c2545290074000854580303020402d0781000744151000300000402e200c410741304400c0030b03100c08109030002c41600d41c03500341402030142c00342440d640c12a081564403407048500612920103001c0c0e00301071001900c00c05165041c8481c4822520311035881441c43e20f108440007409440c12a40e0701c00c40c0050011960ba4240015402401442200c07078101500103000c0034041101d81c0128860b910071102043c031120f44002000c994003d0b050003c0a081c4800004000c901c840004c003852280700d48104d80b801c41e02c8030085115500041030001c2c01c6003000c1000e0007080007400c0c1001110b0429138a15013001d00e04180d4030707513448024010403443c54030b550b52021020340038811301001c1c5070011b00c00d000d17a4206110041c400344220308292a8014110000700381203200e1f004990040d81100c505800483d055080f5500174a076050109002c0b000401007000040c4d1607001b00d1a607429543c90390300f409025401c0103402c010500d60083c160720070302c0360103000700c039401c1c05040324482d01464001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 667080224 1250 667078974 667079123
    0x1802130b0612090c0a2d1511100603080403170315220f0209040b0303130b0307030e0a0c14040c0914030f01050f04051501052b060f0209040e01050f0103032a 69
    0x2302c0c249004240140c1d01c0b28180b800100c148848a80208202d80c81045168000d0300b5010104660703000550f01c4141d0522450350b2076045180001c0307440504901d28241c08960031040c0c41e0345044540c0c90700ca005400d034021075030901901e024402d03034520794006d6020710301c2c1c16001e41680184c100e081c040c81068600200100d84018820343c05641860b0240c01154010f034101e0070860a170170340d9881090040071990486510754189801610f82c404880e071681c007482410301008480d0005407a400540505c00c41c0f01d07280d0501c2013400340c50701640e034211422a5a040c44c0c140705081c20981c05542a0040c0c010004111b1030b25040c2c444d0342017a00343c01c22110140c0041c100c0c102007000b40c140c007400c40c504140105035034401541c004c0020a00840c0d023089001745c0d02041c14240c40c000c548001d074a0383c8100040000c00d010308911070341140c2100006001e90030182140e00c4080f5440c500359038424070b161901c80c0002141c2180900c452102c480741c006e090000d10b0504141c6043d4414007454000e80101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 667081474 1250 667080224 667080257
    0x70f0e06040b070b090307051609050105010e090406020a03111206031510120206040902030a060509180c09150d030f18270e011802130b0612090c0a2d15 67
    0x1e91b41d000748d00c181611450401d00c3e050751404103842c02400c80c1d42b440c0c640005000d40c01040c55040c400c4019140c03e02d181e03501d8507820000d402c41000d400c145511a1004100b41c00141d004040304151803810034040e06001c4103040c50000120440c0901c900c0100502480311a011486401c807004c042c2011450103044c40071601e1400b89501c01d80001d070010050240244550f004001034074001c1d600c4009070f507107040c41d0050715001c00302c0c070301e5964000104000c20340c00c001610a40c0020701c500005440802d110104095181c03800b029800194002140800c441d4001080745e59484000b043c60840d0341040ce000b504040303103da024900b500b5400094055143ca508500550070107031000300100d040d2000c03106c50300b90300688224840c140408021400590500c00c5400e10b1741d01411050030320080c10300481c521107024040c2c0400340b1551001000c156910130b60709021384000310302d000910350300ad6142e0b48205800d5140c01c2004101550501400a0981104080905514000950a03055020f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 667082724 1250 667081474 667081477
    0x1803020615030c040e0f0c030309010c02042f1b03070c061808120703030b040e120d0207060f02071202060105100c08040f0f03050708010b01121112070f0e06040b070b0903 75
    0x9a082e0814200380400c1181080400c1611b83c01c1c4209040e9034201c50a5400c1640760701c200d070312007130100f107c0c01a80005414240d116200d00c001c0c0225240d045042c0002c0c06515044414000c0d00e82e4200055800c00110200d41d8855041c0264000b0350502d14240d0716404094001e01841041000c40580700404030b103103d00e410001c1c94580283d40590b0201142c03607085900c411019404a4240600701c030417400c1c80d110309050380e142400a00300065003034000764807e6124010b943d9040e5000e1188201041075881800000c10348007000690f2030b025458001d4a155400d0181815904010010003254a8064241445000c2480c1618004070946404c04260040ea082549861014000401c0c1e0b210300c00740d0302d005c0c2da0007402110300b40e981d00c0e0100760a9881c2c08000c2c50009030300010b070483e841525006280c1451001050b682041c0c00800307080000c1d0070440c0c22600084103071040c40003054000c007025424110968079989007078100342c102d50603449aa02c00401c0072440c0d00000c4c400850610 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 667083974 1250 667082724 667082743
    0x16030c06050c1e1b011125030506090703030e0609090a0506030102120f040318060c4e021b0603091908040806060a0510033c180302061503 61
    0x1c021045400801e03030540e54505001c02100d100c488454130358005503000e035205103a1210500001c12403074868010040700d000500b05c0041c46901404000320014000b4400c09201d600c00500401f04140303507080080c14603010801d02c9009000c1003051107415182d21020b87d80c045445540410546c907100d021a009100d41c0c00c10b80c1041212f0418444014120701c0454051800380d5030340b001c1d40c04a00744101a99076688100300c003044114112500161302c0107588841d0103aa003050701000181c101427610181c2d1411840c2c1041c5c0c08181b51461f02040e401d6140396100c11510007402c003901c05914000001100320002d40c801d91012002541002c4100040880c0d4900340c04103880c1450945032a807540d4103c0e0052103080c0c010000050403a08116840008a0304000d02d165450b124005058004100401c00c8a0f40740c0050f80c00d141c1c11440c1d03e00d507141c82602e0083d8114005075804d4031503040b03450751014881448050300303101c00417940c002089500000c0c1030701d00015444400c0700085c640903961 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 667085224 1250 667083974 667084003
    0x30815060d02090f04051e0a0906110c010c020d021f06031202100f090308061e06040f09050901090f0b0a06081e1606020d050a0e06040905010816030c06050c 69
    0x920600d15032400d402402d00c3c1c00702581d18908030b661030380c10082a00c10032103000c4e203a49468445040000340d49108a070700302581803000035000901d52107100503940c2124508e00300c06000a04540b503401c0034410402e09801d180f000d8040d04a240030029280c0c0200e00da59105504122001030480c03647e80d20150044d40c5c00501056400d0b41400081e484100825860b001c19190a0465450150601a46080603496a40c3d8001070391000100314005c80c0b401450104500c40c091804250b4541c00004e0001c0c000c43c0700c0340702449103060119170035240b00500c1800c1f10703410240e203c00094004c0250440f1301c1d600c1602e092032903543c440100c00a111950000304503204001c3c403c0702d01d51100507503128503592401a228100301d501852040c0b46294442c40b80140e02c200c09100021348580081c0005e40710034a018189030b2600030000303100e90441d422820425540d5001008a80810082281c0c0c1c0820a09440310742455900c8180071846548a4002402400203800030500400c2c071840c010f0b401817 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 667086330 1106 667085224 667085227
    0x309010507120c140319020f030301090c0c060603110406080606090a0c020106030f0506010816061409040b04020c0c040e1f09030c080309010c030f06030302030703081506 75
    0x84403209040083c10000440000c1c19208103a5180454400858494102c60340d00d000310540e03041d4810a641c00b100c48445910b01c0807055030304441460380700240d0300014980a9515048054000b840c282c40c00001008028500f00d6201c00b030030069808105003034498000c15500d150a42c1c1c40c56110401d240080c51300c6020390085101e00c0030520020903d00d40c0c90f40c4007010b103000448100c03003507089000140b1205104001ca504021480714030080d80900d0504090900032401e940c0038030100d40002e40910b692115009182d0505001d84119940c181c000740d000d84440b0100c00182c451820b007031085442c1c1100041d0700f410612403155000740c042410841c1802800305100032010302c0001c440b64408a6070f12005184100c40000c001709411400702c10007402c4501403a941c024552030201c003400800c3d03000081d540210760500b07003004207444d9114414551603000104c1607000340c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 666906474 667086330 := by
  have h0 := BRFrame.cov_init 666906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 666906474 ≤ n) (h2 : n < 667086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
