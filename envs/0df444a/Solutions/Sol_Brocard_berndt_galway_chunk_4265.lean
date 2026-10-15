-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4265
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:03:23.875765+00:00
-- url     : https://prove2.me/submissions/ff66fba3-a78a-4c84-a1fa-a4d2d72f24af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 766906474 ≤ n < 767086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 766907724 1250 766906474 766906487
    0x3040b070c0f03081501030606170903070b010603020d0b0103050408090d02030c0607030509180105061603091203051903050118090f0b090d020f0706050d0c02070306020a050703090f15 81
    0x108000c1c04119045200010740c0d110309030b03504078400e460b000d50354104200140070310100d00c103481c1c1c1818681002408802c0d004000c14100700d582c00000803a42c1e848204480c00c50146000041415011030000304440303805402600c59403001702c80c01c01042c62444011000d5400544000d0940c04041042c10b07400c1c10465030252030903001070b04450035103080c040800d40c150b1241300103074006140407a064034989013a8a20042c294841c0200f000705504007800200030748202013100020b40314000204082501401c0800010100000c12001d8100d99080181a0b94442ca9504500d00c03299124402218000d208040c1618000c0d2080310f41003140d111202c0052500300000d483c0d0a103443c0c480303000603041c114160f108644440180050400018000c2d18010303103641c21107403981001c481030260650090a07075003860907030440413801c0b080e0000107a0a0456039000070382481d0000400c0c280d0a900400107120a900c030741c0e03c5004881e9907da084174210168001d1004082020402c540000e12511 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 766908974 1250 766907724 766907731
    0x7080708060406271401030c060f02070f0303080603010516140f0d090804050a09050f2e03060e0d050304080a1824200705040510090f0b040b1503040b 66
    0x180005100c0c0d0701c0d1519114800f07000344801007005160f5418003000c40744c0340610080c00800c9164102036505540c0c0d603d000821502940040007d2240d052103480c0c420040603008220034450201100e4482c01c000b020802d044441c1e43c0650b0810000c07902b0b10b5140c92104103180b200d99220680d00c000d080302d40c1c003590300a111005615605002d401c00d1080a03128a03451b140c810002107540f6450301051001e00c02c62540207510756840c1c00704200c0d450a8041d0b5140d030203803003801c03484408030032180601c2c624070701c03008202e0910b410540d000c010000e072035100301401a480c40c1150040d50035a0411200c034841124014200a07040c80b0442c2c100e4000d1304800c0c0365040c03492040300446c0c0c07512400040400c041c00c0c032907187d1401d01e05000c0440c3e0041c0d0424040b0440118450344644071480d41c0740d585640d403180c640103680d508000b48090521050210242080c03000c20710140140e240c1d40409003681c150003a204074540401c0f00a54a8070045101c0042001c640d440c0c156a91602c03503160300c1300c004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 766910224 1250 766908974 766908979
    0xb1614030a3e0604060e03040305061f0819060e0d0e190b0a1d15180f04020c160611060403030b030109080a1101060b0f0f09030109020a0806070e04050708070806 71
    0x210100301c1400500301e49000d484950b44000e09003403500b420301c1810f980c9400101c1c45035410030130040c00450f03000304109500104152981c00c0000c0e446482d0109051603911000b0580200e04845103000d40070801b04034298020041486000c80c00ba0b1140e88036840d003644180821080c60361700c00542130088803541c54a040c0740111900310341d1102120b80c0c55010100c030f100000c2180c01180301d505811003d0780307994441541e5804032035094580c4441d25114245c111070180002c01803603002c0703650301d000c1504e2400010300255124800d00b00e0f00c999800042d1740a51441054003000f090a07446440b5552207801c150340100305680b01c540f8180e0042c402c5501158255480e006440f002c940c40700014000b003102da80d2010401c00581050900315045608880e621600c100b0035441c000c0025400c0d80c1d06039a00c128400d03aa4400307034002070b005150243d0000e4001c04545030009210304081132040c4aa8002d4540203c2020743c102000110789007115a003000c42da152012601c070f144184030003507010303901 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 766911474 1250 766910224 766910297
    0x1119060f030906092a0902130611161d01080607081906030f2924060909010e011805040b040f0201020c150a030c030213140a0b1614030a 60
    0x180e21009085c4203945504994107504514070402d101881c0d409000a10083c0070850a0800c03003440e050300144244599030805c03000008050040da404d00603503c419611071054020a0b66505030700c00e50210984080d040c1800540001510402c0400c0da80c2c07080350b159641a900b5030b00ca0021a20484c4103041061009135104004400280145c4411700e03958011004034862200b0120f400a0300003a0103411001c409100c401c4c000d520001c00b05a185603440c007030030402c11182020108035a40500b0104c0ba0b400b9040c080005080009500720605981c646d19a8030110301008080130f003911010b80b40100520701c1e0070002800704110100601c0554414810740c1c090344000d000103050380524145444103031900040c0b000d40140c262048040c0d01c0805c3c1030650500e03c3c054082d04000c51203114174a400d00ca4100d25209a948196145002d8001003003e80d881c6c480400e5001280d0005c6d003801c640c1c540340a0107080005500009540300300340180e49a56126180190602c0d4520301c1e00804004c41c1003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 766912724 1250 766911474 766911491
    0xb0103060f03064101090b030706030c02120d1a030303071b060b030f060601020f30070807050309011202271306030506040c06082e0906031119060f030906 68
    0x1a8001c09560080139180c1d008044840280d400303002c0c1c40c042e4451441c1a10f8210707011200e8402141c41400c0368801e00f40080e0618442c030301079007884040010a840d4907400a6100c0e040a482c1d4040c0e00607995406038400c00003514030505941c0c2c072041c1e075080c0224030303601d0810f020082e030040703500b034282c0c8100000b00e402d42c4001d000c01d00d0b1460501e0140050340000c402c010b919641041503002c10103540e4000c08201d01104c0d140c40e1900d1400088a4000603116200c01039140300c0e1049400e0035074442c0100d81e9842039400c003140c503500400c0e201400a18070303215a01044190f4000ea91030569612103442c40506400d00d2541015000781000341c00c95060351410a05955a2003000c1c01075000307801601040c501890246507a03850364110300144218481400500b01d403003142042038411030324400d1240e18110980003640c0754198440040d141c2800401300401c401405144507503002507031b00009002c0d20000f1070380f007443c40e4000d01c00003c0d40d5001d114125403103034025403c11801121700161551 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 766913974 1250 766912724 766912781
    0x11e110f030103080d29040203090c030601060c0c0605040b0901030903030f0f0204030b0105090c09190323010e0a03121e0c170a23060111061006030b0103060f0306 72
    0x20801d0f801950302072404070701154400034a020b40b01c01c03100000c0c0300c81282c820884001c40c0f602c103500025806a6030100004800d008204901e28010034010200c454a42c0c0d5104001c01000310020308851281e81c44500107903207070088060310300b41c03901c0f250840d00340754255004500a1400b0703e41a800c05848510945504510388031340c00c50200b50f110301507902d504604081101402c10791003075018481200411041c614441c040c3e40800400302c40c41503407022400102610518107400181980300699181c000c0391018000d03140850740400000c2c84545220700206450f1211240064081440030940f00c09001c3c16a0250303d15002800301548003000c0c45068004440c0900141000318000e6904001a80280e000580c0d01c01c5142e42d00344500c11081c482e07040e646100c080002c11250714040072405a0303000d1071807a02e031001100d0484101d4506180c90344aa0b441da03200d07410100349001c03180320441d4481d008040c00d030365810740c1c59540366240d5541d4200514030444140c0880004500e01c80020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 766915224 1250 766913974 766913977
    0x31605010204090c0203070b0c0f22050a080a1205031906081501170307060504030c0f0b04020a06230d0b060a0e1e030c1e040c120e011e110f 62
    0x11402100016100c504140c03000e000c64111035591410365006001c0d64001a00c22174100b0350141812403003036207518030041d11400724091510305030041c9102140b0b514101c4000c1c060030044442c01c441284800e07648031045915a008000c000d0000c00d4044000c01c481800340000f5a00300e0542001050b0440d0800c10f100c007100c005400030341c46c0f900448030480c0f4038000c0c0411a409094140b0100c40c00b145140c9540340d5034440c1a1000300003680b0b9a0000c2c0502d802194400a4507802880318500300800380b800900040e4100c5040b0701c910000c62002c20641d01c9260380c014618501c0e005445180d600806d101d0241c1c04c11a80400660b807a015070710100e80390351020f4417510420703448a201980000c820812007c4070b510500c94404d041101840b11603800040c0b4605100702540c0d4031354a26820051400d08a1000c0c0c0d80f241c00900b054141c131a030350f03031000f800c0c0110744c0100d90030400508206013980c02e0f103040d0b001c1c00ba0018104294a024151075511081310b05080d046e43d189845441072041925 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 766916474 1250 766915224 766915267
    0xf010e0d0c03050d050a0203070609060b18040507061416020f04150801050108031305131506020f0114040b0f18060a1a03070e0112080f0414180103030909090503 71
    0x5144a200701041040410403880c0c2e03500c00141001802d0501b0a00029501d00495002405280d2644004010300039240d1081d00c4660340540520415000031074020403003503050300c04483e240b01d060000952240f29021300b48010f560319894514115240207006104c110002c01a0f0f4041c81c1c184420915a9491041c3c402481844945410152406070340600b100c1c030503403010b200c5401c1080000709140c407a21100042d90f0040b42ca0090991055032128010140b18240c2a4210303846000130410700d80000d12100741c0f81d0342c00020310001c0580f00003402d2045041d80c4c010104804640410016821080d50f15400100303480e02c2e455180d0f40f441c4d000d250810541d0b1080e580c50b50b0307260556403150002500d0030840b50680043c03646038079001d42d803222200e051207480000b4141e880136901308540039086610408440d444184c03200d80f11181c2c00c0343c09000202031881800300700d0310354540c940c544a4280c12281c00d40c546002207468044680c01a211140c01100d182c042004003220205560140c1410f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 766917724 1250 766916474 766916483
    0x11040e0702060f06100e03010207030206070f0503100e0a2408070906050a0509130804030309050909010207150f18050304062c0d0303022812151403030c060f0a110f03060f010e0d 78
    0x40500f80080e0142400c82033f400c0c14400c00c44104200305021024042c08000c8035072000024516a5803007000100030000006030312640081c030525030351805040c103000c20aa030307c82c0e42074811465032600150111149485013980103122250304200502d80202d40f04d6101e106400e0800342892030b0394840b01654407641084000c2204004140054186040103552002445008626140399510b0303184042e0184800f15201c02d44400108003440e2071604040345002203803c01b00c10b020204d00c0c1c12922a00a401400d00148683c0030a4004902c0e00340c1d015940c050a40040803103a001000b03100d60203425102c180d041c190200300b01a01c100002c204000490b00d0209440015049810002c103104810040604c1d42030800154025980c0312180c1002261810b400f50f00d03411142001190841c010407904201c540502d02c100701607d030301d08000c107105800700c1c4000c01560305500d4508010307000b020316a0702d02c00c0080c4002445400c0c4a4855800400141404030424040f140043d00000e0301340c10498 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 766918974 1250 766917724 766917733
    0x7051c0219030e030d1d011103090c0f010f1803120806091602072706061809090c09020d06051011060f0c09130e0111040e0702060f06100e030102070302 67
    0x250100005011548081034915090104003d45006203580780540c107140c0c00290f43d28600728003c5c814502856410b0390701400241708460302c000249069404c00c50341500e082c02908070300c041c1403800b9000d42c08841701c140c6440b47c40903070120084480b0340200303800d02c078000e112660100100c5c80d448420542e500c125615070406191103010f1025400c07019001a1040b280c1d0070740141e120307401240c41401e841d5202010495074082d40401701100c201040341075041031901a010501d2640242590502034680b003020a586542d40703010421505030050140050300080003e01040c0000d400804a006076400b01290894480340040c0c068002c01c0d8044011500038801080f0700f180038081203070302c4010408071181e40e2034003000034140c0f403041850b034501c07a175151107186c0254011507000c42d44410700700000b0040f6034491141240c00d58024069942d085a2080c0016102480090014030070820b4494990b000d484580503c803111504440001c1405103042c1404050b440c240701070241d25000783d0082 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 766920224 1250 766918974 766918987
    0x20d020406032901032c0106030203060915011203020313081b0411041509080d05130b0a09061809090602070c050a3b09010c0305060307180507051c02 66
    0xb074200c0c1c0626440c0300451034545003002c0c200e0200b600d5400c0f04502800c0200d0310410003001d42c1800075151012100304150f00e00030b000c2e034020550150043e83c1c400e800f02d80c1151207824246070340f03107008840d00c080040c695006000c07085201e915501040d209004480c20281d111021381005405600100a2170b801180359066011101d07060040358030091320100405c50103070100c0c2c1224031480c010110000d40204445c00103d00c1082d41400402b58582980e00240c0c00c414020b0140c1d1184030070703e00480c440350300450210798075012128132560645440050318600041500d00b003a50146000500502d2540054030340302c20701a042e136581c410000180d0f0340081d0300c0c101d1010f51481c1c0002e802296000303410f1003610f2403c88441a150008100d9221110b0b00944410740c2c0d060407040410034248903400d00c83c2c645015003003c003020f00103440c103004694442c0d0038513071380b01294410401740d0b03d0019405540700031298089501303c0358900d0600d01e41048000f000b0b4074002c001001c40c0710ba030383c0015807 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 766921474 1250 766920224 766920227
    0xf0c0f030903020a02060a1107170105060117041b2303070e040512031003020a0b0306040b03010c050f0319022b020901121a03061306061703040303080c0409020d020406 74
    0xa0120890103040030480145642c40003541c070140b041c0000d000364000600d20701c2c0e07140241412250900b00c01c08444001ba01e400d080000d0407040d00d0480c10540c2000c0c0481c03071a40c000e5070002d40c442043d100c411500c0c0d8941c1c44014400c00c05c1d580018002c2104000803907980c0400044000c0020114020118484200c040c140b501415071301c080c500040384002e1100085011600002100c3c4241c041c5850f503c52185103a410320940c2d1000350300040c0c0e024006000102d1030050751007000115070411202094400341400e88480b00000400103004210aa5040000d80c018580002010311000d6202d0f90090010040381d00c0080c940c51010464941903a05003074081c200c260380c100026081d81080c04000010742203c040140805000362590400c40c130310600450440310100c4000c040701e0031070400302112490061f0552003661032078280740020482c4520381c80304030903070140000110315041c510740b0201e0740954064410041840c04001c005034401c1e180c005413601a0f001140169114039200c030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 766922724 1250 766921474 766921487
    0xb04090c091d01060b09131b0c03030e070602071502101d060a02040503071404090f0b0a0b010e030a02091003050d200a0f0b0702010908040b0c01110f04050f130f0c 72
    0x520032040c1e040132000d001008480c070507a544003109441c40120f032180718008070040c001506154a10343c1c83c8010b96030b142584001103e030300174003c0c0c408100d00e0100c42c01381902d9001b50301410b0090303031108908000b40b14000d641181a1112441541e0313180d4007240c0740030160740d4904c41022040d45283c4151104c4403044c0401600000d007c2c40031480c2902d041c02180d111009445034800700000c8000d08031968a490700210b210b10b50000003200c103c0ca0318504400380d0301054415401d100d03c0c100c190809540a0400340700b03079040c000d0084c0440d1004d039003000b24000700103015040c0c81c04008000030002d10200f12070703a5010400e4441c0f40c0780e040d0300c028640c01d040f00c440f40c1054a0340b02800740000314000400440303066401c800c00900c80c0da5002001e0380900301521000b80000000640010a400041c018060260f0140b009104010b10314626032814090040c481c840e408081000304003616000180c4c0409540141c50561122181c5c1101c400b15030312081c1048001e61609003110b181c544c840c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 766923974 1250 766922724 766922771
    0x10e01140c0c0601120c0801140702070b09090105041d060403110c010305070824030d0e040c0302030613090201021f140903040b0703181707061706130b04090c09 71
    0x80740e4600300020840007560320401032160000c248505840da0b014400e04500090190032080001c1c803805c03012015850302d24604603407401c014003420b0804aa199a8441121b5660f01c00401d444043c0c4d080c81c003000001c02540150242d200032154440c1d150340400c0c01800d1046010b5250b407402500049940342c100248958041e040510342001c022605403c441e00076002104d004d40481d0304507184182041104141520a41c140700d14036165801e180c0c0401070440c1158203035404e0041d03021b81e04080d000d0b40000d0303d40319030000054001c20740e01e5096074045030301c0354014030407241080e003114086010b02e006c10201c80700703a503101e00e621180f413030565140640150f80b580c000d500e41403030a03071120400e0050070700040c20050450303240100140141040070180c84522706071580000d68102c000d940c0c80b210300c130302d0010400300801c000c13001c180c051103140b286002420b80300741c1c81d0041c2c00305001003144080c010b43c400d5591118030042460255504041e05241c040010702c0003058591060100160 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 766925224 1250 766923974 766923991
    0xf03080f010506090105120603010b030f070504240b2503030e152202150a0c0c0b0c0d0309061d0303100b09062208100f0e03070302060714070203010e0114 68
    0x40007032075100d0b6401000c441f20b841404c814581c4946420000a0141c4603c45140307034140b050242c1c179414607078041041012038100711f8003003055500002840380f5110b6244803145d40d001444400704100009040200b148481015074080d0a01e806c08000002800018013900020303550f03c03080e61118410400c4510b0001e41500d280c02c03603c1c01180850244100c296005061001c00c04060215101d8070b8100c800304005404094640402030700003408641c0c82e02050320102d881150000d4166040d008a54a00d100b00c000390903c400c1604044d8054010341200f11405e541d5494030310b60600842c9242c034096801500a1035481c2000f80350403440705003a81100010290401000c1e4866454500700c0d007004e41280c80f0b880c1e0041491214544001951340f0041c10346c0034242010500d04040c0e0b20801c088658101c0070800801c844026a030340c1c0c041d01c0d400801503800301000c691210f014011030a84060400303003441c81e00345142c2c046400d544a00f14543c145039151000c05500481d0240907d40c000b041c0e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 766926474 1250 766925224 766925227
    0x50a150608091b0613030b0f1f0e34020d21050402010207050d260403020907110c0604060c11041e0507021507111509031e070f03080f010506 62
    0x1c1040c10f481d80c1c00e42c948090b48011070310b0303100401d40750034003070300d00e03c3c005610b20524240c0c0e40e09101c48819000c503a045a140716407400075000d8000320b02d006041038604801c064003e030a01002880300580074144081c030742044444c071311004108041c0d40c40120b00e40d04059500468481000c3e1405043c4d40182e4280130b106011510016000d808069105036500c0740440c46444900060b820519140c205640102c01900c1d08824841070755070300780d0b40042030740c903061046050300000e540f207029902000354002c0c11072000c200035034414014090051001425941c00003040c20000300d480e031142d0b20440102d01d508403240c05010a14500e00b03c080026601440042d903041400c0390a04c8070041d80a82c820f948002054000c0e100700b00d414554040329801440509254401a03e4110590310030002d07446420034040003080006403039030068002c0802141040892038101403d03005078a800c41d500d14080c019003001ca582101e000485a0080d169a41d0380e081c1001d460402e000160007070b40c01040c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 766927724 1250 766926474 766926481
    0xf140a061d1e0a1e0e06010f0c020414190e0307020a030201081306050c040302090615030703110f070614010611070303030507031b05030106030e0c0f0f13050a150608 73
    0x209030040c034030a104120381c1e441800455404442c5001d8001d12502e41002001d94003080b240501e510140d40c00c00b0300d014001c10b2564554074030000c03000c200d40d120b000400c000d907401c64160083c810407150394030060000c40e128480c1803550560600c11100c4000c20414070300a81d018003030034440d40c0003886c800390166145c03100f00c2d0041403083c101d83c84000c6c100010400010f0300000c0586503052031551240d03082c481400c2501125070960003900080c0e1282c04600c0c0454954541a840114404086070065007144d4506400ba00285104548501043c2c0c04010300400c41035498000d000b1148541400100700780c10780705107921700c4e00c140c100600788400c00d040d204602c03200242c820120b9500d071070f01082603038a9100443c003070402500c150202c3d682c0220f50501494200c0c000c0c5060790f14941d01002400c080c100c25030741da50103a10700107030001c00c1012114510308092107090714140020b04420b01c000b0115540d882100e070f045595812595482c030f9500011425038003204000c3c0b1061a21404606 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 766928974 1250 766927724 766927757
    0x1b0a050901051203040801020f07060627020f09060d050a0513170d110703030b030c01030213090203061f03200a02030a080a0e0f03030a06170607030e070f140a06 71
    0x1503040c010103200c0d14544940389148281001101c01070038080000703544520740211790116940200784111021420f280000c1010380c140400f040e03100d0495207070701c1102d140030025000254402c034984696054104541422030725510000c1021200e050000103213450000c5d20300c1704a55000d800710740d041f1340c080c00d08004610384012030701b8440d0f13100a00e5a525443d0100c248000c11503000d03e044000ca01141c840245078040d8031010228105074142c69404503c00e004604a1261102d80a50480c02003424001070305540e01856020b48082c0c800c40440c030480c28100d03004000608180002919541202300094118144152044c0b0b01002c0e00c1c200207c081d070182d101d000e22240e50040000b11070000d102c20b440b41d00305903a00030750181620114400c2898103900c0740d000b182c0344121a400d0160000c0d40c4080c10b140ca02c26040d0b100c000e00030716194400200c025003130300007808000c1e10540801243e101d1444030040024030107044804e800e9440c201c01d02081a409501200c00c0c41800e0000d800c040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 766930224 1250 766928974 766928989
    0x9050306010806091c1701090905010e240a0902040e03070c0e070e040c1e020106140a0e04080310090507050301050f010306061b170301080d02120702010c061d0f1b0a05 74
    0xa00145c030b64078940c0c800c658204c1c2c604140c1c000c0354034036850b070100002e40c90081e9070004040743c1c0620700a011111061240366900c07059001c0041c100016130003d880128018028103402800923500460340540c0c83d0002000c0d04c0d00c004090b07005820001e0104100042505c2c410010720b4107088105942c070b01a01d018042c621000042401203441d081c80c400082d02c01c207846504102508000140e103030408100038000c014600a101d0a40050038141c01d05140c203440740011035140e2810344500da41c4943d141d00300340c1c10141000c0c0d05c80704101c07400700b04209940210f510560103543d41c0c039100e6251030108000281034103a03040c149494007400380000d41d80f2440b1003505180c0c04c1c01413111141c0d01d1a222a01c0700000214a041304004400800d043c01c0100e0510380c1040c0075170032038032418004004400310313111300c0100902207494141000001400340e0010710000101c1403c0d56207903000b0708107150416960411440194103d26800a4030000da10f107004e5484c10141d414650103410b29003c1000d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 766931474 1250 766930224 766930243
    0x1b070608040605040510050c180102060603101805032d07020f12030c030d060602060f19050403090b0c0a0201031506020a1b0f060801051f020c10050c0d0905030601080609 75
    0x520f03458400103028018100311103090030480707540410491801544e408a213404c9505800305108480f5000301981d03100041c0c2c00d0282c4401800b400c800541107a42100400e5894440d200c618000801e100124009201800306261034040741d03190611140c603030881d101035410014000040500012016172502e01c59521407039801c1c2c41e1070114010400c030b06c91035402141c11200c4a4800060b01862101d0703680c0251040b03034015021100c1c11b480e40e40811920500440e03500a141b20300442c0240d00302c0a0390407044d00302d40a410803c2c1c03600c0c0c40e844e1549096008072610380b4554080103107a000c550b8548035005c170709000395000c0c003580c40c14448025181c8009602c082c05041040400180f00e441100f40c10004002c245c010340314840d6140c0024100100920499205003811f2018108040c59040d184000f986168094018080c1c01c0c020030144503c4090b45804204003804946d030000c00401070103d840180c0d460700c0310b10134035000401d03242c912f0503007000010340c010380284401c40f0000112b0100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 766932724 1250 766931474 766931483
    0x130314041d0903040f090b09060306160e010917010209031b0a090518010c020f0d0e010f050c0a050601260106140607080d0903030218010905060406180801050c1b07060804 75
    0x290761a5035840310700e14002c582140301805200c400c00520980c21f98450703403c14100f6241031a00f940c45200b0584c0780e40e030031609903421000b01c0811203c001d00c5244841d2044005040a00009486c1d000c103440d04d1500001e040716503940000c181d000f40c5810008400500c0d10304004036150500703a001303c2c0d021403443c41149010f545410200e0103490380001a41c00c4407034400d00030001c622a8540c002d5445a5040207020140115000d04092602c515048416100180c407204003007108407030201c0750b9500080c0c86000c2c6003d8440e50800080e402d1192a0080c000ca09070201380900000c0d4580c96050b500b10041e803540e242500400c1010702800040c2c5000d2000c030b40c419200c00c4141041c020905c11741010f201d90b98609082041016059405490318000310075481d0003101c403c10065850400a0050079444501030004000540c41528080303051241e61780070b01409a03550000c80e0075100140c40100c10000c1c0410422050808242d2004002ea91003000b00411450003201912491010700041c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 766933974 1250 766932724 766932779
    0x609300b1e090d0e03010e100204030309140d0b1503010501150906050309122d040614072a0801090f060509060c1e160c050906010f02100902030705060313031404 71
    0x900170ba40a60141204240c04c078140c42c440300011501000960190000700c0c085441200040f490500c0b05e03c040305515000380c0140300c03100c4141c64200002c6c07001441500e1146014486003d9a01d0a01a0a00070031188180c00800780c0c4400000e0015040d94004a080210520811280300c50014000041160052565546649000d4151800d40c000d0b141070004000c0342545c640c0c1008002e0061013111426541c80092810b0701d01c0d204044d110b41e003c0070744401540e1180071b55a0780c2c00003c141030301344a44e0540701041e9883e00010300359640b0ba041a10103405008110080c130819004040e80007030391350043d045a1810048148050051079504030314030001c484c42280c1401c0b084c0880b08420100d01401070740110a203030548104441e03016042c01182c0100210790316500a9990860b20202500681608012000288002e114040040e64144101c810000345e5440e106c0042d0f000e80280b106984000c681804d02400e051300e075600388034285900301300800c10408103423440c0200c68102c00f50350 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 766935224 1250 766933974 766933997
    0x2705010f0207032f0a030e0109060f0f0f0918050604050702010203131103010617011a03121222030203030a06080a0c050105030702010e0102041706010b03010609300b1e090d 76
    0x44407035410942404c410b6106041240060507040108000640c609980340050651140d108030341d2035002c10340400c08604840240150310780503411000404441d884c0102c110341d941c1c81803c12810602d0030b50f195190b40c0d42c1c140021428140161a8444098002985103080800c0401c0c0f024030a4480038104148450540c0c0c039990b401c3d0080c0d401040d6030200300311034000148885d4000c000500b9000f198001c801020002800e02117039690760702c0440c14290703080240c10b2410b05c004c0349005045601e40e9042c48501000e0b0000c80d1403814109001750300842d124070304200c45004a03030594000c80607590100d900800050300c00031444c002e90f407081c80c00d1074883e110380c00280d0240804070400080c65001007404a81d452101c05005144510740044810590b81c0d2510426244801c1c050100010742040c4140081c0481401c24094180d5000c003120032100f140d08a035080b510380040c00c0300da408055041c0100b0f401d90440d0181c0018410420408034280782440a07507401c8101091014441d850000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 766936474 1250 766935224 766935287
    0x30204080c042f13060908061b04060e060d020c070314070305120a1101090b0603011d1c050403060603080d050906250e1309030809060103031202030a2705010f020703 73
    0x60310440ea41c19003000c80344c15103490016102c160140218401880f9400000c0c44444210600408503419400380d5487c06007805800c58107042140c0407140c0283c1e007000819058500d40c1700409040c940a0040d1603064103500d8110990180c841501d40c29511644040c40811804102d40300180c908502c0540c1e151220391041e10401140407415901354a0706181c2428026105e820520490b82200200000000d414080c0e8100115081c12102075000070807401c02650302c6407080c560107101d41462400c2c1a40c2e43c1d14042581c1d001e80044541220206900c02c24000c540501500014880003401c9a842c140b0900000c01c06240d044078500e44c0d030300c64000704560040480c1c1c0001c0b88050b05c01030261b030440000382c028202c1040104c000400090000315018804a64141660750554070f4041d83c18004178010040c0d0030190601d02100d50300c001c8854484105811140c8034a1554010031240d141401c0c81401c480840002c042958010442900065400980d020030414000800314036a44030b0a00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 766937724 1250 766936474 766936477
    0x60801060e0a0803070b270a02060c010e120403150e0c0108060406170303180604030c0f05120703020d12230a0912050310050102070b0a0509120d030204080c042f 71
    0x400380c0113000c0021080c0a010324003245501c0b4001c00004007400d903401d8000451240b82c083d01400c4c4130741000e090180140380c03100041807400007100000c201200c1d910004e03401c0004114450601e139030002810130810000c5000c001c0405040f000c1000440034094a00d5204c00751000d0782410081c0b5640000c040340d490740e0158018204108080da41c1300745000049a40782e200392054007449081071850010300000103400d40c491035255446040c2150079030396480c00c034510010f044507d401414407010504450001074000c9138001e034020071a0b40b403d1a1b000c1e1454034400725800300d03541801880ba0255080e00144c8082d148840c641c0c232455503601910388001e040c016001840030b103038000c180c0c8507980d0000c059802181e8000c0034180e0719980300c005a0795000705110f0304080c90010310941c03424034019000360289a001402031504660070a00c0c0e2030034580c994070701038080b07540424240301203036040000045164085e1400c014040550b240003824908005929950b14070003030f5000c10117580e0310b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 766938974 1250 766937724 766937729
    0x8010b0d0e030d020d150302061b0c19030b0703060e061005090a0b092d2e08090c15120c0d020706051503150402010e0a051908070807060801060e0a 65
    0x5483d2501840c85100003e5400700e01c000394410b0803d610f100d81a0301510240e01140e07801046a4a13002c41151480b00984c107416686c1054001c045031010a0745840b04102d1505428616106002d4114a00440341d06000350002003007500c0c100051044032480d001d400d4000c401200c2d00f171001d00400c4e5007282d40307100d608021600801116800150400340c05c1c0505124401140c4001d0150700c20801c4070702c5901d900591a40c0e1100342c1d04000803600f49080303c410035200b00c4040d08010880c2c091409540c0c2140852840040c0908007000a18402408500758030b4030100c0b10302c501c240031400e44615a01402000004410503e00490607814400b400c84110502d001d1055480d40080d0130404001d000031500c5030400003030703028001034601d130116480c08541c074039000c03000041d2165001190198510040320760004030380000803d01da07549003011030020311001040751019003405192070070110290b00c000c9807a440781205005182d000019141911141d1420305241c002c2d05001464a90340d59 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 766940224 1250 766938974 766939001
    0x1e010506090d15050412020f0d030203060609040e1006090e07180e0604080909160c110109050d060e0d110304030602090409060617070e09031c110415110303040308010b0d 75
    0x640c048900c0c2083d90300514801c5000701c1d0584a000c2c0c141c40140c1e200e8000007820603c54100c0c140c12140c10b40290b0141d41c0140c80900f42a080c41403401c0820201c0d50004540b043d0340c0e000514401550b8407034001c0030302a02c040101840390b145140088c1d650740c007a0307001744c0c00540000001441960226230117290b1140502c03003211903d0415041400303080c1d018944850041b17422800107140380c4504804034411111076a20f400c80c0103000e446400101d04800c48181c10000c108400084540d2140c10006981d8003c1c3e80000d11269001c404c01c0c0340142005200003404030010484540721408000d41d0101d0790042c0025a6a090180024000b84030011300240b185140c6800402c091500403000c03260480700d40e048500c05034903010407074503d80d000c40341c82806034410040c01055602c101c8090055500300c00b03002c1052822851440026045900544075100e070541118441c0d40c2d11604440c184e019480140d032542c1000d4a005000e080140651103d4000c001184c0354011101e2340115000c4004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 766941474 1250 766940224 766940243
    0x120309010b103603110a26060a050c27060d06060210090c122d0210051201060c1e05070609081626030d050f1e010506090d 54
    0xc044043c04040001d01c1640a81801c44102e03420020484564028001070f0980d01d49690b01c3c6985616031035144d03002c01500318150000000d072040400d01c4560310000401d0064008030405440345181000041910f407880e800c00c024403410706440c00450703050000959807030061a01581c89075a902d00310800d85504102c000580307061340710644d070180064a03c158240c450b03481c01c0d0a5000140c407450440075244c0f0580507010802c002c100601082510301c0b82c00d2000b2045840305100203031642d0088031700003002c0c40e04008002c5141914864403614910f04100d8103011a0000382105030105015101c00d002c0d0b071020321001d20440420b82011184003407aa0440c8a1a40c50322544400d00343c0700e03aa0200c1d0031041c0c04101c041c0041202602030481001050b92a071078081e0490303107064100840000e40640781000b0014903c240010b0101080500b00406e40d410104410403103002c0003800070b03241c2c1211000b98040184d641c407409044620403902c072500c0d0300032760002924481e0062402020b1254 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 766942724 1250 766941474 766941499
    0x80c0a23160b0a0911040f060b030115030c080c04051c0b0411040b24090409050f0a030f0503011203030c020c0303040608042901150915021f0608120309010b 69
    0x9044801e14100ca104511a8030540c643c15140000c2d103e6a9000403c0050303000011090ba0403d030344006030010002c600429081d9513602813205540c020780018000da41e0300c511460b03106406018038071400c002460144100c0c54120218000382c0114040c00f0300c5540c080b9540741e4201301d0760702c0000c0f21035000a001030090a203441c0800d030400c940c103002c0740114100302c8490160300c0e190b8110000d2480c020a05c5520560702280f948d03c541c486031086074403580d940788020106200300000c040b181d400300014040034409040c0030741a492800ba010080003420001407002e007150000c6006015450f0a010030100f40346841a8180400030901c41c0c0c0500c4041000a0810f910400c070fa80201e00620b000c00c0c03130f01a5900789045000314659181225a284001040140382d0800340346c0030704030710b45800f805103601d4841030b440c0345016007200401603001c1005070303490134400c8854000300e2004040800c141840c2070728064072982c058100c2049a035001c07002518580c2c0c29007240c21105001401011000b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 766943974 1250 766942724 766942747
    0x40f02030402040501090c140705280b060306040c0e0603071a130b19080c0705060703060627050123070804031208090613031107090b01030c080c0a23 66
    0x1002128142c2c8200c4c204000003c40c0d0110740305096450083d681d40c2343c101007021180b01d129501c00c10003120345101e450410740b540042c403604881400c0015074240c050180c24246654541070152070140f00390050702c244800191440c0d2003c003260005200b60a8542e9070b00d0000f802c05445902440381c0302440e401141c259800600100a14804080013030f16103a00d65082a00d103004101d0318525840305140441e0049000f480c03c80d9100f031101034410310709940f5540300350420714192060b070042600c0d40ca05225443d00401081a124601c1546141d92415011062b4a0386110700c01d05040c003600c400f403100030320b110144603151070140170380b625604c06052500101640c050702c402d40d940c54140e1131b481c180303500c50316840f4003c9000e480180380b00d46400ca8082d00740702201000702d05100b01c03800622503425060182c0e00040c030340c0140000c0e01055403000034083d600d0f00a01c407001c0241d00d4003004004581d0740103640841c4282d00c0c1c031044000241d401da4107000c01b07902c180f06c48142c01241116009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 766945224 1250 766943974 766943977
    0x6110c060702030d0606080402182a04140102030313080903190f0203010507050f070308070512070e0307052e030b0d0c050a0b0a020d030c1b03050d0501081501030818040f02 76
    0xc104c4002c00c2008075a101c00c11219000e09a42c000d6122003076522074203100911203a03080c0c1000a411358032040c40b245035668014080300d100c1070544000041410445481c1e400401c03a44444280060751552820f1841080c4082448030001d180c040045202c1129460030403804810086400d900c409a0700c0c24107080d0014044080100d00c00c1d070070000004d4100307104005035000e5002400101c2e04046150f41d064078500001010603003040f01c148a454505020040c0548c0200306c40e8481d410025010014107084c10040d030800350281c20700c00d00704000c3c11560000e200c141041c000c110002d0f801c1241e07044015200890307034141d01201d02d0403143c0c188a502c1d0300c00d408076032088031000350807544c40d90244074501980b0000400358220b480036951a5010b504440504855890007210390100d42c1800070000c590010150002130b00450b03400300411451254901400c1c40d01c001b070a009600901882040700c05002c014146070012480b0035041102502925912000a000f800328101000c2014003d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 766946474 1250 766945224 766945237
    0x1704090203011a0f0f03070216170c030f0c040b27180703110907110105160810050f120a20010f030e070603150302120105041a0106090306110c06070203 67
    0x8002c02148004040f0082011035045a100755806030030120060f841d2000c94000a096500754060407140a200e03030030246010000d00701070800e25180c984031f03c080514208000f40384030300950040c0501104103800041902507080115004150035411030f0100744205910304a2108203409030032510261150340d050a40f2607481000e10340640203000d81e43d582d6404603031001401c2075a070b04d00c200031541020a6026030003291400d0850030910119100c90855000f154002ca13081ca880c00707221180c5034000c10490700004d12038280001e11b401c05000500080e46855168450340e025102d4419681007440229082500000001c1c2002c0c404c404510300405141d0a240c0000c013010312185072140203208803440076030440000c204031410008140c000344040d50545490001f0310000000580c1e46540d43c11194602000200301418541b50114580e4240c0a15284202c00d240050040651140340641200d07000755011941389004001c0108500c1b40d9511380c41580150b104004080d40c0001c000c141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 766947724 1250 766946474 766946489
    0x21f0c051603051e090108070e010e0307080606031501081e0a1514070216090b031515041d0a020105030c0c191b0b070f060605031b090f0105010e0d170409020301 71
    0xd01403000b08a00444d8071941c00c1441c003050501005c03402151203001c601c01800e2040c14005861451080001e00c1c044140c0e000100c01e0740b00008001c06800c0c02d01c201017000b00d240402c610554104101292180e03000c10103804500c290f95502c0040d002c2c00c21151505541190b4062038424001d41c00d9006170009200580701e121801c0c3c04240283e00c00078100185021701d4905070f803114104800d02020300341c01178200d07901d80305005041e04041d0f181c0d00028064607034180811544818001400295046419810411059079101c2007005101041c95580789a091914030354a1f96140f01869980c00340c154113102c64443c0258840d2901c0d50107000c44130f078031f004a05201107440c00c4468244403d803d4080d810030840c040c030054000550101501001520505d000b0805548940100e840c2048091400c10101100079602034107051848004c2e030040d101500010156041400107840322100203030b2280129280b01c106001c1c0100c09140340307446c7c010440c003280d40c0c0d5601c00c1d403e00130b5003081c003c180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 766948974 1250 766947724 766947757
    0xf1203270f050d03200f030d1407020a1721010306020901080c0a0906050c030f12040c120b040206130e01061205130302070e0901060816090b01021f0c05160305 70
    0x40c0c0340c80c0000b0f02400451381a0b0303a01d2071800c140c03a26960841d0240f1400740040c4900071144410740000c0c00030341030607020a6000a4a130700307581040b8807880006808601503400903105140420240314100d02180071400107145d070307032105d40e002100d4280340410003200c0721072240000c0100305207500240312281e802d82e1100e0301a129290902001d00c503400400d000718044201c1004014000c0015014411240341524100b80150780320200560181403100110700920342040304019881c03102201401038115081d030004410703910041141400341000c0d00c228008200140707103030320410780000604001d045034042541e40e08000350207a402a03d2018203942400e00007012611020000400550554010450945000807001c444040a00350011039501c6100200d8600002c2214000e8400e1104266050600d05080c07032084400040080d41190441100c170040e03021340ba00c07841268200088002500301290100761034502c205082224071002040c80b003070038960018003609510a2020000c07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 766950224 1250 766948974 766948979
    0x30303050901050604060b09041a040c020d08070c0b0106211b030605121c1209030e1e030c01031505030115090b0108010b120414160f08070f1203270f 66
    0x10741e1147c1c0146031000c1d9042c01292400e203802d40012450500601c291252250f45602090589080c583d150025921102d08001c0c4164040a07c6a0241840c548415044999603544801401c1071240100300131a2000800800c030116081c030f062451191410000032140021050000101e40b24a00119151080000f0103040c822002d210f9030440ca000b13004070030411407038070090303105542c0d040040048801004403601c01902c50300304024025140e203d0322002e85002c0200d640301591105100d103101d10320b40f101c141c0f000200042c0300c52090078082044140c0400b8200002081d0b40b186074507600308422440e22903440c100d07290944140b44018041c0c8851400151030f4203400b8869280d42c032400300702000c6100040d000d00c942042c0f14080b9074060840801140c0d14041841012403103405c217071502000550418420580144150f501070081d5604c2e00804c0c052098040c0714000070031805002d04010503202d883c00302c002c1098a0030f08160b85030310b00d48100021809004050001071101c102 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 766951474 1250 766950224 766950229
    0x308060f0a05090430030204050f0406060e0d051f0504060608061003080304050a02180708070908250e011508060f0922060e012c03030103081c060303030509010506 72
    0x1031030165840500700d2a2952101c0e900c07900385d409031054144a07164002d201006880380a201250955000c2d580980c1fa181014104030031640c881c0c6045100b0340c0752403402c2000e1900700c3c2081c41401402c40310021601d110b404c00e00d00340340350442040500d0101e415810b4400642c0d0b408540543d010781000c209058440320803a941d1203064580c0810140030300001c1002807121002164000d02c00d00a80f9940d0a1a5000c52402840d486807601c03e039140c0001c224486921221045c0c0c0440c2c103203001c03a4107618100b40c0a032100300d01190229003040f0240c55482e04ca450040b1000204480d60b1800360340d6944503550050f8240301441c800008450134041a042c1c9005d00805a0041c8000d00354401910b9500303d500120030000360304014070b105c003144403000c55400d22615540651940002c6040c902100a040ea000110441030740e040c11000c0305600002e200100303070703415a584080f0310340c2ea407041828907078001d603841c064415480c1e0078110080101645034028901403900c4000a2200d80c8a0408 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 766952724 1250 766951474 766951489
    0x2010f030905371e030903020405010603270b0711150405060f01090e06160c0204060f0f08031c020c15010f1403030910080c161b060c03050405010f090801090308060f 73
    0x240034003410b244050103400c1001307018459070aa031090401003040d070340d280d01190554200344e009201103035444415168405000d00d04810880c1c03c2501c454000c2d0303050baa1004030140140106040041d410f00303c81000804015018400019002071146031409140803a42e80b01d0440b24510b03508104000000c0a151a000d0b1003014105007014000b182e95800900500030141340006081014a015900240e200e40c4940000707059801440c80c039007420b1114810465045c0d51044266138020028a044000058103045040000d848050f9a038241411412718182c00c29110090f00390595000142d64410580d0b1001280c0c101c003003064004412804240c1c0301d024041c03c5a4010101c0b6078003e203024400d070b41d901e900510f01c070a402d0610050000500d22600100800c84129080c084440719034402c050030040100a0352820290142c06950010040c0c040e070700c00d450520180c42c0c44440901c1c09003e028003e00f401c0c0c8020483c41401d41002020102e041d02d06c14043c00c20340300c0d0883c15082022 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 766953974 1250 766952724 766952833
    0xe0c01020610030b0a02071407031106070213020c0319020d1d010c230321010f0506040b0d060b0c0c0a060f021510050301020c0706080106080f0402010f030905 70
    0x1580c514141c990380319802e150340c0c005c0009520386c0e420000c080001c0c40103009181d1a000d00ba004100140c194070700800c541519410305446050309000f40401070f660b2116a0080665844015845812103000d051860282003c045180b007a07822420040ba81d000079041004c035880d41e1400c6540d18418200003e21100001c0d02e8006440d0420780301c00308030000041004501803e80350140e40b180780312408c0c1103400c0030180c1c48107124648880001c1400c00400603015003040c07440a0450b07440c04001400f00d02c01c030301c0340c060300c001c000ca1340c0d101c00c1d010750307101c54000e010001c09070381e959041062450b02c540c54000f2903403103800481004a40c0c02e12400340d0710041d5415070000c1480114901c00d00300720f00ca000305803030402d404004001c540c0b81c03820300180c50341030303c00d900420f07200c0c0c1001d0010b0b20710141604074402300b12070a420000520130000b0202d802c15020308282e040185002d608501400708441e000c1c1c1141304180004801c03500d20f21648e49018130302e20070303036030502d03110a030f0070800e101c014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 766955224 1250 766953974 766953991
    0x121406060a0c032a031107050904021509060d0e060a09080d09051c0f09171c0215101406120114030a0c06020303011412100209010504030602030a0e0c010206 69
    0x3071045200e030501940846680074003034203002613205000306038886941000340a680c01505a80000300030903401580320035016507801d0191070040e092902180c1004070040011b44aa10010702182a000045045403041d1101400c01680c07041c00c589440d010b003e5841959500e480b4580c00504201c50500c149007496501410b01e0b85008010118540a084030700c0f07069441e406103190682e20300b9042c0007201e00c050a00c1e211050510143c039006130450030340350700c200079079910074403411107d4401003800c1822210f0802441d02610705010200d1820212007001c49160089030709002a510000f000d400031540c01240c40001800c0000c2481098040d1090280e4500c146900610401111459a50303c4e4003018045400ca007040c0e89906040d490164001c0c405a08004014000e100740b500c1003409160b400c0c0c522015100c001c009072a030b281c0608480d88241a8041510800750303125500300c80046401190564990030004186001002c800230380d91500c0c4a08441403519500200d0401e00c994103030b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 766956474 1250 766955224 766955227
    0x50c071e020d1103010f0207060f2a0f0512130b130804030f0f051203060913051c0210060b12011d012309090c0111120a110307080a12140606 62
    0x103030358442c40f01c0000007507a9815503c0d00e010000b0b0490a10107000c04034060400880c0d188001c00c00c0c00d08480410500c0040740080b01e002004103000070031202c2c0500701901c1d0120640c080c00804803824081d02031074601142241c41400a42c0c56001c0500c0115405a010500305855420f00821000300320b45008084110a0108102080c4001c5d0340c95500e41c0160f0f13050b06a107015645d01820b000050700440c80040d008014055035080a02c4082e90248100c05484210800c03501d40903035400382044800360017800307540e1a00c800781c401c1c0000180300b4210382051103103580340c0304200c41c103400c2042c5044e141460880005415840012140001340710036854195903401c0818003084400b0007040c0f40c0407458603d5004000b0f0300c4002c81c1d1752151001d0401740112203522000140f920403400b846031010780c070008541298a001c4802c440c4542d0082c1080300100851860844c00d60040d918080c2400794042002c01003a80c01654541001c6440b281c1005100008014801c905030152442e0380c00160 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 766957724 1250 766956474 766956499
    0x30703060f050a030620040f170601060c0b0a060e072105060f06070303060e0c0a0f032c0705120115170703020d1e03030615170c070c0801050c071e02 66
    0xe140e001d10b00024450f51484400941c0011308880d81d407141e400514024400c2604109c0000700340800008070f900c250240101e540b4204000309440040e240203000704101d00d02042e48092554800740085c90445040c40c0585042c042c042c0016150340224261441d840030181c100061521405224010007080d0b000200080313410300c030040e04500411814140c0d1342c600400c0a0418050041c400e00c1d4050400365222442c1200410502c0607640320b03420b040c181004400949406990380240c40541c806400c3e90106443c207151a10150b5441150400041071b00c80c2030180c0190800000425024080e6178400c1c1d49101000b81902000e00c00d0b0455008004e061005140441060340c0d00d600a022941c0c01d5207075505505e604205041040b40402e98500301044201401a502e00e0780400904180c9040301e2160f103005080040248500e0303d540d400144182001090b1071745001034000030008004904d400040b401c542d41c8141e0060f204404840d40100c090b070f03500c10070300c091140d01419039003a001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 766958974 1250 766957724 766957733
    0x9050c12040827101b080904060504050903070519030f0e0619020a11060708162901030213060b0d112712070303021e030d0908030703060f050a03 64
    0xd401500403503814104102400ea0148143c204007080440384443c200070582c2030b41000111008282d03610140314100c0b03203040480c0704803c50b054095410001280d07030341ca4600002001880140c00144c1d0103407078601400380d1050000b0140c003402c0d20400840388210305415685035006014500100015007050071108164892000b10f4140d0802412541c102200140c2203600b01e101601e1813001a4042d030301207001d010354280d84071034110007510b50a01d01080d1f900c42003040d119240b40c02c030044405060810401c0f01d101c5012000d01d1403041c0c044801c0c2000306140c40401c000b840282c0c407802101c103c4440380388440c442c03181111610076400789441c10081c40c2070003508c400311003840c10180a001409502c0e401801e80b0250012810211020300000820890440060101c4c920f07103034840700c2d040c0300081c0c0000303040d90088040c01c0701c1c100103012000a170307186100e5214904240e5062154840c2041301c0c60016600418490301c0601c090352300c5031607105003240c5a00c1141e074031503041da80c00c00c00304 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 766960224 1250 766958974 766959007
    0x90307060320160807050f062202010503060d08030903030106080a020a0503060d030c050d21110322050109080301081b0f06070206040902040f0510050909042307090c030609050c 78
    0x400402e1800702508a2030340b5a00001d80082e001a1000d402040e00d0180d4600240719a0358800341c6c480c0305800840000303905000b4122700500080c180000000030420650b28581e0710070310705a205107810fa0b00d00d40200100d8613030b0020b21545005c5481c0d4008500401d9142c001c1c0c6513080140da44140c250340c2c1d0401045040310400406409100c01804c20101250f010b0000582c1700260351101002760340c60700f441619240059108820003803404140d128421042070480b03402000703400f070b08640d02e18039039602201d100a13035000419a610b420540301c00c22034210081c504070b5164400ba142c00c0110b02c042e40720420310743c099031607201d061000341d101d07a442c15001074070301d65002902990409480d0030070041264441d07008103440e90f880080400091410007030380442742810380740c16030411120354007188401401410003420602900003114101502800b0117000c0356904003190017031595071a0b140010b011422200740020300b0007002089076112401014001c20003c6450362402146400030200c5c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 766961474 1250 766960224 766960237
    0xc190203160b070b13020405040c1e030206030a0b010203130f060807080f0f2d010f0605120c0d020c01020a0306090e120313020d0507180f0606020a020409080408070b090307060320 79
    0x410540080f01c0003580703030741c071030548527920030021034003c0c5003058008004400c5841c145665415202d40500040e1500c0d42900e80100100300b012071401e60304801030b030031401000b40c9001c0c0f0098500000481c24406055841140e182d40c07500c1041f6104c030601242d003100b0803102c2005003902400843c0410201010241c2d1024081034240b1025100401c40c1d07445d000c0d4001c1c2400d5020148005000303e403c1d12452030010310a60809516103480c0c400b41000c0984010301070151080c01007001c94040040e0340454074904441c40003190b0791502140f0280050105004010b80185481c2e1509a40000040d82140102044242e18116610300150704244d01100500300d0f0032513045540580010700411284010f8598240c0e003442c0800d46113504000c40700044082e4000900f41081008181d8000c140c650620750181c03404a0705580b203040110b898402e80d80141900e20408030001405170031240070302040744044055502003640c0d05421000c2d81c03042e500d24803600c024061030325004000007008008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 766962724 1250 766961474 766961491
    0x11a01110a031d0a0f080609010c08040605040c03081908060604080a02060304140a05071e05010c0305090d05030412050c040603020105041e0b1207030c080c040510050c190203160b070b 81
    0x501c3e18041015124954046440c881203690300b8000c4003c24888158002e0156008109182648100808016004e44090411540e03080840e00b4003071100d013510080c6030003403c1159105000d0f041c545074041611410b0000035807a43c0400c0039413411804481c2151603040040a09009940030420707150f002034030445812180c4118101e014a0500420302d01c01d0099025003030355480c1075030b000108007070061480b41210050000340003ea8000480300441a05840d0a580b2181e40c0d00108054904070400034040e48400324001408583c04440f0200c40c6105000340d81d200d03005441480159281030000034003040c0140700a000344280740040e0304c040c41c9032011700741c0040d07990a46003d150740001e0900c400401403900300244a6014003820018010900c3c0642c2903281c4414510102c0c0030b94020580f04040304030002078017910490588855403030b050142c49084c0e865109518003015004e908030f0180c007a01104110643d100342404044a1941003030500d000e409a8031041c40d484010250f03032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 766963974 1250 766962724 766962767
    0x5121b0f0f07060f02031009060503101802040e0d0e03070e0703151d06010e0d050a17090909030c070b0a090317070f0b0f011208250b09011a01110a03 66
    0x8003c58040e0007824a114411000140d076404d00f40c02c84088400b458106580c524200341f070030440341d01d00250319058018480c0740001c01d1480085000b02c0008081320195100d0301348410319160780d402003103805115660b82c950042c03002046e8245a204e52141c0708011003003105800048400e80071340c21a00c088143c8003d5849215100d02c0d1100c8e42c000740c21140c0101654003010050355503081160318294150858009002c40e119681d5140d8540c03060500502c000f14040201b100d0064840989501040c01400304401e80342a00a140d601d0300030514600345071158280010b800340c0c03510304403035079aa5103503a007074003407421038507540381d01c0d079540e8100741125100300200004145c2d504d02c5d82000034070a1001c1c4241d03041c00d08280300c0030030041e0000c811803041240204006103140c0111804000f9540300f00710410503000780b01c2c1d0400c42400300a801e0802510801030300c1a41944440581e07116483c084041d180307982c0044400342d1000c9034160042d84403800d0080443c0c05202e54900b0b5260511021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 766965224 1250 766963974 766963987
    0x10509040327090c0c0203030324060a110c010302041508060114040b0c0c01020f0703170708030106180f0b0901120f1d010608010b151b010c05121b0f0f 67
    0x24442000d00d403074240200b00122505102031001801104401c0c001484c3c84403000d4095000240c60788070241c44181a1801c208240107881480e0401101c207000c010015501e5021000014002c0448820301c0340e02d501401c000401c4d1580030380b090300c0c00e8841d82401004910f000d00c00a0703405100141015043c03060b180c401501e451003a0000380041c04180300002e4560f151501001c2c64000d84041403810b54100e12540b002d001800110401101d07000352658107900c3e90001d005007140300e4001c016003048000000841e40c246c004c031800400044800e44c0c010003da88090110600003a4000c0b100e0341c000401c484000366210b01117840802c9001c07800000d82017401c2c0001c0040350101d0002d1a8084103552506d41144c2d0b080c42888000c05855000f40500d45483c000544a0704402c14081040c200100310007030302c141c082030b42c00b0302e580700c15008020f43c411140b405000f0f41c0111401780524410400010a41100001000340100c840302030315082100e0030310002041e03003003c080100043da052101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 766966474 1250 766965224 766965257
    0xf0c180f041202150403090e0a0e0d050706060f06020129010504050402030c12190e0f0c0d03050409140a0b030309010e10030902090a0203090f0d0e0904020a05062811060105090403 79
    0x40c50046101e40c440c10512442e01000e48c0381c50b400141001c8140d03142c40c1c20310404107004030b02085514982c1c5405a51160a03260100c014070a0360031203a01c0e200309040104030035405600000c000290302c0c2105d1228158640900c00107009001070900280050104002a00301600610380000c130033642c02c0d0800569803042c030072814045545819101c020f62502d69507106610075200300001e88800b40013020f20201d643ea03a0b405c15a0a03003400740740d03250010303800c0c076201d207041d10042c21a040d030900502d034043c0b103800318900c419035199000c246425015006440e0001c21102d148906842c1c010700e9172107040c00c00c85800600c1c600a0241610307140f07598016038942561a2003044a8280180c0300d041c881c0d016854a0b01500103c00154482c5014403001d6400481c00c401c668021142c00300259114408074984200715031245410550204443ca0981641000c1c034036500c049545800c82c010f030b078400c01c880d0800c01d02c1510b6400d40003a80140010b0518200c00b66006c1d0103070402c401400f00c802ca0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 766967724 1250 766966474 766966513
    0x20070506090109121a06010c032718090c0608040b180c0a06050d0b0f0d0605040519080901121e0e030408030f0403060b090f0117010e0f0c180f041202 66
    0x20444405c0e40c0300c100d021882082000554000000703190540c40700003250740c0688001c0803d05141200c100d00c07410311492080b407284102c05030803204092141c803030141e511a0058030b140c4208030307100c6e48200000308000303100d0f80c246482150052405071490300d8042d5030840c0d0442201e105201400350010031401611032042e807500a0900b543c481c2d40d40d00400e44013000312190300203000e10a0035201e00c1e80c0c0d065551522038800203600104000f8258030789203000c511b80039016011000c04061210050140702004015241001003030f00d95156008800505400702c0d40d078070050300228a00c1603000d118007d03680d4002d03000164a20105c3c0e25150702d46011070325640180320710014901c0e0000342441000701070300a04501001c103981c08111810085140040340d841400348030750850502203103541c800404d411640e01400301d0803d90780d4406519403519159180a8000740c007030180100c0304000c9000700b003031140c8a55051001c01034617850300d50300c800280c880e000c141400c61040311008a5008540c0c103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 766968974 1250 766967724 766967759
    0x60a0507050421140d171302060309070801050408030a1521020a050a0b0714010902010c02040b18010b04080d080613091a0c0301090f050f01151b1220070506090109 72
    0x2c1543c3c00c0e101e58020410024501c42c045041994801d0004111f410751a804600e5412903129031242d9031f40c16000e180001542c401100c4d1b42c281004c1c8014410300074011030050500100500102540480301c0e00d400c4110300c55403241d20300c10305032100c024107002e081e100010b100070b214080b100e80d02c60001c1c510344080c1d0402d4500e250b0005541040145020f80b40b184d08010400a00000082d1b800203408241183d0010b4011500e03002e00c0740280d50703800c40d140c24051031f00f94a0407a81d40c403100050015005805804a03500c03401105609203401000c03a82d10406000308030f503500a01d060900c2e0043c21001004503102900c6521420408001c8181c0300d03c605030748841d40303403a907240c9080c56080e07800088a10281070b29010901950869211555040d122602810345d4594001d480446000b0803050540c41c0b250f8240f07500400b0003865421f1500c0c192496602c81140345622100c0120038049050358039030035440702004000e0750505802900e0b00201c14104a0010f50b50340202801c04814103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 766970224 1250 766968974 766969013
    0x30304050d114303051b040f0507030e061005030304150516052103240f04021c150602031206040f020c060603071413020c10020c0a0302060a0507050421 67
    0x40602c2203031480700f16400c5900b01d04440380d041c209455511446d03199221225401c0d280d030304403208501c080d1502d41041c40c032452444800c1041c0d29115100070f00610807116014618003034040400c0e00711076100c0350481503d03030040140d8502803521440b01d2208840c01c1a15040c08018004403620001c00a800c0307441c2405000905402070841c107941c0751145a100100001c0c040900c01e012400c80060b0330b014454502540655141c04500001030316214003205007980030340006826080240040d00c402c0030b80b47c00c03070300c14000c0b03011802000c1c820720001d000d07040040e1b100340002c1800501c0d0241e8117401c8640a8000544071171041003440503a0b00542084505500c41014402c55050800030f403002001c500443c94540e03240c00c0c0c00240c2e401c01c0d642000144640104034000c01c050140001c48465036207440c01c65903041706c20740030307900c0e101d001405070098082c840008034001810301400d03114002554650b8035241c180710382e110b402c0c01180c04000740885400b0056000a0203008a2000700824 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 766971474 1250 766970224 766970293
    0x6010b040611070b160c0515120a0603020f210304030308010311090601120c17130c080c060d0c050d050c0414030a121b0b010e04030e03030304050d11 66
    0x400501500c1000072225001d0703140e01551041104c401444203503a80d811002600d4012030403181002d981c1c0060310b4001aa200c07802c0840c2c80004d10284005003c0c01c803003d030b4456983d03a5803405100c00c58030280301c0603403c00070f00312048029242c41c220118600070410791640c240707200307400001d00e1504140c2007240030501c0c0d04018024841e6100b60300300421011141d0103054684600000e043c035004042d6241c2003615085910310340c1f8043c2c00c0c4410302c460a1086a00a40b810f600c40c440c1201062405441c52030031498041904440840c98a1004501174000c0c2e1a0020044010b00140000b056030b004114081c8034041c2139501a008007800b0344980301e0400e450300d08000c421103c06000e000300301e200e94011303044600003c080360401e1000c0c11050811000c8044a00c1545041c682c0ca1a80140344e40702180010075941c4160095500a0740039588011281c1440003c0c07554902c000e540146c4280e0201a400f0001d61080130240545012201982e41d0300242d1060031070150007140c5120141180c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 766972724 1250 766971474 766971479
    0xd06020301140418170a020c030316060b0d1e030504120b01090b0d0506013006050103030909090b04021002030c10050405190804090903031d0604110f100c1406010b04 73
    0xc06009648034161101030a44c42c20565a4501c100d013503074010b89034100c41c000f06030b0600301c034024002c544400034050142c950380c0c4c6190011080c00b0329444400c1341d4540c6014055961410310814428031554485030829110f0121903c6840035001ea0004500b048800c00001c910a010710365080e140c41d1098030000c5a03035060a00b13000684210140c903038061840044403101040c00025000c2c11a0424400240613006111f0b45c146a00c0d2140ea088401c9842a40d08a04000c0213502c5181228025550800d0302038a8190000c16200240405802d10700c1e41408180940b0302400384060640503170040b2481c01030a640941c1c180080c500c00c82000c1643c0e10200028404140700300403070354440c2100344003080042c1d80e403086640242e000b00a07003645e071408003004050180d03114440c0314600f000c0700006007142d2500180d450404540403510264404030750041e600300440c0181c0e446034018503d00035802580c0b02104c0b54803042c007081d120081660981c0000450a205c8140030303003401b4038080d55590 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 766973974 1250 766972724 766972729
    0xd020406110d030507170402040e0f37020103020a120f0606030e010c17090a021806011b12121506080403020d0f170a0e2a0d0b01030609020d0602030114 67
    0x203080b00c15502c181420304081040c0f43d0b80c425603000c02250354001140a0392201c0c00071400611b001c001401e182d00c5221440316108000240700343c03d050071380c2c40716501a918248038400ad562102c100451000407821420010740c02a000790855180c10b15109a440300c4100d500c9042d200580405c4404a80c1c41d80c046c0a115414050385081c200740c5002404512185000180700d030300c502042c2190020000003281e11114140701401c101c0341c005082450001100e00c0c40c60913607800380c40c003e0118908004400c8100d01d1038802526103508212000e60b91403c980b42513032000d50082c130790f410761641c601010107600000920302000e001159108020b502d001c1c82c01a1511039080d40e100c3c01c3c485e480010707040c0640d0180c2248400304110008402c01d450f00700c02680940300340c1c081806107000d03500140c0e02d6005c0c008003c07041d0f8917540841120a0044106011079452440c1000d414404142c005101050b01c60300592142e0344050440440100c0c0358a48000700c0c3c0003078100000c0b005003c80d0700380d07107403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 766975224 1250 766973974 766973983
    0xe07050d1b092301050915010c08030c190c050703030813020a0e1006111f0f020a0201151715090313060f03270b0c0d18060f0203060303041404020d02040611 69
    0x180f0140d18503000380d5041a001803100500240340340c4202904c8105407501da40300b001e002d00c10a51024400d40c60742840c0b0502c1c034654000704a40c41c402c40405141c01d82041c86214001e103029048006860800d00b19101203800c09802000b040484c105a1300d00340043c2c540303003124001091080c50010090810041e1040c042095501c01c1c01001100e40c00c0c1d41c5045404210340b950040071000c11310004d4031503003903140075000000764881110720102e442000035806400043c42240c42442c106150798076420742c480312410035070765a1440d9101c1d4000305180005c11f0b0801c2d4108980008581c28007620307441c1c140111041e9001240010409114146000e4040c014040144400e20000508030076946400502d0200204050720b5124414040791016404408544105a440c5c0301031164043c01e01c040d4a900c0000001180e01c2c514003540c680800320240b02740c034040c1c00c6c0100a1880e05203456603280c0d85642490203a68029402c00451a009901d88006c000600b441c0e01c82240e00380395a030b003c1e0700b017 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 766976474 1250 766975224 766975271
    0x1031707050d050903120f0d2009010309230709110a0e09040c030c090903110106030201141c1d1b01050904180807030e03070602010e07050d1b09 64
    0x404000d126a10000d003010a4002c52860246422034542110000091134a1500c00d1024044030000400c0710100e20800c00408806d080c0382814404800ca80100c050b0b4200301945040d02c50005002d00003c640c400c0d004000ba181c0552402c042c3c00340100040c00c92152845840c081a81c4011410040c0e40300e00d01418286414038030919040903281c0d18003400e40c080b000f84941c4140d0300100014204406103840710040c5403c503400e081016150035688000300780f145002d4022550350001c503070040b841405500301f9130303906a507003400d02c7d0311000211245070807903000c800c40a400040c081000c2d408031b01c10104105000408040d248010071086410200b26010008148201102c2c0d114207907048021616000d9042e50001901c84007004500d03102c0503849001805a0000503450382850307070004412014000441c140d0b100d556550405908032583d2a84000d25900000d200300000d1800441d0820700f140162031010320411031002d04211814207410000b107161b0394031803040c05142d812400144 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 766977724 1250 766976474 766976513
    0x8010e0601050703030c0507050709020c2112091f05150103151503090f0c0603050f01180506040914060906070e030a12030e0706120507051620180103 66
    0x12181444000201180325061000c0c05064950030941e00740e80c811022915015003110545541c1034131405088041c3d40026030402c40c1c7d00c22a8920709000c20300301d5040070001c65042c006490810058100304081c0b4005100781a5801000000701c0e4800501000030200047d444001605180c4061150151041406c40e64101803034401e20340e10144894030300342d05448500d0810350002ca40c1e17a0003203001d080a10310080c10022104031481c1040003100d160001e0302c24a89042c056907445407411054910b007442480c04440340100c0104c0b07501190381c00250403040152000c203a809140d00c512980c0940a40c1100c5154054810044d03104070a2040756040b502901c0d20303600180d200e900190b0340e00000e500c05400c401c601c0e0024205a4001e0b801094411000010348080342d942d080081c146014036003400081505110004460a20070811507009482100c2c0e00440f42003d81c58003c0400380d508481c05025000d0802019256292550a9006252800c015649604501c0c0c03507032843c1d0305c03402c0598 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 766978974 1250 766977724 766977749
    0x2120c070e070c1e080903070b04080c06070c0b03130b0903030901050708060d152310061b150605220b0f03120c101b081e060f0d0b0a0501060801 64
    0x600081c1c001c02c075a000b071040d41004c488111400c2c24030324494070a0505a03035052044480000301d88050034045c01c12901e000068403200303411007007400018491600b008004044090081c01aa400040a1a0080c0b8101c1c0c100c031854009035180e0194080c1034603444007980c0040200401c4600901800c2d0303215145241c04007d904046020860360801010000d2030120110b103e41041d95107540150b401c04002816034241050480e003c0310034603815223103800c540400c1080440d800d80070b000c6040108120442c0303103500300400d0300c42110f030640075903800e21259110b01000a80d555038041c664403814035080d003007100c410320449039000c540240c1092401003404c600d51030840d59020800c20382201c40681c000707075280902c0e41e8081c142040c0d6036a80c05070b03e1500651188008040d81000040049601d07190001d842e0800c1103e09001d4101c011510a10795400044441c1480b00542c000d00001401140c40c1c2500c1c2e170703140c003280803044615001940e6034a00420045134045252801410240c10700c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 766980224 1250 766978974 766978997
    0x1090506010e0a09020a030e100e0708150708040318090c1107050a260a030e0a061706120f15060f0a0e040308060a051c030906180504050702120c070e07 67
    0x55143c89152180c02d00c4a980410780b01c0415001c2d40210f40141e02c940705580d004401c024000005011007482421a44110000403607101d03000138402c2c11840e5401c801c1042660f858104442c412402003045042040303c034003404081d028414020040e04a42d4008155004146c030020440c206035081640c05030b0040380f08100a48500c0308420075a140240d101c4103400d88403200e00d06121a107100c032117079071003a2120841810303880042d40039000821185c20340d10564456003119135410580101001c1c240c181d010036010710b005ea1090301808010300c00d41e120200c2950110f0b082c0341245442c0c0240010420400140b0b1401030614801400b0407162001880c0c10400014992031008100400380708e9a003010445540e240080ba0707008110007030160039800080303408a090500d02c00422030104120940101d0941e0040c414001d94038184080001d40c01d24000800c03002c2c02d0050030b00819030040b016902280540d03d4018064018007800810040e45044800020004024200e00811401e00240c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 766981474 1250 766980224 766980229
    0xf0105030f03090f04090201110a1110114b0c0103020c0304180615030b040606110c130e01051311040c0c06090302120310050307080a020a06140c030403080301090506010e 75
    0xc4e00322040041e14005469410740c40142d0f90040c403072000c800b0038400c0c103840c003041002d0109a40240d01080d103440d80c110342d03000030070b550a0600782007221840d04010007012088180d90640541c1d01600400302e455145000080b601d03003040c9001604034114118001c00700c50382c007080a2008cc5000303103000c51908a02c003141c681c0f40d0041c0e0041501050206020801582464002001500f400c0080450070f50060364060001c0c0207080025002c0c9060002c0003807003600407020721404811480262107612220410405030078800d00b4a2100b00e0b0340d80b00000b400030001d00ca26407007540340190040e64011142001703c5100b80c9801990711490412000e5070b5100d42c03101c20030300b9480c0d1202c0b011840342c0305490f0681c20858403100b8070300603035008001c0244254100803461f04441c010b40a440400703846e001100d03203684098101a41050080b0010014180300350051a41a140e65084905201c8800d600d1030556001d50310550318054040014420000c140c801c8035080384090810356600c4903101c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 766982724 1250 766981474 766981489
    0x3060c0415140408030d1a04090308070e0d060e1f1b11011b05130b0f07080307140301031211010c0c0611070b0a0f0e12041203050f030f0105030f0309 66
    0x5210003002014410141a151204290f83c05000e000b400d6a8544c0200540f11005000194450755001102c1441c40c055007424881c01400d25056034440303c03c1c0d0342e80d5006607050112130310780d03540000c00c8000c644040b4101e0302c1801d40b54864840503004c18500c0c01b5884c1415440070140008662400408280030900002e00c10070600150506801c5100340180d190b0051501c5190b04060032040d001c9001013036880001042c1040ca1440040c565903224401d0301054014114010006001085120040f17200350001c3c5030302400c070340b82800c00c041c0403144010b074507003080c0e00c125814140781400b02100b07031300403003d03102c0e00000d81c00802000d651100c004050385841200584200c1d501d107001e2071082c1c0e040044820554000c0302180050800400d21001401007001e0003010f10310300103483c03150741c10100d03c18903000c0091141c0e41c1050b080411074144c0042c000c000301c040c0002040f258081d0000325010354890710186c1c2040713500f585880309141c102415200a5807c6130010400d000b0346980351300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 766983974 1250 766982724 766982759
    0xf050c0c0d06020c010f060501090f0b0f0f091c02041a1305070e04090305070c090b0a170c100203070317010f03032a0c061b0f0206030405010b060301120203060c04 72
    0x2a8208201090750070042c000b44940b40410340d05508102e6405c10104130b5030404005c40d070f030031b988800c1019a0340003010203080c020301805c503040c00300b000100342e000c01d440c0c00340a240144102182c5410300000002c0c64039648602425020044440c0d000c0561034940f281181e582e054140c3c143c3c6020020001544122040480400850303845002c14549032148005000320b94005d002089945003d04000c0e2558000200850b51003061520100d0211410f010341c2c8100b40c0c010700f00b010202e0800340e50303c00000718403501080922401a25a800d5a070703032003c0c3c60301902c03560007941d0b640000b8100104052007109000c42c0d64080c5c100104480012441d030388048a81605e001a0501c2c16103010a01503908007085c410b20b0b2100012038018080d5845800301100c0c49610761310b1200c507078003841500216410b900542a6800c0302c03184005400e10750000c40c5e20600c100000070700c4440074400114242c0080e003105085180e840701c02c0045080070410160085030340e1600c5410310340b80a00d030011039114038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 766985224 1250 766983974 766983979
    0x90a0621110d0c0b16140705150c0606060c0c181504050402010e010f0c02060a0f1707051608090409050d03140f01030314040902030702031c0c080a18210f050c0c 71
    0x50308840c00004028600600c0d60706c00b2100b0560212112403d540d880c0c20302546114081c100303022545d401c18030040b20402501100540350700e946160801071240c00c042c201d0340841c0900740c5051001e42d12011170442840c10f45000c4245401c0803a85000c0e10251031020600a9281070140400f41c0e801c40f0400000d00004d01c9c003c0c0b092940c054040b1040505404005d40004021a481280b0f9800c0004a03407940510341c0c40d54107210f0018a91101d803102900d05501041c030403c010203458cc15215600306043c0240f044901e48100d0b90003160444024000070794083e0042c130454200180d041c041c0f03c1d00220500c4604000341080444001c0091040c0b20050601c6101d14000d0307036540b10f01058800416410320304540324170b842c9a019460ba4403a840c107240171040400c2c2103010365414451904105180d41da548010303654142c00c80300030600410010b48141072001c12400140001c2903070b07441042400c0c400621a400300c00c000d0150340100840308144141031081c0c03031400100148440404104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 766986474 1250 766985224 766985227
    0x904050606190f030b1501021506090a1b0c020a061805040b0406081902030c100c061113080102121803190e0916090603050c09090a0621110d0c0b 64
    0x49151100000c0c1c0c540c3c400036035143c4610b800401d1180c9189035510460703040e0100700000d2004001241c6030600d14402c0044c0c980a880451141d0800d40c1d41546e002400c03010000f80c0c00b240d0503000411001000070301d40000c8601d1800011400c00110910082000781410b00f40104003101c242c903500003901446010725987c3c04141d82079607498110100404042003a11401c01e001c1034161000d400a480503070080c4559104c4540c107080c0f4262100602c3d80079903038046903403029a949805801c2e2051001c80e801070511200c40080a0081d03140018072010000603a107520095051008001c000c09009007000300021400400c803001c0100c84400000c24403114500803220800d45010302c0d04008a50808079103001c100000f40d070342d90802418070342511184c030320a580c2c800031402c1e52412212204180d03014444142c8a042c5518000c1e0002d070700c100003003112900c8039911400c81c0748a0a030b64440c44101e403020001d1000380101c1c1042e0410541d40181c03c15059100c9000400d418891011841c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 766987724 1250 766986474 766986499
    0x60509061c09120804060612020f281d010e0c0418020409231f12050a120207061407030c03120b0307080105060f010201200c1e07090b0904050606 64
    0x9155000114041c3d0040030840040d84410009115940c200d408070740e03941c503102020940d580e802600c0007140d54010850300400020005000d00380c0d10b80304002001c01c48038071100825030315008150014101c44404030500541080f00502c1040f01070303228111002c482818000c501280c00d0403181520b07495654140e000b020b0b900f00100032b1082e6801590310a1510814047c0a070410380c140b504503480c4c4004440a07250400001401405140000c0d02d180c180d000401484000e03010604000e4003410550f1032030350036621200201c51155081c2c0300180c20158040c060b285d00a00315058001a41c03224608104899170064096882010068144005842c04800100c81600005840c10014090b1025199220440b60103410280c5159208014130b1008500551051082c0e8482003030040703003010911702c48054140344c0e5000e4078228820b801500d400960801f941c41c0340d5111146007100611030706103840400012030b079580280910400702c450900c0f0204000050780351300104c1c11920880c0004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 766988974 1250 766987724 766987777
    0x9010b0a050616080c070305100606050a081603062619030203030a0b060702061c05010b0724141305070b0c100b0a12030203031b04080d08090a0609080c0706050906 72
    0x17a01d075120301c40c3d1240781d001004100001c1854450301001001c01d10140740c440c4402c0d90280200d088d000001100d44001491b0108103403540c4c2c091914504000031102e0b207828002d1180d480e540d500810403e1b260806401c00d040c200256130f489610f040003542d000e1410340d0000d46910000d80b140e548161166100071160f610340c03049036903150f0f0003401c040d9540b2050311540b618441c120a880700a80c98030340001140a0b81c40215107049a100e1588181c1d5100c0844050804407040c541902641d5900c084807040f03000a6890b074041c11039009100c919045072b1811510300529604002ca10403014401e140c50080d0008003d0481c6a130040d000c00c0e00d02098000c9943d8007d00e034401506c00c80604590400d1680100c000e45c0101800b00c580605c0c41d02c0d8070031100c1a4891442211500e601c509400d28116105112454000b2800802c0e00c3d001d400c81e44031f01c802ea0304c1460060f2090705000440c00031020301000b03180001e1a06090440c1444211070000f011401214016145080280701c0754102e234 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 766990224 1250 766988974 766988977
    0x5190806010905090106030f0e030f040e100306060f03110f100807021615020712031b080f030411030d082e08010c09081002040b0702010e12120309010b0a05061608 72
    0xc010290901030190b81d0b1b9000100544031a03d07600507418a016400309814001104544070000000b0081c0c1c0303032078503050040307800c104018440ca00305c0310340d0b54010001842c140101c000a040c60305001103101d0035407c022040c40081c1a6003881380203038041440b49510744c00762104040b071080c10315507056540d0800c164144110240c41c084094084c11000c102c00d926000b40507452a02542114842c0d51145900c1040c41515107010717002c5144002c0718107241c001d100204107020f00c260403440c102414509400e0701900300b680c045519102c6440780080c942000c100c00804001036180011107410101c8082c146200340d40710720000750301c000c10400012640321301510014541900200496601ca500040c00200c50340205041c0e03000b001d2142942c02564000d03601550760703031200c031032078105143c3c010349403c4412740c41c80741c001400348800502c442052150401441c0100d011980d80d00c0e0802420f421103600000280c454040c81d6414401c50b258202991414085041d01c1c0042d0252818008040d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 766991474 1250 766990224 766990229
    0x6040221011806020c0f030909010e0612030c070608070804020d060b030307080304060518060103030f03150806130624090905010902090c0c01142a0d020d0e0d051908060109 76
    0x42c400140207007401c000380d50f0b005081c2c1091810589096416080030f0039182c0c4511a0900c0c1c0c4401c01c100184602807a947c0034681104004003e81281110740302120300b107030410081010940c00203501002802e07004a000d0b03500004a24000d90103107040d03070010b9444602c1e4040949516500e11010b0840d440800807a4801a0040a003c5d168901072501001801d03044802510000080f800505000c0e00011190305803681515044450007000c01d04400414006402042c0e108001c000040c00351000d00800e40100300c4030700c0c2408081d4040c2446406d456106034100000090001c0d100c0703412034000301d071106480e2014000700b6038026a00341240074005000c000303540b10304a0720a010006c62084014508460304c00000e20169084030510106400100d50f40480ca204504d020220300b180c2801c00300480408004060814072207400c0001260458001c00c0b40b02c5aa9040301c9021000030030440c00e01c0300c030601d401841e0030805036100c40d014000d500f481d010301641201082d400e81c00b90a22001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 766992724 1250 766991474 766991501
    0x20411070605060307050301022508040b0403140c060a0e130204080105130b0705030f06010818100c032924030f070806010f0509010f03060825080604022101 69
    0x129003096041010003080203441a61003489280c0300012103041c18000d54502d81812100010360100c04003210000078031122040350300b00070420001c164801c00740081d1000c0c2d4000d03e000d01540440001c0305191008a41205d4030469040c051321080c04c1d40000e492600344420345500513100c100003414000383c0241c1d04004465401c001c10801420b000145803218640a2040c010031521110310030340e428401940e042c6a450401c100040165004a55041d000b2202c601210001c1c3c14400801d070030121403c2c4985082c6403205840d824069050051880e50742c1c40a010300c1d030064080c55003040607020a141c0c50b000340c103290b80e00c00c12960400c2c045844084242d00442c0c1c2d034070302100140d4940030121895404100040d02150440d44150441e0701c031420b2030b0300e81c03d28240b406c10054501c41500305004040681700c030804640c41d2014419850021103a054007101021000d0000c501500e050b004460107031302400400c0056030724040c011000349980455100f84000d101318550142004540d04034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 766993974 1250 766992724 766992727
    0x40203390f030a060b09070503090304030206090315040c1d10090921200c010f05030603012429030a020a030612111e030c091f080607120c0c0f020411 66
    0x105004158011707003500703813040740c03440000c0d62140d00c2a10940419a12424036600c20701c004e00042c2000801020700080040c125000c020f004412144403840803101214014040700302001004a0601458018144000c05034020f00c2c00e60262034942c0030350320401e0f044985400552060100c0e0b8280044a080c1004e00708110407216003010700100d0000c0901081c0c04840c440c0468409404188680d00f000140d594805450651804645540010b032405505541e078202c0620092183c8100e2026407943c45007090038289070000000c090280104c1d2082c4004034000403d0307001c1c52560031668014411840180c44d040500c0303044001344100d402048404540841c2c030401d102c6403400c0110311400840d00c1c0b8620b44000c0f000346107030f0400e41d61030f1509540700b07410084480c6002041198401405102841c0150100c09107100b444804d5002000540002040c801a079500510150600310254400d02a01c1100c502c010b10360204c082010b0a118002c10b415400c5546540040300121026420749 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 766995224 1250 766993974 766993993
    0xf0509210a030f020d0c050d0e0609030d0e1002011808070c0f080c210706031a03070b0a0905030105070e0409031806090801240e07111005040203390f03 67
    0x601064036404600c0058441c003000310058506c18445d2600316503100002c0e04014800100640745200b51018403030380083c0500c9208150345080009144902e52507079040e45045921050100100d4480c003030f0f108690411b10f10785500e2442d0012608615809200503649080724100780c2a2003807190080c600e81d000c2c801c0000f500700d5000540600ea100304440785410800c003c0e80c0342031820761440c0b146040b90043e01c820400e042c000e0307000980312441d04000080f00d9401100083c200840740d04240c0f021800132a9035161145c0c023003443c20140c58158002c001604056401424034010300c20414865600c4c3c44400c400c062003441c0d08a00000042070002d4070a03141c41000c0e0254095010700c007480d41c6000203000a0007880702100d103003010703030320340401085040102d000c0001c0c0380107080e03405200a14102c0e41810001708000c58101e17003141d00002c1e06062910426040c586031842180c04034822049401c00350f40c8556034100626024107074080810a0517011801e06e00d4283d9a00b80e0600900200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 766996474 1250 766995224 766995227
    0x1106070f03051c150e0f040b1305120d15090902010507020d020f0904050c120303160302070305040b2a0d0e0108061809030304110d030504061b0204150e06010f0509210a03 75
    0x444040d900c1c0360f4105c201035580d000c0c5d4140592030440c0c000c0e21400100010410039909203064521842c05a0309554110501c1c5003040c030720758032441107403041a40d10360001e070300100304804100190844960074403c6101e41d40000f40507001d0300c0701c00703803180c0c141091000855940c52008141d031800039000c03d0301f500c1c0504103d61204015500799001e038200e40361100110a02104803485000410700c42d400801101070110b000f504918801c03020700c40700301720202c1e850b141d00c0050b000407400c640716030428100700d908041c4203090300380e00c80034603512803c03508603c0c41c0c01c40c02e1a034142e442841d00320b05542d110701c006502e0f0603c80885c1c1aa60703456106015925002100030761003207014a5400ca14018840d003031181901d581000640000c1007413109100d010711403c241281041006550000c50715280c00227400c9030456038401ca90101040301c00c0100f2a110300c40c4581c0b0910900b480d4101640b25030340501148554048248181490380c40a1130040c031005003100440380c103004071004840035150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 766997724 1250 766996474 766996511
    0x114040b030f01050406110403020117040212070e040c1505121009140423060403050d060906061d030c0f0609040207050109050723010f0f0903050d05071106070f03051c 74
    0x5091b1000c0b800c015403c8908000041200c0c2181d60617900c0342c0054039000b400884a960190080b80c2c026840b2843d05028401000200080c180b80b1206d032080307090610300351400a100754010f1201c84580d0602c44c0b941ca4004d4162402c2094000c0c41040e80e039152202c01d10128484e0b0092604c4074601101584040d10340140030340714034070071003103112402107042250034038400703180c404581780e8407a0f0300040c0040d101c0e00c0a07189801843c1c2c000704055468549d40000d5034016000100007030a0910f004200000042500001040030b40280032580360301c202003414080361030100c49c00b9100009881085032559411180b405403c81c000b00700c104514903000d9240d1007180b04130520400c465601100303040e4420503280340c11405868680001a0094068035072400c40c1c650042405090702c000008501d0038000c164000a155a42e141c1d6a2151f1800440800d00600054080e900c181b02c1400092462041c010489800d81045900d440c01c0c505184128801d0a01108105040c0007101c0c100c410000c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 766998974 1250 766997724 766997731
    0x31e02040801090b1308030105120c1011060a0501080c040b0a03050328081e0915010303080109060602030f122d04060c050a02070e0907120b1501020a03080114040b030f0105 76
    0x12641c0d026407134040c100085e00424480c09800701c00108010491403402401803c540200384040c0c1d074000c0306460015600c2200c800c00c1102080250b01d4010550708248040c5600810031802000194149400113030398002407000c0c00e002d603075500e01240042c1e55540d104001103500000b2030340e80da6500100041d030341d4990008050301820103612542e40034082c64084e807181c032006084212200c0c4080a1602c0220007401c05580341c020030070100302c40c01086810358044c502a0729542215403500c1822400ca60302c0742c0c0140b0031900240301c0c030826100c84800315040030940082d805201c6d114541c607007804d01d07072606c009100d00512605542110102c0144584200d005100c100110b06440500343d50611801c5007260040c1c10034901440004844060241c10403019011a68210f80f104d50158100110090a031180441001007151941404001c401e54030001e20140c01c4a00f030954024208600c180103000310003030074460300c58460b01d99074001c007480d80300182110044d2a00c881514000d0800b41c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 767000224 1250 766998974 766998983
    0x13021e09041107050d030b0406050409230706020c090403090503032706040e0f0a230a060501051e031321090f080c1c02060316091d07031e0204080109 66
    0x7185102e10b0301e040c280d99100350003201400ca0b9005030301301200140400c00c141c0d50700c00d0387c404d00070800b62220f206d4001aa8411a5240c10300580f0349030138804540c503211804e603194071030941440382c0c40e400b01d1154000b0350f00359801d401c41d46682c6016074040445420040e0544400700381c2400f000404541c8000c017203404d0480149042c600014000d6070310560140c0c401103030f001d0300450785540e1905000ea9100d90070520001c3c101002140d0658242a0082d102d00610941c905000c109183c40c411200146000d003400d80c5030042c45900b10202219012952401c00e00100014001c034620000b01010301f075102501030b1800c5100d024120a1365000c84079040060200d450104078480c5241210080d00c0d0b14400800d02d4511013410010329501c2c8128030314000302040024030068482d08082d5010303120000c010340ca0359211800c002d1408603580e10080104139007001a06540440040f082d0b0401320750319001c5000740da03405e144000c00d40034001100f411840043c002490f118198007100c0c00504ca07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 767001474 1250 767000224 767000231
    0xd06020d0b19091a09010b07060905010c0905090609040b040b07090f03080d18110f0f13020a080906070c031b020a0303030b0f060403020603160c0f12121a13021e0904 73
    0x40429028828150000c1c250300105c8240050207170b264114044c1c9080d5100d0070004c60046169550b850035903462680420100c0c030005003d0100c4c0c07a11041140e0700603015105003603240307010384034501c5030f020140010f000f03079490304082804d85120f8004003014258007041c13003911556074074080d05180d11030901c554041c0c1c03408601d503010603405088a4505908003071651000070900302082800349000b2101035201008400d60f189a458100045001c41c0d038040005032500b41c181405400e10348004c0848005402c498100401c0381d8100c10040a2550540380c60104818a211f514100307699000011307500001c0030707200004040d813381000041c2e80c4203603004201c0f800158248a018011804000c0d444a41840001c0007900c41009101058076686031503a03c00016464a030241001002c0907200003030b0b500301e440c025941100d4800040c1600d040300304040c41c40d820000c0184074456a1051184008191280d40004280c0640700400f010407106d10100d45d016611035460b502c5100000e006605 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 767002724 1250 767001474 767001491
    0xe0f0a0506070f02191401022a0c0108010b070b040c170604020301111215150f0c0d0801053f01050108100203070819060e070c0605090303060d06020d0b1909 69
    0x3000c03a110082d01e50b038811045c201a4103a40c3da20b01c148407541d9844081d0f50900c0160201c0e401c6443d07040320040d11429042009000d0040d081c200004440281d042c4006000104280240340c1d04036010310303421100401c61603c9514103000d00718041d03031203c5d0110f6081600d012200c1404106c0f203000b244201c000f00003040c05050040401d0140440d0b198a02541200041004401c4010b415548000504202144440740915419608201011085144041280800300504220b85520f6092a042c084c10542c94003002890240c407c4145101090400c90000c3c40c0d602c071042c01d4914588042d00c0c08120704200251980240000d20401000d0b10410078100f888403810310032a40600d800b584e0f0b114459450321010804424925103000003a680d40307d00003442c1002151950080010365140780010724141001c40039140e0140c03885026030000c005000ca1595210b0350310010a51017078000d41c6800007810b901c00140028400150005580b5a5a0a02403032405003c0305540602104000601 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 767003974 1250 767002724 767002727
    0x1090b07060203190c1205060a0f1e12020a050d0204090b0901020c01061401080f0403020703080301060503061e030304180f0504060c1803021c05010207170910031803030e0f0a0506070f 81
    0x20b50745c03004500072030320481d0704014180c17294101640c0300b40c01816103440d1a964035a1100c0754010f030340c001026101c5402c20f510108659504040c02460b080c82111083e000d1600003a0640303c0611071180f0410040c10400d0854603280c011846c1250041420381c41c91a02d01c00c828040c3d889030316018020f51a00d00b010845c0503003031401806294042e03546010340d50300c00a448801c03042c060420380c1903120302a40040026144d00085000e820383c4e5640780c1d203034200308003070041100c1100205404d04040c2c80003020161030010986080311840703c040303201e0a0160303002034001e0980032100e001150804041209200c1e031a0402101801d4650b105408205030341e0030403901900600000794010300480d062024a0805010425081c0c0140001442c2c2819aa1340c0d140c1821400300e82505030102160a801c1881c1c120480103040c106400e090103080e80441002c8180c5c3c3d01514000c0605940300039048440e282000322810a03065030040b1900d6030202d0400603641c2000f1105680003e036111804006903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 767005224 1250 767003974 767003981
    0x30d05040308040b030601110102340b0a050601140d02031005220507050d1506020c030d170705120c03240907030f0f060b0325020304090b01090b0706020319 69
    0x22078001c2840b500345801e040d9000c000390b00c041d00c3d5504022840318940e05005003031008022940f03202c012181a1102071092402c80803d040c202c0c9400b40e860380e0403c01091003d4210317a03101c040d40d4030005444d41c8130790060700c0c009803844c0002c4501030041404212080c4950040d402910b00c806003d4010f6940d80c20465041d400ca040b10f66801c550701c01407401083c0c01e420a0307811000d0b41c10094106590b2801040c1140c0e02100240c420b500314990400540e034050100060402040d0b014040052003508090a901204561603640606041c0059803c0c0d03c00d809464071700c0020001030b810b40c1001100f000d40c40d00142c40c50b0740381020811400c0350f60741514460b0784141d10082e000595940d07894505900810b013481c0c8050310a40c130765001a0340d41d541d9100b680007510012003640d44909007410b0040606040c0d48414034001c102c11506540250004181c4084920305140414222400801241d030902903600c49000a81c000c80c0710300800159801842c4601900406868125013111010054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 767006474 1250 767005224 767005229
    0xc030604020d2004020c03030402010e03013e13090507030b0109030204050a060306050a09050c030f0a0b0c1903060311090708070c020415140a240f11120405030d0504 73
    0x1103200c078003014000840510f80011804000f10341d104030035000c40c0106040e82d0255690206503040081080110341e007147c0d800c5142703c0305800030882c1e4010941c0c8141700c0e0141d03401c040d09480c2c0c08003e2000284000344c06a00200c12010050f84900741b02098512a102d5030048940e40390611000a141c07074801d1041422801c1c05950b42c107119031442e001c1c00002e1034040d03d000314a51300c80c000400420051b01510740609600200081c648950303092050405003c21100780c801d4010540d105400f0b41d0016452501710781220200e00e5584420b0208216445110f0320a04203040c00056a007050785c061384840f0841e4010606112000202410890f0703082080b94080085119500890b60443c825640c42c802e062001d480019000392201c0e07034541100c00e951144c4050006480204142c1c05c0c004004001001180b41240c0c0c41c1c180d18140d00654400a00d1300c0d01001b15007180e14050a11402da14400010014250b46010f0b81c0101c144025901601a01d8028490308920004851045c000c9808 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 767007724 1250 767006474 767006479
    0x51e030909010911072001021006050d02012a0501060515030702100e030d06080304090e030c0309100c021f14120606071106040605090f0406080607120e0706020f0c03060402 76
    0x16181e083c0340c5414002c040c03e200070341c4d4039102440b00b80c0020789400f481e40508006444000406030b00c11000a00d4019441045052141001d400304500d864500908503c41d0f82400c0211111070b602803a41080000c1044c00d035080b410600800f414801c040d4413000545030241c54118540400083c01411071205848440050b07100c0c00060440c2d101c56840840d400640c082564a44480342c01d141003581c0d41038105054541000404101c1d0094034407480210980c003401450a05401c0390200c3c1c4c40c0e0080e840b8150055072050703400851a0320030740503001841c0d801018240b10350340d110180c2c103013500b50b8070711400440c1d8a099042d140c2040042500c402d150007a405005036030700d001c1406402d8108004c125041d030303440301440751070781d0341c220280002d0407003642c03503544a17005401004901901c1040b024003940c5400c00030b0120b10400300d12260b20041c641000443c582e9140c0f0031000400e0703800d103010900d0041200c0445c0156002c2011542000c0b0321041b80d2000c1c46030001c00d070302d9144c26a4002d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 767008974 1250 767007724 767007739
    0x506010203030a090c0801020a090f080a03020a06050a20070b060a12031419050a0212030c0d0b0316061107050306130b0712050114040f0b01090b0c19051e0309 70
    0x110841e030f8035002120068800d03222220700303d990710940c0d030a980005200c440458030007a800e02c110755907210400014212040104034114070717901c010351a403500784e002416103134541c00044d403560749070f401c610100020b50008448142c07a1000d00502604410f00071a54103807140c02041c2585810b9260505580b0200c0c070303510345005546d50585002804900c0041055000c2c02403c980310241030308d6180b80401d503120650364191840c4028103020711000c440421703034018020321946c1503560b000d48000104001d00064117000c290002881e000c0885041001c0c441b82910100d6019881004003c00c6840c01080300e03e4140c03034104054031a00c6c2110f6060600e001201c80e00d011400800c0040d40000342d5003410311030310011000b0710060310400d03004212046001c50800c0d44030300f814802d4a4020075824400c1000f680740701c000030311294191007207902000c0c0219a4070204803041c804030a00d02d8201090545142481c03418581320121a0286c04502c403161061801400010085440101c001884203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 767010224 1250 767008974 767008981
    0x403080c191101110f01060e01080d030c020c0f030313030c0501030b04060e0408160c0e0123011d01020c041a0307080316020d0c030212071e06022112100810050601020303 75
    0x1100d038071a0980b4020744c68410904c0c1100241002c1c481e40c0058021000101c10035810442da0f07614081d1074202040030140303440b00803041c40764080784145682c2400c85106000d06000c0300001e107540540380704034682c010381c0c00f000820070540139020001c03a1000e0b01e09004003aa0007080000715a150700c40e607058011550001030000300102d0042641c0780290440b003401c00016101c56004c03050640180c080d0040500041c0a01c4c00703a030441c8240e84003000c82e502c000d810a100000c004280c05248a1700001401070038040d544e0080c004e40b500540007a200304250038110351103c0008100c030503400c1c0280100c21002c00c6018021084323891000005840301100c04055081c41101e00c940401075031107003a0242c0201c0107947e401800c428418182004001050400c23605000500c81c0041d075076140c01d41c5810400881d034022522702a18200c01840c0b460250b11050b03030b8209840380a60f600b609200c2c00040181340b0741d04401d0202030f500d0300b404544d07407581c14403030900031540207440d0540540d00c00d0000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 767011474 1250 767010224 767010227
    0x20d0822021302071e170406022d0d021b03012d14040b1005010f090303140f2b090b01030b0402031018112713080403080c191101 57
    0x358003600390307001c2c00500c0c0c52a103407102e03004140300d05601a8004000010f0006005071004040d00e06540010180d1405150010207503580d403020f13045401c1036a000c4180f0390005022413003004020b40c40b0042d0380d600750304618002e4481c640b44110344162451244001400d080500c140207002c104903480e809528081c80c2205d88003c00e00c05600c1d44661203507044050400034041d69030140340304054001c0103040c14410844401663f8010a0400603018420384400343d00100721801c40c2c1e014100750000710b1600480308190b1051166030000031000180428819184500720a050710420b0344165590704003c1c3c0200c01d41d00340b10f0000d8220031000d80180701043c5c02c0c04007140c010384020100c40104010f18450420382d40442800e11903000010005000d00090b0420802401012175542070b4004101002400802e6046e62984188648000142c00b030202841041382c0f56810044c2d041d1601e99a103014621036220381189147d0340182c6000484800c6903805d00c0c00c200d50300400850701c144101c0700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 767012724 1250 767011474 767011489
    0xe010c08160824030d090e09060f01060c080d090b07110102090607060b062a070509190203040201110a0b071d101103070f0c050301050606070305041202011e020d082202 74
    0x41d49494a01203d9800601ea50820011540da42d298a481d00c9403442e201c40300c0e44605009100c1000c9410850402c42d020388140401811f40c0d41c1e0b4180110501c0640c1070510041c083c40c0c110700c0e01e0380d1038203a0490a00c540000000d11650b4190b841d08400519801d41609038015911482c1c2c00207010300c15040000c3c0780e9003161110610181c1540d051080202d00c8826444c803909104c07080c100c1415010940d4041846100083c0c4410781e600100c07424490307508e005000d44401111115907000c03010804581c816906458414038000458210300c260f8140807000070307810754501e0b0124084c1880241031507012460040c0f6104003d2070700c0c811030305e03c003015142982d212040c172105000801c8020b00154480e440e0600c182c1c01026074000540c1070205041c00c440c001341419100e14000d204580000c1e50000859095400c0e542c0c1510115000b4401a1921846c003126540c0b0385064243d06200780781c4c00a80160494a240d50f00921929950010701039440182d40012120b03080c05040000740c10800d9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 767013974 1250 767012724 767012761
    0x8030948011e0903020102010e0115420f0c030215091f02040515030c0d0c0309080c160501051303060b06070827060310150c060e010c081608 62
    0x41c1540c500e56110906002000c45000b19004121001030900540d68241b260b40c1c0c408811500801c0781d401d1001d0180d00c2c4104521410300f80e80405c0174003403145070034a8680742ca0380007250f561002200080b628200e003000c00d2404500000c02e010151440d943c8284e003000201c2c0c1d00758003c2e00c4d01459440d140b02402d07100400b041100c2c441ca07030b45040740c0d00410448030b00ba260b04e940010b89584c14030041184060406c041040c118030284240b1213044908400c4443c980150040000c000c018041c064010341640b20018105030004115140380020100d003071210068108442800c041c0c8500040d24240100000c54038855080c6e03405200254440e41320744100c540060042c1d051011300e41d103000b0b09600030401682000c0b45041103121441800803604281c110441c0c0c1141145401032200708202442d109401c00a20313441220b580c90781c001c0100c0340603d6040f11f42407000700d45400d035082c00b03080004020800100c0d03d100007001c00070229440403140413180d40c6c1035282d031503080440c1061603402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 767015224 1250 767013974 767013977
    0xa0303090e180607170f062d0901030f0615063204030503040e01060c0203030d051306060e061008190b0303121018090c210803094801 59
    0x8590780c2c611440401031a84904c9055682c01c41d142c05c1041c80001040d800741510b40c0e600088010310901c1e0b42c81da00d08441c07213002020742c0041104481c078054905d0030034112054229031554004818030000c8131102c0e8484e4008e00c03080c0110303840c150514082d402144100307000a0440320b4400f40d2044940120b21f03a4140d0342c994050b4601f454201c40910394080c1c1e108a5079940000350422a1003041c44219004241c0340c2002898041c454001c25164403038100000011640e650000d01c20305042d14860110f2500310508200d8907482c1c181c0758103603040a54006100303010302000320703807054800c2411301d20845070454280c02e8407454506140161040400d5554140424000200c448000761a12803003904d0340040d0a111078a44111500303141a403c0318119114245800d8074041b070700d8400c0b0007089a85110704110b0151003500030352181001a030f0014400360000051002811000801d0000407864805480024136048100c0c80142098092241000d0034508150f04190094002c00c0d42840c06 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 767016474 1250 767015224 767015251
    0x210303052a09093403061509050405130215090a050d0602030421021b0f0301020d09061d10020a030f0c020105040b160509040f060b0a0206010e060a0303090e 69
    0x1014058001c008900340a24511040450b81903124036010800e00e810500c020300b65a031482ca24046440c8090502c2ca1116640c0019090b4030413883c8aa070003000100005507220941180c2650000c0042c84144100d512030303420040441c1c068441041000708160303000b001d101c0d00c200c8000d03070151070350040203941c3da018001840000340c0d500c40c000c8183c00d0340e12860300141d5a1800f450030301c2c5e80b0714003030000c860340320140403194200540000e024500b406a4894004040441c01c0c002aa850000c0e0020768055002140c04005110560006000507200c0d503004d024010003c021084445404100c40b055540408190b07100300c0c203198002d04a130001484c02049107224540c07940161041c2001000050395110104014805161030094012015810310000c18090980c000c100340030b03680c107180c40b45c0d5450344401d10304805580082c0041c05014103a60302d030000c00001a480700424896824240701d400005022450103001d0042540c5d8141c40d80040309080c0303101010790745030040c4040b050012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 767017724 1250 767016474 767016511
    0x70828060e0705070605090a0b040f0c05060c010c170c090d0f02090c0a020625200105010b0405150708030a020a0513180b011b0f02032401060921030305 67
    0x10907010261042c038542d11a55501c054034900360f07044580040c0001c80365080100942d0000c1c004614079900701d900403540c0128400c03a4200804107000d00d0380221703480070f80000e5420103007074190409412041261200da0103000090f40007041400100c81c1c061000300c0070054441640b6041c110a4541406400044c150041030b50102e141000155603e6844440100d080785140d0f90402030340760b114080c5c00b10f0341c2c85580c4031901c440d01300c1c0b020507103030b4140a00b0441c4941051042011841d210000304001d22455039074900e03024031039016000d43c6000b9291412884400e0a0307c600321040264801c3c06a40b4503500d407a00c0d10025080071403078500b084020000c60030742070540f051282c007400c48104421451150740031100c08450b04031407460705124000c004001050305004202520940207096a20110090701c006410005850aa4494901d10b51004d541c240c0001160b64141c1700c26460381c2e003a01d62514920014208a201100c81743d0701072492480000e4820f03041107401000180d5074080070312 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 767018974 1250 767017724 767017739
    0x2090c0f0403060b04050606070b01051017040b060405090609060106120b040e010c09090b0904080a020102071202060106020c0a030506071409030d08040c0f0308220e010303120507082806 82
    0x50055100f82d51484d260f955180551609114864000c0c0080302c401d494181c0d51303030355289210414071a491180e1082c110314030100c1e000d50545081c1c10402034a4003154901813400700c251a2003940c1c990f014600d0007000800648000880034010002540280074980ca040c0f011243c402c11042c0a2030f8641d02d6a5100b07115444030300624a171941c1e030f400042040c003401003000700b001e0410761010542034101105c41c902512407502c02c070740254202010558a90a03000164068070a80e0001094a020003a1350f0302010750214046040e0f80382c030f900765030404d00d1a00410200124500015001c1d410003400701d03903450f009402c1100c1496110148a08015400d0000307420f100380c0f000d010011500d01e02c108000c01844003070b02809400c82c495454002c40c02c680343d13411503004000d01829010300040711080056108020302d00148103401c05002c4560f164500242218400e00d505c9068034201030105001d00e0141c070406100f0f8054000e02020740c00700106104000d064190350081051790b03100c1c0880c000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 767020224 1250 767018974 767018977
    0x1e03150a020319022d130f0305010e0c130504170c01060f120b2202101e0806010e0d02010908191202060f010605090609031e01060e01030f02090c0f 65
    0x1034008900060302d03450300000c40d455481c490540d55a02610402c0020f85880030f40200c0c80014120300c21041445c4050000e101592258510105200086810004025000d21003c9058912482c024040e18a00800301c4c1d0365400c5803030640d80d1080b9683c44c441d1604a032684060b500901507044942e5500070b65220345119484172030028416519200c0521003450201c2d1404010120025544840c9801e6103445080c040f01601c40f090b008200348104014502548446240c560020302107905010b209002601905811111808030040c0101042059004a040328801d40c81a1100a9500544010007034402200702c0c08a05100040c0b00c00310f041c8500300060904a05803a102001185850900c54820142c452204c81150f01c00010032200b40d852100180c11600242400390300e640800d00016450b0040e49903c9405104520380f1074080740c5248040508901c1c0c642c001c105180d15018101c440b24130900003d4103d0302e40c05080401801d0901c41164441110f59000e4280303603c40d2200c000c0c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 767021474 1250 767020224 767020231
    0x30118140408281d062802010e032a071505070303060501032f0708041e080304030c05210a03090e0603010902090f0705160b1603140a0e07050301060608040c0e04021e0315 75
    0xc41b045a5030780e40c05409100d400a078004400085043c4502c04907040d51200c002515a210482c81824100090108100741000352034480c0741c603c0300310701241008000d60028202900044d052500028295000b807040109171b65148800d40031026400901161003e26003107800702c1920100b00860200300c614003d4409020000040c039807480464404041040103030b082095a5003081000300300061460f102c000460343c00f6184007806c0201c1c0e464000007100f5104440c00b06024400e0600c040541c01020101980c5240401034003544038041498200e9000c0a002900080e484001c503100300c802c6800c4941c4000c007407418070f11308000701d21265031801d50603404440701000c813401e201c6c26240c80c07041d08000802a01c1c00f0820071000c01840668030f00080c000c4038607141c0ea60140e08400c5401d10400c00504400360092041a41d103150017000100300312030949480c42c00c0c000105141d051510011b0040d40c008210586101029418100b0021003d00140e407500c19882000001202d12801c20320 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 767022724 1250 767021474 767021527
    0x2c040c051b0c03071a030406090c090609020a02060709060e22060303020706080604050f22120c110f030d11030d05130b0603060705030118140408281d06 67
    0x140c001c0345000341803030041681c020600c2009446020070105d86139806495105400c14004500c154260411000e000c2c825006203800a08113080400c0340c98082e0001c00304c90000750300701c0d41e059845070022034120815000302000115248428a041e282031005490b00450300402810302031080781c0e03000c0c225030440d4012009a003000300304001c2542c2121209034042c5003600d042c0102d10b0005929410314900070310320582c407101030224240c010900715980b4280c0d0381c000b100c041c410070308100103011071103010821201e03080709501d074450318140010524154100500205248440000e041e1341600707140c1c401203030902c02808440007241c3c003170203424020070620b03900a1040c1800d0501c1d003040311004180750300030340c841414003200230b50242c2224119004000803003001001070100b90068082e07107032010300d4807042e007050000384a0312000031f129650700710351114030085400102c6a008608080360300046040744154011094401d00c84910141c00101203616048590102e4071416003502d0040c030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 767023974 1250 767022724 767022733
    0xb010e0a15080a02040806011203120f0e1603081b0f0105010b070c0b0913020912061f0611070b13080303040c08100612061a150a2c040c051b 62
    0x501c601d40090b10719410040306036042d803400b42444502c0303996603010311810025805803c140014180309107603100405108034000c1c052804000c000c00b0251584000719802c074028070b001c082840c90203010703260031a540101d0884c10400b507130780201c25480e9001c5100d40c050040c502c020007004000c0c030860f40030306410a00c00c0c0c1c440101b400c01c140711800301c3e00b041e44e00240c20454031032107607100402212256071000015a0300c46140d40841d1012400030000d031610320982d001e101080c0c0f401d40303200141c0382c20707500400442c42da100e504503034480034510700c134200d90070030703c414032595070b4107001400d400102030410303040d0b07955900310103103598022a0156010b070401d14092169800038041464004840c4c081400618200f112021488094100c0100039943d107226003031a903500e40c8803107041844000c007910410111095902e080e680164080400500c07142000a0b443c094240c0b010a880c076a080a0074003e03006005100003000c0c220104001d102c02841100180115154031512610b480340140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 767025224 1250 767023974 767024009
    0xd09050d02012f0c010f0e04270305040911070b0c0a02160801020c010f02040807121a070809160b030f070e0402040b040602061501050304150f050a0501032307090b010e0a 75
    0x15040004001300c1da030400007500810f21500d94802c094480301802101c0c0012412086030b29002d41c564940129903502a40148101c24150040090821140340c458240400b00c464000c040583c03040c808001c00c0304158101090075005094040c100290303140c0100c4284032402282400740e07040e240d011284680d0002900d91207000203018603064099807480950034907040590543c2c40d00e51034040c41d024110380c0400c0605010902c601d942c0b51403400c40101e580341c01c081c40000c0003c10101c07580b4002d845a0112801900501c40a901c22960440340345420358661500c00030f80c014003e01036004000d000c0c00b2110681c0d44920081000304400c401d8142e940c1e24240c40a401d00f48000e00502140f900d408410100742d03003203403c0f240e0255014815000042103140c00c0070007004c004c00d500d6100c51411b42044481c404690009c0c0c140c0b4013545072121b2148010b800c2d010f9138a0405010701194101d40401c0080c03200c1030f081480e0070513050410517612802c3c440440c9480620741c1c40307101100c6d00780c5280c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 767026474 1250 767025224 767025317
    0xf051003031e080c0a030209060304060501031a0f060904061506080a0609110405040209030a0c090603151e0f06030f080a030b100e011214040b01050a05030d09050d0201 74
    0x11100b4030462102003142040000c082e00c244801010708002010001c2c4003c26035100358100e8581c1c0d08010100e61700d81c101400c0113401824240021030318644c0c0d08081a00303111000c480c00e44507025a4a0001e05540d8032018040303110b202401c00c0b5041500c0b0540d840004501c10842c50150a5565031079085180600586086d24510b510030000581750000b0040c85440c008101c5066071010b0302c0c0035942c2e91f410380200f843d061542d400074156450320800800c00d131055401500440307004885410b11010404074010071a403ca001503141e60001c805c070a035520f0525084904a14107102e00015405d650343c4540000c0c111100003250b10250000c0d4400d0389a42512407024006020b407181e900900042102424070f0000316079084c148000010700411030307102074001c3c3d007140e40f075018051413504040c138140491400a00900344a0415260f001c5110308001070580140b449958501184038500828001c1b60008604207a041180c0d00c41151500c600415140340c807038030500745500560314003001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 767027724 1250 767026474 767026487
    0x30c1401090201081305120903070e010810060b090904031808030f070c060806130906020904022703060606070623090706080c0f0f030a0e1608060604060f060f030f05100303 76
    0xc07101c0d40c5151504180041040081d031f01111301e207641e185555074081c510019203030a000b0392040ca03205408000115002c170f008a071014105801d0b11040c05940d46a000d5050b05000300c0320980d81000c248800580807074400d0101c480480e0200089040003a19903803034a0440c1e01003420044a200c00045141c100040040c014004106901d800e1000382000310003d2002170450b00c1d0458025107802c014801c0c49015030442c0c050440c0180300b15590410900c00b4a904511980e26400d50011706d201c02e21281004580b152003400b00820b40b0b07243c42d51640c4c1d00702c0240b03c01c003515070040141c04901d4403d0080780203514014110300300100191340c0745c144000c0c400640101103421741c040034484284000c5103041640c2e0f0084503455140d03203c0e516512a0300c014205e182c0074a555120741e002c041808005282d02d0030545124009503480c554407801404103480052203034460b24101e6400401005100e0110320701800031614012a050105080718130643d5019550381c1c05140f0b4001c020002c041c0c2080c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 767028974 1250 767027724 767027731
    0x316080f070905090406060807141f21060b070b06091605071217010b0a12060f050f0612010e06180405070509100b030c0c01050705041809030c140109020108 69
    0x200361034100c1c585600d008008500521805018076208070110301006141d03040140a040e000c8102c44c0f0140d580c2e0102c0700f01d4540701da40030b0f01828040f411011603079408005610119615114002c004620004000702c1c1508860321a504d1942c6c1c000101d41002000c00801ca1540100d0171451b840c1410307030802c01c0110014000d00c40b0007121018100d107258000003510100303900440800854207086d407068402d481d4080c2c014001d04204030011403481c0788040a17000a600a6554900510400c1500c6044542c603015030700a010380f0100400c26440c100820010118000d4042030803e20000703e94000078200780c10071010b60700714800300800c5042020be10030103030026035103e0741c450805844098440c00c580c01014014a1404001003c21140921000003000c80450481ea0ba140a107005581500b00d022006115420000410f1803d80305130142ca0594041c2d07982d22003155400c0f400b10000f050b02003021800e021444100384080744e000e640c841e2200c02c00e46d002051030265480010604c00b0004d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 767030224 1250 767028974 767028991
    0x8030a061a04123309060507020d142104030207090b0d0206032403030c06100503152809050d030c050f250803040311060a0606050a180b031608 63
    0x9000c10000c0c0100300e001000016000182c2519861144c000d011944440240349000d082d902c1016101e802d4080d0303c42c8002e6405004108403136240e21718101c0c6c03580b11160061000a9a69180703070600d1440b200140203540c003001200350300b10341102c0042c0c450a81250f042c0c004da0000c6604200c03001080c015958894811550303060400d190354001040380c00080d21034189a44d1010100500b401041541c1002100c01012039803281e503441da4203036440000f211a06601d01000c07500140504001a400c6040b840d00025910140e951803903e0800304800040740485d9440500f880c107120f0460301c034024026000e5005000c2c1130741624000b074240c5401e50040f0701085070800c40010180f2038441507484440d8540224054000c00703584c0c01c1c1c40d018640b000603010081c00000d00c030801d41c0042d81c2c440045407600c245c40d840d641c0c4401d200c045446910805010039800c01c082c0459521420311f004132422a8200c031600292502c4072561903130000c96007049400401e008240509800c1155a03611003805d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 767031474 1250 767030224 767030227
    0x1215090c020f01050c0406080c07020d0203192108132d1a010807180209040f020403140c060405090c1e04182f0403050319030c0c0f0206030603030708030a061a 70
    0x407c0030041001d0402488072205440102d48181159600d140310451143c000b400c4a0401d04100f0a000101e002000c0c00c81d2140c14100c100c03900701d60122100e0072585003e0329480821f0351281d40d64914903103184411503140700713400d501c01c000ca42c1464207110380c62600094101c540b20140352800802c0480d00100c03c038074010f00d00410941c01c00140e88401c2e901001d2100341c112082201101c0a0700844500d50350284c10b0984181219207150302130800c490055a4101048051114030b981b600c0e88288201e82055041000f070201c2c2c200f201456410a03e80ea0440d031410002c00c4040c00400920b4080300308150380018100024003904140d1a0103101d922401c0192403013030135140460060f4521006215a20503118506503000382e020b540083d5003003c1940d40c1c50803a100b09100243d24111f22401091524603040441842640b55010f01a84610400b0b9000040d80030001641c00c01021070b507162008200d540e001502c410042c3d0300660005001040321400c125003035449030b500780b1440200f00030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 767032724 1250 767031474 767031479
    0x230a060c0f03111912080106090e0c030411030102070b061f0203030103120905030a060e070608040b04020d060b06040915150518010903080415110304061215090c020f01050c04 77
    0x309151401c40481d49401e10039041d0840d10002c60a2608120300082c5804103403007810207110a403961610210f01580d28002142e807540c506861444480c042c00151000c0400026030710001c4030021034109008003601509490400c00003800d992205008440c800c02c8442403040c030341401d049500e00140c0682115441d6400d2500003540d9000c140300140400c240602c030403501d180146141c102402015050718414207450400c80090320007415481810f2107506000194903106001d020300542e44840c4003201070310345400700001c4042040c01a504155600c00e0048607641e4580100000c000c42a00032918040d02486a46142580d9004000c480e0b03481c1180034443d680042101c1c0644100e0308105500d04030140104c800c0390007504020800a40001c006c212480d904c20806103400c100d580c0c03003039078281c04605c040d100c0c092449410041041c445e980c510003a0b0b1500940858588003807495a203070b0740c600301301d0301751350300c801c05c510158004800c07905400c04280205035201d00400c0c0401c0c075141c0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 767033974 1250 767032724 767032733
    0x103030e04060905091b19030b19020702060f0d110313050c030d170702030705150105030c1e040209040e0a1406130302120c0a120e040c09030203060a1104230a060c 72
    0x111105401280d405901b80455069a071403d000b445012009030700c030245a00e034039001803002da05503004100210040c3d10b0311006880b6000711540c2a5016108606154000030102c0e81c94104462607114140c81c1c40302c02180b0126980a180300d065044404800e0f1280c5080c1203040814100110340039421810010b0400c41d00070040b0080c80d401d1007440a2642c3c0c2e241c00407400e500403050020914018601015090b0140039105d606a42044081d102150300203000c0050740d02b00c0c28000c1c440c40440e030043d00780e9460a0390207020319100140000c100c5518100b406414800f6013401107900d03600c0c0510f03e400040c02001341944c80503014845140c3c100503528040d590304030040071134201c0e002c00540034041101c244190084542d000046501c0c8548001000d445080c00341141c0e40a00c1c6041d4402074040d10030103441007100e4000d00a425161603040104021b003040780489000a80200310000300c2544500c0d05250100407074444100082200d02000301c0210386078080c03000c00018510003000302e07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 767035224 1250 767033974 767033983
    0x4150914060705100c0905040b0108060904060e100f0603031808060406020d0209100305070e1504180207080c15010905041a040519050309040f0c05032d0103030e0406090509 76
    0x11039003150540d4803071280b490403a28103c00c2c02e01078201181413100760580290807980810548908440910040081c04011101001c0859180754000b0b0080042030104a0542c402e540209040c07050700e040300b072003107000c100765108031900010003a074a003002c0091507070010a404a01e00f06106a50400d4a4401d4007075650b580500050840c580c0050b24842d0390021368110f951480c8050420b4403840c03c40980900207100854021000c00e40d9044140c40c00d02d0b1007903030406c0c81d1040303c2e0250b050504103141c101d03c001c0c03440c0001070705960030080c3d14082211640981000d4804500030484d2518000c1420020034040c1e1040b941c2d1414001804002072946041c401d5698001d07100e40900c0e07075181001c624110036100c10f0f4224040780511002801800710043c1461401900d040c0a0814400b024108440c03d91410f000055010310108441600c108540607132a002c4010b4125900d40350100810440b40c00e90044021842c00000018103042c2801240c005002446042150340341403070707995440703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 767036474 1250 767035224 767035259
    0x90c0303070c092c03030709090c0221040e091b0301090b040b060f06040605040e1f030807062d0f0614060c0a0b0c0a12202b02041509 59
    0x541c8440d44004507501c40c1c80c1c410b140c040d1800c2080001c4c603101e1607903602c070342c400d460503400200ca0040c082071007041405a100360b41425070041039000a403c48020240c245800345503181d000c10000002c00f000300310078182c01180e00d44064444003000584420b00540140003040c002c2c0d062805413004114100309850f400354126107818151750f5a280001c22a50080200c0c6600c0100410085007165100015005494442850044640341c4c84190624030f500c54074080c0b40b5400c0c20310184002030080018045c0340e44140b0303010410b1703000001c01920354000c40e4505091007280c581d0444245409000e850b140c044850010000c03a8104403414048640d103403900307406850f0001c0e03400c0344083d00304144550107400c205010101d0500e0b8581c0100c0394040340c0700c42d000441040107031961612500c030f2071190055440d00d4013180c0c0b02491407082c440c0c0040c03601545800c1210403030001d03a041d0402941038401d00010050381e40d42000305944901d5031003006402009000e14040c44048009040e8400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 767037724 1250 767036474 767036489
    0x7020c030601090e0a02030d1d0d0b0403030c020f030301090b010e2d030c13060504050c0319090206160b07092709080403020a0b0309010b10020d0807180e090c0303070c 74
    0x240300c13080c28922450500c3c1c0280c000d41600c42c50050301c2501e5405100e44240011441d00c0c0680d0010150800c0451440500d015011003c0c04000c034001901076413200410390110300507195040c0d00700c8e80c52401e64000b43c1c002a6869198083c040d503039a8480041104854211000342120002144010a80341d1210020010f40350100c25159143d0b0304200c03110341c85030700401440e011106040400301501c4144901c500481c02e00c0c2c00300c1c490089243c141ca00c282c0c021200903007116035002500010301510036040e60030032810003441303140c1d81808041310066405107a01240500306160000c00e400d503a540105800380b00e402048d03a15881800300080005940000400c9036080e509000c02c05215590000b984050900c100180028403200990710490b03480008209008402082c08850105144844010303000003060301c00d035034014400039030040741030702c0d10440c0d0b280030000c00300c1c540c0495008080000b041c4010440300100401107a2944071003600a503003800c103e41e5039001d000209004900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 767038974 1250 767037724 767037731
    0x13030e0607031b03050f0a02010618060501080714130303020c03060609220c0807080d030c0201051b2a1f061d0c0c030a030608060709030804090f0905030705070e07020c03060109 78
    0x1001c1c548600190f50b0940c06011041e0340c7c40e140c4420280c000c1c00c0c10b1007400b1070361581e9407075000510300c40d12a043c111a01a11180616a1400c00c110b41c1280f0001d400351400038140700401041c82c070407036000d002e0341c442d40042c454540003004151030b0000042a0398480c0c607e94041103207505041c00e0000f05075004821904982e01c02e441c06040c44003c1c1d4000804038420718000148600c4c0004a100ca0300c42262800c10144000301c42c22400d0300d50444070f440446c3c0e420b10b950851400c0701d80040401d503041e48090400c0004240c00191904101d03e011007141c0d00c250004020b0515014001134940354a401c00c11100c0d00e481d081049140d41070184000e00b21000000074880034410b02100c9450030b02c00d099075598418140041c00410710750080000c80c0c85400c000402030f5000391811015250810107881c2014030b8031940c20094401c10005c607040944600f400c000080b0100050190a03102e00c01800f001400e141d03088225a00080000003127500c032040142035900c000c1000c40c150b403402d51020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 767040224 1250 767038974 767039027
    0xb0a15060309150903200d05161b03030f110a2d1703040c140102060a0f02091c05012904020a0e1002070e010b130b0c07030b13030e060703 61
    0x345962882c50302d000034a18100010b6400705075202d0914500311840501481b0f1108091940ca0383d038a10243e4000007141040002d40b00320030205500001942c41144040c801d01200038000201c661a6402140032800301104d0104a68004a00d440c07030712242002044040034646450f104401c500102562100c4200340f01c0349101c62039250f01403115042005070295003022001c9908580c421241566504da441c0b4000c100d01c4c0b00040d4044048605a00508180c1c03a1840303130000406251000394840343d03003041450a42d4031000c8114103a04818642880410b000d802d149003500c04415441804c001c907801c080d1100201c020340c101100005507030050711100500700541d82e01d1200408150302600303a00e89a1725903580014250305850001c00050340591303031520501000d02440000215034140860b0601400340036401800d1503980800403a03d50603a80d454480750138109550349815107403012005014103030450140a000f0b0001d840130380ca40a41038800525954544e00c0012044071400180c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 767041474 1250 767040224 767040233
    0x61b080318031303060f0e1b031f0501080705010503040201080c0d020d0203190c090605041802090d230307030c0602030604110f04030209090625110a0f0b0a15060309 73
    0x80707011541ca004032956014816241c08001d4182c3c4000c0b00c0c52400d02c8101c0444401c24011f1580c034090b100024120308000f4900c084619441c3c0c81d50981522901c00111000d100e0a0f412440c0c0d480ea0020000700c65062414090400309550800c5050107410400c7c8001031740d00044040d841000152290340300c12503070191720080d115a48010165034004420720056464810036117200c080040030803c0f00c4c101d044802c0e03854034a04d11031107000c03900a100400107503e60558600c04075011600c01460140d0f44000074030315a6020340c1c25100d104c500d144121900040c10031400f00051740301c00031400c04245580041c240c83c10020010403042c0c010000c5000f5843c0d03500079881c50314285030b15585443d10b111801ca10368000b40300a0b8868074421000c15071800010441a0003250303042a00302035a2400c0d8080c441100001c0c0001007004401c4009100e10101803046510702c81c415031104600c110207051003030a0071000352010403241c0c0b8190803070308254130300c00d484000c4880c2e9041c040391210403400c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 767042724 1250 767041474 767041501
    0x2060c0a0309080426011a0d151404050706030605090c0a1e26150d0215030109140c19110114090f0607050a081b04120b07020106061b0803 61
    0x30b0060030307000049000720345c9612200700003e03d00312a00030201000c40d80012182130f2039181030a02c115504011400429090594401000601801c1c116032002321108440003200d492481c4580811100010300003008420300105c0c1c010402440e06201e0903040800050208102510010b5403080004507030190350f01500b40306100411124403209003104608010340900c2d880c10104502c0040f5444c032058440079488524000c01c404c031541b0440d0543c0c10144508a0301d0103005030b070302485201910544040000043d4041e0640003000703c1c000ea0049840c40750800c024000700d01d846401c2c01102c802008030461504400c500f450004400740800b0600c0780100148403042d2440d502880070064034400001d000742c1d808003110f044031081c1d90381440483d214000c408801d0001142180070410b820500702849800c0c410300031032285000d07918414910101c20031501221070b4005142000142070b028030035200140302c641450a600320107500400c841d4094800024618040840440c07281c020818 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 767043974 1250 767042724 767042741
    0x6030e1506090406091218080f060c07020604030203060c220303120923010b091003030504031101032901080f060123090409201c060b13360302060c0a03 67
    0x2280d801d004c0c80004c00907c0f00c03081c103818120b1020308920010ba109000140030b1211143d200c040c184940759605190003a602c1301c2c8099078480028040480580c0d42803154034042c00030700700156a40c1c03400841a00101407444e0341c850200004400410202c1d4000320303000c100366194540010440b1180ca040c02c40c0360f050f80714203000c4500d192107541500320150302a00c0b050408a58115880d56215001c56041c0528080100015024841000080c040240602c0c0c84581410f0200d140c1681307022000c0351a200c01002c1140c0607800f01d8400c6103503000751419401c5054030108884501d0203d001030f00d070000c2ea0032000810154000d041561001000039203511006c0140140202403940c10070003c04031000d0201d030740c2d0380320721840a095450008480c410400b0b110b40c00700c078000c00645030680103000b028542034000c000c442119030380d00f140f44a8810a17120003600f150010305001c82d250148030040c40d840ca040e10280d00d07400701181d000252180c3c41483c00c4400ca5645001200c118081c100a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 767045224 1250 767043974 767043983
    0x1a040b0102152805010b0702063402040b0103050c19090305030a020607021510090203060613151b0804170708030a050d05090307020915011b0b0106030e150609040609 73
    0x20414495205014001c40e50300e0a210303081aa81d15000f2495002210004e120704004188100445401402c188028081120405181e00b07603038428002d1a07001a140d0321000001c9800b900e5a030001c62419200d001c98407102840e0030491440d0101002c0d004c1c0c881c2d4074062100c026602714401500740b286031039001031a800000d890301c0340c0898038060340e507801c140c0b003800141c002e000714030311680402400c403882882c15414080500d8542a6188000e5102500c40341d0801c10070003030480150190f0a682d0005d102000213040d0944000d080144200c00f00700d603150451aa80b400800860320b200250b50913200d207101d203202900c000400032860304031340b075001c115980404250441d80ea41c0200c080c0120a520f04002d00580d0348600aa81d2a80326410f80251710400600110302c10b0300b441d00c070b50211a00c3c1030405a00c000c50801035281e40005d01081141c1c0000e44600600c141649409041c100b051501b00030301001c050450725291502000740945d01404181002400b030213000d800040619822 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 767046474 1250 767045224 767045263
    0x1818020f0f030f01020d05090a170304060b040203160e030109030e0f041805010e1e1e0304090614040c030509120c1207050a032003091201020405040c0c03030e011a040b0102 76
    0x94001e550203074000702800c5101c140f0381f40c00180340c1d20303012480e1a0110b500c0305035681107901d451200103080d0000790085c0d911aaa81401e404152118401180030b00c0c8151680e00c28031041400c001e01c1c145502d2171150207641012403400000e500800f074640c202d07034226541d0141800481c0460001d1140845074228901902c1c1c0501c00d10106500640300c140c4500150780c0240031a009000e8550707501d40c3c40c0c050300d5022240c0c004500345092004211030b00c1c1d00d4240c900c1e26985d000c0307a0007569002e1300312000e4408942c07102807480c680345c85003046100d40c5007020300c0f1500c2c0c1a459035450782d90540f00d980b075980000861204214003405149615a130000310181c4a00c2141401680c0d202c1c41a07045021507014041d074007152140c0c0c8200c03025040d50350021880c000307030301c01844000340013800b00071211f43d024080070501d40d07102d00491803076940c5036545000e028058100201603582001d40c90300907034900111115082c0c00321070042d14020040d10b006c02c00c0ca0740903004070b20382000e4070b10302c050b4100c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 767047724 1250 767046474 767046493
    0x209090f0705060c101d16030803071803020a0603020a080a06030c0303050c030405090124030509100b0a03170919151b05011a0f010801050d020d0c08060106091818020f0f03 76
    0x36240f5180702c41c10204412200d147c0c0c03610201410b217044600010344998000d00c00101c0e001d01c640003500441d2080070b0341d403c64a60b00d0340468251000b5400ca1000302e500450003c1003d03500c0b1490542c000000030043c401c00b413030740d161140d4240c0c450102804020740012031084c00380c0700f0000c031030040c10086c1c0740440940e501c1e00404c00d41661819040f1050b27645203001c00c04075110b80201c82c020240300d0088d091000d858481c0d24003c2c07200e4030501c0e03042140e5840010224008800b580c003210030f03d07000250f5402c1c2c0741c070070400c40502c210047d2420742d85680b01880900100911200c442d0f030f031410003480c02d18250100c10f040c1404e4400040496003064030b9600b06008140d942685041c1c00e0301d92007a5001c1400064030800424000e507900511451071241c0945014558032401034010035440e1990303501c41d031400d0708000098001601145964008000358508000c038132001108400381000b044068007000c0d02088403110010780b08500c0290055116074403032a040380c01140c020b044030394600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 767048974 1250 767047724 767047751
    0x1b0607021608031215010e1201020a0e06040e010603020a031e09051b06121312020a050606040509061f0b0d1409010203131514130209090f0705060c10 66
    0x10840780541c1c00004100002584400041a0340700b641c001e0748501c00707640c0c805400c4451381000442e1141004441e9606414a860384000c485810828900140c1d468014540180640d6078103200745015440400041003c10040c55100341540d010703141c050303514000b1981c2240542000320500160400744510b038031805115500880300d5903c02c10569140c0040c44005075803110364503d5443d00903404100000c980321011220540c4a40e43c58140303109500140c071015200488140c0050242e44851141014800304004140d4821000c0305c040c01246020302c0141d480b0700025011002c1a00700e802c0d8210480800c04c40030020342003200e5010380b540c0310000030380050551804105031400014000c144103c4040c000c40b031040b0b54442030061200980d41c2c3e0628400103011142c04042d43e910081d02d6100708144101e03010b4880c10b2140803c12185004104025030054034542c645e0344040152252044045101d6003120001c1b07440700d0b2284810802d65041005116030440800d1401201801c2c44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 767050224 1250 767048974 767048983
    0x40f21021c05030903040b032a031b090f0f0a0b0d0b0f0a0b032a1603030b011d12030d020301080d1806020a020603040501090b0c03220f02061b060702 66
    0x800001d00030441035a00709006880354401034611002503042040b05201848000d40199000703145140f2500340b40046d0300000395202c1520780c00da1708403000001800f6200075079010000155601000292030521200c1c0080c8104042e001100c0c0100f121035425082540c0721745058000706058000155520401e1848100515602841e5486004140741d190f03114240196150144c88501e00a40e113182c0b070318000c08483c0d5003030410f1410509040060302040c1e01608002d0400720300000c45a507018070712441c0240903550000202c904010034241400c000207004a41080d0030f140030348003800401e444110720360440c8111110100e500c0d0000000003003c0800058400c00c1c03000d550f403040c4800d48100e0a003840c0e58280e1080340010390102c0190805803038000c00454100d8441c1000140b441101d9440120100c01264444e90314000801000034800f2111a091070b10320fa40380040301d04031891350321803198070011000a4003071000403492414003040741484906d0380c14081d00311003a0749040c0c880207598 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 767051474 1250 767050224 767050243
    0x130c170a1815110702090a0203091c17010506090d02010503090f011503021c05030a0e010c0f1a0622020304080405150301030c090e0604030e01091a070506060901050306040f2102 78
    0x4492920f0743c680300c0c0207050740c142d50707015500500c82c59441d1074040c0900065007026040300c00134014504031030801413150400d40c0c90140c05450308410455001e500b00103030300050b4081d0380551804c2051600641c7c403129500307085542405d02c1c589035290100c0081c54100b034001322001642c6031411605404111b105c0c10022280300b12407100001050121809451042890040442d8401c0c428404924000c200207030b0584018500800c0c8103403181c0ba01c405058003c2d4099840b02c4003840ca4038214805d90841990080042d207040b00d02c03000740240114102a03007030030043d9142d0f011020604101c00c01e004c0300c004103030080100c0c1002495100305a8164130030310080340c00203154100060181418016480082c24180280029684640b41030350014540c0c02c0c484d042085104010806540c6e4540e02c102c041d80483c079894071030b0703c1c0e440c0081c640030001c1c02d07251003906050010400c6540016070380e54000d070b0086050841d04111715040008401c040d5a1410041e00c80e198401c195500158040e817 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 767052724 1250 767051474 767051513
    0x21c03031104030b060f030c010c1712070f031109011b0c03020d030206010e09070e010512120a02070f0837080a1e0e0a052205010b09130c170a18 64
    0x1180050000b05662641d61481c058085881c4101e4ae1b40031901c1501c3c0e02c4a070500c1ca00c559441c054001c0c89002084500312070590101d4103c08450a0709681441a4800345000c4001c00d45401c15000029120010100010072011441601102080002400d070070096a0140c48d42c2c4106540c0d20300070b51605001d020728854011703100006007003a0800a003040807662500060038243e402c00f410301c02c00ba25a81d0605005210307074500740034400311800080034010000d6010703100ba035003000000030801c1d41c594032507015503103d1045c0038121180111071b107102111b52031100c8800f50001051991034980300e80003070080600814a00480e60300001c1d4413450803420701c1003405540c0c00c0c4500f80c2c1c1d900380c4403403005c0d000b231000c0d001880036040ca95124801c0303000004007034400c4143d030200a010f540c000d03041094007200c04180c0d8419814542d05003011400044014000303040c02c0c85d4010800c0f042c2148020080c807800700801d030710745415885401c07022104400400315881c82d0400030449204400e4004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 767053974 1250 767052724 767052739
    0xb0703020123040f0b090a14011b110c0603100b0304030512130b042901030f12022a01110a0c26030910020f060103030815060304021c03031104030b06 66
    0x100d1010168602d4400d59010300c181500c02c0080d03d915156080042041e180791003451460404a00b041918040e951900e10011413010928450844007000d41c10860b400d001c0000a00751840401084c5c03c0c10f200c90603641180c4903950395070300103019200d55210f200324400c0042800103050303002c0003c1c1885411200400c005480d1102400310380ea80c801c102506c0120a0008180010b100861400d60890b4901c01c0303030104052503180f034003041001e034400c40360b51100081c0c1d2020444420450942c01d085030002e0030504d00c080854a00800f1007107190341000980040c0c0c402181e02450345070200c90903007001ca0749140c0326032500440e00140d90143c4002c000c1b2354901401c2c0030b0f80e4681a10300b21000c0c0805142443c4801041c003800d50325207601d0f00d0540c05410100070640c04200001402035010359180b00c1035040074040500300309003120603c0d000c0c1034100100405619041c80200c858682d02c20340f0010708600e42012001846100c0b25000544030000b0300100b030200380044980140d42c00c46004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 767055224 1250 767053974 767054021
    0x11418010e0603060610020c0d020429090c030105030601030f0510020d05190b060403030c052407030f11090d1104050a0e1c0806090405010b040f020c060714041502070b07030201 78
    0x6c050380f0000090000168400c0c4400f11031420440d41403a54a48094404901c0644d4185075408201d00e0f20b00a48810341802601c171101d00d000d04000307070081e108400043c59541003401113a01e5120502000d000d403200a4407040420004125180c59180c04060854580c2d20302e1207a44058001a200d00e480c0c1540303131460001031541031041180041c0c0040c96a480c081c03039640c2c156440c060050054501c2c0c0103840386444141c60724106207200d0b0000b0028aa036130700d012603000d0200e811100500114502d0401201600c0f80f8141c204c03031015030100c0303500c10300329564a040100704a44280080c2c200d8103000c20b12445501d01e4010f420405101d00c01c0d121980100300401003425103000b0100f0001d5080340c081146810014260798210303004a00210300b00568502080a032143e0444460070150300140100c49040e06001d40c9421000710301e0040800c0081200c0e15441e8000e50003680b241e20b5140d0480080d95000300301500040104900590725008207041c043d00030300006551038030804500858 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 767056474 1250 767055224 767055229
    0xa1110050702030307140c120a090e010602030d0b03010b030f031902060f01050409020111010212010314010504120f031509090c080d39050c0406060314011418010e06030606 76
    0x300c0d84284001c0d4011400c5075110300081ba0580d100c11b0001185003410014416900420310981c072910040c0000a69148000391005009001c594800c2c540000030070b00510040f80c0c040101c4907500d81e08071011594030818000280186040840540c0c54818001d00485120001c030141c211881d0460b6400c15a4440c4034099894001c201c500304010754901005000c1d43c5400d070300a007901401032424050303004681c5022800c903440214846010780110004000300681c5444c1d400a000c0f8400090040341041e6484510f0189001000b205200c04280c905082c1c51003940201c0703602803072944410409940d40002d0009221001060b10b001000c7c0b0303000301c0c220303000040c1c400e21070100741d9a5991481c51102c449140390000703040501c508406240c0e1940d454060300311115602e0040d0050700c2418a11000c010868109902090a16040c00401c0000b041240c104e07a04503407000681c0980600003034001000010080680000c2259010001c0341c1c0e80065141c8910540c01a002c4074219100c0c9403c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 767057724 1250 767056474 767056481
    0x2109010b0d03201204080601031214030414010b03010f1a0a0602060f0423030a0207230f0a030b0c07120219060209040f0f0b031e0d080403020c060a1110 67
    0x1005400302e1001140c2031603003207990000042529001d0300742c40140252030411300050780305901500842d480000140207000401410164a00d0142001c40510402031000030081c00001c0001c1d0800c01c0111250056103000e421000b5801001402007003003484c3c071940c610091007030031240078401260311b0800c003260800d100400140ca215400801556076401a030004c4030300020402c6400c030038000902c0040161800344a03070303010050b0014580702c0e10319100007882c10030f50394051841c0c000041032044241d680303103202244030f14055502e541d440e00300c080031841a5045a00003403519080d0300070081c1100c2c01c0406042c03d1031050812107981032000504907034803000031107041151402d0755809000260681d00800000740090310100b46100c1c40b68100d01242c901005c81420f80c1c0c0c940402030483c2c80c00f0301450030031208110360320540d19410000f41c5c0e5201003294103101403003a064041410706000300300100400c00010310080c0c3d40c40810a0040c04550501c9244189100c0e07110b0361401d1a4007800b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 767058974 1250 767057724 767057749
    0x14a0a020f0412060e01060f0501110601050a060311040e0f040c0e041104091b06031a040917070c090e150a0e06070f0e040e010204080c060a232109010b 67
    0x280d04500b0326003000820300c1082102c2c0300840e419651204c482c0c0e540c110a0054500401525000b0748819280030009030412408102205041e08004014001a035441c00040103035291803030001040818441c0d4503041b44105e4104981ca10414010003213062260b9240d40d124a03c1904e110400c03590350717481e00f5403142c4260b400418840390484145040c0c10503030302c8584410f0240c00300b9803c1b0090240e00101c141e4280d04141e0001e40c036801c41c1c0000d0024a2041030110030107a40c1000001229244c015420b10f0183c04143c90440c0020f070754040c099407003070110152010500421000e00d450440584e40c1d1091012020b0b0340703481d071300001d80c601c200e8410b444049407098003500f4250740301042180c0d041d0620480c0700900804070384845454446200d03090440c401c03e400184c1c2c0b24101500e00340f800140b02c0580303214410030054042c5c559444007191210f1307030f6200e43c0b040550241303886943e524061182001a28880030300007004e0101c01c40b44143c040c034882002007018140c0041809041c90b680c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 767060224 1250 767058974 767058997
    0x60408030703020706021b0d020d0c1a07050f0301080a020a0909031b080d1404050105060d020303190521040b061e090402030f03040611160608014a0a02 67
    0x900000c0c1229000c0d8008059441c400c0c0c5005203030003407d081a050100300010a07a5043d803241d11400b81540c1c041244001501260500303505540b07103a6035251350803e103052082100c0145401188196000301c05580049005925040d1130350717100c0d10100d50300d98070300c1010b900c184070b804000180a80603114180d19030ba01550750703803d8064007558550311544212012101e00b002001601c2e03200c0114860b459425004031244101d03800e15050040c02d54501809d420b10074900504103000682c0e0000441d90610342c00a4170b200c4c05100f5a4042d9201d020b91880311500c3c020701c0007042518041080701502ca144544807403141d513101ca03018400452006056960417505241d283e101502d010094245c2c0580300138200e0b02101b484c0701d85107007560045e40c803c60100e880c080506410303880500204118004d4100010001440c21a008000c00018031a6441e10203d00b01e030b00403e14103002001d0240d40004031b982455200c9144411010031081440320452070751180802d6010303103036000b05d0303642c500003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 767061474 1250 767060224 767060227
    0x30e1e251a0c0c21101b1b050610030312090203070b0d0f020c0606090c07030203090d020f120616090f0510121e050601030b28030803010801060303030e060408 70
    0x1110358680240e21506408016103e00c6001c0d8626a669042c1e001d214a04a6045114100c83d05416031624040c4101d001d152400c0c107088002d8901800114040300059286c1020f82001d4000902e200c0410800040d2460140808002002c0740034070300c40080324800d036920001584140f800340e00311402c2140095050704a29810801404801d0103801d0500900d84001502c2030101381d19402c80e842000034041d5a00001c041010720716008041540c00404a01c000e481c00344580c0d0000c1d00c0c2e105050b50148241003580c20034040d501c07041c08080340c0000217000c03201000e540141c444d40c0c41c94101c0e00710303042150080b145c0740218418080d04044a80c3d00701c074800c42c103003004200700740c000b54207043c0001c02070300b1100c110300943c0c0c0f800b40040c0514a4428004214002003401041d580d00030031250505081440140090704d418105043c10074054900341951540b02c1c04600d4111010340c0b014050b80030100020032400c0301980100d080b0b038480d4800300034150304010740d11380b2072600703e90203400fa190 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 767062724 1250 767061474 767061509
    0x140c1311041e08060c0f0708031005060a090305010b010c020607141207030306140108091c0e120105060a090c1d01020a0c141201050c0a030e1e25 64
    0x164224200c100d0415100609140d101c509000741c2203001c50003145510b59103441040f1801c8140006038000d500302e4401480d005604110518920408100524424000001510304e442c5115050050301004100c19078450401400801c40d000324003080e20194030300000c0005541c0074182101403141e003c4c100904041184c0c07202c1c0500d0307800107901035241c0900d00d40503040040000043c400300e03100c0c1d20000703401d034241a0a288401a8012302c41d052054038024459040340004851080138401c0404000201ca00c00c800c9944114510503e42c00402c064820070704c00a064000501c9030101303070b400400541d660f40c0c8041c1503c800c81c060703030081640028540307044960740760b10105130403041c01101d10884890381e0314220308246500038200c12522101084407403034076a0700c034103448540100030320142c189030309805003a11801160100b07059851101d201c441030140010120041c1c14a40100455400820340d510384141081c20400040c0c19052401018109844c080556051309071080c0d504a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 767063974 1250 767062724 767062759
    0x1002091302070606030206030c0403051504020a0b0d06031b0602010f0b060a080903070b271c0c0c03170421030e010c0206071401021905030f40140c 65
    0x40c81982c0a4464a072a0340c3c000c00907842d1900294068106512555030342c40c0b446c149a814100300100401916440b0000c1c0005a900c031644001903c101581315680c44612030418002401c080e0300003010117040720454821101002405030440d1307940c0d0000c0c4050380c0b003c20418112141025010741c8040140080b5000038070903003844e68006001e004891400041d0b444008080d5412141c03035088001080b4a00d000c0c0c2d0014044408030075030f00c001080b03508054614241001074010000040008201c0b20074203100035840200e00441c1c02c410b0705d03503010000005031300013540306019980025210f58000070103400c0e040c00c1ba1040035015a03805000d820000011117507008942c1003aa4040c000b80280c00204216088400e09070815500050f50760700342000c4030840b81a0101e82905010041c0200040a460002d030f0701d51000391b400680211544550958401c1440d010080b46480051180c88420f51003303009501c445014038425960b40900505440d9140d80180015410482d0540041d025a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 767065224 1250 767063974 767063977
    0x3010b070b091e0a03030b01052106060706090506012603040b03281d01150911070b0103060203060f040b1018051002060f0108030c07060e04060b040603020304051002091302 76
    0x244120b02500c2c00110760f04904094041450746919094005080340740406400d0701c20150400820f00f081803c0003401d40d016040c8540062711500305a0000d0006956a6955001c40340c074180e00039002c0201000c142080d40d90f506c000d01411900140c5101e400c0d040c8130700083d40c0b0001440800045283c02d092030520f410582000c1e058400a185028045115000c20118444a0903d000c800200c1103000b06941c0c0f0100b4122440c07040d16450660446503030a00036064074280c802c01d03180800c07810313801d01590205208c0c0b14000341405200304004000c1114030b400650080000f1940d840e03c13055150200005c0707401c40104158000404c07070f00060301074020f142c0601c0005c410207140f5241903035400443e016901400794030b0016007110b000c01094504048103940034141c07400003103092400940c9216034450480c01600300348890040c0718100342d0358580003c009401907940c0f55499030f56070b180c043c010f03410946003110b0718000e00509448030030300b83c804e4944000005040c5043c1140045d8400000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 767066474 1250 767065224 767065231
    0x60405150a02010212011202033313081b07050103020a0504180621060e07050f06030c0f0a0f030b030a02030606120319080403091203080a02030c19020d0f020303010b070b 75
    0x2d40d5020b0290f0003012001c0c2140c4c500900c08a11140c90302c5800e441050700340210f111040c11840c4010640c0c1c59030700d0b1203802040b4050510344103555151541d04a180d016001c01c00020702030000000c64001c0c4205005000211450070011501c0f103d071114019003d0740035181d8848001a001d02041207003141180d06a4030724405c841000610585a503200c80244550080141c480d9003070400171020040b0394130407101090504006001030360704200000d5105c901004403070f4030074031020010a5500320801c08a510384c501c8403c1c6c0a80c2c4403194000541039414001d4000b002c0392a0540000450801181c0700c00c850390f008003d0520ba036603103400c0140c002c071001c85c0c000c401d100c14000c04003100310210b00d03510465160380303d1200302e01d494500203000720b8080d04881000c401c00081d13440004e80141040d40c0045141c030000d0f8072030340c0314a99420399000d518000a802012210a18191383d0003040301d172131301100d69840710600c10406a00f40d0b901d200a02c1403c0c0d071110104005408210200ca680741c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 767067724 1250 767066474 767066477
    0x2071104050a020901021b030318132d110f09010512010e10121104180204091a010506040b180414040c0509180606040f1103190b040516110f0f011505060405150a 71
    0x807140030b1340f0760021119500359414011040ba0700c0c84260140d48cd0205d00c80700c8540800380f1540f429688482c1070740c0141103000750300303c00202d442400c0d07a0080c420b4a800034004d0401b503000b90380d5480502001c02c010345000c0320080300a83c010441c50f81c0714446800e0f5940100340c1410b6500c5400c1848000c10720104001a44805540c0010040e900c9008000c0c00c2c5020f10348141e084180d403815441c103d1410380c000e6101c3e203400c0008209001e8820144c4d0302103508080c041c50050b180c0c1022401030541c610401c50407082880404c4100100000502c05030780b010f59101e401a83d40350009042084d0040b1381901d6944a00300050301450a43c10420200d5584400840c19007540681074032260425207044d140710368841c02108408049100b6203219102c21141400a41007202c882000c840100d0083c10403c460882c0c100d03024031040000c003400c0000002110300d868581c1c04414000c04044507004012819540c001445190842c2543c3c20703203100902c080c15142980c000301c803559100990400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 767068974 1250 767067724 767067739
    0x90203150118080307321b06160302100b0307080a1103100c05180a05090106111c0302070b01080a0203120d0b04060306020403050d03140a02071104050a020901021b030318 75
    0x19010000c2c0040d0004d64406d2415035818010042c041484642c0d868200c00800000480c6540c01000056402c3d02005040c1d9010741c0d80c1074510104640d0f205080b4140007030070903240305004156001404050022810208200d281000b004160b2a0032040c81801c1c407c1d8815444000420300145240d802040010704444c4100c0ba2040001e041e6000d0b114071001040d03011031300319202800281e82200359103044840d40410380c100400514007000c107004400403c14000054030000d00c040080e04948a00c01894143c10225184024065440b400d002c41e1401840c1000140103500042d0700030916900034040c24416240400c0d01c0c40d0343d0000222000103035211413450240d40c507217100340806940100005655941941801841c1c0310f24094040105403400d0100c0007c550b141c846030ba08017103083d81c0966241e1007801c00c8599401c48820140d889440c1030140020741e50786500900d03242c0820380a890f0400315440c041c014840e55a100b458154004105103648100d110700d090204500040440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 767070224 1250 767068974 767068979
    0x21b2407140d1101060e010e0901020706151a090607030f051909031703090703020f030c03121803190609021f030603050c1002070e060411070c0f090203150118 70
    0x1000010181c080400281c1c00102046000e540d00110106203081c0d020700038800c1915190b601c0d2101001441341480401c03881c808206180403e404071951960011020f00802c1e0180044020034620b0344180d64000c410003995004850820040e1005070800410141c102409614203642202100f004041001410402d54048810714003410303480e0415550b40780380442c11840c05000b03580f03503c0449085560144200484c0d00d00008090f0103481d41a03c5110f0801d050502080c038100030fa4211a60501481d01c2050843c44000c02420130603c00029030600440c03494103141d1560420340607100d03250405113243d4003086035500b240c0b10003440681004a2505040e80c400c2c0c0c9207410303014100c0043c0e2a042c042050120800c2621605103007200d02c0203030304900342000380d55110300348500740004d204030340004c0a95580750300010355403442d0300c034482d42d40640e8a40040403e6507409002d4180400541c0422407031080d109484c41141440340f041021520040151140320340c80700303000214800c1c0d0901 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 767071474 1250 767070224 767070233
    0x6021f090c09140f130f140f06060f0103060f0b03040f020a03060e01060f05030c1311040329040f060906110c1b030a0221010608070f06021b2407 64
    0x29800a1448190000f0f02998015040300d40c02d80160641c02003034860014006032600e0759941e01a00c0d680312141910a030750a00d00702d0728021500303a0701d4219002d900ba42d544040f6010500621403c0100c13600148039003601d005400315201401611109007040b90244082500003005580247c0150203c050920b0340340d002074110344403a0402c03101d20f03458604070740401000b4000d40000e807042c8080d04860b02d05042c0401d03502c13001242520712400d41e654001d031900c92540e0111141c5203041e8040c030780d40d5443e030800941c0028104442e820721024a48031591b0040c40c54505406150303c610309420800d015143c207409840c8030881030ba00799036291500c06030306d86120010074a90710a103010b8068003001000e540c1103405801002406a00100c468000503034581c4018166808542c5503086800865070b981401050036401420991043c500007040c04526500e0348801ca0f0541d5003141d80b50311140c0401101040120300740c9800c4040d00065501040c2c03080000c000d0035690030b11050500040740c48 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 767072724 1250 767071474 767071493
    0xd0906020403030e0f0a03030f0c060f180b0a0219031a10030f1512060213120302010f05280c0302120c0307080f0f040b07090e041b090606021f09 64
    0xb084020510480d04040f0608000014840f1a0800c640384440c50b032560b100a014821342500381010004100189420452aa0300507804100040410003480745a9500030698100c03111042d2030300114240003502081d282c0c000c68010004031210310b94040113039000ad40181078090001c541900c4070042c1461191074010076015092629a0040342b0803002400b070f0021034002006d031000b07404030fa00003448808000138502c14059480000180d80d44001403e0320303c6482c86030000e10304140d607480c40b8820b05505400409040d468500d0411094a9007a411001c00d01e203c2c4c0b90a200c00c141c510000f2844c080e682c00b4400d42220303420702520306500300031014500d140c02c07140c009000c040401440404d5520842a030750018028a10500c42c3c181809900082c0c08000c2004164039030358400602014410641480201080a1000d0f01414a441c2040c41b004081e5032060303448038410310000e12503c1d240110411100c15401138941c08460201c031103030401004900c1920941c842200a001804202 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 767073974 1250 767072724 767072729
    0x31608130803030a1d0a080924030403110c040b180403180b04090b01090f120305040312020d02120f0a0509041107081309021e0d0f051005031903080c0d09060204 71
    0x10006490704000380c20701d40c4941c03505c050b02c83d80c1c0d0010310440005012201281e001d01800c440f698100412040744002c000201c403160400e002021040c80704258220a600100a111000341e402643e0b12206102c00c0b90070424000340e01054140f000d00380200c400c00e400c0d400c40d0080c40c2511102680314040428600160b001c8001d008001030200030715002d034812188031440900c0d069114502d00150074210310081e000c1c0d00215000c0c840309008060180b01120700440d84140e10f0601000c1c00c02d8040e4442c04100d0380d50b0098040e46030000c0302000780d06d0032502d4690344a90740b2802c20f40458012500382d0401040d50341c00540d03403217034515182140c401030081d4500c41c00001d07607100c92000c010600f8041941c44111074a0040c80000846e02c0f502c25a0307682051054441070321112842c4200000d0280060303008046880c0c541400000401071014074180c440c203904540b20300c00b040140032548185100060000b4250b4030114210140d400020046911032010114483d40c050702ca500c201e13802503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 767075224 1250 767073974 767073991
    0x17100807081f0b01050304200a140306070206013b090105100e0702030409020a051e030621060a0507090305120a0f0e01140d180602180303160813080303 67
    0x252040035480c0710b001010040000200814030803070540e00000b9081d030001404c0200f0074a400d01580665039030310310b0803089454000702200b4260303039920942083c2e91040d140d0303c1e01074001e01001460050000a80364100c2e490103681c0150340d01c1c0074500001900d017850301d6541c26241200d003021560381415040e80180c0100d0000605801c0941031040c2c1854240d002402c20402001003112442d0013200f641d04071030a8100241c0e0b2a0300d040000c45841c0f0074050340200480400d07001031941a004000345200d60001d03a00c501142940405440c0010100b813117441156020100162031a2003d4003c0fa400c0b0b00d00782031a650580c1c581e552103003081d895080300305401c0d0000c60000c0b8080d5000c0340102883c209410f00400101c5180c000a110740116020181c1c98800042c0d0fa0b0005603003540080d01c0300d20b0100c00210000b960385048800f039803000402c1d4003200307807902d9030304110300d40070044590480c03900d03800480b030131010b40d1040345a40003460f1000c15907502c1103000802030410720042d44030b00c004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 767076474 1250 767075224 767075233
    0x1030b040b041109030105061801030f030509091305060108010204050a03110609030d02030a090e0405100c090914010e1005030601060e19030f02010f0212090f0d05010c020a03110a02011710080708 86
    0x2003050600f15040141600d105407031801d004441030940441f414107503330700300c109100da21000703003000d0391544030b21680c5a40052403501081413501203003142403d0140f0801c207035042a640c1d003802500380d024901400fa845103030b0100400014018400036884410041d02c1d99081c0508180083d043c04030b410050340141c1c00c0012002030303403944071038150050000300000103140d04058880c141d60701c04440c41b00e9501035481c108280e819000f441003d004100a401c00e001400c030380078889803514000e00c5800c4032844844085989190b0f800c0c916010f40d2400742c010300c1203030f18000c0119660000018259007200225242040f07404001498102540c05000c503c4088400c6100050034805152300c0c0b201190001c003000d0202c0e00700303601103032840e1008807280e609446030400040c25000c82480010040d40c60702e4180301643d9004900041d00c0d80c001d450301002c200021040985800200320700a0019401e001101c2d12800b14120068204480294509280c0d8071980c0c1603240045035001090b01c1d611 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 767077724 1250 767076474 767076487
    0x30501080d1d0a1d0a02041206150b0f040305160b1215130207140c030c0d15020d0b1e090a0c05120421020f0c090c0f0f0301061b1101030b040b0411 65
    0x8401141d17030000e059640440c905854203003003010248401c9401070a0320b4075011040690203a08224402901025030196502c4203d070300300c0115503116101c1160507005804003458801c0940c000c0c20110f4a103a4540c0c3d2500601c140da52400c500c0c000c0c400c840e162000d8062035843d48690302e0140400509100040e960000c9051040c0c0000ca03c0e1180f0344150700c1400003282d41d44000c14100c038103e105854a050b0080f40e443c2c092501002c006c580b40100b0b04c081442c800001064001c010321701000d0f540b10064880700810f00084141c1c00c01c0143e08854100d01181d1f02c20764560100d8054549460210f0412a8049520003200410f0710300b5200000d03a02081c1e681c04180c150303d511601c25500003820002540b48507941c40e8401950326a2040c40420300041e4100d0080044412410000c01d1580da1180184201840c541080c041c0b480054203032000442d94801e95803102187c95005031094826080d802d00440c098803010602c6500940c0f5000307a001389880f54003451801c1544110940d48421 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 767078974 1250 767077724 767077769
    0x60303110a030905040e0f060f0f0c28032903070f0302030a080c0a1415060d03170c0904020d3335060412030501080d1d0a 54
    0x40c20240811098100141e0744000a400c141d00e07504983d4280e4010502c4516402190700342080c07103c40b60010301501e820800c0d10007040f030840d40316000c622a00e1017030345c88820404e042400303607000000581014039031242185080d070903c01035540c1186004a0106885442603c03000c5003811040150604d280031000e503440c044c050003029000d80c009050040d0302d1500004d80c0e0750049000507107418030010703400303c8000c000e10003006d186400c00c0308003a0804c0024080ca03074031640400c140b1803c1d0350881c0031561b1480c1809881c4841f07600f641d40c118001c0c00d00e00041e2030b04000982801c040c4402041082c2c1c0a40352800074000d0002c00705000922180c26210500d00c019007050000c1c5020780c0c01207040541030b10045004182e80e2000411070141c401c10281e80c2d45150810404981e08030301d00c843c000190400030b03c0f58404c030310031a280000301c2201c0d882602520000e0040da61b85070001920441139610501800400c40d0300b040321580300011440203e801028960001c0c585200003500803000302 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 767080224 1250 767078974 767078987
    0x80d0f0605040c090302010507020301150b040e090a0b060f0f330a1403040c0f0e070210090302060c090109090f02030603150403050414040f0e03090109050109260f10060303 76
    0x400c801e42e0180088550341d14010102c480300d000080c18050302289000a40d1000d5004041034045080125100d6885408244854100d80f081d80e008001040014986210110f070205080754403601c1d40800303445040401041581c1c4190142d0009507503031422225545004000d40800501b042800c041c001007140c012944030300000c1c80181501c10420482020750055502c0d5945002408054494a49140503a2549400e9000c01546403401e5004641407025410070380c0a122140c08440c0003405c9680c0c84807d80702502d4000e0056040000010003801da2a802841910750524109810544519240c0200d40c0e1592401501d1540401003100031304082202c2001d071032422850700b00070314040e6401003043c400ca010f580000400f10a59811a88443e00110840c2d803a03082c0500c003200c0704007450740d81e80d00200c41041c00500741c10360029095005002d00d40541d0b0010041148121002e80410007206060059003210b00c9980c455a0b0309060603c030f810385201d081400410020325604004080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 767081474 1250 767080224 767080229
    0xd03110f030903060f09030f040e07090e060d060b0f120706140705060a090c0b0a020d231608090d080409050a021213240603060c210e0a080d0f06 64
    0x750301c10458502e0a80c0d0000700e45034071003c044245483e0755550a6942d043d4042c2c0c00b800410760344080b0300891004500c041d542d204201950b0f403401d07520b40c0c034550719084610039161a900310040c42c43c104041040354000c10319001c03002d02040361032008180490005c40d41c0201200c1103800000c410b1040b2030303001191511030240001c40900300441d58455130f48454000e802101070381c0c0d54400c100200081d89051000600001142d2616030081c050040d48031480c43c03036040005580005809020030540c0942800c3c1d11080e0a840e003070090003422049415002d280585c0c1c445000d11209800740e640c10340b00811584138815068850b450f180c070342000e542026107041525070052052510308004080f082c1e0340310034002c5180481c10100c0c1480072f1080040041c3c401a04100c0d0708200da8900c41d90071a5003100e1141c6800c1055804162003112400401080c200c040301150110b04c803171807019040014403210107002c1e141c1e81407290b80c0791a01603012040c1d030b034000364a5481c4448051014801c0100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 767082724 1250 767081474 767081503
    0xa08010b01050307030c140301030302011e180f020a080f070306051617040312110c0715090611070801060611011419110909040606080f010209090f150d0311 69
    0x30603656040040c0460200520260425650b1b20b0b034094524440d407002070350030460003e810386c0c0756182d04000303000e4a074501103101c02c215000d045100340c0301e035882000700c000703580310401c0c052035150f540c1e500c220781c00c0800503a403200d940000403c40303150502a42d0310207680c48004002c1c043c80c40c40c14901b40c540083c1340d00e000280d504d81030b940c500d8101120809104050506030002d5540f4501583d9010750b004800114034a0001c000c0400e081000c0180070010040040b070b402035688142c1440301c00000c8407802c00007419280d0030014070740603900540b003100b01001902c1c0d00319116850310342140c80c16030007480002c108500b07044906c602807146100d40c5900d038a81c0f8000d0714040c03240260a42c20040142041c590b16520101c00031044001d0b41c0c4241001803002a150034241130500190256000e50000c9004111315824401814422a181e5100291000d40f440d91741c1200c003069490010030141e00c43c5502d008004980c3c1e1401091701002e88283c58020895058080c500e2500d218203000b100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 767083974 1250 767082724 767082731
    0x4020102060f2419030c08070f0f0b090a120809011d0a060f03020705060405030304030216180c110327031f02090d020306011211010c0206120408160b04020a0801 71
    0x40c0c0c0040443c045803028078250340040719950610124108a12a025204544074684030200030045403411484c111201442160361441d203480d041c08140300c0500c100fa1545e8104001049641810b0014007181c08000380302c2c1e5540c0b235842020441341c50007814216005c08000491520640e0803007040080d14a0f0241c5418049400c200801c3d115000350040000303001c4013100d095400da111703404580a142d803000c2541c06900b01403510b680c0ea40c1040e44c00700c0244c041e00e03c1c03003083d100303005044604603004001c3d0001e14192103840d00004100100c0700c001040b0807100c0d031118044c0c082000b01000310307495134030240f190181415010401c984403911403181e00000754002130b80152002d60544035000090050781e428410000400580e40500002e4041c0210000018244c08a0180411082c090040102940ba005c00119030310400c40c04d000b0740c400300600c00030440000c1c81418590182c031a8840510b07120000740090040c001d10802180c080158100b084114185910710000038031203d0004e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 767085224 1250 767083974 767083981
    0x50703110a06140a031e0c0203030a1b021b0d080301080a0c080d0527180f100e01152307020f04060b0f130e0a0b09090f070b0c1e0604020102060f 64
    0x800f0b40c8680701ca004c040503261008400c00ca20245403103401010000020408500b01710fa020352a600300300e0702499020702c2d04140c00d0342880900c2d41c1e849a5502075020302940c000c160b294804960741c0e00c40060b003206c400d100c0e020008802c400114040c012040061550184c1481c20791261400da4014070304a4007d28022052240c1060540301044c2e4000034442281ca42d248034007003010200c022080e40801d85000494509020416050060300c4507940741885513600031045580c0a13140c420b20240340d00c05001008000c802c6000c03e8801101071900c2c80c1489810848801481110b0040385c60740e5200080b00021441e01112820700ba2006a48c10701580c2e242046a010b41c3c082d440a0415140d80020002010503004544401a2980c01c00e60300c8141800d950f100001c000807154107000d42d07514070210702c0601000502510039828030300107180c40c0f401c000550345107030000f0a10544912916094101406c9002001c10742800000020103803880c107800028a0038502400001c00842d4030010b1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 767086330 1106 767085224 767085257
    0x30c040521030d02030c071209080f01060b0702010e120d050423131503051e0105131101080417030a09110634050703110a06 55
    0x114140100107a98040c698200903003840040c2e0310074019009039200700d800850740301c1d180061640c1416a103945a000c800200041c1001003044d00034144103a007030400c04174082c04003070700081c058146010f078600002c0c07042303a001a04005c12001c0300ca45e80d855032a601600c41c88507000300c0d5004942c802004015412034000e145c2060031004041c44145c031151502240c241c0c5c006c051162007025200400001c05400c001d04d420070580c04800030100718281309000e0450b954002d24045c100400c1c0304a030071200014400300d20486041040000300d02c032582640c0c4203c1d003c3c07d00c842c2a071180c2c1000c403800718449140041b110000010424040720742d4001000d01481040398030340d0003100b10108641801031158560b2141d252240170500f1720000707003452000341c00ea020030301c140b000503031507181c14607549400035110303109144141a280d0612601100c01010745241c00c00224091411 = true := by decide +kernel

theorem cover : BRFrame.Cov 766906474 767086330 := by
  have h0 := BRFrame.cov_init 766906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 766906474 ≤ n) (h2 : n < 767086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
