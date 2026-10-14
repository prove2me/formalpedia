-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2533
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:59:17.068976+00:00
-- url     : https://prove2.me/submissions/578abaec-ff1d-45d3-a8f6-8752e3a4aec0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 455395683 ≤ n < 455575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 455396933 1250 455395683 455395709
    0x4061424010c0503160803040b01080319180f1403070f05010f0507020d02030601030f0b0a050412030216020303042d0f150e04110306040b040c0509100905060d0c0207 73
    0x9840158450540c4401809080c07141000c8400e0800904500c141040070000003141828001045008800795002324010150040644c3c0c07542541a680c4c8292a207101a60030016081d00f03410744540117201c1d00f2402c41285001c99a510350b542c0301a107420b500641c1d071011a1041c07034829030408010080c000c0c00c42c002c01410043c5000c001030480c440012a1900b003040001d46441035455094140e0003880c1d001e41115540d6942e810304042c03000c06106c04603894044070000c62211a4a4080c2c20700954100d0321916880112100136402580205400407000b10a00300c100c000da03405001502c01400d118800c1110b1504030704042041d800ca103c404d0001202d2030009100944a04135280c040e1f403180c0c0040314200c3c01103030302039625600c501c140a5000d803d19140310306000c10784002c4d500981007581e040c00201d411100b0402521485003d6000240c800d0007221030516010840340800c1c020741c2085002c254940340030950300c3d400710f500803000c242c0740c240c0f040d401c60b0304009020040c0491000c0070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 455398183 1250 455396933 455396971
    0x30a060303180e010b0703030921020712020114090409050109110f030a12030e070e040303090b16121805060a0606090506130b0f0d0921051c020f0c06040614 69
    0x1c00c00f010600a440d8207001c045101d10806002c1c2c1c0c1315496003500f04d50a000c00740d41c104c1c80401480e0780340302c5410040c051502c0000724805000d0011288640c16110895081d03888000801c82d9048a00d003036a129444500c0f41d00421000e108402c41e160040b4002c2c1040c070380000500200a2038110454021741c03003641040c011440095101c501d024140c82e01145c040b4244400502d0103503107802044050250b407061008054041d40042440b51140002001d1540d42800700741107880814407140118001500c8200465802e03840080380815403040c039040b0400c1920358524009040b1035a0010990300c5205010a0f07400c034084000a01003114100e01d001110420a48002c201d882060a45000421113103204c9451109032180c3c1d10580008114015060901c11540e81d0041d002141c3c0c40700c2d41c00080d1400c0e01c1441150307503100480303c403800402c4000c00003030001d41c0410091003044106000c0341810800601c905401a40100c42c0803910800c1a80700e4000c00700c02501d070b04200da201005007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 455399433 1250 455398183 455398199
    0x7030b011b080306060a0507140d031d1e10020f030a0e0102090d06180b0a09060f06051507060b040213170c0f011b02040e030d11160f17030a06030318 66
    0x242d500c042d0a0316100d1b03d035a203202003035586015060300240040e04d140c400c00d1411a0000c1c03140807211940e5000c2c40f003480d40c00203245450007a8250120070790054903169010540c16140e07500401c40c200f04031085142580a40b904036080106500781200001040c016040d80314001d800199191000031807030044100d0009051000c2d0a6008264039212050028040207204516643c5500490f50803480d02d040e00c0945d00800c9032074000c0f1009417078041d824454411a126110a0701c40c040c02ea0140c1408840100b5459003100130110348454941880300256241d50020381050b40389a00740c0c0c0c400c00c0c28482203204000301c4604035001e551000e620001c10fa0ba42401d40c554480007806c210002c8004030007501001031200d640a5040740c02c2110a00354884000300901d907003a00c2c0038041044001a1840030751a00c1204403c6840e0312070512404041880300e41d90622803440340f800902c1041d5282c000d40c089030000c40e80000300360382d2907a0400078941c000c011140c2044102220050f101c3c242000307 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 455400683 1250 455399433 455399437
    0x406030e0d080609130203011a031507080c070c0b070809010f0c0f0206390c030601080304061b05070f140105030907290d0606110609151e07030b011b08 67
    0x41611541121001c03402c05c03e01c1e1100b903501c441d0080e0081c098203c07002d00001a000302050b180c7d000744217030682811004100060140940400e41d1407034030603142c01a1055007030b0400c10054035204503102d000903824408400400170325101d0346400b516030700d0b01c5001400200c0341e401c0c41f20901c5000e0442c1b900140303170180a105951b504844140d01c0d580c0344c0c001100b40c00d02c4225480d4886004078002d9000760b102d03100b00403640c40300e00b04581c1a00b04031428103444a00a1182c03036170591040c0b00500125001d400c40b16030349802400003074040c0c200f0b620b403107141c90365941c4a2200d09074921400e214031802c0c203c2d00202282c00313090252440c204510081d41d600000d21508100340c25000f0202d44040c59803500600d1921402c40003070301c441c0000d0290b4014140d501c1001d020664140c501118101d02280d91440340180344064110070400001c0545054002400c1303803822030201800e0740c102115694560b00a0701596000204103800f00000f45c83c900246829002407080a0340c0200081d105c501 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 455401933 1250 455400683 455400691
    0x4110c0c100306121b06031e0b031207060c02010507082521060e0603010b010504090b0307260705031f02070f0203150703141509090708120406030e0d08 67
    0x80898428841c4002180142026000041d40003881c0000f907090001401001c04e1401e2403002041245669030f07002e4003211007032903080400d040302c079981041000b81a484058030a80c042d084e01c007494001d01c0340c5030341544a08012140326036902980d0340d545074240300d1a580030300d0780d0501613820b080c0b2021030075006034045840c0002d0b440e11032068a186124414840700012522200141003608070351000250680d80161018104100001202e23450140903003c111041038541920300350510a1030400740c513408a9040d0548100b01d4001802520000400d041d611841040182540c00d81c0c0c0441c140105980800d1103540043e0400920f0a4120400d00750841244401070b65440b26103030101d08a1801400a07505001c2c05c10405080a0303461012031040006540c20000140b914102c46035071071090380d041604039030383c08201c612410a960020780084004084410301c65981c00d05501d09141001c103420361110101d010480b054140c06000b4111070b400b000b40c0b40700020008010030303101c0024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 455403183 1250 455401933 455401939
    0x714030a02301c0608031206032407110328020a082b0c0203040e011d071407020d0c0f081b0607170307030204060905090702062701090c030204110c0c 66
    0x3e900400031000c600c48a03051003950009000e010360b80c030820b540340c0d000b4503420a1144400c0d0300040092a0201d451074a0798049201c13003954034401c0c2d07807100a03008020301c0142402280281c80c05160800c10140858010b1082590303080c01c68100290410340d8040302c00025948003007c0040040d41c040180c404d42c0b1502c07503100304680761140e540001040f1044604000d14904030912105503404001041500c801902c8440c0b142d0344d40b4030064030205200021901c0703054682c042028a40b0481c02c000198036640d02c0306040c101541c00040a42c1080f240032186003a10800811100300c0c620340c11401800054050040d03060000e030010f4403900740030200c500c6040c0004004040092120840c0c0f4003280701c0b50080d8492401840141c02540f0a00a0340b011404410000810345095200b2074031412066010305400c1c0c4681e0000790040b641c1079406d060184000b518102c0d000f1003442005415400303842118103161540c0180800c946808560701203080d403c0003580c03000030303002030651403522040e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 455404433 1250 455403183 455403187
    0x15090b060111070f080d09060f0203040e100324200d05130803070210181a07050c0d0305060f01080609011e031707021318080304080714030a0230 64
    0x280c11071508100450b00594441d000c1814085120240060050a86d8006444004403540c03120300c2a1460601c10039601e0049c1d10800c41030081e0b03c03c03000500d400200098905c40c0d9540c80703035108003070241c3d004240aa01c6940c1c90702c4000504079402002e000008081402c00c0e801050710385280e0794402c409196a80300e44031001f140b4050000d05800c031106402c03914054883c02c116070001d441d003402d205407020481c00c14848182c641100c411200070700fa88600a5941461003980c411030501d40284900c00b031150a002030500000300740000c0880f5859944d001a2074030b480070800c2003419103c50800e040200800c108203283d1108010641516845c0610205011410342d1562450015404c000c040c1e0681e1890240155801e201604401d8421220a46149000500d0408440403d144001003024036004180400c2ea00c00013590094004d004692030021540c8804000880c0c0420140305a400017a01801c4154148207c40703000c801c0c400c580301d11101e50091100004040c0426081047c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 455405683 1250 455404433 455404457
    0x7120b0303072f01081015090902041805010e092d03040f081009030e0d150c05250309030308190504110a0f081c1704060915090b0601 59
    0xc0055541c0300f41d02000301407601c502c981e20768044424a0900b480e42e08032010310900700c0e6004400c3d80e0b00c16400c03580d4040703690346412a0380c4d003a8004600014240005203101041c0b509890000f440501401c5100000b024003a402d50713022510142d10902004200ca0240210410b000c90400c4038070215643d810b00040840c11110348007481010710361541c2c0b10005000840302030081044044401c4802540d84a6685400713010640741041401000294a0000c14980c0d107441000403e400f40990851808200d40c0c10320501210a600d6500e0085480454824600b099204400d000b48600c01c0034424141d5056802900b040201e00008060100703820008804c02035090388801c0034281160240268200b41c102114959a04080c45005011500e004510300e0406000c2c401103034110001400d8214420110030400e03c821404075007001300c1c20207c0b01e2a03d44011500d4082c902403000014a00e409242c1816001d0452000c985803504001407000030901c40e1240a6100501703080504210030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 455406933 1250 455405683 455405689
    0xb030a120210050f01061103160b090f01060920040602030d0b01030e0a0c0302030c0102070e0f1003080307090f0608011401030902061b03070b0a140a1e0e0d0f0807120b 74
    0x80d40d52a1050b116181c2801c1006543c4c2040c0b0040c101c4403280c442c55880c400e1200619102c4c400e00d0441042c40d401b940001c0b00158200c64050390108000381519584840e4204403030071366035564000301b03009072680b00519038040d00403085e1000c03102c0020080d18251400300d019440740200203103040300b0340d540c038041034141e4042e811502103080301c40b060f200017a0503407401348000d25150006074042d1044944240055000003142410b40f61640e001004076a6009440004036100070b0000060030200c650020000340954080c41c050a00ea880d02107465090418181c20041e00f42d001008000c6100e0041103401403602e407560b070120742843c1c007281b0840300e4004501c0ba8802e10351404c602842c1480d60002ca020080003170803455209600c0d1000c00d480d512141401e5806c2c0e42c1003140305555210205090382c01e00d03840710400c000d003913240c140c40003c503110080444015144c982243d40040d800d288805503c170a901010500d2410310b40420300f0481c1c0e00070480404c1061200701c5035655010070030155 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 455408183 1250 455406933 455406943
    0xf0f04060e01150305030d1a0a090b030109050d02150a020a050a051b0d0302040603050a051b0c0a1b1503060b03060f03070b07030513060c0b04120e19180b030a1202 72
    0x1681d80c0c0320f0340e21503a500d141480d581e901003c000103449240ca5600c0554400e44d07240000c840340c00601d058801414000740302d000309003512100398959600d90103040061070902080022201680142c0000302600c0700083c14827000401c00007850b881003250303030000c542107030030b4443e2404240b9000c4e881c2e0388a00207074a5000d1840601c941c680c42204034020007950f144c0c00910640702590f80c10302940d2103a01c0f020b03040d01c3d404d0b11000f140903500c030b1000359403558480c040c020450650040f00c0241d18552521040b01c4280240b031a000200039406116002007a80c0200c0140405d11307041100c280303041c8c001003650002810051043d040d401d1001340b15941003080c4005044200e502607038400300c521f00a000790f448181d4000c545014040000b414034012410080c3e00c50300581c92030025520b550707a580c90056208020424407061101d8249251118842505110038807400c101e10f0034280010740c0c0ca0407404020070001d03a814034103462030b15200861a9920664040c050b140e00307845105080c2e00b80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 455409433 1250 455408183 455408201
    0x90607140c060f090c03010b060702041509020307031a0306060a05010f090b1306090e0108030d090f1e0308090f0309060c07150e01140304020d02100e040e0705090f0f04060e01 77
    0x1038810b02007880200441c10032014000e840c43c0303040300c1e030b000d00c1c080070700d402d0f2600c01c00a03581c42203040c0184005824142c20000619021445120340a921020000101c1c2c02c261498800a907860900d4160044404040160440308600074032240c54044009940d4007082d025544c100700b80c0c85415429030b0300a2900c032003e4070708402e036640c80303011600145803024010712521001030010100000d502c85900c003064144d40c404006140741c250100a03500160015801c01c8510480340c45055004c549034070341901c00744013200c4507400c1045036810018200c40d40580a100c180e00304100d1a030302c5003400402c0700d0101c3d4040c1e403140e40352051040d0440c1010302070f510450000c10545000c203d04c2c4d83c0881e080300c203003409072513541e8201c0c80300341c50002901044130029001020a458540940307841c603181e0300d42d00007178504158126650404581a500b5002d20701d0240d50095100307000300c0c580110841e601003810360700c4038200d28003003000760041341010300085c051030340da114515201c1c5000e403c03400d20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 455410683 1250 455409433 455409457
    0x1111911040e0604050601120b0112050705060d021c0203010f031401060504090b040c0b090105030a0b04200c0c0d0512030403110706050c0f1f0f021c050106080c0309060714 76
    0x50504005819440d0380f004c40e01100e06003c1c1c0b030004100050140704216515400884600c0c8580c05c00a11700c00131250f00c2e106848900c00c0c1c1c1800915640e07228000c043e4000340040240e200c0038610700d01071686c4c00124020780324034010b00050202d40e42132002181181c1d0012401400001c086a1040c010301d0315821040e081401c0c00c0a02c014081040313085402540306404041240340e85d541d000d83c035401602c10882c0002c4003040401c2c41c10110360825020040011700016105c0220800d0360040200951120000c3c0404248082404428080002000707010780381c8041004503036549684641c01d028248407030a01c080045818144030307180480320001ca02c001ca402c06038035403070040c0c07642d000b2014402d0175200f03199805d00f02807000f180c0c899004810700548500d40c0c0e4541d003140050003035800d4508038140c0c01d00c410300750b0a03548550098074207440f620002da03550405c4401800300e840202901e40e00300040082c0040e015002610951211040c6441d41c1d00e070106003540c089a1040806c4103903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 455411933 1250 455410683 455410691
    0x201020d0e0415151103040602150403021f0b03010b1503010302040207170a080a0e010c0f03020f120a0c0e03070317031b0705060901060609030f060c1e1d0111191104 73
    0x2d1030b000e058070184c1840030113403a8800040328000700b03d5520311880c003801d80140c101400c1ca0880c1c1c07000610381d0b80c200e8442c4c01a1100380481d5150124000042061001400d86407074a060b0503003000c2c81b81d80d840701c1043c0e880d079121300325418989845101c1888000d0240784e0004030003062104031401c840304905c002d2202a81c3ea1030340d0303100402c10f20061326030103262480d180081d591a6014419821918003980311500c922407404410340c000d40226a0711001c2c0d80e0200401ca0140402c078411070b11810b02c1c8500051046054403004002004000f4824000e6214040138000308071081c4105109910b1a4143d980c2e030340d41d40d40166080100090280c0c0131301c2c00400c1c10000c2000120308180310700e103814000c200c020360f81d00040320f41c410140b101800380c1078403400c41f401145a0380c20154000f4201e0400d00d40900543d00080c1c18540c0c25890200062000c041049140d51303101190310304074909280494042d0940d4204a440f00c139042e011030036585c96101400100440d4a116015a40000b04100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 455413183 1250 455411933 455411939
    0x5300f0f01020304060612030c0210030204092408030901050d110f070f0b0c0f090603060f121e07180c02011d0a05120705071205150c0a030e0a0201020d0e0415 70
    0x35020350000c1d1411515141005404240c0804800007440f415406a50381d90744521140c080c01a1103180d426810201340d000c00003c01c400449000d000c010101140c0500d140c5400180603a83c6a007080c2c1141400343c10070030029841d0703a440b00686483c0c4d60400c10014204c01c92101800d00c9205103500b0958a020104800b000d1100114070003d019000d07400f0420155243c07014031040e44560703441c10748107800034845203241741840750255610000113070544001450140c0010142c907071070b990b12043c513848004150100e0001c850808000c2d00a400108051810003c9588d40b00c0040a00d01e4032160381e51091111030b41c800d4020506025185054400304c1a41090766521010070b14810380b01071103441d0401084410703c40859107190340002c05080d030582082c1d59810005020038050310680300e032910b2101e51780a10b5030203500842c1c00d04000d56944040100140079642070781800d0b17845030400f480900260343c0100304240001d0052070824400c00d10200005d005110101c1c0e02460400301342008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 455414433 1250 455413183 455413213
    0x130314010e150403020d020d0f1211070b0919050304030212011506050406030c0507080f030702070b0c0d030b0108071d1513090b060316030c110109050c0a05300f 71
    0x10902580c025420750f54180486a801d032303a00c2d00000240d1001401d0304855409052003845019020404110046056003100c4002d07031054100c01340941d80c00e0004c00500000307010401980c4002c40461407047c2d8a465151070f01e81d100e004912021303004d150254440b102005081d4030504110706510200c80d003990f10307484001c00c1c50700b050141c1342c00700346440050107003140154107076240300f644800100c3c41c10101c846102016000074048000f07612420002040034815079020300020100340004048008032500000c1c02d490990100c1410301c20074405022003582d1140b00d034104401c5076007110881d040701c0740201c0c004103020b1000711030201000c6045000d42801986040450b03404040501c80c400300b10f13040041d20f200559913461031010390405c02680a010350003d0070b0074545400c00300d2500c1941d1481c0d40c00e50b048141e00700d5045c1c112100c5280b4518104150b038029100a48410340c45096440740700070488008002e0b078240d4482d05d4402c4401f03c10800c6400303030024445e81641c1020b80f1403014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 455415683 1250 455414433 455414473
    0x90216050a030909050a06080304031203060e0f04062a080402011b1a0906010b070b0402030a0c031a0115020709110415170c070201170a0902040c020304080c06130314010e 75
    0x42c131516181840301080000445000714410740c3d250ba070246250524664805103003581103001c2505250322548005420060b4014503441501008079800442ca030510340501102c00c0140040322040c00103407049449421246018090155401c02034810b85907800180d60740354896a40c03101380c0e08048400001c10020512010540649110510b1951288442c0c5038495209010320f0720360150074802d69001c1998001e1241d007050002c0d00740c0d8018910754a400d1f00c15140c07604240c8402e0202c0300e0014080d0900a10580109066820010441d112810013501c4410724800e449503240c44005424503014402c003120000e041030500c01d80c01e510909405040d0340d20b0300d291000d50619940004140404c3c0c03d0454988039416904c84040c04684803c1004880d805480042c0d00c03a5246260b01c0142c841d44030320f0b40c1c3c141407900156210381ca00702d002c0340303000304a02e040360180c2000d000440350291401090b00581c1d92005102100e0f12030a1500d500502008000803d14400d03003180b01c410207050a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 455416933 1250 455415683 455415689
    0x9040f0e1c0921080703090f0311010f21020c030c010e010c081003080703110f010f020c240c0f0c030307090617070801090506031609050106080f040309090216050a0309 74
    0x120321039483d83d00e00c0036040707080f082d1600302c00c2d2610a107180e5000404001c0100f864a00c2820942c0c20180c4a01c06001800c10907003080303403003046c100b0348004103680001203458005503526100c40724a2450708001800c20505100c1d61020b900411300c4011014144140c5c0c410f0600e000082000c03a1010030907901800e00701c62003801241050010442d10000307800f01505403900100001d1404400d50b50440c0c0c1c01c0070810102c0d141d4003542c02e01e0900c2075000e015258890080304005616034188a44644c200950f201503810401d0454041c1c61081010302916544000145002c540f540014421070a19200d211260311b954080001081400c81c7c000340c103981a01c5d9141e40350051000e51034243c18500301d050b21074a000c6005200100a00300340c80c3c00103a4000070160940d450040141c2151424580c2c80c0c10201c4034507226401408030942c0400c41b594030095280c0300c642903007072940b00a000c25940d4090030380103903000035603500ca1038083c8004286071a0f0190840d4440c07180d0703050080401103540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 455418183 1250 455416933 455416937
    0xf0405150c0a0803180d110d02012309070315060e0106030207050c0405060105090316050405090102091804170a080a050603030a1b021528020d0509040f0e1c 69
    0x8540350840c06601000e49100c00308240c0240101c002036100e18030f858100500b082d8032101380200580072a10b0611034500151070a8440624940800c01c8032820b102c500181d0700304580c03501128030085000e20031448083d564510900d04030b5181c620503d0304158054102030720050b002e4481d039240600f643e01c20011214019000c0f1121790b00c8070011001d0f4424a10050101c0d44001d0020340309213000e50003035402000504040e4a007030b5442010034288a04410b100d8142c111449080106080c24004d4a81c0031b4a40b40007186040284800264400149a40180c60362807840004080001e0558401041611500d48580b03842e02980010f003001c804503a03080308181030102080d81410000705442c0c1171400c9d51210a0f180c00701081c8040280502d807010303270b07009003d4020401841e581ea030091006d0500c185c01c1c1507510480d0b03641c001100301104490401c5502c00013650181070b03404001c3d200d01c0002110701040760010403040300090841e01311021098003c402c1001070001c0d22500d010008046a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 455419433 1250 455418183 455418199
    0x406020f16050d08071d010c0b130302011812050a110a080d0c08010f0b0a0309021801060206091209040b01030902041b180806070c020a030c0e010512011a240f0405 72
    0xb189044903080b4050345c00e4404617403150f04501081016040c042ca40300410326020501100a46580058800a0719600501c12013090103506055083c010b08048034a044c00c3c6410100b042e81e00e00500302c5210700907a04000010500084803441098201210240d040843e041780c201428040c480740c3c44030a01d008110300c0c0000d91062076020f950450b049030b002090300389071b562402c0d24501060780700e00710140405035590341410060b03440040301000a00090300c130b82001e40c14090b020340340840143c87c400c03943c1e1207050180e240494103000c441c00070301c040d40d0200d10400a10011f81c090306140000a60040c00c0c070917060b2004c018a01c2c043c44910300d96071940c62403240c0c02403030129114070f17000d2100250415400151168040d01c2c07041543e40c4050b004040f0150790b900e80880001036a0040c4001900240040203503240c89030b2040110843e1b03500070070440100c1d0f81c40d1026003502c520001d0003030440301c000c86c0d4249551056000200b485120b030655403540e20702c01d074400c1d03442805118420744c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 455420683 1250 455419433 455419453
    0x402180f01260c0621010b03040203070e042f060c060f0c0a090b16080a0903060f022701021e0a06150302030a03050f070c0801020c01050105150706050406020f1605 72
    0x82c50b21030050030003078002d410a03108101c140b041ca5032001030b80540841801c0c2d1003c034000c529400c040c0c000c04c04c542d4050340307a084c03030b10405050030010380c4031119510300b0200740000b01d004000d500c41c00101d40400b40c81040c01d50501e000318089d600c108d003940041c010807170006400000c00d506200700e450745060f4801d0381e50012090458024040d0000000394941e00601030b40b42c92200615130310303c503000b0003544540c180c0c0e10703006e41ba070050901500055602e0410400c11120780540c4000d400c0302e103000e50409404003800c41350110f251402c0c80040e0f5041022240c50b03402800100c2c040f10084050007110320029200300c5c4c0d50440d500040b6101443e00740d0640f11b6150010b01d40095982c0100a008a075501e40c030101c450340c00980c02c5000d4218100136003000140074601990007014424005601d03204145256802c55505912145c014075801245a1280311000115010945c3c040c3c0c00140c141c84505014000303020304080551103044c0000c0c01e5440740e003043d0410700c80300d00c83c40441d400c1c0c0700 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 455421933 1250 455420683 455420729
    0x40818030d1202030a090609050304080601090b1f0c060614030c150a08040503160609020f120c010c050c150306091b0f16060c1e0207031a0402180f01 66
    0x1c005801400500103014210024100b5001150024881c40780801d840703000751039003011612070b4101244c042c0d0000600300008401030240a005003040c0508204c802050b03800705510140c441c6036490040b51030903800c003049000c2c0d50806400c6400103001c01041d40c540d07444000045007181c1c854428420301035400f12600e004143c090f11809000009030074011070103c103403009007001c0d10490701030000303010404482a1000c90078600601031030340800c000d03100740140600e02c103000081600900303644103003608031341000030310700d2500c1001e02c0c016401110b00d04065080040e60b0551950241e440342581d400e5500c0b10001c5d500800e801c5446040c2e0340c030380912250070709058101c140100359060100303072a403140d544041c00c9103031003a150843c11440d40da41d400044074456003660010800d1000311402d0010b010300d011940b600140020291942903031108a06400e2408010808628540009045464284500010001102c1180e9103410001d4008440c05802d000e480301d40ba044c480d01c00d290b44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 455423183 1250 455421933 455421943
    0x2070b0c030403030813051f0f02130501050a1202070f0b06010804050c0d23210405090a020f07150f0b0a060804020d030207080d02012f0f090a090504081803 69
    0x4040c00c00440c40c00d461564140c45201d03000304150246000042040080799040c0030a207040c01003256621402d0282c11403540c101d5142c00640e010052060100d040702c04401c0d05824107840013420110780b54000580c0407103ca070020030284030807034000301b80d44041040c4440c0302e2a0092003103070f01c20501d603140d000441f0701d004102d40142a503804800030f84510708010390030300c08040c0200782c00110031030380c051199141c40803142401c1180d4040b8207401868155004485034032010740e00101c3c40e2500c0c0200184003044054100700c02c0d070b40d0000f00c0055855502d011070380b01c55407008c031602110000320244401420b01c101c07401849814400d0510b49481c00440d400241c58003521411000d4503607800b030160b202100c250407010340c4941140490101c0d003c02c408490201164008500f051610341030310044250060300c00001c9000c840201040320f204416910100400c2c0c11882e01c50303001400188035480b066104908652400c402e005c14402200c00900040b440c2d40d507403004029024007030590321 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 455424433 1250 455423183 455423197
    0x3061005031e0406020d0203010e04021206150913050d02031c1e090302010b041a120708031c0b0a09020403050606030601080613020a0305030d0c1205090d05030408120a0c02070b 78
    0x340074003040e1442490b8400481500540105001818811104a200d049038020382042074481a000100300840c608218400c010300c00a0002e0310071424840640205030040300d01951040448000207821031301c00c05500070040ba0480200c440b0000c1c0c01c40041c0d141c0d0300002a10950680c156602c410003869070003545925001d08500840d64205000900001c1500840460855489020345025036840e07004854904100000b8041c1d0341030700004003c1c003544150f001700d03182e0300111410031201030040148d400c00408a0600301c7c05503038058541004002c00d0582c2c40d40400d05120124160421f84d000c0d009507072140c4210780b8191075002c10503a4030007092060303840640c400000110421041c4108650341403005e098030030520b4a0b03556940c11504505a1400c040f680c034020100c000780e002c02c0e184d07000750315030008002a04209103540c0d250111201d80d4018440300002150400600c4411030305001d009a904644600305401c1c03c3c4040c00002c801c2000510880d600468048100c0080b6800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 455425683 1250 455424433 455424451
    0x40303090501080c1c0204060e010c2a031403030106110102090a050f12030c0102070b0f0f010306090c080d030e160f0e0406090837020d110f0109080306100503 70
    0x241901d00801102d04a10080c00e801e1400e000380b016415044501d540c0c0344c0d420070311000258a41d401c01e54000c0c140c40d9108c1c00a410884030402943c042117022038210304084218208080c1000d141d0040380b0039400c0d030f070310082c41500001c0c09450b002c1e030048051b5058540940c0c0d1900d4a000c011203042c06e0f4000c142a0310717801642550100b1661a016101550320711010381343d516123030f0f140b420b190305641212903c19000d035000650681007151090b400ca5101c0746a03040003006042c1202440d100382c40500000f403456603944150301c02d03c0f2501c6225001402060220b5102051802c03005000d0821070340c3c04c05840c4507614050200b2030360308082c50265207035072840400ba60b2034445185180ba0014100742d486039610801c0201003520813008004030306400b0180442d2902042c803416400411a8413002c20b04002080c0700b1315503502107400b000f0810249801710020f540d042c2c1c19030400d1584d881d40e040940c83c11100004008074100554403440d41156000c2c405003150340c00ba900c40c0b00c201c0346030036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 455426933 1250 455425683 455425697
    0x3010908180a06031b0806040f020a0c0b0f19020a1707020d0906021c030f02070503030103030903330507090e0709090501050a030203120a140301030b09060a14130201020309031605031002040303 85
    0x100461107006e08030303031002d001400450070014444210049034420418800000c407061899001d00c00c102d0f20240c0c1014800010728824500032000e1160420040600580148c000820304020b074481c840d400790b003d1618034000e1043c10502400307580c0b089243c28480101c0d000840021346280082500022034014102d040c11a0789030b407400b00d0007400242c0648134020307402e100d0080490001c2003e103001e5442910780841443c11400c094824801c401940842104078120030080c00140015280090f04421008105601d5442003a50302d1502c5402c0300381040340c1d0508200e540d90341301d9040070031188051020882c6981390320512161b803081d0b010194056004882420800307640320010321030301d8518038000e41071070000c1d04101c0c12270b4420b80c07003507904019502c203205507441e0600c002d40d0001c80341c01c3d0800026040e034590400154000f0001d0607400341c0c124100d01564024011128007010003004d450300f600e0310104030214110030b409058000d01c644212440710402c0340c0b00312410783e501a11145 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 455428183 1250 455426933 455426981
    0x1903060e0c21010b0a090b040b070f060914011b020106050a0605031f0303021e061306020d090203120301030c05010912120e1009210f0f0203010908180a0603 69
    0x405950b110381c4001000014028030b092140c29045007042c00303030503038840c130311394174191860024503401540d048a8075012040204104407581030b011144001e80c840c5411140d0181d070704056008081030003000e040b0510f603a50041044a043d403068a044000710098050b207210444101d0890740f0a005554000005520a10550303010b9009580d000040440d80c62001010019a02100e03455510480250f0321804191014100c0e1840c5003848000c608001d1029151050030342c0351f0000c05040140c80750390f00103030306001102180c000d0210a40c0240442d4500b25149030b890f201a8001d00c001d6074541b02000000c00d0941c8206100780460f1042c00e4420310207629902d41c00b889440641c00740041c030030548030700016a21000c4200c5020a00340d1162000c461800b131081016031440d085803907111880340000400100044410071402da0410b44a0812944a201003401000010f50150132448040f59050100b40442c000c441107000680342c1200082e60fa8106400b900d10344c100c41100c5116030542c0d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 455429433 1250 455428183 455428201
    0x412120209132a0e010207150507230d0e030c010302070f0b101a030702160f0b03190501030503041404090804060806030c12030904180209040b040c0b03010b1903060e 73
    0x80f401e0707403091200640314485034540078a407200d01c07080c81e070200380c0d44a2402025038044c800c45008044200d00344202c410f6941004000c2e00c10400c1c001d020008a01150400d04408160400303a00b140d182140d10b1100b011f0005450048072480051180c0328592501000303511900a0341d200300c1c0d220007814400d0703a055942e0b999046004250aa80e48070344100041d401074000040706031400c0c0f6455032a0390b0b080400c3c00a0905d0451340b001c40001da6011002c100d0101640c03911421208122000c60320398030746001196000d50b441c1d511f0442c0341d04040000c824000702000500840c4c0318078107411000c2c244a4180415520610006415628148020031180d030098850710761050000f815280e2804114001800c10084800a90156070001c10003540d5401c052082c7d20361005890920b65004641b07074005600004010001010801d0b10000314040010b01844103010b000c84010303060b125038468240f0716098002026126012000d9411010703814001d20420f010380341c140341c1500d140d40e154100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 455430683 1250 455429433 455429441
    0x906091b02032502061204141f0f0e030d020a0f0e0108160c0f0303060503150c0f0f0d1103040b0c030417180604030b090705100207090b0402070605041212020913 71
    0x2c04200c07808400f41d00030043e40c8440080c119040083c0c0d190030142800e080030074000c0328000c8014519400039880d0301c50a00311244d000e40c040c02e21036011403504482c1c0d44000182540c1c0031445042d20011415504610450300649000740459840d0144400c90810464034481108030b950f0100b2074034400b01707011000385000788080c0d0703810b400c00e42868003a0b80e541603548115480c050b1300083d40d9910600640c03400b4404864510541403150003c0d040c0028120f0301e030302c80d003581c040302031400089403008000c2d030405440f160381000c003040000070410803961030258030481d01110005400800520004000710a503800b458022440a0807843c800d50544a2a440904507a41e412600c1240c0c900503030710000100040e500c44c07000d00400341407a030b03c45441c001d01908814800c10b81441850070440d0300041240444840d0040890208412408200248190000a00360509100c100028480560800c2d0002b0085540d10107450548000c4e0800b00e005040c1c80950000d01840148910081030308 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 455431933 1250 455430683 455430727
    0x40b01030e0604060f050106050406051204030e060c0a0308061e0f0103021b07150c0b072304080303091002040b0a180b0c060a0e031602120709060906091b0203 70
    0x100000e100d84000d201c589004400c40f800c83d801c644850700c0c0201318025000300c50040841e401c2c060700302420508054040d00a50302c009510010b040005003c0c1417244030b440306100c00c090522588c035400c41c0a840d494002042c41a40811071f4840450a58141300440b0881842006110220f000c0e02d0030401c0f504052a80350b540c100b5800b440071501f030b2040c90b1000780780d0140b03540042c60707424074108040e501401003405804c10701103841c1210010135028040070350301003982c0c83c0451411612000340d00702d01c290b610304100824408500400d002c200000214040c85000b02182d2448080d006180240d200f41d015400803200b0600c51003140da4016101e010400384440420f900c5141c540c5407400d0160461044045140d201c0c2060048040c1144130301003501800001442c0b074117240094404540e0300c10407000f40110b034000700704c14090b01d00744080c0000d440504410702445940e23b174480d0192003070780500d400c21460901100310240180c80381030b484104a401031420f06001d54011090500b841c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 455433183 1250 455431933 455431937
    0x60e041d030c01020909011e05060304031209030521090706030b0d15090219140f0f09071d060414121006080109210909020f090a03050a05060c030c030402040b01 71
    0x118504200300003403001e450a490410001a200c8031104c00b000a03180040e072280c169254080300d0b0065480d1410540700a513001a02c3c1150380e5129490201e031551060516602003a151103604410560702100924424000444845000b018113209a04405080c0d5803800c09600c004020013010340a41c100440c84280240b00d841c03607510356240e130789030500c41c2800740490707076599403440c4c0c21450044520005240a041040c4a40f07003009041d452800c110808039201748003408481a40b507880015015140d000a070644a0a04121401901e0000300b0301a070080c1300300c0d449440c401801c00d0001d450442d401c42e1202c40507070101900b4000309885041c030361007890141852020b803554041c040e00009012500000911000318280051404140001000441000d0500c8401300d07500c80c1000c01070352550740005079500c2400c03004903024420b0360002500014549400021301c200072800386501d80c0240199503166503140c140484c80c2c44100c032005115a4103002107000750510340d114540720b42042c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 455434433 1250 455433183 455433221
    0x120414010915021e030c0909130614150f13090309080a1a06040c1e1806020606030c04050709030305031b030f0603010f0605030a0314090a030f061401060e04 69
    0x1e0711085075203103a070200141c8190b00050300441d0801811800708003a004c503000203085007050742d2403101521401300000c2c46598400302160040000008100d42a940b040c410800704e0401010030f400442c040b80d0260888060714001d0207541070829001901c06002401c0821814000c031191005000c9000d0581c1000b000c60004112070104000601c0c01a000300b0b40e800360b02e640554a158a450001c064078010f0b130400c80c0c0790a01d0368000c9080108440c4d0b944144061a1440004444c86003807000d0309803803c20001400681c55401044e01c900440d4264256944d04500d5828070090720780984120b40007a2120901708080b9101b20042c40d08089000780c120b540c041001d405070310640090303c002c000780e085201402014902445800d20b59031054406100722490180080d842c3e40301d4560284c01c1c03002003103d0755a141e5681c0212107a40c0b20051420345460b4485c00c0001b003403d55500120b903540c0c585005016511107042074281215855075649242c41004801d000152101c07002c151010740d01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 455435683 1250 455434433 455434451
    0xc05040306091a0c13051f0e010309060c030f060f030b0622090b1812031f0b07060204051809100e0118030f031a0d021903051f050c12041401 62
    0x40c01c9580b9024444d40030000d600c3c0c6401d41e0000e08070349001da0107030348180100419581c0039218021210f0b00240c0758203050004208107030060380079080c1c04000030318071460940e40c080c60300d40550000c0e903004040001048515281c403007400031030505010150680b0b80c0c400025034140307000c4401c00b0710865058800c5000c20590003c41003642c07600801110928074102c1080002c1091260201c000f10785c1100418100700b00e0201d007001e070310000d410038200765054501408080368000f00c0800810885540c05d40e58001d5050020082d04940600d40c40303448008560764072465400882c5002e900380234050b041e102800c41d0004000d0600c1480403046549800102001500490b281c45d4514003903150610740d1600e50400130116801030001e04150b8a01c1581610161106481e289056a050314101d510809100203111070040b203500003807413441010038511624031550480c01d104821484103002645405491000c540902c080102c01d50440030006408200078000304801001081300020303403152 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 455436933 1250 455435683 455435723
    0x3151c020607170409290f090c070c030501140907030b15010306080d0201050714070f0f031106151008010302031b06091203190906020d0305190606030b130c0504030609 74
    0x95125000065960040c400070140c504e46080301510001011030303014840d46c00081c0721001000b00c0c2d43c050001c150004610103544800c0700c801542003405402119902d18205010384010400610090300c48404550000000a10482600da10800344902a41c41803803803030316215211080360402d0389900300042d09203810300400580c8c6107036170300108892505d0071000d040d41502414007001110104880300c003042124603c0c01a45174012049030306c8151500b021070f103000c02c0030b202411501400c410301445041d840c05d1011310a40558824641440e540800d464981c4240b1022b5015044984e441138070403125a0706c4c000c000c00040c1114107140b9040c0205001d8942c2e210003000940c00000d1956004060601403483c0325403601d0941d4450741065030094440300007601901c18142c40300049200d444103c08078940504031340704100b0403d9502c1000601400d0842c00c0d0714040e40c07010405480e40ca03418003803512640c046449562803d480d5a4541d402800306501c2034809088104010401003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 455438183 1250 455436933 455436937
    0x61b0d092103110306030c06210f070906140409090212030d060e09060103020a17070e0c1902010b09180c0a090e070b0c0606010c02190b03151c02060717 67
    0x81c901c000101031155084001404071950003c8070300c0351900510401415540c0002c2d070032503100d170644606844160142030742d41610010790505803005181030800c10007005140b84a0320409259540b0981155140820b071000c10329600c0c0c0070001d1408100030310140c2c1e0a60003c0800d144081c103850b060b14103025105065400030a540c0b001c03903459241c00c100c000d00d8a0741c41900844040003a21165142d540081c2e80c2206134420700703100e440f071801074100c0210300f4015100140414010b1888610f40340003e039001b5400700c0b1440c0824820f04c81d000f408148144505030010201604070b51158855248800100d564904c001c1d84a1080c0820760403140c03500d01d401030007006503203804908880703410719150405a27142c102240010702480014071090001641941041080c01c0c80c0c100e01e482c0d070012641001c00303040c400040504000d0002002e000b10701c003d51090001d51120046904514100311a084480c01e007203548090300300c42000545400401092a117100700968600d00d04007215110180d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 455439433 1250 455438183 455438213
    0x905070317190e0f1503060108100306050109020d14040b0f060a1703030603071a1c060504050403020c03060a0603170d0b030a0c080106050a05180702030906070f050708061b0d09 78
    0x140c034843c9500c01d80c18105108034007410102c58042c4907400003101d9910300d020081c01c1e05d0410004102090082c001145580301854120303030107102c15a10b4200700720103036115000b050050b80c0b4010082e0714204180582d0360081e0f5016500780241d894100c0c0340d44018802810103982f180460f0701c0000c58403801d8000da0700040d00000a1500c91408404240c200f2005610960f03040742903105010306c415410007200c0710a100c3c40c810083d010560b04107080100001d0300300580107803410050005040e00000d19800c02c1204408a0703d0595034a021102a10410710004001c00000302a5825070030b102c901030141302e92070850008403008100c001034942000e02209071410b41001c00d0a01003203100f8080c3c00041c1c03034166100c42c40e0510304000b286020441d64002d038401420100400c030944d10070310032500040d50080c4290f85030f00e26405d084403101007035442244c032481a030030b000403e424003095041c4a0075044000d0003800d0503c0b85800c0d10f6a03c802c14050500d03507645481d100007500380c3c0009d044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 455440683 1250 455439433 455439437
    0x5060f04140906060301020c030a030c0302161b0b04050109030201030519091a160801050f040924060906151d090a060e07020106140d060603080c0102120109090507031719 75
    0x80381000ba6100307042020140070b09000b640100000c039035044d000000c03110404400c3c9000204000c2c40d040c1103000f40549000d00641019044180c801c0c0112010780480301051a01c454507103940d5045a00c5280c8141d208007404590405010805903000707503c41030380007115140320f0a02481c000b5000b4100c4006c20403c51f42d1402490400110034204548140e2000c1e0102e0200d043d52001600540300700740510500703100d805144500071440d20703190041484207078404881c0f9090310300000702e00300caa84649a0740040600c2e1100024412a05020352030481e0341c0401000c3c1500020041142c0100c041940710800d60001ca1480f4841d031500200c1921400440303800250ba54200020702c4080b00025144e0021681008414044003004a071918080b1404079452480803d561501101400c0e1552001c1d06c20140416900101101900180140c4c107810b020440c0503078030f840c0c80070201d4040083c00351079907003c5030f014070000e5400e03d40020403d140034589409e00020104d44894460510b0007600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 455441933 1250 455440683 455440721
    0x30f051608030f09150f150120060601030b0a030c0506070807120503041e021f09090e0c04060503070e061302041e05151e0a0315080115091e05060f04 66
    0x40c8013420310010705000c00f04070304542242841603100018080180900428a0305000d11040c168042c401a000b08201103100034004c50314a0400c503280e00d0101c0e05075020a0030304140d860310340342c2103010805403503000412441031070601c02408141c0c0c104c400704a841c03080c1007140340e010030a20001c2018001495858507603900c1c0524010103805442c2108020f1082c08a040c000142c3d1000720300d0304400c413040300481d5052400c2c101201c002003258410328402d8030300380c4440c003030f060085001c000c0c072141501d09124a6580d90107041e07a400d500c1c800c0306091400b1350003103446850311a00d0054641e00050001d8100340d21110600c5012140300510004844111340400c05428108800401256040515420850300c41659911525604418241070000003801e40080e402540002c42010410108034101e94403040194000c005001c055a00e10f40328050001307030301c1d2490007058240d01010716180b1041a085440c0b0001c0c11000d40301d907078403541c94030f26a4696140d9100b19410403140c401404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 455443183 1250 455441933 455441941
    0x1d0604060605060403081207091d011d01080307151401140f0907020a0b06190e09011a0604060c03021e210906070b13021008190603030f051608030f 65
    0x80072585194001801141d044c84100085940c100039500e20315260b43d4039003190381e200032040314a0181900841c17454000f4845005d619803011000b40c1c1603a07103d0407200c62192911020641c1c01c00244a03806070390f4030400900000071002490011940e044030808141c1290400d00689411790076040b240b0070100305044400710f440d040101e602944015203140c0803078282258000d46401c803810000c1d00d218681400314210303456100505c018920004903d003030310380d2a240460040d00b010303908082d566003804091006240b0b0060500c02c178080042600d882d15180c000e05071031031a661001507055025407110a21540d502c12007111001c007070400508403440802d0150840c1d50150080035060160030701100300c4070b4907102c085800c9503800403041c8010761b8460301034001070162004000e400608a15240360103503003001c00180a0a0030055100d070a00c4d41000113021117401d4480900002c00000402030000d000d04002c0c030b5501070580940f010f030f14440d01d0b4420035501c15100f0341c1c0c1505d840e001300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 455444433 1250 455443183 455443193
    0x516030b251b0b0f071b030801090b0a0902040b281209080d0507030b01020708061302041e0e070e090a03080103060f0b15090103060f0e060108152e0c03021506041d0604 74
    0x20b6401c0202d0401c00c1b10406045450041880e0014060301a00320b81e582c102d80c080785e80d07141c0d2010040043c410199503031a2188440082500700e03400080c0384429072450494000d410300c4803132800845603074502d0180701c210320b0305201500c140c1c441910011030401c07090148032518040d041c0300d04219200840e2201100c4002440c104056018111540001c0240008081e04555061120742c0454002c6035102d650405110b001c01e1941c9403006191030b0900703d03210326501052520480710410820041c1d907030f490341c0207030f12818103000c000d0000b0904e100500001390f05e41c0c0324402d0900c803208002404122040451080c0c0d12400040c491a4400f05801c8e003190381c14042c69018080d080c05642c10b4502c0c1c4606030160842c00b6146034180b04007000001d114044021069034000c600604007070081600b00012914010070310030301c2c21a9226201500302c3c5034080c0751000e203000d81c950b0083c450001010024219200c024006d913520070340b07c9000642503010b200f201e0480441c2480a4005801e0034942 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 455445683 1250 455444433 455444447
    0x7060e1614010e150f07030e1c02060a11160906260706050d15090906050a1e0b0f0d0503030a0f0b1c02010c0516030b251b0b0f07 57
    0x80340070484840c141c00002c1e64031812001030508150707844840c65a01403608286401156012040740c84049108400d05038443c0e44425202e41c10f41c0c0401c198040c42e032044111038042d0002941110040103441d8801d849403143c1c0e42e1310078100703059620ac610001a090408e800366840300952503150342081c010700003403150710041e0800c110320801401d80f199540544418191140704c081c0700000c507030b401c802e00e242d8100120405001300d8000c901798440348641d000301212541a00e1051400002825401b907070b1248200070b603042c0011640e450351058510b806858000d048030781000601454650544903100c00648680c40384c00655100d00d49440c010045450250001c1145030a2010850894071403600c2d00ca184440030000304000401d90005a58100c1d502c6801015481035120004912030b018804806507032051a0386001c0d52aa621071403203843c00154550030500404103141d13002400307580321111000e012466500308082031307120f2440070f140c200c03103500c4484040e00400c2349450b40400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 455446933 1250 455445683 455445689
    0x1c150207150507091e0b07030c0b0a0603080315040e03130e070c03050a080c0c0d03060f060306051c0203100c030b090c180907030f06180e0a080910030207060e16 71
    0x1003040b65190405008010302d00b18403400c1454040c141080240482038800e80780908550301c40301d5500c8540b03180c010001c204d40c0d401a100340d80360b000030806180705030040c4400c698000340000d06548420220086000e21990002c1e40199555000d070320680f0244003810b83c04504007440d6464502d040301c0d840041c0002007480040088101d56040000d4028042c0c0b200811780340350044407651100204046e03441075088040d01c502c641004a4916070b815040340c41030f64060103482d002d29540311400e40982c0d85a00866a00c58501d05e50030f901000741c400300041300c07030004044412a460105000c030458404c000170400094071141300404c9420103007049138100ba01d2103205482c048440b080040d1100d805801a03200310720440200e9042880307500f0410105118400c10000a6941c28100c6001d0728506c9a0581c03107814004880007540f0045403068030681c000712050301d054965010404411210058403042c19401d100042c04202e4507c03460004081010040200000f40804030300e4401c5154 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 455448183 1250 455446933 455446973
    0x2091c080702030d090b0f03150d0f06060510020a1415010b0d05010b16030f090503030a0203030603241504140106020c0f100f0e031002160c05030106030f021c150207 73
    0x10010404941031101f29030222240c054400c0d00d03500e507440d0000c840c49403043d01c240d0007540c170704000041c040c0501c040f0b800341d44202c6081021725518020300c41034450714040400035070000c0c020100800d25103145980400191819a88030141000001c4201c2c1030a030071540c01040c001c00c6540300584184201805090b001c0600c9003032006558100e680161049401400c100250081d00841070203000c0d0300d4050540242580d84074800044002e6680d001241c01c0d0f44a84500d0041008201c0100c1d19007154001d20f07003005d5031650f5101c0d02c6440d2000500d031641e410590ba900a00c0780e080c0914841800b8102550150165403141402c00c40c85011800c02c0e1440303030610001e15074105420600f0410032460710b05140451a441000003801c200260030340c08141707400002c2d0303443c07900c0081301303050002481100c003c209276440e8414142242d145010040c50981d8001c069409880c0501c6104041f20364207080c83c1d000840390340c0310340100984000380803503103170049026020082d10b440700d110301503812 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 455449433 1250 455448183 455448197
    0x15180509060121030e03030d020c1e060c0c070914090d0e030d1409090406140906010305210c0f060a0608010b130b18190c031406010302091c080702030d 67
    0x1080c141d007040c6541d264155045450b2003c120300f014002c03668216080001010390361103500300c42d6000c0c080c1d03001d004206018041c41c42010511004608800d601c405a00010300166490000070345c00d65001c44e8142070701d072186040c00100e03004c16001d031081a460f50307500c122450404ea00d01d54500100c01e02801c1c184260152a80c603191000074101170b2241107450b1145c94440402d920354280c1c45213410050300565124100428003500d90401d01389041400e4000f46a59500000280c41351001e01000701160004050142c040c20f441849801c40a6442200717854407078884501440d0102c503c4c8070304a19000102000f4410105200d401c000380007081c001e10112004c400080c141c030307400609101040f0359038176220b183d81c1c454a20740c00d00c900d20041d84030101d04100c101449a8100c2031b0460400b641401c621030380c0284a4040d200010002849406a0362102c40040d40039402c842400d641090641481c100001da800340c490344054010001035035502c24600501d801d008103001c1e048144030362 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 455450683 1250 455449433 455449439
    0x8070f090b10020c09280204080d02030304082d070b06011d0d0209070c050316150902031c03150e0118020f0d0b03010b060f0a030c02280501151805090601 68
    0x1080c01c2030b1980045070441d410356a01c80c120f00070b61000c284c00c06e0242d6000000300c090009035600030400e49070f442c41210324040c8015402ca9a83c401241c000340750890030300409c0901c540c0700158054004044000344c507403507180c2507602195000403809851031a00030090100300d58202d4454070704030404d0710359401c0301c050740c1d4041140f130994044000c0c060002d520003e20818812803150440c10750280c01d40e5990705d10f040090401c420b01c0b90091301c0540340e1a41303031080150b0612604a00c65405405081c0d09014000300c8511a03500f80120414103440301403080c04912544c1000300a840900c440134010350511a10110389141c4801d80100b0300c0c410481d00c3c4041d88130809851600000710004980f07241414042805051040c004542105000c26200904400d0b54040c020010385c5039002c104151f0050400ca0740c54402c9800e1403201418106010141c00340001c1e50038110340120004510081354144048041d084c035405100c4140350700c150041841440d004180d00310b00310340300501d45541 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 455451933 1250 455450683 455450687
    0x50d090f0209091509030309031e0906040b040e06091003030807030b0303191101020309030f03101505090405090109030e0f0102070f0f051017060d02010309060603060b04060f151808070f090b10 85
    0x300b04030ac0c0080718000d20000340c200182440841e0b44091001e01156141e80d59007400700300303035001406000000d10041740050040c0c24076400c6944101f624a01007002d103407440e101074407280f00241241c02003585031100c1480d661001c100a00706a00080c1c0c4070a8030035601030780200b132114030950b01c0115034010003d0015900d800001e881000c4400c402007030ba20384030310b0007003103141c01c041e40320748506180c04a02e001e4143e0000050102c040c01960f051105544040e070041c00c80d030811100502088501341000c8541c00e29840304c5149840c180106d50f0790302d072a203d8143c1c10000320350007400c0d0b004010b80140f22504009042d0042e80d04103041280c0c0708041c02c0c140f030042c090010240c500a415011400e800e40e0302c2500b01d641020b41264040002c103032642000c4000d00080291140901d040507800103c0c034034142007580407201c8a580f8800003131030340503003140c00620000e40301c603102c1101500860020030510100d00104880c41907482420324041d400000d640c15034400740e00c2980702030ba00d101c4640e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 455453183 1250 455451933 455451937
    0xc0503010f11030103032604050115050d0f080307030b090a0b01110a11010f09030803090705030106050d031407021210050f070905060d0c09171501090b01050d090f020909150903030903 81
    0xc0c0c3e040c2031880314031180ca035580802e07007806440f00030101401f0041c0010703c02c040d44040403180020508400c0d080d00c800a004040c10082c800501600c680030f420004901daa1028580240d85443e004c20101c080703000041c00d50f02c0c06d907070071000651f90f00c02c1c45401b580c01c21180080385200c035000e803009071240d480e00f05401d82e00710301ca6414003004c2d9080428151145485001543e4021074058880c104076500c903690f80000c0c000c0c0b0303001b03620305140801c0c40c0c40c042c1500c000559042c2d075842400ca40220b194420f940284404a8010420000243c005d641c00d0140b54011000c2840025844ca0300c1e8403105001d85001c0d01550034030050304011301a540700d540841d81180307480b40e4041805600800122500c9020f540582052102c080010501e003001040a44000075442d00440490342c0318020300b0304842c7c44c14203250204008000d01000c2148c84e400040c0b0840c01648904441c40c1d66802203040c925040302c0307010503500140c40d04100011220000b42d00040c0c248002c2d030841c1707000b0803810350724 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 455454433 1250 455453183 455453189
    0x4140904020d06020a0302070f1101020c010503010b04051e040e1b06030f040b060315010609050a0f0602061f090c08010512010b150d1107060e0d0305091504050313030c0503010f110301 81
    0xd0313000142c1c50780090098044a0303040303900041a69400ba81820101c0d40d04030303820021070041c0154503029100350b00c02e00c1580c0c140d8060140c0c452406143c0010402c08046003030b0203030440145004040000d83e0389100e140b9010a0182c040d084600040d0101210701240109042c4200400d0042c0401404181c010643c0140e00038480b05107502c80c1c0b0002480c20a10102c0b40d40e41e100c0c80c0b0000b2a0a0354490a078a08880d026140301801503102e1070009102d031120300130a8016803040000480300c810703600d0030000403a15030980000e09038031040c01c1400d90f0300d1082900701107054440100481d0a0030f034424000e02410800800a0903594800a680380d0a4035819410403600424000314200240d4030600f5038000e0954100d50316101441c009000d480040c0054840380901441da0035442d003e8083c4500c14100300c40940205126021806000400500207480d144000c1c0711640c1210210403186000e10f01401400f040c4034030b881d0400d400d41d5002c5022207000c81c18080f465404080d61001c1c0c03415 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 455455683 1250 455454433 455454443
    0x90b070b04030f030b09090705030114040506040305131a0a090509060d0308090111040e06030d0816050d0b060315030f0102040b091e060d090201021b130e030f04060504140904020d 79
    0x80d003c000b045016140800d030743c2e51300055041c10b001e04500d001424804542c800d600a01c640380324810041707010035040742e001d06181c00c400000340c0040c0c41003000305101e98144004110a640343c10f0002c900340100d032070304074101e400011480c500d10b03008140007008020032610a4010b1500002041c0c009003409802000d0141d000085500540290407581c40d40c032a404155895681d504070466107000d055504600900500341c500064501c0f954041c0d21880e000b0b0342d061020618010215034035031080809000103030f910300c4982c0090380e444000354042c0e4010301050340807109003010103040a07080100140707180c0c4100400c02100d5541070a4400400045910f109031102d0f080c0c64086500100c1d00b0030780c0c406070014031251440c40300c1e070211241074000c0e0700300c804442d624003000300d080d80341c07400c81d075031040090850442601d443c3c1c104c91740306451a01030320704000503c0909406a0060303000a0003045c0c01080c10f1045c403e41c0207152440e1502220303680300c0c1d0706103500488c2003202c200b407010744 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 455456933 1250 455455683 455455697
    0x6180103051909050309130c054306050703021e34111e1306150903051902062203020603240415230310020406090b070b0403 55
    0x6105070714141d082911042c0b150188011002d6281c026140e40c007051215120303042695000040741d40ca0b12455100306072039195586800d81042004810060101210380e07800141c1e820702c083c0000155028111040c55010000c1c200300c0f82c50681d00f510001003142013014410f004100b80020481444100d011480c040300f5503aa40308910030100e042088500c0340503403004540b845501401562440f10107001c0c502d101c1c00c400700001040404c0f101821460150a0303810000c415600d4010000c1700d103011400c00004040c1d5403032098000407050205064040b40d6648420070a004c2c0500c040011624204540e00f2403522980c00a442401178107401e650301c502405132110960317110100c50000e582c0082c00f55803680f8020540b00088a4001346038220f403004021140c040e8100390245490030450b903e90f12408a00301801c40c2e801100300941303801100790800c962142601c041c0708804142c45505400740e9030390308003003020b088440c0035440126010b20401000e0041003014940302e07001589454491 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 455458183 1250 455456933 455456941
    0xd05041202062403010f0c050408100209010e0402091903080a021009080d1517010618050708040803060301090206031317120c03061f0e01080a090803061003020c1e0601050618010305 80
    0x24014032844c0c0b1401d18580c5047d200d503513201e4015014200f116500c408079113200300c12034a11000d80c01450000341c007241c81c02c0e6080f1003d107000e0300500044032000d400481c400c1d410701c40c0c0480c0d11a45510035030340d641e0005901e02000d9070500000313408080c40d10301400036006903501c46909102e0b403043c03494200d5a4076104180740d080051254010b0644900b0755400c007400c161420b000f0800d0303210b542180d00b006a8801d03441d0307a050203528030030a05a120b42d001640d40d900d0308100703684003e006c1c0e42d01d550795080013030050761074030040c600403482500205103501710761070510465501d030f904102e508a01072040710310003581c1d40c901580c04105403612644a0302c03190081403e25155001c0d91440403441d040d242c094540c0104030b00c80e4040240c0e00c0510f6512805012000c81d20b003102c0280c8080010400a5a00c5c00d0141e042000b44070103140040c504400e10340300504020b10f100c24218188180180c1c480c009604021490160008645062811281105908407c01c00c111003d042c591640002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 455459433 1250 455458183 455458189
    0x501050d020306061c1a070207090b0303070f0303021606090203010606020609030a050c01060e0a1505010302040f291308060a0b0d030309021816030509340801020d050412020624 78
    0x5245d510341e200c90950b411074281c0a0b031b0209203408a846030018424000009800c2c24075000f0101411801307005907203003c669443d03801c0d80303148003001070742410b0b02085a014183d501480300c0308841c1c007403000007504040b0f40c410142520700c50760245007190703c00810b20003442c80210440b402c05005003800c503a9400c00303841440c0507040590122061070404410070101070030f15001b1062016881c20349075840c90318ac60066040340602c2c01103006006410000380110000080b1500d8100c80312240c1201d9074440c11850300490b0700c200342d60301d5a030305070540030028460100000c0d40c000d09004024069042030b4000b20b0884418910040c0070540c0340d04a10041d0740390300c10038541c8100c0b03c01c108461f503c0c00c110002000e0045034100b000003071401300043c0c12841c012407003a1765102c0100f44e00116004401c0100380c0c0107120701c440c2014260320b0400140020307091001300790151803988040b800340341c079003041a1070f881c104d0003420944d0443c02c208106018125007589100f41c241a404003030039510008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 455460683 1250 455459433 455459479
    0x601020c01051c1805100603030905040c050405091806010603050705030c0306010309050604050d0212030907140a15020c0109060e130c170f01031106040803162a06030501050d02030606 81
    0x2d500d803600d4804c001d02144c044501d0034a10a000d8000c503a006c5048001d003c0845045100c041d00203000c209050101e444c00350842c5e45048030924100e0700b8192500c0c00115092000c0c0c401c00828541c00c8059401c0420a110f41801000642020403039454400000340c01803100070120242808000001001603002c1e0744081c09040e0800708640c01446c00f841c015030313540742d28080301015100306404100d0800c1c80500704c07480f03012144040c202c1a032070002d500280030424107180c1c3c1e01005819000c1110101000340c02a1007003941e000702001e010007800584400201d403c110100031402c0440c6c520754030b4503d01e484400c0c04000c000904021012400c454400c180c407a104540e09062080c4114000350b80b1109058902981d800c803a0155040d040145134840c910442c0c3c0c280c2c0040c40824100b0300e040402c54000c0c2d0041c1c500b02c540662824491000f5900032890b05c1320803240c46810b012030380d03251066501414054442c83d690b521140c0001c1c0e40d035200244683d200c0d03480c122540b400034640b158 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 455461933 1250 455460683 455460727
    0x3030f03020d05130516080c1e030d02010203011e03200319060204050f03030a0f030b0f1203270d0f060f050408190309030e190b041403070e0601020c0105 68
    0x10040043d814110001c2d294000180c900b50351034840c010100d00e00000300002201219070b0003009101c0c06459405102a99480350300680341344140c01d90400290b2014094002130302c10690006a4a60510680410130400c1e00c0c0c45a03001008503109100144940c1540030f507107040d00419261111121001034079041111503400707031080030546080308105483c0c003c0c2c4207803401110240c108203603190905649024840c000c1c000181e002006501e03541c080d034801c0710768910142140e0b902a0f1004042180d1510a031030b07100c01ea84c130020303c0340581e101c01c1170301140712000e02002d06e20f05024600013612410012001500f420404241c04007000199400024030070b22404040c4003c1c0f0386030400c4c40050700448041a408414036031a40d20140c868410a02e440d54540c8400c1c0e4404601000e200c0c00030b1240240c0481c440d00454041207044a00020308014950f503100c40315400c40240506041060030b0380001100d0b554901030001a0b80c0214007054062000c1ca00b072515181c00d4580703c1c2020055031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 455463183 1250 455461933 455461957
    0x2c161209240b13020904050906070c0206071401020a1d0d0203031c0b040e0604120302030408031501030b0d0507060e03150f0402060403120804060b1206011401030e06130c150903030f0302 82
    0x700c0410300c502075038005d0120f110048904100d1583d41440d0a9110311041f80e8160000e940c000c0b02e031005240210140c451180a807650708032110700d1000040c22a03200c58113440100c3d6451814a43e0205e00302c01441d446103040d100c080e0007100c56130110380d60f030040740c2801b03003521206825480b07100343e20b92241d01840c000070018400300d9510001180c4640041e0f03003d0314446400301e1201e000c10701a000700d07030055910404140c515969400203034841c1c0b0307134055803504040e10b40800c12183e91752100010741050140000d0f02140c1e1409002500741b40d6900c0c0800c0c0030303420140007407029001100c1c00c20307030002c1e03d820081156920f070310004105208a03003000b4104902c2d0a4581c00c40340e031200b88188124403a900c20404180c0c82d200300802d12548880c0d181c89680720030010310005070a4990005411810b06000c00c9440c0304d014107904040085601c460081d000c0000b00042c0041c0c0b2001c80c00a0a4401e0040b81c40f09007140c00408240b450300000d81400a060721643c40148203a0445940d00b01d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 455464433 1250 455463183 455463199
    0xf060c1a0a140c0c060912040b0f1224010c050c09040203070b04030c0504050709050603150f150304110108010807030b130b0703020901020d050c072c161209240b 71
    0x800025800350001058949244201800156203c1b40011000070030100d80581d64140762402008988582c44410707500a12202846032054010007400b0365801118200180c0c8910040045904069a1042d01c814104200184071101146000c40d44840031719040e5061000e44d0341318008646000001c6e4003401080c8000a0000700380039070011040281c6604550038880d50b11004405c5406107900e011301a8003150410205410901810019a1403000900f00f03880803401c0c4000100340c817a000f10203900f18a0008104802c01203140c1500341e0545003420441280c3d410006555542c16441c000180795148070300100e172020300d9014030040c0c8998046450720143c6012030004011b5040101028003510990b40e004040c04d0150094070680030080c40101243c2d8541014540700100c803d20900c9a1098018034032500e1086c21442c0e48100e900000324141940714442c0102025040b03a12000030034a84a440400210441101610f88500c01c210700000a903940c440c1c1c0003801342d200010743c03103200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 455465683 1250 455464433 455464441
    0x20d02040b030a151107170306130c030e01050609010f0308030408070b0703061809080316050c1504020a1d24100905010210060b0f0f1c02040f060c1a0a14 68
    0x1401040d01c540101050030702800c140e204864045c3e000d0418020704001c05101070301540e01404014591080004102c64940894800e01c2411100152103240009032181c210b0320f0350706000d000303031f40c0c001d581600c0d010300d650316110312207610a00c0c5000052980c0c07000001b2030709001031003082d0780005820200344078540c1404240030300140b10394401c0c09195962202610404c1c00203106000503e03410078035080c615074070046103841103410b10741054103000c42888a040c1000c400c0000c10220389055a6690f55424140100200241e1075400304101c045044681945459607450fa05e40040090f5107041003400100000d0756a20507043c4d51507000707001000741c69030195024541000719882a002d03500700e02c0c486000c00c0c0944220f40940030300a40200810b9070307004080e10007082030710108d00d205030415840d00c101041b00395080a0b6001c5254011a003481003549241c1800c000780341900b00f2084d030410320307640d112641d13041c0c044d601200e420860020f00b5090b100c2d04442440c0303c02c00140e01d03007450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 455466933 1250 455465683 455465693
    0x80d020f0913090f1e060203011d091b04090c08060906040308070e1c03050c0d091a040806040b10050d031205101208070303291305060d020d02040b030a 67
    0x7000000c81e100d803421540402c2480c0d403510901e803405030001c5524403208078035100e107100f8848020041c40c100c03918040c0140070131060701c051401f030020001e445040050050000c151410042c14403850783e000fa44803c4400d0007500d2243c00101e0056901090880c41d50411140c202900d40c00100e107402800c04000e150f080120310030f8441c80c0329481e0303051f05455824080f01e020b0389a0b5002c80d044540d80c0e00c0900d41d00ba0601680081c54441d1030a01d280407900e00c403180c2003d50007400040403d0b42c81100740996410260f044000304000b82c400e0303040030314168210355161800341005e840c02c0310300b10206480707110200d0000003500c4090081022383c030061400820142c0f21845c00030030140b400300480d101d0580c107420380084030550300c4c3c04100c0440e140c903102c101d42c0c8444000c4091658810f141100b8a03880910303456144400c480b140040703007070641800300e640c1400b02c8140e041d40c0303008200800340d50399050503620144c06031151100d01e82a8400f10340206035441c2d450f40e0500c2024413000403c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 455468183 1250 455466933 455466937
    0xf080c0405120a0b15060706050a0906180c080610060c0512030903071a04080a08090a02030703120f03050f160e03030f0331060c03090f03050c0c030622080d020f 71
    0x901c51340407140c01d03585915151005840d41d10b002a0b1164080050402281c2c00382c000503080a000e6030001503481059031400111020560188001c1003022640340c10300540041400c01000402c01074001072411040842581040380515010f2026031107610b070070710404200701550301c4180107400c3d650b4100010300c56a0b9410144d0129070030710143d072030700d88030150304000c5500031a40403443c542440c0945d00142c1d540f0a006004d40d00c140700302003118004d41ea003000000c00441c023070b91014650100030030300101080ca02050250601d4141000d00940c2003900348050350002d190482000526003c0d80102c030101c1c00304091b140d05120210306100d01c016408021400b0700210380040b02d411145506074010030151041099134540300a40070300104031103400000074982c2d41c0c60001000c1013a640d50600e0360150380d030103070001080442c980030a02000c214100ea03402040b0000c00f030790324006000b000b51252025000c40c4021004c1020780070812a0410b503801d0840c1384000f59110609204c07414099 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 455469433 1250 455468183 455468203
    0xb0106030f061e06140d0510030b06060711121203160e0910050f0d0f0605040309140a0b0a0203041a07030f030c080f0907051314160f080c040512 64
    0x500c2c60081d000410040c02103211403003180400410542c00c2c944032095403206090109000710920030400c103001d891303003803103040c1c030603007448180180a505504044aa00303400800e1140079003004c200c100f010070260181e80f40e294104a4180b050f00e21141100350521250f040303c942c50510200902061140c1e415400c9842d120315581c0d55880d00c685000c10541440581d024158404581001d1005003040d9440d113a0b540000707000e100c040041503444000c14441e050042e01d620303035a01b0034407040603800800340004020200c1245611880140082c01c030803001c0c401c0c3c45081c17500103145100d00b4001e0040e40c00a10b90f11240628000e052104940684c0c4024030441c0014040104400701c940640b1032007031100c54030354070f0102946d05d480030150b0000014010302d046125500c070004083c0e8bd503460400414068030f50106004441800120010030040c010844030a03240700c000f07011540c1304a041000050b140f0f018202c036200c8203900d000ca4070442e00b2094001820140020381c100d0000303107001306 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 455470683 1250 455469433 455469461
    0x515060a030b0f01030203010e0a0e032503110d020309010806040605040e0a14070b040b070c05032424010f0309050604080a0806030c1c0206160501060f1715130b010603 74
    0x883d01c056001101244800d0140c54542040140802e1900015501410305000d450007102c1c40c1c40d03002c0481c106100d45500b2010030b0200503140740d41c200340d400100341c6804100d0000400403034106030000f030344a00a0b000141d040117200000543c20342d54640010000300800782c804c00c90302600803811912a160140190b981910100c1c050415410010310402120401d1107524207080c100901c2800c03540c041401592038104400011079560381c180700c48c0024210a81d80b4004002c50f030000b12081c810700a014207070521032007110680b500324283ca0203840600c00d180030000c0100030082900145202680902284519000c02007041003990080914860701d803100740c0302d50740740410565103403890072403580c0243c1082c03a0307500c900b21208031801003548000d04c96400c01428540720300c180c0729010f4098556a444540400000c60340d0306410001d00002e08641e906420703400388190307503201c3d58281d40c4070201218000590700310faa03d2050311400d5100940c0e801959545400130058004c1c6c0389042e40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 455471933 1250 455470683 455470699
    0x13020f0907050a0f0c0201080f0901140106023003061513030f0b060d1109270a020f01080103030507020d030512150405090d0234090e01060b030402060d0515060a030b 73
    0xc104d60107400846841a0305940f040201d0390340a0388000381c040090149201517480c2c21142101c40502c0d14568040c2030741d030740104402c103140f0320075114141000c6031032500001d100c0517841110040c0c0d003c80c3c1e400b03101641c8040c1901e4242a09040074801c940c0c10b03080c444004a4044104004483c1d0342c80361038001c20b41034903c3c1c1c079008104108105980001003405000c0d48000419040c1034241541c050110b01d1080764101580c0c00345000c200074815130120b581c1001d0b000800f14038104001880e101003e19090703d9540c150755000e4601d120788803001e0f2180c403100c8012020144608200c480142c046602c0c024541000c1260349000c40d09038040b24801c0d820f100000f031601c0000a022680560f855000340035000c0542c01441807525400340348914407492032101c102049480b8410b00082043c2e00000810fa10100009808c4030050f0300194510b810806c00d000c09a90b900341900e0502000000018070340e110003042d02030740c0260b031001c0e9800c08000310314102e010303030554810500d145084d41e68030b03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 455473183 1250 455471933 455471957
    0x203030319051b0a030e030405030d021e0d080106140d0207060b03010f0203090d051308060906090d0903170d0902150903070504020a1b080705010f020a020d0c050613020f0907050a 79
    0x8000c00d40680c40c002803c40013801000c4100b440380e0042c20080c010601660f03c1d0580300c001003410308400c0c0e42c0540c050703440203440d803401e04100501c40c07911451a8000d8901488030000040c00100188903140c1009151819030384266030100c00ca03241555a000115a584080d1610b01c0c05007070754001d26840395190444600c020421402101c1c414000c1c5800f80101080b00702e015035086e004000502019501910040b4401404018445c0a90070b900d0051006141c4901c1080c500b0007030500c41e001300070002c541080029440e08290107551358500d404c13600d9202400041004010200020b9880403860710141003517034900004010281060f01500d6100e501d60b001e000907482000740840001d0843d000c80441c0d100103032112a0031602c05e02c8190f00d000159220203007900d20380011040d4440d0b000030341883c4240c040100c14000070440c04e00004031209500c0d00c6440c0d440c024460146031392002c1140b011503a600e80000b15030f1800403e038031028180702300c00a0054008110140220700c3e084106 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 455474433 1250 455473183 455473201
    0x405011404020105030109090c030803040f020a060918380102010c030603080f0c07080a050c010e12060c0903100f051b122208070f050705152203020303031905 70
    0x241d21694042c1c481c685964a00003802005050101068407050400303070300400000d001d40021800345002c2c0545400310702d0345004012400d01a41c0c091800d105059104204030f0812064030300b20a000010001a004441424074900211140000300c948030300d00108400d03014900003110404a003a4003c210a401c1c42c40240c04840d40e074003000c3c02c5505c06004414180c400400113100130302d4100c0c00c3d110740c1c0e6a1000068500080d54000300d5068000d07210a0049591104050201c210112600b03881030804101003a185c800207860f208504600250054044d00c080029800300b0070050b8041080540c0c5558100082c003068801040ca02403041865452116110075111150032a243c131244036160700ca2000001c0d055440c5605407030200e00400c0d400301d40e080b4041e221180c007078050350320f5141040c42c0c047c0c00c040036500464810074150356035880d01f003510400d440d00950041e208002260381e40362500c4004c1c0c0103602c029807600c000410445203101c038801410f642884036005010710b07147c00e01e007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 455475683 1250 455474433 455474471
    0x50a15110d0e03090306010f030501050a02090d260a1e020d022e05090303040b072604020604150215010b070210030209120616081006020d0f0210060608040501 70
    0x48000503000500400041d05065400000d084034041c00700c901d000844004241440001d83c41164218176050080080c84000c2c0500755000010340000c6207801d00c01c0001403041c10703046034054003c01d04404484800054800e10402d4602100d800320384800b28200c000348100c1c545c101c6410782015441304000c0d101c5c000101200310300e9080d00500481d203a5010303221000c1115040890760309100003140c08c9044a184211802450140e01031540c034603203802c1030081c0c105c02500344420002c1d00103045080c030980b0441c54411507005401c01015840e0740c00010003600072a0000000d02c100c03486206140b540000d00c01038509091107000506a070f907914404858000c44402a4020440380c0b903049156100794000c05580c08000c0c1001d0f510f07000700e052185000f0088881c0f580070350340010209890740c0c0005071503610500740321040403490700f0103030020340b12203c2d010031074180080d0340303e039000480c002d004842c002c2c4500c80c41084043c0c0c0d1404000c00105050310103645035441c0c001740ba98070408001c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 455476933 1250 455475683 455475701
    0x7092c0105041a0c0d0903030207050d080c040b07080714060f09030a02070e091f0203061e060a05032d010e13030e01110c12010b12030a0801140d0f050a15 68
    0x1100b440000c001036822141c0901c02090f00805900800c0600c1d900001403042c6d144180c0a070740d005890b0751184c0790580ca010301c2d0b1a0064140140001000002514101114143c4071341a900f15158142c5280c851038502951700010300d03034a01c41a0441e542d0070000380d8544504054401c000c8140c841d04403068413881101900700050308910030078012008c0220711240c00821040480d40c1d100180120b440003000a0b01402c1600354002003444100d00d003104200d61005061300910510038885800100c043c1320303049000040c010007000241d4100d84400510310401180e014004020072002240100b403002400b4480c0d0180c0c03290007003400c0c1c2c00100f0340d50004690603100d01c0c500d407401c0c00c019240711405c604d1506580c4034005e84d00889443c0c505040c0c10031034120b400801c16880341c4042007030a03ca4060a80400d600c03d1164404403580100c4482c1124404011034a880d58000d0206031a09031204024000300d01d403a11880401400155a41c0f81901030b10000c815051600000c80c25240019 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 455478183 1250 455476933 455476943
    0x50f06150a022808030403020d0f03060b040e0403051b0c0301060e06010e090919150b0d1703070302040f15030f1808210106080426031807092c010504 66
    0x41000072240d00c0300580040400c0004038038105a0030b00380d480c036000d45c0c0101d40450060704840c0c80f00c0b130b4403608100002e503040c2c40da040a102c1c0c5402c0c40320400c81030045100740380141c5c0500003c20241030003201100d807640c2295180100c0003205400c455902d8041c014000c0c0203600e00500001c11054201d5441e000e00c0d81607442d0742c100c01d410000c01c005180702400007034190003125894035140b884002144547c0c1c0c41106c882c0c02a001088201e8200c0d400601d041e0f01030f06150964a0004484001849002d90122540da85070b44806e0400c074000e001d503421908006015001c04aa909140c2c40d02060f0202150b6040c07201c0040340704900700307403903130b0742c4c2081d0440041400d020001500d1001030300c550460705e4210181d50002c5106900903285c02c3c1d1108020034070400901040c01000c228510904020783c07181d030100300c541c00141030144070040041100840f03c01c0a035000180a021400080800c44c105002c03030b1400c0700d0b440e1142014503045c4092081103e107110324011041c01400c2c4203030340207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 455479433 1250 455478183 455478193
    0x70c210807020f03010b06180f0a08030f1c0f05060f010c050304060c150213030b2d0c0c0105010312120504020310020313050a0521031b0a12050f06150a02 68
    0x2682c01e002907090f007280b0041d0725548450b0070b201d070f82e00c0d050003520581400261000701d56450809000ba020000140c0341e010b04d80001c0140440b610010485040c5000c15201551301d4460f101441c000c1003452141d20300c454200440030f184802c503a00854010b240881e20908240c40690054694001d040380003441900b007400100011400350003c0c5064034061040682c82106100040080b0303032200060004100400f8000d2081c01038102d02103070700103564401c05e4402c5809201159034100100b0300d04021004240004040e0880e0380e0076280180c445400a0201c1c0d61207140905070b02c500580004000360030202d401c40348034a14050180240d8010700945042141c5c114050080d5200070704100c00d110410502c50300150b01048907440d40d81c040c00c054000d4403011009805001881070025941000034400d11444c4048042181c0700d80e8112a540e0340d45950410003a107008201c0190410354901d0300080246080d640d07111031348508011030b030108091120344c070031005a000d520320200c01640130b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 455480683 1250 455479433 455479447
    0x8010e0411040c030b1309030f020f030909060604030605090f062a090402071505010602061815040501060906140f0301090309090b040f18020a23061e070c2108 70
    0x3070380b040f1650006450b02041440407103000c540015280c881191101c1d90b01c100410500d5400700d6001051101440a080c56002c601007050f40c84c0200206ca031300c200028004074000780d1b07070344c01240c0080d40d020805004600c1d04188080c0c50b85940c4101d20000d008490000d501a07002160081308110400c8171118291288000d0110360b402c188580c0b82c009a003008260701241580e20400440b5000e044045403941c10184001c2c10000d01901d42c0c0c000d02c0074135980764600314001c40d91007049032946103503c2da40e55a03420298050a140d41c0807401e661701c1c080004c5042c020001e404c00032075906980b20010000c944081c1401c80b1815a80030340000c05016082c00316030b806420059517032100074004249201c0e0309441008851110302c8070110380328088800011810010b003444000c0040e400120750f01c403c1e0314814610b40b19070104c894403800c80003800340441000100c07520082da4412000c1910b590080c030300300b402200640201044110240d407807188007401e28068060180d8080212800e001ca = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 455481933 1250 455480683 455480689
    0x101206051003061d151005090403020a12030c090510080c070c0302030607080601170f0c07050f120c10020301240302121918020d1214030108030301030308010e0411 72
    0x1000340500c1112481d012000011a44074015070344610600401c0c14151112041424500240f024011008641141c1001b090441c07242c900b80c112103059900084545c0c4900c0c0c220701f48811841d005001400382c06109620980c980e10400e000382580d1242030080da1079004101c0c0c96914240d070a4002142c0d84000354039100703648050416107204c0c0e05003112440d102e80c000f80c10500111740c03a1001948020070400b41f581d002145240e4102c0c81d45070b03040c00341410f032020303025401e0082508150f00c800040220030400104500d000607039004040d502002d00a07020b1000c3d43c2c0c4070039407500c0c007840b0b4907034200c88842c254070859040b940b00105058024010000070080b43c0c402e007031180145036090040281849020100a2050010080c05803000201303000c400c0071104892041c80d22080902813100058a48404511115420000800034820811030444001042c006400c0c1e0509010000164041000000c0c5060700c2c441e80301c03600503a80352482002d12000448014006191038641501282 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 455483183 1250 455481933 455481941
    0x6100228030210020f03063d090b0f040306050606040815060109030506090a060e071d13120c051b0f240f090a050406051806010903120302030a05101206 67
    0x141c400e0040d9103200ca42d9007141c0c0200e801070901e100c0941400020441ea82c6024030002001142d5072889405030000121954600c4104a00f42c00d41240014100a0014064000800108600c0d088290f0300c11072084035039000d412901c02260164100b4011607402d103000019201a51940002040c1c204005021b03035030282d20141100e814440d8040b0b002c804113a060004620078815403004001e11145482e00303c0031185054500e0025402201007400300c0c0d0320004030b01400c0404056480b13400d456003051003031440a0000d00070001c501180300d11030132a8000361841d200b60f000d07106590880c0030505405d840000351403489135200b1403442408455152a0501207000e4600c0004c10000411200141d04241c0c040d65102c2303180000807442809034603000c031200e00608010750303040c05410b02d00030115030701e00a009181007041f42440c00051590b4829583c0000964000744c00e00d0500000384000740c001d500a40d0007002c094180340000d5200e021030100c403001c69031103081140c0c3d909070540301c4070020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 455484433 1250 455483183 455483263
    0x607051009060f1b080f070504050d02040b030303070801140a1d100e010f0504110405010503041e0b0f040b070201090809060a140403121b020a0501210e010203061002 73
    0x6540d4030440c840102d4076202d56002c20280080c0d00710284d80c0580301030700c4110014010100c4ca002c0d2000c000400c0d5004041d2000c13200150b9482c0c80240c110310024028200b0004482e0b054032003c02004441c44d840090a07040b904281c0b280c030004420b03c024000f203010360f4080e001209003001c0d2420f0244002d8003000307922080d4000c3c141142a1211481940560f0a030b00590940103a05814011403070325105000c5614492041140741c54039010001c0d10a010080018002150000e00325054108040d10504680e9010310a100c8501c0d0180c0c2000e85003000340c030252140c568036030000340e605005206024400b40c05c11259400c08820400304881540b210800c0401c20184159081068068030080c00c05148262854085030090210040400142c1103c100741d80120b200c1103405601c400d106541614803c1c6002c0ba141c01d64101c2c00c8917805c15202c1510700f01c501d80114107d40d010190702850003414101d0f1455902c0f050050100c2c0e8965684807410041160080b0544074044106100004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 455485683 1250 455484433 455484443
    0x5060d0b1002071a031006080c0f0406120c030903080f33091b0f0d110705100f0b0a09180f0503030a140103032f0a0c03110607051009 59
    0x24046420020900222015050070090f0340700800501c00d552801c8454a400b543c03802501c0c0c114a0304100a104280701481210b06004280b00070882200c008800c44082d01401400d55544694582c8020048050306170340e0400e41b03141c14038640189102e402005400c42e050b5540043c6900e83c0460320000320380182c2100300c49100b81403100003880001d00d001000800300380c00031070080305036820b000d07804100510041c07624100214a00b0a2108032007540c941064100c03505443c0c080000d8601c00070602d040140023030300c0c1d02041700020800d000030b400407044405141407100072014064102505c40060072503501039410343c402c2c0704a00266000a13040c1c2500301034008402229110525000401b40040d1002d0300000708000c0148502d024050044007081c09064640d803650310002c0c140341041100d54521103000b410410340e5419904140605d000b1074003510940e550900d0420601c2c0d44a202c21280c80400c0e1003151803516111068810a1750800003820b12016035040c0c15009004d060307000c9074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 455486933 1250 455485683 455485691
    0x71e050c0f0312010b09210a0c12210f0c050c040920060f0703031503140d1106070207030312061d07020616090915090903080723030105060d 62
    0x4520041004a00301000745480950703501c0e00b040f5883c0c40e40081c142c00081c1030070410001000e0765154918035601d005514180042c0c405141174200d03051107000c081c0505480400c100100c0e43e50407800c17401e5031151140038030030030900f41003040c3c412000600d14180c02103620f00740c840c130b0703d44d000340740340307121a0b10480c00e80e6800c0c410140041c045030715030328041e500008910484114403070891b52030005c003141180c203282007400781e40c201081842a980700808040d02d6010307040102440004810145521280d800518200411119a5142010300490003c0c0b10807020780c60b072a03c0441e1842c0641c80c240e000d0400d06045440940d540261460080030542c0e0350180094550400e252040805440d40052511818101d40003450b02401038065070b9001207c108501030307141c00c045224126081c0c49004114451462070141c2058010340c0700310030660401070890300701035022030b00c144101d003680c03158290480c000c1072054418081005501c0c0448041005105900c3c149020f413a61444469003c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 455488183 1250 455486933 455486947
    0x10b03060106080c0c010608060108010504150203010305030301090e0f0601180b0a080d0c17030a060302120313150207030206070f031103040e04030302030c0c0f07050109120803040602070819081905071e05 90
    0x49d1a2a50980c091394a9940d60700c148410003101e5802554003440085041d03096505548034603840e4841840f821a039507644015000710300002340b0600080700c00000c00e4410640c2d40301401003400034901c0c0350300080352600d0b0282800d80780ae0f506540590710002c00804007000e020f801916181000101518030f03200383d41c444c0e251284028020351190f02084000300f205851803041c07040f0242c901049140d02c1d001444441c040100c19112141210680000b01640d00c1d40014180d00b0b18116410194100500040c0f101c14440a0006c0b80045c1e442540c1c0d2042030700301d0340c60007900c0c3c0c081c1d4003d00d210381c03030b9400100b00840d02c01d401540c0c106070b54213440307441d0404402105241c0f402800044486401ca54420041c0b50f070051031420007440881800b10860150355201c850900c070040c0000c0a00394081842e81c14055000d055406292881400800e036108815014014920480e10a6007030000c040100e803c034002da02400e402031601e51141c00040c8800240800380d0040000d08008008040c4002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 455489433 1250 455488183 455488199
    0x70302150c070311010f450f050913020114070309050604061110110702061e0708032406030f1801020f0406120b15070816080c010b03060106080c0c0106 67
    0x11000f103104408480021440800240055145040d03100600803043c20400001c560703074103c44820762028004030034007001000d12034981d100c50036070701c44607444003480801e4900e03202c00404140c4108440201c3c040d40d51080504211000510090001da0b5000007028460804809000114440e0810005003500c0340085609500158024000902d09003550000c02c081400602410800401c0034000d0540704004141c03144180c6400a00905c00061101a4052190014180c8103041d0884691351050b5060004040e002680c1c204803400e2514003c10305a88200c3c141075108501400c40c600303540e0741e40e050003c00c034070051640c6032104103018a032032480b40030310081c00d034142038007001c03602c46047c0710005010344200c0c54403203013240ca000c51800b000d0f0f4070f2000640e5804e45041c030300380c4d03205440d203400e8200340500880c501c124500f504c000760030003480501600418400b04003c01c403418108080554500c820700c0388201088048011840c0046100b00034140005288000705850340c0d04d0403c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 455490683 1250 455489433 455489443
    0x31513140a0507030f0504081902010608030408070e010b03070c020904020402190302130f0e012714010905220206030c130e01051002030705060105040f090f0c1403010e070302150c 79
    0x80d0481da42e40e208100310029406214004003200100e4003081340d80340c59a1080040c0c800c0300e001c1c0882c0d00c1c81102c000000c51003500071201070135900d0166510345548000b0141e48009a0203130102c505008400070400382014425280704800079035580421aa05409021204101030820398000340c00300a820003034211036006d180d010602e035400503a1400110260178000c00590001091511404800c010303001d010b29010741590088213801c41c1d000007031070f0181c099090008540804a0600d0550881c690822010b14103e600040042c071260740d0b103014000b19101c0b8401d05180512540c02d010000d0304150303002e10f50100101d00c07114500b080d6501c000f005400c841d481402c614013608014040d03818100202000c2c4240c40c002103052400130342d14591914814015240141d41c0e40c00c0c110146540d0303400c0a071740c40d500508094042d4442d410019941400c40c0156243d0228a418400a07420141303c1c000841c50346501510f0450705680c200032644400d84a5040510030612101c2c3d100079003404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 455491933 1250 455490683 455490691
    0x140702040c1101051503100b0102010e070902070b0114060a0f02120f030103060b04021213020607171b1c05031306020c0d0807030c0c12090305070801060f0b03151314 73
    0x241c0b0040b100e0503801190a40300014080c107102100c2ca8a55907040e1000a03000840502e00344000c54044003500c0100d0060034014030714030342c41c03140d05000111909180d00603c2003e0003a0365401052380c0782d500070512442d4052095030032000400503211010b110303139440c800180036881a20401d280715040c1c0c00054009262000324850000010010070505200f00c1c008000141c1e0154142561001c0550322820b0003801000500f025030500000c65070784208840b18164401a1072480d19a4418502103a401c00c020700c001c03001070b801500200380b400090b02c40e078031810301d500404108c010150840e295000a030000b410207040c44503c1e030000d0040c2c0007603c04000e50b40c00402c1020408440181640d0016040d0010700d890074403055484c9901000e00100c0343e402ca550171408200440c42101c155940350b001030543c0c081d03503801190240f01034001e181200d00c605511114192140040c10051000b5981103001c4d11042500460b941008007524100306072070400003804040407280c1c206103d03c211 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 455493183 1250 455491933 455491937
    0x1103180c0603091b1c1719090e0711060c0d0b040e0a0b0f090705100c1b06090b04150c140a080a110303040b041506081204080724140702040c 62
    0x5107040352080324580050381062800c46a40c01c19880d5000c0c19132a0854031040a449401e410a040b40c402818908588007c0404102d200241e141d00f64001d00001850041c040c240220f007000c100241e120b1030342070001c2d00440001d800280c88043c0d011200ba0f002c8000ea00c49140c070380784003262030b0780c961180d40d2102e110300c0d0281214100a2400042e405401441ea0031030040e8503060040c2031030001040e00c1500c109580c02c0510b0300d80308100360b03280504804000c0c00300089100a20035035000d031604008071500c03034550022040d03e8222000f0340740120300a40350b4075400d000e10410b03410300c55180031101e0f5000b03070940106034520458880c00c14002e0070050b510050700091034072103135911000f05054444840c01950540c24280e0300d00d242110007610103041e07019164070412440185603c1540202414400c4406505083c038481031542c000788607a00a5000310707900000c0d21008518030071110340c00f00051201c1c4800002064a618000e58012001340c4003e101103801030300c403403150941c050025 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 455494433 1250 455493183 455493193
    0xc060304050d02010c020a05030d0f0b130603030f050a051204020f06190f0c03080a0b19031a0901090b0112050a080a081b0c0c040203130204110d0506041103180c060309 74
    0x48240a8290317400302140c101194405185840132a0011043c2d50300841d0b14200840c3e0885940c03201c40c081c001e0002c9040c2e200c5a0500c0c0c90507190a2507006000705c81c42a103a0f6885210a0241610a4094a060640443e400704052910380c081c440405034403502c0282002c103074002c140b0210346c454010038030320304044070f5895180d00607a42000901581d05540d2074443d4044806940041c080800900280405620f0f134840501a540300703125a402a12101c0640940990720b042c21120407101900c00d0105100010120b041454180105e5520a80281d8001c480e41d20308240d41002c00000130381501d03140100100c0c14006070402c801001401c00c20390300c1211900b030141440384542050343c506241da80d003c1252511100001c01c420b203030042e0407030700141c4076515401005071801204a00a502a19200301c00c03500440c41000b07414800b60341c640402056a5a000384012075070201020141000e041c80002e00700c0800f110906000001c40c1c0c00d541030701084402040080e0130940740404c030394000f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 455495683 1250 455494433 455494453
    0x30c150726130303090f05010f0302031510170c12070809010b041a13051614120f0403091d1504090f080d11030c0a14040e1017010227030c06030405 65
    0x802044013000d0302c0000c1b02c400d81d0f14035100020344200780b50f0700a4014550040009620078038070390034081040b140a080a02d000701c0346c800091158642c0c11400040600b01000715094403040c40c203490382001d00442691450b164032001360f035492002002da144941d01e078540c2e0407164455004807201403000d0301041f1314a40f036440030020400034100d84010420310700030420800d049521000d150103c1203007040d008602c0d07040f03c0b00341288241042c0c038405c00e00b80e0003401000e400420209200b076009070788410280c0e03200e400d0418544019200141d600d40c82d41c1c00b08841d01200702aa030f540c0040144001100c41040c0d8520710b0350070181c1c5042d00c8a030404100c015803070466018584003906047c1c852451858480c0b84600c29002d80b10304030040149a01c082d030b801940750300071078002c0e002c1e107409000c552409443e00b4840c3c146a01403d08041d1104503521002c10050099884641c0c0307807594042c0215040c09815103c100130700c9003507494800c15100c42a80d0710786000540c000c0e8041c2700a4240156 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 455496933 1250 455495683 455495687
    0x314041e090f0b13230411210304030b07051b010c0f0921050f12031501080c1605011508010e06070801150804150e010902030c150726130303 62
    0x21500000380b12090a106502c078141e40e5900c5682018405032400158561884107054003070402c09001040c3c07484400c09000920803180101d000302c5e003080387e000b0b0102806807464a581d000c0007180511550040c042400025444600240c2c090b20314036040381040f00b929103070621078a100f1010562030b599842001400e40d0b004142d41903880450809005040c58000c8a080881800c10601c0c001c1e0400700c182d8040260038000c54150000c50022108511100c0d1485601c580c000d440701c660340004821041c0c025401090001d1103219105616402d185044403070038103951343c00c1000c4a45541e514031a1801d000c101890341d025001034400040e881000c003000340d1a0000c041c04882c144000b2000420030043c2c40854004c0c0000607107880f0030945c40327a2502031140002054600c420504041704146141c205500c08071050740210100c0d28800d651105001d01810300c2191002580400c0044002054103410314403113444d9150095080003041301c84041c2541c010341c0e010310004685603010401e040d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 455498183 1250 455496933 455496941
    0xc0203010b01030e0d030b0d050322060305040b0703020d06080303100f0b070203210d0c050c06160206070e01022a3615030703140f16030314041e09 65
    0x52802c2c241001350b0122404603654814580070003408040c1c0301e2845c0c900540b2000ba50690701e076407240c02c880e101e02c625222104003000032501018141c00e0f03d840080c10f1071080c0501d03402240c002c0c980c0c4800c0c0d110707044124041d510140210640f10744034040041d007030008100541c801c46100000c441002d0400ea40f034508840d50380d02c803150502d024004038000d43d1780801c452190006c0b101c40041c42680070355642296000744103040301c1041c075045103401015000030040180310303507240944a4a903142041c5000440490603442d0051340702c100040d48960081112401400b0140101c91036082c034101621411040300807400314084d0148411074007428078440404581541030b1440c1070080700c40185d44500703215440030904c840701102c0410140e200c040d8210b488540082c0550303801a880341050951b141140d441004280f00308001202080804101d006484151990500309070b49580c07003c99107400c10f002e0414500100304000103e0071504111a540c140c201c0d901948401c0c07a040496040b9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 455499433 1250 455498183 455498201
    0x71b210c21090b090306150d12030f0b090f06060c030d020f1e0f0f0304021c110f030a030504090e16061d04060b070209092401090513050703060c02030d06060c020301 73
    0x428040c000c3c0b204c26603001c00d01d50360000e030010040b0850211100022010040500c01900d441501d10109102590682002034030200081082c07141d4a010303001d11203040030445940c030089846901049591410304001c1024249140841e800c100c103078a4042d0480e40040303411422508001000c0c00101007003944190064200c40076142001803040d014030040c49105412850071500100007000c5584e00c3c1d038640c2490030304c00108051213911785040240342d003580f114644103071000c00500c805850005411017900754503540307090420780b0704654140545010440d43c0d000780562070310f04a0005908507110001c0841e591000c001d5000180107000414036891468003403800c2000a01c0b01c040310104984030700d0b038103444103180366944081c040d05110000356180300c00c141750904080d5644140c0c10050585140700d104101c02c0e2030712000c825170b03092003050042036604100810404540345511000d0082a2030044d04d252894262038901160010303040350002c81c0c5d4221003101942000d10403a546 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 455500683 1250 455499433 455499449
    0x618040318080604051c02031206180108010507081513020903070e0c1209011a0609040f02040b1308010905060612010608060703020403120e21010209090c03071b210c2109 75
    0x80101b00c0b540082d100d00c00c850781c02c02d0107024507010420780c3d10b428245d1030b00221000c86080701541c503510010f002e040c00351174030000902044081501e82c04040c1c0c024901440041014556064000c90b51000c5c0d0041c12131395070300d401601d00000c0c0144100354143e124415000030380380e030350b464414903100543d4041c12034002a031624008403010000b0040071418488111081030701c404451002078050720f0a504820461030000c10002503c1031060301070110705807421003001d41251109941400c0b1421500080c155520280108000d1b040c0101700c4800d0003500d0001045c034584414000f49844020340303c440020340d00103010028058144002ca068040034034020440c00e00ca640012031500b00d2001064185c0a100303401c0340e4ad04400d6040b00e0030420083c1c4a01540c4c6458010340483e40c2084a00202290314100400f104d600300003072500c40039900c01030340003100040c1040500ca8000e880303000c1c0c06100b0106101400300741051320389140c080c02b030b51340c1c5811050b1407000145030714496444411 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 455501933 1250 455500683 455500723
    0x3070305061c020a05011220090312132121080915010303050a09091506020609030f12040309120c0801150612021e04030303020c01060e061804031808060405 69
    0xb0050340c5400410b0110381c001d180411a107104480014000c0003080c480702c01e038540036000303080400700e02800b91042c0c86040b0140c0b0070514050781d05508a1182d0520f1041c0c10f5074140040c001c0cac203c440e80c2d82c4551201d08800d801107507203640d50b1410892000b448020b10051041001480c640d00060499109943c54040c014845c940d0800c0e000c1588107020080511101207410003005102e40030080c0180701881040c040514181400400c1c0c1603079002e80801030080d6800620700101c000708032107906409449e29890000c1803000e00d0500f01c4090320407404c1000408000440443c7c0020300c0f0385080c001c1c2441d2440d0b614021681c1d08643c0502014402140d140b50104510b40e00041d144404105208001da580d0341c01402544600565000e80c00c8a20b0000c41d000c0f0506034035901900d00144014001c00c0305503119041400c2c007441c21a90326600c06500e1620541c11300d00c44400340d030490700c6804e010a01400320603202c0403201d001e4010301181c1d4010003c100520500700b01b1800c5889000703c41807 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 455503183 1250 455501933 455501989
    0x5120909010f030f020904050c0406060e102307020f0607080c010e0706050a030218030a0302060a14040f021210051311150304170702090f07030c0201062103140307030506 75
    0x1031001e11800c4406031041d050031b4005000d000c4140001803448a008004000c45522004c3c043d00381d2801858040c010000c000e0841d2041d4000c00500c100801458043c1c0c0e00e0036106240440c1c16403104100720781048036011003075000c0d2100700260414a200b101c0061f00d541440c10a0b03801c48022503201c03803107544130120800031542c028086513550001480e015a03110710451028030741000e9a9403081c1c06100d1210110189039000c64200c0c09070801c02c00034041b640040e0752000c0703041c5003a18023600000c3c45811000040c03915004140b0035940f030100381c40710895240f8146041300e00441c0c207141c9840041c2140d0003085607600910004240c11186c12803d502280305100942c080100014001c0032107007038000c0043e10400c2078402c2143c0c01811824140790004004140207020768070500840c1c208855210719500601811050b1115800c0d00e03214030098418404420b19011010303428408a68401c00e0400c5c4c029006610036100c42d1008299403c1100034411455508882c0e0303d51041080041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 455504433 1250 455503183 455503193
    0x3031021080406030b04021e070b0a0c1233060e03011a12120307020109060e0a02010c11010c08070b01051801080706140f120f01061805040f0905120909010f03 70
    0x920b081c1da000c0e140c00940401108040390080c407404400140c0158898045441c0d000352100808449214508904480d150a50740300d060711102402d42c0042071900507015107140d25940844903210100e1850244510703c04034542d02900141210b01a1541c1e05100340030130360308900d20303032105042603000300820719803c0b000c0320100755411340e130320710844482c4500315405508000181a000e40c15101560300d0805800283c02400020700031161030b400c1c0020400c1d060700100d420b06100340c041c0c403a40e4802c0e040d99109504e445000000905001441d02c040000c240d126015116040c861207584440f541064100a2880100014000465aa88014803070310300301140399002c842c4103040280e0380d4903e29200000c40d00900001520754a40400c1820400701e0700c2d43c00500038071010503601d400c1d980707071081241c14088400c0103141400c001c5000b04010b060a51180012030340f203120000f0b07003841c1c035503506d07080001ca80000c14008201050704001440c2920300703a0b006194500c914814030f4a15130315 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 455505683 1250 455504433 455504437
    0x315060207150203041508100b03010e070305040302120d2a4a01140a0c030e060408060117120a0f0e04060e0a092a21050303102108 58
    0x414520501c02c4455280301c5000300152009407806080706941d2100c100030041a028044960044900103150000b9008907400101c9050780d50400d400e1b13a05a80700c920560107004050003ca045202d0314808041c084420405011444180d031030100714103000b1064030a402c6101503c0c2d0f0010a0400c0d4a10109904040460280090074682a0829149400c030030100b040403c0400001c5000710300e242d14503100380b10048851242603ca541c801e1400545410f410f0013242d15200c04a20f8442104001c01d006031810990820000d06c5a440c140d02e81c1085c6080141c03c3e400071040300c01c840c0b03815006540612038040385442e0301c2c01d56414102d120400030700d525032000444046c0840210302218a440d030342c20000c06000702282c008818101303007242030002c00321140195200003460341c00010038100244e03462106045004c1d102c2c5841c1c1480c68144050614098221585c1034000062000a8060001e984500420360442c51010300d41148560b038440481404061084103074004400100d003401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 455506933 1250 455505683 455505689
    0xc0705121c06092304170d020c1506010518220920010c0602030c070512032d010918050d09030212010c02060a05060a17030403020a051c03030c031d0604030315060207 73
    0x2c4030292660f0420790725501c0a501b10395070b03244000903180007039207454000303003800a008002c4940480341b40480003003da8003940c1a42c0010700400200c01d210070880c208071079640e0700034861080605011000c04078803814410038001a0b440c0c4084000307001c407a81521a50800700018000e1071030240000901032220080018a051b901002144409642405603011154048112500c60381c1000007843c0c0b0381c0044540c1d9811500b10182c60000b200302e244400800035403000e00b18080d90030416500f000c1c00881b17040f9880203060540410200c1d20400510294007096240c0e040800e0550040c080340002c44454a0610307030600f6001001c43e41e001407072652040700c03050006000d803034140001e0412003255001c05c16403800b108600351059404401001102d1003160b030004410f0f80d51051045648041580e0315220341c80310310202c04a40250024101c01c0c00a107400941182c1c601d02c0004551030134200441154404070801c000c26425100d2200c0002c126210701f120f092810900940d16903441c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 455508183 1250 455506933 455506991
    0xf0c07032102150c180d05160b090d021c020d080a0306060f020604060b01051303150c090f09050417030403050901080603010b031b030f010c050c0c040b090c0705121c0609 75
    0x140c1c0080207170049961100d01400103005a13035461090900c00d94403240503030810040c408a403800144011603908423940c0c2c14020b0203003601c08070385400f0001c0741c06c100c454200c0400034605040b401a0382d2051000003446c42540020748034450340a00400300c1342d4070741004081c002d800101c4140320f40c0010300c05a105170b2110000c1407180405004881c607014946110212002414020081100e455034024503840f5160302000341e000c0c80c6804840c4402e552040018000c0c4164040c461803007240c04ca00da0080c01b9032840c007035541140000e00c180341d2088405800054006ca5076114130360384451030a4018400b28024048202000c00003a10307903001d10300200c0001d05c2c3c0d40d84805e85840c00d02414100c01003560081081a0101070b0182465008410903030690240c5034280d0340610f868400c1c04c11201014103002a10390f510388060001d41c0c44801c003030340c082c41005c000c0300b501e2602c0801406117040041d00020340c2c08030800031509550007504094401405d00c1401d01d500c07a038a045075210308a08c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 455509433 1250 455508183 455508187
    0x90a0209030a0501110a020613020a03030f05070f0b060118051c060b03100b0909150109020708070209190608010b150f040914060a08030903120f0c07032102150c 71
    0x90006840c0c042d001c0d20041403542468015030504076140c01030b220007942e40e0240d88003a616090000c6036500313240c030000d60001406605201091003480800710030103803410031a103449410345403410490040142141c440742c17101c08010b141c3d640b20b80703008a80c500200c00f080d00f4a003020300103000203e81100496200c0120b200f8030701800320580080007407210150030f0fa04030301201000d0307001400d4500302c1f283c01501c080001c5000c60100042e8040d00d00c1c40441490207507403c20101c50040c1d40902c80a07a5402c000340100c40141c0d0314032114a008800082c10014000f1084008000381c4d840d540c08010710784d2500800030541c1c0c03100c2d1811600c0d04240e41e8015611444032030f0901d07150045400c0014041c1ca00b00f041c03a50140309071461070089004a645000140c0e5402c02d181d920b1242483c07140d09900080304031600c40128030701510720000b4100c5050304002180c0d407101c1c5442d44651043d580910220100400840d070b441106c10161351610180081d0f503405019002d08007070141c242c0d0103810700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 455510683 1250 455509433 455509447
    0x120309032705040519050f0c07110604081005091207030e0f0d05100203252718090c060908071707030c060c15180f050705040615030e010902090a02 65
    0x386500072000b411008208100030308002c061a40c00a0351041d683d140741c0d103018085114601048102c42c4100302c1078000d1840c0c00d0709076a81402c00e402c402c522640001d418400810104024400d00241c2060341d180082c5503d0300324446e51602e100d4000103031000e2010800b80b40841d61042c0403d04080c01910541e40200d90303440403480810400c1800352032401281d0a1b002040060780007503019082100d20311410070a6000041c90042c60002e40001082e0b641d4003858113090908040c9480100c0c00d03c10060203075481c00400b40800928500803903842c0c0d640181c500300180020048054151440c1c455001c034200042e0540d1440c907402500031500200f40614107808040010030050360b0f2000c1d1000d40b040d9641c001501c10000a44121041e1030f907400c0c00c61142c280c1c2d2042031020b0881000110300c104054a4581c80410204400e070341da802649408100354887e405200014900c210580c1343d4a148c00c54000c2c1210003600300c03c60a03074100000200582e99101540da04500d05003c01652450 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 455511933 1250 455510683 455510747
    0xa050a05130801060303020304090b061219090c081f0203070e0603042d06050609090303060609060c070609061112030403030e0114040605090f030403050303070f020f0a05030712030903 81
    0x140c40d5000802c15828203a01008150707010010b8030440300d0000090114003002d00401490303000e03055101554480800020740c4840c00c0210a8180c038500c03d0002900e02d000761202c41c1d6101d0641c1006500d580070040560b8020b04010242c2c101c0d0030a00c10840c02c6040030342c00209040d0021042a2080030080041014028680300310003104002c511489401c603182021b103400d68080c41020b4a001e440d20000440c036041a00300c140c841c000c0d50014510310756030b034002c00c000c0d60011456180c01032002c5c482054040e00401202c0040d02c3c403611180015450550000d2032640107804030682e41c0c120607920051070202d842601c0e04a0ba050070041015504d00705001c0c0140091001e2403c0300d5400004d020502285600080c00b45000e5030960b20b000003000709880e1740e442140300007000c2c0d500410000329924840d0360341000c680890300c1034402500c2c1c3d51285500d0591102c1098410707420000d007900802001c600a00f40c0b00c40541070a120221094130040d040303a4031140140900c100031400101902 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 455513183 1250 455511933 455511967
    0xf0509060904230102030406390f050c060f040b070518270a06090e0a0b04080d33090e0624030706020127080d0218090c0a140a050a05 59
    0xf40c00c0b580210b480e4985400c10901810209003110f80d414440b071010100390071584100120a081c0f0540801c83c840b000004a4402014451101c10007a05021a40b0307001d81c2401603e00450300c200d030145076410941010540d0b250003070456010303c0001c0141c1100c0215000404108400c211825080c0c0720613000040e07c3c010b20b134070004880b00e0042c0200804c000980e405001a070700085030402c4048010703500c5a694111514000c0e003c0e95800000078005441800144205116440b010071f5000100303060301d50713600c41d0b103c40302030030300f40920702c403880592811100e8010a4600d2041c4951403240c01d00e41e40381c40c0d01404c845a00c030f03554070801120080f03111000210340d101904450601e81d542c0002802050501945200d01041c0380701500d0100000c82600c240703681100816107000c54a031800c0001b540000b5450984002c0e0b100121016540d0206080c4503000128410350707560a4844010100f542c0f00300401d0001e4810310a0324100b5500005440c1e00a06604203a40e58080c2410116592 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 455514433 1250 455513183 455513243
    0x1202070c06080f070809071e0531060e01061206051210110406050a110f03030c0d0b0307032a030c090e1605010e04020f0717040f0509060904 62
    0x60030804000240703140e80301441c540310362038030410492141c85003102252100000e640441c090b40c00840107100285c102c0d1300d100c0018002d05076080000b955a00801c040c2d0f00e6a113200c407442000194503104000052800c6900c0722120181004540d06052030b0b00340d8100c041c0110410841d134080d203940015502d50000300608402404490034507801c031462951040404000c00300d80d410f08114000c004060f409aa09562a0707407202402e10034005011a164461425040028440e601010b16003c0080c40103502410041e040c1c0e075980e43c200f1580b90252401588007501035030001808001007110035010700ea408017140401c1c07242c0001c0c021040c44a0007035820140c41003c54240020b200ca540e0380c058020b0480c1e12059901a50b109850201c444081b48107040c0030945d1301c0101e14491801e03600410302150520300c0c00703040400a40310080701a2042050301c4120070000b40901140a22a28000c020b18044401c0c2e0034070b1811078080354202c03002400040ca42140c10038428044184c550584642c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 455515683 1250 455514433 455514443
    0x703020a0306360f02060d0f020307030c0c05071a0f030c09040e03030405060f090109210905031912140d0e0105090d051206010e090a060515040302180903090d030801140d020a0303120207 82
    0xd0a6523002d0f00b00002e500946400010a02c4d104c49032018600400da040113003a040005403100c0e61910048600600501c107015011480400001390901070001c01b46005900c1c4400e0691544204030a1004481280103420382c1d0f58414000c10000680001e8042c0e40600840d00d24803245c1c5401031914050803804100802103501c020b4419400312030101e040c1000d5a480d070b00d41e20311039030340d00915842d40380e01d410080b0705118412075880820082003000c9498007592500d00160040100f241006400c00701d000034265845007500101d402e42402001e800050080240070781284880d8068900d101c4c42c000c1c1c403603184480001400c00d1b0b000384c5040440f1031740903200000a00e4080204002442a0300617148510030800340702007810030002c00e072000d90364044e058801c000c070f45062035801c28900400b00750710340c40700308000c08207610b8120710900901e200352a168003a504024201c03142e404c42c07201480c014440c0300d50203c00740e40c610031500222609401c001c0b401c80e001681200203480b03a8440905 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 455516933 1250 455515683 455515691
    0x402030426090a2907020d031d040e0a03030509010209010c031101240906150503060f120f0d090503010b061902010b041505030c0f01020d030b030703020a0306360f02060d 75
    0x10300e901105040348a261a035a13054641c6444200258010b000d0014040c2d08100f40f03211500011340102c803c91910380e40d1299000382030b034034000001c007900c4080c40c94030b056400171807046c010136800d8040e19400c41b01000c0294103001c03400000926409111501500300601d82103c0220714a003075000300010005038800450b64000b41a0305160b1302c40510130114424581200010304105020f080b465003201c950f5103900c2e42d19031104002c586000c26440c59840101c0c0c0e1120400f07900c0c01c000441601240d2000383c0003000c421400a4101c0c10380b640301500990411000f5a1300399260f00c115107045920f00f0308485603102e0040b0480c0181041200660000d180c400441072890f1507036640c0c2e00f254022003c40781c01c0034003c400c0c03001e000002c0c014103015a000b1070076084104d000760001d03100703c00c000c1d04131102141d03a40c000405c64506c0354025110b07075550710046003003803044c198042d142100382e0960982c41e004441d032120040b94202805060f018402c11010115614041120041802c03120248 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 455518183 1250 455516933 455516939
    0x60312091a13170a031d010f0e030f061f0e16050a050f04030812060f01080103060c022407030c020303040c03030e270a05060a05090c09060c030301060903020f0402030426090a 77
    0x42c0d1348101c91802903010030014a90701c0103503040740944001002040c2e6901540960340c02d41550252525200150706002d24291a100c0c070000f0400d141c4966a20000e000d40900d448002442045c003a4128a10580a8804200c4500c5e0000600d1800c0c082a240c0540e40300105a41206ca80c0101075000c1641c020018000051058000244c4054000d81d5110b04080d1102020000c0400000356001d002c1003400700100042a140e502c0681c0c1c282c80750060b2078000c01300341708901c416205d501100c4e0386155040c0c02c1c8080315a052181c0c03800718106d4002036143d41859100c1d132042010b544401410042c1164090405403224181401c02d03400d0905c4c20003e000d011700244640c0142110058a002d2802000a0702c0703180904111040f02c0c0d02416180b603545440740c2420465101c1a099030b00017000700b0200c000004100300540c0242100d40c0d404640360300b03510401c210b03c04030342c907607500c510f00500a1002241101145420010004031800314840b4410040c81140c0110382d07642c0e6021a25003000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 455519433 1250 455518183 455518229
    0x706140a0c020901030b0910050f160504182906070803060307050a06050309060601090609170109020a0806010f0806070f0e01091503060501110a050a02060f1903060312091a13 77
    0x20307e004603680310984200c1485004e00d5400c135441103501102984403480481c01c5124588130244030f0700742c00d2034020b15140c2c41d03956000c201245550701c1000e06540c0c0e00c030b00e592180c50103403203540701e0446140a100c04e900d01001404901074108090541000080030610750759080090300d00078500a40b43d80c3d2066613800c000b030400e0300201c4030340c0080c0c0603840001d0795540c440d0023602c0a44156480c2c400e421030402c101c1c8254040c210811035400d650720b4004070050394484041034002c01c2c07888000d000c95814402106080038981e48503148a500420921441a8010344246c00ba9506807410920720442400102c2c0c54491650003841c4200d00c00810140c410360541044d002d41d20281c8401d9082c028035805c00d580c403182200c003e0125000101030a0040c03800c1402400e640b041815503034180b04040c00e035014480219100c02d0082903540c80100108242410020404c00742424510403103440c001342d0705501c400d03180d0305280803803000486c491030a42c01d040b0a00503040d800b5851000d20028449 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 455520683 1250 455519433 455519453
    0x4020303040e10150f030c08040507060309060b0d0f0c0b0702010806120a061a0a0605030c0304140f01150e01060509090612100e1b0d0c2102061603110706140a0c02090103 75
    0x6017000080c2060340103440355000e00f000300c1c011380d40034000b095454a4420100c0c01829600000c0f54000d8942c0e4031024199940d103070220015001c0c005c0949c8008071450030034003102e80c0e54803020b1441d20030700004001d40c0c1c01074032550380140c0c1999240f240500071004c150030308856020080c100d9181804400c001c814907441084110700640302c2c105200d40341c10090f6000d000886618480510820000740040c1410080c0c441418016045407030840507408400e00303440c00010b441d15144010102040a0300e0308184c8a4010302c01810110302e071608034408a281d0b9140100041c0c013503204c40412026411080064016980c1e40400030045811100385080d192014041d1240030301d2176802613403c4528028000c102060b0b40b111002001d64a011140600c40c00c03035881c001d4001c1c43c0b450b000405a110003004000c201540d200500c03296580d8500500030134180c9000740c0a41e0310400003804180d4026055110f01540350301d505440c0c036441241141c80c607240d040001d4006610000000400c424543c13 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 455521933 1250 455520683 455520707
    0x3030207030e030a060b0907050c030304110d080309370b0c1303110a080d0f0305060117010915060905032a0a1805090a1e02120d0e0a0503030304020303040e1015 71
    0x10f203044a030b00c81c4036080710349d40200c2c202c0d0482c9030030800201c3c000075401900c2e5202d040010380126540b80350340e121920b16410413100804603410280d8907801d942c4903200d400000308181240c400c6d582c0310584190700c02a640034402810001c0744004500550650801c0e01c08060042a2070001c0343e4407850184900318006403000c6c01640007900201d15541e01003249050200603950302d00f102941d040702140501000307420181132102c0000440000e8005500d20340c040c010104011803060032045a0030395103811944014108400020180314507500401d100c000204034840140000284a01003081e107240c420850385d0041c140c120010310300c800400300ea1101d4040708800c1000c0c0da01c20207410344030301c10940002e1840201000284280707540ea400030a080340090510082d1092901640c3e141c051b4084100000c100000f00601071880d18180103800303420241c01450540c04d081d80400e86d20301880c0100200003000e00005042d400f098642d000c0101120851039004c046001405042e50740648 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 455523183 1250 455521933 455521939
    0x90c03060812030f0c0702190501020d080f0c0a05090d0b010e011e062a060b151c02030c0c030406050a1d0a0302060a02010b0d05101401080a03030207030e030a060b 72
    0x100c00000c1c55100800e034440d64107401d21101c1d1071507480b082041c42c06180103140300a4110103201380d60241e101c900d40485a550400340040d600350820001901d0003400d0302008040045100403c040241407180841d00001c0791075555441c2d58880206840328080c60440d20b8010700805042818024010715480c12518074449000060f42c031007a0602030350300250820a41c40c050304000700903030b610030203001d01c138880004005c2101d141e440c01d0101442c00baa2405451258685412121914007008600c0c0125540c01981d480c1654030513908402c80601098020096400300008410101c5001182c05440c0c10030181d9035a291103030741c00307062a0040704148002a905109952400907820011003070005c005142150b01c0c0c0c074640c200003247c0e012407000c008554850b68251070fa034407003d204c40040c6202d00c015084401d1003d0f05802101c401c41481129840110010880c0007004194051004e800d85005652620305007000e0354185a100b40752605403141800f02e8050004503408985008011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 455524433 1250 455523183 455523191
    0x90f050303071b110d0317040f170a12110702030601150e060901121d010e0304031101050403021c020103020712080709050103111c0e0303040308090c03120d020304060b040501090c03 80
    0x1a008031481000c2c0c2801130500c020704407280b03024a44401d9110007a446442c1c80120f003140f0516240c1050401c1c0c03421144014014610410812150200b031801064101031030700b0541803000c000c0110012000b190941940c1b05c50f40302c00240380c4011a03440d19000f4080344c3ca0740d40d442c031382c400d13900210000e035000041c4100b23204403240ca4007008603140c0c0741050b5540700c803281400701010001c005143e00400d00c0d0b0100010036460280c00c1c01040c5180002d4005551a5071942c1051403e02481e01001030400c0710810003800140c1d40c09210082501080d950341460380158801078009103e103060107459010b4111107440313001c3c1e0103d40359100d041c80e42c0d20285559507600066046d500410b081442c00c8000f480800d4503031b404200c43c0b0011882140000c03440344405160141540d00995080c0d001540740020401080002c00c6042400713901500207000c02d0108080c8070249008070324400607401d80000208050112641055101d04001001042207580d1a40d019000341030780031010003c00c1c14 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 455525683 1250 455524433 455524457
    0x90a0b07060e0a03171f03120e0a0f05030c09010503150406110d0501051f02030a1803060c02070e13051e0f0706092907080f070c0b0306090a050610050c01090f05030307 74
    0x2918014aa04401406040c104075040d0390b60402148c0c0811111307010415401c00b070b050203507070350b0042d0802040d4500c5034440700d0f8103044c189401e1440711070100b030107004c14000420154070000b0300c00b8151b420b5080c2d281c2040d183e07882e10f0b9002c0c1030002c0440130000700216005104240d56030015049072402c503050b00000184640200401200c0c403207080c09600b00b03111001d010b43c0901c2d1a54100c1d4000c0115121883c0c5075074515044030280110040103034080f01c1d00f071081e0a08114070540190388401160480051980e50959420070f64180342c507000e0076072280e1023007000300300103e5074411036100c01d840c107a5031240300060101d200e40c4101422090b00501c0c10029681e4031091360711644950000616000c4161201050f43e441000204507a00341046a00c0100f0041c0400da40604010140644d81e400d080081100799440a414a0750051070801407005540d5003030646445010755092841e202c80d500c40c5203500510135641c02400614041e10302c0020024040000d510500941c1c9030307c98640e02d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 455526933 1250 455525683 455525701
    0x60b010905040e0606090601050405060318010605060c0d03110412050f0d05120606090613061101060f08210c030c0a1a0702060415110705031e090a0b07060e0a0317 72
    0x800f40b003160015004000480c00380d0500c2940c0d180d0201c1d049c10581e107800ea40741c1c0032501c0d035403040b5030442038280c100c0c410a018003001e00454000300000c075212400c050708881100e4407021851500c000340766641c000e80d2031012450050701d0003090b02c070200864034042c0307081a68890110031074000c001c3c0a00e0441041c8a4060300c19103e845088a1042400c0d0b51003506004407a40150b8405510500034071007040d103c540030000300b014044580e291681e18000b00c21301429039030346400051b0741415144092083c080d00007042d0203212030422621107510208600140f80744608031190340c1038000020070302400ca00000c2d022079251311695003d1015840189411700c0740405070b42e031000507000440403170b020515422528107803c044038400224656000104034207580202412a415000811034207811501c82c004407020180c0500303540c2c645481c040007d20b000180d40144983d0100100d01041840f9856004a50038850304040314012412410050240c61420142100603409240042c415003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 455528183 1250 455526933 455526941
    0xc0a0609210f05190c0920070f02030105010602070f0e010518180106060f1d09190212041a010b0c03270918010b0301060503190302030412060b01090504 67
    0x445024a40480c071064100595100210340c105982c0d00d60b0b04000100420390520159510001c08100703203aa6040d5441e10403d1a079955110b008950301c0c0c00d100c1241c101b10b140c41400070341090049241d9030925803920043c2032103034031006900341d86410008616036400160640607114010390610829642d11110180388500340200c0c0c2d0400386000d4086900c2c003030880c0b06504038808100300300103000c2036001e260131201103512000c005108100409119030f080500c0d02c0004222814060105504d440819000e8101408121501400b5040001c51014580c10741e8103803002d4110b0720005040605228920200e42c2d44142c047c400c0c80c0d4000a81d1320344840482d0281c0301603401960400c60080c0c3c4801060080d2001212049102081110b1350341e18429154413504404070301c146c0e0078902e051901d08485046c12814040d0f858801c00340402d60f000261042d04000c81810b07020380e00084e1400300d086006a078040001404206565010006d49401005160b2421380e030346001280e80b201003005036 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 455529433 1250 455528183 455528189
    0x20706031107110f06040305011406010e010201090308161206090c110610050105070602040512010504051b030a06150e0c040519030b3607090501060504061205090712050c0a0609 78
    0x4100c0b400910b0005091460501e0b480c8031300242a1350400da47e03034881c00d080d681d00c1108035400f24004410005c4075a044507d1300b10b5000284020840c2d1500c1d950007030100038024000d5a004140ca91102c11a548204c50054161034041024090942d07940030340400343c2801940407010842c5c414081801c4c440024265129190440380d022003140b0300401500c50354003200003690700507001c1001060603144c02c2d60703501400c90010000a000d18290078480e04280051088a1144800c0058030b440d41d07800003804c3c0c1000303800c1040007860001c228055410007810f07a000134000c00c010010859480100400745c02100c00c161030101030040402001c074080111800014503d01a4501160000c00300c403000840546441d03100e24098130008810b02010028135801c3e640f41d604c120301c00d000105a90048070f00524040c18030360704040c148040640000b9003800c42c01c14a9940b0b100084c9088000c101007402840660510300894541d07013031050f2640120002640199550b81002810701e100d0b220000403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 455530683 1250 455529433 455529443
    0x609060d090c1a042907030206061503060a0905061207060203040e0f0c04140103092a080303070c0209130b040308090105100803040b0c01021308030403031b05070311120d020706031107 81
    0x6018105081041003011440d480400b180220200150340d5100c03000901e80503022340c004048504c0c004c8100054601d041e00912024001072003400050f481c2c050700301054035110714001c9421b40c0c502001c941c5143c10b8144907461449252000210190040300034402c3c2c8418a2107000c42e0795800b407100a075a0000d40304614418000c200c01c21462146024141d0380802c1490040b966079220341381d80504808444030705468058032103c50095001d0101c14000410074100a142586440746000c0d0a40e0081e150107070141c0110000151380c0c6070313001d121346251523101c0c05000d00340c2400d0a00070200034089485000e55031900001c80c125080c41070715141202c1c8824000e510f0282486001c03000f980040002d01c00640d002c3c40010603089a011100001e061200300442d00e481c44e50134010601c40310b0100d041641d1818040c1c4101040011070840d081e0303900300149240800481d004501229040ca04400c035501808100480b43c40e404100e0300d04581d06070340c040c0310074000c14400c91a144544600244 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 455531933 1250 455530683 455530687
    0xe09060c04050a0612140a0c02071a2b020315090a0b0a05040c051b0307060b01091404090804051903060b0a0503031b01060b040b04030201030c14090d020609060d090c1a 74
    0x20005100e98100458240c55120118013600780301c44408a03103500b1f4458183c0aa15161079441d0540d0400c101e100400419000f00d14918a0392004804d52103000c0d01c0880c011400103120168a10200151484041c4030104540d01d00d007a4a030303000341c0d081c1584414402c0d023580000c140001d64034010340309641c0e03000700502d160701c0c0b4040800001300b104040740810302c88184046500030345202d800450400185025654544580c5054422201c5619426050004056040c04800c4541e00c4030700b98500d00343d4001484242c0c6080074140f40c0500c0c0c3c0260342c80422101006c044580c08551181207a01c0b0f9102400761641120402114001d0380c010a900f44c0d00070b2100040d28a02d5540c031015202040000142e07080e00c4d0034440c95503510681000042c030300d00041c10000c6503070500c00d030714083e041c91402c001000c1036803040250a101d0210040d108918140d1114159640e4a0440c0c0c1c0d40c0030b00030300c035a0350750381c07120340d08006400309902c140c840c2c07588841c0001d2146d03101081040300b80c91224201c1c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 455533183 1250 455531933 455531939
    0xa0810050f0c0405010f270605040e09010501060912020a1a0903010608010c0507020904021c23010902060729010f0302010e1203031f0801060603020c060603070609120f0b010e09060c04050a 83
    0x4502495400801d601190040c1c0680000ca202c7e002070809040f10b03a407501e54880c24001c0f041885c460180000f41c041c0c0c5000010465540d12040300030070780e09000c5e003403002070768280005162181c103904004481e140c224011108198034000802d441d46094000b0710656540b40a201c1c220387d80c10385041c0c0800e90030003090005250405500b41e1241c40107008818280300d02026416544403034104903041d01d03258103008469180b60170444002030001c0000c0c030001026a020400c54004d4510081070640b0390700c000542107510b42034092410500c485502190769541c40c19481c900c0c0f861109a010462000c00a003440c100315016001c4090250021403842d100e100449507c3c3c03070041d07400b41c91401201e81c0440e900000303008d450020b214540d40035858101d000022410813078040d00aa110f980701120030044aa041113900e0200c80317020201c410100c2450614a45da1000e110300201580241400468817409412089000352110f8003100c2d290394503209e035840644154000c4a0713012010a50030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 455534433 1250 455533183 455533187
    0x309050309060702031203010803070302070e0702072c09100f06123c23100203090316050d020106050d110d03030902100305090d030917090a0810050f0c0405010f 71
    0x60128a1014040b40e4640c1b400c1100410720b034200307810003c0d071900300049402c1416410029007010f010140c0b83c803000c03800c201102940d500498840c0e45120030400d80701000300400c003001c1d061461409011507015241418072182c5800002074200c0690b8940501005031911603c200c100745c500880115242541d96117400110918449202d1801130003000b10b01c0c040c0403000c1c000d401c0000c201841311480d401070308d00021a003280c803031034000e03076064550b40398070303c0344002010580140b0b440d800598a464491032941944942c0c00c1095001c501d04204000b00480090401240c842079402040386688450420010b0b200701e4401070200340c0303000c4418400386481c1c2d0300004000c0c1b29041c0029118801da0106550840c84030600e80440d80d03079401c002280c02d003444118482102c40c034040000c507101c0c0d980c0b070b48100d089005078000c02c0804106c0c0a0f032a200d41600c80c01410540e021152140190703401e55000d000100c5900004081600100d42d00070300e0350342620142c82c0140c554541c00c00b007603241 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 455535683 1250 455534433 455534437
    0x903230601031e02031b0f060f0901080403020708030f04150306030c03110a05150306100f050d050c13031b08070635010b0c0c0609010e011103040b120105040c030905030906 76
    0x103c07103400000740e0302c1600590b800c00400ca80c1188000458500e59100740400100f0240305035481c0c0201c4042100700181d802c1c4030200c40700300c90242000107040d00c4608040307240007450303000315a21b40310014182c154030f440a0080c1044444109a03000c0c581d82c40c0100301c05a900c80c0c0f000074001c045004003840007d640038241940c03408081c141e00c1c40340350b44400052581c08a4203558480040010500425050640c9180d4142c6004d00300040c40e00c0f20301e00014005c0c498918a9200070f43e40d4008142100e03e0001111030b40164002e81c4030f14952203040150355807021586001c14950342040c00620003001282c41e500701c1d01c07903886030302038a504800040240c0919080400700e0300c0500701d0031001510b4403000300c0c3c040e25800100720344030b54400c6001e52a0041800121303215076028004544141e81c8108880018102803071704254060216103c40d04d1400356400a82001d0404581c82100e89900c50f07401c0d04840080310300340000c0c218035105404507244080058840d41003000702010904000700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 455536933 1250 455535683 455535713
    0x11040e19061103010b0d14041106480a03050a0e010c0501060b03010807270b061303050109030807081626010806040c1d04170c0a03090323060103 64
    0x25000c070365000c6180c62810164426048107140240115800f0207156947c03080d4014994507a01322082820280c40d43c1110700b002020300d901c12400000c480391001402140381c15690382c0401700303454041031314840250880c0300d1540c10b07000801c20f00d901d6444d00d10000b11104c2003909502c2d858900110810200c40504030342c0b50b0541800000bd907100300044003486410002c0401410342c54507941031088282c2490301a9101d0898808101e50280501030510300d1035000340350340d00300081c40c0b10328003003c20304d0303401108000314114203c2c1e100002440410342241034154465980c080e095507903650107803907508044d01c43c181d0942c3d800e14042d0403030340130b01b07800040c191800000480c5490414450382c00c0c003801760001e0510340c00c0b85040c08200b1903082080c10180104001c543c10741103509800025031540144068880050340c040409100c21007412030300101400c03c2078071100d640b2410094407185841c4012a555180041200199049106800721040150000e421140d196403180420a040c40c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 455538183 1250 455536933 455536943
    0xf050a1106090d0e15090402070623010e1602030a030e071e080106090209180c0708070623060d0f02120601060c0311120a0804260711040e19 62
    0xe2400d004440c0e0030003085102d000508000c0c4100d0020020050406400002083c050000002000718501d4108283c07641d04100341e90060f03c80301141086030103480072a680342900cbc0c01c0211101c00c5d03401c1409020b030584d503030b01c40e8a82031500d5504e40c202184100c20280320050300309011005106109401c4009a8060b1908031800307540c48040150703082d120540c0201c0e000741d40740001c006a0100b03008040c010f01d0654000c42c1801c0304030022601400342014942e42d0f5501850000d4111a50702040d01e5603250002c12032600e918840c40d184000300140300343d42d42c000c4886800c0300d80e1101810619071141001900341301c1c00722450f5590184e005079008080740e000d6207807007440140b040200035190080190343d03950780c10b8400a013000f9004d54141e1101e12450b4021018064012604404803102d030801c515260156958600f082c1d1005806564400034004c00080702080484800c4051312405000344070b90011003c1e0242004115101140040c002d5000541d01035080501158000080350182c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 455539433 1250 455538183 455538197
    0x406020313081308070e0112080c0307063810030b041404030206160f050f180301050103031206080a0f08090604090507021c02151602100213080114070f050a 69
    0xb640e511102d604030080b91034001800600c1000340341c070304010020080c81584151041035041490310729208010010152089100141f58100c00c50300304103c030029500b00381d0030000ca0480da412512210010b229102110b20300c43c10054402c0c0410000b1441110700400301103480204010550160684c2d0101a5002d40d41d031801c00340040742100c26620840c400e40c041e1150f072401881410901c440100b49008201083c2205007100f03400030101c800c903151100084d52102071441184035210f140d00b820980550070708000104142e0030210380070045116020074030403180c84204903a80d450300d0f120041e0010440210000200d52078400034812031a01030011340c9402c0d03c4103c0801030310300c2962010016480940d24a5991150f11403403800004144084c14020b910525500440d9401406158501802a500060650007040030444000c1c10b11800c1d500c480c5003030103000c220761191184000b19400e2080d5035104034484910b0910840b400d4495005003810580119026000449010300780101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 455540683 1250 455539433 455539471
    0xc0910050d0c0e0705130e10051e010905030a0b01051017040f020906040501060f0e0303040f0905150303041a030606120115030b0102010c0f030e03090409050a03091a0304060203 78
    0x106804258520b0040100c10801490002d1560039440c1c0100428108032042c44041004200e14203003800701d030108403c1582d980c0381c0c15079003244c90300507503c21503002900104a0314006624035001e54045004d80750f24000e07503070b5907080c16114040894020001e80c1e00d24014003162400c03a2000d40d082e011403901400142e03000f0f41001224006940a4501100c0d02d403600c000c51400320200d0364460001e8600f0700440d403400d540039280075903143d401010300210101d1b0000940b010402c0d40c00505003c0b0b1180c281544d01c0c506c10303009010545680244442d81500d02d2242d09002080358116007510500c0c5440501c4c440310b0b181c03283c00240429a10130340802000f40d100701424542d501800740d6011848034500f03404406411550703a0107545041da41050b1003001503582060154800c101c0034180403400040c26034003181540b164420080e0b02601e841c0414017442400220141d009101c0e81b101c0901c1525207041c05500c025440081c0c02d180703000c10014000503240e801464000d41c0f001c950f0042911 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 455541933 1250 455540683 455540689
    0x3120a0f0c020609010b0f09070f020f03180109050405070819060b0d0f0b10020c01030903031b08061816030207031b38070c03180f0f06110c091005 65
    0x155840034a00140d000300213008407401c0a02c50140c0e00f6108940192201c050301c030200d003061134018040d40c02c1c0252590501c00950080c0a00505c010a2400350f03a0350f4851143d04460b176042e4228001e002132000d010100b000e0030a0720406010b0101034440c0c52069030780d8404940f00b12107080c4185001c1e501c3c0c070700c005150100d003406000c8035031101c44046541c0540032070081c00ca40104c92000d20808035901c8501d40f1a4000c0341d01c17901080300b0702e40820190b08a040990140040f000c030f0303440000d071003000042c0680d13000d905103015440441d010026500500900418003209507503180b203800c03110b00c4c2c44c0c01e2180240e0040a82a1003401e1a590b012031402100e054502011070544045500403403070048081c80c40e85d070860113144030010b211001141e005074103040c01d00400d01d605110307072907141b40b040c0b50040b98005000408a10800460798441440c1e0703601007442c2c401e10f480104014008901d4601030001c1903400c01070700c0010900110351400b040100c44000d0300240710610f482102003a2a1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 455543183 1250 455541933 455541941
    0xb011d0f0619020312091c03051b040b090906010c031d0d0605100311010302040b120c1207030c0f2a031b20030c090c030406060e040516051203120a0f 66
    0xc0b140c0140d91a100d0481ea590740e0340c3c0008020a070182c0201300c01000300100c114865030f86011764a80060075945103454134850354440310402900c0d00c0040740004070101c1d1034004060100c020799004c01180c90f1007005507600000c0d0200100410f10424003032201d01e030840d00490310031500900d407000486894848104494058544451410741c0250900c1409803010030348100c003100386400c6250038580f01e58074229009800c1c0688454200c0800300c6c00c0da8500c1026242c0218601101c08258104654050014403e4142100102d90346107075500d0818042d0a10002119020031800c4171010081200103128074406800c07810320609020000741c0c140064100303103180e40324080050458038400301071101000701e01226403080d449000d00c01240d840710400755405c10a4844081c2e101d0b00e96291070806000d031500045041074000040105000c1d0001e1494030001861003ca00d61584030002d2024240d03a59001321142c0e40f08014480301c030b4902090b0580d000303079410750009144405010410036a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 455544433 1250 455543183 455543227
    0x50f0a05070e0d110916050927070507031b020607020d0201021011041716171009150b15031303141204150e0a030f020a0c080106090b011d0f06 63
    0x1826413204401e1282400803c03150490a101d03840c1a0700c00c0300650080280c8104800240642c5030080100c51124220503940100c0340315181d900b00318600340d00003c1207070700710103410350000b61a8240c501887c00b003005075900ea1500580420b00c0c0c10f202b80c003030003034038140039000702e0442c40703904030034028514a8850440f0090a040318159181e160410620004070000c03106c1c01c4607004000001850070b8442d00f0903044030f1000d002856640c5a0b9980301c1d0500510b0174001c1045070500d1040010081c12110000002000c07100c05c22558800b6018410045000c0b20380442601c01040480c00011601c01d40303e05084c8680b900003080c0b504428113101c41d4114100c811120241d030401e120030400d142d140b4402c68003844904100201c0304041c1181d0b02c1c1c1c4810400fa00f44400780300402c128070f2080c0510103400c1d4108070b6100c0d07440d98a020850090600d4407c41c09218034002e940801e9621501e000411001807111040480d001c000c03c01590750240752410f903112104002c42c1c10303a1426803400c030140c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 455545683 1250 455544433 455544443
    0x909020f070f03080a0e03210c39010506030d110708030415030509060903041e0509070c1e02010e040e1e0a02030c09040209240409080c010609050f0a05070e0d 70
    0x850411205e80d1086e52200e404e40c01e042d400a00c6940302010448800e030304282d2000d01100210b031601e2a0f820320b40d01c07510420499a0fa03100003104454442445d100c0300d00c1c80410200d0608074001d11045088074400d0300e0056240d08070740800c2c00c1a601c11000c4260f00503245007940c41c40c40c1c7e204072042c41c5900030b90160140300ca0401000405076010b100381c1c1d80c40a1060040d04251802140c2503850344a10b00030301e014801228154070341900040d040d000644000f030031180040c20442d0b00031700b0400240008490b03e06070340e04490208094043d400c0440340d07060f165035029110610811024090300520101c0c40e10a03a081c0c241741040e14542046000201c00103843c41e48514018076003400d01003001e041c01802140140300040c1c42d80d0030301960040c610303005a10420304490311080c1c88030811003215403040c2000e00041c00d01030741c00c1c0109000d0705158004c120407580e40c140349065030000ca031403c0c103960002c00081c150b40800d402c00395001e0030074070745200080303024800152424031007041918 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 455546933 1250 455545683 455545697
    0x50706110d1107050a09090218130b04060216081309062709060c110f0a0f03120b0a08030409180c0e09160e01061205060604210b070302090319030909020f070f03 71
    0x5504041c40b603001d0600d00c0271103140861802c075031198116110848011300d0440c243c00003c1c144a907540c1a294001c0130700c040c6016000550404100c640c02200c8905000202400d000402940074880e40c4112400c6280d0b640540c001c60900d0841c05940540b64400746494404040010314107112b680c083d01041d13110106405a0003203854985007260b40c800007070b5806189002c000c91183c18040b007101c0ea0520300f1003405000818060050090300d4803c5400520b0070401090b860008000b81040d01d040100801c0b4110034032980c00c034001041e9001400604000301c060144d0402400070640c018600e00440e480d80c60b12083d01c0403e041654041e0600160340320040c8000c690041c850000c0c08200402032040d414104e0000b0074a224620a00409000c1b41c58060766074601045d21801c5d203900000c80105900d000480a0040c0d8401160340380320340140b079000c10100306202140c454880d010350360100c2440c14200100004e40c40030380701705031210b41403084900281c29091100036141c4641e540203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 455548183 1250 455546933 455546951
    0x1b1504090615120c05071709090a05090c180402010503101a04050f040b131d0102030408030a0506010507050622050a030c15110d0203151804050706110d1107050a09 72
    0x10200c900302614409407138180000f0821140d842029590826080030194219401d502c003607402921030014050b8100007030b1801c212146c05d055008a2180e0380c1d1400303699006003c10108443d8860800d51703c0a070b001243e02040240d407061002d564010138000d210840a600c03850903011403d810f10702001c10010004041c0700302c3c10a10b4595107011801d841c1070121815500005402400f03444610642550300c1214102c04140b042400100051a20086540781012308100b500c40d8001c0f00c42164407400e06002c140f0300e5219008503070309141c0000103030800f03480d242c0c410001c0e001c04203006a0422001346410020900c144045030403070b813007602c80004140c6545002e4280c07101c40c0600c2201d00c0d04e0100d010300c4024500d011500c240c1030608006961340e0702d02400410307121010f528540c10000c0c14044c00803034500895420f0180e0300807021501c2e0380d9139488085400c10460316040a06400950301510007034050800704403c82c40d000b098a48250300ca4011851070b507840e81c0002d414030b4503001d1407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 455549433 1250 455548183 455548187
    0x606081b130c021f021318140705030a0c171603110a2304090608060106030f02030c160320010f050108120919050d0b06121b1504090615 60
    0x48030301c009441c80c24440340721503090180d101c0d5020b03040003502800c0041e070646050319507411501e4a030440103800c203c841d2101130310101c40040007002c1e00c041c0c0c50301060007000404401c100d80314030510ba40300d03841c6640d03000e1210060604d90f4141c81c10701040c3c038441c61300c0fa640c04046920488007000880300740310a150000f01138551030460104405020031040c00748a61012103464510404e0a0b445403001500ca0a000f2a2240307510200761b45107840b00100300c504004c20901c0c100c5040755424482003450701810b0f000c03840151900d00300c40400304420038140a0010ba02c0c0600e900908124007a41c0c3c0500103250007500038050401c4c565907030703200e1405914140c0304150140268400504120b002604420080d00c101c0e2207583c8181c0040c48841a4684180e58a40c05414050040340502c0082e140c5010f1f803d02c186e4000744288200810000c20000c00508031017800c0386007603000d2100120a06009031070182c1c802c020048103003040b0101d40b2400e5401408000c12910f007205150604074000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 455550683 1250 455549433 455549449
    0x105070602040306060905061305012607080d0c020108090c060912100e01020a021e070e06030f0703030804030f1b08090328050601050603040b06060d02190e010305010807050a030f0606081b 83
    0x340b40e4009c5d142000502107100c200044d8140004802000c010410740d40b4042ea140143c3c55228003020b106821030003200d903511691070250503200b0303200d4a41644980316030b16110b03078410003a1604020305000e55078040c40e100c2d89210b000c4800d5000c0e640803217920310441c0291180000c200301130380e40015445070410f50401400b0085c45008440745004168070310703056190040752103800c240401c0700020900742d81e8144104003544078202c048a101c1b0f92b9074603000d05444001c0303070241d0104025030100c0c410365004042501c00b035015429841d4180300c80740e9460165820000f26650144181c0000a003103040740d84210180d0b41154071045001505843d00c03a01d4090140c0200d0301908081c018840050320304801e103074100e54211806512864030f00e0041c0001d014840c1110080c0102a10252145422401d00c44840c4170a0380c092110381c1e02c81008035526099441056000311610004002041460a901c0c1c0202d110700408681d07155a080b102d4503044206018030000450000fa6482d83c2c60441c40d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 455551933 1250 455550683 455550709
    0x6080601091107020d1e031106010506030105060d0c0323040c140901060c0f0209040605060307091109010509040b031606031505100503040201140d0c02190b06010507060204030606090506 82
    0x10060042d030160100d4000b99001e2464020f0141042c00c8a003410010015011080130660706001e004c81142e0b0b0800030b1141c90340c6550150340d8010301c8000f0400c0e00300041128140c0c0c0014103154a0454030045040051803c0341a20b01010b40d6100f902034030078209483c6011031048030134404d40c103081c681001c1083d0142c0354004641502c88400d400354176280c0d8007a95046803024103000003000000d040c030f1885046c3c5104002d500a80d4a000c02080107039551020b07014500507404c649886441d02903042c01c0303170085444540d0010040c016200c40758072940c0101034205018202040020000d070100f46003500710880010745c0c90a14506010199051242100d140144112504140d10b00804500119010f1080c8400c0240000001b01964019004a01d00c01c0c01c402c95a40d40340300041d0420014000214020018020b82e03030350f09140d000400420100c503401c0803096055071620760040d40c1070390003c04115400340c0c00f44030000101d4501e214080080104220105444c078000013000b00d09013041c3c1c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 455553183 1250 455551933 455551949
    0x10801080c09040f11040f09050114040507091a0616021302120a090f020307030309080706080c090f0a1715060d05100b0a08060c07060c05040e060d0f05060a06080601 73
    0x100e4140001d59440d10b80030b4120fa0000e00e100072001c4541040c90b84200c450200726007050510513140710449082d404144600e006d04000c0208600101c0800040101500e001e13049a000c45003d114003003080d44151414120544c0d000400007010010070880d40100c80c0035401c5a41080705030080d07040002d661986210300d25000c40c80c205045038a152041c0e400340000b40740c16910361b59041000024420012299002402c1329451582d03854010800c83c80b900900740c450080610000700603004070f01181c019000d00e0b80460030171684105200c2d105040400d0795621501a400c000b070700000134008140504a54005010070008898409050365000392003280982603041c1840085580410400311040d42240041000320f18007000030004000c6801c44007185c05044240452404244000d01d1450310030b0009001300c3e108490151014001c0380718140c024201d0200003007040c03620744a030301f10b140d10901030322038100102c1c0c441924141c000c903030049902d0381e120030902810400b00055130040c00d0031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 455554433 1250 455553183 455553193
    0xc021f0e12032a0708191b200f09040503030106020d09050937020d0c1e14040308040e100906050f130207022e0e18040501060e010902040501080108 65
    0xa04880103098545401c50140c90900000343c03074607500f6003412503032440d81082000352a94400c80c41000e000c040e141c0c4104c0410b00404070014940b404d1007014603c0d41d0400800e0000383c1001c002030544245c4220415803000d0400140c045c280d0b01c180600b4002c50080d00219142d60510b1006840d00e00406211000d11100040400995650944d000d9024540c211054440e5140c01034103084440504071105403031181c0382540950365050f5006e4450002d0300300050007266a1864107884c0c00b04040c0c0488210900d4251f180c03842d5000d00900318400d180216524545581d80d20747c8106c6070403680081d05d40d40550000e10041c4042004000c2c0a01000340040040e10300d001c00103101980710030051030003515840c10224080190b541900d0031243c01034400c0404052040031151903540510340d104c200c105420404030064840d05114503a0000a003505000c04c0703400a0000c1b030400000e1003190782c0c0d03480d40790200b0b000381c8244e00b4a0080000d5180981c44a0a0000240900c8016080004240d1007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 455555683 1250 455554433 455554441
    0x3060604090b03100c21050402030a02120312070306051201060b04060f020703050f0a0b1e0705030a0237080c090f01181e0b0304030e040c021f0e1203 66
    0x60204035000c903410080300140089003200441d0804c4495074103d032a242c07904050540058010320340303140e03007584208800b10301c9000c40c1c40314089135001c2c0c50117034159000c11400401400c0003407003c2900f1305c0c500c0460703007022000c14810300e4480c0c080f212000080c2d03c91100304070504020b1002400119081c009010701c0d81070407030303000d42c60040f80315180401100500c0184464020302003a0055508001a40d0608404070304d0660340e6007142c802102c0301042d050010390301032030050900203130303007011200c0d401c00c1c1d00e5501046a954101400023030b030b100e80c200320101e414100c1003007841c0b04c11150718140c1051a40441400510500c9140800901011004200d4cc0c00154801c4030404407003218a0405100c600004860841d0b03901502d50700c0d81900c10010591020340c1c4501c403200141e080b04100056251038203002c4034042500d0080119009034141005031400350402403d0600610460b4503441d0280f1100c651444106d0705070411503a45c4c40365501c5500c0a110304d2038920a042d262a01e5810 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 455556933 1250 455555683 455555689
    0x1104090b0403230706060f1a03040f0c05030303090d11010902090402060f070b01082808030f0a15030b0a0e010501051003090c05040912090501030b0d06020d0f1e110306 74
    0x60000d000030104070349605442c110030488104480c02c3c1d6a03041d0503a1310f50041c0d1405038001d003618099680903401e900707400a0003034000d0a4080d400306a0416148c2035407202c0d0f580800264100700101c5815076413810100706520300700b000d03511480c066402011802001403024101c00740001c080c0040d07174103040103000540c48401f03450f900304c0e5041d00d06035a901e1403411002418010081c0c010301e101a42000080c55140015104161070140d2941d002280305400700917804070343c0210000d041c0e0074144006440c0da400c01401b581c0c003900e420404140300e078441d01500c9140e4100e4104032090014502400152095407165521201d41da41c002c20907941440000b40902d060a6507240030540c440c41c1e100200030184a03090020100580f051000840e9480e003606e45640006034800001c42070440001c1541c8a4040c60907501c0740500400d100100c5502c3e8030010f5400b2103031400020380c54010801c9031106130703c0740200d400500080711032402c10f2030b40000e003641e15501ca1107032003100901c18407100d03035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 455558183 1250 455556933 455556953
    0x406050606130b0708090901081b0a061e020f0f070911040806130c090c260f0c0f040b0a03060807060c050c010e2e180803071e0c0f03110409 62
    0x43c3d078030300030f581c40d001c061824500e640700d50254a0342210000000081c440c0c80020022036180d003501c07051002c4031044c818460302148600c14840040c60110400d866050810044883c0040910686816070501c060542c5400180c1484424641c0807420070070603010b04d03201e8510301c4200003c1c00d520780f034501100706e42d80b07103006000440702c0720b2008028001c00003008c59100c028070740c58406006030b260303000d0080c090f6030241c1860003c440f000743d030a1710080b070b04da00d24a21500300c2c5403103041c468440400d42c1c0c2954100501224020904000c0441c2c078940d0b86001e010404299a808180310b41464029800d0908662050081c002c0160060000510100d1040e61100007071803d880c410422078001910450511000012111655069000340005229013008250551640500780000c3d08402070600380b80e10403807159030000c1c0300b44000a00d90018205803a40254031072201079000d512092030352407540d032000c2c0300360507c00e00c10410880b04041d140a0740b035080b5820040520181c0380c0070323003003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 455559433 1250 455558183 455558189
    0x200406140103111e0a03110306030a110301063b13020d020619020d08011707151106010602010f06141e1c0c080f07080304090b03010b18040605060613 66
    0x1142d221021840030a40344000c4c1d511680100c01440b4130b403d141502103007241e2020300001d0020781000307000c0300082030080031a40641400740041c1403003120741e2911032001441042c00303a415502c6070b600003003515049008554500440d040710504140740c42c41000c449074402c80010400150310704000c1d91107012207108075801e4040c1c2e0180c2d00350200c0d1000981a104020303074400e00b03158012984d01c4c1e541c5e00095105415105443e502c681c0c1e42c030307000c030310310540940710104525500044052060200c0c07140456120350301c50400320b00c41c10305008038500b444002d070003003070051b90b485c80303229050a241d0207174800420060151031914810080410b88901014940200703554000808068680390070303040390700e405000b68036803003c8405890100c00550341c03482004c1c024490040351030040e40010400408a031811b800840c5460305c1d11107060040d0000400c0540e055503560204082038aa25401c8818860301460000c21441d0900d0100e0403604040c4c0b503d0300804091080040c4803200751400750036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 455560683 1250 455559433 455559437
    0x7060c0218070810291303051c090b040f060c020f03060717091915060b070303050124051b070f080d090602010203040201050703030c05070f2004061401 67
    0x1280600115201c80c101c01145520308a4480401c181c4a0388820040e0296040141c082d014590b2045e695170b00001060369030010340c1081900c8001c0940081c010b00c070a03440304e4944507816039030ba01c0e01c601b031110340d406054a052300d0102e80350b00e25a2207070400c0003408211140318203013801c0150800c03d4410501448080c41741e180da081c015550b4020308044c91103002401c4501c5031920500040410081c20503d062010f28140030401010010484119801d0307030a410461a10260b00c1e5400810f10902030665125694480402d01026020086c03108502a4502242a5141480301450070b42c12901a11b40e00e400341d00141005039102d0b040700c0000c1410014100e0032500b0044203420584190f000034151140484009040c040c00705203040015810348840400d59501c2d1343c00ea0903440104c3e00240000d4041142c5c0c000030340280e21011111006140031400e019959903500394902d200d4000b40d40e005101c40960300005080205d07070041c83e0060b682400501d1402c5000030075031044514081c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 455561933 1250 455560683 455560697
    0x2030f03031512010f052508060d02090c07120804020f240f1b0106060f0207060e09070e190e090d02150c160c091107052d0a0311100e0706 61
    0x800031000350017184032a42004001c03c241c0c14828204110003007045d140d603824440c00040c1805090142d1885407060202034007100100034103900b080075225008044c5903c03540700340100b00100d4100c1c08080c42c20700c0581c540056504060040000500ca843c0c1c0452064401189014818078000940810403a42410864407001e410510b61080e02598488136489003500f040086071100540141d0212949a151407802201140c2c0480e2034a00502481780070540b84120f18080e402c01400d010b6011600e8a00300205009040000f03601c01d4092600c801c207030344144000e014101d45070841d0358011182d08014443d00b000500040e4640300c050351070002112018000070342403d030010844440351450190218190514503041802942c01e01840b80c0c228500441901c800c1002412101c119802400600c005200e6032403170503c2108510030b035580b660340c24440d085241401c00043c540d05100b600c68003c1a124041d40c0c0c1d01d0704055044101d0041e060905031510048049044001d803041c51030185 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 455563183 1250 455561933 455561959
    0xf030405040b0d08093a0c090b09160203040312030905062d1008030a120b0103020405060409200415030e0d05070308130b07030507110a03140a0c0512030402030f030315 74
    0xc0c0c3c1c0c07049020121b9000400c00e094144c241030794001d4041e820311541003040400d858250542c01c0710011002c85e90000443d001007220540c0101880086401c5441201d03d419101e40d64000340d40007070001000403d895040c50f004118027440882c0d4450090401102c00281022030b982602e001c0c0e162000d1010303200f2001c24085c0d040f03007814001501c2c00c1ca0842c0d95405c00c0c03010003014451042050032000d0302d0400703600d5480d84030703008840407980010001401c1a003080444001801075543d01200200004a860340340350300c60f400381005194242e0804401e540120006e030076145031085002403078210814145034140c01c2410754114a0b014a00811903030b40e000e030030402000c1c00002c0905508420410080710b5541900414442d16042d40d40c0544043c8400b0180d58034000c690005011450445140302100940c20103044918280c0ca45902a8500d03511140e06141103e068110000f400108000550a042002a821003032a00045155113400183c0320201e07996501c2c440d01c40c0c3c565110340c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 455564433 1250 455563183 455563219
    0x101409130e0105250f080a1a040504081801050301030b0a0b121005061f0804030516061a0306011d131a0f1603060305060a020705030c0f030405040b0d0809 68
    0x180505003041e00800050034204c0300031014112030b940d0007507108400e10024200512035000880f10300c105172104403041c0c8460030b4040203028041000d040000301c0390300b01004c588d128090680100d000d00c6815a6480f01d82c0603205007040007101181c14441c040004000240c10440c040c5e070b203c04403032000103140790240c0000e100e004481c0c40d6622144225501da45100040f81d010034005d200448030f68109110000c503202d00d169690400c480420b26200018020900510043c035402c45200074102c0410b00c035a0f2001c0842e078403006070032491030350102803040d14141003210602401072007482c2607032000340c590000105400188280d40d05141c40318221f040062051040030740320000381081c0d18900d84926007200c980001c861075183c44c1e0805650f08003140c064031421065941102c0600042c1da03412003208003035484403908807528441084220541c0c4d070140010310540c4070344009503560b50328103020001960f5080070358510030409085840b0010ba600001c0340c0d1310350000e40e03101c2d0055200f0210 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 455565683 1250 455564433 455564441
    0x1401020f04060810140d021219060509010c0903150906140a05061305220203031303081b07180b190f050301050f060108070c06090812010510140913 65
    0x15402a1040204002c95141d801600c0c491285580341c070302e048915a1080400c140c0a024540e550700324508001c020054201a03110825040307c6100b200c0d100152041050280382c0000b00c280c401e90b544106000800500b0f00400c881840d8901c0c10200d034604548501e04100d4120001d14000d960b907030305150800103240c0000345101c04403802020603160045a40c4003500c41143c030140319010350803400c14044244d110704c80c000d44440c0f42d100c40b0202c142a08104190701e1110690341440f0510800c0c07281d4403045800805180b052140540300c61100030240640640490b0b030b840c00d40c10030541071101c00640c0b0000d5541c0c2204440c0800c410400c1000300384007140220910800c1440d42c400869101821080308040b0382d070a40007040701da80d8185551604283c241e5400780000c03140008038110f035102e4038100305e400d40210b5000901c800c940c0d03240e90699018003115504070700004010003540c5001d5032070394007048130740c00d10b40f202c03581107090701c0c1306c512610000603ca200e40000c9143c2c41422544 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 455566933 1250 455565683 455565697
    0x30f0703020111160b09121b01060e0a06030c080f0a0303110918011509030c0e0717040506010f08060906160e06220512060c03041a07090f06030b0d140102 68
    0x18040da540d0040020400300c0140d000781c05c3e10442c602c071001c00d003c080c0000740c0b000c0700b42c020301c1e10509180300c41c10820060b0b4020a05040d1541d01d450000c23071240d40c40d04131103010350b5050f100000c1440c03441c5080e450b8150141c1c0281ca4540203600d0540b1101008038100b041c0991620380050341e030180500c820207a000d004045030b000075088450900a0744044a514165107641420761443d201c5410125403081d00c501008041d8503100c4010004010b80b01e1015400404508100700c0991490001d0351202d002143c041c1c501e0303403198004204600520342100c0103000700c0d5000d40307005d24100c88140da803154050140100c400c0070301d19803c002441180d0840030a113005050958072449012a0301182860f00c1e1000145401d00380000707100c0c60801144034800d003008015004d07030741c0c070b042c40740c00c20b03410041c07003071f0741c10b08101e40c00d103100c491041c1c1501d00c140325a4a0351842c3d03504100c1d4140b403256441c0c0201092529140c2074041c695101c604c500c800750390142080c01c000102c0c00160380a8001c1e04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 455568183 1250 455566933 455566961
    0x2060604180b04030f080105030a030c021014070605070f0e030c010804021504141e0112051308210702010c020a02091e01180b030303061302030402180a020a02011d030f07030201 78
    0x2e028402050b9105005041031100f03035480c3c48050362100c0400d40c8a4040340740c0103000c40c1c4904d21400060903c0c10100e254140c041c2000300c0e110340d060041c0a42c5a102c004125101a80e42c001c0260035900f060005807400075510700148080c0b0048046942e40692412517810b01010704005021980d030000f03100e140110100e1270316185c0f907440c04203611180c1c800306841d22624050410342d2100e41d2080c0d94a5200c80c0c16550440401029002e60004246c003404506204045110f000c0101d559000201039800c2601c14140d0010b0015405045554010703142030110b904000e4101d81c0558000780400303100da011114100b650f181c10642d130700c00d65107501c0f4010b98041010300008080a103981030340109080d100e0103001520002007007684034882154190b5020760001c3d001d80001c6440e60185074003034400780038004294202101c40340c84001c12200c240100381c0005564480550a0082c00701c0c0a80d21003103840004409036a2039100e0080c016140400f0f44045103a03010b040c400d4200310f6000d00d00c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 455569433 1250 455568183 455568203
    0x3050d021e0303040203120a1103040f141504231020031306050a020c040504050705011b02150f0d06080a0b01080d120b01020705130209100f0206060418 67
    0x203901c60040c0001603420300140c001030310300894040202d13881154000d01410101c00b01942607400f540010740c4450400c1800001d6401810b802c10081002c1c03d01041001c8089180586c1e021254010501450295458880038030316643c130041600c0a5940c52000c1403040f241109161416a96a80080f680400213044100b51180c1140c0c9c58021000e000201d5902c814a11240e1580c0740310b0144140c40c1e14001c14010012103204402402c8100c1841c4196840070030240000307400d84005580c2030311127400c010b20410407176030010207110441500d901c4210747d0f421550005100c2d181416400002d1110006032a2018000da008554403190100e0382000001d880d481c985030703074101d81c84080f10031304013801c00072030502c1d0001407500005140390b440c07400c05d081c0d4004810240400209160640c81414000300b00c6603950030074160002c5604030300589030450181000007a144c481c4056091100c0024045007290f4041040c03030348603000f03450100780e5000c40301015240103921100600b541ca49 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 455570683 1250 455569433 455569453
    0x10c0309180906021602100503070e0910080d091806080303040209150904060204060f0801050306040f0606080d08090c01090b0301030b04150c0f0201050a0b030a0f05030c0307050d0201050f06090a05100305 90
    0x2481d21041705a5000383c0390301d07004200d070300010703038003031205030f0317200000c41c030207441001040c030301003e50b04e9101010442c25086603544c2c40445242814003014107010a9825000317000811400e00828241c04605505000081c036181d1459200d200250010b40203401040000c4d1083c0e0b0340f02040800c84c1401780c140e00061a1030b05014009401c58020940001d010052909041d8806c40c0b845060b11001406441192a603944072180380e1803220b42110800d46a43c40001c9501c014040c03903c100c4403d8580250512340260310a041180c01c28109041c00140442405141c000304166070659a1081c0e90152603200d6040940d403c00c540b10080c0262402c0560100a090388a4000c3c4442d101ca83c00078401901c400752041305644804c04402d030176a1282001d8004103802e480040f080b1406801a0b038508047d1a4190f030840d40200b4060300d81e58003003442d20702070a80c240325065001e050340e024032440b03080100c000b821031000a032408018988600108220030980c00b1108002c542c05421502c10107c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 455571933 1250 455570683 455570707
    0x307030807031116060b1e01020c0301230a0f02071223030703020f09100801030b0a0b0904062d0b19080331060201090b06010c030918090602 62
    0x4400541240050580c40c0800c802030b000707000b4100808891400b25042020480d60401e1008001074180e4980c2d898084601464541110369105c0820030301d03a16000b01c6141d8000f9291250315a0040c0c040d80c54405080c0000c00f440e014110302848241c0d0301002c507207680161801414424682c40b0340d89100007008802c000f8541360402c89c412007901c0300ca280418403010720035001e415601c804500d03481000010704a81c07203603009186042005403000e0502d200100481e2548080d4080940891078410041c002d200c0383c140c5044d804a8200c000388148030b400300206201400141005002c65103452502440403010414120310310102c04090200000011101c00506051380b8080c7c0600c80303003160340a404040d059420140d40025004501d0321400d054a0b00072504494400650701100c4024456400a0b4900a000030100c81c1c2c0045005216800c0114080e200507040b00d05000705400581c001980054100c4101c2c1c043d001b5510341c40080c0c550711000350540001c0180304506c00510341d01000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 455573183 1250 455571933 455571937
    0x30501050a02040f08011e0b010504030b0f0601021c1e1e0914010c020d0206030411090c0702040c0e0f040c12020f040905010807032a120f0303050705190305090c0a060203 75
    0x21842c601251802c0d98400c170141c229142000c0c00000600c1000c1d99141e207000c681c00104501e04185004c034906035481d120003600100541d17000120b150a2002d0281960381042081c0d0721481e03503420b07a0350242078030102400301c0607074040e141000c08902da2207925130781c02040000000300c104042d20a40404a00f0000d101001070b018165248520700501603c43d40b14107480740245501a200c80c0301c080da182c0802400d41c0004104480706008002202060303261440064040e20000403c0c80c0c660321030b4410841070781c0d0040c261008201d00d02603026456507600215400e4040e041ea400125410b524204a8500c0c0c40f0007007400d0402c2c0006080d004402844004000301e9504641c1004540d803500401600d0b08210320025051000038109200c050425500d8803c207800c580850340070071b903694900110072140b0f08001b44c40c0e8000600f1441d06040e014040e159011456242052a00841c51240d0785490080b40d1140205507961000070300c2200d04021a0300c1d00c440042403c12242d40e1054001e68036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 455574433 1250 455573183 455573189
    0x901111602100201020c0723030a230303040803060d0c080f0d02100b01020c01050a091d04150506010f0507020d05030c030304051603031d0f1e0406080f0712020a030501050a0204 78
    0x10342d0914510440d114810320941d10510540c10281034442e1501c400e202000303041003014a14900460350218150382c08100e0205454460b00009041c09801078840102030465030280189402c10000c02001500f090110b03903000c402210100d1002511307051031000804250440c008038456481c106010300400249000030540341d81c201c0b00e9110455000500795081c2c00042400741e0301404000750150301860140002c0443c03403504020590303544100740c403c800711380e0010980c001000c00b80014400e0a2058404003484603030284010304020340000d107812500014481007210124480341190340f08510414400d40280c202e9031509441080d468680d0300584003140c5070711074004100f00e40c0150414000490780c0545440643c42040c01e094444282c40412140d44004c0150110440c0c2e51a4030800624413240800c0120200450382403000321107403a00442602d40c00303090784084d10103001800302e055650b02000b00b20140d58600c04942c41400383d0700020000d5003000108072905400b64054011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 455575539 1106 455574433 455574439
    0xe070e151f05030411030f100f0213080f0c030f070e0a061e0e091203161e0513060807050714030405030703060f0501090b03070e0901111602 62
    0x1030a8007211450010890100a000900c036100c5444240c054094000b46004140408030035035621050641882036900c8840c60000c108541d0192188a468845660206900c4500044e10341c14032102c00c5415200b40c4080a80501d40010440000000000036180003400c1c40000030700c128000f0245003101d80c4500c0006038201e1840e03100260702e0001d5140020303840c1400d42d20b65031224003a20b03028a9034050360382000c0000f8083e04403500400c0d4030040a00c900c101482c140da160784c43c02424545040182c507a2034141e6000740091504004e030540044c0010746030300003941d00040603074420001600c01d008040000b01c208000044458050088074105030382c480010b8500b040c16002107840726120000c40c420740c2d505004040c058100c0c1d00c0309101441220f0042aa10b02861107030798414104071000c948807070420342c00005100e17040841e9940c2c80032010420351807080740c40e0040380 = true := by decide +kernel

theorem cover : BRFrame.Cov 455395683 455575539 := by
  have h0 := BRFrame.cov_init 455395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 455395683 ≤ n) (h2 : n < 455575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
