-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3078
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:35:29.14635+00:00
-- url     : https://prove2.me/submissions/81b4f9a6-7a63-4c7d-abbb-6d1a43dcd3a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 553417266 ≤ n < 553597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 553418516 1250 553417266 553417289
    0xe010e040c3201021609091a160807091a0c03120a060f060804020303030c0a200105040233090102010207080c0d090e0f0f0703091a060a0f0302011215 66
    0x3250b610b803040b00074008001001030604041004160341c030215a00711355002402c002c41c0d10b6800c1600d403400074001d11100302e914a030358402e42200388841c1600148103480c03000790b10654644840c0e0180c0080c000030311440412101b0750b4103010030320781c240d60420482e0500c880d9540b110b886030341d01490743c804d043c0109540f0b9090710411554a20710342041c000d50391141c86610210b5900d0030b06031202501034400a5060300113000042e1381c0e07c1154040c20700d110203440c00d100c0d08654031091101ca40c1600244604a03516903042009609009140c1064040380c00000d07028102e03140e00701030000c40f2040740c1b009070703040000300351240349e100f50117031403c2c9900460300650320030301c00304820b0b501c0610003680b9001c03c030180c000090401c100282c41e8801c0d0000135290303103203944280d02003011500080c120820303d82c0d40d441c0741d80820300100030010603014000c2c041710142050810031003a1b61207907024010314414071130b0500040c0d9101c0400d50040d140c611001c2180206a8180540c003040f03500b280e1107542 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 553419766 1250 553418516 553418549
    0x20c160e090f0703111216050f06090105030c07051504050d020715050a120f060b0d0c020309010504090c02070b0711330304020f0909150c090a0302060c070b0c01060815010e010e040c 80
    0x2142903000e84c11230303004031608004c144160081c0006402440c400e54085042403000a0440307882c0002030403002d21400c15124000c0d036140410303203015000d80d070589040d40700d42d910341c9403560100003800140070100703400e1401c40380381a0f00404910a030214101000b2000804000c131140fa074001c50b046000048091004a84506c04800b094000714012400b40b403c108004a41500200480c1d40350041a900d8600d80750414120002070401034030080304503c43e5500001f2662000d4000d00000c030300c03914603035003a14040820001d03000405401c0721030b1075134419250154040308040f50100d10300340c03d00c544d8480d80c1700d000113081c260003c01c07500e82141c01c0c9400c000003807601207510743c60340c0745a05c2c80c0c140035100d00000c0c0c1d9050041d45280c6030060001e201c180f016140c004003420764405600100d07008951180141010758104001a0070380d0b0b91907110510482005000311542010b82c03c2013000701c0c0d8904815013035072220601c00d065000347e00002140500a580943c0c2010b00820242d015108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 553421016 1250 553419766 553419793
    0x803030c0a090510050304021e04050c031608010f170c0411091009030f06051f030c0f0b0309031909080d0207240e09070201020c160e090f07031112 65
    0x194801c2440400040350304501088074a040d07850500d141c1d900c0e0303448a0640c0c0d920750a020b51409060f44d04641c10070140e8003180c2d1795540340500f501c01c00f107840c6040d0b2603041c1009000c95050b12032540c0d00a01c1500001440040c09280305c403c100c41319000c085130071454100d40e207420030380a001c250780c0080c1440d40791010001c42000a011510342660400014001d2080444014803540001054040e0801043e801704000b034000c180c11801c204100c00c41c0c00c540c4501808401101d5004030b5000c1c542171001c11000807102a0440101081e801d00b030328524140e01c6285d103e2050640c004680040ca0503003d402034464103100d07000e4260030049074200c10700190003030764441e080e2150743c40e8000340c80c20021041c002d94901e2240328a03180c4440e030491903502c0800010001c0280710004665007400100c0c401c3c00200901541c0c4034403814401c04203410b00503030740c0c00038100501e007402c00e50002040c42008500000d81e0002c40790082c00510f9206041c1d000034160600041c9551000e00c03070311845d901d10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 553422266 1250 553421016 553421041
    0x19030f0e15070e011110200f044202060a0b090609150901081005070f02030702010e01210218040e0d0c0203070e010608160806100503090708010c08190504111306080303 74
    0x2447c2e440c0c00509070400003003a407408148220702d05040359030420b21082011000340499000b61110b003500c1c0d0180d103400711500c07100e18a200d650300c0c2c0b00302e030002c4c205895064040c0980c030707004040d4034000d0202c1007054021800841d8060001d074007039016040041c64102c001c0003134101d02c40e4014401801541e44191099580e444c110018100c9494a80032070085406480c018940044130740245081c502c03150010f580315003000030750a040c000000412501070303034801285080302108140042c0c417281e21880a680786182024454061454981c1d40000410001540c03040d00d01185071000030b522040c40802d0a0040550040000d004e94400118100c1d403c400454440d291006001c60302200b07480b4204c030050000e4400c0b036009480441243c003c80d100314000c41d4000c01d0f2008864000740c0e41c190113400c50380e4014200c00058020400d11004100035030b125000014080700034025400d080d128191030443d44625240308602d61801c42604d840c16411110090090005994403480d158200580 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 553423516 1250 553422266 553422281
    0x40b010305011112072709090302120408030417030909040c0509061906050a03090b130c090603020a050609030c10020c01020706050412021519030f0e15070e011110 72
    0x5980d4200704101c0680c3d4104030580b8441400e01135041c0702c0d501c42000580e0b24902d03601d0400a28000d05140c0b4031000c1412560784001c141070f040000b1003e070203040c003c1c00e00003492802031020a0401c4100600790001050b2020303140001182c0709c11741e20004260389184284184241c104d80f407a0100000c2c03014a802c4d1104980050380e0f039903c0c59440d0700070091928405076404d0001105000b05002d01c510910140c1000240f40c00c0000c0c1651203038440d56443e0000b1280759001140904400c42044a840071810040071903000c10b001c0d460840d03002424280c41030159074000c850110340200030b9941048a0127134804050b21306000180e00400082d1201c2880342c1c95800351041c1200011001d02c01c100300c070100d500610b40e555410840343d007002541414802005412001485082402d540d140c070855010010b039200055194040d20200c07003951046c0000d41c5050f00104481c0090b1800c88a809900034940e01e0500d005441900060f01c4409082004801a205a00c00b09603007402d00d500c29403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 553424766 1250 553423516 553423523
    0xd05010306022107020703031803060e030a020c1516020d080c0f010c020c0109120305071202070503070e01050d060b040f140a050f0402061603020309271005060403021207050306040b0103 82
    0x50300c0b401c4840f0320000e0107a4010b0016071003d0002c002103413203108010201e030740c000d07401c440480d900d440da5016201d0010024810790000119200e0300754040100340051a0240d07421903d0b103851015584850140072400c0e0940903040c1d1103a004c550741d10140d00c0845602892850300c9141000305295140a1020307205050340ca4050100c810500024a1a10545050351855000c40c06e25000109150b01034004505000d000c0c40f0b80b100003051801040f11051043d0300400b000d03490002014075001e22a84280151445000103008903110b000c030410510360480c0300841c0e070704140c00100c0c1c018a600d0805248491511444004041200c42060301510304a00c0c28440c941b0741858090f000c04c1c050300c0083d4000741c100440860f07045e140c0112600c60340280162410710340c01001062411041440344e0a0540e41e41540044034191003504680000042030240034590800e004201d0603c02d501019110300201d48244400e104100700c940d02404c00074040d6882030500d4a0440c1500c0c5080c00101c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 553426016 1250 553424766 553424797
    0xc0305010c091a1606020c010612030807030c050313020109030b0c0702090f0106080402271302031b01021213080d030905060702060403050d0513051f150803120603030d0501030602 79
    0x280340020060000684000e10143c1c9140c031404552840844c40c2c620b0080304c000741c082c8401405007a0030710420f00148040000c80b1040320381450010000300c8000c20100a1600d40510810910342c000c6c00d40741e00015824250103144201d00042c1d070301d80166403004014050311020806120300d14009803605c50310a903400308094841c2001d5400c2408240034082c001036001000030054544662450880c503800310310861640f5003441d1311100c0e01005c0311f064218569881101c011814200035002c100315000d80381000029690000135100c40750001072610700314000c0b410251404400360210b00800c0340000b00c5903403001020011b00904070304a0181e40c240100c1001031400d81c004138090344a940d01d42c0c1c0f01440d01914001120081c8000340100c80d100368030b0010000003034010000440c9103c05116404042d00305840002c080c4c0b20aa0281d000105424400300080390707000040ea00150102090f0381c55607650380c3d0200f40745005441c00e49010a003001d000009001090303005015401c980c4401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 553427266 1250 553426016 553426019
    0x70506100f080c03030a082a03150409050d0e0102010608071707060906081311100c020f040c02060105060304080f1b15240f040c020105150a05010c0303020f070c0305010c09 76
    0x1103030345070300c0c4074040f1036050b810400800ca0301070300c1600119400180702c0e510088210004000000104020510b4001071000009100c19010003080d18040507204950902c6818510b9652a031620510403c040601c042c4c01707010040c84e8000e400000c081c0503142d0441d0000e03a41e8403080b00c2031000c2c0342a4003603680203c0e400030844078469110042514000d8440f030b01c07030340c4903000080680f5075048070655000048044170032403966405907600c10b1000035900d00d082e14a02d40100491681c040280603c260310f0045241100d03900843c1c0241101d00407143e40744c032030340c8034100000c0074802e56074101514200000e08800c1103800c482e01c50000203c11007158203103c1134003034801c00500c0c299444114801440c81203100b2000c155900030780d003000138050741c11200c2020003003001d844a000000c00541d450300108584010380300e501340451441100c500e0030311440e1000103042400b403124060105500040c1c8200e40801c03540880e4039940e07010243c50a419542d0902900038400711080000140c41c2c00390 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 553428516 1250 553427266 553427279
    0xe2d040e03130518220c0306050412170112150f06180522020402090d15020c0f0a1205130e0414010506040902030c040902181510181208070506100f 65
    0x1018491244c26144550301170000c0400c21003c051507508682d40d54000c0004030008500b801000d01840c4646a04d110300c00e5201d0001e08100341c60b9920340c078524241700c010000b42e114031000828068101461140180348401c10304068810400c80e1000c59041c0030300040d1235425608100c1a04c1d03400034041216440c1e80a40e125111000104000300400c80d142c13910141c81c043d13000f40002c1400811082945211380d444402e4070b0300000c22900440d40c04104644000b80c280700c1c2200040c0b1090141030001c8169840340e181c290550319020800c01c01165901107100f2002202c0c3c00f900ea80e0616290318501392500019503900140e604000e5401e2034042a000d05050043c0c25130543e009014010b280700402c1070100510540304242c0e0300c22a00c100e4012100d8a548400d0300a410b00741d081d2034807030050020300121a001102c01010458601a08105044a03041c040c0958045400c10b070243c101314100000d07c0e004100015090f03004000c14008810401007101080300e940c42c804d40300d03066031100c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 553429766 1250 553428516 553428559
    0xc060f010e070f0201020d0e010507091a03010b07020d0f061a010201050403171f0f05040b241c0c020120041805091c080402010e2d040e031305 63
    0x12459800c1070390400821603a9006441620448036507200041c1403120034250032007a105a401c01551303030395490080c0710640364440c1d4020050404190050a140380c49074445038688030500c035101c0502c0300071402c030302103660300030310382d400f66820640d04d8016401c0d50074100c0040102030b003100444244a4522440f550041c0986485142c0540340c1d220b82603140c100181c8140c60040c2020480049900d410b40305801140403003000e8111401c1c0601c916061205002c1143c203280c100c80c0c880c20318100c8000089251001581290758031050003a00c0365540349006048030f40c0d82c44210510360411460200031a415032054031000300145003c2e407a80d40e840c000405070301c01c501640d296035046c16580e5040109540103140c011070000c1c1203880d07040d0a18100d1012081480840c03000941203420301041d5a40f00004000d001d070100c44e00024120440da2000c0e1585540e41021246210912407110541e1035a002180075045142929903a4071035a40c0d00424008500401344904404083c0c141d1b02c411b141e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 553431016 1250 553429766 553429769
    0x120a09140f01030e07080706020a0b0a0213062102160b0709050d23070b120601050f070326010909020a080a0f0219030c03060203180c060f0708040e0702030c060f01 72
    0x14007820344a00c07000c0011806442004841c1400b0701c14172500103440102001858000c1c0819405064070001528140c81c0c0c100000c0c00300c440d41401800703403105030020b402c6a41c00b110705906010955038000d8410704104024440a0300c0d5082c130205000441c01c8a840f24041064070a002d00030150381c481c0710980311403603039026807500501548003140009800702c0e07821042860910080e40307005181c460703030351030002240c000003550301010032089035a090348a10560803da00b42407150a107145008a20401e0080301c43c094100710003003201c0240701015404034a101c808980c0003070510742e166480c940c041c091282080303000300c5045500140f81030000c180d45405c1e55102c012480302e500280c081185208242d8000b601000585100000158415410f04021440750f4009603d925014901c2540e803030115410040b10341291203c003485644003c01c8500100c1404c40303540d01c0f500300e070401d0b6120380100d410105c1c1c4000100b041c092940d0b000800747c04401c003803004541c1241d40320106028152000e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 553432266 1250 553431016 553431019
    0xc0307120908160602091216150e010311090405010603021c06030b13050f030c010f050c0307080a0c14040b030a0612080904051503031305190612051008120a0914 71
    0x1070010f141e010b2480c0c034030140d100b4001c0034090f0a000580d4000b81c80c58607c0c010440c3d10340c2c400c1e0058811403408881e04001041d500c0200d000035040322101400b82426541c409040640c0d6484909840007104251118004040e100300400d41c0c440c2e2000e4001d6125002103181c4c4400024034110303441c030b503000e1a000e0320344c000d0071440203403101e40981c6030700030a481d0f048885018800440e41c07610010000f80c0b1580d40d00d00004212814120141d6007241c1e4050400c0705044020400c100c40a0b0700700b0040c1d900800481342c009004180c050b012608449004961a905807000800050a05c0ac40f8050740c069910a80c0400c09203a4491f681d140c0010b2110b00200700d040b0078400c20320a80307002d0b030090390300507240042034400f00c20240c0084d0030359019280006041580032001c1c0704505201c02103080c4100611541c2c58003c3c14802e020740310342e04000c10300c401c1a0b210300c0020764140b480101d2078001d00520044902054406214841a401058030140002c1c0030072000199141e00c0101b148500c1d00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 553433516 1250 553432266 553432283
    0x5160e061b030f04150801060e0922050106240909020a031e0903020d0f120e07090903050d0c1701030206031003080a02070602100c080c03090f03030c03071209 70
    0x2521062050541080481c50000503200c44000300394030050000708525011060300c1079a540c1090082c5030910b602c01c1541c02000580b90051205642100700c4200304a4111100a503584d100e001c0322505031700310742c2020003922900410400304101500020283e5a00c400400700d039107a801060114028000c8003540041d40030001000318074030907801045807100c1440c0103c3c940b24401c040f006a00010355110044a940d80940401c5c95810f01500300002c030b6070b1030079511444aa05008141c00285d41020010325070300c011442c00403404000160003821a08020b100100e21810058081e0304540e1410300d4681c14203405c60314403845404030358100c146d04041e405440c0d0a640074012507400040c100c2d40038039200f19000c808240c410000e860030703aa556008082160605100900b000d00c50340c180303d2158100300c20384519a0300101c0c450f6000c03c0d0740070201d13201e541c0ca0025500d840404100c0c08102c0c000013044c0609a03e9500042d88a4605d6071100005018480010780807656070769009030030010b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 553434766 1250 553433516 553433537
    0xe0d0314030a0608030f041403010b0f040216060f0207050f03070812090a050f06010518090304030209130f030e090601110d12020c150105012a020105030a022106040516 74
    0x28003900915045001c0b280009881030729281c1107480c69200d0300c000c114111010508010280180d07514004214040d0024480c4110803404203900c16a00c4404604c40c640208050080203a8044040107058001d4802c5c00b0f03210709865810020341c0070000a440d1360098001c10aa0b140300001268076407a0f001400c01e14110b0450b0386001c04900c0130700461050700444041c0c40105100f00141c03086107208901070030955140004000d01e44081e140c000600c03108903010400e2411003c070589003100d03010b0750075103000d5031103000a20342003c841800501d4000d1140b02402459803000342c4484012080c3e80064040e1601e400540d411a00b54040c980c840c3d008107080074465220f002c04074442c0880fa1400360a00805403031032402d2a002e5500c2c0d40040c0c05030b070b00400c0a0b681c0008200208100c0c18100c1003510469911040c8007130b00340f1400381c1404030000100707540d54490f504503034002c01078001540003045000c4181c02e80300d0043e2403141c4100d0618012520f00c92150f02a03c041006640301c45a03582f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 553436016 1250 553434766 553434797
    0x11041703070b040b071b030807020f1f15050603090102041d0606070311030913050919020a120c050d060507030c05030108280501020c030307032307080907150509010e0d03 75
    0x2448005d00e040c0400c410b0002c1a07907201881d001c901809031090719803156600e041d090081c038085004034044216804800b00804e80300352200310f801c1c403855802c004a2007180302c245600d9603090a610403504418000b041080c1040c040d400f81041d5450040c0c600c4440c02600c5581400755030a0300d665501142c100030440000c1d004622221040b102007094a040c1495400010303040b040b90002241c9142e116000c03c80364a000b44080c1302e5103500c41da9180d02c4420150041482000b0600a40011440c1001d0031780600a03104094170003040300a0484070f44890030314021001e86425103c0b0307c0400e0801c68107001907030241040c1c3c0d059a03440c00080110759104149240801c5d00b40f040404881c21850b0b040011910a000400d40d100300300e4019070380c9040812004044900c04141c803003080e01d0703020307014602c0d114404d1405d400c0050f51510b42c0185d2a001d00642c01c24500d68002c02e12060b142083c801440d402c103003c2c1c91071a030300342c1390300c28420842424450040700910008001a80544105111 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 553437266 1250 553436016 553436033
    0x4051c050705060a09170a05010f0c030b0607080f0309070504020a11150103110120010c02010e070f060f030c020c100e0109050d0f0b10080106030302330103061e11041703070b04 78
    0x10101c0f140031140c88103500d441c4d079400c48ac0341070011124079440d84060408190540182e11841c0d0b001c2d50903901c0c0000c20340342d003003080c007441105540d0b481e000000719151107810031041018100040c070031540d40c50070b0607000c0c002c4484c0c000c00102e5230040c1d41d0040352840c00b84090904136a004829034115400010044a0460a40c2c01403050341c00341a4024181042c240705840003101c01e0303000001c420905c00d20b213500c0c0107071300e51000c00390840e021400d01c030040e4824003070303a0183c03010709001c100b0041c0c180059003000002c1c8949600000e120340c100040f180d01c103403880c007150000c3e01c1d5100b00c00c0c0c5813401d00542d1074001002030309039036a158404000410168909600044060101c0882d9031211500c03400d40320036500c181c006911407030341020014407184410700340d10014807444802154070307000d01800c90814803000d1721882c0d4640344c5160340c0f683c21280303414500941c1c004200d001c4100108180c141c10502815035a00303d0100202c144801c00011604282d4020424607081e60329507440358407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 553438516 1250 553437266 553437299
    0xd020d050f040306180201080610020309090402010507151e0b0a1a070503120403020c0a05090403080703061e09060608190213120311150c070f050304051c050705060a09 74
    0x41e5000c1000001240c0d05210340165540b0009010466100c02d00005140c610050101841001411075100c5600c0d00082241c1c10070200340c99031001c0e43e03520b00059a860089100c0644001002140c40e000000346900c4160051080081c98103c0c20b070701007202c41114000e85040d6080445130000340895040081030b1245c8a04590055251017619580c0500703680001d40c414440a00c56000d0008254060018042d81a41590040d19991800000411141004c0e201400303002150010a00c0e4074402d810400203464000b40d04e80d68000503c21054000813140701d040d98440c80d21501103807492080640c3e034004c8000500655004103d1b500c948005d502090a0b04054a106280000c179410108403a1a117580a911801240c05500c00c0690800203050a504401d1a00c0c100300114010242c050b102d00356040b4005900742d00c100c1c13500c18070394415900101e600c030240c1c0010000702c140080880e040b0a02c40c000391004540da590500030640248202c0d40c0c04106c03908030034410040d40000111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 553439766 1250 553438516 553438537
    0xf1608010f0b09150406090e0a1803030e0114070e130e030a0807110114190b100302090301020405150301150302120705070f06050c030603010605010806060d3315020d020d05 76
    0x24130400013804180340592082e07001d1070200f01d2600b01000040207024185074081d0100d4000d02450f000007007401c0542e40600d40040a01d03036105a41c8a50300804d41c1300240f0030702c010a140310b042c1803000002d07048010100d1054030a4050111154103140f42d0300444450f41c450000542c108140c201d4141c95031800100044100300002d81790351820402402960050f910007908a40301e81400d00c0000041c483c9040380f40d41042c14103c0d100d1362a03c60480c425030142c10340c45d0060321450000c0019001e4401d40e4000d55004103a4041b00284203010b070011070480d1304040304080d5216494005900f83d01640c11498100348525000030b40190003600100240e504c200074858064a1507034881c0308550007500c800b2604900817040203c20f050910515010741824244034140d071420b480000c60910580041842d06038441c07810004481620190005000b2018000342010b500b000300c0042080310343c49001c0203c0313107005204402c2c50000c6040d1032141182d0703000e0105100c83c500280c0d400d5100d8050031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 553441016 1250 553439766 553439779
    0xc041d0303040f210f03110a021209180109020438090a0b1303050c0a0f14030307080a0e01020c09010b0d0519020409020c0d05132c0f1608010f0b09 65
    0x4460000c030795044d40d8005107448028a0f152691030040444004814503401228200700c1140d4a1340c00049040103e280102060f075190141004140001a03804080c1b240a00803800450000703040d4003c1c00c1a0b03041007002e8080c1280200844000d0008a1542c02c8191619a403c21341c40310b1100c000c201501c4050400d5811541d00e500300c2c00b0543c8200e48900c211450071030140704201040c40b0311140318104440322650750b41004c42c030855524070b903c02c10720710694100f129800c80e00d017401039580e142d8000300450f440d020194800350105190300325160041c05411034000d41458408090742c141c8450800c00c40c1030121101340700000345005001d248920140744142d0004210b180018006041d4411000d6140c61824881e80d1402807000310650a02c4018014425400480482c0e02e04841006602032000d001c0f0103008101f001c0010208400c481c3c2000c00c004200750211343d401d014082140ba552500c40b142c00d0104c07070703842081c00391a46a019600040086c2c5070040c1c050800400d0060030f5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 553442266 1250 553441016 553441043
    0x30816031e0206150411040909050a050a0305030a0e1203070e010e030f03070201091a160c05040204061d040c021c031d010e1005040c091a0901080c041d0303040f 71
    0x36507500c54040c000710006910442c2000441500c8980c4008003d2042c0e07028049003062590409490069000d9030020319601e400d40020b2040412031200792130707042404e503a0100b0b100d080041c84d50784101c401c4a000c03030a2000c14040e103e80011840001c00c451614117065449022044130712134103c0c03a04c01c1c104820b40320428441e41c6d040c08803000c000d0302c5500441d03a403c074910024008840982c4800d1800703052602075641c2141407011556100940b03c000b0683e0b417020b190041d078050700758101d42c0e0400e1000c900860060307000150040402a1030070b100c240715490710100b100340c41c1148013031001070300580703108106c1d03a040020320718115105040100f90540e044140c40d10610b110744000703107d0303074488400b0380c52040c05009a02041e40e0805080c00300e480c0c907441d81c0c403122800d48101900599030715060285080f4480c030440000c04010f014001650f91100c0c0541d40e0420faa500502c1640307001842c2031070303a1078256040385c4025802c5c00741d0b0440c0e07115154200540360f0382c1002d035041510303c4c28 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 553443516 1250 553442266 553442297
    0x304061a031203060f0d02090f040f060c0503071d030c040f110d0504020f0d081911010c0216060f1e0e03030d0e06010e040305391b01080103081603 65
    0x5841a0480d030a11162a46004030400005000103810a4000e178a126405005a01c401380381c89d070300100e1500c00105544071890400031034941150094200e620f44460b000300c4580c40300c011030045006d940d4200318181c20500034608560400d03021903255100440031040c0f0b04164004484c01488680d0000d0b800c00d0800c084001540070664000e2480d81d0781c01003104615009500c69a100780686a4203c0c40380c0950f290020f51180c07000b1001000000d10321020f1845c403581c110350040030403000a00ca1f803a0071b03802c0a036945030714a112071b940803220400850b60134070800070143d1801065a031a12101d400c005104803000c010103040c070400c807102c1c5807a015030310b040000300759035428403e0000f0100f9011021900300a41a00503003411a120014130000c264032205490b40b510b905403038078034405200700c8940e08010348501a0b4808030601a08014004408144c904210100380c507210740c40d50311072004403030020b8240401010101e0902c00c0d40d032102401000580a2407107170404000f102c10820 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 553444766 1250 553443516 553443523
    0x19050409020406022d030a08131a040b01090515010c0c030b10080c220b031e1506060301030c0e0a110304141c08070c030e0a0f0608100305030304061a03 67
    0x2008040540d10210090512181c00701c0c1150360014840003494179000c580c2e071550f03104d12552880504102c02d20303010032094170345100031400080e4004600c101c6541c50001c0000190802c03a820303913240e5842000000c0f0b0f0308041c09524440c0105074141020340b19100010364a91038415415035000b00415404000910f01a407280e000d100100c480441c280d00e0403000c20302d020340d45a81c0a0048007118042002c001103070156030310100054001080f01030091000c2450080400c0019a9003800c004070300013141030105140900d4440341459000b19603550341417103510b1100b888001c01e112070031482000009041454207402c50001440418150400c0c440b202480e082a40e041d950074000200504c4040401c1000c0c1c4840b90b032511a01c00f01d100380d114003a100c0744000b0107000501203100002c2c01090300c1aa60141d848800511489145031071b0584110000307068000c0c140400c0b2084003040401c6001d02840b002c8a50041c020b61550741e90350b81d20005442c0c030035032170aa44103103039400c0c140554050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 553446016 1250 553444766 553444769
    0x503070b0c07150e10090b03060f0d05100f140105062d070812090a0b0f07030209090901021e0f07060f0b060a1d01030902031b030a020d0f0c06050f190504090204 71
    0x2a03031143e0000309850100450061782d41100018004100c000300003e9030210252944280201c1d0103807144c01164011842c0c50280c8403008255000d500700308840098541d0180740c9000404a04010841c3c0c0080350801c252803e002d482ea208400788200d40e4000f03034050440361451141008904034901d240350704d00d001d0b0003001c000c4507040004540304400b00070342004581c2c0180707030300b0040c402c11050341c480103c0300c01c003d00b04042c08095000080d21030b030b00a80481d00c00380d0001e070840c0407038502400214002d4003e0701078030100784c00c49503590903d912188281c82d4400c510036065850710344190344130b10003090b0103460208610b8880f042607460382e44223005481101d03d60380742e5014508001c00001000e41d9450801410b1604d042100c60241e10005241080340f184003400040400ca0040080d140c00110003000350300809041c0c807030082120065038429141e105a4401c420715890f4003054640d03010308620b040c100101409088052802031303804800c000001d060092500d03403680503800603a40079 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 553447266 1250 553446016 553446059
    0x1205030306030d0518010f05090a0e180c010f080a06031a101e1a1e071e082a032116051c1518150503070b0c07 49
    0xc010020141024450414800503a03d000d80c9040150002040d0b4003811611250400c030301910644855070103001240c681d04002000200b2081c0d98144000907150115003060980d840000200704409002661038100c040c16103039220105200340781200e00300d030018020040c40d42c450100002141c1019200ca0207501e8080c01c0340414980058001c4140c050341c2c2c0100c0ea00e0700909911502d000701c3c62003010540302107050300c480c1c400031513160901d42e00940100d52030010760400c0908510010100a0414034400d0714a003642102c041840348001400002c09854800c040110031111607c54500b6622190300c00c090b801c1c48520304001620719004940c01d021214856400c0d40c1d981c403031511030250700119200864441c1300031490028401d000f03510085800d01c0c0b005d062510100800d4000130184804d40c00340c1c2e02407640d030707614100b480d141101403603c0c90b40c5030818101c4649000040c0700306440014000b170030410b2401c41c081d440350f4482e4604880d18020b04501150543c0d94601050030402c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 553448516 1250 553447266 553447273
    0x60303071428020306100b0d1e0617160e04080c0a21021203040f0b0903040b1c0f020304020a0303110f070306060e0112050706050a030f0221011d0a020307091205 71
    0x2d81c414546040d0000d8903520808500003c1000311166500880d0f42060007010046850080460b00300c141c9c0340082060316090703052000c0480c0f00002d03a840180c40445080844040d52103102c03010b00c206116020741e156580f400800500820180402041c0c0e103410320f0221400303060240c4510300c080103865101960940340001c1c00080d40c1e410081c40c1139100300e800084c0c0c40c0d8101a0791b404901d054600000f085ca060400000f4000a002c0c02074500070500d4001d4250380f030320558840c0109101e40ba95400000386880442c03000000070b0b10917070344100e40c0946400c5525041da11b0903941c3c0f280405010b1a00d10601000c41d442c2401801100300440c402c0c400810b140741003100c2040f194405800209003612440b03e480049800000d80e10111034450801c60ba4503001e51200320094284c00112201c05800010440104600c9030480d80a2003140e40c80116240d0322040150380d00111104030059002803070300866410035050b4011a00002e031418040c0f03c9942d00c16408402144550b02900c0580 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 553449766 1250 553448516 553448593
    0x13050301020d050907080c0609091005060703050a0201060f082a2d0303130608190203070206090105090304060203070b0606041d0f0903040515090d0605190b06030603030714 76
    0x4d0108000d20280010601920420001c800802d070f01d40101c0c115203104540b01b001143e00a00c81041c0c41c4003034400a45419901c1946040181c06d6901c402e40f248015887c04000091a10102007802d0550300104060090041000f601c2d40541004046580540300b07400c0880303085a40383c446407034141005103480d104038080001c80c0c0100d00032200110340250003c001407581d0404640e811b80980d882030508404948400110411510800c04d000c4c2040c0c4c03001090254854002610510680800e002440b00d42d0b40e140c00c1e16200d01543c456070f409a0f0050001400040516403030a0b4495800341c09070303081c01d85e1040981e80c14000071110100f2540c007107060003031140d00304201c9540304001c0e00046143c9494100030464149403a01142c0040d1004a0450035a1381c03007210403008a03800038028026410318030070b141801c00c1508003840a041c50501d42c00c03030034107114050303a100303282c002c024605102841d01c07020301b10000c5541c0c1e610355008003100c009080440a603c02d214814240301c681c0340c0d9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 553451016 1250 553449766 553449781
    0x10807031103090f2a060a020a05011107050606030703032313091e022a0c041a030c1905120a080408070302090108060609160926061b030c13050301020d05 68
    0xa0000b1171928960300c0c00c05007941d000c0094a10781034a4041e5005940c89464038412401d02030b00d0b010080c015401d0114036094a886040078140e42806042a07902d280c88180405544088502c001000300b810924081301da00c8882a082081010120960345480c02c008090041c008854002d52240307690380c82080c00c183c0f82e241c81d9440295903c802149030020f03602000c4050f06041d200c07040d5000d403d010100e2483c000b0301001d030609070003030010710140103450705030000b0100c2c0c4e03020103009100d00c89400c2d9807803810759a140e001d840300b803008080c0181440c0a10580c800095444c02042c45040101000240c0e14001070000b02100b10117408410708600c1008001c22042c0d0005009a010000384030150742c500d05480d07005803035034501900c400303080d840a441d503000b168895002c03482241d004920725000c4e461031040e003001c0401a03410750758034607034042207009804605486140702400003600440c648402421503083c08030008a0080d942c0c00003909a903c8860b84042c003d4841c800e1105c813 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 553452266 1250 553451016 553451023
    0x4020a08045313050d020f040906050105010e040b0901211b050a0f08060f060a0b0a0903140105090d0c1a01060c0c0812070201270b071e0c05010807031103090f 70
    0xd480c150055903e080c0d04001c00040080003400344501c80c02108445e042195600100d00054407030107002401a0300300f42c24140f000f80024461140401c00c00b4a42e81c0f00d0f0b00e450f1040940e1a2401040c1c110f09900b04940d4130003460550100240420381212036602003102041904108034001d80e4003c0c0482c10407044c800306016075800820010884401031000d80404101c1581c011140b00342100e03107545080c00904c95aa2560089107100c200085107421715500003444001c4d43d0090311808650f001283e50300d401c03035204481000c0e00380c00800904600b14030030842c0510b040c3c02243c08550501c0400d40c46090408203034840c00110320041c0c40c0c00d00b008120390410300106500c0024080d1003100d144003625611070254024108140001596610740c0c948403211780d1000001000c1541c1341d00c6810030551580140c400795050a803228a40c5450480c03a84c005080743d6108407502d90309442e10006407008140604036205064a40f44001c04240c82c810103144503011200042190200280c040b030705 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 553453516 1250 553452266 553452413
    0x2070b0412090b0703081306110d14040c03081c020d0c0f030905030306061608030403020106230109090c050904090c17010b060f07031b060b0a0504020a0804 69
    0x2d0121602003000700342e40b6803060302c040c25018104400503079a07840000c100c8040e1860020300151510b4000b240188488010703001c00d020310713241003290656052030f07801c00481c1241d004000c008541003d10010344102c001d08418480c071100350125180310080038080c3d81201d01143d403030f2035031540012102035215841c900c2200303e80c2401c100c240126100c06072240700040c802405144005950f07140443c00c0d81d82c4010306504078003150346174281440c00030b01030699446080f40c1c0322160f02074680003030858554112100c10584a400d100d03443c01101c1d10107050069010780500900b800300381903c0e261030181c0c0c40003c0c031400c1549400d5007000c610710301c84a04c8081440703c1e0703803500f102000d040e00c0c2c500071a4202c40c00050302549070201481c04640c4401a1645110031030103021402c010041d80f50002100340d14210780c00d009036602c440c00c0c170080303001344664400004c004501186c082003074031004000150040840440048514628403543c2c10041214400144041480070100d40b1a6a8180c1e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 553454766 1250 553453516 553453553
    0x20904050f0708010509150405090f06011a03040f06020d020a0e0111070e0411060c0706050910030209030d080a180302060a0b0a030f0b070215090a050705030c0607080f090402070b04 80
    0x41e95420802ca0050000105000b040c0c011501e00700490140340ca2000440f6544100500a000c60b01d003000c0b071141c9950f010300b20048c84d4410000041209aa041c403039040d02004400c1050442da0307581c0b00e80c080049000025108107500304a02d240625150004114052180d2038292405140704001004105081c00501d1560415a018407042e041c40d25020b402c01d4000039159121815000028014820032410030070f5071158240004400f901310007c1d100d2140700302c40750714954001c150250f0581c4030b45960f899040e0803030035113080c0301c501500e0225005022400d000a42030000e500c0015075250b20703501500907a0200c1e0401800c0f41882c052000000c800f43d505035040c52841d40e801c0f1803004d200c5030040880c420040084d00c0c1510030041d83c12089204c00c185207050910040d02512054000820b070b0f0700d802000400704003810001101d0720000005000704d403610010b42c0301c2c2125034000c600074111200d8102706010140d81c40303002a041b6140a04004140341c2030614203015070100b0145c090707 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 553456016 1250 553454766 553454791
    0x602091003050105130b030c09011706090607081f09022a03121618031112060912090d0b0f0f0109090302030703120b090c0310090b03211c02090405 65
    0x510058917144840c00c840308041c00d01299000381c090000c2c0c10802c1b1107142a8109445400018210202c0c1b0110350710103a1500075074000f91500703420161502c00465a681c0130400035000329445d400c401e800810080040a100a0410740f40c1c0400030503a4031107016504e181e158a094032007242200a0300c2e41c0312101c03140081d07180c0ba00307410400c1040700004003d50080c982580b8030b040128098001c2906e01440010124501500c174585510300300411080f10f801484041054480b41030005482401403250100410104a03015008101980114611a0011032180c190800140c1d00f40401d800f900300011050180c4c6011b40d201c00380d01d4416805485000d04102004010a8010086918807901071030005102d001c44040c0802814050003401d40000c041410081003d5903240038501645444800f48516075072401d00c036098072145018154075800864a517006d00d60484c01074092446003002c40c0e030602510b002e440c801c1d0b005540030010402e80000d1000360314076041c403c80e07034000c0c03017140308 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 553457266 1250 553456016 553456019
    0x1050a05010207080a020603070c0b010303020a2109030b0c0409050108010507021203011505090d0203031909060f021213050d060903030605010503150d1412090306150105071113020706020910030501 87
    0x4c10766100010640a0b004103800030200d0341442c407902505445a400131180d440d2540d682c03400035541c140041c803d0300c08800070780c12101d2100e12401c00000e0009203a40300c1c00c045040d92224444024080c00c0000030900400002a01c1c1c00c43d40030b414020040071000055a2a0180c0003038103007110141e4a12025108000600c00c1d10107001900311484403500d012600c4070080300100328103c0701901d000e036140c400452000c654500c08240030986404036542c107000c00e5a90700064990700c59544a0300c000d070300242000010035071420702500b110850060481c07070041d6030b030021841c103807200481540c0490725441030038141501402814010402031804510310b00d0003116542103000e51840d424800e1503004403a8052201c8203a090342e00c012108240c608810451501080301d90000202a00a0203400d00260304021520881801002e043c0c5886103080b9507075807844051825032840e82da01c5110080c0c3c10354a90078910241c8ac002d40f040c0c134010b07515100f1800300007020560241110070142020300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 553458516 1250 553457266 553457279
    0xf151c1508070b0a080c160809010e030601060f0305060414010f330309051c05040f05030109080f071b090e010b0d05030a0e030c130204061101020c0c122401050a05010207 75
    0x803504085550314007905d094844071000340c610300c2501150b806c00440011441c051000351001070459070750036241c880d00180400141501c81009204442c04600c1002150980a000c2c4d040301d41c2c0550002c00010340c1000881c00c140c5036540c280c00c00f0401315074000060107650131042144502000c0a0824005014405010110303ea0340581040405817284d201c40304002080290345043c24048150030301c40791810fa0001d2180e04180720342a0302e581d40560000b05400e06120f4000310a40083e420341c03514104801c010410b61004904071740d15242c1400d804010240b208022003e00900c09010440f16a092440e0382521300046190384100500710700d0500080002086865021090400d04080007003140081d090000c81ea214542001034071095006008040e4000c0068944a07141c4000c02e4101d006035a00700c0c040d5226540381944400055400d03071600031140000c0604940c02c55504149805a010625a408594010302c0e019080107005503d004a0a08007510b000e1009000c1c2c0ca2800c0c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 553459766 1250 553458516 553458539
    0x909030c0a030e060d0501080d03140f071103040b0c061009181b0e040f06060602120301030b0402060f07050a0b09030c0615030703050a030c060b010503060f151c150807 74
    0x41c00141070103411000000325440f0003080e10181110280c0410066a5458066840304004003504000903d0308a03030150a01c90b108515001d1405585804d5107940c6450064a801403000400029848140030010f6004000383c02032100c54030031800341c51142040c4038043c02c4070103143c114120403414415540d0000d2481d4400805141e00300c0d10710b4035241c004509078110340005030422800c0548480c02c000c00d000450386401080d038416a81004a0755488030308a81343c8426002c92003440c2c40800040001c1790381982030a0b081070000b88514644003012814200c2640700070411221500211861424060081496640050010040c1d8904032500581e01c6d10b072100103041c410008400d0300740d07152f03d417000c100d52005190b000f81140d03110780990501914060303c03581c00300c076454123100c082181940b050040e41d00941e40a041a0a6850302c003080141d4190f6004a4041110b020f01411825107071081401003411001d200000342c401e1880c4841111070596008610300f6480f22408100c20030004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 553461016 1250 553459766 553459783
    0xf181c080a0f0318081209061003150b0a2301050903120706110f1e040303091401141b0105010806060108040b0403110d0518040911010f090b180909030c 67
    0x1403a00010810a0b03a6040e002000384515800328204000101303020040c4000041c201454019502c000c642d41d4040f44541d035620031240c1c2c5881510b9004204005030785011b0100c0c80d01211a000b05150201001143c055819644180c400c11952030030100001c414641c040d15505084c6882441e105201020075515060082400d41e0660002004014020180d01c17089a04920b5602c01c0e55501d000038906100d41c01040c3c1d0203100c3d01404105500502107003048a0499501d52035105a080c5003035900d40545055154150600c44450410201040003100400400a05800101c410441d40700e48600b10381050f00f1420280d131102d001c0c03050707236030701300d004076a12075480615410300356120f10307080300c00000340b0320b600c8164032514a0411050303802c035001e0500341c7d80000c100709000c01c2280c10802902c07403c01c400303407500c8010081c0320429480380010717001c55090f90504400c17403669421321a81903401100103440003a80e15955620354032f440c4082030b400a901e10021801c0c00d0500d0560350b10f0310860b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 553462266 1250 553461016 553461037
    0xc0d0f0e150429030a05040b13110405090312070201060807052b23010c2a0303020a09051e0102060601080f011413050411120a0c090203060301020f181c08 68
    0x4402d080d44200d4841c1542c0c1c045012055042a113a091610340c001c05400296421101400c041d400140f40d480680b80c80010b050b00011110141601c10051100401000d40113010a000400c144400c0001070940c50f400707543ea6600000b5942e1a04840700e0030316455801c0340384646440c038886003c030552000c0e610004292031403480901c0e44c440c40c1c02094849030382c000281d095648587d00c1502401984203226000c40c43d12002403402d0210390354038014484c0302020b010094941c3c50300000c02e1080d8042d100390107060902040f05629900054806001d2100494091a042c0300d140c903156410b1048541218081c24188164100300c08a1a1104d0050003410f6034507480b03c3c2541c005940e1980004071524042904002605140c140300d6160801900200d0240c28581102d5081e400d001034400719451b008074030130308031906112016000e0740c00540202d515640070f00a20b01103003c0d400007081041102c09126025044c46030500c005403005688000c0904c040030b210788013091012048900000e117 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 553463516 1250 553462266 553462289
    0x7081b0102030405270411031005061c14031201031a07050708070203070306050a0911010f0f03180b0c18010c1509060f020301080307020315061c05030c0d0f0e1504 72
    0x10045020020220040295078170001e06000d010a002da0550400300d00e00040d01590080314002d0a04815a0000d5651a03004001d02008140b002521540703401800d1140981610300304140c7d0240b45180c0054003e881c101202e540100100030b0344081143c1d00841c005400b9101d480c03c094042c00a00481130081e0a0030000a01a01159028498a00a5544040d0400850404058080007410805012100700302c00205400030740d070041030303110311900d80c40d501c12951840c0007404601600441906400e40550b400d4180e0020f40d5605000b4413070219207440d59103802000d82c1010661000a2009040c403501904203400305040111195422007401d0000c0341c0d1421074074000008002059680c44c0c2144040008640d00d10044000c040c013030f0013181114031000d60200c4420b0300e004107840d940c5d84445803224030400d00030f40240056900740200d00b542c0c1090f10406155040451120f0701c500005d429010060540b5082448400c0c03010090700d06505070024101586250700c158040c0c08030300d10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 553464766 1250 553463516 553463539
    0xc09040212120f071104140c0a03060e090d080709030203030f0a05070f080c010b041e0e160603060f0803070530070f0606082410051207081b0102030405 67
    0x20720401a040007140c000099070303500c201d10360311006240c20810f01215003c085100054103440c05005141d011031880e0755041da0703a1185507241040b83e010350304c1042410344980300003a0107200000450320034607208015000d06000c0e03600042001c0c02c0204454207001402606201685000098500092000107259130700c01071340c40d09441501610100a01110344800060100103103440030f0068006560000e101c0300c2c400340e01300070668070280c5c1d02d0001c800034001c05400000e050f800c11440700741030506403095031680c44150103c00400c0e40002010030f0300c44100300012804002c42000030714032070010b5418800d0301d56406442e024140d1006c2e1310400741d8030900000c40120035440c40000000c4224a60300e00680c0b410030050381402c030702039807494544000014004000700b0560114019aa03105224100115504034003503009440030009010a076030208298803203d41256000a070140205410303031800d44070610b00705503411000406061100748083d940d800000795004d4800841d482c0d0200c1c2d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 553466016 1250 553464766 553464799
    0x61506110d0f09050607140f120906070602040f0e04020901140f040e070b04030501050f0c04030b010e0411040e03030402041a0a03030e030a2f09040c09150807180b030c090402 77
    0x43d50042940000c000403100c00700004840400114208102030f9824420051005500e9103284110704d00c07081c1007040507039000d00d0300100801c007880c4150303c010704154440c0203036040b054881c1c00c840c0406906000340310952070088201e9006021795904580a04848004070340820000b01c1000d00854a07014907050f641d074240403603005401c41c030301c40b9922a030307803801d103d40640317015107200310b08120001c04103064809200072181665000032007000d03180d180451034406980c008000f50398118103081030100603aa1800f07400c051044200c025500da0030107004000403205454100c194269a980d04400c854449801c40f00480780c050030030309515401c03040400d0414180700c078001c060900082c07030342c040c0c00192002c8400c00b04a02c6041007a240702007050003000c13036040d540541040c0b0062001c0040c02d040ba0003110044442c0c0f09000e0000b50740d402e090b407401e041a00251240c0c0b0810a0003251100c4501c2040500481140281484212100820342c1d000000e040640248510412403684 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 553467266 1250 553466016 553466027
    0x50f030319090f0615030311060f01180f021303060f091101050a03090f1a0f0c0d0c0e030d02030301140301051909020d0f08040e09032a0c0904061506110d0f 69
    0x10f50340000f01400301d078081703800044803141c55010071401701d02a481c400007000d1000866610034140b4030340703a030990390070034402c076800100d0318150741940b40d261068042c01100c1030014102c019010302c0c244403660f0a41ca00030013612110110840805e00d420414400b1a02e2150070320b828440c282420380d5618910702045001e81910342c400740c000441841c15404000d16810740750382441c0030a500410f142c4070120284012a01540c81c20010101801800070300c241c0c079071000c540c02e00607042c000111250341c0003207820b28a00b002c406000d40c0000c001084060a070901c1d44500034000c900030451454080700c0340203003010f24104656020794075141c2078210341b240c501c244a100c1e004404506001514a014882a400340c0208040c0c0d010f141e0103c1c4118000005459a02c0780040d110000c8071580070340000c0f408112480d82c07007540314000c81e480389030300c820150074003032802941c2c041034040c2a00d00035000758440740c0c07108040000401d0050004100858202e0005c0e11901e04240110501c0204581 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 553468516 1250 553467266 553467293
    0xc0a0201031a040920060f0403060b13050907062303010b250b0114100c03080603070b0406030911120a0308060307050402030f07031d070501180f060c050f03031909 72
    0x100180340c181c0c03840900c81740541c08a50414030829086200c100c1c14103015090084010401c04141c00740700c00e01c0010348a4000d20003400c405440e42003000380c0c0306c0104043e100d055a0a203080e401165091141035804401c1000c0040c80c0219842c40203898440000140700c1403046039204000811860280b40d06490040c58004608403074410900f0b960401401c7d080d001c0c850f80200c4042900443c80300c2c1014911000050010303244c0d001c0351078032034030182e0712120024800ea03414080d07454081b80040c482000350002c0e110a64001031508402d1a04c03090701900d02402520410318081e91482d480c1d00050a83d880c80c2d41403501000700d03118070000c645003840c81d401c0103512a001008100c0440ca4144425104040d569010301440015a990f82c1d04031800407800126504150230611155000e0b0030342115805e072110b030f008001555502c2c6580307040301360341100d400200700e210300c4410320508000300d081c6480b04201461a5003050f00d80040900102d0494004054580c0f220005020b064040401d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 553469766 1250 553468516 553468519
    0x1050a060810270c08060d060209191d010503030304120c030e04050705030609130302100b06040e0117120a0e010e04020706060b27091f12030302130504020c0a0201031a 74
    0x40c02c1c43e02c00458240d41030a4106031034107034500400890f101d4442e41ca0140101005444d40c0404d1f0341940303501019501000c040ea81150038440040fa0320741c0f80c098000d0042c601d1a507460600d5502da0000310000d072040c5d0240748254000d0040c4804504401300ca1140240d6504114291000c1403a0a1350300c0c500d100c240d1a4050302e440204104690000002c40c42a9000c41c2e1285041e030b18a4140382c42001030190107001640021555a160100b503444004500070051a003420256646908128540240c00c8100000c002016001c0d0607442000a0345110744101c0440707080c0451404000d2121a0b014003690410150311a4994681c035541c0c1114503803a0090000d06c0761a40b03410781d000c1c0e50b9011291107080d9032004900b00d10010710ba490700d400646001402d0341030b2070b161503022610041c6422030300c0004082c02c0c03500040500502000100a170300c01e44026803220314003901110b180c0101e03400240568010090759006802c0854241700513075090a001400350200c4c0340b04c2505032180c00c1c055 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 553471016 1250 553469766 553469789
    0xc0b0708094b10020a0c0b0a1a01020607080c0a030f0e060117070803071502040503060109090209100311010f02010b0a270207020616060b130902010801080601050a060810 75
    0x2011003240742c0d0401c000ca441001c2c1c0034400c241400e1680d01c2036100742c01d0b030029180c00030340851420344916002400d9012071441e260400d9030b06a12140c0e10b2900540c1c24401003039036200e414100e0f41e80003100f10001f28090014020301d2a000c41c02506010300201400150b81000540e800010300076071061284003070900e4204030f034203698501340b651000c00313000d1014440003552542e403954074001822002e8820300006103041c00d100e40d8a200c180c0b00708a08840000383c0070311000c226501e042011034020311218201040200381c030700500c04100d401801c000601d0500240520104000481a0450305c5003841e00c00c84580f8410000c034014100c5009aa5121340769403000502c4403044c103000b0590361070b40c3c046002010940d14111049204901000390000800c1c0a0b488200d0105800310a03c0c5015a0300412214202c40001c0d41441f0310034088022182e851000c0c0c0155640645514050641c03140140015410003002846560301485200100400c0d00001209086005a59030045c000000d69 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 553472266 1250 553471016 553471063
    0x90405391603020d09051e09040c050d050d0e091e090a061107060509030408061f0905010603140609010b030613061a030f070c0c0308030c070209041209060c0b070809 73
    0x3034603100600c1303078440042c02840021560f482d0002100f0f040d02501202c0d02c40301b1400006004c2d10000013002030300c01d4540c1c1c0b840001d49031202444046e0300ca12400181c503c1510005014100203488822039000d4403030003080240f40e121014400e030012100f00134100050352050002403034803000c0e1600600072400c1c100032110515583d8080d01402e132290400340b08a5a600e01415038900507489212000d40c08000858100600d1010783d6030303c030103101c0c01111011b489444520640c1c4080e844040040d540c4e4141d5005000701d45082c64000c2c000302d82c1d464885d454801c3c003800740e02010b4101c40c402c01c20003201c1d0341100d202c0c2e80410001c1a081548072104212000c031403203640c10480b00b030710114401600240e080c82c41401060300f107651001040d9405415615020700c0340d00000e04407000c08000f04285070141e03035507922003032049114a20074100c10340b1103000104003403c0b0f540040300340031500074604d00045d0051440360b400303200c0c0d02c0d1030101940c541030060710b403484031584140f80d1083e500d02d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 553473516 1250 553472266 553472273
    0x9060619020c13050f01060c020d17071104360f050a0b06030a0b040f03090e0a0911010e0d02040902040b060c06010f0506040501020a03030509100e01020904053916 72
    0x40c48000c1550844080e40d490071500d0184080d0b034405c913542e1240e04c00442c018486240a0310740465014000740000440c0301003903560703003140400100b40300440500441c48004010030f030159140354500035101403180c9001c040c29042c100100303141e4940900040c0740030211a002190600002c1e40c1c05c47c132900b10310151418100d4803071a800e001901d040112200240c100e0400141d4001500ea2140f0840c04a0307803961116000e64102d40011010050302a9000800c50456003881e401007612080019041c24985040210742c1d0301200c035241406542c90724200e180da581002c0e52000ca8058a01003940419440040c00404203030902d40e50201d07000c901d29800d80e41c00078070b0f41e06a922110000d5082900c4008200050040e4171450380140d02810013100068482c1d0015a00101c28000716190741c40034001072420f5810030f03031501702180e501065501c0149002d00400360071900c0142d4244115011032120308940c1d00d801c5080c4008910a110b8183d070f07008201c115004034140c00030504c8001c10600c3c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 553474766 1250 553473516 553473523
    0xd051005151e130c0804150902090c030601090905010b0915040902220e0c0d0911090903120604020309030717040b1201091d03030624030901020a020607020a02030c0906061902 77
    0x1407058003c4540c4a00c580e950302c082d00c9802c0e84000c1c251102c5107607946582c0c8100c200c0611480480c14161992000001a00c40f00300315400743c0c8600e01e200d80c80e03181182c001000201c04d60b001d03542641c1480d004018071590107048814580003611703260311608003045860001d00c581d03482072160340c0c030006441c0c500d8540492200900342c41d031241900c40d90b83c3d8030710408080b101a82d83e04042d100804c000210203049a0028416610a4070309070018240c0d4030000f41400b000b19440311403a040000c1044141d111100c80740d0740300d03200311011030031800e0104070303607540f40110400100300c1c0b14140c0c94100f0314039150040d1002407011240c00c0d607480e2804021144040420b10a58184c01c0c1040d00121350216034010454407013510318002e500f19a07408040000340200781c0c01510321501801d080c030540541c8800214890f60070003002590300c80c0001c0c0001d00c1c000d8010440c10442d000810f1030001070390301041d250b5203084111142825a240c1400180c4540b244204600c03207154070701616480c0315000f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 553476016 1250 553474766 553474819
    0xb0c0d1104080106051c0b132103020306030d02061303110f0109030e011e080c0d020f1b1c080106081803070302060702240103140c0a030501060806060d05100515 71
    0x207840201307a22075003940c52002101c0750340340242a42c081070000703032304034842e2501c0341e0410740030f4510255513070092002d10241d411002c880c100003e400108109890404000c8030f10541c1240c4024501c500c0c1121034500851080341000b0200054080701d07516242c1d04000c00e603850348100c0000c0222420511340501510600440c09001c1040454620126815601440003180c12901c070101c40c0d83d00d00e070000d0001c6e403200751072181c115401e201c54400c04441d04040d0228280e2000c0a0015503c0c0721019441c0080f610200740c1c403807403280082207540390712a98407411a125424000c030562550040e031035402c0000144007007a44400f20301d1100341540003924078060415902990f0105800603020100000e02d42c1c922150a080b01e80100001415039162803100740000c0107640e00722202078000341d0814a1a0b0050310160344801e000c0c00a203400780402c981001088a4a00c0c00e000035a46054131804d003140302c40295540c80780010550042c2d60000403440100038598030302620000b08104e840c80d4030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 553477266 1250 553476016 553476019
    0x5060c07380f010b1806220305100605031b0123220506070b040c0509040b01060f08070f2d18050a05150a090e07090914040b0c0d110408010605 63
    0x8200820602c44403031061905840d003000c1c58500d403034010000540501c40c0d81707884a0304001d0400c128406240422890f00c2e01c0c12030b83c01e0318500c0501c0c5040c0649032103440c480c2c4001503803030304008020036940050700d180212035042c4150025201200181c440c80707140c3e20510752860050f01c1007042134a0040042580010381e04080c502000183d01038203030f505090243c5038110400b0071050700840e01d00100c5660082c46a52001c03d1180c40350082007680c80c003654115440b540010050003151340141c01c03500d00c05114648500e061403e0b20005208082c525801414490740000e2a44803d0701040480030a00c440d5010002e182c00c02a4010318092403810319440c0890145000315403450298440001c4900c0100802e02e04c4000b04070708580c2c1da00a411003420b002102000280100c00c100e9114800d40154940605552804500600366581c004030003141d4040901000002000e4144041d04004007441c225100c040340440e400c014100c0c200e080e045c0010120f00090040c0054000c5400e8510 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 553478516 1250 553477266 553477373
    0x11070302100e0907090501020304060c110303070c080f03030705090f010309020306250e09040813031b060f0503040203060708070c0218070e0907020c041e020706052205060c07 77
    0x12004c008699494a80c011680140c0080204005a503c130300042154240250074000c081c00601e80041d10b10742c440e46040b540e0001c200820014250184000390b074030488000a18510b14180c030340100b185c401d050801d4032070350340103038403507803070b034070a500800d100c1b41c2c003030304941d0301c0d0800e42100201d030700601040d803441c1c540000e044400c241c45072a604d4090080a48144034684895407a8000760b04402c000d01c00c091080100007000c10b101c2c0710b01c03404950030780029040d00c0f401d1a100070981040344840c40180032082080c4001604e000030066800002842c0001454440100c201c42d284009100a0360050321091105400e58200c1806400350800382c4900e2120b5a000007400311419003242c580000d600410710005070350900e6040280d1721402c541401a50001d101103520490308260310603116a81d03518100710f415803400103401c181401c10009022580c4a50351500c0d501d4500030192012540d01003400b1040000f01c07a807a1111042d00c003901695050301440d80c0c0d03104511029030195000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 553479766 1250 553478516 553478521
    0x414060d0e16210201021504020d0c0e0103062d0c140c010501140306090d030c18061e090f061b02040e100c0c030905060a0c200f0307050604030311070302100e09 71
    0x2440f000c081c034046a06030007405041d01c405690104c0301100810582c0c101e98442ca110000440881028024064041c1401c00e00d5042d400c1601c11101100340f2005004041c0d10300085c01030094040c0e600c0300b620b80c44003084940e82c03180210350186e4032417032203000c502c0082150a00c110040d04107038188c1e10a513400c841201c0b44403082645da1107098803000d002d42c1246401c054103a1198000e0008081503060800141d109130206030307010f921a80c003800000340b1007a003045044039000c09035200324005140c0007401ca03040c0004162950300714420501480b0080d01e18034015044440c1250005800030001c01400d4820050b10b9114040d040c0e01140080c9030034030384441e941c0140b0001c501c55405540c2d1b15020380c2000244078080d8015000c40040c000082c0200f00014000800c01150030300c500e200030a445c3c500014018000d0401003164401c2d00425401e10031600c40b20705a40c00c40c0d07050700d0441070002c20460703014149169a00040c0d00302955903504540c05800440220240300c09451420a95 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 553481016 1250 553479766 553479809
    0xb0d0606030b030a0b040210051e0a0813030f030b040e01020c0d17010b040303080403020a020d05010c0f0503160c140d090e09010506310614040e030414060d0e16 71
    0x4c1c2d13400d0702d00500160125000c00c0150504100308504030b4054108585010b001001c0440e0b00303254460b50002032040018121030a50b405030895410548d450f14004014040e42d40c050310310340c80407401e44101543d543c89003205940c1d075082a2285440f4000855840b660014072030b0b04c4840c03940800300810340240c43c01c51030b24142044141200c128050641c1000d04590701202c40c504003800542c110310550818901594030183c91007102c1d485503000061030340101170060001d800b40c0382c1180c02d001b4240104540f04900c50019000c0801a1605550b998190700c1d12420b0100d4940100403188507401403d58441e03084807030b00099130900034000c00341c1e07960904ca030303400c1c0e03002103814981002c141a5001112a8000401d9400d0100d6035440e051507041c00003a002180c020760b1229541d04188555000c05083c14400c1c0008000b101c4051403410f414024540518201103100a01031000001c406903803e1090740504100160b80040c2c80d455080325042440403040340c0039841c44600b43c1940c0417100c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 553482266 1250 553481016 553481023
    0x180405031201050a060f03050a0f0203190c0302090913030203071b050108010918150605131d0c0102250b0c0c030c04021801050d0b0904050a11010804081b070b0d0606030b03 76
    0x844641b9603440e04050715150084020300b5018082d540310903201d441d02c2c0e4078007c060000e51312504000e200f1440d041c0c1b6100340c00c01514107100505060501c100b20280c00c0c0d866040d404c40d800103504070200101d0242d440c080b4034520681d0400b8042c45140841d81819002d1013001c00d0888030240d94810b00b1f82d89505c084801c843d00900c440038400c501c032406800081000d4910a0586080900000c1d403d545502003804900c01503803894a480c2d5038408400f0b200310718000002d10400f42002056000e00d0388001075521743d203210748400000f41c0040003481c0c0708030040720362000e8840803c1480e01d82020459541da601c00c0781f079695100703000e880702c0401ca41c10103109403004a800f80302040c000c2d103c03050043d1490360210300d042040c5503e600548400f515041c16140c000ca100300010002d204041c00e1425240f203205200904000b0131500340b00110f42e440050f100c0e0014021410f44419801384032185c03429106621070008140b010412103100c140e95841030b000c85040c5d84003881818030440030540c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 553483516 1250 553482266 553482269
    0x20a090b070f021023090604031112030f09090f090a1e020307120201080a1a0409050304080102070503090112021c0c1e11010e060126030f070813090b090411180405031201050a 77
    0x30012010f1000300081120045250002c200240bc641e0480c05200780990455000829468404a001503101064103000101650000c81900034400c1800c08014468841c0901c4202031700c00001180c0e84400a44654510b42d01c0f954020300303c0e00b07055540d14117541c01d041c00d0704041e0f0120700840d0000760240c1d160300071420800e56200913407409100c0042040f00030440520700380c9851000344804540070109100405000e8082c0c0019500d591410000400400c154084070081900600c03003003d4844040b50781e00204021101c01140b40050418115403190704452a0562803046420007a007050304000c02c04417011440009011222070524000d50381c00c800c0c17160662200480c15005194400b8098540b00d829002054034540362a0050320740c030a42280d07000761000742c00020400c01e0310002c5500c84000304400c2e081404264440000034140142c005c2000e003015001030f01d1016542e031004286640c504540448413524101070901a5a80d008a20308410803a107000000c185444c1c0001d0000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 553484766 1250 553483516 553483519
    0xc031403030f1602120c060109150b030a1a130606030b040911090c0739030f14010b060a200f0a20100c020301050a020a090b070f02102309 61
    0x10a0312107840843c0d90502c001807800c01c6010742658891005035042c01000d2101440300105419410000840219801030044c041480d9103441c003080520b0030a02a29840380b1002c000040c0414401c04c0758101c290501c41041d40300c1e0010545228458903980400141c801e04c0d03404100c1c080489090000301c1e50081000351210b0041c52181005103003119016a1100040310224184011940d0b400c650030324100960020074484000c40f10b4150400954000e40382c43d1800510609103143c9894007449180c1801520300200e00000c03078030708c040035008906021380c041c001c00d03982c3c9150354004003208000b02c80404502d04840d05070001c8000012102030048148014090b54075503070f60303075071040880b901b102c103084002d400d9000150303550400c5804048410740c1b40c007070120034644109401c5440c01040a808148180031040d82d823544003003040309403a04030300403555403c00d40c180500451000321000750b00000315400501d000740c0c4000e00400b81000b144408180c2e00380d03004107900d20302800f91441e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 553486016 1250 553484766 553484791
    0x806061e0a200a02091e0709080606010804110f0409050d020c0f090f0c0a090f181407050f0a181202090106050711041d06040605070f0305040507090203220c03140303 73
    0x90301605e06103101c103402c140e0881031605618200704050b00c5500e403c80b000f0012414200007001020b406000c4c0650044007440e01100d94513080ea40c50f4800740c52706030084d001c1ca40d901943c0701c050b15142c0c40760700265000002c466024128010082da5522020011400f440600001e0812814515840360040c0c8290003448088d680d001e056443d2900840020020484048400290707840440e000d0005444004200107458180705010b50945003074040031094510b4000401010942c001c00380c4e241184440c0401e907641040100880c2c0d400c001a04456001e18007040010710107603100b52600903203200b41c3e1080007580c6da0b20821707503841c010440f008d80344c1d01d980801c52040340b401e913010840a0b0b15501c035921520941101080c81c154003160102d80c02c0d40c3d140180000150081e064989000151a040c04a8078241d6900c079114115841050002c0750048041250481c2c1d420700c0080205416a2408651203103080440282505203c1950540c46020320301d2616400030084174070544140708030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 553487266 1250 553486016 553486033
    0x180916081203070810030803010608011d15011121030403390807050a140705040c0903080c0f0307060b0108070305012d090e010204030b0c070507060806061e0a20 71
    0x36a54440000c00e8400e5100d517401020000407442c20266000c1e01c496a90000c85604240204980c80019a11035148030f05070b0f000c01c840500c5011906241c1c06080c41d1400800030300b6481c851505a08900c0001011035015905601a042c0000380d481540a5503c14001c80d1040b83e5041c2000008204602c070091b50000e0700e4041c1c07034004912031503140700700955407400303001d03444d040e040c4444400200c0b00030300c0a1340c00a84203441008000060101102c080004081403040901440c22904c0014800304002c640d414100700e0521114040242a5060b26a41e03151072900d580102504100107002c00e05000c08154014070901c81e640c1a00c000080c0055070104648210a918081284540c95500304010124081c4898014011034902c07900000da200e6080d031070404840c0e00003c0410703040240500a4a001c036100041d09000c950107428400700346c0d240d0001141d128414001541c262080070484aa90030903c4001480d031600300ba660508178100c1003c10302c1c8880d1080c0302545056200040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 553488516 1250 553487266 553487281
    0xc090606050d0216021c06050a020309030a030905010e0f0a14010614040b13020406030618020a022503051f0e0f10020a121503020310151202180916081203 68
    0x1c0440c5400c0601010b03034100c41740e00198044030105806442041101034000c00c00929000300c1d40c02c000308034810f509600d850111181d4a003d40e8107200308140e02c840700c010520000303520502070b11994806503980c0305500080c46554101f007000495280c0d90300c914900362000c0600c06c440076101c2000b808001918281e08000140401c180925400703480e00f070015075180080c1c070040c001072005440204009180aa148808411b80824a10780c00d00400c11001216404120f8200110000c0c0f00c1600340a040d001c01019800b071600300403d030b4410f120059002100703800460a69001c044018407800802ca0359858a400002444495990050030200303500389040e000340002c0022032900d0a0746501031107410080d030b80a1180c0380e0841c60000c00038400c0d030038140500c40100000b03000621007038040c00d0300e080101900d841240c68080f4042e4010341103546008585044080c1525417440074181644c94646905001c45040480e006407000020340b80700106501c03001c98000750005046958141 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 553489766 1250 553488516 553488521
    0x801050d0f06140a05060f030712140709050f060f27073b090106120b01090308130608070e011e02160e0915130f030e0303070f0c090606050d 62
    0x7070111002c0e034072001030342030303078815491064454a481c2901140500b030110a011603008505111400398108540a0006508071541c100c0e086911085400800d580d403500c26041080c41c0d0818072001c0c0c04c240500110780302e50f50451740030389000c40c0c0900b07c0701840f03020084481a58032420300254910f00d10024450503102002d944181a0f00f000c0d5107c5074061106000142c000a5242494006c4140c05448181240c2d03c1007101c0801e17940e419587d410b150700944203050002002001d01e0b11840200c0507070b44285e08080003151f110103166210704403500799620310142d40c0244400507983c040040c0d0203a00c40c42180c007202c0b01c1a100c500687c07884042584041c0030810414065111740514010551446500790b401824a144098040d090410043e0300f004842c404000410080c0d4050207030917428580d01203071003980000c150310902c41c107142c107039160300c03600e4a00c40d458080407400c2c00601202c1051407215030305c1515425906030b103c0f0311602c201c2e01c690040100045003400000d80548103030b03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 553491016 1250 553489766 553489793
    0x6091e0f020903190501060b090120210306090604020a0f031a060c0303010609080714040209040b040e010b01090801090c0509070c080706060e061f0302071e0803160801050d 76
    0x940001d8038080d0034074082803805100b80100f04014500c0000c010a1080a10a180280698a21142c0351603007404c0000c01d94080b010403040c13004c0300d40c5208501c0e03d60030880c90002080d00c82da00c58092415103078403411908103ca0150240b60240c0c009a032510703140c1b084408030b440302d0716150803180410000314014071086414090b1002c2c500082034090342c0340c0020744002600c40000b9035680d0704040c801001281640e004c1c81081c2d00440040c002c516000030100000501030f1001030b11002d005000501030b0140355542a0414640000205030a00c1034100842c4002e007078a449009690710740c041400c03144041d0000d4900040d0010a1200d4606040000c0c0c02c43c1c1d9a2401040c4006243c0780c51103da4840e6170700311401650340300b0810540840002c01e681c4440d003181c1d20725a030a840c40b4030107142100042c0d41400c169001440b10304211101c2d40e608040405810801100f540324908524542c0c07064030003039101050080b00e00b0600b8031a00d1038030305840700a0078410b1400c0091340e965801803400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 553492266 1250 553491016 553491041
    0x109050a1802070501060b0a020f06040b01171011040602010c05120414070e1009050106050a121509150e010b040b09040914010c0c0314070804050f0f0a060e0406091e 73
    0x2080403e0100d0424081c850103441140c007881c0d52030300b40b040c000c0d1401800562140c00381e0408010400400c0070014018111001808110201d038140704006040c9280240b401203803601d85104201032854030740c05041996031036002084032030100c0206490502500c83c400e151440100005000a46403402e03018403002c10704c040302d540c141c0b59450030b60301420031112810410b5414204019280d89070080e60b004100c3e50400f14908446c4100003003001c0c1194030101091601e8004a0f48140c414001c66402040300c00000c00078000c41e0a81050b44081c640300d08000c450801c0004070b152a042c50031942101c0307841d0940f610f000402c0c410300c405000301400030b40c0d80400011b880034220f0001c0c064118040d109a4658407150450700d0041c01c100d54050b030204c80048284500000243c40c00c04582c00e03601c040f1890356180078050001820301c48485a001d030000329084001a04030b410601c440030700d000c01c44041c02081e4032445400100d61895404400c2c504011030a21003500c12036000071003a414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 553493516 1250 553492266 553492271
    0x1a120312010b1c0207050d08101203030e0609010b0102030a181d09060a0c05040608060604120503030f0106050a09051908061915050f12010f0f0507030b0109050a18 72
    0xa824200121218090b0302200004100003104a1140f910704500754296001030021410908552202c42d5101d5178407401e4414001510081001155421058401021111601400c2c80c040d03142c018054106904105d040b4400c0c1d8020580300035040c001e04031000d0040c0c0c025800e082d0310610440b01a820381c400b00c944600c000f5408203c040b484030045038000c050710348400f400e0a060702040e2130840300500540d0309900d020382000e042da500c28110f904403130b41c1e49481235442d04e603000025400c3c070482d400800880d80c045000700c10000c002c00a14401c3c50309001c050401d0f0b81c0c41c81d0654081c8552260726001a00f06c2c3c1e41880145490700560111034610f03441d4070700d00b0303031100c03005881c1a80030341c0c02070f40001c0d40b032a807002034214034001c581e807001d00901c45c81c26031494680410844290141840e108012074500010030f000700358860030000b0307600c920038080d002e4480039100003060160341410000c1d041c504142582c0d40074907411000c60b0000750003101c00ca80b400f0715074440c00802c2d8801941480c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 553494766 1250 553493516 553493527
    0xc1b240a0204080703110909120d0c021c02010c0f02030306060f1b01290a0302030d0f1403040605071e140c0c0603010b0405040b09010f03020d02041d0c10031a1203 72
    0x304005070005540702c6d00c00c40741e0031160001040016003000303024203995031142141a480c104040140da03d9940c050300085a60002003000340d0030500090100c62000300d40c60017141400394150814101e00c0c0c1e00c1c3d2516016601700390b10498503480104d44d115013112040100f4000196507030b00401c3d03030ba0300042c5440c1d101f090214825003035907050000070580342040116100c0d400c011120100302c9207000c4441c440b81ca4030319404691219000817200e024414103c0000f0303d100d02540172900640d0105000d2039584c507240c030b0031300c00408091303518800142540030403032785042c003a264001102a00d40c8624a052504011407003199000b01403c8d120350207810811603841d01c42402641c060803203901c14948071400c00d014013044440c84640d55100d50b84610041080f907c0c03011210081e290140c501c10405065800820003a00e5006412041d41080244082d01c2180225a5881c198411a0100039842c6100000c07010f440352800103c49404240304154007a240000d6615072022004090341d0a14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 553496016 1250 553494766 553494779
    0x60e09030712091d070201051005030c0d0f0c0e040302010f0915050c0405060a02061902040e0403050a1823030c010e0607020d08040b040609090c120e0111030c1b240a0204 75
    0x414481d030030300035000304c05200c1c40390740a004a0f079200c90801400750702c0a00d0000040d1b925040c5440c40c5000780140482d02c428405050071140b00590012019000345649100800c012501100c0a030700551900100e0700c0d114085000c2c0550301508008660318103007001550000804000e0545405003a0401c0001100d856a030060a0a1045500070701a14070b883d804000b070811450b03107407807100ca1040006228603003c1040e4242c010703405181c0551204000704040c1c550011031011402501c0c128000056003204407490103003029103000783d980148801c901490b82e00c40c100c1400324040741ca02a00003119081000144c955240020140190760040c1d864440d1181d1054008800d60b00e0001802c0c000301e5008040f40009040c140070402100035400c0d00200996080310203100d14684881e5801c0d0303000801d40000100b12082e4213455a281000c2c610386550342c1c0301c500d408480e6603c940c503003521068041841d140a0380400104030406452480240240e480106100d048a42c24400450700303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 553497266 1250 553496016 553496039
    0x605100b0f0310150c0b22080313021801050301201c0902060c0d09080307050706080702010f0c021b03070e0a05060109081609061e060f021009080d060e0903071209 72
    0x168600c40e16000b02d070f00d00c2c908000a0b06d0390020900c1d4070000904940746051119000e0f216010740e00062020303200e80300c1000c03000442c3d030150400381d4440b10f0302c1480e4034035990b00003000e8121401103008005280d2040d540340d400d10101c031946280000203100404000301100040426000c0c40d200001310111140c0c00140c15030421062408564001d0000b4516141c1002850014260305001141850341d513030364543d6182d102340110302c100584203001c92070b810b000750440c0801c042c1000c400d21654250700710084da202541d06403034000c154180c0c0714220508000c240c500954a4085815869544914400b005002d002d001c6604000c0d80030703070010b6868020701c44198a0342141c0e00446526251605c4101a02c605801c03da800c0c24808106040d00001c07180100b084903002d04160b8114101200305a0400001d1200900a01d05002e800d40c20003d15034000c0440c003129030f01c1008426180c1c000c10b02444401c1740c84410fa80c2c01080381c2c501059001c81004d800d810607242c104c3c4180d41ba030208148 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 553498516 1250 553497266 553497299
    0x60f0c1b050d0501050106080906041e0c03050a05010c08070e0117070e090108010c031a010e0120100b120f0a03030b0303041a030601091512020c100203130605100b0f0310 75
    0x3682c4e5581c01c0180f2100742d200c403d042c4c020900c41c00800c440e05151b1243d440d150400c002400310240402d50000410108607650401181c000c025511301c000e60b800c1941c040c04c4820a071100088980d800103400a0103150b83d038800110696070441108244985141e100c90054911001d00010800300d001076501c0171903440c003a104d0100049515045d009015090718061a01030340381c0b40c1031a41145450740e001080c080441c80903c0c00c3c9540b403c1e1a0340c006803610b001030300c800b03490080050300180c0d02c3c600e4129202c41d200940360f054502421080320340d11105842aa0380040c0c200440000107c0d202c1e40041600100c000c080d00d28043d074400706402d00c13100a02030900004000700800c0300d1903820041e540001c008071000000840329550004165150b6240101030b1158003240b001c10424080060403500300280300c0456803414554511300d07451507081411100a41480d000440e0b80140d42c4003c1c0444100300d124505260744120140c3c49500300510000b049801460005820b80405801e0780 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 553499766 1250 553498516 553498523
    0x6040b030a12020d0503061005210115110d140a05040b0a09031a04080d1a0405010806090f010209060a0e0103020c070b04210215091207090f0501060f0c1b050d 70
    0x30b0034030003260082c2c00c01c0c0c44800c071442440307000e10401105413074001c0817206080d110703d050b554503401e18505a42d24480c1102820500d5070241c0041203104660502c81c03814030036500c0c3c04d0701c0c003075200301000daa030300013620442d00144005420700386181001002d040c0441c0c5e28107000c0e0030a5110b401805640d08200840c0d03002419109041040c0884500301b41209003440c090060140380503140e0302000e12030b6441034082c0c25650754000c05400c418805110540c64010001c1c020355941d034042c244e682c00181c4401c0036034040d590742e91903011014400c40d041d02d44003900c6181808110401a6094201c4050590500d5000c01001008400910141001e4000c1c1c0c2c0e0b85545131400c0140c51000322a410a080403240d40e51121400980e07200c030f0342903c071306404035600b81d41e80161744080352242c1e60000d000201446202c00110b8109401d4200c211440d5426004107e00c0e03985243c2160581e44c10300c02d59010420310000000444d0503821180540700c0707140b03040b2001541e500e0210310b4001c050841035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 553501016 1250 553499766 553499783
    0x606030703110d060c1d060a0c0b0a1503140c010804030c17040e091f02040e01090e070509090109030305070c320d0e100f081810020d050901050106051e0306040b030a 73
    0x44c0c00e41070f00001c400401b100ba6040c0307003014240c14015000e0141054040d15026100001038242e0038241c02012080c4001c41014601e69501e242031411a104114501100e010301e580c2e007055035201d600001d1160380c160ba50b00c260090030351980c04407a082c00f0407004003481c0400c00440c5004032a11034501030520003000380954042c4015110303903503a48060002c8450300402c0100200c40c044010b80d41580d07112100015030000e01c0041905d0aa46588256001641c070000c2160f1803806506c4840058084d41f0306120965442008039113160004070000c00303160018480803204402400e00441c0b104000d176800c040103100508451a042240060a0004099139206802400c118046108a000c60f0605007011717844803001800011005010b003510031102107000303508400400ca413890402c0200e0085640ba4418034400e40542002c40d894808ad60800c000026402d00c14000c032070035003a010141055100f404e43c48814580c0c409070206601a89844660390a603400f4000302010780d10a1494 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 553502266 1250 553501016 553501037
    0x308090303091216060918180f0510050603010513030516050f0307021207051c0302011b080103021c0b24091f060306060e0906180f01170606030703110d060c 69
    0x40d20404c50068011070308210780359030108030f2080c200720140041e071406040032401c146c11001c0911001201900a80382e408881955400c0c003402148a100852849000f44500d030b40764024142070360026a0958141803040d8555408a849132010340002a5003003522000340d6050303182d03e440d221495040c10019080004d9041c00c514007541041940c1042401420400749040f002036139440a090490303520780490303004070307040501c00e5201400ba0303214401540c400d0110307040d004001c400b003404201d026201d0380b040c5852900b500030f419841564011060310a69032a8001c00039036518402000c07910311000c100884050b6214560f080c4074a608035501c004c03c042d1000c1c03019804030240d014000703061501d002805180ea000308000c006940c02d0303d500001c0d40300e40c03002c40c0e551480c4030818260001f0003018850800404504a41216010080c61242080d1050000c1d00c0f440287d5843d0341c5903014250400c0042c5507111240e01128000381507040074083d68580c881a9010f00850800003080c190030f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 553503516 1250 553502266 553502293
    0x81c0e1006050306011e08060106051917061e120609070e010e0417160c0602011a0901090905030903120304030906091217040b22060305090703080903030912 69
    0xc1810015800c030080c0440381c80e140102c3d40360300060040700f0070384500012041c40f034414a805c43c0700a012280031924950384d200002411600070501e04410700c4c1c02040f81545140c402d00041c00c54411f0703c0b9030242c4c691510780c1000701000c0064a16200c1c0c908000c2c042c0c50559903005605100050318000d4042454034098050501d4100d8010141c1c4209050040c4100b221036500d140d03006501030703501107000d40c4030780120040307008040e16100005202c400d640100101d141b00070048580c681c000f4400c41841c4a038809130003000350700c2c02e0341000b0341d94010481d410b500d0304640b0744180140140c03840d219030f40c070210b800c2c40b490303580d4080e5403a000000d01040650080d01c120040c5401d2903c840040d040c4055042411603103e405842c0200d26102a418592203600701d5006145185141c2ea88610101803c20301ca42c00c18440884115205400180742d0b0081c01900c0c802e41c80e6001600c041381c10356841034416044412810303050702c030a0000002c6074130b6034283c3c5102c1480907002407524104026 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 553504766 1250 553503516 553503523
    0x60305061b040f18021303030c020a0f05011b060908131a03070503040204020721091707060203040e040807081305100f08180a05030301090c0f110a0f081c0e 69
    0x40c1144200d102000104041084243c014068030000303680b1101c10342500e4100c501030b0080343c070705e440902d04a034800020035030841032424070342d4401d40e100400950b0306d8101c0001d0700d41030312400d400b02d504046010120914034107030340301c3c031807241200140c5c0c0407294075500403580002c0710180d15848425020b00c8000707040d1400b6040700900f000a41e1440c41c01d070600070064000a0030080c010758006c10b6003001c01855011002c1660307030407030705084500d8459000500c40c5c50340b4411075403102554120905800300109810b8256005a0000c615203440d025131040620b200a02c1a90811814045003001910040c000c00402c5a8200a10038450500003002400c3c3d40e443d6205050041202e44401c2043d00201115400303440f150141500d0784094030042c0c00d246071958010280e000c00030020440841c15441a200d00805945007441441a4142914100b40c0c903000c030000340d40031030040360010300882e10014016215a43d0141813480001075151007402d40704003400c5260300da00c0d52110900707080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 553506016 1250 553504766 553504801
    0x80c12010618020f120c0d0b0f06040501080c0c0f0d030e0a0209150d02121b01020f03190507050f0105010302040c0c1a090307120801030b0c03070516030201060906030506 75
    0x8020070040e40340c4581d0301d0701c0601000381c0501a68003c40c0300d0f0544031444c001c3e503054001c4000100c03151303c0c002070502e905601a0032003851062508000d40443d09042e060501c41d07074409003103680782505120054805023001000c0301110360003002022041d90f0709112000601c1c03004001000c0c40c08040300042d0940d0951490190301c1c0d0f100000d41c4000da50390800390340c4c02c43c0310441903000c0c2c210791802048000101c00806500940c0304108450744040c00908442584a10318200c80c000d9501401240c83e101401c04450090b8070500c41d40035030001000b1410001c1209040161421045a03141c90401022044005442c0d5564004005600780790040441c02c0809140001c7c02000035501e5a0091034070040141498001c01c000507080c00c410421203880c10f42029105c030480b60356240080100000340011111080d020001c0f410050000081d240070ba1416160a81004400d0a070003110401c842400c0c4d0456403244d02c0050700c0a19031286c0401346001e000a4012850021011080419003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 553507266 1250 553506016 553506049
    0x12120a02061b090d02040b030a030c06050703020415030c0e0d05060703050901110f03040c120506070f031104051e04060b0a020c030307050606010c080405101e08091903020a050106080c 81
    0x34102442642c07142c00100c5110b40d50444400320840128000b082c002c0c04020f054036018487e2001c0030080c59000a184071455116980074082c1d5590840304609070b000b2391041d143d07800c4c09446040d6406000e03400002e142441d525000d0408540388001904081d540c2005886c2d90b0006000e001010b81d04d40600c99100c031031a4002d101b08544032754402080d110350f102120b25200c0101c003040c100042803d40742d000700315226090340306051a00341587c80307030026500c040210345000d80c40c0c07155a02034050012000018101903040601e84400e00c0040c0501040045071030180244000d004ea13102d04c034507005810000d56442c0c030341c081600040c6c07400c00500502032090b4414091100000c0e000103803294003040a00c1c000c42039804038504000c0600541d0059030f880707442034040240b050b5020b0000d40105aa050111000c503a0121080d1a021000c3c0c0c0c010203d46c000e05100200a07210903600c2a400340b080c812169a1811a2105400c58250fa00061816044038a140e1040c0c44c0602d410766a0400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 553508516 1250 553507266 553507291
    0x909060c03110a0f1407030504061b0f020909010216050c1503190b060712050a0806120c01031107020406030b090c120303070c2d030801080a050304050f12120a0206 72
    0x2c0d0100c0c1071849005019090081110005036501018801c0c0304c0e181a40c5d000210131038640b0b002d441d0103030181d08180210740000700712008940480c1c000185e0a40d00e282c01910486528101f50244000c00c0401003464400799020403d5018200e1102d25444d80030703020703002030015941d4072403c02c81c107880380d20b0340d503aa01181801849a491882c0454046440c024000001c1010110b0045a218054070f200a00003c0366500605c14094000700100100e030b02c19603d40300503130303a440304001c000e01008000109560200d440d41c1c5a0754000d90080d505c2d0030b1030180c0141446036550000f0b09440094004892042d00101800200d007020409121100c800f2143c030031078400300101080e80c81c013000700a8020003030b812000200340417030419030080c106400c000e00b0841440031120010b189441c500c0850000e0154400010145000324000d003405512501552801c1e15120400c451407845200c0316034050100405039200b5141007007102e82c03000c81215039a80b18903803900c010303051000c000c104c00250312 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 553509766 1250 553508516 553508531
    0x51b10140d020313020303040b0d15121104060f0b04140105160f021f031508010e100515210c0105030f0f040f0803180708150117030d060909060c03 65
    0x24103141500c281401d100c1c0010384940c3c0381511905024004940650540000140420317260144002400019007a9500b4091f5244443c00094880075900c41d90030000048440d0800017a404110710440310401403000c28204d495a07440110380509a01c4030800c039100003030400880142449411181c202401c046d810402e6401042400c0007078040007c001c0350400c09280c1c01c41d50307500c4104400e51203210031030784200e030f8a010180090120590310040d52080c00c40010396003c05001e0550031140c0180540110741158500c6805000b002d4100200d17010702c46000707060b685540f2480c140b00d4603c05000003031041c0c1c907510030341000c0d0340c4101141004002c004100040c0f0750141a590010508000100c02d5503460801002400d41d882006241071f0001040c80040a0702202c0c40c0c0e03410384007000baa04a00da4454072a07948100101c1007a500704c074020010020042da00405000814245055070310f000004000358040311410741080f00c4003982d40d01d02d84140a81e5103c1c201e200301403402c0800020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 553511016 1250 553509766 553509797
    0xa060e1c170a0320030403020f0c03070b090f03010c1e05030402090f070225050315040c050105091c080d05130317060f04180210090b0301060309030c051b10 69
    0x140203914201c2420900080091203144a42d100007148421400300074403103900e6400c3e09455910948050300103105161342038000341004140090407a41c02030003045810300e40105130800303401c654000c1b9400886120009150386080c09200706407030160b99003100800d0189080744040c06110056002c00c60184100070058841100181c0c000011001099850360384000072031400304414900620b145214103003500c1c1607044a134001c141c840071410303100380c0c0702c084428a14002c012180900103086145c01001513500401c0244440b0a0140600320185150085080748609070003084a8544000a001003915a40e1003256042154404190001c103041c0c1c60050207450303440c036240741080100001c80c0362a078400070b0031100000040d0040c841101d00e06070701610301c076204d08242e005491003101e00114611680702c00f0141d0f10064070341c605590800c44218014184014200c05200b0151740d11404160104820132149640442500a00c48000309001c0c206c2a0014110240318a070503d45024 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 553512266 1250 553511016 553511033
    0x30708070618140105090d0e04092105031b0712030f0e100e100203060a0308090d140109061512020f0a0510020604060e0c28050a060e1c 60
    0x16500046a00d85800050801c4002420481003981ca1212402c800c00b08202504240d88450f0801c030b0000c200580d82e51000301d0300c525100c140c090001d081140d05241606c0c082d0700c1884028001c4804100034100041c6021084031044c80e440081034001c0108074070b01e4000c00011100c0307403400b030305281800d50035640c640350105c580404000741501c1d0650550301d0081c83d4080d5400e810180c08a07801003c4603012070000305805400c1c0142c6008032030080c0e050100368001c4074051900a00407030402451520781c3e41080c0c0100920640c04001341c88801e0108600e462440040701c03d540000a81c0c00303083c0b4000d01218941040d00030840303c210b0f030400c80048400c4030342004680540f50055a010408009281001d03030350881075222066200244001d580000c204e032245100f035004120304d810001c01d43e669803040700c03407059200c0103001a2404042071014a0481a1740160300551040d03180d5000502c4003985400120002d543c400508815161603231040110480d94030b01c02c1d00502507034640101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 553513516 1250 553512266 553512277
    0x60a1a0f25061503150c031b050403020a0509010e0c07080706090b0105090f040507050613182306030303180102091002032106090406021e04090218101713080d060f0e070203 76
    0x445ca60303200d19001c4414000c0c0c00c1201c0b8105051080c40010442041c00760840d01700e03000a070b004905040d000b09950038007142c2d1905940c0140c0c406040c2d40c2d5401702031242c60344000c40442d168a41445038400041d2203004035546144698407000c2c0d2907041c6818003069500040c42611003801ca0001d100114201250f450181c41043e10308941d111002c103034050781d41071658014110a003000d031130800030180c29070003840e000c100c0500e00d030946008800e07001d540c044162800b070f9058100b0030102d00900c800c6500d448244140f4000541040c045074000313403a080d60114001c0241e00b00043d1040080e00d4003a83c0a2801c00d40b1001c11030703e00382840442c20031070006000030a41d0394000348003071449814070803d80030118210401543c03945c84199840194100d41100004000720b080fa50609180076464041d455482e5600c4c4408200441d00110b058540500106d880000c0b1004601c085032100c00145072414090b90301294052500580750880740c81540720031840400704e41841329076a0b0100841e0b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 553514766 1250 553513516 553513553
    0x31a0103050c040e0108010b010f0f0e06090d08070f02031e0a0221100905010b060a0c0f021f080609160203040e091e01090b060a1a0f25061503 63
    0x642640d890b44003040e0383c400c0d40c1001071601c1d810750001450000540000346115002c0c9d07102000101191010789090f424480384201140030030024829601b000e07000b51881c030000404c1024118041c2d117070101154002142660a2103010080b031003582410040c00300c80d100e5100c07004003440281101a52201c4d03250740d0080c03040e044c0340c007103145a0700712020050090207030b2400c0c0c541400001c0c007400000d01501c10700b02c1c2d481d401e015800f0014a0083c0544029000c107031605411003006075100c0d642c5001e00341089922a200d099030048980710b0100d0321020702c145071100003260414004108940f1401020300d200b0039030827512580d0450307000c8161001c0360042d400861154031000301141c1000e84003540d42845d003040c54129041c5640540000300c0d200c0c025a241500c079194030301406907085e0386000340d00c03d0380c40c4903d00d03100d03030007488004149008551200d40e00b000013480840c1580302c507416250b011048081180d2050096500c2104900ca01c812008200c0c1461541c484051b4442564000b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 553516016 1250 553514766 553514771
    0xf0f0315020c0d0f080702060f060105030612100204060801080609120a0e03010504301409011103040906051507122d0201150801090807080a1209060207030e01031a0103 74
    0x54002403154040c0d400c4160520191000701000c001d00810450380c05a003100061028004a01e0311400402c3c414014198204150102d9980500640c2c0fa60720141c61940c001210012101d01a0014810140c0f508401c00300542e40d1071418000608014040e048100c6903003210341404041301000502c25200c0031501152901c5124111040e071344c10a40c03040c19174155003410208020040d15481e10342c2c0c044030b1200e0000c2c41014a10720002071078480e2350000040b031a20301d032501d10180d100d00500b025020500d4000700d42100782000074110f4001d980004845912814240650303d0052890300070010014410343c1043d05a84880b80740041c1c00f554602880b002c0ba082c0c4004840b1a00009440079002094a840c210300241c002e0003080c410616182c020351141c00440c3c580e1040c0640e2051507003065041c0d04005c0551981c0d403031a40b0502410061004901080f20000c03154018031040f94051800140c952440e400d0240010100c2541e41d41010310705040c111031102e1002811000c407400b1700c1d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 553517266 1250 553516016 553516043
    0x20c010b0105130e040305040e010803190509100810210317090a03080a02040b0c0d030b030f100c3c09230a0b0c0102030405010c170705030c0403060606050c070f0f03 73
    0x1550544115000009c6000c400c81c008035546e0380000040400d0300d50320612882c00c000c4008116024014011030540c0005d0040c00488840c2c4205c1e0341c10740001100500798689036541c440c40f50310020301c05001c4502500c1080781001d16030010a0f9051003a4120844030b0546000c2c540240c4905030500010140b00d43c5101058101049605039405020b41552460343c90b59642d00e00d55460380c41621442c0040d0504c2c0c0080f403903042c04a8608101d086180c010040c080c41139001d800a881154107040412070900d00c21300360111116400f040441403407414540d00f010041409600a100780d00c05d00c14804044010414100024012140803140da0031a0080d1310780712001900c0c0507440d5000011042000c580300030645c9041d40114010f611031402000300c5628844103071200b1044c180e080100d218070400050030f5500500045030b101744044016071800ea00c980d00c0c90222042034201d0400910f01241c00c8a001d034042003039102403c000c8195507600e41c074160419030020741c1030100511041d0111017 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 553518516 1250 553517266 553517273
    0x7081f0207031707021e030913020a05040614070b070903030323010501110a0602130513050103020d0210020f030f0403260d02160b18060a0c0e2803030201020c010b0105130e04 77
    0x11b0140c2612140c0c0258007a200b030f1610580d6680c2141d06d03207500c5140022440301d01c12205200300c510008250b00c4680c10b01d0306e0318800381c0301313000301104401901c102004690001102150707d02c0c030400d44c607242c0200290850400a0032154950003594a00034000c58801ca040d0300745240300d04490003480e0011003044444440741c10106040002040b007030010904401c0109003040d1002a12000c0c0c0b1780f480d00c1140042d02100359034080c400a500302c1d042c480c810003d0b0502100501d0741d540d5600441c1d603402c00d40c08003c0e165a001c4407241180e03180c041824001c02261401d81c21089104140c2e007002109440054100352003021a0600065030000e030112882e210b014a5280440d0860303000040d6141002d8214065082c015a401d803e020b1180007820300ca0f90780c80b4a0740e2000741a900d004202da10780701441201d150501c0b19000340c1c0c1c00c4a02c1021280cbd291451400554401c0e8005616802d1410141d403d4030304592901d41406424080480446d09145400301103404020b403201c811340703c904 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 553519766 1250 553518516 553518523
    0xb0c030c070b040515040b040b25060506090a050f0c0c0c060316020c061305040b120303040c030309060e180c0c0f01060e0a060b0a0c020402090307081f020703170702 73
    0x15900100780a444000100c02400300701030000c66a050741d040d003940703008200360282849280910081081c0c1800144038001410300078005403540010708101c09156a840320300b81480000003141e016440d0001c01c400c90400c030130003941008040806010a041c40800701d541d20b4802058095440300120f020b500d00401000615000c10005d080540d403070414a400d00c01d543d03007000d08240540714224600c09241010000c0f0b400014015071404113150500d030400c0090001c2d2000b541c3cbc0640d254440c9841d0300f109000440c06035103c0d80741d410b1140e00d5440c0240c40117640358000010f0103900410501643c990382003d800210440f401501150303600451900344c0d004508203030b250341c0710b47e60006550000551150b400d0316506800c0b00712554032805081c041c2c4240e80203405800d0000c1c403081a103d4000c0c060002d415200501c0507040000080c0400d141c480c0036800380c01a42e0141c0c8808088191544003002da00303601110651502845480c060302441c0d9821210135109410000103420381c0c0b0a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 553521016 1250 553519766 553519777
    0x1b0806010e1e0312040e01030609030e06040e0901150602030f030406091403070c0b0414040507020c1302090405160509100c06020f0a0216080613020a0b071202100501030b010b0c03 79
    0x24451507000107a090869141242c071905140030344105160300c058055281c0540c0c080702c00c0c41003294116803c5a03075400c0580000c500880034000c0c0d0300e03140c04996032644054005000c6e11000002d0714603084c140d8070b0a40da11408a00b0b080019181d040c0309899002c012681311803081150b80b5501e4585140540041002180150804038080c021115140b008002848024001c055503501c1d241c4541d44a5014401c40c481e5021000b0b810350b51000504080c0c2000b6031000c0a401522074801d00704010a0703201302d9000c00b92400c543d00185101c440e00d424401c0a812049c00303da944058000b0901c05426889420b002e24031843d60310602e080c60901c9840d01713507541c6901590941d16940d219080381c4198000307050800c0940100000000d0b8084a030300010700301c524403c001c1100b80ca40c001180324143c80207505070703000f1582040c0403034000000d07002414614810071900109410107180203082660b5842407554280c00d060040022035000a80a810f41c1c40d030070f480ac0c1c0d807100c041454603d180301c2c0c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 553522266 1250 553521016 553521019
    0x41109040b13110418020316060503010303030c020c03100b12150a2a0302040e01080f070618170c011b1a062808071205120a0201090803090313091b0806010e 69
    0x3c000034183c805e043e58910b1600903100380e0403101ea40c0b016025000212002e40101d0000030740a00040020030311a8000900c03001850058541c00d1b05620042803c200300741d007444448641701d844210480c149151001445c04c0003601034103140c1c1c81d00301019407004000e010410305079102d103e01c41d1034511480c41b4030300d030005100e10700c80f1070507100030050042c1d08a4407480503040380c0800001040b58000c0364504038900084060165142015000d0311546080d501400c00005110b1012842c0b103804ca42040d510387c0d042000b0544014400001845c0b01c6850042000046280400c440069101c0c0c010040322080309424551560360000420608107014603100340c2001000c442030b803480071220a0f01c09480c0d004041e507081c2c03525444500d203411511000100240d00c4910526140c00030003000e054110810301c0041b40c022400d88494078039400c29107980950307070000211034258400c61210340c170003400e0517441031020398001c0c090041e800741c403801090144005200020382d035a10071b11100311800340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 553523516 1250 553522266 553522271
    0xd0c091805040606170604020d060e1002070c05010e0a1203031103040f06060b0c03090d02120303010b2503050901050a120c030212150906101214041109040b131104 72
    0x24403668024200640b41501c1840c5420b40106004698030034000c0740d030310090000e21081e111542841000301c1048400c1c3c031b01d42d503143c01c843d810302c40a11103d00e40c0380480c0000358584c0701e9414803110f071242603070041e41407141c01e100040d40ea48401e449c4604580d50842034281411150a042e0003414080e102003c81600000800c02000300325018030041e14001d81c1c0030001075403544007064452040c80450900765006122a025900c3c0c600301e411f0f42d1a1000c1c01c180e508003146c2503103900e190000e0b0800c0c0110003000c100c44411034a0b0701001320703800500c040f0f045c0c04109140c0b0054403a2084041710350421500050554100b409403103694413021406108000d9580c035400024025004605c0d840305000c2810041940141007081600e0b00900003441404561139440030050001010300c100c5040c002c0c4a00b146070f070040548034051003861103900c00d4100c0c2c0303000c0c9084c62080104004180c810350342d0405002c0032803092002c6607031000490744a046030048d181000305118001e018419407050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 553524766 1250 553523516 553523549
    0x30a0311160f210201270b0313050d140315010309121d04060311010c170315090711060a0b04060801091217040f060b010306052110060503030d0c09 65
    0x15110040812201600f405030846000b0101080700b00c0da8140d0043d000a4403200c0281182d1135060042000d220000048104184d554440e9803054004984c207258101c070040320300c000d005061001e881c238020b0310b2a0812030a540752015644500010b0001c501e900700004480141d81d0103503018559854000314042205155008010b1041060603a60010940c0004200d10f81c0d080078024501540e6118580698000401d0300446204940e15016101d04998010f80e1514104800055000d04071881c60028581307114028802c0003007001d031544040014941d440300b03407403c001c944030381c0040c84c03550080703040c006075800900600000d4000f01401d501c1c1440003410409644607018420440b0744515010203140c69038024004000c44002d00b686a141e00b01c4800205607a010079501131050400003205900e6102080c4d02180e407544440403401d01da02000c80c3d03a002000180c01900c086142030000f1418100401d450b40144c0800604464444a050000500902000c0c0241140c00740b50590710 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 553526016 1250 553524766 553524779
    0xb06030a0c090807030c0b0310050607080d0b010c0b040204050910140901050601170c07060f0203010b0d0b030d020c010e040603060c0816090320031c020c04150302030a031116 77
    0x20507a000011002c00d9090b940000d00c0c480208415040f02c1d000038856640f80d05d0080624920340c4028000110042040360104d815540c0e04d025040e41344c0030345280341d10703036860000110480e005462420f050229580501c000681d4031148264000c1d0305450210f400e4031814140740c54940c0c0c0480d4840141c0c10148124101c0400b0b0041e540b048540c04000d00c1140c030380400550300a0741001c0c001c130004070701000090349000568000c200c9144a94000510311800440740000c980081c0c01458200c0000036404042b51223500540105042c114003902c200310003008003030340d0b60b0000560f080c144041107000b0442c6541b154000c034001d540180050141e48042da00040040c03800f1221400030b1071901c800500054415882d280959900501003944640445210303261355001c03078812603040c1b0400c034001100b00c4038105621180788860b0000c00c1c421020008100c10741c5c0c00001d212461075640302003000035907000542c80b40d42a406081c050010b6190740525410025010301c0070440400007103000841 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 553527266 1250 553526016 553526021
    0xc0f010c05120609131205040b1602031b0906010e030a08160318060503130203031b01051902030c09040509030d050106081e24040b13200406210b06030a 67
    0x109074070b00b211226640e89804001c64031105481c03119604404070120b0001600709107150002c00100d041590400f81c1d039800b4000309a00040c3c1c0301c4c805040d1454410118282004040300800310f244500d041c5d90070110128401d4000200000d041014120f40000c154034140119812280c008100c59a10b61400070208100314428100314002419080381361146404a040007059410300e40e501451921010303c03020407142c0407441030381c0c507000810100c1d2000c025106000e1507060780000100700351505a21807071800b0381e48400c0c800514010000c00c048441c1800c121131100608840026841d120300c1c0c6110f1940c0a10b22510490754506400441c4840d0441041b5105010340720820a207442103d081e245004010354485c070f5156040080810035070380f80c00101449000c041c100003000384d5100c0c001a00844c0740d18681071030a030303180c2c0600c24180720b81b25103500003a00760715010729042c80c0c03090081400084180001c8a00b40d0340c0b021304040c410903007011403280402441707651a0b06100e00354200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 553528516 1250 553527266 553527277
    0x913090807051e0d0f1707020f010f090b04150608152d060f12011505130507080c0309070302040615030c02060106020d05071403040f030611041a0c0f010c05 69
    0x10944a8040c03103003105201c615811044001500291071301c0b0300031800590f81c0500c1d441c3c0709028440209040215006415910f521a80c0b069000b8242c04402d08510b500f1160071001c42000c0300d060648120104000d0b0b0031442d013042d07120105176111701129009900a048030340002285010b038450110031300f900c0e4200382d8029803407050300000b0090080c000707100e01001e0b14030981001c0c0f00080010300031302d42a100150011720250082584042c1d0f10340c11821076100c544141951100c0040502c45810180259040c19070800380c100000e00f042a0080c2110790014403091079850f00100003030140030240300c1d05009550140c410b00038940ca0b140d0b51005100c1801400d03002900e003900c0d5000152000500b94122021a0044d194040368504102c80e291720518064484500340b45400c1c014990070002000144008a50a00c0381800c40c6051401d1329001d040c9c604040509102c20301600306c0908500b0010580400440d5880141402490510541c890150069440c00c4c55114195410400a25 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 553529766 1250 553528516 553528523
    0x3070b0c0d09030f0b0402030a0203031908010801090b18010204031e15060e01060f05041a041e051011012405030d090b070206090a0314011a010f020c04020913090807 73
    0x40d0300240c00381c030446010b5000d11000d010003600903200e60100d400345980e6900107001038103580c8280101d4000c40c1ca5a07005039008141c28404403025940c103a44840d001c0e0150000400070f000f505110740750000b8011000d000f5251082841030800c0038660250b04540085520425994500380094000e40c3c0d00c000d100e20980714240041c1c8510700b4801c21344912000d46030440184d05003030b42849000c50fa5581400340341c10512404001c0444c0500000d180581c04000c0c0a40440c0e03940c1c01d04401c1860000c58003042158a40e80300028800c50b035894001c0c200d1400030b807901c80c801129110325240548600300d6100700100000c0d2003e00c0e00c20701c859803941918000c1c0d04071101324941140c00c0b28011b007980b0270680d410b01e00380880d40c01442c1180082003120b10040c01c95035501e80b42e80f51800c580340c09210768845a99282d0480d910f43c9552007030342c0c0f9200003d0900c0162004091800394030350103540b860b54030959001803a9100d60391400341002d030b140700303124081060382c14500c1c00500684c071125054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 553531016 1250 553529766 553529773
    0xa0806250302072004091707060e0a051504030c060f0f0605010c0b04140106031401140f010e070c1704080c040612081902150c031005120d050c0c03070b0c 68
    0x5080c028001c54040f40e6010318100a03004407a98011400050741c003210745d10607250f411404c0451511056006065032409016030388190380d01e80300c011250307400300e00e40242d0011041407021920206100750b070484e18070420251139940e8a03040f940006500c1d00184581d142c0456091403410075030000343d808030311020820683d03444100545003d5402d800007405800c0c184000303400520f00500d001c01c01c4080c1c0c00041800ca80302c2d980c0c1e00d20144c0d8184894002c0c0c0d500c0144800901c0403484058000040e0b0b80d1403e010750400000c11b404a400928103400d218880c2e41c01001c00803400d02070b02d16001000c211a4456445000081c0c86041c0124460302c120700b8460b0109a40004100380000582d1010b5040c3c50010f43c114204520111a4440b4065000300e18ac00c076180d201807000c0300d11414034080c2540e624500a1904020b005540d009240540800d01c4100a403e030000f0340004808001e0506035203031840d68000d41d02d002c110b40c400b56014040c0103000079201e0554009005d5003511101034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 553532266 1250 553531016 553531081
    0x1203090a0b061203041202040f02040b07060b061e030403020709060f050a0b0a08280203070e040e070501122a030507200c060a051b07060921020f0a0806 67
    0x100015003c1c060b0001c64650400c010800000b4001210000d41a10150012030040042140003049800950000481c0d8400240c1101006003500c280c04c01c00d5001c84806080441070056600070450086000408420010102c0c09250007000104020b01840909000792a200c2030980408903071031250714020414a030010496440c000d09030380361a86140e4400e00f4179910711180540a410f503140103c54407220095815400704d4a0009600c1445140c0f1041644451340381404112815100754460903040071000b40120381e0301560003009111015000705032032058003403002c07030701c1039071054400080030130b940b03000d4020f405400041c4035508585541141c2180140056a000c0b03000b6010990b503049019003650900e001c1e0064608400207140c421b090410120b034564200107000007108140d84005400c004040d80040424040c0c841045140080180d05482041e0b44224102c024490001c10106032010340344d01140e0401070420108854490419051000410310085a814400031a9811 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 553533516 1250 553532266 553532269
    0xf06171006030f0f020a090204240f080612030d021606140403050a0f110f10201608090d03050406170105030a1502040b040801020408160f0312021203090a0b06 70
    0x145008480e0010105060240300d0ba0790428504480e1340101d03800340204c4008100808280f01070b1001d444141502c95100c0410a40c60580f0a418808641004800710004107180c2e4001c40443c1c00581c1604e00c010b01001150509055002d400b2038040f84910210714200c80ca0304003941d581110f4040e1404002402c491710040e444020221005404035170200040c0c03010780c0c490100564030f181e0b2403a180d020403013024030309420300c50461401030b615170200e1a000b05524162007104e9080b1000214803c22071a0f41c104025580900380300e02c0306210314047c40d038003071100b0941100e0548038014403514106c06140b41c0544a40c000c0c3c003c9038002058882c10755111101c1000ca9070503038000030020981800190703030300648103042050402e902d42c3c0130b0100051100d0f90f175010f40058240c1c24005619a401e083c030303a44c9003a01005c0525071681c03420b202000004140080e00b0b007900c2d0068140500c00c10300c0c4000343d00c1c0c03d03141c1c01d000906120000070440b0a0401140360035010340b140101020304e0f180d000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 553534766 1250 553533516 553533521
    0xc091e060803041a0a181202010315050109060302072d15050c0d0e0f100218041a15070b0412031a0102060a0c091706010602210a120f061710 62
    0x9000413880040d400c5400000f820029024040c454a01556070b134020204110a62000e54001142d0b0101107401108568142c018150685010001c003543e4624180009080c03011a1241e02c050650000350381d005d0040500d011074105195080f0074002810001c0821945c3e0000c003429a04400c8907001c00e2414003150042a004881090485043c00e1086201c80010154459008142d11940700700303041c090030601032038058050700c1c0401a11003a805100540090860b03012600c507501d03081e0504107100c801ca5508418040907038481026880b01c07a0092168400c06602501121410003080204032040c41c16414405080d030701400942d0382c4060014000e1201d00115025030014400140c046550f64490381222083c2d02c5c05403051350741c4542492400c490804402c0882e0031690050014503010010000701d200d0800c0c0490f8070b00140c4040705502e0203124003100400c460700b0900301150209400035140e6107002c44003002125500c842c040c41c031200300302c843c5c10940226550460010841e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 553536016 1250 553534766 553534769
    0xf1103100909150e210a09050909060a0c050f031f3c1e170703080711010e03010e010b040f02120114060f0c0604051203071205040c091e06080304 64
    0x40441e5155544450341c03c0181410b010318030424440c545d802546065022040e80298030303220f140710381c3c64580c01c03c01800301c4101d8000341d0042d41414244511910001600c1350310401c1c07040b001402d01c0300150122024450202403000048000c01846403160300c00321b28000d2940c1611086c08180d0b030321058064100c0d0104032140c00c0c51020085094003041c0410304484180740980500300107512480701c01c0310082ca040e0170301000b400c0d07140103002c442c10110200d100960784800400485103540d0b0ba05d4118071410b00010060a4001280012039004080e0105030810040c005e08c440008500740314000c0c00c20080c1c151040b403d080102801001e40e02c200c818500940644d6030b000d0b030912400001c08940d80c3c04042d00000c00708150141460f03a48054006054190007610300c0e4141820f00e60315013040c1002e290f20400c2c080041c044d01c03580204d04c00c0080780280c1000b0906980d03e003082e800e0402d150b4007503004581044c0407000e030004a8400b0001d40030b070101081103619142c0005036901d0149 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 553537266 1250 553536016 553536023
    0xa1404050a181101020106121b050906031b21100c090f090b030c0603041a01050f0609010f0918021c180f110d0c080c09040201210f1103100909 63
    0x281000b0020a10b12a002240d441040c000800e0b041da6a005000418000480513075035a24080d40d050728010314400302000800c012605201141040b10000340c4415030070140029101c1880c0c15608951107800c008010300401410446042c00b400c0140c646400209550112042c94542611a118000c2d80c2520a64030702c8408074a00904040c04070008284220b6010342c54414036046c4507441d910400214840e9100b08a00303840c048034003c4840c45120107070000751085041205442a23030702c03400103849008409213001c4014a8520506403042e1285411a50310a00e02800003500b07000c8030380060600032242085041c3c00308200800030110f8220f0412007100700800074611012603982c040b8850f0450003041e816142c41c24a00c0002ca03800e0742c1800c00c5a00112141003000812020701c118400154291004241483c09030700003840110100251603045000070b1580142c204107512011641142d04010019260800c0030440306e604100c483c518110695070740030032000d10900a40210507030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 553538516 1250 553537266 553537301
    0x10b0a022a0409030207080a081b01140402090c0c010e070f0b130620010c0801150302030622021606140106170c0f0d050a0605090a0e03070b090102090a1404050a 71
    0x84040400c0080c0032034030811340c11031264031070205041005010941e100d9102e940c0d05036841e54480080320020700d0f662503e08083c1d00d80405041d60122898410360301a50444490240b0b64501603468042d00480000150300c1d072805c1e00101c1d41003400204001614100403d56441684d01e032904046441040d4403404c840b4490001080b00d24003c840007030780c0000300e01540340010040b6956500711243c41010800040c01c80c80104180c1031410142d91440c1c00c5842d0540c9540b5018000c01c9280007a541012101000031080c01d241c04000c3e415200e41c9038000f00c1ca840c50400b0383c14590042c02c949041400b25510706400000c2e410b00411f070705600d940440a591900303540d0002030243ca90440880000c00001c104098085403405200b402c1c4550880c4030000760850801c003e1000c040170003840071452500e84420340c241c842002040c8da0015502c00380c000000c0d6510790025002e4018034a8454015600031008201039502c94400410034605840406c13080c0d03603000c0d00c1c078141d41c00040866203079031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 553539766 1250 553538516 553538593
    0x80a15050f04150510091a040b180102031e09032b030e03090909010f0605040c1d06041d0a0e0703170a0309081606240506180306010b0a02 61
    0x42c40d0300060500030b00c3c910358607420340d60b80010442c08480c4895290003d084200180105804062090700d0354281d4400141041d0511885810511403203106055192030b109460310140e10820444216074148001440c2071118808603490036084981d401e44a0300600e14200038072160000f12865000507040403400420b0b80d0001500100803040811782c0a01041001d80d1090321414003150141e49004000070310402c0d072164040480700d030340d007001e4400c908000c035440680303910100d0154100362400c0002d40c10b1010000140c0c29101c1c9070300124020204600b0340200d40d0700d5401242c1703d20101c070410301916100c0e403049a01d0303601900000305800158180c014914a0b45009820206070324100007a4a90160721143d100b50800040c02d1000c0e079280424408000050017041c4000020070268081c4024001c18040d0303e0700c4c1400b40e03a0080300085251144402c0c22480c0700c8a95001605803241940c5440e8442c43c940d1041d409580584200c0c0024240002005060455055502d03650311840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 553541016 1250 553539766 553539769
    0x10e06010819080a1b0c062d0e0109050a030303020a02151603091e060518060f07081b0a0906081f030803060d061805070b03070804020409020d12080a15050f 69
    0x42d003040c242d40b010850703500100c205004200700b080c174a15004007000f98034030317240000080c0412818000c0c140003174075007411501c01c403102480c60503402c589414000c4110b100240100d80703a000300e40c01141c0c021175243c0001301b03254040e0300420606040b80d007503400780c00c4a10045d815555080e04c00000c01c1d1080c400c50712140c4c0c80b03a40140c1000d48110740c100c000d000305c2410b400341c00c21244070680340c03140d688090000b0b20302140d20b400300130440c410181c1410302c1c040c1030042510000a0002003031206a0340007510701003402c5913074400311808092007511180034030700003401c000c0b00d402400701184103a400700300d806100b0740565519804107044440041c0c11a030f500c2c80e103500040c1c03080340c04c10034265025000032028010074001244090700c1380d0560301c960900518102a41e03101c1054800100140038040794002c040c1d0342d00507010340f001305946031540701107a901d03007082102a00e03070300c1018070036400d0796403100d881c0703000303d400003002e10920640c60041074a160840c854954400285601010700c1d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 553542266 1250 553541016 553541033
    0x90c0409061103091e0a02030606100512040312060f0308090d14070b091c050601031101050409060b0310150c02040f06031a04030306081c0c111002010e06010819 71
    0x44074450140495511681c1c1c040c0001ea41060b2107100d160f4000c400014244502e052803941c80006070001402d4200340c0c4d4012076140d40f00070b48268081c0700c0c4943c045840740e0203035085921120f50548a0b606520f01424020242c105c1981c2100e122030038860005103a0a0b0110250152a00860343d1494505c600040189041e000e0741d080351101502524040070075401d225203c010300341c9800d020380c0c40401104210200c1c812203440d2000301c0f00d16040301c001c1a80040c119054130f1b4404c01d04070b034140e500d1005a680f03001b6540100405401c041c0003003900b650080156014882c030b10b031600002c584400b400c00036003440700301c3d03140000e800c81040703009440c0c5030b001510010504140001c205840703032108651070718080c00c89050b102410050104051b810301c10000240f5a01003c1d02041034011242c070003104040d04500c041201c140c000b0030500c0310320552108203200052108140129030711000c3d0180040035203203007080c05010000aa040c20200f0713882070403019005c1c410f5002c4613030390f01e2400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 553543516 1250 553542266 553542281
    0xf010b0d021b1204141207050d06020f04060921080a050f0705121b070b03010501030911090405340b070c180b0907020c09060906030a05060412080c03090c04 69
    0x501c0d240281c1e0209001c1091210f1a0f0500d420f40c80190f071241869035121100d0010380101d4041d140240a403032844a0124915007a600d04450000d009025401c0040c060b00a5895800501b40300044c0050201c0c4c0020003001120100c240e41a0b0203201506040e071240e0b65040d020340407401c01c002c2e000415126200408091907505d8406003003010030780310f076454460309803c41c00400d280080c020020080d13000e02013000a4200006041d414244004001103000c1072081a0516440e102e4980c104006560040c1407000050402d41c01c518090924a40d40d100705140e03038100700492241c100c0c2c41c40018500001e00303102c00480403802444c0000b113100c00e50110b402175600350450b110100782d50750360300100070071b180c41c0140114007003004030704001203410060900b13402d6521003d1082519201c40181c140c3c80f007021110b01100b0750f25000441c3c14003465003001001401030104010800c04c295a450200d0703d4141c0e0b920701c0b1030703842c0c3c126500740e40720544581c0126800710085000d82c0c039058001e0003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 553544766 1250 553543516 553543537
    0x211a09060f0a05010f140f040f08030a020304031e05191401020a1e021c090801060b0301141207080732090a0c1e020d1205130204051005030a031101050f010b0d02 71
    0x185083c0c07010086c41d030160040190070040e1840000d040004042c1001040050540c1201442c9070000901019549115620004000d0340c050840481455424020522080e030400e05950085000404484042039007a508840b0080724540607a1926414825542a0b070080d0301c03007011503071082000d0310365040d042d03024201714030039403421400d9085080b4a00c0e24102445e00c80d1a0f900d42411000342c00c1da00290410500420b0a20040041c4041c000388606102d0080d0b4104c40c48262407118242050910b401141c0a07110742c400c001074600c50b0101020401002c0d98a0b103800058100302c015a00c10301001d034540c010344200c00700d2080c80190703108051000960410804201070210070409000f8801c581c140903801c03418803040c0c183d40181800060b8030300c42d10100124903190f076200c805144d0040b80a401250344100240309224040f00300da029040c018110f809000081c60024012812a0450300b055420040171503481d88410600078166405d140c440350900c0188804100203410891110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 553546016 1250 553544766 553544777
    0x6090f040e0a12090b0a0e2e05090a0b030603030a051303060501180c0807140c030706092607080a0e030a120917030c070501211a09060f0a05010f 64
    0x4440c01000b0820940050310403802c1c4030305008880300c09880c003a040e07803100139074990401c2007507030399648003000d40c140c08821641d00c02c4c44039024400ea030350344481005039403805c0001030100e04201d400c400607012200c403c441c2820b04940321600da042c1c5020644e2208d4060b4000d00103400000e004c0c0c0c025003030300585494038004169494440c10161017085e407008400100007481072059000601403201c103031281c0e00305141075091003407000f84041e14a08102000290104010300420414412a1000d0760490310910003e00c050070401003410002540710444842440914251194001130307039142604040c455003068840d41c81500c0b82d104200e6416494020340010b00b000030305244074046801526580c0985107824030104a447e030104101c0f4014540c010702071032100701c0d4005080c005607203080c6000b400ea48401c0d10031081000d9190070342d0010b681060203014406c1d086180c0b64a01030340403504040da075100c010501602c104a40078107034009070003000a10255000f00c43c51039182d103032440c26 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 553547266 1250 553546016 553546031
    0x103110d020703050306010f02060702121b0f0105011e060203030a052d040c1d0a02220308070b06091e04150c0905240d0b2e12050606090f04 62
    0x60101d034441403040700444d60103c1403100c4c5e560b0001340136842400311f0000b0042e03418030a0010354ac0d81c40200384904200400150710703e104801071035518414007072208840d444002012880d028003400d014582e070a10b1314081508603440b900c94220200c50454000c4d515686840d02e0071780162400805030000040d0f0103110034034141d68080e0040040102c0c0b01e403503035a070030280380c40d505514440d40420b01c050609103c0b03a20407624403541d903404c481084001a503507210400c0b040740c44010302c84c581c500354009800001c20311107031400030502680700b0201c442681d5181c40130030540317520540d01c07880e0701103600c10120905503c1d5070384185c05ca4050010300041000b00401641a100c000b0002d8000070b014030340420481c2005101817000200603d51500f840003000c0e20707401903005800c04480384c0743d10f8213080c0032140ca40e0307050014140306103050350b0003c0040e0701d22025060482d200600004258003d554004800c86c882d05d4022000100072030f1a09103510108051440503490742d1794016030340c011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 553548516 1250 553547266 553547287
    0x61917030906400e060a09050705130e13261c060b0304050c090a06081203010e0609040201020712060b04020706050601090b07030804030c03020a05060f240a05010311 73
    0x103840e211007454821420f100c010020004220031042118001c0b00003203000000c4204100c1040741620050996018240d80b00c40014005900316032085041c1850881404000c50303100f002001600c1d266030543e210503603500a8100121000c072032480b00d01c44442142d50020314254481c0701840d9461307400c00b030f40301c88140241c42e03940c1c0080c0400a0f07000c518040300407940114060780004203040e0301518114603003174460f50b480e04040865680302e5020b45c00019030104140d4007072005000390303c1c111000d000200c3da00008030f91081c0250303c1450320040c005441440c0500910307200e558107034050700c00f140c90118842564012100c1c03c46415071039900344181c80d01e0300d2014050642c091031000c01c0d6070500e28005840c1d0406034120020100e01000004003103038100b803078107401681c18605980d200c00c0d503041c01ca007041129100244580a8001408805984000301e90b000f5034103000b070313a809031f8448030240b148126110b00c203a0f0403e40d1444100010341c081d80c406100c01e420301c1101c900d001c61101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 553549766 1250 553548516 553548529
    0x1202011b0203041a0301034d0a080105040f02090a0605060715061e18090515040209090a150e030c07030c0306050615030a0902030f100905060619170309 67
    0x28032500182d002080030401240000c5005108075507400300c481c5194159180d000700390050100346190685100000c03034555842104120180300c0d5840005501c1c0c200aa001c50089403c80129114440d850380100b0521018403031207015950000340c051243d65142e00f446280c0d40c00501c2030102c6a91b4100010b0070b511480010003e9901c40c1c2d00c44000c01c61400032010803a683da400100d0300000c00c0f5210b00b4180b10a600400c01e480f072402c0c158031000c03094441d64026044d4070600400500920804c1000c010000c0c1000d80901d1013103500c005255109031809541d210030746405400ca2440d006400000f0304035600c1107419802c0c1d10b0a6030b00c0d181410130f002e860651540c0c01101c10241c4030104100340455880307040e4001500715016140620011000c445600014000a001c0c81d0380d42c00e40d44c00c55608200561212581c0f200f0f030341007140718000d50001001d2416041d100d40c09500000345603850a140705500304d24002d24107407605420000405d82624014502030061311040240110325618107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 553551016 1250 553549766 553549811
    0x11d2413080a021509060708070f020d08030f0123010516021008090111070314031504060906050f040c0c030809120d0b0111010b01081501051c0506100906020a120201 73
    0x710000c0150420520500401140b10030400f4030310902445500840e40e00d003400c84801c80d800810198603140302c1e040c40d1654220000c0001c0d400ba00ba885603004025103100035510070100b101e00000c00b40e0f41c0c0c1e00696610f00c180c0a0f05070341210b00d100d803032202d90b010724060001da06d0340c6e10a08580d01300300e6010590701d0710001010380c081100d510800c07a2098007409070791074507818007440a013841299580078008500d000003035003a030b0101000184a8800301e0b960004c0d0000b0040c8248002d40d5220954002003500f17000740da0003050b50300c0e040d01c02800c140c083c00c100d8140c030f551707054922105602d044845c1034000d003a440580c0100c0e51b40d0480480040040c00b4000e070035100014080c118000054070184504003440344903410b00aa46e070450b03801000b0241e1201e204c801d01c00c440707240e10004039580d1141494542400f0b8a2122401040358154841440360006582510701202c00080a555200b040d20a0a005a004040320000542500040d136401c403682e00000c1142e46442c0207900c12051003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 553552266 1250 553551016 553551029
    0x120f15100f120e0607050712180303080a0e0d0906090509010b090411040308070c060306170607030c020a050703061b0c0f0305071401020703180b04061407111c02011d2413 75
    0xc100c07d805c2c01b40081c1210500074003030400410502c0c9112089510b100e00388400f4041c03280020010700c0280c40d580044140001340e600340c89480e4251a009040e2001c03d01403240098020000810a800c01c4260305051307554404c8401d0a20340054104005070003800001000c64105000000025810310042c11125102c1d82041d21802c0c01c19000400304ea410350f201a15003000d04000c12071024002c180240c00403000e10b000300d50032860900517894001000f50040c00d6201d840e500009000d1035901c100d0b62520f42d16000b11000481880403140c0898100c40039004030169407400002a000e10014040244203510001c42c51f00c0c0e070b1000c5406c9070001642500844c40340c01c002c3d030481864042c81c0c0c02400288590601f4941440d90091000c000117141201c11600050486c0511081d00341900798060002c4c040e81d904034581000ea002c50300044000c03170100c3c1500350041c3c110302d004d45080d03540e040c0250003d0100905140c40101308120040300701100300b82000074034038070b030f51030307000d01010300070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 553553516 1250 553552266 553552277
    0x14010b040302040f0605010e090403030617010204080111130e1315090507060f05182e031b121e0c0203040806090d0f0c030302120f15100f120e0607 65
    0x61801070009a134028000c081c589032615105000503a0041c0c1a0480d102d0160365034100b80d5903601c2c09500820241c1c1042d2401071014001e0103040105400400669981074001d0000d40e556002d00784442c040c9565003c966066510244807616100400300e0b07012441d01030505180000c2e8550061f04040031082c040c0158503044000300780041042100001d14492070300da080032080700d500410070301500301181c03100740c141c43c0840c850355289000707840f035070414244141c81c0d10960700490154070762211400010038285800e401190071089203031441003105403501c56002040c00040c8c0024810303070503c40d1020800710340c00c6d840540035101d9504015101d4000307680d035608004a441c03510400501c012030740d522030300c041154540c0c401044180300c116418204d0051480e440d00fa00a4010050720745d9940400c24200071400c044075036203a0103010803082605400390030350280300076860500002c07008103080c441449080c0d07104a101640010703034040300060404603544064201501512103000080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 553554766 1250 553553516 553553519
    0x142d040504060f05100303080105040b0409020418031706180901090507060503101703070b091516110a11010e031e01060608060d05060f0c2208100b1e030114010b04 72
    0x4890321686420213202d07400110b217645107a40003003d040050058a00407a211181e05416845d142c010b058a00d43c0140140f040d0b51010f05d0310b0241e2a000f40c8141d00041c103801d81d212550000c1040c041c0101c03000b42c110300100000c480300840001c1c005d80300c020190361740d00891010504c103100020180800c0d5907040e42e40d040002410802524542100900303d0110000f9081001c000003100d10b0243c0c049003101440da5101c120178107083c1441c03207040c84e400d60101000f11071a04004010000d60706c988401042d40d1303401c40c0c01940d494130500010121902d000e1496440d6025101e2501b000c50014101c40040e02c007002803d03030301e1941201c0c07080b040c4e4640409200598001d020503600460984075070540391002d846032983c0310000b40205580103114000f2511510044045038074103051070321510611b501f11141054580300c0d512660056005000060348100c100d4000d40f0401040100300c1c0100760b2000f900392407e00e141d10382450380b665a9040914403004003151550003440c5280806803103a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 553556016 1250 553554766 553554791
    0x12160912150b0102011118041104080106091103041115160b0604050106030b03030d051f030f020909061612060816080c01080c0d021b01060902070507142d04050406 72
    0x10740d80711a042d815641020540c0c143d82010360140c80307221940228201e854001c003800314000b001d40750164845190005808514460150404030172500d00507400c01005c0e201800c000554041502c0003000b04c0c460441b111500d10b022101200c0118600c0c60719803400ea84650152003024003034100300c403980810f0781040114a080d02c0340758010259070038240b060b03048a0001a13201e01c5800d40008900366550040b506e0405000811000207420740c400800291726810104c44072000c5020403442207d06c080000c56000010807194007402900c01c42d100a0140d07400c0c240c0e0121031000c00201c074107642d074900055040701008500400086200d068801c0e9050117202428a0042049241804a11410b0001c84c2030160120380041c0e0051800580300c003080c1204210304000300d19095281c1d820030802050506d000d80c02412810720034012113204903074036041224000b8074104c403594404170011140d000440c2c50341c007241c8001c090488989160303444000240407284140d8056490316540d6265007090b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 553557266 1250 553556016 553556021
    0x60102250e16020312091606050c0607030b210307060c090509090114060d020f090a050a0b190504020708130303020c120c030c120a0b1f05061216091215 67
    0x25241c04200040406042c80c00780d580d10074070701c510742c4000c40000001c45ea0b002c180324901645485000070001c031952404001c0141e0007136014000c683c0201c2c0041008540240b1030300d07c0d88a4094149101d400d050180b40d40c3ea0107102080301c03140d001c10080792002483c503210307880090381282c507000d90b543e0828050000420004003031024a80c074110034610024240348019510150031100c03080c00034180d10215a40c564142d90035508941410241700c941d07491600094400e0116031000c0140018410800c02406408048500c0d0081e02031812322850403e900242513076800740d9005d92819050100f1f02001d031500f0342c400c1e130041c1c00c0f140401c0d81d80d2a00c01d501c51f00d5201c2c600c0050244107448030009444031244030b0b01034401c1580d40540f1040640a0000811140c1c10062800507031900b000070000c400340180a115240200d1000480d840c80c042056400401700b108440d10305e0b82d10301300000c011000704542441030018610340003c81d40143d11050002921401d011030155006018039000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 553558516 1250 553557266 553557271
    0x90d1a0f0603191205090405090d0206060d02130504020607020d1202011a1c03120f1a040903020303040305130f0b0d0f110d050406110a09140d08070209060102250e 72
    0x842d4000c905107003c080403440e41d4080507a0800ca400c0f00c44200d2850903109031041a080d19049400e02c410800e0510001c507030900f1008458090340c0032552403030208040046903c030020b40c80b5010101050301d5400e01d41c0000e9209101a0080b450301c4c501c2c5e000110315502c0c0c8041240c1a4210317090f45544140c0c207010b0380900864080b0713012100003048000500500c00001280141800c00070080c0500d4424031100d0070242c505082005040c2d070540d1040c01130302c01f00e212140e220810a0640000f070800d84a1000c0180d0035902450444d1250341d0203c4143e0300c030030100140403980c1500890900944602c0600405c408060170340c0d01c03c1514410001d03510554207001d0b110740b4080b003068501d180041110700740201404000341d81d0381c0b5854494018035444080701445000460300c500351a8009201c9801d03a0072101103030200b5958030040040030b00c000d002c02030801405000d280c005003440c05130241c0001050060ba030640314510111440003048001c020000101d010f810041606014400b58 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 553559766 1250 553558516 553558519
    0x114010612050c0904020c0610050a120618020402030a150e040302030f0703020c0603011214010b060307030b1c030206060111030f0403030f03140c13061e050c1e0703170703020c0105090d1a0f06 85
    0x180203407600c1c0f0014043e941e01c040140c00d2035140c441254ec4c4980c0d10b480c0780c466650080085449007406081c440060040b00d0125007409545003000c609402000022441103515038000d5142c00500e19426005400040040342980f00c0d0709032000703c5660f081c0c0a103000c2d103059015107400722201e0034000c464070202c0b045224282d00d8121200125200c1c401100d5114070030341400306120076070720040384098034940307400c1406040190402d81003640c0403800038003c0900766a8210602e07d258540c40d280e02c135207a0151702500007003004000082c016203d810f0600e00c5818001148166003941043c09034080710810040000083c2c801c420340010000c1002070328451429030244503025500607801c09807108403005000b804501041031f04404c2002895a525104150756803854040925a481b40940003c40300c000300350b8030b41640740c01c01100391080c10350140e006145c0707001e0346401590030303a1144c00c241d41c00c20040d8850a012079040c040b04002aa44031054802a16003c07131480c40002d009469103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 553561016 1250 553559766 553559779
    0x30b011811090d110a03050709050601080603070602190606080316050d17041e080a020d03140601020a02240c030d0609020703080f06300114010612050c0904020c061005 74
    0x301c2507100c0348206038905a02c00d0b04044c0e42840d001c001410072006034401070861141038030100b1644401d403c094007a00342a211404261280c004042d2138402c10f00401c0016803000b030441d000c440e0341445110640f030250f4000502d607501d4920660031544031446010394550a41800410400100420f00007080d20f80f800003a008610f10b0343e441200409840500040704441c41440d01c8031080b0340400d56941d0250b0070340c2d920101c07107a01a442d00c01302410f0502007450030ac41c0d030592240d00080a44501c1c030590103020021660783c02c0090004030030526000080034142c22400d01141c4000411210103c4002552101024041041611407940162000f1801808100c0000e60003941d080e4000319890036000ba290b9804010524a014001580360509d410560682d801c030242088006420b128a0087c000c85003034403601d800003042031086600161044640c507081a140c3c0d0700440c1c001003003041d9586000310312030000c2c040e80c1041d10000e905800610612036601e4a6090440c0104400c2c0c440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 553562266 1250 553561016 553561027
    0xa050601090602061506130b0304030c03080610050909040311010614040515030c060c010b090705030901150311011803050d08010f06140d020c0a060504080309010c0c0b1f030b011811 80
    0x11900d62a5201e815401b03803c0101741c151303007001d0101d02c400240109500164681c501814001d00c0b20a09410640c04154640007141c101d0404103040503030700ca015100c20340b4014030747c02440b00704040284181c08010250600410380d210078000c01c0d008200d002c80c0e48020042ca0000c120441e48047c000c034110318041041040c0c141c40103d500105005c0440300359840d205030620150141401c03114141e8004c03400d404018641da04080075500480c0001e00070422051440d030540803440c1c1074003014045125440000405622030102940c0300c0e4011143c00d00420f42d2036803010304c0c2c075040e0021440400c441000600c00c3da507280017904000c0401c5d00d012071081c52a05910f0240c0d00c02c00c1c2807401d40a400217450845400d04024030802c569115804104074a0035040c0103040d5001034070401807035403c107841130f441c4a104084550030780c1c1e0013004410142d10f6590350041213104003031502c191690b00d49000000701e0010b114141c020000c610414111070b50071075400084808a0b031803040c00c1c1030140203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 553563516 1250 553562266 553562281
    0x619032405090c03040503040306050f0117030313020f04020909040f030e19060507061b0306080d02030708041206060b0f0a0212040b0d0c020c03010908070606090216030c030e090a05060109060206 86
    0x42c0190003081c000b141555903140c6050103411441a900041e12080c2008144415000340c550302c4c41c101e51040b142169281e50b20460130380c0740d02c810b907079a001000702160f229025180c81d540700c1000301c1004100503c0c100d00d1030049550f000c4111810b5074032600c090060800d040d0003081d0392003010030232141e03c980700807140b81d000b0400b0080e0244004110303000c82c2010420400394400001d0f00091070f02c54078903050311880180a0f00080c041c80c1d5490140d0491403075824000001d503841d15038402d40981c02d150410b1a01da10880640d2419140a91500b0000a0000303800000340725001751040155030300c0d20700e04006032410351000d1024401240402c42085000701813401d4440c85040c1490114038050001070492604041070700c9264103500e050361900400c50f1a400601d00301d0300c22030302801410f80e141d03004801c07130007541d0050181e003034020000c03400240b06010003039155120381080c8503490109000b0510228040300c10f4182030783d035034042c80000e60b000000c0e10000c1025100510040ca40700300d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 553564766 1250 553563516 553563529
    0x60f050604090c090f09140f1b061e12100f06080601120506010c17070b0a0207030e090703061223010504031e020a06020706020a0906020a1a060619032405 68
    0x8100c2e429260b40300d0180940702459003286d402640c000650000c07003042c652900352104102c8411800500c201d00e04030740101440300005565440c010100c0342042c030b4407071107500c110000c8484a14901000c001e07a0150402c0442d141d40500400072101080c9410600d00302c0c2e0300342aa8000d40180301c00001048103c0c0c0c0e1011000c860441903400c00302d007036200c510043c1c1d07110700a610000c00b103e50102454540c1c0e401000a0b0201c45d00032003102d030b155101c10307185034200d00c1040000340c0002d20b449021180d6052040142d500045940f0700040c400d0f540300d03100742c6002d204450403924588010030f04002640d10300281e10b00440303002c008200ca420603950107000c0901c0303890807a0140800300030b04c0c203480380244a40c04006801801c15941c840c494500b80000354407800700c25020501427030010802c50301c00900820031680c40301c00075038540102c40500705800d0000b080e40d40c0c001c0c82002900001028104411800101030300c021031640c16100c4120344000c0c2458400040c244040410003003980c03607a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 553566016 1250 553564766 553564769
    0xd02030906030103060b0d0c08161d0c1e220801022107050903030d05101d0c16060f0f18170d0b0d0f05070b0f0901032403060f050604090c 61
    0x408001803480306c4034041110104000805403003064200c0c0300141e8030070b02280c0d07101c09c0c05c2d00361704807842030b0303103800880c00e100e144070089007166540310001400c0107004200401c0403405881941c1a15800c03503c03214040c0d4028100080200c901d00e4021103d4050072200c5009820304600950400402c16002c001c82c0da01e915128004ac031840300410031140c00359040f0b429046001d002c0e240c2d110310f0340f4402e1002d8076040e940c0c0814030314800c00c00141d1b01281d8400b5007203038000702d003001c0007600d03088002140c41c1c029201161043d91025000030029601c1c0c131942009640c80d00c1e010035a8015554038004450038030303c6000390004030451190005003d041100582100c804009071580c00e40c4040c1401040391420540c1c00841c80708841d02401400030310005418401d80889a080c1d4407800b0320515400b034a840c044050200b0700c540600e40d8001e801c08d00100214500142d60100382000e8000c41c64607903130040c0e80e00c541e00c80521005400c1c501611354042c509840900100ca0b107603480d030600d402203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 553567266 1250 553566016 553566023
    0x1504061215080a060204140102010506010f230408160e01120f0c0902040e15040209011e020a0605180f0c0d030807031e05272509020a030c020d02030906030103 70
    0x201d42103005691140c04505025103600411a01428618500100203500c28080c0d8914906694136810140d032050080d0340c85240103a55441d00038925281c2030303031200e4480c00d02d0703000b03103c61000c51804c02651002a00003454414020010700800c915940c40c0c189a680040b1024002c0c0301c0144a006591440812a1a4441d04a84d244c00f118204250200d0740340e00f005138514000034002a0754020072075054059080822031014694a4030308220491281c1c3d4070186c007040110202e20401d81d03250301612301c20003543c01503d80b100c1060355160300b11042120303100d041e60240200c4104d4420100b128130700c404075940041403800d80d488001100c0c900010310090802182100140d401303407007a04103e20b440e801c11180240080410a070030040d0400716840b4907032122100c240ca6003868044645650005050050958840580781110440707000b00304049140c0c854480002d81e040d218402002045880c2da00000e51004001000b82000688260403003198010710406810b50798903403c4074116980f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 553568516 1250 553567266 553567271
    0x40506121f030b0c07080d050c07120503190203090109060c0807090506040806271b010e09041a07110f06160c120c0f050312060108100303050403110d02090903070215040612 76
    0x117501d80307000d5610460f00d9458009041805100a516405001d48040d074031651940c008601a4003080310342c0c1c0000c907808000d45e00b4880b41400c03088880ea004640244040c800800c0d21000c40e01c0700d0068514059000c0300141c0e180c420001220b60082144003c0c10044864a00d454640105985d5402016082043c44004152421a407500b00d5031507002003c0c01c001030b0b0300e401c03610615422030b0b040300c0c160381c0b400f00d0072880c00160310f0b107805058288119031200c405000184401071440d50400c00400305000d04c0107200701605192420028210f429005400402d5180b9004a42d00b00810b8004512814001c8a0a08100188401c40f81401c0c114252402c02c280304694100301e5905401254064024000091007a0309001d107070341400c0c800c03042a00c50340302584848503003010382803103840003800081c0c0a01c001c0c00040d4091000c030b180e04400400104d800d807455000240d000c0015904a001d5070300c001410001c60410300150303480386072402d903007d04040c60f0100107002d0015074112400f05030ba = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 553569766 1250 553568516 553568527
    0x606090f1009051f030c090b1b03040b040e011d070804030e0112050703050f010602030c0c090a0e030f0c060601091202210f0f010b0402040f0e0c040506121f030b0c 72
    0x1d12890b6058020729008202c0c0303031968807814150403e01030419038580042d0070b16419516140c002c2220004a03408941414035007520390017050600b0761034110f9074420f400200300001c4c0725011078001d40301600450124241d03d500d417040005060120041d5001000800000c00010700c1d042140240d009401d4140002d03034034a180300485400c8111101040c2091a001c18800000c2e4140e01441c4a110b0a25600f40c2903602c074a0b090343d580c0180d068900751680b000403922118208480d00e0794103c0c0e0709080100e0000001103c140c115040203900104020000c0303400f45802c441001615040102030071706071403060a0001d0200c0c038640d01070010307008280402404640e0080d01c9054090795180100303803503070705000c61203103500d03100b0b090751800309582820503003807152604d4401c4400700c0742510b2001e402186884088103660000410314180a403080c440080c00352142c0c4014408452101403000303071440c2005615620b980c5210000b004280d040c0b00600006d4a00c280080e04030780f02004054650 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 553571016 1250 553569766 553569799
    0xa020c011b03210603050102070312050906091b0d0203250b070506060d050a05010e1e070b0d0506030f0f28020108010306110c07080a0611131203171e0606090f 70
    0x4004c81d901c0208503601c006000001e040c3d001ca8607100f0320715004070500c203a0302c0748410103540d14026600d621003504603001220502030301e00550105190b0140003201001820f1300001c5c1000c01d258902804549446145030458003004d80020141100c86001e5080c0000c58440c41d070349510041c442c9000e141c0141c00b0400f40401080300b0048668801c000340035500c440c000181d11001880c0b49080050841000387c100343c4d001141d0b11040e200b00d16034090610445850710006443c0150071036800d030041c0c881204005e20184200d0700b000c11050000c00d0f40d40d01c007008030740910a86000c175042040662004134010f1b03902c91280380c1181e4000c2d8000c54150742030300a07095213109504810b4032034410058001042040412900d04040c00381c9010465501c528904081e41d20802c07494180e1040b0404007030141d8140f010034002c07076034081d203096003c00d0030302c039440d81104c241076401656044203a68641c47c04c4040c0400143e120ba81a81c40a05251a210101d5001900404560710400303032501c020b981d8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 553572266 1250 553571016 553571021
    0x20705030d0c1115070c0f1208191e0f0221090411040b040f18060501020a081e030f040507080f030a08061201060605070b01050409030e0103020a02010b060a020c011b0321 75
    0x1e2074140031020360b5507085450070f1541d004880c4603402100441d07c0b0002040030a0300d682204007030704134061a184c2241e042845070045550b002510a1107000361189894040c0c81d0100000c8030b1131030701c59041a1b584c2e200041e107460b06000c00d003040d81c000a0b03050b400034144081030b10000c05d07040d6404114036407050585503040c0201d0300401000c80003c1000140d03940b030307003607100c08a90f44040d03482207821100e5150800d0322098000c1301d02507403082c105140000d40300070060020850920075000c401800b070140c03c02d40ea1041d6400b40442904001b40402d0003001c0c0300100051001030020444001190070054030703030003006110001e000040c800207000f51268000c001d003107413420000304031041e107800000e025038112840540e140302c940b200100d180d0400703114101600b07826803035a02c001101c00e030046001e54421417400c4115501c030300c809221501c0da50b0141820701301c1500a030015008080005014904145581e403000741c882d24100d004c41d82101000d000d07440c20311b01d0310407900014200c0102 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 553573516 1250 553572266 553572289
    0x3080c4b0a02040e0d030f0501150813020415060e03011b0c03020f0601060903150c1706062a2e0b01090e0406050121030807080a110301090606020705030d0c11 70
    0x400a0825081c84c1a41e440070811301909a0161820001e4020440d984405c585d001d02540e07000d150010043e260721030141c0402644894606400100d034803190740804e00b81c800c9a0751540b0034503d04003090000d41e4104402180c0138030103400800072161400041c40480402c0c00c508030500c401810080300f8180300b407000e40590780b071140c1224110359580600501d03c420900c004e03141c0308120900310000c00c94a0140341c0c080540c0d695503490780803500b030b41100c25130800707060360340d220a0070030091000c040d03e00422004459161042c1192900407141103090141d01c100246207020390300d002503581403581c20750517002038649600251850740000140e4117203000350400d149170803650b42040100b1006070000d81c169a514001581c405c52803101710401031440c010014046189080041c11551044502c0f5074004615030021441998000c2151400d50080c3c02078180e0b162640b20a00c242c03901049800000c01301a00144800c0a08500003404040320b01d00080c0280c1c00680c1815495841400d00c81 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 553574766 1250 553573516 553573519
    0x603121c0501060504150e1c1103122b14010b090f040b0f0904051009050c030c090705120a020f03130224070609060603080c4b0a02 58
    0xc0d030340d40118980d5803010304403000c8289603500308800810715511620a0700c0c00c55080c0d1108240070104108140c5181e00c10b4030b4126000041444104101d030401c0d20390105141c003403024030b810942c00d001414241400d405045807103060070415243c01c018224490b1584c024080d601001e080402c2d00e05001401c0c0c80c1080142d003001c404004a0301072140402440701d0300040303490441c83c50450f01440103658001030b41d03640c0010100310310050340c1000e138885a4080d00c00d0702036548a000582d081412104280015103556001a240a4040c1000c00001000070700480d11281c2ca8a0480001051071140c0003003458005400404a5244c80c8643c041d01c0c01511483c1c0010340ba880c0c0051403001d186a4040700345d00c42ca080f00c041c500181090b444a0666419913900e4902d00540e41c2c540340c014080c800401c80700c050350b0384800004901960b01030100006208007505000034005418955001c0050030074034041900e55030901c0907410003107810038400c0420381403007a0001090115042000c201d0300a07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 553576016 1250 553574766 553574803
    0x1515080a11031606020607080f1e15040c030605010306080f190507030c17160819020a0e040602090306150d29010906061d0a03032111070209070e180603 67
    0x221346640c0108420b440707010306a03590483c540e5070703007148000d441041c1c0d80c0d5a400590103003500c84052090341e5855001d0046200102c201d080c40380450200d03182a030300c842c0000d030785030021300c1550782c5405060010a03901c00206490207840f0070668440c004841011385404020840380200f11007400403d0007990006600051b0355520860500580c00c1010061300c28083c2c41000c00e0840c08400c0c502054a9140d03000709005581c440440482c0c9810900c2a81d0041c0b1040c0b000404080c0c00e00398500c12441b584015807201620014145080c002505554140301e0280d200340031a01d51120113a40f10750002002c2007054034158000e550800000d40d0300d51480030745400460f4422140c0c00a01c22500c681d03442c1c020500c0d051400b20303156410703040d50342c7e03100301880b10400100703100340c0b09500b42c080540d0461680001c0c004444040b29032190f141402c048011580d44103501e00240d17081d40c040f5440c100f0041030002407001036146403003000c110760f418a544000c02e001e91002c10550805902a0715103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 553577266 1250 553576016 553576019
    0x80a0c0215030708040b0f040506011703041802070c2c06060f0c011e0e03030412170405010c020d0c020f0d0507051005030a060b040f03081c091515080a110316 70
    0x5201131801c44040c0c0f240e86850012451030162070511314801c64103c0040c00d216424040380b818803080c0303000442443c0c0b1040c0004128000b10183c1500c0c0a2580100160750390500e180c001596a465400b5036030004a802030b200c8100302128160801c070554200300f807501c0d900d0200080e1603005a03040c04140c2540400c40d03401000c015800394222180d03110140501044c4d03030156200f034505140310340c1c1c420b4000f4808070300055800d02d1084500503a504140c582d0301e20440c14410b0710b410484045d10140e46074040014500e4040c0039580034003c56182c45402c50990b5004140e030040e031102d0710b9005007540307884e0400b400420f000a00142000411000420081140080580d0415215000468a4080c001603c2c1400008aa04507101d101c8007682d00f038a107890b4000540c0001039100c00c40211841000844007451213242000c1d803140c03011803402800118003c0071142d10010b0013016241100c0c043c010440c0001c0c0340e083c040d62000402488182c90000700f803c000c88010b160300f0030a8070180 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 553578516 1250 553577266 553577281
    0x15070305060a09020301060f030f02120405060f160923090a091a071b03170112060c020a0213020f0915030105270703050402191818080a0c021503 64
    0x10a50007020100d5480364843d465803030103400c07440207228540120703282d9080070310858081e8200350110b05e11014018148024410308001b21002140d08a80340e4010b00304000717a5190302c2c1780142d004145026811341c103621804001d0820391480c090180555a2852075601c6404c03000d804074000d800107494801c003803c14005101c0a44491a41120a4600744d664031140010340042544142841e13510040001c15500d400c0b03d1000c0084000d03405c014404800301585d00403990303c540202341c0d0701a000c070042c14500700113040b42d6804881504540120061501507550051154032522071000d00603501d4141344560301d1103100300c004c0b5035000140305a040d840980d030700b8050742c100c0c0c20996404040d8200c40c2091198010440005000060b005010424091180e480981e1091011300700250b052201e4039011f002c0062540241007140d01d501c0007409429142c000c7d0340c140e21660200d1140600346560303100c0705002321010300041102182d2010f007999074a0080d410180c3e4000c0000e80c0d2800c00e6403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 553579766 1250 553578516 553578521
    0xd0804110d08192a170702030a0803010e0403090510080a020a091e03030e030d1d01210c0e030a020a03060b0f12030901020105010b0408060a11400e07050309150703 72
    0x1d00c1c2c60703122109000c14404c440e9600c0030044a40c0442c01c0001e034400e6612400240e044080207036003621801c040d0000095502004601070082c011032001546400d19000f0310070815508894060042d00f1054040e454001103c2a00807004043c09611303804c0c80001100c20305501c0c0d01064004040d054540d07600080c000c0d03241c050300c1c060341c1d030b40a1240d055021305035240000c520610004403104042140256503002c1d4403500c00c014945040313400b06040004200e000000e41002241d070361400d08140840c0c000640714075800e0309801500700c804441d000a174070199a4403000d0102d640304c007180841903a0b10032400607828401000d082640c0d170001021750340c075007080c000e05000d5840c0c9400481c00c0c0c100f02c001e40e0200d035183c60060083d9aa148a0b030070141158210984d0000c6080c40b5500c65007809601805409454207401c00e120006140a41082c02080300c01d83d0081c5807810060159120704042107070b21401c10b041c4150341e91120f503402494010a4040141041112414400d0301035264 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 553581016 1250 553579766 553579787
    0x20c19021c0b1006053f070809100c050702120f060708040302070b07110f01032018100f081e0406050105131b030b0a080303010e090d0804110d0819 65
    0x903c45048941c0319a0151941d10948881592207144c0030f64000b088214503007501303401c3ca00d0342c01c3c0e408206084ca646801403031055400201040d101e80c10480462001c02490160800c1c0c2c21050003c00c01003e000317000b074802c2c3d64010303010b15120f020074560759000300f2042e04c54058036002c40c3c00e079250240c4001c2170b034007068a049005015640b000a2541c00d6481030f10041d0b50014000d145a0040c0001c11940f42d0350000030034140764603210303003002c15500d00c05c0d101800089001000e60341c03075080c2c034603011510340c0007400d42c8548016814100529400a100c040c4e00400341007800a58441985120307151f00024072243c040c5240d501000100907041c0c1106040302e1081c3d0b0400e8086008080c91401e46990b608500e2813031181c01c1515203c01d100b900305040001001e000750500c10f8036110701508561090700300d415010741c03240a100c8031003010459408482c140e403a00f0307030080c2041e945a0074008191066644100c1c4411700070428040920100c40400c0c122320940720744401020400380c00300e40030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 553582266 1250 553581016 553581031
    0xb040e06090a05010602340b0405030c04050c04033002010b01030e0606010206040b0a0b120d0207060507080306270f060102070504062615040f0b0a020c19021c0b 71
    0x40c01c1c00b2588524150041c141030702c20640280c240003083d41844016800002103c1840120f0701d030440c3c0c54441d4403002032000e08041e071541c079030380c608140500d898050700b2100e09000d145401c0070048201401d90070340c0d0a90760700c41c0032081c450301020b00349034610900d0809000000d4010803052602e640541c0701401300602178806005283c81d56070400c2e1240c01c1203602d180076030004000540040d440b43d42d0a80c2c04854044009050842c10002c11400d188444030559180c1c001a11000c03810380411a800090410303152980c5888469559507110b404090305071030050884019a11001a601411060b00c1c00f0212004016150003c0b80c40e0340d104003528002c0c058000d805010940d802c15000d0141640e0001c960142c1e000a41010880c5268140f241046540a0000e802e401410b003a88954001d5020364006194440b02e03080540300741c04050138950600c0e03c100007032100200003003200d40c0503240750310b10404018a913002190b213200c3c1c480d43c112541c020701543c581c100079122001c44e008482 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 553583516 1250 553582266 553582279
    0x2030f040902180d08121b0403080301140603040f060e0c12011d01050705180d02040219080c070b0c1c0509100f0204030209010b16060609020316090b040603150b040e06 74
    0x3c4800601ca10409500c1c4043c003014030800080510b44880e00e040c07600031196039281c2c03c020f024061034170003640207a04102da00620000040014804a101c0890b80070021520989141802d81e01c1894038108400300500840c0c450350080e4100381c007808801c1d9030240c050101110501d071100030324000c00c50002522001d126041c443c403034130001445020310540003a01d9861600401e08090781100d508903200560002607140c111780140c403640050480d00001d4030708040b0a03014144050300b851401804c9001c258024130019021603855800e994200c0000040706540d9000b1b100740d0048062078079041e010241c2450148143c00400140c00c2145181c2c004040019002c40c85040041e44194840650f000a000e00103200600444c4002c1c42108000802d1046501c3c4a6417007106881665200030025070740401004094000040001c050302c030185004441e050915103074019134015801010105940d6005212569007100c00350409403a82c0007406403076a80c0ea0659215489040300c034a030040c00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 553584766 1250 553583516 553583557
    0xf060c03180e0c0d02070203010e06070801080604120e040902040e03190318031b060f0c0806220203191a04060b040e31050f0d0f0806040c02030f040902 67
    0x2180030301040c20340340d00203210141c5450722201c04003d80c201e5901400640d07420040780006036024411010a0007400c0054401c0e807034080e0000d08070400c140d02c91001a0851001c0100041d00c0d00f0b0600007000035814a07410500c00d11020170005c1065820094000f0314240010701d0b680f20000180640300803516013049070900c1c030300b411803c2d15001070605d010440303108140c4000038001d40c000e0705c0c5d00c0e03822407440169920350b072120410b4511242c884866a5550f0140b9070242c0c0d4405481e80e402041625282c0407403485404503c5042c401c448038400d040c1d808408100070b80f11304000f034a81d109080500f4000c118940407666440383c0c0100741503200d1490400c2c0003030074442c01415141200c1540710605103c0e501c00ea010610410b052600d41400c200d4406410f107124084c40c42101c1440c040e1000340410700f601540103240802040050060000100b501040c1e00e80c46049a40e0140c41964045411240030100381e185010740410345c4081a004200403860b2540d9a02034801016900140c106e0349 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 553586016 1250 553584766 553584797
    0x40f240b030d020a020f0324010e010905090a02040e030f040801021218070605071505070818010e190510020c030a03361a010b0705070f141203040f060c03 68
    0x21195280c2c10005038112003401e03005841c0c10006255000009025900601900750302c614581c0356941c1220211816200140030542041e03450300c1c00340109107010015414000c0003669625189600240f1454990701741c810282000c0c001c0c0c036003682d0a181050348854444141034081d4100c40581c13101481c0388000102c1c1c50724490079000310540000c018180c2c0c6400c06d0b8080b519680b092005072262003102842c414210050300c91a84200e100b0390f00c84240342000b49907007030004140d44030902140e05044030b00108001c003091849041416041c9010200110328015060003600160051401c0c0301003422030300c546011000741365004813560100f1a00c1c201c2510000100300c046100c4c0880103520403c01d41c50105124403c503030f40c3c050b0408030150b400f2940402003c000903004040c100d01c022440c0020000108440c8001c1c24180c0510300c0d05e0b0f0300301980980989000c03c0440d104200b07495000704c1164003881114054031070b001800800c1601d17404094503010641e10104d0000d84a6030012000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 553587266 1250 553586016 553586023
    0x7170a020915061c06080304030803060913150f15080106031b08070905040f0b10050f03070b0306060a0912030e12011404060218030601030b092112040f240b03 70
    0x94018520303420485007101312406240b00741c10640340726946010100c0e403524200003034002503100d03141641d07882c43d016061211074000070f8540140610b1082e000d00015002c07040b4543c07248030f8142c0c0000d25030410002e54000c0e110399403d1000d02c0da810013000c0ba0091040d040b620982c1d0003a51001007078546c04440d2944584030788501d040907044070205001c0c0c080142c00031a0000d0107160303000c1c0010b4103901c0c0c0543c0e000090300d4000c041c01560100b0003050a148081d06035065044018100b014500412002c59110061180b4031640303000508180c214001c10200001d0201c07461001950803051030060b20b1030300070700314692080550100c83c00c4505014080d0b0020404050000b55064039103903107000c003a4005036071109020316050801b0495803020400c950080d400b48180840741e0615141041c14a81440d0101c00410314148001481d041640100c80c4110041d076101c0e503495075141008441c0400f117410080601a0107001a40a16000603501d9150211190104032542c001c904040c0d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 553588516 1250 553587266 553587301
    0x3090f0604030503131103030c070512010c020a0f0f0b0a02040501030b0418110a0812030103060606050703090e091914010b010e0a0308030c090a03120e031204030605040507170a0209 80
    0x3c2c40810015103030002c500b44085429100710f00c00c541c800300c00b4000900f5604030321114200c43e40f0100d02004549044980184404550002088400e9101c0802034903072802c40c03006015040c0079080c403001c04c107951480c081c1041e00031050840500707118203c02c1c082d52140c460302340000c1c01d2540741c03609440c151045961404520706c03030b401c00304000c0d5a6410b46403001450176511403c6964005805c000500100b95034500a2069917500c5d810342c40c01300c1c22500142c04c0b0004002060140d080043d8003d0301d080d05540c0380040d03404a40d500c400300b1600d41a654040c001201900411220401c0804050b05142c000b25074020b2203a9105900115021003072040c1696019400d80d40800104240000441d0054000012a0b262400da0380114a0182c0795a008032480d889065030007100940c010858510040110b0141620881d042405030300350141d0300015040603135031b80200e0b0421108125600c01800c0240d40f1512120b02950002d403180e0f03802406074041c0040b5030025200d48031034203070b280 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 553589766 1250 553588516 553588523
    0x6010317040f0e150a080a022409090a1104121a0f06040b060405121c17060f033d06030206121806041514040201020a0822030803090f0604 61
    0x142e034600d071100c00c1810b60406440e40100c0c08003a104120341e5180e200910003d40320440041c00880201e00c1804001c0854101183c0c240701c660b0b280c00d84000b508400c84607800e07011120009540c6886c041c80b401880420300f41400c2110000d000500d03088210704150605000d45224806040303183c10940c00c010301110081c042070071160000d40380b4a031030750002c1901b180141c505400d260725080072500c1211300c1e0610350200d03170011110f0b5003a2543c80000d48403007041840c007560200399000740958400400340c10030348500c20180c140320031900d00300481c00074402c042e1180d0341c599940307070540e9900c10ba055200c949034888001c005441d00416000310421668080d141614155a00c0301c2280e40f8000a841c81c00c600c411482000b00d0100100409800750b40615582c001060b0603580da50200c0b07a00000042d0141989010440540e801041141c40d20360440c5849556a10b21070400c0141c0105001ca540d0190340307c140801401700c544055442014030108a030b11500b0040342c83c40d40da003006ca400a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 553591016 1250 553589766 553589789
    0x20706030b1008010603110403052b050c0601150507082206030b06090d08210a0b010801060c031d06220801180f0c051f02060f01152f0601031704 64
    0x100700c0c1600c02d901c08100c06401f215018241a100c1d62114140502020342c4004440903042e240d44003a0f03410440e2200013000d050080c41d02c202051040d844280521542c104c3c40f07210042000e280c0d0290048805a60340301d80c40303d0b614900c2c184010300300d02c421100c110707600302c01070008a0814082d100e481c032007400c018a502c1c100012a410004503004140045075201d109001c3d828200300e140d01c0808540b00403400b8400710740752201500c2c1c03c0350311014203203041014000c0104005500442d55000b495014946028141c50000400100c440c841d148181c003c0400140345036a008021070150b480d0400364140d0090540e907803c100e0076141a50340319a602440d200f55140004e00b5486102c000c41d204400520340c4603580c10010b40100442c0e15250992840c185510a009a042c08600d41c014500035418016504061154500001415070b46003845460076071503c258007107101603014140818211001e05091415098848400f0304c4115560003002d6103c21042e5160020f40f01610401c87d000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 553592266 1250 553591016 553591019
    0xf0304080c0906040615050403031b0201080a0c030905060705120108070e1909050a0b010e070201050106020606130b03030409020a0f0c330504110a050f090414070b030403020706030b100801 83
    0x40190180b405406290701c640d072054001440071545c0d8844040c2e25603070729525151499410080c0032240c18150705105801f0944800c00140c0c2c003c1c20b0103406c11394a1400142e58444101c041e00240306120b40a08244103c4003000079140c0e204008041001c0114001039150b680c441d0103d50b588036500441250342891000101d500315013409944a94000c6180804c01c900e0f00d4903900c1c2030004500c0151100c0d82c9007001070248140310000d603074200140f0b2008011a62501e1002510b0340c00250086100f4030380c4080300300d40d0441e107411040100000406507035031960f83c0c00ca0f40c80294042544140404c2d00ca040301c0403564002c8146070005604150240c40c2a2914030801c22440001301010070f000000107061204906c132840b405100714451203986a0381c0c40080204109001942d0285108840c0410020426107920300f1f01030304030340c0c0b0600580464660a4600c0d05203985a000100100400f00810007070503800030b00342088400c00c0e101040080204005e000d600c6100f0740d803440201d90360100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 553593516 1250 553592266 553592269
    0xb3003030f010b03131e120c2004020f030c0d0b011b080f0418060305060604060b040302060306030a0f0606140d1a0a060b0d0509060c030603060115020a0602040303110f0304080c 78
    0x115400a032036021700f00344d40c80c6980d642881d0240180391180040d408416981042806050601e03407126034140005900346039503450048008907941240c20318801c140084507a22581c041d64401d5010310040c54881c40c0160201490303400264100c9051400d00b2080409540034000c2c0220151040790b80801410090322440520351084020002c0100208000110300c442c11170030403100c00302058045042c41c036600b410f601d000005030400d0312a070b00c1c180c03003042000000300031103044a60660340551203540f40b2002904091040c607000e007941a1128003070003044856403000c815a094200d484c140c6480c881d0030f2000b00e00c07088000a0042c6007a0b90300a20f030080c46404140e00051148020840c149c88064054094002222a00c449526101408001407050240c01e510811030f01c0c0383c50550ae00b09000a40e9038a0600c51040c0008000b1044c5a45a10a001a40354a0b030096029580d91340d49180041141440210840d41806242110074041c0c0c8007004a400300c0d000c150041184510900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 553594766 1250 553593516 553593539
    0x1030f03020a0c08030703120c230909011e0e061005030402040e101a040b030a03110c090c07060b010e090a0c02160609170a0206031303030b3003030f01 67
    0x40050302580715400e0039000140c1d058080c00e014100d5080038545030440b41c58060f10b085090342c00101401e007001c4002d04002e500400d0040990040443e501b20407450003640030343d611a42c44041d410a160600200d00044550b000495144150071007140142e910844201440c406403101d0b54030074000c072440c0d44560f110724065508240020000140b100021018a150207072851010081030707181d0448902200d2512001d1030740c00000d880c280301360000d000000b6210b000d0710100074140000d00c4400d140b4030b4001c01003201080000340070207016051901c440c0e86503800661088410904100100b5030a500c91200c888503c20060010304083e16030042c032038040d02c0c09101705411489854558500c003140350340c045000f0121038440782d4403641400b0819a40e00a0860300a005c0d03840400504010b8480d0b03400c40c0d90043c0e42407000460400300389002c030042e01c4028800b581c08260040e540744501580c0c40320b142441c981804041d8481058459141c0fa40401c450750480180507070010000d545100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 553596016 1250 553594766 553594793
    0x12313080c0f0a050c130504050a02041d010213090b01020a1a070219080a02010b0d030807030c05090d06050604061a1b0312010905090d031e0c050910020102090405130b0103 76
    0x8802d8034481c1100d4460305140600c0c000382a10076600a0403000520705203607031190004034040c2c600740103518280d02c0e201d40d1740f000110000d0080d0307501c90f010010034460f001510b0706198520021b542c0d0f507160418540c0a021a0701031b0607215032905000c1e42c00e0f0360002a20341d041c5584085480310241058034900304090005000c1029801000b5a40c5807400703600700c00300e0040344211030003034a810883c90000d0840e175400d814180500078880c00a0017180d0490202030f40074000d440c0200320082c40c180102e40328080d040340c803500208600300d05070802c0b059401161159100759002c0006580d9040e41c04012130041907441d0342c803034080048030f009100880c0d2003c8804405003c503890000380824405c08032000764450130402e03070380c0c0701441503500042c00300070003c8490703180600c140240e040603180c0320140309407814440b43d5154012082c49005000756580d045005102c14a14115041c0190107580800000d600c0b8501d442c0000340c01c00080c0800035200c5070440d0340c800940c2e0071036483e140c685e07521 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 553597122 1106 553596016 553596037
    0x30b06090708220c0909060b0f0105120a02070c0e0103030e041b0305060d06150e0907060f12020f040f2c0619030503030901231308 58
    0x10782c030a40000031070101c1c41110041c4100030f000d10300055801400d40d800703104c0009a0309660b920180d0540c1c003c0c0402e01000c4a017108000d1502070408501c1d004c83c9080c032124002010824040c0c1c0c1c0070103284d00041c40c1c071450f52922111041c4550004140c1c080c803400510805a20022070f00b40340b50f013640c081c484102c0081008101403009200740302050b58590001c1c05540d03c07600003428940e040f41d8108201c410702d0703041110243c00c50164001b4561001c001c5400716030002a60800c9500035170701c4060403524200300715401070200030b2005030340b50240941199003c0c0a001800184000300140080a182c80c2e10414800005041c4488011100c801d07035042d5190008010303070060088038106440054096082c441e000d40b60806080b03440301004004010005611003e5034461700290050b0108800895210b100c40c110b0b0008000410740794054001225040900a007050 = true := by decide +kernel

theorem cover : BRFrame.Cov 553417266 553597122 := by
  have h0 := BRFrame.cov_init 553417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 553417266 ≤ n) (h2 : n < 553597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
