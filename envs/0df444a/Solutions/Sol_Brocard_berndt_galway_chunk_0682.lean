-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0682
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:07:13.459984+00:00
-- url     : https://prove2.me/submissions/52d7b6fa-1668-4616-ad2b-ce5d385971e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 122482014 ≤ n < 122661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 122483264 1250 122482014 122482027
    0xe0f010e0303070e010507051b0907030b1305150315090d0c0b04020f18090a110f0108011e0f091b0c0b01060c080c0a150e03040b1606021606050a061406 67
    0x440322a0b00004084d41400410002e000101750140015403070002e50103034a200c03141d6604144400030703500502030401c0501d8012100101c0d5a004e401c185408655400403801d6241c501041d503e00c0c0540a0041e411b01c100044091880c1e03013030b082036100d00403100542e0f111100504040d140b1800d015401400b0300d001000050051508086000081030301404c21550101182d0b143c1c03e84030401ea030220b88940c02803540030200001034081c0f06004405958207445560600b0000e80000818007034242c00034542d00c1f2041c0c0b0310210702001001041804104071410799030b11102001001e00c0b140c0c1426034031282548542070780c0030307100415132142d0188030342d1001da00c3c00c80100d41070001a0310440742d44000704000b01c402c00e020080301d040c007402a40d903403c8940e03002035844201e80c000d12204010b604188000c01402401c80c4c151005400e010b180f5403183c005520700340b4028440c40108884c0b0f02440d0f02050140301140d806a407080083e040100481c80e198243c44403000c45044d0602d03030148042040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 122484514 1250 122483264 122483267
    0xf030204020a02160e06030607050403030816020309040f0b040509070e0a050604020720010801171b1903080c01050f06090c2107020f0c060a02120a09030c090e0f010e030307 76
    0x10300d00b040e42841901d055008000101c000c0119035403004000361a02c80074046130385000d201071034204031507060240c40e0a240d03640181c21000c0043c46141c0580c9050082849140240126814010000c0040045604218005c4020200841c1c814022880c000000c0c50b4000002990300c01e1302d07025070150a059840001e50009801c0080c04640c10503000c1c0321040000d100e00400c0d4103021170f404965075444807030000060440e50160311004210202500c7d84201e00808641c1c881c1c520000f51079055080e00c541d01180c50340c004044a1180e0031060600002406200c00260410200c484001d124645803002c6060315800e0944903c0d40c0610f0107800316002e90007090060500601c040e0410413405130a162004075403004035118000340e0404040745030540c0003405081e940280c21144030b81082d40340344000356541c42141e00f4081f08440094242080c1d4001d114503801140c0c05180c1c2d8070b03081c0d1100301c0c42004c0d001c8480004400d01c9004160704205c40c041c010554810110b0300154115502c0710300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 122485764 1250 122484514 122484517
    0x9090f1707020a0f06030c020d1b1a07020106030c08010506060414043b0604080306010807120204080d0f08070c0b06220c020c01020619050a11070c0608010f0f03020402 74
    0x1011400d0440402074880141c0740d110848009110242008010340d24208001e810390394030394040da0454104c00c0716042c6058203c00400e150322468241d559282349280b9020103d4000350405503040d12002c000c200c0c48a50541184003903901c1850300301c2c0e0440c1d45c0c500349400d8404c240c039400e6204d5410300080c44444801e010155900034020300103d081b04000d0105003410b03d51079000720380d2020600302211170081c001d850b1a082000d1100a24892a00d03441d41307502c0c5c5c0005488503040001c010b010624141c412020803c410400d51003c5550700e0b680c0d405035584001200e4101c0100c0c4610301e980155a0250307c4083c4200d105480781010030030590b0710342c000080300810b0036034403078001c034011059211445001c50b0002a09103000a02c000350a801074901022800c1b050b0442d44100304011030320040b142044a42250340d0800b282d01e17260318001030064002d0b00c0c4610032001010035482c0500c4500b00d042c0301290040d480300c07144d90740c0355a51100300241034000c6211340e800000342000141030690 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 122487014 1250 122485764 122485793
    0x9010302071202010902010e10092d0803070507090209090a0e1009060b0909010e0a111f0c0b090318060f07020d08031009022109070905010609090609090f 68
    0x5001031074003801e507071004000c940079060600143c0d5130344c4503d4115604010411500c160844600589130081d440080440380c00340a803d502c0e0f200c640ba242d41440f01c12403a100980803103c04000e52986a0f0001690703a00001c0050366039105a44000892040a108030f85054402034261201c031358070390398108041c100da246894200c1c4030700700c0e10034100d40052082480c030520601d000304081d17604d002008880c01000c0e240c001664900719400000602c0019a004825800b6500c0c6280f013a48000041c0ca0b10f0722000303d00d04c0c01485850625507650711644520040d480380440d100720b510780341181da40e00d005078121081c982881c0400d4005900d0b108006d486042425034078a454070006030f0128210400254003110065804003c0c8050035500d21080030290045550850a003040640c04c40e501a05240c2010004640080401c00b502c000303002000c090014848203000b1540e50b50802405180ca5104220742c0074646800842d554480303010703036610305805c204011448100787e21203650586490 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 122488264 1250 122487014 122487017
    0x10c0f09030212070b04090c0e030102091023030f0708090a0201080703090516032312030610230901090806091b010c15050106030c050921100509060103020f18010b0901 74
    0x103a80017403491307100310042020f80748802e07020410400c80400604041d075105005446640144240049601c0c5d4440420030140c042c50b1002d00c00854101212a2002c444205070720040d0000c20011aa0000c40700c0ca170288070780d55910342e07280d13031040c50480e10740015003002800181580d0103d25000c0c42900115401030243c0305460001c2d10700743c1947e400c80e00640c000c45c1c01d43c1c21901a045020582480750080011302d1024041d1140801010340b0a4030004081e548100ea802940b50b6aa521800007910f82c00c02403210800091040c203042103040d0000722106000a001c030714041110440441d031140a80f002c00000c00b02c02c80705550010307410103503d04181c1001007440c10b0801246071510189140010b2200c009281d504041c03005003138501c040114018000c0c100f200c1c2d29a52250007031601c000307080d07070f0307880c03161000030f0b00e1107818000405180e8480c0d030b0509061003000b40012803998100c134400c0380d4000e01c244e118014000034446000550b54110103c10042255641c0302c4000c00e1000d405 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 122489514 1250 122488264 122488273
    0x1110030e0106030b040c0b0a02030f0d060306020706140c09010509040e01091a04051b061605011e0e0f12040e090c0d14010c0504122306040f0302010c0f09030212 71
    0x800e41007030840300240e0040d0342e400300b088203010500031000b01d40c001030000c02c8012403a01040c82d9000c0c0d0b40e48034607025112002d40015151080303680350343c8944051030303010500703550742c0c0a5400c144c0045c040200d640716181d001480401c0e0104143c00440c1c502e004180c40d00c80c00c14110008110003019841c810082c90b549841c805400141c00c22807401c041443c40104012508240c107189242c903c00c0e600d14046010307415401c2ea0a81e80341c0d401e0b100b18401003005610b042a0f24544240175000754145200981103006d00040440b41d680c1103480c01b00c03d5034007181c40035850351440b180e03980640c2900004698080109001c08082616541d03070200b180300865856170315200100d0041044030390142c3d00e80c00d00e642000598082809109114082c034a811070800341407801405005902240c010802c2d841030050184a42d44201d44002170740026058440602e07250819556903d21120110011752800c08260340300c5004200f017800528566413200c042c2415942800321420b502d0a608000388038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 122490764 1250 122489514 122489531
    0x1051804020d0c0e040c092c010f020d090209060a03031b0302190609020414040804180b0a0605040e070810030b1906080f1006030b06090601090e0106020c0a05060304111003 76
    0x143d00300080100b41003958001d240c40c1c03504011400800981105011034244100316500284d440409158807007010000380b030455107042c04038010240180c42c50441030002c112015010f00c40c2e880214003900039510a0204eaa0b05400c201404034a400010040788441079a00d140b03c501d40300c1c90400c00d12030300455001c820446c01200d050312100404555103a00d40b8070000c11400c00380507454425103d401c4490590410360343e00c1006001e617000c4c4204640403110400b01c1003400d9008440f010130050014420030751281c40080c0340c4d91190088018914440700400c4500d4440c030902482102000e243c0e035405801e40e03413011201000038011640c4486606031107201801c00780f1407100142844e600814400008031603182c2046c101d52444800300780b130700320200041780c06090382e103600190456000c000c56851200580b030104440d0004001d50315035a00109006400264400c440e000840b605131100341c2c0c5500304401c1d840103c4004105c10041c3c2d13000502820707c1420200002460f04011480740c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 122492014 1250 122490764 122490773
    0x301061d010b0f1c0603060b010507020315100b0f030108060f010b070305070312240501021501030b040218010816090207020607030c030e03030708031b04032019080c01020d0801051804020d 83
    0x1c0040c1d40304041a07985c01c001c00400004c2e12514140741001e007131443c1480d4103a00025240c0c54000b61624400410340c1c000345403c2c1d0941102805460002585600e482e01e2014461990f0001d00a4030000d04c14040807400c0c041c0300d80a11030407100315080d170791701d014410740e011100ca41040d80221b0a000981000d010b003100c060140e04107505600504855032001c4030315140c0c1d810307110b40c06941550480066108030252aa4810741907903006034841529860f680f01103910b1009144803000704440240003c208030a021403072074103251020600c04100c6450303507556812407043d480001d602c0b402c20800d4038002400b5902c25401c1c14043d00740000010b02030004a42981d000c0301c4101d40070800003082086810385403c059880081c10040303d4242415990380480031066511140d00e02c0f0221002e64196175500003404040d154004000c81c162507407181da141e070703c00440c205540176000e01140884458403039802641220300c02002c44d121901640c454180e42500984244c0c1c00101144080c00480c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 122493264 1250 122492014 122492047
    0x910020a09180c120507050d1503021801090b01020705100e03161404140c0306220c080103030f03140720060c03010e0a05100302120f0106060203090301061d010b0f 72
    0x70b440201000c41d1421810500130031105195510a4990b072802041c4040d80d98420251070010580f80000120030480c131617074011000d22075000079403101d1300c22142014070a100c061241200e40204d01800f08001590040e41c94104078000c030394200e00da0303101c04441ea40c41a01680324410003d0155014200c2003c010000141140c010311280302158520041d2400e092146180c620521018816141410848191544006081140714101604242e030302c10304240c1b8100c41c0c0c001e20340c0301000018510200542050000d01c070544c0810b03d0301300c1d880542802405010305056000e44401846da495000c01d41e450780b019881065611140115021048420230109020b2207a4104840e100d40c0b600ca80003582d01750050480d6075981c140780c148450031208510701426264100c4000c84204c42150f0510301d80100000429215803c0010016885401000030035100c14168003d0042940321030400307004058508500c0d41680034000108079074003d190140940001407070300d261a0460500300810036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 122494514 1250 122493264 122493299
    0x602250507080f0102030c18060d0911040b010c050604030318080c1c021506010806010c0803070c0b0703061a070302070b042c070203090d0501060f0305010b1003050910020a09 77
    0x40d070303004120611101c1030410503000c0e201c103007600075451072411640102c8680901c441c0000f540c0381c1104a0f407081da03a460309450300e01061035002c21441e2428142910813911111102e4015072600d100c0d0891035100d051a5045c0300e82007030060180f51141e607011001024003844e62080c44201e0320f003080c00211005c00070801e0a40d5140180300c2010007040c0c3d14005044080007078190350000070282e000e030800004181d408082420000559614600141c1d40c0703001d00d5800501800740002081041504250720085513801100030718119510920164100c60b006c1c002c40715280580d001c1d000005000b407006002e40b0f84203206a558040e5108120b83c4560055040a035401200b52441c00900303081c03a03004034406c40001020413260601e082e020303440340b01e1000624016a641926003080c040d00350800401008000e9081c400c440c0c1d203040c400d0003000004401ca12544000c41114510741c0301e80200b80c00380421031b029151003c1c6900c0140000e50060b00c00708140090248001100c2e5401c0446102 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 122495764 1250 122494514 122494523
    0x2a020309041d0c03032b0b0d0f111207090f091a070f02060c0a030902220f06120507210f030f020f0d1d0102010615030204030213050c07060225 63
    0x400740010741c210f091021000b0401e010360710a008040c20344a251074403100d5240012015121000c42c60001005441072082140e004056000880d04200b884002d002071107002c2d00d0f44809505010303040100c2e0202c4075200024943c01000d090019180c0b5a1060fa85040e100100003800109565481880c4e0103460301d007150a0751203810800388603040055120001c09900c05804245000c2c404400ca5002d200c0d001400c1541d5030403c0c90440d15480500c6d01c4001c26036420350943d501c1d91a11001500410a10400b0141401c80c0021038070b00810049941c0e582c05000b4240f81410005200040300070b0314032042e4042e43c071600240115240851410106000c0c0d9541a0039901003030010b03240c58405d80e080051640150104d040a540c00303101c5e04030711085110000c0c03c12014a00403809454550884250a040781c0008007016401d80d004000f02c2e8800e4032030030302d8040056141d000711401111141141c3e00d0820801000903d26030003050040070344640e884000f840b800031140000c0c00f8890494 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 122497014 1250 122495764 122495801
    0x62d0a0806040c120507090507050d0e0f010e0313052205090c010e0907080606030a020c03161101090f0513110c010e160f051e19030c0501032a02030904 67
    0x82031007a83c416480260110f0028a0a2140d440c1d6803030ba6144c10340d1107030000065807800418200b0f441181120351400180e1000c2c4006041404ca043e140c070248013985005601c6c00340c84214000011040d113850300310f00c2c09002e071344620381001d0104141e030684000d1180e010802c100c94082c5180d104003400344682c20001c080c40c020180014242d00454076a66104600342e404000703005138050300e00c540c0140181d92164907616a001201c0290041009001da41d000226900901e800c0280342c0b15002c500481c040101c810b145001540d0151244c005c3e011807081054040c071050910044012980002c900c00203621a00e410242c44550091010301c2104c3c0d450f1a0700e102c0e900c10400000c500c0080406c2500542c45c64034100200c022000c3c45520700070560f08014100003030040031103001380c4201800e1004059140c9400110101e039500045030403044441d0040f03032552092140070300003084404c1c105602c81085024190105881c03203030200f14402000f46070f00c15143c1c1d010302980001e01e0301c00394 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 122498264 1250 122497014 122497021
    0x905190605060d050604060c1b2004050f01060e0a030602040b0702011107080d030b060714030c0709060b0318070305010c03022d190e0306010f1d062d0a0806 69
    0x400da03007010304128803c070944986200130601c089400c58006a01000c00074514110740000e4a100e503101484425030101400058280600e05500c041c4c206503080c0452480380c582c40403c41211019180040b9034107070000144616405460140d070f400d80700510310850030782d4a60ba61016070f80719800144218201040c07800071035801c0000401d141c5001409440003030b003088030965580c0c411f9010a020161102e0720340c0d003261070b03010031141e009800075614581c01114244285e40d030b50002c801c01c9403a00c0303040d0000940d070101c1d04c140000d0390110040145151544042d01c8115203200580c000140100000000001c00921070309034140c403951005611100429031015103164049a107a40303045e4802021300340a0820b5040340d18050040c0029400e03010000343c110380c104181d01596405d48a2400080b030a241300c200905c2c04c0b5004c00d0030540c850100b02101042d0942c0503100d041e04205402c0c0b45543c02880e2000c0c81b0342c2c01010300307190f0340740304858400584040000d52045200350406000e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 122499514 1250 122498264 122498273
    0xc010f020d0c0e030c0609040b030303010605090306070f020a2a0e0a0605010507050c09090a06050406090b07020c0a090c03021314090609040c0308090409050615030c0f01081801090519 81
    0x4007030b550800d03401c1c60441034003e500030a4803042e04501444c482d56001624070390b0b0350b8443e07000e210500800b0f01107170f8580d0707120300003d8800c0c0e00c180c101c10310900c9a6000140a01d20404803458655442c3d400752540042070340d6501c031f44500d040102081070180e1103045070304100f40343e019401401c42c00c5007102142041d10443c000c980c001d810180c10800700300000c0c0041040040d4158803010161030010095491161039420203595450040116040000f84824000d03180c2000748514018401c11003581c45217001a640d4510080c4100c2d00804070010406c19080240d0203201c06105904026140c000c2c061503160b00c044154014102c8800820603107109410a101e41540c0403070706480b00100341c141038a0340d904242080c440244603100014076013080361581c3d0481c410700b075030090032901c072070610942c14103070010390a40080c080d1144900075419450402d0350440944d0040c1c54000302a2600040340c3c85003803203d0424203a41d0b40344c80c0d24400184007000840c062906880300440842500e00c0d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 122500764 1250 122499514 122499521
    0xf030c080712260c0a1112070c120228080706270605030109020a0e04060308090f03060610080405070b0f030f010906031502070c09020c030a030e161205030c010f020d 73
    0x30f621000b81c2005511102c141c440030318150b0044412100d03951a0400300c8000c03900903049003c1d82043c2c0c0144400c12804608800140813410f2003000c42d0032007191aa600340340510104d500c040d40c008008100c542d445100c01c07880ca950b00d18075101a418951315140414600f84032903216200250098403844104010f803142c42d4012820180741e0008107143c103030006c0036400180078242c2c0c480c3d80080c0c40c40c04540034083c13401481c20042d20031b0194642d40e040c202101d400c0b1001035409030152030200641442e01103003032441828010b0002c0102180c0b6442124152401802107805124196012422240d60005082c5002c0035000703140d5240b80c0090700035030007031040c3c1c04034a105041c0101400042c0180650890740030038500300580342c40d041d040200344c900c00e50780545951880069010300050f4040000e041203d4192000e00c29644407489031550fa40c3c03c07a442044910317000310140705030450f0b5990120914003c008a901f00a203482003103085841d00000001d06640c00200210700031020700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 122502014 1250 122500764 122500787
    0xa0f020c030102030423240103050d0807080c07021c060b030f06010b04060804060f06060518060418180602030906040210020c1f020f15100b03010f030f030c080712 72
    0xa00a60560816544403103004c100c036200b10000c2109030a60091b0410100407240382c82000840411496807000d000803c1c0101c02c1c002983d04c2e015858200344c601d400752a0040c0203407100c0c3d6403d0f02d00d503101040c074041c079003080b04100d03031004440d590612441c155001511856000da5000162402220300305440c0ca5180c026661041e08407000420141c00d801040da402c40c7c0150500220660719450001c00400a5081c00140103161910119442e039200020b01510502541c0160b20741c00302d103003046200d000d1031003110013146491081068220300368000601800d9485401288001c2d02d0b40c40d00183d810880d50000e0651101d02000194601b034101600c1020702c60015140b110a0000424850080001c20002c2aa910741c1c0141c80b49100b0821030104445c40001d68911860000390031242060980d100c41148956203804500640b8460413241251411100800c1c0c040c603680c4d900c5035000c04660141c0910410341c1c000408540038030018208540704540400c000022000064005c44122 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 122503264 1250 122502014 122502019
    0x4061704080702150909040c0801060f0e011203090f03110f06030c2215080906010e07020d0327061d030c03090d0503090a0b030a05150a180b060a0f020c 67
    0x180008034250000320b445203a01640c05008040a1151003c16031041119550f04990000104010f100148502000b5191030f18024040c0554803140900c00b000c01c2c0c040c03109044442c50040041c2415200e01e03851283c86410f0040030b4940e41d0100070160040c5920598004495150340043c61400004c11141c1c0d000441e2602e08504000d183e904203070150780d2003915003010000f4010810202111a40c0041c500e800e982e180d40e940c4541c009240240696690050303124000000c83e46141c0340803d5072040c00258010101024086002c8000d8075074401c3c45014410034005004802001c001e9180395607000d02c10116901c402001316500742980c040210340303680c00901410944040c040115522103004581d07981200b051810324600b54800c000c1120343c445640c20000580c1c0c17484401a44c8201344600c0308109503514150136004220000c40c4603a03101c003060700280840c0100312140d04410604190002d2034542c15004158107600502214000c12014100040340c0b640c10440300303280b0a0203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 122504514 1250 122503264 122503307
    0x1101050a08010905060a08010615120501031a041103030417100510090b010e09040308041406011a16020a03030905041508030304060b060d020706090215070c05100903020301060801020406 82
    0x400c2801040d04106004200b491929100460322560b1480d0100c0f01a0414000801805503038020b0710034054241c0d4200c401042c40300f580803001140502c5214126030b04601038a0610b06044480341034000700400071101c1e065080c081c1d00d96030f10708001501c05400c80c2d9101c81100c40004c2080d5140004c1800072890b0300b4141010400d504050445082c01c81c0c9440c1d02c0814440140320060300c0c00c0c1100030456400902d034808100c103140e40320440701d0003203020704200d01c40b04010030400d03074850800b4000c4540402c41200e0348400e01c0c418000030100e05034403c0142c408002c00b503000412200990344182e002880401d410b114900d020b116a01240a01520b1440503526200c511074980c000184060942030391410b040500e07807904000c8401e285c0002208540e198110306c3c0410050003170350001d034080c0c0e0207610b01240582403032040700d40203504440e44010071440c0c502003000172040c1c00160410003030410b0001006031424024070700034022020015860700e0a15000501d4042030b680d1a050140c2c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 122505764 1250 122504514 122504527
    0x8040c0e1504020c03120c090f1c020d0309080a03020f060a150915050a030f03030c0302070503030f1b0a120c02072714090c1e0307120609051603110105 67
    0x98150704051100d0300303880150f00d852000d0340b034030f003580140c030850070300f11140100300010803409400800c1402170840700403030003240b00303000d00000b030181d403142c5c001070103040484c2c401514008404000462191429203516510341c00d0203410108891401c80250b0302202003c000082c2c03c2c0300b01c9501102000c0c08200542c041e540302a507038100ca104192101d56141c54114046040c6004540905000b9045120b215600d15000301c50803100c1d402030b00043c3c03504060f9000c5074403d00031103940c0368001d030095085403103641180c0818140a042da880207010f07400d41d180911141030103003241c4145602c1d0000410326040e404001d030385140170643c3c2103401039803041c04101c8100400d402c00b03c40c181440300c018958844a00000d0540307055082c0030401d00820400c0c01140098803000340002900c0c036a80450f201c0740307283c1101610518083c4d05030404041841040802a00c182e480d901a04011030080c8550f1600360402c64040c20030b0700c040d82c002c4001c2c010300030110041a01c1c4e0900303181c058a4000d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 122507014 1250 122505764 122505781
    0xe0c040b1e191a07050d02030310030b0a0608060702240f0c1c0f02071203060f060e1c03020105060a08030703050a0c030c02031203240a0306110c0105010608040c0e 72
    0x1842500000c2c45035076865484244441041c40800c00342411601d1000c0d090768035030022a050704049401c4035944201103144040398400b209513130041c0c14030840c1000c02030661341c0b007400c49030004107801012580ea10000070040401c02c003040c0500c4070780e005806000d01032017181000920190b02d1001468030802840310110002c4140d42d88a00c407508100d07102c000710a04140862a02004030400c14104401106201040d40c01800024882c490095010003001d2040d400d0b40d5251041114068050004000d0103005a0300d9803400d410041824000f030f100d1790085030500f40800c5003640142e540300c040055508111f11458081c01c9200000c6050160755079000380301f4802c0c10610003c01484620107404c05016440003010558000c0946e804071a24424a80d16508220766101104031034881c0088042804035504c1d64800e80981501a41130554488070302401106407550ba03036202c1000315100d180804e200d00c17030203041240e0700d60015060500342034480c1041c54102e404007009110900000d0b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 122508264 1250 122507014 122507059
    0x30705010e090f061f090e012306030c120109050601020106080f0a030c02120f1b04020406020604060b010e030a030906030c030b09070c0c090e100c091d0402060702040e0c040b 77
    0x520f004a0206940c03840f010640b80c003d03d401070503050041e0b41c0c902c0103c1c1c0d0415400020344070841042d00c0160382e00c1010b00c0b28038030120356001006806041000032414000c1c001d5a101e0080c00405280c498254541003a94409922042400d559181030003080c2d80d0a0045c10028074818000345283c2801c50081d07600c804508800078284071464110904544410f1420301d018070107203080c1d4056088507043d0325281c9010040002980101005c0622207150620a0341d0660780c0950092400350307950350b82c5100505524074840c0c140030642e5000c40b0903540c00c00c500c204e90703031181e500c4041480c50f004000d0140d0741c101003c01c05040c14415201c50030340f506104036601c0b0145103400354030300741c035420444000980c03070f04003210650600004046813140020701d0308031519012003c2200d51401c03c01142c1c0340130507015035020940f000b480316554600503040140c1050004142a2804a0550025007140c40011030480140c000c1e001d04044c615252042c112029402d80b0300b802c81d074074012240c1411 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 122509514 1250 122508264 122508271
    0xc03061b07051f020903070b04120b0c160c060e220203130c09090c1a09060315040c121b02060c0705010b09040b010305060a140705090111010614030705010e09 70
    0x140c80114a0708140031040081412242032100350100c400064215040a540325400c8107009118031800003410074620710803903089407a8000600b200e031040e80c1c0e5044000201601e40d040841041c032100b9503d0f0824106450702c0e6208002049000c1d1070884041c21880c094a56030703100742c020058034100810b0500d03e4004040240c54010f03900e40d15640909224070301040043c021740c0301c00c8000328985801e030784400017082c021491003454943e9502515003468410b1007000b134001013030080c0c41560422802444c1c01041e00003248083c0e40302c0401190444811100c00c10000c1c3c0202100b045041062054102ca010000c4200c0181d81e0341c0400603681e104003a08a207841903000882c1000d00900390300624480d20700030041251070030303d414049074522080c001682c050003500b0100d03865181d9407040042c0010300303407030150142e40c07403281c05d80d250703081821014144410b104900c40c101c0000e220b082e01802c0d20000c40e60000f1545c90516142c11680c6d0011810301490f800c208081d903640c85a010b60 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 122510764 1250 122509514 122509561
    0x10b060708090d0f0b0717040210030b0303040305030f040e0a0b030c0f010c02091003060b0d1a0a09120c050c0a26160e0901140c0909090715030b030c0306 68
    0xa4a00c0c0d210003145100a43c044050000302c04040301104000c20005c2c0c0c1402a00e460b55105040221592402040082658000d40c0800840d414a10303490080d08007410b150700003801e03030b401e040d941e84416007942c0c091445070442c018002828000d00001185054005031000d404005120711036000c03d684161440b08030348190b60040b80900103038401c0d50080d5243d035025103c00c0c002e040c4544203211240803400704460040c03c200c040030190500c8401c52562540224000f24480000d0b00b50580140c400b901c1200950b03111a030540c0803402c0d200024484040070f5803100812103c50034428284018410100d00c40c1f60385038410080b00107950301c00f189c5250b21100448041400c061102e14040001c3c030a1a000c000c2741c100012151910100248100d011100901606804201001c0300b410200c800303607403480041c480b294450805804941c0d000c01c00800703c4007429296807010204001e04030302c9000298a83c0d8404919081c1484140480d410944c010321150804c3c4454003142007211000c9038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 122512014 1250 122510764 122510767
    0x1e040e041407120803040c0905130602071104020703020c1f050406030b041503050706080916150c2a09020906070f150213050f010c02030309300307030809010b060708 73
    0x4086140510402d00104052505100c02089918004407503401c1201c05a5412000c29000034241425008841c880d1400b401903112900159035480001d4200c14025194190505140300140e1a148004e04015000790010104060480204031403051810280c000444000c0b424904481d044001d903819a00340c2e04000c03c0d000b0380000030038005d2840d0300c5013902c07030b0074950000400c1c0305010581714152410f5a944c100d443d41c40c45011aa035142841784c0f1005009081010046c910380ea10201071300d580580713000603480030f080c0c80700d1045e01d0302e5880c050108c5c000e80e0249a919541196108014101105d00354141910040040d80ca40680c0e540946034016600900f0104150b1b48059181482c44003021521400310b003008030780c442014010700f400b402501c2500d807a2580608040c003c0746600800551400040c40c040c008121001d0420400700340c65500072407c107054000301c19204540c120f009584503c03880c14002d20083d00a00044c1f4203901d0711180c00103503100c000450b001c66821a0346503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 122513264 1250 122512014 122512043
    0x3010b0f0f100507080403060e0f0a03020307020f1c05010203160c0c2106060f060306050913020f0a0314010506030601050109030305030f220302070e0a0c0905040b0303070f081e040e04 81
    0x583d040c2c403407600028000c20300000c010007000601d07845004140c07044000c80d01d0350420200090b59a054a000140242e070081c441100145480030408a0f4001d020742002c0100c502e441301c0c0344103e8840c50040710140d40210400041030b00c403107a49680800e4910b0500d030300750300c1a252038031450032900403000c4206080c0d62114101c01c041e41400c10640d4420b008001c4c03165201e41c016280c2680d0b0080030b001a091090000c0d4030300c3e103001c00c01e0003507041c0a502407a4054035800c004146e602c0091142d00010342caa0000086a07811003041c01c0d1303294000010071035142202c2018100302d4140c10840c1845401801400032030350000175a50302c0301980d01070007000c2e1203008101702820640c1880c450340410201d05102010b5012500d0703c00c80c1d06844bd152883c0d01c0d44801c460035900110285400540e0a03401006a8a03045c0c001d91941100641075914041c00303500d69038000045a8401d40d0240000118001e10b44c60700040718280000b42100c16003001c0c1400881280c0c0403014101a048c400a00e115 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 122514514 1250 122513264 122513267
    0x504050102092107050406060806010f030e010e1501051c03050708070b160906080112030c080409020f1b06060603040b0405070b0301090c140f0712020304050d0f0203010b0f0f10 78
    0x11100c02c1100140410700d803651419440701d8918901500601c0d500031920006042e00301801280c0554219031140d90340f03652400011140745200c600c40e00201501d404860001c0c2500f8400c04c4c0206001402406d0700c6840e0568140c035030001030340080e002d00ad02d21100c03000400104600751401e941858050f5a44641d81086c0b651030140c0f44025103a46803e4042c803940780751005001414071250b44070024507550340e100a8034180000d105100d000d0340c4030844c030f1001034800c603050144103119504172420561621011130490b0842c09110480200014921446c11803800760545898a100014420351414001040907400040d00080c002c0c0e02200c00700e003c109080c88441c0140010409503501e80d03945d4021100030f0103140e900d10010a150b40075062158010b142180c15842d01140c0b9149480c0c1c80b5600d1040d50b0882500c000d045000501c0085241d6030360f204d1032490603025025807401e00c50b0900400d0b00f12090005d0a522501e20203a04c08000d031100c00d40c0f80044242200c2401d0542c104000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 122515764 1250 122514514 122514517
    0x60f0406141c0203041103010b0f01140c0712150902010f0e130e1018020a061103040807091407020102130e060409050111030412050f0324030d0e030c0a03080405040504050102 77
    0x1002c03020741500002845402496000e1445140680c1d5480044010481850308807610039110503009101e1303400d11300d01d03075005400e1403400030b0448070710904e4800100d64190603c2c4554016907640e440400e480428051814145101800200400c014001c1350780d0011b0504001c2c100c2c98000d004010115011542e1031240210400030000c0041c445a40d204c011513489420845420140341e240881107a03240d02c2000c0d03204a144d1303001c0d18100c0d415082c68401d0f00d5215482080044500c401c010104621405002c1c1c1780041159450104025010035818501d201c0d0080c1003800f1a03105000c2c0c000b0509500000d08103c0341c0014449003152101404900540003160028100e5800c044860f00342e0050b48000354411401100d1880c044a01786008035118401c1c080d004045290a1010500c8420110300307030200900250341000c0000e000c48042400c206d04882400e000c204407060071043c904050001102d4004200d0310f02804505580c3c07156264080c0b070007800d000b00c0e40c490004081107404d60 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 122517014 1250 122515764 122515777
    0x5040e011802040e040b010603051320240d110313020d0203011112160e010c062408060a0b04060b040b090301110c030a1106070c02100905150c0c060f040614 69
    0x244c4408551078141003606041c41c00313105034800680f4000025503441c00c81c9150300000742d1301280510030301c8865000512042c62000219600c014000707440e6456003180e203d004075485011207600e45078101505100d003201c0400000c03104d0594100100a4002808007a88000300d80c1103400100c1d8091a00100780100810080240b846800060007091403841011403407060100c50301d23003a03100195501c01c440c40c032a80b42d0f4807804190004001e000158403500700411051304000080c1e811050803250b2034020410342e0041c04150000002d0100709821401003c0340001c060304c083c07200628000c0c030700206200c3ea201c0c5d8204003001140d818602d036003e4100100310456401015241c41d0000c1c822501e0390311180b10100403a4000030b01c680070007000315a66100c1c00150f240c414500714150244000d2078a000c00030420061a6200440c01d03541d2002d000700c04400ca9402651904050b40e0a1840c00d00d081a119120365410701180c0d0a40c1e0105e0100e800351005441c181c0920013400b40380c1c855600568 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 122518264 1250 122517014 122517029
    0x30f0f06050a0b0f030c0f090a1b080405010b0406080c060c10020c031b0703110402070201120c0801090b01090f150c0f03030906060501050c0703021c0605090a020108060105040e01180204 82
    0x202400310342c80240d0041c072034215040f603000d100920b42c0c00c00c0507551540d02c00940e801c0601340c4007020329441e201c003540c1c0d44100c840c1ba0104200c0c5032014070004140c0420502408110b6400c240024018240314031180d41c1400d890400c01c43d8240100c081e0707541008440e44c1d110f0360b400100b0000c500d000f0301c41100080214081036480300103015009840390040110b400c0c244010354103881d80a8000a1004220380d0040501c1a0340038004060001075448880300f41e06210a0f0440390540c01e45e148244500c1581c980e50b00c10302541070040950945d11082403c9040140301001440807103103001a0604446902440c503004460201081d58140f0148002a04000341240098140741e0540c116210403031043e04100121501e80d80191180e019101e80171501d40e02400c824001420009101d042e640c0318071202619082580c1d07503007810f03200d003240e8180040c0c0010003000d0840d60041d00850300100d00b4202a4209428032850680348201440f40740003500300d01460300f01c85209541201d0280c5041d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 122519514 1250 122518264 122518271
    0x50f010b090303221d0f01090b0d08130806010f080c10020a1a0103030f031e0f060f09020d0f090803040b13020d060b010f0f020706180521010b03030a09030f0f06 71
    0x2111882007244840b441340c5800d01c017498420200007001c0c000031512a12181409860f281d0070100100010f01e2003485031171f00203007040304060200740c0a9001c3c21a03940703a1400287c0c55420054810300346041030380b021611644a881c180a102c10204920300082d509680302071981d0307030208007241360034107602e0b000e00008081c944500c540c0151040711410ba034084d403518501c0b2000302c0f03801c80c1141d00e2480c40c1843c2100c0008a00420b016035007081a8009614202103441911040301c62180d0010f64040d0025070744c000b03280c071501021400390300c1c0c00740d030801402c101061240c2c0f988101031100400041c0030710515000610846007075560030300d6480e0042d000301e0b00000b0b00d10700200104506070000e40442e212260982d8683c0c07107120700641d5200260701030f03c2e50364a016002d40382c84400401c010301d412040c0001051548403400c3e0036038203900c40b0f613002460180302c11a803400c44080002860003600100869000c107070304014280c04070703688454141800001401d148020303100d121401000e60b401d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 122520764 1250 122519514 122519557
    0x203150604170d0807080703020c072d0e040b0606070f060c170f09031b0712080406260c16050a0606051315060804020109031403030106080109050f010b090303 70
    0x8042010184030211003c40f0000d058580003a10445001c58100d4001703070b008000035100c0d601c00c0e0064800071008100311844581c03944242243c03c030600700d0030307007501ca40814801400c1801094001c01090000c0c401e0303c003802e1a4a880c5021000241100c2c060400025440d08110521001501050f0000000c202500303690100a0100130126640010b00b592100410098000070142c113004030040c100843c0f500b48081c0312942c064084910f4090507014101c400180718400000100325144100c03c26903546003080d00103403001208a80c007801540c80304070048031003d2001c5040d0b030000b0708211800c1e185c2103582b10139094a40c03240402840e90080c003013480700308036880c0c0000007900c0045900000040e0008403c400303d55800007070011044890301c040054501664035503401c20f00603d00402d800d5100d8a48004c04a4440041e010542c0000010418580d00041e1140545a01c400174002820502c1c0c10140499041c01050308900001600b8080c1d9070342081150014032010348803118501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 122522014 1250 122520764 122520779
    0x908060c030a0e03210601090f0b0c0d020d050a08040f0204090b18030c06130206040b0711040614010c0201030f0209100903050607030204030b0f060109180e010608060115030203150604 81
    0x2001980c1201c449410b1040300d000c1c01e40088103588001072280603482c045d112000711650340034405000ea5042c400c03034010200700310940240d1100540310601343c86603184c1c11030780300c07600e490352410301030045401a4980001a0f40d02208441e022705491525455a45450924040703800710014000e5000d0b207481507090400500082d100e11a6002e246480c40c00386040300e940307482e80b24030400c03002e09401c0400000c20880700b902900031594005440300d42030607120720074801d1a85c05400160f681d06403203114410503162030b01030080501508030790381030030b03040a8001070f010b0b161a0100905243e2911051411111107506491034640020800ca461920415001e003448080d4001070324540a1640003c145c45c5c0030340229000c5136807107400c10300c456582504101d000807015002c0ca04004102c203000900c0d04100c620001c4144180d0303800508040500b40c00e608503082684045030a4001000402c2079200c518003d40812140741409641c0342d0720107128210410210b203485501860110f404a03014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 122523264 1250 122522014 122522017
    0x204090902040e01110d02030405070509040c03060b010c020105030123040614011815080703020705011b08061207050d08070605010306091511030a1a030a110a0f0e06100908060c 78
    0x600aa42c00c014080c3c45100e0582a50498440300d540404204810480c4850542c010341d0701500036001d0300d041d0b0f904c840009000c0c14003980c2c160750700f4011000134400c0c00080d108400b2000001d080241404100c1d80c006841404144a5601c1d00070044010042d00c00141c01e9642c0d10755070092042002c2916040300301280f1f04440d69103800540220300741421200180340e15400d07680061410301c151380c2200000c81320841c00400c400c0c01c058017480958001502400348002252510b85562842c3d01c141800400c1c20030001c02040c415244540d110f002c0d0400400e030101920b000b51404c220360301302e5052004d00e034400c4c210004c244501e840f00000c00d120503580850620340c4240c5600f90152640e13060301054070100c2c0d911201c4102c1c1040440c0c82410564040c03424440034501400c4254508000207080000c018000d4414205200c1086150310f4480401e8000d00080b9140d441583c7c10121145185400200064041d05030a1a02415540100200030040c84403004039209850980400c9045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 122524514 1250 122523264 122523281
    0x50a030203031e060609090c040308070812090114040b0c0f070c05030601080d02151b0d0e1603050a12230702030106120b04061d0706050318010b0a09051009020409 72
    0xe10201c44140c002511180c50011300a41d4014080703803c00c1490703000c00255000150460000803410080080000c1c0c1800c0a84a22401000829283c440703203200c1c0034030a00e0090074003401c0d1349003400900310780e40c4910b951030300260080201216550b560300c20020321321845403034081c0d00b4008102c2e0390400403285828815100290250740310390742e0f18204640d45030520544040542c0129020f650010520500e05a22010005e100c0c1c0e810b070764000140f01c10758090b83c07010001c60345646503c0f0880c601040008407850072141210401403a68441607126040100000c2c100007100313901c0d8200c00d220308800c2d0030900e40100c4480c0c0051000c107000c0003c0c0e1001404038080e500317024001620703854440c13180c0041130f008030480341a40e51315034511008003038906021396002548058024040c00c200490303800b03000941c40f225aa4100000c2c2514604030300c500c1084c881e03040c12601803054440d0307043c00341190882d0b03030040303010303150b0b0070443c5c0c2c03034000b0780d040945010302c041000140d054290704002d00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 122525764 1250 122524514 122524531
    0x20d11031e031b0606011d0a0504020d020a021e03040b0f0c01020a0903110108011a031e07021011090d02010c060603050a0c0e090601060503010b070602040b0a210c020c0d03020a050a03020303 84
    0x19220f10300f119181e0b10101c43c070501003180500c0341c00f104c00040f900100703002c100420041d0070315210f00028003281c01110407813140301d50118030303803c816404102d2800c030701c11200c4005421034030080d006682c91281d40209101c88002041c140702074058a001ea5800b80d004000070f40d2540e0741e8a4004240354103520042e91404001842150300307500448030107058a1107002c6250030030801020514207540b000e0854003142102425020f86201d40c0e840c0c1d517004204a60252000c00c0141501c40c0c150764005d09410b90907841048400410f50310b803031086408682c28241114101207031708000000f00180d500203041030060340404d0b8100101a1090345c1600c100701200c035110388071201c0840d580ea000f40104404210100014880b240c1400068008a41300300c1c0003510b05a210003d2014503040b24800d0350105031241c601c201d0804024014010802c80307540100044a25207200079960030354801194060f04440000d102890f100303000301001190440c040f545000010314001b5503036481150980c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 122527014 1250 122525764 122525797
    0x16210213020a142d09030109060b0a050a0b03010312090801050108011d01090201020c09090a17071202030f09040b130911010801050a030209010302041512030507020a12020d11031e03 80
    0x1c1030f640003041521075486442030b010080311400b40c42d50361340c80b80181505400300310a0240314020b9400f4007440c0b41241c8249008a095044003050042d59103454101c0c0d0311807600c0c10010f01c000309041064a046982200c41c21008030b6803841c05481c031102d5a0841e98140d401c000022800000541200820106003140c0e054201c8074819620300f00c9819a83c02401a005050803060900d00240880e4008600c1e00c283c1c1c2a00340c0c281d440ca00781a4049041c82056107000c1040001d000c0071604d4040701180d41d0000d145050400710750482c1c01d200c1c40e2102c2d84211f503144528015616410b180c00c0300160400307403c10a180d810704044ad0040340211589001894480000c5900d00b000c2c40314a08503940034200b11466400c582c01c21016102a47c0f84000a06c0c040c60009900919014011156800b90b260390381d5032462801407014000841d0021681c00c4064410500181c98007841881c1d101c0d0085004810012a0000641070054445c00c42c50400d440328008000600c000c0700804110000307034140c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 122528264 1250 122527014 122527037
    0x7080d0212090303031306020c0102070303050f01060306030506190209040203040303020702120d0c0f0813031a090102031302040209041b030b040f051b030703110a031d16210213020a 80
    0x391070314031030080031640580062021030101ca803542e06c4000c200b0322490016040c810007440c000c0c2240c1041106600094542091010b1003001040b402e0140c00d4500d010301c001406c544a840d0344100152000030f4010082c143c9034448410380c1c4c196004540c00403c1507590741000d050050194201e03450031388c031400070701c46000703660f1000151202c00307240300c0d44801c190791802d0b40395904490302d03072582034601100c2084105680c0115040100c041c500c5250490105000c048014130583c10040c03004030242e104006020a102e030101c0d98100c0d042d8102d03405640e4101020100b0007400c0c002d45d0380c1070307440c5503d00d0608102d5055006400c0801058a040011980e00a0345105807072058403822a0034510348401c181e103000756070080d40e10080c00d08000c210a201c00b80f070560164003000400d00041c1d622025207002c00c980e841071001207000f5100520410520302107000742c03803240748034864002c0302d00120044c000300b000e0705003148c80d9001890114010981030072200650320103540d000000380c0085e41d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 122529514 1250 122528264 122528293
    0xc24060519032013020408031b0c01021c030906050106030e12030f0606073f180501032003090d090b0418050a090203100603031409150d0e07080d02 65
    0x107404580d0004500800ca008014452241c8280c0c0b0030b02903042109000c52404458060000b0801044241e009680d64500341c02040c03c1012111035410490f00030103401941da81c1c0c0010942c680114407440000d81100c0c0c1d070020f80043c4000c2200400b178a0400000050301d50709036000d1060980704000341c44074500450007207a0301d07201c201d0f0190f032452001c13404901c0e0350604c0805001c0c801e1083c0c06c00c009480640d4030f10814807240c1c5d280c1400c14808100c80581e600ba4040c0d45114500c0d80b8100141d0103200007002c00f0303201c0d900c0c1c05001d04040d0784d00390f800e4580075090180341380e1420b040c80c40c907030f681011101180c84501100121020680030800050307400550001c540803142409004107401d0200314541c0040d08003c5c00108200d5101c088000140e60240078020604101280c0054698036520f00940080440403e00041c1c40c410b0105882d12307180e0402e03aa680d2400c000350740d5a01c8490300541d00c0100703c22a0a00b403203126a900106090f20b000034490000b11450702202e500e150102c41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 122530764 1250 122529514 122529559
    0x203070503240403111203011d0132150c06070503131205070606060503060906091611070f0803030a111305040f0f0f09030905030a030e010c240605 65
    0x1112aa0640040307030b400c005400c114010398000740300b0714050001e0200c00050078542006101203e070548070000041082c14001180d034882c0408050328890690b1501489607007a22484a00c82c000c2d070043c4040e101c140400084c144c5003004014440402030641e61070110481c2c205e41c0d041c0302035114400100e003c0ca8021000d0b070344642465040c0c8400300107280d488203c18019001c2c20000d02030144517913000a00c10703021360b4007e8200365540d03e40364680f5408104c040d00303010701228000d074441c4050201e8410454100e00001c000b50800780a10035103141c85602d81540782e8890b03410095402c2020074000300200c0114025040454107012162504448030428490200403071803103641401d00700300504013034200d218100c0b4509000156034040d0351084054541482000d841542ea4040900800d500101d60308050042030b8010b110788041c5540107082508501703985810700103040200e104005500f540c20030b0f00003615408170704c4038400c175240c040a0030090140c04d10a003610100d070240c1000704c0d02d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 122532014 1250 122530764 122530783
    0x30e060609011703040b04090e010b040c02031b0c03010c020c18130210020309120708010608061b03040819020c0901080604020a030803070201020403020406030c03020a05060f04090f020d0c020a0203070503 90
    0x1015801d15900e807140d840392540d10080200c089004c10304c000280c41210340c020b1703c018020980c01040c001c2500ca115400c40d0510708844e07104501c1c1c90301c45100c840d8000140c1d124550008105010a03e10800751450b1480c2c44000070707495800c1509050781c03141d01190400d900c40c0c0c00d98002200034600c122405a00c003007100c0f111f6000f00d400e141000541381402070502902e61030700682c1d10300180d02002c80d032810482c80c041c5845912181041001030702c24071a020082c6501030103411075003400300c0c440e10883c00e030020f80e0140c1c85010001c07500f0b001b011002c0310000100b01240d041a035005400c0a9260036900021030300c1811290000500c010020400314407450f4020445140d542c11070381c1e01ca185800c003900b045d0846d0340c00e21021006842c1c92040e403002d1406402c00a900d1442d51040040c000090f0300200c0c0150400d0002e0359913001d4036070036102525000b54002c121400d8400400c4000d01032140308272805804d1043c941071140e0042420840ea074029010f64888640300c400b0b060f591400c11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 122533264 1250 122532014 122532019
    0x3110a0b090f0f040903112806091712090724121b02010f0b0f03070b0306010c060203040f030f0503090d0305040c0e04030f030c140f070201030b03030f0a030e0606 72
    0x80211103002c1c40c280c69107010700c0070700030180944210100c011500b1a09003140072804502080c03c40c1881c40d400700000042180b0078040f21101341e642c407514100b00100f002004140e00c0c0c46030295001c1010301d00c03d0301c149409062030a91118442d002c85070000d54151040c41c450300030620b0100360510b0f1904000038010b42e03020071038102400d6000441c3d00c44000400030340441d0782d85900d80d485003e101c000002050350381d030006c00e01c202c00f5410b08040741e240301400c0d0311075007020005000c15200800c01d030080300d071101a80d98a075900d030001a1010714038010000c1c580c42c4004104000c11015507003039080c2900a640700f852203c140c0c0c0302610544400d5a40502c60350048894440181c441d4000076401407217a00d0200141d503864910301510309050310f040380032805c014405513041354188180308420b40039242100d40c102c607010090801c1c0c03284035042548400001254025a400f1b500300c80039071a00a802c9a81c0d038580c01c9400d05681d0013060700c400001c1d08100044049402c0041c401d40500b400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 122534514 1250 122533264 122533267
    0x306050f0105090a080102030a02070203010b0904051903120c21060b031303110a050607140f0307080603031e0316081b22150e01020d0e2101020d0603110a0b 69
    0x6200103642e180c000810003544120103480c08900600e00380003841c000c406110015032034140e148105425509016620790003201401e007008007080e4006200b81b00c090a0311144417454419050450b80e844210110f40d407802e0510100c0510240e2024010b0f1640001c0c3d2034585400e0340540c0c500342603070100d2050010700b103c24008159001c841c40049018640709040c00c4800300d00c0e203942a410b00c0d1642200b90f510341c10141c1000300007078101103800050205020b02c0380c0b400164045880c2030303010140010b010400003100140040c0c40800440d1003048040003002c8e014402c03148000c0c0951320441d522a580404218070010150144200310700a8010110319002c807102c80f1103000c03081c0c01c02140300060001c03500d420b031210855004100003807c00011108215420200c014010140c030000e8907046611420904c8103030340e400351101a0140e800c13980c0001400f81d000d41d015020aa14a1050180d4800210442d001c2500d91020b0100d034800d4400400c03000032f0000304000c00c8940d220b0a44076100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 122535764 1250 122534514 122534539
    0x6121203050603061f0302090c0318030406080a2c0105010f0501030c05040905040c0b070503070204051503060402040b01050c160905010b12070c020a030b01064410080d1806030605 79
    0x201c1240186030b035140144020001c0e5526000152120803c1d24450710b0036038000180004003d0bd4440701d800e50005000562a103890940000d000e1240180811502c50b95601011400d076840c0000c1c40c8a4040c16241680c2ca541c2c1441044c002d200a2080c1540e44084180010f103d5000303000300002c1c44203e48480e8100381c80c0c4815007000d014000e000301c4444c13a0b27005d8003044c040348090140c042180201d004646402c010310500c002c07202c0240c002000102e00c0d0800d0303000b550700010f0041e400750341510013141c0c481030800180c850307000741c141194060080f642d440d0003031820700c6058011101c2d240e0b000d0100e070340c0c1d0351408082c81c401d1120504003041e01100083c0200d00603c00303400c5007840507107141c03040d6903030381c503410f00d105401c1c0c0000d40000e02c1040001201901000c0350103255039140346a6000b0391403021300c0484a0701c14034050304050ba10600040740c601283c034104004201d5081a9410b044004c2c0005141583c51000f1a00400604801140d801d00c00d100780400c0d45d101500e001003059 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 122537014 1250 122535764 122535781
    0xe09090c03100e010f0203011e0501020a210e061b070b0405031e0a02100f0323061201231605030106090911070c08060601171b0c0f010612120305060306 67
    0x5624400380003199200d070740c6184040080d1009500800d02101440c0c01d27200061070364101c0b05550b5019904551000c0c00314402314880343c03146207404013140f2484200d40400c02c0c0a0b21100c0001d00311aa000d00c01182a1000d01c1202c1a8180d1415818050703400300f945900611006004078020355801d80d01500716040000d02940c103003605140948211412410981d00049615102050520001d41c6400c4c1810f1001c1d0180a000d001d11035565003500300e0060f195103043c20034801044940b00306081c00c3c40a0180c1029400081f03240d03401400d08406198810b001c1910441c1a9041110201501e501c100954455016281a01d04a94500c02082d1400e0103c8000d0810440c0c0501460700030020340000841600e032070002040400c01030622864031100140291901440507091201d0f814100500e441c4035000d00041c00d10108030050701ea0030f0165500e40b03010b0403000c103007940c1c0d8604080419068640c0808100c80d80c85400c85040d80328030254210705451094400940552120002c40c1590 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 122538264 1250 122537014 122537021
    0xf020103091a071d0405070c0b1b0301030515010806040506011a0d0c0306090b0f0d06050a060f17100603031b241b03150603050a020403080a0e09090c0310 68
    0x40c0e0141040600b0340c020810203840d80d032003e60303016010402c0c003600000f01c1314048001c43c880b03020445d0204594580756001074001086104c0040c0b0b180000ca0000384503000304103081da103442503120b86907202e68603071410940d145140d1b0711a00d03d04c003200000264900002031001d00ca20750040291040744d28024861000c0032604401c007044507400d00524204400520929040304003550b000b007002483c0200601c00c0754a6482482c0c0541c0740c1814900741526050000d01c04154481301c005015030715109034000402458108000b0741d100d04000003107a100c0035800302d40034280801511019004005c00c8011500c4900c0010042140313900c8110802c00d40b0145115214001c44d401da07203a1000e0016005002c26030300d4801001036071291880d04040320548100b1500500e41401c105500500c4001e0059025511424080549903000520442082e8055400840e405954181c807102d01380c002410b100071407441140a08a1500011000b84c0000b0f50032303210242c00390240012032110300c45400503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 122539514 1250 122538264 122538281
    0x50406061e0306050d0b0609092a12030403080717070b0103020f03010b0405010f0305070503030c03090907030605130920060301060309030c0209040503040302030d030b01020d0e2808070506070f020103 88
    0x62503a43c210018140e00c03611030001c3c0301d0f8403030007410702c0d80d240200030400f600340040c11010150388540c00c21403c04c1c0c0c603600c3c194110880c0c420803014600455000a001c0c8100507c118420b00002c10000704026005015041e0305204101400c210480d80c0142d44407401482c00240028603542c00410141c18080c041c04141013028001080c10103100d030110382a90340a0b4010300303e015001348200f060010602094005c1c11085028500c0c00f031101c086d42d0307070700c0c001e800a1901c10280301c8040703850f40c0c0c020b0340400c00034513000e80f040c0030390002c0b03a0462000f840016000d0724500c02d82008251682c2c400c400308280024010032060440c0d0030310030100d0041c44858001c40c2801160707a081070160f525a414544200c0c4100001c540d40c9045105041c108111190000305250810000303590982e008905207501c003a10f0b1506005036121100083d00c418007070001c4180440c541d81c8143c51442e0707801035080c141c450007821030340e00603a2030080c84194404c841c1c0241900600a00d20001507110390402880c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 122540764 1250 122539514 122539517
    0x30403021507020d05100c0311090f0a0320090a2d020c03030114180708040b07120c0206010812040f0512150f1006030509030d051909060b0406050406061e 68
    0xc00040c0d9020503a1012601d601703840c180d0245256882604840c001d0019101103450140b00210744c004411a0900624481c00c1c882d0900f03a40031031050311038a00541c011600031041c1c41285445c135524540740b0410444c0c0354002c0c0d101c180015000d0089004007041d01181500c40c4101000060f164011684e803040008a40d80c1c00b008940403d1f44204040c50123030001d01000412039a10f44100030b282d040c081c0f4900304130003098081020164001400c507601036082402164a031346c074040c3c22100080030640105c185c1c0c0c90100003005d0340b607000488a05a80d03002d8100d0f1402c1100c001f225450703004900c50021117510107042800303682401c14007010300c4a28a404c0743d10440c4924140300000c3e5007118500c407410810810088001c81d4041c803a801001c89050420031400d015027456242c2c85031000c04103446407242d01080c0c000c001030481e0729a0142c0300904004110052909001500c002d106092140c0d0811078045280e14291048a0031207050740ca6407010b1040708040501003d0f60b4480000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 122542014 1250 122540764 122540767
    0x504121202030c0f0c04050106080609010902180a1d07020f0c0103150f030302061005060a08070c0f020a060504080105150a060f021c09030b0a0501080d050c070321020d0c0201020304030215 83
    0x840c3c0604218094140c420200900050386202c0248411110140d001d02e0070003021005014494a03489502411345041050269035070440704615902012041d194070340001c00c24000090002c0e07441e035001620103c00388a08100d48440404980d100d48401d26030005401c000310900840d800303580400f096400202015120350ba503200603941108060b0310035409a00494100710b114181009410041e06007159032030305002600900a0100d88020001e00c00d210b0780314251401d01c5186120f0f006c030180c0c02040707018210b0721074000500a40080c80b60f60020f6003403101041c0f01c8612003004121086018080b1188141b420b0011109603140c0390441c000e40c0100b501c1c1041032a130f40302c00324044016980b02c08000030300d50700c2d256031280c1c8014640d40c0c0d0b4503c0d11380103005006000c5504603404007286440c5480b01e909013541d50905171070390310040282d0f45c1c0001120002030824118030b0590841c0e000c1e030303181403552201540c600244400090060700100000d00040c501820354401560082c00101e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 122543264 1250 122542014 122542027
    0x160f02030a050f0f010911130930090e15010504320102060f0c0906040506030f090d0c05191401290105090a03140109051002040501030c050412120203 66
    0x103030074141446400d0300c00742c0100090700180281005420f00d040690802000303146a2601c0d00000b80441c5103401d442107141c0d002d83d86110485400540c0340c150411201c8051a134039000b41c4045035000c400404024a01440d580400380c010501c0304211014000c00d40c06a650f0b034650307032030801800310803103041c04418080854030b07540005100d94403150311040041c50316400c0382942e0002e80801750990441d03101e5020001034602201045422041c60300440b13444001c0840001c240780503d40009410103004030401034041c0c1203e0b4841d01491100013a51103000c0e82000454401846900141040d845010300020a6841e018243d0200c3d000785440320b03008010304401d03800e60b0003401600d5039541e284034004e0728481c1c2240511a20301d900b406e00a00e40007440c004986070000503c805041c00700c407610341e2100d851080d040100142d502c94141c800c0450010700e280f00a4103e030041c580000c0c600242c0f0060035006c5d00c01c139811f580c071299454100d0403050351001c061103040841c0e0300440c0030902c801b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 122544514 1250 122543264 122543269
    0x3010e091e07061209241803021515010203040312030204031403190f0e0d05070801020f0403060b0604120b04031103040f091116020d05070506040b07020f15160f02 72
    0x41071a030006038001d008018a03003070004000c42d120030400350400c0d03c0d000800300002c11890001c0192441060710340d0070440754100d1035004007000f96944100200f1000840101940490318194913240300f2140300854803900f25414010755204109400742c1d10400040c40031075109414a00f1500e9545000342c60305899035038010740550603c21010455101207014040c0d120054140740c4505840e19040710050802ca01c020440050704030b08074041c640c11080179051080038029003004e01000da000b9940c1d108582561201540244001d03110185030500c14022491324404613000c994040c0e41440d0444210f840e91643d000300a8000c030140b014204031504048414000740c00141164901c50340203a1404804030282d580940500c400800e042050306c00b0525194200840e294055645602241142c5052450411aa00b01940c40078000c50006090710840d001014014802d07079508044141031028800c44480d6150a91114a818008a1190301142140d8110350f0300410b062030740e104c0903402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 122545764 1250 122544514 122544553
    0xb0a0b0301181406071e0201150e011d040506010501081305100219020c062a01090507091103040b01140f13140c030c0304080d020705030a03090203010b01050f03010e09 74
    0x51880c0e00c40c0201d4528014415158003c0e0482e501d04000b4040d603243c1618014000641107102540f08003603801040e0005200350b00031000301e0141001000e07081d0301c5103001340b441c4100b4403c2c062200441c5601c601404440b113040d9008030782c498000c0015900f020010340750350034010064082c26802c209240007040b42085411010110703082c00680d034480d0040490844108030340d281c07096501500f4807031035a88548048840340c880b04145481212502800b0106250300b00c1d504564a60a0800040a00501041d00d02c2140c2d0321090400811003441480d107681c0c001141c01a00e5400c098004205d2000c0003500e200b403a540c010b0014200040300d1b8000b41e10301081d0040c20348003940d00c541d10107280d08000c001d1600901e00855941c110b01c0c150701075400d984401071000303086501c04103c5400750711075031b0152815641c5c4003050f80c2d01c80c00700e198000d00900752000d06078444d40c20052282031550141d8101c6542c4202925410b18503801c1c01148000e0010152803100c0718070038580c00082d1400c030402d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 122547014 1250 122545764 122545781
    0xc07140109200a050f0402070f02030d051903050124032007021c021005090d0804091b090501020307020d1104050f011409150904050a02031e071a070b0a0b0301 70
    0x4940d2141c1c01c42c80c185011000b44009807070341c060b81d28500248055502c032610401744403400c0f80d0150751481103180c6a6403003840b61070001d402d48200b0308040515034110300071700030480e080c008148007446d1120084068440c28800c0340401d41c001c2d2001352031203203081c0c80c03484081e55909000c600c1214060b10007140c1456801954140940851584218548064845019840c5402e40f800368078868001901134100e00308032400780000007440702e0464442040e00c81e00c2d15044010395803245d903105c48200c0a40b4900d5022120400c641003403051090103000210290754040e8000c50500741c2990078041465041c601c01d842c40d46121289402030b644078041c4c58440c065001c3c0c024140c0d49007060009001c04112415880340300740070704004007040911003026402408440d001003613103860030000c1c03c5c0303016854060b415001c0c3c00c540c0c18640015041d89900d01d01140110b44450740d54908103001d420707042c240e044125100304840e4005c034018030481504940709913400541a01503000180c00c43c0d4444 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 122548264 1250 122547014 122547023
    0xa140307090b190e040c090b0c0712031709010905061902040f091506020d080c0f070510060609140907030c02100f090b01051206161b0b010f06050703080c07140109 72
    0x80024803001c41c0c0c004e41c4442010000c0c0d5050080070101d80c00a41500d11038000c3c8000c403607010400500381c10b170400c1488014400034a602d803840e801414020a5180b4038160004168900404209001014454210350941007409007641e41c075aa2000c0711ba04850031100900103800f070001194000c0d40d4482c00d0020550110000303503810900307454400030b90141d8012825034201c5403510380b00c13230b80140c4207650210041100766940e0802c5047e1100c940210200a84548031305a0b609030200125484001610f065481c1d500f10503648503494480846410007294000a05901084007240680c0011000f0100740c010f0340d0615010701d201c1c00407910001c464805407500c1e100108180040c0c0d1500901502c41510001e49880c00c0081d0303250749070005002009404410304c000705059101d08482c0b50401c66003025405d620318107081c500b12041c03080c0900701848807000d000050142c020030403190a01d52603116010207550f840034000d81e40c1c000790015a10801d80d5250007020203400c1c480c0420484c804c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 122549514 1250 122548264 122548297
    0x30114100603050702070b0403150e060717090706020307110109050907020a0303050c09030c0d0303021e030103050105060306060310050606090402040306020d0606020706020c041e020705061b0a140307090b 90
    0x1c2203001000c1e102c016203c00d007075420818051148003813200031034054a4102072601403600040500c3d02c010b081c010300d89050b07801400144140703913502c50342803003d1501c1002004001e4031b401e032440345c943c08c00d88030341760159108001210004911640c00700c15031405062660703000b691000410707000c0750216110340050b00006610420140c0610686070040e504401d910b08014409012942da00c00a00310644101900c14145041500c42e8046174144541c00c12290b031650b15007000040103802c2800b040b5125401c100000b0a1f90a001455900c502001001024040e122000368801001d0152441d40c0040003006000e00a8403035000400066210719001641c5200803960501250002c1d0000821500400010071085500007500e0708106c104413000105181d4110080f2410205203000c1c0f0750850002c10400280b0901240d0544254555800b0b0300c5041001d041880301c62203022070380008600c4c41c403040708600c829100550351200b42c03801c0c80040786803142c00b03010442c0c00034014100420b85 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 122550764 1250 122549514 122549519
    0x40902030a030216060e1c050705031c0e030a030512040611130503010e070302011e03021603090f090605030a320c0111011109040207030203070c0e07110f061503011410 74
    0x5050302c003400180001d142001820042c0360014008041c605143d00c10340b81f49071030034004c0c413005011f00c200800004040b500c00f00b50700c1e070903034130110281f0f440c49021502103000103a0504001c1030b050700869141d9aa903140140420203402980740280041c2d40c81ca5036001220450a0300340018105040096030890f002494441010b00b52092035a0001168101c3c0004100507604020841c00d42e85c0200103902154003400c5007100240030b140c1e881c0c08282d680e000323203500745034000c058030058442d0741d44c550314490b0310340411a00740c0310688103041d01540050f0101000c1003800002c8101c030191118151034142e01c0c44402d010064442070b801d0040c1e041590b442040e581c001e0080140b8164900c000e100e4502444030b0b0320202d02404100342d016580008104080520a200712410941e110300701c60f00d201d4540107a4040000d00300d0307603000828034038000e00d94070303850014025810b0000c00000346103030b0350350110302b580240d0003091468056494101c502032801011881520418078002c07021401407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 122552014 1250 122550764 122550793
    0xa1712011202010e01031a030712030809160902071113050108010b0d020105090f0a0e01140108060d080a030f02040b072d0302070b0702060f040e0402131a090402040902030a0302 78
    0x40040c0d005401201c881c03900c080050740c000600c0c800c1c0744000d0034005001103c9a5480072841d40503141c2c00d40c1402680c40118a64503e48480d003100b500070740d600f8490340d03102e40b002e0395500c440c203d02091250b0040e900b003104030025001007044078440c0482d21044002480400e44c451b40960380240360a403600014064003000740315000c405141124815100203036600003800c42e10402002900406a40018680e0b82d16034a0b001c030000c103805144604903684d98516543c9041394004201d00003414503004c20050b107040c01d0a0958550001e003c0da240c45150384065005080502040847c0340d028040018406813140251100c1e6018441c25490400780d0640441010301c01545002409244401040032036030000703000b802d0340d4031040000c1d540e00070303030000642a000e40b12200c407191303000041c007244503602c840500c0e0041d44244c41d80394110369420007210903104803008403085025040580c000307600d00503040c1a00700d4005040010520740580110307003400f0744000140c016a00c801c01d4940e104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 122553264 1250 122552014 122552047
    0x1317040b0d0b0603010513050c071a09010c0503060a15020c04060602070305011401080303010e09010b030304060c0218220224041a03060a03030806060c010507180b1c0207050a17 78
    0x2c941100c0051556041c00c0c0019044449071001101c41a0b80340c0014030000c030707032200300c402c0d8681200030101c0104104485080000c800c4400c802c0c19400c2076802600b03540079505807402280014034040c40c4c21f0400e41c0421820800140c0e602c2144200086c1c011991030358442e1002915841e4003030031459045080050030b6862580d851401010350390010400c0c1c80d0040252410344403e030000c54980c0c2c86400060303001d0204c4403402c640c94080001c0c001000c503008622040c60340d100346c514480a0084101c1ea40324410300701c032001b102103075182188801c0d404804447d02e1861008000c2681d0841103032117441c0e003840d116100080325a0004042c484030b500d901405101c40c4032200164654a400d00200e481110349100c001c00b80000d4070041241540da41050359074290051000700300c14a0b0555005000658200c3d40e01e142c0e80840030b010030b512180400320f070001001c2d201501c0044c4200310404000b0b40c051503041d141d80c000c0d074101100062081d0b40c240401011001c0403a2140142916039115 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 122554514 1250 122553264 122553281
    0x106080c060412060e03040f090b01030e0a0203280503120a24090c2705011103040812070c030506010e0403170f0601030506060f04180c0311031317040b0d 68
    0x90700d040c0010410100c03000d5298840c143d002c0e00c003080511301441350514500854102400d00f40310518049030140d01e84d4000009000240d034207000b82c03072030510301a4840250b190003179010307000448909420200f01c18500c2d14005c00001c01d001030306d4140c807a541546c0003442618003c081c00420b0102100960080307110740090044d00c04040c03080000304d242c03400841e100d114840d0380c031040c40d078000601803146800750240c080030310700741c1c07145e911940c1910460a000c1d480c003044100c040c0c9420420004140d6090312034100051102a07e2540b4224842d00b02c141c0071999030b1003c200120001c0d01c28025035000304141c4040c02c00c207040130b10700500f041c50b04544264006201e10100300c41c2c0d4400628098000000b0300b40000c2e02d48407403001c6191403003014240c03403141c032000034001801030211001014400c0405400c120310b00b490796084003680c50255119001100910218213407003581500058002e10a2018403801c1400d20100e01c210b07009039110320785043c0007003001d204100642c05040301 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 122555764 1250 122554514 122554519
    0x504050f06090f150604150327020d150603051507140301060e0a08010c050a030f0b0a050105030a15030b010503060a0b010807030e0721020307060201140604020703020a140106080c 79
    0x5038a400000310b0002140108100d95085410010691640900d02c81c1401c581e0081e0549503250b4442d0445c0b001c0c212410841c8000900d40344030311002c00e2070060b2410301c01518560703802c1c0e00880c039020810904102d000907100d181901221125a01161181030002d40c85117000d40103402c0d5161118511120052039a4140b003e100c51030168000141e04581c1580d02900302031405005101c040355198140350801d800c1c56103013200301898140c0102c06000500700c183e4041c0100e2107403d9481041e00c00e40307100e03150400048a418003056006101540d40404c2240000682c680c588415054094481d032007550200364250051080b41420700009500c601140e1050118030381c03040000301290b000802c41420542c0c0c0d240010703401d000038080100140054070300102284144c624510840400d044200d10a1041d403600160302401030141c40503015401c0c103450036940c0e40707009100c060351185004600311300a403e2450300250840d400481003483c58000004c940e0700b007503500c034907140c242c3d4142803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 122557014 1250 122555764 122555791
    0x5011106040c0501030905030d0509031b030403020d0f02130c211506080601092607210b0402120f16060e030c12010b06071101020d0c02010c11121501050405 69
    0x1042c00300345140101c450030300c2e00180b00c15417414402c1c2075015000032103a0b810700340710600982140010140130003400300b1030b0750011548000c140c5685c0e84110302c00203400000d140e00c0d5102103001e5651341302540b40040d006c0a0115000c90b02070048461010903100898000100e240310440b0601480e13041d42001c5004020000f410b580b004995411031080320704125040c0d00040c071076403051800300b0040c4040c03012268101c100c07083c0c00e550001013460400c0140700750f420000d840d000b072920310720011110707000002541e00c4580303d59616140080007070360030200b50198419101c60801c134072204248404050103c0c843e04040d5000107616650001d000c0060380309100b03400740e8000c250410b4412044a2540d902c88220102c10701400040303048990022000c0340e40c20038880700100000c0000300990a950140c000d0110a607080456036002030b00003290300025800044408181c280e59200082030506050205118030b03203801e1403210000102e49041c80100400e0803d801540c2c0c020901040c84c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 122558264 1250 122557014 122557021
    0x3100f150801061809240b18012405040b0703031118090f0108250503150f0109060608041209030b0a02040306110304050606010c0c0308031e060904030e10090902031005011106 77
    0x20380c60344400002d450b00c251641a071300946c10540e002211005002d0440341191104019000a500307092042c90030040c4117030382510a80009805202e40543c06450b51814075041848018003504880360880500d60b50b0082070b480c010660014114161101c051201d800b200c240a20040b810060140405003030403d00501c148080428940c49088007400c036107012035100e000c01030350001d050b448207030036018001c208050b0006400c3d0803482481c0c1001c42c10266640d80320361400702c44251140c1e0001401c00408240020a071089070b4010700e8031850802845074594603401c01180047d64000400c80d40082d0030000c0045c58094140d0040f50030360098103620381600c4858850300d00a03c214100610b0080c0c0008100000b036403180078640100f441074aa14160740300702c051403a02085180d8602049001440700d2529100061146d689a5100c0403501320324814010b0300440443c009007400703450f00300407440c0b030424400703981305240881c0100040d600c0c2800240101e140102c02e269540c1264040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 122559514 1250 122558264 122558273
    0x201090b0915030c04031e03020c0108060409050f24040b07030b130e010c030e010e0d031109090c0904110a1409040b090a090b060105040503100f150801061809 70
    0x100444200e1a9103955a421000025468500003102c2940c0c0080c0481030060031100400a030040ea4441d01105005d400c0082e00010144400d00700140140e100000a20040d4412040745030428005013020a03040110780e00c01d4103002d0b00d040240e07150380c00016a90102e5504140a03a11451001842005030810f0b40f5040b881e000002c0c5840280f5844080d0f8138102d0321082b1a0400d00660300c4410020012800400d0340a0070070031030550300090602280c440040fa040c45103421070396040000f0245914001b1054000c0c0012190015082209100414a5880d41c181542c42102e02182450b61000704104110844012040ca02e9440d10244145640240c22401e00490b669141d81c48541390b41075100000e000d001c05012050700000c5a0381400031020132038100e00241071044100409580c0c41000441d414000d0788a80c42d80b5500401900d443e5021507407080b11f541c3c00c03924010501c0800f01ea05058070f05039550054296a5543c0740030481650110314a81f90b04441701000e00108009072079 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 122560764 1250 122559514 122559527
    0x6030903050d05041421030f04020a1205010213091a0f01020c10050c3c1c0503040c090b031009050111040312030501050405061503150a0906140607030801170a020406030c06020c04090201 82
    0x82ca00c510f008d880301203010365540152101c010802000707a440d0f21240c51400c0c40c00b1303404c907206803a51b00040780008995844280610030600b80d03e40010905010300c0000c0046001100b40c1940c15400307600c1d05e01643d41c07651100200d1074411a10f841340d0302c84c1c43d0030301c40349000c80400c55040b400482224555034080130301015004c1840c6900d110003002001c0652034101000c44000c00070b450000e18108a40603089006184214001c2540402040d0780d4144581070368040603001d070b8076401c0480c07800440300d802e910042030140180c000081d00c140a092990b00341c0e005400c2030300c1542440c4840030f2107070f5040c0200d1f4090402607030f00348050300304240420405001a01c65010403003001c80010702c0f540300070b00d8821400c0c000501070302c402d41c1c1e41e15081c40101514080c403840812650b072803003d5030405000722401300c0d91682c2c580b00f807686401807401e48040001d000c550580601c00c3d542001d40d8440c060800914040d00340c80c0b02c00c902e85072001e45828420086076000307604245103c40036030b81001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 122562014 1250 122560764 122560771
    0x1a0727080706080c0421020f09060f120307060204090b03100e0d030e0c04050117151e060a08030703022a0a0e1012060e0d09030c06030903050d0504142103 68
    0x10407203039a41300c2a0b81c00e0900d00854001440c1e410004507011081496103885008842c002e940e1143c03854010410b002ca004400c803400342c0c1000c02e00c581650385050071041745040b14031103001d0343d0400041e85e0b2560280d9100d54030125005448244100c124038061000400342c80304014100948055114190b48840700ca0711000705165503071284448090301441702000821008004000642e100d030410300310302c0d40d42403000c0500d20a140c0c40182da0301e000b1410b0f0740540300907085501489060400340038950070040501c0e8108401e08000650700c0d0013080500145442600680031120705100125418101000c503405219503152800c04141c4464429906842d0141c20441955460216600340172015520089103130100f0306146007444000d0b4001c64484015009075518003080d01821110303188203000180c20510162401c203c41406039020400d054440d09040f801d0075542c00390391088640444041c1c481c0d12003581c922000002c1071184504540104968075900041408502072500008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 122563264 1250 122562014 122562017
    0x604020a03060504180b01060914310218011d120118030203030f1501050d021608040306051009020f16020d06090804090b01020d0c0b041a0727080706 66
    0x1540c103888601c60b80001019240160051000c02914a02100c2800d4003600c2510441a440000308280c0d02c00c102600440342052341c0c84500c1c0c4003034800c01440c00340c039254803e901c1d000c0110803855941d01c0010703003001d00c0c64801c0058076503e165107484d103103040001e0014100141c0600300755900b07a03940d4100038210320946000b450410001503543c0103004c9106200c4080041c804894200f5900200640c0300326802c880070745aa1300c0d10381720140da1500041d009804200140314644003281c199003d840b8200322405040b1a10001d51103080c2076500c2030f0802d8a04a84650400c2181c41e443c000000060854520440c903102d00d415003c1418028040301180c14007020b140601903640710a4007440c2d0f190000010401c0c41e0140c0707080c0141d5481403141c100c3d41410b05a503510a5800452000700c070b00c4442c0c0f0380d800124819035500d0381c0103100a004075800e08201f180c240e0b42c0001c10752880d110700095201c0f80d4085035a01c6180f0786141c0106c0b001449841c0001e424017002101055070411103449 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 122564514 1250 122563264 122563267
    0x3030c030f040507230a0905010b0702061c0533060306060703020319030501150504050a0e0601031e020a020c040b130b0d1e03080906090d180b04080c0a05030303040b060402 76
    0x40d4070b881c0c0d05043c1140d0140d8580410301c40300e454240345d1281ea0742001d0104491018080d541c034004003050315024400c4030b086180034800d0b500903007000c0005010b081a520030341c5020038404030751081202c106943e8103100c20380d036100c5106800749000e5203107807580400000202604900d00020020302c0004c05441c0903010120340c03042054001c000741c0762144145035148580b503219010044c02480302348203c04011100284542005020341d080342c00b42d920140040c00c000381400350a00b80204050300f082d040650766902d008a00380d2032002075030741240003003001d40e907803528070002441d1120810202d440380d031403c0002c00c0da0369596a101c880c54030300d40d54081100c003036500005103038180410016200c0401c65a0101170b41c0b0b01c200101e502503110b91038044503a25a850030580d5031604403507031642a84540c1080a6840c090044603030040070410038040310685500244410b50015845910940d0051818191500c2d1550032200540f030160f00541c214a019224020b0090300030b4009802180e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 122565764 1250 122564514 122564521
    0x7080f0705131a0304020f010f0c121b0f0b180705190b030103050604020a0e15040b030c0a0e160c020102030f0a0c0b04050303182e3b03030c030f 64
    0x21a94074000803c12255001206028080784005560088508902c207864141d1008010760040240e0020003540d6540d2a01042c40e075680c4242980e4004004d40c144801400143e00517141c1c0000080c07824400c151062460015144c03000750030704050900100c0200d50002c290ba0f492000036100121001100e8407414443d10720781202c0044020f8001c0115010700100100a220000484900540c800d682c60345081c0e98614014804140a03555408030502d41d00c5001a6403415800c1381214100041c15501c0051210b00011403800d82d6070b112a8440110900b0850b0f42101151501d24080140c1803000315084150b000039140d208260003502541804141204505e110341c01c1040640d0703016030000d407907041c00c1c24840c0e5290012a080340c401c0640e0b44c40b081e02e8103004942170152240c401c01c0850309554648007807108048c00020b0b0759502d40c1c0d50020400701403070b000203e00b030b000d020781e8045141040e504c1d48403425600e0300d0340e1302180d82c4104240070780c60420404880d80458031800442c010745 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 122567014 1250 122565764 122565787
    0x3200708130e100602190317040201110d0c21050406140906160b181905010f0f0606180e01181d010204171504020105030c0c0d02030307030507080f0705 67
    0x20030a030400151040c0100801c83c05104200028065410540844091003543c1c0061204070301c0b2540010700290881c50782490340001e0001e0315400520504017440880b00ca80075052402c003200c100000040d00d00c071324680c18001c04100003440c1e01c0e40c44544803100051180050305a11030b42c411501004032072081d070380d41402c030903050310501c000041a09550342021025102d00c14179101080c2d460003000d0000c503c00100e00529043c2d4207500401a000e000c07c1c6802d0a1195201030300184c0d46035480700d40c8840c59480c24131400f000b10044440000b80181041c41c010030156042e80c070b9110f80d00c1042420f000d18420004114111a0040d4102d5140707200101142c0141668422007407200c43c0e40b00180103c6c49040d00a4020390389034103070603070200c00420b00b00740e50703203030071002c0b04000ac4c50820214015501c40c400442e44103060328582c600d0000d846100d02d10f000c001660b501c0050b00040188070f0440d40c1809960380242071407030140000c0c00c2000701960507410151054007800700c00541c2c5041c03003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 122568264 1250 122567014 122567047
    0xf04020109080a030906030b030c0a05060a050f04030c090e06040f330b01080603010b0901030f08040305030309011e020c0d0e130c02030c12071718040e01020a03200708 74
    0xb4080300040d02d0070001e00d4a806003400000303000e4400480e080141c201c002d030400041420b0241d0700100042e6041c0c1c07416050007441e5000ea409501000800c100e107182c8241c01e80b0003000114444d01031800300070f140c1858a0304845040200b282d10341c110b00d060001013a0b8100c01107031415002210f005ca0659042c2e21000d5600ca100c944a541c6144145c0c00c050489090303110101c03188080c0c840c0d403050350314181014221108941280d921208500060000c1801d9405c8060454487c48805140540301e032240d03460341e0001c03240445140c0d1a41c07004e101d90505038101e1154055080429420441800c090359121010801c0b040100314a404149445544018034070962902400e02008001d5113100c00940701d600100b0346071220300c5a204480750701c1d04400102e842494020b512095401c08a05000c142d55101d981c5000e02e04110180e025410354880c8120400d9075142ca00060f5a2800014040c00b03807031449104d0001411400000d10b05543d2110440301d1155002d0b200c655907407110a02c40056 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 122569514 1250 122568264 122568269
    0x4060c020a060c080a050708071409030321040501060b130501030b041103010620070303080c0d0f0c05030f06090405030405040c09030f0b01060207080c030717010905010c05090f040e060f04020109 86
    0x520b03041c4200403c40903000701d480385c01484e0391320040c000f03661034010a84c0c402c841503034540c0009440c4d191035111200328901405042c94028296458001c400407141c070281502c00300c60b9242a212811300003000400d1140707400511030f0611035810b0951541c1e6505001c0305a11515044c0b58560391a085560f0b41c0e070f4850300d0401c2254422036100d5842d898014113040303908030544134402c00c241e402d000701c960000d85c00d42201c0d45556180c02a9592100d03804894001c44003c080542d01d0b418845007130315940c0078513001c80320156105d5440b0716117182c0005840d130024091500034840d5401780808250040211030a03031ba0261000310b15080c9103c01150704440691014003070300038600100301000081d0358403c0c1210455822034400340e80f590052626680d851340c2d455495440000c00300088000900d802842e003040340c2c00000c81c0c0780c0c1e80c4c403041d095594403c3c0c84c030001500001d409429242904100000e69000c0d5401c010072041030007001d660380c50103082e400d052000c601c0020116071054411402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 122570764 1250 122569514 122569523
    0x6150c061d01020a09061701170a05070905070806010509010e090c0702040f0903110d0e01080612060f010302120706020709020f1303240506060d050406060503030a0c0c050109060804060c020a 84
    0x328982820301d0a07000750020113545000a4081e200003640d82d116041d800b084a0080075003620f242d05e45078050141411400341942c0500407501840d020606c180584001050180c002003854a49150014130704100140300505005d800d0041e058a03982c0300e001c141c014001900e42c0190b9445000d20380002e801214002540b242c1805600682107405400c094200d0380f01e6114400c06841c5071072490784508400000c400014103002c0c5841340d80d8880d001607900240054100c0721240114800075052075001c40c0c81207480c07100c0320010000c5090282c0c545543c148400040c1495505002e0000d484400c10b10406c00060b8000c00e01b11007082c10311046035641000340004086450390ba15160002d51518242c0140c1c1d50b030885203941405000e4054030f44601310082102d8034103400b00d05200c00a20000c0c04c16180d6a680e4000441c40352800c000a01000c14940c6031990809060720305281035000f00d801c8281003090194041100d55000f5031300d140c00c1507024101040140c8820422454a010303c07101030b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 122572014 1250 122570764 122570801
    0x3140106020a20031b0a06081e0c070b0103032d02030406031a040207030f08010503010203150d030905090c0702130b010f0f03020c01020a080117070303120e010b0d050f0706020106150c06 82
    0x500d54000c0301c21440004c0ea054503201c025503601c0341c00f88e48d800300445030040481d036503480c0010402e4100e49100d5115a2494010303041401039160144060030980080f00441c011081b200e00c0d52841c40354542d62000d4407040046039800905000f9101d0107a407042405140d00e65984030150b5808400106900c0c0b805442191240040e082c018290f020010b05007010807680340c00801c02d42818000c59220300c8840800004a0703003d20b042c01040701003c0415030400009c0c020105041d0784a2200900611003038003401e4940e03506004200c40c5590042c00210b045107070039242026a6082080490b2107002030030000d03400c036059a0103070040c0c0f088640075201e5502c0002c0301c43c4030941110760141a5002d19800805210751496496902d202c180030280c003285100d0142e0b035882c20541c0290030011540400851180079500214801c503060060407100c0d07070044689040038200c1080803c00504d040d02c0240f00c100e25014400e003c060503002d02c502000a50860340c82800030702d40105180c00c1e0306642c0708 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 122573264 1250 122572014 122572033
    0x5160206040914190908040608071b0308070f0e0d0b1b030f0a320603150a0218090c0919120606090c0905010503010b0703140a08060103140106020a2003 67
    0x92502140444904a1310010190706010001e41d5104840d12554004182890981044030980314150010480400c2000c40d06d06d103803100400080b0440c01501ca520340c54070324188140701034150002140c5441c104403c0d007400140c140e0382e055001c285180c000d0352481c4c6a40300c00c0d10210510b29100c03013107280704500009102c03180380c070305505510648030320310300300103004a0304400800d44401900c0600f5240c170034601b07291948000000d40d600f0034401000c60301000000c0212001445c4215100c0d251158081008030400c00c41030411812080201c1d106081031038803000a002d240201e2000a000e943d001420000a41900c001580a4404448580b9014000f4074162000e8103041c021080858204130004105034014640c110651b00143c440e5419070b82040030134078980d04448410b50030405092003820b90080000024200e66042e5541c48603a46807007400942034a41c0c48080303041c2d205040d0b004100380ca0740070943d40c0e0381e2603102041c94500900c1c0c500062541001941031a4140070700344c80c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 122574514 1250 122573264 122573291
    0xb0406090303021b1506060c0606011805030a050703060e010203130605060d0b09060402131b18050603070c0c0503061603200d0c1805030a0201050304030309061a09090a03051602060409 81
    0x1e110b1010341720305101e540d6a51402030003501c0c0107a904c0c030a4154051b10101e41a503000e06001d050850f40000c026180c0c0741c1d901d000906e056840103080d142900102e9081c003d12a5500603000003000d400000c1d860340c00c02a041081000300088060300f40c030b80d0381740803131166919405942c1803603070460102c03105030401240f150344481090340c0403803007a60303402c0f02c040a882603402204984e64904001d07000c4c0b04440c45066030024045001c1142480c0603840100311561100c002e540a41400d0baa0901c6034030280c130b0410125159604103601c65404a0100440ea40c0e03020000303422000607280c0071815075405e6204000b240c81c181c8401d00040400302d101400c1030000d42c01400d4a00e802e0b5130b0720343e0b5501942c1d904450f11300d444c003869402d900500c52707040155000e20b009540180c0301c0e1034001354003400394580008440800b500c0103161983c010a9290b80c0c5800103250f03401180e2140500603a0959035405001c40c4906002d11040c0d0a01020b1142955602d80c107442c01048801d17401d10030800940c14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 122575764 1250 122574514 122574523
    0x206070303062607140a03050f010e0f1501030f02040e1c09050f06120403110a0c05010311121602010605030114010e090f0304210515100b070b0406090303021b 70
    0x1ca400300f0302e8101e00d510040d129480c00c298001c42110203040700c103042c200c481100d02c0c6038a410302d0308042c440b0300000020b82d08002214101c550b507800001d103282c0505d10b240c105507511014695661190f02101c009507001800d50741101e512108078103841c0074610120b00a000305a142c07845a0044000002c00d40000005040a801e11580c8210010f03894004104600300030b045102e4201405109030f11b68500076001d1260002c0c040d0600840e80301c80107130290b1a2565031007040301c407080c80440800c00c550b0507003d84440282034440c03075818003102120f101401d13036004005103200c3c040b0f85020b608560007940300c6000b509024000b8409440300604c6185c115100b8030608400c140060009684c9403c04501e00b01d0309100e40001c0c514081c548503d019000324000c0c003880e0400c20014001000a00800c0440c00b600300d403514450451600440341d50a50b80a0362021318603c03002c0048400080c80c18080551042c2d03c0000002c6110490030201e000307016401ca1035940724801390101491190014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 122577014 1250 122575764 122575769
    0x70c050d051b0102070b01031103010c1407080910020f01050f150d03111b150405061b1203090a05010501170a06230108070e130201050d09030e060a03020c060105060c070501050313020607030306 85
    0x180404049c0c005501814202ca520319408000544140c1802c42c9620042c801800014015010760342012421700c0040d0484036a5040640941d200103006c20107102e0070301660364803111031901414640340c02e0700c4042c10700c500c082c2c0c035502c50509007903214201030061195031040070501040b640010350740501c050706030190b818024441c0304c2042c00700b00f014012800b20303010313103501400a6007094000302c004440c042003c0d002c2a418002c58210120018081019501c241f08010081c64440c0c901e0030503a00311201031700001d45c40840f440c24501600310014100d003216902c20400100b0307103130110482d00c4c00c201d120012034204c5c401d400006081e030750001c0c0034000c2d41c403020031218850f200d05000b41c3c41c1035074410300240452014041d0480d080000e07032007144001e010742400c2c103204040a0000307a25510035000500480e502140a8019840821003240506416200c86280421445059944d400280b1519041203400800144882c822082c0440000e6001c1c0c0718075100c15540c80c01030003408160 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 122578264 1250 122577014 122577023
    0xe01060914030609151306050a090b09120301180b030709090209070e300607030c0201060806091209010909140403030b0118030221160806070c050d051b0102070b0103 73
    0x1980807086440c0c0400c180d0b01680b07060b0000c05000325000d0080c0f070200002003441842d540f0300c130503c0d40820200c0c040c2c135200d403001300c1c0c0c0003405443d140f600f0403440d20054280c00b015400410000c02d00301000c01224191605810920101da50f1031101801620a0b0303c0b8054050181000001707201801da0800401d0b80d1007180c03002e00c47d68900c48121072080000f1f400070350214030030419403202400d0000c050490700e5003000100248254552261420074240d5100c00020b942d10f42000c1207550a201d8000030b000313240050205400d0040c0d2003603413402a4608148024400509040b8603800348081100502c01100c0a0001500d140b407121400c0030b08843c207a02090901f454589158480d031840300d8080c5c0700004040400d415a000d1054044440b9059100081001c00c107128810082118440f01c2c0013a58480540d141040a12030402901410582c14803401d591014005400072541c1000207402d86070840e00c42858000750480881e00f04c00d5403020354400298901441112000b81d07050300d019 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 122579514 1250 122578264 122578289
    0x1104060b12010612060b030f0a0e0109051203070e0904031e030603020105070b0619080c1f0203030f040c05120309010f050405150306040f02030903041e050a17070e010609 75
    0x15014001894414001d400608612020041c008580a1012040c4581078030000084264940c4900d480560083d510a90000148001c003d0303601458018520030b06900402404844502da44580d50380001e48a509810300001c400601c446100310321094200200400204090825080c09840640d5194207400010002c20303403c46410701a0140780c04503a03040c0e551030300d882d0382c5403a240c0b58114060aa541e00c02140640c14080040b844c2c003100252013610b0290860400e6101004406070344104403400e210920302c421789042d030300032058990101c40d400c00136099648034500510801d4441d00700aa1061003019101811039002024091804085e03d46141c440420002901c0d03d01462207a580d000c2c00341c030260f8161945803005542c10680203040462544902031030b00050760003c80740071402da0b001003000c10956041d1034100d03c034030206034014000701c1d040a02191441510b400361031881d21403c800c024101108105072401012101948202e030750312280018580a030611a01045521 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 122580764 1250 122579514 122579519
    0x3050c0705030601120b0405010b0306010f09150e0f0901060503030f03011e0b0a0311070606080d120509030702091f09060f050a08070504050c22030b0f04020d08030c0c0a110406 78
    0x2c0000d40c1130f040c1d5801000803080c0b9280d580d284407414000074021181d03552141401201601d0800c44580a0181c082e000020503091824400866120319003030dc890101000c020854600f18403402c0b031704440050f11845aa07a02c81170309038090400c682c4415003500c0005034060000c01060061810b036408101030a100015281402740300f12114024000e601c00e080088004d001d000754441d140800c2e07078141c000d04108490722150111549584000d00315000020900e900e240d120205d560351701c07610b00080140b030404180c15503480c0541400240940041e44c0481c0c031540b00490301018014803c10342d841c10540310b10810300945428132805510f4984a08045160b141420400782074403181d0f0014910903240c039042002034180580041a400820001603240703480040d401796038407001c45d6400710030500d1441c0c100f000d0340000f4501040d414a803000c2c000145e8072041d4004407250000ca40d01e4480d21401c215001c0351062000d05422880303205808000c12900900c070600c6d2000840781088800e5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 122582014 1250 122580764 122580769
    0xa1109010602010203250c02090108060115051314210a1211060406090f140f060c0a050304030804060209030a05071706040c030305210a09021003020a0c020915030a03050c0705 77
    0x2054506249286000c46c1500c0c10040c0c21400c008070859611744031401c660030740c010900c022001e0f0410b0206820040040c40301c1c40420318a042c0c10000c502c0c14500d401d60303d540141040500e4022003000c2000d41c58400079558800d00003102020403030220320701d00307551201e84a84da484001c10496a59651003402e81034036000c6c01410320200c410201500d842c1e6100e03030321030f030042031500c1c421070340c010381d40215402190a0a0b080707030ba000080401003001c50340d500746d5146050070043c050740e40c4e44c00800c01600b80341d500805a94201d54181040212900c541c5040000307401340c1e80e01c1c035402d4401c1400380d000744140000c50320201c41c40c410b0707503140510015031841d441d0702d0200c1e0701030181d4054810410000348100b00400e9506658802821003582146030001c0440c020342d4003074099604d40c0609019850701d10740410403031156003000c43c500071400c2c40c064518001c625001c0d1151801c0b00018881d540c0c2c00240401c060b00043c01d480042d1040d181c0501941c020704401c0c131a42c8200d000200c0c0700d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 122583264 1250 122582014 122582017
    0x20319090f06050c060906060d08030c0f0307080f1605070308090717010b04061706160c060606080708070c2609121f0c02030405060319051006020d0203040b03060111030c0a11090106020102 83
    0x3450094005410805035465110003540702813300c01d104c0c00200107640140c503541c1e0245005100e00d0303403000385904014411140700c003005000d0000000001c03261141c959041402c0710015035042c140080380b80d858003034490038940c1c40d5001c86505480c40f004018140c1040d800f00034000e604507400c01115840e01e80c49101c0165010880e1025840480400e0500c41696204108440380e442d15030f09120407682c410b429143c281e4008404a0361600130306c1a0140c101c04c0441c0d0044092500810f0260b0584504a1503e40c8940071790f0b00740440303c09078031a6071244045a00411002e801052001d210b106079a41e01e924180321411440e03181200d04000c41e40303034010803500190a0f801182001e041c04100549584043c080c0542507000030561107444030342d401054411100c4004441c501882d103000a030074080440d0b034020454000b000144012940c610030f980e000700081c41c04c0c04100c01034925252451080d84480c1c84948190f42c04081007100360080300070000703019180300b003c03030f6030b2450300785d080c1d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 122584514 1250 122583264 122583271
    0xc030c0f140f0105060d02010305091e06060405010b0a09140d050303090601051c0c0b030604020415030b01030506030109231f05010602010c050a0219080f1b0106050f01020319090f06050c060906 85
    0x616038131051b400356101e41c100a801a82110594109081c41050911120358240d10b8514981080b0108a06131409200d181c5c010011680000d1030106040300c02024001107002d00011100614803148458035040580400e1a600804481d030301d083c21440155135040c24820244165907002004604804030301580034200e81c002c007003408030790429100d66030b241c000600e01a0450343c2440300203440d6a401b003140240741e1098600103200d400c544001015180003c000030f0190b81000314400000740006603040d803211212042c89504a6095811414583d007a17941380b101c01242c07402060001e00562003241207a02c540c000b00800c0360000002e40d014010004400b001d44c10070040104040703c2400f0091441f423040c081e161a0810b44505010701c0c2d00107107104400f07203c01210b02641c0d4182442590054842103030500751071042800001d42c0e034414880301c26008070b40c0405104105000d9000300006d4a603900744c000055454180c02000341c0c11440c0d602d459440b4600c0414462070020905500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 122585764 1250 122584514 122584519
    0x307050c06040513020901020a06060e0a050105010306120809030309090f0906070807090e070207180204051305040f02100c0b1312030e03030a0c0513030b010806090d0c02010c030c0f140f010506 85
    0x74540c411303280d80070003074111008141c103501031503042c140000c84510401005e0411014002600d0038181001e00840d201600124141450000d0030321038112182c100500460340114481c1c2c3e103070700c004003190950051920160300211000140045070111000d42c0340304400d840c00b1103030140e4034144121280042501c801000c039015007414825084500700c06035000b900f600484103480e540f041581c41603110000305280103a40070400b84080d10702200580e4518038041420f00c2903003044d4880c1440b80c8440b880091041411401052003039010f0500502803d420206944040c50990a002b0320a120628122807894010402010786400380c03040039410503080d0015411950307007014000c014101030f4460424808144405020300e0341c401111800381d4411000c00c030302c031752401490744e18010001c0e05011240e00f10240e18590a50b101c403155200741d4091914454a02e1a0b0409030740308110450040c005000300307280d002c03e100362501c0300c5426481d050219401164140c004a080b40c1d0152065503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 122587014 1250 122585764 122585779
    0x50604031211030a0b01110a0b070e030a020603151c0503030a0b01230a0302070b0c0406090f0e04020904060b09071806090324020f03010312030c0c02090a0911060a020307050c060405 80
    0x208000b10350751120312420010f052030000080001c41c92848c004c0380e503e080b2488400c007000c105006a2041c0306200228060f80103054405140d40001c8217404010072070351a242920303421030340c03585d03411024805c81e01c80341c0303c82c2d00e980303419050094032a441103078110703003543c103060304040a5481a20003402140d101040522401110402192141d0084001c241019024070819011801e450011340c0035014440f10b8590b110f140c84c02c05800500316501020300e0030400c0c00c0c10050701249489060b030046d0b045030010255134952420b00020814082981d412401d280c08000d80c56810900540a16403074050240b0600d58801048031100c5485c00000e0501c4402188184100540d1090003454a9448005418021144070000982c2c0090f4001e40307000564180c1040030076014030900440c80001d2400f503007101c1d00c40d00132451040c2c01900d0341c0300c250b80c0d0301c80d01414003001406238683d00f00000c1c07020395191074560b400bc1d43c03900b04120079295805070784039030680c6140107001c9804840003d4800c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 122588264 1250 122587014 122587021
    0xb070209040b0613020406080103050d0c05031801020717100e0c0a06051810050301090e03040608010303110a02061303060509010612230601090905060702060907051909050405060403121103 83
    0x8041d490340508040c1d00a05001d604110036225400500047c0205640d440071540c55030400031301d0320308244961400d2185c40c01801e0042140481110400c2c1c500d0a481c4202d6151140102d2409100c1d41c84501424004041c03c260940d012035841c64603203400780280404900c0b59440c13901d03083c40640d05680300314006010820315006c1c00261040c1c01da03416001121024000105640000e044210300000d540000140300c2d1407080c0c482c000703002c00d444008600709410080003603e680411300025046c010000d80c05c4001100c20450501f80580c003410154070b41e20030305200580d680c003034003007281c1e82d608040004405240501c01c00702140c2e02c4001c09066607149480700c62840c401700640c1400340b4880480100401002c1042e07500a01c080903001482001da4144141045806881901150803020501c20003030701c001401c00958004a0307018086d500c0e01d0301c540c1103103c155804445214140001c11082c800d012a60301c0c4a28000d8813034280c2110340d42c5200c42141c400080074410b031001403000c0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 122589514 1250 122588264 122588273
    0xa0323070f180605071b06080402011b0512180111030912120a020d080a0902030a150209130204030515101e0305060a09030f14031503011d010c03060b07020904 70
    0x500c0012442c24810382c0d030440d82407020301d441803e411420229800198500420008941c00345141c0000302e403107260300b400c001c4010b100340005403010b41007006c004102d0a401401280440c1d0710b40c0e1101c22220b0340054805240200d03080300c4050b080382403c88401c040705500030b400c2110324480302d20144d0314043c0c0f8007007008120074810248400d1032140741e502c06002f98401000f00b40f81d10490f001020f010b180140014000d00c40107003221845030a0101980040c1c80c00104640040d5102010800c2034805036a01e9000303016582c0030301e6001c8d40036280001c06078003aa004200796800340040d03420003000003440d100070b0301040d9454880c0480c1c5620800021144188042c482e10100030144c0302ea942d02c0e19058a4440d01b51250245c1d80d640320716080030903400541400c0011a282444403c0990300c403a030f80d05a0000901c00301010102c81c141b2445a5000e501c03202d0306088108562900c2480c840400307000304010705402c4003081c40c000300428441e03818415948252760041c51200180c1d200c0c0c2c1c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 122590764 1250 122589514 122589527
    0x6010812040602120c0304031401090605060a060503181c080f010603060806011202030a0204060902120703050601020c0d11090103081b0118080c15011814040c0302100519050a032307 80
    0x108000c8501047c040400001c04200d0002d4011050314000705102d401d0b81010310480310042c0040388140d0218004001960700001a00e070300544105414503410010f141e003a0518040001070702080083d951214101031300881c03c0c600492981d15407003016a01d83c038040d41220914011175080c0c0d40110010001312a5072450700303004074405002d5070702d83d2074560301103400d0b01d9041d082243c1480d00031401040c0b0300001c3c04810f5000e03903a0300c0c0c00c1c4000d0428000103521281d01e0381080d40038003048a000070030f00461804203504c18002a1003c00590785d682061040c0d9046015950410070f0781c00d0f01c40304964014050000500031420400940c45151741c4c03621410381c000c4c504100b940c01801500728003003112101007402010341803804d420802c040780e0440106d40341c21403404403403180d460910010950402401050369410b40d001d960280b1034031f4007610350780508421640240720328516507003140c0e0f201e409000b000714603403014000800c9001051001864111041030110036140004490350700c40d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 122592014 1250 122590764 122590777
    0x10f060f03120513090515010c020a170a0c0905091b1c050c030703050d0e03150610140304080a0e03060609040602091513050a0b0310050d0218090601081204060212 72
    0x422900c4d05080711015242c4045943c0b000f41c11030340c1c0703400300500c07003811143d0007260a074246000005400503500090000131180034061744007101409100e04904100020000d481d0804a41d41420380d961001c40d0151808840703100e114012059411013541001009402c0040001c040b140c200700041c41610381c9503003d820544107885400d07405000c5840c00e1103c000130314003883c041d2201043d10701010709101c550f105400e0095001c6000030442248400c40c40b504144e08460b4030341e400c0700d080c80c201c55901c0c000842842c208400002d21082040b407030003c0070040d5150315103400e0200071004158035640d04980750350b003000c0454006000505240e004224024008100c1c0d82e6003e25220180d055410043d2403041c0001090414406840d01d00e140364000c00030704000c00c0c41c5183c07580014100d06101c0c802c04c2e0040b50030821110456550785032500d18000d80c0b07504043c152619520140e40c804003841844281d001c0e032003803049142e520034111000d81d001500107110400081c3d000380c0040d40000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 122593264 1250 122592014 122592017
    0x121020d06170c15041205060a0e030c070b0a0e03070e011a0a050a1101150b0d06050f0105160501060918140c0a030f0f0605071d0d0b04030f090e0117010f060f0312 72
    0x200000324001403840c0e031481d106c0d0301a0700206814074190320041d048030030b080100180c560052101c590740c1040082c007030082c0d8103a00750f41038480728030724003d4607079a02c1a131081d0b0745405004004120183e29503102812a0255003032006081e444100500181c8112082400000c400f00f0490380828021440b60316140c0c5110f000180c5c01c4070014181c01613001c26040101c0600001450307401010703040c02400081c0c0f0f01200c04540380250280017038500e1040072840203034658042c001b401401800e5001100a10400c0e200b8445017402b800d80051a00c00c0c10001c03641c4800404050b040264006156054000702914845030740d421900d40c0404950803007400c84482d038408905078001a0903010f05402201c0613100c660b2110040703490340e5089009844001d0060300f40c0310200e004070704200107142d04541c0504016017001002c01088407000f5880d0080c440300f10024000041001101ea211441040080003c120010089c840ca10683c0d205100c2c040001034081c86c144040798100c0d503084000d0145 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 122594514 1250 122593264 122593267
    0x30c06090c08070b0702030f1b1302040906060306050405092d1207050105040c0e0708010317270f010503090a0b1905090105063303060121020d06170c15 67
    0x1642c0c4140c0c5010325541050030358010101e800000c60400700006503055944d1005840c4241c0003100400902c004140ba040c0710b0038503c2e2400840c2c1102340d04039406018a4102482980d44a882c00f5000d8440c5100c0c450103140b0707050008040801c08030b00c0b01c0000d80c0a8007280d4140780030b100d46004c08601814003a040b405529242d40305440d0742801040401c1c443e00000c5298a030606214420503c079a00c20884210340e0010807a1b4a54001c500605580d030046035070801d010810111419030007844d4012a40d162002448014506252810200c010080320740da42c1400303d031401100c1c54007041d00c0c02c0c58181d10012840c000500000c00032035108281c00000c89214052817202e030301340c2e44180e41400d03550359540c040c441a170505800c100e980950744665401d000c80301e01b6282450703a40d80807084403421404030124800c2e038464070030f800a1581d040b04c405242c01c12031076000001c1d482000c041303604600e04100007034100807520703c400359181e00f0b40290a51220800a00ca0f54402c1c062280d11404030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 122595764 1250 122594514 122594519
    0x705190f030f0501170d0504081005070c1505100b0a050d1a090109050702060f06010509010807050408030c0601051e01080109090321050609060303090a0b130807080a0c060309030c06090c 82
    0x2c52003082d00030003910200c0b07251645801300712414011915034a00c02c100c01084207204003240080d0101c800c5c901030500180c0343e600c0b0241201d011071031110003031090f400d8492844018a2540100340240603c140b065102030b501d00103a051031141c5a0700e54081207082c801c030304403208a80c0c440701c0b0205400010038146000c10b00001d81c02ca80c00d03001540c50395521000c0c0b111655042020175440380820503e00d1080c1414030000c0c00c40e000e40b00c841c0307040150480001d41c0c0284614180c40082181c641200d4440d2001c40d84161210302c00d005070780c0150a03414440480303503141001c5070001c0d44c040e11500311503400c0c0307013104001c0e101c10719090f000d224401d000400003500380c03400145020ec601d0070000e59030038440e0810100c00300103480c09119500610100e521580c99145100456004104c07075a070740c50019a03501a03c3c1000d520180150003003150006603460003280c2000114440c2e0030241e0032a8640c00181c0845111180c00f50000740c00d65000710000701d1552113401e40364060f84004410b0ba0313 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 122597014 1250 122595764 122595791
    0x9050907061d060a020a0506070203040f1404060503030d020a180b03011a07020d0c03060c08060625060e070608010b030411010309060e12180301110304020d020111160e0705190f03 79
    0x10f04c040410700042c0d2080c070126090190901c01e060b0060114400703145054036045202c004680c03e80100c00e00c4030a03501084020b581c8a03407041008110103421359031945c0c030f080948000ac0d00406d002501141c020000f0455556a14203d003080d10000c4500b58110307420180e42c1b4031640c282d054007103944039040101d040540e441c3e81883d40d800b03200b4221285007504503d44101500c041920f51801d000303108080c042556503070000e0700c2c640290000f10101081c2c0021500122580000001c1c1c1501e2400e401010380550110340c207400e640443d220707021b10b40d0f03854880c00c54902c021100030342090060310030344000e0741c42900f18075803090158001040900c1c414800a08001740601214041d510008004009580107407068034080c0048008001c0da440002c8503103000d12004000030300c900c90500e81001160301403124407a445604034205c4a00030b20104a01e1203103456402100e81c0449190002032160f441001115198612101000844440d00905464058419506406150300e0b240c075100501c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 122598264 1250 122597014 122597017
    0x30c0c0a14011508010203040515130b10091416030911060a0807020106051905090a0207120905030c09040f030c031e0504090605041808090a15170109050907061d06 72
    0x15074031000052480030030745034403400161a5220f001c0d503900520401010510220b60401d6040c4551b0b1070740070310b6441a0031551200040a00100341d49400c2003484421850190f40205640c004401080150300d070041160076464212201c4c0da4584107102080400d500c41d0f080302d050648104001c1c01c5072404500010066004803103002c0c00280103004200903940d0902800c0c00408054803902100190144111b069121030f014003402040d400c4c01040d680303182941158000c43d000400204030102d000002000807029200c2c85101e4481c4c80c0c80f4100c1c0d03190070785a203030156038099803281e401240748d0340655031b0f0000d2100990601c04004050070660489000c0c0c10342040c01c581d2856911818103e2083c100c40b1243c0041d40524903001c0c5a14032500c6030b01c401c52000703810606180d00c41143e200010004c2c501500000145009018081c45050704400102891120611072603010b0782c0b0b0380c22030002c50700c084030020b1180d44002403c03ca500d010f418960094005072405180b01101c0070080b034002d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 122599514 1250 122598264 122598293
    0x24050403050901020c0a050a0303140c0703120206060118090c030902060a0f09090507050f030a02070819030b03010905030a0c02060912030703091401120e0f0105040b0105030f070506030c0c0a 84
    0x100d040001d003070340c9541e0b040c0117650040c0401c668080000e07082502083d60b60446000c010244039101200040c0c00d03111303c00380e03403800c0995412201c051342c4074070713001e820100d0300302e035820140c46660041030b11076000c0e000540030100083c1051510358a80b00d115400740c01140403013030034103950320901c0b400340c2c032041e004000320446a11400d11211004100400102166000c403c0140c80d210034844840da1050803200d414032071403400ba460303071103c0403c003009100f020f0004214220002c0d115005540f1450302e100c148103d0f44007000000104070034142602c16004c40281550402c01824122307500074511282650f0000d84803908140449001c9460240316420280040d480030411008069000007070401034004090740080024ac0300c030000c0c00b421f80181c010f02200c1e4070341e1014004101304000250078800c03480020f000d01c2c102802d0900f40c024080c040c00740203004010b595040240b0009160302245c10150500e461940c40c3c03910300d5040c1e006101c0094103070041c01d005001103002c81d0004141e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 122600764 1250 122599514 122599517
    0x2040f02040609170a0f17040e060a05060c0703020405100b1605190c06050307260403020c010c0209040209040611070501020d0b040608100e0f07060c05070501020111040324050403 79
    0xeaa6040c0310018160340f52640c0f21002c824000000350780321240100311181c03265407084c0b40101000d0a8501488101c0c0c810b407010203800c00120f00024490b4004498901480d81540c0c00a403043d125410b2217041d21484183c0b004651011004000500302a031003180c0c800c03008024403e40c1da031a85015400350744100000105401000301c04414007074140090040203428080c0d01c1319503119a40c0d60103040e501481a103040c8031010000a0744a80100d91020030308080c1481181000048045101c08060903103040e001842052a171000b40e502a0001807a115002401c800c41c5a80f02d9080040702e0400500840d925500c1c2c895008100c0040000740015500c580005078640c1142005007080b100d98a550521445c02c00e1810041c001d404920740c100c081400c04042015a440e80c00546401800b5000e50068810361030300194007507002105403100d81c4544160760005688000490903118070648800d0004020401007002404007014600414181d6850403c411001840c074021210f04a80a60 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 122602014 1250 122600764 122600767
    0x106030b1029180d0b090606090c0409020306030703020405010f2108030612160b04050a080114060112140406060512010606050d0b0d080703020a050607090302060a080406020702040f02 81
    0x2030528100810031020300303040b9a81e0800c510321085200754000e95806621603100c400100b418400240060800c0c03054409402002071030910701c0c0c60b0030081800c58402c030799801900040b40e071503d04990b84030300850f060131000e401d05082c104c3c1400291303c05401c0c02d50501c54518004010b844502909000341265031034034038a14070b40700c20040c54040c0c48a00819904603a413804000900303c40c10759070058030944d040341c40000340d02001840c20341001c00403000e52801047c0012104096401407068490a4030181240d5030b582010500b0b8410001c2ea030505d13061a540000d11359440360756011403005401501148407000310104205809003540c00303480682d210a0140400e040504c268003560341030780000c1100074541180140039004403010454419190110200b59a0f41c00001c5042c09070002d040301ea03545554500a940c5180c0010100c0d503d0003050002082e07031f400784c000c0004030b98000c0d000600d0240e42140c00c840180004008540c200d6082c0507800140c1c031070b4410104114101c1a005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 122603264 1250 122602014 122602021
    0xc0f131d120c0d0e0d0501050405030d0f02040815130803190b01021c050f1b010c030b010804030503010303120e010207030324031113060515070c060804050a11030f0106030b 76
    0x150030060700c1e0007011180c05040105038a4481c002500e6045030300c0614084200220203000210000b2480201500c00c0d82440d041c00207001010005043d0045c10810030041c030616002980241d001d28442c09546404c0900c1d031124039a80c15203a40d41c0b00c4400720421507100c1569951050a40059402d44000300755800081c40807020b51040c2d4628030b00900007800104003440e4821505a05940810b0130004d000c641c5201e040c21107130507500c480c005440800310120703505201030300818120800b10002030070a18503a00341d500400c1c10034002c035010398950340355030b0850720165881d007603440100e694643d81d09040c402c40e400038400780040d2407290f500410551002d004008640004185001d2040b010110030400100311650100903200155012030600c0c44490201009200b954415500710005203142460800000010010701d48641942e02c80c01351a040d040380c0c00c540448004096520a41080c0007188200d04151200b10b40141200c0303106030f140c880c003801d41d0020307442140c5100340303c07051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 122604514 1250 122603264 122603321
    0x307031107050402040b160201031d03031902040825120503030603070602060709050d02130c080a0c0203040311120106030519030e040c0507080a020304050a030f02041404050c0f13 79
    0x1d00303008200803507042d0b003040d05025082c5c949101f95400306a103600c50901d160110390003500315200c550b40d0010550030000c1ca4414440c0c03281c0c003c4880f5910800042138040b045000ca00c25101983c010070010051740306490032181d9190010760f03501ea5081503105001658a21036408501c40d68440c101440c0c49050880506142080e0f0390071070020345d003140741080015513110107403108640c070454407440d102d2130b41d00105000608069070305542605055513950f0494010030001d0050034284402c1180400075001241c40c4e0040703000007001c0248402102c83c480c68408160340c00030810100004a407a40ea985252801c03401408040c56a10042d0b8440289600300c50300e0480302609440c140142078030742c14002c1091207808030040420802048418801d4820019074000e0207014043c045041d031070b814411740310410200700b24031450030400c400d0380001d90442c0083c01039902100810742004104200403134000d070040855003022103121480c11503c00750185613500c607000e003141c5200e03220203080c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 122605764 1250 122604514 122604523
    0x3020405011b02030d0516061107020310090f030e0301020910030f0c020a0803010b03040309170c09130c0b31050102010e0a0c060e01050c15010819050c1309020303070311 75
    0x70b03080c0c5505112100c1e5809618040789088a403549490641e5440f0003c0c4e00c04481c40c0f450240103070805141c801d60020441c008001040c08600072001c903850a00801002d0f41034030341881e00100962a000c580c98002400340c009030800c0341d00240050704008000c07011031004c022065424001a803075070702032509003400744128802d21400b48081c082040b070715140d00c41e05110601c202c1c1a105400070014091501c502000005401d13403202c50070304903114403c01e40c2d4824980703007070038824160100801d101280b19062403c10f241d1100c24943c800b4900100d101d120382040c03034220f00380021003034000c85446512100c0d040c000d840361820500036003020700081c05c49041000c0000d45601c9600c9400104002040160881e4003519003107480f0301d0000d004841e180914002180180f00c0d001402d80341002d8441c0141c10b03074281c00100d071640389049a000b016810f02c1213025000380c011103280719140c146880008120160401d02007542c151560209145500400040c1c0018200a00d01c0885604c00e21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 122607014 1250 122605764 122605787
    0xc0108130b0a06050a0f06080402060901020a02091003030306090c0e01030b030f010f0e0105010503010b15070204090f030c12030c0f05160804120b060315160c0203010c0e0a05060a021903090509070302040501 91
    0x40130001b000d800c105000c3c2440f10060b101910401e004500b0001d168420445410401d502500720000d60070700b0030011103c10b03024003049000c01d0404a000c00c0d1038805100d1512480340d6542c0700b025048904005400414051094982500402c1200e42542000f402580c0d040c4084d10400039040642807e0282100d170180c0060303100707904202031a2481c1d620f00d440740c00600300310700269999441602c0090000d0060042c01016551107003514011705400038224000903004118002101482560850803140303e03c42e00030204540540c00d03904644940050241c60382d41d0080c0c030702e1942d11500c502120350410340c0550302000024507018100700c00c0d0381010340c1006065005101d0030301310160700c903002d00e4021f1008201001c02090421024840c1e1000b004198019000b000b555a01d50001046031440c610707214000c46c207507503001403c0d09040003281d00403c02c0390b0151603070003100c54105114400d140000d60400c043c3c0c440200f250f07070703440c000030b8051400da80b00107070750360b14103c005058007a404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 122608264 1250 122607014 122607029
    0x708150402010c0201110f06070c150902031f020c030427090209010b0a1205180705030a02090f13051605040f020c1c050d05010e06011403090c0108130b0a06050a 71
    0x840034000142d03000640e88202e940c0c2401c0c00d04402c05041402d85c076060340d0758420707001e910035807051091081d0442035010b0079a0042c1e040705070720b600c1c0300e08403426603504c408025059405071040150000240e40702c1d2880d242101400b510f0504003100c454655003081d04544d0310304804a07998004903000b82d4010020304c4c1a49000e106203034858001035440742051240462400c40040d03601e100741d1003a00200d00d040343d074080401090401540584421280c014803446e140324ad500003140071b19001400842c003030350082545900780d40d40b03000d5400100010f080b03280c004031a200d0007000220184801038071440100c061080071403802d4100003d031948160010803203403040100160078070700410300c4140b40000308051349416091010440380c03807081c81c800600c428038000c00402d1400c1201003150040509a8440c00d56003000042040144015112660320b070740121110080d039400b80760102e9110603e01041081c85020b5180c00b580000219031408815940b68028800e92600d0300c0088003070300c500c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 122609514 1250 122608264 122608303
    0x50f181e03270406080d0e0415090c0306031712160e0d0501050910020f07020f06160c050301050601082a040e0c03161803030305040c03020604060206010611011b0f020a060c020708 79
    0x103c1c001030401001801107600543e201c0501c003103012746207449140104071b80442000421447d80c00200180300d00d00049442d41c0c1c82c501d414244041c0d20066032030740a0f42c01c0700381a83d511802100010f03000342890603030a00140b2006080e10350f6824407007911030340c09440040f07190301d4004a003038204201d84040b0501e1610501411596800c1e1005581105906540e10408840b0303000001c2d07450f00079444c0c116a600c410784803800c1000030142018007180d400760024040c1d0b4a4000c01520030320022140005541d9040200c107600100050300d0344220440b100c800783c0391544580050840042c1203c0d0002e660714000188a660f0401d80c1c1104260245441d040700f45c00c0042201090003100e0f0f220280406440703070046814400d4201c0e0600c0110b03070003440b1342da540d41d5401001c0d445103803d02c00d031004101d03c068103020300320301801400d546a000e061014541c0001810a031072480500046030700314440c07001040c0c009601d5201e01c520500b8182c005040d45403418140078074010303400008034041d250 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 122610764 1250 122609514 122609533
    0x30304061803051c06050a0815060f060f1e0d0603030e0d051f0204090219080114060d05090f0703060b1003110d0914060109050f181e0327040608 64
    0x107120b0b041e1013540d80410b0304105240c01400a00015012a800c907641c45501d2072030016248400042e200034280d03d60190412070b690b80020019006206164180c02a04c204400127590000030001c10f21194211100d108030706040c0c00c0d69050760800045003850039134610040c8181504810851403103001101d11045100f1960b0320261242d600c170004e030030310400032500150f5071541c5405590190a52040071901c41450610000d0440301034190840070510800001c00d505404510300d03049500c014011a142500301303205107000300001401c0180034021000c608602000c103114460081d4040d94020500120000c10002c0d41c01c14200404241807030304100d50f0703010401c0300c25989143d40768400021020098201082c0c0c0110740b076009038070b601480d4000700340306101b5440075000c0e81070400040403503519074488921103d40d1303c141d8130140d80014a00c82d4261394245804508013040c1007a2814003e510141d48014900340302c035903580307a00b02d40c4035010608061146800400d443c078010503030002c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 122612014 1250 122610764 122610767
    0x90821040308130308040b120a1e0203071103221e0303050702010324050307050607020904060e0304050d03030501081b0303090d02040b0a030818240307140d0b040f050c040501050c0a14030304061803 87
    0x2905038ac1da801d0305401000203140e00d401038450003264109031081c0c03039840d281001d06d130303400300a1070040c0c14051105c1080170501a115188000b02401c0041c20220103078110344050311140c00c0000124100b544400010130403019140c01003d00107454450a100e2901300f030101403c0000c640c00080c0981814005000541d4417020440d40140e000300c0f000032961103244001c4e095101c3ea40003140c02c96000c030a41d404240d81644018101c40c900c1040c0d85845240d840041c4001e107070900b103554554010b102d4010145010122960000c3c401400002c2c00c40e94080420903050899000340c83d075040100300014410710f0030ba007103010b4072022201c000c8504440c0c1601400c00240c04142e074008036010000170303101d6005039404945841c1001c1c00d15121106000118003802c5003020950145081c0000500010200d01503540141244c13541c0a0401d424000110b440d9000032071100040d01c22210002c021521100e41211b4814025000d50340e6481d10381045002d8a0f0246440300103408641c1d40700c00400e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 122613264 1250 122612014 122612051
    0x2030a0c020f03030702030102031806060102070b04060f090915060212041a1b1005010303020c15040501050a020a0c0608100803040b0901051810090821040308130308040b120a 77
    0x5941c101c400b140c0d80010040480d185010b4408001d41561000003480481c00c00000c4140302c446031071007101d0443d60394600498803240030703100e403c03805d01c01808144815030060b003005004420900d86001110b40d1011800165a40b8484001008034044024410310340c0c10702c01044034000484041e46400d1600c12149203c05c8a030a05000840c004240140280b0511740f0f40e01115541004568940c1c0c040141c0760000c00082c8000c8015100e5031684c48001d050090000b2074400d090b40800d81000d103450010f4885510030310f0790200b1805a6900a0b000810801054000d040d031540c0340181803030302c0c3c20140c0328103106401c000441d034401d00c0300b0403021800600f1150700b44000c0c40d00c1c68980002002582181085480040c1d1098642d01c1440e03400303a018040c4411545020101c89014a851401d03040020800d400d082d0f030321800700020300c0468070542c01403e459100003100c0183d10381c0c0303886044003600150010416400c0c0025648460303c0f51008031030704040c03c0c890402c0382012444100c03500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 122614514 1250 122613264 122613287
    0xb1603090c090203070207091b0e04050402210708032d04120609080d1e05060f03060619150908070b040e071202040503030c1507090506030703090804170109020306060102030a 77
    0x1503d800100280c0b609101b070001400810300c020341840384560608807540c400e0040d601460008403000203084952805010300c030b0085801600081070694910344201c0c1c81c0700f4140503020248a203a01c0041c1d0510100000c0c0000c880040f000d000b00e821407407160780401e01400c0c00d0640014180001d101820300c01c1480100b070b6900180005104000340f43c1321010340123144540c0c541e54545200c3c00c0382d0314480c071840207115011900030007850380d0342001c00c907640e82d80306880b54169001400060003030600c1140c807025440b00145512000b50b0380c5070001a06901e07c03a0801c009409000e0070428104200403101c090b14032490344c1820306081c262242e110138802000c41e0200586003851004501c6980d04076409088017409a90b42c0b1152b54107219501c59007020707400081c07000400002c480d6445440d0600a07118000d20103440d640300e40e00100d002c0d0818140941c3e003c40c041100042049440e01d0280c0000e5449002017036003002c80c01054180000108150b041d500704101da240c509034403c1c601000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 122615764 1250 122614514 122614529
    0x11805060f060a03020a09020a141e09030a061503051516030c030f0203010602070e0604020703051909050a0e06040c02011a0d170301090912020f060604020904090f0b1603090c 77
    0x1030350382d40d0400007000c0c0562540003a42200ca1014042030844460300201a10200c94450701d2150155800301803c40c460130b06a0a01d4090a0500e802c00b201070000a20302008010100c031643c41300f40e02e454049404e500d0510703202c00000d17401001041803c1c44488221b040c150030441d4246096080c0311001d03070604441100301f503074070100c04500c00d020350b001c02e00000b64902c0840d1030b9a141e030740203540c800b4180100030381000b40d0400142c140c509030003103424040d855a1140d04003807281c417142d0a203400c001440c034140100100041425110654180e000705030140b41c140707041c02c00c00c06200072241e060300e0440c00c5904000c906c11554000000304c54001d00142c0f41d0740d1507210103040078140310100b180384100c074040c0000005840c085903005145414015418400b030b40300400d4083ea0307602403030385010400743c120100046091601e940074101041d0301510100741c1c04c0b030350354841c02031404595003161070b081010284118400d0740340d00858035901e14101008003c0060302c0e0b15071a100da81c0f1520703a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 122617014 1250 122615764 122615791
    0x4051203031014011e021e0115032405042001020307050703020108092103010602070503071505030a090b090d090906120f0302161701050601050708070611040515040801180506 77
    0x10b0703d40c3d00c500454419083e045a50400044c07100f100203417900c003103035000c01c503c1c045196814040c2c0750600c902704020382a80002080e40b032640d039580c0021241c00206840101c0b002150b40900d4410b8000c080c8141d204c5d1030b050540741c200a000d00f1040c2c1404843d141107600c240903181c0003941c00904282543e0b02420070071510750361940b629290048541e4450b4241038040034003400b20700c1900c085d6040e55000d4080e15641520381040c50750f036a946200b0080d8068450030a0140d0f18000c90045401026061000c0f03024038054450051030442a94840416809546d42031007450340403003000003505d0440014010a454008402803090f5000e801030305e51003c0d1222501014000c02c11540700e4400f41c1e28103404070742e403500082e4981a084001d2850765003802300042d0340d9031091007120300540d8044002c41c10078810751140c00040094152130070310103604020200790382d41c44600e00300300d480494a41554480c2881049403d4900002011001c1c100b0b040400780040d101040702e40c1c2c405020703140007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 122618264 1250 122617014 122617049
    0x8030d09080d090606030212031911030d0203070e0405090118171201120c0801050606030c0a02070938010f0c0f080a03050103030e1212130302060c03040512030310 72
    0x50640c0b29600c41001858944250501000001d030003d034200d82c02145d400164210380201d180d02c0b44101070100800d403d034071140040c254090600e0200300d5100c4401c890604200d4045030040b81e1003aa1034402160f00354510316641c3c82d040c00b03000c1e0f1204141009009920350709503050700c143e9120900410303003168050080c1210300743c202900e030154080d03280c490165a58908040c0b8021041c5419609914007140c0481d402e0414068107015200191401e440c43d656840ae122464005220140450142d102c000410410601482c160503d6803042e0f082d989840501450b1311520101b180d490020f0b003640da56640303a8010440003040e0185041c1504690000c1c0ba00c51004192a070000b0700740080441c1c20012a981170380114140c83c07294490600100001080242002c1140f52544059008030820811840e805000d002000741500c0b02c000c031035032254000b8986800c120420b41d032179400460308010701d103001d54440140d0b8400714003030351443c00e0605000501d800382c0d021f060320250300768940 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 122619514 1250 122618264 122618273
    0x70507030e04090b0601080f060306070c240507090504090f0b060d0803040b0402091e071101060801060801020904051f0e07050705010e011b092403060810090302070e0108030d09 78
    0x15060201070040080107000c107140b6040511410984007907002410b13000000700c0c00c1090603085401040c0c010014801581d507e01c00b05c8010f492410101c580720080c0c0c41c0c0c80840000c1d6061103049103d401000714283c504884024104e03000350707008a100da404e04204c50045584190030401d00c81d00031261031219a26800807440d500007142c80144252000010041400302c9811114010b40c4202c4501d51541c0300c1c0041c2e0340054089038103240f1104151408a00124001c140680c40070399101c00109070076959821043c00c4a00a500270903541c0d40001d400866441d06201d425809105805030351a0702a84c0c44d103103400c0c4201e50060340350184500001c5012103000d4020b54400a6101e0000c0c00080007000c0c481303003c0d000d08000c555882a100c080086810300840c2d16605507201515495492800407a0083d0208102c41818050580d24000841c0c000018071101d14410400780020800b6029441c0c0240307003035030640c0440c40500c2100c0042c444404040300316442d070070070050003064501d1a42003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 122620764 1250 122619514 122619527
    0xc010b030d02160509071205040201030e0706080402120312010b0d110a030b03060703020c0c0910170604030207060e0a050f0f1306080606090f0f090c060d0b090a0c0807050703 77
    0x41949841000c00d0306444980c00200501581040005180040c0da40e13400d01c14612000d03101c91012695481c03046500b02400c0e40807a078007900514022440e485061521428111705410800004040104110560518014038041c10080000440c68450f240d000062181e9060007403800b08a4001030b502c8000c00c041d0040f160000692075200c5d40c519680d50003500810007013480500070301800b00015205406882a03402c0100c408001c1c003800780e41201003107800c2c0d0f0b004041621503580100041143d00d803502e42000c45c5c210380c0b0024141420181000b902d0040c045c0d118000700000c0328045960340d190040303900708451094403108140c9103a58001255a0038040c003643c0c02c804100c0820403e0045504210201c40d4110107840090700c60f5428020710700e10031100d50160032500700100e0b5a0803204010306a100c461300d815103018008800000f80b05510009580660070345400d1101c0c00c40c5085081c44c0e03001181e4010401c0fa001d5403520142a160740100400309016010500700c040c14091f42 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 122622014 1250 122620764 122620781
    0x90a0c06081906260a0305090411070c0e04020a0f050f09180610050a090b0618030a17030105040507051306050c030915070501060f080a1502070f03031a04060f0b0c01 73
    0x20b070b06011050721070504000c41014130035128a00162684e00104108010030b203066801e41642c3c0340c62900c005641031001601814210003850007080150300049260949150041d1120020050641c00d05004200d400c1c0301540100002d40c5080804110940e103010f62810411300035940c040c07080d0746195601c01880d1a5403503003d514010401000f0300700d0006107920096980441301d110000d030316114804122000b02811503001081044101c0080103580c0d0b569441e40c5008044030882a4169121080801160241c2003138400201c01401341c0d18050240b5a8000440d00c0d0403400d0034060401c681e80c8000034807a01d03040c400b0020384001c0b0840f003130048440680003e0b09074500e242540c00060596030111200703407250351a085000c030700b81240e40d590b0411a0804802031114001c16241c1e4005d5003040445004455400c00003440040d2080c0c1102a201b40039407000103040c4008010309800180c100350b61889289001018860100420290f100b075841c2c030350485840c0d060b0404110300522050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 122623264 1250 122622014 122622061
    0x4060c0509031b030105070f090b28050309011b050a08060307121b0501050a02030a1b0606090203040302280311150c0c07060c03050a05070c03020a14010305090a0c0608 74
    0x41d05001003c00d40300d03c9505003e01a030080006c0c2c3d0358100308940c940c080f082c0810000711002c0c0200000c20841010300505104907000341380300c2500e6203001e107c413003e00302c07041c0120f600442048100802031284012042c07000c0a00703021040d04a100610510074040a10b060056080c041400703a1400c111040140c1740c400320198545040342004202c60018190a04110300c00300408074543d403040003503c4141103640c00650801c0d10011068880c0e80380030b4a00e10310082070307040d070a0224600e401220b00401c0d207468016600d0034282802800d250a50391020000c4d0008103030b000c0c0d40d03103043d00300b0600d0135090318100f05440d4894910608101c1e0152220900505141c14412924801001458a030b000e020417242510fa40786403d860380d01680c10064046102032000e040903a01580081070114818100304048030b03120b50002e00c54095641082d606c07000b010b0016651075070584140358000140b41d006102c0d0220583e9650500805400b074541000610f03400f255501d030038001140d41e0904003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 122624514 1250 122623264 122623273
    0x80a051e0702030d0608070803090108070e0405180c0907050f0d0e0f0f06090d0801031509050d0e0301060b07020307030f03050d090f02090c130603051308030f0f010b1204060c050903 80
    0xc007000941da5080034004100a51900d48002a030040c002110000c44882e0400b45040a4540d0010b542d48900188203a00303101320b81580b0ba245940e10311030103220b411071551403510241c0380c1c03400071b10700070100210074000e0072107406100c80345802c00f0689014005110006658401c000e03001c102414032182103610f64441c003030b44400802c8001c00d5041d007010701034040340c10070f69801100036906e094a00b01003001c134448000500100c1c08181c40200f162600c00b0b400700e240c5a0780d6458030319151405c078640b4006088200d41225a02e02800340f840200a0412518284510340d0006a10740310513100040094146002c10400c150144042d0b41c588001528200312161140c103004008480b400e20480c4600010030000b881e0120780010340c0c00e1480c607180c10300b1042d0b0030310000303400611000d40a280e2042c2800d411500048100e00154468401d00000b2501070038000c3d070101c10100103803c80740c280c01050200c245004d000402d090b5026410403400725088680c010166800d1062031055a054080e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 122625764 1250 122624514 122624521
    0x7020307121107290301090f05070503010b0702011803051e011506170a15170706032a120228020a02060a03150f0801091205041a0705030d06080714030303010303080a051e 75
    0x7400e42c80841c00302d82c0d0701011701841c0d82b040821502c5210900442c442400700348000e20155106181252484684180036a010344c0c0300d0f141c140c81c114102183e452003100e51031405c2c030310310320030300503a112440031801c2d420343e06080080c040c20031b0700311401000031414400e00092904420b5008003403500d10072079005814503159070070024210082c00440c040c45c4914900091018424030980b030011081100480440f11201031043e0f1a44004412004101c000d4495201000f5148018007403210702200c100c1140000061100c040642c904110056400c44118503004d038071540201d0705180100c0c540024480980e03001c44403107190a401400f40b01c1100000415244015030083c4890b90082501c011440e41c405006c40305d52085026114243e4581121554604d01040283c508036200d1400c3c0c03803d0241049002046038255401078420747e11020042100c1e488800103401d403514254055403441d811628080c10114002d0300080c0850b0740e550008007940f00d040c10440300607041030681c080608 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 122627014 1250 122625764 122625779
    0xc1603050a110d0804020d060b1215100e070f260604051b090402070203010b0d0b040b0a09030206060616050109050d0e0f0a0312050d0507020307121107290301 70
    0x100301501c004085088045510141800055a00591101540c40e103240741d886034240303c00401c0d901d00403128240c40300300d402400e0342c40090380003442940e03000500c010a00d04610742d01240001e4140260301103104401d00c40030b81c084240c2d991040030b9040c103010742e00314004c003240c1c004081481105482d12150500c4a207440c2e420580d40102c00480c2c091055440d440541d0074802c1c0640d0f20707001040820400c49095040c5500644080c5000400000c0c012040001142c400c1c04e20300400c83d815644c4204000400c211545204d40111040a0401108020350340195072010f02400861282502140500600703200314503944840d588680280440703901481c0461303a0300c86000c1c0e20804604040780c0c0c6c40c10750030828040e42c1803450003400c02144a1941c1c55904070385001c29054000c002c01040140700011150040600400d500da0065540da80c40b070911042d022048940a13081080e000001010045c002500d403041d103000c94040130401d55809140345034500082000000311802000021b40e44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 122628264 1250 122627014 122627017
    0x41a090a0b0c030a030b0f030a17070803040f02040507020a1505130203011a0a0803090109140402070c0e07120c08043309150204030210030b04060b0c06060102070608090a0303050c160305 82
    0x4040648083c42034140d1881088401020461f030290150b000800f010007042030040c815110166200d64585840030544401540764001c440588030112a86404c90031800c0502c40c041d4031100764400f4040000c110380e9144400c001110f0300b611840d458102240c40e8804640c0702ca1000c680c02030007044481d1541c603116207007031641d0320382030310071008058000b030101000f200719240150169079039500b25007880c2020342c24411480c4000e8010340e00303212820000c0c09800c0c03e00f0240c00c1c0401c00304202e2030108802031001503c4544501090b041c0b200101c03000390024111504164000c0880c44001d9420341c050481c9034002c0b880c90b0190598849080036034000b5800402941d000d85201448050b80c91007800691050b88402504584081d55040106200383d118040c080c2c00100003003402a81c40f10030711155040342c601041e1a402c980c05200e00381d030301040313204020001c604051345645840c5500310344442c40400701409243c0c40c0c80000b42034106800032140801407100303001d4200411400c008089 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 122629514 1250 122628264 122628277
    0x1101030b100c051c0f0503090c04020f0309060c071e0201020c100c0213050403051e04030609060606030b03011104060c05190507030302070f080c01050c031201030b100506041a090a0b0c03 82
    0x2c50040c400759854045080d4800781030130442e80c40301c0c5020030503e00f0440d101d50000302020528000d6590400e4035a40c5c078001000304200a1a0b05522070070454030b55420803030f01610441c04001c0400c070020001f80f01c3e1102200c1801d480701d00c694841d80500041c1d007010316905d90307141d20840e20141c07418044d030008501c2510324000d4074003030891020448400f0455805490180215900340501c041c0920040c020904141480310100d0400742c0d20364980c010b4900c0384204440a0b901c441e0180089589407207020785102d4210b0007805101d01c02034500380a80701f14010740042001d043e2510060040c100300700181d030b00101201d81e080000743e062a80d280c01e1140400c0300140691400010702500f851000c600351840f5101502c0594030b85401035846c0d0b48010011100360005028000111100322513481c001d501425246e56035143c00302c5085159072254001900c2598180003d000c400050010382c0743c404005400d5076510f00380c1c400021100021a4812504840000344004c0424000b1006c4c0c4070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 122630764 1250 122629514 122629523
    0x80106080309180403021501030305120903090a05040b010917010605030c0a06020c091015030614010201020a02060a0b041506020109150b060306012f071716031101030b100c 76
    0x10540c650552039207922416401a0b4060760b090b0803503450782c07035004581d9003142c4030740101d42d07003051180b0b40e8004841d0264404c3c0e011880100c1c00c5240030b402200c07907c1d48480c1b044041c40c0381001d0400061281040750280340e0161fa0b540ca0305843d035074004d6044201800400c54407081034a55007290fa070190216001e514082d0164605034070a500b03021443c1004d4840c80c0d005001c1c400c00800a00158034030041c1215820021b04100060140d4040840d1049260980e008900e0390300340b0107013248d10070f842e103a1141107a20412094030a00d80c0401c0c11604040000804900021a000028054007846c05030b4106150b00d182c0000c0c0b007a4055012240b00c1d4800c010b190410305a02d0035580450f400c1c0710305142c200301d0420000b042c96116800281d400103007135009220620019034440d22040c0c41d111480065030208401b0701c51415503801d1807100c00076181c000c0042003071381c09034100b240c0750b588401000c02d510942007141d20782c042e4004041e030503070103440e011b2400b80300030b03004142115103503054a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 122632014 1250 122630764 122630771
    0x60c010908180f03061b3001080f0c130609140406061a0d050415240902030610050d020903150604050f0412050a091d01180504030e120102160c0801 65
    0x602d2070800e01c880303506098000b00908002c2d684d03d0314904003032808502a80f00da00d010020702c1d2202c040d141c400648042c2a001803a5810070344582e83c07d0122041c6c0100c1a00d900c882c40801e074400c80003a6410042c3c0c410741e0303c0b504184c0150441006400380b03801a150301801e00800c0030140d1040d50030303944a40d0003500148999580c03070380003ca8404c400d5101d0f00101d04100100c0141c44801c0d0040794000b40300301070f03443e070400c621a00e4208a0f40900101509010a0038600c000d1400000a034009417414403c11403450030401c00154103a2001c105e14418880c011400d0481e01200c1e50680f4607407200035060360000d00146101d40802442101e1942c442e514050100345008002c2c3c0c91030b4801c55020321281b685114007801540d140e0440000e00c070400c1020800030840d00c80c421070901900f0759540c8160115418425160180b032030803e01500740b14a01800c01002c02d61003410344058080a48084841400c081412406031041030200b45000020594280401c402a1008011118800000c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 122633264 1250 122632014 122632057
    0x60510030e1b0a09050f10150203040b1b06010b190504080a020f03070e0a0b01030f0b0306070503060d0f150e0a15110d021b0106060306060806040c03090b04050f060601050304050a0b06060c010908 86
    0x20380c0700d2200c11408c400107a00c18441845442d031000014203050868100349060710344c2800c140303807070441e090f040041100701c042080c80701611620380710548241c850078594202070034502401c1e078407044202c010780b241e980d156294176030ba1020310850300986265029548280390a090801c058801d5185050000c4e19010900c60341030182d00c120500c0800041c064610360301c90700000c5800350000342c1501d6101c01540245400201803241600f4030900c60035803c01d114401d4221a411a00003c60315011078100302442c400180b000c0215078110b00088900040390320405040c412140a0ba00c240d0b202e4503c005420300c0c280031010501e03004004688003c0c88400c0d101d040031070690718107100d00d401281d801000300b80c903854150000c907019a61440c00140701e131010348554000c1c8500342c40503599901312444c013000b44541804007a5000400b820254a181403d80d52640e494600754005840f484800d4007052480e0307541021150f81d80001c000038070030b06500d818072800c20352104100c10045020020348 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 122634514 1250 122633264 122633279
    0xf090606040c05090d020102120705151305070308180d2402040b090f030c030102130306060b031519030b0118050a0509030405011d060d060510030e1b0a09050f10 71
    0x82e2a640112079607032504140e0800c0a1044090410404034150b0145080500b2a4500ca40162081e9401b07230780100022100b16040c0890f00760702400078000407040c1030040340840c00c0015040d04aaa00c00c84040e540c807042e0900301486246d110486901091000042040c4000c013080c41142d240004805000341040c224510224032842c0f0a0031a499401d22040520b4509980c3c025002c2c5030140c1540d80010f87c0d030380007a08a034004104043e2040c08100d00b070051050522030b1901070054040410303c2c509140750003840d015185069613102f4003940c844004e001080050368002107501494201e420758413069081d00c1080300c0100000fa0030302c1d200000314141e00600800d401501c0010285192900f040300449004080101401d0056100043e94500303480d4980140415002d5880025115041000308095183c1c1101254201800c01030b1f201500e00011035240c12404982d4000304440e001000442c500c000c440d0303c000815443d000030018040c60f4401014480c0f402500d1034070000d1f4603000f5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 122635764 1250 122634514 122634521
    0xb0904030f0507060608060f1b0c0a060b03160801021b0a08030601030c111002090f0102010b090a02090a0902070c0905010e010602060408030604180c030203061e16030b090f09060604 80
    0x20080c0005078078220a0303002a020301c0003407030310502403c004100b080c5c484298a142c100c1c2924081002c4941d0310800c0940c3d19288078040b6034410380c0c030105140840319250359a9440c0c0300c0341c000c0c5c0116554814040c2c540e40820105111541c00c0017103a180e10b07601c0a6040c000c0d006000112800354610484c0c4810343d40c00315000c007285501c114081d046880388001100244500720f6420309020807125030f1140b0754010090081074140e1090301680d00e41c0343e001440540b90b4541d9526055a0400035000c44580c4d40041f04c1c1e03480012142c0050715142d0020000750250700c15886030181c980300085030700c2806a604000b13801e40e4000401804280d98070b445110285600348140c03c0160050004a40024155802103130056030041001c10b104400c03c21f58031130940340c8501260260341d528010400c604040c07100c0d99003d500d0f010324507421503002c8540c4c01c1d1100010150b0050305181e50480a64a0081d800000305e0310000c1c01c1800145040c85451100710400e9031881401d215110000350305251901 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 122637014 1250 122635764 122635771
    0xb1f0e0403020109020909160e180f2b02030a1206090c030501080c1507080705011b030213090614010507050a0b0903030709050906010e0d17031006030b0307031a250908010b09 77
    0x14119a6a482c05a9027100b51174050b160489030031841d014985411400c00075034490b5401c100103070014240c040403000c0788804181c194000c1400e100850400d22750040181c6408601a081c101e0543c040c000b4007100902c100e80280507024544416054540da140d030005069800000886228840300410020891005801c5a5050341c040000f00300061003200540801d6100307100108423480d600096441c40580503010b07400080e404640070300ca01c45044000d000810a0800030401c003814610000303c0001101174071814080005603c2c410000c0400000b800c0070780109c011002400c00a103115141d074410f840178400181a04000325680c0303080d03040c80b070042ea8140c5030040010504418800640b40602040e03c27034803800c1a24840c0b61036440001c610843d10351141415580c00d200000d0100c40180d161113010b548806c41c00d200040c642c860103031000014090b00c4041c1e5540700110700e5001602120070b441c02c14071040000249420040400540740654001c2c0002c41011041c17055039001107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 122638264 1250 122637014 122637043
    0x172b09091104030201180b0d090b0f010602030d11122508060d0b15090a060503011a0607060b03120d0204030b01120b040201030b0319120f09030b1f0e0403020109020909 74
    0x100001c000560090a126130400846541c0030000d47c1c0d01c3c80880503035004074182c00d18060301c2e0021001080520150107621034030b00c4400058a504100000f5541d0042000d0150083d5903810703241310f500112010f8580c251100d8924003c0f0b03260036a400c0b150702d10b84036a1501503200003107080d04528096201c0b10b110321005001001280019129071030080c40140c0144c0119041c1c102540803529004500c602c10002410003090140ca03040502d400c664080d07600c0030709201c41f06079529480d507c2d00200e0343c446400a4001c82c4410f5800e00003030805440c038040803492032000451214194060300544100e03030161603201c1450ba6241610131050500103002490354641d100000e00660113039110b2500c50700003504940e0240c050301c08013030311001400c1081d12071406071848482e13595071001981c1c0b03250303c4610b40106650710750b6071043c41c9214090250407400e09010300b410100400c5220201c0280b83e411540031030303401d103818003900030b0640510590040080380005503c40e14001194020701d480c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 122639514 1250 122638264 122638267
    0x6070210110705030a0801031e15020702030f060907061d010507021909020412060c03020913051e190b0303090616061407050a0e090f01172b090911 65
    0x404641034018885007150780d030324541c14040d400102d8410800340400340c8070354a0f45a138550440c03c3c09480301d6030110f4410078002801000c140002c00d500071090f819540100c015880300010702c0005c0c100120b440c594400c078414081001080c800000324a0b08036002901e848221b109907405518086c03584980c518041070f400c0144400606190205081219802810910341ea454842c0c01099134019880b580540b2880034105090125620915040c1086424118545129070000c5103400460f40c0d02e0076180d03513944000503130541035011445200f45038255020300920b0070301440d40c20071481107140d040d40d500d464184042c070f040001c1120800c507002031031a4207001c0c1c085815001803000003811141c0030345620031540c85002d0201c1d114088d0800f6200d45071a14000d6a0062501141e405503612408a0000b4019a00c9000320103606480107079006504141800b00300300d182c0000c1c442004a407644144544440000591042040742010b917101550b141d0740750f410780700b030b21005800d035103101c8070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 122640764 1250 122639514 122639533
    0x206011508090c04050a0603030305011202150309010f050a0219020c0102030d0e0f010e06040203060a0605060a0503092a12011104140312070b06040f0203071e091a0405030f060702 79
    0x14054154881100c40c00c82e10210300c3e035800701e0141ca01c00d99610000a0311014207104042e090f00429025003060f0403c0a916500340d0000741000001402c6190306900000105041d2042034029915010300030005101c10700740351514178020f60090241c0d54007500301780d105101c00e510100d80a00300130303c1640110300300014903a6240040070a081841000c0c49040c03898540d1000038080d1200d00e01c622009400e461030b00340103040c20410001c0c500500649081c40610150340d501056949102a51518948075034070000c841c0d203400c040140103140e0340d88410745401500400c0440c15106401616030a41d09144091210300f66060620f21901c1500144000c5c4403591b01c100b10315919080090885031207003034103038020310540e0107041c059848842c12020000c0d542094000c48020201d410011032451610030002006403002000c007201c0d01c000301d285460003d11a035001c030050301c00403204800380100300005455603405446554024001d507991410020b802203002c074403034007141d00609011007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 122642014 1250 122640764 122640767
    0x303070804060f0b12100e0f07031205040315050402030c040b0d0b04030504260d0c0308070e060d020f180603040b070e0a030c0909060e030408150c1213060c02060115 73
    0x4405000d044840d03511398113001e0554130201607420400b056005420121000000601545c1d8032024015455000c2c0b604400038480c0002d003107080785e401c010f210401c3d99000508441e1445660302c0500615031451000170f00c0300c0c4d207911a500817882141141c1c600d501801c00d100640752219a948c2c1d104c2d06540034000803030b410705042a4020312a1030118900b940794540c044506e40d80828001c102c204154408042da5820000b18001d503501e030800109451455a0042100c840103180408104c2c400301101d225440709001c1c0e8100d146204dd0039500d81c1e0746100c0900f095000440c40c04402e44400e40c40c10b000381451000c030f902840d0002c240c2c13a02507503800342c01e0311425100d202c2e0340d802040e0803c000021942901c103200142c041c07240d021442d96518180002a41ea003180c6210b910340040008200742c2e840007502140c81c0481640d455010360f60810216003d014480d118015102c02d1002c0100312030a40c40c5128203188241c0c0e00b00065581240b040740d40d45024003504040038002890b251209 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 122643264 1250 122642014 122642021
    0xc031b062a120f0b060c0a03110606060d0c09050a080d02010f02030105030c0d050a050a0605070f0f0207050d0320010519050f0403030b030a0212071802030c09010e060706110702090108030307080406 87
    0x4001e19000310b0212038500108445d41d1080103030b140c150304032090030001c1551004031008102680402000103050035070001d0800e2041c2c03c0207141e065a944100201d0300d0090310110003e20b07009107001005980c4007034840d281d40310800c00c040194a050410f241c1b007240e5100762070680c0c5001e802041040b10305014801c80001100c000e6402d80b150024000c0014820010b440311103101311000304070350410340070240801600f102804103102464050221880d400521341d011180111602104440316040647c3c403240743c1c0f000e407001e84514503400b491900301500158090b01d0480415840b100407804101d040341d2003519890600c030501404100882c0c400d81000646190040559513880c0f42c5a0009000a807000d0300e682451b00126010406490119032020103030060000075890341c513000010003154801c003e0014140080740e41c5915072034585400703031035a0961028042050f0410046082071a40080d08100d01c038110403000411040d5001c400c3d00d006003155110303040c05868995071507018 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 122644514 1250 122643264 122643281
    0xf0204020f04092a050a0f031509090b01060807090605030408030c0c0a0515180c0d05010e0d0207050406050609101d060a0e0901080d09060c031b062a12 67
    0x554600380b00110705083d40e48280250b8501030b000300d8034200c038103400186010072440800c07402d00105201d190000b64000d10000d080204a15000840301065048203844c14a16042118918035004440c0c0c1041840014103058a0454980d03510f80c0c1d45540044a4440c044c0c047e0340002942440824001440c9002660300140c40c0b106241c20302c01d880302e01c0e03881c0022102c0203507480d601c010511803070103034804501c0b500524042c0002c40009008031300c0d20350381c02080315014092144069240d060100030350060112207a401c0a407400b40201c500c00940d10f51850144c03520892802c0000145403404c84103c600991010742620010422440284c62000310032420355240040c0b01e07e06441c559480000303041c11812601c400a11b00d000b0703004c0c0031602234145c1049400d1350100801d00100c94001c500d2a0450b8110f280200404013285021914842e44045803180310303008820f0a410400c140d000b80c2840480d4604072400048260311400220700d03501c0072140440c3c1307105480041d602564000401c1c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 122645764 1250 122644514 122644537
    0x4050c090d12020a020d0809010305060f1507020607080406090e0f040b070309020102150c0a0917070b1b3414040b03011803080615030403050a0c030e0307090f0b0108040f020402 78
    0x10003040e10780114201040c0f400003110103900010f072380c0e4442d44e05882aa40c103c482a500701109585441c042180324240042140340f000011500714110b5450301d0840d04041e500500d41626140da8a001401d940b000b40100d000400c15100010100c2c1c1c07080c10628403840d0440c40c444c5940d11030110640080c000080f050b8110b0080803509140001c0d90f407512401100d00034016076850000c12070041462896401005160100f0f00d81822011000213003041560030500d0199520310354406181198048001303503600c8d50003591003121260700715000103040d92840c03040c6174154021780c0640c4088049140107915410480380c12460180c201548040300381000503000182c0c8481c15071740c483e4002d07503001d000ca000451807420004c0da03003010492140c0503003e6071703007150450419039406801801841c203c0410000300255440900d44541d889000c0c624024060f20480c0b6210840407001d0312001c000f0b82d10b51800e0040c00041075204005041c8105d400846d00910000309908120203988090070980 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 122647014 1250 122645764 122645773
    0x11041202011709061b0906030406051f0905040201030f0b0a1502070305070e04061b080402010c0c03060212060111070e011214060a0606090506030f0f06040e120904050c090d1202 78
    0x9003100b0842c403501c0d0203801c0d004004c21042c80c10b505440c865014a10103102100320038000351000ba1078a00607240c21a0b480100440d059075030041140c00d000080c500004490796040c40083e500d1042d82c0140d000781d000381e07403c0c811141c6003030758481070f5146010b80a80010030388004102444642d10700c40b40b15080ca02c103448990303036240c60342c85c9003001a40041031711015050512040010302d2060400b114110b0500c80301001100c0005400401c0007000030b4103101030111020100400342200d9406180c0c0840c04544440ca11214402455001c49171a40400d050081501c148035000030414200c600c07129030310300107a0a00c0c1c003c100070402c100044541341041454183c80d00c2e41849070500c03541c0e1a00e40002d0440c40e21000601d0140d855201c0c074052001001070001000c001c07045254424000190388003203072100c002050003084c00205051060251307034034500d451800c00009000817402102c00f80119120308005200c140b1030b841400703a00112000c02e810001e150b51a4080b496100c0d0b00546 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 122648264 1250 122647014 122647037
    0x180e190c0e03100e070e010614071b0e150915131d060f0a0b280902032409010602190f05030a121b210209040204090b12011104120201 59
    0x3860580c90805009030f00d520b40c2e5210540341010882d0000a00410300e9803c0d02d940b40a00c0502600c031208488403502c1c80004001f018001c0401c4000c06080c091035190030000da807502000a000001d6495100c00307407007064215a64500a106c40f03010b00e810300030004061103078078200040301400040f955103032501d6164441c010901001266201c1c000c80b0090406031602080307a19504000802c55190700745000318200300750b101c1c0207186060006003034007e261301d4107111900c0345100f400d90150780d26600000070041009606941080c00b4150300040120014040041140b10071003402220010781c4403071684030b85090074490f0500703001d001d0b4002c1074810f030840c0c17241030669001d5071815000c180380405a2900d0f10b194030448070000444d19007408910700741103004000c82e01890328854035007000c20002d601082c580e41121549403009004565031a81e480359800500b0700c484c181d81c407908102205009040040c000c03c03400014032240c661415081460300550400c00f94000c3e4104510300481 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 122649514 1250 122648264 122648269
    0xa1803120e01030f0e060610020105090604020d0501020d05090102041a0c060c09060f0a0c11040e0c0603090f300406050915040504090606030506010605070302100b030109020a06180e190c0e 83
    0x1017940c104102009401d952401006000100021880550071685898204000c620011902c6a0010b5049032603013202d251a00740f07103001e40100300ca20f62400313281c68107100800c1c00550040003120038070584101c00080001c10713605c460058100d82e00c1c541c2c0114002600b100401c074000e11102c280204086d007050250b072407000301c5410005500012414203501c0d102845195441c0d103000c2141228184041001c1d044c04549a81c25552044d008500101c0400c062580502c011031082101204460f140070455400440000700e912286000c22002122030b442920400112000e50314280c40c0d980c0f51100103801d003c6840c1307008001051100c41031001080d21b0340c560041c6060745000321400315003207003181002401c003d810780c8850288a42001100000f83e00403440b1081d10421890024502185c400401c0c0900f5008900030343c04070034403401003002a003100c0c81c1c1003108860400f44c0c13000d03516081207141130981030341c040f6031201600c40c40c2045400725400242c2080c19030b00d007029070039603614003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 122650764 1250 122649514 122649521
    0xb2203080306090112030f0c0201020c040c05031905071d040207020406090e1c020d03020309070302220c08010506090906030a080c01060e060906090112080906040603020a1803120e01030f 82
    0x200e40c61000001803100c00e107003050207603014041c002e100001d07580403950080c1c82484006e00304003d00c400e410700c5105681c000d0040440c5000d000d4010300140c2c4040c1c0b03005100364400c42d000000108004d254804407106845045e22800d01c1c1d448895070a4044602c10700508010440b040d44a42c0820001006890300d014071b80050030f4800c00400c80c071182042070360400c810411050405410100200b0a440d40000c0e82d04420100e4200142d69440d079500c0c1e642000c10a402c0a50000140041c03821841100b10b031110803d00d103400f040000c08503110044034200801e100b540c1d4494001d0000315001d29140c2c40650b08440020201c0e04040450750b42c40040d600b1644c03840302c0c1d69645041c1009034050600310315906c000100d03070011841c5810f5001520817903041c0104c080c42081040c4907004c00110b80d08803a41c003840104103c0e1180e660346401000303503000c2d507104000209800313282440394144400c0f61040da513001d040e0344100219803000b101d44112660301c181c10940c0f2440e424240150710310 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 122652014 1250 122650764 122650769
    0xa0b1b1504021f091707080102040303050307080f1506030712050a0b01020f070506030112020a031e1713090e0102040909060b0a05010809121602031009050709090506010b22 76
    0x444a905441c05004000c000d00110982488081c6800d08240c2d242c0d42c0482c02ca400e4441124081c1c440191803516180ba20f66260880029584002400b200b4907803c00060f41c4103072290360b00c00d981a03980d00040ca0412000b5201051100d44080407100c030751030400302031944080d240ca010000384500040d40c900b0b85a05480d101d0241d9a00d503205030507564140951220030100034000d01c0d1862801d4040fa200d8801407254041c0211524205000c664490113001c0045030052400c0702c249020151004241012201c200c1e81c884405186200c2150703040181c44400803040450b901c00c91030041c40d01f01514400e200d90f58155401c0102048200c0c072886042001d034011000081e0aa01c0c582c01e02070045000d4120078140300d1070108109a4580001c3c481c0c403038524420315103881e01c10030a42c0d01e202c46240c400095040c020025644482c0c41f441c2c2c00f0241c941d0050782190b09082c1d945004604842c141c60010300a40c111b00014000c10260900800c0c00845c0c0106405944e10720070080b0800c005c0a4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 122653264 1250 122652014 122652043
    0x90409031205070903030306091514030a1502180108061305150a0609091103010b0406030f02210403030506010e0a0501080c0c070b04060f1b0605040c050303360a0b1b 73
    0x1310418405d041e414802e5801610a00c04104291009103000b401115082d110b030b1000c11413400140c415a48082c85204c10b0180d122090035190305601145a010390810b48000542c94000c441c10b005961003400060702a10002d800810b20740580300c078110182c400207052030f0890b4600c1a408410b0389449559900030011581c1d85d00c0114280900d2009585640c01401c030707800700510042c04190450f00031901141d010742400140c0305074a010801c0680500d0750001035905821b680348000160510701340f80b0a030310940d42000303c0c0c1d66000054a0200e0001c49090f0000c40f0b41605002c1940101c544075080350305201c083e818840c0218100380b40000e40d4002003080f11011038100042c94114001c4842d00c4200d081203042007403001d07110341c1c07405140207019190750340396400b150a010164000001500014041c2ca0b80c030017606e2034050300c8030b4014401d00801c071141003640c6120741d0001000700c0c80702401420703500c2d60341c9030a405602c66044450404a030801d40150252620340400002c0c010000c40c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 122654514 1250 122653264 122653277
    0x80301050d020a260c0a030218041b060504080f01050c1b010e0109030309031706032a0d050607120608060109020a050f03010e06120303040510020c01020903011404020a05120309040903120507 84
    0x600d6002420b00250780b000d107000c1c802c1b000d81400140c0d125a6603004001c54602408020399450811484802071099050301e0301c0c03446000840c815510900030402e4a9000048950010075405103908072102161445007400040c0600140c0101c442140505400180008a0402c00503a40142150030014044002c0f0b6510181c0720105a04542d02c0071400c042e90000010a03c0c0040109032120101c0a0200e4000324010700780100084034400b2040d0791202800c1440a0842d52401c0382da503e100b501d410011407001c0d40c00040e44801c501445007a901000c0180c2400e900e408a1100a90070140030300007031150510140030143c0300030014500070064020b00180d64200507007400b40c0d00c2c0910442000c0b6820400403c004143c2c0080d04206641da010001680c940c0700d011160b00a002d03040f4001e40c1942020040c0e00742c0c0c030b0643c20f2a4080c90089541c00d2503a80d80d8801c010100d42c03130781e01185d4182c10a0200c100710b407801d40c2c00400494001d00f041240da95207410898201e400807505032012411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 122655764 1250 122654514 122654579
    0x1206030c03060112030302070201141c0501090903050706110f0c01050406060909031b02010203040f0308090306060324040204060905010801020a08070203180f1504121e080301050d020a 81
    0xa04008206820809401500a65042c2018068071200351800507007816000200e42045900c104420021022f903542600c2e1680c030392030301c1b881d6503001144401841a04120010411003410b22410444075410b80380ca903c0c0c01143e40e9803201410007540a0050718030240700c4d8401000311200100b0b0000e65000c000541c5261501d481021500705406c0581507600c7c003c2454002a000742030700b405004081d5003809021202e10040b840d40c0b007240c01c4500340b0742c284080001000030230405440e18410440036514907550f01020701d5a5144201e14001c20414101c000a806481a010042c0c08c98005007000ca4510307220b070b20280990304c00703034801000c07030394005000d5204036070207040144c10050b03510141d4500305c2080d04101000c2c01001003148039490310b4074a881e19603141c820a0307e01c1042070901c1a1290b5488400440020800409840c4035044104549070300303650a14154800783d101c2c4220b030030b40e400c0c003050081200050740100d0700010001c0c800300d50f440503c171314050041020740e02014a801c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 122657014 1250 122655764 122655769
    0x405060403230c060904020c0703140a14030306031c0302070501090f03030c0e060301170c0307030c0612050c1b2b0905120d0e0102070f031208010e090705040c141206 73
    0x80020300003a030710b0f400c000075155040c2d072a601129442103040742c016031980600b0605904024990348001c001410080c145500703960003041c0d51849500880055903e4440c40c40b2054a030f200c21131746160b042d00b200c541100b41408602003a5040281840d005080c81d00740d6680c1421138051400a0314803141400d43d034010564540034440c0182540d1030580101301c54507002c90000d003c18041d95592a4880f0700080d8120410070030500109001411509000e649003480c2e5058411405801d0000b0710a0240c03552403125130040d030380a01d1926016174904001d0051030800000004044001c50040c80510700900049042050484400d100342e01c01c80440c020000e0030000d029440300b8042c00319000e0440c400c100106101d04c0c6203c0600b0321090707148100d030040741855002e400c00701c800725440c030000c1f081c0b0220038450b203907100345501e8800d41a601c0303040b0042c440c0d1044070f44010f1644107080920050602d500070464a410720304064140540803000010740381c0000038402c1134012100c04000252 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 122658264 1250 122657014 122657063
    0x40e1501020a0c05040509010f060311090718060804020d0b0709060f03060803071b030203030a080a1404020d022e020105060418080d050907030606060804020102010c0f1b080405060403 81
    0x468090004041c880700320b80d10640200070a104503886541d80d54002155243c0039000b0641d80c4031030103402c0040540764a8040c41021031750203070b00e000310030f288000b41255003d41c0b00110940e4004407480d140a162010803902064001c0089030800300240a840004a1020007d07020710001e0329070201d06410418000c1c8030404104034541010f04042013002a2600802281d684581188862412800d00c4910303c1c0303200710540c4001c1d0144000146041201c0c1e004a0703140c001e080064003400368601c21020859001c00c1914082e520070b0325010070700f006140000301f0241001900501c80c12054001c00c055418100500ca0701001d40d45880421900b454603206602040e034928800221003542e54030340c810640610798482007280c0d5500e01003003000c10100100801150310420903c4403c0e260f0900500306d149c00d6070100d02560800d4840e0032032034050340001805c6020742ea140d0100c80c1d2500a02182c21045400c159081d210030400801c00b0b89070500140055409030307061001284920700c0303580e5034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 122659514 1250 122658264 122658301
    0x6150f0306040c081308031005030a03080708010e060901180b1306030c080604121404050d0305040303030f0501080c0f06040807152601050402180a03030e040f02071203150308040e 79
    0x30084c00d01c0c1001702d01c05890705008481500420031030b80300e1782c445030340c298109101e0300b020760705109046800d804c05a100300720900c2101e0565850b441030341c1c5e0314011001136100303031041540480d02d2001070044c2c0d07501c10061310700c1084100c0c0116618a54502003045018100200389802d03444940030f00c24000c1120400340142400700041c503040c038068441031201e0046150308010407011116107010030000200f52030113448010940703d041d1810345809015a40607105c11001b29003810307446000d008440c4110390480b941310001c2d0900315503103800c1010185880250315480b010511004c6413034101002070f58003030b0920488149560000b17400c050700280e082c402c40c0c0c0d03502d0601d02c00e030400070f00d1078200641103031410398000d6181c0159500a01181250401c16078016907003407000018194404200d10100301d0036a0100003000102d140c0d502a4804c154000d08408030341c2d0741c0340c8011842680709440c80348480c08014205522039441c00010b40c4251700612651540c801407004103d1030340d40e05082e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 122660764 1250 122659514 122659517
    0x1f030b0a0c05030c0a08100911030f01060203090a0527130311190209060d06141b040f030f06021204150614091807120c090b0103020703090b0306150f0306040c 70
    0x452030308000041300791080c400c41030200010b01002c40c4d00030b411010698042c0004100512290408402007801a00300300c0d1803100147d41940001034071400070046030406400601081c0e0340344c0c02e00081c8520b504500d44110003181c580300b0896200d940e1800c54038050780d884d070610b592500c2a4180200300d160807142d001e126402052202e4500744509405141495043d504540141d403403d000820300c4003803440c05840c00e03041c10410f40b8502a6030304c81c680306e206001801103907a0303800501c1c0d0100b401140a944040302440c20180003280185403000d18252061320050314054540c4110300090700291012102c2114151804030100058002c203000b40a03e0f024001e005209840040c41d0264042c00c2071003402c07100c411010b4000020701c0043d003c2d0400b0000081d8000d200d2030701c2c0f4006c180c02d04c9214002407900603641c0140d0300c80c0c0215180076805a4541c40442e0906108000d19031021b031983e40d1040409560080503025800500180b10b108071510740c581c40c0501c10f000950352008640340 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 122661870 1106 122660764 122660767
    0xf0303050403170709120807050a05060f0a0207020a03020402030403171005030f0c060702060d0902130209100201090b130309030803101a0915031f030b0a0c05 70
    0x6024910030f5031429106500c10900c900c0c4854103464001c0015912801000346003078022000c000e090103014203030314060f9aa82d8882c03810340d0780241140c454026100704081800c4c4880d4443d448480310405510b0100e042d800584003001d00d001c028032881d40840400d007490310807189a0044030303010034030b1191820302d600c01c80501842440345e80c2c0301384644070321000480404900c3e60300d41c03c1c015100c82c0c103008041d800c10026401c004400c400e02031340c90482d1005071b0740303000c940c1c208a4155100182d0b03034420300051207040401e85040b10150fa0500c8c03030102c0081d16244065610620450403101b046015203011116802c49038000b0306985404001e010418440c40d504004540180581c40d91500c952054420790b40200f60000b40c0c13000070700d40f42504800c100301c01198815414010b40344410012001480c40a1058100b9560307000d442d8100b04460702c0501c0b40a543e401d0608249 = true := by decide +kernel

theorem cover : BRFrame.Cov 122482014 122661870 := by
  have h0 := BRFrame.cov_init 122482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 122482014 ≤ n) (h2 : n < 122661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
