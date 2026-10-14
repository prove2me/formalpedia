-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2626
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:16:06.157472+00:00
-- url     : https://prove2.me/submissions/a1d1eb5e-06ed-41c5-a49f-0fab973bfcba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 472122302 ≤ n < 472302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 472123552 1250 472122302 472122323
    0x5031611030d140c0702030604060228080406060602030f040909060f05010e0103051b130c14040f1403070b0a1215031103100504080d230a020a021207080301060507 72
    0x1000214a10303000b104070004041e0700c0300d40c40001d100e2081091500911201951481c2c412250082991003c001e03100a000c03941c0003c14040761040145180c2d000c0d0740c41203c2c1203504401d4180148440030035601558124074244001a8031400041100c1503114803118080c2018039215004000701803801d42a6000d586805046001c0b03100e81c41002d018000d000c17000d41e40c0354150b007001850013001c1c1e208800c7d001d03503103442d4216a64551101c102c020041d440c000c20181c3d1150070860701c84503280e241d00c00c0070002150104540c00d110001c88269071020759140345141180301099034440407031144c00c036004001c00c200500d230384c417401c078009016402043c0410b210748180c280b9240e24503560b00c2610505031002ca107408074582440b0240c60001241d00520007030409c1d40b2000c000384544c1c001d05207410380c4c84210341d17130044815410403c03001c14041c00310198038091400c00702950240142800501581c0503212a800404d0241d50040390081081802c5d6802d10506444c0c540c0101000d42d24007610 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 472124802 1250 472123552 472123577
    0x6091b060d06090501090903170912030a20090102160b091023190507110f0a030501050c0c0105091f05071e030609050114030a02060a0e10170105060a050316 69
    0x1a00519001b000c580800107a0020b43d814010300c2d01c0800c03a42150000a25000d12000d14000203582c1d28104030324005580d00c1e02d0780141800140350f1030304480340314080046140d50b0050440040c199080d0f0a070252421100490300600e1020100e00500942e50014000c8014a040c101c8032400746d1b4103503003001c0350340c040c0368130768407815500310601000c0e052000550030080114808411603c5402802c003141050460b9460040349040c50100c540600c2c080c80840c921541d46220b03c400954000000308114281114003180b90f900030441982c4640c28140403d000035800642c01507541900a038103e8103a101174140401303440054982c5041210b05d01702c90080c02900c002040c010400340e200002d245203452111000e0b240140d00ca4500c0081d03e50070607007503480209003c00c0e160b5044034555580c14007070000303480c040b038001001e0303402c07007960245480c171183c0040c418004100a070500701ca5580c1c1c6d690070099035105610301400001d50030f1001c42c41107000c681209089400506060050340701 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 472126052 1250 472124802 472124819
    0x92006091503041b0503030703031a0a180501050d02060a0f020a080c060f0106030c0507080c071d0f01230904111215011a070b130515070206091b060d06 67
    0x310401c01c03445081c03000060008020301e081802d104400c0f0075900d04201490800042c0c1c4034015014041d05140d2594044070260450302d0f621800d00706c0041001c21216102c400207110604809241402907103030000200706403402102d1403220f030768001d042618100318160212603010700c0443e00401d40c410500d0140001d081500a001001c14840080034680b03842040360b4120001a0b020b0b500b410301d010300c4d01071000c0d403080c110b50390550829103090362a4180c1000c68030f04286a07000c8085046d54a187c0801076190090040c0115030760324002002e0398071501413103c408801c214501102e4010703590004582091035887d5405030240d43c041545142200126426103100e442503005d41c0c10120120780319141c56407455025000382c47e1070080c1820160003004081c0b14258000e080c58240800142c41040d038441c0d092045684141540c0c980c0504441500d19443e0543e2074a001d401103800180c44600002940d2032440c024030b0084410002060074002641d000305080702e41251600004940100c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 472127302 1250 472126052 472126069
    0xf0f030106031b140d0207080f03010914160c0b061311250812100f06020c0a140919020d0603050a05060907140906060408010f1e09200609 61
    0xc003501c01103002e80100e40d002c1d070410300c00a00c0e80103104c2c06031290b0032011506070542d002c084800800582d1070a0a04090400d40514002e10104410000000c1812501600300c010050001c075802c8107103842d0b051009031103501c002070000000e40b00f440c414000c0340c6035402d06500400083c03c2c44044844242303400c4291001411200d08080c4e00003586104805010780042c45403100c3e03210015030780d0706070b40d84025522030050030a400201c0340c0c01060050300c4080e100300c018000491801c124079510500a07444071800b0803090b12609006000040148903450020264080140112855550341d4000000f031220310740c9010516a003800700750804c038654400c00018600a80007840010b400f0328105203002c00c010302e040000d4210302c00130042400009500781b8008012a0b40c10080d60b03a40700420014003071640038443c190b013000707026800c4481c0f651104001c0034a60800a5424a090001400b80e801100006004004d540d19a403080305070040f500200d07a90041006182c802084002080c0d030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 472128552 1250 472127302 472127309
    0x40e060121090f0507080106060215060f06030f0a0b010801031104052d0a0c0c021e0d02041e0c02030901210204030c0e1e0f010323030f070203010e0c0303040302060f0f0301 76
    0xf0b40c1038881a90034020200b10b04001440d6050080c440c1508100001f5103407920f0b0109542c2c045052004688103540301149040744a0001e040aa100d1402d1002c10800780070644416500f50f142c451312034995441903040c1410ba0343c0180704010103820b00c0040c0001010014406641c0100b400d001140701594030100c890b440c415202c9552250a001b00705004488003407651200740300c0c40b6401000140ca030360340007605030741e10030b044510280802004600c0000348820f0080d4403500d060100001107804500c6031030640c0b804281049281203030b00d8160390303a00c0703020091404940024a89140701130981112030070401c603000f0150910790b4a40d134035001020150007401c0f45101542c200440410051640002c4d407074000440b0303001c0c0c14000d296500a03001070201034001200504801c10008000641024a02c07503042243d0b0398a003484001c0150742c0143c1000ca03c00e5003041420701c0c200030700054140c140c580c000e001e18034080c074641c2005802e42c8036503d02102042d05100780b138000d0002101440c000e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 472129802 1250 472128552 472128563
    0x115030b0a0e1213090207210e0907030c020c032116080408150a060f052809230405030f031824061905040506120f0d020105070203040e06012109 64
    0x3c907544c800034184100381903049401c0d01c42c07040c480d0b000820084c60807205203074030750742c150320b9a9510b82c1e07000c8448110a42d0016007105420081c45039155060f80400540f10141d401d80d01040032000405071a00c0b0988200405a4079000160b260321500b14001d0098020200d94842c2e41c40341035486d0300751034009034460940382d00003c01b403a1b440c0030110078113a4400340c5050200f04c41802c00e90b0218121000380038030b50280640c0c0c00311503108180a0310302c2103003854908044099903a11500324001d02a11000e420101c0080e004180d0f000c00175501090080d540000a5814560303050000f240d40d0300001c001c00a029020343c050460a00d00740b0144180d104100031100071001c800304401c2000c2e5002e000036000c1d0b8048000e0080d420f0114942d0344c1928400c80d000300b40750310b81100003072703010306151200c44c0503010b28480c0c6a0900707800a1000c0b44582d498009010f83d80e14882c040e40c480c05144101c5a1044070040080c095601c143c05da149400d8504408403080134010804008540c404001100e5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 472131052 1250 472129802 472129807
    0x20910170105070906050309070b25150606031e090c1502161202091303350603010c210f0e030a02070b0a020a02150903010e1e0115030b0a0e12 63
    0x981a44000313035102406a80c107240380385040c4075913a240e0710203562103104940340020403a00f1200b181d040c81d2a410704445551310803181c03800c0c1004090461051501c00d8014502000044c0b9580240226200540c2824240a03c23a1244d41008090007440600b110400702c40310b0045026030f0000302d1306440e81002c1d0700614003012181080c0703011501c03d07049050700f5615046034400683e20b14040992001c4905d50480c4145442e00d8103482013012039644410b0b075032a40301205070000d0701c1e45000c0154000310203605819140d0b4800d041c01c0316008051900082c0705001110308109055010300440d803000000020380d0200412904100c8800c0003036903c960300005074000c141e40e410003500029090340f890303c13407801c2c6c050500650b44100041c00203010b1611034406002500a80c029600c0350003000e002840b603030032051060ba0b06d4031000480d4014040d00021070703845a0005110345c116940400106000050458461050294000349142860794817400b450803480d90502c2400f01c8203498540d441c2c4c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 472132302 1250 472131052 472131061
    0x1a0402030405072c100e01031506031707061109030601290d0506100f020c280b13090e0d0e030a1703011d1009090201050415090f0603020702010c020910170105 70
    0x9405503405000c0180440b56017500f4030002000ca0300250460754000001190000010081005400e080e48050007880790a0715500b480c0000d080100850741c130465042181504c41c1281503094060030315070a130598401d6005208400111007000c0310800da0204d010030781403800401c1c150b264003d00900605a40310014004ca40c20040b100541c80c5000341040003001800090003540c0d02518a1a14840c150500b071342c08912074400c1c0c0780b004405903440460240b0791580255401907121503440304405460b5000001e06046909c140441ea4481b280900700928202030704443c4100607440c50b9906000309a44280020305404060105d6401c20f03a1f900e40b42d40c54403001480c1803038220030160360020f0503003c000c404a801c0072560150780880a0006000070b81c0d00040f00d5038007803a0008404060380c0302c0b0500000da00500c500d4122581c440b5421203440d15418114241e00132400000d001c10502170f0450010f1402840090b4041c62407000d1407451a6102ca460900d8007040885081e10b135940d50602 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 472133552 1250 472132302 472132379
    0xf0b01030509010504020d030e0105090607110307120309030f03050c06040c05040c030e21071a0109110f092b060e0c03070501080106050a140721031a040203040507 72
    0x70390710440000013000f684c90b0035004030342500a070304e02c01002c100010003214003d038002d409a9400307c0e40034241c55200c240500d018812840003c00c82031181c4180500082c10b0700e0f4428014414076856580c1c00a802d20319940c0300360a821043d8120b09204003400800c00d01002044001d1045008083d00098103142c0014801101d0204407500105410242d85030902c540020385813010360b00d0242c035208503011800005010340981c01c2c0c0101000d603c0c071002c3c141002c0210019050310700202d005c100c20541c3d40b812591070700c98001c15492014050060216520303103410828410090641011003605004900003d82e440c0604200c803496943c2d540100c1d01d007800c0005803a40081900104521410580080c129120501c03480c0c0810000143d100d011920030b40d000400315032403810380c54560156103004811413100000102c142c1640c3c000b034100b618481e024585902403041048020350b5400002e200195000510030307034141c400c003003000403462281c2c01c10782c40381c0b0700c503c050003000044240503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 472134802 1250 472133552 472133561
    0x307140105040b0a060b090f0d05011b023307030618020a08010f0e010e09070503061501170709090c02010b03030301120b07090614070302011b0908010b010207030f0816060f0b0103 79
    0x20580c13444e142200500c61400f0400c211030000d40101e45280e02c048584000816030030071924014015420f00c551512841c0000f01c48c10f0080c03e6540035982d490024a002c25a03100400320f21002c0390411310030f030b016118800050203401c0b04403031a001c40c039a03849500c107241c103981036000040f54590000380040420b51000000d0702500750702d01040c48032449d00c04174052468042c091101c0748071004011580522080009100402c0064183c80051524103004203250400300b9846021441c500e504200000c2102013892260380540c8502c4002800e290141c002009d03071841000941d941d03204143c250350b8007000554000d01600070034020a10b958505800710080c080c0100b4103008403400207000346900304101c4030b00711580000240d214015410100c1c05412003140c440d442450002826076900d501c1049003040d02d900100030310000280e41d004aa58080c0b42c07201134400301c074803014840014034280040c102c070030701c070784410684000644401040714150888001444d949440c204c0195815025 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 472136052 1250 472134802 472134811
    0x114040204080a020603060d1403030f090607021c0201090503040b0c010b09040812100b161e0507050d11060a020c030105071706040b150c0a20010f030e0307140105040b 74
    0x50541c1000d140444850ba2820301060081c8a51000b20010b0044d899000c3c0701680c0c0c903041031074012038400c065002030b203c0d8815209070743d0300040140000d003441c0000828500400c4142d004203a041d030203907081c4c6500c1da1000c6040085548894064021400c01c10251001d851010f40503541c54910480042c2101c0c4d4001c0b080340a540714030204000708105c50103840c103007282d104103180e1942d02d0361200e0303044030990b4010040e000d90124000b0818401200c90445c00da1107800c51014404400d44c502d1480c2c814641e008200341c1c00b01c0410f0110341007410081d412203106259401085100100107589500303c00e40c2403005030f10203929849145001d0203800e42004003810f010006d441c0c005c4400103107101c0101428002c42e00c61004078000c1e12140d85021f10f20710030f200d00710740706d0700340c100b8140c1c5807401050b051765001e1004a00f40010b100c403030119000220140c4500d411a0080c4500340d02070a0549044001c40c0401d210b00d90100d0070120100421190440000070a850070380342c540d44000c400741 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 472137302 1250 472136052 472136059
    0x1704030b06090106082505090d0503071b12021c0210081b031302040924061d060607021311030a02071202070b04050402090a090213030209150102070e0618040b0114 72
    0x3024001d0000380c0103c80b9414041c8890141c00304080c0e0310061f0b910b03214116103950800400080d2909220011020b807207802c2c4140c0d405c002c889034000300d0050079821402001810152111500018644405609160004e0381ca801c00f4210241e0001541008107080a00102c0e96a00820059413090700654100e9584180028198103000a03900c00c000a014802406680e89402150038031014a24485800450300080e108480080042001406281c8100007603583c801e10100c020041c0d0250b110b10694000d0320040c1002810380030000e2100030080b01200d0f941e9100112441c1d000800001c52080340701038400f503503890b21450220700c4c03242554442e50864001e6141840010301c0001100c0131114221400358580d0f030440c2c00680001300950022000314800124404805a5803d40e0b4007100c1c003c03a081c860942c4e0b8141684440c04401c03480c03900503042128240000f6503591032250b003101001d000700005d00003a8804420340700080e6815140494200010001c80a441d00d07000800130b420f6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 472138552 1250 472137302 472137317
    0x60402100302070c1401050d0509010213060318030804080403050a1b060c0203060f180a05100506090c030a020a0912210c0206030a02180a18050a05130f1704030b06090106 75
    0x380c032518842e203424003921105d000e0040b0101420313807282040e0360500f801c04200700010700b0b00c0c04249001b980021b00c0502404000c01e400218a800f0307124000d49001c110068014905256038110b5050b0001882103c15101c140404404207004100d04820f9a10407850700419002c2020848042c081c1640b110007001610070030800140c40100c5d0050300000b01c260000c040391030f4a03007200062582281c11210b148a80c1018909001d8000740120007a2210703001006143c98107002e2191000041b40c14101d03116040011030101010317070380205014816450081d0760191202a005110100060180c980841500c00302c5101400043d4200006049007031150001c80300343d000c202603002c01844407402d41d40c00300d09050f4203d00003802455a56000300055800d54656031041854080c000d01004018948000110120458400d40303001e249805150010403a00360b9803180d104010300c200300c8107200140102108004400d01400c040c40c4542d4090000d0310b0f2070000d00401c00c40c160310440c00c11020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 472139802 1250 472138552 472138567
    0x10142a0c0706092301080c04091104051f1b0c050402030c03180c011b0507080d050310090506010c061e1107050f010b01080609042f010e031c120608010e060402100302 73
    0xe513801400244401e00f0040030a54802080b8040c9000d564000b800c09030805c82c0703041800e030301d04008005441c01100c9440440e9140502001c041c80402c10410100300e081090f01008220385074516200c5108020a03128551244080b40c00e83c0c10070b45000c08060707030100c240001c0486001d440040b540403000280184440c80000030f080ca0311090701000501da2074440c00c018000c09102c0540036004007401c51319201c80c045002411948210380700e000d130400c00b01000c5190400c80c000caa0041d41d05030340f0f07101a00100e444200081400c0d203010f000302d00d03041c003850100101c030340504000484465a441d4030340c4101c0c04e1181c1010102d14081700c9513450a03000a800340e030807100d519009101a030b0050855600ea1822182c0304022002000520031014070b040040440c480c05e0041049080e61240e000001160a141e65096843e6800c1408602d10016400540c481c00b401c4001101c048008110903942d4903285086602c0d101d8611b5150300500208000e604007000a1581c0c405646021490305a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 472141052 1250 472139802 472139849
    0xd060905030f1c052a13060c03080709030309060f030216030207080705030a020a27020705030316020303090a1b03060f0605100c0b01030305030a02191110142a0c070609 74
    0x121143d1400d4005103200c0001c1d01405d5110a0f200c1040d085101118590349824004c0e060481d520f40490010700600001000d60307208507280c8003103d0349501c0703182a007402d0000c240d81032600c009698080540c02d00c60301183c038605098184815009030090240e00c0e00b816405401d221080e000f2a001e039104610300e00c01604c03005060380442e0600341002a80344007020160f40040b0510340fa0b0b03c0d526002040030000e02002000640c00382000c8050320380d41555010060783c89010132207003031120f0b40003461b004010a03415902800c2103102600c401020940343d54802d81103901c6c61085100d07080d520703031050001c0d0a03c400c03101e0507422181014180b01c911550340c4c2000380c10500000382084004408940f21003840d80541d100c40701c0001c9000e055001c5844003c05e101402c02d54215244a502810f00c0360013000d02ca42000c800040344043d038103036280704140083d0191802c803820042800500c2e0426502e200307000e07205003144c05014008262400c0740c004c201001d07a03040949021840d580841b401c80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 472142302 1250 472141052 472141081
    0x703060b0904021e03011815030f030f02120c070e01080a081603020c061902010b0f0a05010809030c0f071502070b0d051b1602090a0c0e0d060905030f1c05 68
    0x181c226000350303480050401c02c4d070020a03c0303210401015400700010070988540700b011000710169103000c00907201110400d8141d24168400600350000301190a0f02284c410120110200c0803401118440c00400c5850400c1d544004a40c070340d2900200000e12840043c1c411060040901e84000c0140f109140c684006910416651000d0628003c1e5018101802440140c4100d50004c00d0140c1b40d00201068500b034560b80403c2c00010b5203880020051460421043d115500e4060504e400181c1003000645120b08041d104080a100034448410640010884000c10540160150101500d4402d201c600004a5920350007503421034903060103240c041800f51910310102c6000408c00d611707000d120284c0714445100c0d18103c82d000080e0441c0d4081c0340c00641e420310f482910a40020380d80c1b030f4a81002c98412801030000180304404006903480c181b4070040c690f50150305c000950080340e549861070340d801190b060540e082d000ca2148a0100d0b0385400c020318482900040c03015207400c090f0581d062 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 472143552 1250 472142302 472142317
    0x5120a0903020616090e010f06020c0904030504050d020102030903030309010e060c070203030f0d0912020f0706031a09070215010e06090603240c040909060b12031305011407050a0c0602060703060b 86
    0x58100d01c1515501300c0c4554404001006020100c150558480c40179188200c01c60003590094841d4820707410150602e180890711454143c3e43c1c490810f81400c0400003070028000d4164118441840400d12960f4240015405504030000000b40304072a10b50441c10844000d0034022100010704c05440581c5001c812510701e440c5054a0643d50a8038145450040510300300c0034101d40c4604c0807103803405400103a0034590800f11002c60783c186a0304c880032015107000c8904045105861b01c143d40050034005a0706421040900507200c0b200260f000e003610103034003680004243c074030710b8092003200d0400180c0940c200109a025140348455603520044203080d080f40a0403000d003050000d00250001000c2d40c024043e05e06042c0300050742c0b400c14001506600c0c00c01c078401d03002c0c5011010b50350000400c440c585a4008000f1a03a00d14003030065482000440c4d120070bc0000030812400094014001c000041c0c0c03145818081d40e500740302c1c00a25040b07008141c030040c1460808184514032118064a40d00c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 472144802 1250 472143552 472143571
    0x20303070815040603080d0e16060203040b07020f12060717070206040b07141c06120b13020a0308070b07020c010216050904020a1505030118020702100309021f05120a09030206 77
    0x155100b0b01040051140e60b0000c0c2a45d40d0220f0692940401c0d60003004807000244122040e8010410002062449600c24000503902c10081040781c003240c50301404010b40000c0c04120050b072250007240d6180340d00c00802e80550800400c12144a0304401d03100420884070008508505d031605020307607103550250010b44504030300000107030082d00c900f0400b01c6403850070822649079001c58459900800701c40c1070a08441e8203148020a50743e00d24544080300c00c0d0460010b140948402c0700704200e40b410031a0580e00000c00c14000300208065400500100c1c0c400d1039602118501494024103041c56a01d440303045400c204040402c01411180301416a4412100744178a6202c51000400c4082542e00080d40d912030465a2554540c000f406503040b50b40000c44030320701d4105007402508a20a400700254040c2519888850007482980010f900b0307440a00003101e8080b62401044c142c108259841c1f0005000062512074211401c5c0c0c010b0b0085800802440a0341003a500a0b454890040c0210030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 472146052 1250 472144802 472144831
    0x1502030702220b12100b09060918030c15071706030c04020d09060e010c0f09032d0b040803011d01081b010c0609080436020a02150f090606010203030708 67
    0x18060016840f40304941001000c2d20382c00000f83c0d00e2682c5980c003204902a04030b290259100c03d60408144140c403e2034000c054800e10381c0d450f811940e030607442c0300940702644018010b0b02d209100c100500481c40c01e90f42224480c510340746200820902e86400c40c010900c5010f802d010f02c43d20300180700e00c7c5a40003120007584525204030394600a144440000d0b100b241004040c20b00c401065002d100c200040c0c1e80c0b50134042d5845e400964110000c4d1000070309020384561720f0400451000656100056841001d100c458a59102c46164540540341510308a60010042021850070b82c006420030a8102004120750f250808480c0c5844810020500555171141003141a0f8407440900d4009907005a040040f00c00a061031000c1e60058041c240c0040b1030407040c4080c4002524105c07202401060405581c02c5403030b040c00d4043c1d0005500ca10030b41c458a0290b4006103802c5e0f00710381c031841d070071410f0b5500c62810381c03a45480c01d6400791007141550000c0041c012161323444144990321080d046007084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 472147302 1250 472146052 472146109
    0xc061b140c010b0910050f100c03200d0216090608030913020f1209060a0603120c02130c27030c12050c090c0307020f0106052d04020a091502030702 65
    0x5000d0a89010304940c0241144c0402c0154003400300a542964425a03403070303100c0c5085100744800f90250741c4050000c281020700080002c0d01c95000e14100c40d203091100c00d04d500c1e200103061321b002403401d44100941c11852541000c90942ca0745413005008040e0140203c1d803174001d0041c1c4903c1500c901d00c2c00340410300260043c010094044901040c00c07001c000d0781d00c20305002c080d08003410588090700340c0c0c081c070b00100d01e0300b150318083c40c41940c1c0c104010136038046428070207845080c4101c50481e0820a01c0405080c1082e042c45080009412a100c41c080e40a0014440200748281d2140c0d940480748980240007094003060100c003558117200d201045c0301c202d0304001c0d10703082405034a9039216100310200070180e03000201030744c0500a69000c032481c2c9800f55100d503003a2482d80c004c0c9a00321400c010510441c4844005460190240e03e07001220050082c0c04601a07910081c030b41c0012a580c03d1041144e030408010304020841070f84041c41c244965580051201c46c0c8582d0821408681d024440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 472148552 1250 472147302 472147327
    0x3090d060f060f030f05100506060d0f1b0e3a1b0b0a030b180c0702130903020d090e060a06030b03030913050a0f05011203051b07060c061b14 62
    0x1c1015080d61941100d6480e0b907442d00c03246030400c0711700881d05030094954840b100805409114046c0c00014032507414004150450002010300c0301604003055210a000380d0f44555004c0b01c440640080da0f81d04090001140902c681004d10581c400480850075000f0004004c014508a264038408108040c9003880707418204005000862441c0021054040010702500a0001411540c0c0e254505200e903c60000030006003996070540c20203096070010009081035014401050301c0d500c000c15441c80a0540b000d540c0c12541840d00407005039100c880880026a000a0500f00402501c06240c41c607151400c0030804080e41c6100301070030701da100d22160380141d030700b03109840c0c0c1c010700500820101c1d05d0100580e006040203aa03482ca00a00c0d010103c80800c3c801c2c041c032410b890150030740c980d078141203075030494143e848044245404400848203690558042c804140200a1562040e0b6100451301f418030458000c243c25425071601c184d840e03c000ea030001c190940101c000001e15446080c0e11081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 472149802 1250 472148552 472148561
    0x307081e0c0f03090a05180106030c03090b150916021207020d240b06040e01141f03050f060904030c0201030e0309060a02100507030902210102120a020a080903090d060f 74
    0x354400d00039142192000b5070000080c000c0014120740c0328007840d80c3d80062042548140070b01582d20f003011401808020300a8002c51410401c9250010f07880501d030329240d9a44000b6038003400e0300e0807001c104281500d09889025000041d0408950b0480700106020355120310344510841010004120b400070740d0f590010100800741c1005940c0b0035140703000ea4074002e043c4004c0c0080200c911340395031b00c400c41c2054001c0d40c094915052112040380d003058400c404000002082e07662210750700310351010350801c9031351441d865889520042080d007030060b000184803800a0049004621400403c001b00352710060b4599116020b00300021000e900d100c509042d0b1196142c1250400c2000441c0152154005008442003142d902c0c02c2245488800c000c90541b2410321010f540310010a80407420440e6070405002d44c00030700c100040ca08504c2403100c64004400f01c690510056002c145188455003180750250300600c60809903282507040c000045014011903c05003800303275610be1164501031280e01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 472151052 1250 472149802 472149817
    0x3906230432011e110a1112070503250c050603060109030606080d0228021903050601030b16091a071b170d03050402031b03211b0307081e 60
    0x81e1a081d1020030448a02824102c01c10a1610040542070b003041d0310244110fa5910a4030310000789000c403820340c11584034100000e10541c90290700318041d8140c192034003c04c400b903c0784001d1030305c03034055001d031040c0d070008001807020b250f0b400f0714400b00142103008100c0030b840c400c6a030180c50f501d44e14012101400150402000b1500d02440413a80c0d50380001e00000b00c602c503900b100e040581a0079055420201c202d400c10380c01491044440040c5051603011044083c10040510b055543c0d8071014a49902039000303803802074070041401040d820090909003000c0d481d040804900d843d1640703d2100307480131034803640c0c40030003c16443c1c2000141c103001020740c0c0310881c3c900c5410b83c440e54400921180460f485019202c2da025180c0003601a00075030748030b250010302802098481112a50310801000b250f2945401080c8070440c555130303c81000700030049442c9001d900e40240d211021001248901409120b6005004600c009020352040b606ca8190301000c11101c98600d20503070105011702003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 472152302 1250 472151052 472151123
    0x708040f02100e130b100807050708040e070905040515040e1f0b09010e01140d030306091d0106060507020901031122020901090b0403030503040339062304 68
    0x300d0341607605a02603a483c5102004440000304015140d078040c0841da060400640c1181a90301e140c0780c2180a012003a0741f005c81402c1c82490400c980d07403004501d6110750010208100b40f001070110b4203620070045000760405030740400403030800840c00080c0b85813101c009489103843d008042805203080c860b80850758843e81d8200034010360100c816003e864040840c501401e8000000640d0081303078001141214218000424400d9902080c08000080b008040d4245030b10b03078000085a1070b44d48140e180c1800b0202d03c24802896951600c0d00f5107070300342e020804220b401e10180001d640d0300540c850440b9840b40d62840f43d105200c0200c2e080791a0f55805088168420f400d03a060b240d0250000d00f4208000daa17000941500d1f2003070060300d0301036800041d001440a00002d40040c0c010328000d8030f008c02030045008028074052965200c1003180c6002400d016004030b9400800206005014045603000d00200340d8203200c288146110900a00260480b2501c9169203510810581148181c05104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 472153552 1250 472152302 472152319
    0x3030b040c020102090909070608040f03030b1203070302150106021905012301030507050102030307050d0b0a0b030907141507080a050906040b1b0c03062a07050607120b03060708040f02 81
    0xc20002e8000d40180300018003a0104000207050a0b2000c1298415550142c64240707040c1c59503141d030740b2048080c1c141101403550ba0003101c000c0c1c2d511900d4030814030194400855480c14149070003410400500314242007205960014010940c01252030f241e00312031003600d004800d81c20304085000d454110440c1c503111020820030202440444c0031503050342e01440c00c548038580e070380004a07520304c000c075242d9000503424070092041510f2504200880d22008003036150041d00c80f03010141c1e5a1042e60312116661000307104100c103030030394152001c46030421a0b1040304026050740b6040144500309004100c100000b80a00ea0b10b800303441940c00203d8007500702034541307444000c0600c45500210701c0c070001c024581a59144414002003000232903101401400c802d0300d90607096558a11605003500e403410460131288140c80748800a0300386039000d1002401e8909200c480500a8240062041703400e40c2420060040d5490000741c890b0490200e02d481102d507a03407030611102180c40454001e41c000300c40d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 472154802 1250 472153552 472153571
    0x60303200304030812160518060313140f16050f0613090204080a150c1d0a08010e01090b010512060114040e030d0504020a141507030e09090609070b04030b1303030b04 73
    0x88001d014400c60705500014014068031b64155003d000300d00d20760304030780041008140241800009941c1080c0120381600e601c010b96980c003550300751418814000360b0721903440250440000c00403c0302002c941401d42e80315078142070225030541541408207000b4000000c0d116550b500c1c00b0500e200400c8500c90441d1580e440d002c21680756441a403060784c00200c00e40007907224404034810b02c0f60301c1516403500040a0248a1041224001c039195950b001542800004070f40c5c00030301400002e11100400050503941900c4c22111419040e08124014482094540c03490700c00050b00c075054807001c0c8419507600280c0c20029002d2f10704160b134800c40d07000126002408070342079001301d40198800c03100b003070390a80c2300d940114142d4800e080c03003640032100c182c00c200d282c180350f4020708000d4000d1510340410348605002c65060340047d0340d0010190721507010024800414401d02d0060300100f140390346070a1443c1c0307903081c40090242000c000807501461660400d8025880003128000c084e1040c00107004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 472156052 1250 472154802 472154827
    0x50c1c0b040b0906011403060a0b01050c0109030509040e01020c0d030510050604031b1e0608090304031a011d1005010f0908010c0905011e0206070c060e030304060b03010f0603032003040308 83
    0xd83d00c291061250704000719042c210791080581070803014004204541c0c81c00ca400c006440c40c0c14016060040400c50f50303038095800e000760f0301d04070b0007a1120b96803040840c0030300007150101c0703031104550392040c0070641080c00c012661345502c40c0d0300c0c940840c80f44c490f00451914120654002ca51040c4000390000c200401c004003090840081c5200341300540d610302d04051000600f0941240240c940d00d0140301c0f072401352040b150010307440400c4a04203174580d030782d400350701d45620340080c003009100703004225641012004400002080c0c3d21000346041800f0b0384448003025014440c140440c0600050b200b61264122070000c2c40e07078600a00054000c500040e01c200700600507030b4001070301c0003100c400d000000c010300e90424545034020004c40d0303150002160300d2003000904a81581d180c400141c00303500e0070405035000b00e00138100028015002c40c109030840b0400010302e009541410020004690000007013100f0309401807840800c1c0544810050841c03049402c000c01e10741e0017003000040d100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 472157302 1250 472156052 472156073
    0x9040c030b04050f0903031602120c0a05100612080306011e08090c01020a2d0512040e06010c020d02010806010302160b16050f0a030933060f03050c1c0b04 68
    0x1005442c108015120072865002a00003203910b440c45034800c00200307881c0c000d5a00a02480003c901c1a07036030000d8118680990341d1b0204101e00c0d80350f8400a007041c02d002083c04481c0d0b80c84081c2e030081002604d03020143c000200d00f1000030382000350100c0010b407540d010700444c1308196094030711440424150100940300000503035a55403144901d0b12481c0b803035400018000704d01a0049041c180c0076030f8040c01c0420340c0d00c22a01030258414207401e0030b0000381003084a4010420419140c648544c10b2913412810a04018032040c100414240c1210150f2100300800c200c0036020718282100303030740b17000050340617110381c48400c195041e00c2000742090181e16030815004141003000c4181401c040c04046840f0b01440000d00044032007005541642ca000341d00c1510707003030301c035406c02c200c40404903c940880003c60700c00c6142041c0d45507064801d401480c41400054400584100803450468845980d14010b00782068000c844103a0141180c0345d00350480c1944a5000034040720601e0180340107401c48 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 472158552 1250 472157302 472157321
    0x9030c0507090b01140307020a140a0b060a03080901110304170106030605070513091a0405010306150503030c0c1504031428020d080d14092406060307110309040c03 72
    0x203000300032010940c02807500907082120f8050359155100264404000195030014041da002d510420782d00b4000a14407a24005000b112000500098403850800c1041204010811441443c01140a00c0050241015240840c4080ca880b040000c100345029255228a420560550780701685619560605422100aa91090001380b2094680c0d80c0c0030344480c001c00444140040342000c1c1485201001d038002c40640828101e9581181510f001140456a00ba081980c68946800004180d02c0d9403107841001404260700640c075200d41d0703c0c48140c80f05d004104046c800e040034049103003008440c405035000b55030401c901034104801003244654911214415500134100035000305a0500904280500903170040e06c0150b00220556421790140d114010643c1002c0c0d07509200101d028845490074410074804c00184045801c1c8031400740c800c0d0418901c0024074480030108042a21400705413601300100d400c00f24447d007003049155066000d01150260024030b0001c030090006d61641111112 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 472159802 1250 472158552 472158563
    0xf020d06050414041502041806030308090c090a0c0c0501020d020901082a070501180303050709081b0f15030408031806060a0e0915010b0301060201060f061d0402070609030c 76
    0x800d6540c205000907035200ba51101c0c08840440c0015000c07410240340d81001c0c91100c28014a0f10b62161170001c04009035189283d021a0385032800d208060f04410f81c20340000b1202c00810440301c3c0710000881000000f08094074294880c8403c2d42c0150240c420f85401c1944400255250701c0c0018261000b034006850850001b603051007c1401260050041c6440d12000c1c0d5076001064210885013609901410007101e01d50740c0d486817007a00d200d1210f4480d0b0010f209075070201c1c1506111138014000c509640007590f064000110480341d42100c008025094901a1821600d201c4c1c80000610328907504100c00a11039800004c000412261400443c4980380d99a200401d10b1000310b10301e5a1103504441060f040b0907668000d0000d0f166180344c441d07100303e80008032508203000100c0403407011020f80c8112510078010005002d031b60f8081c010140601119007544918034540700000344802c4030030303ea9412050014003a8921515190119082103400520a104a200c0f600e00241916400c11081c1d0341c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 472161052 1250 472159802 472159811
    0x50a080303040605130309050123030a140c0a08061c0515100f08100f0204050301060b030411060909010b070606150804060b06190e040e0a0807030306050d02150705010b03010f020d 79
    0x41190345804c507900f001b90140d9800368014103000042d10507071803882250002c221401c00600210300850029031298000000c0400d402e02c042103100f404a5000e8520007007200d00380080007d032079120020541c010380460344514640e084000c0102c0401e003184001d46076011351070030b51154501c491049801425030003001b402c0b0640d1640c411495403102e0151141d030740c2220101108501c0990802410f85030420001842c095607680000d085500c2c0d98444071440c1404010802801803241c401d07143d0107004d0329400e01c1c00362400006075401e40140038a200c0c00d40c0104038101485a2a03110102400c030040c190554805a80b0000d043c001c070469040305c040b410981ea010403420003000791012070300f80c0204043c05860195041c0c0d42c0100d40304886800690f01c1010410401d003c00803950403a016156117a03460445040003000d03a00190441400380c27021107851001130300d941e09191403500264289548a000c0e9207002409002c0c031014990741903081000c006e01c080d04650061041c120650030400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 472162302 1250 472161052 472161061
    0xd05030711150a02090f0406060e01080a15060c11060d061814010b0f0c1209011704020d0807060902190801150b07020105090117040b1006020a0506150406050a080303040605 76
    0x25503400680b000660042c2030300010411000450700517140750b0748001c1c0884e1761003c600f00800e08a0744294040d0000400020b032003892940c002e01d0320740d04518005010700840c0e80d5100c0e41c014004080c85142e0402040c50100d030705000c0c4180d8001d00300314005140a0751045880306000140079207009518107110403c201d503051800511031092800a140104080790380390000302480c541122040c1100000e040000341b00c040b409002c018412000681c0b201c0d12404800001010021294000300c25503180105100c056615144e070082025403007981182da40c840c510b040c00182080a6000707421505691a808070f05035156101e8080d248014020007402116603160101880315125a00c4602c104000f02000345d4890002805840c406040040e580380c0741c0e01d411140031104603000c1d1002000402440148040c0800540c020850341c4018008150551034050311000d01400380030a0106100030020680c4950b0840740060100404001034107507220305040d00d940c41260122409032400c4000b0703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 472163552 1250 472162302 472162337
    0x31712010803280207030501150f05030f0a061e050702390906220603021003050613051803070b27120f12150a0905190218030d050307 59
    0x2548180c0190494610f2441d24007100000a5095590303003045014428010001c6682400340746080c00c17420030310911041c82c1401c5105a20305980000e4801d4010000003040280c00041c0b00700250381000000030313102180d403d040542050380c0040140d65080030308015035640c0118010410083c41c0500300c49a1140078281500402000740402440d40d5203070b0700207024103040003040e512000213400c0181013a041c0c00380c030b0301050148440003442511a0802c1c41107003400680f21900404906050049041400010750b142c01300420305040c041d07441300010b0200c03040346000d982d50359603041603e99900950030501a6580106c64250042140e102d2245e82c866100500c209020341c0000540341031560100ca40761142d00602d01d1001403203040c40216071141c0303550151401518416500c019203101107060006c04600c550080d401246024104560003000384428100c07405501070040e07550400d401250010390340b046049800d07100b414021052980c01c14021401180280c40b244400c01e50319015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 472164802 1250 472163552 472163557
    0x611010f0c1d0a0807090f020909040f110a1a0306010207051909060e01060206040b0a061a070501050f0f0c0a0306030f0f0c090501420519110a120207031712010803 72
    0x11366941c1d9204500c02c100d240200e0b4001e4601001100c80989061005c1d40019001102170f5000d59002050a07003210402c06040802c60212070152910002c21346006500015070b02d141c0d4034030056007000000951603a00c2070120401130140100030313480c544482c1c408a43e03120700b580901e004491030080e000c40d81c2001103440504843d46036000300348903601c0c2c1c2d48880405102a000c4442540c9500c0d011441d0102101d60056850b80c8460140d21074070076080c01801c0d144081c00b4501c100007038034140286211143e40140c0e04c03c10200116584c0d600290b82200101010343c0302030300c00000f400c0c07031600300550710002c00180ea0040240900c11911110408200c036828810010398003c1322032074552107000000d865220f407220300c3c5102440507006581304050850040100000f0788000b500d1350844d090420001803030a880d207068500102c500208a43e11360300010003600904403c041c8640840c82040b188028503400707109c180c0fa141e419000d0f030728507400070003105c1400c400d60710012075110340020a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 472166052 1250 472164802 472164809
    0xc07060c020d0f03050d0606020102030f0f040c050907210c14030114040504141b13062d050d050106090b10210605060c1e070506040611010f0c1d0a 65
    0x664056090383da50700e0740d44443c031030088082c000140b00d144200380c0d0b82c1c400c860081c40a41c0003da680d1904112070b0b0081c180003024080c10005500034040032546d40c408400a0756070a440b44002d5803160030b015120501c3c207980c00e08003480f00e2044080d0401450300701815610054849018800f1003000c0306c070f442e00090140d6008583d00120a10b1303646000e800139030300180200c0f982d445281c0050a0329091592100a4071030045000200311014200303403840c14000a030350001041450300f0200710504000d246011401d0200caa80d001c0050801840301520090400401946c500e00d494076129002c0c08440c41081401c603c1c01c1c0a54101d41005000b41c000c40605503103407490107004c2130700c509401d508001400003080d6190300110382c940b200d000500d03940000e20014603808201c45502e441d00e208880100b036554000308000c201e00d0301d800050b1420f950541c146192065420a06180180f0400d22088101418007030326154050b00038824000c0c111468410f025000208001e1140c010028030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 472167302 1250 472166052 472166059
    0x7240c02030a0f090f030f15020c0a11040b0a0e07080702120306010c050a021504031b08060f090c03071d07020c13020a0302040302061305030d0e0d24050703020c07060c02 75
    0x324019503140f082e43c3c5084401c07454201200d1440c0c5401c1c45040360f1190350002c6031041414900c3d44103001103894040c0035140880f03815071a200362129800e071629506a8010000d01c40903c002200c0d41c5d8a40000d00e010a01a00c0311000c0b903034815003405041e00a40f083c601141005011540c3c4a10104031214000c1d1416100c0f032450b2551001129201b038540c1050b1028012a50b04000503622a5800c07030407030100b00e04260326076044d424407582e8402d080b0f420002c00340d01c54030100950309010401c80e9025a840c0061032165994040303460030301e024240f0095040c0201100464500c24000c40310110440441d02c0f01169911040140d80d01c00614034069400318035428004000425074000b4071010500349000350801d590b030344c04144035400044440900784042071302440306040406c070924140d1040c0c5082106803840101041445808407400341035540e032160f140004070b16199000b4918800d01104000b2850071810080081d003200c0050380050242090020b041446400c0280240341c005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 472168552 1250 472167302 472167307
    0x3060312020d0804240615180513050402180a05220c05060a1404151e39120212040e1f08151906080d0f02030f07240c0203 54
    0x1901e0754042502c0c002030748170840c80390400030b403680000d5004800041c007802c3c083c0c5403440c12040d0080c0001401241880501e1525a030402040c1e40d481c605401954200a0005480e1a503001145e00e01c1c5003940c40c501803007000011311450348119481507126103901c07841120128081480e9031508003250002501490350070a060206242060040080030f06c1402c110864020880d00148260403692241d075110082900800718540c000e4a00484540100000c030741e071260100000d02201200b0f04a900700d0240800e00c2d040960b4009500c40c050f404050a000f90303101c2c140b0380150325480c0c95030100e0040c0941b00c01840c020042d0820b46064230b16900070707482c2c42c0d620074083c000c41c200c905c5e0389a084480a0007001a801c041484038000c810903280c0036903490b01d0240440106106a25240c01c0c2407440d00400308110103000c140c04030005550300d030a0300a00703c801c100301e195002c2c4000130204c50400040600c01c00403030340c1c0008501001074440303040710780042c083d01084904203020200076030000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 472169802 1250 472168552 472168561
    0x7020615060f0d0f060f0f080601090b0a12050304090f0209100206130b060411030103050f0106080610060e0109171f1104051c0f0b070305060d0309060c0807021003060312020d08 78
    0x1c68020309403000d44ca01c40080c449a844d0144a00030556600030742d0b043c0160242801050307410312110b4050130101300c0034840507488030b000c00c40d40c0ca810320601000046a49503002005801d00032140202580343c8180911a45622228000d5000d840c5041c441d07941840c6214844d0300200f042403244104182600710303a0350340c0d00c2c1e000b125080105911352095458000c2c00c6010f0750940954041c41c094002010401403030f42c1c0301400c442c12341e00503100980c820070401408801c0c074600001a5140c6286c00c024042034500180c80300b800300e810542400301c10ba01c0c0b07a22040d100040140d40441c2e11600300250001c000030341002c41c0c02d40a03900807445010882400241002648201c1c0803036010f10024401005840b03100048060302d40807035502012a040c000740c2613050142c190014021150661041e080d0395000e0701c12403040c458002032000e4202030f00c040c032446105a410190b00a03109492101030071000a0084c200d0f404201c0d03080809411240640d80300040311002602a621005481c0d108d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 472171052 1250 472169802 472169827
    0x20c060a0f18050718020405060708130e040f06021b10020d0b04111e07050f150105030c0a14060706020c01020705070b0f0f1810020703020108060613090b0607080307020615060f 78
    0x4100c3d0300f04202c0d1b17800300000119522008000d00c20380c0d009501041c0c54100c1d48816080b00e0050b680201d014550034000d2101290060100603500d5a0102c00140d44020100c1007403142081455513103024010858001c3c03048070f850b0020008840403610800800c4006402c002c1150a00401e0030b015500501c048104140d044442480500c0101126030801116070307030341ca203041000a01d290b4180c0215881c5841841900be003240907141c00c4024040c0c40b4000310202e81c010516200c1c200c0b004107100d500a105848080c200d410780d41d0000425540d0318200052a80070358030100003241e0780e1040200002c1d2412095050b0313070311032600020061410b803403c01c0310a4603070410070103074006440b1844c1500030b540e20803014402240c440d402070540e2514500000d0302424004004500031030003080181a403032800c0c00028107441c0c04a40000319410b0000100381280108940140b03a65000414846410340000f90b040c8101a128090851041003105122290080c0d03480309400c0c1c0400d1001004100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 472172302 1250 472171052 472171079
    0x121e02090a0e0c041a1804050718030507030c0806190207060b180f0a021306081302060a050c0d091a1803010606110609030307020703080a03020c060a0f180507 70
    0xc000304030719600e45001c608081000e40359031040d0540003a0800810b40c0520050056171980d1240710b003001c0210700e00c2c4d0003000d110100c603885541c0e03a100040b0010301030a01d4244000c40c04c030440e050182c0380d02c2c0c001e80e03c4181d1300003a0707030f184459000013890f103070300003002846020703603104010780c2d9846040014040d40006104449a0b512280ba000454803070041104504000381190709690034122518100d0050180c01440d49600401400220303912243c000c004443c030340d103007508455071101c1200100480f00705000703501003070000c0d0107072100b90300402421800356402c05489003615a0502030b91103040c00d225100b00007804041011000070460040c0c003080445510100110480000003821a641034100310302151460240c010444020480e1680c8018200000c0d031960424450203940c940c0d0510008090300c00c000b42d4024410b20a03019a01440d404c1c5089038250704145410001419174002c4881940d8600442140180c0402e40042e00e0380d50454042c3c407059061800001924 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 472173552 1250 472172302 472172317
    0x903121119020f03030a0903030c14180607020d06090b07020a120f05090d050f0d0e1f1101020d0b011214010b0306030c030a051e03130501050318010905060403121e02 73
    0x10300407a400440700c1e0703d060000710312030b0014010014500a040c0740c06412148124600d80030071254502c488085e40102007185c0e02100d030a400050f00d84000000142c0902c0f540038025048000000344000b0080103070060341c5c6641c07141140c0c40c0f19581d5640100c0e901c5200c41001703030013008008a410013242c0214841001551903140c010715144000000c00e50300c14655a04503025800000d0b403885030a07060200d03024142c1030303240c00e1400031480070000344200030350001c00c03a54564002800450310b0080c14400306181c030010095459009840c8074400400c0307922001e0b40410f041c3c18541800c55503a21820070310190300000e454140e401e229543e070160700b0040c01c06426110b106004000e42d034042103d441441e10880040003071800311191450071003200d25100b58168001c0c048941c280c2080c1c0c0551083d85c07004c0c44e003a5100d42c1c03815401c1c070807808030194410165181c4500a4140800410401d20840c040e4031854000c854070020b03079080390a00703940c2c41940303114a2902c80e581402a0000e0404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 472174802 1250 472173552 472173557
    0x6180803061c0203160612110906030903070209010e04050705010f05030a0b01050408102702150d021306021e1b130908030c0409240509090a150903121119 68
    0x141e00307240c0d000c2458a0041c1300c941710f48280e05002000401d030300a401c0b40b0ba5070a11102840604903182000300180112084e441c401c580c0840010030f902000c10903185680d0300280b500c8800c0d45d5a560210450006a03001d40343d07405240c802060325401008103038000106a5125480d56455850041c010f1008804040c104030f400c01002800035402c110800f03001440031030008144203580c0c41c0403007089078800c0b4040220001034940c009607451200f00700301c0c0240108002d80d240101a214402481440c042140d85440e0040c045079540c1c0c0012010318181d1084540000b05104502e604c1d62891283d0950702080500500c410f030504141041d541e030100c44041c0800c20a4150b0344a0b200780e00112021060b24501040130000407011b40114018210f0703400003011030000c0010140d400320350a0007100e00690300180803600c50441004404031150f0005018800400b000c11a03c01400f4200815400201c20010f00700c4000c141d407040c503a407600c10f40c0c4140d11b4040e404a882074000f01c020880170a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 472176052 1250 472174802 472174849
    0x70b04110a080105151c03050714010b041103070f0306030b060f1504060c1a01030302060c09030a06050f0a0f060803090f0112050403020601150e010207051e04060b070618080306 78
    0x5000c0c07424007a4a00442412002c5c250000c04541845504c0070340003407003102d048508180c1030100790001e0440b0250754001d21070072408034400c00182c3c050b00040e500503401902d014100501e950421000c0c5001d50f02642e41c6030030201162804400b13441940c0030183c81504038001003440b9151200700040070040241109414541c0000e502c10142c01c40e40c85600480c050303c1c00d0504010b1011608400d9080c1c5942c21600c55045450003955142c00609020035410002402400e41c0c2c2c1c1041104180b540c403c3d001d01c000d1600a00d03602d0380c040d044d114250124140203064110707038981d0240e03000b5581084011414115001c00704207a003030b1541012414001280340b01c0c201d0010038020b5611440c000c2d0006d10055140c0300464400b0071030703c42001c3c20002000452000c030381e40400c40108442d8215210140c412010106060300c002000000c2d510901c0c00c00d000070307c030841c0350190140070702a080c20040500c40007007807100034000600c01040107200b0030000b41a45090b407448051007000b03004120 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 472177302 1250 472176052 472176059
    0x501090609232a1305090702060708042f100e06071502070506070905010f110a020d030306080f010e0c0d0201020d05030a090605071808190221030f12010506070b04110a 74
    0x142e00450043d203040c071050001580c814252200452080209010303540b00c20035150225000791126000790072002046403801c041003e0043d042c6005176840f42416008030380300100807804400301c0840130014011503100e480c0f444094080c01840c3c90b55400505400c1c42e200d0280e642c41d4210000c407468001e141da0a118020100e40200300052042e01d0a0311084291420180094401c0043c040301c04d040140302c0d0b4440022040214800b840107505942004c1005c40c0c0b498240e01030b000e030b07403c0380030340b0f1090302420140c060b0150003000124806406441b80c110143c8140024104a250041d0140e406140301c451a01d1094005550003101c1020019001b07006541e04016180156008000600c8140c0b00d07540d00512280d5000c01443d80c80001d03c001854483c0030121200d5211010744150380c0b0340c1c80450080182c01e030514070381c40c500c8162540c40007056040340c02500803044961060500c100080350a007404021601c4280d00016104800d58450b900c0000b10182c1303c0c00c840e0040200000003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 472178552 1250 472177302 472177351
    0xf13081e0d0c351003141b190b07170a022107050607081003020d24050103150c0201150b1b0c010203160501090219090b030307150e0f060901050109060923 68
    0x2102c880440c20182070001c5d5035030036803411f0f0800c603140349100e10816910809101c410600c50802c403503107c2060307900c0b001c0c035041c10000504900400e81c5140400141c0003026580824082a00c0d5603105083c089030241ca103c4101d24041c09038020180d50042c0c01084201c0d010304605a4030031740d5145014074480c0c4036070201d1f80c0c0312007607241100c8200600e0312941248480c440c0c1b040a0081e0440100110741c9140c6402050b08809031842d20b18682c1c803451210124400e40110031100400c04280d0011540d400715a00c0e01d0b401040c19140c2c07919516940c0002540109259030304400c164003c50910009070180034070740f00c0900040b5403d43d07071b1310004001620341c440d070030b0b41110641076802c0c0702c0341c80d141d0325505075103003031403801e01c203402c100b00300c07000070780d00c1d0a4030b1000b0151050300207144881e0800355840e140050441c0c03035643c0309420030840c01e000e054008505903078030304809219031a81d6403441b000340c03106015246081009000413108000e1100d07102c1d81d110b10751a814103541c404d0640003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 472179802 1250 472178552 472178573
    0xf0611041802030f07020316030302030606040e1302100c0f29090a0201180308030a0b04150b1314010c020108100b0d0b03060f13081e0d0c351003 64
    0x103a1406402000300101d44c814440300710744c440841d001852400c1c0308440c5124000129000060070315901202052560315079030709690103000306c5c0c043c170551030508003074107043d900800e80203c1c0308a410f699518040f500c40d00365140b0072a40181011070715013059035890000e06000e02e01c50b17400d2100140d000c0300c0a51406a0900540050010780000720141c000145516481e0ba0209503049000c6001c01c0014007941c1101d5200e210554002001906240000d001c1c118a00c1c0f02c0d0b220001d180c02c003081e40603116006042140d02c018031146103560b2076940340c00152a408805002c103043d007001901550150071456404a0529600e281803522903480c00544e0300314081000724180d4622021540d42410000142c0040da045e144001602e02816201056542c5010040c2421001304803410b050015681903006a00e064220580314100001400001c01d04206400000f90881607041e121407110040b1401482c964000894038200e41c2045161140b400342a01d66110306000d0000b010610700b940 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 472181052 1250 472179802 472179839
    0xe06180a12020c210607020f15090102070b0115081f03030810050306010f08120c1c1101110702130507141b030f0316050301050f0d020303430f061104 66
    0xa0100c14501014644c901e40000100000c040d580041086001400e0000d03110032040034000340c00c2d410756155880310740640034a260082140c0003040c00424000b08a940381006c1c4081c0c3e644d802c1b01c5544911a80c01d10100740d200c5c010401c850301c042440805d01c10144035900c140c08400098403140c1c0c030008645011800d030b0000c03402c51f007604401d014540b024840b4041d02c41c0c51400b4142450082c2e82540e0f11110100302e840c40c001201d040b0100901d0280c9040c01000948100030048020070080f603d00350f50002c0c408911945440074900e00e884554400d10f405038841d40d079441180a075905c035240469108000004101d04414181400d16104200502d20300c2e40e0610b20540701d0503c0c44036200108940b003403410900800744018801d0703031203114500042e030700d007110b6803030700c1c4241b40c000b19055128000d14104c030001150315809104020700030f0110f200d0b54a81c805980c000807c50011207084098100900d2540200800302c04200e040e0060b2130081d9450950350b02e42030307076040d161440151010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 472182302 1250 472181052 472181089
    0x30b0310020a021506090f13080a030f110c060f0a0e07030f061803020d181e080d032a02250509070f08071d0a06030e06180a12020c 58
    0x68081902541130008481c0c4a0340140212220705000317001039411000105840080072207440080d4451607c1e5004000300e540000685540d5a881c000c0280a00000c5100c109510b040107000070041c0c0c0300c1c03403c40d00d4500040014019079140d9003000351510710064944180246c42e4a01c00c0c1c0740410070320656000b14814038102d004000507240c044107035485601400c4a184070403140c81d01181e0007081d0305000c4135080c54a42c010b5074000c660002030807030b81e07042841c1a50400303e400e003000c143c414440d070507911001b003280c041d003004d4501203041d10910081008100e090401e06113a0800461550b858155940142d03031030f0000151100c060104609890100590280c4e001c000301d0604190300c5401c10702034035048032098107490380030f000508042d14860800c00d02080d1000a0000c3c1994012002030082405005613503504004000e490625480c4140c1c0c040c3c1004075200c00c2400416031a0580c1030000b90010311090344031408002c039807012003c02c1d4040c3c0c0d00c0e43c00241c1d940074444406c0700103e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 472183552 1250 472182302 472182307
    0xd0606081b09090a0c090f08030a0305090d3908030f070c0209060d0614070306030c090b0a030201080a15030b0115020f0309150405120105160509060901050307030b031002 75
    0x103201d1804450021151148004010803900e941070702c500c1d01c0141c2c416900c2c1c03400b09410b40c151a003141c6001059001d04919240703240d010400420110003400a510f441c0d5080c481c2c0d41b503415041d500d0320541d1540c00301280703445039004422800341205040558120419803000f0741c0d403400038100b00e40140e0b412a0154000410000e44d40f8030a038801c1d0304a040c0d49070441e4061a29400708580c0200078280c18810040c4000c0c02e420800507401113154291903001e510041e003850540070303000d004240001c480160310510082001d036820b225010308140000e00310001c0e903103940c005541c0c07d1405010920380544507812a01c00501702c00c503a000951045070100000e614040141e103404081008000071074000401410700e041001042d034604200495048000300380d1807180002d02c2c440e5038002500510401800b000704036040d8441e0b44116100346a07440315506001044900f481807000d80c0d41d018800388007800c40c6500c900059503110b90642000501081d080000a24144030768003c486403a800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 472184802 1250 472183552 472183561
    0x6050f0f060c0f01050118021615090f051c0804050303070c0318150905010206060112021b0a0c031a10030809040e031803121602041a0607060e0601060f020c12030d060608 75
    0x103480d00300c7e900d0f1141d03a411804d02030f050b4200d010414115a0103826128a10200b131442c00d500e9200c18a0964850040b001c41c018500d8000d8803070300c00b079030a45018070112030400101c031f000340c10031485543d01201851131075456600544400d4018078080d4200072020200625060805c828031002e80031681c64610782d00c13058035001304a49440d801013411508080280721f9181d0b0824110b81c2d10001078080135890308804c0c1d600780441e81400c14441d03450f2181103858014444403000079030540b4010b00104000c1008046510300c0c0100984885251041d40130b010170108804030007070942c5090003040403c508000c14101490364014040203102c04640018100310391800708646000414828036950a002e19299441740c4007040e41c201900590315a0300141303c00c1c0280c150510842c10040c20280c441c115820103c00410740120030600c0340c881c410012a41d14003a00f20844003025503401445c00c0d404500c28001400c3c01c10040200520090100307682c03412030781c004c0d40c010308a03d039560b0406190 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 472186052 1250 472184802 472184819
    0x115120c090608060402010e03010e24010b09100f03060e040602030f090111121009050916060c08030711070302040203090c03070b04061421010b03061306050f0f060c0f010501 77
    0x1050740c0240764241ca0448100184203000c07030480e40c41602400c1124210303941c1070209000d450500c2e100601800707030a5207100c5082d8414164084c890216148041a030303280c4a07081a280f146005080d4407110030748803506028410b0002400b05952464040b52250b5144000c1d081c03a9025101101c803d900403040000300b02501d010242d114003041d000f400100540f0000c61410b1082a240b810100302d5040010b00c02512554400c2c020b180c58202004a854051000390b11443d140c0c3c184a000440d0b0100001d600c1d209000c2c4001e0b15400c000554a1522080020343e05501d03c0000b2001c60b0103140c500002503550f41c40910322803680c12001c2c01081383c0210070582003245c280c1005804020030b100621480e94040c1803403030360010b103000c00b59480040c014070a15004080c01c01b40340b8017028000100c0e0304c0408030091400740e103082c0d840070405109030b40441d051328042d0141c0ba8001900c041c00c0803031468030003506160550b000d000b139454040110180c50405101c1c0c0ba1000c2d03145c0d151001000442c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 472187302 1250 472186052 472186073
    0x2c04080307030e0732090c040f140616031b060f11030c040b0924120604020c0c0103180f0b040c0618090c110d08060f03070323011512 59
    0x325028013800f04a410260124042084c03800c18150160580f8002c1e80d0a4440c40b50345030590000070301040712807500c42407000d020345c441e000e50030005581c3c540014401c91014484080458014090760501ea80c80d01c180000141d401015400c104210303420b11411902e000c488036499000b4000442c00c941c079060b2070b8003614041d4002d112712150030000c1000620035070082d102a50b45180340750340c2e260104c0300028998103800c0080c0d12100c0342203440090307552011000704440300c84035408084544c0c4040402c800c901903202c5412441d0440c080c0d2862544c46035000d21a001280c100780394403001161500341c403040c4000c1003191644002801d2000340404408484002c080c01c1c139140d2000c28a81d1074071004164588500d9064a444800200c003450268240000d11151a000c48500304840300008042550582e0018007502c0d00040c05000c03410040360800a0b260005089c8201c170101141541d4051801010455295a43e42251003180341d000080c400030120629410119800e50070300c0301012 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 472188552 1250 472187302 472187321
    0x50f09131e061703310603020301060f030b030d03090203242e090b06280e030304120b061c0b09100b090c0703030906110706110903072c0408030703 65
    0x5140500c0400e0050008112030071481d0007410060407603040310792446000f0000d0480c2c1136424005e803001c03481c150f256004d0350489a95075116086407104c1300055003100e0171403c6c641d8058000f5800740b12100e000303403c540b0728588090216000c0c95900c10306000c0843d0a8000c0040c20076582c000d00c00c0e081c110420040381e1007019100042c410303503112000ca00c0e4883c3c0d032080800039915101c55421036541c51003500c000311034590300c0407404002d042130300c02000c0480714920041150314200383d0741420000b084c1e4040e10070840444107180c816840700414143c0092500340c0c400040e01c41d11041030100a003009415102d6a84402e003800c14589442c02e107101c648040208514005e44c00c2c00c150b50b0540001d401c541c0602c0ca01e50b8900650a00728090300c1d0841d0003404203400c0c010b0380e4103000b4030380004092031400740000300300d80d524a000039022803051384425030745a8401a42070102d18035841d101214074400c1c5842c0d4540340103039007031081e2a15089a0032340d5240004800c0184043e014005c04000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 472189802 1250 472188552 472188569
    0x20901050909101104052b0f0303090f14060f040c1e150201060f1205061315050103030f0e090c04151205090a020a0909050d08090f0f0a02041506050f09131e06 70
    0x7c520840100c6504100212006404d1044605240b02818002d41c01844403030340146c1000e1001c0e89908200419602c0080c88081500c58900050591328010004074010390f404524001040d1606110b0a5120142c600c8050320001801001079102c1c5014401c003810034498001091062501c5107030a5003081d542e000c0003441084851540015001040d0190b001311203170060a81c055903070030000001d05000c01c0b15201e06141000200615802c00841d072122645541c1c0c1c1c0c0302440c0c0000a0040c209030643ea440b200000a100034448900c40ba8044801c841842c50007041481c0c031156071030195101a01d0400082c2c01040d070b01825030820001d0400508005030041c808400c0c280c0d140d0742d403140c000380460108030b003480118031a20343c144654404400010122038024410601464540384c904004a00c00c03032403c181a01d40804440140d82120425102d0303900340900600c013001c4030340c006044194807260b064200c201c5110288609002d02d0f0171900c400300968186140710b0202c400320b802c0b9214 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 472191052 1250 472189802 472189849
    0x1031a070e0103051b0d050609150a090b01050705100c090527150d08030f101a0313060606050913050112140c0913150902090105090910110405 63
    0x24a41204400030010402c3c81c2c000342c19514956155465502145265414000015a1007449240360401030150100301c1d04e080c010745a94542d420b581c08068102a0003c1e0120400c111401c12a404241503070700c1814032520f050000d59404d0b0510450000b0402055916a00c0d0020164803110544c054801038401c4940300b0000015003c11016400c1041000e80d04a1300188400c00e001e49d2054a400e009400c9482d051a6840c0c11700c4260011100040c2000da00800282003000c6c8180352011070b401c0d01403481c0a440c201e01d089000fa8801003601c450002039402c8200010510703c51a0014411542c402e038031188040d080100144d03224070503500c1c0904140c01400507036000c0221842e415800340740400c003014a01c0300c4600f41005880b105170700c083c40b1820800c203100207610000c46603109110030010311414401030f4086509a15001e504007180e0030040c003c030b003050781c3c40d2030b0043c4c2c9034001c94108106165001c1c007a07889000103402103c070041000c000f6802d24202c4840500a811612174 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 472192302 1250 472191052 472191061
    0x6011406040e16031119080c030606041505070803131407060e040c0309020d0318121511070c15020f1c0e0105120703060512060f15030c130501031a 65
    0x702d20302e901a015603444103240d48000380c228081d50100c1c0784100000155034036082e80408143c1c150581019035004241841c00040103c100002140c1c0700d400000d00681c200303810407484410169000d10070300184030081000740046034446000c5e510944d0302e000c0c40c0341811014070740180c1401018251240d241c2c00800148819500551800990681070310001942c0001d8001140a41964003019420164004008040c10307844040c082899000564441241da6601d400101d040e500c03090141284002c0422186280819000f1001d40d120b0307040901d061040c6a21141001a1103601010703201180b01ca03c9181d458051002801844854029241000542d0244429950507080c51000c1007503010140005a0013042902c040e1462a640100d0a107070180d80980100300c0340c080d07035100d420000741032110350800140c40c91040b8103855540100e525010461400e01c800034840a80c5401a4032a1141540b02e04281c50038050787d101c00811a5459414801c980768540c16501090811000800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 472193552 1250 472192302 472192319
    0x32a13050f090402041e0f05010608092103280e010c032c01110307030b150301050f1e0d03080a0c111f0b0616030311090a05040e070302120601140604 66
    0x343d800341d0181d40110f0308010101c080302c5101c2250041d03e40c50382c0f40c0000a0044a0140d00c89410b80c0c1d41a03e801c903c82d04e0350700b5010b540f0a510020051044500300140d5506a032030f1026503085810075520b055881d000e41040240caa03050520791708415a566004145150f0074000c80c030103e40141800c00c0180006038403610410411030310017042c01e80c85c0c070065503904400d600511541c03078980d03201030f12030620682c000d02411441c0c510034407a01d918480c8600807081d0030200c1c0d040364001800c0401d10204c44042c8018491080e18404a0a000d0900305c50280c540c2c40f500f080d001d00c265a001020b00c5d20400b403008449145038840d0802c44849801c3c02c008400081044025000075000c5d80381e160071840401c058040325160540184000c030380d40d40201e680134000303429284070f61000d1086002c01c28a111240c011140100d40c0045c1c032400811170b41c14540c0c801d4845124001c242d42c103241e1a40c0104040305000c186c1d040d5140e12900c010000f20040044a0601d080e049800c24070741031401d61907 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 472194802 1250 472193552 472193569
    0x1031409030412022704050f1b4011070209070804060b031c1d0109090e0a0206070c05030601060306080606210a0c0614040503070308032a13050f 64
    0x1000424800000c0c0b4105540d41d01024118094080000c0d9652500e1000e50185c120002d503000c9501d445068040701a0700c00100d50080c1c509850304010f50781e0f40030103041260b90b03c03910440202b60500c0300c4006401540c04c40d0000120080211140300518160000c10110b542c043c0130201d40070001d02007a00181e94142005e41c0194003494400f0117901c0790700300000200700c0d0300515a81445684094481c86c101140c14804403c61a1140d9151040d0700642a01802e00080380500040040070b0a105200325a40030710004030f15281107a9240041794003269403603200c45070641d104081404100017902c0c04200890143c901c078541400f81d00d03e04000645e036008068010352045200101d80104000310528681c218060750046860701a024148503107a0041402043d000036079840c112880c88000400321070895101a00901c0001e1a5440d1010300e40c1007d00f00844101c0d41d40d074210040c01c04064800948140c05200340d0340c40e5410b00e02c0d442d0b50411580298002e80c05607012402d00c0d5141c501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 472196052 1250 472194802 472194809
    0xe1002040b040e1f030507210f02150c010e06341b080a08040b01140109090e150915060904020d1203020912030d0e12180d020d03020a02010314090304 66
    0x1d078428213807546068100c01070440c0503000100300304000004280301e000a07031501111004000f0011221080c02a010440301c003003000340031104504004030050800c607038072150b0041c03004240c1d410145865009403d440c15603003818940c0d4015130500c450400c000c8807000d00380012040c501c90000492442400112000001c2c5007400203c09038401c0e0540d03000d210720800c40c0e1003291241da072104d1340e4000d80308a03000e82c0c06a9050f4886c41c0080b40b54104000c004200c00300584400c501c0701d1820b01c13488082d020300144900c586c020a2148241c0d1000f80b08003900500141000e0719030300511242000d1075510040c242c0344900d4020085c00056143d05c0c1d903d2020a4004212005480d00c08400754064401c08152503003200d070700105811450804806410302c0c040d6000184141e4803c0d00303e00c0e0f03580850080071a03900501f0400964681d240540c0c48240c15805403c4c0c40d04010382d5000150491800c0c06c041d000f507044040b40c4400c66906110310380e141c01501400c00c6083c10107100d226505c3c0200d02 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 472197302 1250 472196052 472196069
    0x30603051c1d030a02040f2c1209180103030903120207060c02010e030c101115010302330d0507080f01150e040603020a090b10030c080604051503100e1002040b04 71
    0x108849501c0e10144038032984c0c1d42c0c000e0003e000c10b5a66080100080455030500c4402008045007102e03065004034003c0d0002220700010882c00040781a1945564840404103500800b40094518005449520346000f236000c0c0c1c035108103651541c01c100000080b1030320f000d4119004800300740001a085924030940f6502071030026101e2010402180c03a00e4050b4400b00c0c1d001c2c4610582c640016803003030032908a0041001950f48113180303040070120b81002800000d61002c0301c403071200f020207002c02000741e4081d04180e0b14154044130040c0b291885c4d201400c40c0808070b031290108030381039030030603030300740c0c0082c40c040314101c070381d0b252101000491a0b50f201135070030131002000da10019590b5400100185070001c4c2025005135485900c28010b08081d41c0d450b01580c111000b0b640804d000b449407034901d00039038541c0d0034140d46100400c070003008000c000030005100381d05034010a0710304000035241007041450006040ea1001d11840c07601207208010075900e8010001801044a184103550440e20182c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 472198552 1250 472197302 472197347
    0xc0a140703170a05070906020c150705190b060f090403020c091005131d15041502070602030a060306061a0d020c070302060a0203030f070c08161103010c030603051c 72
    0x14034040320100051141c8108842e40c401c1408800401640000c0c0a00c8403501c40e802c540380c0e00c0d6810b83c1c0313403000c520b50030303501006030384080c1e010300e80703100080000d03500c6001501c03928000c222412040c0e5114680a481c40703004c490400455040c01c1450150350b0701d048443c826075242590f4000d603541c1102405034041d103c410040740c0303004045030f40f240203020004c2c11012801e01044403e002001d902466510705502030b09600e841d4480421000602209095220013954490300c56180e03440c4056000030711030f54200070746004603031544051801403055040c0850f0311031660074803a00355141501318100390880c1452044a101082c012220301005222016840b80d03100e0f05081d003003141c10341c40030390061000658800b042e580413000398880c2c0100004091151a03441d0221802d440f00800240b0402c0b0401c40d52081c444201030700b100e00c5118040d0b034401008044003003425150b008004c50040f07a2181e0090003000418410080c8000100700d80f0b414019407054000c09101c100500c914001111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 472199802 1250 472198552 472198567
    0x203060a0c0917060a14090706051606110c0d081905040c0519030c0f0609230604230402070f1b051005030f0a09021e01030204030203060a0e060c0a14 66
    0xc0103404003c1504809002a501c8006007042e201d10046696200051400e1002803500c50f1000d0a5401082014001d0101e82d05040b01601c0982c0408000342c950031520300301d000010070602a5082500d1880f20441e104c2c0e001c0c80110f80745c0780c02e461f8000d003400440c02c200300d4198015600c800c1012804d103004606a107880c1081d030821411070b0811a0460701d4003d0b0000360103480c10701e41045034440c05964006a17500c10b0075401d2012240290000a640c0b500b00b00024040c08060440c100035000035030b036800c80c56800003140c42d4400d50080c11001e0740d00541c1c038640d410100d82003030780304400e0341c0562a080c0719584d0308641142c0301c0001020126460126920030742869407038030141c1006001031044070360703510010700140c02c115000074264240c480000d9207542180685400607501600031540080f8103030301d040c900400480428101542804000003680e400c11030306004e1034081100140c081100300c00c442c100040100005441141000210242036100300002e03800d840c80c0e01d0042e145c809 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 472201052 1250 472199802 472199807
    0xa031d0a03050a0c150e060f092d031201080706020f0a0c0506031012060203010f21030e010c080d020d1d060601050304030c02030607080603070f0f051009080715030f090203060a0c 79
    0x3608000f8401d861506d008041800b01c00115280210490040389425030341c0c220385c0760ba40b03521122440ca44c082d004610003003e8540d40c0070345110800304a065034285040c0302c4802c030700e800d801d92029805500c803002c00c02001d60144844400c8040d4400541401e100c251109860700d0750710321445009100002c001000080144001400740450100c4004003010f0340c181800a5002809603010500000d10006068103130700c0c048540b20070441400914501494034140c2e42142280c0340e090500503680e10b14000201d00b0001801e5080074080010303101e01251000c9003c580007030074081100c040c001c01c024420000000e41c2607102000b442d143d070f503079580c600c3c04450a0a803080d0081d05440b462041c84410394101101300d1046030150101d0301155602d022200c41481e1612550280c0c003403410702440241024890259280c1560801c41440c0c0e581d0320035949001803950103280020317100740b20800d2065050083c03081c02440700c88140000090343e000a0307280c1c00040c04503004107540e0311b5542c2c0340300e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 472202302 1250 472201052 472201073
    0x20111070807020d020616020f040513060902030c0d031d0402070218072c01030c020d0531030317010821030a0b0901080705010305060d0b040209040302030403080a031d0a03050a0c 79
    0x82e40648110f071244c0b007000c03088036122400c0c1707c224800d04c4080e0314554241460b101c0e40e44205400700d01042d503c2c880e6242c2d40000c1880d607400360f03058042c882c3c034548a80c5900000300180b91080da01c04516410b01c01c0102c80c1400c4000010307108034010451103016a84105042e00c00c101c02c944040019204c0702416200042503d1240d4942c00c0b180103072400c00c4600f0724504e000342c02c00ba2020721841c810040d089031150740c100010700c0801e80c14000341807220f02500710005082074102c00e2000c103c1c061002028003071100d03401100064046020321406801258034a8014900c0704010122003003551401b118103074a48001503200d0502000043e8900c1c2d190b001412003000242000d612540c54800081d01c070112801800d000c6801c20300850050f040007200342c40c107103410808a81e107903101c036401c100689074043c0c015003c61009200100100321640b00030820000342e071320001001d0302c00d2200e0003a0488031030301044103900411884004203400000b120340c010030764900351825000500c0d1040140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 472203552 1250 472202302 472202329
    0x10f0b1018050405070c03180e0a11090306040807020a0f03030917010f0c02030a0207330522030b0108010207050601090e01060905090304060e0d05030a080c0c010507170702011107080702 82
    0x150a2409010030170f41c10000010081d8041e695005445809070100964078000b40704603000b80710b03294002140c14203907034407040800c407a070320b69580f038260f400000030302d0f10000303850a80b0400c1000590f841185400800c0c0d100801034007050301d800524584016012313601c1c52240103070303200090a000c3c801d08002c0d448a0612080d040040203000d980c403000a5403a0000101d40015101d030311408078406540010010a540c0100d19028030041d210542c081d00c11001003d980902c941032044500c01384504504209658076400646405e5246050845080f5810f90040d107481e4410031088012407008240c1605460540030017040a040c5980d0481c010301e1243e0100800c0c5140400b401080300020006204454641d500c4283c012000030410500120345a0018926170042003034440307540c06204143d5015425144103070800020400c160700f504c0c401ca40310800681041203107110030015500f100d81026040c40200f009001d0251049994800d40a001d004d080300891844115981c0d1401485034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 472204802 1250 472203552 472203559
    0x5031c0302090f030a050609121e09010e090405011b0813060e0309060403140c060a0206010e06042705161401080a15120c062102070f051b0102010f0b101805 69
    0x5c2924a041a98458170151041900c5006024440300340d80d03a610291400e209084240c1200e0400301410020746078800b030030641c10f000c000c02c100002d82d50390422061040c0d00403000450078070a080021070784034140100c0c2c1c40600915005008030f154014503005081640041c000400071a640310140c83c1d4000c280003e5880540040c003c803c120750019554014030b0180702f1150180801010000c00f405415503d1006a01c654010001103200038112a0410005000000c2d020b0215201c9841c451740d0241a00c0c052650342814810481c08024030003142044902040d030050505120007208000e035004141049008400300d807107458151b220031030030122500d442500541c2d0b82c00384183c01c2c82e266000d590410710000009070890142d091070064000c02910304003041e4040000d8002500024000c2c2c5258618020100000d00200041c516803400054010a0516581c000a080d60700301c0750703403004c103909001613005e076070321414922080b0640504203d00305409060f001c03070304248240d000d141d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 472206052 1250 472204802 472204813
    0x902030a0501020a0302040f0b07261632030d0f02120108060601110a05190501020c0106140a0f0315050402010215070c02041b0c140c130204080705031c0302090f03 72
    0x40941c00d54010012510948c1031242210b80c2c48840f45014003a18601410382c00c400d90b0b140b0211a49407005103800b0a403009000d041c0502040d10b903400c8680c00350700700c901e100303800309003401764407407130114003c40c40d000b4585c14041300c4000f5030a40b40d0141e05180300c001d607140c440d51049000c040d015110250390021a2580720f43c0c1d00c0c12076660b0343c5000d039082404035034900c803810070214012491050721034000703004000586c03c00c420303040c480f03864000580302558244141000341d4000e0003940010030103104800088410201001107041090b442218541c0c1c0084040002504c007a0141750703002c0c400c1900240769074450006034200340305800016140ca028204000a82e50007005121500d13000392020440b0680c000e00600000100c0e940721004509c001844da0002a134070740a08002c3ca10560590303444c10131740c90100710300e10003224040d85503039000f04040c41000700400080c8001d040440c01001030306107174070320320010003269428001010340008100001d504c61041e51352320004003a04031003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 472207302 1250 472206052 472206067
    0x30303020a0c06021c1103070e190509090d140a140a090b0c0a050d08040b0f04081e0702030c040b060a08040203031c0207060b100906110c03030c07080d090b04090902030a050102 78
    0x2e00b105c0000c0300c1900792901d0301900c14500c40c0c1094901c5040180c0b10b485c0c1001c0d00404028110f941507441c25003003080180041219118442d0240c040c03210741008040c8000c06d044080d254660300c25054411074000d00c041e0441540c0310b80d00c1c050714050090314503940c01409608807030410050300702401c070440010703125a1400000402214141c00b95082e21040001c0c40401c0303c5d0900c003920f014003401c0c940b10104290700e00f00305400e50010301c5650980e1400c407034041c907980c0002d655082e41d04e00d80008619141581014030482401c032500319010440b501c0c50354001079150055000303070020416035500240131034500708221001001c0d0f003600e42c1078040803152002d000c0d40c08284c0c103d031418100200161241403460100070301c42d0f416184d4010141c140041200d03515030080314901140f00710440070b007003a1418002000705011960182c01030b1420010300d5450002c44005400400c0503198041040703040340010b880503111a68400b0442a00d00c0c00080d01d84095a400a8441c0d440001d103070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 472208552 1250 472207302 472207327
    0x40204060801090b092419080a110612070f020a02030a110120031c02070b0c09100504081209040e010f0b030c0904050a0308092118100207030303020a0c0602 69
    0x254103c4000307100500520f030140040c40641a401c0c5c452400c90f00d618503090b12018001c8070b030040c001c0e50184c840d41d019100c510342484950b1032540960540e4001644517014050100311072126103005480d0710b0329000c080160400c1c0342600610343c0b010042100c241d00c140d64400e011100029400a080303d120420500741004008020343c0c2250100e600100a000c00c1001408001c1c80c000e103e2000d1400c050f104141003000829142c00703404480d034200032460010310121072440c0a403070040141e50301e0380c9485041c000c0401401500c2c1051120500040001c070310000345070f080305064249450f80390026280403902038400301c0c00014965003021045254600c6560150780341e9081102240d00d07009020052041044040c0c401405070303081480f900d40400e004001084d0010b03441070884000240100302da0300045c40f8481101102c6000180c54076181b0602c2c030381d00034134210441c0c1c00c1002c00501d52019507030340c00303500c001402d00d0380201f05041a203001e10510920709400c1070703040d5592000711004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 472209802 1250 472208552 472208567
    0x20f0c0f06120a0501180b0a05012f03090f03030414010e060d0e0d1d03211209010504030f030507020309010c0c0902040b1b01150b090f060c1b030d1d060904020406 72
    0xc880300c1c00844c4221406d40c00440c083c0c00400c0b00060841507041d41400c1c0111031440c080303401056079040134462040d082090001ca602000319444c0959199001001007042060000d00310078417951085c0030900c1030100d81c0700745100881c000d013480141051090081003a50044c020340820045c94010702901e808404690703207100145c166119500298030410400a00300007440094042c1d0262041d807075402410340f108845034540305056418a8042480e421030300408171042d140c05d944400c01c0c0006c2580158480130071203107a0070280b00c0341c0381a00e0000c5d900e010b149609810082e003141c545080c0b00b44600840b01a1100500030355a4540754a410031140d4440d0409207500c4110001d03181d005c2c101132040a48100c2e201880d068a1484c00c60400690b421003030a00c0d5200c40d0318414124196034940013013040c0700ca203402420103568400c404040d50000d80c0d00040c0650841c074a84940300b64048940600c56010900c510300802006c0042841801142d00c0b0703d07042440004c0c041503603a00a000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 472211052 1250 472209802 472209809
    0x40303081006080709050103020d060902030403090e010e070507020105070303060905091608030909010b0703090905010e04020f010c2a121b0b210c1303060b010e01020f0c0f06120a0501 81
    0x207000225964801c2254607150850792980040e000750000c2c032040d8800e03002040e03900c22103a00801c06689071001d480032a03006840403030100302603c40c10401442c0d40c0000d60300600c941c3e0300c40320942c580408050094452480b00a040140000340a001c05000364804805000007140c1007081d0700c1d0200c103007992114042803012161140706400a41d4940010854076000380c00342c0081e07030692a00500b030040e600f18000c21402c0c0b24007008042034000142c070a59009000d0f61004c1c1500c0d042c980144800071228110142c10090600100004160310811a9514103801032a004044007250f54401c0e41c0c2c031054000c502c5051010340b8490074400e2032044241c10113404c44984480c20750b1703400e40c0088c500c07551400c18150036011140901b522503d2401030f0b40180407080345803030b0680002070300010b56a070750000c8458954031024003036a960b0001c1c140c03c10123402e0000300098040c0d00941030fa91000305409600c0b8842c000751f04422515880d094031000c203500c000444107424a010090040d040900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 472212302 1250 472211052 472211071
    0x60f0507020c15031302011b060f090213090b0441011401060215250f020d0f0c0204090c0e0403050d0c0905060a030c05040b0a0e1801030b190b0604030308 68
    0x103c80c0c3c00b03050048100e03400b800351044444c0c0c0c9450640d006462131440c500b400c0d9007402e001c000f0400419201e02503510780c00418440002c03845068410040c40c60f9924a070685e82515003119a40000c2048101c250460341140743d030310f0f080d403545030b41c0b0001d00000b00000c0100070400d0300550052030311010581c00b10340e100000f4050400300c080407040c110703c01d00c1500d00581c443c0c1180118440081c1c2c00d55040030b17409007090b2075580c1c8101d2940d8540c00c0e07030b5141400250b95510004a995043c01150340e114070b90318040c040c0404078080281040108c46021b80b03d42c0d40c9041e15001c03c024120100c0062100d1f0b803400c00c00307251504020b802500000c0144c544141003881c2100b034144940d4581c010381c0c400070111814031111b00c2044000741081001d60040c8030080002041341c0c00a00007601d001011560781085ca03600071801e00850000311002c8404075100c8400600000b00028650b5501030380007210400d01e01c011f03074840c001404c81d00c545079412040004022003070590089000e4030484001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 472213552 1250 472212302 472212319
    0x5120405031c052409040f0204020702120a1a010602100e1504140607050403080a1b080309030403150e070b0a0207320d020a120f0c1707060525060f0507020c 69
    0xd004c00c85441001038040c2e4003002c040300160006486038401d2000707074005400141010361507400f2401d00700c0d01792501c810951004c4185000c1250391840e0b11000b107110190440309500d0000065a1508180920b080c281d856690800c0c14000412000c5e01104904180c03941d01c0c01e01d41003001c0d20103003101070140b10b4080e1000040000b4001d804031821130703a2000580d481c0c03450741c2c103084030094000a4070000c1d0505800f030042c0410310341d8000c0c60280c4500c0b0007640d641ca1840c40d0032810611545850300d040340c28690090031000700801c45504403115028821341d0b8020a940403410b01d0404e80042d07080c110000d1728042c1c015600008101441e242c0c02604007480c0c609400c1100c2e070401e50704003d606c800c0c0c00300c09000c50210885200d03c110322510401c440307110295a02c0640305105e8004555400e100845a640114200005402413080d41071451030b011f0102c020300c4d80c90303500c017001c1d10151524402d00c90400140b68000d41070078005680806c16802c00c0c500094039041f403200628410a2007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 472214802 1250 472213552 472213591
    0x180609080f0606030303010902031f030501050a0c03060806011a1c0b01080901290d0b090a0201090f0b0f1602130b0f0103060b0d1107080a0f17010605120405031c05 72
    0x350b5140220300080066055078a000d0041000e50b0000304440030852110000702112000c1c03400d41005988294004901480c112180c1d108a61810041c18201814a0030811425101081440c19600c810341c0524030600030070714104203440740e084240b01a1000d10030800c1000015444000094030990318104151541e01d010380c00e8842d085248000880300307014140760002f1450070050300c0300010344002d26141d12510782c0c010a202c1110440e10740d402c40d6030510f0842d80c1c007005e150050000e1950000d4a641040e0b40100f07280a0f082460100040000c1c021064184184d503401005500030401c400214600c9030314070280850559041c007039041090303526220340c080d008400039a14490303240340c01c01c2d55101c0c600020b4002c0003c4440016000c020722400300d10110003c00342e03070000b52200c4000440441c00208039240381307a6000d03251000c440c0144000c90f817040440703000131041049510240c4907414400d0441c8641c1e0110030b59014188009078410109402a81c40303040507241c003810003c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 472216052 1250 472214802 472214833
    0x3030307022a0120491e0212040b090315040b040f02040b10050a02070503060105010c02040b06040b040e0108060a05040f060c09080609210901020c2e09050906030a2118060908 77
    0x600008045c0403030130703a40d011244400d03850103c6a50b440b5500c1100c07d541e29041c80ba0307206500079000030044100014441d501070600b0088010728560b503d400c50b00d940381075119080c00383e1020304002c010441480082c01035507603641180c820707444010b140502441604001900c075a000690070300160055402c00200c0d85008200c1d18100c4e0381c180c40301d50003441c42c2d500700f100515541103070b942e20810520011824070708404c0980701034144101c410b041c9504001c01140b800d2001080b080c829414034007000000360000c819141042c0c2c0c04203000c10f007010340f5481130704d070300c0c040307070002e840b244030380001c21000031400500d20040488030050205400c00090030014a4841c8240ca00d025922881c5101030301d06084100f0110800030041c0c18945100c00c40310702d21003110704019140000c00340e543c00e0005140c609001c5400040481c007c01e003100c0c1c1960b82164190b0000c1141e1044506d10b08075407400341c028040b1002060344081107141064403444081d00740f089900803418540301d001c041544004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 472217302 1250 472216052 472216183
    0x7081e0103050d1101060e0a0c140310050f010201090204050f10380705010c030c0806041b080604020d05010305070602060c0a120b0402070203030307022a0120 70
    0xa030494003402032210f602100391107401540d85000195982c8200020347c540559a88a005504440020400720150580117020f10034408100c034280d2810800d0000034030381c0e6914041211016200001e0308904100103038010203900300080d410a04140c104079402021b107d4180c800c00742c140030380c0c0032982c444560008691720500603c8203244080700fa01c60417640d02404c8918400d200781c4051414a40703036500d909403181d004180e00429240c03514810840c0c1c1110606504c07400c1074600b00401c4407071f036400003040c810000800062002d2007010611980f12501110040c980d4040140002d50352840c141b6aa40e807144200c02c014000c90b00131078400301f0003204642e00c00300340d0341e40c2c20340b8442d0815220004100300074816034410340c02c200040058074103002640c45600c194000d450002d01c001465601e201050040800e030074121030703400c0d50503a0001014112504070b180126025403d03103007800e00d0141100b0190201c440400402c0b040c1051041500440c041401072450080014200180c1d800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 472218552 1250 472217302 472217309
    0x12030403080906031807080a050c010f0c03080405101a0a0b030709030b060604030b0106050c010c30090506010b180102010204050d0803100308130602071a04061d0907081e01 76
    0x1d0108000d080020b241c04805141c0002080c104200401c515540503442c040641e80316240640007880d6000500100388a02500ca000c2030820030a20707007007000f00400441310944002c003072100a0b0082800e01c60308110000313800d00c0900c0b0411148110115040a02081c0303076410b8850488070704003007448002c007419a4000c003216114032004608595884000d10b400804a58104005200010125180d42003450081100e920b40c2985e80c5103105000c1d095850144a5200344070484642446812010301315020008036690000c1100305241c038400050051901302800340d1054000200310504120003c001c2c40103480081c810000101005a0030303801144103e5070b101c5288940000801c0500c3c0007580c0c44062003058054140d1240d40307012980d00b240c6090094200301100502071a80c04201080c043c11190001c402001c43c4446261440c2c4240e0148d8010010041aa0300c0000010302d03900040d458003d207003680c94603205900406060086480040c0d0030301d010201028402e01080c5036058 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 472219802 1250 472218552 472218563
    0x20a050613170a03020903031b011a1e030c03010c0e18101703090a0620060f1303090902040b0306091e2e180518030406031e021812030403 61
    0x10220382102d466140c00c00002d40b8240341d0200400150381e60280000d1100c941d1600080440740c2a884178682103c1e85274400400c004101d152400103a96800f0300c2041d000c40302e0005400401854000c030742001501d81c002a015820030070708001c09034001d44483c0300c0300d40030f490301280703141d642140320b01648083d1030300c0b082e40d90410024060084400a8502d014180d50100e91a0000240128001c442c5907409140000c150f1920501d000a030f181402800c1e2018030000c08041c20140118144040040c2414002085e115019400c0602404c4c11800802c142002191115550340311101c0550003110711a114050b0040058410110307210780403884004007445540a90311004042e04400c1410b18031413120002410031010491020302880182c010003050b0f00c85403880d4050803059910141c41c0e4200d0440d04d400c0195000380000580d41142d58516020948020964540d070800c0c0c0344829051045000041080c03031804101040c201d40302c002e403014004001c508203090b490340a20b000003802c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 472221052 1250 472219802 472219823
    0x120a03030c0203130506251505070c08300130050a02040c050f0409020d0e03120412121a01020c090c0a0309060f1e05010501080c1c0e0d020a050613 65
    0x6401c2c88000741903a40300c02c1400c402a0308003903480881d060f130207070030442d061038010030080c51b030f88010f018054000c0c0007801c2054202404e68cc40300d44d58000e40e0912a12036074081542a10144460b03445030034082d110258404558442c54820080300614604104c4104042780d080001490354081000b21600000900b803907120583c00c00014080d001104000c0020a216843c0403030120001400104102000165a04040c0820707100740c0301200d40000c8603400501221421414090040354455030114210b00c41d04035587d010307038080c00c880208000c1e051505101c441c8000c900700a109000d0030036000c4030769041c851410489141c500b1103404d0b0444c007050000c81c4116001c0d4014040d040d01c01c0d0008180125294030f0ba80856030b03590540c10030310742424007200b81a030940c0700e00e42c0034010038a0407000c2450918580c900700c0c440c102c114041108031078521740c42100c03140e114542d0304104400747d900f0300b109142d0080d1b580d1569001641c0c6805040d0114a504c0d190604203801c0340c3c0d110b1032041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 472222302 1250 472221052 472221059
    0xc0901060e1306090b03070b2a0109050a0c080c0a0602100902040f02031317160b070c020a0305030c010608160b070201110102040605120a05071202030a0902120a03030c020313 77
    0x10740707601d000c4111507084204806071818a201a004500240021940c0080c9002d4101c00301345c0342102c0c0b43d1029024210822500121030075116410614600a545550741c3d0501e4021050061617039000c05011805004210810403294002c940101e80d14001214005001882080142d01c0a4810713400581e00c64102441001c046401103241240010070014040c84054200c0342aa40112440c1400ca41c0c000e40c1c5da800c000422403998442004410500c0c2041c00c1c011088609907800034004d0501c1a604000420030fa12507108501100d82c00f07407840691650300c3ca8502d6403604240b07400c62595007046000315140d100050740c01e05c42c4108291802a00c2d1030f10340c0000c0385a0000da410b0341082158031119603c00e074240010b000801169568580c1c54003000c010320403e04000d8080355020381803000740401c0c5c551040d000e01082c030100c0801640c90300d07241100e40080228500088d080502d04103000b140303200205820b002503000c0d44050011401a00782240c481c451503c141e4072140c03d0203000cec07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 472223552 1250 472222302 472222307
    0x806090703030e030f0a060516050705120f09030a0b150d020f0d05011113150804051b190603021c0c0804080c01290a0b0a090e10050d030c03110c090106 67
    0xe0700d140001c1d007a01c40b9420300305c25060074080e0560083d1003064503417003400043c404086900a0380c0a543c9095030600c04183d541c1510380e00c04403003240c82c44001081c40d40e2106404412503030410001421101031040d580307000c40c034100080310401410701d1021109030550500800c1810f056500138581200c0d91103c00800c4007034040030900361810b65071540d240f00c0414644009003120505002d519000e249400744000a0394241e04018040200a8041c0000102c1c009000c1c000c0a4030301c1e048030714402888010801d4581150300c00101c80502c500c1c0000d001c2d8050380100380e4110502e50307007a5412000490340d4180d428420321040040c041c1d80021b40815844000b401401359131070004100003004005000c000141d040154149031240c00c2041500d141001a92000f00041a902e42c2000464034020304070003200d101c0c1d880b05480080004228000307240c07251010384002060078144491904000700f500a0420084020680303000d202880b0000c00194a002d03240014620070f460383c2000400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 472224802 1250 472223552 472223567
    0x5070603050c25060603030804050c04060e060108150402191e050a110f120a030f060b090d0303091704151e0309060e0a03050a021005010503030405040b01050f0409020a09080609070303 81
    0x3080e614120890550f00007103150065034000d5010f40c1d540000d42c181070a2840c01c200d00901498400c0b403034807904000884900b01400e0b03101a007400c0c556030b2548d92114244841440c0302101303a00c00d20009544020403c004c4002c08079606550b606186641281981c808400d5082c481001041040c410700880c68814201e620140080b001135500007000c1c040c2d558680b042103407440150500c0458246a02e50f403521440040e02c1c202c24003802103915054610300c040c82a24807490003240b84007000c101307050013504000f01f81e03a8807000704903d804011302842d041c0d412034002c94071181c0e0000d510f260000d10a1401c0c4090a50050340c41c0c1d80c600204100707178010045044100d4415881d070011019102d8180320744d60031903010b1384605540300d81c002c10003410702c1d460b07032502c0c007242e480c0c40d005002076140001a1070a4990644000849189950060701d00340902c0500f8841034200103000301f8003441903006000c0100f010b4954000503a00c4156141d00e501003150040c410741e010900420100380318000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 472226052 1250 472224802 472224847
    0x3130504090f05060106030f0b0306040209012d09200f03011e0b1602010908070305100c090e010807031203060b1606021e090901081212070e040c020a05070603050c 72
    0xd281103402c14542d5502d0034103000345d0003100840c0d62400304920560300303809016099082100030b4016854142d0010307030a07800602030f000403010300c0204000e6400003090f2803405940202211460f0380c0c0d84884103009414076454610203642c1003441200041500c0f8180c3c0d0720115100002030562713003011020b912032400c1c00a071400f060300040c1c000803001000c80c001c1000f40c018071100150011b4600025065000070b901407519075108060130408100c01040070315030841c8a10010841300c1c01c1ca081224100c0c4207801491071103914000014032860300181b50012a80b042c0c00c4404240071098040e02159042c2c0301b10543d64074108010a5000070301c103690b207162446002c0050411015645060811600000c1c00d000148002220303038040c82c1c0301c49400d0042c1000c40c020881c250300c0307004082d101c0c003400d042040049040004282c1c0203010300c19540c5084d030040d0040005024a0500075902c413b2100140d03000c0c0140b500100e801d910a000d0302d44174501500c002c0c2d01c1d003501506807016080c00c051 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 472227302 1250 472226052 472226063
    0xc06160e060a03090308160203182701030302010c020c010804080901030e0102030703230103031b053a022806140103050313080102130303030c0e0a0e01060e030313050409 75
    0x210000c4181e81d40c03030140220780420340d0001449031311480c01926412000c0c2200e50308a80751600303503031156400812141c01002018000c10f186c100d5002042c000c0102a40c6012400c2102d4068007900200c8038103141240d000394005d21580e105580c06030b854100c807070070319070000e2911000100420b2108005020900b018940029001c0000600d80d089800c16a81d100020fa100c010260040565507080483c03108842100d810551460f60f004d400e43c2800f41d070000c01e4004204402c81030100034000b01c010a1820715451528000c4110301414040c8820b504c0810b20111102d211340301840040c0c113149980004040303003010304036904031041000d80d800f0110b0349c041e04d900800c9810000558424002c501c03c9004546510000e0302503d0168541e402c02600ea030720501071002c20140c900d00388401c40340c2504002a4175014640c0480e5107040190609402240480001503802d08900016040317034283d036030302c1e0b051142d86000c1546a124083c000741c0c0040983d64280600e00d0140d0100f41000d2064 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 472228552 1250 472227302 472227317
    0x7031803110a12022d10050612010606180e0601021015080109050d140a05090409032601030c0b07030c06020921010c031103010333090b011a0c0616 65
    0x1503a924070f4948800180c0801030700072200c0780c018414420291203120050400b00d0a21140140400ea42d482c0700146482d03030300d42c07603c002c5034903503d95030400301507820b40030000d200090b16070381c01803e85500ca042c481c00140310380100281010010070360342d00440741603018200c0ba240c81c01c1e45002400d60344c0c0001c40c1400140c000011441e00900c16803441c01d1042024000b1100070910180403200e2021b0400c2c0e4100d020444600c41e10b41c414101e43d21035a04440c0062100c8460404403440080344c000e405400c84800c450000440600010904803485002d45440030b44d1a180f4144c4180142e0000030b001c51980300720580013402a40180107904005408801e0303203407461481810448100c1c6500c80c00d079541e82d0403181c003194140503c20383c40540081040c0307503524590340c015403900e40b07400e5445091150644208122851034584410b00440d45003030203000903904042c05440028882ca103600080102080c0100f1034200688001080500141c225035035540151610203220f40a56020425807 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 472229802 1250 472228552 472228573
    0x9080703030e0c03010911180f04080f1204031e030e0a030c061103010b0406030b010e1e0102011104081509060f040f031701030311190203101d030a020606090703180311 74
    0x24420380088038000c000d400d0040b4004004d004a105040d021904003007103000411010b480306802894208bd4841400c941e18505400080d40740c0c051300000060f00b00061044c1b205141d44003011920144611a20071304070743c01c03850300341e003240e07141c551294640d000700092102180c000d590009c00140070b22404109903100d40c1040070980c0c000d070014040311b80041814071032590305128100c02c0b04c2080c02c101c1019103420002903820010307000c8802d00306900515134603e80e40700b0b40004012086450340c0580b255100d590440c0c50301c40300b800604428008000160450100151546c0500c07501d01c82c00c800350712207840b80d00d80c1005107141a400d21070031845c182c0120000751303402c9000314002d0307441c1410365000e141070909207148450b4011a4220003240ca002607076001c5030115022003000000030300c000f00f5100f42d82036503040d42206800d600004ca0201d4880c3e4020490b0b5100754070480c3d4808207030352400d209a040312003990901114014a40b02180068042d10044540e091010f045418000a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 472231052 1250 472229802 472229809
    0x6030e070b0c0a0510050c03060d03121a030f1513021c05070e01050102030c06010e0711150601140322021c12140a17180d05070201080a09080703030e0c 67
    0x200010a030032075070003858082c3c1400424040e0790311300c0c4031780e15052081e42414248405103000c0507209911400c1c00112010806026044811180c001054203000c2003c81c1503030000440c071000c24060080c058440d90120041c3c0225180807542409981ca02142e10b59900300c01e204048440202c0c0c0144000040c04c54942150142881c0309101300e00070b1920742e0815000b000c01b070070706030700060665005019540a244d07002c2440c27410b465015100981c541d4400343d013110810300c10800c130500390060030100c00c2e00d403c1c40120302d8803822003030305e6909a101103003c0078100c92000310f603000c6006250710485c001c090340c0341001215140c00101425000580410748803021006c0c004100d400c4805050311042c00b0f80c00503030280e0750700c0c1541c559074141030600310082c1584d52003407407103405498481c001800201805d20044400000b4404840e514054064050400e502171074069020491080c0020408509801040c014a920440c0f0724204056a60207902500300000030f0181405000342c03507001502d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 472232302 1250 472231052 472231057
    0x50a050105100f0b0d090203100e011d061f05100323010303170402010c140c0a0b0a0207050919020712121e05060a03050613021206040203070b1c0c0504061b0b0106030e070b 76
    0x40001030002002e86901c10042d00312011400000900b81c803c200070010014003080710ed50060001222031456031f00c1e15901402e04034941c02580d4071900e01a00401071550590144110380300990500e810712100c103d080300340d66400d1000400180b4021130003180001104641d6821900c103040106031055107a440101c000c0c96000f0343e00245d031011810105038079103001d610008019941d9450318210445000130340328401c60040c180296a150046a400460b1f0319075003120f484000f038215102d280a1402d1502290344206d00c2001810f901040744485c18244501c0413184040400038410b81c60b0481000f010740710040a03d640f03d071400c10000040b403801d21007a0f10400803a50310035041c01191040000800900b00c501640f0b510130020400103807030010703c00040d940d20585064964081d00d00c0c0300031b9086031031030381c200705400e00e03425940380354100029101780c0b000303030700d4488105485562005042030ba01c9009080008a40010010140a039101d044400701c01400d0f05c800607102c44095210340d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 472233552 1250 472232302 472232323
    0x61b030f09090604141f080d02030909071403360706031104080a17070c0e010e01170706050901050408060f18073609050a050105100f0b0d090203 64
    0xa50300020414142c1c549044031582c00300c0d085a0800c006888a09280c3c0c0301d00c0c004183d83d800c41006a0400d05c84c0648800307507402003030410210fa601542040c0000e44a411012109004642c00c2c0c010464040c05030031801d480400d04480745007540d83c1c00401c2c0320943c0001c08039030000c6221070900c6104011003003128000a0070030000781591132801000a040f40ea45031004820781d070092005100100002c1a0f400003641c2100a480e8035407241c0b07008a9a0f441111402449a04210000100d8004010714941240c032491103020f0160b0b40c034a10203903a80c1018059480715008402d09000780d0380600098494140c0c10714100d801c00ba200e002d01c501d4004181c80f4a21646c401004015101c4010107000180c0c04007032000e01019498410f106d86030114040d03001d032040a083c0b00c407005009054007903608130100c105c018082c0b6800c50070b00540300d4142207010366030b41d420140003503401e070000300544007211504600311a04611f00381640c48150010700c100203d044d00e40c0c45940c0541d800700140303841e2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 472234802 1250 472233552 472233577
    0x3060b0a09030506010b0406020c1504050904060c0f030b03030a0f02030c0d120606050406210915090b0c09030712050f0d1d0108010b0a0e03010f0501090f050f011202061b03 76
    0x1c4a096003400c40c07070003c059010f4903041808100a203c1c051703010a00d81c0404900780c3d8010000c0110558a03900ca009a801c0781ea002010b00003080705100703140c0c00c0304c010301700300351606040034050303050440540d030804201c00e403d0b40c81000b02c81180d41c440c0444540381d80c80c52041e6428507400c0e41d81c0d1030503c4002ea00b940d0010380e611801e80d00028603441905c0042c629814180c0c5401d10307092026200320b805c891420b2104a00c0030500310a41032981041a03603991002c0c0507542e04914451080040c41c6400b000e072183c040c50f0000840305100344040352007a110040090085528100300e40307108250444044815000394001c0c0d03900c0c08801c1003188181407a42e100d000715038007614900c08100409003a86810400b0450040040c441600126100340006152441c8495841808203000d4050300307000c12007041c901b500004002e606a80a900c103422007410500082e00d81c51821100c80b03400380611003a07414223410100061030054001c001c1003c103040f004080045458009080d500300c40003400c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 472236052 1250 472234802 472234817
    0x3060c1b10020d0e061f0621060329011a0c01110d0b0108090a1106031315151406040b03090f01090305130b0316140408010f02120601020a03020a030f03060b0a 70
    0x42d001e50500040f544810705011b4400e1001d0103081c0303044207200600c50703403007448035a4406284081101f0708030061054010000d00c4101d9403454101d583d485212450003210190345078658070b03031681001883c107c8050403800d4a010040c0dc00c02e5082c0c0d4451480e040c115941d6448403801c0035900f002415540949410000d44d04030344030009010410000c007000c0c0543c01c501200400075904140a145541c0140c03112500c0faa200410799241c1d65080c90080c0800700c3c00701e03031441c404800c2e411503a81c3e601c60034070404982da039a030340440b04450307244907582e80080f00740f105005483d404405542c0c0b00da85281154010b462801c1100c0c01c695044100360001440002c42803403c0405c90406001081c8031110b241c69840c1110042100d86509100d80b0101300f514240044500188030030b48016110800c020802000c20a42203070080d4440c000c4d01601ea00754500086803503002060745d01e8015015005421034404d9550100e543c038040602c0c1d00d0915554040214401d07414401926040e5010313114080c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 472237302 1250 472236052 472236071
    0x5010f09170601360c140c07090e0d0503010b09010e0d060218462903010303051b0a0614040308091618020408012903060c1b10020d 58
    0x503400e041001e0040540c3c0300315100035500099440718130098101c0001300040140000c2001c41d82c40781300280c29420b080c40484c80d180240c0c000b203003050440720710365000c000c0d01c0304900d10141c031750300a540b4507008540c05000400c03d40c1c01c00ca00030000c890b0149040e400c01d61a00f00040c0b80c1214681c000e4840d194049046170241040b0200d604691a0444040321800c0305680d010100701088801c0d0500c46000340c10032407444c0c1010404c068464034040011088946880344030161103e5079480340c0d444180802584070305481c06080382c0c181da4040d91031502d442e0003908880358440c03019205214a00ca2908100082000f51086440c04004032054043c18102400c0042100801074843c004e280c1000c000801812800a200022900f440961071110341d4032602800c003d00440d480318100d5403d10b181c804480e5580400e400c0c40c52072042025405a003418185995401c0c1140c1c030000b0320b0f10402289100d00101d00018071640c1007001150901c641c1028400f080c0c0e04041441c8501649691750700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 472238552 1250 472237302 472237319
    0x80a0305010b12010501030b0409152414191a07030e0a050913080415020c010807020106081b27060a120b07110a2a0501020a020a05010f09170601 64
    0x2240109075081c489400c080300c10082e00c54140c0184038844c11f15a940100d00160b44950f00485040350300090b0000070b102c3c1d40c07442d10014000c000c004606203070444e40341080661880441000b646c149100c45001068010140f00b0b0900d2001444900390b000f444000500701d500c1107106507401619400e03203807510310741e02e006000b0304501442c01c0e1154190140506c136944500c1c0705160f024401d8408a81c0c0c0903041d0610341003e00ca540c000c1203005070001040b900039600015a0a0a4942a41c81d06d41541c1c6200c4101e088070014014191280c001e071101402f02100181551030808005000b1090000348100b026185c0340c1c1486100c2842400c134040204a25010b051803005224104909a0080503541c515600100c024100c00601c0030030050501481030410034840210340c451310540e40480e50040046103001d0300201c10310300740c1104902207965440821102e800a42c05003542007002d06200c0155040180d40da10041004030500000410708001161800c01400c50005000b155052140d038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 472239802 1250 472238552 472238561
    0x50706080106020a03080a0c050d02040b0405092410090b0a0305010602010c03020a02191b030305030405010623040c0311070c030c090212160e04020c03030f09070b0a0305090109020409080a03 84
    0x96400c40415503001c2504038020300e51041e0b81c0040000c0c1c0310b0b003808c4155a907001e110740001c20035102050114402011800030000d8034001c170340000190703543c42c103a07852007d00204400400196803506903a103041041100210316058244001c0082e02c642075903100d50000c0f0321040010303498400402c1802e80a20446109083e1890158907100300c1c0d00d8007130354803d60210319503001c03035489545000b80414001083c040981c60b040d0034042c00d41c1c03030034000e141c0d030802d6405513125417070f003500042d40f0203104401d0316005481c4080d03407007a6080c0344100030091040c1c2c81c2c0403042c1521030705119203c032285801421280d1064000c07000d02030840c100440850b415800c801802841004180c51400c800444e00343c0c403907600040c0603d00d4231500d07422204100c3c0041c01c2c503045400401e10401002000c0043e6101307803c000234200003655184040c07962060b5074851650111410802d20329114031070342129a110301d00000214044409078046402ca46025200f07588030b074004151008200c0d4103014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 472241052 1250 472239802 472239809
    0xe0109091b0507060e010204081506190b0a0c0212150c04050105091e04060f1509150518030f060106020d1107060c06180503091c0b071b0501090507060801 68
    0x100700000303031084000c1025000301c003441c0001d01c032002c11030303500f081140d400c41004400300b40000d5450355a01e00d21144e45244400d41441c1d02100500021144c0c186101e84404c1103440000503510246072400510442e0b10140a8a04202007070360940c0242c1c5955802007d144040c80c01030100110740c2c4c2c1c4000b600d05014100140c910030407c030401083c0e9000c025142c0c41e1004a070703041c4c086203245055800400c15203900603006401c20500003120454091003400312010114030b2541d240300104112010101400741c035054800c02c40f00484c5451141c009032066044040800001c1211000082d2601a03440c005c0c00490340842e0051049035414404d07015001c00e03034206480310010720b07803401d902c0350058003030081007001e24200e003000e01020703400100d11482846441c40d071803045da05000341c9070b52100081754002c1d50000b0f5140f80d075196641d00d846206420035405462034980010840d640744943e0340d1b4169100f04900611b0128100f840340d2110207100320001c00449150000c0541b00c20310503071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 472242302 1250 472241052 472241069
    0xd0f0801050f010503130b09030405120303240a08010f0c020f0a1104050a1b030b090c0906030604020c1e0a11220506150406090306180807030f0309020603070e0109 72
    0x4105544900320842c0e40c111090805580301ea450380e001e45141e074040d041c09003070320241009100344081c0110003001601c0060b2080c05011426581c0301d582d0f8401510091000d0190000c9566114840920b011001d0740c0101030242c01a51928070500b541e08000e0114a806d039500c22058110341c0400c40d0751040714448000d4030102c0403586503581440d400ca06094000e0b6103038400628014005d62002d14412820410510400e0380008014001d140303050400c1d00502012000c14402680c2c81c050318622031004064a21355610101404040d4003c014650564400c44408140040c0020481041d0041e550010b111074500d42c2061080055000340b814012030380c08001c510410810707a0140001c4121800100b1162140c40201c0d5042a8921b01031000000c0414085021070340011030b041120b0080100f80540c8080c2c0b59034291080c0225070040c54100300300082000030340104508662540213090016044507a074020400c554011503200d800070341a04c4c8201403c1d80c005110300042c00046 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 472243552 1250 472242302 472242317
    0x120d0b0415050a1502031314120c1003020f0702100c0b0f06010c08070c0503030a020d0306150c1b0515030a05070c020603010504090213090b0601090803070302150c07050706020d0f 79
    0x3000302e4150140d03406444d1040c011109003c81c8140200203c1e59075a00441d2014400c03540e0301c0c442d0781c81d0544051800c0c07045035488400c0046220004a5984001005280c02c100380032800c0e00350300a501c454000c00c800d00080c441040580e50b4000781000b85400c0c0d44030111809600d00c0d111950700d0f8020f081d04140c0d49402c090020030303603201200701f07201c540c00340440c1c0e51052141488100d402182c0e00903075051200145161702c0030781c0494070101c1c092007600c0030b00c25140c1755504654160600603030107000032192310a910200341c0f40f00020010507203220725480016107903008102c200314800401f00c80044000240021078955224507070b4003900030301d030031840d2aa041d400503200f03100c1885694461900d81c0c105030255030b5100c8408103440d0202004002d00c15141c5021a20f8400403034105000c1a401031002494001c044111042c0a61643c00b901410240b04000188408003800840c1016014491003001407170030081d1501811300368000b45080513003518001c2001161441000400064 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 472244802 1250 472243552 472243559
    0x60f040c09021908060f030a200103050405150403051902011506050310090c03020f0d0906060b0a0909021318050f06010c050319020f06041101140f030f09120d0b0415 73
    0x2080801c1c00d883c1d0040c6440ca40b00d840b010001003e44101d44d403d50340c1401000c0e5208200b00201140441c030926900e0302c0042c5482c0000150101c600484000d44142c001046140000d1010003120354414440d007409801d21440c140101a624021100071000d40e55aa0014803084030241d040030080c0b2880ca401c2d03140d4540001090090005481184840b5440380440b10400c0e000f0380645a00c60003800001d5281c80e801d80445029080800c003d030b41282c0b070b200740031441840d0781f81240c2d1040701540795030704807510b0f0007180c0b4029448004041c0700300e802d03d140410504009012003071444803e14001c40c80b4100144410701004010380105e040c0320054100500248010040d180b038049801916603024600c900240d05004c081c0200c0c80403406048100401c0050801101d1400282a603801011002548403803010348105140300c0d80145040c0005800c800c2c55443d1790b80d210303984100741d030790264203901040b10a8210034100704c03240f901c960130030080d0700b0180301e81c0100c0c1e40d083c10a0040b031440c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 472246052 1250 472244802 472244827
    0xf03040513111c021e1308030405010816030b15180f0a1206020417210315091008100e010b030a0f0201080a0212040c050907230d0905060f040c0902 65
    0x1e94001520001e5426103c1da414150701d50603158640c014018031040002c882c041111268070900940b4034054400d81e000c0b4800070000107403010345006031140c4406844a4114031781e01c03a5001000801c058483c04805440d03242c1c2e51064040c40c4c01c031070140e1745980c0320700d0170600400010b60034180104510000e860056507800b400c00c04451009024256100d10390034484064030a0b604440030400319080c0e841d40d8004002010401e000d001c1884008040380341b404030015220a44402c4400044d4034a401d803180750044c0c5864111502c0c10f060945569a091054140305c2c8101101808039641d01c0840510642030050184007103086001d400703049074694408406001c0030001904001604c4002040c1c0d030180d42c11901c410360340c1c100b1094945414a44014072548a01504d4050325403040815800d600032000440000211010392094100c01e04080a098004a0741008a2510790200c10042002408018001c0a5807540311003140b80c036040003d580c600c00ea0000c02040c0c81000034900da040b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 472247302 1250 472246052 472246057
    0x515030a0323041707030b0c040e0a0209061207022d0703060c05040b0d05100b09030606011b061d06070c2406030203010507030c03050a02040308091306080f0304051311 74
    0x502c52800c00c9003580d03206688026004036044003503160368000b144c1c1e003a01c00000b04d2904a070300c40e40007a160755076240d40b0418640161f00c0303101c0007060b28401007000c40500750040d03d07900c4400b80c8898200007407521070109442c81a6103030005a003010094000107042070f206141080e01e0207504007015000d50403615510003013444050002e80d41c41143d243d5461140d01118010104501d242c0d4441c1400c100000040c0020b607509800841c0c140c00001e52040780030203a41040c4030080203400e140d13807840b006594000441d081303846080081280300e400982d0300c6c454141c1183e0070450803062800c07804092450068054409014440800444e100081c1d1909140800799103440c1c440b11095020b445240140c0741c0394000030750550809003001034031a8541c0c054505d078081d9030f400340301d01c0d19040c80710004c078481c60201421f2a00b041041c1c56107805d0421590004154140c40000c01e0b550340c41900742480b1031100e50700044d03000010b0030050f914011102d02c082c0c0340818820040c4e4a0f40d040002081d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 472248552 1250 472247302 472247327
    0x70309150e1804020307080703051b0f010e121603080301030203010c0809030a0f1209060e0106170c0108040218130b06040605010c1103070305070f0f2c09100f0515030a03 75
    0x140b002500040840d2020701001005040b400c0c01c50b0b80843d00c03458807603200c5d0b0258003104c04410500003029011b03d824095440040740684544824030095010b01c540000c0728400042d05120b0324043c06240300241e01d445c0300070f5010707801c0ca544030750440c810542511158031000381003180c0502030083d406000700403a0041d06150811011781032042070150b550002c1d14582202403840c202c0213800b4003e40341c00555990807003070020000c0c682c80e115094140a512858424140d0180e501303180b0030350051110b03035000341c0018205c9035140c0c5400d8140e20301110455041e100c1c1001031481c03000f04030014400781c1d08098101d07002d02607541000f0008200301c080301c0c00900a070420903a0604036460501102016581100903a03a081792590034906c0d18010501c80c41e519400b0450700051124000d0150f44105c66a0032450540d801c03a140c500710541001030900c80b95070007000302c448039040c824841d2420202c103008d0041060724180309000c0d80300c10050b044038020f400200c09070700000d40c082101d007800d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 472249802 1250 472248552 472248589
    0x4020f12131203050103030f08040309181b05070c0e060303030402061606050f010f06020703150e030409020a0804060501171f0609050408040509010b0c030a0f14070309150e 76
    0x1660307a6080c00da4125901d10300040c0503161410360030b496041d49604500c0c1a079000e03841e111042540d4100441d001c5500b02e0b400381c00a40f205100f48880d0b800800304601c44600014007090b990100304010342503a00710318607900451000650760301000005001c100c0103040305591043c040c9800c3c00880e80b280300013000280b1419001a42c0900c8070920050302850f160002800c0040d031070140305040005d01c081c001c0d0408600f6030400090441c4c4000390500541341d01c00d80c141c2e81805100c801201900000302c0b4040280403d11010400741000c2c400303130000c10216507030412103007001d0400d1802c9a10680026160001d184010f08884030001071241c2845290746c40c2185040c030b0940380300700401c0307103421010440f1700b00020311040c401004003a00c00c3d20750440796031045981c0da4440548902c103001000200781c01c148414801070b40144400c1e0b082c84414284130007503028042542086034000038084000c2074841ca000c1c08000b9506040c505041158208080d90030500d00010300f54078245040d102e003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 472251052 1250 472249802 472249837
    0xa0305030d0b01092c0a021336060e07030c0c030806130e0106030506130201080c03130c12061a0105120a0b09070f2d0c0501061a09030c04020f 63
    0xe81c4d100d524001d0041c0014111030340504014204200200b00011408020511800204841701b00500c02c40c0d10a1031805003d110140c601505015000d4202210001e9040760701551041c99125003211005102d09000001d4020701f4007038540c1c6150805080d090406240041172031485402c0103981c00000e03054104043c0903922600010010020030680350482d909100c2d0907021840705420810649110b40c00317803900c0d9512551400022082894068009005000824075606195008542000c615480300301d5480803a140c000c1032a90591100007c8050840048140051486220000a00c0d40da84288001143d80006c059000c0c040502c4074015018001c5025100e081c0c1c0300140c031a00250052110303280040d800b610f900c410075160408643c0e010314165450101c0c4041000310803400c1200c0c0c009140401c0c0891741050010030440d001c2d035840704080340c00510000c001c81080204982103644010b80420316080c42000b010f110300032030040c007104044c14454000d80d0481881000f0160 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 472252302 1250 472251052 472251071
    0xc040e01060e090a2f0a0e0402120103080c0114040b0603060f04030509130f1803080f060d2015040510020c03072715050f1c030e0d150203150a0305030d 67
    0x104445d8920100809000541150725039110035009070807020b8a5448400c02c0d21140e200b40002d81c0705200016002410f5100144000392598000e41001e400d000000106420001e50246495206035001c0c2e8030a03414200b0040b03941b40c2003000943c8400c1c1c0a80c514503a0409503800307040c034000c1c910420b2098007010006881125207500121014400000501600c03a184020745045c01141d441a00011240c40001745c0a00c000c0211074003900c2c000e4424070414940b40c03103c031009000340700c0c0c980501007480d400384019982d07000c2c1c0240f440d002c50001962545820100710603015070420b80c2c0d05640042e4410001d580e00480c59400300c86c69140c520355103001e1188a06c00ca410000b8821031283c1c03400804000c103804080141c016640140c0f01d501c0c80d01c00881c100564581407211300000c5150030b20045d00060b1180c1c81040301140c0142480c038207081242e807900103500b41c1254815203681c3c0801000a00e10340304000195010701078400f01441c50031500d60584900c40d15071041d48054840c070852 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 472253552 1250 472252302 472252331
    0x20102151f091d0a080304110a031a06031902031c020a1a0402031509061b0912150109060f090c0207050604091a061611030309090c040e01060e090a 65
    0x106141d644400c02880d194a4904641c028203252001101426005003500c2021a000800030100c4c0d1308007400c1403d6903607030390354003400d134030081201a00000722040010005000d015110705014140f4007415145c98032005051030940e0311202054a510581013100140c0c5001c14130080d81b44203603100c10742203410a0400c0e4904011400c000300f940c19004010300c44402009406d60040e403080307041d204101404868820780344416122000c3d41d410080218032009200c407403881c0f9078200049103a0821070302d080042c200c034000c202c0b00031582e0051044100b19030441613015024043c40c0404100c164140b00a0301d80c8007015014101140f607849a07a40e142d14000c00c2500000c0c14014011070b0b8540e103503007000000e040c1d0b01c0268030110f1201c502a505900c4c042054400c0401a9079041c1c0030f600054031021080811007104170b0701404100041000d03070300c03510501440f5058800b400c0d41e036545442b030078101885051703004000308020150f9952040d5901c0e5681e03600050a0100030800400d0314448 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 472254802 1250 472253552 472253581
    0x1051b12040f081308060a020f09040c200102070209091c0c110d0f02010f0e0609010f05070f030918090201020c010305091e211903110706060803030f07020a02010215 73
    0x540001004035189411901e040024400d517030380541620243d445d1500c12400340d0148080005145005001c1d00c030140c2170580c003040f1805214940008901c5040c01c10300c800d001511280e407640d0b50006a80c0065007028407440f9007080a501c0203003136110100e065010103a4141c03004004105030f00240b40240304005c0f014810f02030008010b0b600d01c9400f0f02d005920345c100070710300328041640701603031200a600914017010040c0019004a02c1c14040c1401120010b0400145006000b000c0c0800c101141c00700300741e000210310130f0f19a040b1141c2030606840b440725440000034101805c100c80000144d074041000d148016081c00c02140944554070903038244448050020300b0488146a00301681c1c00015030610002000b5421100c1c18200d0041c00a4a1041070903441e00c240c0c4450260004906c65400f0020242e05458080d040c2000b84d035681c815201d0301c1d031017148142c0c40401845401b81045501980200e0a40010f024441c410703030020351101001444c1521105a1100183d5883d603444075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 472256052 1250 472254802 472254833
    0x4020a03060c05030106031d0c1314191b09140f1e040606021506190503030403030323240105090414100f0f17031c0e01051b1204 57
    0xb48000e18041c0e10052154009100f1000000e003407128807a9212415030100e10381100d40005014200400030502010600c0d881407080c8070b584e81c0c00601c16074040c0c031031850301448070712071032140c600e00c9041000152452005039000845c100303000c1d031680c030360002c00000c111509103030a00f14241c00a00050781e004042501c00350030460078901c40c0441090202840203404040b00e041181d5511a1412a69401071480d25401044544082091440c15031100e54800b12480005c0c241d04e5140d00119055030400d078804c4020a0b1214006c0c0c25181120300751401211144100458a103006542c03949030702410213105190801c2c2c10704124459100380200c6d60100d5004e0300a104139100d1034042052608100c2d520480c01d8064407003c103101c1c52040b12507003140c2202c1a010b41090400d8419059000e500084c190700344010483d65440c0740100c2d211000d080e06145000030405051401242540d4009184141305011046840e00c40354466007515a2200001004d42c1c1a54a6240c141c03890006c0e8403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 472257302 1250 472256052 472256063
    0x19050907270e07060507020603091e0303070305071d100c02090c0705100203070f080703060806070c05010e060108030f07020406030804030524040f060903020c150406020708031c0504020a03 83
    0x1807480603984a00030922111451120041050404000000303440c0c00307060003182d0020b001040404050714000b009507400c00c41810a6801901d440116480b49540f03640c40701c100740d0004005c00c1003080c2c040c03117242d0340f140710340c208103101c0c51103983c00d0030074000365410040c461800d107913080c0d680500c209102400c050b406010110b041c1003440c407140325600044401c40700fa100740000c4190500306802564081c81c0309484010601c01c2882c0c00361610000180500101a560b55000035030450800c441d07409000070352691000c3c0206070401d00e00303481860094031010760050004200e680720000c111b0341c44040e414001e603210110340c80014094845a40040d0203140082400b0041c0b2001049408103112110402e203041e140200c82e800c254402114003800d4400b1102ca0200030860540184030014843e1040d0744078005003000092410206d4061050780c01004035050001030b404000f05000b9000101c01503003000707000d6000c86012140310800d06030a503202d02c003160441d22180c854030301955104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 472258552 1250 472257302 472257329
    0x40b130506090f070915050d1b0e040c0801150302011d03070f0825091512030f02010c02030408071a07050f011e06050f0111160e100e19050907 63
    0x10104560f8907400c8141d41d8103140640440022031580710322540503541d400d010b1500840d45800308104045c2d010304030a44850420580c85401c90300c0b8013560001a1503050401d000070f00b07160901e14000b0201340c0102e07255a14000000c241541034201002c100c0b942460440d494403081500c2461f803000c0302d555150540b040c40404203500044014002c2902c50040c201d815112036115171840d005540c040c01100049034003004d01081c0d111b0742000028940c0c05c40d61056041d03440050f103401c06080c0c401035002840d1108030100c065420b00500103000035910045007032030308242505032900c5092107580c0f034500507a0b4446030701e001c41401323a0f4009a00801038039084041d038088903010f48161811078000c00c03500421340701850b680344201030030341d80046c006000d00400200159003a080e40310044002c1c0c802c2c5880c0e0350300c039050601202d001e0f001c00d103507103c598104890080c81844080e040f00403640c0c0c1c8007040240d540421026600c0746080c3d15000304403a00c2e108640c07401d1110503001000107070081c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 472259802 1250 472258552 472258561
    0xd0f0213080f0d0e0108130602070f0b06030c041a1311190f03022107020703022701091b0f0e060a09080c120705011409030102070c15020d08040b130506 67
    0x401c22042d05810041911034060b00428200d40646400001130b001c5a041800304a103811040484c00c5254440c1400604c0c1c443c49490702542e000915404460048019081080e1420140564154001c0a43d03062000190764101035070068032051401d03008242032007583c640d001c0c1c5038004010440c0001401644c2e140b400603204c40c0386000c0501c8a0104036010043c0102a200744201d8107108503201d010498030f052922250118600513040c10114400c461f8007202507642c00510001030b08414107580d602c62044511000da5840503408140007524200302d80d0804060301c03540c40310304d00f214074055103401804d503001e40303001d040c1d0b02c2e8242e0801d00205d200410540c115186406560341700044540250601c000c105d101150510b40ca800ba0300200070804c0294041c0340c000100c400d084541d5803c000d0000042400c81e04030b032100356034020f01c801e800c0240300a00001c035215103125101400960f98035400c058203202001e0f1000b861200100005031144440c079070070384400d50380541aa0340c00d041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 472261052 1250 472259802 472259819
    0x6020a02090115080c0a050d0c0e04060609030809101202030702010c11061e1915031109010b040501120b040212040c080f101817070c0b040b0d0f0213 66
    0x15204040780500c00040010841411180e12041c500d2040e598540e41c650380c400307044160390003010300f101c1400020301c030f00050041d2601568240d01c145a4643c024a00c0000801c1b050f108a680300c82c0901060500500100340c03004200c1d0707808502a44c0c1d043c0444480301003102c2c80c103503208800c00c149101006120b817169041d0441040442241e81320186120700450b015100c3c8810707100c800c00c4240380e16489100c40c0002020315803008030100141c00b844503007a8403000b40c64901d00301003440c41104000b03101b000075050a0601c03540c3c2c1561261172035814169480f01c58480e60040c50b0611140c002c2091100c00d00303070000340031814003810a5440e482c6907480c41c401c0220680303080318420046c030400300702110005422030020350204000c0c041409080640d400034035607100c1e1070400c0e84140d101d0f00042100f650320740014401ca0b601265585080c0c0c2840141c03915190070000b00700d0000c0000700708a61200e410745415860341500050355a009800310350007803040d54052000d040300c45a00191000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 472262302 1250 472261052 472261063
    0xa060203060301061d0610200a1403070f0308040533010605031005011d0a0303120b0301060f060318140d020f010e0a0b0702070306021204050c030d0203090d08070c0602 74
    0x80003600280000780e180c0035451043d401d54045c0d504450004c000107900c40c41d000701d40303520710030440c2444040c5110032204040c182c543d000e898000c9030301650440c02005030078030343ca00c00511588050b40c00d00d109a80e802481160280e4007504114011010a06001041c040352000744450307601d40403845c90341e41011303100088000aa03d003201503180002201c40c011400c8030300c81d078030210303004a090741000010342c1d8141d214903041c8a208054035007900240c03a4000b9050103180a40c450652608600f002d0800f91030481d20007d00903410f21108010001d0714000442c00c0d55450300303003ca049d5030b14841c20b10004e1888c04024000308140c01c51401112070106841e000c20069509546210240650803802c5c1e41c0034001c0c40226038032014017240440c0d0001d20042d00808507106036880280d89844a02c2a03810400c85138408501e070205100400c5400c204050001d14158060041001d1095019469010b25424980121317801c0321003004000f00c1400300d41c4006d6100d98002071a94071200700942d40ca = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 472263552 1250 472262302 472262311
    0x6130906090b090f101509030204050703051012030804300302040f0e0c04030212031c0b090a0c14090a1205010b01201b0a120f15060503100218030a060203 68
    0x151a1040400d51300b0128640140c450308546081351450ba1a00c80d00c3c50425050980348002c20550300320201c01641e80e401540c0c0190241c2d17030082641e003440c041458020746c50790f020404200c82c20912000003074200a2299210341c00c41040b90f113055090032291036815481c907000d4880c0d4003400380c15003203c4d050f5001d03200b0390318908e0205c078050341c4510301d0119943c815580400218810b110400c01440e01c2c040e064400444241aa424400c030007409101c844094500801c485032103016501d0b85042c08016182d110100300c2052007080f10450340030700b900c0e440d20703c128040000000c411109445081c1407030f00a0108079003280000c0601c0c1840360080103040701c481d001071690342609403078543c00401c0840d000500c201605021040c44a032641d0313003031081845500151194000542160261030708100280280c00c42d903041400c500e0008041d03031243c59810f0010b40303041c0040c440c0b07880c0000c140e0340c011800140140e45074411580070840c4621109019810310982c0114070800070580c0296004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 472264802 1250 472263552 472263559
    0x90e070c0b0709050303120702070302180f0705070b060d020109051201023c09010c060228110c0d021206090a0c060c030f030915180c0905130206130906090b 69
    0x10750322102c00072615040c55200b0568550310512071502940d4021a405800c07a041e801140c02007a07503580410a1007000c13010b4581a4401071081002002c103d003112940041c01d498640d1406e0020380c0d9030405150083c016a014124012591045902801030580541001032070b401e0b14a10000701c2c1e42c01b030740c050442000c0e80390382e400825020b04001081c803480c045040d2141001c10505064214082e00101d1666040220005101021a90710300c000c0c05100c100580241410b041c400b459544007d0510b003100411908907aa0710100c40081195a0401d100704c8480b00020034a0000924145442d2422640343c05820300744a10200d00040c10320001d03108070300c00c200c402e81c1d400e4162803d5040850280c00300e6403074605c2840712846030303010000440c0319841c0c14065000c41c0d10307000100c1d200402102c1e8000320145443c0c00780308501d41c09200510000c00144014a4859100ca86011240790000c0c041c142c08a52000000100c0b1072540c09400e5207401007180342d0340c51421001030807941081602 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 472266052 1250 472264802 472264823
    0x1c02030a17043008181e0108150906010311090402030f07080c120c0a050c070806060f030a050a0210050c010c0c0b160c140304050a0e01090507050424090e070c 70
    0x34030500705903520340d0104a100043e081018035154022241c1c00f01c0b05c0c000c0c218500480000f601c0c1c4e03603248540300d2180b4041d05d5000b24854040054080900500320b10b00642450410300d12580d0380e102d02603840f03a400c2c0380c081750f03d241f24400c6004034015403203041e03403160003c0200b024020f40103910034801c01c0c203592220016220380d00c411050707118030114200880001c00008502075601e800401c4145840c3c5005440c0c03801c00d40a107130030076a0304c0c1c1000107070743c001d003081c808645080f45000e94001c0046019141201c0d031740d51070079074468406030020f000c0d1034000907091940740a10282e03403a03000720318001d02c488025031038002c0c040741520b10212030703004c170365008554100740301c10b450310001d000358032410703000c1040d0f4503083c810007146140030046200400000c12191600702141c4010541c0d005010284e5040c40110015220300170030340e4041042c2403108104801c0c605800c8c801001070405480441e0168100880303141509400000c036520701041403100555204d004414000c1c003d49000701c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 472267302 1250 472266052 472266089
    0x70b0f04020906101e0c060203150a05040c0c020420030f0a0507030b1e060d02220801021c090c050d050c0f04061511030c0703050d030b030a021c02030a1704 69
    0xa500710b50707442d1034000454104242c201707042082401d40406005040c50001c0b070348180e98000a0340d00c01c07592407941c01c81b40f18265017a4100f082202019200440f01445209010400100360381c5c00034002a00c165150a11800700501110300158011405011315a891400107400005400d095405464413480c02001071881482482900380418009012151305141c0b10b80808503110070b80c409590115040204c2110391501c0d00c01030000c4040c95030320700c3d400440000d25850000c1e060b8402d6000303900403c01038010040b03e02500c1c0c0e030071000010010381c03d41e05051008441045400068004c01d8040d4814240311002841901c0c454040300c0b02004160400144803e482c0c05101c0e0728417801c071907040040068054456441d2a50341ca4046a003002c0d81100e911389800c2c802e41c42a41e054200a20742c0703030f03100d40c980241050080180c0c020040041079a0108403820b05002e41d510340340301041e90100c01c55505100c80300803140c0101d1000525000920306102c01d50041c420135550344100741c1d481 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 472268552 1250 472267302 472267309
    0x2708090f06120f06190303030209150a02010c08010e012d0302090c042606160c050a03172211040f1410050406052b080409060906060503040c0614070b0f04020906 71
    0x82d0071017034031450761124585035560560280d0821301ea580e521401c2d82c0e4030307080c0602e015000352460842030341c0041006040341401500e00c14041e0040c81c40046c1c500300502001000300c103007400c042000c10903140010310019681c1025143c58200030f40c0001c5000a00c6004105080580700380c400c01c0060f801c680507084c03c49151212940383c28451900304000040501c0c001d400c2c00602d40b111410704003c202000d0b03580c107080c0200200700b1004159030070342030741548000d03001040d8840d64058126404190000ca00ca22001801000912100c50002c50340440e88580c0c1001840c500c102c08244140c042d05c5140b15502c000c11980c0c07058911400e0303000242498140502d0085880240c283c0005005a0000040e00e6841481c0500340c81400e41081c4001804580107000510f0703000d00018005040c6100c00c000d640b4079500ca00e00f0072800f4003e100c04122406c000c0c400f00c4110b81002d5212140f0307a07031000c0303007070240c040041d0640603000b0400c100415101c2c0018451807084036101a075541c3c44080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 472269802 1250 472268552 472268569
    0x403060f23040201201504030e01020d140a0314070306140303070c0902070609150e0c1828090c03050120040b0a050904180203012708090f06120f06 65
    0x42200002020106025500404200074028183c01250446421703e41c226480d00d001d5901007004102e0300703802c10041c03591001d4000d2403180248058540d124042000a010003100b44814480c0500081c82c41241c40c000e40c08099003000075250169507152414014009180b40e100781c4031601440290601240380108c116004158021307000041c0c9400d00040350000e400c0000212030392a07940f8460f4000c5460504101c01842d810300c00481c490310f2038640c4030b04107054960541c3c001d0041428800503604550615a401181c0d2403201c1c420210a140d039280c2244020305414000d8a05014142809001109041a83c1c0258024060059500e00100613002c1c4e000310305842c00301c140014045294070400030314002c012440c0c0f103410701404000080c2151040c00c00c00794800172a807441400c605003070180e4be4140e8200010300d118000e5819000e4414208041c00400007103001130714405643d03030796620145002c00030381548c0d11910605080000380d402a01c600c810b0b0202c0000088541c0390802d403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 472271052 1250 472269802 472269851
    0xe0a030f0c0b0a21180c06090504020f1606140c0d05091902010f02010e01050a06080c0d03050315010c0b040f0308010e060d020405060136082a03070b0403060f 70
    0xc0e400301c5000c4410040248060814006607110384407200c0ba01c243c617414540049103405a01e00012040ca040005000180c0b580c1c003680c0662f0062150341364a0007540c0c1529904903007800091420b001d1450440000e006054800f01400119000d120703d40030408040c00180c58036000c104219121401c819a43e2982c140040104d1541c05242c03c00551159007604c04001da503000200b440c0400c0035a4509449040f40c04101c91640d0b14000c00003d81c08108821b480b01c02130f40c0010f5400a44d0302e0051551000414040c0700801c07100e060402648520204000245c05c5040728413071b41090318003c0094100300d08254001184c2d0340c008a80c0d05100c1c50a07038081c00340145280403a1095a0031320016003402016241401031030881c585044140803265195000c100034001e19a043c800c0b61402001201d8100344495840100000e10b0404e0b180d60413a2118925040e8040c0301c1062030000345042e5158210645071070010400000300b014a0700101c000269210090000800c8903407140da018a4590 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 472272302 1250 472271052 472271057
    0x180306060801140412050c03040e01080c0a090b0a030311120309030c071e0501080a06080307030c021e011d0a050303070c0807060c020108070e010207050d080c0c011103190e0a030f0c0b0a 82
    0x80600e61454040c0c00101f005040d0395041e682042c1c0c0d600e82000c0300340e00c00d038004902e030741010490a401d4600b240300071024101300182000019591404a40420300e140001000e01200d90100361005a04102c075000500d24101036984d039141107068035890340c0084100c10114032410001040f081c0412000781c0e4004800f1004c06181480c00004580c98140038140c5c464075a41d802001c0b80880e428401011618001d845a8441619501c1400105016004103242c102060803074412141e07401083c00700706d03000d461071a400d0f440d030f20380000d000500b03503610803035161100140003002c000f0b2500301041114825016200f00c140c0ea008251450065004003d0010741180d0003e40d0780d900032911001c1030308061040b180c556440d00041070b04200d12900075101040003049080b981c410400010380166420301c3c20b0103014841e0090b565a0f405413808202110222410052610784208000e101c0c0400c02044460340030768904183c0d42c142d01011082c1c400c0000000007040110111084861041c01907 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 472273552 1250 472272302 472272323
    0x30809040e0601051f0318031701090b060a180b03071106160519090b030a0204090b1c080a030f1805010e1c030b010908030414280302040b011803060608011404 70
    0x60300c040d404d0030805e407400300034981c2d20201003140c1400c070043c1e0101e051081e110b05c105201c0c080c18651440005921071095981400035101d05521041d040d2a48901ea9040c0b01040801c42c040c02c0d030f5140700c2904038141c1c21201104001e0328130f44c0070100c0503500089409070f41c0140c41c2d00814500030480241c9903800315404010501c001c1040c221600c0e4000100c0c0340055005890f646a00310079801a01c64044540c0c007c1001d002c042c101e445201c402d01411669039030a4050220030784490f20030340101030801c4002150240301c490280d0020010030030000000c0140c0044907401c0c1070700f8071404000340d6845d0301c0c2081c14000c13081e0019410040701c2280c40491034070042800b080b4058420982c550741005010303034001074007503400c00180003c0c012410000758100c200c8010300c61002181c844c800d00010000b072003d0b403c10440d206030801d880d015200030400d00b14400c01a01c0c407800309030000c206c20043c607a0000910003598001d5050300d00c001e000788103002d0b8800c0b00c0001002c0130383e000f500240b442d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 472274802 1250 472273552 472273579
    0x91507030e09061c050102090a080105161115040c0f080c013e0a02010f0c0b0403051b0312090d0309020f090406110a021c03021815090307030809040e060105 69
    0x42c240c06a40000004c04034803441c0100e511108003407a410780101c81030303074000c103618500b80f4102d41034001400c9a100200701615000344800142d21807034440009011800705211034a040074001d124502d000283c0e2498241854503040c0400d07055446003601c6001390b047c0c00b0450f00e601161200011005070341e5021b510044818040c1840700c0c01c1004512145c02e02c551008840c03d8603051440301000300f01416184900c2e00015180d418004900030800820b1038104000031a400a841d4105070189003058945504908603c00340c01501490075161001040808240302c2c04540140b00d01ca001040d075000c201900300542c1039800c850300c0254440804066403180c1e0034641035a551043c0100c5021401c009441a022419805a0364000041e0030040721044990108100d0050040341c0c0d1030110724054a17541186000c000d55155a40724224541d80351400b5620340050f01e540e60001400d803038010790b4030319101e10907501404a1a00540c146140d0700c2081d50089000c0303049800282812910218 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 472276052 1250 472274802 472274809
    0x50d1403090307030e030f01140f15090f0901090b0103080a090f080c0f031e03030121230c031002040f12020102030406050a1707050406030e010c0f0e121002091507030e 74
    0x1d80c2d05d030103415101c2d0f20900140e800302401152507444001d45640310758102000706807500035004154100085d560742842e00340b0f45801d010950b01050105442405845905510b4003421000c00c020b401c40c030390300c000031033440003007030092010040d51748401d01216990700c0c511050700c1040c800c402140d0441d01c42c0c440c65040c910f107400e14210005061740c00c44544501090584111128043c00f42c6d130000c0700600849907400725044842c0c07101044101c2c0b4031840da4401d01c9080d1100c41c2540c00715110030040b100c411301041810540100142550111150101144021f400031b1040502203001c00500088088030b10a14400054040e8082c510305810701c01705440d19842080038804211a50202c501018410002503000fa5940d540d69039582d8540f02c0001e0503145682804072851f45042455001c1503000990144051500d040049401c90107200141e40020000400759132030040100034001c4042e81d60040040c810111601c0d14291400c5d9072008042c00307803810003804114410807070784040c070f0f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 472277302 1250 472276052 472276067
    0x80306010219210207050909030a1107241e030b0a12050d08060303040b0a120c031a040506060f070b0103141c0503041104150f1d0f061903050d140309030703 69
    0x1c40c02c4c0110350205680d88080755507240226505c40d0f06070030104461981503405034010341409103c600400c01542403040c090005e07c40540c54400804409400f011000c0c040c040701e080084148880a9000180d0b130740c080c0142c110146824030401450f1808111021041c00380c00046400500515044003082826159042c0c00f038000c2ea4940310500c000a5914025801082040c0059507035600e0000c0c529282426140d018400703006060800c0e00c180900251400d51061040341120b0209040d207811006ca010b86c469070002041e01d2800140c0d101c1030003002c401701ca040f40e2042e21810018840900300c1600c1308480c041c404418581a41e01e105803038440d00c059504a8003d91700c0c0d614030394681c8009811200105030980304081d8004082040600c14041003009100c0c7c1c0c10100418140b9006402906800408424813070b00c0b42c4000c62440c0d11181498000c89210400702001507499080031a91410110101070000b01d004aa4107000c5c0d00a40a0702d0044051100860402d1070955043e10800d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 472278552 1250 472277302 472277363
    0x20325050c0a12050d030c1d1903081b150106030e0316030e0a06050903030901051312080714010213060c0f0605010f0611070509070c060e0604080306010219 69
    0x248510806008940e4403000b0400c02000c0000061419946604e000d0741844480e064005c02e061414005814071900104a4140040c0d0000b05048010201d400035040041e0700601301c0212509920100812036000014051840c049507032132035142d403041c1d0403540c40400c01c0b207000101c0104c1d00104400c0e8001d82240040300b031004280c9007014186180d0251130307412104107070005070b10600449028100003444e0001b900c0390307203802e6150800c00000b00b556803107250310a6040140c00a40ea40b941c5403284421805050040d46541411440b800c04107480d4119850a844003001182c050107076038070500c22195601074561160680918106c8140c59903c102241903030035018621400700040e600c0e1107054040d0040108681c601820007a00511301c0d0b02e194000f0340a60301c504410301c042d50704c081500d070b8040c8007032a101c001d290480c50218050071008031070407100c0c804c11043c00104030a2802443c4258001e034200d440301d08181895840c4581103440c080d10003002e90105d6620701e40c00000c00c0048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 472279802 1250 472278552 472278563
    0xc19020f01090b0406150602060114010905030f010b090a0212011202060d060e1009060825080a0c030201080f130204110c060408040e1b03010b131e0510020325 70
    0x8110040320801d0941d60380d40b800b1250204840e00304010450a445140d01544a040b285c1140d07506201c4060f5440e5410f015003028561201c00b1511168810071b4500040c1c000541580c58042501740102c0c040c044642c1c10b180301c3d03404c00002900700303003891081d00c03110150300400b22030b039907e8680d1110035003c00b51416600700c0c004110030107031229030f401000002d00d00d040c1d6440c41868407580d50001c04c10140c002075103850400c00100200000040c0040700c07403407007000400080c0f0354100368003a080400d0340081654083ca4298100340314002c180201107174000c0e25014040e40e41d81d41443c0c158803045500071b0403240c4030b407000c90241c1000da00c003d107110850045035142c01e46035590740d842c0400880301101c2c0d0010028051242481d0725241d56005511440b00c03584134484000700e074806000501842074100303c04a0780400155285d40f655006041134040c3e11040c0407681036140700c048090080a0060440b0302820440520010480c2c00102010050800d80001264104088020070105032107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 472281052 1250 472279802 472279813
    0xb010c060510080c2e17010305010b130e0a0308071803050f011b0219080403170310050613050d0c080319110c0a06080415020a170109050c1902 63
    0xa2180c81070324042c403a6110081551850b02d1901c41c6440303070880300c01e4040c2031050b41c0142803607015092101e80544004000300f000ca00c034802200c0380340b003a942c09480d42880360000805d000c81988400f0045c0070035100410000070003000350b0265502c898050780280c0c49803281030b02103032244080380c0c1c00003400d1070701c03011320601d074248c0b141809a203400999040c0c200d02c1c9051003103502446101495000d200c040254400300b01d6000c1c0d103a06040c00e80000f6504100c092504000c00982264061a84451035040f460140d00c591405900704541c0c1c88020b403080c9078042001e1402c0c405544582c81100d6849002c03504000c14069802c0001c50b0442d01d02030300c0e1030007041c00310701440901400c4400c07610313041d4840600c6000030000b07640c444c100c40305604a0403405855440c0c0680348405d81e107c906160030310381c540d89032581c001c0381078541281135140b010600c01c94550340450240394014940d0303484001642c0300d020407000c96005440300030001c0f10400c04180317004001544034800c254117006564 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 472282302 1250 472281052 472281077
    0xa0506130c110709060518131a070e011128020d12090b04081005150a2411030702011107030b1504062102240c0102070b070c0f060b01 59
    0x102620841e64155001c03031003461008500d081c0400c090300c010006510113020381d5241501040d14461f800080340640100c01c00090400050440001040c40d441a07aa40e4a41d03940504010440016661a00011070348a8100704039031040682340d00307241101c0003a010340036215a001c0a03000021403480074040602000c0c8016031b440c1c00035458040d01500d0303500300d554250003000341200442d0b000b04041003800c0c802840440e40008440c4541d451100c1c001582d80c40c2c0700c1d11803400700d0002034950350103041e8000101d440007401a442d41802071141c51408607414200043d41d07a41d948040d503100c00d5009002040c00f56201e120840c8039500d401c0c0541d01031795102c0d01d54015811044401e00a014001c20740f100c16418984600700c01000d01c10001c0041542881d858456042d00c0003019200c1e6100c8108040140818450f020381c1c024016170307666450f1074103040b803030203500440340c107840c00003081e80042c040c9801629000401607221a0a2001c070700280d441c00010400340f8501c0781000004078959 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 472283552 1250 472282302 472282339
    0x303140f0f0726011406070308040807020406090c030c02010e030a0815190806091009020f040f020f1b010b030c0123040e0a14070212090d050c041103041b05090a0506 73
    0x14420f0106800964119814460b01c2007519078071520307060003204100004001300e0360102119401561202c0001d694020900000700074180d16041030030110b181c62550029690181c0c00308140b595030f50001d0094650320640c4548034050f94400340007103030068001030b801140d40034004c4954400100700030a50b2190807070041800f0119003118441c3d5010b04d09102203074000308a54030508441d0041031041200c0381e8081103d04020704651405079448a4404422110b150141ca220340c040010140c0c6507200076040689540e01d80c03810b440703554a0956400e030301e41004110f0424500f0180c591040358021842294202d0119080c552140e050500001c42d0040380200c810740a082d900d840401e81c6000c0d4100411202c0014202d14199800905082440c822403802e441241c4811501118540c040b402d1180c01e001c02e5a900359842440e240d84003403109004c0010318003450050a08081d03150040114418404540c001c1650010549000401d00480345e048140d2040001e8866000d002c500d9011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 472284802 1250 472283552 472283597
    0x1b1201020a09080c0303040303090e100b0307030603060f0b030d050c03042123100f2c12090603150d0b041412030c0f091801120303140f0f07 62
    0x848000882e03240c020889000b040101c03078101602100a10301c1c2a1441c0d402500b984182d1140c0e40e4007280040c0000c0b0480e500c0d614000c010580c61404070350b28581018010300525040c081112141d1800c10300c140c0da49134900c03658003411000340051603d590703011300688994200c3d860b02420f6101c10000031075613182240b0b4240510809030382141444c4103601d480c0f1915039400071642c044c029030306503002008038002448050442078810000f2141e4503230448202070710f00140c180044071612600003401e01d02c80c6002e81c0386401000203030345000500d00200c0b0341e07511a4404482e0700c21418400300e82407042d408074413040c4190082011884c400660b96000040380120740503502d00e10b401040d071040c98402c0c42601c803600c4042034181d1031858600802c006074060844034080940f1702281c86803040c1c59020b0304880301035004070421801d6039120320811584121610882c0041d041505182c0d803010030586841c0a0300221702503c05d1030352104615a14218018540c2041101501c80600f100e07040618 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 472286052 1250 472284802 472284817
    0x613020a08010518060d080c0102220510080103051506120a03031a0f0105041211062d0301051c0c1a0403060506010903050a06020903010914010c17091b120102 70
    0x861415540c5020100504c40b00001c14844e144404202001102c2c1d446040149545612002c0fa980710707824000054020300503940400c1d180b8a0030341c8040340001c9180d0505e0f045444c129003142242c0c0f03102d10f080700c10030310a100091050380b1440e000082d507544400443c2d807101001d481039420ba41c0c03100715680384c44580c00d030550110785c0c0c81c0c040340740b504408404c0340c80465098030f0f20034482a4840001b4042d104600c1003428584135280801c0070002c0e00741d00c0e0f42c410308008108076201c1211038200302d900300c90707103940e0048042d1101d81c000d00c409246c1c040c0c1e1304807000103011071180459070704032001242e94043d080320300c420358180c08603640c0c00040940400c40090f182461b01c0301d00710b18000c021200c0107448941440a6490b04000241c0c000411030740040d40060017607140c4640b4000309000d0000640c00030700d100c4170300c8200d034030700d513015031000e1600201c076514407040e03d08000506014a10503102d1560507000f1210402c01109010541c0d01400009040c81845000c611a481d08a1f0041079 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 472287302 1250 472286052 472286057
    0x20d020d0203010b0a030605030f0d030b0d0c0f08060a05010f121401060605070605340905100809160812070807020613081c020c120a0b0106030b0a06170c030613020a 73
    0x50720345c444c03980c580305c3c0d500900342c00e0300103101d0480000006507440d032041d010ac808060f15607400e191252582c501000b0944d0b444010151144e0302c40860001d00520307030162a049216280005004241d01d004990403070346c6c2c1509483e40241805210a103000000d001981d101082d1a40308ac2042000d1060704003c02071350380c40c551161a5440d00c28141c0740c0c0941511200a002d0301081c0c003000c004280045850901051411581101e0f5416a42c1d01500d41c845c80d8000025417649401c0354020b02c10074440c05c0503c080d5001812412920b03c4140224014440c16034030449d0341d61184a80c040081003890b004250305400d02c1201e50004840d80d0000d0031283d000da5864004200d007050030001c110044a14252080b207012004200a5a50300d1001c05d640c481d0707103510034481320381c002400b4032485140c0005040e0b0301581c542d0380c0580139094640c0090b000e8031000e00c0001e02d942c403d26000c003002100c41074008858507001456401508007409035544010700f0700c4c08886401c140c6c40203180001003034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 472288552 1250 472287302 472287307
    0xc02130e06091f150b070c0e0702030d0506030d080a0e010204051201020d14010b030619030503160308010501141905040f120203011d031e0d020d060e060103021c020d020d0203010b 79
    0x40465420100d40301c8203803c00113080c280b80ca860070841c00c0c01030382990302d2651003580301c610302d09000d00b95042c030ba40300c5660902004144900300e64040014000c8503100f00c000d00c4640c071910309141e90751096410a1740000c00b0000864100803083e0482181451008005800c0076111070004014a000d101800074980d4001a02d82500343c3c1405201900c1050000701c1890758036210541c40d1b584070040005104a100c01d60618139820110f49442c041c64216048a03101c1c82d46540320240303941c1c5498290049401d44000040a61207984042c0c16820030300c02c010300308941c602e012240703907034007145078402c5c803200b4003020845103a1009481c000306030450743c0841c0210b840c01494211a184010b04241151849120503056070020890301070300014500034041c8440a082403026000d042400d0195900000d05180d1005c0c85805c0b46094405807940c07508682c94000040d0201d106000b10419840d81d20030031020250890b902070822040d0a03207000d0302d007200340244101242d02c2608449c45100c0b02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 472289802 1250 472288552 472288573
    0x201301d0f07030b07031b0f12050106080a0515030c01080901061a0318030f0703390b0604050f1f0306020706050a1506051914070b010305061302010c02130e0609 71
    0x40c1d812240c010704603040c00c001c0f201a40c07c11410711200300103034800f070083c00b00c1c030445914400c0f15004030814001500b0045035854070b400400400d400c1d20702000745801c0501041c21800c0301c003844041584020004c00032303101c00800541c1c030000b0040c03070107240703550707440340000c1640091410181161010001da6a0780c644100c0003104d46003c6644114154810700100080c030320071904482c401601820001e040142007c40b042c51741d40180d1103102284080c081c0300042d0483c00d030120222a100c0c100c041c0340c60340e440c07003844100c400440b0310038005003040c804580c08090b181d641407440356258000e0f2150300d469840f0141680c3c0951003c9615030b544800700054525184644500b032906220308000d490b1400300000e04501900411031045180d803001d06003140d020b062a85c290b1102200401d48a201d03d040c084100344027403000303480314080c1100013050380e441c41180c81c050341e50507102d0703c010380e101d5002d114036030700d1032000180343c2603683c024041d040340c0c02c00171107104140d081c00805100c2c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 472291052 1250 472289802 472289813
    0x10908070203210d020708090316170a020a030b0705070b040b0f09061603020a05090a0815060109151407020306130323030114060f0a0503040201301d0f0703 69
    0x150040c1112603842c0158943e500200c982044608200701104003507110182418054950b1141405a44d8988260340c0c0e10303003000044640140840c1c0d41c803808011504454400320385c4a1000110081d84102440f4003403002803060520503812500d24500380741000c0007680c0350203013450300340c0e002e6070b040c44034804100c445c0350b43d4070b80e241c1e014000e40d0280000d810101c01501d0310800c00503502080c5900450b092008600c2003096402c039180c010074103818150f41d03550154a03130007540181150101c100000038040e50040400030704a030f103203003003c2428402203602160300080c03a201180d0440381c01c100440c00342e6410002c560141d1800b51060620403980d1a020b4600c080d12070041491a18001c666100a040d03101601c4c1124000325001c10b40305001d030001409803041036445001070001095082e0001c3e440b00c05180300305d101ba2034010040b00c050103502e036441041d484620020135425111081014070760445100130081d24000b1a82021450741c2e141403c8800c03010012a6129040c100107000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 472292302 1250 472291052 472291063
    0x20124080d17060f0102120d050103060b04060b0703030e1f05070e0f010e0d0c030b091c051c020d090c230a0e0f040503070503040e01090c140313080c010908070203 72
    0x50142020407040500302c44007015104014400c902c501030b01c10460010744d0080c0078411100c0d001411140e030f43d03c44054014020f04007800141c0300285442c5500300641001c1c4240b0b0143c2e410703095400e05180c80c0b55402c4010b4480384150b41418090144d181403001c88281d050f000e1051403a4020a05141c468401042110380d000c8880c400c1e2100d18080040340d8108104a0340c201041d5640d013003c1c41740d4140351500c5285680010580011882040841800841c00d199620340c4500c081c501d1892250b01225140030310402c0010884100343d40c02c0a0b107503107034001d0884070404040856600c900342c0311500307449010343c4400c10481000b40d103d1440d2040b2810069407010489041d208142403680d41500484010003500c01007401307030086014001c0400945401075807003021031755141e444680b000745455003845051030980c2420f03e4521003902440852011f0303030070381464504503a190b181d00d6220740302034030050381c03020010085212034540a00681d10000d0186412560300c20840c8103051401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 472293552 1250 472292302 472292323
    0x8130b070b0a090804051302070807140607020c030304091805010e0304181a01052101030c0501140a080c03060a0308040306150e07090e060109051905011e0806060a02012408 76
    0x1640362980f56030026400809460070380c0c40940700740170707012072000e1030600130300c1101d2028061240c0807541c101000880034154035440800340a40711607440e00401a0ba448643c2e601c0382d03915401c240700c24042c6204640c405000038054842c20450150542c840c1802c6403940340c03124403d908009800c0c020928800c68181d014411114200110324404800c2500a100d030a0311904200380010340204c0d29a05401c4000c40c807030f100528200659682c43c00183c2c0020394070074a800324004240e80c06c0005e8441d400c2d90400b116a84907080340741c1c0c84590710005580000d110503401002c040c0007001140f8108060009140320b4000060358200d0002d0281c1d8070030890348004441203400d010442840d510031524000c6443d00c4020b00d41c561181c8005817688500c0390419a00300084150313450307004620318400030807100d082e283ca160905030031013070380350004607948c00b5000303c1c580c0c8010503013504000b4010030f88901113100005104140d0741e80408802031604500701c403900c4819060200324024007218a80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 472294802 1250 472293552 472293571
    0x1a0315070e010e3a020d120504050a300503090108270303270d08060d0204140403120213031103160b0a0224040b1503191a07020307020d08130b070b 65
    0x101006540058640801000c0007070047d42c02200c000000b0b4024000e58002d050024949000700340c89640720010030001080e055801c100c1401c036440d40c22504a035900c00c0075048400b03103107030030041801501c040c031010340100d00f00091183d0360250b4107080f1425803443d441e0800a15038a00300024905103200c031028440c24404082c41c2d225440400000308048c0c29041410301b14020398030700e000500444002d24000c0d40190405021040701010101c540d4860f0b4403a4071070800884018079808100d0082840c01da08202504106002064101010380d490000c0207080320950440d207869091551010741c00104080707808500055015010300241c00340660f0b82108096110928648019502000d08082c110805810200300c1d1342c4900b8a840601c4903001e012141c01070506805000841284401650240d0300c2080d070704d2035182c4200000307004e52010b90082d41000c0c41a02001600c48598400b1a00e804003008150189500303903900300e006001c41c106107030319081c085c1090710030024028130b071480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 472296052 1250 472294802 472294909
    0x302040305010e060f180f0102280c0b070e1c0b0f01061d0f031c050a030b09040b0105040e1908030f1503062e091a0315070e010e 57
    0x1502d8142025190f0f000090310010f40d00d4480c0c0e15001400c0110f1f4001905265000003805500b000e0303085621840c00355400d4096002d51860303a012a8075051a80b401400640b15070041401540318204031405814014900080034445800907540c0c08009101141d04042d82d00800000d10311001a581c0100410304000040c0d00b04031034a45100da00c4240306a1040d407102402d000103440400c12890000b4640e4451182d00341c292401034a01d8201d203071400c0c002030030148411290b0030700e6404640103903406409401580d0070035003003102030103400d8602c8000e44a00300c0c002286e40f58052a05c09610701540f401da6503400c0940c07240c03e00e480000d244a5070041d01580540158030300180403544001d04002e01d100904010f0f804a011001c44c0740711160450900c400072030201c0484d445540e07210071034403281003011020418151104800100040b0706404240007801450003880c401000003c140b414812052022000076960711a162001540b2903081c0c959400000b1049542501480481e19490 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 472297302 1250 472296052 472296061
    0x60911090907030b1306020a1107081902040209180f0906130f0210050d060602060a0c03060506070803090102120106020c091b040639050c1e210d0302040305010e06 72
    0x642c0d0b181240700042110004030000f5040d4069214800380e95a80000195510036441b10010100034254061032950b00a904002131010350000d02031345441803922050316000c020b40c0801009420082c0845d808c01c04800262078004002400181328400d03a143d5480903050dc00f845920300100204082036040300090300300c011561b0104e404c03144590407618070900e1042c0c1c02003180c035405102a05048241490804100b468002c20410b100340c403445020803814a50900880541c0c81c1c6105071500080c081081001040c8040c0055500901a20001d40341000e02162440101001d82c000740c01078120320702400c06882c02c186025080b84a034804401c054100490034100351103903110700c0c030510080aa4411140050314800c10501c0300c50100c140036110fa00190342c108050182c81110140244250741e0340a140c010b03050070f000840c0c020344104c03510f1190140040d103420100342c19109050300326000c1c8040e004112040e07035411280e41c0175031554514900300d801d5811340c8016109a400000410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 472298552 1250 472297302 472297321
    0xc03050f01030807050c03073309051003060f0b03070e0d0c060f020705030601031218060806150909010306150f05100e0d0f050a0308060d12050f090d06091109 70
    0x39030650b80c02000d407039a125668030307243d880c180030504015010b0061407400a40d0091082d43c0c8201646608104024001030500c000e00c501c090104442c04518959424003490401800381c182056480c1800a240e80c1c461090031464003035588020659100001080385c181d52191989503040000d4602c58000e1400c4d0781c0d141c1c034840860081c41c0c01c0204039914140b40034800c00000f0018000034007503403181d503101c3c10b04a00a410455911010800350818422600141c03400c80080711a140c0c0c6102040e00e0f21810000e0442e44c06404942600b81403040400075600c0c40011402540b00d074100091544103e4800301040f4501d600004400030400d0040140d0380351007100401101051a01c2e00d10840300710001103000c000810045c0020b5203800c3c10008001c00010004201d1740a0385401c00d96550300000c010000c2c4919800920a000316011131120300d02650291200e0050442464184145031020440c1d0131460502500c80a854840c2417080c00300b0220f007000d10f1403040d50018420724040514 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 472299802 1250 472298552 472298581
    0x614150d03120b010309060623010906210e01020a0207050a050a06020c09060402040e0c2104020d061e0e030d1104031e020a090e0d17060307031509050307150c0305 72
    0x1203812883d200c00070b07410b840c0c0c425400840b9503980300104000e8aa150103010030580c2c0141551300345100c05118040c010b41c01003031040211030056072100c200041e00c1c0181075440b50b25165480303039292640c42d07007000c1c00c0c400e0018080310b40c00e0350300612b2501c3c0340c9401c103c14a14654007050003443c001e02c0610815074080361001a510003640c038141d49403a40f4001c500203118951000e10505d60383d80c2030100d040c102c0c00c001c00a0b00020007055015200c201c0203a0b00201c000d4800039840420545c50b000001e40a8002008680001d0500700c0c000c03402d907503185c0c1541d43d0700f47d1a0081c1d07000003e00440a18581c810400c0540041702800e050500b1640c0b450900c505800e110346020102401e400115a501da00000103480c091400380074a44400e40c0c4580c0d1540d8010541d004034081c51340a01614040b21901e520400e0010300a0111034699260418100b080312400b0014607192510013001c2041003006000cc94401e0700d80340e00380070225a9190841340740014520426081109003da50141140c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 472301052 1250 472299802 472299827
    0xf04080f2817010603331205061b030c040608190608030d0e0712031815031e0e03030a020702031207080403050706050c0304030b090a0b09010e010c0216150c0614150d03 74
    0x203980801c0f4206c04805030000c0c10760003040105500120442080700102c2c0d01c0780076004000c0c1d044244c40c03046034002040d002c12100440001801c2c041044642d02c111b140b250030454964248031000b500302e207008152801e0383c1220321160310010fa9105885100e21950740442a201d010308101ca0401400005423028400081c0401c450010b920341c0700e50684440c403000b03060068062000058081025012380900c040301054480e44041c03a2100551030b019107002e000c1180e000e0342c61581d80c03107004002504003050598041c030603680c404501802080007000d40030301070048261074518500d4442c2c40c028081d0000e8040100074000ea1140a80c0001507505070f030b620003540e0f4110307540d0149242c035001d10b0410182c0100e1070403003804006607040d4410b40808118000030700c0b00070440d10341a41d80306050900100e507030200c0001081000c50540c1100503040c3c0e28585103224040765195901510740c5031030085824607004040c45110040900311321041001510041000b0300551405001c50300e5481 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 472302158 1106 472301052 472301111
    0x12031008010e010f0c03151e0e150918070504020f12070e030c01030b01200c060307050d0b0901060c061a030f0601030b0f04080f2817010603 62
    0x47c41030000006426100480c03401003947c0e8104000440791600e14514200450300c2c8401e42055030180c100c03548071040e1040e400082280501000d80350b1810a8400d606292184401046280480d80c08680040e21004d462804108500c2045002c0c40104176180801401d16040f0604054140c0c05030100c9065010400c015011180ca04840e14040381c01c0341c41102894480425803400b440c034503410340c3c119242100106809030010b8580401188000c104100403203540c0c4200c41c1e1424040355072865651528101138000342c80c0100181840c1d8480b82c1d034a40c10729840d40302581c10b00c0043c0c2201c520070040b0030100d13201e020a000445051000c100030a0f20703025072240d681e00494000c10214a80b1945121403025030b0f04c0441030801d00206145c0707603406800d00d07441129500d00c04e03807650410b5a98414130001510b005801078000c0c14607051360074100800c10102e8511307800402 = true := by decide +kernel

theorem cover : BRFrame.Cov 472122302 472302158 := by
  have h0 := BRFrame.cov_init 472122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 472122302 ≤ n) (h2 : n < 472302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
