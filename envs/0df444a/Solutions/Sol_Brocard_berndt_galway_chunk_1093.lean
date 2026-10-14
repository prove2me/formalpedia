-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1093
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:12:35.633909+00:00
-- url     : https://prove2.me/submissions/1c4736bd-8eb2-4e9f-8208-3614c49ce6ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 196402877 ≤ n < 196582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 196404127 1250 196402877 196402879
    0x4031505010f03140309090a09020909120f0915040b03041e0c0e04060605060f041406030c070b070e0409060b10090303021b0a091b02060709030b15130c02060601030b030c 75
    0x12802d800c1d41c5800c00b8500400c1849101884200250b540c0c1d9110418542c1c0b1580103e500058441e013580140600a00018103100d100e4205014003070990700e40d40b00f0740c0c0c441c000c0105d0040c3c40b00341c20303004075811030482d0160741c15505001c01c0c0091468952802035200e244a91101d100080716920004032490150380018a0707908020710907c81c01c4144061264498050a80440c0c0d2940d640d0200e0700c0e6034454400b07000700901c002030500c81d480000d0048400d141060b15404d15600e010741c80c00c00385016111000703080241c0540440c656500c1419007081c482c5e0001d00c200032000341e52030030500500390024882e00031540109000605070041000c002101c4c0c050b00541081700048103100200d091071343c03070300f5030100c28000045080381c40c1e40308203001d50f214281d41d00b030b9a80000070040d02c1c0c500002c06134030410008140503c0012450544183c00040c0c590603101004403080020b41c40800301100403019034604040b65841c43d0b4001065401141d084e282046040070150038035840c0d01160702e00d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 196405377 1250 196404127 196404149
    0x10080106140d181b060813122106030b01060e01020a030302032a07110910030b060f06030709050f030a0b0c07060204180902040f0903020c010e060c0f030403150501 72
    0x4040110303011004090342e4890303520005481d1080c1c1c1c0c0f512103a80d40418182c2c0c10304004160500c0019141040c4009083c607401c0c10740c07140c9003407584060305c40c0800000070410f000540403040164041e0940da409040640400d03903442062140050082c94248015164039a5180000607507a011f800c0d0402c4681060f400342c00104425201079010b0350018182600d1900c00080248044012036900d115a8440380030784c95a62410b41880e100090b40e56150310701c60014041400b0030131000c1c1c0182400c480c3d20480d4041d80360744802c0050803031031209030a00d4010307030000100321085510900300e000740d500803108800261102e100b407603500c090f200300040c540300d6200041840740360500c000e001200c0c411745000d4503040e141e4425403002d0400010300c200490300c030011328085241900a44809000516007000313201d5141e01c00079500c20340000542c1c1404800d44041d050b81e01c42c64112a09511480202c81094030b0030220b26583c0d034005e200c1955615040e0902030800161401481d04817542c20b484 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 196406627 1250 196405377 196405397
    0xa0b070b010b07051005041103030a0c2a2907150c0f05090120072402010b0d06090f08042702040f051c061404050f070b03071202070f080910080106 65
    0x1c640b00400c4040c1040e41c0d0a510b80000c22303c2944c0400c020018114140d403070614802041c540141c90340300010000d149034003084a10446201068244400c40e40038140c0e00c060301560a41c542c0b954281c0c00c1c1d200019140000700d4000340700c5c0c900c8031100b031082c08003420031243d52000f800711000d912801c0c0110000d0402c104042041d8400e40c40351011006d00c4080039201e8030000507039880c085440e40032043c50a54405031800c85500d50750960300c407a500340000d020f403003a06400100c200d005104010040e9942d0288541070100000c21b829145a000d580c0300c0d51181ca035a0b02200c0c189142c2d0f1800100002d0241100c4800668025074040300c0032044c1c05101d00d0701b484100044d50f40c06001d02000000b40c1c0694002064950040703a00300342e844000541c2034100b6040c0a4107050510b02d5030000c2d988050410070500e41000c0481b81e020203136181c240c0e244840301503000003070f00c9540409000659400e01c1c0d48103000d4103400428400d1802c40b070700c0c111410340040c117842006092082c3c2000c10780c5080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 196407877 1250 196406627 196406653
    0x61b030527101515020c060703110a0f080c07060e03030306010e2b02090703150501110a060e16050a0b031609120308010905240607020d020a0b070b010b0705 69
    0x4010200307294070100b611410340350840280300300d070038640c121003505145490400c94000d81c04540b034900181031000d800c130003c0001c003081c402d20034080010304000102000c01d84010040c064006910b6014120200100f002d04080c646c03500159404811402500030001d68180500112000c80c1d9000c2d01440c01c5075154001500c04440302c00c1c1e00d5400583d21304480d55140b46428a074140090000500e80480d0701c18014040721b20401031101050520f49400c440d07124000b15030305c030110303042440d000e900c000c00300c0c40c11801e22894003002440d0034100152443d6440c03000ca03031100e2000e0075174030507940e02d44c0d91000c11088904612070040114020004101c001c0c00e01c5560304240d41c0c103400d045560b00e0759001400c072803e0841038242d00140308100180184070a03405200e81001c0ca4980d030703446881a40c4540203688602040b2280701d20b038005026001c649940304980e901c25001454845101d54a0114138015480101e04031603642e074801c00403a840021030181c03038a03a5042801400c101104c40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 196409127 1250 196407877 196407931
    0x30b0403021203040602070b0a112212061b030b0d060903090b0a030504020f0a050f13110f030403020708160302060c0f0601060c02130612080d110403061b0305 70
    0x180058046002e00d50030358891000c242c00440c0180d100740c40c016920500360400c1145600007801100c0c1c030900308a003407004040000166000b140c80e50388124034030107101800561070207281d44003200c150409103001c0188042070f8060002944031030f4800c1c9031180100000c80132500e000080ea603000c40b00d01c0a51b80400c0b034503880300c0c0f14280719040400e510b540700c49040c20986c11170f07150344000a446208000c1103040c2140240044442a9403090710f0354201070004020a005450715401541e251509039814104d50300048004010300078140e6454030700d505801c03444e80c003c41e02a0054803541c00300040e14400010101080036070000905145800d5074204500b5a2086008030030510079804010212101440314038000c1c805500d840c696030b942441480b0100c4081c612100440e843d00c40d0403c0104002c403990030510754400b0103a83d80d14012104000102601c984201003c44081800f0041003903940c0300c202c1440c2075840c2d000482440e12800c82c2980c80c200d0365042d03e504000141c0c103001102c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 196410377 1250 196409127 196409131
    0xb0406050d0b040624030b060d0b061309060305160b0301050907030f05010b03070908031213020604030605010806060414071e111005040c06080705030f04060902090a0606030c0e0a030b 81
    0x105070108401d100b200003c0c2c02e81c1c400e60040840c62074040ca28825025508580340d100726030034141400512648000a492800794200704040a502c48900d62026500c00080b144c1120258201e0314446072904800f0f001008140400c40720362043c03040d0700319074404009803203040354100b44500b440e583c20130701440468000941760780c040c1600c92850040d502c100307000b41c40c040c00701c00311003e440b0302e0310010003030a0101d0350f400004181c20801400c1c0d12803211040340c550040d4408180d400b0174150740b01007801072003240c1c4090030f1186007000119205c00e0200d0550f0003000300329400d02c045414030031800c222840640d80e20010400002d200741c40f0000340c0d41c1e00004401c2c81e007889510301421900e150b0500740710744d56110751165158200001c2010001c8008003404081ca05494140340805000c0c0180c80080e040b0701030142910000b9003004425084035034182d60142c0340400900305244c03110013074251030045101003800c11003c03004182c49121501c03405cbc0c0004040f995114515101c00d6900c03c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 196411627 1250 196410377 196410397
    0x2f0f04050118050402180a0b040b161e0503070302060c03090a0f020a170303010807080d090b36030d0f0e06181005040e06040903140309100e0d0201150b040605 70
    0x14440001c3da81d0340da1024003d0b2078170f80050484810344800c10800c3d180d0054000241c500c100b480700380590401002902c0c00c001c6140d00701d500102003418110f00051000e003212a01c000717080380c6e0200300305000c0068040f03244603400b207a01589401c0700b02c03a12801704607138810f40d0781d00a280318408184110710741c001c007500247c04080801d4440c240500c0e60071300b0440c1c0a50682c0700000401c01000208010301c0184001070140c840341900050040024840b841a000600804104088080e98189140f8121120400440640150840e9101500c10b906078100d12034010f100f1541d002d54000c1504286012440d0f84105602030b454080111580015495141420042c03c4120591b1141500008003000c02c1c0c966a454903d4039244004080c8000d1800740914100202035002a80284103075400d600504003086d101e9684501d214035128110403681c040c02e050038017001d025503020400c81440101a130081c8035500c440316a40054042511481d030290004001c10801e20b8030542c060000c10721 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 196412877 1250 196411627 196411667
    0x180204090303111b0601050316050603100e0135031b070f170715020c010521040b01050f040204030210030b120d08011508060f10122f0f040501 63
    0x3082e42100711040d00444c0c0d402c2d03030070f0400004880701100c042103250300400e001c40051205181081c8040030382803903882100c4c0141c1000c0007013803d6180d240303c400085c1407032007403005c900d6a5688102c40704c0300c4a442da0001006078201d900011980c003032207010444500c032004620b00010b03000221103030303d051124802170340140c0740046140c40301c00340d4040c001d211703022440d826a88201d540c3e0b402d00d00154400400c04d5407580c1e032180d0342600407035084091002404c00030740344c80b4198452a100c6841020310070009425504000801200e001c0150607540242d800c01c1e4881164000c0c0000c82c42280006503010704040c1010034554865006000c3c19480502014500c0204000c0c5900e01b0701c541c0a10804200d02c040140001c000d02d407401c902908031868021601d003020302c003144012101180d09405141d01c01c2c0d09a40d054000c2ca610025080c02a0f000c22450100140d0001c1d02c08080800021a170710703581c00740089010801c2a9803010412048840c941454100155409405414181d190b40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 196414127 1250 196412877 196412891
    0x10090b0f0f07060204150f1d040e030c0d02010c051e070c03020a03030c050d0c11100905101e020604080d0506040f020c0a0b0f07051c150807060e0103180204090303 72
    0x41114090049180f0880c1c002d6161400c100b0004e04540080a40c5030410182112034000d02d5800890043e00c001c6010749042800f15100c0441c0190019104080080c0720014521541c401c00141080a0245550003048401030160046495200f0509070a1710101550001d01c124070740351009103c0b540c07003058919a1142c3c1c0380e02007540000198415000700d52416450000d01c007042c0004005071031140b5240c0103403041a030312841651074140a090082140e0502c0400c02c4d070146034141c02404000b8440c80d1000d040000052074204404c4142c01011903580e4444c074068000030b00c1c2c1d070003680d11405140c10940c10340a6038004000040145900ca03031101204826007080e8030040079000100c00240205c0800c40c1802c1210b1a40036040d41c016a008004015025500500b0349a0100740c4109003000468848090405001a812142807150301500c00007019100001c006088074156100c3d007041401c141c0055045031440c00c85492000024902c4a00504d0f10707a1141444a00c41d040001c2c0d88 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 196415377 1250 196414127 196414147
    0xa0e210105040c06090909120f0c060615030e011802060c031606050619080c04020702030109080a27030302030a0503190608030903070504050903040504150e0a060e010510090b0f 78
    0x900d8041e01c0a862101d0f4400c82440b03440d50110000000c0c243c14402808000f50540c1d80d9610540041c680070208002c20307900e5403100f40300ea582d80c005283c0114003804080c0d01c8808000d1a82864004500402d1620f1410500c002040c025208040a07405031020409119024000b907503000702e022101c203001c20402d00300407110946446000318010440000d4914010303051004107009100b60354615100040301b0000e01c003001491200740b00081d500940c8070003080c404a0302602000030000d1034200080750351003006512017401480030415660f00150080c1c240507005a10000d400043c0058004100c03001c6414001d100440d04141c2021110901c011207002940c11210a500680300a030000500440c007454100842000740c20122820851800c012402030ba580c4070300d03c10f0350b01907600c42c0c611448a02d01510080300400e001850002a07103803e2074018010001d82c059988030b00c602c1d000114182c1055060340d1010061a1200742d4101d040c0007120031b594000f8544640403071020000300c040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 196416627 1250 196415377 196415381
    0x102040b04060e0103090b150d08270126070e03010c031a010509010903060b01140a03091a0402180613020a0801090b010c0210080c1b0c01140a0e2101 66
    0x340404101552518180000140760781d010f034916a04050501e20031401041603016041d070007030b44080d00400e035002c404000c5a903070b081c141400b800060b8085210f80440542c80d48009040b8498008880c0c0200d400c0c0042da01405190b034400c030690000c0309214240304856207003507040344a81c20701c084c064003080d00082c2942d410b414080002900c40000301f040c100e40c81004d401c541804d003031143c104007203c400280483ca880c40041c0c00c0a813144c102243c240d00034145054002442696103070740b00719010000d000b07442440f008440940c6100c4c060200d41c2c05d4112928007c1c1d500a0520078038040e21440880d5201000d0842940712202d00201c4541800034401040402100c4d00d40080c81d624100000003140d90040c422414000f08111000c010386d02c00c03464041c019094101444641c4070721400c0c29180c0502003460719000c00b908030710004008006201d000b0000c09a889c82d695080c4008400b0075402026203c074040382d0f043c08030282924008100c50040031608108502d80d07500c145526003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 196417877 1250 196416627 196416629
    0x160c021309051f11160606050301050c0c070605040b030403051803190b010b0403050a1502070213090210030e1009031205040b16050703020c040f020c0f030405280501140408010204 79
    0x241c16800002410050305640c0e184010342e5030500c0003001250390780c0207005036a114207817880380491400110705007049017690280000c1c00010300208154038200410140d60b0340840c4001c1160321808a000413441c0c46881194160b4030b8202c0f585d415515603507825141504140d40590101c1c1d100c002c44c0360980c80c1008104400035a000804406900904200520000681002c403030100100300c240007042c000541c54408a42c04005e00008007001c0c0c40210082c0076034200291300200001201c03c0c65022a00500030107802210030100e245105001a811604d01e2240104030b60001c105401c50215594003240ca11030090500300400d1042d01d980701d003101d40803103080310f01110040070b001d0704000300f402d000c40c3c1503442d00785107181c250b05171030195880c81c2070603000d441a41c4441e10400224425015240241c40440440b0429104543c078036450380c0142c040c0c14001c0e0031205a2900d500124000501c190080c3c0d9564501103081c178004450880603040d07141c4d0451000c00001946070000d1000304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 196419127 1250 196417877 196417883
    0xc0c1203070e0904020901121b03030201020a0305010803030402130e0f150421050706110412030903060f0b1302090402090d030903020906060705030d0b1306030f02090f160c021309 79
    0x1a40ca141111000d011042d803400301c1405100140104030042e2540345440741503031501d4281070300101d003914100f0042d80402291445c10800d41500004160b0150003a141b0300100d40c4051145070b884046e210380e2800202c42c00796204001c402c84a4100d00a94410503014280360306850510340650755107440d2280c00c41c00121684124010441401445241160005d0f00905440440c18891500a0541c0149440030341a02d60301d1091514205901c01160002c140a4031044058196414041c024415a00c801d944803420041040000764541c031403880d1003900100309049080010804d031000350400301410750019406c00c21101603036110b142040025200b070360341404141c194814030a0654025142317502611040c06000000744000c000e482401001d001c0000e45800c0c0c1c1c2c00000c4022001c0c1d40c0052000d131806002005110b002c8005100c518000d6400d09940d445d6103048202c450001ca801c00010360708120902c08142c418644000403030300007007440341c0031840c50507171500b02c8242000403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 196420377 1250 196419127 196419163
    0x2102040b070b0a06030b0c2803090b0106110714211b01020102070f0b070207030b010b0d061e060c0602040302060a0305010611010522021203030c031f0602150c0c 71
    0x4a04100d00780c00c0d0160b00600090042c0309445c90340d0b03104041401e000e8605011064013148043e44003403811300c10035a29242a900303802c0d503191000050000e00c01510700b5581c8001000002c201c0d00d000e1a00c400a01d0308030802040411318040c061441c060f6140c486aa0161865a181c4155a00c80800c3d00c9546000070240c000c0340c10b003219450403c3e041d070f00200c1c190b9005000303240201e0f03801581c0c2142150415040c0781141c2e1817000c201c1c1010400c0d000180040f0b9070324004514050500041c20303120074540404c0180589400c2111000c1010a20401401c3c441200c10f0081d50300c5042c080a205100b00c1c1e01509094586d0b0014444e60021020900001c0c1e40e100100185030307004400c406084150002000301341070040242148040c0000c403003440c0c411700c05c2c000d40bc546a0b401c404180000e000180d82d120f0601c0c3c9450b41a65100b0b0310f00300140e1010b602280c07026864401c902c005c0703e2031600100b0350040074803a03d0b1a80c0000402d0300341151000d210700f02c101780c03003440b002401074400780d05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 196421627 1250 196420377 196420387
    0x90d02070e01050d0209040203010b03010f150608010506031f03060c05090a090e0d0f0e04051e0108030a0503060d03090806041b0f030206091c02030d0c060f0b030606012102040b 78
    0x2850400d1aa00c400040042503004001c941c6030000000340c0ba9030140d4038406c25646a00100c0d02520344014026015860005c10908540f1554080b24246203401c0140c1c20803966860115480002801410b50015081002c00c10100c56259640c900315600346005441540e0ba460b1103080715510305600011550000340c01d038649c904041c8181c05409503a01c2004108607601c00c082c3d881d480b40c44854107100d17001c0c00c8456614000d603c0240c0010300204140014500007800c8a21340760305c1c11644c100c48562000100f80d0301804000e940482080d81d4949085903641c10800c013100c50002c03001c1d414820303004000306a200060000b103126900403010001c416029400307612018440d90321130300407070b440705005000603501e803003c03106185411503011060035410440c90208d1784907030000135814400c200c5040200c036080300782d1020b0300340100010400c10121680800035a4240c0c09919816005a00040d580b90301980824000101c004c02c62084000350325180000c0f0382c4290007510481c3c40104d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 196422877 1250 196421627 196421653
    0x120a09020a05031e2802100513090e010b090906130305070b0103061409030f07061104050423310c0306060b0408280803091501090b0102010e011406150d0509 69
    0x215a10500103918a446002a50400410251800d50000e108401500c00f00c4134088c411001d40380c5900c0b081c804001490b5456201d0300041c030600c1c00c6001c4a500301071803400e45140403c60f0611514028024000325034603108000c0c907141040200b2824410144186408100c0b5180300718061880f6080014072121614200c02103a5070040542c08070b81c1c01004290a20003505061310042d40c0c0c4164040348914186040c50854060fa80020f0380081c640f220b0416200010b0380c54500d8001035800210180c0c455402815801c3c0d0070000c00c00c1140708040c0c0380880b50150350550310304a4002c2111462254481d030746c06c0107076005607000c500701c4000400d081c41510001d01c40f05440007480000c405004500c202c400e4454030403080082c000603c080005000c946080c000c540f601002901c00b052590b0315000300d1002000110904c1e401580707025085c0514500501c900b0000c8404d20620030043da40307a8082041c00c200b10301441114002c24010305c035003c1c0490040c0c0d801f0304a50800740070440490b038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 196424127 1250 196422877 196422883
    0x4030e03010b150a030f021b01090201120b0d0201050c010207020a0e07090602030c060703050c040e0c070c1e030b070c1b060807080c030a0c031b110105010605120a09020a05031e 78
    0x80e40c19118014165146841440010032903040f0201c0d8200800e07200c0d40846c1003030003800790115a4140b152140c100c0c0c68945019403000c1c0c04503100740c07a010301110a10a905040300c440e51803154110000c416807402540c015009010300d400060300140c03804403180d02007000400241d0051460100d44418001c11071741043c807a502408151000314108880f4031b555a586003409803015041c1588c0b40c0105202407a0401140c0103003182d551000042d0800f80806001c59000c040705440312052218045010b030000704045112031f10044000001c141191a548241d0101802c08418005000c04000000b581c0503400c0b10812071242ea40c0031a2441c03c1005440035100030241c800304000c490030420070700740c45000d0f070307421004110000407c4107039170b10143d000b0b02110100b4596a0144450071030900e912082c42030403000c9020083c0140c1e40d079054162803500540c0180074003500108000b500e6190b899001500c0720380014241c0c2c030f070142d50b000441d0501d98421410341d010980e640c4030000b06e090070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 196425377 1250 196424127 196424141
    0x1005180f06040b030705041112012301110319050c0f100f090b010b0d020f0c160b0c19021807080708060102150406051018320f07051204030e0301 64
    0x2d48060001c080a0000251614014003850348650b0340c868042000044070030a641110f0102e5100100c00c1d43c44030031260188a000340701420103890005e041131203520814220300d40040420080d400c00d54400440c002001c0f03040001810040e00b401050302c180c0c41000341420007a07000307016003400c000340d5000c001660242400110b01300c0c1000c3c1d0002c001054264100c2c11a0000c2c204035441c0c1001d05c2c52880644541130007142c80702c001141042d01c7c10000b0441d03c0c0c071034001030100e000059a50b400300049019030040c1c100c0b01d0300446041c29020764458400886584000d02c0c84460303803042c0d500c000d80d080d001d60b11580007503911002c01ca40c1c56006004c841c0c004800740014111500c4091040c020203a008000400d001d807541d0204214480f0036100c0c90103031180e507660b028441d0b064094980284192803070003449502507c0305941c1c00100e410440052200840ba45801d0381e2500d480050504c409442901000070410000c246103460030082e43c019440307640c50668020550302010309640701 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 196426627 1250 196425377 196425379
    0x1209050d0905041a09010e1308191701031707020103060e010b0405091e01090902130e0d02160f03060b06070f06020706050745030b0703050903130e1005180f06 70
    0x303d5114410380c2c07000011741c1191900d558880b03480c1e40d40010f5860003200c0c2e900041c83c0c0b00380880d400311084820510385203040c1c550350760710b81101c10151508030b500304288805082600c400141040d03a4100c0300003050058010b0501113852681c1e12043c2070000f1090717104c4004000c012409100500d41040d109401003000710140d0010f10300301c3c140022505042c03040c00c05065495001600715250203004905201890b903040040e105076011a6454008440180c00140074549022840c40c916441e40740c00d541c0c1080b0344400403800c5a403048014030780b0445440c6d100805100000c00104030311123851420744079071000b503151559845e01c4c1095410103491501030009031492000c51003c0c40310064800d48102030003c43c00b202f50b000c401c2c40c40010403010110316821050102c2030005030400180240e000d50b90401c0a9519030440300e07103034010044c5410f180791410b001000310a010900c69604009071101c03450310280c0d0b602c001000e150700e28809a0000c0300800c1080b1890010410155010070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 196427877 1250 196426627 196426661
    0x5030f03120f15040212180a0308041502070c1202010e060406020307110a0510020a0c0f0302060304060c03021213110405010b04030206030406060801110c06070f0804031209050d090504 81
    0x10520000546084010000380305811924001040c5410056800c083c04001034421541ea0f625480061400c50044410200d1556100c4040610300000100c00302810380650b01c3ca09103480329074817491418000241c022541e0b40a01c441e41c04130355181c01e20f00c001c01c0c02400324025542d0b10301c0058801c016039426507104510900007040f072107801008031034490b5405201185c45d074007464002492003045800203904812002101c80c0c03040d0700040c020340c23811701031034051440682e262102c01000e502800025003004c41800494002500e54021041091590902505005202c3d8180d01507050072940c4042c400c581252090510240c85030743c3e00752103816203050001d0341c140840caa01910072440020702403007002000500f407101a03808000500600d400034414002001c0840c001500034191030085809401c0116550b940904183d22200c4070540300c40c0010341d51501d06407500f40700255102e09a070345a41120001510030300400c0580011901c520004c903040c9003c1c0300850b00c2c0301c1100f0703030981 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 196429127 1250 196427877 196427887
    0x52b0203070c140414090c090108070305071703071205090120030f091201060f18050f0601030902030c09040b0106030f060f030b100b0d020d0f0c0c230703050705030f03 74
    0x6400d0040d150507100309140043c60b00014001080050540359881109542e8040c02c0c48507001c1d007c80c000400307070012156560f40c0d9881d001c00365150b1540c1d100043c1180d0041504000301e0001051081c400c05840007a2420503078103445d4815110200001d40b40061000640c1606668101d1136a80310a5005111034100405010020340c0d41d200303050310604003480102d03c9807020369a81c907410540c0084030b8002c2c40095900e0072040e103a981603004210407200c070b0483c6401001c0c114801d00d48121494a260342303540e110040158003c22040b00b09980601039825000c1031604c526442034003030f62081113149219803406030001c0849140326501401d040c10700c14200280c81000d243d20094a403c400a00025150752200d00412002030f40064540c480c00728411048490f00e0f809421401ca0f00542032118141010446086075482c859850110307850305140e1004c40c40c0440c2040c54428a450801030400f01541c05919140543c4c1c8120780c3c0d076006090078000350a050210900320010700300154205 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 196430377 1250 196429127 196429133
    0x2041d0a080903120c100e060906071d0306150a0801060302180901060e090a05061e161209080d060b0720040207020d1115032202030a052b020307 64
    0x910084400034001c00310104681106a500b8816408000a00d41545542d45c40c0e070f00b45951500540c018940c807031071400300001c0440030045022446030402001902c066a5041420b480f0009100400d01004402e0388002e030310391300d0400c10503000d2004e000703070071480f005540100400b01034190000482030341480c40400042e2181c0b0000c1d92031140301d038482e120640d00c5031f06503401041c0c030740d0004070b00101a6003131101700300000c034036038014030302401c15102c21f941c452107442d02c0d0308401101c915a0280100019402c4503058250703000450341e920f070440010780e10280002c282c4405075407d0303443c400d000640c18495a41881041c0083c40010b40140c1051500c0d102e07040050b013058202611200000700b603035002e0307880b84d0440e00516401801c441d1b1b0703806c4509141c06001aa1684940206e100c002d60040181008055074810b40c194001d4607000c0503082042d440c83d223940b41c2c003280c25105030040000020410302c01961910070074503260601c0040920020061000c116000d815504108582d01c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 196431627 1250 196430377 196430383
    0xc0510051804020d0c0f030f020f040b0d06080607050405090a050c16031103130603050f0402030709020c160b031e0702100522031107050102010204050303030f0711010f0902041d 78
    0x301c6103002180c4011841400440d0180c42004d01440303916240001c003000680d040141c19090803919a01003001400c040d01880403480313110074402c0c88030014401048128951401808201003151011541c0c6983d6210070789400d4051f14682d020440101c0c0a0159052603403031507503c000d500308240540c5c22f1105881e15241300d84d07042c0301007502842c0341c0031050501907246403042e00e034140c0071286d0310014426040240030082c040c090009041c000860041103501c2c0265010340d030024054901d20f0320f80301d0321000a50018040000c203011b88003014624090b541800c10081900c481c1860303a07442d0410080036072480e01044031622103880014402219030001d881005056000000074007912010005541d4101d000e103690141e45808840c0170030998001421844601c0d8401103807941c03078440c8010f81c241e001d540240d9806500a10000c5c81040c1c400d000d0075040318141c24035014400702d034801d01e802c1d500310701e10210001307840320003200031400c1603c548114900c24003404144003046c6e48907552 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 196432877 1250 196431627 196431637
    0xe09191b030b0d2a030c09020a030c02010504020f0405150a09020406031b0507060209130207060b09061507080901030e0708030711040209131d0313170d1e0212030a090c051005 77
    0x1c00c2d04c0140302c0985410940381600c014541241086a050707a440c02c40c240030703600c81d40c00d01001a09004020b0501c030b00500986000319801000603c00944c0c12080c0401010020801d0349410390b0000009035948170390a40ea800351601d0340015944500700782001c2e0689403d0580e520307504c0d0004030841031041e0b00c0010307900301507841035016a0f40c5400c60000b60b00c000e443d251044003144000344540c00c000c1c41c0ea001e0042001c0a5031114400e940d42c03820041107000341c02001d85c2c5410100b107620001400d0000a0580e400705050010b08e00e41c882d140e140c588035240c3c20103440744d40001000d10074460884552005800111029071804c000b400200748a03c0c0460021150300e6210020b066200c044011414155800f0070122034580b03503804401d490751250303841104840f6280c070044018003140442d020003616180d07101c6a45514264400111f02c190a420711411030043c4865104049248401035000761510324000c95075006c10b01785000b2541c91980810b10642d02d0003500404940c114003511 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 196434127 1250 196432877 196432913
    0x9041a28030f06021911100b0112092a08010b03010228020c040f0b0f0306130b09031201090c18080706051803030d0204061202030402010e09191b030b0d 67
    0x2615920140303000d4000e409100c601003d6101045c031900034055000340045074182c04081281c03480d5410300701038001c41da00b0901d0f0a000a260410400700841207421441c1a10f1140b65409a01c0c0300155a0310180d0340c00810015245034a10b00810910009000d19006003100320000c61524817404100c01c121460711841620b0ba2a50024807080e503802448480c54164001d002440144002c1d031030384000b8803017070810a200340c10807120080300e42000100644a1215040c41000700905503d5200300300c500140304100500c42000b000c0c00c0d1501003890f01d40240514100402c1c0703101c1e051805016141d6058000c044a4001202000030f1750001400f04e00b01c41c03079424010b035100001088602c0b0460782903140b6825110014840507560340c1c0d64020011601c2d2542d5009a03898000c01110591005440280c00200c1102c0c0300e41c418500b0b1222f0340d410040d110402c20300e06408481031010307074900d47d480381100d5032142400101345400d4064400340c858210741244414030307250781710740d0401c984c1070b0b0718 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 196435377 1250 196434127 196434143
    0x606020601030f051c0e0102010c090f0918120518010f120e0f070f06020601120b071d030a20060406120b0a05360f0411010509041a2803 60
    0x225050100a209090820302c5c51040d00a040c080004003400d103d6044440600541ca0320310001d06c00391041642c84c0c00d80701d54000b0b103003c80d4940bc04010203082c26141001c8094072281050b80062621080000f8125007903c94030340302c840f810100c60318840001d6085041c0104030010703090341980010410025202c00c00002060703100d80a51a140c28400100c5110701c1c4101c2e007004c110b040c05403260900721010355089501c0d5030388400402440503141c0d0f000400d5160200e01003000d481c043c945001206580d6140c81502001a0f800246010b0b05540306035080c0c3e01c9002c614a50707036120003d494000c00305844a51410345410001030480b1440c2412451007580c4600f4071406646851400c0c0003058001c04e206803071040320340502d40b007840010768115149503001a1560100c1020529072260851001501c02c95951392075181828040304089410400200b10403440d5039907911900100d0080f00c907459842135039100c140082005a116074028042e00d641c03030305558450b50b0701102c099942c02161 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 196436627 1250 196435377 196435403
    0xb0402030412030f1b030203011401031b050a0216090903200c09100b0408070e0a0911041805060a0e06091603021002010204080114040618020a05062206030203090f01060602060103 79
    0x84e0030010071003100c4240c0b1071504010704032620755254000d141a00c0e070040c040d500e100d141d0070040d0100e8000c0d180f580300c14100d00001e0344085005030050a4200b0f00c0e40107807881440c18000917100d860303031500a000070766600c0d515602810390110981e140105d00051a29481030ac942ca010780d1103c02004007032048040740e0008100746024035000b0004c1120700001910b540d101d0320039a07140c89203405064039000e13400380000d018030f0752070180388000c64000c40741903d064004001e20010700762203040304036840400c50600000400421515209110b80000002d4940b481a030660504102401200f00c43d40280742e6000c8140c070414a410449034102d42e044225440c0440aa0190140394040600c035403030402d000c110340ca0040d4020340724601c10b4074100072030050404145500c1c03901ea04069001420048144854100100144400e0303442c04c0001440b141c0700240c0303010003989d681018000a8020003801101d01c0200000740121290070000d216072030030001d000355900301c140301c0075020000010f8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 196437877 1250 196436627 196436651
    0x90302010204050306040620070b0a02180d110a0509010b040e090a050312010e06030a1104110d0203041209170d0323090601230904063c0b040203041203 67
    0x4100d5000f0080a002c2d5641841c1504010008020b0100d80d8620303002c04144a250507884082110001a80310340c82c41255292103001400075080009901e00844440c10140060340da40c501201116109118032045204144140039181b841c0394850350058120400601ca508948010b50302501c0c1100003007207550fa6402010ba2a240034080040c1081c00005003800024881521050582d914222807004a49554082c5a5541580303000580b207115500280b08003071505421521182c260394640d217003003000c441d4070101264030540d0200c0e9a0140d250403102019004200c9400401c4400f840100c400c002152842c2c840282c89548420140d940706820000c0781c0380942d902d1210581d0700d4a44962030860b0080e65180030a00490141501e45601c25024022081c5501204500680440910344981d9247d0020b802456014500399428049007005d8100c2011030f100b02860381582840810303030001c101d20071602078442c502c0c022401081048080b8100c2281d51200c402c0318a00090702100c0c41d1307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 196439127 1250 196437877 196437881
    0x40b07020607140c0109060c2a080708030c0d02030406021005040213020f0304020414010518040f17071505061011120d020d0b0f01020a0213060f0b120901110d09030201 74
    0x72100410151690f050607020000010700c00b291038000b030701c58241260300c0e0b80050310341084040e40240301c10140d007000040d20101511358080500300b15138403c0003e445400032070810419402c5414580d1000c1090100c0150400038100e4a003c9030000c6c62601d420044000c1d1990001610001140d4840002c5011501e640b1880180d0700030700390046403a5060100d00d461070354410366090b032140e8144100062100c404080b00d50403114024054420f00c600d444042e115039000400c1901c050204049200103c3c80620f01c5500c00c071003400c0083e44d170740110302d0040200c0400e41d2000100502e01401c10080e51030300d101e00d4000728240e051103400702c001b81b00c1d01c40c40c050f030000c10000c1c500004035610a4044464000c1d0184600c2c0a0061011020031000e0111001050441b2070051307012012010143c101500e940000c5440700d0070203e0415140d200310340b03581c041070f407000300e10071400900300c1d44405080c0355990f00208118000d00810002042c00107003030080c40c2c074000206035210810800c0500035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 196440377 1250 196439127 196439137
    0xf4e060c0a180303030609051b04170309040f050f09010e030406030e0c100201200f04061107030f03020601060f0f080c0a030212010905150102060108030d05040c0b0c070f06050a0203040b070206 85
    0x7041e0740302d6100e070720b0f0f140040c050075580c8038484841c1d0500b0041048024840054502c1c6444054210b043c5458424140d0742100040741b02c40a41c007042240c0502c42e110381c061120117800c0301c0d001103403601300082c40c00b0b15420018000b40c400d0b403404003a804d10103000b0080701d044a4461070b010682d1003400004038281781d520b00d9210340c00000b02a1a9034802e4064000c5c000ca000f43c4c3c40c01640105c2034090304034103489a070007039442001c1c2c200024022680903904000c85001e940d012600d04603104d981303210094141041c1540541e101d1001007101c107500c02c80c0700300c8d0301c2854649007980203990300c00a01203c2d0041c000c40002031010a01301c425920070ba0590742024142c034140801942e40700760190081200b5102e4110304664a64240710550001503038504179960342006501c1c08026000c030400900c005001110072900c080c400085a18607240070384110100180540740c82441c0c402c0c1c21b200140c050348010140b0005102d60103c20760040240c5089442c0c070080c0c150f8031419440019800d10030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 196441627 1250 196440377 196440407
    0x14060405040e060a05011202011b0c0302061b06060a03050a03080c0c031305120d020613020d0c06120f1104060c06021905130b030c07020f4e060c0a 65
    0x35091109429500002d5607500684c0c418a0420090b606c0d40382e64009540c113508042d010503030403240c0d03500d1070603180c8a08100e1401811245d030119201d034001011340d0b00c8100c54004150700b0310001403203180700303010140e0414802c441c09014a0318680e01d15481d03003c40c04014041c000c058000410300c0c0c0103403049419144400301a07a40d04c075a00741d041c1c3e0124006000b424000c10003000c0709000d00c1d000103a038080907080703900106031541c0c03402d045245000039400220b0b01300300c000058600049505d822440900310588808040007118801038040b95070001921304403908081c1e0703405141407160f0840d0140c1c0d20b0340c540340401c85807500b00720010f480340d0006d8805007580040203003059544000500100300da0380f001e004801d950303410300b4001804141e6001007648400c1005800514122144100740c2c48041c01e8000f03e1001c0640c160390141034107600d5050b91180422038194614202d580c1ca03602c503920008a00d004a1a0000707a9407103c000740644522040080c0740802c0c0c901a01ea1500e20f03d50b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 196442877 1250 196441627 196441631
    0x60103090b0c0d092a050a080606190509040b0f0f01030209180a02150c06010e010506042d060519020a080901050a0903050a050a03110105070c0b0606040905090307030f05070302071406040504 84
    0x241e00d45e00324030034408080c0689904038401801007914074191260b5000c440c48180180426213502080040480215003100c0c201407918100103a01c0d2221107580d44264025101d030603903450005aa00f4003614024101070000800d01c0040c070040e40c506e8440f5030401074159501c18403901007010140b4150701c0d480045d50040307442ea00c1c15040f1445d180240200b00c07920040c2c0c2e5041e66038040c2ca48614500b8081e035a4410000e00084c000060a00503880c4070920310300101000c9280680364110002442c1c1040000502c00900a0b00d0302c01114494248403d051004011070f65072510f0365800303405046021410800005404032200b80b090180401668004043d1122a2141c0c6041951800403100072030109807504a02c0d85441d030180b0420380f0030130160302d500121150660780e0050300f04000b441ca03035000509000200b90f0701e00902c519031107101c0e214019955207203c2c2c200501010050b00f14001040000c11020000a6003c1a008110390383c090003480d50000a00c0007038514022900f08540082c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 196444127 1250 196442877 196442903
    0x61303150e0712110d050703151d010903030b030c0604090203040212070603020a02060f0403020c21100b15130b0903070e0f16091505031305030a17060103090b0c0d09 73
    0x40d000c002540f4590b02c50710315250050070000500000001107000502a90031200040000c6800c40404102c500c3c00c1c0140052500700382280c0e0143c8000c1100030458682d034400040f4101038140c03080c0c0d94a103800f01c00030800380403030340d0026045d44124010b80410387e40200c00300d41151908050201d5400d840000d42e900d5079101d4900800130b400c034540040c01071040c140420302e00d89440d0100d41c05180c1650142002d03040c40c006200b034076030f84075104085120942030000150324040c031110103044010034010405450074001c005204404602d00c2083d0701c8100411585801ca4120300c008039074100003516205d110183c0003038180300300d0780d0140c1c000301d500c1000c00040c24903070840c061040010142000116960580484403181180500d00301400f802201c1c014450140e03000e50350208902c0c400f4520f0700c500381c2d00c2e0350a40e00412060000b088401019402058004c051140d0144003807038204100b041c2c5440c5c400d01a2006458030624001c0051a130314409140d8100040769500240114845 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 196445377 1250 196444127 196444139
    0x1090f08070b0c030705090402090f030d05070c14010504120501020c0a03030f0509010509030a031a030a064107031401080601051e1305130b04030305060f061303150e07 74
    0x3984644000c0742e15145a40000310700c030114400740c0707020742620740d1845c0c1404410342c2400029889800078590294000b001070781c20f907504004110810300d242d540c017a01c5024500e13140d54440d2098100803880340035003640e4919645d004069808445110414020512503030610318020b11401031482d109020764501c0e035007070542503040540745150001041007155101c9841d2801c03283c042e40d0415a940041150000e918400c3d0000d0860401004800041d112600b000911700201c00703004503482522000d90b10300003607001864030b0200c803100301010728040d88105031035800c9510892920001c448640031a040078801d40c414191b8841079801c507586541c46800d40c0d540c602d024404d061090329490880d421038031040c2059551203201074010740c0072000c0a203518014002c0241038200b00c1004942c407001040c3d01070722071801075000380c60015003400c000d07092110484145800300d014403c2049a2103d0742207000ca0141100c0d00300c4c031802c0c0300c415504000c002405030301e110030030540308696000c114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 196446627 1250 196445377 196445393
    0xe0109091107030e0102010e0604110609091f05090403120f0b03010507030f11160b060d0f060b04060f0501080a050a06080307150b010c390e070e06250501090f 70
    0x2d250b020f0b0f251454041c113003400490984403081e400700c4094201c1004a40000d0080329000c00340c0c0c9004107014241607807035010800b407403401c40d2312a0710340c4649030b0180e401d4820030a418001e480181c07400d40051400c0c0c0c8025241b0a101c03440d041041d13a0301c1d810303084004202d6105440001d0000c000344007604106500402422040e0001c21b411890b1021010766503140c4421529072844001c0c40210b1590317140c44801c81500300802030b0390045644207459002a080168810341c1600c503c00c0010801100c1051004440140e04480910034070081c081c00b040c0c1c0c101d4401540403441200101c0d040ea10501108003034842580a031080c0d100200f106800c011034140303242c000084c4032100b0405860810011070f18103210a80c060301031b444000c503030050f080c43c2c50a2251404800c8407151314000300c42d108200400c120781c0c00800c20707c40c44003d00c607a141d400510b4101c1d8110440d401c5040298200003a11003900502c1c08c40520074024628504000080d0030150b1401d81000010310046128184401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 196447877 1250 196446627 196446637
    0x8100909140607110a0303021c021606061d0402060304050c09010603020711030d050703080424060302030c10020d0c03090e0108030901020f0a0305030103080d0b1905010f0c020904030e01090911 85
    0x10a501444000a032558400c0c040101d0101044c0b000340984140b42e1403c1d802075111560b0311452030003100c00c0394010082e9000034800c51043d01d0400700c2151450405a003140c9842e00300c0080580c0c4000510600107180b1420341e042078044807e29501d8a40346080c0346410b4440c1416600400750b50000240346400d50f0140101074080c051041603c00084101500c60302180c0c03020001c01c8e4207100f14000b01f449a0400303680070740f1884485102d480c2101c04504070380c244d48030303540150b500c039407003441181030500c11403400d6542503841c80010301814001035280c48500c0039200030420b0020002d42414412180d0300000e082c8807050440550f119000c1513201d0344140643c03809031081d1a110f0300b20072000107400c5d80d5140c040e03a51604517401d42d9503c5040f0341c41105082a240e4841c000a000c42c1e4070344101420380c0d28a00382d01e111f018580000075210701c0ca0700146000344402003407070300c2c096160742240a1348254540340c80802c2000740c03001070712065080d80201010350b01c4c0c002014091000340c40149 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 196449127 1250 196447877 196447913
    0xc10050115020d030504122601030f061a090117030403240b0d0528140c0906010c050a0b130b01060207081203010b12090c03031c050c071208100909 65
    0x780f201540358206a060b50400c0d80d008120181c071140121000f4410039040e080710100c040008100017044010010300300080e0015145003400c1e4031003034204a220b1040600f01940740303205250303004c1e002e80000e101280500c0f0b00b80700010000c004402504080c0300303d501543c1d01c80c003402c0c1c1940051906480c0d041e1401400e82c40341d03203800c038402c80c54986026890441c1d175001d0010b141d801e0300c400d0102d15410300140041c9185e4480400e020008442d402c0d045a42c481240007801c18042603802c00c4800400504502c2c10b1000400301e072000300300003050600d44a604002080c03081e4440039003011004055400103001840200d00100f55154003090000440e0041e80442e03d582013001078201c0340344828400c0700712001080018038102c007003c1554540c00b020920980b40f049135018040390550740544402c0300483ca85400c40401d061003480703982e030000341415007681040200e82c1c030000c600d030002041800384031032200011141da010801c078034041c10896000380b008046500e0084d100042540d050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 196450377 1250 196449127 196449133
    0x230f0414040204120305130b12090c010e0a0915030209010308031603050c0406082701021b01020705120322030302070201030f091e1b0b07140102040509010504020c1005011502 77
    0x3598103150a000340c07404c2c1c4001c0c2e6014142d0030520307501a01c1541c0003090f0310400320400a000035124240390702030040d090030660503030a2850092449030070952001c071001d06115400c1011242900c60404c0041500c000120000e2601d00880045007940121382c4001c0d0b2180d0114004020801588040d41c0034000450301c105000c60385540a41c240d80003101c0320101941c080c403080004920600499401102e00b4201c402d0603c450080c5a089007200b10602e5a240c2d000501d07402c08044040620780184041c000031810058150703034240d00d690340e108040540c20300100110b410f40200c55010400c0410526201d841030351240790181c0a03400422003a404280f0340b000041c0520a54090300e9000b139403180b05c028a0203183e0302c0c06d42c0c9003210600d003552138000d0113200d6410310407103108500140000d4800c664039030358586015619200c1c0004820500e9006020400c450b4680202d601e05445080b100903858203800308400d0300e443d04090400041c20304003400040c0c9003070781d0500d051013060f4981c00d03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 196451627 1250 196450377 196450409
    0x90f0f2d0605090103050a0c120b040b130203010504061d0f0d030e19060903141303060e011103101e180c050702030a03081801020412080903030c06070908010c09050d03230f04 77
    0x40c0c0d00359600b1a000742146070ac0200086c00078162020076940311100f041142c0000354550080b90071100f040740c04403011942c0e0074100813007040f1200e00c01640c190324001010088118034916442d40c0703841d46540145502d41c240045a46400d10040a066060320101c52080ca698107005014003501d185c168041080c03182804602084d42c03003150345009441041c010410f1855903600c00504050900d60415543d90460f801c01441d0b030802140503500481120890714100044482200440c41c441c0780f44410000c0204500001c1e010f9030a2680c010450024440002c0c8805490034460030400035811701400b4541381c101034115480d64001d0090500245130311090840b06401c0b4891401410f541d1ba001c501d0603400106090000c282122000d02a2800c2001c0305d40068a880ea01b980d084001c628205001c1c0a90711003481040c003040414a002d40c1000d1620022800107108688098100b01c5044400343c80b94040109001e2000700303040d00ca45c0d40e03070305c07035000785074147c2090150512403942214 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 196452877 1250 196451627 196451639
    0x90c060309030e15040512030409112502010e04020d020307080108121806070b010807080f0d0e0907030608030f18040207020a0501050310030804090f0f2d0605090103050a0c 76
    0x205500c1d1441d030503150320107803809000400400700d00c1d03e60180b04103d01000086001d0b119901e44030b0100343e0420003191100c0c10300d030f051020f0340e05244000705285001e0100036400420399942c0c594000304040a40248401800100c1d0484c400d40182a0003500018032807002041c258021032254003a0b0360342100c40c0c1d032500613954903004444000038620b142030100504c8681c1d01289480c080d84001c03c071a02d0140555100b40c0300d030030260304c50300154002080c1008256014044000e02101c40c01c0076003542c90202a002c1d020078003815120340100129400105424025400718000d8900c40c01229102c048440403403109911880c503008000405000203040e604081c0241d0301401d50050644084904140046895030002002c070207140c5945078000011030320030304c001e00c06040c003100081032130040c41d00003805035a448100c15a0a40c509005803840c0010380392454018205030100340c20100305070602001070b0641e80c21450b807020707424000004000d00041c04982d1a07225074120541d03565600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 196454127 1250 196452877 196452881
    0x6070c2303150c030703020f04090e0604020306010902091f1b0b01051201060b0307030c120f0b09130c03140a0506090f060c0c06010302010e0409050d030914030405030a06050711030d090c0603 84
    0x18074945036240f81400031851081c041d401511500204484c11401c00759992400025140003103090001a0020400d020a6007004d00c4500c0c09080704100c01d41c1380525440100302d80c204d14075001070000c0c440d2456203032160f129404039500e54080b52468100c0c010981030085100c0c0084c03049074072a2482032a020f101c0c41040c001c00d000c94189100050440da03903100103a01803c0e020401d0020083d0038820034600705100e1240b2401e00003e528001842080e5106009a4000180c06e240c2c41e0fa922490060014602a004130180c0758804401d4201c9a01030000c5071070b000c65428010494007440040103c1c0b42400951074869400714821103915498030005045507108410f240421394100340e00520142d40111202440c2403406003000904080d261100c600f090183d0007800300203a00c8880c220140310040740a00c0d00400b464018501c0c1525280c0001d503113150107040140f403662504c001070241400f50b00e0071aa8091a40d055a0f500c100c00100341c03000304084082100c80e10804c007008125103100c4c5c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 196455377 1250 196454127 196454131
    0xd090c06030c0f02100515100f0201060b180f0402130b030f070302070f1b0b0c0c01030c050307020a0303091a0c120f0601080f1906080f0c0301050403090506070c230315 74
    0x164000e800d08220b8036800c0300c05080e0091084454000409400c041758480d007407032030b112302c1c1036960700ca58124800e4002800c1d110030758001c07036031180240400030003405000240f400d4a00c04036508502c000120700810040d001c0c68000038500d600050340064007900b940010351081142c0d2168000554400c44207070220300a0380344c0600b142441a2401e00010507480002ca86894140c090610566a03101500300c940e00c55040d048260b00f0004103140c5a503094090383d40c10b10324500b08076007903281c0404000d40e40c20350100040d00309603d8000850600076100000c500c8440b07900c46103502441c049600c44005e40c0040101240c8411032000038285515020342180240b00503502d4103815100d14003078000484003d4805844404402d40a04060426202c0c0e14010581075014014072403018602c20b04243c0602c2c020b6010b41d04150401000030b6000090105541c421140c40381c45850321b0800507060740c00768221183da50b841d07000c00c101d1165140b2040e00301803030031030450310102d001d24980b20b860481 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 196456627 1250 196455377 196455407
    0x10e060c03090d06020904020d0c0f09080c010f1b030804031803120c05011d0c0a080102180630010918030e010e0102010b060f07030215040c06050904020d090c06030c 73
    0x2c0c4082c24142c40c00001e4204128080c400141c10040705900003002c030792019501c02c078140c2c0c1c1c0b004d61a441c0c40d04007034525000c02042c2440300701549804485502c400d8581100c1e4100080031610b600a54021448800c0c1c200350703852848150042850041c1003894161425008107420140c1e00860304150b035141000c0d00d0740498070407401640200280d13890130f200d1034111929521240390f0045148580580355001600c03500418200001c40203102d04208241c00c51111030340104000c214000c2d9031226944190000d460461b5a41c584d0b46820004110181c40e00c0044000541d074034040001030311a9505841540008000d900400722141c18041103010004000c1f80d440500003d141d0701490035040074000600002c901154002d00003851680103500411498002040300c10038558104080c0a0400e4610030004481c10180c54110300c01c182e83c0310780e46c20041d000890744440c0d00d6640541e01466489003040c09440c8041c46c00b0759080ca418082c00000034030f08070880e540d19108009900300c80407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 196457877 1250 196456627 196456633
    0x305070e0c070c030b04020d062c0304081e1608030c100603020d17040f0b0315030c061c15060201090501050a020a05160524071106010b040e1305030406030b010e060c 73
    0xc555545d84055940040041e41c0c8500d0610040c40483c000f8002e140c10340e0711030201405100341c50300c100541c1680410055115500500080c060b0400c00507271503d40316441c0342540c9160301d40740c10441c50001003004644006a19050010303034610004003604440540704103882c2004200e181c07880c2241c0e460b10000e0741c40740b26038002c803002c00c1c4111640b08560002c610602d240c03a4580c40c01040004131507201c0150b00c1700c00007c000c2e040400d6100c5122892046028140780c0c54a47e001038240c0c010840843e80c1c40044480400d402c5011303512001c000c41c00b40758100c6040b0ba55490107402481a084180c40c15400c0500046803100c1603c00c60703034184000e4880c142441124070b0300701840c203a9210100c42d41d106414548e03004100d1030745002d005107200c02580246e840c00107802007030540102401a034a80c091001801581c40300400c1d41c00f40c4e081c100400b006d940c4d030444040c40315000040b02420501001a000c66a04e9050b00700d40b00307040003a21541c40c02c414100900080e0300c070b8a510003459030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 196459127 1250 196457877 196457879
    0xb06010503180d090905181c030216030e0102011d060705091206010b040819170a02150a020309010e03030103020d02240c07090e01090c1512060305070e0c070c 70
    0x58000e5000d59000802d010390348107034088600e14145410354408201c030200714003180c00c22104040b805110b030b00540100b403400000c80502d04003644c90480c1000e43c1000388481c505401c07854401d9041c0c800340c46084904190a182e00d050281010b0581810203005509110034031f0001c8110382f042a4075110301d80c0c02420b41da03840d013200310380a4204644090344014034a0100c00c282ca010440c5038007928000200542d02c03413918070614035040c1a6950039030074003000300a080c08161502c922404240c4d454000303940e10300c0b80080407401c14030150b0700840414020350600500d98003988c082d6114400c07040c001c00480c1c00c090500786d80c0303000c24400254400922145480113003409004502400b140b8a80c2180d42c4201020488494200c090800519842000d0400c009507450160407513081e0300100030042201c80340c80c4d21041d03403614041c00101640c5202103400a510400d843c0c7c03080c8115600800c22541c481c0f03091616030b1028407940c10340c2c48418010608625501c400c8030321007075104c0c070b01c40011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 196460377 1250 196459127 196459129
    0x1d15010503100308190201180c050d0c050409050c1309020a090c020106080304083007021009050301020f030a060e09030a030e0c1503040c0605040f290a02061608040b06 74
    0x990000345228070702c070b42030b0303200000050441025054151081a1040380c1c0c800040c4001d00312036034105100c5502c9920700e90368005c1504481100d041d11400ea41404030130086003800100403c032a0f0007a604a45800030144c240302c40400c2c2c0e010b802c08200c40d2005090b0b041e003034030030940d50b85880c040c1d44540090300070071040c00d45520400d40141d2034000446c031141d6038814181540c106078016900b9400c42440b07071801c0092107424444098003164004104100c04031446071034010b08000a026040010742e0b59101c601a025104c01407000900070b6503160704450354038420350030980782290403e00f80a40810380d03036a280d01541c400c041100007103003841841581200a80320310f0600c10000e000700030501186468640c54187c0c10304e00300030016520705052400395150701c02c3d940040e04114062000344810600e0303198000c1115051102000320150b50b0703022000300784007140408140c4400040c1380c0c0c3c0b500d4001c107000388146d184109a00703960400e2003040d24a048100c1d4020065101c900010302c003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 196461627 1250 196460377 196460387
    0xa0909020c0c15070605011d01120507030b18120a0503040b0411100302071202120901140f04080105070906110307060e0307020d03030501050a062a030c17041d1501 72
    0x20034414100d50030402c040001c10308200b110143c030101d404001454900b400494019240104a0061107201000e6030b408181d000c4041806030008940e00180b20308140802003213540c1c003075a005107041d901c50a0131040c203001c01140ea5944683d60007004109a80d42c41e204090710440c0761152100c516680da2a5525003170700c500203000702c4000b00d9001e00c0a0040d128103001207548040b6490041c0c0e1145a41452620890780c00d8a000440d070240c5032141c600c2e8040c0040e01c80d0098203007810140e414558440c04035901800c0500102c00101280016682c48150840740c041c20454881c40740890311030700700f00c0e0162170005c400304841c1d0007041588005041540b10f9111442d226050340e0038142d255000582da42c12001003540080d8482c8010b021614107401d0000017401d090800c00300701085c082030120004c5000c1d03e40f11003918901081c0e4103050180d00c108201e21750180e140003800444070840c0045070031601400748800ca1454042984013841a0458003550140c030718044200322031401151 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 196462877 1250 196461627 196461637
    0xe06040f140a0510050f090c030c0907030e0610030209070513140a08030c0604020109080c220209031501140603040218191508061f060e01032304170a090902 69
    0x446200382c0e031140001c50703402d0142c04ca91300c02d14140402d4908282d00c649011000103850b03100140c000c04004042c2e543d00040e00041d8601c00d0301c603541e50f0b80d03503200d080d0003c0c052890004d420380564801c02c156010903003080c0c0103491003150700344180d03180c80700120387c5030184200248040b40740301c0c1c00307020210340c0e8010010380c404002d00071110141c455204074110b400444162205a01000622007190b810a0382c60014048000060145269000025a05101c1d51071034141440160409401404c42038044584605010b82101c0018800320100301442200b4440ca07540a40000080115850b04000300c0b4041d6800400c60711500c0d51540c000088410090007042c80007203181042e0f0b4080c0200c0c020380c002d00f02c0c0c09060708221071070000d20a040c181d0013085030890182e02000f200c80910303851948026149640341091246c0305000c0113030000e0500d000c07154012080207018040e9980803003030091146114050460700c51400741840601c41c052164400080b4810290030b202070b281690141c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 196464127 1250 196462877 196462913
    0x610060302040e1801021611100305060f090a0912021e03040302130f06180606020f0303070203040608070e061b0f0c090601030f0906050903041e03030e060f070b10090e06040f 77
    0x5181c011045003c41c0040c520a0b8115010311021500030428548027100020440050a050200740340000001f07404800001541d03105d50380000104096524607400300c50403651028806005000c4820043d51303131492041c0b4101c803280c0a601c00c2d02c04560101c240c0702165409002c0480319002e20031100b01500c0c3da140720500701d40e40d8171703c000b03904c0d203202a03020b0003035414000004115040140080c14100c1c5045042c106074820400d020003554000102d4007126074038904900c01c0e861740740084036803030b81407190158000c801181d40d008661041c144c4640c800003441c104d606581100c43c6058440906004140e0310401007800a451540250409a42295600f00000d8000483d80d2240100c843c1078407441d405074008942400b20307034080c80b0b5900a022894180c124843c2c911b41e4010900d00c189840c04e4003551010418140090f4800c090b5144030b07600ca404090240ba08013018100b8030010311580003090704014040b00003c5010803501e000310b4111003446099030003902c0d400507002d038002d081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 196465377 1250 196464127 196464131
    0xc0302010c060f0f06050f06180f150a12050612070905070c050a05010626030a0c17160309050d051c020a08031e01140d02090a021603020610060302040e1801 69
    0x8030060040c140328501403e00000000035040b030406d028020b002d01e005100d03074000d403010040100d44441c00710400c1c0c01c0b2030341140d12000b810444004901c60000c624240c010501f004542c800343d443d00030700050120500702070200455540c88080101c0d054402464500c85d410900e02846400c0e0290045907100085041071112040c041d6101440c0c484c580b5802c3e00e059554050031702c110000e80c005104c0d900d0404440038007140078070280035200d206194052092020181c42c0340100514140c030140000c041c0052030780c44051000c1c4c09003607030409100860004072a0031012900d0703c1e1810f000c189a6402ca40100382c0f52101240020004964004540c03c2d80310351009600044e00761030007188150b0002c1c403410640304a036955445010b4041e0044009201c3c01003030000c15403507004004000700c1e011509840305c0d1311000c0540c4000d202e042d07140c403044401d40c510f481c189a00001c0150040090310110401c15030380c2c8401b201240142c1c0200c6820000300c401058180001c050242d42e09803c200c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 196466627 1250 196465377 196465391
    0xb0603010501080406360507050f01050d0507091802030402040e01020c07030f0503090301021902060106030209130b0a050307090903080a0c080f040c080304090f1d07060c050c031203160207030c0302010c06 90
    0x411121076820400707032103103000784100c8801f00f002c18007800005000595299403034504000c0041c0440c080e1708051300c84265a0000118024440c1c403442008240c4824a803101d074414082c4440a03510445d001e0703020f1030400801d4050300c2d505108a0302e4407207440300644019811135803200122441c4007801e0303c1521051010300301554082c402041010515480745c81d031a24801d03130107030500c00c05920902c245032060103907500039240d407204d64600c17003107814000900e6494507000500c06209a00301d00d400d4401c2042c0494034629660100840780c3c080e40b14015203941e03100b851429205206078903c001074014012030691102900c500760810300c1883c004181a840e034035400d24607002070748606482501e405011008502030303c102c4035a20701049121000030311800410f81e603882a4400ca008020b00d03200c0781014442d0500095176440340c010b00741c42e40502c0c200c0140186800039500710804c00421586080440d000090503000c0726032040401c10086c3c039680040d00d12040b02c4030b0503035080f5180c2c0071b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 196467877 1250 196466627 196466681
    0x90510110102030a050f0f0609010611010f090c09060b041203080403021905060613050f010b0a030b03010e0106140a0602150a0207290109020c0a0204020d0b060d0204090b0603010501080406 83
    0x1a600c5140729003c0000c41c2d29020440b1b90503050080c1c00200e00c04040014401c032a160800b82074195003080c01e00c0c1c1030f1114a20b02c1c81d4010312006182d07811232407034028920308212004106074110707002d0701010305c212611079480302c800384141e201d082d5400407581d103011300081c06407104540c05802801525201d920758400151a80ca0fa400101c0f00c42e0401c13400c001c42e9140144c02400d5049030b0800410462404004c50b0458590600943c01c03180000b041c0d03101454420f411164440a01500a0201010356081300b4081c0640b4000c560159020700540d440c40d0410348180d400300c4125900520708030f20b204600b0040c01c14040c0c406c400440e000c10180001c03403030032840601c1c0e29a03030301140d6a0340486811454407104040e00481086030040000750341a000004911b001503404460060350b4490501c8208001d150191a6541001d800b0800e035260321a264054030840e22581024024210880c0401030540700c00d00a0300c0c0810743c4040410041580741c0d101210308140020541c0320413288070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 196469127 1250 196467877 196467881
    0x10903110a0b03160f0c03020a0b04290a06090209060a030203070c0c0b1803190b0c040905130302010c080f0c071130010603050705150f0d0207050f0a030905101101 72
    0x1100300f146184526001364031140d1020441401c4000e81c5041c03010700c0d0040c0c2e0000c0d15080226005812a909400490248015854031411300b03444410001c4802c10380945000c06040b08039280e81c0354a262840001d0015014021031340c0100707000300740d18600082004260025007000e04005d04100c156040c8000140000c1c4140700a40704042d85181c40d9107401c42c69010640703903070f03d074540244c224448030310126142d0303010150300550000540700a0355440b6681e88150107a640168040c908150600030030880804000700005c0c0294020f006070025440d00391100c4100343e83c5100030284510005003085602c502400980d0702c0354403a0a090091607001503407a00c00b005172030032551200d410b28505a098080704030008001c00d402449030519644613140c840b0001d100d90f0b030264150300c08595503010707200c044400d00c49501810980354002d2138042c8000703400104003100c01d4442c5200340301603004e00080d402c1100d680341c1c0d5914203190810082c844202c42600b82441400405400000400402c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 196470377 1250 196469127 196469131
    0xa0b040b07080c0c030a06094112030703050f0705030c030f04081b010606030e010612020409030203040306061d07030209090c0d230a0522080306010c0218040b06030309010903110a0b03 81
    0x494001c1201c8d44642003001c1e0048015072468000140b215203503003503124200c014100141084405520001d418103180d042041c12031500c806400001b0412039101d415910190040040c00080c10346981c500d0400d42d061b02c410b07100c5e000200800e01c00034502000ca1000320340d019110b00302072410005c0501000604080c40c040b180038070307512401d040c440140e06201d840c0c60003080d84003e224480c90081c94946161403c0c10107800b8135154045801418002c1080380e00555000030f040065542c0e4a5a85240300c03900c4140110701070412001c42c080500c0382c0259080b940009044080d15142c48c428032000381c0c1f10f4170a0f0700c54540c81d0168000c4001341d00740c49410740d44205060450518181010300e0403190300070b200b4a20b00c00ba145003410f840c19500c200a2145034018140d507a44d484140060740c1c0c5040525000754010401c0000d2000d0690321a0024081e91060780c450759141c540508164880c021a81c04600182d100c1e0410004503890000501e00391074090700c5d4820035611070200c05c14039481 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 196471627 1250 196470377 196470383
    0x18050105240a0e010b03060118060521010806130312110405040c08040305030114130516081b090d1502072009040309180b0405150a0b040b07080c0c030a 67
    0x7101e102100d60801c0ca45400200d200846960340c0c0c075424540440c00200e41801340e45a02003022002820a9000380003034840d5244032542c03a44080d40c1c1f00d4000342990710080a4401040001c00d07071030002c03000412024180c5841e400a8000c80d030307482070403042e130704803d00303045d000c00c4012005d107a0fa607080e521891b44034075900c61a0643d2642003000384801e81c1c80d6a200302c2c00700000b200400011903803082c20b581c1940c950000c100041e05441c00090146903a0b29001c51015280200f40b1540c240401d01c0000d00202c2034940c001c0e1a520100c2e0380e1200c1641074a540c0d1007002c10882c4401c3e514100b030011500c28440c51556031510040c1e1829012600810b40c12292401074503158a0800b4081e9035032aa0b41008980c505003900e01913078010b240d50441d20421803100c0100141e0100c0440c80d030403400c0c4d0075101800401c0341d8540fa540704c98103100000e062034002d4507100000301c0c034510524225004c3e19030500029280000d00e9881d00c48a03404a10044000d010f14014150700b980c0c288901410940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 196472877 1250 196471627 196471651
    0x1150609030b1f061808030f04060e031506010c06020c16031401050c0d02070203031c05011802180f0a030f030519030209031e07030206071208070c030206060418050105 74
    0xc1140b5080360103000260802c1c041ca090081000040600500443c0036180107140c140b0044808074a07905941040c0d402c480c415000200704c0e1158015060050011031303849a46410a05400000b8143c61f0194000c2940c10000300c0d00008034a0350191082c401d5643c800d42e401480d0002840c1c20034248181081c080100c9040810200248100182c5140c4000f604c1c9000704694141884d03802514032400c07840702c40440c4c0205500c1d040d1345d418825034803142010001e510007491032401440c0108800d005010441074660076110140e0914420340c6d65a04800c4805900074105030208403038008400a015400034030801c000c80003c1303018020783c1000e44682c84042d110a40000d0400310b001000340c18004040c4180545c044e903550000e41d40b41c2c0e070380e0342c40010501a10943c0459090075065000a90041d00c0040d079281001400f20205558209075561a60b040d140d0b0f1030102d40150a0140240044e407020740411000d14069010781e01d0803800400450030400d0300e54802d03003500d1044581400c070308 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 196474127 1250 196472877 196472879
    0x131e0302040b010f0f1b060509010b0406090e03070609050c06160309120b070c081b1605010923040b0409080a171308030c22080706050304080702040b010201150609 72
    0xc1490b000c0d228948901342420301c2044a8890020610450380014008100740f00301143c5e98803640410408105800000c207010511788104030b180030745015000c1e580907900d4200001105051841203403101d0410602a5240508649903000036042c4200c080c2ca15001e0f0503030140c0c2d81c0e5a90390050045164448203002140c046041c05810821540d01c01ea462444140f0b015000030220000c582d031202c41800d00d910099810300f000210f0380036440703e0085200c01c0c0c10b1780c0c0084c118000b803243d04602c02201d04112468070380c0011103800c00c251040800d40f03488002000d40641414050700041c82000e44002941c40014001034203641102c81c041d12407140c002444808598000c6807880340000000c000d05450901c0d8210007507901c511140501074140c08804252424008811602c103003c02c200c2095070b8283c0c28a100210000600c40d4502c18032070004005400c90051050305c1c0b0454100d00440e040000325020301000c1c0040c54806030455590780340d40220030b11030790000809001039030b035038200d59 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 196475377 1250 196474127 196474129
    0x905070f140906041502150705040810060807030807030311071a070e0906040207060e070b040608071b0b040303090b01180b0d05060a090305131e09020903060c131e0302 74
    0x20748800c0c030040303580c080049003542e80729481143c1c1295400e0b40c1c0400010428076040b414405500c031501a400c100070103200e078559100c000383c820b45844c0810381302c090b0701d034a0360320303040313500d60b00c1040d003144c00a440c200301003020075014042260090501066000042700d6105042d84681400c4590705007802003030040660380a1801e5100e4050b060101081c0c449d80c002400d580c0e002000f00d0721807500080c9040801c001ba4210400403220071f4226410341e512420302e20001e030000c1c01031100044040780000c0e0ba05104907070780b16502d00703410a00500c1607016103c0300c2900d600240141c00b070607192800d84000070020350029001300101e0020a40b84810301c40c0f003c0540708040541ca01c0707020f400004501203140490140d40041d0400000070300c2d9095480d00b92002e002c3c40000044000d510100051041541d12100e50007514208400d071176980c80741c018000320702944903510307019400807001035a01c128100c0141503c0c10100d64040d4120303501e0841e258151113240101803042980e035820421 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 196476627 1250 196475377 196475387
    0x170c070e160503091515130b01020c09011503200304030e090601051315020111030406020c0c220c0201021308010608060a060305120a0e090103030f020c03071404020906040905070f 79
    0x70002140c601140345061100c0e880d0340c0e60f1202a990017072042c250000c96180e228403a0b840c0c110368800f0740b500c0200c035208030346400140b4203c04504c0c090300400304001120300e4040a1303141611590204c410404501c06021030090103884150070b600360240c0c520080d0a001000a107100781c2c865901c402141010340240080c20902034441c90600600344485429418215442419a040c210000e00d8000c4108800c0380036010320400f02000314000014002030103203980003415207444110032907510b04400c02c00e001c0c8820382001e41d4401004582d0f1a18280079084d003011403129034a100142c01c180c1c0500a411007001036900030180d44c2c3d520501000000d000340051a40200d4001e4204981c40c030b5511400e0311100b02d450598661140000c541803040e0244403048446003028022080380d6849150103440404c040b501e001c050311515140b440103150004d140000d450f15407494441881440f01404041d42003007141c81e40c0b0100038000030a102480d0312801b4490704d200c0e40c40580200020034041c0c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 196477877 1250 196476627 196476661
    0x6030d02031306140906030c03010801050105030a03050901030b042d0b0405070e0d06020f03180f01090309090e03070605070e09090a2d0b040809120613170c070e 71
    0x400d640042c801400e001140b9010003045518505012003404900d210f180303820302c1428195540004040207201c1e4859404c03010318180d0b01c0c0341c0c001b0010360342c8940806039994003102e40180051402c00810225500c030b900104181000903001042e800d50f01d110110011300d10035861041e00004851025000b8000d00920211404c1600e04100340d09020b030300102040d80181010f4001d05041641c00e003041075641c111107210080d995090740300d080100540c48140220358503c00c0c40d108066600c16615010b00c11036103a0307541502c40000c1207151158490140100d25400d540c0b5000c00d21110020030424003a00b0f10442e1503070b8500c200e5800c0b200410070800005402402180e000c40c0e001d0002801e140700e070308614808182900800312030b0140c0f01340100e803e000700604200e40c100a0004100740311024104101c8d0031502035a240c803925a00725981c500480e0056196034400494402003450140c82c87d41c20100780e41c11629205214032000e1812500d82e1005c1d51621458040017400542e01210300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 196479127 1250 196477877 196477903
    0x90302060a0f050103080a050723070302040c02011e05190f0501151704030e1c06060509072a02010e0a03050d021227010e04060305010b0406050d080304060b010c0b0f0603 75
    0xb011303506603200e9503080c0c010705040c80e084c010002440c0c4180210b20700c050b0b10307107a1072298075510390039094070f0651620201d1000f00d01980c06c04582069440c018001c0c03105c118810050303a2039440010340c024001d0070001c4d013480c4a80182e0980b2122000050181ca02103940d41d01c004101540761200c5010382030545041c1804124081c070018240782100c90032203421940610300720f041c0742016800501741c6404060414500e1900300c101c401003203e560008008c40e0801c55503000d15586a01c0d0556551100c000a400230001c064654011000704030710ba103198174018900300401c8190341000c0b580034895030300192a5a440305145510080d81008414030484010032068200954103011340e00d150580b02440c9403d00001111b01c04a034440e11048074220002071042c8900740c1d0702e0030554002c150700c0f50582d01403420200c0c0880d1724144a0181e0700c5441d030003481c03a860340d0f40d90344881d0001d10314103507a5030400c140078418a02103030f000e07100b440c000c41e00c00d007140c04103041a13400c25140101480e408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 196480377 1250 196479127 196479131
    0x50607030e1513030c2405030604060e01080f010c02011a01080405010f180606080309010c060e1f0b010206090a2d08041508160807210c05032707051c06090302060a0f 73
    0x49101c1d0340d41000e540001b4031741403054494451038000b401502c056004048011344c92000004c01c0080000c20103d1801500001c21500381803010407403e0359508181d20321744042c42039040301d00307521450710f8683c800d0196000144544520311b0840a4445400c0c0c0f001c40e1a20704c84050b000d00100d813154a000b01800801140f800310010b00203040c040d45040050640c0d5580c40e0b48009001081c440f50656039a010500c04109440301004001000342d05c030403500502c54100003c400c82d10000b40d044a00d41c0201e0070b001c5454134280482d122200001c0d40c030441d4160100400001f03002e01c0080c0014001c04806841e11072640d400041017254000d201f401c480202d0f500b011485074201d51080c0d0460501d2a126084200c0280725040001842100d246050b2500000180c01980b1a02947c0201044800d402440ca4003c1c541c2c544c01400c0041c00038150400340341009546004003402900c072420501c031100000c80380d12804101c0c0c40c6c40c9030030340150704403c0400c551b0403041d104038444405501c0d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 196481627 1250 196480377 196480409
    0x1080c0705210a27050f0117040818030307020a090510030507030807110103140a02033c01081216060905060a1409370b0705120f01050607030e1513030c 67
    0x4c1040e01006209090140ea50f5860a510b564440d0744c1490f2101d00649554895082c6445d0030003682d802015820380188440303600c04080d10f008000c5a041030380042103643c559082c840da1100404c0c001d0484042c610454600000085d0705000c40d200842c0120300468807070314035080c403003060002810340c58101858403240172003512038901c806401050b0781d0b100686a035903610600a6011107078110700a00ba00c005a6142e0104103040000020307908000c006c0c0107a40e0790700d04a41e072402850f4000d11019401e2202031040c5442d5904041600c1c002d81c400306035031500d0f460300c034101001a1107d0a00c1503da82400c882c4083e11041e00b41c001c0f0310240280100c00c0d98880d04901383d8444290141040c446502c030065003003042c0801007045030060308511250505100251965101c481c0000302a1990b000103018800302c802800e0480300041c107410700d4000595400c0f02d5080180c107000d54002300b000880d481c1000c42c03e025201e0350510003003401a040c21403d141904600903802004d0034202902 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 196482877 1250 196481627 196481687
    0xc0604060203071403041806090c020c01080a27080a1e050708090d29090a02090403050c100513050124180608060f16020a0201080c0705210a 62
    0x200b00c40c3c0e4240c02c00320f21401152969a07090461040f0f81c0f19584040040002c800144982d034043c8085030f0b030750901001604000c120503626880070100301ca0100d40707801d00151842c070441c2c025205001c1d10a103a90245055074403103841c1c07400315240940318640c000c203454081d16040f201c16080c00b00c0013000078649040d4034034010724038450070038020212a0045100805600c4d400400003042c0da014041c0020b000da000d50714070a400d00701504a400340f160101150080c0000302d1424415a00075061025659450b101a90349a2001c580402d00d880340002140c107440e001c1c441d1900440c00485030307001401c91414500d095440050008110100c2d03003060a189400c803001000c03c80c3c818031000071021501c9a41800108080d0b48040c0d0680140402c0010201e90080301c1c910441240c0210f14030860302400c22a03980703103a205c0090200c2c16060100386400030440281c002140b10303604403010031001c001107600032151b0601c55880d451000c03900c1010240c003e036540e00024071032840513010b007401d80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 196484127 1250 196482877 196482883
    0x906010b03150d02060403210e06040303030c3b090906060411040902030708040314070201020705060f0c19060c020d0906050d0b09070e03010609020906031f17030301080c06040602 79
    0x14019003202d40003005490030035140d10005540b0742e90001c1c80241c03202c1d42e0f0304003411610140c0c1c40f00d0480c001402001c50409004084203402e420b406000582401e0550b0760903402040b0300190341003804141c5441540e20703070030903041103d0300da1201b1101c85d8480c0340c4610b201950780c01201d024412a2075004104940b07200041080d1b11210403107012039480b42280b000e291601c200d800c0380c0c8200d0300000400c8201604201500d024600c030743d0301e410442147c00351613040c50080d04002801a0080c0f0350410441c134141c0098241100140a01d03403078403034112032462411303505003804241102c0d40d510220500c45c0790b1140b00c0c4c0106150026010401e80d8920003400504a40178402c181310010030f001840c0a100c0e0312142400714003810f88070b070342d003848000034024400450200c1c2c0300c2e40c05c102001ca001c1003d40252004c00b54003400d01c0d401c64485509080c4140035006d0039890208070b242c2c000035000c00341d079000c1215003200006103a4a504040e90a401d00210b440700f1401280c0070801000480d03400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 196485377 1250 196484127 196484131
    0x30608122a030307021b01050702030a0f02060d1802120106030c0e0c1918060f0c030302071a0c070308070e0a0302061c0c0513080c0d0b0a09021005070501050906010b03 74
    0x34800c45994061000c0c00d422540d040420300d0201d920020042000840e0006148410710358180d2545900420320360044502d4454100c0003505900500e00c0003000404500c3ca02100e20301c02844241025203c04100e0111989514003403210000f82d0300300740560038900040940400302c0300c001d10456046850f40c0c008441c2c10b12420000b0401200003407816080e000a45280700c20b00203105c1051510312000400340950390086c0404c07c80307002000a4424005c400245201580707849004447e1a2a2010780082d000030800f61820100e801ea43e0103070000c460003040c46511000c1189840340141e08008003011001003509040c4859603461074406c1e61034000c0c20080341e6046070501da580700010a01c1e00034184040418102071304003240840e1150308100a07000c1d01c0d0030800c0f0702c5c01d420303a40d441c407565503009000040d800c0a1000b05000c08640c4503c16140c2c00402003001180000c40703580440c101c050440d81c02000036802040e49401c1000a000d1650044500c60080101e541860304854980c480 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 196486627 1250 196485377 196485397
    0x1a040b0d08030901020c07030b06010e0a0f120f061815020301060e15120c04060f03021903150b0406081608061f02010603050a0f0b01120309061206170d03060812 71
    0x301c0020070683d001d40440b10888140410b91340001d5aa1400307450440b0155903482c082a016100004513041c000043c1084501044400e40624941a084c44068808007020354144102c0442d1002007110780c000c920200183c034010881000c500d04080b445100496144460f01e401080100842d5500c5080a007041c0001c85071183c0c8101608810106407041840d030548102140082101c0c1c441d6100181084030000e4450742d0070343c42d115a04408a204100107204100540b4030801c05007442540582c0d01600680040d50b051a00c4081c0720155810503130008000545801c00c10a00000340b200ca84410402800c00003042d003440e800042822031070303504040d0908600e410000000d0300c01d402c030f400159009815144d0311022400e205031005091481610100c03203083c00003480c117003110396050b031003901075940b00d510034105001114285031200e10700b02040d84400002c600800b00101c052a103103115001040e80001d56900a0182c0700982e1004d651500814103550062074030104803050480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 196487877 1250 196486627 196486643
    0x309010c0519031d0109050606090717160504030c09020d061403060a05040507050a12020f0126040501060b030a0b0102160605040e1803070503070b10050a0306050604110a02011a040b0d 81
    0x586130201c10109491070313542d03001541c00d0015400520001040d4540520426030705642503a503020800d41b95a144505d2902c1c0d902803a000187c1d1440c001c0d00859982e040601d0110b24281e40c2e0f840b9040c3d05c1116410901085030700007161518854184210341c01002286241d8400383c84e83d130700282d1200001082d64540c07a464100003400c01c0414030841004e0b00c402402844660f071141140d0102d40f0040c0c0702203002d8614010400301c19070041d519210742038039404005484000641d03403840d18071406441152990741381d0601169400c2d031070014501c10f10f0041c000007004400d03000024681311516003100d100c07001008003808080da0100c11202503a41140103403120341c4502c210300310a0507884250700d625000101d81c110800101100400c0c5250244082c1c4216460303095280405084501c075090b84403c402c0710400014016030070403503003c1d800500004086110a0446500b6480291500c0060355200b815001602071707585031202500741603504101304070406021840d8a07030040c42c0907040007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 196489127 1250 196487877 196487891
    0x504020d090c0f0f0b0405090711010b030a080306210709020a050702031203060312040506032d01081e0f030a110a0f050601090509010912110c0a0b0309010c051903 72
    0x542640226501c0ea911041400040395203001c8034161a6943c090188420600140059074801180696058031001442c1402c4c40d12107a000380d5040303074507543e0b110301952902410162560280201c1c0c100324080c05401e540c81c68802c04010303501000800b503024031409902000400600083c0050640381c0b08000141e0300c040302901a1030300e00a400c0002e5152260f100c40c3e06500410002860040100740c1c200c458500d01d8144000d51801113000e55a0800020310000b0b5500d071528002001d140d20341003044800354005c40c07103990742c58001d0b0044d0100d540925060007000e01003044014090100101500c50340c07030070b107072040e03100d1240c2c4515008210300030b0303410500d01c00c081c04080d40040e40b100988124405c907140c1075440d9403003441880341051400c00050b6004078180510202d07603a000c141408400c14160301940d00c01c1030501b290b543c61050640c0780920b0b49560214401a00b003481016850f454421406030a45010b04001e00400c142400b0140324050101c40a82e185005810003051907 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 196490377 1250 196489127 196489147
    0x90402120109150b0d050d21020f0705151603020d1107031107170601120c080f010b0405070306180911060d0501080c01090e0c0307021c030b0910050a0501140d05041b0905010e01050402 81
    0x181c204004103208061000590392039060300c0758012f20741c8a104205481c501c001840800700c4030207049448505105c600207258248034401c0c0e000b401580755000300010303006501420a8200e030020710084001c1307001c42c1800c0300700e680204a040c00034010500d20302c00768654083e92030f84821040c4280140d05503842032440404c413400302e8010180c03808408440e05004a51a100e000c0c14603064014010752801c000316902c28424090300f030949207151810000f81d250102b80200400300c100050360002801300700c1c5445070f41c03190010015081110004203103941041e08183c00c3c12192080d4905101c00000c00300448800103c086501c0515414041d440b95070310030b800d0b41854280c04901c0d0354854041c001c1405107801d1f030302040840340151402e1519989440d41d116981e5954081c4540c020341d0000204601d41c400d0590004511a2180807401c0c200d03440100016104d00307840858030f02002003030812811020222880c0100840101444107501d080341d95160034506010301070055800250391901 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 196491627 1250 196490377 196490417
    0x5090301060801052707230a05040507181409070804031b120315230301060308130806070201050f131407181d0c090402120109150b0d050d 61
    0x24580b0200a001d1454812102c5080f80100360003c2072840518000300a81440020200141c40c20000401c2d19880800c54000f40ea01c0701c0d2040f65800340c0320000200d800c0e1120f004803030084200f03440301d107100da00202e140c41d00076050340c010380c0000281c050301c00a2030303503a08c8510742c0090032030410a07a5601d03a4101249c03403505c2a001c098860307510322007440400108800001640030b035690704110200081042000c9410700b80304181c500030b1000c0d00105124244642440f4540000340000740003030f92660342402907006030000700c854644c0c40404111400c001c0c0209640802d15100800c800c4c0b4003140b441d0740c4004d01803c2e100b00c1c400c1a0710745004000541412120140b02c04044604441d6078404001e03a0740d491007028000c4901304011500c00c0791081c0000005d5040140191610f401075001b400b0500d0342c001d20584c2d001c040e02030000c0103003c0a1244044042c014488050344041d505c0401c002c2d98900b0180e14015400c41180d0000b1900114500400c200319251103a040f00d050100c00803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 196492877 1250 196491627 196491629
    0xe0a02010c080f0f03060414090c060c1f060e0f01210204090501141807030b340c03030b090c0a110102270907020604120509190e0613020901020d0509030106 69
    0x41d1490f0001441100310710750303001440c4940000c172802d000c030340f01c040b610b05924a0140c0f45040584d100c242500c2052400c003014210000034a003c0311420042441d00807034912041c0950a40e15039920000e1002c810b00025030f1b84c0c0048154051a41549840004034800710668100003600300410076aa045680b2074108104143d080002842801c1f10140207111110003030301d483c10b2758032000840504554001c030722803086a401c100c1f03100321569030402d00d2111071000011b41c1d640360104408075441ca16442880140c00689540b200c06501c424940601203da00e810307510b00c00c54030041080526100007045810321119032802164244c052801c00340a405410003d209100891802050b88042403181c41d0148c80212a085829200d0300e038249e8584005403030180c2026000d540e1344041c10300800041001030303805130218010441e0741c0d00ac030180d405503401c420618541417080c84214546000010b070182c1a2140451034280320303800103541c0c0d1a0743e0658400b4001c0106428420380d0b820360104e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 196494127 1250 196492877 196492897
    0x30c0f0b19140301030305092d010804140d0c03020f010204051507060914010207030201050105040923030910120f27020402040915051e0d0201110f010e0309030c03010e0a02010c08 79
    0x50b0f1256160715000c2d2a0782c003c07141e2680150303c011400f09440c602440100c0080000d40040e40030300207100011510901c000708150f62600300504150005801002072080c48801d6aa51400c0c8143d9460001c0c00c2041d200c04550312680103020a10071551004c0454011000b00d0202c10b40c1c81180d8a040c202130030921001078000c04c2e51138201a1501d1064004003401c621a07402000240c1e240c1c0100406c031842c0650151104e020a9405809207920034850038064121800f00ca06040e10540040c40b0908030001040000b1800520f42103407040c0390046071560030540d0014001c0b409500f0514800ca440c1c040480c2c01901c4494240c015911103030304a60240c8000e1400388465003c6001240c0b084895100780c4d4010406005114500f160f07444011004400045c40e1a84000c210740044400f40341180e005060f5024050110707481d62001d101c2e03442074080840c043d507103030480a42014107015121014034041e906180d0740400c10079000c14010442d03036090038001994030702800c06c29000d000780c080700307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 196495377 1250 196494127 196494167
    0x6030c0a1106010807050406050103051009021e0a090320090f070504030f0b07090b070b06060304020f131b0302120c030702070f03110f10020a030f1b0804030c0f0b19 73
    0x130645120100343d0700d040d508141c5083c02480c2c0e0764001101111802c403a0a82c5d0f08414140a0000c4c5800d600180240708101000c003072060f010001c0065a60300c00c941c4440030484002d81001041045a1b42c3c40201114811079410f1071402d00104100c240010034580c048121803000901090141c0309880185402c004a104a01411302c1c042684803402e4a4100c0800c00c5080002a201c40200858201941c48600744c04030341c03586c0090110b15000070b0005caa0004051045003400d459964806d0740030700100d2030201d8100000000c00040794220a03444e410140100104100c10300c110090ba41c1154441c80344942eaa5650401281054402d400120610b4448100007060000083c0701000d038050440344c10070228100c0d41041000680c42040300b000d81c0040d00c1c0440031900650203201d21065070b04048035407684040e00d441d0000c6250a044401c02d83c082024020703c04841d034440c01428040d0042e614080c0bc1142c0000580208070b240c8142201060300182c03124030031005600803101400300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 196496627 1250 196495377 196495379
    0xc100510080a05030c070801050105030307061107080c060411040b1c020a2402011b0c0807030e03010e03070b0901021602190e1006020c010206060109090f02090a1e06080606030c0a110601 82
    0xb10070344a922117000802d10303204000003c14100f006214003412075030010015482e040e1f15580c8d51001c0c050310700c95100c03581e4090001602081089004107003408a40e17015000c43d240602c2d005c1030b000b19803014580203903e054400078280d261000603591908640301c228031110418030001d00e203980b03c5e410882803010000d850901c003442c001034180700c5034100d80083c4143c40b032040038510f21004207044c0b000040c0d06040361101080c40d110081103064028a000e03d840055840130074251000c0d403a40c0c0126500c002600c009210100c102e01c2c2c0c001007110700a40c50a00b4440156201003100080a0700c0b13030551400e02c0c04800d02140032207000b001825110070507841c10651008030120248504030141c01205514005584081043c501c038520584503005020f080807180d100901d00c1c902c00244495003048004090b580b103041b44001001000c85003204440040b16420410041d40d02440501a500041c0000c5546440a40358800b4003c4a80c80c1c1300d1181d1801120682a00600d00c0098060200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 196497877 1250 196496627 196496633
    0x1f05040302030d08060102100507120e0f07170606060a0512040506040b0906040b071404050301090b101707120c0e040c080f031812010b09010f0e07050c100510080a 72
    0x180003224001c8003038503500400b0703242c144da080701c0444007a40141c015174845400c103800c0d42e02158005202e071418821020707500041808881e000e61424000303501481c840f880b00c000c100030384805400d04e2484204c007100b030b865101d6501d50003d071280b80310340b001055940d40c46100704141d07208524000c00308440c074101810a661640403da90503204c0500c3e110019910b91030010301540113030351080141540c1e560f1a50112010030b100d0000080141c010040002e16507002d02030007500318040e0481d240503040ca8480108103a019034402031401010032170b8a080e8483c04140704040b2005000d03203a0684803a0725009508040c41e4000501d41d001020501c011b0080e8224004169a1107070211403030750050000c85075a0b8020600010803294450780d64030b10f103090042c1c02c070041500703103000401d000300b03c1d200140c03a022090b00329046114001c0c0080100409202802d50000d005040161405104980741e5843e14001291580b5080d21000450220303680280c210700101864000c0da40c410503546 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 196499127 1250 196497877 196497887
    0x90605130221040c080c06161101140708030a0501060c030210020706110d0507120506100e27101d070503040c030803011205011a06070f05010605030a03031413030e0f1f 74
    0x805074004a1080507004030450404900719200c40c0500c4070003d9008181d6681c5103030027800082c091b070420000002d8030b413160300c010019041c0d80f807044a1540d26841c2c164158802c5a90580c0400304004070625500c022940201d0f1b120309150100f40e0160781c030b12540c2031800103028481070f12010b03520005420500f000c0285d00490041c13043d035880003102140340c050f52050314025039038680d0100c0c02d03c4662111a00400d816a000f80016107450007d07843c8411700d40c0f51410407070034003542c5524041000703500c031840c01184000e0314280007000000c2c07800000e60010b80d007004003403d09100780003000c01d00380700c8042d0001c4001c40c2c3c4039040e59500c0d0b0b11a100f000d07851202d820201c42039803c06141c64240841c003280380001c85000341c0002d040c24555203d60f5aa9859130000366015541c901010907252020300250108500035240864141081400200350381360003003200048400f0700c0800d5001982c007002c007242c0c10904803000102604c000d80024185003116100e9441d03e09200503010240ea000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 196500377 1250 196499127 196499129
    0x4060905040b0a030b0703021c0c03060302090f100e0705090a030302030d0b0a05030a080f0c061005010f0509100f090b1b0105010509070507020603070c08071b090605130221040c 78
    0x103440030b0000740c6801e020b1218904403400002d01c002c003084002000d01d40309501414803a0102c4241c030300d203a11008625401c90b6128141d0f480020380710b00c5c1c10300c10f42c02c020354102c1d04043c801e00d01041c03500e001078202d190214280104550444100c0c0801c001902c1201660280340d0000c20345d0070455901c1c500a90b49501c0b100200c0719542c28882103800910380681d041003202c071f000e0054010001d644d611203c1e10fa12141401ca241b1005100b080066a82009000c0c8150192440c0c0302070541800005405111142d4000e070422404010719881500ca0010f0700400c0ea1b16400e100c0d80c2d2123190b5800342d90400098101c1d4481c0c460100d400d02e50300c054020700a01246c9264003c108036600d1f4401e0185004085406501041c82003040f04014204180110703400030184c80c09039800040d50303488500c5a880214162210551440c062450701130300810380700102030401040020034500b10100328110040e0801c00300071a40032800344051030705642c074040d68407141003030301e202031034240b40018443c801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 196501627 1250 196500377 196500379
    0x6090f010506040908040b0d0212010603090b060a15120204080d03091106090901061b06020f0d0e1b040915110a0306080105070e0405040f2001170105060322020604060905 75
    0x1c1c00702080d030900b0648034003644035402c01401468507061100480140e481458800b0041c0d50070070146000103400041c1e24042c04103950041000c0a09060000c8003500203000d0f17600c02c031200e0008003c5000e40c3c550380d0030080d0342800c010025082510102c1d00038015940b11301e03ca40926000d0f00d40e0b04c0d41c141d024110040c801e508031005030305038134280b12150003000304254200c00b441005020392402024040360002001c1c1480043c04a143e580d08141c3c0c0110b00c0b40e0741225800b21303481424002074028005d084940d42d005149070320100f0341114200008040890180e41e03604114424001a00884100194804c40505c40200c00c100400c81c680e00a003c00e0f40040d1409034003040c106018010240200c14a41d0392030000d88030301081200404001c0c204036002c035600c008139400505031861414207503030350407009408801c00394005000c608082e0742c0000841d55850051050b641c4006c150398200c0d0308903e440c803200c5105c214420f2200b41040c00039600c02d0340418006101603201c0344400650740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 196502877 1250 196501627 196501631
    0x80a03090905040b0c0c0f030a0806010e041e091e1a070e030304030816060c050301090b090105060a110f0a060203160201091205090d0213060602061e01030314090306090f01 76
    0x303650200c00e000c0b124291030003000c00045a012030051030000010780795800202003507490204e40c00a000340345a005407103a00118042da010032001d90b801040d5189090f40a271030501c01c80b409100e4807201c2c1848140c40441255031150020305002da0042d4005040c222108610460005824048100d000c00302c20281c91501400010b5100c610074040d03488581d40150046080500b180d4880c41d858106014030064001e03072400c031402241090007448014059915110fa0301c4d41086000f030182c2c3c0f1154422030103145001c00420540e2180310484130408407624100c1d01400b801469281400350030040b891a5103d4808110300f4001180d00850060141d52154805003a01d41c40a9080e9041414050601c0045507240944103008070020328080c64014103a07109500541c0c00290784410700142e00342060390b25070003480007607010402d16400c2103c00c2c0c501041018110146200d401050100604103c2442c0c405001c405507102912a0040010290b8955107051000310341d03074904031074240081e98 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 196504127 1250 196502877 196502879
    0x603060603030a020607081e07081b041406030615070506070813030804140705030f01060905060f0607110f0d06050a15051008060a0512030a0909050123011404080a0309 74
    0x114000089841a00f640d0300035005aa503100d4059803050b01c014034120801c41080110524441618622489008503807201c50842c10076203c600386218070441c0d00161113070704110601880351910401801c1c2c010490b2501c2c1e5075540c6e480802c0c1c1d41c000300c40c002460084041031140802102003803042c0b04510030750b42c1071b010b580c1e1401002c0740080384000240115590a01240c0400c02604180c01c10411181c00c54a07a6076407040801d140000c800500007a9940d42c80040c06815114010381c2d82008040f100d07010114010303000524144503400c4014000c048504803c250307912440041200303002c0040c04611560030030f04160018260489030414610315100842c15113240d0605100c1c141c542c0681035010201020b035042d00e220750003600c2650701030f024030342c0040c0507038540d001c00003489504400f458a40880d41c0c0f0182009130380380c1010ba10b89040c1001844603401c6000b0512810200c0c040150b004030013a001a204c2c00c2c010b178800e680303400340002e021a40c40800115205068481d5551306425 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 196505377 1250 196504127 196504129
    0x70b0903040b0a03152402060f09122104080405030f01050106050d0b041808070b0c07111509090109021b0105041a0403121a040509190318030606030b06030606 70
    0xe4400e42c0602c0024410920040703202c144241e200300308540301100396190040c0c4034071000c40c1c0c6411032041c200e418058900d001c08216410b001071500040c01d000c60440508004120603200c2450b4502c900103514040385106100d4140790111900c0ca1400c02c001c410350400703091515480c1d009004940c0030340300d01851480c84d12414480e1038104c541076a00d550900ba500e218160103001e0000c0c1c0240e20907110010301060800200c200402a48902031041c2d40f12071510b400c3d049442c004040310914601444850301240300d8010032207a410044500540c110800105200180038007090301c2d03000b8003424004104403c4e103500a1031401d4401e150504d209800526207420380d6002c42d03008044a40c028000c0c6004640761032101d030024441d09001c0300300b048559091046484c40d055200e810b000f0f80810144e0784c1058030032a5086944100034242402e811800d82d440300065120007400c1080f00350954030101525542900556400107013403104554034103241a01e200700741e0b446442030090700049402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 196506627 1250 196505377 196505383
    0xa06020a020f1903150b010905030a17070305040e07090807050628030204080a120806060a05031b09030106080601030501110403050d110a0b0a1406010327020a080a08070b09 76
    0x41590040048008469440030301c02da46507446180b004000f03d2100100029001e8040707040c4407800030328001140d081c1000010582480d581c08a8002e804c4200804042401402c03c1207000032554040760fa9407040b460203d409104550182620807082c8c000e00c003d03107071300100c600b01302c900c00b400314bc5003242c64004115452240c4a03100080d0282d0042a0b809050200303465200300003c0c1c10014209a034403041d0b181054001c401c00c541d030f40c02c1000e10b08071154003d64a00d03000744003a12072038101040c515020f402440090728154414100f2a82e8103401d0320702c5002c50b90421805002400050f665502083d61400207020440311355003840c1407051554601010756003202d80090040c003a8004400c000d854002c03044c10640014002c1446c0b04d4041081c0b602c0c42c03030140d03182c0c03100020085a4440c6040c07041c1009058a0304040c10401410110810f03030010000440c076403079511407100003074800540444110b030300240c00c60240861620501401c0b5007e083c00f140030f101c009085548488400b52 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 196507877 1250 196506627 196506643
    0xe030609061006110c03010c091806030b040605040203010605220608030f0405011404120818090705190c051b09010b0f04060509010521160e03060f091014060a0602 72
    0x11040000b200c01c003c100d2040c44d001404101c800203851304803035610301107402e542d00340442401044e2120810005c4082c00301c80d011280086120804c40103080d0340d41c100f00aa00500041c20750398482c0c010600b5942c081d48418010503004004881240b040c1d8214051112640700c040500ca103440000600f016010003252501000c420301030345820b09040040d42c4524500c02000c085907414800482c4400c00c00c000503c0003402280e01d640c894480850351041c00415500c2c4e280900000c4007800b03030309078001301a45e80c44885d01090782c10030b5a101108449005070140058002e1240100f140342c50720b03424103281c880040660704041c407a0b0300c401e0b14903920711400c410b1803092881080100000c52058024014141052501900e031103820207594600c0212007881c542582104001d0020203d0200b40c0c4d068084d0603410150728041413032000a031210030007400c2e208856510400600240c000b80700d05103508a06035030422032010102d00e049009182103452900a80064101050640c00081e42d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 196509127 1250 196507877 196507891
    0x705010206220c1a09040f0b0d120201021c051602030c06010303050307032c011d0c0607060b12010c0e0904051e100207030302120c0403030906081003120e03060906 72
    0x304001101c0350781d810700340c10301800903035501210300000325240c40710401411110111aa4950320f07040403038100021503c800c1000c404140c0340810300c48c4203484008034100030744c0d007110001c4100344017210181c0c003910600710744200340b09040507480640c112590101d4000c003c250305030541c1c1510f0840903031703483c407030086211490f901450041000910030310045601c81d5a0f0315021822040b200058000e0600c2c052040c0801c40801c6d140b130080d00c07000d2042041c117009102c468401513017481d615644a2003140c2025008010000d0801e090060a0f0400b08482c4006046406079582d040b24040c02416043c9048000500d02c3c203910380c0503d03240402c40c0c001d40e0018041c010314080d4088149003182204001017150080b405101142180f0748003800340140030391005070755149a4045061207075130091401500c00300070320040c008240d03c5030b0000c0036500582003074841522070200c2031088052950005103200242d603504a0302551000c2c0440c0c48500c00d4023128a640c492100c841c0d104d80c4116007603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 196510377 1250 196509127 196509151
    0x81005061e0a120b0a0509010605010c150b090103050f1009080901081801020f0a03050a02122e090902120106060e0f010c0c120317060d03030f021c0e0705010206 71
    0xd0300d11040c400e420011080005010480d001d503640300038071195034100b03000e4410352581805c000b40c4132041d01415034442d200360b000300131090408001820903038082401034914940c249130881000c2c1c103540203550403440100704803515a92490050b03034640700080209050701407901001c000070b04502450f900941c0c404402400c01030b164004440401c0028002a404581c404090069102c20310013170003520f0181c22107a5507040c0984018082e07807000b811710006c40d48100403203080340300401c1c109a0004070260721442d03100001d10f00c80c59007440c00360b510000c0000e14280010318400990148113014421f03100b030a030324100085443e00b224910700c10180495207210038409117140103800103c4119050408104281040c2c444000182282d0001a2482910042041816040f1590070405c04030461800070618140e80400c0c010071108100405241c0c407a0801c6100352100c1d0181d428403500030200740702c00082000c001e07000d8212a45034010b80d0140c840d010800c1c1d440400c02ca0701c40c908200b10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 196511627 1250 196510377 196510399
    0x12050103030e06030702031c0c0207050603090628060603050103020f010302090d03082d071e090b030714030717130b040f0f050f0c1f0e0d050316060608100506 70
    0x501103c0e03400200340b201103000c20458103044000241e50014452041c1800060707440800401903e406040d8024a00c00c140c203000300440103400088196000320300281e000101c0c5842607001c0c460521f290300030700c000742c1450004900c5550541c000c80c1240c1c001ca603004031054202005404030f1080040e00c135000200842c141000c2401840503907007001d16404401602e0300042e1001829080c0480900c442048250070300000c2c40e40001510700e10144020310241d60031424502034011641440f600c000004044000f89216005140b1144680c2582400d10758134139150b84014220b122020030748140300f032000049942c50106041035080c55510280601c540d803900e855903400001d9040e0f04842100d030b41100000020818095000e0300c4032103030010403000c8800010403032040c6141229500c06c0301c280c007142002990250b00803022b52005d540e50182803059090080c154480c80f100341c0d14501c19092164204640c1d54040c8040314854002c1d903d06640c2524084141c4d4025200c20f40d05c481c1c0303820 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 196512877 1250 196511627 196511629
    0x1a060609010809030913150503030f030403230c0102090102010e010e03070f06020705160905060f0f0609012d1101090c170c03010c08060f010c021f021002070f0312050103030e 77
    0x1051a80050182e81102d081c101c45000244c11042c01c1408241410784a400c451a40d081184030031000d440c040380072b18105000c3c04442c01145c00002e1014080082048510700344115185540b100c200c200c4113820799580e96441701c1c0e4041d521040354680198605800c88a246034103105008201c51480e0280d46024156203440c1083c13a0320020035100310b41d0801041000800402170043d0f018004504000d43d545040d580318101c1d0001800349014071a143d06072026580c4d503401030420200101e40950f180c3c0e0042004a4184e0030f2040c054141000c6202c049441104078621840541c40c20364500c680c0400c896032450a03030b0b014050062030045081410b01005040600a1a1910900c0203c031500468140000c1c00d503071000d00030741c0100d20b80006110f01c0b400c02043d8144101d50a09007003146108560100e019021148044d80c4070f1039400503417074100c40c428003610401240000d015502c601050610f0681c154240c001100400d410340c0b140c003002c80d43c0d0b00840b8102ca806807031b12034000b11144 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 196514127 1250 196512877 196512887
    0x3230d050a0315061106070c020f01050307031b270317071401050103060b130903020c01081512030309072103030c0504050303071b0504140a090f02090903071a06060901 74
    0x1c0c40c0c40c4140354507001d0030450007184088038402051181c2d55001c5000128011904042c0043c041d201004180301003000541c694035105205454207180032992a502d0082c128024200c24122000c04002d400100c1e200c0e9900c4081e84080700840b11007526265000c050f0301101e0b40042c8002003c81d440450301ca013010507454043c003007541c01500b1129518884e0a109801c4030760980084820301c1e0b03984500f05103414080d81c400c40c0000b01410400c0b2051003610701a40d0365440c03203041d42c100200d400025064540b2000b07030f0060b401004c2d0003141ca28088600c250340300c0e0012aa140c416104000700014a54070340d1405034110310007001220459a800c0c0c030100d000d410381220f00750910031700b0070001403251002c0009040c69406030001e25091700b40313042e840e2a80c1025512242c0300d14103100707241511100a44045401c0183c2860004400c01c0350f1a0400080b0004000a980045160100680484040010300104d403141c140f003107500304940013140c000c040a07a000c0350480e03010301040c070065002d2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 196515377 1250 196514127 196514137
    0x5090a0312050705070209070306060212120f07111204090f1b0c080415051e180607110406031202060907060c0204021b01020a0e0f030a0b0f1b0304060603230d05 71
    0x13860000c0c50318034950041100c141c0f06650800c0065907400041110b42c0c0d05200d944580221040400c0c5403841d210281400560050041e0300c031840d041010825a60107003200b04889240d01e007d440c1803211f0f0140329852a0001d2140c084560300300a0100c0801140d0b01c0b90f88085501c807200300e400900c1042c001ca41c0c01d8580307101103605030b100b04008119a02d0540b03103024120210b50346c02d60384001d102068002c822018021488111042c02450200905d42008042c9120306a400c241c07104a68100810014940791459400034608180031080c0281c2407002c1800038010380031500d0030380340d619440342d48101c507100d8a400551188280310041c41c150f0000e02c1030362003880b0741110407074264404a003241d000100703442c041403e488580e200350504903181145a03001314060488a43c0320344a40083c0c80303008180c4050710f0f01c42c1c0000380180182c0c800b03c0a00441c9100c50325140c1c81c01e49030440042a1034041941c0c0801da4080c1e0540ca00801200b26162405803000383c20444070215040d5115002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 196516627 1250 196515377 196515391
    0x1806031e140303010909050d08090309011d090c04030201110f150a090204050c1309020f16020a03050d090e010b210603011e0c110303010b220909060501030605090a031205 75
    0x4100001c0301802003080514080c0400540008400346589051498510f80c8507a40081c004900100b2803031400204c252030340300d042800c0807807002205965001480b5601c0241e554814103100a02c032040c0c00c0103002c0d0042d00d00c05c0c1c80c2c4860900070a60503654400c0803c01102c1c85034044c00381010461620316070301b504001d00001c04035940c0c040b540040c05854007220249100600412030341000c1380e8100e6004010100c3d0242185004c00700c440c0311010703100301d0700040419169030070010119240c81541100460b00074080c7c4014614290005100002c0f91048070080003142c0000304400d09c410040754144130403c5031a40040603103800007001c0c404000c0805925550701d05080e4800074205005411107120700800140d881540c04026011b20708540b2090b545a009200510001004004941880c2044c0e004006914000306151240c0012604a00390040c28194054200005500220b05981c4035840c00d129a40d9032102c12559060b0480c2d01a0006546554a441c2c0c104143e01240d00040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 196517877 1250 196516627 196516643
    0x1902040902060c011a04050a150509070c05031909060512070815030f0102070203011406060409020304061d0c0a05151621021e030304030503040303240b041806031e 72
    0x2c003444080742181d032501030300c417107034840c0001450191605102d400d51004144108215440d80002c0c1e00200442c030740186800740680b1004110002d00454818240c035a110f0102c03a035030440840103450b0001408407040104006402c04112240180183c1c0d0020504c1c8410584941c0e541d201140d0201018000c0141011544c0c0484820b407002d01c2400ae425803082d0015030f4030401841490f08481c40c1a2140360040c6111091120940da40400c5034104c820940e0f0158480d101c40c184440103141032500d1032060031400d000d03050210004100e42d0000030045600b4400b5550b94070038011090b1582041a090480400c12500e45180c0140100300c0c0b01d0251146103002c083c0740d4884d280300d23200031a802c80503034800106101c100005086810503c42504060750a60500f0356000e81070f03004c0030b03100900b03141c0c60340402c1d41c400341030500c0f00301024001d80b072000706195a00003400085d4000d0050301003000e041d044c503260f51415400390104507a03002803152107031003201002c4140c03003201503000c4074004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 196519127 1250 196517877 196517887
    0xc090409061b021b091501050a020f2e050121060209060a030605120a2f1302030a18080a1b060e010525020616020f0a0b0106020609190204090206 64
    0x3038040c01c4028521842d41e0010714161900071403058451101400143c030406055040158100f80d000422601d84001c0c02c1c12a1140000201a400c0001c0b1510100303440c0300da0050300704807503012400c048010500e2003e482d001420500c000003a01d5003402043d0507041120680074035540848640341c130880c0034076070060520700160000361a41e880110702500203515103001344a5403425108007004494010300500c020401c0340c1d00d80400c030f80844503d03070316a07400720040c2441442d00c030754241c244500200580c800c004022a124029042900d2002845151020b68a050300c041003000d0701d50354020125a007003203102001192000c409403801c01c05040d421202c1d400150341c6021300b6080a0540f000403c0e00d140041038491421074940f001406e403111a41480c110030703004a0100c1d00b003078825005205c1c1346441c1005034509a4181c1400c006403040c2c0488a0500c030203001000d058545a40c2615882d44910040e0f6580f4024841003101c0c81050098020044c5481e0340700741d1354544040c120500300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 196520377 1250 196519127 196519151
    0x1b0901020109051207020f0102060106020c04200d0c0f020706050301030f030201110307030b09070905130b030f0a03031d030f030f060d080d091a16030e2506090503060c09040906 78
    0x8090741200703030024204d01180310b0045242c05016003108280a1006207801d62402100a44c0c49101c40341560083d96541d004954800c40e0042e840c0d04814846981c03a1307904050b514003c000c0c01c4101000d00050403008031520818030204207402181d40039680c0b142941d003161039084007010814811003e640d62000c01e10b4002c4180409140728400b00e0701c0020b55203c1c1034085c456070601c01401c0e40200145402e05000594030340905030455000004005640301d04500400d10b40b41d401d0720b50701840d03c5100d419004050785608418944002d040300640d0800c04c41030159928010401ca100c107813042480058280100c01c103505070300800050150040c01083c0c0c998040960000e40c0084a40b501c4502550500940329143c1802440c1d4400d40b600c0c030300d0a40e115521189040b02072000301034030341c0b200080c000401c100c551080f44643c00c0c0d01d00038454220007076101007007900c03078131000c151020000500c615001c81c441d4481e59114001d580303011052020040104019803044481c5c80c0c0d140000128 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 196521627 1250 196520377 196520383
    0x20a170c1e0703080702150a09020406081b03070e07080610180e0f1609170106090501090c080106020d020303060f0613030302070f1707150c0f08070303050f1b090102010905 76
    0x10560580e149903110b945050080903072100030803000556120341030440642c112007404541c015841031002841034900c1c400a80500255805010b0910980413411491001508942d80204c8218119100d291340d03070042d107082e01400c03944400404d0241c00010220708141c0c0151402029600e031080201240301c0c0c0803a0168055000702941c141d42c00100308142d22190307047c1c1d41244200801d00f0001034203060003400140c0d0b80c028445a8a040c3c0d4038020014000d401c200040c0c00c6801d4240515a1112018402092450040000a20b500b00000307509070011a541d105454035902540c91a075079081401303681052411410b4210404000c041c1c00303076840e44044c0c00914440e6002c0c141d1245040b800c1034014880d9041511807141c203803080742d01c01c2c0f000545c80d01100c500c08105000b03410042c00c15103c040d00c044c0b0203049140050502c80401092500912505110392000c2000b9250a4803511503800d0403240710403295410840303c82e18150401c081c212511052001052613a510754445007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 196522877 1250 196521627 196521667
    0x20406080f0603011a120c031e010501060c0c05060a141606240e0907170a0605010b070503090d020f0a0801050414030a0504060516020612060103050a020a170c 70
    0x40000c0300c4a041c8514504541070281d0400740c200e000744610815804080380000c90450007034424aa68a02424010810711046100b8180101901d0302c1c958120b142a0940c00000350040855107080c2c00411160300502c5030514003131300220349091903414201804555071090140c40d080c4040908a9003d0108807401000f000c02a0f142441c0480200d01e000c1d4152621590030402d01c0c0003552030b190f05540e5200c240812034080c545400c555440c3c480d5581d08050b42d0703401800003000b140b9108000207000161280c41184109800c000a1780d1340c8514980c94002c9810091154004012260481c548000e0307450116000510f01c0060422041c0040d00a80d1194005003050b51100300b0401032101c2c0f00030b1a0400c800c5c1c3e002552511035440c500402520844c0601c0e828480081070301d020302c09901042c1802942d024129039590041c1000002d60340d6002c581090001342040d00040d44d000740c03402030f1441103442d0303110f00d042d00340c2030900c01d0980c2c10b00034034140241c102032008640301403030031500d10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 196524127 1250 196522877 196522889
    0x405040501031b05010203041202010c0c05090c181905040e01060918380705070b18011d0c01030b011e0e01020d030e0604030806030109050d02060a061e05060912010204 74
    0x10810540c8690f8602070b50003158061030654005000408c5000040150101040d5091034041d01c81c900301d251044402445800c003c1d0171132001c100304403180001d103000300f1103c2074008018401c001124100400381040c5240844c28000040d4108250b0405820044008080000101d81e40c0d80311221081111108041c0c218407050b00c4039130000348808903103043c2c9440045008030822035200789520303542034011070404c0800a440000541d03014403650944000f154080010401400c00c0c0c00d040c4501210a02e100f551540707400c0e00c0074105009003000789001c0c0c0c0384601820440c0d511000540c0244403843c10749040c0440c00b15081090403a030b21480f500d1150301d4850310100d441880c00203240030f8042e020441414a4401b014074841e1000450319031090b498680441c495803100b01284c09450042d0008003d4800c12008007001034002c116148580f00705142003150b590b40c0c245815609507030210410107146880e0080c0954149100100040480a028402111010303200c036422680554020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 196525377 1250 196524127 196524143
    0x904050403050a090b0403020603060f010210020a02011506020d090e0a0b060c0109110109030503071106070204020c06180a0c12050c0d080702090f040b130204060f0605030405011508031c02040504050103 89
    0x140700030340e030802d6a14000d468840805400e01f0b040d54049212448080c00d040d10078101e205040c01d00e60301c2001120000c0428007410354403100404400b90190900461440103108016004140c1c035100003102d000d00381003691a00d65079880c101102100c240d02030448500e10341c8550f4405000d40b5140d0003099002d020b50000544512242031001d401042e203d5950304200c071070741003040890000401d41d40803580102d48020031110350400140240300b8008000d40141c004501000b101d5404114580b08002c212074030701c070007240f88440c80c2e03d48040c81070060003075140d00c4c4140140302c2c003803405030407881c4200100c81c0b4410b04500001e03050400e1b000d04642c001c000203072200450900350740d02600540407805400503420b080e41c130030918060041200000d01c1d11100084159512071300420300420803680800030003a00d85c40e0080081d0b10481f003d89181d030901c04000e0f080c81b040d480c010b08445001d070246042c0038048420324411503800045d1f200d240d0702400085170556542c8a028000c5110b0500303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 196526627 1250 196525377 196525387
    0xb01030e0706232b020909010e041208090a11060f0c06071d0906010302180907110c090402090402091807062604082a010f020a02061006051c02090405040305 69
    0x281441c0fa280000a58140303c0051007000c0c803038141c0c03021300c1d031400403410300c240c21360700d02d40c82c1440080c0140511245e02464541c00003c8403800080041c1c000c1e4000c041d0321600849540f42501e5000e41540c1d1260f142d480704114401080c15020511b1064000502e4035107080c1da407103424002c580049030101903a401541c10300900d1078100a580010300601d0701c0200340c1111020000d220042c00a00c000e05154000503c036220461401c0700d4500e001004100384024244054001c058005020f458400380c891400904854a03054047c0c81c0304aa00610172869561642d082c0200c21101070001c5048035540d800030080701509101d004068013007944c0d00d54080c501d103080ca43c424804486000b0040007000d050202047c09582229543c4d48481000310180c0120010400ca81c0c00b194103445441d40b070444845109046034000b0b1010840170f500b140c03400c0d06c03411800c40001c00140b1504012440400c10ac1c8014100d10a0b60f001403106d0b05401802c00700100c1c00705003a5801111300300c0001e400011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 196527877 1250 196526627 196526657
    0xb060705012301051813020d0506010603150302030a0f14010501080d0e0d1203020a0e04050907030614010f060e0103061e0501080114030709110705120c010507050903100b01030e0706 80
    0xc01d40c20641034000c840c1d500c2d9450300e40070540f06400c80b5240d03500c103c89203000440c85480d000280a41c0c036800342c0810086031503402c040391102400c1c0982000203042000c44c005140c005105042605e4000300544101c2402d5900d04a039801d00e05404c4800105a103594a140718007803140e00d0090145d080940391001c003915000b440d250010320b03007078414068040380c040803a00000b031502c2c140ba00c500740140d443d00218800c2d01c03550206072607035034403505000810541c0d14011842d202200e101d080b080c0100142501e90300700c0700b8800d01503000b40c541040f80811042c0d11403208030034035031030605001840e55151f1200103255500c00c0e54001200d91414030030490795030311003307060040203101812308407008a900043d449400071320031040c00c5910f41e0182c502c2401c024044a42d604c1c0d000080707688107001705072450043d41040f40c2200d91546400c0004483d00c0c010340072110748100080c090b000c0030030a0b44078035000f090400e44c0c85040650340ea6158440c88002c01c481c02c0544440d03146c0d02080c0d14840 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 196529127 1250 196527877 196527911
    0x1b070f09090213090305160c091a0f010c0210081b0406030c0806010806030d110102040b04230405060d1e170c01060f0602031611090109020c010c090e01180b06070501 73
    0x10741001c3d0585132490140101c2e5004055030002d96010141d10010034840c2403400030f0030043c3d0002074040e403500b6240c601d10070300c0c4400b6001d01c5200396110011000c04c00c006544aa004140c06500090b0146e854400301d0301c43d2014580c031940814242502c011081e1b80c98116411035003080011940d10181c1c0a40c00f9004110705520210920b0103009510702400420b03100c5040c40d40c1c0c0f0301844080e00806603840001e4040d100a81044407589441d250f580683c00790000c50014520094510318441310400c0c20709004440c0f00c0c02c005401031428400300d03664901140c1c440d004806824066a080a001940b201c0e40c0120203240c54480e1034455844046140c2116907a501400c480b10764140c0820000340c000c4182c84001402040011000e1220b040c130001d68001b10007003660140c41c81c000420041c44a60240880680c80b0008002c03144400b40d0a84034203000d070060303501132100000108105040e80004600715680c8220201d40c0701c40b00f20203e6000e4001c0d910032078507a510360b0310310040417a1138 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 196530377 1250 196529127 196529149
    0x40801020a0e01121104060e010e0d052103160e18010e1008010e0c0603060a0e090a060e0606240903010603060506090c040b0a0c02010c1e030305010504111b070f090902 74
    0x603c02085403200c45c1d08170318214810b130b10501d000c1c005207800d4100700e030380194810400b500c8081d1400e0100011391404039120004002c11000524205104c00d91440e1031405480c4920710645030841400d22032281070300c020700085086644000c0d5811108a070110501c41c09000f40a0754030656603900701034818081c00d66650304820026850603d0386001104009002039240106440403640c0b600d5000c00b04e0001e5036903801c0740a940f00500c00340700c290b203400030341111700b03501440e07003000015900f81d0401d0301ca81080d01c00c90b5001d4080e081c014030701c0d4000a03403e0b80c070000e50400ba520f000e26200c04a803e44040381c2c01030307401c01d680310200080d0741040202c9030380c0024074200f91407629040261090311400303070cd1240070400451035126021640034103000c844d4281c10400001c94101c030451000c450410003d001c60000342000000165800e01e4041d81301034540c03112009040109149905040380068221070a840c4540d14002500008034440c5c0005480040f070041002c0004d401403041030300003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 196531627 1250 196530377 196530407
    0x507020118053a03090b0304060603082d0a0e121e0a0c060e0603070302030603011e05041a0702030f0c1203070203040305010501120b040f0c05060a1107120c0b0c0102040801020a0e01 80
    0x781014003c0040d510403090025200c0010b02e007038a80d11030307040200061586800080c00c020000450180e6101c004c81103c0e9541103039003040c00b281e01c007000e40140b2402508141d00102d856000007170300340d207082d07600034406d80d58900885800c2c041071207a001441c0c10b030b1b60720444a6003144181105010307508490f0380241c5031506002d0098090752000c03a250344030050030704040650200c0480c190359001c1d004101d25141c1c101e00d40c44055070b42c0d003007900241000d860032a02c0840a41303800307a282c601c242c1064801c1503c0c6d0040c500b400b1040c06c091a0310350203007800c6006070190b00443c400c981c0f84a005540103004990045071103500710302d07090f8215001a009009080001d204000004112042d19903009038880720129220180c4e16203042c0e0715546400481c0d225002042e50b101882e440140c000341c1111722801c41d80100d6460002005030059800701a00c182401d0100f4015075405d600240f41d80c03d00000010303e0300c0e07510028642242c0000c90030340001402c11861020300d40c2d000034041c0000b9a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 196532877 1250 196531627 196531729
    0x10020403031704140105040b0a05060a050112020f040e0c19090f090e030d0606110d080c03060928020d060e090c09060109030b04050c090f0403050702011805 69
    0x41161406041800c5081d24054002c4441001404000b60851515001072800b802800b96003042c0c80c0c1445116002c40d034140d0780615100029110b071801c0c69280040b600103840d50601c41210043c00c070081d5211000300400c80b2820040001c0885600c420b0900c114074005021f80c6543e42c1c191081c803880c4081501c002001001e500074001c8885039082c3d60210b400322000011141c5480c40424114003405054030155864507400085086d084010110a0102c8005075009204005000d407101c240507103141141d001c0a01c00902c82c0e05042c0400354000d01a0040c02d5900d10500122184104903c00c4ac17204407500425030f403207605958002c540180c2440301c00d5074440d260040b000c617514880a00501e2142d45c20001240560b400f40500101071b5800107103108046c0303841c0c05c00607981e0394100c3d00c0e503000e40c001e4800038040700780c500311107400303207070325907034580c600b40c03103500111058a22008607a9407610341c40700c002010794038401c5401d000110b12205452140001034a0001e4214410007104966 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 196534127 1250 196532877 196532879
    0x60903141306050d1e06050406050102010e280807030c0c0e1302100e03070f0312020705011403090705040504060c031505010f050f09030f03031918031d040204090b0102100204 77
    0x40714020002a2541850800d489a015401c0c0380d01500400803201240550203088400800c0c0340d42003501960415142408103541d940012400c90320200c0004416401076001c040d0461211100b01c803007070110503102841044c07191180700c210380c00000101d01040308050324a007008280340000c0000c1204900724441840e180c40140041c040b1000000d1062500003000b0f614580a03681035018440c0140403076040355250b51360b200071004140001d444034003c1d80c41d002030362807001481009494041c2c4d0781c1c006181b88075010f007001781c1001d4920300e401e0007102c8000c14140c481c1c5c803d4611640c0141c40100760b040380000050103c1d82030101c80c0f0504020320f13000b40110398120303040d0b41c074a1400b441e00a40c0c81c250302900204e540600c40030035070326009000c090000884000003840c02900240c91500c1050000b008007000c80d200355071980b07a40c403480320740680400d0261074032540550b181721002000c0781004d000038040b80c0c0b03c0d80051148541c2d4150602e500d580c1080490580884080300718a85 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 196535377 1250 196534127 196534147
    0xa0503070314070e0607020a0e011e090b0a180f090305190c0203060601052a0303071101091104020d0b0a08010f0b030309090142031b0c06110f030406090314 69
    0x3801e407590804e4069000001c81a0441d180c5880c12001007540c0b0600c001c05503110544020840e0390307851052074070481b40c031003c0b506000c00e1098841070440104407007140c0d45080d100c58060010060b01610043d0b80f00352254124415001e0108044d01ca80d4481c1e6459041d5485002080d10340061a0100302c032800550300161400600c0d02e410402c2420f0454071013640e1000c910503400e45c441000e1001e03c02503000c1c038103000300202071400b44180761240354031307941c00500d01822280c10317030405441440341c10101510381c1000d5005013258a8003a00100e500c05101011402113070081d405402107a644048410721000745108802e410360307048000d94506001640000c00403807042c02044140c140c44501190610030248620036012010000701d1440d10801481e003428500b100080c8000c2828108603030b901c401020403101203010a601c8042002419803103e02c02000120521000414100b1042c0a03601ca201d014612071841040e01246e20b0300c1a280041a44199008500705400c0c240404465 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 196536627 1250 196535377 196535387
    0x9090b0a0513061701091e0f06020304031e0207080f0a02130b0a120308010501020105010b04230103020c071220030d05180904030c23150603010608030a050307031407 73
    0x480740d0846001002c468001d40490040200d94090300c0e5448080b201c0306020740d0103403c000250f44c0501040c0852111004140f17950459071200106021a5005c2000001d04e0643c0a95002406441e016401c05034001440014645c40f01401c8056480341c00100039030a41000450001402034000c0c0c054000c056000c902118002070340c200849843e81012506a121a5598402849008024040c0402508001d44044020b0141038019420b01001103880c00010084070100ca8099440c050740441409030750600d4428030f0a000d0405408000703d4042071130401c06170000d8001d500c0542014038951504103040c4001004048440382041c5c443c00c444c0e6030200e903076111140d080c01c00580d02c10b040401d482d000300a8808566011981d00c00384020b142c0d0000012465920901c42003c19030404a04401a0180505569590342c800500c00c40c0840c041940795801620140001c41c0580c0c07100701d03036819a080f0024810000300044100b04200d50b150094a0851000c4121403400e42092130380103007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 196537877 1250 196536627 196536629
    0x7061103041a07050303040305031b03040816060608060a0212010f1a07060b0d06090302190b1b19081f12020108040809040603051b010206150d03050f0a08040309090b0a 74
    0x1414864a0101825000490b03088482d010760010581e0707602d24080c85c001e00550001ea404694a6072100207030034400c03070301408590050781c100e2051803c2105040c0021048040100c04880103a19054000342140d400c1058074001d0a62540261700c400d00c821014100460580c440b0b8803102c1c13461170800c6020200c0e19030160010005c590160380f5505424002c010340300007400960024621130307295061040991003540801e10076402e4418611100484042040c030f180d00c0508407000ca03030040384058400e40c0c141c1c0201e480b4046ea035420403810400c246004000c02500e000130030000010030012070040d01559801054401005030300c141000400383d41d000145000074144000103001c101800440400e031607941e080108144032030350326454400c0e01e03081c0842d02c400140c0000041c0074025800031078080e00c25112110349214507007801081000c001600311099091060410903006070342180c20082c140340703c20b92108207450400345402802c981103503108600484c035140c030782501032350f80001e00340c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 196539127 1250 196537877 196537889
    0xc18010e01060c031b03091809020906060d06030605040b04060b090106120515030115081e190602122410021005190603050c0a0504020301080601060f020705150c0706110304 76
    0x618114951500369140c0c1c03885d8801108203041c540074034040542c4140c1070010754841d040081c4c1803042100e045000da681095000350b000410b1000107105060410190031165900c05001c2801d96aa403a800101e07030040e0b81c03d44002202104000900045002c0c214107084266501101917251080041005031210b100b500349a8850010500d2403050048920407440000c008000d18011503d4103010f1401d1072144160350f0041212206807407940308140010079900c50080d000302841d5121107203140541318002c8502c15420301540c2c000d00e088212981c41160780c00c441c40d82e0400000d2508215190810340302d84115814010400c4070707907011801803050b05c40454003080d1610f6040060702c1d0008081c04260f4100d10f020700000a00c40001655503462005803000140140c54209000980c4001d000b022600c7c1e000100400840f0f102d90107002d00c0441e6881501c006a407280c0020b24489200c049200c0c04010110712403120303003420f00c181d0009142c142000307040098004841912402940300721 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 196540377 1250 196539127 196539137
    0x1060503270a02060f0309210d020f070f0b15060a0c0b0603070e0717090f03041802040b04060c02030c0d02010905060d020708032d01050d08090301021207020c18010e0106 75
    0x103a0381c0c0302001c004241d0300d503500500c01611040c8400419845800444000c0d100344101040752000403000e5404040f0300740014183c0d4504480310a50b000698403000324180301c23200800c0142c3c04204602130303071000b103486824400c600f82005560070707801140c0300d0303095407250074100080207140e41c00081d041074541d40040e400f412903070341500290401307a46902c05d800d60f0080104003d402a4400180c0d025501040c1246190b03031a01503003903070380c0c4041039400c100e41d500c10030062026600442c507032588161658005441c0684500a40440b41c206600c00400f19045501e10f10441c03509101d03d08411400351a1045121201d8000800da2100f0b07100e40750160b42d000078156241010340c0c04445100d0703000b40065940e070078002c1e150403000140c0501c4100c0340210489440319500c0255409040b540006c2013420701e100c2c20303103895549603c02c7c1d40d8103a1641d82000480204071038500040e100d500b66402a03c000180d000a000c9500000213009401071022001800290001080d040c1580c070a0301e44 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 196541627 1250 196540377 196540441
    0x122c0607052b14070f170f1003301b0803130506091606080106020303070302030c0403020d0606050901050301020a09090e0f0a080a031109010c02100311071a01060503 73
    0x30b101d20240c40310b40c4090450070210900b401446204805005160940da0256258078514007140d0380007910480201000b0070346c01044a01c0f00d0501c0c107079008031102841e184240d50b2982c4080c140c103418044802c40b8034001090fa40120424802a0000151360405541d9260384080300b441244415900410b1018040701042610048101c00c00310a54020f0840300300e820304002840da030341e40182c07844880810301d240220b8950b01c9001d0081c121400d0383c0096080d6141d8400a4000e900014840004084144400400b50743d0781c8202d401024014040014820300700720a0008102050300200d000741c0c0108415441366521a0001d011180c10b0784d0300040d03840554103040c0c10080309901c001c030713144962455036040c4107100c0014421501c03546c40400c1503003105100344411340035804086000c202900f1240c005414403081101070140f6910700003504a1080880403055041b110065501c0701000801100840000b0f01441c0034051a060060852810340c0061a08030940340c82ca19008046010b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 196542877 1250 196541627 196541677
    0x1505120d031e0212151903060b010c020411030a05010824060d0203010501150201050a05060108150a0b03150a09020408120d02120f0402041b02120a122c060705 70
    0x22822184030100c00e00790354a4001481030102588217454040d48030040401454440c5041c60021020100915580025602c7c0d902c074a001011455499814014007100f5180103907102e208103c0c85191101c0d1194076400c000340114125139050700b01da4556840000503e01002d4120028007034002c8a60b03030b0048030350f692070202d0300c4030300e810070000d4140d030800d07001085180703100007810003010566000300641d59690303800c0d0701641c5095030f40901081074000031501c0c08a480e2441220048050581d862943e0341d0445541c20781e10803140c0101d0049c980c1060102803500e070148200410885405500701401d04420070b49440e96001c0010034900005413811101c0340341c2d01a90a0030071a9182c0740118900202040104001103030128402c0c0e00e0301043c078180d0800e1600f590024841540100341950000003d03032401d41c007000c0e125003030004107019601441c20301d0007004680e480c4800060000d030561641c0810350422202e895000341c01141c10403058941c06421340f40c061130505041020b00000705 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 196544127 1250 196542877 196542911
    0x3030d0e190803010e0f01030c03030507020f030d030605030705040204450501051503100308030702030d050c040603110f160c0302060a1809020f03061306181505120d03 74
    0x564210036600100a201c00b40311504002d90b048072004000d04800b40c0d02c0b02e101c624510424007005042c04801241400424801c4000e00300e598400b404081c0240c080320006807400d250015a00c0001e620743d1010b1003e4141803241100812090b075080d41406c1c10404115000001c46241c1c03101801419040b40002c603000c0034160240320807049032003282100c06100c03009030034240a2a40148a40c0160700240010716080304e2007400045002c0e140341d42550343c0d81100380d001030216811032005210329401c14449200d000e005230340882c1850b94640ca4114040c0a590380c0e842ca08c0186401401404680001c1104a40760b841e8840a03904124465140ca403000a00a03040a50000030208a0304c0c0555040006581c042071000b80194103140c0da80c46110070307845a50905006903030188003240751f6007040e041c900c404400c06800840c00c0c41e02e408490421601c50f604642c00c0c9916525000e51015089185202070300041e18041c03200c030031280703a80d5a00d1310301c082030f40c08043e030b1414150100902c00d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 196545377 1250 196544127 196544143
    0x130201020309090a05060f060a0f0e040e01020406021c0302030105090106081306020307020307060605030705030c04051b030903130501030501060c0f060e0303090a030e040207020d081e0a050a020d08010503030d0e 93
    0x1c0c100201418041013010041a00700c8100d40520215507401095146c070005480e4125041e40d50f0b4240d0384810001101c00c40100c04e0610340264440324440640c860a0001e0006805654001c003150f1039080382c09240350300c0c00e94100043c144100014031031502c0b41c8041c0d42c190f480720305291140d612888000118982000c8025101c81e2020050101c1654084020075000780070350401d0020300d0f1514101500d68016128a540c103501c681d19004480c20540c001ca40e004901510f105204202c00f5000e9081c1c1d0710441e04203079150000540c04880c2400041d072140a001e007840e0402540d8140744000d407411081080c0a0107842a80300700504100950700410307010714442007943d8503420142071455403600e03404c3c0102c1c007082840300e03105041d04040c0300352000190010f00340c10b4024040c0c2c6a61500398800c00c0840002d20700700e900c4e09007503541800100002d040700d554a83c0c2d03581c0b1240c4024144180c90f540301080003950340c0104041d0f1360000c1a1140010301203030008486003070700b151600e0070780d007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 196546627 1250 196545377 196545379
    0x150b0a0c3011060105100e090f0103170f07031409030a032001050f040f0203120a0c0b010512060a0b0a0302090a020a1112041505071a090d030c08130201020309 70
    0x2014103441010740000c0c0500c0c10030140e01800911000c15101501d00c245070034800489540280010411850807942d4000a49980d00f04050710812000c0404c8102004580c81212091010010800c00c2301c0c0000881a000001c9541810000300d0b40104000e4030440320b0260400080c8032803164910318980c11100c20010003000c4400940f402c0c81c0c041c02020f90002c81c43c8034840280b0100d151048180076403480340191020b0000b1740e81e9242d613400c03815078486200360b03054460342d00d040010b138510500522002505031101c080700c002c10701d00008400030580003240540209082840d82e8600000d203503030003901014002c51044038102c003203003400b54030b41d001175409900403060000c02080d40c0c1c028201c101980c0e50b00d00607940005400b5540310b10040728840810020441013040b00745200290a00401e1890000e03d4113105846104c80d0180c03910440b00c081c000071091003140102004114201a0039050602003600079240c0601840d030003d01020307461184401e1141103a01c20300490f0181c4c14 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 196547877 1250 196546627 196546643
    0x60803030f0a0e010608150907080f010506040b0109030f0303050603160605070b060904120305041502040b13061404050f0307050306040b04050105070e21010609020a020a05060a150b0a0c 82
    0x20302914072000c070350420307140d07645007525040340540700f0314040c0204816111004014113051103203514200032032000070001802c074002c00c2004600080144692540d4121003000410542400020803003265403440381e50341442043d0400b040010200c08182040c43c0d014100001d00e030b81d803078020034140784070a400780000b4403503110b000c258590404054000d01d805142c1d03203840381d51050306200c0844d0040d103018111560002e103022445219400680d4031611407a0707401000190003c4c503030160f801c5500150322100f400301e01804d540701c084c05014028400c40c50090503404200c0a500c00c28070503402030500489410104201c81c0e202008981c2c01000040c0440d9014a842d080c409090303482903c0440c0c2a500b05004500e2251091800d89101d0b08021f024100004d00c030341d2500c0303044600c0d01c0501e0655485900004212100348060300725103280760082d20b6525140d10b01203042c10030090507140350038504040a424107468482640076544c10802d51a83c1d100da001e0700ba60600102840140155 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 196549127 1250 196547877 196547881
    0x100314010b1309020304050307020603090c03060c0d0509010501180c1806030917090303090d05150a020a090902070c090506061309060501170723040b040f08121e07030306080303 78
    0x115941c008080709040c02480040e03154440b8603541c240d00c03040c4d401401650042c460384000d858800c00850300306412b0340440711380c00303000c401080c1481c0046444000386600841c2c0500c490729140142c0c2d5000100c2e00080240d0b40c144000f01078003403030040141c45041e94403020052941d00481d000321280894a04400031142c1d2408020080c100000c1b085900440d401d08070840102c40c00240c41104500801560a2208103004e110300000c6880d400e50762446058105d41c114115009414024591300e1000761343d4030320703140d4050030008243e4030030140280704002d03101c0402c090822940070303a501c10700e010030103482d4180024003e01540201c2680140b4548000aa006555000754121042a201d08401c0503940a4004026004840c002d0106000c3c1c80044481e4100b0a4804040310780d103079074542031980310100a00030703401640041a1604800c8424020901e00300180a0115288601c052500d001c6280201901807000060034000002081810400d8020b82061000d403203503030120b070345034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 196550377 1250 196549127 196549139
    0xd020706060f030507170a08031312030c0206150307090f021b07080601050402091806060c0d080f0c0703020307110d080c010f060611030906031f0303080403020f031810031401 77
    0x2c00c2040c4011a0300384980500003c5c0b404c60708408480040512020b440c1c991000e4545000700c0d4002809034015407007480d029030000300410000c801c03209403582e0020307800e0740b650406480d2840c0500914105800c00c001c41200f660005904420390b845680040b55010b20300d003205010380950075440189440e00034032001003100008950b000c83d80258103c9040366038543c1804101d22415a032035401100305030140085034400306c403080c1c1090010300b21515003441d1113407075410300015642a80001d0360240c140650016981900c2c0e42040e00d1314980c5d40381c40055039020317580f8800c4d104c2c001d02140410000d0380440d941d12402c043e0b4607420000c600d40d21006000c85e1070082882c080d052210f0344ca03140c0e0100f11207118607105600c03803928000840c0740c144504100002508008c0c459992400c10011424140184141c8800294440d850b500c0c850709082c035019003800c0b001c8a5580483d4824048194981c0c0d03058024840000c040c1d8101103008030480c0220003078040c84039818603400300c1c40c00014031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 196551627 1250 196550377 196550399
    0x1816051b1906051506030402040c020c03161a0901020c090a060f12050f0d0e040e2406011403070e04110d2c010e06040204111c1a030102030f07050d02070606 69
    0x489403107504108560f80c0d5130300c40c84c5080b42141d41340540202d01400050b0040c10140d1100003220101e00449407940019800030745400001480d12049040c685400c007d440c4c013101c007000702c4241c48405141060b44036070000750b0f294540b040142c860030060000c5a202012070780400041c040c00c9802d4030b61140c460101d100c00846070300b03007200c3d113100340030140303262200124078101010615a41c0e514001207100401c005050402c1c2043c10f01d0080001c460403054403d0302d480021500180481303202d1a0200000d040c0c02c1e0040d0220342103001c10070400031b040b40d01c01c5006640340e5040301c0004002030f004100d01614041e0f4100c11840c90720b859070f40d690142008017000030315040c0180e01c41241031341d40c0c0240e00741e070800c1d0f19030342c0b9651100300071074010300d400d8005146849500d4541070805901d803084041840e0f0311400304400f91340e10b480351400200010140b00c03003d02c0580c0254698140b00300c060715103c40040c0a00200400800c8180c0803015580440b4203441e0007100c24040c40c1e40324255115 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 196552877 1250 196551627 196551673
    0x307020d2f0f010c02031c03021314040b060f030615040503031c0b19032a06030207030201060e060d0303090809040c0306050310270201051204030e1816051b 69
    0x100c500c582d4003507460382d903100f14454520640d0140c0642440d15a035401201c02880e0f0118007014560207002e5045041e000941c60401003081e801c00c040b080c0301e03441c02d01003251504104907002d1541001b60b00da01182c4507080b690010001d40c0d040e4000700c0c0070b0f0f031036911a008a030003443d4107020014400d10f80d04818901c000000c0b810b4481000008416070410108965294402001d01460352081001c25001c0c400c40341c20030b44202103811010f450b0858242d800d03485400c10404203501103054402c0c1741d424170541c0003600700c0d1f44014120b03080c2040010ba10003420303400101019103600d100001c0000d0a0140c914180011b0018041e001c4a004060090015806958028810080800c0c0700c03828a009500d01c44140c1c041214032910103c1181802c0d0204100aa040c05410803c0058038200012014410350091360303030300300512002080108582d0b01603517080c7c3c80f10780c020601c228110701e12842c042000d921308101da5914147d0500500980241d01c40301d03003500814461a100042d0303500410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 196554127 1250 196552877 196552879
    0x12091501170a06090b270a0212011112010303030b030d090b0d09061803080a09080702090702120f1206010309030509010c11030a14060703051506030402030a150c020c030a050307020d2f 81
    0x541108442d61b01c0040c004419030f400700a036800740b403001c03000d81808401e030480d029600002107402c0e4500e07824442d10303522a084002c1c01c14140e50041051650510030050741c41811000741056103050b5200600303216860140e071218000002c0c149001d01801c0c2d00c01800740c1c0e80124148419400c0c003841030006025400144c02186202d40001d5040e03090744038040849030711400c05401e0445980038002d10301401000c420652140010f98680c0000c030030041d0103103000f1034000035610a03410410950260010700801d0606003040107803800680c0100c00da950035030081c44d0081c2c0c652940e041020781200c4820b5155090300484c2400410710031481c60280101a060044a40b9502c820100f10100c40086511010003060885000380500c1c04d140115007240c0020200e40320b60075540c50f031521941c200c02c400c000c120364540050140719014003440c00d00300411001350802880944850ba101d11810800034843c030b51010b041c00030040340304441041200c003150340000303480c48080080c5a02d880d240c166 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 196555377 1250 196554127 196554151
    0x605150307080709060608010b041a041205100606180915031a0a0b01050f0f070303020c010203240307080c060a0203130609090f0603120e01020309040c0512091501170a06090b 77
    0x41041c1d4050451f030b60494040040c02858a807070b2940300140e403511040042c0b640c200410000581480e0705a11541e410301801c060000e125401c90603404445455015a082c0310312170030300e54580604111a04211914401d02103859840100c03802c4108510360070042544a440c5848044440140203007407199800b0f403820400c0040c40b10064401c9d0241050700d010004040002082401d01c01002d4840700c1c4c400d08026092801038030001d4266003048401400310030f601c91400400381101d03105d411034400c042d4040c0c0142c1d400c1c205896101d04004180d40c0c0100c20004501c040325208104807000500c0741810012246e4541c3e400800200140c4140440300742000804517114440d0300c00d0000701c0354890707035400e800351550030151021584c1c03607003840c1036010510000349691114041c4000311450741c2c1d60140c0d649165010f800c030301750740941104003d42c803a0000031485203094024a0560b003a400121901c0784c03100480c54030304101e410009103001c0c00e1406903010481d10381c06050144c0c40086003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 196556627 1250 196555377 196555379
    0xc10031d0a0f06020a050912100614060a0305090705092502071d04020d0c0f1d013503040b0c010c0e01230c0d0c12110703060515030708070906 63
    0x40c40340d4a0341107200103820080c02280c84000611240c0c0206800d40413800c20320b08100010000448040c5007483d6a080d98000710004140c0d4450b138450701018001c2d040206031900707018004200280036100c861000d0540d91404540c030303843c00700000002440c009000741c003207190161080380340c1614074100d80c03603020007081e410b03004c680042018402e96200d02c1340c0000d016a50380ba2443c82c480060405d0b82c01c40c1411007505c010480c4001c0007000f605043d041000120b160a11000307502d401a2003a841ca0000c843c010311007040101d4a03c0c04117140c8034108800d0f000e034040342d20b102e80d5104480083e02e00c0002000140200140d01802c1b014820a000300105061600300741e1304101d400c01814009058110225540340409207e1000c540203810454149041c0807003031442c08020b07243c81d80c0801c0500d0081400c201300106080c20501c0c1500c2c0401d40712a030b400c2001c2e0b0300c0141d400028074154031000000c0361003a0440d034032109201c0042c2241c203925910440345856580a01a0311003542c14040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 196557877 1250 196556627 196556681
    0x7020a080616080705210603160e070e13020301080a15020a090501030c0309140c09090d120911030613022103031306060302060708040503070e0f04140c1003 69
    0x10041d201c2d208070340701c0801a80d1000300440780a00020701e0042400001c3c481003011102c0c4030f503100c0907050000c0c03d040312414007104062802c0d0340d4007c190300080d900082401600c000c03150032600f100f65403c0080a140350b2000199070901c094005d921202e1000c1f000003041c41c000155511030900860fa0f0b80000c1010303a040c1003d80c41400c071f400b8007041040e0401c000c29407107940110310300d40c25450700041144080d920008524440703400300b50190b01c4443c81507600d26019107002d07000350810009002440e505003000c1c140703201007140501529900c00f0036400303011944008118841004042d5090b600c0d004103510141c03074540109900444200d00400229118291030b000c3c2d0380310310300043d4150340d2a9035641d20304c0308038003070102d80c11174840070000300684031600540b901500c1070109584580c107101c245440c0204951102c2c0b0800c2c0a0340a02c212402c034001843e40058006441c9040051818202894021200032451308005400c00c0d081d404c90703150740b040d07995501598201041c016195 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 196559127 1250 196557877 196557883
    0x12010906140f1612020f0c060a06050a0e0709030b0103140c0402180904020d0804060816020109020d03030b190605090102012307050309120d0c02060a05070504140102010b040c02010207020a08 84
    0x3500b05001140040104025400d0806640fa07211114548003d03280342d5195034005903085505028280400800c2e0601000f4080c484954010055241004224034081c0014000203440c4946008402003c1c0415191440741c0800400307107402a070646420b50b56481d266000b180381260320340d964084c840302c42280b450700703000f05d070b84000e030344a41c00c1075410740d4100b00074a04801400480c2d0180083d40c121740040e0708600a0300091000f07840b5645c0710b113401c0070700202c0c54800c408280116450405450010b9440c000d80c8092036030540b500150148100f00860300782c40c240303c584030b1710442210f00003a40755800001040341002c20b80c024800c40c10728007440c0ca181c0110b040c23240c1d0000030b6071000810291050b0040c680c049000402c031210380001a5480140d98461025000220340360320110203030381e03010840e072500000809010001c83c0340c002e070300524070f0140d0300802c00b4075024180043c110740e100f5000203102c06c0d001031040014007140000a4001d51210804034040c114070039000031020340c04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 196560377 1250 196559127 196559131
    0x31a070309051216050d0f09080706120c03020d0e01020a0e03160e0702211306020f100b030f03030f011a04080c0f040e0d0201050103030201061205030d0908091201090614 75
    0x40070051038010b080c1c11070b0080b1500806007102c001d421342d01c00540490400c00c1200c401941302c3c1c032010340c01d189908005012031029040780007141c0c416103040040d558400c04a8803441c4298400041d84c0c01c412200310003a10030680301f01401e42c10b043d4000c035651130650060801d0000fa8542803013010880080c9600e94055069141c07665101c0a41048071603483c816082c1d100750349106462440e12030b140e042c1c500104610a10504110210f080c86e44055081d8000740a0b00c50350005000c200e4503c0301c07056039510900d111441c05038072444034501944082116901c0d040b40e02c070540c1d8491a1650010f1078a000921900000e0f030380100303120720b540502c6805c88082c2d441120103001910408001c0c400100b0080c20b141d070300142e60340707074110400c0d4050025140d28001940040741c2545141030003801d45503ea0401454108003880030800520300100f11903c4081507040450000b0450400b00514094604400d40003901354054000c20501940002122403140908000010340400c54000f02c42c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 196561627 1250 196560377 196560383
    0x507031b0e04050a0b0d0f1e0b060d031e0201050a0b040501050a03170904090803040203060a1112090f0109140607020a02060403140a060e03090a1203090312020c0604031a070309 78
    0xc8005182080e403c034a902811100011407000a1103001c6a005c91000d04113844440c5410160010002401c01040d2504002c0702c0e690200402526585d8402001410b0039214440c85241c030000c05020302503041100c40c4d5518a12400501d074040130340a4a01280e906400514140c2a40040e1500d0311580f810b9910142035a20014119658400c502031200c40803040580d0a1002500b03d54840c0900c203c401d2050750125180d0416105161038500041c08802416007440e030100d60010740b0100780c40f03004400c028070180c151100300d40c0034207008800c1b080001550905404009000070701d809081c03030601c000f0032100b4507526402e04903101c1e08107080003075108008100800c007184d440c0031a100100b00d0b0a05039040e07070700b03650369150032a5905085400303541c0012507002030a28240c61100001c29040201c100c9843c0320b99001800c3d940140001450410807000c104c18541c42000f580c03000b180003400d166034882e100c0c1003a403d800000e14103c0308040240b4001a1043d1190103502001c6038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 196562877 1250 196561627 196561637
    0x507030309141b0d052107050d05120a06080303130303090c060e18010501020d0c060e07030308103f120903140f0d030209010212030a060e2202010f1704060507031b 72
    0x908044803043d006d81106408a001000c3c455540460010300803143d0340c0040703444032aa624942010320400a9004060046881c40c201d41007055940c0030003120750010039030540c030f0040409850268001e02031290061f1610a5204001c81c00907000f96844014aa080320401c2c0c0c1c00c10a019094500310f000d015090058002100d184179090280322840c0d41e861040002290140a5508107807500e00213600640000d1940c0050081c4038848030307988005419407807031280d410800040e055208000c3c0d280b03c401540c2030201076100032021031017200c80940d84800c0560111650013401411240c0c50f000640e014410070041e0740b4912400280a1202029080030b42328000c80408141c0081d040803c0c1c044c19405090092070035421031600551007840c2940000030800d00f080c43c0300a61010040c2880ca250820801d042c40130041100c00c2c2001c2642407a020360920080602110300712a0b124520f09000052020300c010002e1341c0d01328611408081c6d40807c00c0040001400c5132140b02c9000740808aa = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 196564127 1250 196562877 196562893
    0xb040b03060906092203120c020d09060306030f02060912030d02120a06031a0705090415080d050a05030a0e0a02121b0105030105210703020303040b03010f0e0f01060507030309141b0d05 81
    0xd017084110001245c041d003880c4161521849440b402e440704100380c040160030800f099600c80e90030041c2c0501902c00d41ca0100505803c50790ba81c82c0343ca8108202a10809010482000a550356881120802045005c0e6529080c0324400b190103034020800c088842c007540c1c0005184407903540b05107402c03a80c0100d070042072080c1e00b042d80e444c841009407083c000c001013004100c0468480c0d0060070b04030000f840d011103403140341c6648107007003a04040c1480c04000c410031013250b40550010581e9008041244e0000d6072030340c045511440c5c00385441c0001d400100881c28980c5003080400c45600c09510750801c1c502c441c858600440703041c4000d000b85c80e0300c04425008030140001c04d01100160405d6401195211134517600000d18540082d48003045045001005000c40c0e8140f502c0300008102e507400caa10356003842000e0f1500050140100b904000c80400c4510505200750440c2040039080b1034104020100c1c056000d0711400380e0b141d200b1801124215100715820680c48000059403c040948000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 196565377 1250 196564127 196564171
    0x40c1e06030509161205120f040303141603031e050405060a020705160b07030f0302040518060402090a03120f0203090a1a04030c0b030601081e0402010f0302040b040b0306090609 78
    0x1840082c1020100d84122000420880c9100d01c0410103405c0d0324480d0300c51098189081031908404110032441514240001c2624807500829a02601e03814104034654240c8190080300360701a4024011040103070308078101c20716805500c0414040c480380448131200b007103240c00d0350640b501640d000b00181d1200002036032484080c1d01a00c1154411400d9401002c05a403400c0540f4241d5004540107003400900c0004158002c10480221045401c0650500b8680400180794061030105585011100c400045159507654100c03004040010f105040c11074482c140203014008401c2c0c0381010800000341c0281c3c940c000010740b000744000414030b40003241020b20000c54000c00a5405c04070240502021000030640030002c406062050031060312171030118001003525502400b90b01d61080c8101804010304840d115242d840b680a0800081e178003280c1400b06c000384201d40c0280c92480001c0340c04148224160021401003030110303000c0c250707611501c1c00c1240540d81540e03920b00b0102c000c200d1200c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 196566627 1250 196565377 196565381
    0x50406120b040206090a0902040e0f010509010303080f040606120f15020f16170a0c17040b0a030c09050a060903020a050f0904060b0d0206160201080106030e030a0507021314040c1e0603 81
    0x1559001526001d1b02590300c0d0740100c20fa80142d000070f495a401041000040703510310030000e004240469010415514584018040c8000941f04003010f400e40400142804901d8001c58010120304804c41d00b807003030609203a08210f1030030104943e86400f07085074141e40241ca000792505d0001c0c48220034900900d0241c5c00000b45c1ca1071100301c030038211b602e510034240c00403213014080100325516000d0100c503080c60b098004640081c0065a00101070105002c000d00075025101c42d14994200001d850300010000d94a00140358005540f08201c0680030400b00e5004403500d048910a40705044113940781d804000018207440c4104d038001440400041c0401d0303241d00718280c10030001e044484082420b401140ca00d0b8000084900d2070540f9507451400c659109800c5401440545400c05c034915030340310303150345034030401c40500304200c800710790001950f846520740c140c0a40f80a6081000110811000c1d40c00e3344115415200505030000c00180700d0200100013540302c81410001300914145041a00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 196567877 1250 196566627 196566637
    0x21b1f110913060302061303060b091311040e0d0201061701020301150516152c19080d0f0b0a06020309031207030c022d12060601050c1203010f050406120b040206 71
    0x40b90f407110380002c0941c0700d00c0c3c005c1408403100f80d0100001e60441c14928291000504c0040c003a5105004114500c4109460116401c0d40300c8102d083c42d9000c02c001802400b50320070241654007604049a09003034055108000b2103901c4d01102a81000c0500c00a00303d010074401e00c0d0403214090410310784580f01b48000c0ca540441c40704c03002c00b01c80311503d4201020340d61568403061281d442103094600c51050307409880d0800f110f00c850aa482503c00c0b455210001c4402c1c42c1e100e0131964140d1701c10054614103440d8070b4034110004000c000ca00c0100d40380503100c14800305004843c120804144940f0110450b9025503002e03005203449a072030f5606400703590140b00c0c2502041a128188001a43c404250000325020f902c4554400202c0d0074041c4404603001410f24460500d0145150310303a000450031680c0007400342000380e1584a0790301d00e2400c06051007404a83d0303070340002c00840d5201e41c00340d40500380c0e14284c03001c010040c1c0300e040404507504c5400000d006041700300001401450014001e003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 196569127 1250 196567877 196567909
    0xb03010f38060c03040909050a110303130506030a02070b09070303030b1008010e190207120f05040f2c0f041a0103110f131406090a110f0904021b1f1109 67
    0x85d01d8a80c3d42c4160008607840040101c406801240b007100170301c901c0051581c02000c00b28099450810136400c00c80250a0328854940105000700000c0e902c0d05043d8195502e05401801a468a00e0410038840d16101c80e03000c2200801e1400104401c05d08040341c0c404120f000d02c0d221881182d08101402c40488002801c464484245003c940600325490010b050030310300c10f088881c00d9600c461000750520525024031810044140010005004d0030300d03a450841d49100107070030030301e10104070b400d4261100c0d50b00011100b0b10302c41407210071501c28055620442c0514180440c01060100741801c1d041d00384070191681c0c01e034001c119010300c0d10800301d001030354005000d00d00603c40100300e401034503c50b030603951100341240e040261a0900390f03401a030001c4480000c00883d0480c81d1180903074024625103000602c00458803885030380b16941103580342d00d010701c4880c2c41c88a88540e241d940e11442490341d0012240c030110038030045000d00540c0b40c1c12035600d1006091014510501c015a45032000203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 196570377 1250 196569127 196569133
    0x10312030f1e020d0b0402030c16080409230603010903091e17010e062203080c040801060b09031516050708281409030d0507060b03010f38060c 63
    0xc1c100300704208100c0140307440100c2c80940c888220142000803648141c0116001e68010401c000304604c9140403525071300f4401458440401e1941401c8a6a000f16000314503154984211142224070701c90404840800440b03202d4255660001814281c820710704004012175101d4005018924a50b1f1001401145509a0055441c2d4820400c01c01844501c200030b0582d6644102d042e0340142030041d46e0f4403061705004002c8402040b00e054409501c12107010b03007003020b12004a2035500940085030000d0809000911605032030b54180c200726070080fa1410b00c28407803651810318170100b04ca0541e2080c002c480c1c5210f0404501c050569295004171000c45100500300003002c240300c0304c0c2000c00e502e001640b400c8210030540c0391000d0054900080c07072203006042801180c40310f84d400900d00154154600c0c1854441c210392500c880a082c0d265070081e0301d5401d15900c0c0c00700860644c4822101d025140e0030002d0b2954134540c40420100d550312100030f4030112207124001d4180000104a004907440032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 196571627 1250 196570377 196570391
    0xa0906181d010f06080d08160503061201090803010f06080906070f030e0a05060702070803030907050f01090b0c0c0901050d020a050402250507031a0c19140403030e040e06010312030f 80
    0x4424211030034001241c3d6120790700c81d001d2107403200c1041011036940d0641800d004504090020200c2da483d00c00c070002c00c000d00000002c0141d254200803c141108100081c0409401c61a10003620f400034082d0220b003480c8032600054403482403600ea070148000300c02411031038440d80e408032030031555001414203042d21075903c203000441c20002c0a0b40140154042c101034144100000d003080c40b107900c03c1071558018014819076a00102e6810708685040b1040e40780305c40741d000180c40380b0500b0351100c9844580802e0340c040c0075038017040380c5060380e40440714401c1c180c0c2c880080080725106910041d421250007803050145c0e082690007880e1581d2680d50040e9802d420400301d100600100104171803a800c4400100100100000c8032412440340b20580d0495107094460200c1601034050181d5902c1820740e10480c08601071141ca105840208001e5641c0d1501c03030602516180814110380c1c003443c50441c00c000c0381100420f051303050703a510000702107454030b0710398084020b85800032003905c07683d40d1200c3c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 196572877 1250 196571627 196571681
    0xb03070b121b040806070210271e1b08010506031e0c060a030c030e0f07030605040f050708070305010510050f0907030615020309010e09040807031413140f03060f010b070503120a0b0a090618 83
    0x2005035013441344000c400bd8001c0d42c10b00c101c1303100103584105510b030304110034440203560101d0010b0b0104424901003a450305c00c4600e592a15410442054006800181d4040843d03030580203031442108544050020840d8181201d130f5130803e0a43d8030100d5044100c040c0001522504a1500b00303028816401007114207486150906a140e440b40031a61b01c80304081007041000c1c000c8a81c03116800c040505400d00c0c1c81c0c08540c140e142c08101501c60b61100c80080d5009000380c0c08880a007140100c00c0d61850101c4901959942c810351402e40030a9411f142c0c1c0c1010718000044d02d10a035030000e2414240851b40c2e4040d10f510172150610041c044d000c0c49103403102102d18411400a101102c140803a00341b8401c00d001c107024903400d400d8040e4100408201b6030403080300e4424110b5803030810031943d8a16034100329045000c1d000d4201038000314a003c2c05181c8070642c01804880d20220f078500c0c0003035074401412048550702c1c452a05140c4a81034001229040342d0b210518080781080d00d84924044c9003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 196574127 1250 196572877 196572923
    0xd030c090510082706040201050d02121501120e070b0a09030503160b01140306010302090a1404050303010305060108031306051b0a060f0b03070b121b04080607021027 73
    0x5850b600c0000c60003400c00000b40b1041c8040814840394100155421498640e015215803004101030705000c4002260700c006001074ac1103881000c24411080c000d405d10580413034418104410440c0040c122107209000306c0c0541c8281e1200802d104001c101ca01d1400d4440c82658214a00034014407600d144000045101031004004003001006540581c1c2800d1030300071800c12044e004242c0c900d10600b409103081c2c90002e007050641c0d070100d441011980e2014007800143c41c00d4555080d00e020400f080c8005c02030000b0145058a10a0782070f900d00743c0e00c4845641d50390142e1001c0305005d48403e5400c00025000b070004020540c118500d200c2000703520407a0310f2801c25442011903995a9407029030b45002c04510580c0c00c0c101045010b46005490202110183d000304900c006480081e20041a00c03e036030844d5000042080c0c1c4e06858413031b59a030700f5541d240d92080754a440580186048200f0054942c49122042c007582c01c103520080f00141d60705102010302c640e08603940c0700801c46086841c580c031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 196575377 1250 196574127 196574149
    0x20c0f1c03121107080304021504080706030501031a070c030804050109080c0606040606030c050405150d05010b0c01050108010b1c0302100e21070b0408031012060509010e0a03020d030c0905 83
    0xaa00ca00100b4012510074074111001400c040c00307140030900003600090316a004507a00b09070115845021142e0302d0718607404034400c9510200c0507100e811000134099415400ca24120790190000b0301e00f440025000580d041c074100c0300000042c0300c048081c00000e01458a041c1c2044c02800001904805950388501a41c00304110300d240e64480800c0000030728180c080d010240c0070902d418030114521810240050040e800b17070718451007650180340d4040211740c0582d090790f072040c1c1051005595420310311600c2d90100c01101050750070800040380794181400b42d408001800b400300c001c60303080040c40c0030f0380c2019201c00b00d0440c0030305d02c141c0d072a400300741c01698100c04000700a08102c6c010b0744400380607206000c1d1044e40060040c8291030110f48421031a81d441030300110b03a250382c1d55071418100c0361500f090704414181c0c004452300005002c25640417a21508285008100030107140202070303035519a400005006a00c402ca424190902c660440c400b606101e0810003006074503040010185109 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 196576627 1250 196575377 196575383
    0x307150216030e12010e101107080409140a0b0d030c0302010b031e16050d26030a060e09151906080f0a050c01050301030302030d0b0105210402100f020c0f1c 69
    0x68150000f070700d0314148464120134885207000b0801140400c02d615115481d00c01c0c100c0381d42e942c82041903a11a00358040b81d414550145580e5916500c07a554540100540e11900d510f06512000251010315a03200c3c405030703e0030003440d030120f841060f03034111202d1070410003c50444d501c1c1c0d8100310507514100025042c07441c0c1c02004181c410780c0e0910302480d1034121440750010100002c420445910344000500c55241c03c0b400440c0ca0403001c0c0b9205950007101e41580344420400400c01c072100655900050a03160300c10008041f41d1502c00f80c0e50b658111454088040440703a074082880f203005800c0084142002d100d000c50314607a00e520b42814115030440b03004903504202d005004002d030500c49a00c0c1d050013400c000741154116140255030380110f0601c902c0c210b50342c62003030300540c0c010003d48e09071141e820a00c58100c2c5d8482e100c1d000031402610100e009450038410740c42003a000d01081c42c0c520146074010050003011808110031030141c10401a0003c4042d04154504680552055102c2e40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 196577877 1250 196576627 196576637
    0x90201140d0504061a090606130806010e01080d0504060e0d0c1d1005030f03040603090c0905010605122202040506040603120504080610030c03060f0b030d0909060509010503030715021603 82
    0xc3d0070700702001502c4400142400031210280c0450499607403000c01e03034002105598054440c0302e10710368000701c2001900302240c00d01c5107000028079032880482244c1603d036400c040d190040b40140d0f0554450107140204800f0400321040c3e40c0e62030a03e03803071401e010390052219142c003595a812141c1518200301400390100001c800300000009083c0c4984005d000540060560442c05003406449004a008902c10145c035015400180101c81ca06000a000203d07010482c55035141c03406000c40c0d008411880088244a002500039685200088400c04c00e00c44000d0140c08070351708100062500400350380c0c0c002c0d030326803022010a51010780c00c90005900d840b00f0340d41e14144400f0781c2c0b030580c0c02800f0354440704024605000044000b51200200d9921410200785251b008481e44094031511602907014030800d80c1d120300c8564440c0da0035040b40c090042c200001511007051192a034401d0155a805501c100560f4001403101e101c0480b4100b107640e4014105034841e42e40c600d010030816015070020b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 196579127 1250 196577877 196577881
    0x4060b090f030705031e0705180901051506030a0c0c0b0f04050610030201050f0a0c051501180203010f0b03070c0f060b091501090e130501060b0c0609160306090201140d05 75
    0x70400503000198040220018003000d4540070001e69590010310022032a540700003c90b14911500b000140c000e03020041902c0440700000ca030300d840510007250503080540c2410007040380c00d0b44c820030b4103994080c0074140c035280d55541038880c00a04aa281200c1c10842c04540440100b20300c040c8182c0a050401b4102030345090500302070b8034051001c0c12800900e2507850003000180c0c0c101045a000c200d0000c06180c648210040594480030002d8028209002e02500b40f40307000000b4942a041c4c40396410050012454940c0c4907049010074001c10146101c86030090103040c00010145d54041011700c2c00d003008600c0d59030b406d0381144501c0c40450749951154205c039a540341440380c1c00e40c810045540480070b407079141d0009080c031f0094445c441c110f0140001084a603c40d003240b90035150f0700000284103140d900c01564703100b680300340840241d5000e200301150100c0030119a82c3c8183d550540d00744541802c2d5202c240041030010412411300010a41925129500e00040c000207400113400040c64 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 196580377 1250 196579127 196579129
    0x121006020f030f0301290d0c0801060c050303130501061a070309091a0f0a05060a080405011d0a110f1008341d040213030c0609140405070c0204060b09 66
    0x40702180340040500d030002d00982c0f4000345100140e0f4110758981c186600d404502540300100620750500070740b41441d0005040004c0301c13682d0041c540125103655854138580e6207040899004101030001441d070b400400200e400c186801080201d914001ca000041950382c88883c00f61982c0c0c0d20001c0888420080b40c444140341d084100c9900800b040c2c6000c0c0101c50800d03559145010b08011108d103c3c0300b08400440603030302e4103035118000e0320700034149a554040070346000d092000125001c0340c1542c2003d10b00124102d41800841e11120f100d8001c00041000b592142005040030402940107941085803951550700d00c0c1003005010801c0d19004204d081025260b10f1010561150a480041c2c422400880c085507003400c6039820b00c10314211801c03140078809155040c242c0d0102a5105001203100030440308007c0d003130b104680c800d0364100102984c9180540b003032289417140c01d04c6681e041c0e20701c036424100b03900040d0340801a8a071070103a69504d540010203c5803141c00440500d940800c4a50007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 196581627 1250 196580377 196580383
    0x6051f03050c0337150504060506040602031c0b09040807060c08250212040e010e07020609030405010c0212100e0d0e0f010c0f14010c030f02090d080f12100602 70
    0x54a000b440c81c03440c0782000500160490f2100011428008003040fa16403a2034054480b070300c0c441d134040600000700511004c1c6800e05040c09850f228a140800004640c80d001e01200d0440300c1e95005141409281c404a404540038083c80081564403018410055600c0569a910441c45260059200d103404e04002080f40e80303c81840b02801804001e00040c44001d441c481c8009041c0544040d00c102040300403800e003030800900003014080400e0100c5ea002465000a044c4c0b85044560302140d41c808904036039544080e9624110380c0c00c00c01042c00107520901d110382055001400b000904001c40803000d2401c07100031443c12505a03600d5122150641c10300c6002111403152500e501c81050002c0080c042485840c40c013814170000d901010204012207200c22011600300c50002003000c0380780d420701d0181816001090000b031915000480c00ca62520940e400510060429881c11032540d0380c105169016291107003205400b40030b400d0070203040c076019501c0b030004100407014980c80e04201070303e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 196582733 1106 196581627 196581631
    0x406181a2205070801140403120f06051f090816090509010908072d08030720010f0b0306010f060807031112090d1d061c06051f0305 58
    0x20a0000c0032403d1021580e40900a000c1034a25000511b03140c2d108a40c0200801d14000891100343e4441d130000031180c0860500044058440c00042c1e6019551200040c941d94000b09040740c0300c0d8450100307001000a00000d0240c51011201845000980e00aa10301e0f503a80c2c100003103004c0002d401440d2032a400032440d82d920400c60034117010f41150030703480f202c924040c20ba0018099450800322056207800c80002411515048411510709540040d4001c1d040300240d001210140300f80710744401e0412481c80050500c046105241c10b05805074400034502c103100e0020844240c22030855075200203145000105907200c480b040e0f82c6070040b14440a00c48186200b084120040043d4441913907825440d1864000d840d00015805545400460b40c0c0141e41802100c07a0000d0b408030781260b0a0a1010100e0171a403101e0205020011241d40110351207000031018041c3e070341520a041e = true := by decide +kernel

theorem cover : BRFrame.Cov 196402877 196582733 := by
  have h0 := BRFrame.cov_init 196402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 196402877 ≤ n) (h2 : n < 196582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
