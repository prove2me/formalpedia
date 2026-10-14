-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0732
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:28:25.362002+00:00
-- url     : https://prove2.me/submissions/98af1143-06c1-443c-9f1b-74a1f6f7a829

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 131474820 ≤ n < 131654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 131476070 1250 131474820 131474843
    0x706030e03040f080f0709050c0403030e030a14030316090302060708210702010506040c171518010f05011709061b1b0f070807121202010b270109090807 67
    0x64080e851030145521030200e10000281c00559460702150070070701c2c28280c02c01c0e03076501074490380300c90b05a5a040d203c0e40140c1404000410101c1d1040700c0842924400a064500d0401c0c2c98941c84280211741c3c103001c0302d5410010034402196482c0840e60846030300d41c205030007030902d1500011558080c000029129a0b4001001c601e01207810400c4606100307100c016941501700360000a0007003608581150180c0d150040392505d9a0181e00d540c0c00d0b074070380280d14003000d80d1804040388030b0b00e030368410340c0d030f0410404910416521003a1907264060103070310305c41e80340441c0740000040500c00c3c0b80d4048110380c0b0035071040c010003c401052040e44150a990814001c10125032014500d1050b000071000800d41700b52416804680480e400700011030300300450f80c2194450310515224050380c0b16010b007040840b200c2c000000d40900c60102c0c90040e60000107041d4110740c0104d500c880c060001c230724207100174400d50a881c2c031030120114050722841804001c28079055640d5140c511071080013400c4060300304c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 131477320 1250 131476070 131476091
    0x9070f090203070e150901081311100e0301020406030905120703090605090a030204180b22030c0c092309030414040207050106150c05010f0b010816170f041a0603070603 74
    0x244c030020f56008002e0880c2c2c5010040881071032403504007150183c005034980c00450840307001d091841042070707003120b101c2083c4122001084603d20511744000c082c0400d2950f040081e0f90f081c8050001460161408a590000351626604100340c0903140380c2d002d4818001c0d00042a032021050080e0740081c2407466940719468002590524980d200079071090401030708a41ca120704880c0410210320034000030110740c68a40040384024000c2c20b00c1d111000202c007231000071030700c20450342c1d251307a01401c40c1c0c10160362150920300c00d40e4950010090300c0d1021412042101405254550780310301004083d42c189400d015180e0000c106000145110703030340110b00310091240070350144000b01401c4580d29440202008054901e55111006503050352a1813108034411125000d80020a04160b641c6042d46e965003190b00990f6800d4500b07081080b0740c1e100c032283e454a40f0810b0b640141c07056248000c0c2481d203880c2c650340c2448040400ea04440303100091094603100000c1c04002c0c2d44460a011485c800728 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 131478570 1250 131477320 131477327
    0x305130f020915091e090706021b01030e100501061206060801060e0121050703180f020103020f0d02030705090a27020d15150f021504080a0c0803041103010509070f09020307 76
    0x499555139408240314044c0015100e10329001e544002c0e1411a0004036a04d40d0f03e030540b0780702d45100f103c0260708071340203001645140703500504c01741c4414113001070340803455010f444c6400164030380b14212942c2c1d0302c014003030160040c282c190a6150182d00b806200d040070001000300700c0c18400c50041c85060300c030441c45680650a0841c054003003030010b00f0640c1c41134000c0030141c00150742c0b50300071a02e0512504d9861755411a07103512280c1220548208840c5507004500a41c41064070821103501449520015007641c002540070f5500e0350341c0d661b2200c10000410240c4e51071623010b64041e2101c040d09071000c2901200c614082002d40d0b00042c1c517840303424806005000302a1580c8419401e00c800800c02d03440140c82004000e070199940b1004441203c8141d9441c8076040c488800c02c003040c0000390008083d0001028036500320b00e0300e09000c0c10705940707003015604103031003c8030300805103e45000181402d00c44c3d00d0340012403400802a20b89811100505e010103406002049900080001c035104d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 131479820 1250 131478570 131478601
    0x20906061902070f050a080c060a030902061c0506041a0108100915090501060e210109020402030f060906012604020d021005030a0e03040f05060d1401150305130f0209 73
    0x381041d480800c1c08010402500c0d00b025008900da60003400c080894181000c5803650240c4040d40b000b401608040e178100b12568001c503500300304142c1c443c4001401622800302500c0655034aa00c40c0c1d9401c4041c1001405642004000d94003562800025842030000078206450110080c00c04140700d49500c1003441081c150364000030f04090400c80031001344020150108201c41a0140402c640c3c1d0305c0b41c00840e613620b0300d05c054690085000e0138400c02410100c0000c03503000381e04000080d80b14115408101a6041107541000d50003040302006414108651010b910000902c0c046d041c5451001c1c406035099060020600c03250715200c00242113490b02d5280012440e001082e05000161414000340780b41c2c07003101e00c0220507080c2000c04120300c000000355000d0381c42061417000802c3c10f00b4140f040350303000900130703000c11600c40c00f810359000b21012415003c0d00c022442c01803c11070401e005801c0c0c40009d4070302400d01d00881d03100d01c0801c5103128200d804580c100c4075400c0e942c40c0d9102c4031111b540c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 131481070 1250 131479820 131479837
    0x121502090a0b180f0d11010503101e17150c0f1b01020a02100b0916021c1e05120412020a0515040308060d0308010308090a031704081207050a02090606 66
    0x100056000840100c04820b0301d1491411030b2031800901403a1300340400509013000040c8001690680300302c456015030040c40c2e000505001c044413543d9192400911141d40c0c015000018002c44002d105100f4446100020261410002d20658007026a0403111140042c03810150300e4002c240d0088a1480c501241c4581d030002c0c1c0c8103086010f030100c4c454001c1d0310109040e8003511485507a03810740c0c07242c3d004211401d035008000c2e0344144e981220450042135141021400c6014a4124001d1001050403d951070382040d601d9103c2d03905c009209154442041c2a500c1c28007000344a200700401c1d04c5403419510a900407105000018100e01c1a0b00e0071403140c000422600905045000d100200c6207000d01c1140659110034482d19202c05102d40729410401c0078000641c81c50062001c43c140c10018803044e00042c02d5140a107a8940b1080780440000c200c50f843c40c08001b42c1044207010070441c102d15803030340f410341c07600d05440c076610030b070ba145800d09000b40904241e070001025035a8a5042d542c00d41d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 131482320 1250 131481070 131481089
    0x1902160206070b011707080c01030209270105102d181d0f01180e0705120609010506010207081b0102100911010201110f07030e0a05060a020d020106121502090a 70
    0x3402d00d80b918041c3c000d424010714001c00d54100c483d0007102000a180c4c0d003165148806007600521541c0110040d40c84202100d801c0100300c3c9000788070508403510be00171400d8005004c0e1a65050104100e0400c542c042c1c0c2c0400c00405d8100840c1d01917070400200b4255401c0ca010026890b00c0000503140981002d5120398801d5490200050040c2c1a03880b61a044c030b901200743d030080d07942c10343c2c000d44444280205500b019452150f850f17034100c581d000310070301074000040725555503070388001808040c00074105c900160000424460950301c24000c842e04690b00f40040c1036001d04110b149540d0f4900154040c0540503901140c00450740240f0280c031400d96690800c0c040d4042c01d040100c443c503040c1c04500d005610b040322110a8044041c207440010031000d003040d00c0c00d800c6442c1112200080d00303e05500c02c2a02e04005225510640103002504103a000351030154400f4001031f00f181c1e6640c4c0310307a1851645980c00d200140c070070b00c00c00c02031100222006840da04403101161030706981c0e81101d5a031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 131483570 1250 131482320 131482327
    0x13080406020304030c080109080904021c020a050c0709050408160c0f030812100605160c090203040515010e040305070b07020a050a20040207021503040206070516030c0b031902160206 80
    0x15075010004005807400742d03020840b4199264115400c0f00e0306403002509112090100c2030440c0f42680051590750301c148215040301300d0b101010000c90707000c803102d400410000240c00b0164001403054600900f1209010029860291503010551188030016580c0807201070144e4200322040102c1005860b0700c02108103003a4891910f00b10b035a010156892507070611000240700403103040d480300d003031721101ea681c982408254044075000070315003001181e031078800540102f1881c4192003e03500c2540200700401a150307151f02103944940c01a04209074a62480c0204001301740c01c030048400035036220740e00b000f032952080002c03402c001010718020024003039003000f1814403d0f89803400c00b00700c0c0a015071640541d0601c2c01c110072441542c00094002031074a03410306000200740301075540a4000b0740000d10300301b0541d4845040c0f028448030f0519001da07604083c030601612140380d0f8040e14004d5851841c5080002c0a540150007400030349100c0d40d00050a5824041c0b00310882081750b41c090f125644 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 131484820 1250 131483570 131483579
    0x81b0708070501080c0a0903080f040905040b01050f01111203041e06090c0506070f060b040902090a0203070206061e0f0a05030a050c030f030a080103060507210c1106070f08130804 79
    0x111896280310b182c0c001003030800800c445400402c2140c1c5050260b031280000d8030315503910320035290025070480304054010b1200142203103150294510552140f100b516056040004014900c00d842403010304100360496030428440b030000d0051240381c54807100544030303030f0b6902e00043e11b007020203619001300d070f203640e4140100b088640082c03100510640b0128400e5480c6c20520070716000c1d07184050f1000c0b880ba003170080481c5a6902c264070751075000c0c0000c203640c0e102e500400c1c10b81d0407d46052080303560000030802c0140d818460690412001c450324034003041c0d90003490000b407000c8032074a4824005040003003042ea07154160580203010140030382d0814612400e049460b17101044170540039004c0c905204181140c080210742450005440b0b10381641d0964841c1c0d401814000c01c40814461740c00f07090300c076070300e80349014034850380d50340a0100384044044401860703850403404145490340804103004070580c00a600c1c42c900c100c1c91600c968a9541c08074020050386c00c2a50180908200040104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 131486070 1250 131484820 131484823
    0xb07020a090f05040501060e0601020d0c05070f0f03030905030c090402091503100b04050108060103051c030603060f0504110d0c2c0703050402120601030503040620060c04062307081b0708 82
    0x9200f05d0060008008032995040c001244120440b80702e0b0058105c00307003400c501c9026107590000c0070302840031503680b151106590383c44214140c0210304040c02202c020030805500c403500c0c00c086c0400b580a00048440f00b07001c2144108081c0000744113030821000035004400403500885070700001001c4900b05800e03200310000401c801c01e40c140c0036605017400070506d00400110141229400030040000750700caa07038460b001007a410142c404054442c00c0c00008110f0a008040c4007425005001603079041c1441c001c42160071009880d80900c2d81400541c01042c012480c02e01100d9030b40e02c03d1105a080d00ca2809041c98203103200090540b10b1100b4815050fa241d8072580c401c0c1c0c03080c0d44040051040100e205c1c1c1d01c0009100060040d40100828480d1600c10010015084501359105095281c4040e6040c00c00c4400c03103402c1500180403804102d0180d01c541600c0c10400c141f85141c401000c0c03010004210b224080e40502032402c002020324452408032150320280c10041c09031441583c480340c10b107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 131487320 1250 131486070 131486081
    0x1020a061a040b0409120c020d08070302030a0e0d170f070b04080c0717031e040305010f14160e0f06070b04050d0f05030124110102040603021902160b07020a090f 71
    0x490140c3d1820350b05034104d04151290702c44164001e40c5000710b64070300c01030031100741c403482d24101c0e000400685441c0000307080030b024040540c441e030040c645540c90101c00810301498803c51034030448101e400384005c5000319401c90001c0001840b203030746d1168034801d1040c081c8035080004020400b0361013003000f8403103404081d18046100c2000d58a180f5514452030b042141994540003064004001c50b01c00204620085014600300306456810f165607038562500f120a4060f101403103176221189000f01c46c403080d0300158448841c00070407011100c3c03d00001c12040307144094501842c0e0103001c41010b40d0790002612030072540700502102e40d01d05460003035114cc1411318194003240c042d07440100e0b01401082501d051302e15a200400444818045031034040541c1d14000d030030322800d5200d00908807030030b0008101074941600c015981d0100c80465182d80790b5144551000c41d0003009021403c246c444000c001110300d00740031035032070700d89900004040555550007909858a40383d2200c8030f1101c1500007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 131488570 1250 131487320 131487371
    0x2d17030408010e0111030a0c03060302100804060b0114040e060a05030102041508060f1509040b1e0a050d1a0a1803030606110615040e0106050a0305070e0106031b0e01020a06 76
    0x902407080e0b0f101c3c03414240d46480a10240859050000038100800341d8800c030180d45d000d1030045070441c0d81c2e0b004a071a03040c0e01011040007585d50001c01003400b0f8607020b10258030600f0b2030700343c13a003c0800e86811854011030040003c1a8207020104103a9a6144c40c407201070100100215540e555911680d21512a040e6400002c03891a0740000e21624104c2510381203000090300b41c000f0318140480303201050b032104100613405961142d010010362100100c0c1501c00681c4504500390f00342e164100300603010250700481c411191a1074410000301c0b40e40d0600d01009006050354026100c1c032070540054600c1c0d100803006003503526100fa05055141d00500704662007034036005200f01112040507140d00d8100c600301c156545541096105040a5015420460a81c0700000fa210780340c07800078140404a6200340c96030750001905101c182080f01d50b490041c58642010000c080c101c411402d03600c890780f4516800d02004201508417a4000d0100781c62036a8041030411070300034029082c2d036071103405800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 131489820 1250 131488570 131488573
    0x1080d0e010f05070c0819050d030207172505010b1206041a100b0a05041a070308040b06120102030108151006020706050a050f0a120608010e0c210d030209030114012d17030408 77
    0x20782c880c0c5c140a440cc071131880d9080003c0d5490168610f044203459130041c0002c00b82070104041603049015505690740a50340f040c400803a000c001d0320200105407540301031440c55900003405000000c3d404100310070300201c3e0111b52496aa8811800109444055001c08a0058000790750000154014010800c1d03506a4008401c21280c900c030310b040a020740a801808262040d0125011420245105a0002c4014204007209081c002c03441e00ba42c10a80c0b241c00c0f1039104a10f0300c2d50a190852005600c1a001403580243d28904500250740c6d010302c0c403804c0180000005d04800c0c3c01d1040007102c1088441c084180d0741e034041c05900138800b15550400c44481841c082d40400c03512410300802280400c0e1000800c076820081c0100500c10038080c3c2c90000d40881c0591007101c4850510500a0840e03240c0ca005840d920064240343c2501c4005908652040071076005120301c007186078460581c0000301c0101c84807070600c070000380c82b6181c26401450344102c000300d40c0a500c010001c01170050782d54510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 131491070 1250 131489820 131489833
    0x605100903030507171606091e020321160b0601080a06080705060d020712020a03090e070507030c0c0906081f020f03070f02101401080d0e010f05070c081905 69
    0x1800c803030803800e9000050006204011401c003042c070030000131035090200d503c014a0040f0b180d034040d0071480142400c0b0303201c9885003843c409115440d1150002858207642c2c6c07c9012255a0001b925080420300000a2421601c0116410500c040c15202c03980c0325140c2010903d0140d050030070725032100300c0d141c5000078550800201c00b04a03902070300040702c02c4400144040390030300302088030a8010121503140340340e09210850110b000e200d008400c00d0001d030007070300140c226801c0003040400c158102494085580c0c080c4403016600c141159005909464640340304662443e2441403411554004210682001d101050310f0201050312070a00c3c5a1580c2403000386210801d01c0b060b4001c84103000592803062001484260282c440d030b50140c102407055540340800c8100c08021503908aa0000f95095200c0c010300441c1030422411034000010f041011000111741c000030901d141e200c105208000c0c01050b80410020045880e4016105107004d075202d142802c2003503100d400b0002000d40e40c91140742c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 131492320 1250 131491070 131491099
    0xb06041b0c0503090d1406011502030a05070809090403091403010e06010e0601021212060a05010302030603070b0d11040e040201030506012604140f0c040b040c05030a0507021c030605 80
    0x244504003440304542411052801048025201da00301c0c03890a480710300080095203080d41c2c03a038062010651144040003590080c81440e1032800005800200a040056a00550b80c9800009540201140340780440da10200703803600324a64000c2a000782e4020400b04103000030950050042016203107001c41c00941c07800f0760030405087c2c540408141c480741c1c01003401030003508070f402d280f181e00000c180122141c40c04000707003400040d400b034810194140d201e0418843e59280c41d110041c02440c0034682542503040c204002900d034107841c8920140010300050b004951241a08050001e10301004201e032543c0e900c2080c00e000520407501203000a133042d002500c1c540c09602d100004010000030a00700c02072941c104000c0401c041d10588450401c03d0f403400303100d10200303c01e4103d02d41d44000741100fa0003602c14042540d280341c0449120794203003500c00d5103480c0c1c0903040d21340c801c043c48804241c686450400b43d0070035450b14086d40c00908160440846190150840301c129641034030060040482d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 131493570 1250 131492320 131492329
    0x30b100e100302070c140d02060d0c0e0904031209031101060305061b03071209030207171f051303030b040f02040323010b010507030c050f06010807030c0504060f05100203070611070b06 81
    0xc444d002803c1404c919014050398034141c1e0341540b2400060400c00c9030b004990005a07041c0c01240300102440e0b11000c0404c2244c0d4010110b21002d40705551840140c00e00e998003800e4a40b1031709030182010341e1500801c00f8140305039a490a100700120003001840d8490a203151100b030212042031070316100f16200d401e001d07005030480344150b4040c0c1d107c51550b016104130030050700711220103a08500c21003078007042c000c0c84035100c246070725280c8009160184803001c0d07681c83d5400300311540d0700c058074280c100300c00381214007082c500b0745500d45000200b074110034000074001c12038108018101c2e48041008403c01c0b6211207003855440021010200e031180b446086030a0f50100c840d524009401482603400007405903002c0c08060744100140e50849200c00259490704100b64810030312a80234030350800c140141a044140503240a640900400303003080c180c40e124401c94480c6500030f2015610300d14042c0d10a0098407405030b80004103010036008194034402c00d170440b01054441c1d00000c004a2128500b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 131494820 1250 131493570 131493577
    0x120507110714061c02071506080d09060f0c050f010501060305011e0f05130902092502010e030301051212030a02040501090509041a090f0f10050115091401030b100e100302 75
    0x4104a14040d00c001000303040e421410007044d14650203102c0c00c800140965a1b846030b50100e8113002070aa45024504c0707181c02042c0e0360004c188040d06605110480e8000040c80c92401203080c084000039151030300764600707245c01c01c0700101da5207020008640303e6815041079040300c20380d00001c040a101808444480c00c154805d0a140300c4504204001ca4107000b03814041c440311004000406e030b200c640100b10007107030499034860b1480540307030182c9480d26011700502c2e284146200821a407071100c20140d1342c0c1d03c01030150710700c0b9051010240c1e0a05004012103010300c4101000c0c5910b0381050030f0503001030740040c090280420003662011500b81480c20701d0783e11032500890a0402c070f1030b20b1035001002c2d200142c0725104500451074a130140355000c00549103c652850010442c9035603594013001140c806801030b41220f4129030340001c8d01030f0f010408809407a040440390140701c01d004010703030052071440d459940104140e80424072403a0040d1054001032819a1003c0001c0d00343c3c1c104404910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 131496070 1250 131494820 131494859
    0x61b1605090c090d0602040b0d060e010b0903061308091903030801090e0d0c140703030c15020f070b06010e090c1c18030804080d0203040507090b010f090608071205071107 75
    0x9000f20343e4580381c80a44040b44501a0500614203515400301512540c0414086101035442d13510400050742800307080da005110300c9902c06c4c100500540040e84966003e0402e440788080845c46c0401d000b68442150807440e0001c0100c0100025203816030030f115001c0c1300a40220f04d49500010b400341c014011081c24960303850141c444604010800d0711001c44884d01a00c030b120941c0b0006152400412408000c2e6009031030364810307220300341ba000741e00045840364101d85c2030062080c03400721340c11801a15491648440c440020b0341e69000102c6100380d00e4030799154010004420300a80ba440040100740d950407566090039107a0401c0449819a5000000e007440240700707100f500046482000f03800e8125101c0c2d102e90349001503903c0308400381c0c0c0041d5010740369908041d104020060462003511941002803e10011500b0754240282040c98903104800074030031460b00290b04c852103942080d502c104040c104100d1420802d00007812044a021141036503c10303c50b011a000c2d000c0300e4a0650300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 131497320 1250 131496070 131496091
    0x4030c2d260301060203041a09090106050d0b040203190506040504050c130617010b0109060305010303051204150504050303060f15030a0c200d030c18060509061b160509 74
    0xa400c80d9032940030025401110400010340d14240c0340021001030015402006158020342c0c9841c00c20302c0b900c0404c8048522980c0c076070350410102c3c1e81600c590034030f58115211810213584811040b0000c0000c0c1200100d000e82c0248000700300700c3c60701c501102e0300161003d0240100141d55400050000700c40c02030341c1c00380c9560700448901e90306140800c241300c0709680055002c140556180881619406820000820382c4d441e00d50508840d45d1200d6038900900161031305001552560310082c005100307020320190f40f10700c40000501030107031141044026000a02042005103001d04080382ca0750020360780e6500c148103946042c1942e180920040c42c5414503440304515689403000c0b0840103002c070955a009200c5900d001c100a6000310380070018084d034a4014108066245070010229003107109a48107105401c000c0380768504200c0089019162241041070752004208001241750080c00407207440b40001300840820f1070404107101d401140b503881a84622900c07082000b540200032210b94246 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 131498570 1250 131497320 131497403
    0xf050f07090510020a020a080a03080f07050913020702031009021003060b030c090307051201020a02010507080c12091207080409180f060b0a0f24020706090b031503030304030c 77
    0x18038043c001e08007443c2803070045901601c195800704800055540c0044103030b8221150040a064000100c1a4042c0242114249501d41844090001d0281b80c00301400f41070319000302d20700c0a0b160741c116014070342c004089680c07002900c1c903000c2c094040400100c0c00f07441d560382203240c0c40e03000340255002da072040c84505046d951141096100c980242170788a40c144260040011942c44040d07142d5811400c607000036907a078031404c0c0060300395080941900100801c5a04010030544842c003507030072011b0001d402d003030151110440585044800803c00c401c2c0d540002c0c0034801c0000d100c0c020800c413201850f00340086c80b030036044541100030300780d00500b00b03141701200313400060072035800300a04c0c02c00141307942102501c0381d03c1d00d0400443d540055060021a5120741411440c0701180300c9917840500c006c1040c5828540700412440c038a110b250300d81d080100115000c0150030b120300200307000150403031b80c681c54107040040c0440400c26094035000414140f001035009000c04000c01c210704103182500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 131499820 1250 131498570 131498579
    0x61505090103200c0303070914010c020409050c1002070603060b0301050a05060f0f030709030b10080319020102040b0d090309061412060414280501142107090f050f0709 74
    0x50b04600800d2120040056143c1c54a041804064040d0010b08001581c030b030300d400c0801030400305050f0001e0600c500240180395a03aa400014031461950555010818071140e1800c1850a4009062950b0290810105144d043e40c00548101100c1d500e980600c0156550181000340748800e00845030000ca4010080c070407410300400800a802010b03420030300c5c0210301d615804e00e9800540300800050300c0b08100f0418040000c19a68005c0103028980c8442450101e14654074410502d0010802020b05985003095000303505070b47c000d06c42d140c540b581d603030b0090030454003e080d21401240070400c0c5a02c0440ea05110701c500c4017041c50081d84040c83c1c1148180602c4201400502c4650b00c0394aa03007011803030b40d500c00c0085010b50359412915518a1a04141149000c00c6021821179186850010410a111440702e10b220500a49044914100d850400840d4144214001e0450700c00c0900009211103564800a8000c43d0408104941e4940040120108405a03051800079194600a10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 131501070 1250 131499820 131499827
    0xc03100b03070b0c031e0702040c170412031e05011707060207140f041a010e01020102280507050a05060601021b220605100206011715150d0c090c030615050901 70
    0x11800d2450400c503400e1005104803c03c0c0d06d2800d040c0c1e00742d002400b092150450034240174100d5240d1071410100d051034260070512860300300003000034010403050316070307540003602a60001c2981e1035008aa1420000090303600c4003c0c2000303202d402d02c042d02d038074801c900552010610100b0350381c035580542815854170180381c0c05042000c01c040d40c07100c1d080418940560711071041d020f00c4803c0c10000d4658206075400980201e107400e21403815640100078005040340e540c4000421100c040000011080c40e2540840d068010900021b000c0d20904030315005100d000500c051254000741c0c00c940f07889000701400d440001341c00e03c040390803401211212541c000c4012108003405644c00700010711a59a0340042c50b02000c024a46002d41c1020006005034a006e42d000358500720800000c10881650310340c03900300c1c1d440080c40b807070340100f0103140c40c0700d142d07103060068170b6184d00500c010f01e6068580c0d0f1170900801c0e08018803000302c1e1a0140010307102c0c44002940016030000e407943ca051111280064 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 131502320 1250 131501070 131501077
    0x10906050d0b10020a120518040515040213080c061e0a18060f090b03040506010b0304150c030e0606031c05070602040b030103030522030f032607020c03100b03070b 72
    0x41003103521942420b0540e1039400c01c800d404a01580101840d00c12410042d13000a022010790041001c2008856001d00e440d6034401140e0a082d20005115900d0401071888003c2074a045503120b400003a4451400404200b041d00341c6802c80144d0340c0c1030341001c0410900c0c4c03044011680040c0180e0040e1102c4a0400d07028204d003105608012400c0d419815010b0f4101610f030f00140c0209100d600307a00c14903a031040030070001e0040c50b89080d10314181034403141c0c1c3c1c500c41445128802c003000000a82007007260000d0f4900c1203a0840306200c00c0155040140c00b9001400303070b04285101c0c0d400014000d290000c1c8142908075071100c51460000010403c80c1c183c4c1c8041d80a51340a9020840020400d11000c0210700941c0070b43d03101600c80800c02c40c07207a05080410f5070340d6540c601c459018404104104c0101101d1589400d00100e4040b4a0002d10090b1604982e17030314542c40e02404109550b034000c02d841c1d0070b1400072825540032032010b03030141040f10000c02c42a50141d200f104107200503184280203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 131503570 1250 131502320 131502337
    0x309030a0609030c24060503031309021303080409091104050613200c010e07060203120105100e031b030f010204060929031311040c051c0204052d0109030201090605 72
    0x2074400c500c131584499a100b180064288001407911049450221062081c14007a002c11030156290601031564030010701d409005046007103900182032075a540040c0c0b032140003035070720400c1c9a4a86035a140c242c401080445020740b0080c22714440782d845442c00c0d01c03415204120084c01e4419806211301c0c090000c103069603410840a102e081300b50302d01440100508000011500041060107222105038186007050740601305640c0284158041c00d035506a1280c151942034a0b401251a4505c404071b4500f00c84c4024076400d806548808254000d40070f04440c011101035045402d14a1440da00d83c1c202d120310b00c6143c0c0000c10b112401e001e41d80c4004003882d01d107070980e980c5e180c4841d05c1c3c442a0500344e000750f503c003145038002240f4070200704601070031002c600801c580030402c0c000c02c2c0001074010300c50000040460300c00309550042c100c4032541500c0103048050b180c880c80f11175580120031103135500da010f840c40410350080750b035541d80314100503400c0d21f90603550040610324200c420748454002204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 131504820 1250 131503570 131503577
    0xb0919110c0606101107030b07050d06090203090c0a050a09020d0b2e0201050106050a08100f1e0905040201020c0603040602090d150c0201060b1b0a050303071707020309030a060903 79
    0x48011499019034090040d19003860050402070030020100160400300b0000c030010700103c0544601c030107002141c6882141c2c0c00500c0304a50703903034490341100c861040b20a411001440c0490101e00001244d0195201d402500d007194810a58902085802840c501c03075540e000da8240070600002c4615000340002500222000c2074a1904d40006100c40c084540601c54440f155079072695050800d0304116000c1d0000d000800c240d50400c88020700500c80e5000150078403802801042074494520f2800d0010207000c80340d81021615140d10a19245006400640a441c0d0083c0800c4140e024400e40d4061035058008188d00001c420030301c00503802c018002e0320031650034811310b080c507100d000115001600c600258804103000030319103001c460050445c6400c682c50000c0034131405105204443e4244034500302401e0140c0f604131018607003a00340400030824000401400300b07141c1c110780401015203e220b200c903026624403c041f0b070340c0e01510049980c1544007060880100d141a8050b90b1070074003a18 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 131506070 1250 131504820 131504831
    0x1101030509070902091c0605040b0705181002030d0606020303010f08033a0905010b011215050f0625060c050c060103030305040f0209070f0315030209041403120916090b0919 76
    0x40d0303500000c194106c1c09a40450b00e9000300002c10100920981e40310140e82030550030b0411082c5904c0b03030701e0941d1007014000d030780340049006518003c1050b20075041c034408017408000d444842c005e4594101b0f01c2a550355a20600c804038216101005560700303155a0f800c0484142e48400721240c4c503029190030b00d2800c003127021502199442501508002c0340c02000085240c290580c0010010000c54050034031042c60a5000c42c1803540c2e0081c1d4034102c482c2191030400540d40103000601d1886440f00d12100440007440130480c8620410103000554082e207410408070180407000c0e2402d01c42c580d0810602d070441e40052001138044d900c001c1d003144c081d504440d50078000c0d40c04180d00b40301c00e07141c41c1c000c03461403a0312408130f50b030501412614004036a0318aa04074655030200d0020080940014506400300202c0164500d003082a81c41c043c1040301e028402e802e02c400c8041d2161148d00b84851241c418030f00108204915014056000c00060a8140301d503030380400080300c0c51440081c0008080d00c42c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 131507320 1250 131506070 131506099
    0x726040308040e04150e060a0b01050f04030c03150501080715030f06080604060b060a0210050c07020d0b1803030606040909060e060a141806070c1a04060504110103050907090209 78
    0x7507010308050700c1007070668051410700e800c01149540d49400000181810700080c500e4681d0082901c0703401440401c004148480e081d00166181e01072082d800b840c024000c100001400744480c1203104036405450352441094a8010f29030944000740100c1041da40004810064841c030308070301001404181c54006921031038000030b002541d034903030712000c501d62061052205000c103501c00d01d0044442111800e18042c0c940c0c1e000b0f915026403041e00660540da4400107003612203c1c008541d002540189010880e0455203000c00222206440c80420b45098805028030b1140c0007048a028100060400b81858604410000a4020504102c41c01c1d6103503a520040018204201c9009840400021682d4000401c1213259080d00030981542401e00100040c8031020200305960480114601310394080e82d24146800c0110030b60584c0c6256101034400c00090210603440240140e108100308034480b2035040044003650015a640c038684d401071103040094141d03075802002100c0e0301401940034010107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 131508570 1250 131507320 131507333
    0x50f0f10030209011d1f090225050105090d021501170f0f06090c0d0f080306150c030d0c0305150907030b1201020703090509010f03120c0807060e0c030307260403 71
    0x20780c00118105e04005440c290140c070f802406030701103044001c0c500c0c1603079100381c0c1c8200c0000e03500c0b8001c4501c1c6e0010700a00c1042c0c110081a400d01a1625500000752441c034000b4001c000850303642d181405004001c0300303024070104500403001d8107110031f110183d0803d06042d003442207130764484209205035035101031135000c02c1c4078200820440c04040c1c001850300c5001141001d1400c55000d104009c0c1501403c0050800d5602c4000381e90007483c840c2c6c0341c1d0b50f4800440d808542d690b02e0050084000b0a0800c194500040144500d58035031109014509402005074203559050750001115212958101100d0401e40240c0d64405800e00d00803c4215480d00802c00058441500ca15a40d400182e550181354001d03d03004020306003a51106003c0d0702d09184584002228000104082000c4c18201c4a55221b030003030003581030b005103456541e00b005180071402410a0308183d02c0d98010318200c1c2c00350786400300c2910860790b0030440f42c513100c1441001c441c0f00c0490000042803400c0c418400407012400c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 131509820 1250 131508570 131508589
    0x1508160b03360a0203070611060109020a02070812090406050a12030c05071e0503150105030d0e010e06161b12020613080d09060305010b0304120c0c05040e03070b0901050f0f100302 79
    0x1280701510243e82c050062600b0060340b078010105010052903072600743c45001898504541300e159005895004d900e0040303091032682e40c04205507114a1082401c508042002080880c00440c0d082001a41e1002840700320324952045c840c0d03003414078803000e000c60300030891031a00c030748503030146c50007a61148004e81e003142c0303c21985513016100c0c1000344840e040420864004080452180c00c0e10b61420000a84c1c441d0b100326003104201003020320241a034020b0600000811303000340200d0f00d960b00640d244006c22400d4100f942d15807600301d10105046000040c01c002d4031114811034052803265003d00c8110341c0030481280ca0500c0c0141d00043c90b00c0b0a003c00200006503917518035885161100041c03d032101a040f10b2903600040080c40000f404e2050700f80b0b07a00307141d4100900d0305c249a06104c02070740d05960056030001d0410481e81c0b83d0b0f480100081114a2103852070042c242c6604034090301b02d1f20100d0b600c4810001000100d0001c00e00c3c20788a070752244240380c050b861651a503000c90700008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 131511070 1250 131509820 131509921
    0xf010c020406060c030215220602040e070507060f0c051b0309040203010909020909010b090105010c06020c01050901150605070209040b09101407030605010503060306010603020307030608011508160b03 88
    0xf2138a81c0071408140d0b06100c41c103850170403100c400b41e49050940820104550014020a0844524020908000c80c0d0b07010b4030010034048a4400f41850701d00c0c40580316500201701210094503050710b0080f60303011440381d0445a20242d58550916584011822000040c0c0c50310805034401404298001c0e81c46000640c00b8059480d4041102d40803807061108066000e40340390b1207641410212011900c660b580c143c111303002441d02c058916218246a8001d100700d0482d0342c0c503542064100550b44005402a42200030102c441c043d00c1d5a50300f00c1200c4500031101c000b5030247c091004074010404c6240e2140d00310540c0d078151220301d5580b10f1382d0300c01ca41200c0e08100f8560000802c01005030382610401e4010b00c0e007802c0c914518030740080042c1d00d0f6001401040e0600d9408000b0642c1c1c03511a6000b040500300a0008019590081170341c0c8103c60b03054821220f041c1f103011180d03108161188081d00803511038041541c21034950041b4682c841c9214440317443c01d6105001c1c4100e4102090203030030200c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 131512320 1250 131511070 131511077
    0x20d060c030e03071716020907020c150405030c04020903010e100905060a051302280b03010306150503100207030e0a0311010206070509060a1b0803010e07020c030d0507020f010c02040606 82
    0x820518402030182c44600d01c0c0c841e8980c00603c0110301103903202030707095803250748100c030240e4a49032150040d4581c803516074041e400503c1c41c01000307a0f5a4000902c032540b280c0817618003022605140001d449031040c1d004070350b019007050310b0300034480c1080e4015100d070750700050001c110b01c2e4844200601d440e1513102c1c0000415144c81c3c050040c400280710f40381c2c0040120005000070b2518502080360354a11100085c003440c0e04ca900c800072643c001900c038001501408007003816981d20700d500c1007590000c1c0400c0c1d42e02e528040310000440c0841d41c07807001319103021300074001580064150070029001030310107800340311681c2661000c03681c61400d5503024621950b0103c5141002c0400240380a800034807130018044200115005551598140d40f5060b5043c5040c11506509102c41c8050744c15000000300100b101200100740d20009045c1a440f40c501642211070b00d207502d404241d5202d0a010600c8040390b01000300c0c81c00350510000240c450304041c14140c0303038100d5070350219049840542c000c0000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 131513570 1250 131512320 131512331
    0x607050715180f0e04030e04090b16020f0616050a02120a050a02010f060f12020301020d02073f031805120a14040b0d0c14040e010e0105040c0f0509010507020d06 71
    0xc0b03403510301040c0054801c010142c502c00d414030b060300c82d00340700141000d014000079903800006d0740c0c0c880d01303d09402903000d403d04082e07007400038400ea00c0440104a10025000c0c0100e100010038000a4140c402d07618105180d507a10308150054039558005c02983c01180113071740310203410007001070007403125150941d10b131030782c5100b0340e600242100d080c0c1e49030381141c9080c240d04011413020800074805503500b22202d00004091440064028815141c2c040d410070300101c2c003081442003010000e8a00000306200f8404416003082400d8102c0503408560090079842c0f012502c2c00f8402c2c1d02900e03441202225568029159403a107500d0941203c180c64240400003521030301050f44000c091005619501d4031505150801052903010300429611400301569010710020741c501c0740304804250209141c403161b90365103401145011203002d0081d0070f0643c02c80d070000160743c2060f00c644d8501c00710740e40e100802000f00c0201103074554440701559040006c24021140541d480715030034078100c1e01c1103d00240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 131514820 1250 131513570 131513597
    0x605010323030c07030602090118092403030210020a03061d070905030c0d060504020307030c0f062a11030c100503090105010518071407141014150607050715 69
    0x7022001c020031030150350400d00203500d0b40c0d0000114601903071382c410f01c050f858858000040350002800c00915801800c0003a0001e60020340394002405002d120b0755001c0b180c60100329082c0310306100d03c8014010b900c44240d45000443c140e018004603045460080342003540c960303c0140d5000240140d03058000204140554039030083d5030080100825000342c481040e103079000464003101d03418040c015544070303c009421540e00340711590155900c14640d0681035154001c0c100c0d079010781e0242c000443c2602c1c0451400e410700002c2001d007020b10213500d205145255960040905152910580511690f80a85000d075a4841c0c0010521081e94441d0345a00d88002810700b543e806034485406091031101c601c602c044280c45007940988642041003100c000384804a00902c6280d0003c0c00b141402408034201080c049850f26640c0031100080c45840d003481c800616007a820b807810100a4003400090701a403c00c03d002e08a06401030701582e00d041e949544000b0b18001c4401c1900c00206110380805 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 131516070 1250 131514820 131514863
    0x1204060302120906091e0f0109050d020607090b040909150509011a0612042303040f05090a0b030712030509030d0c0c15021e0307020a03030201060906170c10090306050103 75
    0x180c1c065102c2000702040d040c03120b00715849507040d83d600b064442014286e41c0c0001400c20103603035441c2c1c00000800c4100c035182021900c1d81c92480b4202c0041c0621004104014880e425a4003620300e80450280342030f00d0600340c0e030010071020008441c008080f00d001e040b041c1c4140719691140401c1000800c05018420031044000d40440701c4500c240f40a02c22511a00110b407541d0398441d6000800b40140d0000340c800603002d03134030342c054614140710000303001c02c405511010000440b4005c0d01c200a481c3c8410000806484005800d6070f0590b020250801c03e80c1101c00030003020a029045c107900e05502540402d050191642031140030a01d03200010003001041c414a0000344148000c40f0010005080b00a40315812100941a11325100b5a424403884d01482184c1001e94010807892042da40c3c0d183c040c0c06000c00b03205180c421498000c00241420400d4400800b540044021f00282c0090100b0091940109490f040c208842c0d2500400059014031810303002e580510390003802e17a41448042d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 131517320 1250 131516070 131516107
    0x91802100504150c171b0706020102070b0603010b130f0b1806010e10020a111c0b0105090c090604051009080307060b15040302010f080a15091a0301061211031204060302 74
    0x81041311142048002c99000134002c0401c1148041c0940d82d41006091aa0b620710701c40003c1e44280038042c000038402d034055009001551084d5941c080300d56515040508851112610b19040b80c142c801c542c0f05103c1580c130000000700c40e80f100140055850010034602c0c0c8a1032882140c40e400c640030f0160315070308041c00a4204104450b0070640c0400700c2c1000b92030752141100100204070f0303001ca0618a540704100080d4401000100c100c49100d1030800071103030b80007072240c0c501449505020841c6804c0480440d1410070001e450545040d01c1c2105200b02103034204142d00401c003000c0c402241c1c4000910003000628020030f80410f10b00720000421100b69600184034800342c00401007040180d0704490303c8450300f001d03420b0001c0150745030308400e80a17001c0f90800080c549490390703001c100411507500400a0003090074403440e10306148401c0c54200c4002d8090f20b84840c048129003070001d07010055002000d58090292204032080284040c1e003900181c110001080e0041b41e2650072070301d0b25146 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 131518570 1250 131517320 131517359
    0x2001021c0f05012d0509070203181918060504090f0501060518070f020f0d020f06160e0607050a0501020403121206140d0c03020a06050301082401091802100504 70
    0x10015075141083c2c8580410700c80900d451034500c403424031215440b001141c4c074014030002d0300d6207120f0b28008030025201d9004880302540b0422120241d00c850415500d888020381035a00019074060400494440404801100c803c07110340751176000c10144c48034014503004a21031f80c2c1c45044800c40f031401a0135200d06400990042440c100112500760503140380030f802c0b0146003416003c8004512040303051030382c150140b503143c1c407900060007000781d40000e89900e0042800142c0341c250311011102a550b203411020b40d00062003a1407905124030f440d50003000c945210b9412a00104465560303d030030780c0c2083d84241e4080403c100701d1003903281c221181d11484000b000d4108007030350602c142c4041d0a00303407002e07203800390320019000020031070740c1401c034006180c0003042a000f0b41c0d9500c0340100203034424001c104d400d0140b2400120407034464003a90710950800081030b000c40e820113402c00000c2280b14290304402140590030030250300c44c201341100e040c070030344d0f1a10b40d128101003603940504484c541 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 131519820 1250 131518570 131518601
    0x215090303070509010f020115180c0201110306090702030c1506040b0103150303180b0d06050118030b0f060d210e101710030213020903060a110a2001021c 68
    0xc01002c540d0000c12221800c01c02d0078400c4251b10300b82412401881380c0115042d06030000d24011411417070044825900e800781e01000d100161415504a09844105403d00d03071111082c80070030154034103048625444289031045a082180b5840c60ba880c020701e807501032a44502c031078244201c40c00c01b4001c4026500081c24103000c00d0040c00c030b040d00f48a8445c4005000c000c142e2814040042c91801c1c90b42c0240603422400e81c64003452501d440050803144034483c00300e207991400ea541c0b41c0c50041030000301e07908402040091355400100b1000480c004000540c0302e0391150006000800710900b911150000c1c8103148900603e505c070180640310402e43d1544510039104014482a17031010203020741481402144085480e101800c004014042d08001e60204241c005e00d04025441e034013034001a4030403000c40f2040c1d280c00919600700c2c0d8207402103101d00f1100b0080d0b100001c0c007404c03001040000c182c0054050700200c015032801c90304042584114100400d800042c1c0e080f580c020086880305020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 131521070 1250 131519820 131519827
    0x50408010515060d0c05160305040806060d0b01150e09151002030c03041205010207051f0f0b0a26010c2304050607120302040b030c211501030e01110a02150903 70
    0x40003403964003584c0202c058440d00c80c140104a04d00c02c0042c0e80b840b2902070041550f401603490007509542190048565a11619002801c203142524040602076041000501e1a03400c01c00716883c402e030202350070303420300c54031240c460711030b17112182054440c01e48507007029520700e0102d0400195104070740c40300046500c24400b0b0102c1f00e00110881d822203200f0141040b50760010319080d400780c01244006440c500446080741d242a940001e0082c40e203001002c03c22024003500d82500c111144503c0c800d8018810341c8052001c1c0030350001c001418405940209800040040004d0030340b450004d030381c40010b1028038001c041c0d81c65030b0112041d00070092030f00741c2841d040101140303050041580144c441c6800e4169008824002d6040354060240312003800e40e00d18040700c105100d907004a00b5010314405a141c0616840702c04001140510f00079440d81c040e1003d2040114003510685504182d6075595100d2030302c0c2c101195000700f828120303030f4014107100c414110509040d01d9005041c4000c81c1c1040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 131522320 1250 131521070 131521111
    0x4120c0302060a0c0207080102070b1006020f03030c0306040e0a1415010828050111031008210d0f020c0f01050f07021009140307060f180209010b0c1c0504080105 71
    0x85000c1e81e1000380321030f0020b8220308001c4200e1816609501071201c2e5440042c849041c0040300062610865640d0138244d11181d4400089030358440f85280481c0d90b42060003c0385c88001144015500028000c0003c540032140f55001420a000508110b445400c901000703004080140b060729030a0b44410301e42500e540c580500c0356100e40640e5425031984200405180f041920900345c038600d07070342010003005002c000b03203a041880d50095412011b0145108800690100d00061140d890480300410702000030101c80b07020010b400201c0b03064401500d609600500744600d10252a0510a040040c004040c022035036908403a805082c031881b40d0900020400c815400140ca9a1100e403a600b0025150410b07041040c65210034103500da01902000820409004454108501d6020411003c00011318520322a0110603449d03130303000b5004043c0e800108040824240548400d00550341074070382d20001e10420401180e2b16001d0440891404241031090860034403a50ba480112602090b14101c1c01c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 131523570 1250 131522320 131522323
    0x10303091205060406020c120a230304200310020a031d07120807050304050d03050c060a0501080c0d0213020a090f060905060f03130c260604031e02150f04120c0302 72
    0xc002170322041d00080e0344112918208081414400171681e9140c942c8a01d880c01841011041c00d500b200d02c52401c000ea8040400700c1c200ea0240394055031490700701d5004924204020200003015505014122040c40c0082e40d5000600383e6881070b540002e24a030300044429a020052488420383e43d000282c1030040210911181807181d800400b0140c0340d4000c0d240c10f80c558807468101c1034001100d081c45404054029003e0134403406240141d400700d40e00e8a50300e108a403424860900c00380d00c03000145906091954441e4000c030f00241110141c8514001c4120a0740c0c06140c0400008200d580108986104100c503074001d8044cc5c0780c00d2040c98600000201d00e4096526081700042001020a01c003140350b2070656441c03a8000300300b1541c155200d8414040e244d041065080040c6041c00c0020300c1d00300411040c0c82568941c441c0114010750340c0d10365928641e018203140c194070a64010410f8215440400340c0f003060003000b80605468145000d100d00c15202c00a6802d00000c028100300080c3c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 131524820 1250 131523570 131523583
    0x10c081b040612020403120c050f0c09011e0305160f061106060105090409020409060b03010608010506090a150807080c12010c09170705090c0a0807090f03171b06010303091205 77
    0x410f160504120041e144010001d120b103a00c000d00c0002c24905918980c1e0f0861594034100d4001e0301510103180c4803007403560720f55091042441d804858a00103110016a55040c442180e80d40c0041c100c0c50380d203036510a45440c0046981059101c44903c08100450907010300c54058552890700c1d4a01c288003040d4180e4503a0080c15242c144000410215015116a80f1a203512038005200f4840f00c034032418404014165508103a0181d420700c800402c0400c3d050242900a00b40075000003021798480521600400c5032009001c41d094541e440060740b00d07010040340c009461080054202034088100300081a1108410714440e030b4180710b40c400d006500001030208079108241030a03844d0b83c1c1900c020b800d00007a43c2045a0002065007403010404140e005040f07402c14a488504241c2c444203030a0301c1d11800b611805111140c01801440003400d0304141f2701c0e4a081d10b5044a092041d0b2100e2000e007036809802852990f40b010b0010030a0660100c400002817130325101c3ca000601323440e124a61201d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 131526070 1250 131524820 131524829
    0x303010605030703090b07030b1507030504050613030f0503030603010501090b0303091011030406030b04050c0702030a0807240c02070603020a12091a0108240f1f08030c010c081b04 79
    0x2200080d10f00740640c01c0083da290388601e81000718607002801500a0881280c03035401072048039941014030220f031044501080c1c042d04e0311030400346460200302c150341c0800c285107040c41a8100000005023142c046507640c5209034007850f03d0b85424404e02d400c46105901441c8494240031004803a40c50110403981070140c261840d500e803000c1b034842505e40c2c00c0c5422003401944000100007078031607810390005031000403c40e400c3c400ea8a5045081046000d450350196140c0c01400c01240040e054200a11031144902c604c00c01240701071401030008004491841521500e40020700042d0794180315403c041c2180d0308045040803003010006000c01e5000e40010386103541e03441081c050080d003200e840d83c4030109080383c1c1d0556840b030580a803908101e50381c04070070300020b5401d0342140d4480240c01d841620194107950003a40c907070414a02c120620311200640783c000c0500881c80401c24401011400804e2001007003031648140d00400d440801080c40144a1400b2006000841c1e00b1007203d00301c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 131527320 1250 131526070 131526077
    0x90311060304020a050d0201030e0f03070204060806070e06030a09020a030303020a0e15030118020f040b090a082b05090301050907140f15130f0e07091706010501110a0c0e010312090803030106 84
    0x1006d440141d00a040300354440101344903000c40075034100390010040412620986040c040c07a940c445c140359452100707444c2c0d900468507650f00400b0f103042800c00f445c0d0003400c004000c51b400e0100c0e0081204441d090b0825030000390002030609405070086020070168100f0b8a0001c048200d00070742000901040c058041c8154003021180842c600700d40503541c0c0024400e003c184d03565500c0b19420070b2070740691030481c0584000030001a100b900444c07041d684001e504c04010404002507403000401000da01c1e841c060110500840b281030310244140c5200d800204001c004890800b44c00d0512080b2202186114402d801c400c058907841d02100100100111114903484500380da100c280603250711b420001c010703071903000001850b010818010740a030701f16840e005a45508e403003031303120300c0c4c2a04036003115542e000c10300400503540310703003859918a20b000d07081c6c42514003d0380c2d0b103041c891015400119008024001482400500c800649883d5298101620306a14003c2da4a840340030510945050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 131528570 1250 131527320 131527339
    0x9031603030506060d060e040606170c22180506060d0305070b071704080403031b0206070f021504080f2509090203150a1d030a21150303090311060304020a05 69
    0x1e501e0f643c042c1c4d185d010a1200900c401341e1110003040100408984c1a540c19003040340009810201140510301c1c0d40b0f0603806005a00b129100380f0070640c001a914480c1440c50350010320f2150305600c02c0d2602c0c0c0100300c0004211107410705100d0301d4200040e212500c954619819200020b80203821604441da11881024040e51281c0e42507030b49403103206810f082003442c2d008000070420100001c0c401d0300c2c401d0721030401c14140300201c0d400440500b40000d4020804000c080c001ca0780c0c0c000842c0c1824402460102c000c0604400b151340d81d00309601c64061580a400b120032620402c0c800109904140d0b0707803811418589841000381e0060030701c01c10184503a10300c000c00c01e644051000c9841d481144141c40068104404d01800400034801c141050780300b100e5035140180c501100b110304d1001c465580c80b0354808050544a180700c2c13049626000950b444040c1c40a04692160003030065010f0346452030340c40d1840c04d00c03c0760400b5101c3e00f24400c5a040040200680d100303091801614001d9509191 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 131529820 1250 131528570 131528581
    0x5121602120307060203010b071a01050a030b15030102040f0905060409020a0e070203071205040608180d211d1006050a03060f022101060e0105070c060c031403160305090316030305 79
    0x103603c600440a03052070300002c00484c0c3c800c54080101041c91050683c1441d4070f0458900900d031007828000e050740306a04c0102000801c6140b609142c1012048004603884090038000908a07405540001401020340c1010459913542d84286d07540300704151410b010100c1c042d4000b81c5940f0250158a800c20412008104102d20820507075960316400300c80354220040c400d0015000380c01c0740c0f00b8200000c41c52070000740d1b42991500740442c602203542c0181404150014107691080743d441070030307080c200114101c0d10001154017600440100d4021942c2248403224519420980c80302417054011b420a1010049034680210201c2100d800c040000f400b0380c4810203941c064401c2e0040c0703c500510000c00040200304200e001030407183c05071118102611007500643d058010804080e02c2c1c00d00c03804c0104085d5009030b1020007400d200c0e260401c0d41c102c90503a204d009400c10342c1c8010107042c4e05a50f8240e01c1d034041c8542904441200300940c20160074485041c503124080d1380040070142c68101107003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 131531070 1250 131529820 131529823
    0x60319050319080604050604291206180f06150f01031e060e22060b0a03080a030230160905100815121b03071d040512160212 55
    0x180700340310b0000348188090510300020000d90040d194148103900e000c01051151429115145503ca50301141d0f074500d190800c1d186216044801001c2c2e003016000290400b0900207101141c070a102e0364407410140600d0090891600010382594a00c990109040c04090701040d681c64511000848103c045402d0070340c0100c002d02042d501c2181441e001e02d020200c005165044032055401c100f524195955800110540072204070580d5850031141645040c0440d0054110410801010f401da0303c10507601e82d03d4a103540e1040704a50006640440c51280342c0080904c40c1d007440303a1030304400d2441c4076081e00300f007a41074000d00940c01c42910021001d42c21070040c80900e004060040500c5c4125440d240003030014402210511745040100c01050315603c0d290864100300641200200145010302902c000241c440b004541e5140c07255150008240094035800112440c00340d2a1840905280ca400d41c80e2440e02c80c00305024201c10b103c00030f030040051400c8030420350120742003990745130605e4425 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 131532320 1250 131531070 131531077
    0x111030313080d05040f02040506150702040f0216120e03030702010807110c03100c020601050a0f030f0f06090309050907142205090a06030b010b090306010b09190e070201140603190503 81
    0x1119502d090104002c00d0046c2c5940c0040b481e0f0081e50140240d64a410400c82900d89080d035100d0040c10900c010000b60405900442032404218401450a000d1102e9103102443c2030100700c6014401c009511800c0d070340245401034a50301a4011030422820340d0018027441002800b010800c40240701081c0c00c04400c00040322072a01c050283c1c4c0c0181c01840e0303440f01030280d480001c4050f01c110300c0002400e041810340d12003102c07913201584c1c2c02d0904503030300c00d00f40b1800310505a5440000d03482000c045007007449065003a1780701351141152070f49442e0502010b510010403010074014000c0d05103003510122002c40b00b40c0070b818561240c100c1e803980c0c14800e0490301900442d030480f00900400640b1002a4841c0781074030300405410210760390b00e6034442d10034403480b16182c0d0107822680041142d0072040340a043ca40200418006259003170483d8681c04000725400310108207140001d02242e20340a1203000d00010107130340f07292014070f8020b0100790380300d0000c03a4820b4000d021003800d10034403400740143c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 131533570 1250 131532320 131532337
    0x4031d0f12010e010b1c02060906040f090204030210020a15051009020705031218031602010e03010c030507121a10030608030c01050a150303270503070e15011103031308 74
    0x14014240c1c40303910442c028003160341414041e40c40c00c1c1d8a001140352202a1400704090b0584800d808a104c1c0d09110860300f1803501c03a5041402400080780b40030039a4a880040d0864506c0180c0f964998010440d0740d000072a42e40056401c847c1c2c00700c0c042112421205207100c111200420103458524003008251b050381e2001d820584085000410410080010f041045e040b10640009884001d61013000c00401819402903604c00c22492042c00410100300765411700504001c2c10703e4600324042820349240111b90f01c00a0f40e1101000002038201c1180c4a45852141c0c0c10440c1168140b00201344100302c1030703003d20880c9500107440ca014070a802c01c4010f0034034041503e45541b540c60310070780a4202070f5030103454a41014104112070411407900006c40b41c05548a12003680380720450700000b084142c0d50041842d101340081845d8038100031440040c600000000710320b141c4810660544248421018100200407981c0d52003440008196500711110315585030241c44103240181051003035040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 131534820 1250 131533570 131533579
    0x7081602030c030d090b010602060603030406030e030405060d0c02010f0209030c04051503030c2410050d030c05010e1e070506070b0a0905120c0d08071b030512010e040213020304031d0f 81
    0x50032481400c06401c003210281c410000c444250344c840c9409da0300c41c1e0080707480b150107610511080080300e101e6004841c04003140000d403031805480b07101113070b13041d8451410b0302c0006848001c1004095424411050441c8251320110301300404003000031345980d85c200105101c3c6840e80007060b02a10a080c2c1040151001811607031703601c5001d01c4440d00c42c0c18030804035203c0600701d0100032055206094641c82481da15210307518842c244000c004421a065509804010036604503600249092007180754425003070009080f10b808600d0300d005950319202c8140e505400803d420480754484030191003000b41c0c0b020f07107162256681010071000304411a40a011845044070042e00e245d0000014811101380c0400d80c6c10f11048408107468100301a14118005072150300300c03d018548003812024100d10130b2415601d8000c000855803200c84081e001603c0b40e5030148140b01c2141361004422200c000310000070348c00d6240c035450140c80300c00d07510040c074803440421085018940d07440700002e408420051 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 131536070 1250 131534820 131534827
    0x9020a0e010e100905060a0e0c1603050915070f2418141c050a0201020708031008010e07080606091801020d0504020306010501110604060e0c310507081602030c03 71
    0x18032540c100b800554001004030322200020070503480c00c1c020503101c0c90014108003c074038039009072000c0a9a0040100381d07041c10500c040d08120140d02c800b142d10031301941e5003580741c1a045042084410000ca05680c010200704004000034007140322031550150040000704a802c5098801c2100c809402c000c0ba03000d030300d0088207180500302e00410542c03007800748030b00703d16602400107001c2c0e8421805001c0c01440b01000c01011810b81b0071402401c2c0c03510948005030505085940b003282c1500b040c1d903550b00d9000d440b0300501500b04240328188000000500070941a031030044001c0e144c01e400743ca0380d40194401030029110a008282611000c01c440c402155600c240c3c8403490700070710303090350308a1003400751034000200f40d03200e44800710074440b0f07100c0504282c4d1100d0f0f60381c00081c00400394091080c00382c10504501940c980c8940983ca680c802004048510801d4520802000700110003d0a40c034103c148a90b29134450f0b185036019403800c01603815280d5031003040c1e186004c2d00580ea0006e21001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 131537320 1250 131536070 131536079
    0x180c0317130303050c0d030e15270105040b1315020a021c0206040b1b04050d021906120c030c09180605040f1508120f0307210c0f080c040909020a0e01 66
    0xc141c801d51810540da1b005e101503030202e00b07590358080d60322002c0d0710141004401d0707021342e844560015440d8455469804100c20501070b448501100300300030303035511010003040c4401d244005034032043d12103160301c0f140850356550412812140c020014242e0205000c81d80500810080381300607500100344074031041450000f541c1c3c010032101240c10100010118103600c440007038800f40c04800d04030050070a0304000a0005020501c5016a07110300500a05290280000b000d10050011a6500e0715204046d0f0312482c192001905004101464405024040c60f4403141010032b465414850040c3c40c0141c0541e07002800a54105642c031a207459071015245169900c01301d605100d008140300c20030394800005407640600c420b81e981c520b40410480c00c0c03c54004001390f0340440a41000c207004803540718440e00d000003110703034580030981e51140400c19580203010401494140d240406a5142148024241e0b000381e10a2140240d1134002d21000c540da1031050101401c03c40e11402060b603902c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 131538570 1250 131537320 131537327
    0x1a090a21050a060605041b0f0c03031515270e0403021515010201111305090627040618020d14030f0711180106080408090f030a0b0a180c0317130303 65
    0x20300c10580728034502047c0b42030000201184030b41800050700c8000702001049025039181d98001c0c401c03000c0654610760b4001080030662080040c041440c2c0d00304191400b0407010b00031007800c25801e0080c003102030b80c00710104003601800c01034403007075260f0241d181c4a5140076460b118150205412114840041200c180165154041140c0c0260f0003400b1010002d40c0400d06441450a480e5107040d00110a0005040160405402280c082c0c003030042140d101402c11f000801b204850182040d4400030b1200307102050040c40c0d425107522202c01c0c030156055000071141422450001c0088a512071681d034418014819600e10b84502c0b19520355507901d0f450001e204101c080306040c46800705103128500801c0780d0007000e05a41050f01d0351084c0b502c5d2030310b070340081d6004528000e60002809124095544052000c0c01c01e43d4800c0c0401003403410441c41550944207141c60880030035203818040d4001c40c1508417560f007201e0300041c4a036620390940e20000310903c42c0310f030081d10144054500108242e0b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 131539820 1250 131538570 131538581
    0x403030518060c0109030f05040f0e07051204050106050f120d080411100801081608060703021e210f090d05221503050604020403210e040f02041a090a21050a06 70
    0x106e9661081ca1080310b01c021741c4c050166000310052900d21420a1001d042c01c450526040042800c0c11801d040d00300f030010710f07041740c200c6046030240d441d001c04028904002840b01100e28003210302c8031600e4680642c1c1e0340d80d01d4414415078100078a10000c10240100c990045503007180c0502002d400c0303e403940014058000038415280b2501c1100e6500c400260020141815100900094101500c1e0303200101c0194124101f03250580c0001422140844915401030130440300441c0000808180c101c031115034004000d082105203994402041070710320010031082524010340c140152208800300c0c02d20144001c036800e1a481c200c0304200400c11860800c0c454070a400540d0702401295281024401130b0302561200526105900a482c45084441e83c038001d4101c0315454001100050a40000e00b52104c0c0444038041d41e5002034180021002105242e8005444410103441c001000000c03650070721892103a034482160034400070300e0985001c4c0d043d039070007500081141c2c1000c0d11400c2c208000c10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 131541070 1250 131539820 131539823
    0x4020d0c0801020a020f01090b040228140117370207060b12010902030a0b0703020c070b0910181221050d050f040210031107020d08030105100908030403030518060c0109 74
    0x455a01b904014290500640c03160171b40c080400d00c0325403150fa0a00a40d4184400c1c0c24041c0903c0c0d05840880240a145c141c00901c4a0b49800310190035031400500001d16015002c2c41034044013013003001682d801c0b400d070b030703204490003243c0d0613002c6c614956468880c0406500d4480f00d03000094810900400390403035030038000110384a03542c0820000e105422915802c90094150708038121000100341d500f0300c10340e0f00c070500d0704025282c051201440d5080103d0341e00034100054010410032902d0614190280702d030007440c24a071855814801030b081c4d03081114801d40141002c09050081004000000b00341c05c1000d480644055004140000d050b0ba04543e00e2910050301d41400541090707100392007240030b1034004d040f800010340701c410304601900c0c400e01700012900f402c0064000584480d07100004281c0525095510395040904004008080c0405002040910401030200e10310110407034084a600d420026a5083c040c01000c001c01d00c03500b0100c3d8440c00c08100c04407001d07411b40201218a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 131542320 1250 131541070 131541073
    0x20708030c03011a13050d0c030f0c0305011112040821040c031203020708090108100b07030503040606090203091002092d01080601080919080d020406050a0e0a06120504020d0c0801020a02 82
    0x150314070421321555015030050703500711010006040106080c50744401042c0c40c003640200904c1d540381d841e03082e510005000b0440710001e110408000303001d028030890380000c41c3e040100340b0301020700c001d030f06500802074000b0340f0000740014804504403c10038034402e00009a44094400d01c0d190520050754200c0d403109484c41600c0034004d032070592187c405c0b180b03104c0c0e00242d80e03402c0c404c0da00011605c403180109880790440c005403020401c00c1764000640700325442542d4540e40ca240519109041c0d40407540602960360041c400c0c009042400f00310301c10260540f010058442410500081401d000e0000c00d13000d00455843d83d404050303902d01483c20103042a00c402c0190b840380401121808022218070302c094106aa945c00c03d1801d0f900303081f000b05c1c05514041e0600c00000c240340c040341c1c13041d0f1004000c501d001801a04ca00d4000c0d0400c81201c01c211252034469142030030107031000d04110300300d90f003217a641e000081c2103580f07000c001800103400c11280c00c152510f50104c40e000354406d40c3d580d00035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 131543570 1250 131542320 131542349
    0x62502010c05160611190207080c060708031009050a0e0d021b062a060402010f0c20010c1403090411030603030901140c032a0d0906080a020708030c0301 67
    0x56401409000e00c44662941d9442c9824074015406990b03202e814801c4070000c1c3c554160004500824001d0304038106a1100e01c040040100000783c9090b517070750b221121641080d203604d101c03640d9a8041e42d000036003119003550340e0f540d00b01b062400d04074142c221a280c9403405041c030034420480d07404840322844410840340e03280702841080e40d07240840030710018050710141d01c50780e25040034170151591414042c0e01c000b5a00c0500401a901210400d120700158400303c00c020941d82e00050081006060381400580c481003601d0710091641d02500da00000311140d0900c80c4540d00c1030307540c11071140e0058040340741440c0813040aa107030f03070040070300e184a10708001d0181d09690010040ba80603140040041d49000060300040d110384034810708a00c0e01503818040300140c3e440c18001841000c41c03a416a11516024030b0481c200c0450041d1524a59404034440b042c4107074004070200181d50243c00e112000c0d5650104030000b0b8414804000c1c10150044180041c0c1c103521000746060359898107002e0007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 131544820 1250 131543570 131543641
    0x414190b060a09150605090a0305010f05040204110301150503130f060537090606050904080901021902010503070e0a08010609020c0606010c050316020402070c080a020306160c03140c06 81
    0x5441100b04030310421200c004c410410180994010a08041d004d0b008680035070352070b00d4aa003183c00c51305007921003d803168108411450316100340b81c2d071900a00203003030655040a0741090b24049030710310041804400000b05082d06285000b020807072b50b00c2400b42d0142569490414041d040c00d80381c0d9038100d0140011600c008100d040d05200100700c040b0304000d4102ca55150030050310f0440d4041c0c0d0351a69070031010030181c9899103200c1c40b6500a50515540c1d01085d4002407400d8414a241d034024200542402c0040c0c0e0b01c01c007141d400890514288083e2140d55001900d045a0380c0c0c4646c0d103a42c6000c0e000511800c04d500900600c11401c0f058605aa0340d00e40190750031000070780300922540041101e4a0341d00049558040e04c540081d0006007001d04540e01da102c0c944060704980b85035031250320064110300d0100b05495220858100c5400261003030f00f4040e29603d09071b1001001d00c2140304091423182407800c10356509588101c11a529030500d0142c5030080c000303140c4030200b880060183c604 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 131546070 1250 131544820 131544839
    0x11d1b01080705070b0411060a021b090f0f04022b060e03030601050f0a0306050a0603050a0b1909020a050c01020d0c090902040303090e0606130e07030b0909060414190b060a 76
    0x82c0300c0c54840d203585103080d00710395401c2d162180c01402101d50414802076451f0380d46960340540303401c0c81140c005004646102c1004024002ca458010307100748071013070400105500c102030b8140c1200e134040050740180ca6a00c001659040005254100c425814007000001840205a1100107000c1c0a04101180c1c0c40e81c00c654892000301e0f2040d000c104200300442c1c0005a1400a1042c9a082e150001d00a80c880740059014003080d4003c0740080d4460003445151131040c40703199040c1004a420100c2500d141e000480300d080f00b03102d0050010340c04282c0a29803070268049a1030740c50528002c56454058440d018000c00d42c6040c10b50001c0c0022102240f0300c481e51003110301703494164a4a6015501c2c00c2c8800d400300030300401140c0c0152090100040000300b00c0b00d08400751030902c034500341c41d203040b500090482d01c072074034a0361103048128240103840b200825499085500311503035017402c0201c6155035160011226504141015030f030340c02420300403c0d4509074000c1c10121880e82c040359a49213480e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 131547320 1250 131546070 131546087
    0x1050411070206030f071103130f0602010506010c0b07030f0516080c0a080f06060d020307021b0301090c090f09120c0b100509071107080304081e03030705041205011d1b01 75
    0xe4011404001181e0f8440500b03030546d5202c0c16600d0810200803583c0c0c81c0b2411a00100380b5648100d20111060007181c0550620300003408091000308018500340d030000782801c0f51600050300b10340b4200e0100e40c9040c86034010300c156241001c2c00740a00e04101d03003010fa0340741c000110310f000101d0700c1e03002c103000c0a035030400c40c0c10540301d6954000c01500c0f0048404014040900701a5001c6010444542d0040041c00a07500c100c6040d0090701030781445031940d8003031705030840e8854880e915000c108400200440f250005944400c0310003c1d90b0204c040541004203400f2001502c0c41100302c00c8049803543c819036820550744100300100c81c0b0781322911182041120f07400366551043c1d900780081c0303030030b48582202c0c01c8007440c2c0f0b030842d00351a41d82c0100c0c9056502a401070310342a0058815a01c1e441341c0000d0041e42e004440c0021451444c1000740104540240d0182540b844815185102800001d412005820301d0031510603881020001a0599039840542860130220f054010100650b01a1200c07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 131548570 1250 131547320 131547323
    0x50406080304050a0f2709020d11030606061e0f0d11030a0b0402031909020d121d10090e09010902130c030b041e0e010f060312090e0601050d09030203070203060c030105041107 77
    0x400d54040300c44010b62080202c05115000c550340e00347d8002584e5505280c8803124003d00c09a41d080544105160902c4d10007410b9502030102042003802e01601070445e0903a001c00d41c1803140e10b80c16440e1032207003107218145032400c4041c00c0280860001603c07000a50207805c1113042042161018014032040e40411101c4903a4030420406025108100b40c00c54442288001c10003078141c552541d801541c003a0a60142c4005040000d4003981541000d007010030781d12045900000c951503aa13001040c40000703005103001076541c2c502045c0c0340c2c00d0075003115201c154001c000d4041c200f4106031030001407020140c000c0019041207214040ca06040c45414200c00400d490b04503558a810705000180c1100642d84400703660311615013103000d030580300d10400755104865945034400c184a0040016505400c0030110360326100a118850b80c21500300c0d0050340d40070101250442d45424181d045002c2c4140194060088001b006080314041000b541030750f404440812901451070790180040c02003220 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 131549820 1250 131548570 131548589
    0x310060906031a04020a05070b0f0108070e13062d02090103061403060c0901050903030417060c0408150709081005060406121e060b060a170a090203190c050406080304050a0f 76
    0x1a580f5604054000340021242424018a0610b548d528a80782e10011503aa90a185140c80140610310003403110100400d61404001c055042034041d42c0a4000041c2000300650f1380c2d10243c0491342c04400f0041c02d00310019550005000860740c4400c080d600c01415a40001e2401c2c0020541071803c003003000001c1d10241c0204099a00c0f40003050969019407200d0341440402c0c008240140d504200500290512110754003140340648110342c90020003910b80e80804405010502110340e0002d42100c007000c141604c00099110300405403007911040d0010080d9000c0c0001c8138100302e000f50459801910282c41c1003211641e180516003041c440d000c0300030206290790070180005c801c09245649500d00469001500d1a840b200052241c0d11102d00c410100b0b098540345944148000f0140c0d80c4080700e000d040c800706040d0390001c0c4c3ca45250000481c0300c101c0460404041c4a07412480360b024110191080140f40c2d00e0f0411180d8a82051003030710312507111000c0200b219000c0e28100310440301d5000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 131551070 1250 131549820 131549861
    0x203090d1707080603030405060c010204090f06030f0b0a1103040b0603071a0406111c021f0501030209011512110c071403060606070303110a05030411030d0206180a08031006090603 79
    0xc408441c0f03060041d0407144d05120901c80810030f90749807001041d030034411200047e92145013542e05420707262101c291004807842c20310104003041543c140c0c074845030707800541030040c1d0303035254055002081401d079214170b0080040704100030849102402402120110304465031141d581841040b105600d0124210305030080c882048001c0c00f9a54003026800041e064407800e0f450620030504d2250305c41211070059000140c02000311481d4500c880040a0380324051210798150340201e00003140c184900e01d10a4201d50f410b00166220700c40c880003100031030a044c402202e0750f8103014550f4100000210f0360b40600300c000903008800e8845100e000748050003520242c1d440710100070454103d034a0942c145a01e40404810300d11000c001800c4101940c1c694540b07d090504251103aa45028489030080e407040142c070758010740000300540d100c08080b03070000032000844001c03030900071030020080101d00e0200510003541160040501030b16404c0d1b55024240366612421803d684810804061100071034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 131552320 1250 131551070 131551081
    0x1605041203051902061609030c0e070512010b0306030c060415050c0f0f071a03041a1314150f0114060708040506180307050402070c2108030a0203090d17 67
    0x56181038045000e42071403800d00a0f01e24100602c0e903281c092100041e04500c0c1000000c1c5c480084d00300440b001840d00320030050031950781c0d03540f034440b50291401c00841707000002c5e4405d1140080301d403540d42c001c06c0c4030381c1c55079a000032035801e0300180c2c2c40b40c4c480e01550035400100d0805130b045c5c030101c40d80d002400f098038082c40030643ea0f80d03000c00c1040f44207020700c041d40d60a01c07100300305401c451107450b401081c10a2503c0360008611403c4416901ca011007041848003060748000c25104101d907158080c406a192026001c1716582041c034010044004040c030803c2240010801070072105441310342044a030348000b00b03c1010142400b0300d04001780d40c02c40340c0c0d40905211020300520b6104010035403a0540718800254103412811000107401c25042e2803c44c0c50030b050114200400b03040d0f0b4151b0034904207945c1c032125900c450088883c000000e15242280102140380b21a103150444030041d560b0810b280d241e0041c0d03004949e01d4035907104140c41c0e44c204606c14560000600f80c1c1e40310740105900ca6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 131553570 1250 131552320 131552339
    0xa080306060702030a0c060e0a23040b10030614041e1a04140405010608070b07030e04020d06030c0f060e1e01030908040603090303050f1003030804050709140609160504 74
    0x40c0060350490801d100c40401620300b00710108a140c001c0305c909403c14030304000105015040e00420380111103170701041001c2d00e01554084890400c030a01c900c0000707103240c0810010240d0300038196104960490801030680c140e4404010b80b036020002820750900e20b070031b1000317441040030075180114002c984440d00708916400081c04005c0c018540303044402c10f00020b8151741140c120000760301101d80520040190074820180101940e20160102d00d00d400d03004030790390164840c0501808008002d0000c59503965044401c0c03030000704c00c208003c94032401d1000c04c48166020348a412038079000d0118a1a018141058a28000401320b10034400c0d00c240b100a00c0d914088010b041c182c5032a55400040c0c1008041c2c806041290780005e000441c07824010191500035000102d462010818883d03940b246041c4041520f0b05030424182d41e807030358502540350000c194014900c0754944822048050b2030780103824003d040494001e05645c9500d040c500b030007044490600041081040100106010b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 131554820 1250 131553570 131553577
    0x801050112020d0606050306030c190b0c030403060606020c1302030402061b01090c06020f01061e05060c0f010c020c0109060302120610030605030109050f122d2203050606120a08 78
    0x144080c0075041c00e01c03110b201c0f0103550f6503800c03803404500081700300310b03403410b042100c400042811500c004d02d5903500002e14044d200140207420000800089483d88100e04008481c02141c0c0500300308080b598880c3e0082d21040c010309103900c900c034180190403ca100500a590180790024552443d0404c0450341d60010700740b5034012184da5480c0d414a20101d0001c0250200030081c6030042d03c030030390004082034215100c0342c000b03035513512000b10f40c018003104074098502600c2c0d05840d059520850091114503149413060b15074407540c01d02441282e0b4503404140ca600340350080c0c03140c40046440388000c1d03050340190880c0e80080c0c0b0354030740013440340e20309007400106c1f040d418240081d19548500110307095030700e001e4080c0d0b45603015401d010440c5500b0400c41054080c043c1c841c5040a00b10040c80c0000180c08080403e81c981d03036403e11000d4070190007100c002c5800c2c100d01003500340a000c00d10110143c64442921310340100800180075040031068005001c050348081d00420b041541c401d94143c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 131556070 1250 131554820 131554847
    0xc030a0c06200307060605120a050a060b0a0e04080403020a0e01080a121b031814100309051e1507030e030403031b1a0103050607030c050d0902030a2a120308010501 72
    0x1520740d1803204401c0b07401e200034050306004010100b0b01c0c41c10701c01170142c1c80d841105c1a410f1a44140342c034030085100801e070089200da01c07038008202d40803a500003e0214580e600001d09140403541440104403603c402042224030941c3c590000c69a0b580c0f0603148140c1c00d04c00c0b03607a15008010490b00080305018021112201401c02802d060003010740c0422888000c1000c4010880380b030300b03c5c00486140341d4600c0041030002140507110b0f851601080381f4030496400304042c50f840da40320108100301441b8680b5400c0401d5002898581d01000d01959619a0501050315003950350125220510901941d001c0c0b848400042d031a0074556501100c0c012040c1c500e1044800e01261880c002075070b12f10040c1000c0c050420746035819411403d06605159020f003a1209051401c000708141c0c64011040e2a04003901000024070140c060002c03d06100c03880000810101c000915481300740f02803950042880403465080010f180c440442d203615000d42030011700800d100303800401881d8400e104050542 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 131557320 1250 131556070 131556107
    0x20a0e09070306051008120a2a050a060209010e03010504030905060c03090a06030c120b0108010e1314030d18050a08031801060b0d2a030e0c0d050a050c030a0c06 71
    0x507529141c1408036002540c105d036070134203010713400c016001c0208070307152900305c01e099050b00d414125400601140740031804405840740c8000480c1100e00c0600005030501e0b00541516075010451501c1002580a03a14040c0030a1440d95442620308052040350700c41c0354152038605819003040204143c0b90404203811132507100410481c00c8940382e0000500050001d40c4000c20592034080016000c121003d10b40d0366140d00c0c0001c0c2c0241a030b84500d0346411980e08004001454440a00c401500d036840d880c003400c084520101c00c8060580000101061145000101302c40a0084071296800246040241543d844034601c107004c18060360041d500510b91740c021143c044400320f40103007552a03941c801d000303100c00402c0da085c2c089014041c9407070100c900441c00020013000c0c203060141c0c6540355074103001c050b61203140c1c8411900800034003140260051410749084854904142c5e5011894070441c2c09018407103800c003250500142000e85142e02a009440080c00e205040310201856288d20282c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 131558570 1250 131557320 131557333
    0x41d041703130c0e090609030a050301060540050a08030f0c010e06010609090605010813030f02190602190507050703110d06050c1801020708070504021b0706020304090b0d020a0e09 79
    0x2c1c0f400d0801900504042e800741e6514034010b901941007900040030440e00d50000c021b180010ba07400411681511030ba410296100c40d1307030b0251100101809604104202c1e44142c401c1c0d0554150040c00210640c803420080f2400e49079814001d900600c0c2c0715000f0701c0d5000388031401403000c05c10081c06008110500001d10340c00e0030380005181010a030b0250b0040f441c040000d002c00c8605009080c0a8182070030f140c003050074120320006500c150201c0250030812a11005443c0c2e40c030070700901409170100746400d00c1e55441070070110300035805889030141c5d861002c500d040d6842d000d1000e8401c01d81e04480074001d09032954031000b154401c007030340310741d4426102800600054110300c1030500801d03001c55000d45410100c031111740701d140e0030400c9505561041d201000b2458001038003005036001581c0240e1140c40d9281c03c1e6000da0203030071140e20140a012004164154000050421100302d02701c01e000c005450000d10402c8102480007030340005901078144006203004007195088005070301106c68 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 131559820 1250 131558570 131558573
    0x9050a0b0319030912020105070f110603010603020909010806100312021c080403080906100b09011404080c01120b0f01210c0305150405150d030207120503041d04170313 74
    0x101a0003104000a03115034140c000c2c01c1c154004280405820b091201d00710404072500060028000c100700108000707542070b140002c1100303881b5080107c440140c910340d22945c41d039101078080d404c103442a901030407101c0000100c400d0300184181c0200303c0d034686441028110b4441103805001c0c960900c0551155030085d18140d900c040488025201c9580d84c210141854940101801c40161642c001c42d4005028080700300040d120280031500004000340c2c0e038590500050701d4010020414000f030b00c00c0880d001401450100700104e2248003680c511503204803403400d010448006200c46a001044807000b1700440d4002d14080c140000c40e29589403a4595880480003540c0c80f1040302c200087e141ca007408540c00d07142c80c0c50600b00d801150140034921b04000c101ca03401502900040c403038a03501c240c030000d0500a00411001c0c017003100d80400340040700d0418540c3d03640b240c0f0074a80030071451620244259810b01e40340b8043c541c02900d4143c210381064029800d900081c00742c10052070300540000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 131561070 1250 131559820 131559823
    0x304171201030807020406140f060c070e04050604170f0f0f120405011b14030402040b060c03040f140105090108060108040c0918110109030209131704060c05120406050409050a0b03 79
    0x7402180725840c0541d8811052040c4003e0754520f83c070020b440950464259095030b5400008030918105981d166291030a00b0015490401d81d0713805500c4000460301070009010001c20107911440c040d05041150301c50006011525124030b03002e500801105000c11071001c0c1c04d03c1c0003403d1050301d86180750309000387c1d40e140755042d100598040364035070b41d00c0028802050003059001d06018180c04e1044500c0906007481c440c1d0300c00140000c3c81031360340380d00310300d4070741e40d03400a466100160000701d84c2c0b26916072004131007900060042d400c22080d465200c0b02250700c100122546c81da0180e54031003013a150440191500b41010b0800c0320b44411421010079036044901c100c042440b604403400c82e481c0181e081c01d001030b020f0b1070f26450400825107000c1c4096111121295004400711210b000024000d050141041c000348000320300040f000600051801c5c1e01c082c200040340c1c0102c041d6000a03c0c0c444d2064001e124922498001c9482440100584882a80302071b511112030306020400754030920000317 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 131562320 1250 131561070 131561107
    0x7030305120c09042a050f160204020403060c0908120a1d2404030b13020913031202042705010e1504020403062f0901020703081b01050421080c030417 66
    0x2000140b007174000c1c41c0000300c06404600020805814410314124910001401d940314018810600410194510b8210348841d41104c00544c2c01c0b1030f0822244a00d400c00901803c490b01c00c101c00c0d8031a002b00c0400450f51a02154410b55190712851844103030440a07059200c8283c4480354001c034034031340c18503450382103106442c0e6000c4001292076450b8110325102003190009880322543c0082c4150041c01600e8103010950000742c0c0c83c0c100e010366243c900d421900100c940c0710202c401400480d0000320030b04442d100707813484110094009156036031581d02c0c0048450074854681c00000141c08140410011035108003c600081c3c40980b400e0303140c0d00c441c03040e00d0141d0301103008052a1a8030b211a980e4424540c5c100b4001401803e10f4004d030b12000035503c0b14107010207481010002440b555803803c011041ca050740d0b04c41d00900c6103103000e080100b42400030845001d003076400e030f80304040c1e6640b1030f801040c802c9028a2441f070460b00c0300d4070750f11140d0b082100514800ca0040003255101640c103141c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 131563570 1250 131562320 131562341
    0xf03090b010306021c02160f0804030f0b070806030303060a0302011d060f0301061b050a030f090905040311010e03120f0403021f05100f03150f0f090b090f07030305120c0904 76
    0x542d4031028078481d13060645485d244002124030610058400d003558903220a40d240d0420000001c0710014180804244143d0384000e01b15a8111801001c100c040da23080c51041c50303a51505511540c903107060688a11049402c517510401380d01d0700380300560188400c50300744560110700321034001c0310340c0c08150fa50307103c01c0952081c01c00c08001082080d0388103074186ca111034603a00c21014100140e80302580d448003184002c091094001030900000d100b100d689000708000c4909000900b01800c014050011801c4000c00d03035401c0c901c010034170100000c211804a558040740d0100e0b1f41d00d0750320070140184013030802c50450152045501c6405014840c030594020042000206420030000c2214030403060b80c0140c250540c210070400101e2a070418a18090f50010000318089c050300e000000104882d050742880180b0f00007403401403040b44402e244c401e03e1150111030340d51483e0000340340e41c0c403194440100054400c12010741c1202000301803a40043d10f03c80601d041101200000d01504c904080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 131564820 1250 131563570 131563583
    0x140f01090501060803070b0f1302060a030506030d050408100f0e0a0506010806091b01030f0902090a09060f02070c0b18030111071505090c0f0a0504050c0909100e04030f03090b0103 79
    0xc0001d0000a00c9248014014200298500345059a03070240240c001000c0d9102070301c240002484c0c4020316965203005960080c101945c4501c018005001020203903071490080c810007018041260045044038140c0d0240001440540303000c00303840c00540340c0002031102d810344840464500d10360802480c40094811000ba289542c148106c0600d03050000381100d0859000025041031840002e561000610080c40e01140400c0415812800386c408008001e40041c5a0b508100c0e401c0c000d40e01220007240b18a500340000105404100d050303015040d4058051300c08104104556803800006000004200c2010300ba81d01c505d000003404c481c01c0808116040703070300186880400138080206000c10105400c10005401c0a840c0c5580c0c0b900b203c0803960080400d1030081c2216030b10b8a001c2401450000c0042c0030524025034101c1c0641c1006040714010b00d50034010490b586c09010541e800d40c0e84800080f0010f9890381c800b01ca42001588201c418142d03035001700e1000c1004102c6890180d4041e00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 131566070 1250 131564820 131564831
    0xa02040e0d0f0203030f01030618020909010501060f05070519020a03080703050307080a0e0a1502220f0e01120b0402040e010221150d060203040c0b0a0f0201060b070305090d140f01 79
    0x200c0103050004802c0341c40c001c54200304200300342249107a8600d410740781c0160001406005010b0507510800304540040e40c4200700000308001118150000c07416075800c3d9031040c074140c4030701000f6600703401a11001002c64100e00b0707400b2120b0040305904003425000402c0700110315965101c0c852158829607069000031000004c00026941010100e0340100030848104108216031025a49a240112004026658107030014659041580546010441500340752646072003118061100b9211803250080800d010701000604840201d4002d0403190700240344c050b11f400a0b81c840d400514010001c071391041e59164000c808086c2480505503252551440407504050011011845440200802d0f000c0ca02c09621404607264154002085548114003513181d84451404161240003900710150001c0b000c9080c48400f0b51082121504016a0f0020007082d902c0b01d0305c0030110300c101d004c0540822000c004144c49400c01030300b503018160254001041502c1d14000844c00c04070200c01c0b101182e9100c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 131567320 1250 131566070 131566093
    0x708120603150103050c0405060312130311010206190e070b0406020a0605010b0a020c01080c0d0c23031003020f0103060509010611010e0a03020c01080a0e15091501030309090207050a02040e 83
    0x100302c0040210000c4503030004940c507540e01c01d6900c21084041c90f00691b2a40c0108070591001c000c14120348503102d42450302c40740e44455951009645110a0b0348803480c4241c0101c05500110708c81d4000c45059112010507403207144154040c4c01003c00c41d141a10401400040700104800a8406030001c0d03406404500a64240a0199a010b030044041c1410404c5184001c03500010541c102c6002030a06040356503a603058842d481c0140001040081e0a1621110200ba0f120341e91107501c5025030b076521b400001100e05848140811501001d140c010020288058605902d40c842001e03070514021496586800200d00c00440aa000c81c000c11000304050742031070402c0c003c0365040124000107240300341c955140256035000c1c91541c039041c0090f2102243c000c0903190054840440c42804442d2100070324008402040700032510382129000303071028450600030f8000303024101e13030b00b56072041c00540c10306038590300a501030b4030221814403a801c0b0140050b02d8071b001c0e010000d00650080c3c800003204 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 131568570 1250 131567320 131567323
    0x14010503010f060602060106180306110702031b090f0a090c090c03060902120a1107050102030f0f0109090308040b181603020103050708131509050f0105070e010f051e0708120603 78
    0x4006140080b541032040500641e03600148850444e07110345049081e180f05070014407281c3c850b0b5000038200c41d081148000c1070140b910001c10350305200350111010625104900c0d42c2c4111188482603000388642c01158486201680c2c181d000300c007007400061042c0312540c0305c0d4082c5d0003503804030814545444501c01c00c141c152040c40018452244198a050311b0a189032604000050443c0e429613514010030b091003450b04281c0340c0c2964410300844d036034141103161b01c405200440d04c81c8504017a050001c61840b2103802a10b290651588500c0780e1911039a580400701e07000182500d050054298000100030000c2000403447c0800454641e242410b60000400b9154020403280901228009118201401c0740d1404001608a40744001040030300da05030004e0546c2d100701402a200c2c140c0c48103031206040d440350740151180d494027101c0858840c0156282d07400c00c060100420801d0048080d800c2855a1030142d400820002e44e150010079541c6c48210340084401645182d00c0c0c01c01c010f00d9040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 131569820 1250 131568570 131568581
    0x40209040b040c0e0a092d0912020a02190305031902032208060c191803151a120d0e030a0f030810090911060c01111803010b0612060d080405041401050301 68
    0x240403200b4011000f40e00c00e4440c00790300a0440c10660072071f041c8000100005584042411035001040f141c210035000c0700295202880b11b801d920a664208146050120140d115003ca80e400f001860414002221909da45030f41e4001400940c00101705000c5128aa04003040e500714a40d402c0319886800c0807032852503c44000c210b06074045081020a2404182e061301d0084600c0f14075082c41543d80002d0710101088595000909450344600c000701404520341100f410140d51300c903075600c0e4507030315000c10000306403040010031260024118441403621030404014046005001c4542c0003060303590ba20f004000f0b241d010b400180d58402400744d100780b112031981c010b1081038010321800e24907485200201c00804007943c81a0000903205c0980346013900180d00240c032031500703280c07281c1d200350b50808004110440a0301c00d52178001c0a107143e141c044190303481da107030b03000c1c509101b0713501c600c01d00150003180b500507920403c081c80000303a0766565009841100d2102d00c04880d155140400b8582940d8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 131571070 1250 131569820 131569829
    0x309030e030703030219080418020304020f0a030c06110a140102070b070906020319031506260c0403020409020a0305030f0a0807020c0315060103021b0a03020d110c040209040b040c0e0a 81
    0x2003101d0403c20100ea400904100703001d00c545411028524249080c21842c401d950020000752005154041420350b545d0155100398001d440c4844c101014404014095a041c08000c000000080060044d288140b488049030030ad16002c444041420351200d070704120030706900c4101030790001190020824843c40507034111b0864200b42c480340781400d40182d00ca01500c00700000320043c0e03046e041255413007030f04450b00360507060244441075501d03600f009015100200c00b0500701408a65004000582140a14460450540c41e5420035043d542004060070380403500b0399022014801c0400451814001080940b45041c1807a50720041400007503c0c8420007050300382550400e0701500459200412541803401301103900c1c03112690340da00107030001e014210703484521400c0001f108401d01400a202201980640c0071107801e605014030443e5945002404d00d0780e01d0700000d000c140c81e800c040d0050260300c1002400400c03841026404101182c0c2800d903240c001501100301c10007942860341410b4040c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 131572320 1250 131571070 131571073
    0x20f091903030806040207020105090405042a0e0c0d060e011409010b0c060f1f030501020d150617191b09090b010525080301240504050f0609040e030a0309030e03 71
    0x15140d03442c09056100300070101c80c003e980003c4d01108684c4602d003120112100108100500d040c00d041a80103c0c1c1c400388140d8039940344814610080700800c0c4144112005003038007910582c0c402c08000c00b6038010490099050751240c00208400302402240e5010f0010a0880c0c1452500c0b10100040c060041c0c0c48541020f804000900b09420042510760344526020000e8480d5200c0f00c078410048ac107080130b80e0075070041c02c40e000300400806400900c9100580d001c00d1145502c6100c202010000500c50403022540010680c1003084e003442056600c40242c1c905400d850301010000d005641a0301d0301c440c8222100c4500382020354101405078098808150f04000d402003a400181451040700c4e034103c0c0c100c00807450780c1c1c0c0c400f40141a000195500c11f005a0312940c2d10140080c41e042d6049000d032010300c4445442440d80d1295040d00c0881d5001440e03586a039002500b445503544c815402250400d88034a2140301e43e2400704028028401165800500ca0445050003030074030041903c400d200c0e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 131573570 1250 131572320 131572369
    0x601150311090d06020c0a020604090f0e060601210e0d2001051b1c0903020325120e030319050405040b060906042c040f14010c0807050a090306020f09 66
    0xa522102c2e4007a0921340d01860050760740400500303442c944099a40029030001c000940030411559030381000d48502e0b0b445400b4010360300b128580c00e4941c00112102c9001072100e41240c04a10300b90b0104440c1040000390004490165080403400e1050700b20780b15011550307030000704264224078088070421081d50b2008214070704010074035a481ca1130282490110040200b00340c42c12070140305207844401c0c0701a10400c01d0b07941520740a5100d030000d008080c41010b1900c08840050076840d0f2003407a480c0e2008256045d19000b0109450f1444d80440040d007510013889070281d6142240010260760025450b116181d0303207001c2c104000e440c0c0501000380078000510002c0d0143e100c4506440c10b8498802c10f200340050078101c1005201c2005003d0040404c400e4240402d01440d641c0b0342c04a14000c000c0d4001900c2500747c914203031113000ca852400030b4012000103880302e110301c002d0710200800d4500441419901c0d2900e10980c0c0001d40c0e1989840c0c8000341d4050103140600c0841010844205003001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 131574820 1250 131573570 131573587
    0x3020109080115150212030f10060507050a0201031d0f0a050c01020309031b011b080408210307030b0a0b0a0923010914040609050c09040b0f0a0b07140601150311 71
    0x80c4000d0922606040c105840464401c0030f00a00214640c0c070030b150790107912440c00241c4e6100301d600a8070411889d000c1c0501c08105a4820ba0840c0c94190308032000f003c400c0d400d5401100140f1401c246103854041030a82e0f00d00c440001e024444a2092080003803407800d10f107040c55401d01c02d015035002d0540d0300402032403915413004606025480114445050b84110520044c0c44081400101c28004d00c80c00509504014183d0b0160043c1d034299001c0750b115648480c0c1120141880c0b90040e01c0d03491b41031000806c003a200350480912401e018040202c00380c2d80d998510303001d404c070405c2c1d040401c2130f90106201800444240310b07048160741d44031084407013403800042c0841b003090040716200c48010800c640750b51195004032006140300d5504005903d000036070000c0304e8002100107841141030554180f22450980c0d03090140c0400100b0300c0a06070f2400c01c00c10504d502400f17080310450810381580b406000140001802044442e4040300c48081808000741180c6a904102c0c4100405102601 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 131576070 1250 131574820 131574851
    0x1020d0c0c1b1203050c03040e04030903120c020109030818060307032301030b040b150a09020a1808030d09031103030a06080709020f0f0705030d0608100e0601050f010e130e0601030201090801 84
    0x1c00b81c2c0d0541030855881b40072803851401d510a642021641074161401c3c0410180d120ba80441100e0003803601c00007444001b002112040503401c40680010700b80030051021500324070050405403212100c21400c400c0980c049406504107c41c0c540109544143c21164402004003c0d4002c5c1444421500a98116920a00e00d404c01900180c00c200700000066010708a0b0382d003d0040650044c4207260545d555600a070103503201d452102d0010740940d114100341c0e240c0740d01312001c1d200310002441c01e2588a207540c40062690a00c15420041000c03144266a20b007840118094400b80002080181c240700f29146040b29035400803041d2413040040d91004541c002c166107408081d4220301c1c0d654121410060b145000311013000c101e03940f60090008522900161400d00c2c107680c5003042c0840d42c1d800714030307079100d80c0c091203000d030007596081c0c1c42c0c40150b204000c0483c0c1c0400c024114844080e94000c56012502c64580320f141d56030042c8018000c2d582c000c2c0308500103112170700090003141c03c00c16260 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 131577320 1250 131576070 131576099
    0x1090609090512070203160306050a06061112030c091203030f0f16230d0b090702150a0b011808070819110f0a090e0a12020d050406080901020d0c0c1b 66
    0x404038900c0030428108542d418803c0c41c0180c2c2c11199003901f0a516402d00320b00800e030644119131164900a000a90240619031a680726a28500075060342d21110300d803004103610082040c141030343c0401203801c0599490090707421042e28100115183d20742035446018101c3c02901c800c0d00c2c1c09662040012401449000d0401450145400c0420420742201d00030081e59040c4d502c51200008502c0800e207680552080142c1042114143e5090300c2d000e40990f101c21842c0d108104008261001441e0035000c0e4210141c903c80c10b1503c110342842c1e03e21840c50962045c2c0000d0903603000381c1030800454404020f2903d80d50107030b0141241c00c120703a540300c040442d41408031501034201a0700f0725a803031303035030076000c800618203030b00103000c10360012081c40e44441007810304880c10380c0190300590b0110300c006025100c402d50742e1100c0f454107040c40c405803142c00e07009000d26510341d000c0092001250701802003080049a60702d86a6402c012031601031022000c50304440d140040c0710740104102220344060 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 131578570 1250 131577320 131577343
    0x9040e1b030c130e0a02041a04140603030a1d06040f06030b0f220b03030309070f0803040e060603040501270201030f0c080a09030c050a03080403080c03060d020402250b010906090905 80
    0xa000c0b203518444c9030504080010107540185440131180e02480e10264081e44100c04442c1004001c8408000c503841d18019030b2101d4142d0310900c020403019003e8452940c2444003815280c000805580020760f80c0c0d40150007040f0615817001080004a8050103040f0161000312140540001003101048103481d49140740c8a00301603030290b40e40803c41650145020074006426241c1d28031342000255078480561040c803100307414091000070440004000e950607034024030301d40c1c0c02d50380b40d41040211316080940282c8031550f8448899450441025010541d109900c404542003004da000141c1101d0462400111140c109501c2c1d00c0c1059208c0c1016070b010294403400101d000c00d07414101c80d410503102004085200314400d10040c1600030640d0392049100760380b44a2130f580c5600c02e502280c00150f0700150800c080d8400d01e0300626280d0013420616010351006024031400301c110703055040301210269540000080144452501c3c2d02075880644113a5500744001880b95680641d5070180004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 131579820 1250 131578570 131578609
    0x601091a0f130f020c0d030515040b01110f0c0a1202010806040c0504050901080601260a0b0a110d0c020c01020703081e070b070e01020106090507081b09040e1b030c 72
    0x1c80003599a500c080000746181042030810039404a100000000d500079051311500f0300c80d1440f040c181e24801c1c02440c3c4292580001412800c2524003480003600c0700144050612031088200c02880000308000d181398020384009110a43d080c0080c0091102c06800c850052044c1892003800b50342c00c02c80c1e042d004103096034000740300b1b40c854a00722418003807034010b9944022040c0000461010010710300f8180c801c1c00940d4803c1000441c594118800300c9030344071001d90032050b07103e40810f06034421140d01c40c0c1e0610010410103411003d41e1440d0307100d52740075401c1c940d462a1504540790704004242000307000380001d083c0d48d410360f06da00d00d9a011304040b0f4411042c0b14605451055222403ea400301503020141d03014a08000202800d000c0015034030500641c6051030000c0c107500d00f03000e00c40c013520361074881d2185500e403101d0700c108105281284a0511400b040f142c8200e40719485280d84414801010344070f60100c01640c030810b64000d0004034440d500000300304d4216924040a0074100741c0912 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 131581070 1250 131579820 131579839
    0x50c06070f091a12010506070221010b0a08150601050a0909050402040b030a08030714090105040608151203091201110a050a0210090809030607030c05030c071713080601091a 76
    0x8008503940074254115103101e2003c0959480c8003403196002c0c3ca5240d10130410320f44160380300c10501c1124051140041d40c085840103803826440300020480460045403000070604404840100d010101c10340c2c0f090007268440e030030701446c4c0c0361001031180e00500302b460311038900110004000e001c00f4550045403c8180da50300414215039503079010034500300c009016100e020009060000140c0c100310f410768081454004803142c03d41c07040b4126400c3c7c0405031640c038100360a1410031140004014405501c440c1010020605642c40035020082d8040d910025136a45594500780b0810559013a81d8040705e038102098850002e20380000d4810100ca2450b0183c1c0310908110101e1070260180e9050001d1803408502c00c0c18070034024001c04800100f0780444540c0d895800302102191600c54000001540a10124504952050080c00828094642c0c0120306818039100f01150784440d600e110b6503041042c0c2001285010b0150a00410218004010b5019440c040700b581d100c201c01f0652242c10401c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 131582320 1250 131581070 131581097
    0x408030a0c0c020d030215011401020d050306010e030105010e0105210604080a09030b0a0203010317090307030605090106090509030c01060e01030f06020d0609021308070506040614030702190b0103030807050c0607 93
    0x400e030030612680c00500484c085031031400c0180d2102c0e1303071031a00c0c0d842c520f0704000402c442907120005482c602c0c041c0c1c02000030040c0000304880640010704018100450082e514206540c2405014081d01d059000b9001c2549020100600402104454000c0c80e4408c00142c07004240030591a82c0035400691540d0303600c0259508032501101074000800c10b030b440d00144002c80d01160b01a5050768800c108901110703409104d14007803409420301047d0700d907110800074400075800d034002a80220080c80042440e0b80c503a0880c0080c1c4008a80c0c3c5003c0d43d2010800000030542401828001c114980b4500c0084d4110340340c0640c008002c400241c40382c5e0300001c1c01c0070741107426840031000381000d0074215100da036102052138201c5139510900c00c2074440ca000100303076890010304a800703e900d5615800101c0d20390000058480c1c000400690a60041c2018408003092004000b0b40c4140700303c1041c00703e0b42c1145030282c007440000c1c004030100981070041350052200011820381013612420304944000c940d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 131583570 1250 131582320 131582327
    0x10306030b060d2301060609060c0b180313030305030402210a0605040203071d1e090a110d0b1812070b04020d020301091403070b0a0c051e04051801060e01080408030a0c 74
    0x501084180190284c2002510010190300c1a411b8600c90b03070301c2d80c03043c6a441108440249000c0c1014081031420030100714103c0c2180ca5500071445124290303420010b8207072010818000551098002c108000f081104524118a0f03410f43c0c20400d600380d01101c580c070454a56204501c10f801460303da907850208040d9a0100b2900780280401e409520007039000302c01c5030340001c03010b4840440091240f080d850402039080480b42c41041100020104044191202a020341050a43d03070781000d54081110301080d0140583c0b0300c0b074030500c5d104201442540074102e26268210706054403005080c440c1c40b0004040c101c4031034001e41c044515007050701c9240002401070810b0b4070002c00d01603103103c03203c0e02400b0104c0035100741400b5a581c0c404c2c554805860030b0580d482680580000380e4100704041d0205200c452181e143c0c504941900d04051f01c5901052110f214041440b10103000240100b000c142e0081d81095144003e01c0c2030416410241d4403040c01d80800341071060312070f03140c0b001600c0c031710301c1b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 131584820 1250 131583570 131583593
    0x315020f0a09060e0301050f06010507020a080d0503011d0106020a06020f090a0305010f0e071802030c0c0706050d05010909020904120203160b0709150c110f041b020c010306030b060d 80
    0xc0324030200d6640c1c00d11100508410350500c1008041a092105205285018440c541c400c8542c22100d48403503a0b1400112101d5100c0b450483e4862842c02d0080b841160802c0038034420030040d1666680d95043c150018516110031003102048080200107001c059400300d10340c035045038402c1000d621386008804510403401030901c82d68000310b40a400001b801815000400d000c01d41d0581040300c00d91b8002c13419240d00300d90040740d010300348003a140d032001c0e03800783d00a42c2d1002d0507400d40c1c1d04140c80c1c00580d0741044200d1340404001080450211042e0044d48070f420b004021000c001c00440429502040240da00108040c1804111040c80085203009000711800319104400380700008000d441c0040303550001790b41d0000092120080819541d408141103080c02c841ea85a0716010902070751100040302203091a6a00314011003c0c101e05920f0f24050380316529a0401c850400c4451503000a151100001c40039040504001041000c00c000c1c011094000c84140c1350458400200d0030a03045051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 131586070 1250 131584820 131584837
    0x5071e05060324040e1b01030e0721050c1509150316120f110403110109050102100e0a1202031b0105060f1201090b13060501050603100608090f011e0e010e0304031502 73
    0x14440300c8507086404000160001b1000362000c101408070300015907920181c0e03004100454030080c3c0c07002c1c010b945400e050600b4a10500c200eaa1071560b41012603840307041d405800c2c10003c1d01040c1070740e0fa031a00703600d00b01c0c1007490304120130b04518015041103200b1001c5072030942031043c3d003010102152135075000104000e8109a044c030000d00060700e03840301c590152105031801c50b0302c01c0e070b4502c0540c41403103480101c0c0c905074000c12820712002e80360301c01484545441c150341d2242c8291780700061040480b00d20170b1521600a10340340d0403110741c21080300034031903102e640d540d1508007040300c6969101040b016442c4182c440d6190520130240050041003080741c058000350f400300403c914511003140800d44584036035018842c0b44da86a051100030f02082e242c0c13131031700502e40005129080c8141030702c81d40103080c041200c041050140006013199001c1c0a40c084029086262a41d01d103903e003c2c0d011201c0d0400300070400d005404030703900d03100d0244d800020000c04040c40507041c0010170b40c05660654 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 131587320 1250 131586070 131586073
    0x61204020d1407080a02040b0603010e0117070f12030f090305031e12090708070806010f03020d060b040515210d0302090a030c0f09050c0c06061c05071e05060324040e 73
    0x98484d01060754501c90030004038441c509040080c2d01c18144030041c1c1e41250100249070b4126400d015102c0d041d40045200601305200f25a400038000c80d0400c0e41100401202c406d0f0f800c92059810010f0005c0003005e9290184502900d0400009200008445a9101d00000b081c50768109030340c4540e151003120801c00c2d903456400244807903081c02003000c40032541c0a204880c4455591844aa22607070244140084100200300400141c1452a21011128421903000801e1031241002400301d41e011340d5009800002240e00c0c80160a007020000b44190f050b0322038100311190302c07404543c3ea00c500407a080405402286401a42c2c030751035200005541e12080d00c02c00c268a44050040c9003000380300b400184d5040501103075500b0104000c4526a285400140030140d07903044c148a0b102c07a1104841040102e42640300d000300da0240603103c090014800e8141484050710341160000010742c104501ca40001c0080c0400900c0c0428200c14075004000c040350007210380000030f00189141007081685 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 131588570 1250 131587320 131587333
    0xb0301051006020717120a030b19030c0801020f0f1615050a06090203010b070b040305130902070209010506030603060a090215030c120109060b070f060225030e061204020d14 76
    0x710071107500d201d0a584281e802c48800c50364a0703400040843c04656000440e0f0400c07560f100680c1e2040008048490b114180844c000a0050214004544080220221020082c41401000800c0203410300130203001d4000e50410f401c0f100c600310b081c812000165240e145c0002e040640c0c22211043c03452035500200540b4001080e4440f82014050071605480b045242080c003182e0300d5101e100342e0707041c1c4024204071030800d005691011f1240b14041c100381c051050078001414480c03070400c8090003414842d080903031120f032544140f05146006070406031143e141401000903940f800954150701c40c205507000308004810340049401030001401000074080000304200c100358085004066417001d40982c3d00c1c0a80e6207040b500122036107405034450201c405c100d070750007041c24001b103144118041d842c018a8105070740c030452403440b42408044c8010079010000d03014180c01040c0c18004180582d440c1d440c040e40d045072916450001130000b40f090008002d00c009100301c00380800b00c5640d4400c06c40d006c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 131589820 1250 131588570 131588581
    0x50a05010e0d050111121f090c0908190314071a070e0d0b09061303140c0102040b0d09020a0f050d03050c0f01050a0614150a1412070e040e06040506190b030105 70
    0x4040d442421b0302000b8084400100e416440406141078411b8805404c5800c800c0c200813400001e0140d00c074200040040110011800340e10610502081c0c1740c400100071074074812850054010b094003059070900390810f110000200320410241101d4803804c0c04030301101d41d02c400056170300010b0303921019000300d9498609410884504405401207811800f200c025a0b03c028034851807000001001b030007c2c000012003158005100e0103014072118460015007450380b114482c1d6110307044190041800d90302d45141800390b0030240e01c564060445161a0240d940c1842c01250803c0400030008080000006041003640300c1400f0f1581d01c640001c0c020700440c00c0040c0d84c0000303007169003e41d502551840a07000054034010054040c1c1c41d0030340c1161810026103a00c182d806404c2251130340100c3c20100320000c0265640c6900e80d21500c0c16448042c1c9035107500081c4001c450030f296251762103900040c140004184001081580035200075100e039003c081703020320740c4082c1c80c948103c0c5401d503003008203000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 131591070 1250 131589820 131589851
    0xc0a0501020a030b0f04090f060c020c15040e0601051312020607020607050a021c20010507052406010e010503040b07110307030801031a0103030f080a0603080a03021b07050a05010e0d0501 82
    0x400400c045030340241c42170b0014200011503980c01401000b84d0300c100c003080c000034001d4100c030086001d2070055803000b003101804a81450181582d003884c41c1400a07080c8200c80700035192581180003032808600f01061440d640740c29803010b000d8202038240001c0b007003017155101021100c11036400f91450f61607030101d1401c66030352035004004034810304907400c40020341c22420020740941c40e004840c09416a66a01204440c0940d07030303c05604121007003003d000442e0042003007001c2050200008005240140307110094100058101810001601c440e600b10b82c3e0b01205494201d50401401c5900d51981102a1141080f4100103030b0640004a0004203060b003200c1098122030145210408858020700d0f81c41504009010080118200001300c03072100b4850003801d680924401c10004100d500c0780c542c509030741c101010b18030000e0303000103001c4c0004003a070049114105400004200032420700c0300281d0b02804600560341007001808030000c15940e0129001c00b100d0f00300e002040070b02203041002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 131592320 1250 131591070 131591081
    0x11e060c05070b071a3106024006080a0f1b020a150504080708160203010204030c060e010801080d0e03030912010c091d04030804140d090512150109020c0a0501020a03 73
    0x41100000520000700101d02e9580f1034002c1c4e41e150303941b8240c0c13421281240f414205207800e080d40c1943e401c5c08000c0320800700e0075031441c071290700c240c1c407004035000d01c081101c18100100c40d00270390503501e03030081143c42e401418a0350000c0e090080410140740d0700812800402c220f05540200843d140d41c41c80030550045146003d085c010000004042e800100c110f041e0303041580c00820305d000030031103400412003840290281c484d550312201c00d0200c441d00003e0aa810540090341c1c900c241113800c1240781d401054030b40d0041002e081540d000e624110a840d1500d92500c1c02e0b0042c001c4492008003156414421101420801422030800c502d00085190003070142e61194008922480c3c004504031040f1a100c1c08803900e43c005010155035140e408a5107600042e00440d040e0003606503070600c1a00a200d85181440e095503280c1c00d07240b800c800c0001c030080029400600342c209401c5040e4900704c10b1801419100d0b080405030740d800321400754610f4410524800380107075101080c021201c40d41034122 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 131593570 1250 131592320 131592353
    0x32003041406040c1e0f1502100912030b0102010506030a0b060f19080705030f03030a0218030a0b040201030b0a05030a29010801050406060515091e0303041d011e060c05070b07 77
    0x403a045c0c11000c3c1002c80c003a00d00c40c0240c040c55690014200001c015086c00c65846c03509030710698086504a0850009482024000320b900100046107048055490300c0355542401d8244001d2109080600120340c032541c41c280090707d4030310401c001070b02603214081e29220b92480130b05a45c00c4401034071498036028070381d4049d0714841d0103900d000060500d40052402d103641c0001000d0351071038640060310310080d8800c0c00d240d00506203510341c8031503643d8140b00801c000d034020300e503c030a42e213080d02c00101120804645140b207403c110500703011540f00050f41c0303100b541e81b05900442034a450b2143c182030074000d01d110b1900000c50710011035a1201908000e00983c400e9100784280c0d030f220f80406c00b82d00e072074410195a02c00207005c0183c062800781c29040c840301e003241101804021040104c0d040d54803a03000f03d000c10050322861800144000407a50040084c54810300782d01a040c040711649809921408040110004c82c10b014441c081c080b440080c40c1161981fa902c0e002e03464640c908002c040c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 131594820 1250 131593570 131593589
    0xf150705060618220c0602060906100812090d12020703050d090e07030207060902041b0e060702030715090806040c031a1006030c020c04020a0801080607032003041406040c 75
    0x320381c443c1002030064250182061400c202070b500d01e00019460204038074062481c1140040d45030100784c1d5007450902500e0503502401c020b14244442d00d1900a0250000328a4080c2d9801001100404100c2d980383c4094008580c9d9108070b280b0000e9140070841c100540380344240014180865000940b5008881c480d0301998940f0f040e011054500c0780d500d204d030f0300120031500001103145200380d000300500e03481904001085000b03a00454110350240d2290007585400340e880365111500446c00c84000d01c0122451843c0c26030760b60109440340020300c40c80588944000152540f42d0088c02c3c101d003e001000e00b19520b03885d00c1e0400080d284030911040d00c901155601c18031030107a408203041c0c807902d80800300546080c6043d03c114002e001d103140c0541180240700780c0300c41076540c600040040c807040756140e50855040c11400c904103000902100c041c5890500c42c2c102c413084c2c801c0f040e00200403041c0c2c4203032a036a807401e2a0403d1041c40030f0841d03103402a041027104214103040c07240d055505590 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 131596070 1250 131594820 131594833
    0x7150903080c030411010818010c02030c0f1b21060a020d0c030507021b15030108010603060e0a032307020616030e010c0807080a110d030606020c09011809020f150705 73
    0x49030b1140728402682c001d00311541382c406618407540101d031081c0c0c01c04001c0c0c2d02d5001c0d14104800c02421203000036010070041c0c100083c0745190140401ca6040700c858114040c0c651010740e0f00d0340e84082240760113064020210481200880100784810000b88100300c03058400070715210300c007640294000c0446c03d9105e45044080340c4082d100c2e1117440d200e03186c1a0010b00301d41041c243c12a980480094502d40d103c1003000100c40040b00183c0a58000c102040012820a04600c0c2500039948008200a1503502c230458550200e64400800702e88a00f4031015040c0194069544807100d1040e4800030303401c15400034101191096203400c0d542094088e540d50519600781c01c0046682c44000000508040b609014620110b000d002c01081d01d80707280c0c1090502c14043d0640c0a003840d0323600e4280c2c40882c3e07891404000b05501400340404a1008595101103913040000d0041c0208a400d00c50468559035950181191900300e03021040500040810303240006020300105680e00c140e804644500510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 131597320 1250 131596070 131596081
    0x5060301061202130e010b130b0a0909122102070b0714040503070302040b040e060f010305070b090a150e0303040f0f08030f070311120708030103030e030a02030309010e060715090308 80
    0x201c1c805881558000c00802d9200110048000500002005291741c0d56941410050725034809030712140c1e1501c02c0401040d02001041004039006c51680100511810b00e401030001541d440315003002c1e14020f090201c07010500e03194034a03100c099203580604079440001c50070240019800c0b054464905907036030f07407649107031100e440c100303401a44195905648440c03c24030041c600f64110250740c5001401c00548081d1101034940380c0704090742d040c030050082000500070f0020520600700580707a0300d01800d15000608021401c10f081c1e501c07841d5001e410282798a4100d620400d460080da0000030100c03030f02c45454000a0100501622594203c00a0f0780e0001600280210907240c3c41020300d514181081080d0b20290b807201550102d444103800780700782e081c3c22100c80b01c0142c21080e000301e002e152690f04500d4098600b0109141c91842588071203160030041e640042111800d680038603200214001d9980401d00714040c0c810000c03c89039003000d2102941c01c1c1c03a031211000f00e00940c1c40740155210f6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 131598570 1250 131597320 131597339
    0x15010903021003021c02030a050711010204031a09160803030106031d070501030203040c0e24040b0f01031e23060a060c06020a110d17011505120a1805010506030106 72
    0x100d10009401031000300c0c92416a5000c1e5014140310000d01000740180c04001084030200c4c0d104480700c0000d19034400901043d180d000107891480155000214070305419610741d980c1c0c3d010140036003402d02641c0000960aa003061190303c601030194410f00710180d86890000c0c0d2130303030001d0094500183c41e000c99646403012507e810714100aa803800741c1505814000110301a5100420030f83d070002c00c00000094649151546c2c03032040050840501040d400369946a04070903580c013a0500c01c5040081034406c95540c4c40000504403002d0900050511082042104500b41602c00d8400c4900d03007481e544295900e240429105110300c011080f10b584c41c00c013040820301081c010348000071403200540b00010700c0c80d4010314106849040501a4030701e0940b40c14603100f2204202c1000881061105003e9926030140342d000d0a03561000c13944442c4030b00e5009000780034031002545543d5080c40400c2e06008580d2003000c24008400303640c0007000745403c00501901059500b01c1c000d41c0f134140006848a00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 131599820 1250 131598570 131598587
    0xd020325050a0905040209060906030a06030606230d020f03150a0606090f0b0a0302040e040303020d0b04020f0f03040c0e13030908010504080909040302101b0809160510020f060703051501 82
    0x2c0580360014098107010038032009400011416800c810200103107400d50703803110051032003880804008070b8800d0840c60501d05542050744090502600401020900d04041556a407100415112425007013002d00026442582d42d84c001074160088100c44520041030b0300d1020700c1195480400d00081d680c03640c00b1100d00c1d00e0f6210b000440c4551600c18007101490600078492170740280703000b5080503101c29100c04049401d460840201c0e600240d9036201082c03d0045400c0d080c13045030b0840c1800c85c4481c80319018842c81c107416101c8200080010204800740c52180e01030040d140010541d40303004030702c600010034042020ba01240f03021000164880701402260311940d44802900d0500d404801803082a00024004400398000c07264209611401e0344a6001010310f4200311250082c0d04403806401910301800b902c0c507541241403103049450321140c5c0c001c01c4030000d8511545410f00400304070300b0500b0554580981d030040909101035190305400041c020041c2d00340c28048100642e005454044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 131601070 1250 131599820 131599837
    0x60e1f080103030503090703060c0302091c050d050d1506020321060604030807152f03011a09120114070306050d03021f0e0703080a0e1c170d02032505 66
    0x4016038010300000340b04da00516081442a4102d03038075292a66907540a0700d203ca140303200044e0740408d641215141929600c1a4980c8441c120407008249494aa48030299800140e082c40400500311180910a61000c803401c100c9408117101d680e201c1500a45940c01f03120b040c4e00c1c450095a03d0030051060404030390203140d00070000c1d0314040c51680c40744403c1d0040d00041e20004500305006017089140d0040c0034100d078002c00748000d02411043c1d0302e078542c0e50110400030a241d0900040c000031a00340f005140d03400840064a844416a1000481040408402c1d48065080070b2920201c03040c407190481c090701d140c0c1c8082c0071300c94a480510804400003100078006034001020048401703d95140686d0303c2c01103105c04111a04094252840d024041e44202c65200000580900c010342c080f459881140003199150100d03039901a00d00200c0c0c000c440080c115814101c5140c00c1511203404882c120310101c3c10554882c030b04900402c0301c5070180d51079817109040c400c0840580600c075404880221 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 131602320 1250 131601070 131601077
    0xa020a0804031a060603150906010905040c090905070207050913020d020303132405070605041e050703050d1809020c100921050901021e0307020a080304080d02010b1f030f0204060e1f 80
    0x2006003010400208c9003c1c01040c1030164151001c80c00d9180e034020b98416200d10b0b1158004c031443c0c005040120b410041082046401c860414441940c80e000c059411040f600700303500080140c0c0c00021016004c0c0e01e002585880006002d4108003140190b510442c2c54000c510070b4001e1074a81c01c0000704501c400d0144c0045c20405c4480001040d55110503041030007103582c50a12071028000c0201c10070010820b855552040f8010010070400304034000f840040b500d4148401003c6103801a22807489014030924540c003c12000342101c4200610798504409a4080c401001d00d410401440c000c410440e0107660320a052072181d0b82d019400b20f0725000010ba00515041040e802110904402d0360051811804108020b0700541c2d01c1c0807032070020f881e030407014655903450301c0301e200d01d005003200215081d6414084640070136a580c0105c140d50403818840b480d0120200c290403801050024402d2541c06d00c042004108030380d00004c0d101100030241c6680c00c607556075518007000c00324440000fa000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 131603570 1250 131602320 131602351
    0x3110109051c050a0512091f0503070507110604090f18020913050a0203100c092106240f050103060e0906040311030c060103030201090b07080415020a020a0804031a060603 75
    0x41003556102e03210580140295070500909981d06400c144801458002039100031410034018644031a4403002c400c2c80e88000d5110060742c10001c0c00a020040c6004180100400d81c4402e100c5181c00104041000410599a840d1611448401400d80c4418210b0242c5440b0407140320b04a403106240502ea0004c0900e04076541d031000c280d1000b04104001c40303650140040303c2c0e0058804002109844d2060080818949007101c8020616209584004240c1e05107000400c605038240701d42d000c900343c100101203818029203d10150800703a00015128500c28441e00194190b404a480816900b003680c090104641d00c00100000703c1c0306a42a81d0f480c1c000c0d00c00b03d80003901861282d040800b2546c1541d05000c45080c1050904000740d01c184c0150751600543c40801480c00c445031b0f0700c205541004c03000d0b4105619207a11a54408403c40c0c007482c3d0004032802441c2c020002042c82e190701c51040b07507032180c480c980120a007000b1550a584c1a400300d021610501d010400d0301c0c401c28a110707401c80c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 131604820 1250 131603570 131603599
    0x11401020c0f04020d0609060311031203040605040309030b19050c07030e09070912080910110c0f0307050d030225050105070f0305070f0f051006150503040812010f0311010905 77
    0xa000341d1520b2041d83c410f40c20411108900c0060040b20000e01864500240003440c50405000048140322210302c40e4000c0742c442c988200e00c01040e00d400680181c000141942d59140c15210710056400240c1404280d00030001201d14141d0309401828041030107020300c0e214090038052500a04900601181c0e50b0881c80c25941400c10003141c2c42007407854901e80300c0341d455004413042103060720156180c0000044482e114103010a0a001c419107900d40740490481411a003500c1d07104004c03440380b090607001080c1510340e48c10800d0601600c130090803011078452034640a9907a04080480783c5111080c61404507032a024000c00e04101c40040c1c540501c4c07d48542c2d01c07480864203103142103040c00000c1c0103a40110790050181c0c44620b12500500381c1c14101c41c1040c9203481041c0720314158041c18a0b07001d0044075443c95034602820402c0c1012038032601c881c0f8100c13406003e01754582c010035076451300000f50b061003000306c001224054480000c10382e40c0b02004640c000b501d0f001d0030f90800402503100301c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 131606070 1250 131604820 131604829
    0x30403060e01060506040f091104120809040f051003020a0f030f0b0703020c011d01140c160303020d091a01090218011110050a05010614120c09031e060f011401020c 72
    0xc107401c15040002415984420005042d07400135084028914481c090034450f9408070b1048140302c02108a1340d905061a2003840c3c08041c480c40d400400b483c0d0701140244868807540c1008006090b024170601c01442c00e01d0564658080a03c4246c1c4a004030304800940611300184d080166074129408074070350001c42d19410f00c907040141070102019400c2020055001d8280701d5524001031a1740d0010f0b00451741c0f414142540c002c0540c10490380c0c9610700740019000950202d492812000441140000550406400034040c4081069491382001c0a0408000201e0146220380385400d00c00f0785070b80d898407603d504030b0041c540c41000402030004505042c3d07000c0e200c00e100d114580d108940241105001d04c0e000d9400c1502c0c00d01015403035000602405400807200c0c1c050401002400f401c108669502e82c56441d409000c0341210312000840c00c0254030107100203181a009610312030041860091800c1d5150340c202c07800003402101100104141029240340030b071a8605078001c000c000004420031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 131607320 1250 131606070 131606081
    0x2190302040e060603090a0819200c01030c1202120612060405030304020d02310b03010c080402130b09041a060603060d12030608100b1002070602060103080f040b0304050a11030f03040306 82
    0x1b03854501c80c8184840014620310024a0a1450044404210303c2a44409030071034006004030500c01d4090414401030368000100c07400d45800c03d00e800306030b00c860b0308425206000301d92011198240009141907d040350355107528040c000070384104020000c0c0b010380e0b646400091b540207100390810400304025280c900320030505c4500080007410705040300c4188404034910103000100c00c2030f4268800300400c20303074414914040800c2d002444403100c0c0b150010550325004000a100f2010010941040b400b180e02400034603101030045002810310b814880c407040750b0502c030802861510300004500c0c1c10320005803801514003410280f44841a60381c3c40c2d154004624141041507554000050070000400880d207001e5250300d0002054034911041c0804401034420305c40c05e651069104116581c0c3c0021b8090441c0c0e04111051348074650320715050401d11603070b48200300304c001c00300911040c004003249601d0024801d01d030480680300c0040600d070702c55000c1ca0141005410500007000402c03183c2d04070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 131608570 1250 131607320 131607331
    0x1020417060c072d0f020411040b070816060207050a0c090605060414130501060e0f0402030103032a0501090602041d09030a0c0c0e27030906091003090606060302190302040e060603 79
    0xd07856604009200c2900c034400d072001502c5c2403201e40704540550401d0700c260000441e0340005c051400d420801c8103412881115002801c01500081c0d01101d00c600058090101d980081c0640d520038540c1841d83e03880040701c034140e803182c140c03240000d842e000b148550070031644090030700c500f89445c1c081442480b428100000d6000f4400ca4240a1030034074030720806000e8081912101c076038804080a006035a03244110b00c2d401240b04000600c00709810540800c00041003010184003501c040702034550315044103000034182c1d82840201e42c01c105054025205807140500c0501d442c010104480c00d4400307040d18a840190410001c00040c3c80c420340b203065085000f1103030401d4580e61010a19000c1714120340c2002001c40c00802c0c4000380c903240d88184003003001c0200031420602000b002440034402d041401d48140250b8070701e8484a402904510035803600b11030200001c03640c80344050080c0d8000c3c120040003082c0402114a110301030720903581660048507034031003075640d440280b210561020f880d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 131609820 1250 131608570 131608613
    0xb010c11040b0904060c0314060303090409170304030512131a060f180601030506030a12051b01150f080106030c0e150d050309090a0e06070f050c0f01020417060c07 72
    0x2d5040e0507141e42d4640c9018612550b00003c8030b0b0000c80005048030000c4100601c5844004107000041d5400010b60f031158104641c001070301c0440e45480c1d41c00300c82e9240032110440011042200303144d000005410f41420954034035540c0d83d0381c15101042902d110034002d10400c145038078003050028240b078441d4441b80180171100072803001c0c000190703540d26986c0e0340d0f5003064681c3c040060a503414007440c1d40060f030a900a0201600940e00c2c50300002a28031400b0421202066110900f680112a110300010410080041043c400f0068410908034005e00d2034140701880000303000c050500c01c000450781c120442124203805c00315100d2103100c0c060800c44103209035640b00f60607580d4200c0108101803003072000795503d104002c00d02c0311103200144080c95081c80d002003422503001c08181036900040900d000311402c22a5101503603140903c0e81406540d01c1048a020b0110f1015070040050700c11245404a1201000544c1c50b0b540c00111564001c10b1402c0c0007800005070644000703529950700c1e59 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 131611070 1250 131609820 131609831
    0xe040f0b0a06091406190506030a09061b170c270f03030301180609051003060c11160303031a010504150302040b03040b040605070905030c100c0203030705030c100b010c1104 76
    0x1d4405450801385001d41c42c0e4160400c3c001c40785408880350708040508400f40c54050f20b0800003401500009000c15141500c400000007002001e902499000418921070040a001d144e0700030406041c03032000d003000607400f1010601d00e00300201550a40c500c1c58683d060075120780140700c000c4803001015940c024501411400f2240c1d014000707540a0b103110080d04415140031605002603884d150301103420329280c401401035050280311043e0550341c000d00c000c82c020038505401c880408006c281035004d030242c0a4401d0f80d90003810348001c2207a0103a907040c4003090070140304000103020654a02d01050f8100030401112031464903841d19801c581c10014100b5590300d4281c507065201b100e04441c10510f240401c030401c0040d00c59150480124a0000b104c5070406001c692b507081880002c0348221070303d0144041e82d51003407000b004110fa000d0140d039103031442403034030340ea0325000b1044401c0503000d50b604407010b070705161240d2090403005030755444940d800350b06c6841d08182c040d002260002c1d00c2d00e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 131612320 1250 131611070 131611079
    0xa0c140601090225020a1202060d062603130303080601110d02060412030b0307050f0402090d051014070207051302090d030e01080c090f1201060302030d080403090e040f0b0a06 77
    0x180200e074001d14080401507913440e020441c0540305580b080c842c0040f9401460100c016803a000d10f00010389110a43e040701c0842c1500010303400d80101c5403512199418103102044a0040c1007074114145031201515400e85114030704139480f030290f01c0500b041d03020311500420109101c0c002c03081c1c1061040c1444071203c408042010309000240c0d0304031004d130707028106000c1007141400e50000d00e0a04c0d49004c01c100d184040000c0e03110309480c0718442c4a0640666200070740d0ba030710b90441d00c074030318004c05003020340075245803042d00e0303800d007444800d101e5107418040c0301840030180504e4454582d50f800b80015505010401c4420000340d00b08000d0b0503800d001002c0c00352070344001985800c0c000e40326800d44d0304905000508604000b001d404ca80001070040343e05503250707800242e0501200311030040400a50084140c01042a5807001e0350501c14883d52500c0707160452811406a4020f507503c034041c9031146d820b110084003c2c1c40040c0202c1132048036030089102c1c02310881d04004031404c04103505a69 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 131613570 1250 131612320 131612323
    0xc1b041b020f06060406081005100f09051b07051207050705041406040c03150b090303190504090e0c01081518010602070f05030d05040b03040f06140105010318080a0c14 74
    0xc00306a00140e44005074000c108141040407581c00301d0704803414000b00b0f04180d1420384550301e9450400c04151150041501e2503200b140c0c08001e04407046000c8032590b0742c0e200e0440540300540d4600d4000300d4641409045512034001c40d02450340000050496003a40260880e4580c40317404240c1d41030040100118141d07855000d240f02500799040000905c1c10030030100011030382c0005054081c545040c5028040034201d41c40d9a040303c00031170381c0d03c1d12115040003103070440c03007000e00c006003401c0001c650001680e0454080c2013030342c06010b41084034045221490b0350300d103040d4a850707000c0741c100e80c0096030a044d141440241400c5c007400b003121611103400c00c0c840210007030300b108015070000502400301f1009035a9000013017500b10010003c034500580702400500c52406a0202d0f204000006030a00c0b0341c003130b0b85001d4a540321030100070034100740b000411204002c1c02464000303420185440d000c000300d00e400036025034101a5080c47c05140d108282c2c0d548102c1c100c1104d20b0131242501003801c080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 131614820 1250 131613570 131613611
    0x8011a09190e0a021b010e070b0906070b010f080f011109040e03070c03030e03160b1204050f030324030a032001061a0c0f0607050d0c09080d21020c1b04 67
    0x703514050f80301c65400002c501c40652008103c5d001d03a00d00311000f528054001600c10403030310000586030f602c1802d0404600e451285d03003009020b0ba120704000241c413a000d000d090044030b030740c3c400342c0f00c0d0001078101450a8035080b500e03091884600b80241101c51419078401c0022078a20001c40f440c0c00b03030949e103040f1140c1440d0b2055010500b40003940d05241428058200454845034140400908089415486000e03030780c920703d812042580040e0422200300400380c4965034003070450b40c80f4900b035240203022038604003c40100401202500e152410000743d05480591300d91112901d82c183c074410382510300036403074080308103648071600003c0c00d01001c42101c2110b201c844041d0740c0d9040c0b4059a9182c9184140542040d0740010208065954011f0070345403c2c2c20400b2002c1448a0040401c80750f5619641010341140100310603901c140d03400c5061104c10f406500303901c0380240b4129602300c040380200000f509843d0010b440655050f04480008a40c0450007400042c2d12007003131184018a10707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 131616070 1250 131614820 131614831
    0x6060a0311013903030506190308090a0509010e01060f05040803030612032203020a060504031a1b0a03021308010b0d15023001090216061806051608011a09190e 70
    0x881d1483c08206050341801080c0d444402a03410100c01070b400700303442c140d030001440090311085001c42c3e601000d503905a207a0000749401440c0110310750716144004030190f001e100340004514014080301d442c601600582e07003100d001801440c110b0392284103202c0396080c0958480c09074041040082c0c1c1a01e06204030b40c02100241c0d41101c0304900394414403000702c031340f60014010b00005100400004d280c40c0c014000c00200c04203445003d4481c80c04807490740a50710542c0407120004a45680aa030b41a4042d141da409014100c4080b00c0d59454480e003259030480c1d42030340290604040c00c010940b001d084001c0350101000c01843e140c141400781c0a2444824134500340302d000001c8506444890306a11805095406411440c2c0320028448003540800d4410040c00385486845008044c0260324100b210140c10820038407031880c1c01854403980c00c1100342c113100820211800490300d00c00c1180d000340d081040b901e24628041c05401003082d0301c545ea440003241d40854040201d00e0450148201c0d0007103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 131617320 1250 131616070 131616167
    0x106050d1b0801110c10020c060402010c060902040204180c09060206160e090a1401080c0603040f030516060606020d0c05070e1b121b090d03051e0c06010302010206060a031101 77
    0x1c50f80309803010301b811a500c58403184d0342d005202c1c000700c101010a045402582c24209861180d00900c0c141e0007802c0c4011000e903220740f000c1800070f1141040e9010904c5102d06c602c080148580c40c107400e6071641181d002d0100107a01880000382c1d565420f50103100c000e0000c1c2001d12204882c0f000040b0001e400700c0d00d00c607207545c4810283c812580010409405402c2d07100c054244006030b10007095180c00b0082c006081c0c0002c0e01d01190230701d4060720032544020340382c400802e00755101d820000017600c1d5611883c001031040007024460746105501d000505035104000d44a00d40c03030603a91012800000c4c20307400e440180c400440b13100d00c2e6840c1c02400c2983ca10303034810903245010780361070b22022080001c0d00c0c89a0400c001e1001140d0381e60140c12000c40e03041c28469103800b507241444502c588000411031186d140041c042030300210024220f13040340d200344d013110142c1e5942420700c00c81c080c840c03000510b4001e1141d0307031039140d40c010000003c01c803800c0c40c0b2820811185c4051039214030400003141904 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 131618570 1250 131617320 131617327
    0x402011404080a080409050106050a0509010e04090501020703030b03060c09031207110909010507020c0f0f010809070b07050a140102120411010c02060304061a0a08070302010522150206090106050d1b080111 90
    0x6001082c01f0303481c018416405c04a00300901103001401b50300c107201c0480d0421200c040c03105007590b16603000a16154018000315201c41540c54090010031078441024468411000010f92410412040702d0350004054060a2800381142161120340c00908089800026910030b030300207078644184c0c00d03104100e008000b00e01070415a0003c0d05141d84041c075940507566141d0f412199031100918410151028038014903159500b03220380342440d140e07422451120078005100010f10800058440309580200340c0500034a06010045080f0310031650f542d03148200e8a00010046005020b52a2070000181800c1d5013020580d800920540e2041f1021503d41d079580044007080109400007818503902034601c64801403c0081c013603511103043c400203040000004d400250b0307081d165280c900135185203109a141d1911441c00220307160490040c0d10051065000056003280140540421208040c0400c81400ea43c2e40b10030b11485104818520b881a103000b0000e1415003d10038500c000c294006e41c140ca = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 131619820 1250 131618570 131618579
    0x904020f2a060408090603090f0d020106080c0402040e01030f0f17071a0709090f110f121b0406080a140a0b030c010306210f1403040306050606070b0402011404080a0804 74
    0x20700c55004039404100d90240e0b00b08800650f8100445404220854481e80c80b03039901d10145242040c0840c40e00390500031070b44041c07242d0ba0150080c0c0159542101502c0e50360004c07509101c00ca00442c0324030440e40b00c4c020010000300702864034912001d801201c1614505016449095262a12002043d4035580002d2420240b002000074000c1075400d50141c0720782030800241c0100365140c54083d00000541e141c01894008080ba4002c0e900c1000d4540e1090322100400403207543c2e80c000345130b01e038545001d59000a503004424041003a103440c00c1504c160400d070a1800c12905450020140000143d6841c107100010340c054a00a01c43d0000c0f0201080301207034401030500740f041d0204820705241c04c050092084694004e60f0344a9003003903c1c0841c0305a42c0300c0c04d20399088142b00c1030242901789060071a040390365002c0014030590707029060a02c015164503041c0102031051400c09071810f00c0c203001080041d0310800405541e2281c45a41d1402d003a281c015646c10709521420840e4503400c0060b0400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 131621070 1250 131619820 131619877
    0x50118060902190f020c0310051506031605090105040e0a0905120a020303221b06020618190204060f0e01080c0102161a120a02070303060e0712020904020f 68
    0x40240c100c00701c055040031100004100200310107656502071240080d02c080c2c03124400c200514805030000c048803161035040001e0350051009403003004401c54014144000c80c20000c0c1224094034007000e2164071070349050401c40b01d0750010a05281004800c000c0094141518034003680035044000300050810294a861880c110302407031398511100702030200308640350f00070040d281c0c000311441d4844203020119840100c1d00c3c44402d00100f045000c00d038200200b8160f0894001a140301d6000c542c00c540701c5000c0760040c034120f0660704071903a00400303402c51203d01404c114088544040d001046058a6107103200030804590800000300e5021801040880810411801500001e0010388036110019400c08c1e85240390707010b03e180001e80100d000000300001d804482020107481c4880c041810480c44410180d03100d006e06a001174100000451a5101c04410601450a549668030604400c84109001e03420000d903180c3c1c019400e108645210076904001d0505111102000311040794045005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 131622320 1250 131621070 131621081
    0xa0e030d0806060d02030405030705060705030f130c06051305120d17061516060c21050906070f02030408030f090901080111070f080c070f0f06030b090424050118 71
    0x204100241e800510501d038498000310b421034010b880000d40e403030b501d60504a107107200d03000000f0702c248038a02c1006150b03a40580a58014406074800003810b4555000c24488409044809020800101c40401a9030b00941c01454516010140882402d0f82e8400141c542c01c480c16000d1656009100d4600e000e0303901108819000c00d60402d240301c10300302040030841c014015400650386420010b5075000c41052500d041c110300e54000014422483c46180c000c2c110000042c4c10410303038841c10007000350503080f409154820310380b81004217002d641d010320860b103c940c010161010f44c0010400812000790500051017001100c003449035944184500b84a80108140e03c00f9007640d00d0304620b4507004490000f210607050b000070f00790011460600780400c0034401e0301c002e80c000348514000010403e8030840606d0171034814821040000e40e864001748c041d10301428401e0391102c101000a00001c01100d026006001248110150028001c4194007102d03020703003018418040d19800b81007070b08058044c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 131623570 1250 131622320 131622343
    0x30a031415010804080f030114010908010203040f0b0c07020d111005130308090105040503010c120f0b031207082110090c05090f06130306090b010807050d03050a0e04020a0e03 77
    0xd2024508190308034000301c6001861410004024042000e121070482074550343d040c400001c95480d40d603047da00e070000745005d0f4140c3c08901908400103103031b181842507030711460700102c0b4214103203683d551310003403040300500c40070300943e00340401c10168840e01820440103108101c17170800803010808000c18030310742080040c00c10004020000c2910007041c1e42c4c10459502c110801e0b100c0c0d81800050300d0f103016a40029825600e0240c5908650b58000e02080440500750003c22180130819001000d440c2103202d05901130740b005041a8800c0d03210b10003088054040d0405608000c501c00a641110381e06004031174486c0ba410083c401c803901e500413014004e01d10306c42c0070000310503600030281450089008507442a0200c80c02803116445400c1140c10b003088000c10100440d44a01c0c052000b0032201c04191100c6001000200304410005000d1040c0c0304000d00d0310026502950f81211258040710700070040001600400c1c425407580d0020305010900c1d505c400151241c8402031601e05000c0902 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 131624820 1250 131623570 131623601
    0xb060304080a121b0f1403090307030806060906070f03080f100905070216091d010b01021207030504050315161403013011030f01050705090d110a08030a03 68
    0x14400007a41e00d07022100300020754102042d544190307a040200800c691111400c03180c1a52030150b000f55405000c000c15100340c0d448900b62000c40b007030000e040b40000ca0f85007610342e00c01c0120b0801702e4090b00d02507521400040c4800c0c0707082c2c031000100704141c11a840817511032441c42d80e103504260300000030f2540626000a41909840d01000c1c400b0404040d1207110348813560750020851851080c4070087c003140d00c240508013136a644e580c0c0c1c040180000240a80807000d41801d419154006005540480074140d005005d91080c0c12a9469964402c00c2e0403024000208000216900d00340b01154000d07101d00380e07900b05407402101052444030b09035110020030804407401204124480709482c1540d800e85555800c802d01800c04d5404110a0008110580040440c640400440300089451401c0540589000580c07081030203082e14410340380e100100c3e500344110b11403400c01000c14008180207007880d0b401400c40c8004520020300a030803141040d0000209841c0c100d806025400450303001c1d95 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 131626070 1250 131624820 131624827
    0x209030102040f092a020615030c0406030305090f010905030a06051012030306091803090e0912120604060512070b2a010b120f071806080313030501050a0501050d24090804090b06 78
    0x1700a4032140024500200c0700b403c00c0301411b00352030400c400c585028020b0020440300d40c9a04014203a03030081c28000e0701c2050413601201e015441003082c40115080038000b801c03011400e5581078080d040003420344032158115000080d00402041c5c0d107500d89402a00e00081050030040701e58103440610070107145030f509a0278114002a404081c0300200c4030300861903000d039113512000d5410071070b071030380100380c0c0b8580452500c1c281222400034500804080710300708111a070307450510120491a90385020f058000318410400300f95050000c1444100d1610503200180c0b00400000401d800c4002d0400c80d80e5541c6407486040c248030b06021046100c801c0201488400720201e60307375a005501a41d4076003003284002a0407400290004000340402c401543c0d19560360442c038603d078103420310003610b245d82001d010900e010b869108d00d078141c841c09080043c1440d190345895000c0a10803200100c1440d045291000e94582e0f031003505443c0d441001015503072131a00c410300c030a031002d48403680d00c5a141013 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 131627320 1250 131626070 131626151
    0x30d0306151b03080403020f0d090f0509040b070f030f02030c03041109060607110409170703031104060c080703020c090a09050f0705061b010b060412050d090b0d0209030102040f09 79
    0x19039152402e03941071814035143da8a51070224284441d08030901c03410701c02c070b81b1b152038055003100c00101550040040b40c12100d0b900d00c1001810318054901a103040c100340c0100e00868416507040d0b650b440642408030345000c0c0c042201089900884008035519008000e120030080d1092207880312001c1240c502019003440c0c000a220761141200c020144900400000d02c0c940300e03600080519500204000c05401c0380c41e0400300700d139014a0041300041d181048a98a019500c0140e4003503403090380c0d138042600400c2d620b10000c0da100c040c007582944076115410502d651520340043c490601c0c4000850120000d01d402850f220742c94401c480c807500300c6801449186c450009032420110018003000300342c50500d45503801490140d80c40354015800040100c0c9002040d01d00081541c841d0003201d20b01d004861040352602da1602880030801d40c01c22549501d052a03401515104900174001880c2c1540e0303400d804403600302d6911103080e040d116100015159440b86a89186495443e908120a5541d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 131628570 1250 131627320 131627357
    0xa1a060102010e0c2403040b070813030e0105070302030d0e0115060e060d05060a1502010207020f09041a18010515033f040e090a0204110c0307060c0509030d030615 72
    0x50b90b0038035014660f41c00d400c0000d20705528a0221070294044034691b2414642405800e400d003c503200d1011400c40404500c50051000d00e50b1801030309030740c0d0302c41002e022200454490740041c3e400e50840c4820301144184160341d21031680d0318400c2100014104016900752450510168418402c0c01543e04100c840380c2ca600088407010302c168140050150381d1000003800c4005c03990400483e000140d1100006035405500a029442c003c640780600b40c2030002c2000702d43c2d60101c2c2d006020345011046500002404011541c0000c1040d051240c04072807150301034219001210080403000d0b8030110000681000e2240041e0740481000110b440321054812281c0c10f0043c620b10351800c0d41c94001e04580709444c0301980c3c0035018190b408200b82c2031800509035982c500740c01c1a0312452803d01c441103802c080d102110350000701100a1401c0040548942008200b08034100c414042c0030402c41d203959405100c484288902c6803000200e442c04e013101031903014074400022060001d9500c000051400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 131629820 1250 131628570 131628583
    0x7090b0a0e0f150703080402211504030207080a0302100c051204170403061d070b09031f0b0303070f060b0103050105060f090f06160203011a0109260a1a060102010e 72
    0x28242c400c00c01c03030b00b10308000c80c01103103204540010444001c50424100356102503028000d600883e01c0030308800c40000344012189014048a4159100354000300045907680420b80d4040d029006075400c0664524500e410f10480a004500507000305041c44050110f901c1020440c0121b49452130800881220a807003146018102411900440800c0c0089410010481c0d010b1b55011005110700d1040341518403e001994008641c41d010300e0034042090301d0840241c0d40d203500000c0041c6000a04504610074402c1c4d806103a1081c4d60b169441042e490300c0c100001d14401d84240c00b0b11b41010003600300601180c142c40481e5041608000041010342c5e0307014184c3c4c50410650504507603c900d440000f401880d44407602c00c2c3c00544c04180f031b1500049146050642c103000b50000c4c0102e243c00e0380800110180740b94281c0c041007105100f44100304880d03861250b010782c0e408048122001d010071a80c9050721903c1c0481d80d04000c8000c40c1790b0125900c1c4510742014082c0000e00111415040741511201c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 131631070 1250 131629820 131629847
    0x110316140136060204090c020d140f0904060e090c19060e01140d0606020f010f09020d0605101806060e01051303060c0c02040906020c0c010503010b030c160204050f07090b0a 76
    0x180240860044000d030440780c8800c0c3d81c4010700719030726691a585900546408110792015008221a1100c01400354410074204004078061529200e1004000c1c074041d0010340c3c01c0340d000342e5100d0000c1800050306202c40e00456961004140e03035011842040103001c1c001e01403106012007448204911030304161003240400b401d00705150340c075001c25089900c078020500700200313407070510300300003180d035000b0580c45a004400b80080c01100d00f0560403c040d981c29070720082d000f0182020031400b1403804d0f808980c010340c030003111003103031556603070080040700e41080d0060002d50f44410410136590131005038070940b0310078200325040c0301c0840034007510385203248009440070f501c40d41c0c0006a5880b812481a84540c028410462864a410000300075002503080700014451178405d009290301072010b40b41200c101046803899942d946228a031170740c1002c99403800d0011400a4400143e42d14028107100748200300c0e07015101e01c1d060000070f00c4400607601880c0210420043c003116030380e10103000c00d10803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 131632320 1250 131631070 131631131
    0x5100b04030b01120f0605040c03020420090d14071815030308040f06060b0c01050108060a020702030a1b0b0c0a11061305040509030c0102070507090f0c050a0305071103161401 77
    0x1c20407820302070401c400042000305030790714040c108001c00009e00c0c404001d5034000e6404010480070b407600310500ca00310084107900e00f44107012002c080d213080300458641c1d5104510140385211440522850010241c100c1024012140b10a0848000d02d00c00c9107107500c440c891411403d491034801404110700548007610b01e0700d07000740c03110901903a500004c00070b0802c02811a03030380e00580c640500070300c2c0030b000340d5200d401414007141c80410305009494980380c0080c040e0100190a80e51914800c407005100d94242c00202c100080000036a000350000c0c00700c140143c1160070320f510b04101d141c0e25081c10f0510501081c401d40c03000300307801910481620004d9a0000303041d110922914514050f41c1b038080119030000800c02c0070001c0108510085030200380c0f091121820140b4041c003030f80c983c00c400d000014410302c111401588a5002030390072243c54106203210100c218111815684000e21410703500342200c240320200444010000207008841008001c402298821010042203200044104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 131633570 1250 131632320 131632349
    0x80306010e0316060c38102606070305041106070305040801020d060305160e070819060303030b0307091b051e0a0f0e2e03020403020a0905100b04030b01 67
    0x6510200f12003814021071402d0211100e5444400070004040c1800c201d0300c008285c052183c40354207204100010034400c1d80d22403c0321003d9810840e000d00000c04000c400c840c07580000603a1420144041619014040c4c6885910466040d16113850006043c0d01c04052805007008080346400c060b0401100782280c0640d9103200030709046546029503000020036510002c0c540e940801c10ba4000c0c01120f11820640e0640d01162440e1071021400303124040360f00800400185009100e05581540080405849050f8107041022042211041e401c1203000c256542500030aa1604101500c001c20a0740030070f006000c940002441c01008400000081c410085075816154001801851140d10501d50458554140c1c00004115071203640c0c2001c04240e80d28407c4810781040301213001c1103080d050a081d401c0700f1428040c00c14450b000050401c143c4e0a00c00031005070380e08003c400c02010800790110341402d00307421403900e82d1450760208140b100100310400008681c110000c0c1110040c1002844 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 131634820 1250 131633570 131633597
    0x609120c120d0501031101110303070c0c080d08040605060d0c0e10050603040b040209070e100c051f06141008040609021909020309010b0603150d051507020f010b04050408030601 78
    0x50590003401d145a40307000070410203035440035039100307a0489000380307822900785201070010364120400d008031a085402c104001600c9a0040c0315110707455115001403030b011503580e05a14144010010b09c4400148443d0620050050602540780c00c11000c96003064541c2d0306a40b00180c81703143d031181d08151059280003404c041d14034900c1200510000c0c02c2d150f513a2a0a10b80584104c0086504a108240c2c050114031094840c0b03249582207400584860b815200710017054408e00091041226507108644080c0040042c4040500710b4194044001ca946420300d00d00000001101c00382c24040c191200d000c442e01a4003548040d0802d403c10b20004000d00309002007003040000491700d00807040403072400915180310f41e000318451500f00000b000a41d10700170070082144001e452080800040d03841da0051481d1400d11000c10701e10580441c3d6209285029610295504036810030141c1c000540356403030b0034428010051603040071141040b66180a40d034405003030001814149c1000445808500e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 131636070 1250 131634820 131634823
    0x9060909050c1b0a1202010b181519030c080604120513050a1203080703090206030612011b17100f090f090512030a060503011509090203030403060c0c02120609120c 72
    0x20154101c2c0032152071090f804400c3c090780e40d44000002c54004011100c048107403072041c0301c0c0013080040105034084800d810404816504405040700c00e01450f048910750542e66010a8011680c0d108104403507518614102aa1045003d03070140d0003540003002000005014072251803041c104c18240a51a20070078951121500300c01d07001103070041e1002101107603100c680440a10725a209645001503540c54000403025a5051000250000c4050000c11a10302d0300503030041c10406150b00014801684003e80e0076190240880103000ca483c9050304c1001400b4101d40c01e50007603841d41c590031943d140014940200c49240302d03001801d90f4914100614000d642c200403440750f002401c5401c1590038003c20111544180c490a101c2c520f040000a0300d42418003d0704070200c6844440f0114500d41301d40b010250410500032645404204401b0001455a100d00c1103401e4041d40c520a4900e07592040c0140b1034010103101040344c1c40982000921840041c40202035404016610b40710310f8800740c0d65 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 131637320 1250 131636070 131636077
    0x2412050a08031f0b0d050a0c0e040b030102090604150306080a05060106030506010903050a0c06021c080606070615060e03010b040e06041203110f0910080f070c050a1703061009060909050c 82
    0x3c1c207256500c0c03280000d148502e02d0280985080f010020801038071407402c02c404460210342e1040c0816040340000401d890158807000780743c04040e0001d458030718001300140055010ba048514803103d0304161003140740d031500c80d44014081c3d0b1801004015129250300c0c2c1d807400144180300030103880300002081039211f46100802940e1000848501500d24074210b8018845401484014814115040e84901a02109181080b00303500c030516030b82c0761042440714650000c0419180705459603c5a040c0c980341c4203038000104a143d50303a0105074041d000b01400d44038141000b070b101d1401c204c0490b01000c000320703070a5041544454560b0481c94014801e071b02a1a10a082c81d81100300400c0300c115000d0020014030f40800c0480320b841340d42038400c5c4107032000c10017910300e00c00382c80e09100001c42003402042c0c1080041e000f01c08940452803603540700c4039030b0b001c000003440e0440d00100a00c030660400101c07900d0002d1171404e00310a0b00d070034040018003e40c1c1e14410584025284c4c004101c4000082046 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 131638570 1250 131637320 131637361
    0x30112030c020607110312030601050f0d0908040e04121409061b0123010506070507050907110115062c010f1710050108150604050f0111012412050a0803 67
    0x1001d0b00d0f1400c9003803480c0e042004540c0309019018407072500326060509011227201d84416151705040c1500c0303583c40c100e190000f0a0300c04516650300d09060125011034041c000914040e815204289414540390314030b0f142c1e03514000140284060120141d00740a016207d14020035181d99031101c400e41c2050804503c00881d103034543d40707001c40001001d0700d107508401040c01c0490f089842c03a41c0e0391041c80720030722401d000500302d500800d4040c495450300e00a940d4200211346003c0c1010034a24134001d08403030442e00704050305010142c042241e2a0403400401981c040c020500c070100c0c81e03151420504101101300725040080001c0f1180b00d00e4020f180700d40a041c00506101e0151610318102c502c445054081c4501044041d40001d10640340380390200040d94025000790301f070030324000901080503215007555051002c1c1c400304a00d120400d12554103100704602346820042c005800c030400b0f01c0310b03d401070340000c56020512800315900180140003180d0040740c8550f20307900c50190146181641d5903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 131639820 1250 131638570 131638579
    0x20c060f0702220c09050603090304092003090106050a090e07260303010f03030806120a080304060603150504060b0117060f0402040305060c0a1d010206060111070506070507170a08030112030c02 85
    0x70105145956413202d01402581e0f1201a503050722501040352602085600c400b50b64020001442034032200d420030306500e4600790901540c02801181c096054008440d1005241c0d5070748004c001519051110100420729440d0030002103000b46034860b202c958500030803000c209075400c004400300c05141d41350008011001a0f07900e958490a1701039142c529071100b40c0c0094500ca012030f5441c40c148806415110001c0000e0817240d40550f42e51805803c0107105452196407030000101051071130700d003070340036942403980090b1602d09881e01004071041104490b0400004005a0181194585005822203800c0321244c0380d01f043c43d40007a0181c422034100a110f800390b0780c28403540040b82d6003d80186400c684070159040b54402440c0c00b007460781c640860041c4c0c001c40100d0803550190914409290030101a560215180c01c08105550b0001d08203e40c564460001001401840608075000c03100d41d20180038007000320784a04109020600074120301c260070501540405004201d241e41c0d0319806007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 131641070 1250 131639820 131639869
    0x140304051305011401140403120c06050a050f09070602121c020c070611010209100302030703060e0106050c15092a030a0b011404090305030a09050c090406020c0d020c060f0702 77
    0xc24400540400c1c450040f80d9901d580a000b85507001c0c070f40f400780591310f210f0705604051954841403140c0b12400c074140e0601c42c404c030ac11804070701c29015047c4074030140d05022a4070708003800362030600c1030010300c4510244c00400090215990102d0461588003100194036240c1c1d00c0b41d40000071032045004403500c92440000c2c44245204041660300448046413540d2090451041178182070b8400c091304d4944c451440c404449142d4001e602441d040240303480c00107200c90304d03100b40541038036007a084071002c510049190508004100412504030030940409235441c00c24101840d0b0b200c4001039500c4503100b440440403588803030340e0071844251030024100c41e4603e02d1814081100d5100307000b20200d0b82d24002d94031f000c40c1014021042c40c61b504d59540c5146035121840000281500d0204803000e001340c2050000316591085000e01550041d01e0043c2e9852a580e0014902051051801c1c29074000d00c41180303555071400c00b41c400c401090b00002d0b6646286100080300f40c120b0325002180c4c1501c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 131642320 1250 131641070 131641099
    0xf020c030109030906180b0409050406020c060103050f010b010203160803060d08120a0606050c0c04180b0c030a14070e01080c0d0c0c0605071803080c030903030c0309031c0c14030405 80
    0x40c4d80801c884240d120000000c601d1040c44ca0030240c03500454a00c03900400c000c210000465100a90203800b480380142490940d25034107060100c01c0c0e000f89d94580c0100d40440d02140288104040d081090000f1860030b03007400e402c0b0b0064085802d01603d460008800181c1c0754a0700800000d64039800a0256650056410600c46a240540744000c031075261180c0401e29901078402c642c0c1001417140201281c00c4030008000141000031052600d000035000c8042c00950007403580c43c01030040d00c031102d807071f841c060040504407004c2d00158000501c90f842844001038004c0c2d421900d1801c207103000740542d502c1036140e2034103200384802c850f419450006c2090301340b81d1008034856024456003042c1312a40350800300b220510442814445000e80702c1404100062551008000204103441641e0510000c800001e040d5040031030100140c1e00b000850304030918091202d1020404a00307080390340d24480c800c00910080403820010190126a09401140c280c1002518000e01004088030740e5403250 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 131643570 1250 131642320 131642327
    0xd02130b0d0203030703270b18150a200a021804030c020916020708070f060302070515010b0403150c08040209040c0302130606080a05010305120703050f030a1b020f0c010f020c03010903 81
    0x110604034005400e00047c0e09401400c1010303001203070a500c00c003505014456905240d2500c203044080c0d0310100840005481c0c00021018081103110740e00c1c0c401162400807400a060100f40802c1c80b0a03801c9034040c0c40050740c41c03006108001c5101400c0c241c00d940d580c68141ca10044415020f58402c0c0c0384010052510a1403031913103001900d56080e070345d0f0150b950312a203039110312900178803000c0046030fa0705001c0c241c80b0b5405448101d0050b400c94081c8203010f0680302c5101c3c800c2e0405465a40000380510a00800c00c40c5072400ca41440810030000c44090350040a540300070f00000d201c0d13027440b404a0709021403e80d049000d981c00411441d0000a01440480248107501c0384a010902410000704010914440c05040b650450041c00440005840342601a44000002c0b030500605006142c40070703502c1006188188241f40001450301e040c0f03a10280d0b4090300e50740044c115132095000000500011a00281c0301201703007820340a0084441c41039041c012001c0010307425619011001c001e1551 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 131644820 1250 131643570 131643587
    0xc0c120403051b01081308191806050703080112020f0916021005010f171f02070204050105040b0a090c02010207140d0807020a0b011401110a0605010e060d02130b0d0203030703 77
    0x3040c4111120703103100c2000c030f03641e01e00080501800300d08481c0000d04402e03000c0a101983c1403250041c14900040d080d0a4045c0601080e03601c0300150081c5251201d4000044007100035088a0604906103101d0750307002001c0e450305029814001700300310308540864541d000d035139225100042002c5020318000548800c5d80c81148800e50045c81520340381d24200a591040c14141e44021580c00c440c1403c03c000030031030400c00003041e0168801c0c02d000e1101014a03007c004030791682c00c00d026035141d00d540100030079204117810103445207240c103500e500243e8a40005108940b44c00c0000700b40f0b000b08141c180e009024010003e0282c2102c1d0302104602c2001041103001c640c03241d00d802c0e12980b26003600302c0c0e4403155401c0003485e0b4183c05005021096a28100c0c07004007505260411203c0c010310300083c14441d1040c03040324840d48820042c000d01d01582c614a91190040d610007002c2000c0d1b800103600c104100c17010b0903056664803c1d407401620384499036002c90b030b0090304481d510590b07841d00811824 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 131646070 1250 131644820 131644823
    0x10f0c03051302060d0e070503060702061b0f07030309020325080d05120f0604110a020f01060e060604090f060302060f041a07020a0306051005030709060501020601050609180c0c120403 81
    0x2881d10740003a90810406800c0000c0300d40290096080c0444140c1c0c1c51700a03e20300303182d41c00a10540d01e0006856908100f9035203d400154050010b605107001c03014004148031007600c01c6036009101007403098000009a86000c2e40500e00031452850074000710341007100c0341c00d142c2410341c02e0013601012110440e000e0000c42d041c0302c2c01c448589034211012103050007151400c0c00c5017074500c408102040c3c00a41c1d03250308510004c000003800c0c2c0801a0b4092142d000342c184002680103600d0600460000b8402c0340300602d101041c0030058588100050410b100b1409540d4a075075680d0399600403203a0903803164001d954007070f006035611a101e880030301040e00304d44154401c140c81c0004d861101981c00c000d80d10901e82c054100c24901d411540c9013006841e00a02c10034504050352000030306076404012140c0105144000003d85034105000281400c4050300018003c02007040140b07020307100c4203812100d114150040070120380f01e5000500c9c03c0d01c207101c00b182083c49101c0791003d140c1d00c00070051045a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 131647320 1250 131646070 131646077
    0x10f0c060e0102270d08130e042307240201061511070602071a03060d02130203071b050d110703060c05091c0203100e0f06040b041a0f070c080408010f0c 67
    0x10301807038458019142820b52140d003044005c01d0310b500203640b040c007078081031502e40c01141c41d0946900d8000341c41c40080700c040d0fa44e58128552400b640c10308a202e02240d0b2814070140010031b04040103400203c078202c01d41c0301a000b00c0080b540c1050300c01c0d0300000282500e0120341c90301418179100100741e01110f610007541c50151507400101c1c2400060282c0888d41404d2040300200303c0d443c503152882d00014040f0350003950001403c40166561002c0d06143c2e101d2050042c0c0300d09156500403e04040f24504410001c541ea11070b1001c90070004100d10158014035001390301658010000e410003420b6400200000e003840c1260700d1842c3c008000c1c1c250b401040da00e0101500c20b4034030030030708014000e801175010b42101000406540c0c103600b00c0885142540304956224462400c4140781010440d401e0f1000708000c414801044240401c245083c08a0200c400c1b941c00d180980b80c0041c0c07000341009040c0328241800b030f0100895141070381c009001980080000f89540075003d4040c00f0b00700001b4001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 131648570 1250 131647320 131647357
    0x50108030d111204020d060905031b0115030b0a020c0a020d0b010e0604020a05160203190f1e020a0e1e070201020a08060102071d100f2601060e0402010f0c060e0102 72
    0x1c501c1c0c040140c1c1c4090380040704580340f503100d6400f8000030b29114817003070394070544030408500440c00400007018070708607110581c0181d00d186c2e4202070850313a8180a004444030301c12400c2000c034a0840c600c1c0c0d004850241c1c01a511688501140d20b0a18207510007900131203803042c0f450030f0000c0c0c16207d0b0704079855a100240380e07686540401049108000080c00492000e00050209a0420881061152001d811541d60402c0a83c00f41c1d58a803003418200e0310f441c04c11007541d00b0803010310b61080040012900300d0152a8240c0d0014130b80d200c05014106180481d1000188510b5000c007200d03200d03651421145a66042c483e2000f8080d500202002e0042000316000ca4180e5100150300000c03100e8404054040c11002c4501c0101d00c3c102401410a40e42c0610300440e400702d0790000680108060b55520141c41c03d1302031a44400c42d00f01508030a180d2400302d0130000507500064040e4006d90901e030510500e4602201510351304e43c0304070050503a47c80c00603a480789180543c014031480c0a50300d6040c01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 131649820 1250 131648570 131648591
    0x415050a0b0a0e0307051c060f0f270803010314030f120103050c0a18020a050903030c0c01020610050d0305090105210114060715050612011802010801091b0e01020c0301050108030d 79
    0x85c1c0b1403140c410030760044600781459409072004002c0030a01446400c020406032142d00d070740010744620305410044513030380700842c00b031840070f20184074451040c00d45015680c5240c0e444d080e145010520018158008040604074010300500448330914101e08246841d1240349803215210b0000340400c640c14807074000c06514a180a644900450f001074151100032400306807030354080c1d00814242411b00c44180000308942c2d5050010b0884070744024014009036030107034002464614040c101402c0d2581e00042409143c8070b140c4083c00300c40c1c260074000e940d80100390040b20107204c8d4002045010035003450154803a942c00102a0484400a05200481000001700002c5100c0d289009000c00348070b0100800d2401d150304256486000140040d5900110000301801d49481009001040ca5080703031182c210f41c6c0283d0490b0141502e20b4040050b0880d071f0032001d9100030310b04441800d00c201c0084006c140da1080010f041080d601034024865545d41d006050703625007200c8d10720300007241803280030340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 131651070 1250 131649820 131649823
    0x3080306090906040f032609031809090307020d031b0b07090602030a170603071703030f010603060302010e0918030d060312050a0f050703120e061605030105030a020415050a0b0a0e03 80
    0x50007980c02c0070b17008181d4844c65030700340c035000c6c08406e10306085280c07130845400040403181c030607100b10780120165a441300300580148007605492403881c0f0486e07401042c00207070000001501d20071079040c1c4802c0000c101e42e0809072501003030041d84c5c0c00d8601c1c0229014081203404200c40303009400326191165002d45550040c1d850780aa04c2900d00084c030030a07848480284103440c82500a613000d002e950807952034800c0c080050102002003070b44d9034000401e214200640e1515140100064a0b080087c4c606540c002000520003850451080029902080c0c40350702201482019800341d00499503070b14040c0c0e143d00007402c45880181c1e40c00d05039619460400380220201c6041c044107075030b01c0003103400030304098070280c0207840c040e0104410b09010310144580307441001c1c1c1010304080180214a00241714508880c1c01e400c03100e08004c01400100215180064405a010341c1114089002c611000c0642064010744d0300c10365000030701d1840020812a040018605200701d680e429441c0d03d201e2081c903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 131652320 1250 131651070 131651083
    0x50702100503070c150b09041208060f0a060e12100e060604050402060304030507080c01020d090227060618030d05040302090a02040b030f0631060f05030705040c110601030803060909 80
    0x40204998070f030f04c280011010381002045c1c0c80070720000038103142c03240080740e1300c0c0c8000c4404507160700c401c1501c15030207a048501c40754045c00888604e00b91802e0600891035800740c51040f00c092100140c118843e942d0361081010703806004004070380c03040041c040000b0182aa080c40b51625004a8000c204582028055584200d80203030a079490b6843e0303564201e0743d960000c8000d4600040500020040300d10a00042003d548608408581c0800900402a0607084c50300c1d00350114400403a04d01c00304128000259220100702c0c0c100fa1030702c1c548100026641d8074020344580c035010300a51510956005800b406c00e8a00a8800c02d03700da0703846101404030b1140b8055206902814000144020f69a440b1241e0002010b045055070310b03500728030030281c102094a044d44680300301c146c3d814540500d1085100a00d03810a03a82c401f146080f010a03282d04203409101e008984440d112103543d0b01030054401c03200c0b0303c41d040b14815a0340c1e08010340541c0042c4c84262040240c0400b0458050f00040d24 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 131653570 1250 131652320 131652331
    0x30a03200703080c0403060203010308030609010b09130b0d05070e0a05010b04030c050904080409050f0108060c092803081c0f0c051611100e040605010c030c03030c030b060307050702100503 83
    0x4501d04101074809039502400201001024181080084001141c0c0d001443c002c42c0304e080301944a0500070100052000140c101d2500480c042c0040c0d500c69a8158040341001040071000820701490303004104014032027800a00f00380b0800000085c0d040c0c525402c1449901032040411103a40c03a203051f00c41901c82c51001902980b4401018490b80c5803005009420074030070a01c0519141d0790740b803150190f034411a601d45590603040010032110405000d829404000041601e01c0d01c5292000a0b6448410f001808102c0341440504007030803003005800c40280d9000000320ba2201c40491002c00401c0c1d40000e90300042c4e0400c0404d450480e181d00490194801980301c4d80d051050b03c0505070404101c05005481d00c03c820410303d201500c4a003c100c5464402d90f4445000131000ea05003c01d8401e1039100904001e101142640880e6105c0340401c4100da152401141e05201d0640840280c480076200a9114100100303011003182c1000050958920956031340004018851b016262030004441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 131654676 1106 131653570 131653631
    0x603080306011727010902030f0a11040203160f020c10230702060417010f050112030809060c040519030803010609170607052712030a03 60
    0x282003a180b8212844620f5418030300c1802442c80d4604c5a1003000302c000c0070341010682800c0d000104c995400508440320603c08500050701c503080700c0401c4034407646240950005081500a8a20440c40c110f804c400350405400f0580c3c0410700703010f241c401c42c01a03501d4085241d031040c00100350b901040e500c01c040c2401e03010008510042503411101041000c4c829200144d840c00c04503030650352021b00c1c051441c03100c040640d0251003002c00004a11b4182400800c509100c01d00011195000e60381f42d105a0300e5882186031680000e4039048d0b58582d00708420320581c00d000091000041c1e1007101520035035641d03141c3c00b20790341080c0c2080d400941a0b035020842d46c10b4994080c00d4250450001d0320490034110700182c1644075500e8403112207101c4510011b24042c40c141205490500548200b584d103903494507680c2c49500540c0002c0210746071078105200100920100f1300c1c40412042c = true := by decide +kernel

theorem cover : BRFrame.Cov 131474820 131654676 := by
  have h0 := BRFrame.cov_init 131474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 131474820 ≤ n) (h2 : n < 131654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
