-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0249
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:43:45.913262+00:00
-- url     : https://prove2.me/submissions/136c8035-2654-43b0-8178-cac9b710c8bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 44604320 ≤ n < 44784177 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 44605570 1250 44604320 44604353
    0x1110d110c0406080109060e03340218010e01060201020f070609030201060815010e0604090206090f19030302010f05010e09120c0c0406090515090601170c0403080a02100b03070b0304 80
    0x1075908520140340007405445884d03000004a80d12040a001440b000c2e208078500300e03513140002d501d03020b1901c0140c0e6401c014140307298024040c0c0500c2c0008103030740e07104150305140d0041c40c102d00082110146541c0940c00e016502200c00464004607040f401482120002e241c03491074241400d050b541c03210003501c101e00045045548440c3c1c00503c0c0c000803c240101440c9a0404400a6052000340403a660000300100e00c907504184145016858003400c6800049081c1e840d102200100c402041e00001504a8030640741e0010f0740c00010306906601454840042280c18041640d8034011145108000d0b10005c4494220340c0b401800c00e0001c4005105002e00f80c001c0e01c2c40c803621000001c04a940aa0100c421543c41d481048055040000903006c41001211404014104000001c16110780b4107040300c1e01424010206211106000a450003554007000303081c3d81300070001000b900c0f00309802c2586040c5c1d0424100b1000e504c0e0201340071090302c00400c54141160f0322615641d00b030034004400e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 44606820 1250 44605570 44605573
    0x21e03060a03080d27170702090406091a010602031c0c0206012601020313030e01020111030c0c030c1212070801030201140a2706020c040501080309010c0203120c01060303080601110d11 81
    0x117108a44000000c2a0300450071070030052020040c02d414403214000c161448542422000c11800c00140d9a003c10150041d41058000400d8026443c005c054030038410a9052000b012800000e006a4004000c2c2078807048501000701c910880f00d00103003074a00380307404007000d070700120010f016103040320290800c0700d02c00c40c0b8100c200d0b105c4120000d0890380141c0d011540454210400405e25400048100e0b00e40003e2000300101441e10421030748600020704a20651030001460704c00c0d60404105445040b4004001e44c3c0d100201c862801220382d021104601c1c0345c1d002500099001d90060845504036a0180c440c264240c4020482d4041030317220ad001042408441444040c5180c008038684004204402c030752110617007800d102a10f0701803d429003d116070b0401005116908000c1705451504e002820301260ba40c07845d01c002410312945816607501d035807000c18a110f4070001500120212402512030301480d0f100ca03001101d0160b41501046050f40c000700111400740e00c1403a00c5501c2c24000b60 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 44608070 1250 44606820 44606831
    0x3090206040f0b0702120f060106030b0a1a0306090c03070e060d060b0c0f01060b0901020304290c0105010e06010804021c03050c03040b0301051306080d18030803040501021e03060a03080d 82
    0x8241c11500b451070b005110b2510300851070904604005c5540c49050076400020b19908620308070203a07a40405000d14410903440380302c0000981c03243c0c61500c02600c012000503a03240030940754820250021190184201007040124840e010050100ea0150302150383d170340c001c24010018000c0c0c80d80700500741d1130301c15524800001c1c008a141d0103400c0c0d0504040c098503580e5019007c503400e484c040d4100e0b410f0880304000350400f60380c000046800b159102c1988a111094401410300d10b0114202c0c0864070750030000b00c06031118819805203050b201d400082c7d0b01a61140f400440d07407200f08131390003501301184105c8c3c005807080c9521100a0a8401e103812407800003022109030854000750300081d5040d001100500c0b051410030740f01000b012855900b0400d103441d121515550f400c1070942101030262041405040c5842c2000c1c1c2e0001e10f4102c900150b40341030602e45a0b000b580555050000d08402604000e02c81d0604001c9a00902c0c005000804072825038461088a41c804a0454025559207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 44609320 1250 44608070 44608079
    0x1211060703030203040318050d0303150e01080f010e010506012705130f0b06070305190c061e0f0608070b1804051614030108100203090c04060b0409140c0a0309020604 73
    0x50004229403071003650b002d40c503030a00e454003500014215a8142c91081c04020a029036200c01b01e800711a07903014600442c5081003502022010060340e00a10880c1070103030004201c10070000361320842000428000c22040a501001600f00e42c0242e4049000401c6500c0c00b03415200d000c20342c028103031800c1d81d20200c26943c50000401106002040c0c03440c0b103840700c1c0d00c40c100300300c144039440d2000e40940c1c00c5494aa11954000c109101c1c110803d41c8001081541c201c461784581c000880103030b07024404114042e500700d05a2020060485030b69011070030000c1d41840326209000d280e00b20b5154200800c2880e0030811121100d40101d00300d018070b003024054035076566451303018490044050071509010101080001050004100004c1e207418900b007004010b040000140b01c00340e210105001a1280c071540b007185d007400c80d1040da150f80141400d8010650390383d41c20007002140c20481c4200145103c4480c1e6820100342280d07095a0034105100a62149004e6045203c01500c010140e514050b00c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 44610570 1250 44609320 44609329
    0x81204030305061302190809070b030405010f050603010207031706061e0306011106160305040c1205060f010501030b09060d0602120c0909061c1218060201150e04020306011211 77
    0x21201980007030380700d0081c8071441c01d1100c4042c80340c91088030158602445950603481209150741c0e03080c10480d82800040e242e110920501d000780200d44032042c0e41e0f0915041c094040c01d06500c40400652408010450529051089a901e294541c0342d41480c0101c1c00d58840b02098028812130708403004000c10007000d4015400f0a60000c1c0901c4255280e04004c0001000c0201e2034000070f0047e40a003041c0501000c000b21820f15501c514036020419588a02d82600c515032907902c0085010041b007114010804082622449441d07a0040c1c00d202341e0383ca00044081d6112100c10395005120740300441c0300f40c03c001e401c28900c2806003001500d044e5000315890f8004070100c0c0c030b0421448001c00c2d500010300e000300d000341e0050710498030303d032807003103403050f1806100e414030401030120a10440c28854103014a0101c9280709105207103001143d50307440041c0c00303001c11031f80c1001000c2c8024000f203131031100c03584180d0041ea005801041543e00304010011082c8005109403458400c69400b8512070760f5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 44611820 1250 44610570 44610607
    0x80703180305040801140408040306090501110a0c02040b01180b0c0a050717060a021e0c0c0a0906080f01020f0a110a05120405120a030e04090303020c060108060402210d050708 77
    0x80781d510a540ea80c5004c4901703003100c55807500b918145c20f440c02404080348031801500c090320b400001c0003d006003e4541715006044282480003a1712010500b8542c0d280c00145081880780241d8040c85a100351000460b001e68580020040080c2d4880d000e108100d00c50f03028000c181c10307140844500c0561600d07070034900205a40040302c0d50320954841405a241840120340012440b80103500f8004c070000c201249684004080b030011102081d15981080c04125076082c1d1007001c0c1188180b035446265840150656000b40c0c1c565203c2c02d5070000070070030140300b140c0d80703100262011414030303401ca101101e0400705091041c02d01e01c20026640c01240c4107100750005c04400c895065901c518213014003040d02c20510703d1301040d4000561400210350001e4030b0240d00c00048070001010b10b0141f43c00d42c0240a5550740c0040361240400110312203c000480038062802100d1004240700a190041b030f2803903142c04c032200c050708002544251030340101d010344001c0c0c0c41209400e061588001216140c940e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 44613070 1250 44611820 44611823
    0xf0e06160e031912110d030b030a060e0303070e011403070804030c06020c01020d0e0d0915170f0114030d09050d0311030d0518070b040302090402060c0703140c010e09040308070318 79
    0x251003c0079001c00040e81c021400e075101d2810f01460300841c4114554440c40c20100981c00d264a40c0203840b85550148528400e256208108000300d11a02001c079a0b44e07041110084081027060072003050030741c003501c48060300401c0d0703503601031441d540e40800701c640308805481181484074240104000507140d00203840b242c0c0700f1800060710f60305c558941d04181c46c8420302c4a0355a070011600205156409001041540d180303441e03441e00e000080104403136803100028050207803039a400510004240300c01c6a14101c83d500401e0908202c0c00408140c0c81c0c00d48071003020080b85000d04100954100384400d50741c058002d0400003d02550040c80904545c09200440c0302c99036514208041c030150715007140c4500c1c0e60305009101c1607003001c178114076070302c0b4030301004e481088050001011540d904040b507140d824240203440c2d02c156a0701d050490b810000c0d1000070a4019401c0726240703135100e4082c2801c0a00d00610020140d00e45440944900340007030a050304040d1180340c1d003101806645644501b01d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 44614320 1250 44613070 44613103
    0x3040501090506010f05011706030f0d0e1315030f02030a0204050f190501061d0f060406050703030b1504060c051507050a080c090108040314070203070e0a0f0e06160e03 74
    0x71249450a1410590140c1040e080c4081c0f2a50074085644d001c0c009032110841c0c160814603036115080000c0c502a80d55840d40400e10a0402480b4419031001541d00d6601064840d828480340c2d5055500698102c07880c541c8014641c0b6200300b000c14120468140c03158009020350717100c148550081815103e044510f0340c114000c010a00100d84040c2543c07010f030180c600700030003155062180c014003080d40c40000b0f06010841b514100481e45d2500c01c18001c07030a005100e1659150388850241503904508820350201e450f0400c284003d041c01c03516810000c0c1343c400c015142905001c0240c4004074800741c15134062180c600034100700310441c03896a000702600d071622501d59410080c000d014a0005120241d5504144580d80b91a600558429001035050a01c00c030584181d0048295901808030081d40c548a075400001d01005003074840d42c0154540e40c4240200c3d007420303652405450740c55900c1401caa0000d40000c0e0207200340d184c8004103546514200305e800c80c000700020700d0803d00d24103040f0365 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 44615570 1250 44614320 44614331
    0x7032301050102060708190c0e03010204261501030b071e0e130e06010b0a05070501050106050405011b050606040209040f0203010306020c07170705150408010f06030302060a060b07080a0306030803040501 89
    0x100c0da01040301e145c0c011820f24103842ea6240050b1710245129a41e54502890380d111900150713441c0c094000710802100c09002103480341d9561552072001c4449440031933000d4640c1d070465801000204203030000d41d0020b149400a42d103140c1d1600c001c1c10000b4000400c10070a034040703078a01c00488900c86070b00780c0c0300d40d900582c644816041000007803541c00100305491034080d00484107100411207070704542001c01c03001e803a0240c4407400e4910313100f03c04000740b8551a01002080403a0488050001d0751001c1c0d980c1483d00901080f814100307010500c001d4910380c40714002500a2030320741c008061006d0050808540c00003004801c030143e0b0000c1c1c20840700b15401246518818004100c600010b04200420301400703000f080c0c6068448100c0c0c000e8502408401980391110481001160000c081300d2000300b0038040c1c400d21400042005000490050280d40e0100760344080b507015120a4601c64440d440c031700348145e1f58012140d4490702c544828151110700000c0440d000201a5209078003c1002162 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 44616820 1250 44615570 44615579
    0x618020406090603050705130e0d090f050607150509010b04090501061a03040213020c07120f1202070503030f07020307050913060e03030708060d02040912030e071202030309010807032301 82
    0x1034a025030440b224040c5801d8040002c1000000c4604c116a415914880d11160161200c0c0107040e180c50050514410111034421140d4030400080c104e94951415003111a2504200701e4030303200d50040a040281d8442e00740d000540660f01054100c000701000050003e01e080203d0195401d040b030a82e4035035501c5030100a82031074229940c0301c95843e07080d203610350710300390707001410000c41c07180e0020402c0e50110706140c1e40e404c07c01114000d400926400300744481c492824440f4501540c00840e03e003400e840040314110700010f84581a42ca000b0080c40c00d14440a4141a1a803c00c240a903454400c941001845449901c415401036a900e01c0b01c2e2100992820110141c94980c04d0082c0541d004004001d00903a005001e690451000c80d20340900207c640000f81c042d002c03244015101158144048a0362501a03200c1250a401e003019a2042e646d41c01020f5090181610007035015001004010301940c42051440c0e4064041e0600044080c181c5940443c0311035511400c0700c80c000e03036400500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 44618070 1250 44616820 44616829
    0x91502031201140d0b13060213030203100501150c0203070f0602011b020303040c03030806030c12010b040e061b030403050c070b0702010914210c1203040603060509010305060411040207061802 84
    0x180500f28840302c440c45a10050049059603240e0203014080000c03080105041c80c2c082442c4407040c2d5004403003503440c0c42c00c0c40800500c1100b9072000300e20038450b070f4420349120005406410704880389030410349449101404240e0340c4001e648070132681070058120103c0c84503907807401000034014541c0006042000d4502408034503401565500c01d65209004000015084818800a0304c3d418030b0103448540b80da0000c40c0c03800c281410141da10004012402e134a02c84154000096100211401d0100b0301110880c2911101d040c0c80c00c510804100740d00c2903600341900c00440d000b502c40d10f491494461100b64503030405a090700403602104002409805540e400503069026000081e28240d14203188400585000c440a940035841d94281c1c54904900c0310500031020b440d1400303080700c0303015401010340d1a200d81c814000c0f007004c2442c1c035401148605025a0080c107aa600000409143c3c540348c0358600da460b0300b813429541c026002c1106200150301030043d01c0c7c2c42400f000311101503011520410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 44619320 1250 44618070 44618107
    0x50a0930050c0d050702060d0203040303091713030b070519090801060e071209080405030102070305070203010c0201020703120b0f0d0605090f060c0405010503090307020a08060103050714091609150203 88
    0x1001c01400384500c00d4001000f1410710031807101400c10319500d891510108245004100c4d1006800307201008000c140343d01900600c8900344513a0800d81801e405000142d40340c0903c5251101d00780380380906100040350541065004061802d2903820b0112400001c6d00f020307440c0354564009130300c0103800c00044009005203000342081c04814045c600d03001c04010408484003800000c1c0544030f400704c8090000c48000c550150402800a55031001c6a040142113903020740c5049000b0340c030700100780742d002e4410710940b0355450381aa695008411814a0400508100c40c481584000e01301c05400c040d035501801c2040d181d210301004941454000c043e2803c003440380c0b001c400f440d00582c08001c1010f42850460781602d0003400c0c01922519603c41d11071842c010020002d42110005a000c246c41c80700140301030403a031191084440c501d03204e0039481182c940401c4903d81100045000c920300c07200702060010500061302e400030703980356a038103071611201c001c40300000980c10001d00b01948500a1192 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 44620570 1250 44619320 44619413
    0xd1502070302100c031802060d0e19150c090302060f0c15040b07020a050c0d050f030d021e0906030105061605010903050903120f0304030e01020307050307050c18040c030204050a09 79
    0x10001c2c100480170034640319246d0000244290344c00204031045000c107920104400e0001c3c1c0446040080300e0b840805800900b0f8015260306c42c1c0c0d08020049211103000304040b0490a5a510390103a02e10390900820ba040301c01111006031051100066141003040704080018161801c50040e040c5070410000c007c0000d400c1c2800c54001c03000d00ea0214200041e00c4805020a40b03000c0e1200c2207138280b0600303044004c81441a103000000e030103650302403031b500034107801c4140201603a84441d00c1d20b0608101d100d0040b619401000074001044285400000340500e0038200c00048440126695551300f100c080c1d18044001c0b58010a072062142020811220a0841802030030300d45680b040c004144c1e0f0100400c02410812403039000344c0709034800d006542d0404e601c201100e8641c0000e00c5c1041d19040142c0a150003807480c41841c0400e000001c40d06400b4a0300b00a83e43c00c01800c43d002c1c403014260040400021a803220021400a501000c80540100000b903c0345c100f50a14100310300006030700c0c0c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 44621820 1250 44620570 44620577
    0x1503020315190b0c03040e0c041715011a0c01090f0c0f032a080604080301080d03110a0c2603061e1305100b0d1a0102070605090d1502070302100c 64
    0x10860586800711a0401e44a5143c402074540c4031610f0618a1846580c00180050f6140d2082c07060484550001c0d000350f9061000000d020701d6043c003040d03501e8103240c25018080c01c014004202c03030442c1408a02c000070465011a282140d10300d40710b820354454004c00c6a80b107410031003150520511400901c06800c3c00510465054616110101e02103100c800504c08201c51076001e080024000303100780018010f80060b0740c0e06141a09043c0c84540003441a0681402480c010040003031081c840e4003418411400c401c1d040c0384e01c000040755840c140804c00c07500804030603d03043e02c3c461400e00ca48104010404180d549181c05000d007d49480d034010701c5945903400d1740400c0c145a030f6805900300601e00380c6a002a4540c0d40703081d4040e40d20610761100c03080e418001140d007540445a0440f84103019003036141c408801409004a91b540c01503ca4000028003d1141e404186080e1641d1001030b40100850b1110000001f520401c0383d0104100324056486004c07071003402041405404c007040321508 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 44623070 1250 44621820 44621839
    0x218180d020f071a1204120e0a050a060c0c050a0b07060b0f0114030a0917030105010215040c140a09020c0c03070603060b04090e031306031e06030c0b030903041503020315 75
    0x8800b5989001c2030081e0780f0780500040d08018011801c0090707075103481c50700e0b81c00034580c200707420040202c00d10111240e0000307c42096a02c07441c28408451003c44001800c00310040d490031000310385013048110200e80000002034005115079032120b03240060005c03189400c0d42e40c1170528104044811030381109016011604544000e6178000c0d410321120121244d032140d42c0d80d00c6002c110018186004001c00600d8244d0219000d80d680380003650581e0000e800311020303c141140c0803101c041c01100c1c001c001005800b024020b4540383d01240c44051806010440b407070761124222016a00300b4020402194042c4040103810318080000200401060900b005118240b03e201c86441c490f80c0500d0001c00d40300c8007410710643c000c0044a6080b01c1002d00c1c018400d8480e00e00501502c81c42001c10801002d941d00300071390810074465030040b241e01100005041c0e181110f07100554000400082090100b8000010916600750507540c0703400310740e03a005a03646048101c1e0030700b43c000203490324007494801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 44624320 1250 44623070 44623093
    0x106030e0f03030105060c070902040303090e0705120a2007051b01180618090f050103051c02070e1b0703020309031204120b1519050405071701030305070218180d02 72
    0x1000f00d9055900549495a0b2100c41c041d0061418400c1c1e801038030311900c0091300009140e0710444030810b0f00c01a10302d00d00c0580b80c1c4401100d11340203540c246282010b11001003001c10409070301c000c640100d501a200444040d04408400f207400070038064880b40c004011003840c003254000c441920005c00d080030110410700c4806218010005e001d05030034064414030191300410380c1c001c000010142c441d000e00040110840724400b6243c2032100b02c505114400000d03404445000e8131851364001c0350300620000d440c03c0038800800710060030140015025440c0c80c4010080c41700100b2030350707000350015581c0e038004000f4549007000180f00004800b50500c014490300e54094a10b45006400c4041e52a41d901c2d101c00451941146081c80c60340b03ca507102d2403007460807400b4103603400c03500304440401c501d558004e4240e901034401000824401c600e18014000280142c015160311400503050000606a1120511701c6440aa55102c180c0702e49204148044d2410084090131045070310140100b030164 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 44625570 1250 44624320 44624323
    0x170f06060102011523040608030a0e060405010c06051b0a020a03080702120d02030601030e0d120b0a0e0606030702010b040212090610080613050a0203060109150803040f0306110702030609060106030e0f 88
    0x139004401803600e9211141c5403400c2212038001c01c0a4000b017003005400c0e6103146040e0380e0740c01524440081080b0800740b8505142580c1520100c907030603111422006555500c64004000080042058109402e4940102c482117400f9040b00c10940e0010850107503d0f04020300070341c0c0f006100344110762020f000b144555441400381c440100d0070341e10142e20b9840303010040e07010307000c0035100c44428800c01c0e0203850604e80c4040e0041503139404840402c5280f8505090150b85010b03405600ca0001c0076170040303515810070700300440e4401014400000c0e201c1c45d9078001402d07039011080c48501204890f0038080f143d070703003400040e400040042224a9031840c1190280d29003400909000c0c6030080c1c0306040e800d1017024080e0748034950740101500c03001c0da15810328000034868030006414101d10184080782c0d4030300000c100c905850254585034038130741c40e6036a580003400219080010401c4e09119034401600e0030070141d8011804400905082e40c1416001000c03109101c603444040d0384550914541b4050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 44626820 1250 44625570 44625611
    0xf0606030a0f060b03060709060f0305040809150d0501030f060507030c0f0e0307080a080d06060504030b010b0f0705240c070b0c03090703120305060310020a020c0118170f0606010201 80
    0xd2102c8400c2e20310610703042102c000c01e1800c1e003094050094808010710581d20103040f4003900c50545503811002c800200032021031301d046400801c501030400ca072041524044d00c5442d040039200480601d00280500003000703444081e8000c0341c0c0800400e011030200855402200d5001600c0c0ca800c00c01640c4111000700702800c101f040c8414010481c8080d0425141400b03550003426042044858100d018500380f51107500850920034450300e000740120710070f889081101c08580c2c01c801002043d0342012a010015804080001101141000700400142d024041420091582005110170307007010515003c190748018000d65003610108210000640322600c0382e60410440c490f225201d1399003040706032500205d60006002d8039855140e50030780c01e5164100c0ba201c0d8105405603055000005645401d82c01142c0481000d40c01011050039154030480b50b410341d44a0034128968066a510b003e0b020004980100c0c441b075400c00004402405410800c87c0e4002c5000e2000304003030348440c01480040328 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 44628070 1250 44626820 44626823
    0x40209040303060b0703020f0f07150f020a061e05010603060810050a020706060e150303120105040e0c040e01020a1b030f0807170c040e07080609150112020a09080f0606030a 76
    0x15811000c40d0a240c820360001c2e010b0b00c102102c50b541c0b1700c8941006580d0b010609000003161181920b62080000b02140f05403c982c0500ca41d840d40700176404041d0b403c0400303003541104500c10304094501142160041c228042258450304000e281c030141c1200c26a80e05801c51014542003c10420030718030f0026091a400543d0310000600d0303150740354000c000e8415a90050079003800c0c200c011030318403201c5107454040e48000c80e141c0e9400d070402c0103168403402070104261040b07004c1c0d40100243e0425403c4075001ea1000000d880c21001034100040440c0d8400000b00203c3c1e5011a035034984a42008074108042d18552030240444000d80c2c1c001d190312610071700c8500f040f03503643c00700b601580644000044100d450b074182c450782c42c0819203800c1e150028401c0c8452081c0060201d0103e0f80074821032030154801420741022903a909030304a02038021010314904005100ea844074041c9152b201404100100d55202c01150345080301191070041036000c0603281c1d070082014004140d500095040c2000d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 44629320 1250 44628070 44628079
    0x918080a050a05070b0a0621050c0411120a06050103180f0809012c1309120e06121503010606050a09060818010e0c040f06030309050618030304091407170402 69
    0x481c030b1004121540d00500c000242260034040c140200c48002d0342009050303031001000560350280c1024180b9280e1900c04d0050103036000042005030f182450342282d01e00045140e0041d01d01000c04040c42c009000c1200d4070640aa545d041c00d100765039050040259146130002d030101809001d40741c4060401071b19034000c00e0240005040d00c903c2c1d00403825814007070000c24031014040c060703012008560140f503150031311a07500301d6001c0394070780000c2c8107a101c4990810b141c0072001444880030355800501607042c070b900c0041070001c4800d1400901031036118051840122041740d281c00d041c54203440e195000001802824030103001116030041095044985924105003d0385071520515405500143e40703e40a500740b4907403e6034140300003941120b0304c0003a02d007042074405810091003218140d0000030000b038a4a03204101d0352910741c014003030100300100301500fa00340c1c0b80000b81c9158072560107403002640711100035110281d070400c1954041140e04129111411003003500820241c0100000e206 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 44630570 1250 44629320 44629327
    0x30f061306080327010c022b050307060b04050711150a11070c26060f06011b0803040b0f011401050903190b0108060709060f050d0b04020a0c0b0a0204030803160e0303130918080a05 79
    0x92003103d88c0c3c88075820200f0b6907581c43e1103040810281c0004100345000d9810300c80802c9220388200c2c4518404078601c1c01501c60f01d4200507040c6100803000d8000b480441d00c6000c20030000041900403d61b551240e1841c0510030302d890001140c8482c44a111521102c094044c0300c1d04040c04034003150311403010213020046944080c016543c5180807694031090414000a900802210b4401107010f1400349903041043e9540b812055480c6500340036040c0b00c0c0c21a0b140b41d1001f0350061001c0c03c0500401070595224030341c03101c00880001807001c8161403041079900100500746042c88000d800018600c0c08480e20382c100040038102001c5d03012910100040000c1392018141107502c6444100c02c01001956140c0e40c0340c07802030074008444010345403148148082507180c0031505c2100d0440e03500404150a60b1f65500ea210662501d510701c6400740241c0f400719460aa4061001b00b2601c1030b100e281c15045030405c00314800300d0303507071400314048180010b0943d0042900c00065800242651804035034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 44631820 1250 44630570 44630629
    0xf18020d031106042d0201120b0105070b10031a0105090606030a1b0818010209032107080706020304060b0904050a06020a0504090e0a03020f03030f061306080327010c02 74
    0xb01e680318000b2104890081000380020045860f03480e4209201407403901c150078400310090021080e0048000340491060048281859929041000400014106107041c40390540b9070141e0725a040369000c602003c000703414010801000c04241d100b40c40000d1794502e40d13042030085000e840000d040c6070311640020000401c1c024442d0449010250b00b10b1810b400080740e458050150101a200244071581c1c4620005000005100b5503000420060007070208a0b030010708409030340e813142e4110030ba4440404c11000400d88180043c000315204050042e683c0c41e060910404481100c070009104551000078000800c20004400028540001c1c0043e541c5040003006d98003031043d03a2151003010304045128401e110041010700c00640640c081e151001003d8481580701c1c401107d011200307008000129081d41001103000613008413071880050301c01d032680c10062a5030040e4030751300c0d84822461f4140fa42c0b9416000d400d40e034100282807165025503c0da0000380c507281940c0c0c0030701240030080c00c20710 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 44633070 1250 44631820 44631827
    0x209060c030c0c011e0512040c0f0807030b0c04060f120b040905030c0d1e030b0303040b03040f02130506030d1101060308040815060a0506041206060314100f18020d03 73
    0x1030242980030110381da0791400c032050b1501c1e200b1618603a40881c46146442d00b0102d20140820000485c40d034840385482c1d02034001000e40740c80a0300c00d80321055404408607a110142a40c10080d01c00300c03004005061031880c0456009100525001481c101444104103164200215103403000581c14040c000d8001500c184004241b400c01c0e441d4814207020303000051150120040955412801c00c0d1484101c0c6681c06a44003400071169100110f180030118101b9407180e400801e0300700c0000c1c20317640340c1661001009a50f410548043c1c401341a414400021403a00100b0801041042c0c0c806005070701e050030010b40c80d00a0912000c1c00d211043c84041d1003080294000780c00345621100b50b54403580c0322404240c0c1c445200b004460000c1c06200403401c00c0c0b404c003c004040700d500400581c5414182070003400310103500d0700200d034002e464080100c0040e52400349905a0a01d0740010000e0b4612002c01c40181c1d08000240541186407505200d00b1056a10542003060340645005035117204618048 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 44634320 1250 44633070 44633077
    0xc0f030309021908010b1806010c0302100501090c030b030c06041809080a030e0d0e030a02010302071103071401020c15090d2303070b010501051c050916140405130f0204020906 77
    0x2e6104483c1c83d20000030701e400e000c111056440000080241003101030501c03d030080c1116154080c42c007030100082c81ca602c141c1011110a01c03034416915041d05441c0c0c03d80c04d4400a82004000d039448903019000e081c2d0501c07600300719410490080840e403001d500402d40314850344c020f4bc00c98071610f01c408106982140c11001596a20a03005170b610b40500c0401402401005400602400382d40318035040284074890100d0064001005480741d281240c0c0154020350101c541141c000c0322034078030b8001c90359042c8968401080740c0601d41d0200c0d1481c80009051928602d5284c4c403d03068588010103500c00030003580c1e921001681d61100240081c02c204280303d401c00b2545042e130002c0301c01144a0305011020300800742c4034002d6106c10f030343c8600c0190780b03d000703d05107c80000c1320304154540c208030742e4001a0b003200884007940c107081840018007514a81c00c2d0420907503110070010803042828030784100b60307000e2a0001c0c0024461855907544d40741c0000b01c100070b40710f0b540100b5001c900b591504100c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 44635570 1250 44634320 44634323
    0x207030b09030301062006150d201201020c060606090d0b010603020405040b12060a150f0f0e0108190809060417010b0a05030f0d0309080c06071808010c0c0f030309 72
    0xa0400368a000904a5600d5109025000001e9003c6101c81040007000360000ea00c0340780b01e4050034007030365450480200760080303041e03c0e1362207a82c2042000104e1504008155008820b110a8001030100c10600124040c4100111000c0c0c0c4100803024041c50023042e0103400c03c4040310182d594503458070004640c0325003640060704680d5103c4c00018129055401801210000e03102030144682010802088035840207102166802007800142c180e462584501c01010421425039250758035003210b510780642e6500303d2611025905414003031a046d40e4151801015071800400d1040121800c2d00e1000d81c80031001480001c010801c4240d1707988410a4070041c10090443c42441001000b000b4060600c1290345070281502e200081124203001c9044880350a04600401e031aa42001c8210020300d036000069900c0740c410710242500c0d46040c442e45003d0041903484c2c402c0d040d0725085074003090b01c807036200102c103a142c418034459050304100301001c040d40201c118a88042d00b800c2c182c029000c00d200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 44636820 1250 44635570 44635583
    0x60c020d06020706110301081203010b030c071b08150f090a03110705040c0903022706060c0106031208010303080106020a03360801050702150108060a020a020a1a012103090b0307020703 81
    0x9040d1081e42c0c5c100085c60485448000710b41e844003107a1035400c03041c4000c4c0a14418118104002072003070340010300511480f80700b030401d0207141da42406041c48150740d0350442c0314035400001c087c80f0b90141c24206e140d0011001d101146940c1000d000c0d481d91145807510041c02c3c44413051026044a0007030181703000400014000b8422000904001030942649010480c81060900b40b6a9044001c48160854007908540d12000c2515141b04104e655000358524044664940360003100281c0e4078a50500745140c2601d842c0029419441c01506407801600720a0840d4841001032010941c44042d050104464080c1140301500004282901001140f65510009000c500003c1d50000540c0f082d4032a502d03690139201c404e0344100d816600004280305a91241e0f200d400820414100742c1e008201c2e84160380100c070060307481d50351001c0c400419810101c51003007400e401045500e40d160f941013580c22000c0c1d0303030b01400c1080d5a8003600301850340c0116020034a002c03000a1780c3d28020130240c405150440c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 44638070 1250 44636820 44636831
    0x30a030e0f0d20010216060b120102070804050901060206090c04022104030c030f030e0304150e0d05010f050610051e040f1403010c02010207080a0302090609040204060201051609060c020d06020706 86
    0x15000b0384520b07407900010300041d0411000c0000f001040c820f0720f0642c40c524882650600c41c680313910740600309000210b0386c000b0266403c036529400074802000494455201907840301c0c40c0004000e80100140e01101c1550044401c200b2500800705210f2100c103811240161940c0c400003103404242c18032080410701c2140c0000740402d242d000140030858510a0740c0d45c40820444001c00c4003a28050134800e450380d4400d00090082240803041d00c0c1d030346040341c0341c04140c4c0c030a00e000050031114074480c00e8880b03175914182c110025002d809000d601000c29074200c2038140760000d00504500c1003d6404403524800202111803000610481e0000d00341d0000c11103102d51200300d031b1800b50302003002542c801d62071710b01c0f80100e160060083d40d80711a04001c8442c180001710905601035444281d4442c2d0001e001c00664075296518409030014110542c00086c2c41e01d0501d064940410001d0001010322050b0b20302008616401140c45d55801d60564605c5003030060380ca0142c01030300484000510850410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 44639320 1250 44638070 44638093
    0x1403190804090c050c16054606030608030307080f060310050901022203020604032316080c04050903040909060e0601031a0a020309030904050c0903010501090b010905030102040503030a030e0f 84
    0x1310145c07010107a00c0b0240e40c4180901280040800301d24418190065840c141c0c809003da560702c03640c0400c074a26008103184400d41c00084817420403552420f20418460a024403099605110380805802202e00a6184d070030100406400240020b2240e05206038400c0040c1c45906d041c400400300521880050003d0305203c1c0e2032a003c2d400403e03084080c1d9240700c40440011b8000181030301241d8025002070300d410304540b29400480280c990788090b6118070750300c03569800d01c04c018210076903e1514030200040c0c03c0a920508100559036a45e1003541490306110007008040115070440b207004034001055102d616100c4003524804103503132a14000c1900000500c80b581420343c2d003101081c4142c005130360741d0341c48443c101c0c002620180959032003400441d105040030b90015410082902003541410150000242551001d80090f02190f454000c2c482c03055030020b0a910240908900079810141080046541d0b4000c20b4a44410107450384080c0480300e1040c00a0200000d40b4000d0b00e05a4848 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 44640570 1250 44639320 44639327
    0x14120d0305010911031902160b040308010e06030303060f0f030a020a0305010e010506090903030103031b0b07030b01020c060a0206040605100b030c0307020606011d01110102040801241403190804090c 87
    0xf449140042c0f801e0010480c1440100c40031a0711458600803501c12000889070003c00030b41018102d000360030030314030700540842d00303100015210314440d13520003102d0340c10440c00ca040c0d4132001c0c1c00e5034060351052013804055695400c14900d17485060b42c810340d01c0035110340000c0c54100945006504203d49240102c01e001064001035000031303580d0001c0c4480e444440c05e000b070506e8111840c4810390030a00041c00007074420313002c00006a038002803100201c03941d604e9a0301321310411b40b00b5a011941d10800fa15007540c041c000c2c0c00c0039040485026041940025000c1d4030303424020700050841b9551000101e4200e040080d090140140c6d65848e82c03039107404010075040707a0042e5412409071166000140d0250310402e801c0024201c4108000d140e002d0310001903903401043e07651350345d99540903c00410050703c241300701c99180c103255490918281c10400349070b007003a030580c105401d1110b403907048080d0350f1070004205030040f0b0a41d160170403507010303030a06070501c1c00745402020410b400c0000d03428055a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 44641820 1250 44640570 44640581
    0x60305012307090b092b0605010b0c1509030c0a0305040306050a0911010c0f0b10050f09101503020f0a080411030609060c09010306051008100603020f0414120d03 71
    0x5000a8901a19040400d8a035401000c407104000030f90110000c2c81408060320151030290740107052800b8a041407407000214410709848411444001c1d0b4220b400e20619005490060200000851a0800e5190aa91100700d00c28209030014000700104400c0c00c5c0c03c00c100d901d0f076107000c0700342c500210461900500b0b0b54024481a1141801d10300801e000200a1044802d1280e00132100c040440d407400044d170314098455415209180720724110700100b06521000c52090a051070413034400d900f000100894041c900130243c0c0070344a01410450b0701440c034248402514088071803805c0c2c020b011442140030b4428005004041000410846815604031070702a0280c1c0c0300328540c0040c00c03610818103aa40c4802c4070000b4681e800600440c00b4244a64010401c00c0818035010407142d803658082234801411020200c0001c642108005d0300700c03a482c0e0b4980260509240c1580780c11141e41c0101e0030360003513005111200742406001e100c40d9503108088000d03020018192081c0b07440c2210050010b08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 44643070 1250 44641820 44641841
    0x110708060406090b0108012c100e070515120403030905100906020a03050c0a08010e060109080f030703020105130c0e06012a0302010c02030a120207050106051f0e0a0501210f06030501 80
    0x1310508008034504506010304a451180f0900c1002698481e914403805500c034509081140c3c0280011803609081c1805250b42c00c00c0c218004001c11071030241800760b0303582b40c96006505a501440741b0345441d940c003070b04c030303a001501844e01040442d540e051160811034020940000f5510706403101003005070603005001a880103440410042d50b071400350301c4c10381c89078110381c41c0091490030043c045070002d03004e00740d000403040c50035108580e1554910340c5400b00e808410303d440d03030020a0b00420540d0902420381d10000fa00c9011690344802c2d0781d44010480a8041c400721036551500184080c0d04c41c82c2c5414484041c049020074100d00180c840340302c49d0136a0707419401942011031404156000004403184c80e15a0b80d103414901014114030402900718007000c44242d500c4000000349503a68510000600440344800c110301d201b5130001510b0400b41310b1b807c43c0140d9400d2000c110310780e00002840003c54800da80050300c0000306580c480100890401d00301590315004006c0140201540621a0203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 44644320 1250 44643070 44643083
    0xb0105030d0c0206120907050a06030203010f170616020a120f090509070e040203130503070302060f060406030807030503090708010501182403080d020d02040306020c010c0c021011070806040609 85
    0x150004011100b6084112010b904a4002c001c1101c030314015134122a400400201a100740755190000107180d030901b13a1210f40025000f0005202440d040f4075414010401c12000b03100c40851980c60a4a17981e000701041d80510b810029954001c0c02804001e1200c0e600c00e001d5000a8100c043c050710740d601d145052000110100c0c1e012031142010504140514a651242e40100107140c0800c000781d480101702c10300e040c04040f001c1001901c100301a06220f8400d80103400d1070b01c1c040303c4800b264140140b045206900300081040811510000c49401c0f80d01480c1c950743c0c07552075140007480c200c029803207200c99618080001608448842c6950750021030100203018030410440084440c024454982454450450b4100b00148800c00141640d0880c0d180c0581001005007151080ba00280d005940c500d40008200e44034117420300c215901c69105041201c210391540d0007061400b40d034a140340047c07020089080d1944a01040001d00800c2858201d40711440d10703240100c06071141c0714040717030507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 44645570 1250 44644320 44644333
    0x1060b1614060405030d0b0f0303030a0209010f0f080c0f0714070801150e010501081b0a05040303112d010213090b01020f0f0d050a050f030403030b0a090209060d050c0405030303040b010503 83
    0x181c040100c0c00c98080da401c00000c504001c480b2182c540140390f98801d2a034031013050101d40410351001d1000d5445010356038001a2640d60000000d814030708113030301c80c1e001c008590b110226115000256243c015072002c40c800c2c0c40c0c582280c211000340c41a000050140300d102d141e0044000380014440b001d840030b00e00284890701a40f00540010ba11380d00901c00c41da81c2010041c00b8552080caa0a41c5c4080c003240c40880d60741786480007030b205a0100c00c0c2c0d0800108000b4090051681008201080c000d05d1001804040882c4041d90000b842c0c200c00094000516500d011506109405a44608201c003030302c103002c69510201240140015580e40d4094001c001c103050004201058038540c1102c80d202a109104188004454951043d4103203800c1c084280403030205445840055032081c2d2298034000789010060041050700c1402c0c0c0c2c083e55a10780100010f542e40e44641d01030740d9036030002550116207604d88101c8103c13180580d4221603054400401000180480d40c0000b40c1200c2064040d1041c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 44646820 1250 44645570 44645603
    0xd05090709060506030402120114070e01020c0d080901140c1504060609020306060703050705011401180f0e1f0b1005070c060509090610030921020c03030403020109051201060b16 78
    0x2a14001d101d03e40d44070005200040150600b00c6901030030214000002400c10300410400c21840010340d41c0c400001c4496400c50070342e5804206a069000046807450b5503a07030250348140262240122640c10001c10341c6480e82203a60354001c0e5000c03030007a44285d41d400c001c02c40000114150482e000e4407840d041090003e203103201e9100b1a8080c00001d02405e280c4201074806640990140a086582d5941c5064503041050b5075a481c43c060000380403070103e0440580351100580340718509941c44149011200c4440040024400554030b0200a218400a864551b50001400211559078100301880d0408080691003001003401600c43c045000070b01e82c881904903020700070030900769000070160000c2400c40c6840c1c2d03501741681d145450041542c062560341c2188a500f0004200030700c0c02c2c59040714038441d8041c4000301e00c001c0103900071070505240d0740000b001c1100c5031060038080d0b40c9556101d03208103002e400076405800c1002481c1d03590a01c14100c0e00c100402118140c50300b85400c070b42c052 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 44648070 1250 44646820 44646839
    0x1802031e12090307060516050109080315030105251413031b030201080f06130c0f03061406030c0a020f01092321032d01050909060403050409051306020d050907 70
    0x103000ba100a401024420b04100301511103500003803031501d05000d00c4400c03070000b94090080001d010b00c0740f140c2d141c40f0f04104170240c01d05140c15001c940f1990406081103601c0251500001c4074682ca11013400703030742d19400b038141c038113200350392140701d14010001d9100e100c1c81901002000b10391050180102c181c4107149504c00a031801d010007400200104003083d25000c401c101c481e0020001008411801c00380740804007142e0b40500d0110110391891801c1030143e07014440c8900070403a008503a003520040e540081c540c2d100c0140f68000b030460124000502a1003007088144104c86c14008128801039800c1900507038440030990602c05048007204074918002007601034012170300b01c1441d146040000102156500300400c5448020a4118400541c0300905d000300003110400d401c0c8205035040c181403000d100c0d00100243e55560141c418000003c0d4400220b9044883c40c1400090548030940003d2120810503005840180081811000460194421402002020104c8104581c0d525825 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 44649320 1250 44648070 44648077
    0xa030503091003060b03130b0105060702060904050c040f0b070b011a03061210060e04060c050304030f0e03070e0a020c06010807120b0a020405220b040203060604091802031e12 77
    0x10440d81003481084002d0600010b00c4414200c41d06010070071903128030a228054004032031034403418802d0b0134040240705001984502402d0150741c40d030f01d003080c2030b00404c4c0c0d50b00c40c0d40d2202d4015507840e4002485803078110182e801600070010001c507166550000c844490700201c07000d5620005007030001032182c441040070b20080c0302d010b0700c4508640d20b000802055161209002d4401c1c09650a0280c0000c258842c220107040002c2c940303892400c10b424404200c2d5031109020043c407a0804c180004660801c40c91904034031140313002c00c02504000f0110b410498698489150300c2c41d11420b010824060381c000d4514920800110341c001d07a0b941202c55500c3c01684a44490003040143c0369022032007100e07880f0f9100314074100c003500d803a554a011450001440d10b80b040080d0131070041800808103400340b807100c0d800c11602541142010000645688254440c800d4241d5440c5074155281e0a4002c180301165001800d079207040c910b0901007564681c206801124a00400b5030100182d40301e48141c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 44650570 1250 44649320 44649323
    0x80403080106080a09080307030f0e010e070513090507030807030f020a111003020909010303020f120901090513090609050c18010b03070e0a0f06020a11040203060d0b0a090203060103060b0f0a03 85
    0x150469a442d01d00c041c2c40c2980080c22003981c00f9241c41010002c07640d1700000f1400703400c0c036550024080c200240800c0441e4418040c8400ea641084034a500c507680005250050b250b04940c000d0300c0c0e0765501c201b88000d00c69080010101d000302103001040c0f000501c050309000340030391100711103072040c0501240c1b50400c00c3c9005004640d0000a4241800c00300c00b2801d01c0180750500500e0301c0189000504040000d920813001640f0006a074482c800081c0701400642c0748501c010350070001c01c00f002030216002c502400303002c0c0000320b10542000c0da0360b406c0341c0c0607680c010f4400c00c00c0c4030980c10400d40350780c0b40d101402d000380060000a04421102c280440c100c5903911609815070701e9010045070200c050000c0c095010308000d101207148041440341380c00a0607a5002009114518500000400f0900130b0303181c82a807040c0b0822509440c2d10214204c032030707408005a04159500c2c000d030401810340580c081d42500c20840084100101e0b07501401080e1000c652010815000030700300300c03250b10075010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 44651820 1250 44650570 44650577
    0xb04140703050601021e070302030d21111207080402040606020a0312150b0406021501050f130507120603150b0f01170712090501021c0e0c0607020619050d0c080403 72
    0x10a903a200b54020b40d002003051040d00d03403950181c0300c840680300040c1c0030110550010a402c0046213401c003c0c0341c0052800e800d29a070b4003044440305c07021000d1076404500701103440f00030341c2c0d40c1415100100c0d00180781168140001d400d050074002c1c0317003810898040303003d64a41000414600e00003d690060241c0c103a0ba900340c2c0d8050074841354040c10362111886014510302d00d010909031150f1300540042c10b40d0741e00900c98010080152070f1141810b80c8000c0c014035001980c08800e07180c92a41415203039a56801245503111000c08842000302c02000380f5082d4503141c0e020007080641000d404e198940c4c6001404801e103140100400c034440704484c0da02040c01a804640305442e81c001d03107940038010b8103022a0103a18059011709450b8118012169658000b6005107010310000070025480301041d41000000010b0303404c42c1d5291191110644102c0000c507081c2d086540391012202e034084012050100d41e641c1d0300d0b015001d40c2164008520380740c00c01c0e100e995480d200f0140340348500e40503507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 44653070 1250 44651820 44651861
    0x403020c1210110c032808011a0703090b03090c01090b030c070b040f0501020304060f1503051b04060504020406020a1509050604120302070b0702070f06050c030d050705040e0a0903030b04 82
    0x155440001c04101004000f0700000340000e0020030340600c054852074403c801d412089441c031005001a00c07095001d54410703c015503006104440b01100c010075005103035071060f0364421050a06403511081c50b03001a094a80c000200300740d01e18041940d0658490030b890ba0240b15484006075401e9000071203031901a000240b0080c00400d01c041041e6801c24090381c840c241c904501d8a0300c0e820390303000b100d00390380c5540c5a0042400480741c0d80320b040c8a485800d003400000310b0850340c40903154150012106100380740001c59200d05d90f2141c1c0120000d001c014421969280d450501079114200c3c12015104518184541840d490317140c041c01201c1d6034400040c206035a100e0340d80760a0804032005410030160b00b840031400042c00c1c481240d003c0c0f01c96400906050745006a100d500c5c00c0e554104508001d400d01c00d1043c0c15000005079141c0041a02020480381e0720400304856601440c1c3c444a00c641d01007040c015903148661000c449640650b505200d07040c880c10611040d00c5403540140004141c06 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 44654320 1250 44653070 44653093
    0x203040b030a0207020a031b0311010e0f0103022a01090507050a03030f050f04180501050906010e180402031c030209030709020c1005040204020d150e0a05010302030a0308070311030c030403020c12 86
    0x20f60040060520090111070000e480b9100c0300c81400d0914076a4251240400040c0248682e01c071004185000c00d04e4400c0c1d1400e03081000c1040802025051030505401041c107141d40070808010b0300400404210b104c00880748640410301905140900f0346450080400c04112410600c0101040d42c0e0951685254001000000c0380d5075881600c180411050070710001c02d50300001130020301036100178100440d481d41480c041008089025100b41d040c807284803205009030701c0d03010482150344001240001a0f9039070f0300200c0d0905d5420312280c0960b810440200c48480d415a000c0d2100b020300341c00302c4540303a0701c92954000f244100d03034002d1401c0c0e00039030fa000540080c42e0041c0d40d00c01c3c4068005420241071070004c1e401e44200420071408540340b0003003032041741e09004015074030090030f9406012030b5145402082d2104000000176040200c0e400c0000e0800d80250408039070000c000d4a07141e500d2030004424042c81c0c009176012001802444205500c13031400000701640d19200744060403405014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 44655570 1250 44654320 44654341
    0x504080a081b0304050d021203060d080310030813061e090311030f010606031a0d0c0312021f0e16030b0610030b130618090807060b0607020a06020705100203040b03 72
    0x107241c40c020604109803140b8102030200076600540c4100000c000b480d02c0020040d04001c05003c800d03031b400400340208244c0365103051340040541d030031100499517620f41301c0e2202c5011135682c001504603440052840401003d00300000700701e5403190303102c11aa5038003d80c00e0f1500021201d0a00019100060501c081501040000c942c24001002c40360000c04443d405c5095a015900c9040820b039070341038482044281402e41c100110301240c1c0440759903015502c9642130046404041d1140d5160518241c11a008005c0507a02007045107104001e401c020f500c603800f41370351040f0440d01d8003071070b00441c0e04068030b03c0a610a13268080d110118543ea10014442810b40c0642080c00705502da807107100340d40e03c4260f198030b0105503800d00400c50310b0900341140d0341d00c00014940d0301054038040000d40480c03054416101d800d54005e00200b11764040c0000940940220b01001e58031506030340000a0351a000160030040b107905aa030031000400000007661607000303911403510094030070000151403100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 44656820 1250 44655570 44655587
    0x80609010b030303240a082413240f050a0f020a0f080903040e010e090606010203070302101109030f060a0b060703080103080714030a050304060605040c020d0e0a0902070803100501030504080a 84
    0x15034100a00b003d01171800501c59403c268018041900405103003524140012100c0c214403c00012540480c1414652600080d01c0c03050003420a44c020294103010000440c034004005491038030034017080601844100003084107890018200345042e0707018013440c82500a1350340000b059180c08046503140c4505a40014008260a925000c10400400d16803082140c0d14080d0040b0000050f09142950203907240c10405840c0714155403040c091440042d81c00180c402c0c00440f2a403002c540422103a604906034015003c03c0c0b0340c14010f994580c4002540020000c1c03240d003003003100384101000c04003030000301e10030200098005510680140042080000180f40542c481d17041111a1010030032039904681003100b60300e00142000003031200f408100d0007600b0180c5070403501040325502c407410284d07880056401403401d00288000f114041c0d03a40c409100000c000c9010150351381c40d240d00e05143c1030350044031840d4500428440100b1254400c0c89031522507075000448518100070480161070501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 44658070 1250 44656820 44656861
    0x130504060e19050d02031201090b030c120105071205010b040501030506030c040203040f05071d010905071202040b0405090a0b0102030301050d0507030c031109150a06110102090415080609010b030303 87
    0x280c07a00c5001000400402c440c403956440310200da41d803a5914030b88141499210560801154024044103e60182c0d0780071560440d0000100080c03c45401004641030500c2c9880140c1e02500400c820556807206401491180103a0707541c01c0c145e62019908031080fa5002e00030f8840c0003906120500403940242d0140390004001401c0f0341000002400090076030f481214122154012080402c0400c0404c11404001d015401400600c02d80790502002811405105150885480e1000700380150700448060b52110701018065503a95104d4102c540b15910612810b400f070082c820000b90901440e01c140c1e00200c0c0141d0245185034a001c08000180b03028000945503400350110020000d00c04241442c0114850b412030010500e0410420044510050800d5400b80300c603c40b0107800da880300c4104007a1103107401c00045011042c00716500a0080da10402d030400e10b000f2001044caa007d18640d0300316401c410845209644291001d800d07140c80c140344079095481480881c441c0500c0304442603066 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 44659320 1250 44658070 44658083
    0x50a0603051f110f0903100207050d0804080c060403030209031006050a0e04081605070302040e0606030601062106120204060812040e0a0b0405040b06030d09030203070312170114040b0f130504 84
    0x1480c141c4440c000e0703901013502c020f6811030001c0d00c00c1060600f80032201c00d0881d0140118205402c41c0c640743d03100c0702000304005c108554540007a0400040b4015a1040c043c2403044811618191501400035801703003030214440c0c855034030300381d1550103140914400e58001802086c07802c0d06c0d04600950050028000b100e1070b400a10141d020a282094240b0041d402100102042451801400101d40e607160040e451074120b44104074040c0c5000a4190445a0a1800380210003901c3c0c401e080406403000c80c3c8500d00c1c144200013480f12290112182428002c440400407a07079a01032259440d400e5040c00c0f41054000d001c00c201c200000484030303a018926090115001900c003000600b2924103c4049400c0c603215014000c95050400000d20000780505100103900c0c290f40000c2c1d5184682c0c0300c014500c800201182198520500a0703802c0d103851402c411486503141c189503007204001d4225240100c1ca081000210791070f00d20f00813002948080c0c58105411109000400500f03002031066606 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 44660570 1250 44659320 44659331
    0x180307050312090a060903110909010f02040303020a140d021504080702040606050d14010602031c020714060412030203010e04030c060905060a0209090a200c071505070303050a0603051f 81
    0x464400740a034009102d82400310b0340c0c0d03814840082002c0c48045800040c10400300071014800640c4a1802014442c0102c0311600d441e50750f0101d442c054451441da41030f541c0d00100303000040580004202d040301e842488015401c0c0c3c07403800040d90310104468290010b1348403002c0941c441e00d90301005a000380c0078440302c514120141d000700e02036418507403040000445c0000d280545041c203208040051400102da01c2880d494440001e64034041c0c1003424002c0ca0001803d010040400c2d8110b415450744440800001d41c0410350043d1246c6085500b512204056200000d803e4441d01c00c0700e0607100080740c035180329162070320120b480c0c41f880403044410507a194040fa01040d03040010610608000c000965216040700c18031030116806820036035030504001840b096210807500148076400f0912106842c0c0000c40c00c541d1902c2010340c00b880c00c0301140a00064800c2d4844024500680651014440c07511940c490f24101e484911000d4119041702c0200d621114039040f041024032500b5a01040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 44661820 1250 44660570 44660579
    0x20c2e0e030303010312111b0625050c010f020304031a090a0c080606010f020604050601091104150503160c26130f03020315040f080f190e03011808180307 68
    0x510f038000e810584041c20a21440102a60b124500c04801180c2d01e026201d04524011600010800714407464440c0202148180301408a044100301801038884024280e23015810115210034041040a00150804541c910100d000004850803031b81d00101800c18080051454210420060b000d9211070081c100d031a03010400040341ca00240503c0c10260040d82070000001d412900c000007080c0a6404c6401000049130700400c0301030445110800209044007841500600c03840755801a101c002d5094074100d041e107070702c07602851140d10844126120801c440005030345582e02031a00400d02e404000c0c5990740f419041d525014a026140140303800c0000f980280706591481360021116000c0c500340410075458100401c0c3d644043c10100c40320719052945441e4581400c050024051440008001c0300348100d8404441000040c825002c441e900c00301d100501d0580501912807182d820040c1d1205010b80d5000c070303086616032000f02e00d85403c42000100e040460307890541030b07050041000008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 44663070 1250 44661820 44661823
    0x40e22050c0d0327060f020a03080112050a051002090f09060306040f0203010204150c0b160801121e0f0506181b0a05060f030406050a0b15030405010609061203020c2e0e03 75
    0x18040a03070901d50704c01a03091201c011700361000d100d07040045601001918012a4100c000c0340e042d6038285401c05240712460034940d203400c000e01c40007050380c0b081c0d211b080e0720b000700f6501034503540e10103c0703014162742000003c01c00140c0c5c040d03c0c02540354000201190004124940d2030f02c03440d1010f00003608140d6034000c0035400742c416840683c0401c189600c560100028400040d40c02100d0100765403002c180705100800100b014050030404003907d060b6a8140551400c22000145464407100c1801865280610510280c800308642c58801e0501003a440b460440401242c3c4c40b49030001c180d0b00d810180010038090010545c01d8001042144c0460f264596800520f801c2000204203540d0342803d24080d0203e4000030500c003401450152605200d40c0d1b001100d03040c1a1050203510703225121401c0c42401040742e039002c9861140307000c0c00003900c1c80449a9000e01e0030300035020741d841c03200d4900900483c0340300e0305014001e1020540101c0310000000401c2c45440100386003489119042c5004207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 44664320 1250 44663070 44663117
    0x712080f091b130e01020c0f010513030f0503040510020f0a180302060a051b06040506061908033a0b0a0e01050609060f0f070b01030606060e03120a02010207050102040e22050c0d03 79
    0x2c2c030140c00c443d0264a048e00b00340500d1740c111000e102c202242002c00d8030001d1480003112406810440000041b03002c3c0b1508000c07800721522a04411941d488041d0390b00030041d48000680b1000c6980c00b80f580e02d001100e80258070491b50080d040398034021030080c003220b165010050300400640e00c03603124035040c0c0302040070a100341d02c2640201202e080c0300003001031481280000c01081c100215041c4240507011003514009100d102e442588206a0500440c036094a401903608100025590701c4003004960070200c0f0755030064032036440441c3c03265021050080c6c24065282c100300f0400c050142824035100034544446682d14460900c2140c8051030f000340d1003100c0a840c000d0200c4014000c0c0312252040030010f00c0395042c005c040d441d100c0003294a03144842c100407644c0c10041103400415000307404a640c510f910000031075440da101c50117011322010a40c0c246404206001c0c1300c041240200701d0002c440303038020300105185403028040240b06180320b5811420030800d14000952460425180e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 44665570 1250 44664320 44664337
    0x20f0d060f0e0c0a09060e010e031c182103030216031701120b1609080f07031b0617040c091e0e030a0905090c0712080f091b130e0102 59
    0x20169003450108a008420303000381c5401803114040225402c2d594200c0785d601d08403040d6090a01154810000580c0d00e4101003201a806003d503144e12000b80302c2108100400103a0343e00c4000120720b84280f900716400340d07030160301e201e60a04140c3e440c4004251b16070040c5c4034881d00d405840c0c6040d821945c0300045010104801141d11141d022023031030040c00031240505821404c0c0d401d04001d0342c481d008004805090a44900340b025096402c0d83c0c881c0101ca00030300602801c60f40150707203883c025940c400c038a00c01950032240203000500f05000d2040c09070211400c40e600c0e59694640f01500584001014008440a4545500000707202c2094061181340c007007440d0f581c4140344003d03010390058581d03601c1e03000519081000701d1080560410400070640b1401e0310152039a43c1e0b24400800e0a00c81ca880241c84404004143c1c400b240c0d002c859240300d202c1c81c0b00147c070715484110000d503030740d0800342c01c1103182480300b11070b0346413420043c0c0c1006000c0d5030303480082200501d0101d500c0c220780c4132080303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 44666820 1250 44665570 44665589
    0x80c0409060f031502090f0409050708030c0a0b0a180219090504030309020907020705091303020a0203160f08030a02030301060e010c15051509130303111207031401050102010203100603020f0d06 85
    0x80030000e21a540003c02500c0c13940346001e504c2c1241d11400a06440004e4403c03074841d540d00c880d08001d001003000484003500142c0100c9542e4210303c100607681e000d00041c1155160204c00020f011440340d0b0250580f0540600400081184964204003081506c662400f048403481c0710300103103c5515016590141e402502d0001e10703402c0a00500041d4100109104103640c4241c00402c03082e00c0b4a400c0d00d601c0904100e20f201126060b1404a04142c60500d02a60501c12079607a806040207164201040b10011070036801c0960b502c051650700ca018001c1100e016810502c0108003240c020340082a0750003052400309104a12030b9288010a090860007900b829501c00411180e003501c40491030034540100d4449119182c1104240c680c194000d400408258642d0544111403a96400f90382400a210b0518402c40c0b03400c917402001440d030304030b07000c00b80d10281000040c2c9500601c22603015075180c08081c02d0443c281030007030780a0341c400c8038501c0b154a000c002c05051500644102c101074441c448 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 44668070 1250 44666820 44666849
    0x4030504030b01060f020705040b010306050d060e0d11030307052b0c0210090206070f050a200a09050c1206120a051609060e160306050a0b0c010e030910080c040906 72
    0x40c408942d1405070410028001c04207140c05034990000380030b02c201c035402c4038041100c02003c1c0040303024000701c2d40322941090481c050300c01002201e0b044280400100c0c81124034218100c14112040b0507105034000440d0000c2011070700b0703148140700625a19040c0c60301e00b42c1081075803040b50a01b075034200c190300c0c41070781c4c6004005125905019019004100c402c050200c01490f0b00050340c580b01c0c001d0010400386450b1200c0080220071311800000740d4020104600b15103152806c0310000401000881c4142014207020882c80400d100e014050b91901d08803d09042d80a00c805026041c00381144d035009500104505e1100c0040210b0380f035482c440d00240c90501403403045510300507143c1d001405100e007020414801036010295441c2d10561400340000101d90700f41c000d40003400281c201c43e8000036440d20104582a501000300b5440c050701000704001c0301454101a240d0040600503540910091406000a44a98070080c2c12080d0310f0311040c6442d9941d2000011105140c6c810005c506004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 44669320 1250 44668070 44668073
    0x521030a050604050105060d05091219020708060f0103060f11030c131202091b04030c0b0309060703050103050c01111c0c050d030e10020c0a1b05150702090a020307170403050403 78
    0x74050303103810550903034090003594100000951071303000d403c00b08029645d0b2840080c031403a10030469407070259900c40c030f01230f81d4a184545140c640e1185200410140c03103900400a0310342000031380c040c441c4580d80e604100d180d096a5070100503001032501000800e845803040751820300309000840c0038044111a840ea6602c1c2010b10405403000f80d844130022104448a0b100546c8410b03034602d911041c014030300034022044598203000340c021500302614400900700041800500303030000394010340d86071045aa090341c0c1d140d0101c050b1403090000a149070004540032a480d405464060f12103d8958166000d201c0808101c01c00302102035200d1000501c60489601804000d001886016442c0d203400d0242c008000000c2e41c2c0d80782c11094664800b940040c0075404880c05204400c0d1059100381191590004683d082170009841c4c02614032914089074203601c0c4001c0c03a012104c100e03a000e400c04480e961340d03000c070304002d40004000300e0a1240701c1d0710781c28900c2c40a0301c1c7d56100724400d485083d1203a00f503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 44670570 1250 44669320 44669341
    0x100c08060f010503040203060723040801051e04020109030602090f04020c0102121f14010c0f050c0118050a301a0f010503060f04060e0f100b06030609070309052103 72
    0x200740300702d041c02400c00c180009600c0101c0c0f41c0f5032100b07590070118000002c1c3c1a0704000f80160010300a5060f40204002c6110001034000d98041e80e810940d0240c85002c9a545812070316060380c0007400b241d011102040022070760f401070a04618000c1289001c40c54117408201a07901205000300d09960001d043c072040b04003400039941101c00880c0c2791928003810200d007506403100340104030003c0709038020b07005107a1281d0400c0440560100182d900b41e102c038588542d4940401030f015012420341c00c40c030a58101c1c140c500000b00d442c01004403801518251424014010422100680460702c40c3c041c1d51300500c030b030440c903180c51040340d0504000c56040c3c10104011b03406003002c810509080300400c00342d9000030301290409030b50100d14015031103621301800208200760001d1103900500114841580300032a628801c0d40c40000144403122040042000d14481140c42643c00302e4240d01141d102403007030b48100d034843e01c10800c4901140b020302c00c3c2401c0384220551000440400020030204410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 44671820 1250 44670570 44670589
    0x20d020c01061409040803091e010207020109051c0b130602070b01030515101403011e06080708030301030302120a0e060f07031d0306220b0103050606010917070b0c100c0806 76
    0x1e204683e860300c0428000070714030140588041d00001011000c1004e0f40024441c0e00d01c0000360700030000d41e107103079446132601030b40028100380d01007803c81100050604000580a070b00321401185254230200d2941c80a42110b006003c420107000079200840010b40244010180c03140240c1218100d58594076005150040e81554009943c0d500d006200407440d2801d22107058922400c00e0948040105c2e004ca030040629128040c0a14200302d1140301c05001c1d0b078406c0341601d8004003666120354813680383c10350740c0c4428440280144d03c2400210303103403540b110241505400c98503100100f182d003007000408503003166003242d4154400080201c2050703007110412000080f0782104075000b48242d00000e4a8840c020010b00c0b44282c44a01101e11401c0600720f09400c503440200400d0755616401d200d0b5a443c8111001030100c0c46011000c04d22071482c1c1103140290350208000d10365076050045415881c1c10051a40d003540c440d07607241c9605120b241c0640b100107102552141c846180200802201c1c41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 44673070 1250 44671820 44671829
    0x20712050a0521090f0f090f06030705030a050a020d02031c02010605010e1905100c0501020d02181e151c0906150305030f03060a05030706030203041b290d020d020c0106 74
    0x38070711128105840f100e0180d40024000b1220081845449000b1a148162883d8010380c480c02c0c2408008902c03207480b81c540e006050603170840e1403440c2c40e1424140d443c0807031a00508654451080301d0014a41144140c00d003520140950350800f60b00b01040317080041f0f5051000c00342c0d4403540107200d40d580c45205a25442c00860b205101c0d680e682c225050207007010702446002c0d00c1440000e181c03a0f40500300c025010307a0701c0002107560b441d43c2c104078ad0080d0400d04504140c4144c20344034a003140792046401540344100800000c1c1031280c02c0800c4004070483c150110b961409010315034003000c41a00094024003400310200c1c44040c1490002e0468030080209a004a6100c0090000c20000070a451848511859040d40d039110702c4001010845a41d0169130326208200c008551541e140e00503602462082c0c82c1045210700041c4a66074072403950007036a1007090f504c0c02020103482004c14805912460303187c442d19100044000600382d0b4010718a0002082d000a01e08004080c04d01c2100c0040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 44674320 1250 44673070 44673103
    0x40201021c0f0f02070815040b0105060702030607030209040b09040b040b07021606030e0c0303040605071401050408090d0f020306070e0112060b0306100516061b030606080c0703020712050a05 84
    0x207107003010241828516402da4030400420b5080070034650300800848004d0840c0030221801c0070007d00c03001c04181d03411075040705d00725607000000600f400c0142c252034109034010060318045d41c0d2114110029003050454940c0551034102c4034119840d24890540240c0c0140703411101c40c94035081801c120500079083d075045510800007200150a5109107070300b60313440303807a0204095194a40c900c0c54040d00c1c14506515000000c6c2c0003030443d82110040038110311810a050329001088408c03802c9540c211400b91281d401041040c10900e06044500e14280c818540140c01c0b2001e6008685401c0003142c0060100d005034442c0c260560f000380d841078400e54005414040c0c0c1c4c0c1443c402d03443d40c0c000034116034003c2900c864800c206a025005880f84401c0040300d0f25040760072414280064209010042400c40380b0100203481144640076410035508140c642c494a80c603060303c1401c0313960208500782d085014858012540404240c07000040358001c1004102001903801e260f030910f14007000c038400a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 44675570 1250 44674320 44674363
    0xc0a0201230a09021302041502121c050705070507080304060e0306040203120309030f03131e02030d080c0c0601170118030206130c1502150112030e040b01030204080a0b04020102 78
    0x310304005074480d404510303901e0214040155101107400c420030420613021942c00420b0100d15151000341441132a181030717084610501c2d401e190310b40707144100d44e090101107100408010507900d80c1c3d08015003040840c80c000d807a2482d03c0e1240350800001d600004515000094108103031076008100b4829444118082c011a081c903500113995507025501d5035000000120001d0b200840500c00e4a0210030103418255072803400341e1000f1484001983d08840001202c020340c0c4010105207209086070307602900405c0d9140407408240d9400d0401449000440030400c00c4c4d4a1001c4103000303c1b8020000100d25119144640000900796101e8003607420030b801e0b00c16680c0000c80e60010b192a0464200c6501800744140780c181720080d141c2507004400b10501340d21300f400c0d4080c0c5c0040d131803a0b8008000c030311943c1c6d0307600d40b050030300010210b490240c0081c0310140d40368060700d0241c1c03010545c031105040052406035110a40d82c02c05e003202e8025240c03034140c40e00304415540c0500803510718025100e0400007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 44676820 1250 44675570 44675621
    0x3010c030b061801020111040602010507080c1206010804050f030a0306050a0503061003030e030c040603030f0807020705010e0f030a0b010b0301090e0a0201050706020c0f071e05060315270c0a0201 86
    0x1050203088440c0f10105408412118964001e6002880754111242040d0b0703607544408000c3d002c1c1205943c41400114400300007104403040c60706540d200b5914083d0400c1c135880e0350004640c006006070040da80b500504001d03903141c01c0c2c00c00c01041d510a0a0300d01284c40c1d072921042001e20702035980110b0282d08260104038198114603030080c140e82e03060a200008106080c0840d180000c060103441d0010310313044020003490703005500c001c1d00c4c80e41c5a450100503954540d0803030b100c006074824140410b0080d0035281d450310b062482c0161407030000d0f080740c40001145d10b46580728802a8400a01d0050001c01848442401e015144490700550014500a9030395800203055210760000609865800310307208500e04411702044c0d0f0303044407085c1145c1d4100e0715030b5080800548000000000a1810803000940381070900c1034900c1071120006514149850909000049007509040101c0b2151046900c90700c0e100d80c04e0041c003803e9566040341e00c0701401c46001e82110200d07104e00c810503440c8540200c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 44678070 1250 44676820 44676829
    0xe030705030313031b2a0303080601110a0b0718080d0c0206031302280e090304090c020f01061e08011503060e1e01020306040b0105041211010c05030c010b03010c030b 73
    0x240c01020b8103041003452a91130508845440807515411110301d4680c440f601030114804900a0340360b50741c4000d500f130111b06000303403040340024400100455504d43c0005c800d07601440d04803080074441810340e060f4a03040e668203c1c800c0b4080301c43c0404105080000003410f01ca024480c800f8048103402400030740903000c80501880d0b44004024485d0301d00200060341808043c1c8500c1035550301500541404007070354030b0795002e101460a4860310301c403520000229894186105d6000b940c160015600d8141050088800f404c40703062410103500c500e1010168036402442000c0041070310684105594180c2c040503009a42c10758004a00d6a0400313040107020f10f6505050760072a6440f1800051303812881105d14200403004a0318403128401d603a65400002040d0001d41c803448040f10b080044007949001900c1e076000301e0260b40c40c003c4040c00420006147c5035100144070005060002050000c0ea071518038507800b20040d0030450b51504070820030b07403c0034040c0811800301c500f010b0003040d1031200447c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 44679320 1250 44678070 44678077
    0xa0b0f010b0d051302041406011b0309050409260307090f050102100e0f01020f030f090a080d0b03070e0702150601050307020307030c0609080708040f0602120910170117010e03070503 80
    0x250b032040da1400070540320040e0241d040b04556000d403051164020301c20000f1140d038400c607211400f00c0c02c4c100340b65000500c0807071901542541519a121080d0602c402c1c00000e002d41141203e0a5180c2c89a4070040700c100c0c040c220f243c80c82c00c201d05a0300c1c038201c6001001744d582c6501c02183e00541b2807003802103070b03000b1850b0321816808040010390201501c90862924042d082c1e5005503501c000b6203004904214001140300d0f00e02c0808642843d1119855035035900710310382e4050700701481405035460701e05190708801124800141180c45403500d403c3c92105012069031800007690110402d549000458a04558000e100742020703405d6241c5400e0180d00d922074100c004041100003510f04e0304001c0640c0c400100907401c07540071900c80c1c41d02d242428081d8846d0142d0400d8214803a40068080c2c400524651103000c80305d070450808444000313000e0002d00320300c168410f00040c0411619401e5503446124000d001100d00900180040c07445282142c500140b405a24ac10421030900441c500000320b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 44680570 1250 44679320 44679337
    0x3030f010b0702010311041202040b06090a030314040b16020103050703090206030705070510240807060c02040209041d06060109050603010510210e07050109090b0a03060f0207080c0a0b0f010b 84
    0xd594402540c0f004030010b1001c0f00c044850f05602060105543c0070302c60510401502c04c1c1c90410160060340d0401c410383c05095516503110103070120174000a8810407484400c01c0001c0703d0241016203510b501c100541050b994900e03409010b803030850a540e031500070242c00c521740741070400080201c2d40125800740310082c81c000030300000240e80010007000b040712014210203810300704a00440c185604651102d146264510403001c041301080c200804902403046030308c152503845221032140d00b03001c080e400a6014540c016aa981ca5103c0044544550107601d15284094441890244000340c440d08103500107a000307050a000501040c0c5411640d981198140d081c12010b0f236000c40061541c0c07030028140300c20903605006111207212000100c520540c0c42c00d03250055515240d07042d07802100c00c0c44c440594042c48c2e80d4030400214220b640189090b408070311015290a5882d00c0d0005194016011607449a0003807102a061087c0246429005603840881903115454142001d1640c003910300c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 44681820 1250 44680570 44680589
    0x10b09010905120a06050405030a090e0903090d0f060203040c090c0e06090d2d060b09040203030706051f030c030c0b0702030a030e0d12050d0b01020106210f0206030c030403030b0303030f01 83
    0x44000c84224100944e50000b90300441c203214134641450419100d810030040040418401d4502040d03d154485245100300351700030003103043c41d401104100c0c0028800d00c0c10303101c08030301c8142040070407281c0c0000c51080e80a0b280c4d046005182241c3d00b822113814980520410009030980780565860908803005007000f10781a8445210314201049166041500070380343d80f01c0e84940714001c83c111a207280c02c05001d21030402c600c00c8464240304da51101101d00940c160010045400060865440250012340c24403850306400d69407140a0407030b4400740c1007a05c14004e540401c00c1044804560724010f4013031a0b5909080820940c0802c0d55003042e0003000341400000e130a0f22056485a00c0030300e503055003015890071052482030000d805540031082c0c0789000c030308019075407000754014041c0b4401c944508002000481000750400d00d9260305581c100c40030304e10104481d02603070fa00000b03980100000440b84e50340b03040c43d1901401b00c4404c145a54000d8000f4810000c070844030b008014115040740700c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 44683070 1250 44681820 44681839
    0x120e1f0c02130209040c0c050f06040b010303050307090504060605040317120105130b060d020c0d0c080316050408011d06010918030e03010e06010e10050109031203020a02100603080a08010b09010905 87
    0xb40c51406070080070000d0390020f15241c2802a650350006001030010301510580e001d04003061240c5480345800c0f01c0240c806242c00340100f0000c3e1050b0001c50388540f0503e801c1c062952680c000806541c0c03258400340001e14003060070310600540008044181c074a0708000c2d4603042443c0c0d0310f8800310300148070b654403907030f070b0441c038211442c41ca1703000640004401042d082c0e07119085080c1700005e4108071380043c01742c4211048450110b000300d05043c001d0381c1084045080da65071940c0740c1c1048010f502010b04014040c0030028801109004500c5000070076006054621410601d4524006050f07100089490818000e624400030090b01040703001d82514000002c828414042030141c91492003400035845804000200703805102d40300b070b0241d440340e03c1e6061025900d20044900b04540d00004d84002200c0901d2806140283e004003100344140c01540e10070300d003411841c01200c026600c05e41e000d880000d14070015a0740710701454058103403501c08900b481406000203000d4415030080340e02448040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 44684320 1250 44683070 44683099
    0x3060c020304080102120f06010c02030a110d080c03040306050907060f030c05041e06020c1525020303070804051306120b0711010207050f010c020c01020a0b04020607120e1f0c02 78
    0x9100b00c80c05000700400075942c8800b02084111100801c807144005070f80070001044442d07114400200106800800400054015440c0c2c01030b030640204110b6844900d5400d0030000a0b1101c0180500305e0b443e401458680380780d070600c001501c900900b0950aa000107006100b86500700e80030740b01805891400141c1c4440000e0140c0d158469a00b00154104585161211402242074401e0548003c0c0e400d44500c540000c0c20300c508010311107d1445070310b00501c0103c00001c04210365200b214682c803040c04001190742c020a0465101d00411340780d040b0006014841401c16010300d0f000743c00f4540c41040114074080981038144c1d1a0100140310216290100342198811300828070108400d070000c43d0740d4822458400c1d03840c80740b0140d40b8455403d1841a814290000c03409010b2480f040c0c0252502c01c0c0c4940c4c41301481000200120780c020380a10000f0007045a0132442d1601e01d8154480440480301c40302005600c010b0300c00b90503510107445440c241d030654040300a410455050b1090b001e0083e04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 44685570 1250 44684320 44684323
    0x9120809040906020918071d0f0612070f02030a141b100902041104080d20031204030e04050c0f0903010605090901020717070b0103080f0904050c130902031003060c02 73
    0x80e803100e03541c09030800600b0302c1403055a5005202d850412038560540000358052020303100000c40b40003000c60307010038035050f01c0c00480e0310180c000d800c020445592207a526000480f140c005d91074400d406002c0104024280e42c100c06c1d01d500ca554140000c50030b140008400034000c100030303048000c0312000844d8030311030003101c0d01c140301c0d110000c801514007104c00c110111000f040c3d80c00050f44918142058010060107070801c031402d540c91880a4403800d2000710094840111500c416a01400745080001804030240064140c0f200048a510100d04042c10000c0c440303207440051910030780c94982070080c40a0880125100c0300b0036074038041e440380d0020f00000d0040410307900c01c6800c0361200c020810894010350081c1a03051082643c202c1448441440081e1806004c5006124441000c01030011529082c0034010b8840c081c04094609840342d408141520340941e03400003035101c00300742074600292840800e0301230602c00c4403c60441c42c1c0001c071118962a0b512000e040c155a440302c05091610 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 44686820 1250 44685570 44685577
    0x215070b0a09020f0a030501050a0f0b060702010327050601030c0e090a0201030c0e03061e07050408031204060609020d09030210020c15060105041505091008070503180705041409060105040903091208 87
    0x8007540175103544d904116002c1c2a0854050000313503c0c003444040039881034411040200005003009081c5002540198001c010440744450600d4800c10447d8581c5034001e92001e40c144a60060207103945545405030810103507030015070b10910108104190880006210b101da21740919012a980c001c9030707000d9501000c0d91880f01e07014012401040a041c070f0400305000d641e000d0743c80c109031542c0c50540491b224010390080a036150410000800703a070b04031024164125025400008502e1390f600c126000b00e034032a9105101e02500d444600081c15018407000040b240c002400754906004001041d844582c02c0c0000782c00040c14802003412644140709443c0501440040c1c0c09441c106000d001e00b054014140c1d1512032609240344624540c8581e0009004203120b0311280d0445c2c460344444201203414584910803407090110006071a40c4602030300c0304030650b0300701944d81424410381243c1090300c16040075000b98101580b0f03000081c0c1c002c240604569a100d140314800f001454504c04511 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 44688070 1250 44686820 44686849
    0xc0504180e06010501050405030601030b280504021005030c0405011d0306071e0f0906030914071e09050403080f0403050c160512070f090207020301110307030204030215070b0a0902 79
    0x400c01080e100c00c500960703000c00d4000c055082121031503a40d0300c1c01110310384620f01034260940c200d04010000940c00d25001d80d08441034803030300100e015640320006a1600c15400c40b0161548030380500041d4180401d0130000c24001d441c24900c1c51902c0e8007414214441e511507181085010380041d09460050340103520f8a084c0281a50028100880d0003411102484011902001c0d900200803401e4091034a01544400c56200c0c01d601d24070b0f05c5020340007003c850900341e490b4444128940b41c5004184400405080019100304981c1d01c407101a00007080e06e60810004689041d0074080403e4200c60b6040d840004c40c02c0702c0c0324684d00d500d4101c40798040c00c011000c60b2b20500c02138002c8461010511415943d0540b00805a40e5030300300d4065885d41a4441e00c5a030107044003041c03101c0c0003aa002030440d980050004288001c0500d6100c005500490f465270009502190510441c50b020328a041240c1480c244181004640e8956102d0520068030340030078641e44040c0c40782191031701300c50100c601 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 44689320 1250 44688070 44688089
    0x703061e050a052412061018090903021f060906061b0f0c030c090c0e0103091a07031e1a012610030f030e04050105010c0302030702100509030609010603110105040e0a0c0504 76
    0x140441d0620722560001034951900c9118507c00440c201446616041c0ca80c044078002c0000305c0e40341015040050084510690444c021212b4a03209086007459020034030800490000e642464201c400c42100c201d42c12000400854801300c00c081d81103101c50403440c03900b10105115040041ca000c103038455940d48000c28050540d40300142e03403542c5134455588c07401961a142c008021110044048900d440e800411204069603000d10440445403819804902401c0c0000c82413048049180c0e445034071002c0855858803a001580038000c0750038030743e5094000382000404103070310110b00720050904140070824081d1400005850900e829006c10007107400c5141000c0700041c07414010000ba0280c20820300903070a00300002415446520480070064040e4041c505056541c1d080080f03403d20b14403020100101440341d95542c5c1d8003400a07501820025000060031440c41c0f03050a43e086094401d6070500c01c1c148001c104235a41d940396103602844054000802c01002082554940295008102135 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 44690570 1250 44689320 44689327
    0xe070305030306041d060a050601110f01050405070801051b07081b0102090909070609090b031005090a061505010c0206070c030c120209010504020906070813030b0703061e050a0524 79
    0x520002000540c00742c4011307201400400b01100201c0012002e07600220f03416030114000074601d00e4240d200da608040149041701004002c11070b0b1034904104603000c08503030f075528410705c405c01004000c038a000307140040080c88107103850751b065001d89071071000220142c980055914200180309085411005800380808008164813070407034003e41010004038040d0b035030400414030700c0b480002c0070802c96074680d80d50540541400e1003c0e0141c88401c10380c9805106a0b424001e0001c000c1c014280308098900c000c240e085113a08005081d1074030001c2e403038400100007505200613640205040542901920019075400080c5007207041d00b01c0303d91028108003d11540400c01000095880d80303524021070311400315903221030801c0120f21600c8401c0d40d1014042080e040024007800141c460310340c0d504210140c15540e6220361480201c126000303000295031b80400d000d0070590a00c03104281c0c0c030306003607202c4250034078020950454490040324410304128520480e9003000c200e00d40c5648001404180e00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 44691820 1250 44690570 44690573
    0xd11120f030115031401060e0f090c0304170a0801050d0f061b0207060302040f031b1203030c0809010e060109020d06050604030f030305090d1d1f120b0a03020607080d0e0703 76
    0x4103070030070f00610400000344540c01041d90f100f802940d054004140b001d0b9010791814400f60380c010511203269410044100a0810b6030740c484100070b2003400c0083c1c0719640e92070940381c00d001440002200d07009d000c80900ca4408600c1d400740b60380303064a00c203540301d84450210342000c3c52040e0b65000d001381f01d181000140403104040340e44040309906030b07408440c4c1d1251980c2055060340103600481d1002c90613800100041b502440500012407854164054041d0f1600c00321b0030280806801a80031940750150110701c9540121504e80c4444000020058030716000341c000e07100d0304c045c4915003d00f0f4020034281c1d0740303503210350001d0000c01000348029a07482d500c1ca4030500c071100b40c1209501003443d00d000a254800040307514a180030302d960f1506410380c00c603031402c407800c2c0e00c00c0d00140e008507014a000d941800c0c03a08070752658202c103448480c0d003e003007050354606a9511084260003000c03c3c00741000141c6640b016528004d6101400300d0703c94400b600384100500b05c04003143c00300d11801c8c00000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 44693070 1250 44691820 44691847
    0x1050d020c0609010c0f031424030601080601030213050601080402010315120308060a0b0c0604080c0705090c0c0d0302091e1906080103060c05030c090118030204022709040201020d1112 81
    0x520700000f5107501d50f07048182031b010b1b02181c01c038914010315061302c0000105c0c20700c0321000150f604403050b006410301e003c118021070314040c0242c0200c1e400c0d5124a0042c030541c500030452120710140341c03000340018070703080d80020110300380908024189a20b440c6450125018484618081c01302d10881d40344003030042c1801049071100341c0d5414007a0310040c00c0400c2c0c012403803040b0380e09188041c1c020482915140e4800455034012100111503000f075800c0031805595081c801d81c010354034485807903103a6100c0404c040c20406004403290a141c41000204c0440c0c640100300d9074034413940303a000040d51004802050541d10110521030289401410202d000740d005111941039078003c11040002021504c810355051100b0b54901d50012814003241240d50b1107034000b1120701c03100c6550300014a50340c1d400308059030000c041c018038070103d0901d4054010101a552282c2140888540304d90741010f40010352258403078081b842c100810000c0394404054108040d82c000424101000d5961140c2220300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 44694320 1250 44693070 44693081
    0x20301020a03140f06030c10020f010f060602010b01020c0f0d050f06010e040308150a090203040303020d0f0605010e0301060b12040507081902010806030a1a090a020604091401060c08030601050d020c060901 90
    0x80c690400c808002c24030203040465a5072003048090000e0040703c054000b00464903071211074403403c41c801d070ae6001c80303038040a00582075000201040410001e00b0440301a0940b958a00da65046500c0390b03885e1121559078400300000e9210688944d039115000e410a1070501c424400c0c1103003a03118030f800000315552035040192103140a5a51315015454130021082100360300ba070601e900903041c00060210400d03d50003550001e00c40d0030014541500c4e0000001034440030100c003054290307503410810103035800410100c542c0108500810070789040c001501054004c1b020380d45070025090380090108442004a48040c041410071580c0300105402c00c1b8150101c101403c07800100c44d2000f090301d60400241505209a01280d0b0652030311074501d800d81264002001c2c0304287c4640707034034000540c64910080010b0140d000300031404c0c9010f01c0c41c0400610060344410304111010035090003240314441980d800590902c0c0855403143c115403050003074054070341a0096405840d0520011401c1540030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 44695570 1250 44694320 44694341
    0x50d03050606030403020606010f09030609050a0309090209030a080a02010b03101a0a0e0f0a06150504090e070b04090c0e150a02060105040506060406140c030403050607020c031216030309020301020a03 88
    0x1400641d641405008a5000c2a00e006000d40c1c804c2d0081074003036010b9041502900581e06c2c110b48020360b00e44034802a5600b81d401a6040d8001d02021410316501140c0c1c14090041d03a03d081d8075208101e0046541c0301c00150014180c00c10110310301c110305200390044104490000c0c1112005601c0402110041514400c1c0400c400c094000d02401824024049012504d80310a405419074801044031415900101644442c1c1d61390080400c00703148581e100c20300c1400550300e06458900300421441200c2090320036881940c000103007003144440d400c0803542942e071615008141c41d05812400d8415880301100c0e01d90001e60b4403480c036002415a009050208102d9080340d0741c60760b881040c04100c03941035a1403500b008042000303004550140002001c00400d0300c812618020b00720600d2425904140c108031000c0d000780080c07020301641040010301d0100c0c1200500b026140e001d1b4040c2040c4502e841c240340c41c1100102100500d8081da110054898001d0000c0d07648400a50005000300100c840 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 44696820 1250 44695570 44695577
    0x50d051e0f0106081209090a0f180b091605011101020c0304060e090f04030e1002030903060411010f080603060403110a060905161208030c07020d050d0c03110d020706050c010603020904050d 83
    0x2d240d20700050003030208003441300890718020b051424007111800023007440030405c2e10752420070050f10051040d040107100401640317000c0740f0745240c07104520070b002d40703450035503840a40c50519980304500075104030341003420324400007521245480e000e030040b440702001c1808003044c001291504880910040c0b00100c1c3c18075410f40c0c4220f890b03941c4036015100580002d181d40001411424030071036100a81d485030044070b0400d480f000c0000e2414500302d4088030440050105061156001f000c0500c4010135410260020301d40b402c042566041e0061000e01040b480e201080d0292070240304001070990070000a010410a0341040c9650700450b814a00140f04010400242c0002030460442c02c158400c8100e480c507241d071000503002d50002c0901341c1c1c1c405654442100061003c10411410308640e0b21842003000090030081c0c541c00f120038080030207400c40c110010320581e01240748010340d901810200d80f503a040b440b00c103006281942009402c0850001400140240003641d81240c442603503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 44698070 1250 44696820 44696831
    0x10031e0c061d01050a0504080703140105070801120605040303110304060c0e0607020a12022107050301110711090405030d06090209040608120313030e1507060b0303090307050d051e0f01 81
    0x5004407103040d07a070b1040c0300c0307072a400344a500159031241004120320403061900c5c5040c2034440001a0400307107241e0041721418088840f504261034217008044e4080006d0a02954940c542407681c203441045000041080f940c48001808140c003a90069511805c542003950301e0345418a07090004200d450362850200715400100c0701507260800445021a50207409900c0c8540b401324142161380c00385400304c1c7d100141d8011003400003c030000c0b10018140390401400406d107050141030031a2041460203003145810082480814800c010010988105450040303241d40d5a0034a1415402051046030b842410040001028130040d0060003284038211002c00c04581d8a02185950302c0800480c030310810014000550b10b0001e01140301380060007400d101c1c61440441e4001111030743c286000c040c64920110305881400028490106000b0313041d0011842c3c0000c1d440040d80e2356000384500d510401941030300404006017072028044000700911240c100c09503030b640c1070b500c40f2200c10701c130b149541c03804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 44699320 1250 44698070 44698079
    0x304060b04060f09091e05070608010504020301051804020109031b0608010e040201140a090b0a030509010b0a030c090905030c1506150316050703030219050a030e0609031210031e0c 79
    0xd01c900341c1140ea0514083e40f11619221620000e040c0c103040907038038000b91460f62600c0d10700010f10592410312500151203d21300f007040c050045074068000b603003d01d00c148010700c01c648921070140c0c25410014850455940d403480121624490750b0401406140107124446040a40e102c41c0403c0e00d1042d03c03200a070340e1301e0380c42000c600001294043e0000d00701b40f0348018290701d07105c020081d002583c134241003200d407140c019540e603901c001c080d0000a5520b008120440380c0c02e04ca2001050300032500e60340310f1031540c3c031880c40d602e106000d40049180c0c2c4513421800c022040045682a0340004141c50703400c0b00c01104c10201c604115401e5018416451070f0081c81c43d110b4040341d00c40c0030040440c195000300440101c0d40d03904500d400302c090682c20040090700a0030f0203101e017641c03601a40d07072170340c0c81c140ca0750300a06440c0c0c040d40301c000b00c0d8042402e01520760070200550b96070003207005000803150790b0034801d40030041c419803003d030001c0500c1c04280e480c8180382600c5450380e4003031000342200c070b81d44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 44700570 1250 44699320 44699329
    0x6120b01030e030702010c020315040302150703020c10020903150f06010e0d0c120206070f0501050a1505010504031106040b0301080303061801080a03120f0c05032403120f04030f080304060b 83
    0x2901c2d10159240c0003040203c0066000301c0843e4070090025048031072120408520400000c425502500903034040c60124121124803c411036224040e89001e40c14001d03105045540d80161004070041c0c0ca03004110000c0b5610704000c0400d140d000121358851500b0014031000c0500c00c19100780f8001035580c030010b882401c100c0c00304805142e000a07d080342900c2c0c4000f180701c07100c4244040368444400c010303140201d041a0301101c011806540001268181800f0342c6007110043d44180c0c02d40d69101d0b0701004030b030f030b00f0038141c030122070304200d6800228018000088051140740c209a00d0454003000201d83c2c03410000255100b16000d640790103c007186d14000c1c98860509200b0003945503c103014201c00281304154180c814483c0103400300340c5041c00d242c12810340344a14003440000d50040204420b504909040400c02500c500302004841d1001000c261184242c10718501405000079245401d80b41801c1150000d5030844059112131025190a05103a0700940c0c00703441c850305140f9801c005140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 44701820 1250 44700570 44700581
    0x708043315050d06020901020703020d030206060901210b0606090d150f0b0a0303030c20010902011e090b030c09061c050a0b130c03022203050d020f06150303070c06120b0103 76
    0x2004010b00e00c81010f541d141d0001e0751001000030b046025800c0d001005850f40011002c20512035005011170303151640900c1400c2205901c401c49450a07003450003403850100f203142401c90381101c410f90241c0e03117101c04aa802c1c400c0008468105208482010030b10030481d568080c250342e8990180300711103038400400156400070440e01d6000c0410302003003001074040e902c10301034000d060900c4d004859484c5403021200300e006807000d130030ba515850710038219030388841c01980c0001160720354600c9801c0b919004003242480d0003002034024000000c5500284803005440078800001c085d603036101600403038600000125485800c420303040c40c007c9045801c5c2ca0190507202c140180042000740c0300c0e1844d10010304041c0000505141d401c018840001455200c0000300c4032010300f040054a00d1480c0c280e00d01525184203100b150405048800f240a0205800e0b801031190070005504551aa0000741540b192440041c16891002000604641c01a10b0085064002d4400f0850950540015010b030361 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 44703070 1250 44701820 44701829
    0x906020709020307031e02040906060206042a03050607020304090e0a030c03050912030d0506010807170c0f25050111070803180a02031209130e03030708043315 70
    0xc005040a016104440d8080c5903c04110318005c242c0e60718900c0449051030310400c3c6040310302e0b00041d043c45620300500036140103294610040a4514203a00c4210b040e0907108007486158000034800442481800e001d40c02840d00001507442d9401e00e54000b03903882c2d0141c0b090140305801c0180c0000102e030046a00d03406150181c4a080300c08034036a42c01c030f90355172000701c9040d032240e4010a901240e01040026002040130300c4800101405c1000c009414038000030480d404021100c00b074003c0140c1c45030003050b04101c091785150346038405000c07041628040c41c001044074164201c1c140d1041d02804059000c032900030402040314003001d031810180c521900c0c801400c8881d003000811200b00b1224030046928a0300001d582140000343c1c006810000c003420301c600340312000308116489203040000682c01400d280002c00c40242200b004079101d000c0104aa424420240700040a004070405d015102008040c20341802e00c05c0136018480c04481c0100c4201d0712880c208003d4a094545128a015103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 44704320 1250 44703070 44703073
    0xa0c1b1203031116060902090a0209061e0f03040308070e010f171008010507020703150c0c02040c0c0b0903072001080402130e010603080306040c030603030e1c050d020616090602 78
    0x610944050b40078045494090060b80d070100050120419451044000244140b0001c80c61922900410950717840c064030b0710001701c0c41002108034603503e4104503211900d408030180c43c20380102481208c140141103803000040c0c0000204400c16030301c03400c8030784100000d4980811010080e030045904600100e1030b88045114244a480c0000c43d8828066202c07003105c44660040c1d0322510700f00e003512010342d8018090307440300324107000300300341c01e480d1070742d01d480020040100c2d040c0b01000401408060501078020755850300001c406a02c41c815007035950b078110315190324908224010950320703480003034255070141e50000c0380c1d008580d9034060b003e8213040584d100c000d00d41b510340800c40030560420341c0007881a51180090031800b001e02827040254051020319841e85020350620064401c111500320070145416400d10000f5007140380e0710700d650b03800e540790380c41940140c40034400c01a0019014080c2d20071a44004503455000404502c120070720481c40024200c002c0050f0b940c00414059040503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 44705570 1250 44704320 44704349
    0x9060402090109111308070e072c0f19060e040218060a020304031209060e010e031e010f05010b09010f1d13110c0c0301151211040603080a0c1b 63
    0x1441a50400e8004d80301600883e0724044504c0211a40300c00a544410001d4020310b800300100b06e203502c61036030b0100031070074101d4149004140400b0b030580c1600b101403101d00044500b44041d11041182c001201007c0c0008202d42c3c0074440480b165203c0c0d01c11400040c00e08405880e5504060080e2400480c0c0c1428002c2a1541c40003042003903007006001a0852106010000101b20310031502d422480c015154101d01a061071030040454000822042c140402030003031b807010340c0300000c4580c62100d13000031b0100b010400700c3c1c0140c05046620400041c0303900341800070030f0b140c0c0d049008280403082603c842070382d00f40f14503042da4201d042d01e07040030703840c101000d0890007400d10f07014540c501c1440c100001050302004c1450341044c3c00012981005510291101440b4107003403094a5140785040c62441d01d1514054038200c1e5501481c1d030041000440e1b03e201034498035180c000c2c101841d404441d00c0d80390b50410500412050502c907055407039042c560702d09081c04421011040a0310003d0701c0507500f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 44706820 1250 44705570 44705579
    0x3060c0405033301060f080604060602060a1a0303070813080607081b09040501060503060405011a0702040209030a050102040b0310050a0506031311031207110303030105010507020d030207030b0f01030506090604020901 95
    0x19050301d9000f40c04211001c880d000c4410550010009010b40019110300210884404005043c030000a05250007140b600728144261a00000c0c556413158440b074021480c0078810303203842c40030090300c82956014440842c81c8000c02c42c201014056804803800728114443c3d6a0001c246d5518007a5881c80c0800c80d4500400c0d8500001e24116270a5001c60041514110424000c038080310700907070181c00081c6011050281d44e00d05801490f00400d032410008502082030700081c60076202d01c1ca00244119400204a11b5640381880b2034800319070010700031502c0c0c542e102c281801d44d070710458150385007840d8120046020b2410308a00015250701802c0e2038207541d00c40c21000403a45001909035400c110900090b489583d04000116841042e100002d450340071901c4c20044001c9092500ca10981003400180b22a1740e01070b0582d58180e80490f08241c04070000d0409a0500d207040d00040c007900e41c01010080310203a4171048904a034455400c8440550759044150b450b5682a10f009600884d400300412 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 44708070 1250 44706820 44706853
    0x1080712060503070b0c0c0d0309140111070609060f030203070504060503040204090f1b05040608060703110408011505010f020d140307020c120f01270602030a0e0307060b03060c040503 81
    0x482920400c04001015616400007074900400c50b400704108000000d26014100b4051103d01c040c0002a5001e001c5544181c1d4050030811485c001e91411004103021503149a115001c40d800c040e103642e0070780d1a900d488100003884180a8011407000c41c4082c1d440006562007031085030f00c80d003c0c1d517884500f001c3c00c05c6401c442c0c0d40c0c40a401a42d2040e21001d4950210f5601c803880c0740c016101c0e011a00041400802180e030080e0aa03002d01c0c8035918000003044401d80202e03406034030204034a0001103203030b0704407142c50b49400355400c40070304c1e5803a24030180d0324080310548a109030703202600d54110401410300c0803640c48060005802c0000c0c1140741005031040c20074040d54114041e4010380f01222100804503100504107080c0300f040e82e0103074180d041201c000f807290910001095262541d0040d0b880498002c40b4840e1100806d0242c1c008006802c040c07881c0c0c803900b21030001c5402d40e03585070603d04140001c0e1928161345446030180c1ca000c0350100081404950807034001134082d003040c901031031a20703 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 44709320 1250 44708070 44708087
    0x807090902060904020a020d030b040209090606071b03050c180c0a030c0207150804021c03081603090206030f09010507081614090a08030c0106050306060f091509010603060512010902010807 83
    0x481e0080000c1c00803240a64550000d44106029a802408d452220010040542e10a041200d02840c41000454516103410081590200f8180c0b141c0b07540790703603910f450510001d03001440b44c03524842103800b10070000f012540180f9011704550348508841d000d0ba404201d0041910110280081000346030900b40c020b81150440a1312030050301c0340036035101142c0a580101c1c104a000107140d0008010841c5000a42d04070181c44040110b80c45c05540c5d45e0282100300c0c0a08074402d2a2100e410541d44244030b5000401f880307502410340d94490400804000c080310f02901c102c40154200000185110300c0340600301d20600d0140740d0a03120701801030040c1c41401403045000003641003005403003030340d440d5220345400608a0360011030391210059a02400c42e1a00d07005240310740c01070814025140d40f078801c0c2c441e0080088540c002e2684507100c41610580c9143c0e4216000100500002a8183c05900c088120391064030b03d52107507044d0406031800c0791038540009006c00c45030307400310703001a00c182c151 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 44710570 1250 44709320 44709323
    0xb16090510110607022b0507020105130918020306070201050f0a020a030e01020403050c10030207030806090901020705010903020d0e010203031918080408060105010f030209030604021522030308090708070909 91
    0x3808500d0107040b602400c10b5400c036154409030b0302003190280303540c0300714280c1081e0146d80664004d140d008094020558401e081010b8100700011414441c0514580c0816004100c251800c0180303280a01021006a00740c40c2c00743d00c28002c100000303c0071401806910b100d0203180701c0306641c07503a0b5512110003e401103c60703207040560354031086260790313002d00c001c00145010704e00a00110b034508080111901d8040321308010940140f000d48000b0f40c0000c3d4035600b081c0115001013842e940d641c1c01a0082c0105107002d0069801c000907032052540100324100030904964490380041420700040ea901c3c070082d140c5400c656082c910001104009a009907241d403c0c1c6402c400004845450f06800382e0041e0301f0003002c54001000400c419a00304c041c10350480810304066052054840002c2d07141c8030010310207405001c01030400300070380642404641140803407541e0015000f010594501e0a070410f40000c071b0100d8014804184c0616000511104a959a4004001c070380e04092105000e011080c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 44711820 1250 44710570 44710577
    0x121051c0c060905060907150804020f010c02030a03090504050c12060405040515011710090503120406150801051603140711070b07122d03020f040909030504030b16090510 75
    0x76000010300c0328001d01c1c20740e40c0540010200c9040c41c080480c00c1c08400d0703001c4072414482a003247d0b1a076400c2141c441d8410780456201e483c65954800584410041d454000c0d4075008080c49001015004544002510420303070f0304100d40e039501d903920760301413003090160445841c0840000300341e07141c590012039000d442030042d5180c059800c840d0101024083c2c129000da1620780040300704001040000b180c1116200d241072000c07501d55160542c41c0e1040015070461108108006000c6c401c0740e030481c503003609840907420201a0b455442600a0409407441c0e214400342c8405541141d100e0f005101c001034487d04141680e0f16540c40a64100ea40f0072070b12000c40c0201000003520301590006030070068000d0500552001190303000401c00784c1c60050550425506c1800d50001a1100e488406140c0442c100166242415148542140100c4e07108500450404e000c0c03404044d40507016100316403007500510300c15120710b0009a21140e03031008100c0050046542000103242110242440c00b24070304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 44713070 1250 44711820 44711837
    0x60506032a090a06020d0e0901050d0308090c03060a090c050d020f090403030b100507030e090f0c0906042c07080603120306040f05010312020f0708030a03020a120606080121051c 78
    0x800c03c85001940b10001680201c0001d01400740c111548104021048900c0d104641c1000c0010301c54801c20790307000c0c04003d14200007035810748040100a05001008044417081d00e004402c8401400c84000b0468510b08000400103150030020012106150700510100a00040030184484494001e20036010103854aa07c400349880d20f50003400b000303105545d0240d40b500d040c01c0142144c4101da58450143c0000302c01c0001030040030a1240d00000e07400003441d80c4030034000014000340210b8002503c201481d00d1b100865907400c0d41c80321031007170743c05208960701e6580304420360702c2c800101d84068054102d200101920104400110f51084004200080d40008503106508440003600221021034219543c0b440c140d0b01000f00c0c801740c52042d0b000f441d0f141e09280c111030702c0b40103106800040c15004600d2410313503401051007e1001d441d021040020a40d90344000303000d00c8080c82103150700001540c032581c0c14190400085c10141c0c12500030b0170155020409005604801d4910360100603011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 44714320 1250 44713070 44713087
    0x3050409090309030204140601020d080703110d0c02070b071a04020d061b0801080d09050f0a030515100603020708030718050303072f010804121809020706060506032a 73
    0xc0c070440e440035001c3c1d41c501d080c640c01e520520040b50001c5036a1035090303c041c4c0401115a034000307074035000040c49160a842507161103078190301910300b94030401002d14011030780e01401b003603607406062401610707401c4840c541d6403000040c0e558801d0100190030021501a82d904411030703c0c002540107032014043d00ea0101d65a203900085994444010f1980d000703010b254600e6030383c070001c42400b411600029120326511202d0140840790039104250042c8099405a0301c03540e00c803400c0400868101d0161100c01c2130305003150500b8030003251003035941488114041462446032081d035078080d41c40180a4138649881c0c1c0705680340d2070b04000013210810011008a4103850901c0600a401e104050110031952154144183c49102c404614030a00f02c890440850f80c0e4412203490b0401d0f00802c548424003c5000c0464103401124002032080c010040001140700040d0300070103506004000030003241ea1181d080011600c025174105100c1e08601e4003140e02d1002c40c129040d07481c001090a10700d80303038a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 44715570 1250 44714320 44714339
    0x607082a01090308010b1809040f061806200409021803100c0207050603040b0705071103010501030f1e030f030b0d12021510050a03080d0e06040c0503100b060a0507030504 75
    0x100103500c0a6511224200105500600068050300340c1e0044981091030301030b688030f100c0301c110740a20f115003000c0004c1414001c5550100f4421500710a05000351903071416480c2c0c0c00e00c0d0441c81203d100703160404107415424033200380d80d0880176103400c50745448d280c8076201010350403c0700301030070040c5070700041001c65400300000c1180103030148000c2200354800401900f04200d550043c0e020751020801c02c4001021a03d5407580320100e424200e807a9540c900b8580250002d0300d001e980c1540c43d040021041c00180d540d81e40809200e02061003110703189080405d150728407803500030007060303240300e45c000c03400e00036088401044400340042513000c0840d1541e48103100c0030030703100c0c001d60016041c5c4141503042c10b1019501400a002d5015050700e00008202030558604c009041410301103107820340e003441500044546040b402c12203140d03003424105054001c2e031500c2014400c2c80b400400b2020070201e40103803408030704024121070400450302010380e059401154103e04201c000c00010503100b41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 44716820 1250 44715570 44715637
    0x902010201150816050405160c0305070803010e01090501080118020f030a0503220b16060506121c0809010c020a110a17010510120809040e01060504020f031e06060708 73
    0x2600000e20341da801071100326401e01c0f213030307048075015a045c00b040011408261002c18030040d2140b60041751500c4030b08044502d401182c4004156000000001074404242c14a85050342c1c1150304c104003907643d03031001c50300300c8000d49031140940703000742508030143c5840c040c4c168034940042c0a803490311101c1d07a81c09003582e2042d007000c1c018140a041a44540309160400e0f0084c00da000d5005144c85014401007149500001c8002c04060701e0310001509a21000140c0402c80c1c4050220b640300194800f4a400603040184003800280c802c0e4005060342c04140182201800150007400c01d1008544a007008120300481035504070404000010740c0c0402c1e88090a0400c400e680001014100003503807030200116030b0300c00030360084c841400c81c0114503074001311078031001c040358002010703e202d010160141019a1050391700c07030300c0070507000c886401c8080114424158010031a03903060364200345026100c0c064a413160001414400342c40002c103442c00034100358920640c940c00001e5030003c020758281 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 44718070 1250 44716820 44716829
    0x212040210021e1b010906051b030d06170c0a150309110901030b011802030106050f09030a05010e1b030106031e080c0627060c25080301060504051009030b0406090201020115 76
    0xb1300501d20303041c509070340403481c1e81d200c1000d01c1c101c0680c920b070400041c06802600b000064400c03500e50441e8601e00204216403031003c030030b001400b44c0780d035907426516450f4a401985155000e4801218040d144c0760364503a094400040c0c0e5209c3c4542d01113412802000f143c03000322030140c54a01600415603941c5000d6000303500c550300b0340007151305001a10102039030286903034044500500050244a801c1001d540c0141d0003180c0c03c50322005d200c00001d180800701c02d00500954a4a004018194000701d1030040d0083c1e0000d690b01e00345010410b00d800c0301c0191001a1145c42d0800440681a49a603044003e96009040c0942407580101c40b41d400e00c9000e4900129030305e4138007641c000d0500b144101401c03c0c6000030242030140380420f2107004510540d01c01240b810100043c60b441e0581e03000000b202c243c1c1102c01161a0360310b6840c0941700740d00a010b00e07803090020501c1c61884512511500341039981c08411a2207548036a9a1540038201c0203604038150b5485910202c98882c43d6240d2a0062 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 44719320 1250 44718070 44718073
    0x5040b0a052a0f0f070317040507090c0e0a0305060a062102150715200a09060e03070b0408010c1710060c1104050f04020906010f0503010e0406060e010f0302030607030212040210021e 80
    0xc03005c1d40b802800070301544a903210b411417079804000220b5030104025045600b418004a0000359079042259103010705542e1075071000c05490040b0601800041141c0b00709100d40d070402200d52200100b0b0040b0484100c0d414540c186c83d00300c00e0060808201c40c480c0003400440040c00c00c6429910b8409207106583c51200e41a07070b4121100711482d0034005031080079a510111441c1c9245010020300804540c050a01400a19030042c00c2a403020840d0070020030320050301903159034494040502a040c481f0002d00010010b09807144005540d8244c54007401e90707005001001845c1c00c84c10341c1c0e000b0140c0d00646080607080c040e15040d4076035004030783c0f28207818048080c1c01c1c5010706c10040340d00d00c040d01d528100510b560981c190950040708407415141c0c1c0305016082c91340c0d103240000107016541c1152414507855000040d801018010318425a0301c00c030240c43e1a07070340d242c2d4110200e00500b0f040c0c0079000302c844007007009070400081e405d07124000b80c419913034070b05210f2600441081c9038180d0f40030075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 44720570 1250 44719320 44719327
    0x70506070801030809090627040b011e0915170a03110105010f030b040503070221010c0203030f040609060905030f0405120708121303051005040b0a052a0f0f 69
    0x10004140101a03022015040144065056032100d0400e0b00606100a0040c242000800d009541e00081d03240d90050a952241c03000c0c075000705209501d202a201260050764000010030201e160a540f400b08001b100c0b4400e0030b29162060074000f91405440107000d0400e502c00100b8080d4040c0303184040804110b0083c09a42d800d8540140b07802600d0410030707a01c0e4074220052000d0348103070752a101100d4100042c29034030784560401d035003113104119000b9032110b0a41074515100b1b0303801143c940c038413840304c008024581c0d80c1c6030140d07280d100c03c80f15410a00e13035000c001000281254010303800d10340a03a2000400e00d140e41c0e2038503e541d1044180d29030101012404012074500342400340c040084440123040f010f403030490880e42e0740031145100d103000715020810043c580e040402010003150007008a071f040c0d84c2c9803840d900040c1301c1581d00751940c1200a0004c0d11282e90f80c02450300500e072202c458056020420302441440ba180c018000d030b0840c08001c416882da0004020701080c8045a13602c9aa = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 44721820 1250 44720570 44720573
    0x1302030610020106030c0501030b15040806071106010608040305030414010e100605010302040308030402011b0510050a14040201020607080907120813120804052e020106170708060a020a020a12020307 87
    0xd2401d03594208011a8181031003440050501001c0740c0450b80207090100305415001d00045071110354022011882101150008141d80d00150700c0e070150809440d120781d0a070801c1d52541d12030000b4051000807640c1c0b00081000244120025507120340a403d1401607141c41904881c00e46142d110003242c5548800301440303c880c442d11403000101824201149041c1c0395965207081c40c000100042c0c180010700c0d070142e802c1040350090040c055407101c01d80c0c10000360901103100602090f108814140d02c4d020341d0400500301c00c0400c6000b280c0503001025156603601c0200d40b042401007443c81e05000e8810001a80c1c5d0b030954103400000d10400c2466210840c25508001d141c440c0e5004944e01c0184103052004900940121416584150781200d001412500c513600750f0f5a04069490000c45104140302020340d0640c00365060380c11785640903982040340d82550359259903501030304a03030f600804c003c5942c2e00b607198010414014540107035039019a80d51903246100808003000f0000d13820003e035440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 44723070 1250 44721820 44721829
    0xf2703060a0e0705090903040e01030c0603050c0702130c02100c0903060e0303131202011107030818010b060f030604060305030418050106090f09090c091505010e03010212060910030213020306 84
    0x541c8080c0d8203204100707a101003901c90303941e14098441d182c01508400042a1010341c1072003264003420343c000912401c0d5075245401741c00d207400c85c1b180c0d800192502001c10042d640300c01c200e41400d41c00410540300f2400c0708910070001c145020a070b00561041c044142100c20140c0140d03a107402c8240c50303488000b0b03d10f0501170280c610b440221030250708100708000310354071641e824001c40b17a04440480c5509e0302540c8140c0c010900e00309400e00440f00801c85908142c0e0090005e48506c1c201030003c803015441214450076101018003099203d1024480584160321050242d503201d070005202040f583da913902d407941194416044203250038502540c022108806d809070900410740751600d611070314035250780d810900089008044003991102d412605000c4c0c5005280d000d400340c99001c11130350039070440700c004070106031140902140386000140c1141c9410b03c29039456903040c0803003144581d110400c201ea0080d0061030287c0d00b00c03c000012000d611142c0c1c450100d0442c80c000180c0d01c0c20682d0410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 44724320 1250 44723070 44723083
    0xf080d1d07183e040e0a0b040b01020c01050706090b04050607090609050306010302130b15040f08120904050415020a080105041a03120c01110c10051e0103080f2703 72
    0x1551160f0400d43c83d840c1801c0c1c00c08080d0046143d45034080e10399080d040460021200d10400003080d5080401c02003241d00d20092030320301891072500100042c00c50242404240e4010884841c0541c022002000a6501440c020051244210300c0024412601d03902e11904030801e071010380d010313880380040261107074000340f014024041c0b9043c0801d03058613280c0065682c07001400028081c2c0200c0c00d80200710140c1c1c1e0028003a50100401e8030558048290005ca2a50002d00c42c83e41110540070000032490400708458803200b51540d000b81c41c2903040c40601c80600030240040b00d502100400072600c01c1c41a01c05425207400581ea1548954900800c01050342ea209a12841c070000c0c4569552255a0000780080020480e0007140d441d4004000c1c200e0042900c110b40c952283d0000880c1e8021090208184042c0384820408201d030f600c41c00b400c2e040c15008000030705444005d100060021034052005000b0348051464841d140c808601c0303110301090089002280d41110070504242c6518050086 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 44725570 1250 44724320 44724359
    0x7061a010e120303040813090903020a0203120c07051c080403030306140915040c020c0d081213080403080c0106180506010f08070e01110709090312050a06030f080d1d07 74
    0x70703034010b000081c81c00d07a16884085e0005144c80030001c0c070a2815090040d0880090941400c10011080d203824060746070465080128424043d0010802c180340e21039007a10008076403e0000d2000508050074480e450340b071042c0301d68040c91250454000108003d0080014500c83c0e60042450303031a1032a00b075215040c54070a40d100d40000303420072000900daa0745c030030784041e800c0780c01040e910040705017030381048025028150081c54002104003440204001004030201d00840344a0f9981c0300c1c4030000d8070104110004111040c200002c101082c46440a4001602880000195140c0d14032124a403c0200145607071101c0d03d44c0d0421040c3d6800c07100c8040c0d89003150402d1056480d044c20020314116500000c5814007d02103034a44041c002080780401a0640440421055001d07003800350400c20181103400c80c0300d0600b8001640071456006481c1103d034070036060095001d5581c3d0b5805181c000050030800b107075941c890810356064031120700000120b010041c101060038840c0b41c08641e0300d280c10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 44726820 1250 44725570 44725579
    0x3100807050a06141b0d1808010507020604080c0705040903031a09040201090b13050415030512070201020604060506030c0a0b030601090b13050904030c05101a0d0b15010507061a010e 80
    0xb010459079400100500510b840900c00655071042c0d9514680742c40b101783c803075800720703c55903a4401e207843c3c100d04860340300e0007506d0b1460300c01961668035509a40f01140c0040040c0c2201010600140001e805061100da600096a0180e500c44010900300c40c15010150002519442c0390046164900d03100c030752609060f2810882850203400107400303891103104280c1910000114070402010b00d452030300182c00e00400a00804192150300d9411045a001c240c071640504c030810624403010320212292250306070040c1500e0350312501c0300c00040c20002c1c400c83d0107000e010804119980c501164201420018601035242d040c454001000400c550f000921000c4c01044040041d0f0f50415288045403000c80e820446a0b81d1703880c0803680c0c42001300d0024810f00c950419020720910030340103c1641850070343c00a41c014400410010b4500130103070b018110004000209402500c4d000380001d1400042c1002c6280400d20b42c0d40104444a80b80c07100718a107030f160268009588c0c044180307400e2070300c12503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 44728070 1250 44726820 44726839
    0x1e020102090f060d0204050411070c081c03050403030b030a050604050d02012009011b05010209010e15031611030a02071707030201021c030f09030201020c0606190e060310020310080705 81
    0x180460b50a203112112640314641c04216441e40d0040703501280c001e07000180003403010080360003005d03070b19800c031443c11115202401d40120b00f15400181c590041c000850440d40c95030707100c800580013040040c106404050310f4078001d070455141003049a9110713120700f00400903490b10707003400c0b428a448620520116410305101d013030f036002007800c8121400d48648543d561008203c0060740c03180601c8a40042101110174504140041940903158480003a203d10758030703040c810100000280d40c00500b28106d1005c0c0085500c801c0c8042c00940f04512030b040c1407203003c141c03052051450700140301c1000142e0182e102480f08404c04400da9229040d034a004005090071680043d403504504108810b1003d0000a075444040c841d800080d440000b9031000c001e03988850070000e020354448030266180c2c1c03050307801085041c01e01e4103000402c4034880d40c0103c0b403036007013039208100c00314081d1680d6418410508002c030540309a100442c001c1036640d40b10501c43d031a10040c40c3c10700c0e0300b580c82644100039a8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 44729320 1250 44728070 44728087
    0x7080a0306090c09091a030604051005070302070c03060e07051c02150f030f0703020706020d060e0709030506160c06060806010e07050c120903010f06030503031b040305030909060d050d1e020102 85
    0x8002c1c045d00c80c82c0d00040341d03040310400201c0c0000307121000c003903040c41038105000522002046824a03040c00800c02d0200d5074881e2420b405038816400010a204036041c01003010902540c0711b020320765400c20a03112031607910000a00c1c124402113805a02070030f40842e10742140b030040300c0d107106d900200c600c0d107082100483c5079007410302000302000e18100907140055240e43c1700c0d0b41120742d8070368006807c54844040ca81580010000740c00307030341a03104282010420040c0141100070880390321800401741c070340d142c0c0322403003041000366032100a005001301400f0003d000390055401400000d0700405140d8900031a0302202175014095400748a070412900c140c0b12004181c40c21440700c0000710603614500600402c1c0148404c5a0a100d46403404902000b003000100007540100607958100a1682000d01110a5072040784802807440e0b0040200d00740505010f08100d900c50300c02414100a5030a40d240e031814800700e828108002181107903100107010340c1d94040c03042140c40e48021030504448 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 44730570 1250 44729320 44729327
    0x408180f09040206091207180e0105100b0f07140f060f0c0a200a0c06020601080708070905041407030308040b070507020108040b0421020a150b0108010e0901060b07080a0306090c 78
    0x360001c0e001c0c00e000101703030f4442c1d101c0f150306030030320301c20201100c8005507607282c0e80081e010f512601200641c00c082d4000c00001050056601402d820f114400d1514606030100d00e40303501c030501200c1d1001d004d00559000c0303a183d42000a078181a0030203440c8a80e50b01e03a0090900000501c0c2c80717920400324043c0300416207030348240c40f1207110b6810034101d6000d000352140010f001d8000200c0e01403048482d10000c214402490904035500d580864102c0d9072224ac1050b2031b04090701410480307038040d6a0410035444513400150300b00380240745d84a02102c415079050b080206c0794109030003045410051000300a40c4054556125040c0c0c6801418003c16500003041e00c60050702c003610120301c100c08107040c800300910888889180310a4402076143c0c80202a45034480c0c01400d5450503000b40200c1075450030f0740110800403105944802c2c1c580e01300700b920796200001401c80c0440d59030311000071842d01c0104d8000c050030b41c0075881960301c40c070078180014140d6600f40c10142400e410080c1e10681142c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 44731820 1250 44730570 44730589
    0x602030f03180109060e0109060e0304060c08030613020a050307090b190507050f03040609140405090606060d06090f02031807060807030c181502150112060b030c04050408180f 77
    0x11025946980350b001c0880490150006500282480e0314042e180903035502e0541c082281144220014418105810401a124060352044401050004240d03000184408004550001004204e00c03401d420b81c10420040760000a01040821400801e104007180c0054422000f0452017007400e26103100800b02000c98142560440d09012005c0b03442020000280b040700700403880c1c901200d0310b85039640002031200e003ca100300c0e54061802c0030040c0031400c0600401d407003018608020b100e262504000c0c03185c19404003240b001400d9271810080b91203d1a0300408104141c0300001603202e0078040c0505800c07a401441d14812a03000d02010440d050300403144a074889a2402c0005a0b102021001c4d00c010305500b0420100c416051804a000615401c00030320f41039880d0300b01da610000341d400c8800c416600b8000d400e90b1012241c00d100c006441034118050700b190207000c2d20b03003a15000c0c0101e0181d07081600d044801c01d0000c1210030f0745560816400882c80300c00c44840d20f0a008403000b0031120341 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 44733070 1250 44731820 44731831
    0x17030a051207031d03090103060902070503070209040206070501060609060806010f0f030203060406120b010303020c0303040e1611100605030c0d030c060b18040303051e010605030711071e0801060602030f03 90
    0x10301600066400f802079000b941c00340e0700c03102c039a02082e007440351058880d8041201c150100780f4040f40420301e0b00143c400c0d2801c0542c080000e61500300142c080116201c002482242d210707034100b21201c0080c40a0141000400c100c0e100c0d283d0441c10404c000e0300c902c44c000e003140c5c1088029105442c00e03039030100c1d80c01258940d41c100107940c0c2c0c68840105002c0c0c0410381045105022a04901041041c441e0311941224000c3c0c0c00d60315030114038400c04d500d81c8150f2084803a010144400700715121500e001140c007403032990500c0c0b40c100e8401c1c40070038140440500014885507a41004012508061040206928048590300c45203042035034040c2c210202da00c405845030ba40d5982c03000c4241c0743d101d0840700002c842d40808066290915000b030182000300d403104950780038074000145400512400c2030607901651111400c0d40d540c1340c001c072050140f000d41d08103184560800020740c5e602c0100024202c900403665800c41c9428801c1c000c3c00c1d9022980a00d0841d401080b502060501840590342c110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 44734320 1250 44733070 44733097
    0x4030501060e040f12050f070302030702181303050f12040609020102060c040602030f0d1416030605040203070503010905090a060c0c0c080f190606080313050f030a150e0f120417030a05 81
    0x664241c04106c074680250780c8440070b00f420014042d018990000050540c0c0713442210300e000c5c42e150300c200b9020690015101d00b90356403000c4c4410750001c0d011b5400740c04081ca002c00020705100141400c1c0b848800242c80c140d503107a0b03480700000c0665905000044e84078810000151401d03150220080d0749104100d03443c00c0054010485091034400ca0304140b001d5500219030711000d04200e000d81c0341d014404103000b000310703181c840300280606190003600d10031003030381d220181103a10702000c940152000a280c00e2003400792070040d0f80054418811008040c00ea655140c01091076840c110781031428940104e15142c1c0050001e102424000680f0000381d0f5190001069888123450110060040303a04044514080821205107614908028034100c80d012200c0002c50748054003855140d09400002400c0c5d01c4003000c130000001c156422503514949010211000c404110070485c1c01c00700041e000f00031504000408101800008a0800b00321040d440518a00391010381c2c0641207204900e01d03110413 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 44735570 1250 44734320 44734343
    0x150901030e0a02040e0303091e030f0702121507030c0804020a120206040305010c0210140402030d08090313030807030201050f13120e040203041101120b09060d0c051504030501060e040f 81
    0x4002080c010b00c071441e54090130a01044010803001621380d0021259840c00e1301c200c0514680014180628071032018181016524100407c1c0403180300da8407031101030360040c03144840004204002c2108190606010300c110301746080202009054900e001c503040d08100a54040c08050fa48011070078003165070306204d06038801d00502c0170a07150f01555001810780d529000150038500d070081401041004250070030003094003040d1002101c14400c4d40c001c0c1d0140e201e00002685a4040e1000b2034000301c1e10012281807242001400000f2991504221140400403545004043e0240107807a0400e4400354900e100c5d00e0b000c030450341d021501081c040d0043d40440d43c004c1c02c2500070f4481040c0c814024206555038500f500b007803010400030035142030014043c1e103e0f410080c045403281a200000003800d40715203444903000c100205e07484141c156808081407000150a80e2400070f5491070042000d04141c403245103040c000d08440d1994007090031701c10480c08004c0014040fa0908100551000300d4118 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 44736820 1250 44735570 44735591
    0x60f0a050904110303220504090803060d05071701020904060e070203030705030c1303050a1703011401030f0b04020412050607020a11190b0339070222060909020f15090103 75
    0x803030807441c3c142035400d400001000300c0e0010a00003c040075a11045502c00700981d9802440100d9190311009002c4140600202d61503182518000d0740450140d0211040700b9194021a4007020901e1080c80b60307a940051500000d007018000c0200030112100303c600c09281011010751644001030809040050000019080c2444c51003a10003444004c6038091982d03031a0b00d40265a0080810184c4102c003142d115030300d89140302e0046038161030f0b17100302c081c03026401e040040d00a000c0010b40c451065858601061444d1640c5c400740000b001c40040f00121032600b810010709000d00a08880c0c02c6411003108907020426440c80e81c1c0c402c50040d02c12200e07070119a90300103554100c03074001c0362043c00000b041c84104516270070240c5040d54050304038829900c980441d01a01044464840c2d540c1c50244200320140c645500c219541010002c40e01c1200001c42a401c01156078036000006070355502c42e038450550401e42000ca1061000b0360300b0303802d1102c5604e50b592423030054602860415448400070403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 44738070 1250 44736820 44736833
    0x5010f0f0302070b0a0603200a140a15020105041203090b0c0f07020d030f09060206011d09030c0601090609060602190b0c09090c1e070f0b1005030a03030902030105060f0a050904 78
    0x7683d90381c00030f001395800d0400c075003c400030f8541448251500c115001081100043e14010000754440003014144090310b4441d91800d40004031450795405850b03400700040c584141c0c107400112030300b2030340009664035052401c80c40780c14420503070030704240c03900c21280c002403070440f0565000843c08131236580f101c00014503d41c0c0c900c01c0c4c0e14001e40141c80c032030340402091741008524202003a84e0b200c07183c003240c0354072080b03a88040902c620740010030f801d2590100700e920860001e801c50b100c882620b01c2d080244641a20708a02a4000c40700140d940d48200861a11882508044c1c01c003880078286400480d0420180c144040001515080c011000324200d02d00c6407048650344000a00600c51030300e40b42141c04d166070440740c9101640403141060020310f1b030070f030401c0f40c190320381c0680b51500f10003d544900416031b10041c100c9100703524000020a46540402c01015a140b2a0344c010910703509601c149801d6a0020300042c3c0280103080c0031082c26903c10004009480040c0e4180c40250748904080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 44739320 1250 44738070 44738077
    0xa05040606080114010527040803060d0c0f1a0a0e100e03010603060b03060709050105030a151205010c0e090705091905040204081e0d08041b030501050c090111030405010f0f0302 78
    0x502c9586400211655138014144280c122903040701c01a020049a24450010682d02c6268400260300c12002030002070310b000142d40c224601400c0030345917001070b5035164032601c50341d000384000300c081c018200031408036851a40c0c240201200803604201040102a01c030440da85480c610400401c01d058519921840c00e052800c0c6c0020001e000941d50f9050050040501000c95070103401290000b503120b90007404044201c0d003040c0c3d51585140d4425400c900201940716410741850007426000818070f61450301842010b000c2c0c0300002d001e84600300f01a00c6590b82c1c4c0b01d541d001d005e0640800c20904d400909603548070009a86e014185200701c94013281080c0c0b1500015803183c808036000c00d040c5000243c112820f03d82d144110f01d0706111313258050340c0702c0049a5071800251050300245c00600450001c08203011070b420910300c082c0e10703566a24256403088403a01940880403a03d403459603400008190a4911a40514945420040028910401e801c022003c4c0524042e401052500c00d074100d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 44740570 1250 44739320 44739329
    0x30806041506030204060e030a0506010314010b040207030302090310051501120f02041203020f0a1112030c0616020d180b0c070306091506060513030308060102010906050406150e0c030a05040606 85
    0x4a91441c0d444035000f8000350401e0182e4000030b0341c50030410025080014201030b240f9000401000e242c0e00c0c540d039800141c050507403003404035500d58440030529102c074000780c418a4402e8030003680f1401c0e60b000f8146001700780e3b0520701d022800c000510003c15400344400000400c01e107410311340000340701e82c4107016141e192485e1005500c00076000804e001c180c15901400351007503080c0d07481d5001401d00c07195a0450141c02410982c1e08080c1204136107030024070504070304004011760f418016a0074865003400c0b4108c481e11250500000060189a414032002d406892035080c004402111304400c110102664018240311890028510074480c1040001000450380114180040d040c18036002c4507101ca4044d9a0810f503041c2b08011420600600580b100d10b40d0b188244d07011540745441c116642c00b00034000e5819550b949804201150031400b840784218041c03140420041e01c2c203641d102210342e6503808085074500400c14021022560000caa410840c9030f000816907881e50b0034001d00400b100c2e40b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 44741820 1250 44740570 44740601
    0x1203291917100606020d0e040b0103060308030f010e0105030d05030415060314030a03050f04020f220207051606170a05040512030a050a0c1805040f090203030f04080609010605010c03080604 83
    0x80010145000650b1000388020b84106008140e6200c005980e10081d030881c0e071000c104070210f2200d86041a910162011034140f40210300f070380d542d07100c002c1154400da0b4901140381c400c000501102d02200c0400d4018582900200601c1c0b106004c0107046000c0540b0041c068100d100441c1d00c5203074150081d80156412400b07410040c54007103040c03607895100c0ba482201082c01d080024140d200106400307442070b85c0192504040c030001400b0071081729801040350a040407061005071206aa5101a107240d900c00d40051881045d0313a420309104095682c0400e0030444000c422040000c40c100d4455000110b1100200c0d0689035880e009003824003001c4841d4800e10040100150003000e500464000c2c00c00c2c400400240c09601c0c4100d884c141c000f40020440d00c4103407010421420aa4009902030b003030120001481c204950001c5c0c10756001c4d070b4004007101c501280c2804010b809020703140d0002c9000000300721807841c01c000030302800c41c0c020019041c801a800002c81540308c3e5048140949039860 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 44743070 1250 44741820 44741849
    0x30102040f0605030906090604030e01050a11070609090609050103020a030f0f05011401261b130c020105072c090a020d0e07060908010911041805060412032919 70
    0x14005003d0307001110550690f00c26000807502c00b64010500c1400f49402d40e84070400e00e51181c1c011f5540e94404100382c020412221403070b0341401407c0c030040d0302800b115601c031301d07006161003910800c2d2541500451442440c000c01000160342d50009207045a0b408860001205160b0401311b03210068140c0142c22542042000101800c0ca0b210700c6041e94040b282d815501c0e00c0180900101d83d8400a042d045a803202403805880c92080f982440c283c4802080085044040d10000060340c450107403440141c0e44070400d00c00b015030064000140c5000c074401780c800500307207000c5401e85030945c0103400f40a200d801c40403c0440d40b45404039402d0f940031034028400c01048101083d5101803611890002030000c0f44007140740d08040c003d01c9140354118182c0f418030845807007040014184404490280360724030380414001101032000e540320320b0140000b10940c5044040c090240c4d105201c6070002081200402d080000c00352000300c1041e9401e8034010044500e803000c4611031845500075203109482003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 44744320 1250 44743070 44743079
    0x102030a02030105100305070f18051206150d1509021c050a060e15011a07020a09020a030605010311070f0309120f05010f050108150405030708031f08030a0e0f030102040f 75
    0x1c0d0000d50484200361240325200803c901c048044880c2501c42800095600c0c2c09427000f50712a10808400c0219132041000b07241c2d4901c0007070030a940c48032507285107802040402c48150030101001c90190001d03502801c0103280d581da0400b0003003008840440007956040c901040d0344034002c640502001c0305641e40709a01c03140c1049a5280c42c41402101d0440c01c26a10800841c2c000c07a450350300b503103294500e01140e420f080003158400301c003400072181071800744080c02c0541d032205010303401409880801680d0b1400d4181c000c003501e1b0340b504410b040c503080241e000003090312103003211840c90b0040394490b80c1c00d05030324003240c1b2500158004441109040746c0b801c240b006104a003501c0c20b115100801414104658601c2070715024881d820f410703084980910841c40e00900010750062042003580c0c42e001d026500c543c699001038a100d0119000740c810a145c03550212400401750801034021030400c000814004c02c4004c07018030705c6016100c11110503295840940568010b040c1ca540444c001a1701c8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 44745570 1250 44744320 44744341
    0xf05010305030714030a050d0504080c16030c050901060807031a1201060612090803040f05010b060304030c0213050c0a120605041113150c0f110a08061e090601060c0212010203 77
    0x80e0030a41d08006103200c51401c144c030000480c0c404280645030107040001105900006060081090711054402c00120ba6a06800e0010100d0794450449020500d41907061001280075940c20003800360f201c480c014003005402140d200e604c030815242c0400c40184281070071981001d801220343d0058041907a2903951001900080c0a803041595081d9600300c101000d14250398185030302404429041000c40d0104031034a0301e84218070300980020400082c601d0100d15650b0040301c06600046100d80117200314581040704210745810345800340168100040c00c0320083c0b00302c030944014040303100d228170000304460b000300005120050003084042c0318802001000d6004200d203031039180d04403001003041402000e40d010f034200b070340d50342d40c41413501e59985000e010105502503521a00303500c007455140d03541080c0c3e04060100c0c01d001c0c00003420f01040c2041740b11410541c40c4a4482c0309003c101d10394a001524504440300d83c40d0840091040f070022403511034481c000c00030715500000070131041100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 44746820 1250 44745570 44745577
    0x303030c02010e01200c0a081917060f01110f0102070602030105091e01030201030b121b03010c090614090111190c0501030207020f090402060c0d02010b100201110a080702010f0501030503 82
    0x55002400329035030b43c0941508039620b01100e145001e04020032030900b00c3c100700181c010a0740b541d0848040412548803000143c000249000c1203442e10b0600d00078840c1d00ca41c2c094004080700312038202505207940011000200d160075203042000809000c1850324040019981124480000310340d200c8007410110040e41c82405002d000c0e000c0000803035000840c20099410f07405001a040e42c5903400d5900441c003802c19012a40e52244803005100c0145009014000300300c8000c0e1420031a0780705a900b49402d40700302540500900003513507010409160442c40c040101c3c01d400d204681c1c0c0e0b00890005070349140380395034220311030320401440b1442443e098400e501c2141c01a0110491155142d004506900c80d02c500250002000c2e2800010707414610035440d041840200f54030700703081a103035a10b0f10384100c01c40c0c0000141e4642c6104401420702032401c503a01800e0784000d1111070114034041d01580b10b101e401404000043c000195014070130340c0142c070201c40d041428040c035603407820316507503a40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 44748070 1250 44746820 44746841
    0x20c13050a0c0c030f031104050402041701290103050415060312110610060c050a050102130303140a080115020a0c0308030601030c0f020712020d0606091b0906120f0b0a030303 77
    0x80c5440e502c95401030141010741d9000ba456a2800624010f21004402801c0e1406501607014014800807405071b40da800640054070000095000c6091b02040990035a00940528851110325003145143ca1081c42070384888650282004105a201d615180c0586010703002e07400a203e03c1c0900c08010041c41c680a081081c4c4640e03620b40369a141b060400762212416203601c4200366241f40104001d0b4018481c0f04001406041551080142d50303c405099901c40a0455080f0103005024800c040c1c226410b0020301d02c6081c041800c154030154042d08600040c011a0270f084010664001050310801052010796481001582d087d50307a40392900386c941059032a10301190a20814080c0648a04103c408400b45680100055480d00000401d4480c44d1030b800e0760400c2c2e200d00004c010680c640540001428510700018181c1c034040180e9003610140303507251b0100008c5420401030103521076108041c0d01d1418200007040e85030344100500402d0140c140c5600001c085400005144d01603000b00881e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 44749320 1250 44748070 44748091
    0x30103060207050d0e0603070c0f02100f1103040503030a200307060209040b01030504020d121101061e0512060402010833010807020f0a0b041b0b180901180c020c1305 73
    0x40713103015a003905802007076a4100c0014400104c51070711801951816500480e4a440d0903601500402e00260a031700180b404244424000c01c1e2140d031103144640f04110650243d81001d08041c0042e88a110b056280020002d1601c0304800074842d44050501c601001c0d0103d0b41e88601a140c80d001941142030214440c40c40e14050a00b1540a801030340c0c415076000744904483c0c800e0b5951140c0c14510800342d0030401c100d010814041c241d0902c1143d0181560048640c0007503c03c240c440070b080441e800450190030104c8580200007000541aa08250709003025070241c0d8590840008207200b480350081c0042e04410780780c00365a0b20040d0104444402e99507400c250707030333000360603a03560f100c0680e00241940018810808101d80044442e04030b40304260303c0c0c5100316440000d1060054580210003100b000040300b881010000303950801c07050040c2d41c014010344c50688030117251040750202a040c00e84503e072020642e44280203030710003080000c0141c01c1c451031110103600204001c80d0301d90580e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 44750570 1250 44749320 44749333
    0x1501052b0b042d0209040906060f09020703050f030c0708030a0c120b0303120c04050306010e011814060d020310050c0904050108010203040f12030b0a03060218010e1e0d0803010306020705 82
    0x860505002e0003030f041c110b040c0321030303005100c1041d010700414100c06000c90582e030900074141c4643e224007400309020b004440c013180e000c2c104840301d44243c2039035002d4002103104115010029411a040e80c014801000849840b0b07901e0b01e50b051741d1841a0f01000702062000002c0212034121944019540c07a150343d02d000d40800111800000c030b55006e60001e904d13902c28085649986012042d641e8840103c29001341420340e5000405e19140081e046940c0e010b0074100107102ca88410398054910701e181038002d0004a60858075440d0030a00a000c160148002c1280a800e540781040b01003c803450240c01041207107004a8030f40340340d803c0a884544218285400002d90701814002c4e0ba02032a0450240d40d86546199a5194000303144052041410745071005d010352a500c80d048170004602070000980e440d6034041c4480e40c00c030f0b2907180c101d0500c007544502000039107501d00b00c841d4800c10615030300c00c0c01c000701c1c00041021001c21402030000c440000007004101c055000361072614400d1040b21301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 44751820 1250 44750570 44750591
    0x90303020c0c0a0513090f020a0801060302030d05030f04110102150c0904060905090c0909070806010617130f150b040213060206010b0a08150d12080708010b0f031501052b 75
    0x18010f6680b040035030002c079103070343c3d103c50342455480305100521500c0900c0342d5030b4581e400b044901c1d1899004c020aa50b48002c20419401d0a10641d0340745e00c48d5180a62852401d07140c94011000c0160018200d021101c0c3c61501c1c5034020440071204181181902c3c559103001054001198841a105c60085090010004155081d40501c0d030080303250300040e00c01c01e071501042c03151001000300031000c20f204d4030070300041448045c03040038080c09160f600d0421108074000740041400014185103ca012020300f5500414039100003910540e03803003005803c156111161010280c402c180005620503c000340c0613080741513284910301100e40c0b5409444030360380e988140390114041d00c4000004100c043c00010764032010305505004640004002408e81603e44e1075014200480c0f94000c00401e01c24010303c41000d80003c0b006004101400009141008a420781d090a00010348000c100e81469864050705a000300c0944110038074210b5202401d034042011001100201081240f656103003010404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 44753070 1250 44751820 44751829
    0x1181b030804090507030603020604090506010e060c030901030c03020405040c09030605010602060c1c060308030103110a05030303010b07020d05150c031605030105010906081b0309070303020c18040308100306090303020c0c 97
    0x20100c070780111107581060f02e803200c40380103040010824000c040e6160000720050b9074100140001d850841000106490048000b401c4c041140d031800340b040c0424814014080400070446003280303c280303004a008160f0680581c0680241c0d0421070f07000c0d0504100340c040e00d1b17101202d502224000c00003488682d0741c518091b603c8032015207100d501e40c0d804002c100e84462002e802c400e0800d03454400001d240c1d6417511030f00f4032030b003080c4c204591412103290341031400d00c0c3c11030740301014103c11000745145500d0085429030030f02c6012002070089074401184018050103000490b455100500d07c004c086c58040302850140d072084459011010300601d0004034031344038006a0303040e10010703140c845140c1e007810400e55080200900031800003084c840c0a42e80720206030003a600414814009140080c00c51030003074182584039003264045c0c1030070301560a001c081000c05c950030a805061090841e1100864946900c105402c0505101e007403841a1f0100765050380240b600c1c4500070196660402002c0400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 44754320 1250 44753070 44753123
    0x2030114040b0606160507060e010f03050105010503060415050a03060203040203160602030a031d0f0102090f01030506090a0c050c030a090f060c0201021002030c0904060f15080c0301060804030e030118 88
    0xc2e15900380d19000440034108040100780700f00c0001c00325914100d81c0e0340c91030701d0081da94100d0400207030500082401175810240010f00c3d2821800d0510031581803500007003143c04001d0081d80f0803a03d480c4099140640d00011801410b406050f40010395103906202019600035103041f4040d100307007003e001582e51030303c110070103039032a0b035018619041c103000c801c80103003d481100035080301c188010100309140403c509a130b034030300f00000036842d411442d040003100300d0620b41403070506050104000300e80d682d030401e040d4405500e200c00a09100108400c0b034850050000440d01407100150b00c00c1d2040d0010340c040102e5054115000885845500071210440f190354002d0240e8003c07114140c052174145c0285601c107410070b40c0e140c1052a904000b900b50780203503206142c03c896000d0700b808a0700401100ca1405030b86c030b0070958400d00300075258108500c014070844040001d070901103000c05124400318820007400034028003010800c80b05007810502c50800032036941c0e642d41070f0b070380c1c1c0c880c5440c484 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 44755570 1250 44754320 44754323
    0x1803030903070609060f180201120c050d0f240509070f0203270a0303050c06070f0c060e030423040b1f081302030d080106020f0a11040207060e010e01090203011404 72
    0x90760821680d035650f8000f030041280201c41c415111540340300c1d1074129105005902a039103194a980940600000d040700408940c4c030b101c501d04005000303541e1500001252080403101c20001100c558441540c001450403103000984030030b024001000c44c0c003d01140ca800d0b00d0f02140c044849840708131080d2400c415046a040c0960010311425a2260000c0070445603800c414030b50748050044840054000803098100f10b001c11804109803c1d1440d0800071198040300a0410fa00030820040740030304070b101350381c00091255849901c00c2c000c0c01400e00c1901e0040041c8900003892006441980041c0a036080b0054043d80c42e02c00304504a2405030010759030205130036440000310341c09250407100198024010303880319000d0700070480140c40810100e4600d2043d940c0e910129410001c000303003400c08010409415a01c100401c901003240341418142030344003150016542e103100c0c9070020240030308445885c840c2d40703032064035010001c0c190041c90440b032084000700100001e040765061540c030250350 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 44756820 1250 44755570 44755573
    0x1b0106030c0b091908010e070509010b0316030f02070818030106060912050c060f0c0d0e01020d0e040e0f060105101106040809011808070e0702060f0a050c0f1218030309 74
    0x207003000315440c82c0005100728980940407548822400c080008880555070102090303a56a4042c03054408041c08442c0182a0850780801e1951506180075140d000140c03400c08094901e0105854180c004c0e8441506201c500704159116081400e08600c45d070050304101b0b86d51050006000c80074135040c4118400d50f582911004207144c10020300c8080d48500010840b03c602c9008180840c4e543c50300060030b071504024402c140d4900b926207510b401c040355030851900344110400d030100705a8000c641010108024940020304801c2c5000003009480148030600c401d006441c07121880380710216015060300c1c800d545032290181c80342c0d800c43c1d0240c1ca0011020484d0080070100300003030700c420010591103905252188030351792048400c50400c450750b44120700981c0400300403c8041041e044496201c1510b0001d448246807130542091801c3c7c0007405480740ba03594000241010910600ba11112004c40c1c0c51039444060211a51111010584a500c06096003d110800c801c9002040303d100d4002c040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 44758070 1250 44756820 44756843
    0x51e0904110d02060403060b0f030706050306010e0d02100f111902040504050a020901090e060106031406010e120f030919050a031203140a0212060a05010f050c211b010603 75
    0x8881c290328590740c0301101d502490740e00c1800c002d42c1d40d01d4080e00145005410001d5922441801c0040501001e40846c0c001e0300602000c0100c0f9810505590340840207003020318000c058100015903440400c48001d5002001131a91a011540102c480000410586502da408803000e0140c5a0340c054424180d9034108010b1044c1c00142403036007105800034895022505210103d0340042d0781342c18241c00000005640b01d000000142d8100003103401000d09040c10441b561224801c460f0290004100358180a004400c0c46100d441c0c50500711410340d080403c0da10b945103030481c429203940c8040742c0540300304181d0313a000c454640288101c1e0203ca000030311082600d407440da038080140f0700d5120b0440074150b80f20948141c400c142200144100e0304144016643c648141c41e2624402c0050105030090f68100c0050049036085110750204080e507084c25512002900341c11440c00304090700709903c02030041c1c2d80911000002001d0040d06100c0307001161841200c0080d18220380706840080c0c44184d428 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 44759320 1250 44758070 44758073
    0xe0a030609061b050706052d06120d0201140105030304120b090a051606021005190b0d0503040608040302070801020307050409090218010e0105041a0a060509060c07030c051e0904 78
    0x59002800701442001c02003039410404100c0410000e2012600004c00c1c0c00154080030000c041c4540e5600607020321401d0120b81040c0417114545651ba01030701e24101802c0d010400a1360340d2803040c8072117044a030842c2d00002c0d041500a020300f04801c00b0850104401c0d0001c541c516020007600e0a54580340d2550070525040d4883c0f10090001800802980c003944195201054061000c50100b030311101d0020303005440d012000746000b41418111072820329007003d0042800010074140d02041c600070010410711282000a03448559030780d000bd00030311000500040c1941c00190a41c03081d4001e4083d204400c5e82c074080113080c1c0c403007200c01c2c2d000102e007004140021031035a0700c032501c020f001070700c095005c0942a6169650f20001e0300540400080c0000402c40c2e407401d4002c6004540d001d400c20501c1c00000e0002c00c0c42d40341b16000b000c3c18810049009449a2522010b80d010305450508944050359641000c1d00050098010386000e907026900104842c20315004904200701c020384201000ea955 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 44760570 1250 44759320 44759333
    0x902090f090112020118031703070807020118150605060c010b04050702030c101805010e010605040b030109050309090703020705060c07030201050c0c0d1101060f24081006030209030106030204020f190e0a03 90
    0x110310812400507807000207c003150b0381080980c08812030714442660781c00c000b080a412040003d014200b1a81881c0074445e9a6014850000d001036008400091110344422444054249508803030b80012011030b01c10b040e01c105422000c1032030803e03903041100b925036840881e224400c0c0707200c40c890f9620501da00b0b04425a03a0b800401c00010102d2808003600150352001e0a40300203030b000d41d0030750391034050a11292401e1b10408041d0341d0100c0003002a0b4403070790b0760a030b120300580c0184c510650649000502040c00790b0111180e0503030040c00c2c1d50181c9056108540e10790030181c0250010341c070308400941c0b29030021048030341c2e108131031000f040b040c1c0021608032010200c800030701109549614001039101c4c41108014040d04440d072849008118002e6000007400008415608120110041c000344180e0040500c00b07a8943d0319015a82c1d11928002c40d001d0902980000e410520011f0054100da0000c00038080c03032907d548080c0c50400100101311006e608004031142d00c10350121080000501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 44761820 1250 44760570 44760587
    0x513020405040b190b0f090d1101020c060301050a030b06030309060712020d05040e01050405040212010612030806040911091b07030305010302040b0a030b16020f0706080910110304030c060b03070902090f0901120201 94
    0x80e4446c415140582100100c1c11500c0341c094101e41400b030b4110795900340d6806100700008004140c0314581158901400561000010f100180c0609010004117000761001e00440b440d03030b100904050b0740d03104070f0700d040b16130701140009080041c010024500d40241c8240104d60450720905081e081c16420b00341040f00406010384100c0c0d0141000d1048402c4132028080e0500030b10580b00320b6243c010f03840c00c0c050700c60440148014400c0c0e150006960000308400d4074200c40072821fa500260039910f0303418050300c041200100d641c0d038500101d540c1c010107502d41c0005040e02e00c20b440900007207254005100100c80d45000040211131104001140015032140031140304d01c2500c110351080078103c2c1c6182c2401d180790020b40019003a0410000600d10808c040208250716072010000c248413090151042e0001400040c00c21140410000c140042504881d904950003019180040d40d205d810000a5219680007406a8814040070540f85090441d0504030786203144d120201c500c40d503004440e00c56 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 44763070 1250 44761820 44761837
    0x3040312020a06150924090b012706031107021f0e0a030c0915060c0807140d03051006020102070b010b03060a081906050f010303020a030c030203040513020405040b190b 74
    0x30034141c07140c010400310b0044180c441a501c0f00202885d041076440d106460140807811900c8640800c1c03050941909000203080394a07401d8001103a40003100101e4409e070307040004407038805c3d00c2c210200c03501500401d01c5089075090307141040100b40bc0e2412072014024001d0203544611500100540305030f0000948503110f02d54580704d2030758002c1c2d034005442e240b00d5800944511071459001d0201804c140700321a04510003e08540e1010310300b580041c4585403210004050310382c040b90309820040950a01c180e10b5142c0c00954054280405c801401881c0c101e60b0103010385864200068114018800c03242041d40040726102143c0c248119803546501c080c000c980c001c0d1044000085000341400030141e0308a0070052044175007001c0c140390b010b880c4042c2c0180781076480f08004000090700028141d03541c0c0e505052600640c0002d00703059040d030040ea4031041e04050081a41c1d00c40450a41c014016035408540030010355503048107000d21503003454201c19108000302018010154600c01500d640c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 44764320 1250 44763070 44763073
    0x80307030f09050a0801050405060a0209060a0509030c0a03060b01171605030907050303030403050703080f0708011404060510050405042004170c0411040302030105060411030c07051204031b0e01080304031202 91
    0x81d43d850010039036000080e406a5401d954400501c420080700380101900403092090640c1005043d8000070320500c10744209034144680018254115103003030105c40420440149403640e85507882c280b14021b010711203150390004044101d403100383d50150000078001c0e883c0e403800514284941c0c5003910f540c2e001900482c500e10030b10000041950301000114841e1303119542d419100c00c124034000c0c5c00c0340405080480d1040800c4200f1031043d60041d101c0c1e04492a40002e0558440c10001080080010f80c01c5150024401d1001a0407190482c0040048410a840400c0440107900c00f001c500100346941942080d800c00c003c0229080c01941500c1100d6103c043d40e0413403110700f002a0407680454280030905c503010508205514082c8034440e440203064509020cd50b215010b080710314070000708014900705000c01c0ea00107205d0104200b150900345e0455041d95145c030790822180245841981c50b00a04c8030100c080b90350b0b40d44c04d0015049a8019000714102803c42c0d640c4403011041d0008203045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 44765570 1250 44764320 44764337
    0xa0c0603150b071b0b070b0c030604020702100f021005060d0b0702030c0d031506081e0903070b010b030a0c020703050a060f0209060a0e030709200a02011404080301050109060801080307030f 83
    0x1c02003803030300030001c9920444c421000c010448a0ba048811507a0340314001510302808501e0100d401121295404120300240c0f070b5032640e4507030001f0028000c0303010103508484a442d800362171940140f20448800c04035003c640c581c4204160100a0390030403264541c104094078001000105480c04240e00305100d030041e03078140400c1d5820140f03400e0344c4036140c100090320b44690800a03883c641e618005003940b4500825689054030301a0800d58810b2801d440500d40d480c0002c080c018140141d40700c05601c01105003207540e5421003400709400a9644040712031030403095040c2c1d180005058001c40f5802805013000120a4942d00010309100380c07440d441a0f02084000701030303030315203004100c0d031a40d54a410058150100515140031616040150001c0c54580c540350040001d80c40ba111601481c0da481d641c071008400100c3c054241581201508150300d000d100400c01800301440c1640c0d820781c0c03074501141d42d6040896140b03c0038810000300b07400c01c12020000c80e104161181c19400f017030070401003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 44766820 1250 44765570 44765579
    0xd06020c03070b0a0605090a02030108210c0d020a06051e07030b0420070c080313051302040e070c17030115050307030908040915050d1e03020a020a0b0d0507020a0c060315 75
    0x10340c4902114901c0000359141018002072500160003500148d18520460456041c440c075282d50700d042e80060f01c061140c0301e180e040c11014403030441340003030a1801540c0001400c0500690f4036111107208584050508001510100c8407440400342e1441641001115460f898829001820003088554002c2c0d103420aa004000101d24504040540741038410351b508034030b060201d42c0e5000364008a000e60410030003e240d4040f100c00c1c1a00342da00031258844c0c10011810700500070b1046c0c0d40500501101c01c0c00b04040355030012455010071b405004d00780c2032041d10706220012484240152054040c14103000342ca01442000a141d004000d814006401c0c101901c4040050b0480e80c40707680459240e000a00090b92411805030003482e003500d0070001071400356101510744910440340f030030729a803226021051600c01c101c140b990780d80203010310311031648481800c015603000c450000011402c002c045041c1d81c2c0b001800084064100341c1da0884282858000c0b005480d50042c0006015880c150118 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 44768070 1250 44766820 44766833
    0x17130f03030c021804020906061b1023010501020312130506040605090d0216050603041e030309020103050c09010905040203060a08011407030b060a02060f070309200108060f0d06020c0307 82
    0x60155000b40c441c190125698410015403004030001191020011014040184c07145490380d500a102241c01545a0071940c0c2e03840322040140d000710600b0711410141c0d034240c0c0b07a56403100041003504d800580600720112101c4010740420703c0307110b0040c1d02c10860000c05807407101d41139400c205420030300c851080c040d449041c0f501d0001d44050707030680e5595060000d080d808100c2140b210502d03001070301810a020496400521003445100d00600b40000000c1c1003140000c0213040d206620b00be028911207090070000c0003460743e403c04034042450030010464413540c040585034000016520244407508020a000c040d40010348501c1d000240c110000c220190203028100a1002c5602004c240d881d01550050581d4000c000990048508103c0028440d1303004c075429a004448001c012481d449800c0d044004103006c49028100c3d03024102c125019034402104c01d032101030244c0e982c8440e0f03152841004650141480b4455002040075200e03800200c00f0380107003400c008642d050b030b0300701485504c410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 44769320 1250 44768070 44768099
    0x3150603150910050406120309030f11030d020c01080c0301080a020d06020f0f030f01050906090a0b1906050a020d030608030a0309050322090e0313030308091608070503010b0d1713 79
    0xc440d030300303903003c010300050a00d485400c0c000c4c0a5680340114a900640340a0420590383c00080c0c1444840c1003030a0a03c010b1280f04202444080c04907640800c1002000f5100d403c003201e42d50000e441e440116016540b1001941d050716076403001b41c42030b1400d40d030811641501040b0202c2d9001d4007803105881c5076050f10b02400094150700d4246940307140000600e000f03403070142c010030b2140408105002c501d803504150541d00110107080000c689240c0000134102d59000c4042940b141e1041c0c00119199a00002500401c02140c084031128004000260141c401e640038480f8035900910000ba00140b00e42c1041c103559026030103592402c00035012680da0420080540054008000703002c014100d80e51144030740b10030518000c2e50828410280000c900740892001500300203142c004606504814864140080000510500441d95400c0050b840c0d01c3e6038450300e0311a520f0500b1800403802c0074a900403038158440b907002d0544a800c03609002c10340041c0c00c2040803110718040030403030180d6506034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 44770570 1250 44769320 44769331
    0x100819020f070201120203040f03180803040b0a030c020615010309030e12030c071e0302040519050a0606030c020a150203130606120b250509010e0306010f06090506031506031509 78
    0x2038a07920b064500000d0a003000030300e14505003910400802001c1481014801303d082c1d8035182001480c00d911404804201d0281c010b006203000006000803083c20000003001c4d0620181c03000c5c408040b0f102010f031303202e110840d620003400c0c803d5a0102c5e042d41c441d40c0844441031217400c11b40e41440c0d549011034880d02c4000b0300f0035015400081d400141d003500b0030242e001002c1d85440302c0307020303414500751011180f22440020301031922000031807032000303101380145075190200e01d042060f8901941c07002d010300154480d100100c0d26018189018610104200b0f50403604501c407502441d0310b1140c044000c1d03200520b50200307110500820350029071940544802041d840c9040e0085124506168880aa010701b05010b1220f00740c4a000c0e018040124141005443d420816120790400c0b00595900251400c8503505000d07582c00458840c0150740300c002501c400d6600c190145da2190140080c500c0152b40c10260111034401c1010f851078400019540084220f11310f10f461071402010944484040d540c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 44771820 1250 44770570 44770597
    0x209180f07080907060c06020a0c08070c1517060603060307031b14040509100b0102030d021209010f0908030f0405100608010b03012904150503150414070510081902 72
    0x140401c1d10341c00050150070645403409004202c0ca0420040c0c070000c06014018802e039004901c1c41011402400040700341604103520f90355882c5503140620304170751640107400204003000c1c0e11b215407a200d9140000001418000010b00740c442004100b02c81d040206050745c5842540d401000040030075000384504e0320a20310110f05a410304040060752000a4021030155252204006503030030005402560303111000d00000c1c4c060a8100100d0844c400d9401c0b004171a400003403810404203008140030302c1071194200820001100c3c1c2d05800540f4030082000e0076a1b1028800b00b41e480d204898056001841603040714200c0d0401d04804080c2c4a4992080d415039640d00700c01d081074242070041244120f44403403011040d8040e124901e0b0700540143c2e00f00d000300e943c0c480c5841c805520200b410b005d85030080c12160341c40400005244a40d20031a0100c5003601c0080c1c4142002d0707000a8145e044d14401040d070411203030281011224020002c00f070f050701800320a07403552003e00b0746c0300070014401c201c0c9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 44773070 1250 44771820 44771851
    0x1e05070e04060506040b0108010303030c0338030a1a07051e03010608090f060a020f090d081e13060507050102090a0807051507110103020a090e0906180102120a020918 73
    0x40503411200f0060006000d10f00300300b060f164a0382e000200506699050800041e08101a5412070040a40d00d981400081c180725032422014070940001c0e400100c45801201030000180c2030503100c0c9122500142407405000d0b400ba00320040c604055441201803500c1401c010b100d82c0801c42c00840e29280000c0e8000000042c09403540c411091640022550001d000c9120241c4407665600c070000c007a080c4899005c101c560300d00c04200f04a412030740d0014078400b100c0e60182000403459121005414548940544862000c075040042d943d00c11410041b001c100b0303160400550f87c0d540700810407140d55500704803150540e51115111406006107400610500d4240800c1c041d05407003402c0300302035640040c0000c100160300750340c0b004810807080c40c002d621403420340b43c2076075038101e40d802c002421004181049018000014554410220303246428281552b40c0780c29030807403042491b001040c00c4072a00080100605400821707060704041c04012a092400d280914074140c241e03038800c444803281 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 44774320 1250 44773070 44773073
    0x15090c090b010e0f010f09050a0305060106020106060206010b0a080a0209120106090e010e03190203130611070609060c0222140f0606040806150a030b071809181e05070e04 75
    0x18410300034840020b003060a442030300c803000203442200e00c4d06041e0400c000d080e00d005804c0d00c2290a40001c060141c55003951580b44c0c40c12075200d01c024041c94005601e0014002129440051028102d40c03499501504e0180c141e807044402d030100400030541c164080200c0552074681503814030901455100000f41700d0b042031048016038002115608081e81890564031100501004136003080a4102d81d8840425001d50309900b18022003da60329095000c1c800080c0098008800300d40200120041c0c4400c0f0391100016260b284403030241100281d450b00c811001403c007416118085c0107848808040556074115071001d443d400001641d1520940003441408a0399041040c1c00610403101e4508107410861002d6484100406201d5100d001a0b030304101600d071008594051364002403079a04078586200040c0134031140c1500d11441c5c0b82c02c1e20700083c180c911480782a101c11030200d0f43c881551940e8a0b0071040c2000c109132088200c0c031042c02c00300061801c12641000f801100c0800745285400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 44775570 1250 44774320 44774339
    0x705010e16181808040806100303050a20010606020a0b06040b09130f021801080c1002100c0e030d080f090102090307060f0c060504050f01110c06011215090c 69
    0xd00406a408021140d0341e0070703104190202a00d00007101090031244060303011002e403021440440308000c40b401e40c6010b00c01011300800a403038901c5c00300c520503110702c2c8229100c2a0a484040d000600034000c1944840c0b2074526501c240074420804003400021480341400c4410651141001d640500e171f1043c00c0003400e00d00e455010100f1134040020241d1940440c2c04290000e002a80c960020ba4810b02040035188064a400350007402d001c941c80450112281c100c0401c6c01007c4140c41a1401d80c1102e180c41520b150300030340c090b400fa00e4426810400900030f00951900601031140130007940001fa00e0400104802e01003594619090707040a40f4000c40c1547d01404d09001c59004101d00749840d2000183d1038110f40c02071422016017039003078004446450804c1d40c0100101e09003401d01c03040c48000103140103400e92803c000c000d0032a5118065144e44212500e0450a40117034004102200c8000782d0244403500613900c40404c40e81035044007048401d18070301114082032505090040404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 44776820 1250 44775570 44775581
    0x402010f1125050105041208070302150a050601080a0c0f0810090504060218100903031d03150a0b010504080a0206030a0e0601060801080c0a120209060609030a050102070b07080408030703020309031905070501 91
    0x405e0030132510f454140520b418615002800240049400043d9041014030030840c5000c0100c2d107030402b40207800c140030401c000d032400355086400951114046003680d0345601c149841414181c0741c0080380d5890400641e6450343c000c0444c691a200e540e00044d15801e5400796501c1140b04840050f43d803080d03080c9010002da010710b0243c0c080c079014007190318100d41143e00795090369094184001400030f1035a4a04502c0040f030b840355014010401d0000c002500b48005500a00345138000380816400c040044480d40168890303451280c1c0003c510300050f0805400031504040c510b00e001c120550154846403a108081e4801c50000700c03844010060200140441040c12008a41c101145450102040d4440d400000081d100c0e14070030000c01c0303080c0d4408080780d20240c0080d080c0c900d0b42c0c03da8200b4600030b420603102542c0070702c21a4000b0721401c0c880c0a0442c4210b502c1028581540c03100070040b0025040102a92194031040004a103600340f95054101144400c1c0d9401e86e481900f4500b244c207403070b0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 44778070 1250 44776820 44776829
    0x90c06020604021e060412051606030b0f04020309030d0c08040309090c08070e0a180204030b0105030705060f0f070209190f05010e070309020303070206161403030402090402010f1125 80
    0x40107041404010382ea4000905142207920402c1d2828020760b0001800500c41c0d54406003a50700c0d4001200c0c1048008224102d0311200407181070203403035a401d41a025100740341d03001640141c450010f01100d19003607002d1604029034204490510664480590171680b003104860302080e04041008109039000321503e0107440b0075401401440310100d8040d021035000307058001030221400c40d000b082d4503009980c4004000c40e50310211515000d0700740100a40c0117020682e100b0898000204107410000303818011140045c0000d8580781160001009076001340b8071a8204030410003940300580e6910590b40c1c02402038003803480c40030200c004103204940d1449401c0d0310300e60502d0010020314400c030312469401180e40c200411342500500c002805c5228003000258001390100b06035180740d240415030300741507200b0102e120200d070680c1d0b14103549000485000b540045004001001548155481d42d103405080c01d000ca1061030000d441400c00381ca524080840340350080240425010300707042c500080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 44779320 1250 44778070 44778073
    0xc07031703010806131a0405031306120b0301111204080403060c030c0813032708010609240b0307030b0f0607030206040b06241308070602010c08070305061c02011e03090c0602 77
    0x1a5240d644d1812201c0d0807103113403486c03200c0303a000905008040c811a840c440d50f6040400d42e031503d9100103818030f42101071074210546816070b409400d080506c0b58034581a01004180e0034840442c0c10462012002042121640700a020000000f220381c0598000c1e180d8a4030b01080b0004d040ca0f00401e20b10000b811409070412a0f4840008a40c0043c82c10f50b42c0701503885001082c4070580d0b022a044852544014081d44c45c0c19000030300000d05620a01d2561440c0c0c0481d61001c00d80008120307080d00381d0050040e200401c00202d0360450007a48a10200100600000c85a901c8400000d666410900d000d0740541c1065040104006140e01c4642d44640200c03050540c5100d054401c3c1c2840071522600b01300710b070380000c0048612000c44096802401f807035048401b090346402c00203000c2c0203032a41000108250202080080b0701034004c807481058090130214042260140c0140a611a0031060f0305000410703402034041140124072000c401c0389518042002c42040c40d160815690942c002000c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 44780570 1250 44779320 44779351
    0xa0b15030f0a030e150315150703020a0203060c04060203180103062c01051905040f181401050702070b0a0309060e0709091b0503060f180604141b06040b0c07031703010806 75
    0x5d00c440d81600d800010300000b40744e810505070b010450013403020f44030156091002c42c03420700309507000621494543c42a801e0301c07455251620341c0102c0703000718001d00026800c00c1c0401d5003450a0f1004111403840145808265107980342c50004c1d00d9140d400d01a0340c0203110060744084190607540d041d0041c103044d21005007202d401b40300454940294040d180c82551200b66001d6025080c1d041000d0311001c0000346c580f55071881c54a00711901c3c90840c075141c0c9500b4000010021400403070000b044a074480011803400400310412401800086000c4501e41d80c2d64a8807100c1100801500024040742100002d40740d8041c205480c43c840c090880000030301c4060824400c80c0c4022074000c2d004191030005044075181c105541c001903034008090905886604100418040445001c0503c8001541a00c15040840f80c3d10903481048440e40380d00b00c0000c20081142001c0100142203125610059030038194607a40c0340000d4044010b0910109030b07005c00180140312085c02a02d80020301aa2203221 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 44781820 1250 44780570 44780599
    0x50409050a02091c0c061b0203120a0216030c050f12010c020c0112050108030a1407050f030703030f0b010f140d0519050c070f06020d0902060a020d09060c050a0b15030f0a030e 77
    0x4006031030241b030040182440c0401c00024036100d50041c081d60040c03d44641403000c260075401a00b142917588014814611342268004400d407240042d2a0010040c040c1107081400780f0a0410800c0302040e08040000d4111810110a10400f05815407942c0034001d8603000400041a0b50803411401c06c8a902d00702c010403101e14000116405241c581c1071000d101c80002e0407401ea035000d6928058010300803540301c2140b0180110040c02810b02c00c1d02c0401c000c101a14060003100d140381000c5012600c2106442c180c03034002da401031504107000d01114074041d0030360403030810f0b83c46c15255120040d021441d001c851031040d01034107a02003103c002d168184846a180d40319288001030028003201e03030018a60000b00566046500c01c0d60300948034580d2510b60380c8000755501a042007010001c0ca442d84d000c00d00f14866081c5d00ca09a41100c002c0681e40c180e81c0f0b0718034201d80060300c07100e103030f0076903c5000042d81c03800e020302014400204040c3c80202224117000d03040c003c0244140d4400c501081b002070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 44783070 1250 44781820 44781833
    0x20a0f0b04170313090203010501120501030f02041a04090b0105150c0307080f0405040501170f0c130f1506110c0d0c0e070306030c08070306060b090102060610050409050a02091c 78
    0x4040302d440c0c91080c400c40180b41c02e203e0030751180000d40c0d203245042001c081410005d940003103041301c80030b90380c001c2c00042030901c1c0402c0b01c20038000101100760703803003880016183c650050707080742c10301070000c0040f85513207000201259811902190030030268001004070b07181524003804144100d116080c6480c43c8440c07207036100d105080e030080c14224042440a196440002620b0181001910400a5503100e1450050750103403018103880d58800c80c40c820800d5400801c101010101c0138100b54000d5030604214409402080703100c0e02c1c040e41c0c800d5140e50000c1603200d480000c081d1900d038142060085102c050510000d03a807000d00620a4184003400641d11001c04000c49203141040b40d1107407940d180072000b0301031590001e802410300b80000b00345445c0110740340041301c0c0f09034001c1100039603440740c4c0302c0103000302210075015800c410001031890030207122400302d0140b03d00e041c51501c1d44405040341250403d0b03d180e92a40e50105a41c0001d05107980d00046941040035580304200350f50f660b50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 44784177 1107 44783070 44783077
    0xf0405010b030a050c0f130f0b010206070e100f0e0a18180f06020a05071502070309050f030a030302090102121206040b010503011a070f0b07020604020a0f0b 69
    0x100c1070078680068030ba42ca031a404806000304100d1442000f00f120f04100800341c10a606084403131020356a031045182550602d6000103409010307600092070001d0052400b400d0200075418426940d0350700d000c0c1c0e000b040061410145110040c0401c4030081d070100b00858210300700d40b03404241101d68000641814101c01001c00140a001c0c20400e0b0080f1020b001810480a2964000104040b0b400611b440040d03030503d5803a24030190303640684040e41d00c0000c0c0c4d1841d400700c0c1020415610000150040c0421141540346c641030078002516000c1611004080c154001030aa100b03074001e00202030300040d00d0600c0d54480d410794049000c08541150301510991900c11071611642c082c600b641d042e1034654485144e980c0000c1c2d038078049948111020346102100ca4171340c000085500719924032920a0f6800360039141020b01c10321554118603084030905c940700c150144014000003054 = true := by decide +kernel

theorem cover : BRFrame.Cov 44604320 44784177 := by
  have h0 := BRFrame.cov_init 44604320
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44604320 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 44604320 ≤ n) (h2 : n < 44784177) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
