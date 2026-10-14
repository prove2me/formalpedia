-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0509
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:10:28.997038+00:00
-- url     : https://prove2.me/submissions/60f22a49-58f3-4303-b9cf-1e05a8ac399b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 91366907 ≤ n < 91546763 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 91368157 1250 91366907 91366909
    0xf0614130e011a030c0301050103050417040f030c05090c03060603070903060906060509090607051608070b090f0d020d0203040302010302092706030d090e0a0c0903120203030103060b010f020a06020306 88
    0x226285030850340d14510350141d0798141c00e0044102441220003103800b20315401e4014410340c080703901c500d142541107441d682c00d190055004040103481038940c1c078101c0d07001c0c01c1c410420a000b007003d0401c182120b81560716601c0d0280b842407464000a0040c1072160170b201980c9130040540c8d0700000111100c64880d96032541c01c0b51141f01c035500240030141400c18603018085190702c510155803007615805003654070224003654550342510300e800020000c01c84203000c868960001e04401e44500c0c51103140150a03100e800d08100700351500b410a800200d000c0345c50f9172042044510480143c0040c11000400d020040d440b40258032019050580000c0c5641141d5284041410392040725450301d00b2001e98110020740800d411140c032030203445147c03140016540240348503c01c84400005949290f550001c008000d80782a9010341c1c00d002c804038000c00001c001d1400c01c44003070111b07801140c41c0d41c1765042201c1540c4085104c641400140d14000041503804155081c4450308500c0150742e030b44842c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 91369407 1250 91368157 91368197
    0x16050411070f080c070b03010e090109110906010e0409080919030b010b070c230a06032706061d040c06030b1008090705031e10110d0515100e01180f06 66
    0x10318400107005010b00440d4980e07020002c1d6060321422270750341129a44610700c1c1e41c2203e41d0000081c0038410a000c2d001c46501c0d001034030603408401850001c11917501c40c00842c091710340021049a2401e0049042c4409040410303018403900d034424201024549561170301d07210102c045c0030b0120040800650031050200c6040240000c00400f50411107203901d0342001503540404541c0301c6d224034401c403000a8928824007589072401411131056100c20652030f191101008006011202e8a4464a00040d809508008034034450100500039007546014606038806000541068091616107142c00c0d901f0707114100c1e40d100c0140c15052048803078803090319040c5000c0d0a80d01c50340d4144902c02c14400380c0040a84002000c0e4041401c80382e00c0e10b400d1000c4800e50b1041c01320480c0403101071000380500401e03030300026004803c2c42c401c40b1400030f0810204a000d00304104034808100040610071555034802406200c0a5040420507220b034180800b04c03605282d10711840041110500e40410803800f84 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 91370657 1250 91369407 91369417
    0x140a0506030a052d041a010609060e15030c0d0f020a090b030709031709010305090c0904080f160f1a010602030334020a031e230d05010816050411070f08 67
    0x241d00250b92a001318448031083d61044400b19500c0d07080707040c90380d0140500000700e816541680c83d8442a10309100c81120786000300840c00790700a80e60126441c903031008100550007524940200e65440024151890903560207192049003c0d00c108081000103910061441c180c4184030312080d90780c0ca40d840304031002c00c000c0e04080c10380c16481a96000070748035003006007a84013080c5c80c180455654280c802d0384583c01e5200300e0b504070940360000303800924a40c00501c00c4208400f283c0342050b1004580c039084280603502121103594810301c0c8006c1c4901240300e442d81e8442e000243e041c40d810514025200d0002414050108014411505035140018080c0040028018000c2c0d6002202c0714000d580302c540c114207078041010440203410052903048034210121264581c441741d200141c501c0056841c2c2c402c003103a17800b44240078111414145008460003808000000c000d03607803e414000f500c10069601c140d00c103034985421b206a001c0402c0942d01e81d9900400d40164114090820284911803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 91371907 1250 91370657 91370701
    0x5030c151902010501060e0307051008040510020a020102040317071119091a0f0d030e01140405030a060e010e151504060e0a020304110a0e0411010318080301140a0506030a05 76
    0x2044080d40306540c2e0552056040b0385103681c034403018617407420502d5225a840e004103900803691003030342103200e4010f1225a0b001840340302107481d200100256201241c205840e08401030750005810014442c549030f45013070300c80c01400345914111081d51446058041a0b104a0040581210103211072411403000070007440005011700140c0401004101501824881c591007030342009444500b6041055407003200e140d140c0c6509082c0f0010f1070055a040840e0722003840715500401001c07c00e43c9060005100d824031444010404543e4841c0080c251101c99408008a90042c580d4410405504100d41d4010100e08814201603600c6c01c0820003500c0c00d80c02504c050808481446640c94a82c0c1c02140328174003ca20942c006c0883e4010003030043c0d02c034400e260b00d240a07103020401040c071040d541080c20505040010f145c87c400b03c43d505101d818000f00b42d86514010004102c03030340041c500a42901011140b4880041c1841e00060403800044c026582c925500c0b070000d002054038500600380140703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 91373157 1250 91371907 91371937
    0x2061b1606020405040608030a20030d060e0711060c1b1005070917150402011b0c06020d11072103030b190504180803060409051609150b0405030c15 65
    0x40c107050010b035100c1c0c80f429003e14600003000401090100c1070703e5600f5545d17550001300f9400100c0c00d0b01010001c0d90400c600780820030014281805034804c400080048000c000e55074a82240c001e0081845c030380700524140c021200f0001c0070303600d800413141d40e200d0741122030400782c6031120310701e18018600002e4a071a501c0c00c001d04c0444d0707801c400c40104a80000d800c00c2410841e8200da41e440f840d0050303c800c0f5414020001c10010f60040c0503042401c47da051010304460f00c0381d20b0b8001100250f50003503003d0f030050b5034009041944004411070400c0f52600604400d031400d030350103120100030f01d08200c00c3c1187c0d58018040620070381100303c01130300041c0715506004542c40c0a00b02c6142c5031140b14800d6151010200c96460b01c04080b1b030002c0c3d000200603055654480c1404017030080410211204e0040c84040c3c1e541c49200307182100070b030001c0800094000b44ea220240995030840d0425007406c03100340030401441e80c0001c0d08140c010720a85070701506040030f8560140078040c4100003a900c2d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 91374407 1250 91373157 91373197
    0xc230a02030c0724020d0c0b0612011109030c010e03060604050702070e07180603150b031306020c030a0201050f010e1b0f0a08060f0105070519081201080a020a09060602061b 76
    0x7072a2040744e29800da0003a003158600c3c00410b083e0b94a038104000c600114a00c15000e5011600213072009900140c06024215155415000d080c211140c086441029040c046040612414208002c801d02002030034a20030750400d1500080c0c1c2c583d801030400d84940d8071038000510031031080c054000207014822142199050422000c2c1503900c0103c01e003001d0098200c2c000682a2182c05804000c406125540030014189105502c0903400101744135069240070701c000c40007683c02e1000b0540c040c4c401d0007454440c5100d003402825104054501a0865107400040c80458440c0070402d820041514941c00d94444c4170181251501038011841e03000c0c03801240420302141c011012903c00c0b2070464054151a20300030040d9201d020365a030180c401c2c0d02c02e941c411243c001c0d803420309020a0203214014100010072440354030003d4260004802038020700b42170001c60508903070400240002100500c0260f080c003000079a52400103014452110621a482c450100f290f42110302070369055000507400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 91375657 1250 91374407 91374419
    0x30303060d060b0a03030c1b060f0f1e110105010602060405100209010c02130504030e04060605041707171b010c1a130b01061d120a1b0b070b0603010c230a02030c07 72
    0x54401c110590b4a8241030484c01240300c81402c8c0d49060b500c850b00c070901880d01400b404c40701084018000014441c482d400c038808566006c00c806110b076903070740d5092040c01680016074256401a4003644c199880301d4207100002c0c001151382802400e6031100181c4503400d8600480d100030b884900030b50031044484411050a019800040c8218046d891f00620b044164040c001110a07610420303000034001d0105000c1400034442c101758101100702102c89894031031029a0000414501038007103a8031444034141000140600c425140c0c03000d080c5902c8410356074948001071000c01e950310740107502c0d007000242030103a000030036200d42d608090811115070312450302404440c0c5803c0c48030041061184040d9031490030450b1404001c2114001d024010a03607903454600001580200d000812036040c08502d4020140c0600285d50080d01640041d007414014182102d05441143c410801007965a4410010012501c0c0808404d040b00950751002c4000172400d45c060f031404054180034218001a617 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 91376907 1250 91375657 91375667
    0x71a04060f0c050304060b0d081b0c03030d0204050111030403080912033f1608060111011109040b0d120f02030c0303090703020307050604180c05070210120506030c030303060d060b0a0303 82
    0x440c41c0303d410104101411f070020080c640c801402d004149400400c000801580e0032040003050f013100004072240d42d200400020704640226404580007540450200819a480403854003a001d501000d94541811a00c4061061180d90640d9000d044605000e6030200010012909002e6003898040d000d48584840310b1402e4003211841082003d0745940b8400041308a030f4402e010b503a00040b18100841c00c0c15007504c1d40751005000e01e0500c00c1000300c12505650030702600b01b003c140701c0c01540e40d50010300100021998a8140d0a00039910655420000361029480580c040d9103801c100140750003014003249548510740901703445000200c188090804001115401d482c4201c003501da40c3c0d9210ac045c0a028002d500c1170724091100140c248940622940c00b8101c85001417400b05d1a12216801040e4015149120300b000150500b25084117031400b807180035049101203020700b090410920000c0d80c0c07800041d00c0d05104660a88a50040007420b074448003580101a001d19605070b500c0c100604 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 91378157 1250 91376907 91376911
    0xd060903170601050a021b0a0b070c030309091b0305100b040305010e15040b0103141501150206160c030e180f04050d020109031b0204110c010917071a04060f0c0503 72
    0x3021410714408201e041d8001ea007a80e00d0914140c0c01800000e00034400000d514090310003481d0031103407954020540348080c200522016000d180d40b0400e052441c0b400821707040103540041d00311031501c190f0082c80b5200400b0440900700a20300861b04e0344400000184a0b0050f60110031000d2000500204020044d008060640760040035a1484030f454110140905400c0320000c0100a00700014000115804c0d40b540201e20900d040324418680306506111110b03083e085104800c1c0c020701d6000c0c41540c10020b0b00c0e4090320382c10343d0f041c860240490107080c0c9100d1803802030502c42d41c164003410689038030a02007030303a0210301c07089146410f256662072040b0005903420350b03a80c040e0000082d54035005010340240c482d4140d940e01d9503500051000a411203a0340c2e0700b00d03809511a070f4060b421864038800342440207481000010700601500e024211040d0704c904132203105105001241c00309000341070500700080e44400a0419070341d9441c100c4000c024044021054602c0c4c00740c0002c1c1d00da802401341d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 91379407 1250 91378157 91378187
    0x180f05070b030a090b01080a02060702060c030403051b09090a050709020d0e07031202060705040e0705160b010602070f05041e09030c1a040312091110050c0712020102120c0c06090d060903 82
    0x1703000d41c0d0b00d80841079114003106a004e50008010012100141030170402000d84042802c241c03401c003038a03640c4413405c01d03d030400c59a00100100310052054a410f100d940e030402c1040300200128070300c1da40c4050300c59400c0d114515501d81e0104c2d00c13404420f104d030030000307280d0824010b4034001a12450048019904041c0c007800600c40c000c0016082ca00a904903811b03034130341215200e0141d803003001c11156940540c04001410000206400014205c055514003030304c6c6503006001c4d06410010704140d4621168000b0f840349090015042c1011f040c03502c005682c40b01008007103006805410107454140359000010f28612042c2022403a070750002600038022032007035481010003a888a45003050342d0b03c0d010042c010006009502e102482c2c0050b9058050310720b4100203091003910842d05003080d0705a401000081d10241c0c0660840d03034144061f03a01d841c0d211806e5402d01360311070a02c81c1c3e1150100d40140c05800c3c001030010055880d890703d8034000b50b005400b400115010b00e07004024400c07684a103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 91380657 1250 91379407 91379423
    0x30b03060a1a010503010f05040221090a0212120304060c0c050619061d1614040609140108040507120302011d0109060e070b0a050d0204050907020f10180f05070b030a09 74
    0xd0440d40d0304c078108680c102c85220320301c072400c0d038105030401c0000d40c401c0704030540300106004070300411050200c407544540301600203400c21a01341c0c0103001c400c1d5a41d040714202da40103e0f500340d200c1c0390b043c0140d0350440c0e000703c00001d803c03d1980c0141e8000c01e40d41005005807192604203c8820400c00c0ca6405c0090090b00a000c00d42d5118680c012a01000e40c031501801c99110006664180c2a880600354004c14502407003125100031b401e41d241d6100c2e1b041800001c03a5000103010f200b540075416030740c40b0000e203001071092070903444494030342d10310b401192860a10000240c1c00d145c804d41010030428101c6035524a01b0350544000b90003003000c81c030101c48140c00d1a2021040c0a408240a41101d080c09103041ca0652a01d408481e10391002d00c130498075560900002c0b44075250007400601c03441050f0000c0c1907034965000a00d24041010a40ca80c201c2d00b02400c11459030f8541003030801300c07540002d0702d0100041e50f00c0c1c6a800c06000303401480400303002008000b2009400d800c64148a4010020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 91381907 1250 91380657 91380701
    0x11a0714060c0301031a0f012108130305070b040312050a1205010f0602250501030b061215130501060203041203050c01051006090605040b03070e03100c1205011221030b03060a 77
    0x2040106c0d000445409442e110b03010010010011402c1c56154900c80c4007151400e0200341741c0e1403080741d40000c901969403400f60074041c001c0050400c881c2000d040303003050660a0500e1a9502c2600070704000482c0200400401c0e00c030104da0155001c1c0d0001001036106120b0f039038540b440b00701031543c41d128200040c822910ba6001c030211019400f08410451142c01c034640d4141030066010340300c084400c5401c100b0030040c074801c5032241840180502c0e040c2e43c048100180348801c1088019000f1104102c0d5131820004020094000044400b152070040d61800d42d10064142901d090144d103600d002d40c3c0d42007008121883e149034840c1015104035844d03854100c1e032074090840d600d001d07a00901402c034008101207081ba50080b4120121080d0050031980644091441ca0013601c90040c454400700744030681c0070800703003001c0c0519800b61a0494103a152079003e5291000c90741c0b004641d0020b0311300380012240401d403103500b24000c120409400c4034681d042c000c00c0300c0020209040d2008041e800c0700c1b5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 91383157 1250 91381907 91381943
    0x12060b01030b0405060a03060e07030203030d0501080c011b0f03030906050406050106030c0e010e09040c15020c040c080702060a0b060c010e0604110904020904080f130b1201060503011a0714060c030103 88
    0x4034860103a60094000042c0310301f0743c5d44640041581c450011003501c40c0b56030003c01650104020600c01540d41404602545000b04c01450700c81241d1006050021008404860504200c1c0040c0c40382d41045901000d035640b1304050b8020711490074054a064107080c10403090240607007080341200ca0035681000380d04440314049a1000e00d043d81940051040034803034840c1e1401d41c034829046401440001441c07a6509441d40001001c0104180542c00c40710400036246028401c40c0d8103215541030410aa2800b840025124840144541500c40c1e480954031602e40718502174176012101c1e200200714036490181078958407901240c040740d589025a11038070141c14411210780c00390758050714110304c50f01d407a51251403941045101c242c0c0a00144240746510300c4504080d0010502c040300503030340b0342048100c4449200c0c1604101d09002041004001e01c04184000700001d01d8800300461300c420b0b5514010444510700c0d4641c9005110340c5041c840e08401c618000c50480303200712403000a1000a00f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 91384407 1250 91383157 91383161
    0x130b070809190b090405190204080601030c080307080d020a0903080f1803030403051203040f0b011203080a0c05030a0f020f040608090d0206040f030c0321051e04080a11030412060b01030b04 83
    0x10040e0301c0c92000c01d01c2013041a003001d4110b40c0c0c101518100c00c260000c01560903004a80040e0b104030080e40c807810040040c04044040700e0042e040100c0a1454a21180c40341080c0d8482c9010803450380d640080d10040881c4204901d0b40510381c0094019036034441a150460705420241d41601c8017407412120703420300d190010071102202e9125000d400f1710140d504802d81e0903040140181e9003400398260460025013100c91290207000703442002580f80701c281c14010081c44005102e40c0c4120700d0f00002c61940c4d50450141c0354000400c94012a2040700b210288c00070740074118024440c040042030202e2030720b4203c19028801c141c48000c0b104000141c1c002282d5a01d025500a00507121000400000c60b100d9444100e50318003e081000181e0f04050402682030b03003192044c04840d540c1d0051011030784c5030745088800703c004400304489074185622442c501d449030403002418841c6140f60203644500c14810341d0000e250b0222810401441420048050204500c055000901c2c200d0400224070300b038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 91385657 1250 91384407 91384409
    0x10606110102131a04080f0304150315031118010e060114070b010302040f1d0607080105030706080c0721020307110d11041a04090c05030f0c0114130b07080919 70
    0x103501a02c283ca0b107000044054803188026000b034a8100b00030216070010100031000c40c0c1c500c808021641e0302c1c0340c0346506480c00c102c03209000c1014203019149a001c040780e1076040540c0d4009009401024400e000981002c81440c0b042d030540f2128000052001c20f0001c6486c402c40080e00c90042da0b42e816110703840c952207994402481c03201a1001803016041ca9400031400003090000042d06201e95045400d0352100807031410201d40c0f00d0000c000b140740d03201d00b4590040c031084e801403072181d0a0400103041c140d0000c06e20081e54034045081400e00c40d060005c42d40c0951034030b08004140d103590700c2c021345030340c41401d050361141601ea00000a03400d040302d1540c0e506810054400000c0301030380400000d46509007034a0303100480c2031f2800b04190f0b030350b11461548500c9000c0c100305092030403003031505145101d600e909140e00112588581c0366009016140102e240312942544ca60144841041200480d080284484400700c0c50208010380500104840da034200d0700c2c0310a2500103071080c1c1e07804c221 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 91386907 1250 91385657 91385677
    0x60312080c12041e050d03060806090703030315051f0206160f030f0f05010f0f0801020a141b030a0302040914090714031513020a0905270f070305010606110102 70
    0xc01c0204408404502c01442e412a214418507040d50114100e280c414030020442650036800081c0400c02c8103805100b040b00504043c40a0b00d103900c0c050300a143c0300c41a5100c080c05064844400602140d01d6010302c001420000b0040c621001c1980c81c10121034420040d828058480c69001c41c0145592140c0241c90104541d9811143c108540d17044014080c5e2003454402c140e12407080c0c21003032000c0c0c0509400381103c0c10038240300034500104030f200044036900071080c07640304000034140954410004a0304041e5a25a00e03078501101034030348804a0440f41036801800f01041000290381d140d0000d108407003884905000400401b21b1520761f070701c0141c07820307020355001460400c004030080941d03168000000b0240d642c403d81c01100040c505404903a1124030640064092046241c515031aa0180c09044401c20032071401c00002d035450880c846107840c0d0b059800c101c0e101011410083c81c5031600480717096504a03540c0386410360207480300b80100c0d4042466070726208491201407090724941c00c3c1c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 91388157 1250 91386907 91386931
    0x10f0203071e140609030d0b06030903040506031b0408011a270a11030c0904060b03011d06040204031506091a060f0a020109120801030302011401121419030306031208 73
    0x3040b81d40408003514040022203c00751001d0000701405030a00007503104612000c081c50751100d281b000301c2c089070f4000b60043d2117800140f0500401200c008281c50544009807803036550381d150340c44426404480c09064500c1400b0010300415120010b41010701e2101a050304d00c00500752103000c01c100e40c001e103602c80c0d44c24121900112402c1e0031810800303030415009000021003100d50482c171400d5a000b26208080d080d40010241a2030030a0700c16038008042d00035505045505001a808002500104d46620504e540c0040f034256503031941205c0040d544550540c501007100050000a03216a2040da070303680e0700c3c00d0b4000c0c0384810707180840d0400c514014040c80c5404070000c00449545c020b0601030742190350701c11000780000c840b000101e0046400c0d4443d2400b640c95858001c0c29902114004501c00034a6001003203e03a16482956900075030241c0f003100d001100740c0383ca6240c040c40002244006050804030001d0580550200090380c3c0110807610091001c500c00740d807051020f94801d20002c0f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 91389407 1250 91388157 91388183
    0x7060905040e0c12151e06150415081006080705070f022b02040b0609130203040c03020901030320031603050c0109170702030609010c05090108180601090b03010c09030507151b050c010f020307 84
    0x480d00100854203207803040042340c00c0030340710140c400222240001e0b407800705800030140702582c01314130020350042046d0700c0c1c07148452a05c1c0c0c400034014000c1050081ca141c8801e1410000c55031068440c10000e16094001024684030450319446189004010f1303016901d040d10041c610306240045519a240c090701c0312030718401d19a003180007980014401c4d03800710368900c0d0200040c1e6415644034000c42c001d55500c4400d0020300203144929640d03258042c0254000c01c2105514010365403080039440d0582407241c0c4039040000c049002d04011003004242e000650403501c510352144d4080c02c000f40c025822582ca0382d131100360302d50803035200c0358450740071640600280d0b000c0d40c8038000d11130340035600d6040c02c3d110785902d5641903d0720000f0380100e403006850b4030748855142400d1051084400712840d1082c0010300d591116030b22208a0700a9030302e40d145042d41040500d00822141c02001050480e4400740b4442e41806500c628014820b540010740203400081c0040c400030039a20385c541c012442044030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 91390657 1250 91389407 91389409
    0x1031a010c02040f0c0e01080f060306040213021603050406090509190e120703030b01030b0907080a02030603070f0e060a0618060c11030303090106030b010807060905040e0c12151e06 80
    0x14600390340308036441a1560a150803c40d0940980d0200e68016140c6140d1b000300c11001410160005140450b2540306100300452541c000441641064064401000515045078284060301c242801000c0c9002c40b08000410954480010300844c0d007141e0792401e005881d0010011088020b07a07031000d80480094041c55075114a90141684049840c100c50482c01601c0581442d40c01400c003c0e000b01f030ba906c0d8a20100d503014015810002000c071071000841c940f545010b010204041c00c88142658080002119a2020403000001d4483c603400b102c0c40326038030544420382020441d01c25003d0b04800c0400185540514041c1115602c000c0030350341039a041841c11603800900507026280e61541000c00140703600e06100441c0a0ba5401d00081042d909508000010322010780c01031000d036102c040d0810545a204200c50300b5035000b00c4010800c0442501c1aa1800c80600c100e2640f0205030000c00c2c0c0741d803500161a09001103851003034417080c1d403a81c0b1920030480c904501c0030b4010502500040751 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 91391907 1250 91390657 91390667
    0x2606070509210f0d05030610030b030d08100b0403050303090c030a03021c03110403061d0f0705040509160602060117011e0c0c060f14180c010f09081606030b01031a01 73
    0x200d81020701100d16251a4802e05032410124001900101d94000284580c90070400401508030601e27080034060072440700c0220f591b030001c1655a004104401c40410f112100c07911100005007041880952215181e0038442c0d181d80c41911044090303c100c06101d407171801c022440b0200075405070081c04541244122070380a0034265110300f4200369407081a01c60158200f406440554058040010b64043c150040740c440c15925098507007680c4280c541c00303243e0000045050540340b0580d4080f030140c071a40603035071410b1908000920800241940828081d0740001d08134102c824001018484940724540c003400c940c020480d80611990307402d0307017540491407a00158401c290780d281005040c480d94a0b024221007882070054a4a5116504001c101d600341140a804c03c25406481085d00c0580b603e296441003c0b4003000d050241e2241545900c90190b40f14000070b0400d2802c0e5000c8941e4484000d140c0d040d80e01803000400c0c9032058410095101c0d1090301c01c0c04040300010800501c0260055403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 91393157 1250 91391907 91391959
    0x1106010608040308151c0203010b0409020a0909080d0f150b03040308070e030a0507060302030910020903060a09050307060e0a0b011707060e0d05070306051e25092606070509 76
    0x1d20301a100300e030311240c80c5d80350300e618403a170a5906181c06d03884510425095034401d1000900c514100b8a0034005030f5034481d084011a2040280002d164000385090056401240c010703030041480d0220001040070310b03802c60b60719603240c000c100d05001e07102e101c00c1c011400180c5000d00080c3e601000194060b00644441c10700d0b20005040710300ca000d81d03070380d1940303407200301d4000200003074012041c00903070007007000540519240d281055050008000107c0e03030300c001c010543c2202c140c8540c181000c0c04001d01c222500713640c1201e014000403030744040c09070355046044011200100e1100c00081e022a0000904d40b5401c03d08018020403868a402141c1e07000d1012800c50b841412800d010740020404c0258000851040c1e20100d96840d262148081840c4001d011014a0340040e0800c00c040e0184003440752104010302c104070031205002021102e10349150080b0ba800f6220b4140582c01c01400082d106516100100b2102c40717560f9070704111880d005d80303840250020300b2203110051001d03000f081e1007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 91394407 1250 91393157 91393171
    0x901080c0402072307030b010501030c0e0d020607230c01030e06070c08041e081002090303070b040318090b03060a0b011b0515070504080c0102010b060a0c1a161106010608040308 78
    0x15900740c0c04c1c0744140204400c4c80c0d05106581e119480800c2003000c4a4800b0340142024201081680c2424001070300032184920810721808804401c0000c550741e80003540c1d4503980100300e1481680324400b5062401c000f41410b6241481443d401c020158828000ea000244d10ba00141500f5101d20700e0554007d1510301342214407840500000c04c1045d50076125480c0740c005a1810720300310345041c44180c10b2000c402895048940108085841ca0302d00208440e051548004546000c1c0d6036030034101d03030464121511200ca060105400103801c2459008640070b818203d0550382940c84004041040300d8800b02c803c0d0114040c4264480c4a06903040c6000705203008005840c81030121080d00403d180080700c0c01000300b0000704061001040c100610340c000d030b200f030008000c1c44085400151050192540010802104020340000c10070050032075900301c1000c050142030790600710100f81c014602041544001041d401150b070402d600068068103c0c0c40380d46411181d074503143c4045a84a000411f5a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 91395657 1250 91394407 91394423
    0x130f06050402130f0b03010602030a0f030608030f0d0f05041205180a0e16030504030206010b0a230d0e0a0c0b0c0304030b040308060406091a010e03010e060c04050a050901080c040207 80
    0x180d281c84900090000b241401003e026581c202071075188514000e4010020520083c801401f01540000803510307805880e0800090700b0241c52012400340185401030805404080b6030614255004006400c0d54084507605001001421800030105d400858002c2c1040003204801c3c1d0800c3d0150004051204c1d141906811006c00b60001c911641d02c1a031000c00000395010800910350002040c41d070b2a482c3c54035051245c5c0c14503440003551703144103004844400100003140c41c20380703028103aa100240d28655806c1074074074a00d00401c2c2190030441d21940240d00341054183c80410201e40288565800780845034200c2c18210b07580a15001980f008101e80f00400c40071000c159119100d40c407540c0309a640601510f40b05050105465007a84807040719400c20340101109036001d5440c0c0b0b90f66030207103880d00c1a040010006030140c5070301c19000d030361400b401e014811110f412100070030035900c0a9a4030007251b5540c50a000200d8024403402505801902c3c00004614042d0020720b0074900509031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 91396907 1250 91395657 91395659
    0x50603031306030e100908070c120309140d06140603190308010902070c1a0c0d05030f16021e1b01050301030b0a050c0910020607030606033b0d0c050f010605130f06 72
    0x40011284000f001f6290a10007040c810108004c0303076109409004044000c1c040d840103544c01812104160090a400f02045240826952510300030780c0070594000005124015a000d400503801c8015540580a8068010201d800c034054065802a540d815540d850351a03107019180c2000303401c803001c101c51148062100244400101c022200507440c40c000099032401c150201c00c0c6000101418a018820144208140c0a0001c1d01080c1e0000c0c1d0743c10101c4001c044202e04a0a00201c101802c500c101513030a0901e0440c0000f03410b43e4403050402d08101401c2180c1d0064440c0d010034440105200c50800009060550303e80109070402c514030812030801c00703a00300250b0754684001c240c00c010b074015801c1140e0268180100340c01041e00382810815901c2d11440e01d0b60000b810404183c14120142c207030145d0115803d0700c4c6002c50400c0f0300740c0b002c10715841ca0040081d20100010f5545100310304165103180c0043c0304044c115903000300803401401c000800b500151412100d01d40c0a070790380e068 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 91398157 1250 91396907 91396933
    0x210a050f010503300c0601090f0b0f01030207023c09040c1e18091b030206040911090d050c010809010c02100f02070210030f060b07020907030e0f0304120303050603031306030e 77
    0x80c085d10024407015060360340c10040000304660100d80800805410300300705100d0307500c0f54000e00400882c2841c015940384803e0002c90310901c3ca8940018551080301c035250b0741c0b400c440c0d8148000c1e4810700c20010040c2d01c08001c1000355035050b2070241c1a244d0f460420005c8100c1c2200004190700c1482080e0501a07940c44501c0c501c48000c01086078058480e00c04c1d408100c1039aa4500010410030b8031b40c1d00780c034150b40100e0103e0280380a043d18051303032842e2003600350030381c48280c800001001f0815815082285045500c900c01e0414040c081074891001c504004018010619102d02c00c3d801000e036916285014400340401d504002c40c250350811604004d42c5441c59910540056600c0205460b4125480f08007110710940c40f6020081e0140700850059407284040f80e086403c514010818420100c02103082c103001d86003041c0345110004001884008584106191600913101040389a91b00d1003407580700e1051913180030192000c00da09116075802540840c88825803071080311481c80a601e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 91399407 1250 91398157 91398253
    0x9030106120c140d0c08071401020109050a020f04060504060305101103040f020607060906021207140c030403020d020a080f060402030106060908030d0504030e03031303050c060406090b03040503210a050f010503 92
    0x1402a000e95004014280702310f4405544985203108284000c10000b021a1070300c5480b03244220000388940307a03010a10b24543d41b82e80090010f440000e10401420795a4a42507076a040c024145403040c60030002c0c20800c1515200541c1c0c071507a00442108444d80c074a600f000b55a5002c0345d82184d4250399604d00c0703008103d0510203400ea140c501032002181e0f00340140081c2001981c150042241035040140d080004004004d5a0840b541911040c281c08000d00c0010705250b0320b6088820544112541c40d00902c000040f1036001d1070080d4020810350341c991f1300445022460740500340c80d0740d004011500500c071440d03200c41d0380603029240007234810230700c000080d0840c0c1c0824000b545820b040b40b41401482818404403400d050100e50242c505132030044044c0c207601e5180f081c50000344001c40010244038062007200c0394041e10a807a428040c801514500e441002038a04c103410b00e00c0e1400003900e03c1c0c202d00700581a40e50090080054060154801000070304500d80355a10008000c03452040c0c903420 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 91400657 1250 91399407 91399409
    0x1170c09012105060109090203010803040501140903030a0f08010b031005090402010309120f030509010216080a1404032307180c0c052d120a0e0d0b0c09030106120c140d0c 75
    0x115030100f418207200c8001000c580807500701c4412980304100402100c200002110112a030a007440358915226a580504074024240d480da0103010000e414582c89500c0414201c1c1c8508a0f120064142d80701c800880042c0000c482c01d003040d00ea0414240314a1401c15400c070f5019105140110b162901c980d11440380b03408200e000c1000c5a505143e01c04c10035054003c041d40200381000860601c45090000040541c1c00000941000400502500c4003841804800040c42004405a99540d42c034a0300c03840e0011030845412030320700f8013010301d4001c4202064080880781d00120412807014035050500c000c1160001010611601c454280f000420a000c5440359070074410781d00c00d40c502a40980340c4401414040304038070f6002078504400301c5a100007030316044105031901215a101c0640860b8881401781e27070150100752110200081da00c0303441d00400d840d45066000348092951600751100008101c0c200a2250b007003940d09100c0c100c030b081a11842d90a0080c407007180d026041d00c0c0c8070004541 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 91401907 1250 91400657 91400717
    0x13051204050f03030915030c070602040e190b0d020609040b12061005090903031b0903030c0708010609021204020d021c0501060303080105010f050a030e0f0f060f0601170c0901 77
    0x30804101620782540c0b809a15101034001c3c620b0080903000252804048401c0c82d0511a0088041404036044601340c07003070707903500100c01c5542c0d0761038520b0000d0900f401c917003c0400c582811491a0005c06500401c001c1c02c4003d08003110f4101031783d00300940794000500c83d03500030b9581c1015015550b1848580d40e40152510050200c5042850303400003440e41d560810342c01510200240009610002b0807a0b5022808004a400012500500c84014450307600c0807585880b010958004190011445204444514008201e9150f0f101c406c0002e0340144813403441440c08203c002005400c2c000d00144002d880240b5228203083c1590f402d5184400d00f400c10748403030790b40c0c540c2841050b8002c8099030240c2801d00382000d202c4001f0700f004009100351b5604100300750300e45045a03032540e8200800f070280001c4006880022203824801d80d5070710303030481e1a00f40e03091034000481e0310365006942d41c44036000c4c00000740700d41c0e45d215440c5c0c581030781c40749072050b0401c5011007545940c00c94420000c01401e403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 91403157 1250 91401907 91401943
    0x20c101e140f06060c030f09040f0e0303071713030309020301060803030c0c0c0a05090c071110030f14100512070f12020f09190c050f0409051b090112051305 69
    0x412804450b180c0b100100307aa4015041080668050034002042d0b6008410341d072001c07039032032100d03102080c09003015401c0c0040c0c45003040b400321a102e07404006540f00c4d0100d540c0f501c1d00c40c5103822200a034050181c845400d02c082c500d45032402301b03109400c285522800a8000303c0c400c3c2c0d4980205156038030841d2254040000130801c0c040f0f04074248600c06041c1c0c0e01b00c403101c010720306000005507088000391401003178440009140b010000c0d240401610080001d0014001c0c1012800142c080c00301f044c07450b020140752000d040340c0440035001181c001c1600c3e02c0c0300ea840a003000705100d40b003820290918642e21920100160f1000e05c001c1e00800f030a2000c43e500030300751051040c0008a030200c002c20748038119400411007843c50040402640c0b01c00d000700440d05054420040d039130707441401d8036165000030000340400c0d001141c0d005a406000428880010812103060b445554029500440d00050024401d00c1140b0400e8016a40140690324044024801c0d0307036510b03250861020020000c56 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 91404407 1250 91403157 91403161
    0xc060e0111010b0109140d050109031808012a05130605070b0f04020f040c050d050f01030b06150316091d0a0c14030609090c0d03020f0c04020c101e14 66
    0x568014034040501d0405002401044075040002e0082001406072080d84940d40304c0c480c00381e9442400c018070840e0004000c101d142e0481c24024042c40c04c88002504a4096120004103140144551059241d0310080d15910381c01c00004500c103c5201442c07041080360600c03100440300003020a000040c041c5865a941d0764400d45800e1418007401040c80c2c2d0004041d40c00c0101584901c05a07480001c4111800900c2507103040b42591580115404101290b2501d02049444a040e08d011030681e8060f02062086035658001c2107082c0d038403141c45841c110b00c1480460351030130180103008101d0200d41001540d80f07480b55024004204d03440c8800030202240320900032880400d201d5862081120f207060041100710100644062002510213401803500e1000078007905400d0080510f4550b000781140007210702070030020340e10480004101000d0150f501c000146140c80e10894022a524030040c1842d0310340c2000c0c0f1001000e840d4205188049081d40c3c1d10340303242d410b2241d0000485400c101840354 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 91405657 1250 91404407 91404409
    0x403051609060b040506030a0f0e1603060e0c010c0807020d02060c0604060c0306080d050c0307021f0e01021c0e012d0207090908030f19050a0c0807020105070f0507020604030c060e 79
    0x42c42c00d42d0b1080600d000200800d015075213561041f2648070341046c802160070202812020000c2490600c40a294000c025440c54100400300804049134020001840300700d003001503c1c0e40351210301009130301107070b001c4524100151075a005002404d00050038030104a00c240c0114156501c030140d080325a40005040104101543c807800d8015091480c04100391400c1018107075640103000d260905000010581c0c0008590410807a008694094405400304d003180d0700c4e04415442c1060030031b0105000d108840c10a5200044a0a103441058600a1101c045582c10787c8c1070049010b580d0304009040c40507856507061081c103088041d2200e11600c40c001c03103e110013070804101c0d803c8041518207004080b4085040182501e8103c849550090426218295405100780e1400708160301542400d081014007001540118665070854968450030390b6110340807822103104640a5010400329400318250900c0741015203c000c0c40030b0200b625141e22500c801c1a42c0080740d0181000880d415840041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 91406907 1250 91405657 91405661
    0xc0f0e19171006060519021b120304050604081e0c010503010b0a02010f050c1809010509070806010c0c03030c02210a0b070e0303040e010f0e0709140103090b071d0d02010507170403051609 82
    0x94145c41d01c0030b402c00c00910b102c1100100314182c0423500c540030000b03030340c810440c1c10710850b8004c200040085548680d201d00e03c60300d034104041c5041c412071188001403104200410000710b600816501c25141da802c0460803445900080004000c40d9070315518421a640386115050044e070400021684a100d8181c40140e1340c490211103900607002480100110303200c0320b201a4210700030381043e2000e690f80f4401201c0700021048081c10940740742d42c00005143d00701c9160b0b19224002d454141c58521032041c6d080c1480b5400480f05016400f1650000201d421800b015810a1251501111100c81c2c58000ce2a542080d00704211110b028401000443d0701c3c030040c10010454074000c0910b5250603840500358250310310404140070740380340903400c9a0f8440d40c4030110351984592400414200444018602d052082c5941d0f012440303d200e50604c0c0c03910740541451180e050395101d02c1e01d09640e03102e494180800c41c600741d4400c000e00012002407018042c40348200a8052046021031504c102c1c041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 91408157 1250 91406907 91406947
    0xf020906010e09220b040311070506032503061802040905010806090a120e040c0203030601140c0705010e04090501060308120c0306101808010c0f0e191710060605 71
    0x410702000385a8481d194403003c00c1d4a902140e0301400700c11181e00c0b0201c1c03204120b5103500c020700392401003082100b01030b0081c2c0d14140104052003200c810030749900500034544001c0d90300c1d84680014481c82c4211509046940c28064141d240200f03c043c1d0321011003210030300450402c14840e8000c2014020303280f01d4030400e4014032801e0028042800c0404010303442e89404031000e05500c40f50382c84141c06078000c1086d10102e82020f8004c0050600d411002500c0741c00c00c1c2c41d0180003603545002200c2d07100302c08055800b60344007403019244142ca02801900c107108010f0715103401548841426001c00d9080c07040400540c01144c215a441c6480f544105820030700500e090422181482440308680f0340c12140660703013000e8140400c00140028030700060750741d1540701200369030070800300300901c961007211100d8461a035150100c02e140d60070300700030000d885101011981d401a8070100300000484212160b514010000d0b00c210341c02c0c02d8018003e4074910307003201c800b141c0b000031071315644043c00201034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 91409407 1250 91408157 91408159
    0xb0a080a02041a0108010b030705071209150804030f1b02040213080709140a0902060706051f0902040b03150a030501053301080a05060a050910030201030608150402010c0609020d0f020906 82
    0x780c04845260f001800c0a01e040c02500c2c0140404400111824040c0d0201e40500d6048010040c00340d0000c2c00084c134034030040c040c03140d40e0180d4000500050717000e5810940070f240e060700e4890b054400c51504548446203040740e880140c0e050310481001d0f0311244000c1551010311900300e580c290030071800c24600011a880707a440780d450241503559141a20341040d40058010901190f0004180001107040c02000c01c09805a807400003844940606200c5034000110120221a40507070b130b03091481c0c104d00840c07042d61030102c02080010040209840040c090440c010503501c0210f41b2a1078490844504842c00000c4501d1005186860159a45030b1100b40e20fa208000107508060340000304021030151403000c440d515400411940da603550f0035580076040140c0303030f6069450200d003414560722451100b0b90109190085c0480c6c2030700040350340f03501109041591565500d56600449010840950556400d542c9503864401a0f49814841c0081c602844130302104100c640104030030301c0c074041c2000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 91410657 1250 91409407 91409441
    0x10b01091409041a0a0903081506161a0f070201050a0209031f0e0318100c0203070b0703211a0103060614070203190b2e17010b0a080a0204 61
    0x400c001030310803620384400d040907204018140c45030329124102d0904e4192000e0b500140724200000720300b440c1e0040c200d55000340d0300c0c0100c40d01c4e4424000c2c101c40d2603150b9141c0106041040c241c1310800700b01d018036117a09c10b8800c1248841380c014007041c200780558003d02c00b6000ca02c00d104000d582405030a0300404000c808500d07001d90000000d0743c03201d80400754181c40310301140384600249141c0c03215815940d050256603070340383c0320809000c1e101d03400a44148203e00012222500610415005c2c0e881c0d903014000703004681c02c001c500c01c4190001901141040a00c2c100307a0000803085a1030580720510350000301e0b800103c6885201188407446845040500d40705040202d503078440c403202203c45121048594454090012a00344100b80c48080c54600451418400300701400b1400c0d0b204038031038480100c40400c00d00f000111042080c40c1c0a005038042881840003220011b15806103e070504000104582200c0116104103a1640841d1881c1c10408600044d42400e000b00401d1011503142 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 91411907 1250 91410657 91410659
    0x19091d0c030403030c020f030a02010f060e0f07050f0f04030b22030e0f1302070809090a0605130507020102091206011e0f030303020a020a0f0b1b070f02010f0e130c02010b0109 77
    0x24031a001c014000780030140c0b560081c1140d076000740201c41541d9024420303240c0e182080d01019002e000c0030102d04131101c3c5008000200044044580e6008440101c107080007074880001c201c03459042000c1c1d0766150001040b0b40c82d1071211407001030004600c81c903c80d40087c0703413034006458103080080c2030450041c1004408400a94018108406050100c49015a81d8943d901045807100d886221001007480000d0f00c1c03088c46100030181240c050100c41d000390507624420000242c4d0306910035103802c400c95118040000c8000e810681e17000b0410310005041440c0240069800e00b0754448005040c0c01ca50f0051009003202c0da054034141041451050b4181d00e0001c400905000c18400603003015408603200c02d543e803083c0064101650011021180f103516420145020f500c291080b8a141e54000d0340e05200441e082d05880c07070190000140c4866000d41d40041d18450120011101001496116400c070303951500c49045070a0b442d142c00040040780d90402a0840700c00e42101410700c403035694 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 91413157 1250 91411907 91411921
    0x6050a0b12040b0709030c080102030603010e0d050405040506040f0516020f0304050108060d08070b090705010e0a15080402210a02040507110307120e040c0c0308010e130b0c19091d 79
    0x2249a030050f60004200c0c0303207640d40100c01c90b0400100e4200412526000d0000252680150081c5000b040c3c210000c00001201755029542d5010800c00c01c0301007401071000704032070314103a4003036944a00003a05c086030b507420140c58401100c0045070fa1681e44e0684900341c245040d0704106d410b80444000d002036103028103090010303113516001444640b144208148035004c00c0550340c02e4601c105d602c01d0b13402d00340781014801580c58101c0c40c014280001c20880702a0343ca807030100d0701d04040f20500810000c003022a4582225251070050050f07800900d0302652002c03c0441d58461041c881202c409005626045d10400c4251040034040d50100a120011140505004012642035aa121034028a022840e08040ea0143e4443c04480d61107840c140842081ea07800004141d1524130035680c204050303890380b8a040c44142e00b1340d02c0c894171000031940700000680c2c80c05010307080314454a1090801a10700c1e241283c0d0500000c1901c00500b2034a030421180c030546001c01980c8021350781d0503100d0300e4001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 91414407 1250 91413157 91413187
    0x1050d020607060e03071a0709030c0509060316090c0e0a1401080415050411030d0314010b0a11030d0204031b06020d05091c0311070e0c0403062d06050a0b 68
    0x1440180c030501002504100f0881254080203141d034100c020b8039228000350070a480164420940001c19001890005080c43e102d080d440003a2035000c1400030005060806200305960000c1c40603030184911140240d40201c101d14003801000d15403008503006068030401027041240e04005802030311106000d1001840c00c50315004422001c1c81c04560f60340d11400c00e09001d400103151500c409140c0310034401848100402c1c050b070726400340c4c2180c5804451010481c22181c0c22980f51100c0d038965001031001c60640d030028175940ba0300c1d240c010340307580b0761841c1c1c141160300192040d0b0b00c0c294000350410420018a8803c4141682c42c100c2d81c1c0510f25103a400ba469a003800c00e0182040380c001130700d081d540e43d0700c03a44a4103c1001d50340340c0b213048920f140c094600310b000c0c4032200700e82c881c070f030000504d40c08440311451041100e00c40c100e040500d16500c80025020815041d11004c144034102c820540700c0e4100002000102c160204001e0314103401d11040b0300d03407078021707081c10a0704001c580760981c605 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 91415657 1250 91414407 91414429
    0x90906050f01210e0a0b070c0b0106050307020708120408010606020d0c030e120a03020f011b140310050306070c0b0115210b04020c061e010e0705090d0206070503070b0606030105 78
    0x3824042601c25282401440d0b955441d82078082d464030b80100130300480300000d228141c0320700c180c03141d54150312038441c152100c2c001120001c008185900040c0a104e00c10700107107401400300e00449902a8035a03002c40e0408400d2101d03c0300b49007001c6402c02108009006071001459180050644005002e07001400030042504c090b0a03c19616070b10071542c0c55290407081c81c2d00d81a401e84402c90010300d802074543d10188007420039982001700c001820703041203e001c00e5201c52034440403c00095a001d80300c060300b00900c006030052111100080b070303031410301120f8403844003942c488004802c1450708002d204010380018000000d400f12941d6074503040724074250140313442d4000704241007480603145c1c081c0000c08241504640041159102c260740010450b004501058515195504a115281c0828801d00c6071454400c020000310b44094020b034001e08040340043c00b11044040540c001c100107910003602180d050b88005a03420901c0799003402e03183c1004003100c0d09451540b408001815280301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 91416907 1250 91415657 91415659
    0x705060c0711100f03150f170c030601032a060c020d020415060e0a050306150907021207030804060b030f030904020a05041d041401091e050a05060c0a090906050f 71
    0x20004034a414031800b100c41480c0e03280010055191a0781e00c0000414440c10003d0110100b41420b81c0d003041c000c0e0146894054a204000c01c01220303240503c1081840c440404820850040d4451031000741c03800c0c44914003a42c064910780580d102d0700c020798080c43c20001e641d0858208052002d01440d6400104500407a40450720512403122900000e0004c1006001c0300f0322040d500c03140050300341d4121743c046646841c122080c9121075583c000341500d843c02200c00204c02901001c4841d82440c0c42489150016a0b42c8125441d41e041c400600f03140380d010003025008591070703c0800c010030800c3d0050549611040d4058450003043c0320340c45680b8011030003030710311850300442c9045034248110700365002000c070482c103102d40111483c0f20580b4581c013558191a50500c0031880d41c030b150703414040d0806003a40040084d00d664407100f815102440e802e0350417030303a50090300c00c0400480c108005460140a403108500d54404903200042c00080555204032038247c20060100b0566441b09201c200483d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 91418157 1250 91416907 91416931
    0x30907030b0702010e0706110f0109020a1e0320040b04090f170c010f090b1b090d0204060b031512160e070309050a06020306090106030b0303090f0301020c030408150c070506 76
    0x580d80b80a90260009445041c000c0c46150b10008200750720041040c81440c800e01079507040410b8a21240c01c0e10030440c4082c0d0002d000080030002d4598103241c0019000403030549420464072642d0704400d0070030880400c2d80c0704100d000300c01c14a00d05031141054205d403c030380801c01019641d80d01840b13045e42d540003401d1408a40404592035034140d040b40c035000103100081049030722072010139000b03005407142901c14106c96000a010f504001195158502c03120103440c0c10f000340c0b1000c111841482c00da080b6041512a0400180f40c0503880145000380b164004e0b542401c11601d0510079801030310001c04c86568400001c036052000504e01041c01d823024140312420356520140182c2c01703000c2c0610028140d02c1860030203020720203e64007941c0030b424200e914000e140d991307880031425100900c01c075581c990010010021540f800341142e0403c00d00160025082901c00d101c0c050840d0043c1d401203110350860040c818001d240c02083d681d014408909050800107161a070342e03030300c1d04014a031201ca14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 91419407 1250 91418157 91418161
    0xc0b121303090f0806040624140103020f0a030504060c05190507050a0503030711011406060f220f050301060905090303041b05040c05040905070c08090607021206010e070212030907030b 81
    0x180b082d68500b01602c3c0815010f0a842d50302c09289a0b580d004a405a40d040d00e0001c0901340c0344e081c95598204103040240e282c45540c01c280d0442c0f40c5000c0c2c3c2e035000381415401c02000d2410401c80c0c02824098820703403000035040c982800c200007514000b002da0400c0200821020a0040c0340c0070902485641d68500036403150882c5c43c0039403508d000c2510242c62403001004128105078880107207560840306000901c42074805209803c02c078203080e41c1310740e4400020f003d440a0303220b204014088040c0c100014541c4610f00f840460001c1007140c2102d00d0341c1103442028042030800b402198010580d1020400c6a0714000c502c9030348038000a00001c00940c070b0000100140400030401c1c07005044020010400d10740310f52000703005c40e44584504c0c4c10103820b080000340ca040c0502c3c1d82c10100c1e900103000c58a070411242c200b02e1207a008410880c0d00c018030880e0254030201c10002c5030702801882150700503034100154068903004d070380da070420b17070300e1004200300810100041040411250b2003403c1d035040d6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 91420657 1250 91419407 91419413
    0x1d01031b031d0a0803190509060703051f030c081203040c0e0403020a05031809010b03101a2a070e10061409030313030b010602011a1c0804090204030c0b1213 69
    0x41e440055020418441e0602c0d075014000b04034010340c0038820b50380443c903264400c0206c14040d01c404807118112500003100142005009411203a440340c0041070000000c60001c16142d405201500145c601001d02c000071b000036041086102c120186607210542540b8082d40c800354405030034002c840b110301c484400318040500820200340056030150aa0741c07202e10101c40d1010b020035059120348115200000000c483c1d00510483c0c1c0500074160500d622203003401c51094018040407450400341000300000380110202004501740840180040d00b00304000b1031a540c27500801c0e8200c0c1a0b2181d01d0001e00c040c80c1884916603046400d5420b008070700303080c0307942e102d1958020150400c0d0980400a080380d0380820b40c06444054901c41c107000c0f2140e0340c940f4022800c82c0c0901c0e40ca03034a07001e40d44000100070310f080390354000d91107a03080d4442c006d040c4960f20101c0c0da0304642c0c00072080b070343c011400744200104120600c01400c003540415050100220300a041c071700e0040c007071403166219004181d080c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 91421907 1250 91420657 91420691
    0x10e0a0809061309050a0c081e06030c03070602210316030b0402040f030501020901121109011409150301210c031104060b03130312021206120102070b071d01031b03 72
    0x2261294a48000c0781613903d4034000003030801260442da485240c201414603580c000d90000b4020302c0607203818200c480342c01080300c2440390302070411641481040c03001945541d0401080c0301600c2030303a01408041c484e0a6408404401110b28020302010034810032503448030740c02030541c441c00e81d4907020480303074410750100b40288070703c0d00822401c007407500c0702009105054004010240c001c1e038a00824442041102e0102c1e181c2d5032a1029184080000c1901c0750f104100140d0131000c60380c611072511b080c40c1d0000343d4549807403540050245021004200814400c01080004450b031944408010b240e07a0b5001c00e04401c502006208819050300707035909448039030014000d040940c00203941c0b070500d591000f03c100800c00084000500c069031181c140c03146802501c00b007580383d200f1100591214800c102c504003100081180c999802d0200c84007080789003050301c3c010320041d11504151040300d96401e0442d070903800c1306410316041040c11070740294201a0100103201e41d140000b0419802490125 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 91423157 1250 91421907 91421917
    0xa03050d020d060909140a080306040b2101140106020f07030308071e03150b0c030403020f030a1b060e2d061b1506031603060203060105070204090309051002010e0a080906 75
    0x1025514042c3c0203d00340c1c109501042440b80a00e51188614040d42d101c10350ba151140c40091000c0018408503045051540142c145041e006102d452000d10150b42c0404040103590b007075020781c1d1569400800400110150790141c480340c80a046450700e0311254640d030380e0061100070f0400c420354000900030761007041d00f032b030010340344c289034280380141104d00402a002404581c425041d40c0701001980c9180402107542c1e95410300061800c151841c3c00300055079801e21010f9425010f48807000c00000c104c0342d500d400c450101c6e29802c040d14102100104240038240075907005058681d0030704900d248150400c200d101c2d403620340001d0001d0340c0e0b0125405d40103000e07500031200c99244011156501c00300304881040d42c44040e940c2c0030b03607074001015910782601d0800c0840c207580d00d2060002c10700c6500110341c404018180540707403c80384d81c086021201c8448044c0c1c0040c07540317001408280340ca144845d00c071010341d07c004d20105000b00210764442403881e4004101410028200f030254542d201070701c1c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 91424407 1250 91423157 91423177
    0x6030a0905160f1e030f0303020f03010801050109060b031504051018200909040b070c1a0411120c09040f0b0f04051203010f06051305090108030d05060a03050a03050d02 74
    0x1c0e4007645855920b0360811a1070181114040007040041400003060401e001c410202d602c0c04000c035032550711800080707203403000207600705a02080201031110020700158000c02c1402c00000d003170740c90009a042142d12581210411000800600c04005d09561500610a80803140004d807501d50740b540d500c0c480941d512018a0303854080d2008440911580040c0024a104000d2a095003c60490401034451110041d034802550004503011500920f00c455001881e402c0081c55919030751034101c2e00300c01206052842211070010402000b4110200d00e000e10410b641c00180d421300a10b07020340b00d41410250302e0189010400040a101c0c0b05101d04c1c0d0341c0c5d0381007070040c03c481c01e20803000a082c1c1c0f011038040d100c52040e0750b511040181c10a040b41d0413184a91613110b505070402d076046600741d20403018940e10801d1304070042100c1e941e44000034020114500110307a82c1411100c1c5000f950b0380242004e12407000510100046040850902d8002d5494a0150359984440c007120b00207015024102c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 91425657 1250 91424407 91424413
    0x602060402011e020a17130506040321030e1e0c01080603060109020a0302070204050f1b0304170d0b1801060909060311090601020a050601270b0a060513120602090f03030c0c06030a0905 81
    0x580c606c1d4000b0300201040712000e00798250003a02c420030f001446c810740c4402010b02d080c0e00b84104685140351b03503075004d8004510300440c41c20140c00f8080c0c909400c180098150328011182c10303003405010000d4940d00d41c3c00b070034010007070310702a030001c1e40312903051041103d5a40c00050b49001c052007a812165010f6009100300224201000000d8103c03004544225183c001200c26210f140d00714029640f1039940064030222111010b909881e080c1c00113403202821540340c4021300029585c0c010941d071400320005180445614080c001018a0b01641c001c0310114074104062003c286202c0748210988400d4450700c100f40c0710f842c0100e291802050014000b40544130010800ea5075003400044403a841c01d906080b9010b120040f01e00300d80812445a90000d41c004042082a02410141200f2000c80304410bc81c1d030790f9841c0c2e40c00c1201e400b00d41128020740c0000c100000b860302d8809407104c10000d500640c200400000c4d113659401c08248180d02c6580080000380e08880c8a40010b1801c80d842015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 91426907 1250 91425657 91425683
    0x360603050c091c050106050612070e12030d050a0605101209032106090b060901020606010e01020127120503040c030b0c0706020705030c01061401090b031509040f05070602060402011e020a 82
    0x588415283c515008550341d50a181000420b0300c0c01c1011341e07031000c480c1c594000d00303501c401209941c1c503800c00c030402d908040c42c660250160602480075000300b8803a584007203814602100341743d0880e05580c012600c1904016040c860b11548106a0301c0c8014150a0015081615080c181e60b46400c182e400c00d02c4c00c0d00102407208a4405400000840d61451028450889200c0070031089010b0b44195030b0050340f0000010f641d96202e02c00010040070f0600000440c5148100c4001141c605160899440441100c01108001c040c0305e082c01e24190f60b240450641c00c00d99140310b00d60585100141c030800d0b804e00403d040300c001c0380440715001c0c1d0040d02156140e0462a0481c2c907078001102a5400b54608000040c1b5090b8461003071004a405035550324006040c030340e00310030310f40000e02150408000c82e0bc00348466141c0510850250f40110b42d4422075410a240c01440c01040d40c001208541200c424880141d8010300032050f400c1c1030441030304030b1000790001203281401070b910242500c04000300c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 91428157 1250 91426907 91426939
    0x1e091d270a030909060b030a0507030e060703060e061504050d060605040606170f06060a0302070606030b0907290403020d030e04050f1b0301031a0711030a360603050c09 74
    0x118000c146210b030b00d615900704c0d5540c01083c100d43c4580b1030840351060410000d220000d0301c0d0302c0a0382c41505800c00161102012516511b0301300c0886905012035a218414054800c07000c80d01c03a40403d0488417a4100e4840c00c44001d010302403841668000c0211542090410016803c520301601000d84100001556a42c008128080c4405071900350440c0700041000030f040d804140d8401c141c00b0f001d0320f2034036107010b800310002c0d4001c090680b08076684500101c0000c1d2408110b0303000e41a602c000307100807802e100851280101041800811105000e00c0c500c00d8000841520216501220211840842c500b0103494030080c01c85030951040c9000201700c0903034011950310f0b001d40e111041d92262010707144020745043c0700c207000181560704251590143c0f80300c2036281540c40005880d0003008801d1404480b89550058405940800c103902c600d0040030b07803614851220040700410030900c00c620301c09000c000e0b2019000300c40400d51148000340c4848440e41c12984070100190040c0d4010340404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 91429407 1250 91428157 91428163
    0xa0c051c080a0606050703090317040f0b0d18030c03180801051003060b010f021009051c050a030522020d05120a03140609010b2709071e091d27 63
    0x89002410900d407103008100d41d842a4140e892996048c0c84050381c0b03600310388078414135544003489505d0703040c020007000c1500130440012070000c0400245050301d80d03005d0300946056548004900f8400071854550340c003c00d501460011180350142013060748040e0b10003401f0703801d60098220641941c2400c007400a500c02c1c5064600440b40900300400c00400035200440780c074607403000380c0801070784000110210466554072042c40c041c4030318202e0755040c0800c2080d0001c01100d0300040b01207200898242c1c0c43c0b5800d4040c00f54031101070035051207009a4031060030303401140c041c0007078007440040206000f0010308000705c1c040d181030910f0b284d440d00c080401c0140039001c6507100540040500012a07000c1c142001f419060301c1d210455181030020000f100c1c1c040c2d0008000d051092208203000414a84a101c0c0c80d6005800703e0350361030128255010891194400c1e8402041000514482008a12443e05154803405101c0701046981d480740d051462940c160302c0c20500c1020f0100442c0c0c3d154071000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 91430657 1250 91429407 91429411
    0x30307080d0b041a01020d08010602030a030f140403020303040b06060306090c160b01080705040e0106080604080f091909151503090203010608060a05010611370b100f0503120a0c051c08 81
    0xd82c07c035001c4010009088440a00a224850150303206218110b00140650840d13030081c414080300007100c0b2900d800703c1261341405d80f41134000d60400070501060150421a0315400705081d2092440c1d41000800320b01000001000d000381c0b6070003c66500c6072010340c0b107004500c50b50048140c501c00d585502c01c0644070a0980b246030310441c9803594078400380d4818080c07030003201c0b00c00300985010b6440381c842540c1a88400000030608a0400005849507110310b03031011242d1400110032041400c08140c0c070202d5070108240c501001c0144c40400003a041041c42d00c0c45003e03145400f0618044904c00300380500565049080c06003d40c20400101444662100e4125481c0350f860130001c0e051803078050b4030f650307008002c000c4842003082141d20148240d4040c00505c6669110b12a0018443e22040b000c80e1041c2d0f1903c1111301e4010082060781d9252032448040e2100702e0203400c0c1c0010014a2400307520400075004180030018440405001c000c0c801030001c14405950074001c84c0804500501c401c0003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 91431907 1250 91430657 91430659
    0x18090408090112180201051e0406020a02040608010905100e160e0f010510020607051b010207050a02030d180510020309120c150c030a080a0f020a020f0601060509030307080d0b041a 79
    0x1038040003c4100790b06004200071403403807080089840034036800454207030340000c81588002905002c0c0328070207062080200020100c2ea80074040101c81441048180c502d142d1041e03441e68108003145010480210320923614426842d40040c220002c14031403400c161a08102c1402c000c000480080c401803420755841c458000701c02003280580c0c0380c0c8200001c1200a03002c40005a00001c0000ca1aa008d440100f50010000f00030400e00d00d15050f5090a980c802407044445400640b4185c08505042150702c04804042c1420084100081d802c100754016500c03400384124141d008803580d041c0240100c441403480603140c88145521380710f040384d5901544024038002e585001920300030b0700080c01910010819500076610703111381e8500403140c0720005402000c0403a5210030b440d60020341032000701304008454020b02000c070002c1304c90b6800c0c080141c0c400310a0100811140001d80d03008021100200e0740700b00265200c9504200b40303c010404803030b4080d00545040c00c909002240700024101c4420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 91433157 1250 91431907 91431917
    0x180f1215050108060a02030405010207020a1203020d0e03100209130501030f050d02060601050906030406150f0816080706140f0310170c0109120f050102070c050901080a050a02010302180904080901 86
    0x94403480c4001121000d114048a0307400110100c1c9440d1004d4000f10b030494000c4c0000b5040042d2a00058440c612541c040e80402d060107580104154052110820080d41420608044858640882c0d29a03100c080041d11031540018550010741c2c13000d103c05440342d4080d40c100219038581c640a00880030000c0103450700d11811040c0002c0a200080043c0301d80d0f01a034032242440a500b0074490107405c00f500c119403054440c1c440c05c208203a11a8000b00400000c05421b00c80c1c1d2034412010f0904079280c3c0f95281e41004500d040c0158800000e8040c200c425918118100107800620540340d8010640010340542c00001488200300401c03040c034081d1084000003102104003072940d903540d29660320b101400308042d00e03001c002d403511b1090039800d0b0501900284103000300554840e400ca900c16034048a8a6080101c14006c50030241203240c09007c042d80244150403058039a03a9507408159002410940c001501c1035104200c1c001c10416894040e000022600340b600e44400c1c0c0750081a00903001135 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 91434407 1250 91433157 91433183
    0x5070815190b030a02040b06120718050d08030c03040507081c11060415020d0f02130f0f181d031b0606041413051f060620060601180f12 60
    0x3090303521a00d100a44010010154804c440e401d01003e84801fa03181c4d640b01d00248030940703000c03440c1d40f1483d03c0b4000030750714120380100700c060461141c5020307000680a404580a020700141d80d1404a03038100044440c0c03a030704c82c2d81354500946800001c1d0000400c6e4010228021000c0034045014000001a52116500717540e03c50181e41d50b1b07480890b00900507000941d0102091101640200030080400c10045800244001218140d80c00340070111a0507158003401c0021400b201d9410307024102d0344001291013483c06040c0b4441e03000900201c0c518940c0d4004808240e0480b9002a10513030500040c0c03a112410203088103500101455140c4840c020740c00010881c0c5800d118803110030300081403008803925030b020206000358401d070040b180d600c19100540e81c3d541420124041118816002040072403c1400081000c601201e0440528a80d40103a8084040115100e64410802c2c605440ca0880340000d03411030802c10b07170140403410042c0b50040784500800c5104070401e4002c180b020501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 91435657 1250 91434407 91434451
    0xa030801060813020d0507051512070504080303040312090f08070b0a02091014040e10060e180a09020d0803240d020f0d0f0501021218010b030d0c05070815 68
    0xb00129045a00444111112401807a005082c100403500070400c80320f20070745500105138009079040c1524003c50012480d04503e40018000690007115460010709107807410080c00c0e62400041c100030280900d195014841c20810381c00364081c15040a40003103203404030308249003540e105c85000e03101800d1000015229401600803107080000203042041c8005460800f207400c030b50b43c00d404442c0c6900400002480720407100c410360060f25150768a80003149800005003007403840c078031440c1c0510186400044007242c414003840d40074101e101c000c60318480b14400140640c40180005100c86004000d100400700c9804104040342109800b500f07085040c00100501c100741800003d41c050305510100143d0308080c400303500d000d407203800c4100020100742d6138982a60000c401903200b00000c03104220702d01d181108808030340d5880c00000c01060a040002c07036260340c4003208120030b20102d0041d10b400c11800704000001000840705940521200328000700c119642990760070a1000940709482035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 91436907 1250 91435657 91435667
    0xf05101b02010b091602010f0903030b011d0901090203060d021003050714030405071e12030f080105190e070e061801090503070819030e030f0c09131a041b080a03080106 74
    0x7090800501d40c4d0515514040c5411402d91100110421552280e8022402007500e0007a2005140b00303481c0401c0034030480e0001014020380603800910800444810350703258585080039815583c85060150383ca5481c2000b0911010016000940280810354210300c0c9541c942c0c0a83d0143d020350ba200c1001b024090302400300342c0010764018081d900f09040401c1105e044070303888994220b40d000c42002c400c3c2d0301c0c4154032218940440a8000c625049200d111040e8070864150141c80101c403140c16071825884c03041c006500c07a003e141207100800003c182d0f000d0080a035a81c40c100010700300395482c1990760710000d09000f01c0440070b000c05c1075103c010032070f85404103100040e91840c80040044181b914601a104911a04154180802c1c84411000c98a051154400d2020285c005000c04c0b007064083c0039600e10001d209a1000c07541103040b5001031b0045c03198035403280032884035008a484505100038501162a215517210a4a01001507401ca000c00c207110030341c0c06501e035100607a030303a041c01f551 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 91438157 1250 91436907 91436921
    0x6030903020c09040c05060a0305070e04062702090d0c09060e09030307081302060a02060f0903041523070510051e040201230c0708070801020c030301060c0f05101b0201 74
    0x140e0814507940c056810114001a8003500171420004020740d80c1001c10740a42c801c0720a0070000387c9450130032050741d820a1003034080b681c040d2404c00c00705181c01c5090b20360001e0b1450540b01e0500c440c6201c01c040213281c050301c00000c0d008004500c03043e0903140c45490080b10b0311804010f1400e00800050040542030380c940300b404180080d602d150355502c021680000000e00c048000b0b650f9044c103d000d170b122800602200c1c821a00105040d007401d440d05c4c203c400c401841c483d000da004120074032481c882982865010509814441c841d64485a0b030503109010344140c20440d010f0100c0c501060090000d11513741e00c82111007040703141c80f1081001000008022614202100d04011400551040070301022030310120103c12403603e14074080e100180e0106034107107016801540180f00c1c9840078001d02c030003489188021172400c40c00140d0241c036804148254010712075039441081c2448030016140f41c3c426400700c00d5462601e2240d1140000b0401603102c0001a482500381140c2c003801440748507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 91439407 1250 91438157 91438163
    0x10f0e0c070c0b0c01110714190305041a1b0601031b05030a02060d090b2403031908090a0605040302010c090905190c0c020d0b06090709060807030c0c0b150a060309 72
    0x1020b020b0510b00c0e618800d80c440c0507980078540da19000d00d1011144c2e071002c0e110051003100200c980300c2d03000003a5442c0000c0b040c0d1001401c40448070340c3c030019811404450459070340d81540040540301842c0b00c0c00c0d600910b0540c0c1c220311261394004a000402080075410380c0d104608101081c941a00060b400609600445406a003c00700031ba003d4584034010f485000071072f207000320700140300740d555100f00701003542c0c50190701030407001c1101100110b100410b140c1c0e1050f401542040c0070318220a2159002d0725034403080c01095404102942d4013840070ba1510b0360022414082c0c0d04091400a0003400100c00c03060006491140201c0d000203180212400b03419800301032001c4111a80d0305100600c5d06030440c3d1705024441510b400103032101d0124075107040c021149a0407178078140080c03001c4050010030440410480c244140125904110700d990094003601d400114810030160507120280c080f28080d02001e114000c106080c8104503052180d80c805443c04490503585020030f50580d13100100007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 91440657 1250 91439407 91439423
    0x9160806010b040915030212010903020d02161406040515040807050109050607060b040b0d030305061003020c0a0f06110f0a030b09010803090f04020d0203010b0307020c030a0b040303020703030b09010f0e0c07 91
    0x13040098842d4102110902280102c524442d540340d0010307500e40b010202d4540349944803480c2c0c1d024142c040c4502a00d41c100f42c000f9007540107110348036940b902640d001c1d4030440d02020b600c240c070303079200c51080e03034003611024041115070040a8a00c0e140c81c1c00070320510443d4400da29010800754132030b0030303004225040986007900301a03840e680d120180210f1032a050304159074120741c0036955a85038018040b60b0081d240010b00d81800002c0c820b048032120035a50a140c010011200f10140010380c2240ba10380084102200c0c3c0511300e410809401140c030000001d000c0495920320118242008000b582855241080903081440174407555240900c5250440c6d00203100d0b1f460181001c3da440311401f20018801450421079000d0711301260800e0300301151034500441000050380d0100020004080214018020251581e83c0d4295601e0001d1001382090b40105030401014000e4000045100d0024100300982d070715008060040c01080c85400300025407440800c141141000c101e40010390040c0c41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 91441907 1250 91440657 91440659
    0x5060a090312020a0c0603020c10050f2a0d050702151005040207020609030105151309020906060a030b030105011e06090b310308030f010801020a021c1709160806010b04 74
    0xb40c0c449103841e200d061030941c00b6a4072141c0020b82400c40060290500e61001a03c0345d036030302e5006182600c4a4912000b091802003440050146200d84950001e42449215903440502c5c100c040c2552049900016a000100780c049035207015401151040c141942241c22080c4400e0210b140c1801c1520704030b98000525405028509081d0000d040160001d0b20181c1303840b0706031000c070b0308403501240d00031114a494946d004407442c098801d085c40f20303401041481556180c0d00000c6070303e003002d000703c0e00c60400010429001e6000b60800d40414034002e000b040303150307503c074440407802176403030000d289240c1c030194040354603805011824140c030407050300c50781481002c0640100d0400030b160701221010401c04c51726010304007881c0840241d480780400319101e00b015840061b1100043e08a40941d0740140001406294005030701480d4030243c08400c405142c02e80c0080d2500c2e01044078140c00c500d441800c02c1217504001603202801468640d195003800d540c0c140841d200d100c00e0044000303032107003004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 91443157 1250 91441907 91441913
    0x1090b01050702210a0c03060f051605030a0504020a03050d08010911040e0103020d020a03120c061407080a090c180b10090308040303080702030d0507260601090e090f030c100605060a0903 82
    0x70910050b11400300440d0041501606c1c0c4413900718140d030048030f4458071a0620450f28010303005180d0804503c100c10580e420fa8201c010745540401450042c0c5690b07140d00140640d91821242401540c00209841d00c40340c00e1100240f00c1d5509005042130380d0300300b4421a18094802c1c04480480f000030080f000709034215420000200d44900069038130010101c0701002080b030384e10507541e691050703407641c61b46854146840c0e025118020000308107840d08108000000381c2002105e0340c404445980000c011696140001040880750040c5409404558801407901a00d81c03060300748120407a205802201802c00032600018070340802030028030144402c1001a00400c1a82d802945c14010740b0f09080788411644103d6034215030100c00a80ca00d800480c800100e0140503a508803056803d080a00c8c00b8400a01a441648078030800520070714000b87e8410030134414100e40150340402d590303807030110f200c2681c1e03104034110b66140c41c82d1403e44000358070300d022800c8440844107911030300718807840e40d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 91444407 1250 91443157 91443199
    0x905190b070503071407030b0a020315010806040e0d02070302090a2003090319050a0f020606100507050705090a0b1e09060607020d0b0c18010201061202060c1204090501090b01050702 80
    0x4402c46081c402441a100010301e500140350540038000d005102d458514206054034040141643c011184100140301040f116210340e0030203a0002e09040c0025240c00000c6030041c4401d0080d103200b8006c101c0c4800d101c0b0303404221181100e008860504882e1145141c50341241c40d60341e40c3e00d00d4404815409504c0b0400701c03000d503501c6141003099038100150001444254010011503d00041c00003409098040e003200001041180d075200502d0207181c1b01001c100002410302031141881000300e18801000323020481c0c4405840040c01002450800f00003401c0607210701c6494a1041281912034003000010012074140102e004240c6603080c1c44440601c078880d8440101660044e105010b08004500c0c01c0ba5064024a484600c19503039121550141d038184002c18882411641460b004002d14080070045070360b415011200b061f929481100000e14203400e05045090014001c600022450417a5002c1412a0030003a4240914001030004450300e1040e100020740c0000040c1924040f11156 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 91445657 1250 91444407 91444417
    0x2104120c080709020403020414040b1f0b1308010c0503070c030e0d0203010903020f0f011505040c0e030703080a030b040c080a051801090503070c1d1605040b0d020a0905190b 76
    0x2419410044607225504141080c640307800030a107068000504008500f80351081c1030354032050030340424490909940b070881501001c1c251a0f00906900385415000c0c8401e612000108900316005a135160101107459502500348280ca460b5483d04981090442c052000c403403040ba0a5070b1403c002002c03e603015140c140d103e1100036000900224a1001030300c09105c0c085000d4000c0c0c008180b00d0100341282450300c01d400034007501d103906003d02525004d45050094040d11411100880c0040d5154411904042d04904080d418810000d001082c844a400107290305011030b9024040c24072040e044c442981d180f07a9030b480000300e1101c001141141c00350701803900719030007848880e00c1204442100303083d20440503042c1e80130b4200050905c20016031210800c010405024146d0a01810340248501e4640040080e000c601444840c80f070058031034011200036103101000b541c0c4440300858850f000350030075070740840440c5122101290780c1c9448a007800000c0c02286d81140d20764104104c0c4d60040e01f003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 91446907 1250 91445657 91445663
    0x4050c0406081908041215110c0a02010e0303220303120c050703051308030a050c0601050d030e0105032203120b01090b040504200705030c0607051c050603031603030203060102210412 80
    0x10901006c40e0102d01c1903400784080b4000c0e544a01a1642070107100120340200208507050760080001ca40a440003140ca901b00c0d980900300070900c110500042800c5101d9044044210001140d088a0302038500d01c005080e240203696072207800b2440d0078440116007000c141c003008034000740514800203228000511130315969519902e5081e5807a10500c1ca560440e440d0f402c0800c20100d40c001805504000460041c43c0807200c074040240981c80282c141b0208801c0380781004400000205144448916851440708c9840681c416400906008140c05444130800b03074090705004070820305610901c104001c5e1440140b072146440d1422007004010090b441c070034086000180007200c0c120310000d025040d100e02510140d6a2078a51040950401500404100c11b10006105802621000ea00c000d60740700a080400a01620b071070b4006807640c001c00d44002e070001c041403071001c10142e06402460164000f0b03021070300c58018801b8a029203018144503204a10001e10040003100c1490824004483c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 91448157 1250 91446907 91446923
    0x1030b060d150509012405060f0c0307080301150906030e0c041505120c040b0a0e0c0a0507060515010306171c210902030d080412031d070e04050c04060819 68
    0x503060b51030030261502118100c1450b50b6031001400304425a400500144e0039101160020504000010306940a03012800304666000b0486094010040048a035001d421540041d201c0da99040c80303101040b001441100050400d61000902c1c90080c000c41d0036102c000c41c090000f40e034042007840003c001408082e80076000d032400010749a1107001c8480310b519084c00203014015055401c1c4001e036400795000c280200d84149040010f5543c03a1a100e42181d08a82e88035928891410121040c0c0206100684060302d00002d200010005421841d207081003030320203114580d0343d44a02a0001e50a40c040385168129101c03d44084140703000400c404409800e1000300c0d840c03003118050020550386984000156560086415031038100584000200c562074034200ca0301d0581c0d40c0490540800304524149915211034480c060b400103a5201d20000640440e4601c41c0e0ba809203944005007920259081d0107050010384442c101360040c9415100d2040c018513806100c83c2c024001480c40c110103031342c1c02c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 91449407 1250 91448157 91448183
    0x41803050d0c091d010f0e1006030c170a020903060106050306010e0103090219030c0e0912040510031d0a0b0f040819090503030a200a05060a0906020408011d0f030301030b060d 77
    0x8030040120450030822180d42192640c10941c2c04003072800d007500145003030054601005940940c0c5408507040c1d4402b45004100d400c00a6410f90300301010401c0d4079804140c0701c0411403001e001d41d0191245540480071200a0b9903600400d9440748000e8580c940000c03080d0700c0c284825400303034111284491000e0004003101d18411080d200300b03101c9410031030300c010313115404000c601104071080d900403481e231014080314001400140c0c4184280e204580c0036a02004c0c030340020900a80c0540420402c08c45e8249602c01e0307914203e07449541881088900321400800301e820b022510014a02c2039038800a070311318058562401200c06902e40ca0918104a1a51400301d02c5072408d07c094a000045a1940b1071180500440111041031041151441e60321a101d00703c081080011850340280c1c810100140c00e00d11424241c0285c89907070011f444940c02c2c41e105c0e81d030886801c1c800e150885140e8054480030130320440c4542e02c0c5e100c00e2001411114003c4045043c03480c2c4541886a850f1040da0224110307 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 91450657 1250 91449407 91449419
    0x51803121204050d020106060e01080a0e0a0503042d050d080d1a040b10080c0c010902060f0309010612120302030613050a0504030f05041802070503120406020405041803050d0c09 78
    0x390710030005020042034000c107010410030100f0105000108900090100c141414401000c05014000035030401c075810380810300c0020541c1c00030409001030310a0b16841e441a04003140d499100f0b110b03404510781645881d41c00d0407403a030842d000d016008282d80903200d25003001c001d044104101d0035034641104026891320100140300c0d0040d003420724010b100720f2481e50003c000c01c0701d800c217000c60b0050080c020000b41d00340e485511140e0010141c00015111080107010341d0060011150083d0811000180c180988141002651240a4a40090110503140e0101d03440c0c07800d02000c01000b0300e1010800456881c0650050359001e4406007140c26440c42c0400d03444140c0c1c0d070990f0710744c404075515003c0c042416030100440c0745106090034164035240c0f42c0407003e001441c40700328594406a0206014041000500848000741880d00c0a440182060308144c0000d600502c59a84111b181c1a501103104140054a5690390740603280c0d6418420345103034488c0500818000001005117400f004501 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 91451907 1250 91450657 91450693
    0x705150f270901060c05070e093d1d0a030c030e030a0605190501050118031103030c01020310080601060c150507090302090a060608060307081c020102040f0e0702190201051803 77
    0xb01811750310720750242c2c2282825800d24540d600080b001c0300c129801c01c0707400c1c0800a03c601041c1c0019101d59813a1080f070390700d5080f0382e03c051100f030304200480160300b8282c3c1d215080500b0000a00c554036a2450740001d499548171034251006002c1815000c400001c24012020054000301c09010f0b03440742640d0740c0d150b41c220341081710920790031f0410100b04001c0500c2c910803103024080a0070300062000c0800546565400c551100511030751400001c500503843c24000c4d03401c00c00700c140095440307041035130b20f207080314409d4010441c091094000018000d1b2007002040005900301e600007048403601c0d818003001c2e000080041040c4000304100200503201c0b9414a40f180c2c11110700000d000f424000001c0001c0800f0780f0303081c80b80e40605803d0003180408078009540004102c9000c030008080f00060b80640a5503210600141f5180c000140e4100d203240064481c48882c1d0a86191185040f2507091901c1e854401a000410038841a00c1002d503d120311076a03160010222071500d072583c809144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 91453157 1250 91451907 91451909
    0x708091507060e0d09090e19060e24151903060b03100501050f060304021f0f090602060702060c090415030501020901140a080406091a0403020705150f270901 69
    0x90314000000d0300d01c1849070501c101441d01c8042005411300300c0035114000d026003c180250807045a40d1001407020b0441080402d160b0355617041200710000d050709010000b0700b69405450396500810306146d81c0c059200e003101039005c01455074500903031204144804140040e203422504902c410009000d20b40c8440d14600083d4496000801c445000400341800c0c81814640b0701291ba08041c0107100c144c1e079624007400c1c041415660562a551140006199407420981520400365042c20446800b0350284804040440645400000c00e554032800c03a50345000310f45242c01a0040d5020034241d007104001040d00c480b009002043d003184035100c0481010890b48121220ba500140c0b40d40e555030070408400d50002c00303c401c81c1c18414864000707090504003c100402c0241d5500c801010081c1190200360072100c0030540d060140b50a1902035543d103c1c0f80100e03403065040d010b004000c0d100640803183c2d12418410500e05140f80c8060800840da410f400c508a103070444c007a081c00980350414254 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 91454407 1250 91453157 91453189
    0x30209040606030c050d02030c060304030302071a061005090d020f0310020c060a060815040303020d110304030302030402010206060301050601090e040c031e21080c0702031c03020702010201052a070809 88
    0x2d0020301c0d40c40d0140101080b036028a0041003030a100071b0140e64003086c425901d400a0702c00e05d40c0d981d1140381c00c600034801ca0000805040c00042c1e804410f024042036035101d46c81c01c0ea00010710020030039054900f4007a03640b200e54040380c0d050301c0b00b00504006251700341500c4080c04030350782405804944000d90b001052403c1283c1d101000700400c40c82c09010340001416070030044c00d05403e1000000c40110f10013080039060580014078034440301207540c0502010348200458039101d052600d0010069481500c00768010b10a90003c114549010301c00c5500030781050f1910f54a107445d00c0c49480c01c00c00018001e0b10150044038001000c96200d008007034502c8251003054000303101a142040130800301c0050045240151041441c0003600150715a130801b00d40d800842d194000c40c8006072421400225128481040801207001c1c0b84c1c03d9009800300034800d800900171030766052034602c200410559016250f103007078a010355440705004020100c0d2406050101c0c40d101140010800c00b07502c00c5022 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 91455657 1250 91454407 91454411
    0x13050301020d0e0c1f11030d060b070201020d03270201030b063702070504110c01060603050a0b03010504080406182114160b0a09091a0f0901061b020a0302090406 71
    0x800d81c5443e00340700501d440c4504881d40c0d5110340880c5400c56072100444024018003889950a81d2a61000c006131400201c1e0002c09100340c64845031211700507040341c00228003501c41c03000040065070107070207000050308180700d100818000300d140015100c415240140d052503074400103070081d9164280100745101c1d0ba40d00e01406226a866030248140b0310305005845500f890b680b168600e580450098101d400c1100c01007102551004a50828412041824060740c80c010000445d2901900014031400e4040401c11025201d00141800da07501194001c1c6481d03020001401180e00450380d903045500025a5000440c0c0c0324030384807840d03100c400000c400005001c4a41c904200320796008801d01c20043e000f800c540c2c102e140c0740990040e10303401420103d01c8049048410284100050303c02072035035203820301402c1e4118000c980c0402c40f0018280c005c540c5544104070030708201c200c4034100e0f8501e50315190408011508981ca890850720207d81c04207501c0d40c0000942d40e5401c01d20b004074050000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 91456907 1250 91455657 91455671
    0x6130e060f060a0215270c01020606040902130c0c050a051f060608040f0813120210030618090501020d0903050a032f0c010e031b12030f0103020613050301020d 70
    0x401000c1c000800c0207902ca603404010300500c2503400b00782281420b81d0302c0c1c1e0070b00e85d03915104504000010f9030040d6407034a821002d1401c1d15802e0010308814046401c0e02a80e01d103840d21743c244425940810000382d00006880c0e800000d0300300e2988100d40850191804589101641e5109801c010240c541903c041d40800d00c5100c1611021242c589000060301d0200001c0303141c0000078041000041c0090607210600d4818000d02c1a05411600c400c0e01d240180341c812519882401e43c550501c402c10390281b050b0f00a030340a41d0b8080d00c1b030403042c0c7e1380200c040103400c00c95510840c00384c0340343c82048030195001c0c09180291030590181c080d00a1003512202d1f143c0c480707818020221400d11702c0c6400d426100c00341460405494548102c1c040328011a52560340708448100384c09000c1250300d00750342c0d220009180d411100414070031414624a0f0081d03c00c0400c01c10900c0c05580015503c19600300c03041401003005103001c0b40140303003068088041c200990796070f000090886e0031130f8005c002c01940f01e0700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 91458157 1250 91456907 91456909
    0xf170a05070303110c0402090a09050403030e07080d140a09150e0307060c14070303090b131205060103170a02070b07060b040606120b041b030b0114070305071a04030c02090606130e06 80
    0x76910306520107880442c20071030148c00141c1411900c2c402c02c04101d541e83d001c1001e161007504031000d915082c40c00c60b86100e907180159595000604000e5002541c3c1e0340108024000b03420864903489130558a50b4101410621070321900ca944121060911108501103d15610f00b03004590060545841e0b00b10150401d00b0607115140d002c22100045810440b81400025080f000c22815a2111107113035450b241c140b5840025140290882480441208500340c100080015040e059900c07903004c8042071000f50500081c640208042d01c00982c00401d01407049404401c060401940251030100d5100c00340e00208040340c801c0d4000340000340c009040710440c41030502552807140010b4804020000303004240206101002c40c1e01000c040c0c5a40392514980c0c415110995841d010318116a030303601c03480c6401b4046038031920040b50303040c080c042c81d002c030744000020952140b03425032203034000c4e070820346e003000300719480108810b5101c542803182c0c9015618102d003c50142c01030400b507581c1801c0c800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 91459407 1250 91458157 91458163
    0x102090405060d03020601031101050706140103060b010206100b16080310050429040b0301140109022101030816080c010f020423061603090b03070203070605060a0f170a0507030311 79
    0xb000b1a02964014105000099001544a0469400503081e911070700401d00120f030140724007a07016140f241843c00c002c038090302011600303041f03d1084108215100b074200040e42c90300400c85840983e0515280100400c001000041020b101c0d20b07640300102c0c07241c42e91200d50300d40081d521b45c105240400c0090185040ca0710500062001c1402128259001d5244c40840c0c3c00046410340e008644450030035085403425048010041c2c10380c1e4000748950385801c2441c00030b41004168041d10f1940c04000030813070400300c12680c1a06d4000201d5032605440d54581c10003055440c40c00c40344031f801002814203010080c031996200c49031525015907140e1400034002650b200020000403004c4603074242990543d280c6d01212000c44100320b8940401c201802c0c1a160b05500350b10442d00c0040000c1044001c0c0c3d0701000a10141d032141c68104016111750040c030812080d00d010f0100101c50003d81400140c0052001007000943e460480f0b101d001a0307a80c040c10070b4801d0f40120007040d8081020114480b0038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 91460657 1250 91459407 91459411
    0x6020c1002030421151b1d0a030803061305010617010f05030309010f020a0605010605030402120708060a0f0605030f0601260703020409150509300702012601080102090405 75
    0x191000b50f0619080038410003605401c0440c0801c80c1c2200b540210412051240107180941d44002c10884000600221410718001d40c04810014481162024144070442e00c070f52034110011700500788540c1180c1e95992590b101500c526880110300320201d038a1000380c001c190281c83d0039a074842aa100c4a41c101e8080d07071041e0841b07004000060070500145d1000002e4034003031202482c042644111040c4141d041881c4d04030007a00c16800c00001149030740d040401103020f41c1c0b00742c2d00d05140600c45815640c8070000e17406071020f15000500850007078201c1e03400802031185411400541c0303954450000303180c45441c80501c00d9a030400c1004000e110013110911000d4612450a0140c00b00601c80d5680c0340e4400d03020082c425076480000c1c005101d00c00036000e9400f03640080402060920000203075032400501d1000011076102c0c00455007030404940c09821051090f44030030f0a00003140e0040d0745160200c444440c0c0c20b43c08007007003106011380b1802c1c02d0003030010000040c1d554100c1814803042d6000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 91461907 1250 91460657 91460689
    0x9120651030b0f071814100f020706030b03070e0901141b0a03020a120507030905010b01031104150e031002070204050f0601080406110913020c070504060302130e0a060606020c 77
    0x80c00d0400c01c08110307448101a40b040c0c54101c0c0c03260560b42c0c82415101d01d521110b00c24908003604034081754010065030f028130b91403012143c50060311403140d01100d0542038900b1620060300300c04030410003603000b500500c040c034030010706407000191600030380340c0020012144081681c0d1100c0d18442c0c0d0300c5039010895008070000c0e06140100c140381040c000d03a4802c181501c020181e000840200082c80351050385540f98000c8410702480c00c05103030040207481003420a81e030175481e0408480c03d941c020f224102c00707424059081810146020740003c402e08c030508089003030010009005000b40d409102d402ca090584440042c2c564066005000407220000c1078059001c0d2103000344603031a80c01c582c5840c1c3c490740c00280450703140c1c0341800025140c007641b032180b0b81183d2045113020204c65140c01804000c402c1104446c41c466403141008152205448042c0d00081d11880403800c0c083c0d06d41240000e07075440340448110003010b9560a0840308658404001038221520442ca18070b843c09180e6401c1d64 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 91463157 1250 91461907 91462061
    0xf0902030103120e0a030b04030c02011d010e0409020a080607050309071a030a051b0301080a17030114060c070509040804030b06011404050111160b19091206 69
    0x2c15030755900002030001d40d8078824003034940e19140d819a00c030402040a0b41d4028a2510181404d180281040d1000c40c400ca0103d071700003401c40b081050034043c0c2d81e028681603580750581c1c220181808010402000140c0c2c01ca805501c1c08070b01e00c101000440e00442440e5a0f80d6502d180c030301c0c40385040410a0308100e4011042c140c0414a8003044016a0b82007200c6d90000a69500c810a00c625a1058022142440c0c0b002100015960b840400e000c00464060950702c022107030001c56504461109000e4001805200380340070540f0308044e005800c5035007604044854941e15a00040c41e0f8407400c0310b04840e1100b0010b024000c01000200480e002442801c08240189411041c200c1500440c01500d040064840b080300d00d603081008030788000c0140000e83c0410548407085201030b90b01c280d0805402c45104c80481d44282d03ca6242e0b00e0444500d00020408081c1640d2540080c04034916a5800d0ba0b01c030300840003103000d140c80d00002c404010b0001c9991181c58074985140380c2240300110751406 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 91464407 1250 91463157 91463159
    0x501120204050901090e0109020d06020c070603051e07020313080c01030b0102030715020c0a0807050d08340306080d02060f0a0e031b1204060908060612030a2003070c0f09020301 78
    0x1489401d1104d054a0050b04080340350040007080c00e0040c25000c102a42c03105040c0b03d03980c24400d16074014000c1c0704100c02516603032500c8003003e4094600543c1c8181204011341e4810f01c0c00c55524039032079003140c85803056a140c070700d403042c0c500c0301105c464000700a07a400000d5040c40d43d40c0c061003051481d81082c00a07604104032030300c4000b00c0c0341c0c080c08a03d25180d00050080c40c3c6d440c0905c181c500300da500400c4203448040b607040c19503a07003200c400c544000c10304010200b200c0a1000d0f50031070050010444040b80540021701c4c803101e04021010100506d52986008204800141f00b00a01004c00768000c241500c3e10b641c5041c1c0111015150a9113207140011003a542c000100481c0c1c01c03852a00d4611403c4203000707031070034988925030028850504001c5004640c036a40400e5040886072200b00b250001e071648410410080b0080000e0380c40e903031040110208440c050300b45012403000f00102c1400c412407140b18142141c0c17241e0401c86078040740107002d201c6400841102d0010f030507140c0c070841c115 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 91465657 1250 91464407 91464409
    0xe01020a03030902030c030a1406090c0d030309030216151205060604030f0206131205060702060c03040201030b0a09061508090c10080c090d030c05010b010c03090b16051204050112020405 82
    0xe000029014040540300c1d82c4500c10354500b0440348200c0300028040702d10507100c0f420049524180c0740c1e02406d0078040c000100340f0001000030203410301d0500401070744e000042075406030003c05904c0d100b00c040d0b01510703120109909140c1e1800b40146001d11440401c18454140200f20303594440325020303554500710a0200a4980c0001e690517a03610903420748051085000284107402952241c1d500c551910202140325505942e805110520800c00c4405d9902c0d251001c0c1d840e042c00315002c8030b0310142400007070050b600c44d03000700b04441c8000e00300355951a11084404260380803500003a41e01420414808044c5c0d034028541940080c0e4140505254031035440080c103115a0898050200702d500c1021400c8080c0000c22150042e0004000742d09140300c5240207000408074000680340c5500c0c14009945650052200706c85090340741d910303407a05900304401c414441e008061b00d1034807006e0b40007000380022000c01807502c6c1500744d01280ca441b585000c0004141641e45150400d10500500c410442 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 91466907 1250 91465657 91465663
    0x3160f0b0a0e040203010602010e06010f0b0720040507020f0d08010b07082a1f090515070215090606030c0d0b0c03150301090b010609050f0d0210030b0a150207060e0102 74
    0xa850042540e01c0e591440c860045a081c00d8103150039901c10301c00000020305c560154003140d1040550015070340160703650712841520740c816105044000f03070104140400141e00c0d41d60981c02201100010505151100101e0308442003210400056884200002185401041010f407042442c0c030704600658100041d00d0914001c184d001881540702190b1409070345c2e4455003203505002003036843c01132075000407060b50b80d0b1841c103001d800c154600550107899904440c00741080150308540144903448144032401501c1320000c14000850103051981078a11030199400c5002c0c41d42540106214140041050304241c41d0140310b6110720311460303400001a01820345541d01101030724281752240d58000d45aa04a0505030000e640741d464401041c1c20840c611280c01c0c180d4403513581d9101d94135114401d200c4007180e450b072071581c00a0042860f50040c900000044400b503007a18000c90903041400200e816220a80c0004424000c01507041710090342c108400d000528807882c1c920150340c086000030352 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 91468157 1250 91466907 91466909
    0x1d030c1506010314100603110301150f05130306020702040f2702010504030605010605030703050723070f0204020406050403120201140c09030f070906032f1c0210030b03160f 76
    0x400e564000c00010203503802039000c040000b154101c3d80004d40b90003080018214130501880700401d150030b03030b40c01e0210091000c4d24141c5582c13484a20358541103010a41d800310351151301d40704000c41004002108070071521440700441c802e510143c4c07242903510420050750a0442001c5281d0301d0020456a43c90000381002099a80d0000c0c0c00c814441c5800101d4480c400c40d08054035150502c0f0000507101c0e80301c0004c521030541b641c1c04002c030343c5038900e0440d0414909400108c030b09140e51880d0f51041c0000c0300420f8210b03c0f03207801c182100110350105041e42c115038440300203d0030214081003402169a40440e8120352813008100800064aa0801c0031402030010140c5a801182142107902c0402074460794054000458180c2582c801c1c1800140845010840f0803401390380c540c040d0a01034100510180c0702c40200c4030314000020b03040c0300d403008201e2a6811115018111000561078290038000200400e82d00412664001420b06103401050100c0c2c5942c80d006d0b2208100700b843c1c10361504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 91469407 1250 91468157 91468183
    0x1050d030e150405032a030c060307030c09090c0201020301231c030c141605181501020325021806011205092a10020706271203031d030c 60
    0x85a48442c2205a40c86005580005405116102c02c403d6001c8001200c5940c40d0030140e890002c0c01d01840605407900d12180049800100600208a00314002e401241020000746401c9402959440943c011303500034200190144c2d50010041c84176403100101c081d070503459841c1c1c1654410402001c41c050540c08a0b191300c1500350f50b44440101343c4108052551503401850016104180c0100789031100c4030092560480e0038900d40000b040d042035603140419030b50640e4030700001d82c1c6003071064410021880045045003c04c102680750001c0300090280800540c00c0404441d04851041c0100e1040141c6507080c45400c2c5d40c100b141c181c0c0e00896120401d843c8130300111392600d507038041524000c103458840c1c2c050856100d4034900c83e03088962070745000030111072082c04e1052400060b40c40310068040c000000756100d40d41d5485e82060b00300244141403a1000490306540c402d5400300112807800210000703170312a07940340c907246400e000b501c2000b8480009035280c413082c44c1c0c6103662002c003c41d0103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 91470657 1250 91469407 91469419
    0x90609060c060c030204120b010f05040b03030306120f0a030305060a090b0906220c0c05060705070f0f02060706111305010e1c0c050303030f040b0a09021003050405070f090606030501050d030e 84
    0x4183c1e903038440e8060380e009160070036a45e1901c0c5010b01e444401d084d424090420204100c41000807180703040d01480f4854035015000c1c601e95203a0109114998007200800d04852150114000c1702550030003400c042c0c94000d075400a09420104e040005c080020307840800c207503041c2003070340d0041e0340d480c0a01c1d44c004034100c4814003101a108500340341528004540c1038103038680081841140e400105406a0502c6001920725607030750002d06881030302401d0030141040d044041401d000400d200c81000f01c1a00080200d030419030b42d135540300305456101c04020880300b80070079044101e010402c2a0030180c07509003044c0c081821010701094030000d4400035030101009c01c2110f8424811010301113405040d014094990f80c0c034103051602c1d03007508151403ca841d041020000741e1181058801c10407041e070b009007100c91a4002038000c9014100c0508181e48502580030005070300725203031900500500d1000340120b035552410380301904441059000d14050410381001400103580803c1e0113009030300c110b0324 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 91471907 1250 91470657 91470671
    0xc05030c0a0f031508031e041a03040807060204060e1c080a0e0a032009010f0303020613021305090c1002070f0b1e030708180109031d1804080a090609060c06 69
    0xb045015150580142c0c0103024108408680700e54040010311070401c0303e84c6ca031000c00e20300603444025071249209403121744000c20300840d4480721260003560024000d100c02401e05402da29040120f070302c80c0d03000e1400306088500031002801c040b0480360741030024482d0001c0030310203a210001103125003d010303400c110102c550087c1d69907501001002540e0804c894031030384141d041c594200c41c0c000600462140340f0b0100005292244045101e05907545a409440d098880000f441100407041c10b0032a44802800201c0d0042c07007d0340314031813141001c10018500341c3c141034141714459041c40903c40031508010701c24005004400d05031702c110f507140c906440d900d02c00e10041e00d40c41039582001c098524400814418003a41c031100d41c47c05404007503000c6d4203150040f14040d0890f90405802000310300c112200c0c07610442d07619070400481c84094101d84003201c0c0c80b940014114411142229003480c00b103a000c00c6a640841203034041c0c4060f09098000d0350605a001d00484106075005041e5a12484 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 91473157 1250 91471907 91471937
    0x806010315030b0a060608011e030f08071a070305060103020406080f060301140c090415030b0a0f060b0a032906031b0f0301080c030c0102030906091c0209100303030c05030c0a 77
    0x1c1d021000b5500702e01030741194200214a60040c100c4c91040f40c001903c1c0ca0001304910f04a001a02d511140d13002c1c084400c24996034880c001e08880c94810b880300300c820302144001c14201051415212400300d899001480e040c60050300b1548042d064504151041c4014850b50f034100d0b08894114000c4c05620016544100c0024090010382c01c0d54a411104907091212005509014200110086a0520420180e06103c0020000c1ea10018003584082400304240d001554413103150b6228401c40480c00d6902ca560321741c5207910028032500020ba1340c0c003260303040f11780309900100000c010324609114000110006070381804050410030030055661b242e4204e10f09510111210035522281d26a12036a40c2d80c849625080030922160190050f52002d00283d880401221105a001020642004102801e120588000750744000d411081c14290038003603500e130f00266101c0d0001000903001607086260003804d684003004030f07400703002c018014012244800010b0311240c990516040460031007241e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 91474407 1250 91473157 91473191
    0x314040f03060e0f161404090b010603050405101e0614010207030213060f0f0815011a07020307050402030c071202060c0f071b0b0c01060503030301031106070812010e010509070302090108060103 85
    0x940307201e43d440303950122517800f0f00c01080401190b805d24000034400d00b2500511055560309003006001410380c100500402d4065440181c009014000700d84441c00c018610204a03017005200c0301c10b019900c0e4003905000d509014100242840503500090070807602e0001c0d40e07401403800000d104a0343c2442c00d181003159688100024282c10482c0500c2543c0c49a451504c903849000e951110700441b202c03203032070202c50401903040f02e0381c01d0003d048080c1a01e42100303158004500c100d80c075001e580000500342d49d4a0010f14007031420018003642e621006d144c8001c2c040780d1543c0800941d0001010410030f0394081c82507c000a0071003c0190b03554000703107085049d030700c010008249020f01e500d201142da00c1c1b941d0081c00d5600440b90003049125290b00c10103660380000d00c40109002469030f055050390070310030b010b0500e00d0b00c110390450a1280301c0049800403a0b098000641d0000540010007807490101c014980064803400e0851801045400003840d401c8018007150500da110002070040c08149 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 91475657 1250 91474407 91474423
    0x30c03190f06030618032001020409050c0309010e190b0411042301050312071b050d060e0d08010b07020904021c081902060601081503100e0a0314040f03060e 69
    0x10804074008140000007007215000580780709207440c0701c41e08a0305007410806669500b5403940000c240084003004502c031100ba040715483d5401340000034520b0218003a580c06840c00000700c98480c6042d00d00142126174403440a082940401a80c4804448502c1c10451481d001b000b032904556440c1080c085410b500a1015001494284917000f80e83c00c0e803e540125a139003001110340341c0d0340c03002090380e140400d6410b4012400100b00500026180e0b04141c801010300d203103482005665100001c80004035020b040d22015114041c07a103007440d09003d400c4001b612810213800c5541008549075190044840c020300800002c0c0200703003950360310105034204041009040e2041c0702ca0b031405a00b55000200c0100503140901c94082c00c990010408134817031001a565031400c1c0c1d035120301003424030110703054840c1c040c001c21300184107600044c001e1840d202c3c0080010200c030115458021715121f1500f6503e89403410600c800d001c0344030029440411a0b0b00902d000c540c441c0c590304054242000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 91476907 1250 91475657 91475701
    0x60f0e0901060509150f030706020309010810050a08060f0f0708040201180305060106051309060501050901080a09050307140f010b030309040b04020909130b0702030a090e180f1c14030c03 82
    0xb01d040203029024955038007880c41007a1a80303506180c446c0b09041da602a58040c030009a001401390311020351180c8000c5500c9841030319059211a511004034240ca000754000c407040e81c108008104a98076203011554000d0201002c60016140410000b0300c040c1001d880281007004d00c141140d171460001c08902e004d5500301040e25041c2d65074180140140e8018614110340b0784042200041d0b400d058801c40d021120180c60b0b0310714100f0701c000112801d40004101d0744280b5038904010703000c15400c101030008148078400100f00c00c0c91101e210b5261070f110401954a13a030401c200440140c40c003009540c181c600c103035408204241c1c02000200640540e00b10f8540294200d0100310a60840b444081c860301d000e404078900301d80b580078049803030780325a00d10040480d40068041242941801c1e0540d0710082200c132004402c21008402804c18241c94041c1079190300a514007140c80d1400c5c1c000c1d0552801d941060203818442c1c07074040500d0b0000034071400c050b0070003000003110107104a07904540840 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 91478157 1250 91476907 91476919
    0x6090f040521090a05060702090105150d020a0503060f03010e0706030e0f10150b0a050f0f090310050a0509030406081611030c010c03050a05130b15061303021201060f0e09010605 78
    0x201d03648640e40080ca03c007441944145000251820940101d130441500640768804680c02d160a101d043e819425908101c01400c00c124101110648082d0000800700d99941f541c0b400e00c102000f5001d01c0c0225818440c0e458482907040700c02002030785c2d40480300c150401003010318644404a007028114184c5070750b14043c07200040a8010640d100e80c20203e0008680d60f065074451b0189910740c0141022880440e0040204585981511020b450311040300084c041c9054041408a42080a101c01c0342001c1a06d550034080c3c804070718061558410255001107080c02d00d00f981c01024102c02500e0400007160348a29500094864241c03c0c100004603002c8030360f12508611001e000f0545803850074000780c40c10000c110004540d01400380591034030529001203010b02e0300c40001d1440d02605160a20a0751070590007280c8904010702114202031190341d8200345140144071050014000c1003105901d401c6c010b02150f004000f00e070040c1c07030001e8481e82103640d542203554010f0005400941e0310030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 91479407 1250 91478157 91478203
    0xa23180418050703060f02030c030106140d021605010f0203070c0624080f010b0f0109051c14010c110a08030708040804120c09230606070c17010203070206070806090f0405 75
    0x9000a0f00c10490348541400c114810240c030f054412070005440f504d0a180701000100411307882052100b4009868001503072401e9200703011181264000c0c02c1c1640002d80e07640750307101400030070303c40d0319021f1504003000e5145191080c0010f02c10024204010040d035960306001200c0c050150825440c05a00000c0c445407540342c205169540410310701251283d820000203007003500f010301600c86042d0301a164a10360710305150421030540d5000400c50f4086018003902e42c0400c15502d4100c2074192103c0000880c1c1e10401c4c0024810742080e0580c41c1d0a6001200010005109804507a40300003603207072000030342e00ca0380b420340c1c0706e0702c42e0f58044500191100444818025641404401c40f80c0544042000383c056410780441460702080c138103080035036507001404d14100f040007446214410004100c0075502c4a040e180030383e080083c0311b860350794040f04011106404112040e040b40f442d0801c1d915500e490b038000351003c08000c000d0b203168020440410200031040100d4040c030f008091082d0020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 91480657 1250 91479407 91479413
    0x30a091a01060c0203101b0c060b0a031412070b1512060a0b040c17010303030b0607024903030f0902060c01050702060105010c080d02090f10050a23180418 68
    0xc07402c40c03a00b41e00c01c5c040c0344e5070401d081c0700f68440d100544801c00085540d43d00e0040003641d078400c411744c8c15140f294907002604d4603a9602000040910710414a2801007060701d1106490080902200714408500b0000540030400ca47c0525a00421042e2001c1810100c84040b50a140c43d100c0d41c2c000e036105034410320100b100c4039040800750440c191401c0200c0e5418980440d451060003241048880701d120060000c00c0c82500811060310015140b0303403625a540d0301288884a011103d140020380301c1190b52000d940c440c0c45544010301242c1e245031070240e100290700864516880080500d42e4408000001e05d41e01d80005490a40051415841d028040c3c0024003900c4112152401406002c0c004a150b6026207031807071405e134000b21540d0401100c50300b040300941c030040e00c07075900600c80000100c080d540e000c81c400703c40313100b80d45d52501c0d00040c240260202c400d001100c68118800d0031000c02082d444019101d42017461420101ba0f601a18003060007814404481404101880d0b068024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 91481907 1250 91480657 91480667
    0x5070f0608011a0301050f120718021201080a03090e06130e06090f0f0a020d080c0601031506060c031704060b0415051503040308070c030201060e0a0902040e0a08030a091a0106 77
    0x100c41e80b60803c52070b0841100380c44040d500c400d0080c16484401d0114420603420640704250750650000c045645040e00c0e1041c4c0d02c05a0000c82940d98016000600c40ba007807102060a03500400c2600c0060154849999003d010f009080c0034070044520500001245507640410800904240c3d50041001d0003205100035143c1c4421101e0140a10982403000d0541c000010494107800c0b448024000e1444642c0c00c0010140f0010420b540c3d015050010381554074090000c14020340c402d2459060130b0510410b640306a4060f90f1003c0f0510100c6800680402e4000c100d212001d04840d51252150350750b850b14000400b101d00107680c02a29060400203c0c0a07070909100540702c0454000034541c0441c01c0412040c4012100100054600d0380460300a174000d1460304809880381c000443c010341c80303806203808400c0c100c412000c015254000042941094400d0183c1080b9410252620f0301c000e841d0310980b4800600000050b0396100c0e040407c0c0400d44002079042e035901c100c80b0101d540d690303c0045c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 91483157 1250 91481907 91481909
    0x409030c02180c19170703060617060312160510020301091401050303040611030c0a060504121701150c050303090c01030506061602060a031d0d02010c02070612020705070f060801 78
    0x1018a118461420102d0303581c41c4020320039038504407802e160465507541d60300d18400713030f544050a00c00c55005094201c80840742841c8a80240d640001d000b81c6414001455034030100c440c2d2000300b81117028440301d1744010414621206800440c0c580c0da81003182c0e15440031200c414003801c02d01600070428412440390700254100d03040c5d07d41c01d01c4080070021164607110801e118284d0301d5401044100701c0240164800c0d0400c1848034140c0b0b050240c1c29550600340340b203040084a00c0d9580f401044100b0600400b1440440c00d24503144000d44814a0719003994001805000d14800c001c1d4120481346204042c01c8025540c44015a034880c104024010f40ea40505120b850110b428040003410303d0a055050301e03000d1030704112245180b003950702400150b90041c41800c04040c2c85088448610001000310500c51038014010800110802002421109540d140c1011500010307410440c4580c00054020100c809442c01030740d40450f460440e291a1640d48255a94440c030040058926040006a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 91484407 1250 91483157 91483159
    0x70302060f0109060b070605270a05100209030d14090301020c160602010c02150a0b0a0e04020103051f051203070b0709031203090f0b040f060e010b0f030f0703020d0507050409030c02 80
    0xc600380d80703c00c410401d42d8040d000700030202a0500c00700c0d010800c1a00560f4010022540d007080c800c2041d00b24452054481c1d8045002e980090364540c20080104040d0000140c00714045042c880204000b0b510351f100e880500c1d041028903040d4405a00ca240125030b09558014000c554910a010140c0d45990110300c0d491060b03046564001070780c03030041c058454022040ea0241c15507202d20031102d00d8028000d000d50041c030760b4440c1d110b421070b01c40340512000b8220b010420166450540300041c182e074002481c1a1810340107800c03d54034118644960015210102c8000c00042240559036241d40036002001c0e1149505c00c05011074280c01440d24410313603002d0001e40c0410507262030700b030341a00e40015009102a400c051244003041020540c25003107440b521210301c0202407611048265080010542c1c01c69669802c88041c5282c44084028100d00650203401364408680c0015100c01c20780c40b0107405085c010220714208a0180034032006008001c1003040f0300c104074140200100c2450b5001c07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 91485657 1250 91484407 91484431
    0x100c1701080601060207062111030108010f06030c05011d0405040c0303021c050a0302030a0f050a1d15040b06010512090c0a0b18040b0102070f090b040507050f0304121407030206 78
    0x460803880c049440343c10b03110503400914401c0e28084080743c1c2030664044c0d8541ca82201402c42c4655403103401104c50010b443d074061a1654180080c071802c503850540e000700454038140040001030400007401040342c0003428009a09a54800207800b03840c410644141e109151008000070040d00c01800c07010f0b0390195084035030343c581c1d904500d0001000e4a9280d008a881401410b0005219070020356002c42089404100341803030312110000e0751000d852010301943c5800344043d050044020402d61310b0a0400245058110313180e0340290f0344400740004c0c0c124840d20002402907401801207820320080c814801c1d0007440d01e041d8440c2c0712034200311010b04c41c1030b8004000914920340c41c280c6041272070503a40d280c3c80b001c51004110007022007041c0c55042d03000e01403000502c000915101c500520a241d4081984001c1104200445e20003c001d07000740b0005205140c881c00b910701c26290704c070b6401001480e001c6036a441c1a20b10310a1450081008400015860101540403a50a000f40050611 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 91486907 1250 91485657 91485659
    0x105041a090c0907090504021902060705040e1b070203030a02010501031a090c0f130c0c050d050c0a03080a0f050108030904050f190f020912071707030c03020909100c1701 75
    0x20020404001d50300d140d003a6215450400083c504001115040000707803d166140c20340d10310209050360010144903107040701e00383c040d216107901803140541c0419603142040c609420480000b500e940040c0541d03d08a010003003001100c40c010040f503500b40d40080880381c5400390410000d010b00000d0108641c4c04210402c6071100ca076500b24454000c1d00c0c0d82028040d4503242009110b503144070302c0301403a13000c810100c1c0c410542c109032048000b019400d80e203001d405282421310030314cc0729460310294104041000312410102c0f01085032200e007a4103261070300094440c10180406007510803480c5a58915010001a00c0c1d00000024074100c1000e50b82800f03d40d9600750745801c00a41102d2403150b0b462a08071074140c580080e80b050701481381860340141000c5042d00803a110b003c400c28540c840da03125a0342801010075102d5070442d8004410000c10000b0f00310b9445c003010403003600c8000c0c0520038200106038410000c2c403842450400b194020030402070180384c0182006045e04032038140d1481800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 91488157 1250 91486907 91486943
    0xb040602010c180608090c04061d061002070506070c0803030a02071a0415020a02010e190b011401020a03030207020f090c0d0b0109150c0309181a100e0108060402040e0405010504 78
    0x54401c4800c0000050340f1040c0b6040d000d0340e040100800d0b0180c01e010b4200241180d503560300c07911000e4128070480c021072003000301903401d079100042c6c800c07403007110702c191800746d126030015400f8180d0344203403405074031181d440ca0160842d4496801514140c0004010400c08940a0780a00321f01402a0a2150521079030041114000800c3d01e01034810707501943c0307610a40820390000c0c040007035544000103010000c00603050034001208801d07100d80e91a0061082840304080f04580034140000b00700c0203880b20840041d6407032808a4008080c035402081038415503941c20204c0481c00c070081d25900702840e00e401406110341c080c41c100b03003040b8035010078403209502c1002c001042d03480309000c1c00000e04144200f9203a041c541c41e4202d04200c0d403040081380c5114440e100c041d8071070300c00c5400325542c2d0754100707480c00300c06915483c00d009051680302d402c40c0750350041c040300c08080c0a0030000c0c2c880d00c0b4103012070701911664001c402c02800490a11042100550003644118003400900c0c010b010455 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 91489407 1250 91488157 91488167
    0x30a060b0d120e13021201030818040908030405060708100510111009030f0903050c0d02040603020d0503030402090601030b060909180d0c0203070801051b1602090403080405070608131106040902040b040602010c 92
    0x40b4101b800b0802c94401030001901c03890050049809103514803030341e0140d02000406442c040d090880c1c503008048140000c0000400100c2d410075680e040000035407800c100e4102516131a886000e04c01d100c020302c0801030900030a10341b00c1444040b0259000d0026000e1410080d19000200300c0016000009400c44644100c182c0402d403680700001d840060141020040000d404200c147d80c400c0d0f9504002005075038441440403c644500c02551f140d251a0040003603081004021034141802d0100300204e0b03030f1f540e1301214417110045030080c15540b04d541220f01200c582c0014443c00c3d200d11009508029044081e0000c2244210207c071012512681c8850a03030b40152114494545031085080c451408140900800590b41d000981d000000d82c00007107004009441c10b5010483d44028007003808028030070302c0003074049170901c800c2d5400c12400000700380d165600c001d00044055000d00c0080d030b40b800101ca0041071010400d64860b612008500400e80c014070500340550b01e85031925120314003807 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 91490657 1250 91489407 91489417
    0x60910020105041103070b09130b09130303060b03011805090a0203010e150a0605061902011803080402091605090f0102070b04170d080103030c030e0303091906110606030a060b0d120e1302 82
    0x47c003006814004240240705e8000c06520413201115241c40074442c0a40303d00407094403488984408055603802d5040c00780c100e6240d5000b481d44c10004000600481c100e8400c900300c80c060b016400604c0340e0324064460f0814080800081d0b141d420304010511410b00001c44100440000c0191200780d1160140c40d4200c4020344540d542041c1e09018400928001c00445420300c07c9900001c40c00c1c40e04140e11803c0001c040c00101d0109030326000b440103608040e00082d0344507640805284840c1001a4085c0440c042ca540c0701c0c0c400c449512008040e40d100703010060042c07079408113040d21180c0310708802c1c00c20321401a240d40288559019081c0c0684180030950407240c2544900100d81e202c2d85084071400300c0c40315090f806110030494800e0948640325141d60b5000b680c4680d524403418014018450045807071440016403003c07041c00404d075804954945040d501c03c01c00140c0f20340c480081040034400e44030181000440000940780b0603040200da113041142150100000f40350340d1448406c9010f5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 91491907 1250 91490657 91490669
    0x306150504030c030b04170a030609060905060906060d0609111809042103021b100b0409031b0309080f030c0c0d050a15020904021303150506100e06091002010504110307 74
    0xd00c3c0410004180d42d041c40a801c9030080058104c0071400c80340c0404203611000410300081e5545c0c2041218842a10821001d8a04000188404d0400100285500c900600340034810100010b8045041100d580101c00a0803110824031070482c424015207416040401044281e609048040d4014507240103140e100e0380e84500c41420401103082104000d828038614207060581c02c0250000c0344100c02070742207940e00303480b0007090700e4405580c01d801507440001410380124140700c8400c0000750050305058061a07047c0304196a58414101180c245001d94049207860042946452900e040030005003180411041100c015041950030f002d0103041c1010041c0c000c0d0001580c0e80d001501140a02106001c10711002d410030b91404001000c0340d0206c030044000c82a280c004104110010288034079056803040100860f1a00802046606890001c4102000300c000c2c08410255074400558200c850080c1034207880c0005030b0406402800f0940d0b007540d4143c4014034903802072500180c05016281 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 91493157 1250 91491907 91491923
    0x15030f0b090321070e040501030809010306090209060904020903011104170f1b010f0207030c06020f1603030c0f06270506060f010e040e1e010212091209090c070b0106030615050403 79
    0xc2c1d03444900f20700403406031903602001944a2040071540d90380c06041d01860044501700e5403400380d00000f50840384203901c00300010b03005020040c501c1da1184107603102c1c50790a40700942da0394040c1f40000e005208800c0e4004005c907003c41e000c5245201c034100b1000f816100000c441c6184007001c4500d80e00d00c80000689405c50210030220304035440341041c0b80c44903038240101c41c1c25588076900e88600706a0f541090300183c1c81a0800644004100000d443e41c081048070081d5031800d64030010807194610802804281025108808102042e48100c0800d07000c0102507100c08101d02846090060386101581c2d6842614040b940a1901e0074068029a078161030b508c04809903541400b000d1f104071341d01410103004a0781442c02c0110409000213640003030400050b900c80717802c6c420446400020b000c00c07200f40d000310825201030700203508980141008903070034136195540701c01400141c400d510f0000d001d11500c0c400040c5098058000c50203488407501608006c0d0742000d0201c5082c0210311000e00110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 91494407 1250 91493157 91493197
    0x60601030b0f03010f020307020d030e0a0b070908010203071d0415031104020c0307060204080106080d0f0806060408030a0305070305070309050307080c030f1201050109050406080c010f0315030f0b0903 88
    0x98000e07408400c0451014102450603401da2000030308440c054041010900d8000041002403541030012181841031820b003000240c089880351682c0d200038010080c12024441c0104140034020030b0890001c10707184009550300d1034402d0004005624100c03c0f000c00700c0584452840c2da2a050003503101e0a041400c041a0451540d26000c20810103418038540043d420025007140c5181440108201c50107103d025a55516006445007150a140d00400035030f00000820300347c0781e80c41451621042c0b01880d000c02e0a4031060006a01c61140340d1210b0303035904c00011403001d195010b070001c911911054608000720f507110309042d000d841c1001c400800c541c00401c0b0500000701e400c005811040c00c14021242800038440948540364066081090b02d001100c00401c141e43e48081403202401c02a0342c00e02c1200c1c640800d1035543c0d0300704c1d1801030511000100b0407031494880d500881e07401d0082000c107010f85580741410411468030110079110341d08102c0c00221600c8001084591076000041da0000d0717a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 91495657 1250 91494407 91494409
    0x1090608251110090b0f090d0302030402031504030f082a0706060b03011710110d0c0c0203060a06090f060302180c0c03030c0a1805030d0507080c010f0207020a170606 73
    0x1c000c075146081449503110440d54462400c03c68601001030594000a8491031070409080504004080c108041c148400300115000046040016100182405a00e03038442e480083d0030070000d55103000d00e00b802c0303400700014503a00201030035468142d525140960340311343c010100b880040c0700002c0c4440d4000c0e00130a0b0b14004000c0240400e40c0100c0c00013443c1915401c080d4055030081c1e0101c5046e00082d04821002c1100b407003420183c00240d14108012070440d40d445403607008010001910a0b91050031010030390191100a4102d03a00400ba0350541c0361003c020b400400a0b0b006100e140361414100f42c1150400b0300c181b105070b0390018036130b0310000742180c044030000d6001450941142d1050001e10007009040000d9400b58510541e07075621a04548001010320110101e041c01d04103800d9400c00c06a2801326101514891138944542d481c442410005017520420100d005158a0466201c1140c007582d40a40100da10031104402c04580d956681d8605400d05c018049841c3c0060700030400c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 91496907 1250 91495657 91495711
    0x110a0809100512010312021c081501030b0904150b19090c0504090204060306030b0c031b0f07150c020606060a050d091a070201060f08030c0309061308190201090608 72
    0x4030040c0c2e1610714a0044507000740940ca04080e4403c507420006641d400100c1e035010b00a481c64041d81d144031b0303000f0403900000100f95800182c140c18269521601e500d003603910136007000400c2c2d01e0103450b051090620345041c074031001c0b0745206003020078503103001046245410919215004155110b104030300c0d0030107140f2030007446114184000d110701080006078441060005d80300511480d100094003514508201d00384801c02011100c0800003042005440d21010f05880082210b41c1e81440e101c03004034214507614400c6620160011589210b005440e614940240748031407000d41c2900e40c04d40360340c824052103025004400020400511401e540b0841e15031116180c5805104803032400e198005401e1f401590030380e01400180d450f001c0910602460000303207030082c41d85d007009624103003038034003d15241c1c080c2640c824405c0c03d0010b512a1070b01e40c0944194080e04180741500c80710280360121514104400000300c3c08a945030000013441402400200c0c4562400303424000f10680340d55403021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 91498157 1250 91496907 91496929
    0x80303060f030f0610030303050a020702010c11040b06040b1306020f1506010504031205090306060f030312040206071e05010b03070509070c02010306080d0e030111030615030a020f0f0901110a0809 86
    0x2e00b5100f911100588100100003ca001e082d0f0600f5514929086040007010385100038100406180100300300001070760311448408200b03410403880c2840b000f9050000c0c02401c09401e501c2d510140124001c2401400703600141030003014011100d0300190b49150503600c0d07404d11022502c151b0004c0014400703259510354804e5105105142451401d41c42e603a4400f0590780e210021000110f020a001c00c00e07081c2000096000201118681c0c101c106400019640f8840c0381c2d080b881607002903010508640b80c48098540680c0e000b54a020030b0791604125640f09144207a0555280d03007084c8040800c1c0c10003140038415030b400034114240c95a1102403d5510460f0f0003000c07070405654000026200d802400505021090781c0d41d250f202800700000c041c2520b00d9071040701c2d621103040091080316541c0703540d85c01501000d00c3c15a503c2c2d6880200d0b0000038040c061981c082e07040009500e03401818007400902420400f40c84440110b1800004299100c0318a48001d10008003004101054a00386003258 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 91499407 1250 91498157 91498159
    0x5070f0306080c2209060c030c08060102070b2209060b0306090106030207120f0219061d0105010b31030303020706050c03071706041d070303090e0c03061c12080109060906080303060f 80
    0x442c020b1450b40d60401251010247c500003c1d50f2025009549030740200300c10340000302440205449410031650b001d00d8400c0340d44215090500c60b040b5441311900308464001046428401c1008136030303030450480294411a800f900c200b001d0070011449a01070b100343c0d00860703007002e0f01030001e807810402544e40b15001c40080007984188581026000884100c41103d64440ea46c045a08d5100142c1c85410f05550200b8141c0f80e410b2200501c0000d6031030f029621b42d0300c18030303e00d4148000d4800c202c0c0000c83d4501980610002c1d1164003106154250b00188011482818100071907610307035007500a1030001381c4001000500d010115240103020301480340d0403002c010b02c0003a13240d070310f0f0200241540c2003190100880d04141c03010418075800245000082c101040c08400c1450110340c8220303244001802c0c00d102d01080200250720403c000c54160031181e21642c0100c801c1c07220302000e040c10000340301d8145d0346400c01c40040b40d0b0055900418048840490095003107031034402c00c20846218100c009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 91500657 1250 91499407 91499411
    0x70809010302162906010201020702011b030e130e161508190207050714040501050a1203051c0f1506021e0a0c1d09071d04050c0405070f0306080c22 65
    0x190f01254a00718000c2a1406228000100c41c02c5500040c4028a0040042d0b041d64414000c0d500513036003010080c00c0a807050505034066000034903003034490640c680c000300d8004081081c984410802540300070344040c030f00782c01c44056111401500400e00f240340500341e00002940c8950f51018010380400b50040d40304041c000d044003500042c07104a8001000698156000c11400c200b00200c03a11070500300d0754142d8041c0030343e41c1801c012800c03d503114443d10101514042c05002410b11500964080c0c1485c03030b08002041c0300310106d9030003408014190120f002d1a0505d039507140000b50065004456a03038020300300300101e2200c0c50310000307240001c034203941c041d110718100015152049031010b0100c00c1c41822740c15021070030107018240003d148810700d5110030410300c4800081c0440c00b60204100e12240000e41c8e0358500641000c403080e48464000342048144a03c040d000102c604400d13000d0740d400c02190b030b070300ca203203d913260804603a5681000140b0745520007a15040000300c0c1030f90b040080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 91501907 1250 91500657 91500697
    0x190507090302040c0f030f090515070215040b15040608070605090a050604060302040611030c0a060903021c0e04140c090402070f05120405090c12180a02060309010f0c05070809010302 80
    0x120f81038030a01032400e070008035050703d44008180c0502c10b0f150411000041001030020641e15981d55149440703841e43c0c0128103030000384406100700021281540d10078641141070400f482c2030f202c04481521100c4001174046078030040742c1010700c20074089803000001003814a20b02502556030b0b074410340b42a604032003444c501040545662000741300501265500681c0c81b46010b100602003401e8040c10f80081d001049210301314900002c2c60f06181e81c014800003070500081c68145e24110117001c4440700100c1d01d5408220258120741018100d1500740c4081c800e00525050b038401110044400d4451360380c00784101d40840c10981d01070b11025110310440c0c490b61341c060f103400b490144250840c03200c5840c002002c5c000c5051003148203070054580005a8100202c0340550301020100510f9611000744501d0540c00c01c0c402049450f16240e00a0040d035620f090107003a0b9406071401c00b04e03644416042c42c003503140452140044400d80c6400c80006030400c01c182c00114080c0d4400e1240c40802462030740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 91503157 1250 91501907 91501909
    0xc030c1d0f0a33020703030906050f0c0a0309030212160b0304020a0f080f0c010509061b071a03100e0106050708030901110c030a030510050d08030a091403030a1103190507090302 78
    0x100704128500c1003c0620502400c800c804083ea00030074000707104540007060100006034010030f403881034030090300f8520340345e0198800c040010301030300c20803c0c218414500f81405040d0403c00110542e4002d40301c021544c1408040303607a4a80108100e503100701c0800c0300030040c642c129000385400c1440141154642070b41c944d401c032a0040e4540143d400c58202000d14400d8480c01c02c001c1c60f082a080c20510b04000701000002c200c2c3c021404c00594003220f82104956401050000030098214241039040405003002c98003071a400458501c0c06060000d100811320707441d94950a070481c5e1807591482c0c5420442d41d182409900090010740d019034907038420b800304090b490068090002c05d440216100c584109008003a1000036025880704000320070180055103400392024805c9400a618a959072507800080c2c0c000c00301060f025203101c48001400c0304a10001c0000d5018001902c8280449600c00d60400d95600c4161194851440194405c03130140103242c00c0668009082c0c20300508050b501c0e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 91504407 1250 91503157 91503179
    0xd030c0b1f03030323042117010501050c01061802070605010906050f130b0406120201031401210807050d03020c120f0702040902190905270a03051c0f0c030c1d0f0a 72
    0x1b540860361a840c50540f0300064400000b069040500c0d46015945e04107005003a40e550b0106018881c10844000f4400c4050a000d40080c801002c0d2104c0113401d2442d0400c4460080d00400002c4800c0c0b814540001400e20980c06030506403080207000500140103241000942548615014000c0d80c440301c4042c401d070f0300c903c20a00246140340d9401a00041840014100d8480900c1c10454002103c018007a00406a10900070700e44064440040d1440908003c0e500f405820f40081440c40b0704201c100c601030307241e000b030610085040215207081e02d4505544080d8001c0c0200840801001e000d0000945009c0d000304e81c20380c0c005012202c414407180340c2c00e0598825500103c9005440b00188148520840341d450410b00400100341c802d40c41900c1d025440f405040c401030704101c8042a44440d04031000000c0305280b0005000300070010300c1c2c400b414040c1c0400d50312040804e2600004654031801021103d020800b142d02184c075810a8030708108240158186151b04280100400f0406031400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 91505657 1250 91504407 91504411
    0xa0c06110301031403310305010219020f03030103150b040605030604050d08180303010515090306010801140a060e060d030e0402070c080c011701090506010e0d030c0b1f03030323 78
    0xc888855030302d60442c01e21030107034081841c0024940e8002c0008181d98404c590000401000d4590b0880054a082c1c9401460400a4002400369440003d500d1101c4a6230a41e4580c0801e4070b40990700d40d02c2d0100e41a0b03480b40400d200141c444100c0045030349521025903c0220000710003080054429190800300c0e2a00740c085030304035020381c001e0945c03d00031a082903010307038410480d000b4014403032020b81c40f0350b880740810302ca141c0c0684406140381c0700300b42e4440e00391034890101500b220a2903075980803423801391450640702c490140450012404082450064070142c4a00b030608000c140c460406029200c282c0309015000c103e0507100390310280d40c81e40000c019007801064000240c50500c6502400c2c261050741c10b81c103100242c2a80405585450043da0445d140b007640000d46aa03a400180d440b04a80c0e40841c0d88104501c21910416400859010a82c1d00030034612074196100440002e442601055040c3c0b1182a1036040001034405d402c090102803041e1100a208400030000c22010b48007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 91506907 1250 91505657 91505681
    0x2d090504060b15030615030408090d0c03030306150503040809010210020d090213060806070507050c03030f120a0605062d030c0406080f040c050f0d0c090c0207060203070b0a020a0c06 80
    0x40b07011110b954034052018041d003905010f042841c5003003c00019880c1208601d01500c0c0e0540030002906011040040e40c51031760002e8180c03030b041c480b146001601d0074514001200417070318041010032080f00842140101201a44030346141d500c071903c03240810b400041f81a41107200d0f1b0500900c403841180060b000c2c0340c80307500c00420301d40d40901c1082241074148040c208401c0c41c09000700101d10b0002052a04102d041c108281c1e40d4015051050134001c2c150034054040c480010240308e0158a500100341a588003a25001c0d00d031500006042a54190b2141c10b5010005020a5880035409491030300869505403001000200440c80c100d0190002c64032951103040105d03040245a070041050755000700d4000390152300b1b142c10340c2d8510448030a800b41d82e01070a4054440ac5041e100c21002886c045c2c1c21540146803956200080c0c009440d035080e4101c01400780100014800d800081920b0200c1c0d4484002c0c1956902c0e6807030400290003800b14041008002d101c40d1010402c2840380c1c40031107031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 91508157 1250 91506907 91506911
    0xe040207170c070905060303030112020d081612030905060a111315020c06040f09050a02040503100603020f012609010207080c0f4806180a05010206012d09050406 71
    0x42d00c50024103043d080c1d0b101160741400d15042050750340c7c0c04070448c0c1c1510499410060141040c1c0080340c1031610000b03004010480005030b4413100d2022541810708a48104141c0107544448007045080c0d80d003200700102075501140c0071514414050300050714a0054200f45410140090b00e2001450010342c0540329240540c45030100300c640c1170181c50307a554016512035140524110342664110360758400c410752286d03180b012508510443c0c045500408005084407035a0800f40700c06030003481188001c0b4800e840c100200d003000d50003409000c0904030481410074409045090303022011030002c1490031a0b5501304000000200c4100c0500005888000100950800c0389203c0b840c00008119616001e0400700326842c5808421954024521000740d5003020310101310300c83d00244240c8151300b94040070100b403801c1090000d04d514405054203c4c5e600c0c01843d40c070001642c80d1349084c010111100d0803800c140d0445600c00c07c1101407201c0300c000d8200c80ca41d40b42c80d554221102501d007250115 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 91509407 1250 91508157 91508167
    0x732180711250801020306090a020f0405060d0b0f030d050901030504060b030d080906070c0f120905120a020103060b13120f300e0a090c1403090105160309050d0e04020717 75
    0x40042c1c61400142402000851540c03c0c00d40002e052204004d00c45145030f600040d444100d682d140301640c00401e400f9080584501d04c5040c584042d12001140c0c900604169000c0445850001218261302d0620380798941380509200044003d01300050059800689480b01c0582a460800500035912a41d40d0380344542d040c411002d90034140040c1500040100341e08050011642091031030701425401901e2008040ca0030009850140d00c03544180d0784451048200304603140c0c00304000c030a60b132003640c08012042d2203908600301401080c060f081d8008165106100742940b121901c00031500450328440700030700c0c5688000880c50201c40c0c0ea40c2d0040c3c8840807a107206440c0710f1403e03100c075103410301d4885001d04002048a03d681489220703074040c1c071a80c0681106008481c801700030880f0000a59a03441c080021901808083d1103402e42d1b40c5682c10341c1050280309110b01d000e138a40c4080501340310320300b9000c100d5080141034205c50380070703900b040300d8400194040488078a90072a032910613121 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 91510657 1250 91509407 91509463
    0x311060906010305060c0a1106071d0103050c03040222050a06050a050616030f11160503060612030306040f180303140106032a03060302030732180711 66
    0x6801605814155000c4001400095001705503d50f010703003541003d58507031103283c1003142c03190044091948540203050500041d240c1c481c05022803400383d0880d2201c4504024011002c41c1d40880300311450b1407007400841e005140c1340300003a540f04d0f0300c2009810818903149420040369400c4d9007881f401c40d0383d00390801503400d04611080c01010125181c2e42001524401c4808401407180c000301000800b051010049000d43c4007103012015510846868441504210303200d40441c1c02175903c40c0c0309050010703115291901315035002040d6800918210b803145803c0c40301400030310012250190300c4003c942e5080d10080e103000081c3c0c1c00b981d4040303040d01e1810561000d078081a08003030109400c19031000705810307181aa8240e00e03030451550007100c10b00c100040380100380e6500025814080e07248001052032041e46890b2000043d00350303074016180b214034145e6880d203508002c80d82280e8218032100d88c00c08404400355000d800c4e4105410113001402104e0304002d00340307000c1c48650804230111000307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 91511907 1250 91510657 91510663
    0x504030606060504030f0f05160602030d06090513030e03010b1305060a1a0a0e03070306050f0f0c0a090605090f0402161709030c060313050d080106020c0f09010902070203190311 78
    0x1d0041d820080d04e400e045880c0c04040e5030440300041c001c5458182c07154100b25040203140000c4960030800c100480c3c403004001d44a600046c8410b8a49003400d00103d0015480c1c820b9500541488181000c2c050040e6010395100c0d440784907030303541956100e0a511032620f90742c0d00845034007080325000416140500410451103a19080504500300c061000c0c00340246070740c215080710406082c99070000303402500282c0b8003291030300000c0070300381400c090046504900301c006000390a1200041a5035403400140c03000e5024043d00c40000460700c210810669019000400b001c210140001880300c00060200702030703074001101a0000410000500144014442e21130ad8010308241e0441c81c0050000c0000c0d03503100ca0803061442114000046030840c5514a0054082036020090301e03c14424004043c0c0f0641d0300744201005030046407029000ca240c80001c2d80c1d40000c0c000d04103112a4200424000290007140c0201d82510036000840500c0030047d400c00080c511a5990f40700e0304603000141d41c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 91513157 1250 91511907 91511909
    0xb0a0f020d08150d02060f090109060c021318020a0839060a1b0b371a0405010e072007140f10110706020d050702130207080a0504030606 60
    0x411904074203006041c0e16441000181c00c079030010700c81d1011541c0c0400161200d1807114000f5403201d400580f44810003019406842104000d8a07034821459503a40265402850440025400040341c44d0211101d116a0700140c01c3d00a6043c0c51708540c501c0d54046038110a41e0b410103220b50b80201050098407543c00004c0910b040c442005c0c48950950941815940400d29581485640c0114541c0c40041c4a12294101440341c10302e1a0810086402c0c45000c0b044c0c01c0c2c2e40308810148071030007a100640d680e07a04d004000704000780300712408038041c3c21318020b0a00d40307414108141866500035103035440d4001c15000e410b143e203002e03d51382004030001e0250b00c840784100e03001c040b080036152101403001c500001210038610090017625201c0b00021540c000071091942d0080350b00c205425229407107214245041c0702801207400701522140141d07500c9903010f4000000580801a040c01400d00b55a030050300380344041c025041028950f140a029003003001204006030000c2010400c2c000c00d0b0003000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 91514407 1250 91513157 91513187
    0xc0b04050609210f030901090f080901080c0f090103050c0c0a080c060a110301140a120506060301051008070611030705030412030f0806010903060207050a050105011d0619121b0b0a 79
    0x310940301d50f201e04009030181c02040d001110002c40040c8801c4805c2d040800c50329849a1101420308580c5040c4120360850300d05039002544400000d600e8020030001c40700411050f4100d036042c00c544900443c06480e000b41501c064403428802085603110801c50034a484d44240c4041d80c0320140d101160340b80c820018401d0f00586c0c1004042508a00440304170390541d8100701d1034030105040741c40030965140c400e9100c0256210004640402e001f400325950740945005c5000f0b00040d207600c0900401c85047d405007081607003242c4020400c4c0340c052049a001c0108510503030781004c0c1240c403610b09540095201006141100380c02c00201644803000000110342c5040c0004542051f0000030420301c60790000408003039001900740305105003000300d00c0b52558424028400303583c513050380544012200d0000c4102d00c1398080481c011b460020440f0032002074004241160038509889100d40422144060f500d00d0081600034030400c2c003082640d40030b00030100901c0e650358111a0020300d40b02c6040004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 91515657 1250 91514407 91514443
    0x60d09080f0c15010e0412020a021005030106121e0e10021801090b0f0f0c010b0901031b051f0f0c06090b061005090d140c0307120605060a030308160c0b04050609 71
    0x41c005d12401039403954001d60010711101c00a046100103038604003030118080d500034080c108040300c02d644000250b058448507580c000340c612041013014240d448851519400b040c0e541e4030300c1c00c049801e600c51903614014100721140c031900d00496904a80c08590000b440000c81e400310766055030800280e800070112017200e82c1c0340c00302041c80300000340680c1602c2018040000f03280300b40c0700c42c250404000048000c04c1141656500e140641c5030030140c0304500c00400d6060000101454940702160f80c40500740c040f410344282c205011182450a00d0f03841c2e05011503291101c020800030700c19000680c0c0318801030755150910030300308022a2007c1003660304004081241402c0c640303500d40c52080041e406000480c540920708441801c14038828407082e054032840700700080d24680b5100302038a080c081d22040000d41c550307070b040c8130402c1da00c8c4c0800750104482102158a41007044d01c5003032400303c4c03450000007400003a80e030600260015541540d059210500b808014403050221080c0c8026a44403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 91516907 1250 91515657 91515659
    0x6070f0206040b100e16081003020a181814010f0c0c0b190c020a0219050a2709030e01030b0306010501020c04091401050907060e040605090105060d09080f0c1501 71
    0x100940c0c4400c000d20043c00d55500d4008941140020828400a043d21084c40c020b41e25000a10f110044041904980002e2100c00070404030810658290240e03074010f01400c2586062400724003100e59190200809540d9645100403d07510f02c0b45084036052003007003070b01e980000f2998400d00355200803a0304107829181c2800700180315040791440c03000aa0001c2441c1150b174490800c2a131100140e1480c000341030418a0a5082d00c1c0d0210300714251034401c444e60701102e003d050065418442034040c6580000d00c0000c20700005141914500802c48001426024003e0002102060300c580c100d040b40443c600704440d0038590f80501400c8880002503009108542c0b410000039590301500c41201d0080b80d0f200000d10912040c440900c0c2c40710b040d1002840076083c40742c0201d030b0b600394501c10100080c00313400c0381d115146003074010403040740c000a10080703c40e4201004c0200c0c0d17a001c4048582d0032541d41c0000b400065000380035000d001440d640d6140c484104000c3c4609040c09141440504881400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 91518157 1250 91516907 91516937
    0x6040e060112090503040f1d0f130503040b0708030a0e010c0206130822031202210903100f0213080102070510200309160501020f0d030506010302071703010302030607 73
    0x2004960040d400d103000c0b642014030000c07030340040c201240043e1460100040108058444541768400c40702814496600c4041245803130180000503102810400341e00c2000c50b000342c0307841c0300c131140150082064902d040c0d03540300744101c0c1f07a10030403013111030050200c01c104509089200c5e0700404030548000b440681c022001c02525450300402c0c90600388042d055076024401c4c00419145000c0340c0404045031701044110a05840382244402c4408801804083c6141340c404610544140d160500500880783c0d200c51040303964100481d500c0d014411903000d0b81090505002d403210385803c18070b0040e980ca040c4501c015040003103802101d200e030300422881e00020b4000860004100e50110009040030403040360038085066802441c411303000c04030a03c21307440404036900301070324088c0d0344000d42d030341c0c0e5500107980754202850f90807499040001e0810000d4040c0e007145904c8441490018a050825503640300592603000b00266a03010100041c0b04504041005a401c40300c1400d2008240b40604 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 91519407 1250 91518157 91518179
    0x515010f0215071202041805010905090d0806010e12060f090708011104050f21010c08060f090403030c02010e030c010e01060b09090103060c021507080a14010501050d02181810050604 80
    0x703000d4070f0401c03040c200c00c1a88405180e058074050821004654603074144c2c491400d014200c20300175890356500d00804a42860400912011190001d03102c7d400c8543ea0400117407109120700f040107400480c61940f140450100380305061141c45000300c5080305062418125141040b1a08130034116890414800c062159080c1600c0403204100d5500340200b03071000201d1014800d081031840e140001014051103290b040d006210502c840342e0b0399565650b2088100304203080f4641025420032102c5000c038000c80d109401101c40712240303000201e0300840f02c00b1031a185500003129402c0c40d954525140700040c800b070203484000c0440c0a10181011010740004000f07900602c00103045940d03401d6a001b0040c0203016040e44170100070800c0403940f42c0a03501800101040b51b00d02e407010302c2e00c4a0050180360000d0442c0c1a01d5060b50b6181c240713a810004080250702652030f2070464007141592000c0f513a43c052104440429001c04043c4a0030701d10607074002403406070803075445940140824400c00c2914 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 91520657 1250 91519407 91519411
    0x516141e0304140f3102090105030a051e0702151006020d1803061812020105040503031317040801060f061d040203040305130f060215041e020109090515010f0215 71
    0x40c11070302c1082e010500005080c1410601119080800034440c100d020091545c1241c1c04040b031321340c00e00381c8016000c1e2007040348034144040303000c11414008034400700c1c01c550107294469150741070641203880c04440d054074045c0407500b050040c1d02803244401281003c406c0650495424084203140d181480d50181d1689880700c100c908100c48555079007585d1040000020096400c80070400c0080342002104515902500f0161001d60100300107059242c41440760901c40c0390083c02842c1151104115641d001c00742c80401d94103140c20104006500c1a00c3e4020002814440000241640b42005100500610381d009500f4440c00789414041100c40440c4001c1041d411500180c0c1c9e80c0d580d2600b641c403405030340940b02c8000d150010125100e40c00c180c41800b030b02d240b82c0868401d031480c012450759008013214014810b080c440d5048002440d0020340124103403050402d00340c60ba486848510840b1f0049845a000488026810032656000a5110444003551010305141030080c00803040071880 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 91521907 1250 91520657 91520669
    0xe0a0c03330203071b0203060106050306061e0c0105010509010f030b0403120207060b030c06070f140309030a060f050705030426090406030605010806010f080703030f0516141e0304 79
    0x44003040010726003000e2840d8604201414645100d440044a200081d0822500c400c0481e20b80c031058045400f0785c3d001c403a0b00a80c018001c0c94140c0c2000c10444003500003404080d000f500074011020718081c2d200c5110045a1600c503165126404500c0c003d00351041030748524001c0b0303188001800300c50741000a100507241c0040b20704115449601d42158140096919102094400308081003008200d4200b041030401c12001c541c08413040004102d03417803060800007001e856028000b4000510403a09a9110050500c15642018091804242030141d42141207404664800046130fa101e56403140396005116840c2c13550551070540d9581104407610240007022030342d18851f54204840b10303c1140c1840d2030180c4184411765491520401400342801440c10500500c1e0001c1030303800340b0070034034401c60f01142d0040c00ca041c95034900391891250382e800c500410804120140c0c0881c20503a4a0100504c16800303202320280d80c10100d403c14031000c10300c0000304100c8200c1e014140c1c000080d00c1c1500d00d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 91523157 1250 91521907 91521923
    0x307030804050307140c040608060610030b0a03020303040e0a0c0905011209020d050d030911061303020910090237080a0b030a050a050c03100e030d0507030906060b0a02010e0a0c03 79
    0x22242880c41c594001c0d00c4d03006203a54a00001035038040000300c0d5074410408140c0341404800d8031481c0d40e50701e9407412250725811007501d405440f0564402e41055000090141c001e440054a0313401003400c40e8000e8001011409451082c0100d01d031a9204403058921145001c403101d0303003407000007428841c10207100a40d4517112005401035581c0c1c07481c0701901580c040101c600e1540b4148002c5c0142c44045c03802d44500240c46074445903400c01d90216403202680a004c21091825a420814442c2c405002c44d1200440e04030041403041c403504c01044c116540b103424401000304401e0300148020100307942c49400c020389148050007138008603100e0f000f800406000c610743c0780280101e0310380859408081d0151240404c4076003401404a4240c1c2c3d8074409506944c2d41d100b1201082c419100c0d001c2c0b20701c0481e4000c03c040c00303003410740c0d50282d84c00c40c1c160728001c2045039860b19a02c09482c4240c0003000d11500001e09428850b4091180030ad143e83e050010307041c00c03c00c40c0c0b08d032541440984009444c03c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 91524407 1250 91523157 91523161
    0x3021b0a060e031e160602120301090e0304090f0603020a090c0e09060d0b040b18030a0c1203180308092505040209010509120715030911130204050a030305130902070503070308 77
    0x81e400713028007949001d18001c180c0000318001403071540d40030100311904103d0b0440744080355562010400407920402460003602c0d50b4607041500c0002d0448484080e0140024480414400190f0080f10b04040d10300d1000b0038094118010001003c1035580700c0342d4024a4426811603031500512002c081d0b900850b09550345039030700c001041d100f60900b14010b00316000c1c0c0d01003004125080380d0050042e005070540000d110b841c1c3c0d0069607070303119400e043d46c013283c01d281c4900e0015604403c02040300c000d92902003841e184600411107441281082240420107580c10015409010411080002d5440c420921001d410004d419030849036401000d0080b40c00080035501a4001c0b0100c403482c44029028041400c406003019896000e28041c18100c816805821690184a4010a011550011340d42d4001d076000070104003003c050a4100b40c05d0540034040012181d0300c588101d001580261a61596a12902506070303d40c0015001103650300c0c0306101d8200441c500000340c8641550506003a6115 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 91525657 1250 91524407 91524409
    0x306030a0204090203030d060306061410021902180703140c0a0f030902040b09090601060314070e040c0e040e010606020609030c07062a0c0303020d030e0c060702180c0703021b0a060e 80
    0x26110314205007030860308023000002040302661101045501e06400ca520781c4845004200340c00c00c1c4180d160700141e101144505415605030941100c0d1840101030f02911039111311818400d42c0c0c00c03030f10000465641d0314050f0076449205c0c0b4090344211500c0d0a103207402c00810014002d50401c8000b5002c156451b090081151500d0303002da18612402030600c13000780b43c0705903901d560b45424041c042c002800d04c849401904065241c4c2c0d8010300c0ca0f9107405c22082d1791030060200600604100b41c0c00c004500c030400b42c060311076204500368040030b403001007452401c051010703203024400780c1500b6043d8401c00c041004140003042c440151025898a1501c0403000444242c003141e0107080c982e6001d1140c0040410030280d01c0045040703034400d4003035071500b955080c0103a0840e10258a101480d4101341c140c13401c6850301b04000c0c40414401440303650062055440d0301d4036100203c5010201c42d0300001c4060906404203c2c42c000702400301c5a03030004e80744120202e1100551485250140f0040c4d500ca090300f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 91526907 1250 91525657 91525663
    0x304060b0a26030f070f1e0807020603130204111b0304030b0c090d060f090c0905160318050a0c06020c0d05030906071406090d030b0301060506030f150a08070e0c0306030a0204090203 80
    0x16001411500304d480304172a0038410081142d41300d041f82e81c100a0b4201480c0d0b40304c0264200007498202d0080c2c0e007860407035000d01c43d4a510003411251448000c0d141070005903160300c2490002c00c2140700b901c1c0c80e0301e03401913000e8070b510a4105c80c10003580107002c02c0000625800d4250350003907c010210f901c506040b008030700c8200d1503880c000c10307503414404494034a400d00d610040d02603009420100025594407030030303000c442c415200300010100050020100900a4001007074410075908810150a140e465041c100701c0002c0d01100d00144440c01080503e40c10480071010035000c9410110301e009035a41d82d5a01d1240a60044c01010049803007400d210402c11601d0b8491000403d1f80c031780e440d00c40100c40d101da1554a807000071924007810f2607020f082c14440d400694801601310762568884407a032085c00d401c020300051400e0000c00701311041e0b441e1054400018140c102c020072030603081c20b2041e8000c400c0205003c403249014410080165400a0400481a01580d00041003090342c004282 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 91528157 1250 91526907 91526917
    0x7150e0114011211010306080a03080718080604021f0215090a020907030203090d03020c0d030902061902060a0c0219020d030c0c060f0201060803070c0302091909080304060b0a2603 79
    0x100c81c03155480005040002c140042c20030390f101d0f080040580340c44e28015011603555000381c203041d50110218000003401340c010182c01411605210441c156265080704101c445500450041e8020106002c1141400004003407402d000c0741010b20a1489a84000c3d80e8201b5000c02204448000c0e0104205481c1072010070f9201c0d40282c880340603450034a9020300a5070065510b000c03188101c24109007101c4c800c0c400e480d44000c03041c001e08511080b0510890140600e0f5005907881a03080101c402c0c081f07006000407034982c416401034501c500d00a0070741422100c009440c40155040410705042d49000000201d000a40c104c9520301e4000070b42c101103c0746c08a010000340504104400070842903040420041c117081d84d039000b800504d445111058480c00390100027002c0010307025052005240074400950303c45081041100c081081800700300a940d541d0200391381d480030000612040c8842c6e8007a9010106060ba000a4010301d84030390041d80c0140500322840d580e0940320094010304042c01111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 91529407 1250 91528157 91528181
    0x1807090b070c03200a170f010207120f0302070f02090a0b09040303050105121f02070201050f1303020925030e010603061b030e070b0409110c06100314010207150e01 72
    0xa4480c207003454801600c003203600041d10681400381c00100301c2c2c90081003006100001034020302005161121510801c4441c1442113254007942c45024803801d0f091016041d1a40120210348031031f000100064205540c2400050415004004200100c1d800d01002842e2540c195940c0030107a031840c120390014400c2e020708903480f814000034401030581c150400b41c1a03501c102e50101d00010f400d000350350b50309140f01390f084a01d0904810040c8000c159400b8181160040c10981d2a040e102050281aa840070340f032442e50064001c41402503040c0039500551000d5161810880d41c1181e00104000003903c00d0700d0030815480746460407140e4420b4125070011580048203010b4030300540c08447c941182e1025078400607203400c1d075030701850500080301c504554507c50070700d14081c00e11400740050850150a01c40101d42040718441000342040814420051506291215811480c041d6044c9002011451042e07006004c00300c089200ea04078000c80220b031003000a0303108001a00a80517000801e522 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 91530657 1250 91529407 91529429
    0x70506090103020d18170a200c0303030f01090b0103020a17071209050109060f06210305040f06020607030b0109060219021c05030a08010603050114060c1002041d0f0105180709 77
    0x8074808001c0c220300f00600d1413090400c145442030042c6d1a030058090207028400160550090080c08452480c2c2c41030044209030541d003081c40c16038040f9241d0340c800e5a150b00902c1d20b0304010002c000540c840c0c6200440246410345c5002e114140040c00001003040c107011080341140841d1105000d5504005001030081c8180000f02039824141c5c02449008000d81e0240d052020011608600c1d10460307082d1680944003280b0840701c060b00640c00704082c0800c0b8144041007102060f40caa01c0340c80c0400500c0640d006025500d024900102654108000141444801c0c0d205004264012641039208084245000220b04041c000541843c04549246801d810030320185014840b0110082000e40401c0d19001c232030343d90b03540c0d0403001c813a42440384c84548440c4072004081c2d40f50100061000400c3c0408403001060310104040807684184d00008204800d0785200031003001134a80c0c00d03481340e11048444540e614010224402140070301c62450b52006200018031001e01841251001d07045030054 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 91531907 1250 91530657 91530671
    0x5040303030e21070215210a140f0105120715030e01090b1302090108060c030402010e18070203031e010b22030804030b1b031308090109080f0a0605060303030108070506090103020d 79
    0x42e04201e83c00000141d014101d461b40c1d10000c0c0300305608071200e0000541d43d09130001d41d0b150031040c00714405000d21500c41c1c0c4a514584c107030001003d584c0c0c0100740d03810745483da552401082018103007201000c0c19a5401c500020840c41010384204240e000c400e01300032070941484166280104000d81000380401d81c9070060000360410403042155441c800c0e90142035590b2501c000c00d540e400111245401110200002001940705640f42d80f00c600001c1c0012818052a002e601c0b4004000c440c4400140d0010080000e004480d1100000340440e55000d0a1a941444901502c51040c040701c0f000c010390320708414074030100d402d44040065030014680c58803142c881c030300044c00c00310954030308007400ca03944601d684000030a8102c80c050082c0790102005251240d172403c0c0c040c0c0007060440d05020141c1000201140d0074403003480302c00200c1f005418001c250380381c4001100d9000d004580658403d000602c2410780018107182501e00031954161105540c50048010340300d452000d508207814003503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 91533157 1250 91531907 91531963
    0x31c020a020706110a08070c0308070b1605070c0b030601111203040c150e01030504111302030901060608061003021c0207030e01020708010c0e0402070203030d110d050603070605040303030e 83
    0x2016118021059090351005070382c4003021034070101c0c4030011a01540004070403030001003440d4001d1503001d12582040741180e544c0d85960340207030071105080c1c2d50b10907110b04100101d00502c0d122502c4004a0034000d050000729100c2c094074203218090044914000000324800e60b010701ca40d00032050288046803241e48400b00540165041550200e0780c0c54840341011a0403844401030b11140b0002e583c6002034520400011405490040d105403a0348010145850468503030000607018600340020150f0b41c2e0514080700d600b19041c0e98010310400030b503141072084030340c0c804100006c055964900961035002080412074942e00960f03499074401c4c40058910300301343e01320182d041e040c0c0098081e5441c8555400441d401d0360100188100092100b01144059182c03950140c40594009801c80e410101050340b002c0407610120792481c40001d000c44d814240e45030703a000b00c40e403211080c0d01912149180c05030140c150f004602005080c56103d1700001000c1404000c030340d1082001703e0000c884411980 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 91534407 1250 91533157 91533161
    0x1081f1203090602031c050a060305060702010c180f0b03100906030b0f0f0118020a03020706111306050405010c02010e0102010905060c03011406041206150b030412030f0b0f0f03031c 80
    0x100e04801040c0440741c001a000e0002c416110b910b80710400440e0000030802d040b4008200042202c00703c44d958040100100700c003004194410b01864000190801140f240a804100b02d0f00f1504520408048203001d1820f0074280b4008441c00b880c000350f10707900d51442d0318000c098580c00031003410f440c0010010a003c044105c0d070f4080d039540d00000c01141c4178415182c41c14042400f030300600c10341d13000f0035040100d0350340d0082042a5185c81c00504207142d039511030301a1018072622004500b004030350b1000d0007008108040c020310391403c201d0700c0c042c58040060804100540064184007070000c1c45550b5074000e420060300c1c0b551081c286c0d4024684015451015003003806101580800c0e84840c60080c01d00c5c0040390706882c900000d0480448407956148042d040008034408110500c500005030355002c107010703600462081c910305c1c503891610f550040c11216007a2800c0404c2d41030410440702500c60050b510040c000644480150791301c0c0d40b010900e0340c426442c880c50394000049034012102c102d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 91535657 1250 91534407 91534439
    0x11071703041202011505062212021021050a09080a0f020105070f08040209090115080c0315010b0909090705030307050703060507080c030106030203060a05180a11031501081f 76
    0x240100740070081c642d4022400ca03070031100f100400301c0c0c1c0b15400f88080e02c2c1020103800e0040310803160140541c921800340103286801c2d4041d02515815a0000c0d00b18a007861210100d442d280c41d19007941703101340001070882e4002001010b06642c1e11000b04101c6100750304a545026006040a65600b180101c018000c200310802007006510302808550742511a10078049c4071078640c0e8807409503448a8082007407860010348480740a660781c0c21650005c40324904051b000346114409460440e104205244c2040304100b024159504117200611280d8101001d07a8010038050703510300d000e43c2d24010710f50301d81911508500c2e4148400324101c400c0100029100c0180e038410001489507844000302920402030039030b20041002d40920062050a100764090341c2c1c0100003d0a4450450380c480100d01440c000c11170508001c600030041148850b407034003949520f41d940c03200d414070310303d014103030250014680359130b40f81009084001320b8400d04824195403002daa5a440d40c1100d1980d60290025007442c0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 91536907 1250 91535657 91535663
    0x3030604060902090f1201021b030705010c0e0a09020d060324060b190810050d0606060f090602030a0e03100e01020415020307020102060106030e10060e100f0308040302041107170304 80
    0x101030303001c295003150340240d0f26141800340442401d011744400b00070f64070b4204441400c46641c04c0c0501d0354544400d00039541c0e41903c03c005160707a600242040d43c00d4422002030300051085440c101c440c25154035080d54115560030364016119524901500060151540007904500e28040301e103280b00012800304003000741401c0e0410180c2d560b00208040360060010101d02c0c401c0c030a0000078030502416916500003406100c840d01c0d50380380e1307000906001d0003160a503191956004240f040c240c220110040320811400c0001d074880c68080000d66a00c82c0034840d800704100b58460f901107840c01c115a00420414402c107011054141001500079045803040d00d050003140322000841500200484a40540680c041e00c1c0e541c0c00e015054003c0d01c0b660b035104445200300703522513050408521968000d02350350840c5101504152120040d220f005400c9201c82e182d4609007000020312802c11542140e0f81564003059083c10300301080c17128000c00c4405040c2001300040001c040d14242c0045105500c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 91538157 1250 91536907 91536911
    0x34060e030406091a030606070203100c0203070b0a050402151305030a14070501080f13080c0303070c2108180a02060c0106060315030809130b0604091a010201020310090908070206070503030604 84
    0x203501c801ca404e8142000c000140795180420229016082c480010000c1030b00180444180310070030305080c02102c18046a003001a013010a070302d42040780f03a0b10a90741101d80300005100e03504080e0001b9031070716458064801e4030140012015108155100314100918004050b518080040d04001a4000d41100c0b540c2031800342000100300c0e90300500e8064096000402c2800d9aa40c03240410641a0301c800c105540744030702400020405081000258030800942d601c080782500645041264601000342c0501c422102c0300001307001c04e40c0901f0456102403601d4401400b94400001c580c1048102c0a000e904000000380c03104690344150050001c540240c1d0b010050030000006805141440e4000100b00c5202000744130b83c1440d010810406200b2145030000c3d0b0441024000361195115500c0746c1440c50310b81d5041baa0303084948035441d1440100780001d511314070b0720340c1c643c518000a41c001d0580956880c45c601c0203120031501540d9807954080c10056480d0040e0078841d503a904100c0d0405e200314 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 91539407 1250 91538157 91538159
    0xb0301150e1009050f0c07080f04060302130501110307030c110901121202011a060903010b0a090911040b0102070519030503030a0e1e06010603090807020a06030506130234060e03040609 81
    0x80c3d124410b162003540f101160b02110b031201c1220109680c0700c40d07000d4950103018882009900c0d051401480101442d4400690b5508480d840e81e40306802584000e0506c04e10f00c09540080368003100721a4410f0f49494540e520a0075894190350301010245c801e0781191a01002041d11114699001d0140380035140304e906490100c58101d003038852040d4080c1c1c1008100c6110585818124003411000d000103002040401d1004046401e0300700c0c5d0f6111520445d100d2001c202441220f481400100c0c1c0161003d0086e1400100082c0d9940b1f1644240c80c010340d00c8020364003400d03080d03a0400d0099540a000d41e17560b400c22507041e1000c0c101ca80d61401c0d01c3e0080f00c0d0340042d00c403e0940030311188003c02014285036842c154094009101e03102c4142c8103850104400780c0140e4035840b000019110039200011070381810400c0c00750034801c059030110074520400c001c50305000b10501d40e10040d14034003e0b5000108050329611401e0400354002401e05e810f092245410300c3d40480504143c03084d59860038442 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 91540657 1250 91539407 91539419
    0x11d07050f01080a1407030f060f03020603010302060702031c03021201080309031203060d1506301205211b041409040606081b0f090108100b0301150e10 67
    0x1000a44203040c0d010703140c1c440300009540543c0c1d0f01c0303611208020000800002200090f002d0f0301d42151403c002035991012905003d810744540e0001d008a21180c140890655000ca43d40784810f0001920412001c9907000456808001300706140688140c03a80079000344505c040d0194001c4040140d81030f28070800403609203400030503503c3d0380000800410701c040004100c01142e51024280c0c5812025120312140402c1d420003140f600d0344117001c00081d1551034420326103001c18800b00c0340040c80c3c0c0388040d40c50403c6420380220307000f01d03040781d8004c2469071022801d80300ca1045140240082c40d001900c0301c13540d00c421407581e1180440200886501c920320b8a141030a1085001d41086500c0340d140000d49030809003d00e5a10a1080c90005003403512200c2a42c13821980e0101c5c5541d5004440d190480d900b020428414002000e0b51040e0f000d5060800203610b40c480b4070440010256a014103003200c1c3e400350400c07502500746441000400380c40d20424200350034100c40c5000030b040301010000701 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 91541907 1250 91540657 91540663
    0x40303111c0503060409060b0a030503030901050c070201020d0806030c04050c0a0201050f1e04080409021b07050f0609010513050604170f241e0c0306040f0606020709090c08010608011d 81
    0x900c07910b503603868556502c00c02040300402c030440068900c69901d000d082e1071030315110425001341d40124025600e03880c04071040303401d4400050208803442c00030b01c410340040c1d80000b285282c49a241c2021882c45c5d4500010901c0c1c004070b000074540c040d0404090141901c01e071801090005241d038024451540c840800300c000c0003050303464401c682c2d0320310300714907101c9003848105401c03522400245160695075111070041c1d03002034440c100741110064808066050411101004103420303a217499040000000040d414000c51103000d06110000410103440a5602081005000d0040885460b65100d540080781d6110b04130340c084c01c5228981c504405950002381c104109006c16001081040b041c1e103003e0354000340942841303101c280030044280da02940792560307442164060710280d181d14010080000b941c0c3d4502d002400a45890300031700c440f50340824454140d80b4032050102d100c04480c1b5240c48080000c0d4851a925440c002010417808010b4100c100c40f19901580d080070034003009900c41c0c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 91543157 1250 91541907 91541953
    0x603010b150d0f15151d0f01030905030309030301050319030c06050a090c03050601051005130b0906120702010515060304030e0411040f03060606350709080f1f0b03030702040e1204030311 82
    0x149000c2c221040c20180c1c0341c00f87c1c542d10f500c00c1c18035021034004040d0741d9040c9550015a6442c0c040e800103c01403206081c01c103c9104007400c0e51810060000e866200030b4410f030344904000d46801c1d194000500c0e91020740c1c00c50171030b140d80008070320030301596401c02d213485000030701440340300d40f6268501440b150300c0307582542c0c1c0c0703501012018541c1a1070310024402c030354001414907411900c180400c042014030900458400c4c1c599400105651901c00e180443c5110714810f42440b80c0f03030520034030001c60b030b01c003045180c800015500001ca40080d4840700400e801260300040c0c0b03c0c85082e4001c010084035421083c11076601c1e0301c0f400500700258144481517840001e52038034021210504203096210b00640981200041c2810315002d13441d10910340c240030310f030004210154484141007100c42006a40d080462240d28400c0003414001c01c0000c3d168400c40b03201a1065803606907140b1160700500c114044054184005982c42c0d6030b0f41b40203004d4680d9400d40d02c40600074014807200c409190f5990301 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 91544407 1250 91543157 91543187
    0xf0c03020702060d0c14040806041a131403160302010e010b01050403020d0f081905070212060601090303110114190f0207121808010c0e04050603010b150d0f1515 71
    0x9410456041984c0c001020094855010003140c280d0700d20311124110001c0018004120280c0792900d8181415419900c10902d03165098812404104d803031a8410914061242e200102d43c1460f0f500c051140e1450003400346a200c021040342c0c1900406030154000007415800f50000e00280c80d51400540b050301940c071001c0d40201904944000050703804021490040c41340390010705007030300094070b6140b042e15a0240310108600042b00340c2546811403c64512210040081581c0d2a101b40020403240d900d01c00201032000c5e100c6058108002074010305002408182c00221511304808905410a0301d0320300c0041e01860700a25a11f09030340f80c003c481e034260b000090008810110001110f400346140740440c1600c001c642c02284620302809070b025000b0813582c0b1518190a548100811181c01408d2244030381e2401401c0c1080303071624070400307030361280c9903502da070321080301c2000200501030400301c24003084c1c40c0104440c0791006158480d4290340c030305048011252442d8500341d8410803c1c200c05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 91545657 1250 91544407 91544419
    0x5100b0a15020a15060f030b060f12120717030403090501121104050d03030f0609020a030f1a0f06040905130309060509010801050418020603010b040302040c0207151b05100f0c03020702 81
    0x80f0204080b10415540c41c024a4000100c155131081c00c072210500c1c0d9042240d441c1d084906010301407070040250070000f10101d8600302071400076119150303a01607c0002420700e60003c00c0580500c1080c08181c1c902220958040c3d980e03181c00c0c50010101d0341d0600405000c01d8040d0101d126402040c0704000410b1448220949031a00300700c20000b1200c00c001c011810980c0710201546c0c0d2096501440c80103000303440001d600e4501c1a50040c041d51030704000d281e0068075101c4120116080320305607051868064400207400c1e070645001c22001c2c482c641180c600300d4100f0040c000380454401c40031903502d0088d5143d00c962500c0750030071201031094610b458000b89490300141301c503103040d61000c41380c5600040c5d45001e0465690104000d50826841502c80c20404034003001941058054003109960320300c041c001182c1000030102089644803082e200b00300c1401d000c4044141c0000300602c216400ca01101ca914500b200d0312009403901012403602e0301e042880580c0124064000c1d07a40f40c1d41c2c02020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 91546763 1106 91545657 91545673
    0xf0d350919021309081e0a02010b0603041a101d181501030807020f130911150403030507170307050a0206090c0904080a0c05100b0a1502 60
    0x80c01800c02040784807100590351404034410100700f01c000010491418141201940aa80000000f92070403090380300c03800d03030140058000f200d0658001d1001c155181c042c002d4500040e40c0c02480c0d50b1031028002441501c800113140e00115107488a181541d41e0000145040051602403520384095000d000d5460024a0011301300c20f950401000322440b420881c10050405200c042c0000002243e00c10466079901004002e0400041030520080c00f00da048000500742001d040b01c1d1000205040000707400c14070b10700400400c0c1c5444850415155480a0b5403e6108078000c0ba044406044a480c5000050010394001e01840d0b40b841d84460702c5543c0645083c40281c08442280d000140c04002660f80f414180d80c02503000840d6074a0303c0f010030003595420884da1000303085000c4c290703401249410340d078003550882900300d615480351551918100100c000203544000180c100c045 = true := by decide +kernel

theorem cover : BRFrame.Cov 91366907 91546763 := by
  have h0 := BRFrame.cov_init 91366907
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91366907 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 91366907 ≤ n) (h2 : n < 91546763) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
