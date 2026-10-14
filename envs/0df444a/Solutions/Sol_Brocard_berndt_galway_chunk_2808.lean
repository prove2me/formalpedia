-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2808
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:48:25.999336+00:00
-- url     : https://prove2.me/submissions/b78279cc-8bc9-4271-9f3e-f0faee561061

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 504856115 ≤ n < 505035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 504857365 1250 504856115 504856127
    0xc021902011b02031e06090f061915080a0602090406091401031101210c030c170a0b010c06380f10031506020a03171603050406020c0708010f0509030406 67
    0x9125074403010034411600464404005600e5817211100e215854000ca55031155a116012034045000b8041d801c40b0200040f00000e400f405203005040004071204e0382c45200c40140804103d9188080d00c1c0301000a58580070304c02d80080d240510000359590540c5000d00003a100b00b03078402e10610307160005842000310521141e906480d80400e0140c2e4005d00e03100100c88410b0103a5281000302d241e02c1c0b07600030710042c2da0300c03018055809440a100ca0301c038502080d2052002125000c0d2183d0900000516011155000103000c120504100c142e0034015103950080740d03800c0c02040c00c1e054806400c01c2d402500401c0d0008001e0404842d980d01d0744c0c400c0080741c0150070301d402c05030182c1d01180c080c1100c54020b406c00c200d4440c112114040305550364900035035402c42c803074054010610001000408124604041740306401c01c020350101d450840c3c0e0200c1c02044003c00903a0115400e1040300003001050045a00400c560000818400d1518124004444000c0c0c200601c2e070780f00300010815190401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 504858615 1250 504857365 504857387
    0x70906020c010e01050c10050a060f27060e040f03021002040b070b04022704030912030e0d151e05010906030b0c07080c10020406030b03010e061b0d0e010c02190201 72
    0x840d001e11540400fa0051380c041c01140b42d1a0042d00403180c006100704100d6108500c925103403902408815070b1002150355204490040d660490602559850302c489000300803840d0380d03d400b20000310303c4e95070340140001400030769040b6102d4201003009014940e042200541c640d02141046150500c1c200ca202664420060014081400d400014040d503a410409514141c0c0c52800010310402021602c0c0f44000c040f202140801c91607040841c01d42240c40400d90001e9050b19140d0300e00000b0700c00c014211000307110890b414200c2015202c65204240504d000005541c000004038040300043c100a0f568141c01058000346403650800214030102c002d550003c002c0114103640c0c0480d0309113105a4842c8005002c6607100d5900e0651401140744d000700100d0709990313401c00c18401540201426104d80e00c20340c19103648401c011404801c03071248004041c40f41030101505e00790100300c542c4d047c0d810b0941c448426940d150b00824103690103000301070914440c03a82d0f60744803040c280d0000c0c111422403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 504859865 1250 504858615 504858617
    0x9070801051002010b0306040812090307080d02030a0f110c1509060c09011206030f0312140c0c030d06090b10022a0a0b03090a030e150f070602070218010e070906020c01 74
    0x204050b000018001e45c059812190040d0648410b4540390901e150541c0c401d40c00700074140388801c001400c004010041d01d42d80e44d80705058500d0012501e131080041c0d04040c0021108640c0c9880000061605110321208600c812843c1c40e2680d18000e255810300440b1205285032108102c01c0000585000c244903510400b0211029211844540100c41c3ca41607120f030009a1880c0c03074408010300070f00e80640b007455882907a07103039050036042d0841c01c1030f1088581c10f1443d04d0f40d4040401c0c01c0941540213495201d40900c2280c1c10303e01045803205c01d9950729849161070569072200c0c03030f0450404001d200403401d1140000d1004e04083c0991402403d0034400c440383d8540c640704040c207203070354058546000b00781481059459042c01c1c4445520741c401031000300c0104203d0b0368107607458100501680e52820003450305038201440c103120f446e0a6400000100c940f69400c001c240b00582d5010501c2d4003400394803040ca4010760400c241d00d60030002c0500b40c03405000d4407400402000c2c0d40000d00c103039201c4007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 504861115 1250 504859865 504859879
    0x50c030712090510020a0c0b091e010e040906090203010605040902030312040503070f060f2012040204090813030311060f06060702040f06090e12040602030405120c030601030b06010305060907080105 87
    0x290101218102c5903504091341c050483c0030f50b1912182d0000b810007078540520703000300384107a4459880d80c05206440c1c1890b002018511203601681442e009a078450806050440400c9212070005003107070400d04040ba4003da903048460107504092003410003405d01518100451201500020303030301d0044070201361001085800003030030418144252500580e10021101902607145001c01c007070300000b103420005a182080d241d49416803c454040c8030001c00151910306008151064441d0200400680e0013584a000990011340c248005140e09074006420162450451400800c10320724007484d036407550310600603c240340b0384030500e01e03800a400310b5000b592625203101160160031120480106545040313000100d1041c02d4021a0040c2d4903032060f280e010344000e5664030380340a0350103100c0040c1d1003840280128107003103e009141030f1312802207851400c0d0080c0080d29000d0700341c2044440a48c440240016541c05002d0103800c0316044680e40b5141c500801700410540c0148959845400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 504862365 1250 504861115 504861143
    0xb040311042d0612030e190303050409021605030705060f0a02071703130501090b190509120f040b16110301090b0c210103050309031e0a0210050f0d0603060c050c0307 73
    0x10b95010f14000d0003400070f4140d01d10111300340600726035003445550b4054080d04a049401d00c15100140040d42da25071101410a420234501e00001d4102d905c0086010b10038026004c04110104058010300e031280c0000d0055140c00190200481005171002280714018000074002400468039580e01841000310b654480e60b0320041c812040313058220280240d460603814906008461008500c01c060261003140c1a00c410620314048560450703504080790000c9103d002d1400d020781c0182264000c0d1000c450506445e0020b07030380c0c294000c0103020940324852002c8020410b01110381c0722020300450007004034810540744e000302801c0040400210840004815440108801850108007074503070304181c080da180d260455903584050321091003441125029181c0460403c047c440c0d4080c403402074502c526035a400d00c07600946080400e01885400d00080390f11080c0d040290038003905800d808180b203803441c1801c1c0c0c1120314544c10b0400700a42000b00084542d0004211510107078080c020f0410342e0f03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 504863615 1250 504862365 504862451
    0x9080304140f04180201080919060504032105010f120b04021306090603061d0118030806061207020d140a0504051309080406021005010602210c10060b04031104 70
    0x1129100b00c1a032161925105804070f0060042d0400007520030b0304d036100d0340d445c2e210032035591f40c0c910045c090807407030095010741c00a003850300101d8000d4031a080521100c03000f00081349855000c0d000304040e4603038810041245032000e07140100140b02c800308820100c4865110300d42050070003007020b80a05243d621426084083d50301000051030290b50400060b9140d26040b0041c0c0760700b842070f078bc010051038a0914242c50600c261b0116000b000c800d02294001a5019950044020002a40f18a09210706e5104d021220a018840c80c401d9014101400300c0d07100180c61004240f080036180c1c03100f4481d104950741c0110444090b10b608440034080b14805a40c01700c040c0054140040490b04045070020705203400103044081340211103818482c5a807902022a40c50301a1101040c1250440401102101248008020840c8103034241c8000758440407048023601c01a40c0600c1c001c4500203400c0045c171000c1c541c41409101e040724140100b401d14000c540703402c410b05540308203002000050403810303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 504864865 1250 504863615 504863629
    0xb0418020a120608011401050a08070521070e0702160b03060d020d020303121905040807150f0501030302030910050f0a03181a040b0a0c0807050d0b061201030c05010908030414 77
    0x801e4102d00280304040c0c8482c0f416003c0c0c101148400509080d50f4004030f42407030f0045005003a00d050b00b0040600514090801024034070900c0d584010700080440da60158209010b4040a000c03400001c02c03150418010003481e14548440c0c1c200b1060f1100700510103064424100e035000b884c100d0740f106811a203800002c00300e050642e8002e616110000320940001b41c1d40440381e101340c0b189c0340d40e1940307500f41c3c4006100351841205c0003840100100b181e140011038000904e81d580f880c000d00041d03864070f002c0819003220000e810a602507840850044090b14040c0707440a450b025030b2410301d041c41008482e00035079020b850744007410305458010750b0b4048242c1e940031040d501e0300260001e02d90031110b2200d1400020941d010784030020650009440003001d0701441e03048003211303034400e0441e40e5181c80403680c40d000903980d840c4058441801003610341d2504094410b20090395207000095146243c043c204040950040b81440070054003080b09040c0442943e003201c814440340c00d503e0130007000042d51 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 504866115 1250 504864865 504864887
    0x30b03030c030315090106020a05060c07030c0203102a090333020a020d0306050105030708060a0b0a02031309090209040813170f0d0534020d14070b0418020a 69
    0x5548404403c000c048481c21240550030a4203684800da0742e42c1f66042282c4441c0840e0001e8072030361184010607c404c15184c010301c42c0c14002e1501160b500101d07030001c5e043c10782e10050310007440d403941c81d145c07403101c50000c0c3c41c2c801c00040521144402201035014080081c7d40c84007038a0380c4501d422020404002403010b085025012100d40c0c0c80b41010400e00c0001d42141454400501c1080c13040c1174554003d101d00019504161503160469640c000b044072409001460590044e0250000040e480c41c2123014241c00901074015548610403d20a9075000740c0950000b56074908005d00307403026880301c0c0c891039080790300700203210f41e80c006240b1076a114040b01e522090400e20034222a08604070081420101e40d06480b003541c2511444000403940b5008941d00c006800130802423070b960072104046500c0c0d00d401090f4400b003444c1800e80002c4c00200c9120300503500d0051215002000e0181401201c010b081980910b604207410044244001a0080c2c803008c0742e181c4c00039100c0d610030301900035011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 504867365 1250 504866115 504866137
    0xb1516020415030c05030106030809061e0c010207141b010f052802160e070e030c281a070b04030c0b01030501061406030c0d05280917070c06030b0303 66
    0x320000520182c04070350403841c030081e540c5008140001c9000e00d8180075a07000c803600320f202c040c02e081e407080401101d0b40c03000383c1d00d07061504820364103d52014000f02518011030080f00068444105042070801c40d030406044078a2a0000c1800380c03000e14041004808660b02880d02110440707000c0c905441c1e511540e00801c00c1240512070150380c2903164545108092229420344501e52401c01c14030012107000e0261030018581d50b00041d200038821200081080c200404803440c141c0b010001c54180060107041c0246024071740e034088030059860b550758008200c24482e405c004540c800c40311246003c3c81c080100301042620200701454480c443c1c00c9401034200c12000c02c0c3d0350b5070340b4080e07000701007a00c6030700c2d5140c02c4521050309a140000c240c038459010251180d20b0880b103030109000070030004000c0d84e0103010404030030300f01d596913070500b1003000c021030f100050b000c00d1400e0100054030002d410840c140e000b007201c40006030305c040f40b0a084920038200810340c5ca94181c0041d0450045543e034035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 504868615 1250 504867365 504867371
    0x10030609080304031101050417090a0905010f14060c030f0d06090f0c030e07030201050301120311060a02040914010323010e19060509071d0901270201030501090b15160204 75
    0x301844408002540214407a0f1902d043c3c003041184864262207044074003030312441d4040050707901a1009001001c01c0040100080d01940d21402c0100407220203810a54032400041014040402a1000804c10401c1226503a00705501c17200324035a00d216000b0004035002000ca640d8141203955004039000d401d0404003404100410440d0100904401010000003810844c40307946014001c102d64060f2178042e0350b41442c50b803d02c08004154400c51070104c04020303403010302d00c84040c1c00f0720009015001422001d80c0d503c2c540780e403100c1030703030300300e4200511a80070100104001005100302070340e0500c01715116007080a02c146000d005003aa200f08440c4d0b0f0080c000340c02801c0303048242d8010010700c0b4402c100495110000da06070743d42401c0c000e288a2031440b42e00340341b00080490280b0783c002000000814401c907440420440e0002060b1000c0c034030781044100c3d504560b0940105405087c08001c20800c40413810000350506d103403000300302510740700050a00d500e1245040030400668001d0024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 504869865 1250 504868615 504868631
    0x702150703020c0f040b10030b030313060504080f0105160e0117010b0c0610061b1110030219020607050405011d041406030706030902090420030a050c040f02130e100306 74
    0x2c2e44403101540514454600d851015000307282c107100d07444a91034050b1208118000c1000c00f0b4008280c88800140d1622007840684503400c078044c2800c0280109544040d203407841c1511551400c18444c4200ca20b86c2d04110400c03100b811109240418042c0390b1500b1580c1802000c01a102e250300c00990001e031030381071400486d07000d162034002c0c102d008410080b00d080d555804030394241d940d943d000302000182c841d414a400a0012481025020b00032400140b5502ca8800040e503110241040e000100b500820140d4202240000e200e04110f0300d80050441407400903c010300b14030960003410f050200061800c12410f181d0742d00d400c8600000761041010400201030560f44000458016111f4030486002081c414401c1c060b4500096002e0000c440f44e4070b86070394101c048200260211070603400725411100769601008080d12080c0208042d15082014506120540c1c60155403003d4580c0100000124042154100021140305d040b03012110744801410300d810012640c00646420705003000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 504871115 1250 504869865 504869867
    0xc020d0c2307050a0e040807080906040e0a0f0b09130303150b070c14010c03141606020703080615270103090203030c010e0d2f16080705031203100b0702150703 70
    0x81c1e0041c0c65040700d078244c500340d0f128000719002604403001400c80c04184203031000640039201a160106005050300e04142d1900341d907401004085580c1b8180685403460071901607410703c5480d01c508030a81e04a0141d1805284940c030300990440014101540e8452240d404016000c903000540a584070141e900d011b10705003500200320714015901c80c5820801400307801c2d0701030301c1507840d155410744500c52440344001c0082c441c0d4000125145d154610803050300c0c0007400c140300500016100b40c5405c1d02c01d06040d0b05014004400202c1c0f4015248100100095409a400085000882a107980300d8940208004070054520907000a416120206100061b0801900825400d8181e41708490403d880440c0440e107840160085180400a942d0090600c0e034460217101502d070900006c42d41e80150090495a10704821362084203250001d403000d009500d0f040c0a404040114100094214100900456080030003403180c2400c0c04000600e41b0210f40b200d803400b0344040301c500d5400e5103402d200e0070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 504872365 1250 504871115 504871123
    0x62809060303020c100221130506040314070509090a021309021503040303110403020f060d0902190911030c250204020a050315030f0c0f04060306020c0a030f030c020d0c23 75
    0x205240c8180403003001c80501074800108034000c40c0300e1402e80c041c0f0f0340c59014a200c450b482300440c1c820030040964045880e40703e131401840113504c121050207034460a158024100380030340c2c0017584a0000c881c1480959900001c840c0309154044403603210045c40505610000c290481009402c99403001040703005c000da00c0060351041d40a40c03018840181740c0000090b040c801c0c1d010084d03001d01c41c1000d07a40141000070103001c00814031280050044400e40000300d00d281c8121424241d9008802c0038022001203000b5540310011443c43c040c1035007030400041116004107032115219486034042c0c00c030b0030704070319072614042a0040e0046648400401d0010016401158410300d50032100b625807400b17040000e0001010039070b41e009030102002c0c84d0100211540c01210700c030390040c1c0b0b99101001140451005150803440c4100030f284400c2c1d03030b10300074041c0383c80c03c02107206152401020303d5845d500401e08000001103454106519540b0703141c01060b4140100c0d01c80b4003410802d50012000500203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 504873615 1250 504872365 504872383
    0x50c0a0c030f050d0306030c06081905091b0d08030a0b01140a0c0c062303060d02150301080d1706060912010f0506130c0207050d030c0510090201090e06280906030302 73
    0x103400d0b00c4e1403000821007503058801921005060103844881000050710421889030000301081074110100d20440140b001d54500f91480701203134008810000541c10440085280c1c444160383c54451440d44d512414105d010040c03000200d03986031a01c80b44d880c0c2c801d0130200101d1101c0840140c503180c81ca2001000c010f15030f8070403a00b1954800010800900600e015101c80d440003c01d00050b451242d040030107608080e004503040300a110198005a60707803918040050400d40103075450390305d04151a031400c0408482582404110b5030005210000c00c0100c5900c540c01355802c5070742d00d441c5404508801c880c02851041b6520700050075400302041e420035401104100c408050362122000000e0403070380b1404c4004007603405400e0421035410300e0380075118102e029050035031350400c03c4d4456a080171708000d40032062541d565169801c568002c1e101c000944040c2d00111414038058000c0765500c0115001903a0280303165600d444400080011100a001c200e0341c14403129075607181c0603607101c50711 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 504874865 1250 504873615 504873623
    0x2090d0c1a040e072717061b12150405011e0905062808010509030d11091e040e0d02030a26130f050d1d040e0607050c0a0c030f 56
    0x10494000554505800352802c0d1460014050b40d1030b2a130000550305441544e441c0201c0c0509502c02000c0307040d482418200808800359010146140c5054050801e200203218180c1d002c922401003842500c00410340d000032580140e80a542d03210388880c1020112040b128a40c45420000089a40e900c031829805001180f1200307807946503200c0e00311005480c4112603003904031045e03d881a00c203481400a01c42029030b143c4c80814610344441a00d130079100211082c400f02e0f400011403140c0074480b44a1004110503082c00d590412270550005031450900f004000400900d0040d00c0c4929900c5900500c8034030f0003142152413040741c450f0065102d4020f0000303100880c4545a10f01d400d04030710400c041d125007848108810b00d80c1e17500c01c80400c02c4480e80e0155a000f1480005a00050040003501d21446058441c4441c61009174041c0d4400580c500586000303509201d001c40c84580001451500f0880e28102203859007144140a031034a80040400f800b441e4484900106001581594000c1103020b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 504876115 1250 504874865 504874889
    0x100204120b1308030a0c17091c0206010302010906141306020607020c06070203100203281d0f06150103020f040906090e030a02060105131442040f02090d0c 68
    0x1d4550b03650020690490141c200b8a00700005000c5800c0e503800300500c8031181c00e00c901101109010001520421103038103100380d0005010a4005420080b090f0340d20a40c1d10041c1480d41c15940020a1444584a00c03020300c520220301449517203070361041c4c0300c0030014100b1011095030740d8070000b951040143e5100000d030051310712040d0b4905001040701c84950300070340100714405d0b6118611000350300040c03405502c0d04800c1218507182003184905c00c1c0c400400e40c0e02265240f04242c071103d02140f00c2c20414120750240d100c0941c800d4000c14150f500c0300021401841c991001801030b03000c0e00c15202d03541040a80050041095501ca5001c0d0003510001e40d03040080e1400c0c60a00c5580c0c0c8035035400c120150f4400c100400031440c00c412203103000350028001081c0e0803018045608114000d841e07100300b212100c40e142c0d40206500383c2d400689690b900021300c400c040c10000020568400c1480350060307031540e680d45402c40203601103880d0b05001601021440f425801c3c2100714059a024203c0e03603443c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 504877365 1250 504876115 504876121
    0xd0305060a1412030405090f01030201020c090910050402130e01020c0111040303051206013b030c1005070501140c1c1a09150301060621110406050309100204120b 71
    0x209424200300b6126001d802c011141242c40c10041c003494031500301c03ca5840100700100e00c5884c2d443da10ba004406155401002e0350440c8000780c01d000360600360318000c4403441c0410261500000740170444074000840010701d0f40300d5001180004801c1184100344509001c05030b50103100560081c958450440020401c40b00c2d1050103407080d00c520322029000030360500c804898a500406039a030002c105042240040d40d6520300913030810464403072a10400200340302c1c96a500180d200700000441c045001d00307031403808480010220f1028015a0b000c100e8042250303803c002095000d14000d01c0750701481c035103030b00d09400034441030760004c40001004903040f101c01080c0201400380500b01c401680480d9400f1089405000b1140c100400c004954211041c04c00c002c2d440c2031003140d003c1c040340c0d0f80d24101d0381d048100410340b01501500c100c600610b080b00111640440c10180e5060310074902d0082e0b502d0b100d00c1441c5d40351030450082851003610004002608112500f5610324403481400c559200380e07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 504878615 1250 504877365 504877369
    0x306020f040320061b030c070306091101080603030f0d110c010501030507091415010315032a030507270608060601080702030a0206071b0609060e0631140a050d030506 73
    0x81c02ca120510b4210009201c1805e9107850301481401403100ba6080380e04001a41c5800d601c0d0190702d5006072035060f41e601107041400014010744015003402c1c246045c0c541410700109507240728003c00c00b108c1c0803020440d00b900b00010341080700c140d82d040c0041a01c03000d84100042c000e04c0e082c8000c072168401ea01000490400c94012440f040f030501181155a90b507044845440e80115200c4504040d510f8000d00045a051048c0402a5029a03100711140307007680100d1030b03000d5090100941d01c0d24030350400c10026a0000703120040d1100707240d020343c40800c90181c620182990423a80314a90341498000b04502c0c90004030b151113184240d8501541e600c0c1d81c8800c1c0d0f03c900c620301051300103230410000186138502411010030798064000707501c03650341101c1c3c03102d03412903511940840380707141c40380c07000081c03800d00708861a0045240c8402a28a0010790507000a0010030078540b082d9030101010b02c828009542030704009180351000b910001b2580349022034807401c1c147c0054010074030f0140400e20318 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 504879865 1250 504878615 504878663
    0x608070809030919050904060c0e060f0316030b100309210f0809280c0b0a020a15060302091f151211040801021b010509010c09050f0a0306020f0403 65
    0x2610849010b14a0a01c5000034440c036010407071292a0500791090001826840d01c8862900c2903018000000d912a80210000e20082081c54070302c1c4100b9040c4103034455201c0c0c800469800c010428001741c40ba4188907002e0300a050381a4209a114172040040060103405070022100c003403003884010540b90420034951800380d11520102c0001c0c00680d0700c0b9000900405c10560401c0d13001c000c980301a488035903004660050f2210443c05052022034403003c1080d0300d0b0319403000d00070114241d828582c1404e0300075a221000d240151104402065221440c80c403a03000501a507009461030115240400c040c0303082d880c0810300040756483c1d043d800200d000c0030504410551030130741d8075a1980c0b400c010610003d041100c28100c00703940c08020005501400b44000d12440c5180b058000503c621510b035242110401001e0040c0381e4140034840c00200d034000c0c1100180ca10480d0b42060100310803010980d000c0c11900024117161000800d111103c8000001c1c008a0780300740320311403004401d03849002c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 504881115 1250 504879865 504879871
    0xb0f121b0411030105060702010e0a0602010c021606020c0d0f0209100e060f0604050103020904061205060f16080705250309150201061a1b03030a0614010e1003050c0f120106080708 79
    0xba4000c244010300081c5070080090207951b005140c1000c800c618035000501c141c2080e4010000340c2c1d550f00083c028503806004042028126100b004103042c07600c640a510303039604000e0280304a601c401c0a100300030101c0e40e401c44443d005000300c1d01c03c1ca000132a0f01c0707000d0a80d0042011520410340040d010b858481d41b41420074001a00e16170620b40380070015806500004101607002e80c50345130100f04403400e400041c808034020801041141041840ca201501c0082c0400e03806070311100100484641003407601c0d030492075500d03003070303684100d009020440003589403401900c6400001d403542c02d242c3d01c080408180c40d0349101c0b282041382451000e0b03088030914840c204040040385a01448170b42e040c409800c1045100300080d20946a0344815400c0d82c0c41162450b800c160307503500c02d02054043d15110303d00c031007082c00c100c54044940030004040200b0351140c00c0400d51540e0010300044560816104102400384150791601c65103030550300d0090f000d0003802e0000394070f82d00040d4814850001e00d40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 504882365 1250 504881115 504881141
    0xf0b09010906080711010504060209090f10030f0303021210050a0603021215040603050a1b1725050d060209120304030c03060903090509040f0209280b0f121b04 70
    0x51828036240b8165000480100784c1000d010440c803500920240c00c1c05001d11a038801c1038016135403940e61080000004024041c0c00b4050342600402200203c610007040580707410500b6940c40b41ea65241c11000b91180f50b0310410003610f810281720608070610700c6d07002501c404940b5030401c50780360041142203004078038401c160104090041441b010498045044490010784013095494582d15020302d80080d00804490307043c220f0b40408011744140c0c01c040f01900e400340d24101c025050780441c075640c050039800d01410f00d402c0313403094504461001c034a1009100c0500004070b1060141810f0000390842450307680101108c07240024160800b101300c0e025030340d0101041c40e0003810360b100d48005000c2c3c2c000407002c2c46008100814159148041544102c3c4103a1581d640c2e40c00500c1030003085540605425241c2e0464900c80d40c046d99001c490f400f8007588000300084464034100011103292404140c0c81c1c00c518800d0100c18203000124030882e800b585209030316190641c0009000c04c903090b84003204 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 504883615 1250 504882365 504882377
    0x30d08100501030b061308060a060905040201080c09010201060e01080c18070203070807060605060403060e0f060415020a0e100906021b03150c070b1f081902041515090f0b0901 77
    0x80326540c025886080071380f00c098105400c005c050002d404101019800400c0c1a0344204104481c0c1241406440090040c83e82c00f07101e14181980080e02000002e4541e403014500480c1d504074591003580004018250340c694a200380d40e440d0841915064a60040360184c2c004460010400501c0c000b064051803090b0b0041d8a00300782a15164280d800c42542200e00b940c0b90100000c00b655160064009580103050000d00c10034503102182c40c0420100d10012250014402c00022034540b02c030407140c40d82d81e10405640d5490b07008040750b02d04000303070400c1d130f002c403e2140420300980e0082d114420707940b841d000c4441400540ba03191000310603850240c0d0741036002c810111885e04d100c0b2941c5030090282c80d07416051071090742c0d511106940460f00c1001d103810189119264507105d000501c01004108081d0000550703407540345218000307158002c0d008507211802d01e0801c521b6110901c1c020030302c080095002025118000f05021541c0c0300303500742030700000350216245858404503040719005031114 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 504884865 1250 504883615 504883619
    0x120415080603061803130e251205130c0e06041401030f030507380718050409170a030b011404050904380f01060c0206030a0f18060902030d0810 63
    0x112203078413524034040010380400d05c5000c501400154554010742040154044580380008841e201c0604640107c000c00001c0c601d44d0100c0303a000075444400004500c1c1c085030700d54901c040203650141500000b4000c80d4403010000f01072010300b5000d800b03802c0441c0c003403102005160164088007401e0002505080010320000b000a010348001c1181900c20011450000c01c400010f41000003000070107400403400f00d041d1281c80c2d0808030f0b509c1d400341003800c0c001c02c00442d00c184c100c2c00c1e21031402400c0c05540d44690403024040d0a4241c40380c00c403d012070741c0390b0341d004444000300600607150342c0350301090542c0c625001c0e003a0381341c040e02c00713681c0c0241c003070b6516680d103840d10401c003181140794540111010300802410552070102c0c80b000d9641d004400a0b504115a0700000320342c05034407500810801c6a040d00c0186d44183c12a6003051001c070340410b49140d42c0181c00d000380151a800c0048085d01d1403010100700075074009090a40c0220191041122100c905441d22041110110381c050154402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 504886115 1250 504884865 504884881
    0xc0e010303091202030a0b190608030c1905010902280e010e0a241e081c081b0412020102011808090d2103020301050901090b010c020105031812041508060306 69
    0xc0d0f040300754001030854052001644a1080700315042da00b10010903000b6102d038800c1e000c00d00445000302040002103241120700c505203501c0e581c500b5007000c103003004460200c050040c25085104610740007000052a400310f21403030040d0494141002d0b01500200390002817940c80515198101d5420f190240c142d0340c2d41221074401000d6180444207030640d800700c565043c254a400300c40160005080240e0010840c03022640300d5241035201095982c4091843c4021615900d1000020013031414000c14940b100d0580320b0300341e003080c41900c1d4a02d09c0032500040c90706d4401140590039000303070020440c414045d00110441010700e07a000c0c140c01c10401c420303c200d080c100c182c2c0446c0c034080da445520746036102603401d0700c0c211402c0c440e5000a801000500c030a142a1079014014031084030100002c0001d44000f07000300c0000500a414040044002010070312100010302c100700044080d84c9140b005101e01207004e070802d0103088401040245c02d201003e00400506001d0803000380202401c4c2e4034014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 504887365 1250 504886115 504886139
    0x20604020603091608030c190519080f0a0203310311030a05010e060411060412080904110705010c03150506030c03070203090303070309150302040b0a0c0c210c0e01030309 75
    0x100025081c424040184c540b8941151a100078102e118095076a4200e2100114a00410308040703101488020386402c4c006400043c4043c0f20b03428410300340f04460745030304041c00e45014079403224514034400907044d0f1100341e0100c001c01c8940300b6100b0030000142c2003002042c840b039141040540300c142c003190a20205064011078840840d0050448902402668a103030a4541c465010041e95000e6418030040012111300218200d800359451400c013407803c00844002480010b000c4c104002c00a200301240d120b90700006080304052152981d51840c9103403050007030407460b03c1c56001a00c0c11141401482a4480035000c0700d40040985066807902d00a803101944098003603000c1d4031040040340b520b82ca0078000341250714001e44501094138608803070f4900c10010140301c10101441084288030419060007a01d02d000740a1a000e04001d141b49402d00c00d044054100e01c1c07408040800000751003881000500c06148110400078200b0f69581d011b040443c020300000307011581e040700030701401e003181e2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 504888615 1250 504887365 504887371
    0x807030c1b02041b03140708070c06020c0115030b0f100b040e0a02090a030f0b060402030c032e230604060503010506031510030b1e0a05010f180603020c100507020604020603 76
    0x1040082d901d8241e80780005242c0904c412000460344404d46440b00c00301c0d20503101d40c000c1003810030912525081c28020314680d0010802003a0541c04a058074490009505c0f0048800d544c0d1000d080076a2642417800d1440c0c1c0446149424501c0000050340b411201980b8204842c07034110b040e4102401c1c0303071107401d80c0c03840140b2080f0013960034000c603da140d40d400c85640c0118000c0c1c440d0b48084c001d80c10400c220307020060006010354010814014220441d01c1103a61090b1f80e0740b0036903009074404040c0810740c0302814a0a481c041442004038108a42001543d94200300101001903000d00078140720407402a88181fa012620500042003c0c0c02d054008546c820590090210000e032240002402c501c3d11500180000e0740c0e960080b03016003440700e0b070380079218250207900c0b142140380000115145454004c540c10018880030b004600c60150703d00c80703101b58680350755980190711860010029002881c1e0386040d4401e00d4200503580c01244182800323595030f540a00f00590300e9400b4005194409 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 504889865 1250 504888615 504888619
    0x141c03210b03120a122d0209041e0e0c030721050d02070906051f031d06133003020307050c0307050703030809010b0d0b1806010f03030807030c1b02 65
    0x2101980307200e55007030003000c49045040c1d81c455280d882a003001800100640c1d40b00c211649000c035101c1d4140e5104880c00c80034030754000d44030b82001c07842c40101c019020300d4101541003411300c0000f12000300582c2d42c01d65210580c4104000303d01d039a226040d80c801d449041c01d60180c20040b4140b080341048528003080209404008400c2012561001c2c603126883c50f0940041c2c020320803e0280c4000b070300600d00100303400c9607100c0910171041039125060505290303a1013403540e15420a0301c202001040c9504a00b220000e907840c502e0b100c00c500d0054480000c0886100784000441c500507480c0e10042d004014245400c401c01d080e4092041d0003d510240211045c410305214007401d219081000b0000e0740d100341c01808a0324650301e4094030b041400750421368030b03034100328001199441c0d04808507956500700d5500b61058031010100ca05140d00c04211422034014600040f840a001c042c030a01124440d542d01c07501955544402c404450400c4840400201d103059540240c02d88040c05001c4030f400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 504891115 1250 504889865 504889871
    0x16021c0224071235060f0105180102010f1d0d0503100303030506030c0d060e060903090d0305070c050603040807050c010f09030b040c0b1920151e01141c0321 69
    0x15001000c1c41e8030b03010010049502c0d88003034001005101c401a900c0d040b0340c00b9030303002c0041c0c01b0220004e0080e005100070540d482030342400b5160030740e02c00d401400e441d030358503001003107914034070400001c001d003155092040510400d40c800302e0140c0f15008a81c828849c003a907214006d42182d03021009010054610390345172240d50a10121507a40720745002507240304103400130356145501e0701c0350b0034080c0041221405400c01d02405440f62112428003030520750600d84a030b510445031038401807041130703604541c1d0480808420003040114000041888078020003c650181c18880011030b80c20420f0754030040002c01084040000500b14061a42c10520511050b91843d840e12031f20b4401d0f0700072255080410110318400040300f030300b01c20b544071040841080909c20030380820f2032603540c0580009281342c420505002070b60a624100c112200000d015105048a5a5a030b800507245404283d41714070501c0000c003401003101c03030a51803681e800d6154540d07407140300100801c40b03490b1441f52402030700030751 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 504892365 1250 504891115 504891137
    0xc020909030d02120718060f1823012d0e041e0510050a0b0f030903070f050106050a090504050d051c0509030d1d0307060216021c02240712 61
    0x42d0700103000c6602000c10f030001c25160182d0000d242403100400341021005003e000e100a50380006103644c90281410117210492030910455150406680504409000401900c401b8008c10b168001424026a80c02030300a04030b0b410003540550101c221140417100d20201024039008203600700c0b900400800c002501c0d2a04a0711000c039a02603803041203119900c1c010840102400e0041c2c02c098030b000d0340d85043d42814940808020322481c0541c000e65040440042d042400800032107464a03444020305410b0040da1800e58040d0049005040c4502c0c2c001c000412451080c0c410b030751040c0d80150044c01d03113000020b02070701d0645c89504103480e001c0c0c600c00c00240080441c041c07107009440d050010b40d0f4441c021b5160078201c82c800590900c0d11042114401c070000070000c1601e0f15a5017125005030386100c42c07002a801c802c1081c2000f50401ea680b10707041030005021105450703d0b4002d4a424a400456500b24204140c0f0b0681003d0b4115061001c803020480200607150b002e000c03420b00d40d044107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 504893615 1250 504892365 504892387
    0x2714070f080d0c1a15030106090c0804060e240709050f03030304020f01050910170703140115120c120e06091002071e1b1505040905040c05091602010e0c010c02090903 73
    0x600841c0c10a00b4040c0f0240e05814501b02489644018031a4580c200007065070782c100288038040241014003aa070321903a0500c0340f50380a01081c28404622001c80750203500008820400c000c08541c1100494100c420009250030b00008001220303400501440c6503a0f90390b0b08009011885244007410002c00b403010810545030b034a0f4103450000140c4444824070301c0906048480180102024100750400d0304c03840f11440940b0403a41580c1041c1300340311300b50303201020841b9948000040c0c030075030310704050071004025041140d1440d810041301003446000c00c03482c0b01d141c2c1c0750001d45d640391041c0d0000ca02c20550200035405055124400c01c4081055829503034114804040f0a03c02c0c1c6001c2d4a1148a81161800001440003410500c007000c006070141d06018103a030095100c2c43c00300903150030000e01000100125000a450010700c003907450304224035001c601074031814500707000d5807030701031801c400000010302e1110600b0143c2d58484186d84503801d0195562001c0e04c084040d210a100a010320 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 504894865 1250 504893615 504893663
    0xa12080a0f0e070305061b03010e0c0c0a0c06080f011401030207080c07030b100906080a060228020304090c030203060d030c021504140a0504051302042714070f080d0c 73
    0x142d200d600100001420b41c1061030031301e90f000c1d01003054030140184508603040010292070440e220200804443d030f40b90040c0080c140303d18841c901da44d00407108401d0800404141031010f032405903a84034003c1d076070306035840280c040078042e20704c14902e03510f20500709621a030018460548500206802c2c424000c900c03501d000f049400850311502030104000c40e00e03540d10350141c010b040e6904240406480c03d4041526021000005800300ea0001200c0d210304410098a5141c0340081052004400318488000d440c0e03042400b0390810f860414140c80b0016105c0c0c002d59004000040a210100e0815a020760303075245100800ca8010b0407000e00081c4000301d04000e04021300f0018044055036503404208541c4c4003d54001d14490784c80d040910000b00c21414035072481e03035415600000c2c103458140b034681e805041e03070b103607840e804041c58086420400c45000300c0c0101010ba81c00c41d5501c54403410a807100c00c3c0240180082544000c2d00a0f50040c41400140901c5005038401c2904c0d04841800100d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 504896115 1250 504894865 504894881
    0xe03090a08010c020c01050711010c1a130215090a0b070614090106050316030506040213020c0304120b0604091a1009020a0507031101060f0b0c0316031205090a12080a0f 74
    0x41c50b55240c0f034030115207405200c1401c1c2041c2c2480c00d649413101c0f0341e41d6500340d042c80502450401c04031002c1001004040b6000d4012003800c411581010724146a89a40300111208101e000f00b03035602c0c80301c5845110700180c0e044400014401054141000c060280b160070101c0259a21900c9104018007405241c08150040440500101d4072070f01f800185460039803548010807040d035440504102194002c00c20503009507040310703100c11110020840e0000781c061400d01c05410300000500140c400c0004100d10481803140c0031a407070581d00ca00c2000111240000c01415070000c2020b411007501340e418032164000c080111005000391207440c0d20080742c0100b02d0820204200203041801d241e00100c1116800f84104002e101c01c60070002c80000002e1325111311105420040303500e03100804240152081708602c2410b0003202c800d6810028070440e0344401d001c0301d041c07403c00480c082100100c0c60b850700c26040481c08121a28072002111040c0000701100d0207103070303207050030508890b0b94001c00b10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 504897365 1250 504896115 504896129
    0x15031e0b01080607020f120d2f040e0a0203090a080a09120f140c0f04020d0b060d0501032f120f0f0d0905090610110703140706080619090e03090a 64
    0x48246014a8080e25280c02c2d0746e03071100e5652001c400d1628103240041110b1207100740c00b90128858401065403140841c03042d41390603402500d0310042e00310741076400250080341c654801602503910fa038091fa000b2480705031243d00c5950014255940851b48680080c000f0202500d000121507a840905c9040d0440c40c1c2000c80ea0305460f80151014441140c540300c4040d040c0c8400342c42d0103d203690000f02c0041042000d00d014a4020605019594081d400150703c910080d21381a5640d02e061600001440240030854005800e40c1c5808403c168810f42d540c80700109100a03114080301404001001c000780300c0600042c070071030b001c0c10451350b000c1c022264030812020060480c202c8590005d01190070f0f0350441d5018222300d00412456540f04051001001ca440c140451043c203030307143c014180307130458101501c00f509481c1c4140000000041d074004450995459a180f07848030801c01440c0300001c1c4c002c9034400b84503001801000216032107001c43c1ca80c0c04049078600505200400d0460030544e100301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 504898615 1250 504897365 504897373
    0x620010f0f0506120a0b0621100e0304140405281401090b06070b040822090f020301290c10060801140f04120e06040306050406060915031e0b0108 64
    0x7212958042c002d40e074101204450201c628000804056540c510800340503042128440200b8019110320541409a0382c0c0c940b604440188081a070f2607803404035038500b4000900d003901c415a81a00841a04c041e41c0c10310340c4090016546a04000240101030480000d02c001100c4a82e21030b161011035540f8080712180200c0c02c6d02d442c2c0c010301c154420581c0440c81003400d10500101640e1604c1c1220f241560010064140e92141c2c10034228a019400c41003156141101c914a01d038809c50016a04441008000f482040c0580c0214001d0380802c4c8039503840e551414124a91754078900901e5a00b41203840b020380d0803c079030225110320302540b01c10314100084e43d5100c18440d10200b070040880d040100b501c00112030034000001c032000c00c00180050300400700b150b1b0f190319242c450240c001d0b900d50000c01c15500c1e03680301d0a10000402042d1001c0f41c113a0b140031000120040c042c00b58011074042014144035a5146459220312000c0e401040c0b4440e5480031000000150700741c00c514007901e0400018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 504899865 1250 504898615 504898631
    0x330010807142d0a080c060a0c0c0e0103030206191b030209031203070504090506120a03080901151d0711070b070203030909090f06090a11010e010c0f030206070e0d0503040620010f 79
    0x101103400d8481d017151780681c00444000c142501c80c4030403a41c440b0803034a0428040300050801c00741400c030079003191000c41a136100000074182c2c00075a00b0f02404802400340101d0b02c0c00c500f104115907114a014400700c2d000045111024026406050030700c202a055403e039000800b00c80101341d0003119204080350001c503041c08900c15510505a00075003d4442d144030903811500f00307035200481c2c2802020411504002a0307850000c1d002041c02c10b4180c03802c0d0445603240c00d000322041c00780030407404d0003d50032800110058031580381019007003401000f0f044424104950700300c0c00c2d030140c18166010301c801c0002c440a5112800f200d03208021001c00747c42c4194851142900b86240544054416440f43e03a070200032825500400444010908080e1840004600144c40d040410280a445155001e04000a00d5000701d2110301c07039115584c80181102120303041085410704044050202d5000740003d10505e03000d600206000d00c0c2d0382003051003000c0c0144006081d661030101070440c00b9114040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 504901115 1250 504899865 504899869
    0x1407020d09050103110d150314100c03050402090105040f0b03030c030403030e240a03090f0501050708011d041202070b0f1306090b07030804140330010807142d 70
    0xc10300c060102464217218800c0034416507111030245040744566180e81e55540b076001c26089101c40c0045601c03140c1003207014a40002141c45803210300d0102c4075503052000c0e9009051091040310310840e8018402043c0d6420300040c000101407000405000c0782e40d80e0680d251030713902000030b0620003417000003e560304e5086160042001c407440482034000c201e4403000001c94460710307034000850f440110603182ca500c15042d04038068524030f440604445a6421358809028041d0801407207413030036440f042440e0341d980b22002d001e0290b003812451a0352880300468005940f51400c40b0560140d4812554401c2c0c0340d01c100290341d030103100014440a00010204412032071815000002c0842d41060f41c0207624100c1ea40801e403140c000014100071040c03001030f0400c4202c400101c10700c409a01207a888a0500700708100042c0390700b4141d803102d004000c2014558490602580c1620400c60140c2552441c12a030220100451034089910404141d0302c105202050003c0400410245140100a00d14041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 504902365 1250 504901115 504901127
    0x109060b040807170a20040b013006031704030605010504020906090f0409140705030c04150509130f08121005010503010623031008100902010905131407020d 69
    0x220140d0301100500c801c102881000c030f004400c50741541007190100c10020300d0141070884d003070001451182d800030344900010400c030b01100103840580c0c1c104500e4244500648001c0c41c000c580802c884105140222940c843c0058190200d61111001c84c08588a5035401c1404807860035202610801040030802d10034240030701d0b401024291021807402c0b01c0c14011901078840c40700c965008100702000c0403050f840f140e0118207200d41003858081d6a2004d90b40c000c0d1103100f5072049510a204205c4407444130b28241c41038410707040c0c0708800001d0051510042c00600032006240004041050450001080611100246d0f841c4544400e5039030f079201d80154001528041d1070742a11b124680424031413643c108041b82d0640d080750400001c08501c0f5400c4680d85043c4207000e2201d11004800e20410500d00d290740d0064500c0380040e14049030301030318804100c55a00c80041e00040d2046020030203800e01d80c024000d000511350300441c2c400040d208250f0015801d980800040c1d01c0320b81c0900321a50b00c86 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 504903615 1250 504902365 504902369
    0x51302031009090209011715150307061b06111204030305010e010e090703080d0908070803011a210601050c0a050c030c10021023010f1410051602010203040518010906 73
    0x16800c00400f011a00801c041c00d4050042210f1658125103101441c0f4040005283c0c06200600c40d0340c030b034540710070001d5014200301a10342c040d00c24814081540e9001e0204189402900400c0384050f030415100d400103008404801d404d140000c0201e0718030620b108400d0b51082e40251404100c0b54034102040c480030074141d1102403180801c405025603460007144160450303801000540e00c54144028000c028413603034400500d00140013444100304211040658100d90120389100641d418000b00c2042500c00d80a02c1c1c60031403252a17454a050740c400d9901398005406150480c00e005400103101e241040c0c3c00400da54035408004190780310314007004000d580745815120100d40c4409484041e40d20780810030b0452219031148017040d08112900c0c0109040c0c51a03024221255035030f07100e20b4940e01f9190080004100e01c601d0140c226046c40c840501192803159100c61400195607a1401d40001e40c1c1310490443c00104000a12685e40a1081c440307115240e40c0c5a1712035152112200845080c0c2d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 504904865 1250 504903615 504903629
    0x806040c051f050a0810050d1406060f1c0303021213060f110a03090f051501081b060f07020a170d03180f030f0203070611030103140109050d030e070513020310 70
    0x48150b4500099102064500300001c500700000c0e03603101d11038260804803042d0001900700c0007040400c0280302082c5038000c2444030401c107464807038030758000303100c0703403800031404a5088641807010203007842c010b2411522242c02442c0050800c11003003188c0d05010001c0d608581d21014010a5605222140c440c02d583e07407140401c07c0203003c800c01515030311406040c1c0c626003495920384401c003e01c034032980c2140746943d002061721480c0713208000b000c05110080c0070b002d0381c07403285071300c11200700f40510745100b810140202494188410307009011025807003424102c0c1c01007510b42c0c00090a26000801e485040b0f104c1000d0030201400c0e1034014112100a40342032210b125802c00040400c113150705008840790075262415811900c4002a03144d803081e0180104050b140012451032020104051070590f4410714050a005901360041c5080c0c0c1c503e90740240c032b07581011029071042d901039440404030310b403004149c4010326980e000107801d2903141010403d030a41c0000030001070100c4180600d01610039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 504906115 1250 504904865 504904909
    0x1050f0f06060a0309120519210513150b151206040e0307120c0b01080a170c0a061107030e090c07060b01050c0d0c0b07050a080c0708040806040c05 65
    0x44440310301244090300c20742c05000700285400c0c4580c441c0d00300c0031403141c21101c0c42101c42d4040308001c055038050001c07031071544415014030510612409490500d4181e05003020011441310102000902024091800d090a10800c6e240041d8896002e0840c04010344000208500700c20240300a001030718403c0c0300c1a4404203c0a000100c684030000d40000d0709070b07000103400702000d40701e031300d54420000080c09071001710341c0000c0c069600c4081d40600912584c41c49402ea641da041c4280d840c96903500c000d001c0700464421010a5400f8806420101c03603003000c45a444035141c07140b00c129020b1280a080900c00005e204040c1a0025888207450400352891442807074240d6814401e4050038a0043c01161a01c0368000a68800c07004e4903e80702c3c400082e0f030107000ea6940d010f850911054030482c1d5441500002030720b4a8051410780e01021102d40f1801883d40d02c0d4a1440040e03400300300d046480301d0b014000452681c03420402d5501c41c2d8031481d00c0265031410070007008503c07041402c800101182c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 504907365 1250 504906115 504906121
    0x5060d05031b010605130203150909030a08040c0f03060e0f0309100f200604020f09071403130516081504020a0603050907231e150307020f011107020301050f 69
    0x800008480d4240e050a200c01004900641c11070f0250685a100070b92107000403108140305050303a401503001d4103850200824044098003032050081c0100c1f500ca11541040c4141c240c210b0180c0b800c26407080c8140706007070050b030320b40090050600d0590070580e1090f56490044180310420021200080d007598011030501d040744000400c2d20b40c00035460700411142c0012607810600403100340722065140c10b8000b0382170700bd11070309680e070780700446080e440b0b0001c90412940c941084c0300300f1400b078015035440110000700f0148001c240e50010703000d00c8403054040c282c8800b00c0c2c0140700f81c0b14041c0d207109814088601c0c1c0300c01c0320728080c000b01c0076061040600051000607aa415030301c404580042c1400b04140e91203031262401c1c44020b6200b14050f0f0841d48140d400d0f41c902444075104805e045400645078103002d4860310040c40c60040b9640c207d250103541c2c1e03905540a001866000d20148101c64000e590382120f5030a407200f80001c0118110041008021458203024003540100c014a078162146 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 504908615 1250 504907365 504907373
    0x91a031b060a050d090203070e160c1e02030c10081602060118050a0207050708010b2404092f1218120a03090503041d130b0703020a170901050a05060d 66
    0x110a4402d502c040c84000114100c00180303540141c00340540050507201500da4800c101420072004913081c200c4843c5541c2c402080500a60703000c6406904440c84100540b645e200c031748841c41800000766414031a1925102c0203540703c50a1140050380360b91075040b24104418068865280104140c0949d0085001400307014080c1044200f444c2e11141c01250035114074800c1c03c020b200310040501140504030b0042034000054101402100b41600e18590000c2940c51101c2c000d0050701c030340c0007103480c100010005040307243c2021004030344a0002c071104c070700f4171841600c40d8114040ba80c2818100442e5551a9105607401ca13680401d80802850300d4000e450f65123070302c82403280740d4941410301c04585001c1c198800e910520351507500400322543d03645c40e0440704650041d01c41450005642100004421000704038550450035440584440785494128040d000307908900613000411041c5081c200d1080c043c0c070a40c500071400400002120308144008a0680320001d01d517500550094814030009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 504909865 1250 504908615 504908617
    0x9030c09070c24090b060108010803040e0f04080c0a03111002120412180b0c16050d150f0f0c08150d081c05010602031c27020109091a031b06 62
    0x81c1d83c2c00f54660010f450b003c1034000c0c5599103081e49030400d0380760100410800070301e070710424040d64090b01c2e03082590781d0745d8481e03075640c2c4600d014a8907005451004286070a1200b211541c1061141152504000700807807a140b40c100c40d030000341c2c00200103e01d0070360101014400c40c82000752000e0700b0747c41c14100c603940c41c85191020340003d00040c02014440310480c130038640f1250303071445d4075403407400259076011441007a081075010703821600a00c040001ca042101c3d01d0701c41160b101801c140b100302d80d1611030b0164203024010f05110940ca504d041c400078000fa01c9504100f403c0b8440c00224468001070040601c10010705100880000502c09140ca42e540c54203541c445601c29409941d5403c1c0b078558400d0000b88900409902d820440049811030300031000d00103c0500008104100488201c44801d4840e88004040c841c8180440031008400544c2d4400b00f090040c1091100159590600d004075261281038180c00c40e804459140b4030700e02441400311048400c044c981c0101010780000d449 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 504911115 1250 504909865 504909887
    0x501050d08030606090d02042d020a200102072f0306090309040f06080111040303020f120304030c08070f030e031e06161710060311031005040e0106120809030c0907 72
    0x4070324004980b0342015a50f86c403041d2000340d8003400c240141042807050003594207242e900004a0314103d903241c001280301e0f2094500742c0740155107106405010301d2940c844101c4a0341040015502000624003041158540d000c04c036007000300154a44040c0c100c2d1080501c0c042505034440c0c0c201c1010310218443c004155185071000b180c002038045440101b0500400060340041115402c1c240d003507008224050241040f64025000d03200e440c80f91503840303034688000d41101c04284c1414401300300401c0c4aa40000b0940d4441e0306c115240154070780311103000c02003a203001c90010b41c0b41c82502c14281020b12000c11601ca5035900624100c5800d0306c010f44558004003503400c110f154040404485124180c1c3c0c07800188052030503a074a041c070002410300c00200e030007010007190070812602c07951a404402c0745d2007584481f140b8840b9500f424100405003442d0300d014441c1c0d649038440071a034144003c590007007803441040a20341d0b500c9068245820551903c8946105511040805c808150081d034071b040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 504912365 1250 504911115 504911119
    0x70905040b0907030f060807030c0312052b0603050f010606020d0f020601030b3c0105010c050319030b0604170106080a0b340e01030b0f061b25090501050d080306 71
    0x907a1700d88482105c00621003503120f072031584150140082030201d4072004405072402601090b8008020032010744480c4556032903c8400450740155142c803001e00c001c0f01e00303003001507000881d050760303240c940925148014442d42a1655540020040f154041150b101107035241e0a00c00b582c200070b164041c0d1205814800a0a240303518000075483c2d0000322101c512810350300fa6601401801401003018000c8445c5000040d40c0d40000042415801400707001c4800da8840e000754540705c03445100e101d212642000070010316031203044049859444d000640040d104850810f04200690f99200c0d0940380380740d0050405400c1203001c040802c5440380d09551048101a00a116010f049680b03034540c44103c4d1801046d51510300341606583e44001c00342d41c0c902003643e0030704c038120703c480070081d205484109040d400030080044803528001208401084801d020580750700344010031084a00c042c440601c1320b250307680c1c0c3e5000d1104000c5d510841e405044141d8003c0240102655a00e89501c00545924 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 504913615 1250 504912365 504912371
    0xe0409080d0603080406090e040210110a02041a0406090506100507050309060a0302030f0622090c030c06031e02070206070303020c1e0106090c03020f030f070504080d0503070905040b090703 83
    0x4400d020351002291010060341100b005403e941e800c08040e02c2d0400d0250000041600d0400141d41c1c03501c0302003078002c039001460318418107280041034400d8440d100180c40e0b076008090403100581d43d24811500d80a050201c0788100c0c0723a030f401c10881100d01a8020068241c078020602400d9200c0c11034030724004c0e8050410641d9003040382401da2840c0a0b54428a40c460000100c152070700703a043d0080c501502204204813859241c103410000b8024148101a140c440203880d60140140141c00030003a80380101000180d032a12a21005070540b15500008042070325080448450390f80c909408042084800007182881b085900181d190310403905c0140070190086009984500140454506002d40c210b01c45048008036079464040c040368411021010318010b80000858000c3c002c40e043d00703100d1100039180d9515504011328201c4042c103600b0400c4418440810500c2e401c200680c0520115120300d41c5070700d09070000410094a071707040a401a0308150344900c560702d48103c01604074415003004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 504914865 1250 504913615 504913631
    0x1002030711010e180109092f0402090d15020a0f11030a080c0c06040302070602070b04181d061e011401021f02220f0608040b0a020c0c2106060406060e04 67
    0x8825100c4c8011a59032032000c04000204804158882d00b0b400307100399401c001c0d070001c224034981d542114503058603000c07540d25512506850540c7c010008c200f00200310581010094682c01e0810021421a50070305a0004d0940b0072039410401001031098146090700d030b010400e204940d01d9029000b201000c1c41030840109481e204010142e41d0741400340300440d0030518060500039034610b1540711b42405809241070110340341e407012007101c0540304031261805001554010400007026120110062801011009240d803070003440b8250041d07082040f240c4004180380200c505142e030680c0000c40f40f02d9141c40440340760345c0100307420b0b030208140e40e04c07840035003610400480680b0403080b09002c40c007030b95031000c0b400d00c40e07859010090324841c03484a105981c1781c09040c0c1b1301150a0714060b0241c1c6200c0001041005150010000061204192661003000c040820070018112000c0c0d4131307003040c01d5004601d01d83c040000c6c82e4854004c48003480410300e005800f4000300071072080d140c015034450302d00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 504916115 1250 504914865 504914869
    0x2120f06150708041a0408070b0d060e091c09060f0e03031204030c0b060103020a080601080403020c060a0306080f16050603090c06041409060409023f03090a0911041211100e1002030711010e 83
    0x52001005042e02c1440cc81c544260400e840722035040d11002541e50706459404510320030340b50481a201d5648407111000e140c1001681d01c0810854803e030f0601c010040e0340b480b4100c1d02c2d001c1d400b42c1d01c030b13403600304079203c2c245081c00081000a01281c1098070501445861035403040306990400402c0c00c0240264560381000c0741048003a5100c950480400600d0303442003940340d44203404a82c031560a40301141e89113500c031500c900039945020f009a80080081c403117840c081004540155000e0104c0e014070b02c41c0703004108070360090750110132007c00482c0300c0c1e0141c3c1401c078607041d40800300b103808100742c0140348c1c0010804800200150000c207031034114164803504010300c840e00d14000043c01d001600c1c09070515692640030400f014020004228001101003060003803c0b0312200028106080c83e0818005000960454030140e950780e0102d44000913a45403107091840000b160742d9414409041841800442e6000d00c1c10401150301c10060b01e00030890017940042c400d5001d1034051428529000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 504917365 1250 504916115 504916121
    0x7030b03030903010908130f050a050402360909060403080a0f02090909240c030c030a09060e0703061503050c100c021201091502120f06150708041a0408070b0d 70
    0xc50150958a049070480a0042c0303140a805461f8034885a40a8140c45076184103a41d01c1138801d00d90041e804420511207440c10f60090082c50320b00b0440c1700d81007043e020780e00c01c43c00c0c4100c945040c42a02c0380749020f41b50078071000342503000e01034500034401420700d65002000f10f50018507808500f13036507040b44030300a44ca980440d416400002c10b129410b05040d0100d42d110550b11800014099025007250b007401c0d04c0d41d40041c4a4400115541d0856556103190300c09a8002403603c044c20ba541e02d0300070000340b694030a41d070076100888001e10b003403821481c102084a89520800c201d15440c00b10400c0060170004a031090010181e421a242c2120044251180450588001c0d40700c844401c0712042c0c01fa05501c41588035015441c41c15800440c2e100c904100d02c14625450f401010410008180382804c01303626030008009005000b004000c4501020550070002048684140c0010701b0014400c021940e03402d001031031100310746020315200d4500c2d0340c1d01c92849400e08124000c0780100e0129a658 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 504918615 1250 504917365 504917377
    0x170408190510090b16080705120901060f080105040311010216060216020603091006060e0604030f0201110f100f11071205040302060d06090c0206012105160603150902030702030307030b0303 83
    0x1841480f54401d5490001e064800407503a2034880301c0d441c0c40d0080701d01d22842e5918010651a2101072070301c1403d03000b2110a1034000d041000d10341d220103002400b8071412070210002c00c0c04000025650400c0c1c580208042a01c00fa2054144c0c010302290300c1103400882c5640d03145a010100507a100c5c00404020301c1c1c3c07004064069440725011040103c2060701180e10355050000346000c1100c030f600d07440b01b62040c110650080d40c1040c03043c8001c1c000903e08500c007603005030050511012510350b10440314078050030020220140d401038002c0701c4203c81280103000a20031401d000b07112001c084104a00703503001302400541316440c10a039003d6002e000782c00300d801540d00034140c6030ba00c00443d8401005080031f8815400410300d4412122680d62003c43e2581c1620b00c8100f4800c00c94010403040135124000300025242d600550b1308000407100c080b0392480041c8150340300811441040c2c1581d92504000343c1c00400352324010010082191b0303021003100c0d03018840c0c2c14005801310001d03010a14501070a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 504919865 1250 504918615 504918643
    0x5150a18112805070f02101106180c010806090c1b010e010603021c050606130209060c010b03060709150f0e0301091a01050a120803180a0c031704081905 67
    0x82807820302802d00c14100840c405500d0444107101c004030212000c0c40740e00005041142424178440040c0342c070324100705500d407061505034004610b0380c085a08105c01640c4030120b402c0201d01c11503814400b07119001c2c5400307007400c011500349132070030114003c1da0340201682111200000c00c0703110345960712400700035201500c0013004800b102c1500329000b001140020391082200541d4000c0c550b9001c00e4807201164890302401c3d036611407034280f000700c06130340d0400c0703000503024000001d01e0749074400a00403468410f070011070303100003480500d41000c84c060000410403034031841c00d10a001e200d01c20404403030001c2c40c2c0280d540080b020308862800f114442103a141d420000b483c0c1c180701e010ba10710700d18510101c0390034481d40d07600c400b0445480c0851080d80d03140404c079036403480483c0051002d580c1c48140c040224120300c1501d0710a03400c0c400070071400c58400401c80b40c240280320204041c2a098101c600c01540b0300303801c00d940103655405040502c140d41d402c000e444001c1050a00c13561180c0f0000f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 504921115 1250 504919865 504919867
    0x501021e01111603080c0304050c15090d0b060a1a07140c0607050d080106090609050103020702040e0706020f010f0501061b02010c20010e0607030c20090103031205150a1811 76
    0x20009440c8000c3d81c440c0003680002c1e50440881c0101c280042120b004982c8200288501091001031080000302c8145051000d8418440c02030a034445034181d0004a00c501207841007882c0140070401240c0540d00407449040040a401c40e0024000b401c41e1784d82030b0008004d00032034111810181c0742c550000b000316000000072540904100000500040c030b1740740c507120b4007810ba889a60440e0b490712148038450000e041c41104016a500a0740100f02e814006840410600c45e0030808500d801d156900450061b40034500c044180c0e0f1003031041490746125010240200c0d4541840241211407074082d060160038110040411a030180e280300b03d0741907000c4035032010000041c01116644148a83d140e011860040070180a4545030044030501c50f8140c443c0070a0035000d855000744c600314020b01c0004a0515842980b142c1d54018546009511039600d0b00d00c0715151020303000a48070040c040103100008039090b80504d5903001c0901080e600700d51380300c8070300050500f0304c1e0002d081492003180c54a40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 504922365 1250 504921115 504921127
    0x1208070209150d0f1a06030d03020a020f010903020304210203030d0507050c1c0e01020a15020a050f04090213080f0622020d12020105010b121506040305010507091a040501021e0111 79
    0x11050441c2203816004e80904580003420505c40300e08072004071041503164000ea0140640540658080d01c1060140e00c111141d041d11a200c150850788603c9040d000750f84089001c006030b00b055014102c070202d00340d0003504400c0b1141e0219949020f418a010700558441001a011030f12030416220700780d444400310f0303548502e50301182c0c0f8404081800382c0700140e6004000741140d4000140d0074441b50f0301c8203c0718041e00b07801e40847c009401008940f0100401000b40040145400b0042c00c090916868010382d40c51501c0c4903c1d07040385560380100300c690460030160381c0404000c50840d03403141c03c0081c8600d0368080c1b01e040d0403084011280095000001502e40d40500c0130703c800c01c044c079442c650002c210990f2138449409140c0104044c01c29425018000214040d44a071450a085080a400103003041d4880d62500c3c01d40741c0869604c5c2c00601100420094940c5e0b40041ca03920014942003149080e003000d0000751204008100c09034030304070094501c607000d8002d520503201000007254094a44c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 504923615 1250 504922365 504922373
    0xc0a0803151309020909030c060112080702090106080603070906060509093105060a0504120f0309150213090605010203040501030e0304090504140f060c12180607030f061208070209150d 81
    0x1180d40c00740d0151703c0400000781401e90000c1180d0b0b20050030001020f0583c6030140707003015040341640440c0d14407414010100182c90300e800f0b0f41e0184c807144d1196174103468404141458440702703900c26418613041c0003042000b550003208590201c04150303210b070641d90343d0f440101603402d00320480e103045000d003140c0780c209040d43c9229401d089118205444544e15118094002d444094601415460314407010705040c0e40160741c030b54110000d41c100454546266100c03020007440481e60920140c2c0c0004400e691080c023070781100c1c05031203240001c0111909000000b980e0380a50b0061a05140da5003100300c0f40c0303010410580300106492a401d00892500e490200903001c04c0c4000510b1030b128414004000c0c250200752284600b50541c07500341040c00000006100d000050451070ac07501000150b051520320a000251150155481c0030a1400c1c0810036030701218629441414156400c0b00e8100005d03015100321a100c2d0307011a15001c080d1580b10700060304138403188103030740d2203007031561060100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 504924865 1250 504923615 504923621
    0x50a110c0c031015060503070e03060a0b010f02120d0c05070f0f021e010e10200c03070e06090a1d0106092a0f030e0a0c09140c0c0a08031513 62
    0x1c0c1c0415800d582040c3c6540300d40300281d40c111a10003041454680e0240101807150001c4e551084451518484040440011038148001980c07a1107070251201d20082495070001461701a000d264401011221080080c2105a0169001c0e5401145c0c503801e20329226031003103050710962600940320840d00301140c80c2040421585540403070141403600b078001905018111080d0a034203043c0c4401d030700729000b20104500070f502a2485024054900000000300d05170603d034405006d4400d0007040c8072504001090300e400c02c250301034440251894100481900c50185c03041c1c1040d00080049848803000b001a81180c02c0e041d070700d5880c0d43c80d0041c00074075110950001881c8404419080540d01072018018080411140c1d9030f00205054059243c102131003640501942018402611100f032240d55035070501c881c0301ea004094050315400700311102c90500b141680c015600862a5240101000743d00e0345500304040042c04010001c00020002021140e86401c000380060001400300c0d2500b101c2001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 504926115 1250 504924865 504924883
    0x105010f0c05252108091503070c051e1207030309141c030209180c090307030602070c05090402240f160c0b0307050d0e0c09070801080d14030109050a110c 68
    0x10f00d00500b000688445542da60884008107004081103484198403241400d6104e07941d0980c01c1820301100695888100c0b02850190100c0d580e440840e00389400d140d4a4424141e20031400c02c42d4502c80e4461881000a040419910313807940d00380c54426609040d030090803d403001600300390003c00174400611001c03508200d5a50017048003078040c403030488218200e019001441e50406a07130684c07103604002d8454000c1d8000c08840180e03183c134404401117400c04000e68002c942c0c3e9a0085000e1081145403100a03000d480242d60700d0a191929400103490980011a00003030500605540310044501c241252481c42020245958515580c6000c034150380c0c01c1d1809540e80350320b000c004035124040e181180c0c080c0340306649050400d1151030440d40241449000b00e0f040788a6041011525154980002e200c2c0354140c646482c0e80d03151407510390400303c051031250204044c13000c910117501090001d60703042d605110000101550b41130300c0000144a07070144007622180c0480c3c281c150450014100383c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 504927365 1250 504926115 504926173
    0x521010e0f0f0d1d0418150209010e09070212161a04050d030b06090105090a080a030e1201050c0a03092a0f050109030809010302031009020d0b040c170105010f0c05 72
    0xa07108102000440d00c88101c659008407002800600381101d185c5500040c400000300c1c24151130313540303441c0e5a0425130b02c03001100201c91a0040b541810a42e04040601c8c2d03841d40c251491742c064684010029140c040740c81e0140e0400b440400c01c49080102e03100e15003a090f6010f0181a8000d51904c1c0545851104a604950324450303002d8080a80f4440d000d501c0001c200a05030ba4104015600103607025080030702403540201c450480003c50304420007580d600d1030b0103901c0d00e0342040040030a00070040324403030884c40242e04040512031100844800c5865414051800041841c901d01d85504400c0000720403140e030f0f2030303c00f2150b9210040c0301d0f00e52007226082609805041d0f640c8005455292281c072019010380024000800c0550094004680c0702100c51020300001e0f4880003c03100700e070804000d20351901e41c1c0d58001e51035820588505400040c544c18031040c0b800140c0e641803402c8005001e402e040001d1501210340c203a000c2c010011540740d01900b900c0340c01423920303024102e4419a0a080c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 504928615 1250 504927365 504927373
    0x40801090c0504110c06070e03030735130306050a0e030318060109090b0420030a03050d05071b020409060b04020a0203070209061009030605131205070c0506040521010e0f0f 76
    0x8130b07160381e640b0b0407204145441c01c09400241e40e505401da4400d48003503a01a05400100030000000c0c16141c1400281e4030502c070140d0304512030a21402090016502c00001d4000401928622504c030041040c103c80e230010703000c01c8550b00c1040b000041c14200d4403801c545e00c00032042c00866014910f8500810011001700c400d03076030340d4034071031010303141c0740070f006080c0080c04000f04c4c000c00c4003080c91550043c0c503c40300c185912010340c0481e1030200400320036030000c0c3c0040b0380068034031142d002c0d15401400320b26000304504c125503012a0035241c401c0b4020301c15a40d5070641010800e07260450240110003d108546544644030301075280ea0002030101d1040c0c0400000a0700e626007145801c84504060351900101411580ea203802071401a1005a09041c0300080c0000074400d2034401644603040e50314240c86118501d00f54040300520342025101c1c41c0e0511007841075869641401d2540e00c422004400484800400c043c0184202d924140940c000c0c008003503442c0c000000d0700d00010380040229 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 504929865 1250 504928615 504928631
    0x705091801061709010b2205010902090a12030c06151802071e0c120c170a080d0207060f0e01020a2007270509070f0815011505040801090c0504 63
    0x8010011024010840811422600210f40c411000401c0d940b02d4004000014521a0600002d05141c2218040d04103822003400c05c0422000e1405101e0043c01c0d00e00c029400c2405a41c009061003100d801442c12240e403803114081894030030550545450782000003000b105003910501e038070b4520b950041440986050240740710210691080b106400c1e0421714260540802e919517400d080c014240548180c405068003260b100381c030041945d084bc1c462201e205c5a14900288192080d404215045070ba810904070000030460b58001c803500c036005071000698401a40c41c01c403004003e03c2034030303d0700c80e07242041c00700c0c5c4d20205600078464002c00e80c4034500d03141c08a0101c440c06013803050003210990032490040084412071040c40864000b4070850618030318581d07160304202d40702261540b85980c0111010081e01c818030069801074403031200503001040b01d0f0780c10000c0d0410184548200049905900f01c0b603217101e0420b0314098680300c0300030301a14a09050881586229000381d0344180d14007021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 504931115 1250 504929865 504929899
    0xd15050906100b031308070c170a060525141606090201180b0f030408070f06290315070c0c0905013201032a0305040b060627010314070509 61
    0x82d80c0c171a01c82e416201c3c2000049640e10001500b00d07200840e51504241c20100c2c01100480f951900d000004008101403060b5041200a54402620a01c00b52800c0d089418079429440028118108141808415002c0040c0780c1146442001da082c96020720700041c075070400002e5000100c031745000742c2e124a405102401c0d4104810f06a100b04041640c00b00101010440d0b0f41e000f441d03111340901c1d802c9080c030800b03484501c074044004000b21f07102c1c3d64402110500303045120b201020a284200d4045c940a10344000c640d6901c140092401d42e050f00e107001810261203041c15a4901da03001d405261643d40d0b41030000b020300750a0049080010341d04a541c2c0350304002400b00c1c0f00c24009000c8038001c101d800c100640041c800404103030920096040d5041001c0c3c00c844241d035044c20183d0340040c0515060810a044d074070040c00851242c0000c0110075403590850301500158465a001340d0400000783d001a401803e00342c00d030780703410f411503804c00200075040006401e02620580c0c101c4481030100394 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 504932365 1250 504931115 504931117
    0x5150c06011a0315060f0a030203060a170c04021303210f03231b16031704030203070210020f0d0807030e0c03031815041202100804110d15050906100b 66
    0xb8901007440d40034400503465402135110300d000198080c2440b80b800b038084000e58450780c494034500020913000003c0c03024504001385d5130b00041c51540c1c2d000101801880fa03694680b00d8440c16188160303004502c0c503c2c40c10203000f1400003168400920000d01e026000c060a10040c45a80b81c004200d48485034000640240200c4003500d075150811504030104240c491303040385024048504420002c52003202d482e01c0380001740000704005658a154000d40e20700200080c0c04520040042000c40090200181c0c00109a4134060350407106201c80515a41080780740c4000e00541c41040d2040b05245070340990402d400a0003008146d8050011403d0003030f42c0f640d1161202a040c0c1c0544c03041000c080d21345803809802c07281080007044d43c542d548105441125540145d00511001011030718440114a01540201110031140c01d00c200382d031410f51510014900c2040d40309000340201641c07102000108140c804071001c0b14403080dc40b90402d000c406a995500716030715010440100340104410710894 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 504933615 1250 504932365 504932399
    0xd0b1e030c060d0212070908160b04121707030f140304020a0b0d020c01020d05011d04110103020d0b0d231216020307120809040f020421020a05150c0601 67
    0x15004298200349070041c84070b41d40c00394082c0c01d0b642e82e09002c400f43c1081d007118241d00403250741e0788003002c00c1d04040f207407400c04800f0066440c1e200d12481c020401c5d490288181c03001c80c0c0003110491051450703420107403511001c401c000480041e0000705503017016000342d0b281a003140300b50b5401010089a11228400e44810340f000380d4000f20000c0d041011082000c014490804030802c00740c105005030b404182683c000300191056191200014002d90b98030b2000d000d081120034055449030700709921201c2c00c0001000d400c504050300092a120341c0c143e960401c402e07401d009005109442c40c203003051520003000300c00c01203215081e22041d144140c070000d40041da40300350400552038420f036031b00702c10007003086120100d03003500841c1c43c009114002c1440e184049030042d150283d50304080e504200483d10001903150400b0f20620007840441d901d41e00300d4000c41c2c14051000030654990001801700c100c680e000c96072009200c58000240340510010b40a140e5609044540a90700d41100f464a00804 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 504934865 1250 504933615 504933619
    0xe0106050d11040e0f03040602011a0301180f020a0f2606101e090905370b040204140901140a0b0f01050d0908040f03150507050f1e0d0b1e 61
    0x2c0311070300302e580c58180e10054a800c8484101c95141c41094169400c0d9006a0710243c0582d64540c1c0c080e0903420320114a80c0800302c04c1b0000c100010899180e62503002c030303100b03000d080c41c0c1041c1c0308041151180001d00c0f000d44001d00a00070003d581d52805604030625500051483c665110b80701d500359400a5014041ca19958900300f51606124a52124001c40710500e0011108507100103000342e5284590003032036005da000b0380000f100c240f05c02ca006540146003429070340c1d4494013100002501d08448142c240e401603828885480c0c9000060140c510000301d030100085c003074140703c000032056000c100c100e004a1110a03070b5a44442d0b011081702c0580f4031068104034891040481588100014891841082d00000301c5580580703400d00e2582181e080061100312012040c014000f44402e5a1007035007003010b0501592500c1900203005004001d050705007178002090124447d0351044074001c0c4914940c900584807450080441c024041c8c03011071600550b0111240c00710b450304804010b60f94080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 504936115 1250 504934865 504934883
    0xc0d2004061a070507050402030a061d0405060414010b030d030f060506130303030e1606090f0b0c0d05160203060f0708060d08030f040206040504090c08010606052a030c030d0e0106050d 81
    0x11420750002d5408001e088809000301000410155640c3c800345002e200419030001d0310900b0180c01c0440880c02c03d148000711405d05003048001000003c0c91540540e0101c104081c55460000c0705014100c2251007035490700504a62800450341507001c4003100c1ca07617090a1000d6980e5105210f083c1c800d0002402035400c00e9801440442c3c040c2c4c100340c03800700e9480704940e44c2031f00b0145009481c62180c0c00150014008100070040380008070944005446109212441e1081880311036940710b403081c44100500c0b00202c0d448181c40b8410144101842c0c000d010390b612450880c81819031034000311713102c0c03002c00c1c030510100f01d29061503107906440560142c5803070300d9522034044041c0c07441c03c0204100d9210804000100e0b10752924050581e505219000588000307003030010043c20740d01c558011204011003030005002900440b4200c580e41c600e030320480c0d00440050103000341144a550016100380c840058811403026041d40800b10075a1044000c10803a43c03a08104001c1c1c0c40c0004000e80b041d20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 504937365 1250 504936115 504936149
    0x807090504150e1b03010b0702030c0f06180105040801090b4002040b150a08090309011403060d081303030207120c05060309010902120d0815090c03090c0d200406 71
    0xa40f0352645403c15549603840764080072658640784250320036085184030034404a00b5034114102081780703900d00300c0100c403404120102e1002240460060120440c85200058501d0b092a401001101d0103040420300a114000301403d001030f1035401542d0f20b4000c42901c0304030620081c4940d183e0503094542040310000e811600b42000e041103400207041e644140c0e9031a0740446a501c041070003454642e150101c50303e40c15030035009000d5000080400040740c1081000c5a0380703030303031085c40c900d000d82d442030415840c0d464038000f060079a9862031004091542c0002c00b240d00e182143c4001d8101d901c25821101d0690b01c8605140c3c0c1d0a04000e0700070512101510203210510300a03000c1d5611582d07020001406440c1c0d82c0018550b090803800b5814540c010401594101c1c2c5d000c441c6940c061031070540031401c1d401c400085000400014514502c44102001140e845207091050b1083c0110041c05046d003500c0d03506107841d0309544200780d01d554210310100348029050a0041ca02101c8600f000c400c0000c2c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 504938615 1250 504937365 504937379
    0x100b0406080705090a03030c03020c010c0c1a07060204031b0b0a170601111501052803020d0206120408031603050f1906030c170c030307050a1104060e0403080709050415 74
    0x14288034240f007014090703101140c0b02d450b00000118025990700c1001c0300c0c07900b0060b00302281c050110f4100705042d000100843c02c0f145462049500d8801c8020100201007800001d60107401001802c150001400000340084100491001f05c00b403010052107a50b00c1d05e0380d4400e4418180140f000c07904e050032081041600340e000c154007902c18101107202800b5030503c10b05000714154484510320f0a403005002c0e60800d001c0c201124541a1004895a045002d00c41072107040340c4002842124000c0703460045480e807005131050030781d83d408030382414107240c9014000c6400403208012002000b4081401c0603109000c0e10380100c2d001040080c00ea21410304400c101000010440d44051301c5200000000d0304c0603150700d0060515000c0c06050b108490075440c1440c200c2c5007214443c0c0d00c28407411000c10301c0416280c00c0c59501c4400035460380810004100541420307482041000e001c4010030083c950800000c2d40303c2c0b8426500c440d007c503160030400003101c10706040c0c009402142e00083c040b070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 504939865 1250 504938615 504938627
    0x506010206371401060e01172e09020c1006140d170c010203062416020406050901060f120522050c0910090b03030715020d06030209100e100b0406 64
    0x1140d400040c241d010280c41c10b203043d540c101d0202d000c0300300c011004100c01648400328240303e540900c2d10000400340104410b800a5001e0300900c00403010b245040b801d1444140240c030707090b5034840b0030a5803668809940d4020340201400c0070030b6000d001c00c0201a60445d10031a010b076000c4c042407898842174807007840307005802c0d048104c80300440b5025085414492002502056519100240e900d18041c0c1c1880b8646852124540030b05140d59000705802c5d45032000c1d140f43c83c05c80000300350180c1d80340c000200503000ca07074016a0850040400170603055840030014168a4158551041901d000c1607007070100d403003c03180d004130941640505210030030141c0c0101c1c40a8096021100c0c03803041000001c01448063b1050000f02060300303006c0000314003602440c00114400c4015508000a036141c1101c543c0440c040518aa6400074620040b03421a0348540080c64029200001e50304d800c4010018200803409041220032020002030b01e440c00c050140e01c1519901400941002d141c040b007540c3c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 504941115 1250 504939865 504939931
    0x5060403030e0414090f4303201f0e150702120304080708030f0306060c1504141506060706200c0d111606050d0204030803090f010506010206 62
    0x200a45035405462000c44101905001d42403041c06086103080082c042440c1403c160f03003841070484130703507011850210000004013110190103038544074a503001881d07988910081e000144401c0c04a1200ea01c914018071381c803259143c06499114500007941c0038506003002b400c2e4940005010302e14040d400c0c0c01c1801c1c5800403115100c7c0c016041c00070aa0002c3c80085418918684540c4049401c02081d141001803500800c1c6039005945045106a40c002507480001d0a0500842d4000381c030001c500750403c40341200d510502d084407101e04007440d02524540a0340d82c1303102c0c41c0c070a20f0b0010400307526400c103640c0159001007030145810a03540d02c0f02d002d003210302c60816072498200345581c0c11050000007030028021034000f420700000c0d0383c40b01a04403c100e1348003442d950311030440d0451101d901c11a1005640d10340c01c003580c0340c10480f079000c006442282c10091822201000740102a14001142d4060750701c03174002404950b40f15401203940300f008a442c0d1005d41d80e1040401881d054030512210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 504942365 1250 504941115 504941119
    0xe0309031c030f051816061403060a1d1501181205011503030203070201031b1710090606020304050a08010513080a1b0809180106020717071205060a0f0605060403030e 73
    0x20f9000d0025400320840d40112070042e40d0300c908940d8940b03015028840049000d003143c400341265070526000a080391040c09004070f440c000000401e40c0d61361454202d40061a090380401080c2010b50104260380c807040d82d982a09440c440c00c8100d50350f000b9a8103c881860300e0821420040ca0200c91064032801c00350203a40e1950380d4045180e0200f01c86515101540c0240c004541c2c0314020320006045a0810411000c0b18514a036040816580241e080190700861421440b064850841d82c07016000c0c158403009041c4d207008000169282c001c40900b08079030040f108107180c00d5461144da400d80d03000b1500581814410500704000076660805010f000381e11340780140d8802c0840503941e0380003074411400d070b840090104180986180010448545001096111030b007940b52503c082d603540307400d00840b025034050f07000a1b050b1030000c10803040100303040f200c0008a10305504001d91100380a990a031407031400c01d400038003900c4ca10301070082102c0e000781c542c6241500c0c549049903107410495a190f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 504943615 1250 504942365 504942371
    0x10b0a0503010614151b07030c091404020103090218090a14060f070f03150b040305100c0e0f0411030403031409060103050309040c0c0f06061503050606190c051f0e0309031c03 77
    0xc3c454001c8101c40c03c9031b01400c0050074000d06509241c80054400d5010700000d60402901401c0e10038240402900301e43d0a080c08905280c00744009000e80c6208508540c100c4000700800114050000d0703c903a84901600c40920181d0720f00c4130b40358807407804540144a10940f1000b041c907e5100c0c02c10000804a5031400041e000c05c15560950607050540c06074503507100100c0d0a00078801c007403014540c1c440c0742c480204407030440c0c0d11014000b88100c003031151098084416112098480d90001c02e0310014004000e95a4502031070b0240c01481074000100f11800e60500040034108001681030599401000642c01e007000700c4100f0003e8507040080400300300100c8400b000041085004803040c512a45000c01c9003802d15200d41103101160b0a031801b0103091006111954070780e40211440401d5000c0c6035040b810b078200040d54a10740300800244a445844a040700354005080c50402d40d041c404e03414060101da01c20307095524002c0361552641504000b0741c0200c030304640110403456084e982008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 504944865 1250 504943615 504943627
    0x92e0c02030a0f022404091a1305060a080a05030304050601080a050616120c0e03010f06050a170c1e0a0b040303020303073f050601050708032412010b0a050301061415 73
    0x142a0b85c41c3c494040b42e1415030042400d01c8402d2803400746007650b40f0030b11844a81002c2d140c0005403c00c201d03d03c0c0803c0c25070b90740c0114580340c90701e03200300014020310340031103040040b00d1070003581e681c1c4102d0f410f90b807034000e0300004209a078021419000c2c01303030001c00400d41c41d00d905030007840308500708041006002c0f47c03800f0800f25802d5070003045100341c465221075500e280c50318145401c1d138000f002454103691030b2540a1080c0c1e901e040400d42503a00d404541015041c9000e0321618080e00e4401c8168000c01c00301e01d8610740811500c284c944c040003680c94541c0c5560b11071000305580940e00005003d83c10910004404d01d02c5804285801161020010540200c03000310a207074442c6403c03030341c0604038188a150500401402041e401880a1030f08030700c0e00b40c1d943c031406010700014120152009400c420421901683c46103194088070080481c80306c40e014080c294002c0c421410201d0041900340c85c001581d00e018481c01081b0382e40c0020491000002d41d041140304d07150b2240300d131401401030000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 504946115 1250 504944865 504944899
    0x1a030a0b06030a020918120901020d05070c080102032809020d0b07091503020a09080309010c030507030c0b0c03070e031f0903020f01020f0c0601080f100b06092e0c02030a0f02 77
    0x94024000d030000000c2d18000c201c80e060030000490501f1080460410000002da40d00003100f9004810382d18080391140810300d0642041c03000707923008864a6001100340610703080900350000c080c4811444814a210311012000c040d58035034900a03500070003581000002c920345030140e680c40807640c580301c1e60407a141d840b0078440002082304200025404254820749070340021141002d0000c2000131424181448002408000f101d24011b00304940030400108041c0600c810710360095015400c1e04651418803280000c40d042200c4001c000f41c13401c6e603220500e040100c0e401d48030003003580041d182c9001a24219000e0184000210114400d605100400d070b503080c8040d04050040c00f900d2603a40c01049081072038908180c200c04440d40203048a030342c0285002810303914a260011000c19207000ca54009440743c02014a140d80014441c1c03950103a211192003800b0314510100003405011444c40d00c12941c909008600a42503070000e158040401c00031504008858402002c100710403000c501 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 504947365 1250 504946115 504946129
    0x1608090a0602030a0e0a08120a05120c1801051611010c05010905010501050a060203031312051b1c180302042c0601060207051509010c060b0d03050d1a030a0b06030a02 73
    0x1c4001c00580000c6208140740d6844000415240400c440141d649401c082d8815220b10902c400d965012800040d01c1010b940a2420713644400c0200b03000080c0e030b00c1d0884c20200550f00003600c148c03107001c9205080d5201e60240064440b001a588400c0850141c241d40e100b5051440d1180c40c1d05204c603841c4c640001480c01d02807000124450400803400f03501d404203002131000203800c0802950000d00400c100c00d4600800040c2e15500a110501da1814110066035144070fa10100034804010050b1142c40d00d800003a1054240302e481b05070088030044c400100c074841c01c0751048007030800102c0420809403405800c1100004694404203182e4140c1da10075888840c504002c01241e0b80200004000c0356030107009101c0148010740305502d8240d0030483c09103003486083d118030706111030f0604e11824441c050340150be00708409000c0f0074540215040103040f6070042c40c0002c404500302404a445008021581d04441e90050000c0089500c103940d14200380500a1410b505403007098108001760f96240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 504948615 1250 504947365 504947369
    0x30b0a09060f0311010c0222090f08070c060203131710020c0a03080901050f0f04170d0605040b0d02030601181b030f0c0c0506160c080a0824061608090a 67
    0x81042c40070b61031880d000c1a00300d036905549041c003540310902c101507142c83c0c0301a40c3c0c2c83d5201892410030900c1415410040819a030050101d000c6840a0400c0240d120300900b00c46000d000201c3d0410f0740c40e0001c0760b8901c00c0c0030700c4100d8208809000c014003540b02c00c080c440c4d5001c450580303149000b108034000c100e0b0851000c507240c0d58004852030f014183c00421158011a6810007400b03149050303040c0c3c1c0e01104e009031003605e10038030000c0042c040c0400c000f03130340c5560980c2909856135104020b01d0b440c0a001d55028440c03189103001c2c0c0002035450700499240c00140c0c00b501401d131681c0303052100c480c980b9120400800c0d840e15519024ad46540700c451200c80119661000030b02c0190f000750080890307035400204402d00100080708008110300241c5150710040319488220460003014084444283c51940240f80701c1000c00c090b400c0c15003114a05220b42c0c500c05030101112803541440748003a814160740745d00043e040184151034000780000020980c010b00c0c0c2c0c686028106800326043c04030782d07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 504949865 1250 504948615 504948629
    0x204090c0906080c160f02031e0705041406031b0d0f0305121f0b03060f04052a040e0114060f0d06060305090c0a051e100509040609020c0607030b0a0906 67
    0x2401c00340111070708518099042840e00e16220308100b404c40c00c5c2c000d0204c103030074081d2031245407042c281d0465508008035001c0d041024440030b051001c0c51000c0d44e650792103000d010303c140c2c00c0204461110407840611846010000d00404e8441c00000b002001c203000c440c110364100c05c5031685034007c1080d110f0072015091081d036510366a1418000c180c26254406003040700711407104402c140c01455165044001d8805007004203640391200d80c0090000c61029000c00d17003040c00c0500b0003602c0500000685499981400080030384544011000554032440c0146258210750340014056100345440041404034050101da26020444809006c181c0100244545168492a042c401c440d8140500c0341c0210a0100608800340c0315800213041000500a550084039100113250b0b001089520341a5040300181070030103d2440801c1c0282503a000c0001c0a0190f0f0400c0c5000808bd44684201c40d0061a0364001d031a80340c5841108501819060f1503c1d0360042412501240740c3e041481920010b0100b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 504951115 1250 504949865 504949877
    0x6040b060103270c050402040602030915090d05010203040606061806081302090f091e19060b06030f040314030f07210608070807091a0d0c1a0a020c12030d020d0204090c 74
    0xa242890700e407007803900028086c90040c0b20400c019a0000190303001d0000c11140d000144100802d0f441d200c0c0944d61410784e0000c03074500010140f12065000314000d5000310f0080c4802525080252501e502d003040b0000001d642603410460180314a0000d60000040c1a40f400c06010359000100420425982c04060621403030501c400b10604120001e55150140c1610701c51303003003034590a525a43c5900181250f0000200300d40b00300044c0364044e58150000030040c03902e07030605010301e44500c50116422408140060741c0300840c841d014042d2481070400f8100c03043c00765a2400e0449444000507543d0060440d20004908507121601601011706440c40091803014a0288070340d00e00301281c0e00c880d152600d04503607004a50b610004000f8007003015100500209034901d0440e070500c00603031103c030700c66980c406072042e00c0c08032340002e002c2068035a003194422400041088403020a5030060226a4420048186103100303030303005850691000407006040c5a503901040d000d503000d115182c800122 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 504952365 1250 504951115 504951191
    0x8011a03010b01020703030801230a0b0919030b0103020f03100501060f0e0d0b0109051314010501262a030708060109150b07060f0207050d0314150306040b060103 71
    0xc0c244190400c1100c240300902810f450340e00d01071f05486046c0603016810102c2c0826000144015a4071200e07010701030103010b0045d69540303180800340c00800d1031074440d41880824001181c400700840c02665081441010180d19603400c1003484441d02c22807039010b00900c07110807152211031013030034000c1803940c403410300c9517848010003080c500d14040f5040c881d0981e2030040000c02c41c4110340b00c1c10754018140000d0315441d0455452108038196500521081401c070140380c4101041d00414100c1d0303090400c481c10045440429103403462862400030480c2d0100b1080040c0711a54800005035240038004980e0341c0040c503010a00b84181908040c1c1158040300041082e44c116100da802141924000480c49509107a40b035419842450405007583d92900c0080d100480c07140e0480380070b203501070101c8604044030040600640700c040140d510220401c0002a00c010b102d640100200c80c1c01009841c0c1a501c0355907000c0c1e1400080c0c542d504040d40c503c42181a00311000c00d00d4450ba14911000c90414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 504953615 1250 504952365 504952369
    0x601120e0d020106080a150c05040e04060f0c090e16051606060515030f0117030d020a120c02030309030f0708040504020c0a0b070e1008041407090c0806040c08060904060608011a 78
    0x103013459000c0c50566100c001d0600209002c40451001d05240f1840840c1c415500d080413666800f0b1500508001b920700c00910080040a50200f000e01c400d5580610100c2c0c0000030030ba41c410702d20300c100e800555a100000d4001e8141e038100b410740a246050040c00c01009180390494400314190440f03a0950301c6600384641d01c0c1005444d1601905076500a11f075141c1554448030098041c403814400c010b4403184860700c40704c14015210125070094045403124220400205082600811100c00528010b0b11451043c808000c9030f120b031072460000d5140010300070304001a41d01c6001e06441d0700c94280700116469030f0364001401c4082d0000c0051610007a1404c2001030888003601704000e100c100b150880540e1103615000c28058800c0c105100c01d980c9504100d0060056078441781d40d09d0244180101e9030040c6923102ca40c6c983c01e6540c4180c81980c81809020466803090142804600d2002c0000c24a01d03000b0600380e402881090042100380e030f2000c10b6402d48181224500e100b0f00b2850280c1258 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 504954865 1250 504953615 504953621
    0x9050117070308250317090a0305031302040605060a0804140d020c0603071205010806010801060801060803090f0d350a0816020a0b0f01090507050703170601120e0d0201 74
    0x50300030340910403105080400200d036160200d01c030040c01c01102089000e81e01c0300451181034a51010092005880304901e001400c2041a164601c003003100400031802c0b40c4ca001507040000795042e195a46107440d110064422800584012070380a41c0350b01d0301040ca5102c50317014044035000798031001e405e81854502000b01c00b002c0c080c0080c2c160f0100809a41c0c0580c001100650914255016541c80e1252013044609150707502d890100a400d01000240c107100000e1141d0488040c4d01c000c01c9500d0715040200e00b43d6074980300f140c010794800d000c210400e01d0448d11003403081d80001d00d40c041503110b6545903502101c1e45542c0c10103215207400e01d824003004a50f50381046200c050742c9a807804554900c0074040c81d80162800502140d800303d0080020700030000201c415404c102c0000c00c916000040104d146800d0140070310702da003840f0100c0d43c880c0c090020b40d12030b180d140d20350441c1e940700e039000c010303014400400341da041100480c5500d003500e14034454802c032603070450042c103a4001e0034003000e829 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 504956115 1250 504954865 504954869
    0xd090507080c2d060d0c09170102070b04020918070609140906030a15060b0714100615030e0304090e0109020109080d050708070809060310030507050904080a050310091104090501 78
    0x10365582404820070000400942001040c0032071890f2140094001080250040c811007207102464100304140b91500149080c0c1200c21505425078074a5141056070b090b40154a4014a844491004a001072030510501548540c5241d1030101c1294400f22141ca04007140d4070000114050801c140304401c00c60200000b844010340f9690300c0c1e800c0c0400481c3d9501c004010240040c18151901101041550012401440c201c41003d4468404e8204801a034410b00003094880c400c036131401000e200507010300d02c11030300c0707180724400c00c4409008150702605002000710030310f010401c07010801c0905442a441c17414419400054144454400544008456044040c04e680800752050b8660381c00011905101d9015911944070310751071504413040d009040700c0d19400f090201c204000c21b1103419000701128000c104541e0709550351010b1007003016040d50058400042000308103ca28091401103812a440d0280000c40c0e564400c070420456003810036000d03100e003001500700543c841074018980 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 504957365 1250 504956115 504956119
    0x804050607031e0e070b0a05090901050301060e18030c0d09030203010f2a050403050304030615170303040303090302210a0e0604080d0804021c0b100b090d0204050c0d090507080c 78
    0x1003020a040f446460001c2070b0f0100e11107194403440c403908011810301848000b0481c0c21010b54854900b5640680170b504145107003409110500000507640c901405090704544481c48013044540f100c00c001c103d00710b110a501d98441c4400c200e01080580301b00642e003019841a6100c001e52815403041500350781841020396542401c00315220341501042c9a05404480964001b805454591802303403250300680c3d1001e00503000100700002880302581040e20034840003214010700c3c07031b100c4032102035080800361014413a50050002600080c0607a103c02d190034003900444c0c1058140841c4900c09810400f180c58413520042010a41d4980100c100100c03800225030b40340c101410464010b95030300b080c140304000c00410b000032805540b43c0311a141c0314840303c9503040c1920b20036401d1585200c030342510f034894814070354031000031b6501d9144165200c5241c028644481c80c4c3c0703582c081001802c0040c0c00e02120301010850441c100340c2c0c601c140c40b0807034481e00c0035250741880c10007803074205541000c0d118 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 504958615 1250 504957365 504957371
    0xa0b0105090a140606370201060f0f0302010507022d010e04060e0a021803120c0d0c150e010f0c090509060108010515030901092f0f0a1404020702060a080405060703 72
    0x1c032100ea5460400c540c003800980321240c44140190100c00b812042009003940400e14101410401800303036a0103044509580080c02580c4d0380e0ac541100010051003609a40350342030600344012740c416802011150b0008007801d0660200600301c904404c48100d0a03040c0a812031516182541c00600e0001415421236081203c0c80c500400c606e105a4010300922895a0008400c4140c81e10b484410400442c09800c0780e6005022414010583d48070102c0d86915220f1041219802e500c1509040030341c60b800955090b041103d6803508000d4100001803480c1552950f402015000e13580c4900d6400c3c072525500d06500034a42014020380d014090300c440d04218039070006000c19200c0951032110440d1140010780d9a540310b209090060540c41c80040400380c81a503440005800444007110a500545032640100c0b40c4e02c04100070500340c80c42050300700e141a4000c014403842030030308a40c2071002a1015107450240c0d40060001c0c0e001410210100d15110240300a0000810cca240c0c006081c2c1410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 504959865 1250 504958615 504958631
    0x2040e090a210c1502130807030303060b0328092004050603010e0d110c030d050c0c03011a040207050c04051e09030a2003120405010501080f0a0c050405180a0b0105090a 74
    0x522038462843d0291015101402d00807000c0810741c11602c00c0e03922941c041a1681c0c5422140b40c441000c2d120030f0300043d01305a00807500c2034919080f01d002d10851181056030300804000c0900318048a0342c12102c803a44c0c0c0c503540700810301040c0300c032542400000440200100d1722040008980d00900480e009a140c4024040c0e008000140c140fa5180203050080301c681028913a20b1500030600012038150091814445103250041e010b4040c0c0c80d901c01c01d440d24040030400381402c843c0c0e481c0c0c804280c00b900031041c00f0b150401780d004090560142d4246c0c0c036075213400c2000c0b0303080d1a000d9806000940050382c001611600c0c014586c3e4001c80c645001d18034120982c00005d08143c007a000040c048022000c00040c0b0700c2c0c040044400d0a42d80c0e140800c140d2809041040c000d043c24850345050740102905441140e0010640f00316441e0301c010b010078814107160604c4028400241000000388180d0f0f0030104a070420000040c03001d1040c00c40601d9503051000b40071200101401c643c10003400c04043c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 504961115 1250 504959865 504959867
    0x1110a020a060509060f0c010f0b011d091812070c0e0c040b0a0e0d050c0f03030c100b06041701290f0904031e09030203070501210f02040e090a21 64
    0x2090440b0078900d0300075100c00300000001c1044c070540e0018070151300005480d0710080b606412140d52294000e0341001030361600790040d202c4d440081c503505400c070030360800040140f8210050f1074001920200700400c82c42d0301c005076407522003044001941310002062100c03c10880220000150005441c04615410846e0309111540209d0107030015014011901d282164415288451120b5004040f80300303d0900d0708220b0f0b181c81c0c01e4001c1902030348140002da495402c00004648494812034010b01080f1580d5200e44000c3c620b004415034885800c100004030450b288525285442d503200000405000000d02c15491020312061070502080e811514000b0ba950241e8040f10404107030b5640030aa56540340442e291380819141103020b00100781e09070142c0342d010124070184e0384280d08071040c1d50b859500540300d82d40514070382c01b902c159a40780303d020306000e90004481881c0b100340c058107054171581d0300ca030010001c43d00c0807065808070700400140040803024414482d1034602c501c1041d65a910 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 504962365 1250 504961115 504961129
    0x203030103151407050d0c0504060f030e070506030405030319061406090112020f0702090112080403021c02040207080c0d030606080c160c030b060111010c0f0c080d050108070501110a02 81
    0x2001034082c2006045500a005058000a80e02544000e20341294a894003001e02190000d01c0d0341c224184c07412817041e1945006800301c40030381d8416141d480c0000c4a00344110060444500c60410b203005988000920351580340113140502d2195000c0c540f2031611580c404280f034a02017580686608005040002c401e2441390340c240308a003543d0311503880d051040180c2d80b04101c00c1004003114800141078803040864030140c50464801c442100140e40c2e964030307403030781c1500240028200d010200030800051500201c01c8803100c2015841455101180d0000f800300c0c1c000b010141c031901c2c0c0c0043c1c001c00182003800320042e01c401078107007000300781e0a0100c02001d804009104000b45640050342e141110b10780c0700b43d645040d912a025044441d00c074900a540f41209031241d6020440301031400344400018000c551000c5103940d100900900d1485048030f902440365819107904000b08108500c0648c540a0306029042080c020019103107028001041030300c0c13540022402e0340255100d0750050392012 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 504963615 1250 504962365 504962369
    0x121501050d05040302010e060705090f01210b12060a0c0e1f030209031e0a17040e06150c011a0907030c0e060d2702011b0201120c0513030515100602030301 68
    0x903000509560f8620f0140c0c010600003070010b07243d10801c0200144254840c00601d01c01c0740a84441c004424424011b41d00140840d10900b480f4424131100311b0000c4c401d5120340300402004148600717100c0040c151034203080d020364600f5070854035030300e900c5815a0071140c000c0700ca040565042e10210040140d8604003070b501d94111080640024801c0201d0343c1c200b02ca41c0740c0e00c450417050640100b0b40c0ac0c045542c1d4080090031540d5004558010f8000c10b0b001041e9011100d081c042d21030990f542d8410014201d8250407c0799046105010401c0061024401c1c10981e44a41070030a92884d813503020821408801403024003090b080c0403c8040b2030354015409a14007906860054031808008038000241c901c1c0c086440b0031508500700f6040501030440c44c812403a000703030bd81a4000d004200c3ca00200c064001c0c0207408507042c80701c0b000302d00d41d4603030060a40e01020b10b00346040041c0c42100c4200c5e418160f00981d801c5c0d010214030f03680b00b1070714208540c0180e1842000001c59162500182d102c0c0014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 504964865 1250 504963615 504963637
    0x9061e010f090b130f06020604020307060c170301090e0c030f0705091503010c1706012a030e100f1d03060c07051606031a010305090309040902030f010c0512150105 72
    0x41403030707071015805040c0d0140034008905066485800348481d800314409a4402c04502010203840090f00c0c03800402c54a00035130f005000340a01e5414014150f500034690304044802640f6a40504a581d00d050041c502038004100049007143c0008022840e0403002c0461912940003000c004814800008401c003c4a10070b903448110b80d43d5441d0410003204021001540550070101441c00311580503c504443e5810380700e803c0e0740d940b0340900441d08410008000802400c2e10190320000000f0040d05a0101c2c1c46442c04800c03500108010804000c211540e50000c00c0c100c80726500e0355a049243c421920862101240c1c00d41101d5000a9481074081e00d03041100c0c5001034050709100042c054641035078840e4415207032442c0c0d42c3c40028020700e8806c402131380503595600ca02c042c0e90b1180c01040e0050214400442c24912110f0030400100141041280c0c50703c207190100c0900b9900b0b00420250518545406440300381d2400c1c81e0006203001800320748401e4000038480b40582e003103000d803a103039101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 504966115 1250 504964865 504964877
    0x302090f19171f0b01081506040306050a020705011a03121201030803130c03030f090605130b03131703100803040602030313020105040302180108100c2003130e0609061e01 75
    0x140c5031550034503a081507100400e083c40d510a0f03000d80e850740c1140395804802c0e640d15a02c1d41e5442e003020380c846c0381381700001d44c000c10800c0100081000f6402094100c4400000103103080d6840c2e40d0a400c4591200f142030074001c10740c5d400145403034180001f070444000d03400d42d14138060344007200717070200d107130501008280c458080007050110502c0c164141c0c19541c00031001800a4407402d002c0c002030001c03018140080c500b0103003c00c1a6116070280c0c1c00c0c90ba0310b0b540b04000c290030480049034030340005002441c0d068000581802042c0c04051048480e0031441d9100e6070703070030920142a00c200340398005e400d81c1c0e8000c0004010080c5e000048a90201407441010700c8031800b48012a03807032146600c041c1d4020030b10003400700c1040d113840ca514100c54525080341d00e018000103200c42510740003509580031842c0c240d0080448022865600c1c0100e0204082da49480303403611040002c02255002065069041000c10105003401012180c11410488040c095002c501180005040f15400242d040000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 504967365 1250 504966115 504966149
    0x1061412040512030a0f050105040b011209080f0a17010807080a03080604090609050624011430040618123f050f060904141c0302090f19 60
    0x7038284441c40540c0000d50306503139a4201303120b8001c090214114240b28640c039240000619203007520900c450a5010b03140d40c1d43d02040c84000200800090f641503a0440040080f45070b007050312401440311900036111907210403107501010704e0060051300401e03001d034082c40c0f0034000c08800191454030303c0ea0610b45503100d5034481c00828050482a0f20082c2070f0b0f41800e50300f408114021401c148a0303040c0d0b03500c1303204500d0f03440c2420300c03050896000103000c110008142440120381c40d0040c401000c0070702240d850070100010402c6043d003e100b5a403000030814060100b0031100f401100e060301d500116000030740c402d546412280c3c0c030780080000d050000c2143c8852400a4001d5804120030f403031800024550340e0b484101050420006416010728903000000d103050b40b460308184d00900010742040c520b40d07126503481d00c800200c1d010031042031041c4542080b1501c11801640e0410f42643c2c1c000d038668921100b4011300c03800e500c2046200c0d549030ba190185450420860780115800c64049107d400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 504968615 1250 504967365 504967373
    0x201060f0303080c1c15090b0d120e06090a081c02060103080d0f09020306010b03150405040b0f06031510030314030f06010f0e13021206030d14030a140a050406050106141204 76
    0x1441070001115068180030301ca0400000c25444a003c0f103403061f405001d200080b008000d0305407140706000b40350010b040300c5000e07464441c00510341c06050103018285016081c03000500f016141d5071094001d9800035501102e0302081d1050b60b080c40b800350009000650540c0d60f041018020300700030031200c2d5500c0490041201c200d800c070848581d0058162400d6507151569811194403c0f540d010021004020b12210303800c1c1440303100c1c442c40c0c12085421503511a1904040c540e07038040c141a80c940314003a1076080130140900068001c503d212154001c240c6140790281c40001050501d040418040c030800c07860101d120b80c3c0c954483d00c2481e15900d02c04030300c101501c50010342c120003604141c1d150a03240b03900041c2e90090038141000300144042d643e0303c90030195a400748050740c4001541c07802c42840d010038104003442e0404003190020070383c5060890204008541217801407484d03501c0350180b1051102e140301c3c40f40940401d01d0040740300841001410140e00c1204000d00c103242e0039000280c180 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 504969865 1250 504968615 504968647
    0x4060b0604090507020c03060907060203120c0c15150111150702070819060605060a0906030908040e090102090a08010506060a1d040e0a030807020105060d060c09150201020403030201060f0303080c 86
    0x2d401d0000b02005942443e0f200299500b80800c0004d000348500b10120f40003078000581413003101c00c1c0d030380150329080800d08150700320030000e4100b2600110900c4968100c0390184800d401800890285c07007010310b0704c5011040030300b41d4812414103001481c00c000354400b001180c0c065400700da040c20701c03019448050040b0300d415801c3d0302c125103034026005400c81c0c016086908180c4180141410320060b0744880401507144a006018000700b09036000400415019402c0180100c0c00b85114605180c2e60300a503840d014021111001565800101c180981c81e0070071026000d07040c0c0c2002000740d8509107022664a03c20301c0340400611440644c0004091015840c0c403840400181c42481011501c011140da1078004070310840110740f0700070000714968170504c03405106503001045c03945d40c451961115070050605004a404124030090042604200c00304255501036442d400180c4d00c034030303604000342120300940045d411305e0a9200100f020950024a2582180000140302e0b50b62003041d07004031203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 504971115 1250 504969865 504969869
    0x80f33060c0718141617010e0402040e2a040219020c2803080703030207060504080d060509040b07030c2105070e0108071205101806032904060b0604 65
    0x1008000190142540c1c1000c20064100c0c0e94908038161640080103214050381c00c800d0000030440481000a282c4d0101d000c0c0c00b0700d00c02c0181c1022041c9401540e5155002d00c0700341c1001c03104102c1e040034401181014441e44002502d40c00182440c00080c0200c85965002d19008142c000710710301c3c0420343c40c0e85543c1220040310a1101c03c0101904680019440708074010303081d803144141c56140c4410031240441e182c0700c0e07030380c1072207030002c00c0c0c150b60b03643c3c80359000f0600035010194284032940c0000c44034442e060049019040d480e40f6407281602a07003d4860ba9000716004503020801d00c400035007030101981d0890014200031680e40d01d00741040355003450210300710364002c0d009880422026200c0d403100c1d01030000786d50780860381400c06e0300540380700d1820789041c000a12a0b207161480800e20382d00558200306400c134507018160327480f00344270301054954040d0380e00d0f50f0f0740c6d5204000308100380380004a00100d0410340000c0d41030b109000321a044000304045d11407910313804013003507503038940e411900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 504972365 1250 504971115 504971119
    0x1706040e1b03010b091b0a030603060e1b0301060602030d020313020913110409021c05010209031002130f0f090504030302070b0408030406200706020c0f010c0f080f33 73
    0x400328000741900441c1e03880c80704009029520348000e80c1c01a04040d41550310940d4500c900390401c8504501c0c3c007045910041c0403000301a0780d0400800010b000307000d05608a51454006e114588a01030b03104c0d040f045405c2102c5c0310760300d8030404011017a000b000f0748980364812000140c6030b650700c1d0074a400040407424000e511107250001c00058422034441d032641d00d4004c54080e80f114440700e060104030707400540007a62003145425402d4249a4000c54103200b0b601c80c1c07001508142c0040d000c60300c0c001c00d645050621540200e48140c040815a006a0081160000400324240341c42010120800c0601134400016140d400140505009070115612107501c82c0c0040c92503d401d00b4804400d0b0000d85048465604020350b040d1f10843e01c042803440820000101403070b0044039a00c1100940c131401e000361241c000c580001503030403820300c04d2802c1031000d0703198000c880f100e0700c00041c00b8910040040034680c104406005104003210100802c2456419200002200d00c80216402d180c00400d49070b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 504973615 1250 504972365 504972373
    0x210091419080a05060a0e03071505190c11010515060406050c030c0709090218042f090405030717251e0615170d0f1404080606010809010b011706040e 66
    0x3c00c00200140c440d124582910b000c1102e040100c2001d5200d101d8410060400c00c8607200d0141c203001c03240d00080c1c2003211065090005901010348000b520340002049011a100080c1004145002c1c05071075840303104c220680554500c1480050110f0280c0c0c0115400c200d4082411290b40781c00700300312021442110111031905983d03070903140280036140c00407030103000c583c280c1c014103a8001001901a03039011050300180c850503c0640031884060340100100302510041c0720003503c0710100507028500810256503030740b41c030382448400c0d0401e071450340044800401900101c2c1101603205a01808400342c03500d443e5003181410b240d0044030703c24071030007160314000c01801c00110313900c40d8604505014030741e01d41940c0c901420030201481c22207842d498000f250180b0034540301d00e91050f409400b03420700c000010501c940c8500f00da0003a400ca18900e9101d0400e05c950b40da00905400d500417012402807080b0f00d003800000b01700051416001c0c1407080d880c00460019659038101c1810010020119 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 504974865 1250 504973615 504973633
    0x3150b1e03010906050f0103021303060f0908040e04120807020a02150d020d060905070905060409050907180207020406150c0303051503010f0501030611030c0412050a140604021009141908 82
    0x904011300052180c40c0c0304651140e10210594080e000760b909500d00c2c42a848001441c40d1030b00f02c003400001d040014903964a680500002d0848800342010345580054026a480e0a19006003500050001e403030600c10b12500704824036500240703880c00c0c0d03541aa014038030030000c0541800c2c140509020340c843c2c075002050b40c2c0c441c03120b942d122004031140340034244401c0c1c8403d0030560f00d0707040600581d9044070781088107008214a0745c1115400c158410102c815556844140300710580c0840b810140d0390790002402400d61a0500408014081250104104250340344016090103070306d00c00101490340707c4000810410b41c8092840482c100a0000c2c03102ea041550b4210080c00c0902088030140d240c400500b45401c2902c040c1c911410340028801d141504205d001c44814107071001c221514841c50f03444800003000401d4105c00c200110700101098100b030701c1040540080c64030b480c01003141182c030070401907145a008990b20381c4203844000c40780e040700451011080700c5400105080c401e03102d030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 504976115 1250 504974865 504974879
    0x110415021006140109090b0d0f1a0117010b0604050f01030c0c080412060f09110904050a0c0b0909090a0c140307030c081c03061410200c1003150b1e0301 67
    0xa00c1152031400da071812205130700c5400c0e00049070410556260010400d0500070002441c9111780714445004052b1442c007183c26124400010009170082d51800c0c003a03890200c4080002d0042030000c41045858034141414040425006428513003201d04254841008800c118003c0a41c204081d81045149035034036140d4580340409500e81c04100c1e61540741803104400b61030b41c2c0c8200102c01e0303405000e0341d44040481c8100104620301500590b058010804808002203ca01e110b0004108640b407607520740302c9003000c001191b0b5000f080340754241c0001c041c4070000792046400000b0b0300c03603480ca6824152840700c0801d20b0040d45402c000c08a20218001003400000041da01c456031a00e0b08249450241d061411030545a103481062801c40044c4141203d62602d207103000d28103004c0385012014202107002c28240051182c2c2104129000710000000906025540100110b000c0c203041c1701c035851090f500f45a4000340d12900e4542d941c0419810b00560219400d0b210b00340a2080ca580c41e540c540c10303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 504977365 1250 504976115 504976139
    0x140a03030c090f0321120c120b030c0f040f0204180213080d0503070e220509190b040803070212070b010806070c110d030e100509040e01110415021006 66
    0x256500110b142100002154030b5032540f80030540340c1c0040010342500d0040c1c0001480c0003811288014000c0043c0781c00750040240c41400302c070400c140e81e2441d900800f0b45d0340d001140c440081590003a00050701400d03181d12110711241c051901502c0004502d1154a801c0d4000d004540182d0354405c02e2680e100c241c4100f9401824a6031140c0310300c85103056890600640e95242d802e01d54001c180c007400015000307401000000800040a05844105030020300508154a0413a0500701c010343e940d014001c0c145410850600c10b110307080a114030f05207840d00c0d80b00882c00000c000130402000000001e101c1c902c240411407069080600031501e030640c625181d90200303000d0180070303046d116210020324424499811100c003980c00503866011040e040c400d000c40201e9001d000d40a10031014800092911802c4042100e00c019070f4038542c58900000401c0241d0314401008501a030501922080c1407950b00112030454003e40004030341d03003108407020b0b41001c40e00c600003005603240080008130b840302c0710 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 504978615 1250 504977365 504977381
    0x102100f05010905061c0f03031107061505010918020d140f01080f0123130203060c0405040b0d0201091e1a040e090f060114030a050d0f02070815040f140a0303 70
    0x10b40f050125980c0d00c030520010368a042da84182c000003003c0c1810100c1c4801c507004074224003c0c44c01103038049011001303e6141c0d001a008486860ba60301403040948003c984c0744002c3c0c1824a0302d4440e2a00c1c3c5194684003813494000c403040d181c0d0000f0401c14248550b07101100ca10400c81d810704140c50450414100d0b06400d11818207540940107a01042c44018441c00040c003403c11012a26204500e40b02219200c0c01010b10702210318240d802405a40c3c100010703881826034040440d03a50f030900c4288025501c1c08011136010720048070303140d40143c5e0031050312025074204030b60300300d0300000c903038210030b5018103a07440780200c8a803032a94a0b00381d090120003001a50b81440c0745201d1515078854a43c1d441008025140c0e482c0c04c464010320100c1d080301000411000000c0807110801200c0e2101402e007584c0040450124200b03416902805070140130041c01400b81c0406400c2801a070284920000c000070401410864406110700400014050b42c540302108103003261700c0f010003440c000c3c0080c2064 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 504979865 1250 504978615 504978629
    0x31f050409081902070f03150902031f0c051606021e0408010b011b02150313062a1e03051306020d06090506030d020c100302071e0b0c16110102100f0501 67
    0x148900c3c40b014000038890040307400c03800d0403000252a50b2100c0840002c0c1c1e5001c101d031680c40709050380150340c1c00c0080c00fa11013802903502070700001400e100c9044807440054030040c4642805103501c0e009a546d02c5924850b000b5901603681d036199248231240c030b016044c0103424402c3c0440c0100b620030056014900c4100b00381c8031003d007049040036a240818294000941c4510103100c404c2c800031207200a5030300842240211031124800350b80702426258214005907403401c00c501301124461440250050b01285810f081e40c2d00c01901280e46541e48100426109240c0c41e079010914000c0c00d01e4014075540e40141085460700380c00c800362000340c0203500c20f5842003030400002c42c10078a80410180c4245c2c80396002041d558a840c02848002100b0442d00004c1c1a421b12461000c2032071040394045598041100342580135652501504d0070340e02601151031031a080c0284540e80c9015405444141e400141040703980040100403880c050b9425140100f140c105000440c00c0e481c00d80019040c4c40300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 504981115 1250 504979865 504979897
    0x2060a050301061713021306051302090f041401030b070504090c0f020607050f07020108100b070f060509070e061c0c140307141513030804060804050c090c031f05040908 74
    0x16221201a04c000340c0d418a0880d4004000c2c0e801498030400ea4031484c640b614010400a54420026491081d049203140000d40c0000b00c0da0f10924001c0030840301e21104403010050001c000c40245130301d4034140401817941296202282c1e07240d010310140c0c1d00903c4200000d02065880d2000180702c0c003501911400503204d400082050240900240c4a641020030b0b4000d0415100d5001192031540140c403e00e41c04441c01004030340c6070055030091400324080d81c1410b91f20800e0f490440100ca00082c400c43d0281c1004d1000d024410a041d010741d000b40044131851011000303c10b03c1c0401e803400d040c00520785c008101000500c0c001e89409030500500840c03d07075042e1941e8201d11002ea183c0b401c03071907511030b5007a61341e00c0e00b280004014001003840131560220300c640b83d03580e0405a5100b0340001000c030380803501b04410400c0400c2010300401c02691400118207010540b4040c500000e014400c10380f62010050f8072a50f45094207800030079000f442072101502c2410701030300991050840d1050106 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 504982365 1250 504981115 504981137
    0x703090506060111060a0f020f0d09050714090f061804030f14040b0a110717070905060d21020a020d0b07080708150105071104020a0801050301050603280f02060a05030106 75
    0x300a10383c0025100310708000c5c080540d51417030180014260f016130550368503824840d41c04110914805013440b018088800540c14100e030822030b01d0407900780d210b0780102c241b03184e007100e80380c0b1460006034003c42c5004d500400740e2224000100d0065541d00c6c404844408032041000f03159000c841610b5a915684450420740c0240303065001901c1a80180c040090081011041003481403810b10440100081512031058403030080c601410010b8495800c82d0740150750030700c043c2c3e840d8450590010400c56490f04192500d0f03a41c5540d0651404006102c5404120600362190090100740e1845500610001d000320403450f2507802c9c004140ca2403030009100c400014802d9008200e0240101030202c403070000070141b5001101c0580c0003e4040301c07850064102c2024540f294000b800141206442c0c03220650306003818142111802041503101e5845610321207100541b490b030302d000c2c20236030040c119070034009803c02045421440e40e0081d000301000a80a04103984040514180c9503240c0da0b0381040c203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 504983615 1250 504982365 504982367
    0x7030c03060f0b120a120e090402150c03070501051f03050c0d1704080319170c0d09080d020c0c0a0b250c0612051b0a051b061317030103030e1005040b0307030905060601 74
    0x80a01521f9600203104c4004100903151031490301e1840308190b07040300c2c03034403004000890550f00304070000c0310f00ba91070743d083c00201180b04800c0c100c040300c00400b280c031032403a5448070741d42c413080c80c8032490060408060307000501c010500104c1601d0800300d041507503290b80b460140d55a500071101300a11404061905061718899071001e51200003013150702c0082e0f1103040c42001c4c1a44481c4859400075605c0b0000c01c0003c5040c0050990072656070070043e00d4035040d002c414104220046214442d00c10b0300303001d100060040f81542c903034107444ca4621901c42000f00024407401c51245000e0022030031074400240035940600030111000d40400140800c1d12110004118ac1809034144840ca00702404000c1d09030344140050100c0840c8420f03451417011001e0f038414240041a10110f00d0a003e004454040c4100caa08100004014141c2d082c5550f15544005104180701004244281d0f80c03443d005492900c9401640d000d400603240f859505d050100f0081e004001d00e807000c03070340707801420006003040d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 504984865 1250 504983615 504983627
    0x20070b0c010b0d05070312030e0d08011d0f0a0c11160f0f030c060815180a2405010c2105040e060d0512251202070807030c03060f0b120a12 61
    0xb0740d00070005c00344181140d0710300c9400035504a580d810181d8074111822108003c0280e0800000b03144c40b040040d5050030f1500d41c555100c005802941c2264005001c01ca1030080c04050b40010801d800140400300c200b4100c03240241562410420b11a00207900c0c4502d41b068000811112080200e00440d83e03180214a1141c8042c800601110380003101000594010441075500c12a00313045504c8080c50b10340050000c2c0076144010007a40e15400404c5030411040c0b041110304100449007844801c1094150f074031254031402740e181044100c01005c030410040360042d60351201490b0300220789032200d0200502c16045489102e400c5036044003c034100b03050180c0b10f030301810341150140c81003008010990a581d44506850100300c415644000b03010048142c0c0800d107144500c1615280144c2004000d14020f100c0d000110960800c1c0d0b020000219400380c0502245c0e8410404222040c0c5902c80d40000e00001d0001600402d410310310104d44400496228109403290340c85c0c40807944001011524 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 504986115 1250 504984865 504984889
    0x15030f030403030e040f0e060702060a062102040621030f03020c0a170f18040b030d09030f03020c0d03121103070c061d010227030a0f0320070b0c010b 66
    0x80c0e00204400e00c00f20740302d0341600c004410090800700d02d1a1040b0380907011900b110603002800d4110348180110b040d81803103925044901007030300b8405242040e98951244221501c0c1042a144450b018800c5485980282d00201481c40d000d4044201c8000d001d8081148081e0450000d030702c0c400b24041d05c5011744265090401081d00078205068207039a00c000110f034401c161403560a007400303541601c0c0c0304040101185d000c1050110800c106003004d010544080030f2880d8420b07000402c880d130b0001c0c4c0c8030500e4001c881d00009180781e03050b51803c2c240c0c10702c10140003554000c404e17080004281604100711282642145000704902c01041107004020301080d56041c001400842d520780125585420400000b10301d03200d101c0b89240b54142403400c9034088e69520316010031000703036a501c0c0c4018022102c01c012007034000c5d060900300d0b540d0320845c06905a00040a00103034050144140104030100c40c641458001150101c40d03c0c0c00d070118098006050200c031f90f608044c0200200e0401c1820090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 504987365 1250 504986115 504986143
    0x301050f060d02040b04020a03020d1b0c0f11040606080105030d030c0e010e0a150c1b0602030f031806190b120d030e030d14180c1011030c0105010902031503 69
    0x61a00e8160801450040d0150b0030b07070744103032074101c581803d69592000313008002c0035450040e503800c0b81c604e04c00196540e45100c20001c21801060019075500500c0401180da03001c0d04130b0308125140c1c90401c0102503191141a0024075054011031140d400c01e0a06050f00c10440840c0c203400c0c804d80040301900d8001e60300c2d400044100c080441554004c8880c1910020000c1048070303160380301c0450900001c0343c5d4401c1000224969416001c0c0540c03506600c2d42d00c0203000c19008880e0a100000c2d64900c58110071403600131002001412080000001c0f04280c00c0708015a4642d041c0002042d814030000306c0b444801529110405003a85400380607910420007510142c5002c0c180190305500400a21a41c180b841c00104055140c2c40340500c140540d0b103800c65144091810a030080400c50791840c06500c800e94042c070b000c02e4031036a8080c3e50307030701c40465441c00c540113556100c000c5081d405407400d880c4e143d600780800881d82e00c079142c001d54441c650a03a11050f030201c2240030181c1e18246050511 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 504988615 1250 504987365 504987391
    0x61804020d110102150a0b01112103060409060f0f0f060501080412030b120d020c040c120b060405030a0f023606041107050c09061f0503090a080a080106080105030105 73
    0x10001402c00c400608040e405005440324020081c00d4443c0e45202107a400014503503a44054519603000702c040340e444140c0030000c004051442c000100605074118450252000c00b2001416903906d40e0800c41056601500c20310a003240005000c018144003450707000080d041400d4445600c0c840e07c42e11044880c16510091240c81d51b84420319106004140d000030151a071525803d59100d2080006402d42d41c000100f507011070054000b4101401100c2c041e1089040c0700e4124150380e48111881c42082032504000741521900303000441d584202c0d8010380d05401110001002d008501100101c2c55000344c5810001207031007845503994007820403100d14403810f41008890901c000344d81003648041c010380005144080100800d1035508002d030103c80550000030803c100e07090404600350440790944107618000780f8506480c0c000e00f90b011240c010042e022001031120242080f1403408503400c01034590f6100d0300c48400810b50744c000d010b4000450815400042c2500301446410300c20302c510a550 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 504989865 1250 504988615 504988639
    0x603070c110409050f03040906060f090b09010e220b03060f040f050a15050a0b0a03020622050607050a0c0e0603031603020c090906070f020f06060405040f0b0a0506180402 75
    0x510400711107400156000350b0340f5014000016010001c00d0340c021702c0e2000a40e207840c5429041002c1d50840c0e0000740402c00000b10450b03045400c501200151460190540c0e1115440301c0100e62221010fa52540c0c040c2010040112200c2e40010b640000400018140448031183c0140b61340c4180944442c600b001c0c03080001000301303107686520354240c0c2c0304900b5180d040a150710344ca045941e078001d000003036603901c0f414008070240c0340c86a15484a8180d41300c081040c5160000b44007030050010b91842c0c1c862414007004603e086000f44800381000801450b140d5650781000e41e80c614180301d085a801428480105203100820900ba2007000002c00842c64078202405c40a001080c9500441c00e40c410402d50328103603500c81d0441c1e4401c000e040020246407424441c0100401c1c0c00360254001d641001c901e501e02c0d900040b9800c2c3d8800c42c19070303004c6034075101c07403800f2030345040c0703505024001d07540080c20301c90303201600d802460080030100d40000f40d031007400c007240c00030701d00580d0025408504000a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 504991115 1250 504989865 504989873
    0xf030b0c090303040b030705250b0408030c1b0a120c200409020310200702030303041b03170705121206090601030b0301060f030c170d0507110607200603070c 69
    0x418180502a00f52810243e940c140c0c15680c0e00b0642e0450f0200713102041c0010150b9160765403503e136040c010510002a401c980342c076810b006000e040a4071080c4000001a03204580104a8299445150101e9140401039600d661075181da05000c540100e01d0070085051640b00f034080c0905240c1000f81617140c40c6d031901c0c0030302e4281c84044900d50010703110700202016a600b40300030b1019060041000c143c00744020100158a030f1905103519022006008074405a140002500c1e132251780a500c170001005071507914403038244030740d10050080f00391074461910f8420080c080c02e070342c82c403440485061404008001e1094003401c0706404c034100c6d43e000056418501100055040760040c140050172038032440109003034070b4064001e68070790000240c080041242014500000f4449007407140c2d03c0c521500700c20741e15045010000e0702000740108410301030001c0c400d015400220024074442d602c40f40c600d000f002c0d401150300d910718114080c410801c4942070080451b481449203591300a035444035582e0f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 504992365 1250 504991115 504991117
    0x90109140a020a03060e070c0b0709140d020f10090311030c18060f0406141f05120c0c03132904120c0f09020415110a0305030405240703060f030b0c 65
    0x3c280010580c0351400040c1030f90381d03245014010f2400da034424807002c600303040c08092000060400030411400250800005004916840c0c982408440d46048145c59000003a070701d000102d200341e805922191480382c01c035080402581100c0c46030010894000c805030402d5145e40410030440d40141d5a5503410000200c240251540418000d2850300d550480c0000300301100c1c00394000c1c050309080344441a50310303d854082819040c400c03584050310b0481310803000300f10340a00c3e034803c031020700b11201154408400c0c10903a004155248101c03034880d01074110203505015248a07600d22000c41c000318074609504400316540564810784003a140502c0d1441c102680040b0b00e005030344071500307040082010f4810010090041480d54000750311a81002c203288200903c2071040707001c1c00031392021010b5100c00030880c5030001da01420a41c1d00c83d074550030194109203100d55070041d02c0c40c441808800360a401c0701c1180c040c0c2c2e03895504104407a00c031030380c030ba1042000340030190640c1c10440009482e40c1c1004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 504993615 1250 504992365 504992377
    0x190201111e0c011d16052b0503030c040306050106020309030d1808030c030309060c040f05010309111206160507080f0313050d050d050c090d030f02011508070302090109140a02 77
    0x7a42c03611003080416400c680c00e01011389440754100540c81e0b51410200004035410343d1011a04441300e01d0040090f50700d61070f6080d809810b00082e07074201e00400c5a0503c6d00350b0350350000d09403640ea16000800e10241d40c0b0501089910328640000814040d2000050314800c06014004105d04071b00300304142c4507a0100042155120100e08020800070b0080c07001c2c0a00c402030100a58881c2080794005003441401000038000c448244810400038442d07000c0d0300100c440a00300090302410074241400100388000340103801002035030700c041340241c0004c1c0c5a0711a00c80603681c090118108103003219070b0f100302071010f03142a406000f407800030f00480005581000c52500d0749942404180d4400e8103107040d015114000c1203001c40c01983c0d0300801c0c0034840d40001c03004120780ca820034080016100c6004402c0c003404221482d54a200392500035031080c290540004a00014242c0e589030140d85c2d52041c0c00100c0c011050030000056594140c00f4000e2035031410ba2070724046685683e030039002500300c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 504994865 1250 504993615 504993667
    0x605041506031a1f120c080d02030703050906071a060906040c0e090c19181a040e060d020303040803040503010f060f03020d050a0611070317100b130b03070519020111 73
    0x905610f810510818000400404000c1740c10f03045a0340b030b030611091080c0998000c4030240c014048075a4150340c0441140c3c07440d0352508146481d0020f4001041c1e8901608030300402001d80d814411111000198280f842604100c0d20403840b40d8612041c401030f03403c080d40c10700120760351841c0f082d031500d8041c2d00a0f81c020030b0b08034494200001c207007840d2068503108108030041204161000c0503e4150f07950400030708a41810351141b800141d24a0b11244124884d480d0641194800700342142e807002c3c421a607084c1c000342100d4990340c0381c02c0c1c99606c81e84503208441c401c8d03107090080401c180c0d007401001c04a840250f80d8013030f1b0b44c3c99070302407140b00c9c00b05000c01c031024040d4030701c013100046061242c0c0d003070a18140802610b0300f621f03103005420040c203a40c19107803020041e001c000d0601d20044100007a510100c1000b921041c2c0c0902e001302004054006002c26030002c000c00040030b81c0310003e00070040c592050b4403070791a040e0b80180d080310164480451100810841c110481240d081080340780804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 504996115 1250 504994865 504994891
    0x1090e0a02030d030e150606030408030c070f03030e191a2805010302012607051e0301030f03030605090c0301030303020a110f0c01080a0608100b01020a020901030605041506031a 78
    0x403550000342051403250900703001c25070b60b4090010240040044011014107024080443e0408800145050200030f10051a8210000000b8003115000c03042d220b07815441a4070304081000391030b0113405003240b000c00c4000c5115809085c95410b1f5104501d00809800900c2c4102450030403000380950a4001d040c040c0001ca440f0400030f03000022003804511000d00c490008465040d803000511400303083d251003034081c0000040004250300104107039000151403c00c141d036400003582d00040500456204400700f0700104c000410321007040f0075518424480da80401944e80c0760030400030004000e81d80b450209506100520000b03000307900800b032300d10307181c05c0ca1420b481540c800c81d8584100301d082c4000c1030b0403a50703621402c1d58008050380d401c0420102e05006490600024035900c001e0b00141b00290358480002d05500c0c1d0081c880c6844e29074025000c0002586c59041503005408295011559480e0410007500420618070810040c0ca43c071080c0e02107034401c4800e10b8408004050030464010413 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 504997365 1250 504996115 504996133
    0x1090b09150d1a0603040201020303070c0c0503151005150a05210a020d0e0d0f051b010501060225050d020904020a210c0906050321041a0d1a010801090e 67
    0x900341d0041c186050142e000414204216183c422400c0c450f02956030181c1014030500005030780200c01d0b00e5025620b8a0906243e6055050440840103030b68006905030144203610060148400362451148e0040d000b480d1840d40d03941c0c11700040700070a0b03d00804001e01480841c030558881ca0003806411070f03180c0200c208480541c1300800460080d10042d03c80e076400140c079014401103000312040e404201014210043c01d950010b02907410b841e0422003001800503554a044564036880d41000c503a24008002568541d00080e64500020303c034001e9004003110700515450f184e41e483d909480018000f44400d12040d130901c150610090400c907407041a904020450290b0040b00c58041c49260225440300d044906009101400c5d0342c0040c181113042100601030358500082e9031700351070448290402c00d0703500302503203611500464100d21100205504090750421920000c1c0110034039100b0b0800002000762050110289403425907404074000d8401000300c03032a0f1b6440488050034800c19204501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 504998615 1250 504997365 504997399
    0x317090c041a010806040524130c2718050901020712021e01140115020a0501090506270703020f06041d010f12030e062b0c0e01050901090b09 62
    0x158032044100680d0580d080b4001580da44800c0550700041d0a881c1000b260520b280c4281001e902d180c0d800c0040340001c6054580d64841c00c00e4040d811800c1c1c14104040000350500030844203801404005403662603005552010452591400315108420040d1140d0b4240d0222805404020711071170072558248081c9001c90040c014a001280980e800340c0130011030481e1004100c241058000e10581c5482800c6650b544005500e5054810721140381448800c1d000d0200e1a090140100034025400c0644074804c115000070124011074000143c9402031300700340c208590f102111807120101e07900c00281000035041c00043c0c3c25542c50040c05042c0362507210301c1104420601400c000c0030507169140100203080b200e0b0b001c0d80152002c44803030500030b484d68600a00c0c50b10700c0d585542c801c11000403040014519004003e9034500255461800074144208540003013440200100101e2815039201e003156105030201c400c0380c6416101c803040281840f1060409030000e04245410240300d100b245444 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 504999865 1250 504998615 504998621
    0x3020f160504180b09160812181923010305061008040302030f0a110c01300b040c03020706140714180a08030c07120b011206061802120c070317090c04 66
    0x1088001c0042440103a01d0704010482520303075100304859042180d6001c0350314144811990b003000c0038080b0889003109d800004040c100e0001203014400a89a0002521028a0310303020340415007610728074007906894019400d8490840d90140d0201040345102c0c1e00900481d2035580143c041d00c100c03420b01e064800300c12096840700316404045000d4904c0c6500d070440c201f0982c1c40e48a000e192038044819202c007805c1c41140c0b01040c001d620303000d6001003024140103a001c0d0940360001441840340444011014000f98441142035440d941882c110281c000e04075501c45024216982d00e061501007040c07028003035a00980120140010800700d46002e9036a5448882c0c040c2c41d00c030004d140d9600d850000a4030300b894076404000320350412840380000c42c422030401c034110790940c00121060a568030340f0300014985c5400a49200c104102c10304080801d50b8040c0c90480c1c801100b203030103034464080780d203401c0c06000c600400140c54550100b145800040c015608041c0b10000c480b0004c00030390014050b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 505001115 1250 504999865 504999871
    0xd141203090a0212010c0503011206020d050c030601030b090705160f0b070503060306070801060206041103010207060501140a05040209030613020d2108060103051509090a06090f03020f160504180b 86
    0x6542c04004040c0540c074101e0020300c05490f12400800c409144008007a104e40414400c018200d00d100220740c003480300302d8040315a0650b140e0f600300060b01d800d200605982d04140d0b40c0c1030010346070400384034007410a610083d028804907100c2c141401c8000707480e030b000100200e0084030054048126000028a20035030701b80501c01640b40c42d600ea14050040c5441c124004003c0c0c4108640c03500100311654012942540241c1c108000d40b144008a0000c01e02904ca0a500108020300d0314000090484001e9580311481c01c044603800d50b07440d41c500400047c1d014500305a98980c01c044082100001d011124104e0184058918030b00c1da285500d8841004446403d0000282c00d0308080c4281d00307520440c0543d014500f400c08109604004402c2c0d140e4040f02101607008080c0d600100b04220820090041503076030007002800020340d580781c500303045080f400d811000f5108400c500d01030900003050b0700b18568200c0c0e88420740d0900d040200800340c18100f229000450745a94640041051034408500c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 505002365 1250 505001115 505001131
    0xf0a080303040b060d120f090312020106091b050d020705070312030c03200316022503021201051b0a0e040c020303060906060405180a060803040f0614090d141203 71
    0x144900d40b60400c0c000410707000748441d00c50f52100110100040301d4202018800105181554040b1018407003503602a015801c09010280c44862200c4200e605400c034000b500c041d04e40c2844001c2d04440c60b00c0c001070462002134049072003405402c0c49401c0130f901500361640500102c076011035403903c428000409912840b00000d40b14090a84415058041c488900546410340883d1068000b001e25860102400c091800000c0c2130100c51010320030002b1107070700410102c0c01c06881c0b002d454400120700d0f542c40224001d076001200c2402d4001c0c18170815100b0480412080800c0a80d4080914941e1100302030001b4007880f91108020b54507180308030b014451aa4008603aa810303c00c00700003404034002d014a00c191402c000c180144e403030301c90303140340d40742c03a070350628040368490f01070702409482d0580001e01b062101041c0014040728070003480c8116022a196026100415483e08419100304406c40303821030030b034032400000101c59445000045429606580e41d580014041915079030094503c0300d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 505003615 1250 505002365 505002367
    0x20c0d080d02070305042102060d180c1409011e0612021201170c040507050a03020705010902090a051e16052b06090606110714060c010905150a18110f0a0803 69
    0x111810082c4101d103611103c3c0940700d4000c10495500042c0b9030303c10959807444842d120401481d2809046110761a80e40c0d00240c00425151242370f80008079042d07602651145143c100000381e00b0180f610710464121015002e00a02400c010044d10000700c0a04021661a42081600320070802c0660340340c0139014001411400c0081190100d1410895180251060345410148044140c208088440700400ca003805602c030300e402e04210b401003403268006074000c03d0f82000c0000c126001d03800710707200d810b07402c19140c1800400d07040ca0162601c121094480014601d00442990303000c2c201078004034845541501340d005544088020040d60048009030260f00d4243c00d004880d918003505001d0001c43c034008490f903502c0520f055a4003102d1040340c1211a48c0c0442c082c1588070207003122011031104000340302d1005a403801d246d482290b404028014860b510203d80d01d1070007400b03500e5480011403005a60700d006602c8054440c0b000454613680945c000840c40c402c3e0321400c62240040201034091 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 505004865 1250 505003615 505003619
    0x2120a0c020606030601030b0a0e060f0f0106020f0327040f06180b06160528050d09030f03080c0d090c030231091506080d1707020c0d080d0207030504 66
    0x20190368140038036806640002c400c00c00d040e107002515604603074000307101a46940796802120300030600b0400c2d0354958040d400402400010704a0014095148504010300076a41c804049817120749410a540035034204002c0c0705d04001c400c040c4c080350444a51100c0311050500ea000508071850500c00e010025100d00003084088006040321401c99036440703091040941000004146206d81e940505c0421380c46100603003031010420540c07084d44548110b200d034100c40300300440003028400c0000c8442d0302c103c1ca041250703640310f545580e084130380c02183d40c1c83d141c00c1994207a8050500a0180d50107150600004021104600a8410303050050000c81d14940c21401802209055144034420f6458090703840c001c0405221400800d040641000003000d0b06c1d02e29211034080c803131480c0d411060f403c00c071000c00c814001052008064600361143ea8068603071180012494030100c1c0e00d10301613045180250b440d82810040149802c0c40362802c0e510304211203603c1030480e01700c1181a800201c01082c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 505006115 1250 505004865 505004881
    0x203190501180f0c05041707080a08030a05010603090f080c16170606030f070b0c010b13020c1e0615120d0801050a120b040f0f0b0f150f09180f010212 66
    0x10306000032020303e60a01c1014108072010300749103d9845071140100d0750ba042d03540f880105100000242c8101010340c0c0b100d40050a00c0d1055401c00e9500c808a64500030001803103074000d202c0c2d0300c00560300842c11000d10183d619080e846422426141c440b900884c0500360f958064900e0000c090311408002c1c400210107192400c3c600080240300d18000d0b8850440400c2e103140024031001100d0f16003800b40c4e07403050415070090141c5a8000d20f42e0300116444000c4002d07404a0b00900341c104004005c4508140404418080304070300080c0402e61a049a0049210328204140110f41c5d0b401c0500401d100c110380450b011b103000b0181d00c52100160405005111925043c04080014550a2010001c3e01c140d6200c00c6210315002e40014038250582d19801c1c20444201e0344101184d801011203480b91034046501c802c0c0c024201d515126061070034051701142e00e861040070000740805003502986903038941e801c070185950028951018459408959a03101c0309000806046080070b015409a00300540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 505007365 1250 505006115 505006121
    0x1060f020106170a0b04080c060901091230060506030405030403140d02030324060a030615031505040209031501091b080114130e03121f080a06020319050118 69
    0x24101c0d407000140c0c40e09008000007402d006045d04070b8951011500d407850100018810006d0308100c60144804100350103070103500c00d040c11400748039640106001c0340300c2103880102d19054019802c200d04195403d46011088080030200059400110b075916074000400ca6001100c00311400d9000103000d2081180826110700b5005032400102107461061034003030b440340801448484000e0740c0c024418004039003000c2c10321001d000039106580d40d04c0c4190300107001d0103082c004c0441c0040800c030441c900600c170b4820454a414141d429003041400d0000304800795100308541a81885040310024502003a0f01c8298001c0640c401d000802150213840505004443da20000501c00090010000102c3c0d0800c624034501e000c03038400b01d44282c06500c4400034051846040160b1001103600d000604a40b00140e02950380d030799150381080d0359543d204c401d4640300e00881d109904a03101600c00580c458001d160854990340300c03900e62903090f001d400300301c5000360b010000f00440d01103100c14100d2144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 505008615 1250 505007365 505007369
    0xf0f0908041802030103020d03030b0d02060d0f060b040f060507020301060302151c110412030c14031309021e030a06082a0f2202070602030c21010807060309140601060f020106 77
    0x2e44c190345c9035400143c280c81c0560005000e00d6181c0c2d030301900d19594141d00d00066940204059111000b840e0070400038000c4071820300c80300c1d141401c04220a02c0002c1540e00b250b07610a640d0a00b00e0401718215026081030804981540d07c80f0008801640c0d204146086a100c44121586400140045641071900000342694031450182001c103408043c00880d01600c00601030b108440c42146012a1241c580c400090031690302c4540c4407440c41c1d00840201100c8150580d400e00b0303652282c0c40c0704201d100d2034401b5104e8100c403140b0f1030140100c880140d54429492500064050383e5200f2550400d90350044040b07c1485003990b4040081306d003900341280c05819070700d80010205100200e91480c41102a074280c03d22a0203194070a0201a0100c6000070b85c0000107548a042ca5140b40d10b882d0420708c040641c4c0c0e1083c1c10503c005244c2c40080c40e0490708a05d00418a840ca0400103800825500e2016074208015074a1103400400030001d4034000c00450383d544107190400a0001e084804079 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 505009865 1250 505008615 505008659
    0x6010b0301030b010e040305220519122a031104111809090a050714030d05071208040c050402131a0405010507230d020c0306010e09100f0f090804 64
    0x6000502c080390182a0550549080000c0018181c4503801d06503818095040f5202c4070050041c1c01c0d400303404800c00800c0440c0e01c140e42503200720b540c42011a210140c1406400d03401c040b00383c0002d007ca00c0302900c1d006c05913044001020402c0e1801145000c0200c0d0ba0000e0724200e01038442140c49080500c80c802c0140800c5002c241403580c000380c413a0b855414468034074400c1482c100801c003c05400d100d01014640c0c0300c02100c40c090381e21103040c8100c0200000061080c01170644080150707005204483c9842c0e880300220035041030707180301540c040ca0081c2042c0c2c0c0906088a0100d01a22240f00820403c40b41c0800000e401e890065900c01680b0310b40d41e015040203042c001001141d80283c107407140c05d41c1c00340d100b0074180844020740100c40d45c49908202244600902406042d402040c0325032164016020b59940d03a0f00d50311603c3c005542a648540725512282c80017039140d8bc030f58066510290100070102c2d03204641c0c0c100c2d80c183ca41c031030003e59015100280801008001024881e814026 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 505011115 1250 505009865 505009867
    0x61e191409060105090111030d0e100e0312040311030f07030e0f030304051003050a0908040f14010f0827030a0201150e060603010501110a080706020c01140108250e070c02010206010b 80
    0x101d40c0c0000c007136000700da1a043c140045a00400c480c100240141d6110b501c030503401304011024254031a69540f601002d681c0355920301941c840c2c41c0f08022080f211a448074000004458490303980864001003407601c404002d00080c40700d8141c008500d0010054580250b83e04100e00c00310000700300c0c45080da841d81c0c600c60b84c42044100b00c01d0f21249548044c1e0f0129080004440ea510103901d4098598010010208100014007040101f001075010080e90b40c03403011001d01c2000d180040d030311207034403e200c0d40101d4803040000310ba15405103103e458a001c1c44902c407214416001416145030071695a400242c1d45032602080201803c5913440300810340c0c60010101414114082541403106004560400007028400309000c081000a0f0752690752005100e603454509090820094212500c0070340740d5404c1c50608a150074441559905071403c1e2005801081000481c0354040e9105042c00900080900000955440b0028440c0d200786d131181c4989842011a1000a00781801604001030580e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 505012365 1250 505011115 505011121
    0x60108090a05100b01020a0606060201140a050c0319232208160c0b041818110906040b030115050111120904020d0e1e0c01030204030506061e191409 65
    0x4400180f080c00d407220000c00080e01c02003140100d003440c500d00c20140007681006000100154154484042405480381d0280240c454900c900b0940d1415142c1e42c09001007071010a10950210305100880880401c0010300c2148a0242c0c01400d844030000c08105403115007000f42c45114082c40c10204c40b070145419540e0800d43d500c0c804280a030381401101c01350040030307542c20040c180d00c40c0c401030820a20703130079260f940d9808200043c00d0900301100d03c2a062244d000040001c4035403d68415a00445081119080e4403d01c2540e1000a0203107034400c1d00c039050250341c1d44080c4103111010750b40809402c20941002c0016043e80508408540c0355400030350840342e044181010b58180c000b04480140c1e8560401a01d00060718078207000705d0341c90141c20143e40e560301c80e02058030786142d80305090340d2a40f515603005404038001e5200250440c0c02031070014100d8600b04407100c1c1c00e5020500110b0302500c6070008034040c96014081c1c203060758560744043c00001c6480302021a80b10003251031583e145 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 505013615 1250 505012365 505012373
    0x907050d0816050f0a05060601021b0d030c150207140f030a08130321020304020a0905010635040f060b100c06020d060918020a090c0915050705060f060108090a 70
    0x210640001d1801e040700d0301e000b001002020301c00c40203580380b0791084400226081c144661684016620079025208442800302d48000c0b000c0940b070717000c2004250007011249038800b41e0b4800090001210060307010741c003203003d040961000e846030b00d0017000390b880c00040103003186190991a0440c0c155561041c01054101030340300b0f03013003903202031110414034a01d20070340b03801e41c0c1c8407083c0340310b001c268440e00492040c024082d5000e940700324000c891600c0300d240d43d40d40d080115130f020b015000000b800c00c04008858a0a0b40344103411031078007c2599100f02d140d0200000a60042d038080ba203451502a900087c0a8140035810305046c080350010380d0401e103400c0c0901840300865005100c55000b064445807240d1310340c4071200070411000103120202c44c03500741256825500b0004c0341304000054012500303110501c034080080503203032075155030f8600300180c036811082c528100be801c0000030004200010300078081640034a20320004c03255507003007610001d80400002000850981e000401c108081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 505014865 1250 505013615 505013617
    0x8010b030c07030f02011401030b0f0a05040302030405011407120906140301080303010608071205040c0f0608100302011b050d03020910030203130305031005060c100506010c050c0f0402160b0907050d08 88
    0x86030301d41000510031040b0001030303025047d180d86502c0c01d1001c0000010503c00510107613031141e40c0f02605010541d40c0c01071400304950050b0b501500581c01804144105e500a10411005410340400c450804d205942e0f034102d5400d01c0305a03240021040c0c4000c0200b99002071001907500c801e0500c0c24159814007400d9a03a9000500c21103041010050128071814041d802c1901e541a0904084c0721a20306800c101403950150310940c07180c01030700b5400042140c491004180280c0c83c450f1201c1c0c400b403654004482d004031240c0091a506079500f458000960300700254140e20480351400b58951441030300b040194000e402d007510505004004000c64002a10800c82d106039160412503281d403522900e015800707100da0440d5410800000301c40f41c0e042d200240e00c0ca0150703100c2c1424025966810300454000c40b004800805aa02c030701802e52840c903100d10a41d8103100058001070600c0c0503520350b4001039002c16010340b81c1e01695011f1000e17024043c0040701c0604070640d20340d00c80d000302d070740c6000107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 505016115 1250 505014865 505014877
    0x6060207030b060f010504082a0301090302250b1606060f0303021905010f0f0b0901060207050603370b04050702070b04140a03021914030d0f030513081908010b030c 72
    0x8202041c2c03135403020903030003001601c3c0542480400c0754480041d0300d00e00c074218080390f0242c00800c0e2511060030100e1030305001d030f07504060341503000c2d0241e10f01e1480c03e56081840321259410700ca181034000b040341c1c400040a071401ca111901c4840b2503011a003000f00444080790081c00e1600840f11091001c42e40000e10704113032102940e01421901c1c15070900d580100000c0c022603207242e0900403041d018400c2c030380214002d0702c0100c030855202c0e68cc400080e0b0365220b440c0704140d080344042c000075600c1c1541008640c4019040d4034828280947c507900003942074001515040707600d90b02c1c00c8140e114141403160561028050004010060400d600c0c42e81600451040d034010411070600500702d0313160144a5002198050302d03c83c0001c202400100c4840352502030302e80b0b030044000043d00e0902c0c0004042000205a40f81c82ca0b61501d1074800300e02400c1c0042201c16642034071001c0c5000911030100815500c0050000c030a00c411825000800502d41139001d00380a08090050101c281c11010480349 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 505017365 1250 505016115 505016119
    0x80105090714090f03030a09090b04200708040e0403050705010509300c01020301030c031e0201050307121506030e0d030615030507020a0b0c09091f2d030501020d06060207030b06 78
    0x43c03181d10100025080c64480041581c150101041601c8250b0b04103c1403020b49145040600848443d2001d200172078170401c608003121b410320740104801d80054001060020700a901d51481d094845144105030320042d5811800210001000000d0013800e10035a5001800782c400780c5145075062442c0800052035510311084681c4000c4508502043c0c3d03002c455013410644002d40d10ba60356402c2107030b18503a603840b040d0391072400030b02c4002000f1050072613160300a40c1610b850303040d5218958100c44c1243c0c1c078080301a0b2180d940c08100c1d4102c042d00c00c3c03040184403a44d03011a4004407142c0e01800c0c0383c0d44201c00814541000410700143e5128404d40f92400020300d4005419910410103d151060f00d03003000c3c101d100444c1c1031062419140c4018001031030180c41ea26036586070340c450b44012015401c09c80c160744052410901c40300320300245805000d5286050800c4001801d8040070502510354001c0701d42d41e600040c0403000c0042801500c008045030f00290061a20b1501d522910b6480248803078 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 505018615 1250 505017365 505017367
    0x403060b090721060e091c09120f020a08060405061f2105070519030303270204091104020d0905061f0e1306021b0c1210110c031306080105090714 64
    0x500c44042c0350320410041082c09a40d00c2d0a01b4880f64a0740c88200081002907500350750300400fa09203000f41c100c0000c98040c0e2000301c4401d202d5840e6000c60f40b910007006c0b6030000781d40c0307800601d604041000c81d0203603010b032003e06010b0501c28010b49800305244201c035460305d0050401c00c200451001448028a100300440d40200c1041c549070782010f8003900aaa805500455290800c3e414224150b055034440c1c1c408010000c11017801102020241000300c060011900700701b4018201600302d0007a03184100c2d6404003250005000800741c0c2c120619405809030340c0c146036003d106007040360079004041c8010003100f40f0f03c1c0000c841c0c03110910380a02440452118003203848200c1c0c4a071031181d09a0400000c5490351030703246002076140c0314501038200c54441c01e60421118905031004808080018009105680c451400c1401600b1f0542441c4550b0800f4051030381c0401c014002840e401194140c66450780d8100b2034080c0442c072060b00018003030fa181c442001400b52704012041c40c0700e09080510313 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 505019865 1250 505018615 505018667
    0xf060903010906090c0e0c18102c090a11030402060304031103040902070506240d020d0215040509070c050303040b09160e09120f040b070f050d050403060b0907 70
    0x803902502420304002c1910b883c2081500921204205507400d40311519400d54154803140707004110790280010360300c540b024584814031031b4031f801e07400c004260800b401d10441d41e0300c02e17603260303d252425600714804015015000071524a04800b109500801070102040b0001c0c1c2440c460310a03000c002c01c000c0c01164000b005c030b02410300503854199034021802c204c9c0c0e0340787d0f221601c0e00d002e90000a4125003500c113543c0402d03e500c0c0306001541e1103440b0301682d106001d082c04208880109001c0013070341c21840c0f4505240150310307040c5407801e05005d80132405070f4403440c140510084041c0100040e081042442c1420009040841283e804c83d41151a0307a003241c6071581c1503400d15507041c054080c42520848009055030404131011701c00c6c1100000d58034100c000e280d4121b0710780301d8200c0074091010108030030310042101030081c091041c06051044501d54095503250f1501d80300f910348034089000402c0030410002d59002d83c0c00368941c107442c040700e142000b240190440d0340d800066110400100e10f1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 505021115 1250 505019865 505019869
    0x114040e01030f02060f040312110105090d050a0e031e0d0c080d020d0605040212090610030c03200312031f154a04020304030f050a020c0405330f0609 66
    0x540d401b4012114003280d90380d903249050401403819040c140040390301e4546050004506110b220b203e190307500003800906c031058400b210181d00040c54002800748123201240c0310344040100c000c140f09110300200c1150103030400d40d0304d841d015001d8a000c2000ca03006c0c030000101e006d0b0030365520712000c6d00050707150080020b100cbc0141415400c441d401510100c0d610b1518400485801d008104900035580300d600c800d90340300c000044501024000400c40203042000806100e00c11243c4852141560340c4a5900c0c40000c1c00c145a207898090148400b0043c410f41802c0c0412104031503400c1090321840d40d2a04400d42002ea0b5640105010311028034004001142c003640c03031480001000031001c41000701d00010311880b0b00300c00c1c130300b040342e141240c130850705800d1038800c8902880e056102c00c00ca0b03805540040782c1c1c950112764690210300a080d030211441c0c0b1180161402052000300680a2519443c00c00502e008101c0c034101d01001c0b040440103150700c5d020000400c99074142c1d5140eaa441807000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 505022365 1250 505021115 505021117
    0xa0b1b0412080708030c1306140f180a0e040c050307060f050307020705040e1006050906010816022103070201150e0a090c0b1b3007031107140114040e01030f0206 71
    0x1501414044c000000c1009061081d40200490000c10703a060142603201d10088510035040840756414480820070702c024401110050903080c10001c07014050300030440080b880c2c070308083d440300d400080c202e410f100c1003010701d016001c040d04d000d4000701185032600c100100304040000425041c8280000401e400f10300c240a80f802410000d0410320400301d5410300a596441e101080941d11440c01101042914203149140e0252005139210301c0252642080384405240c95034983d000c0d8440d40f001281108004c1414880c56102c1d080115144c0c41c01c804064207503003110b005042000155082408a0111080744580090b070300e410000d000040c80c40e1030040740c8110703003203a084100003040c0c1044c0c200340a10784e241406980d405440e8540e108540c0b81c064440c0000707400800c2d4808024442c00400e200d005801124000c0c42c2c1011812030003a00700d42001a2a04080404042034001905130750300144031010402c20400c1d8203252a16241001d1728900042c00018a016504407401082d55501c4c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 505023615 1250 505022365 505022377
    0x1090c0c030c1b061215050a0308211504110c0d0e010c08040807060e01081315020d14090c010f1704030c15060509100b1209010f06080a0b1b041208 65
    0x104103c1e050310740301c2002500310001c0c94a002021420103550302552400c500d5801e08031040900358000b203d0840d41c4100c0d041d00501c43c070380c1c50250128402101621408032860282c5000c80f08104070810180901c029a0401480d00b81a044e0030030802c48959000210402441e440b850300700b10600c2e50a0040720b0110107007502411000004c00e002c21441c101003600b06c1210750075101c1c6120115a00e005403020300c0200c1380c108a1032000700b2503201140c0c1c40150701402000310400185422000d8040d51304a80000310561210282c2d03000308018107004005640d1480400d0074490f90b500300c51200206110342da141c0344803002540e10301040401d03014061321402c0e25407009825900f0380c33002003a180200b5440c07150364455a002400700e40700741c00c1507099070140d5945226807031510400f03500c556015880a8940300301596101c0790f0301c2c0c0c0c543d4036104000c05003134100040d204141c0329091181140340082c00605c0c4546a1900041c0386a050314212030440f01c00c55464030000d1014140011140114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 505024865 1250 505023615 505023653
    0x702040f06150216080f03040308030403031509141f0317210906060409151a0a06020c120d080105130905120702031c080105061303020a090b030601090c0c030c 70
    0x102c507810009a0b00407640e032066400d551a183c207100d640b40c00e503d03030b1003002e10550103054100304000d00115166000460f03000e80a410041070028282030588040491580500301c469075990b0340050100343c000e0203d411072903000051015aa81414645504140f440700500404070886481c2c0d5650301402900d1400c840d100c44200b4083c502d40100d82d0307001c42103c0079016400358070001a0f00340f0301842843c40c0e00e5042103400400d220103501143c0104040407803a44003421044401840c0c0d995048500060242540907007002d03004c01c018032084408150000c078058110740e12000c807150780952502d046800032a5080c1c041030320fa560950091410090242c064010710f001c1400d4407600c0c0000701500c61013a81280c0a4410710f1414442068004201c4c00020b0100c000411a0345010006051000d0311291026a1190784e43c2c0000c9401c45280c1c408210103445011a04c40c6d86030500c0524010440541c040c0860400da0310010104407000344000d00340011685881c082c0949010050480f2543e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 505026115 1250 505024865 505024889
    0x1713020102010905061627270903030204180204080d081b07032105092a040f0f0b120d0c08120f040b150a140607080a0503040c0f03080702040f06 64
    0x821681c2055041208803904007182c041e103c0e210340c040e06a811307000e06d44944c03814031a4032400c0c20b4148c43e01720b503641210b00c00380e800386c4044400703500e5074032850284904c01e480c01a80c030361420301001c004e65405030b12045180c0c8148030401c0612170205c1d007546822068500900b842d03031500035003081c1400400110700714841c049040d004046d0440f062104030030120000d40e0340100b046214005641007156012220b4100c5a000640303149459000c401013400e00748600c169040ca40d010404030740c001001c00d0b00c065111a00a40c61002a11542c0074001082e80d002d41c1d0080c0e41e01140360380b080c0300241c842c1040804503c4509010205040c0d0f4078010b18880c540e66a0309000810744e0350450162000d0360314212803070108000001f200c1d0018180c0318060125007606e480d240340c8a031a01c0c81200d440d9003182041001500240e00d8800406e8250350680b81d040d26420f06081c103102485907908801d42a0440110500200d10644240c1d809154100c07004140d42c2020003901d0040e0200c1d9104880c0b00c0c07a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 505027365 1250 505026115 505026121
    0x14131e0f0915031b050102120313022101110d0b03150408030c1b010b090a0e0a1b0f080a0c150c140f0102030a0b0415060c140f100606030c171302010201090506 70
    0x2c01d001e680c1203417400d81c22101190000e0310300400d80d1005031407441c02075207144000300060500090740c0310032125001e40114031000c4a0b9010303081d200155900c604d24074000030060000c0fa010300c98005000001d0300140300c10440d40720034007039043c0060400b0349403420203c006000c0483c0d03541101c0540c1003821403641e11050b90717a070305800782c40c2c01c1410520503c0401c0c001000c40c50140f00d810503000a8038001d1110505e1074451644050007d0070031510441c1581d00890800300b002c0e140300040482d54028020032010741031150010243da044050f9114a5000450410341e000440c80c2226030000030919803581c40604a034074040080a10782034650000c0104401030b88a07034004611070100361400d01c9001032400c3c41d0051841240a080041a18600c41c4408a6500c00d10403d82088203811200400c070780344941490b046855a40440c0036071605024480f059040c00303030000a40c2507060244040b40880496804001c0007469801e20700b0000005005581c400d4200f40b2280d9003140958145013 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 505028615 1250 505027365 505027403
    0x609030715091203092901050d0215030907030203060a150603020a020c09010810061d0703090302070906030c03150203070207090f140c090f09070804060c14131e0f091503 75
    0x5c40000801d4501000320300710000d62a4400841620071881c24201035a5030703003130a0401035480c9071894180c0c0c001411030a40c11002d109540298051001c560040c03000b14a11710405140940080c004680a800e02d510b16201006c550719807c142c0740e40341000740c1c8401d60010b04903e41b2805980959000f402c0e8400050080c00108248080c2051b00205110340d82c0c907069258103040c0c00c0340301407c0d007110000005408904c280d1020b04030314401c0c07040e01e0015175500c84403426181c49030404e403880c01d09a6020000c001d20001070000702918401c0c29400c610b05250042c1d111940340c412002182d413944441ca41c1d0300265481401c440c1035410214469082811002d40a60040d5410034020080220507140a2410500705032003540705a56034042c6aa0f103984c1c0704090020740e01d420051241070951180e01d4140b1101600340390300780c82c075508100c0d8a051740b240c0061810b00040d61404100d1207083c048010040c07200c2017a03d2410303034042640b409540d0596000c4000b03600280202d116145400162 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 505029865 1250 505028615 505028621
    0x60f12060f24150a0c081b010b042906040801240f05090c0706060e010b0d0b040606020a0b150306160305010b04060804060b1f03020703020105090609030715091203 72
    0x2d40c4480c080399100d642c0c1e9040c03400c9000310300200c0340d4000c2d0455514540790000000070000c640c030301d1030704442440080d5211001074100b400d02120320091214484000803003403041081040003183c0074040b4552010816150b424003840d0349050300001c1915140c00d441e110115070040041e00000c012442031111000701d0243d46000342421075921400006501030108041c0042d11030050443d06140c5401c4440e0841e984081021500c1719220840000c40f00c80207100c0394000c0c04881e8103a59904031000c10300b002c59940e041014820303031500d1000c0c80360540c00205442e0b03485e800004820b03961191601076010342100768a03035500d03101d242c0030815804540710702d541e1002611f0b101030107507907250400340245008500560000400a400207004107482e50041e0010040180c054001201d9403820700740415014020800421340000e00c002c10594244074403a0701034002005820a03017000404240c80344100d980203013000c0814a00c0c1009404a40d010a401e0f80d444510051134560b007000160107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 505031115 1250 505029865 505029871
    0x507021c091403010c081f0906061205090f0d0c080909100510021b31061401020a1203020307210501140d02010f110c0603040b0a0b011106060f12060f 66
    0x714441c1c200b1204858101401303070410340300d00c036141d54000782c0e114404a034908081690300243d00f07034504800559401c00d07104080c0500206d0390794020b602881d0345003c003138482c05401a03100e5401a5418240500c0103d41001c2e00f004520746104030800c00e04103080b0500840d80d030594028000c60902c00c00800070240350084a405903291603240412440a1342ca070750741c02400301c4c2c2200718484071802d503103082906c0c40340800d032650b41d00c460701005d061561b00e401040c08107003802e2070340d9420500240300002810340e1161002d00c01844c0da10391680d608081403901400304800d0bd60048042100503001e80e5001440c01d00030310303203540401e03140300822010300402e11440485032040004c1312407908007440301c0704140b82c0603166041e65044400d012074544528201c00412805014881e9645681300c030002c6020340c0c044c4507841014241400010202d4001940146c140711401e0212030004a000c16150303840345003201c541082406190114107040444501b2115038040c2c101004132444c124006940 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 505032365 1250 505031115 505031129
    0x20f0c16060207120609060c02060a0b06071e02030106030b0c090a0f08210f0703021f020a080a230f0406050117030403062a09090b1906030507021c09 66
    0x250485811409500c415400e009410060300903035014070480046645042c819845a030000a1030f50040e01c44408503112a01c520005030010701c01d004501c0010b000c0c0b013003400303c00ca03070480c41e10a480d92072600c07541e94917003058003007070050100805655080d4003d00c02150002c5560b400c91400ca40b50810660249000c688a51903803000801c1003210003044400f92804580104460310b241d8141c00c201030351890328002600c0040003465488401d03e006404500c2c03013500180402840400c40c00c130240d013900742c40c2034131500c1400031a000540c0120501e41081414500254040c1c0c0d802e8050004506a5200300d2000c0345501808507205440180714171988c054002089aa600c4803250b202c1c0b122244541e49966000380001c0c00881c07950340c0003104941820304201072500444041032040310003d86030801041002004100411543c000c4101d2000100c038a4040766224000c1c4039111001070080b6000c040e517a2001a2045008000d003144210403c00e0094000c403034845c0045c034901003405a00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 505033615 1250 505032365 505032373
    0x40510060b03040803010302040902030c03070807050324010b18060703170a09081819030b07090801060510121d070501090503061e04020123280c060c1101020f0c 71
    0x506000c41c0c60590340541e5100d070000d03155034a10f400308406030000200581c2e040c001c406a548050340c00300031840041406e8400f40c003a05190000701800d000300314080380c0d0080d035603400040351281e006c44102c1c15214014000c1d81c031050020118010043c0e030040081e00a80c0004018007456041000005500b040c8102086141c0d60388c0c200d1400c3c0e03014244014480b800038090000c000303040031150880e5070750140805000c4088076207081e1490310365501c10b5652030040400d01a219038401408009022000d000340840391804010540f9401a00962020490b0f03458000150b10607039045082d24100c125444050b504280718060781700ca44030b02c1880d010034842c074000105030401040300303485200709801090445503407100f00141c0010040089041140031340d56110a40441d13028039584199485c44c20361240071190388038486000c404d035201c0c4401c42c0351404020065002910003c042d900c02800304802034051030589080750710941c03000441d400415040304101d8154082c001c01034042e0121 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 505034865 1250 505033615 505033619
    0x31e0702040b2d0d0605150a08070303120f0608012c15060603040302030c0f01060305061521030d0204060816090503060a020a02390108010f1e0e04051006 68
    0x811034014a4100400800b208802007410100920f6080d50744040d01d0302035a0403480e900d00b000c44104a07031800e80f4510a030a03034a41400e2028200d00076064a400034900d6a003183c402822690500c50b1404506440b01c40283da5a4410f810103030062000b170740244845501c804500c4041100d800030707042c0811100c0c803490702c0c03640001001b80200040390502d45e03080c2c460109000300755000a20076070030343c4010018281c02d02c2080000f90022408000001071190552401ca401e1400107403490303044a59480500c1c0c0c69594400b0242608801c0b55540b514407404600d045055000d0880320010003480420002241c60f08045224410b1039007200c06070700e0701c91102083d510f40702a4099a030301980128005030080b0b100343c0c000c0041c0c00103801140c0b012901c800040c0780e061503c02c650300300d0140640740400c02c491030745c3c41820806400d007407190b003940c10402203095038105403140703030480d510409010003401c01700c0d04070202610060580c0f01c42483c00c0d0031301d65500e03044144a807101a24200340 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 505035971 1106 505034865 505034869
    0x8010b09040905030f0f072f0d050a120c03020601121208040609211e0f0c08091f09120803070f03020d050106030506010314061809031e0702040b 64
    0x703c41c0c7d44400500d480f00c191000a420720708007409003009a45c041ba00e114030305049500680e01b5600d02c1030a42091031030400081c03000b40c0082140b4800804151340003000e403441c18025001c40d28942d076550740d0902100d0360b402000c0c2a42e1461680c1c2c440540c4030b40c03a0030790490302400020511140c152100f4101c035046070100d40303a4a0360b50380c00d013480e6504041c04124080b0380d4140d00000101d00e8602600345030310070381c041c010080210141010841c1c140191202c1040240025022041d541241c203c0350340c100030401c0101300301c0000003600030203030084a04403d90100046096854218042c0e03011450b42d003a503000d041c0c00380b02c502544900d511440c0d0080403c1c4d82e0124440c1814400076003101c00b51039400c10f80c004142c04009058881c00100d20000d9141d106002156542880c024298019810000b40303a1a480280080e4500c580010b400e0581c0200e404102c1e01c006113007 = true := by decide +kernel

theorem cover : BRFrame.Cov 504856115 505035971 := by
  have h0 := BRFrame.cov_init 504856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 504856115 ≤ n) (h2 : n < 505035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
