-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5447
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:53:49.973139+00:00
-- url     : https://prove2.me/submissions/b7b72702-aeca-44c3-824b-1cc8caa1e1e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 979496402 ≤ n < 979676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 979497652 1250 979496402 979496461
    0x20f07030b0a020c0d180e061302030c04080a03080411062a070317030a0c05190e010c020310050403090501140d05180609010c0315050f09100f06020c120105 69
    0x1440102e83c3c1150000c07074518080d40d05c01449030000400d44101d501c0e08041040380c10304041074224080300c00500524006004220080d05243c605000e07400040821a40042c24080000c04030b01c01d02c0682c0310b00d842940da12802e441c20b450402409200c0440981c0165028400c10090390224064200800820b8410541400300d401c4440d00d040d810350401808001e0f8120122454481c110285011354000c4905006404c820041180c45004030504518101d0902440109150055003081941841071401e40c806040540200c0d00e001c41d40090200c0b601d41e140c04000070325901c080044094a42460410b044005094807001d080c0140c0d11000d0107555540040b4105ea151f56100e500030106240950f2000c0c540300070040c1c020899240c0344000310b81000390344d55008100411010541e100100402e4001c01d421050060504004200801c1c6601660001c11800d00c0c80e4450402000700e44e00800c032200d03050081c0700311070002142243d03060b8184814407404210041d1501548540c00800380e9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 979498902 1250 979497652 979497661
    0x150b1c0905010b03070b0408100b13050a060f1203021c0c0b0c0c0a23010603020d060c030b060c01020c0f0708070b0f0d0501060f0f080f071412070c030807020f07030b 73
    0x18010310f8050320f45549481800ca000a109410402400442da0340000f078421181c0f011003041e069480c820181d69009044402c0038404541940c0100d030002d521090000e1059243c3c094403406984540110155800305100b10003056410000e5003450326444400543c81800384402800c40f140452004065410f8640001c440f10351400640e0350006000d03049408044403030a0401c007030a5900c000011000a00b410850545d1050090b101102d5001d051601d101e582038a48000410482640008060300c03800ca81041350388000140c00d0f841083c400040c1d881324240c41c124907002c074180031201c0d1030b04801c000b001030f524003041500c111405071102a070b03180210b00b402c1949d0711420000203002460324002042040d07001100c0302ca00106910741880035503500205540e01034040740c43c152984012000118014480c00c141c00ca16050310842c6400c0107208009070103400c10072178200002910b1a0209424035522690701c03500300c1018000ba0011032001042d0b95124041030001814481d030490115 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 979500152 1250 979498902 979498913
    0x605010e13020d2408060c0a0305091614040f09020306012606010608010303080606070b071b0812040b011d01030b100302120a02091f09180b0a150b1c09 67
    0x541108101d80c2e82041300c2c501180ca00380042554108506103101c4259000c82d000400040f8540034180e0706070b201c1d0500020460850151000034480751740340c001d10f00c0b810060000b102041000e809840d03c400c0c0d412007944140001c03100d8914034400e4035402c2452910250701c0102d552815103484495040c2d14142e580c011800c0381c9000e8000094601c152000042c120740c0c0607080c0c5041ea40710fa80e81d8511603d42904101d0980996807015004603d80746c0401c000740e0044510110200c0314084c000740d8440c26444001c02600003949141d0602445d804210800a210800a02500c015140c3c50705a50398841036450011741400024201510040410314109160240da00155401040b2000040c2480032013521008160012401034003407101103903012198000c001c0f150000c1c1c015141900f854100038070007400f0072a16420103030344810a03860100b0300c031440861043c0040310001c6880e082e1540307940b081030460360202200200c140142c03410040d5aa29001c07440750f010601146550150030075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 979501402 1250 979500152 979500157
    0x412021203090d050601090c0f0e2b06020c0d02160315020904020d0b10030501080c09100305011409070e0601050403030e1201051501080603011116031103041412010605010e1302 78
    0x40c1c0c0c0b01603548900410804d001940318141c801d505428020665a1007007a2080101c5101060102c2c680d000d5080250410100d0503021710582005c04514103550a41100108100b00c0300381c0e8140d40001d101001d9000800000c60180850b01c020803c0000c0c02c0d4160020300c9081c00010600f0b01c814490039280d80e51501134650030580244215030311030103d82c0309400ac21945005070300030303071146080c025144d0080c030415040b1400346003c0e10581c10000300f0007280c0c2400800100e40c10149107004800701c1d40922443c80c410484440912882c204088018505100b943c441d95601205c0020401c0e031781d07402004e542c1101c2d8075042c2550707072012180018100300c3c030b410540500c139841d20b410820b000b041c1c0700c8a4110a042a21203005649981052600366040d8440f010a45001080002803080005141e44281402403411100d5a000815840e0031076009501001d80c40f074500181400a1070300000c0103081520329402000780c2440e100001e031001000c5034129100b000001601150395025404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 979502652 1250 979501402 979501417
    0x50603010b160203030a030606200318040207060507082a0f0c0f1b0a080610051c1407170606090c0f0f0409090507060219020d0c1d01030510020412021203 68
    0x3178a440b2591140010001d050600c0f500300003460481103071500151099000360004840d802541ca00880c0f4004040c075180500c01c4190002e908020303403408101035100d0fa600498032a40d82c039860741007081e0b4407018012102c8900b00a803200c8030060350540080822101c0400341006115107603822014401d0800c0f80640341680c4500031221500078031030032011500039400d801c1360f14908154960307021640d100400c8500c002c51048100040c0040d10340341080e145c0f0f10340035001c0400140103903664110320303604584d46201d09a00008050200061505960000c0e40300f500c0200b000b407500800203680032501034188002280001810303400076400b0301c1190a019289156140c4d00c0e5542c28403030303004112212042d1110f00416201003807041c40402c0e2210900e10424408002114a40802c4041a14064102ca542c11030900004039004504c5202c0504144003075800d20540c50341c10302c1c5083c20301240468000610401c0140110001e00b0340003034125070140e41003100705c9104070000d0f145125049 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 979503902 1250 979502652 979502659
    0xb311205040b1c0e0f210405060c060105100302071e030302040b0c030904060b040501080711150903030907061e031509091506050904080706021606111b0304050603010b1602 76
    0x82c203007143c000c0892003290340f43c401042007154001c0c0300d00654803600803141c002d40c02d40012540180080318241c078082980380d10000646065501c1c03002502c1540682540481030304154010440b600c0c00308110411000320381400e600c1d04c481c7d640c42285074600500800b121246041070072042c1440303541987c0180070010116a40c440242e40d4051380d0b0741013104181d2003141040c101042c51009003050301c1c1103c0060715102e016448058080d54031040181c4030b00d09500c40d00755200700c10750490b5010b50003042d41c2400307181d980c1055040c0c2c1d81040115046603090207042d00d9061030b241e08502c1c0c8951003000503d00018840114108021011280c0c0e11925181d070400c0101001c0c0000740b16032403a1140b5000c0c003042015070355000c0c00000401210060580340c1c0030f0201c4c9002c200d954000741841c40f485146401c0544107607944038103c039610f03007903800904000320b180c1c03e004601c1502070241c010034600541c00c02e40392400045032444140a210b10254003c9a64100368140c080b01e0004642d004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 979505152 1250 979503902 979503907
    0x5150307060c050609030c07050108040503070b010603051503210901030f090809090a06050604150c0f081c11090607140d030f061203020705090916030b311205040b 72
    0x700300051540c14000c030241c6280c040c0d00081001d042000044882c041601030241c644903203020015200d5640040050f03899002c00c00411000801c0f035903480b80a40b00d55200045c00d810000040070600c50140700d1203010798800c0c9500e01014201e80c0745480c50481c8039031000d0762214000c004034050b0580c03101e110400390030700a002e0100108a4050411914140c9000e000c0ba60b482180f0b1094070f20920400b41c120310100014841070203660b00c02c0720780310f500382403c190980391540ea0041c000c40082040e144c0f0100804e00b81212000c580e002c4003c00c01c82e541c14010b620f1241040c05040c81040241441000c0009400c010491810307510b5101c074041c02c0030b8071041d02a603070303001c2d0140c02c90421460030a480d001000c510801c07049884100d0303541650040604078109000d00200c158040c0030800e10340720342d001156210587c40743c058040d42c030036840101d1900303000c104152100c1601d4010f02c0c28001d100c0440d801702241200d5941c20582204030000302003000c10050b41c0a200e95040002281d100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 979506402 1250 979505152 979505159
    0x10b1e0d0602030a0f050c160f061e0c030605060918040c0f0e100f0810050a06180f181e031e180506040b0720061b060c03160305150307 60
    0x20f034042e00b54266015424000b80c7d455040801c214460340014055030701c14149035202007800c4e500300556240c0306036070000e2241d10b0400c400c0b0303c42041ca901142900d86039040400f01c03c0d0301d07004040062138161226810040310380006005e00c0d075074808400d000701c18400000c0a0004101c8900b00802c0f00c0941c0c03504d69602d50380c201d140b6140449810b10004001000018140842c000c2a400c07121001c0162803000781070100780c8040c00010b030039210a551280000b1925203400c4401001c0c4924804000038888042150784040c1c400840d9005514200300c0720f20004105094008140d51060fa17424010380301c0903160640340c1000c140c40c00040e42c514041c07000120390f0441c065603c0f142400c185054866910006c05c4810310940c02072280030b08040c81440c00040c0b6204440c4a040104102640c40b2040c1d40e000c607105401c5010313400d411060343e0a0000071401c0502403031b0740020906407034a01d54905840000c2c1c604845a0b03e49081640c0c0b0340000f40304042580c5054042c450040c00e030380e0362b15503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 979507652 1250 979506402 979506421
    0x5060904060f080a0309050306040f0803040201090905090c1504050913050f0712110d11010509040608061e0901050105012102070c08031b0606030712050a050a061d010b1e0d060203 79
    0x640103422000703c1c50b1400081f0b05032074000360040c032659101070140d003c0605c60361072880710f410241c022810b00103081e0000c5014a014044c82c2d02c0340c20f10b000203040c8440c25408005070b03210381c000807102e4101e082009008a8075018299036101120070200c000d18201854114034041c0341d0400051203009404001c06c100304c5c1c500d403026030305020703101c00244265500c041255005d500c150041c00b11500300c4421569500074400303444085001000003076107035900d44400c0d04000045500032803840e1221f1040c0040d60070244c000c0e802c0311000000304110340c10907001034500030142c203600308003030400703240100181120340454440e0350b801205820b0641d0740c1c1c079585a82e074011440320700c4031240c500910750500c1c80015103e8880d640c000c2c010055039103400c1258541a203c808180c40c3c43c01508070344808900104000f027507461288100180c4030580f4140c0c2d5002150788101d081d101c1e41070400851007562541a1581d886003003503141d1001d1100c14002a412420f114001405030740040f04202c46003c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 979508902 1250 979507652 979507663
    0x80d02040605090f01020f06060f0a080604080306040c08010605040302130f09030c0606050f06030a020a05041203180e07020d1107120f05070902030c04060507050c041b2705060904060f08 82
    0x41040c1c41c42500d0130f04550043e40c80d0240340e18840840c0d481400001c0c0310745852600c04406040240c44910000e458080c40c5003049400c440950794000004240805801d25200b082c0829000389000030195041c0300000f4450700c942d100c0031340300d40720001e18018150134a501c44001d1000007081005200c0840c50050311036040071034141da03010b140890004440c100000401ca1203040100554a11340d50909100c000750424070316181001002d000106600e54040742128845000307440f90851a0460350088005a155410079124a000d000900405540000301c1d00c0d600c0703049081c040001e02070b850400340350038a01c3e8890b10b02d607604e03282c0c10b40c10700030360342e000c040b0a034081d00c00d60701010740301c9031440103911003130720103546d59a010041000f800d032091001d001c48038402c2080d5400302080c07c0005c0c0c2950140203e000180304a40c51052400f6040418482002224100000401400e404009207801d40741304045c00791360001003c00fa683c0d2554804009441801c210b49441510341c0a81683e42 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 979510152 1250 979508902 979508917
    0x21e0a030311030903070f080f041805061816170a06031509050a0b090a06021b0c1203090f012601051509090106030c170109020a39080d02040605 64
    0x181c070305100c20880c5000d142c1140e22500d001001035141520903600c4c1d003074214883c85c040e503640b4010f001001c44410030000a01c02040e1200003000c5c1180d8010395a0b08899028040300e2007074142c9100c10021600001d0810342c070200013000303a081400310710310540d078840e0b40104642d0641c040c0c0d010419410229844102903c1c05440c00c010000703481c03072401046807034144010300668060b8a00b08001244503c03c9940401000e041e5958034000340d031010103a0b00440b603c01030f9a0a000b071140100442085241c21404c01111540ca0710342e01140d18035140e100d0103458a0003200705072840e0350142d0003410404024142c0c041458143c10900b030750008240c03000e00a041c4209560f80310725512a07030303441c145d8440c09001480c400c603a07441c1c88015401804035004240502c001c0b40d08024500a69080c654007d100d00440940c1d1880008002007028074921100c01000084242101c0c0c2034100d0b000001e48407540300300c848201341c01360901d01100c1c080d411400340014000030b80802c0441e0300c03c003c0c2040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 979511402 1250 979510152 979510157
    0xf090711070f0803040b0c150c09011409130c03020405031c030e0307120302030a091e11064003060b09070c051009060b1503100e040b1303021e0a03 65
    0x7026210001501d400d0514031989055900030f02c070520442c034851008000c140741c20011034400343d5080d180340c2080c01048601c248074900200341d0745c10558000c0e43c0940340c5440c681e40140381c050b10b0030004802d00c03400d516140e00281e8a4404c1d4003198000c0e030449000e0b08000b0100d03000b407800c0c060400284081e018111001900f044503407140780c1d1001080c2c41256600071903501c4104d8608804400a410050080b806d450711a20300701d001c5840c007000d180582c4040d02407200301c0102030a0503150b1454030740010740160b404000203044134407924608801500705407030304141d15102d00c60500444441000440e81d071070356080c000003041115407103001e40c640c0a5901c40c10030b96894001b9a199070b11440c014245030031441107490b01403000e0344038a03078040c4038a60000b22500030030301260aa104412014603840800403e100b003103c1d002440c0402408540200403992502d6540c1c80800400a0080d0700307002c0c11130700c0c2401014000d100da24074000c0305442d00b102c913680d8040701990b1440c18000c10f401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 979512652 1250 979511402 979511413
    0x10e030d0222030201050307110a3809103c11090d020f1513052404060819020f030123030d0f02010e1603020a060804030c0f020f090711 60
    0x341d480402d09000200c07501610780c0c9046030b03109181030300c00c1e1f040d01e4501d9000f809010341d020000340150808007021200d5036085106142c11034000c072402140401d4840c0807a95000422440500000d8088440c2091640104072003901c0c0400303205101c0c0030070b18412000054550200c0381130444007a0441d09907641402e01903403a6168402d01540b28183c41c260704400700113140c00c05401c00e030742030400704100a0a001d00400e2611442115900010288900e085845000b0041850b00c0317031180c0a80c4409188890710b10340c800b2803420700341c070552203040d0521800000080d030501e1207d04134180c01c0d07030b10b0b00155602c011004d06810258024054030f1440c0980400c0014592010612034122200c0038008011040000341d003a81ca41e0b44210100003150b40324101d510391003030f05100c98136005003154816114203003988104044141550030103010400e4500410000c00d0380418500c400d40d811200c01c2e980b00340c2c02d0020801c28403000841541184140c024055a1030b48901c64040c80348580d802d0700c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 979513902 1250 979512652 979512697
    0xd0606030e07090504030509040902011707080a0c0810031b0801090f12031803120e0f1c0804110f010302090301050f071103180f03010e0607080103050d0806090a0e010e030d02 77
    0x70480301e085d00c01400044c0244048005420a640302c4030303405005040c4004900c40d142c00100d560f00b411030b00100007500301d00c18003424401a0041040e038000c41e05102c0258900b441c0c03c10041d440030b03c00908600652915002c2250400e4048000742840724000c0c445401c030380c1030041208180700001c4078031707805170520401d415104c2e1080d40c103410104078002017595083d40301201d030300946100809000d83d075424043c010120400c01a10f20388404409404001d16084800c02d549417400245d0040c030000104200004104500a5880340e900310b9005507208500b40c0100c2c0240210900c16408d036103400d00344407003148c02c4081d0a120f400a035a855080e607100c24041c80d00c9000d450f20b0707a041d43e13603007200141061416803080040001c0280000070100c1c200b1030781603c4c0c00c9080d0385040c0464002d50040c03003800010f00c14600440e505062150a60601c2e00c045648944028190203600b80c1e00c4200041c1e140c820b402c503d24048804084036265142000300d43c0c000d40c8103146000c18101c1644102 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 979515152 1250 979513902 979513919
    0x70839150c071a1605010221090d05030f0106110c0409030e030c0102030f091e0406171015050d060e07060207180917030c1204200301050c0a140d0606030e07 69
    0x3d400c1d8550144603070500320019654446220b8040084130195000e010120a0901010511000703090300c80010704241481149181480c0c80e26a480007000010020401e104000c4400c0b01c1c1126042d03e4122018240039141c28142003502e002141c2c00750401d1100c2e02450b41c0301d1061442c104c001c034141c910440710300c03005a030381e031040022030f100b5580280b211450524105c3c10340049a101801e022000144c0c4000142c06c075800c2e03410140c035491504d019200c42a40400c941510054502810841035003901000d1502c844103100f40c502c0361050400700e20400c40e498202c0709200c44601c048960041d100c0002030b40b20542c50007a000652490440c40403644202d01410305d046030004c01400c0d48000c105000d030050b034030083c809444900c0c1004009041e41407945d50512035400b4043d2510745c10703148003640708200c83c0310070120701c07980c1040140406600704c6c500b101c802204a00b06420003804e46086186240100c0c00322496a510b4036200041c402d0700364011a00343c06191040c1d4105544440350f8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 979516402 1250 979515152 979515179
    0x10303110a03080c0a020c060c070602061302150d0f09030305091915020328060302090f060906042309160816090b0105040e07030e070839150c07 64
    0x2d00050318410214018008201c014840d00307103944181e90a0808900118115511051007840203a04c07040003008034540c1405815000b8080300720b039284100c92600050b44400d1b803c501118030074000155003641e10042d9009605000f1094001d2140342c04908000d40149001c840e03210081c040d010201c8901d048410801e502c90f580100f640200c018083c02c8040250030050440b02c0307003800304681d502c60781c40340c461078500e00308917090205155041d4414015070502c00380503034040010130828040300c0d643d01c00c00c0701d0b070040d0107a500041c0011508100050110f51a40842c2000314000c144540080c0c08a00c02261072010a031200300755a503881101d540341c0380c0c0301514000d006c4402d002e00c84083d041e004000d00000524003030b4103141d101c584440041005841c071001003640c2e800030090414003408013400410142002d00044c00303480f400440188040205500c1040d01d0005043c806c1001aa1810072481d001d064040b18420b500b8156849601254100005108001001503600041c052 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 979517652 1250 979516402 979516423
    0x150306230109020a081f030503030108030c070b090607020f0f19030b09063c07050a0f0e060f03040c030503071506051c03050309070b0a091805071709070e04080301030311 75
    0x1d414403543e50301003014009070000982c8202d5150500e06c0040890710400246011340200c401544c1d5801004007403902e00040b0f98070001311204144080201e65450000b500d600316010343d482d01280000c00300240c8180312514000e40d0100c250810075205910901564081d20300c1001c0154042d10f0300700000f9941c01c0d040311007448201070300c0c0c0940411a1a2114082c0c85078980421004480d0892140c2400318411a002c03c0066408200111200d41c0700803688280390041c180440300b2001c1c800891064824a400360305004000404030b42048804640d8600644e000801e8907101c69591502c1c581c90110241c0c1c464420b41091030200781850001500c034904a0315001c1107081200c141e5041e00d483e00300030122005401416400240714200384000c01e004211030b510030602c18140040001010386110316151558a00b20030000059040f02e42101d510a001c04100d00395612001202d103422210741100c00402e400c1c00603c000c000c10003011714160fa100ba102c1100002c680c07030515075075040e040c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 979518902 1250 979517652 979517657
    0x2111041503020d030201110d0e0c090c04050105070503070204151a0f0702090403020c120c0a1707120c03170304020a09090b06101403010b07050c0d030210150306230109020a 76
    0xd204100500d400c1000e140030324070074000071501c0200711021110541000c00723019231440e1a42100c01030401c05101c1038203c03080495040500d410211054001341c0a24061035060003000552802806002c00588520710f80c000c00a020301420f103d04a16940c0c041d00c21000940aa558024900c64500c0241c1d40720007503041501d0304080c1c035a020485200e8018200350250b0241c1100d0445a0b02d4450300d0616034450342008040d000080c500f8030032a40709913403011401880c1c10780c20303c0b252a80850f0b82c0b8100c0341d188580d54107403285400c090740758400f10740c40108010454640003010340d9503680690f10803030003203070b10042d81681e54661100380c449004008044000e40320003e45903140c9490f880060404d40e240495041d9954800010a64400c1c1c0151155101c00302d503c00800804210459112006894841e10f852243c0d074040d5850f20f000075030f10060303074030f90440d102c100c00ba82e0400002981c025400f4130255504010b0b00001c44580c20803107108510120021590241d68000c46001d0002603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 979520152 1250 979518902 979518941
    0x31b0d1e051c020a0905030c1c11060c07090f14130201110f0d0509040609150312120c21050c04050f0a170303010f05030d0503071107211104 62
    0x84000c40740c03648034084080d2580d2081010100321905071029214084403a200c20303100c9030408040600d01050680500e1003403014407120301040051041d144003490f0b0021300701d036160620b540092407501681e01c0090301031080c0c001c0060080041c0c2c104283d2460080c42c00c0101d0003420040c052034030800c44420041300c2c0c00350340e070000552065107000c4a0307151070000d03a1158865044e4a504201803180c0391790010301c000c16500c075a46414414076006021210003040105910300341c503400c4511611000e002466000f8400000c64041c0c2c0c42c21070082c21085080241d411201009030648030210100307145000860200c20072030107076100d520b00640d200411300f420035180804200407421800d440740d402c180705031000a03080d03503080c3c01c4804680e9084091a100e6041080183d0044156800b00e40b09038000c00c00ca41c0d110b81c02404482d042809403030a00100b2503401c4209181204030b90104402d0503400300500003003c2500c042c00003940c4991210a64903e0810801c416101d0207211550f240322031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 979521402 1250 979520152 979520207
    0x100c17070305121009020d0f0e010509061b04080d112a0d03091203110d050f19021e01020a0201060e091b0d0b01030b0a0c031a0906030f031b0d 63
    0x400d203c1540c400c880c221194070303203a01d40c0d0340041a40c000609030404a40c03201e40070030040e1200c0c0600649071485100030442440c0011b9116500c0c0c2014103000b400c0300c10305404280a02d030440c1200c010700226070440b400026000c8004150016424800700c40d406110f030b803110300024022122640144090695400344c0015007081800c44261500f1005e01c0740f00d030000034000c4072980c0300f5841c90380030f40c5030441100c50340484181400c0101032480d08105c030801015156404900c141c0d0301111403c02c0f0442e003000c00d05400d030702e040307507900e420006080101c1100700505015001007214503665402405900c0e030702c1c01c440420b0306059981128a4000c0c403031074106042400c0900b001004020401c8100b51015100d43c006801c003a0419079500e100c0d071040004101036801441e4821005103400c011310200806041e8080d20070508151041c02d07240b0204a15503800c00c2100f01e00c018100a076070b038840d10b294101c2d500c01001d5070701c1d1486010300e968203011503006003010000030180140c1c00ba200c082c0f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 979522652 1250 979521402 979521427
    0x41e151e05032e03022e030b06090405040506061905090c07060213080c0406331e030e0c12030d0c0318030f181a1602100c17070305 58
    0x1004050341c004080b180c0b007500c01040821030610064900c4074120f0342250650040c01001244110b60540300c80c2c500035034448001c00041c0b201560041c41c64000340c0744020384001403a40c070841503002c0c0d1250405062009100000c0b403510300a5034219484003c696010f801d550400c0f0780341c1318503584041c1450000d00440440c0f4000c0813001d103d800010724101041d0341400740408141c02c13103080c607800403a400129042901c11030010700031200c00180041c00e40c0c41c040182c04005000c0f1521031b1000000c2c040b0142c021590441e1401445040c654142d0000d07070028001d0601a030a2011845072000c0002d40e42800030340070b0346500610001d1403030487c41c42181c801501030038480d1403c0558440150000c54509941c4c0031140d4486d955500100401d0240140611a000209806041c0742e80d010064604143c4211400045280840b910b604842070b21801d5000c099001a4200b0a03c1100c995126804030208a84900c649913030b038501811060400d00d40d00800c10001c01085082041020f41003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 979523902 1250 979522652 979522657
    0x30c06043804090510030c0303080108010e2113050301050112051b010e090426070b15011d190b031b0a053f1506190e06041e151e05 58
    0x140328010f020788840d902d5a47c01d80100c1683c2c002e41c00540c4500060040314800e0103a0000c0384103110003400440b030203c5503110036500b4101302e031744c2d40c00c00024180ea041d1003c43d6504000e0000800801640d82d50f6211300f1a80c0442c00c408440e98041c0b4401c1c2840c0c00803d00c40d4400381c20045c1d54045c0750041ca8424001103050142054030f0001207130000c40310720010321030b02100d07502600900c3c80d2241010702e000f5801c00001b4250020302025114106482d0368402d51815000f09a104454180b550f50008a840c6d03401c1501c115404042c04a8041040c40a05004500410001e518100d00100b01d001c1008180130f520b140344000b030001c0103590140c0c003c4040301e801ca07a5008283e0500041440e070080303106070f66501440111288102042481501c1691621880f802503441a14080c00300c0c0c040003031110142201c90510503021012211626040c00b514003410b5000b0b041401c0080818190200b00b550344688c5d1140d000d034a224980c0701e44207800000113000700e00e001c010801d400c1c481c1501c103034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 979525152 1250 979523902 979523911
    0xe091509031b03120403020d030c21050718090903090e070c060c1106090105041709010827030705061006030b0f0f0f060403030e0306070203120114030c060438040905 73
    0x140701c04d0029488181911950038007440c4030390028014950723440e00217400d55003010340d4041070040d80c5110300c0b030594000d0140d80c5403102001300002c2c00d03610311200351248030b041c1e040a12155406100496000c11a0780200c503e2070080c1c0b1050b07032003552242d00e04e6240100b02d501030001041c0140080c0000d40329041a00c4000c05810040b10286112404502d08501110ba6400c9a91250140014000101d081081d40d9859040342850031044900180070391743c001d00480410300c0303101d4800341e01c0c1624a00f400c5030400420140e036600e0043c0d0501c20741c1c3e0001581d00b142d081002c030310300041d0341d80244180d8450343c0000c1c0502d50400c10450811100038a2502c4081c0c100d001450040f2082e55040700410246101b40c0b55003e1040040341490702e0300c3d40090644080d94010864102c0d00a10400c0160444140c030b0b84480c1040c0070380001c03070b0400c4040e064003900032002240120f5007080b0080b41c03489000c40000910b02114072942168540e4100c0b44541105a004100902c66102140c0201364007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 979526402 1250 979525152 979525207
    0x18220602071e0204050c0c0c010813080c070807050108041709040b091807090b09040b07020a080315101d060a14040e1905010303170604150e09150903 66
    0x4050164480301d030341c681c45182c03800d020341480c405182185440e10500d5000a44200c41c0b07410300d001c045106d50740e48000e60401c2d06000340080080d03241000e0041c40c09100341d00c012119142c0700000041692a100c1f4040c070001402141c0c000300c0c080d445001c5a034825a08086100c80c000305007000510f181c0d01144070203410a480e280b28419a440e444280390240281e000c217010b09110f13507012607048c03007030b1f98000d0003401e401c081005490f84e44041c101500325402003005807441e140da00041e864101c80032070051600d0b0b0f012081001000e02030b00c003084e0019042d10885410100c40000711b641c00900808440407000500c590303070035800d0401c007404491601e410451018140e8100303c0089420607405862241c0c1d1002c200004900010110702c004001280203102c5541150360140c0034034094085441d0b040407204c005211030340c403508207803d04c0c8400c01441d4469911140c004003a03c008591404491203142600a0b21007075980451340302e00d08580186003480c1981030305000141141948444 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 979527652 1250 979526402 979526407
    0x7080f0601030f06020c0a1104111201210f0f020108070804020a090b01052208010b011e3c0e030a031202031003080d150509010605070303092303070218220602 70
    0x580801f0400480707014080e0040c07111654a0500f00301c161880e03070290710480c45080c804810320b29107400b4240d05580081c0486010081182c1c51504544055407014100e40d0404c5025000d20042c02801601c05000707907a1030400d81d07601001980c40e00801e95000390070144904080200c01c286500c408041c03130f0140350851a007081440042c41c41445ca0701000155034281d101006035640904c1111045042800c0094010f02c824048110040c0414103400a215080d108106c0030244032041d071107010315041030111150440c0007200c100185800c1f001e400308510a40c611650b1a0014030000d0182c2c0c1655501e4680028694050281d0009403a03525040407200b00400018040000b5015040a80ca00041d40b1100d914000328680301e02d40c065401605402c00600c0420b0380032040311065030f0182404245007006280020111030310345107070001c1e1380d041d2801412160000c00103000c803a000700c0789043d0b40a0080031220002c00283d4038106440303c0c82605500c0e10b144041d1750034240d40100c10060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 979528902 1250 979527652 979527667
    0x160e060d51080307210206090709020a03142a03060d06110d090b1b09010e060a0e040f0609111602010c05030d110918040c090e100903020a0507080f0601030f0602 71
    0x2483c40c0c0005104441c0c2c0044e510120b0002d480404007105414070368402403000c1c1c10102c072100c1e1100d9041c0185240d0640000c1c0ca4064180643c0010f0407032106411030030140c0c0b4155a41100390039008084452400c0c0101c0c000d021580747c1801d5034020317080200f1402e0340f0401c81d50790303000401030f0079071000c00e0100501c00d01c05221034610416113464000c01c0c00301c3c01d9142014150350a81405180d40a2070300003481400310b5640d00c801e008846040a41d440395032402a0741c8152007400030000c60951180c1002c47d44403214009400c55421107010340d50900c0307203410000c4a8000c501951010760761514051283c07102544c4034400c0108014042c0098030f24104881103e141614034000c0b104890410000f10b50a0908000f00640e00d5010006901d980509240d51340c1c0e9810b00c010f00c1034032100d50700c40300103403090001071003d12a40341c441d4208100484072442c0c041c2d114000e070704050b42d41e401080c100285140c0d003c6001c0700c460765150040c00c11a0300310340e6030840b02e40010300203407000b982c03d20814 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 979530152 1250 979528902 979528919
    0x3060d140a08070b2a090d14010f15080a0602161203140601020607090620010603060b0a12030e09150334080303160e060d51 55
    0x98098600415501e59101c0f46418040700d07501000e0000414069500c0103d0703040407018225455001509104564030000940040c08500b0103107406014001d005861400420056014400c00740c003903601802428690b4142c60440e0b241441084500e0300503445d2080006c12660082040f90306a02c105000015943c842e110f05280881c18070000c42d0b0b865400c01c81001d10b298180782d000e9002d1004201c1c910b0450710007804443c0c80c0c40b554040c00740182d1495200140c0b01d0080c55494034090080080958a040c9540900b121074603190007044527030700c007266181458502240c0d02d901512410070300746094041c0425103100a2807600000c10614501525907024401441c1c1030341000441c6901040a180c18429004800e05c8030041c40040d60302005200c3c00801560350240460010138107144409406548100f40f40e0381084d80310500050001014917030707074480003010050742943e43c0d0303030456207035445110712140c803407c41c0d07148028505402590007800c1d000101c1d10000b90543e4010740d81d8200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 979531402 1250 979530152 979530163
    0x7022b0c0f060906110f120601020c060d050a11132d0303110c0a051005070203030c01150609150801090f0b040c05070302010b0405010308090120032a0703030503060d14 74
    0x4036401c40c0c40d4050703c81440344502690205140404035035107005540858000180301b41c01c2c01e845583d45030b000080382030b03000340700a040a090140c06030b90b40700055400000242812222441101c0c9040c50003460740d204042030326030042d030300724a40d600c03035061500c0b11015513503e800d0141d0b0210617403103c12003041c2c4500780c080250310a45a104402c880c204840d4102044844c8542c00f803c03c00d0310801c01d541e80c03082c4070041d1010034200141d80f11042d0010034203510031100240082d40c00c0a03030b01e1030749140380c0c0c0300d181c222032032030703641d641c81c9521040a2804848110007000000d015640140805240c0707900141c180003148000044001210700801c00391070b15803e92001140c40800c2280c18580c081c02501d00c95101214100040e41c1956260361380741c05030000143c104000c0b4041200c00d4850204024800840c0004407a00c42492191903001410040e80240062001e43d8403018442c00004d4100d00fa02d501d6142d081c1195204014007085144900e010703121092580b81c10100c82d90203000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 979532652 1250 979531402 979531433
    0x120c010e150f07080c040504020d02070605070206040201110303070509061c110307112b090905010f0f061b03050a2609060f092505120601060807022b0c 67
    0x610700d03280380065110400c403074014000428403108008000d031050401c0122001d0b103504441c0141c5951812440d07400901541200604441c034100038001032a03000195544114801da0f00c0c9140300d2a4070030b04035140c2c04295008000300c1c000f071200050030310741075001c0d10703174280748251900b803441e011094241964074106007091401e03400820301010952240034aa0800200c0c4020129070740c038002411000c00c1c000e2210001d00720710800d8144c00d0780c8642c0b2034000801c0300c14414051942c442c03100c0d600c8404d0710b206a20304005075410010300b460103201002065044007050304c038020000c0c0c6040c0d409501901201c8100400184c12010000002107881221010072450300b805181850b441c600c0c2580150055070214103800420480c0c4800098034100d061048003070061108180660000c1c542c1590070640c0c1c41054025010720700f801c000350310380c101d03601a52040700c2619103400598507100517040055410803420100d0598030f00000030000003092500c1c1c039083d56100780d161004115000e00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 979533902 1250 979532652 979532683
    0x5010f0e1e01030b011407021903150c0f260402030721140316060b27060f04060f05041104050a2904120605041106131d060102120c010e 60
    0x403007121107592510490408040a0901e08180c48051030302c05030601503030800078400c1008841c94100a00d52102c07a1005592000c40300c01a4080340e0700101c00b1300f46410545000950340801c0d103007402e204005605110400d0340f05440f500e0529031001c0e1200e0401001642c15104c0c803240002d0095151480003c1d81c220241d400242c65581d15021442c40240040e0003540e51051143d512503041840c020041c0d15801100010003218003070100e140c240413a550603270480001c03070412099642c3e441c40d80d44110801c40f42d00d00c8008070f1408010485131a070094000070107005000707024905140d170011084980d0fa444450810380d82d80300250010b0b02d5900180069a90800444050071401c0c0c07030b40c102c0c4880007840c241402c1c05c244003002c92494180010380f9168581011a082c4401940c4200302d040c4040c102541e80d4040001088424180344615134000d90515605d40c0ba0601d5440740501a80c0c1c164040d01044455001d481c1c070503005011009030365543c40e0450140d1510800500c0320162400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 979535152 1250 979533902 979533949
    0x825090c030e251e27050403030c0809010c05180f09040302070302031b0d080d09060c031a040504120f140c010f0612170f070c030503030f011e05010f0e 67
    0x12541c0e450a280c1a0300000c07409010403441404191000615000d0b14500170140c40313182801c4540c5c081c280380e0516071040152070314080c0b005060f070540065403054025203070150ac43d11604041e500702c9600c100d010001500c1409100006842400ca0398081400181507403034030381c480c100040b1100c100750780442c00350f8020041001141000d00c80450321080c1d000364115400a4130000c1041011b00c001e0081a4038000250342d00008043d9118200c0150010010881d190081f800030b40203014010302001280318152000942e40340c24059140b00759844070404044486042050310b80c42a00b14852050000c5424480384007140b407000350a6460003880082070b001c0040c2409000c4541c03d4101c5a100305403107401001003105c1d07654103901103011141003690341840f601c071800c3c503000c1d0520040045180e503c0000502900001650090040303d008035616682c0e078186070b06900d41380d43c11080c070400029041141c0c0d0700440340d1035150046401c03d259610310400c0016106504102d5828400382d80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 979536402 1250 979535152 979535203
    0x8060a08012c07120f03121d070b04030218040819031505010f05030720070617150d08070203010b0607150608030f1e040504150825090c030e 62
    0x407404040300c1201e41005000f146043c021854041005040d000e010b4110707040c2d004081502c035500a21091840100400100d41555103882d00b00005005403040c903c114400801d640d0f6600d000c03101140e42c01008a03605244130220b201c1c003040300a10903a8034510600410040e581c41070451100c113105541d0008001036414600d04403007071150440d504003d0035101040415400c041225003212142c01e20101c141c803000700d00300481502a80c2c1c145140aa4640080e00780e421009000cac00000c1d920a0400b20380d00c102643d20008181c9181030341c010400d1102c00c0202d8184001071000900107000803d000303481d032002c44c01503071021000300c4240e0002c0024000406140c41250094100200030b540f41c03002e180103810707440c080c05003d035100303264505041c0b5003d43c101c412100140380203070040c018410800b011200b0040355219a2485000d14203418000a4155410b0f200d51061044240e020300d0401c5003407001031001c0000c406c14107640f88100c3c04510f90410000300036040c1030f010000001503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 979537652 1250 979536402 979536461
    0x20f030c030f0a051b0c01091b180c02120c070914090105070c110f19030506180a0818060d050c0a110c0616021f1e0513030308060a0801 60
    0xa000c10030484c81c200c244050005a0461304002c011004480b0362a156010000da00410480c0d6004001502030403075684031140f8450300b202122060381202c003440040709685000c0d518058440001038100c40c00741c003506e060100140075a5842c81046624141d180e51a190407500b104441140c1c210f031750810094864001d0213040d034010128500783c00004050303607943c1245600b14036003600c51200305850525580341da12500c200032022100b02c00300503640e800d09d9500c9501c2920460703100c0700345034094544802d001500070034036540202942c0c42c1224006860245261001980d64030000400142a0082150052a00600ca41c14401c1d640c2d4071031290103005010005003020b043e400182403080340e99600415588106100302050700402100c0c8005802d11007545010034809034561550a100360713121048000800820034206440e0050400035101c9001e81030410062041c0340d03200b4000244901c0c52544c0062004d094040381e40d86892025027514000410305041c0d290303101c0381404052 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 979538902 1250 979537652 979537681
    0xc060509030d06060e0120010b03060a0203040b07020a080a080c0c06070201060f0501030c12050603032104120e0d03140426060a050405100c050f0c0d08102304020f030c03 75
    0x1103d404e04019141d0417900103065001555a01221180c00c181464204202034000c1c9044007001000d60b141c911300803502d00025081500c05891241001c4001100c6500000e00d040d10150010400741c01c100c0d03140c008071405100100040f903485824400258085410004079005501503000810301508001c01c423101880f06a210780c1c105403e0240f4007038601d81018003030140394441c1001152036a2150b021038030750704c501d19080744101c0340449076046601449005601030b0348a844405480c03289030340229400d000c000c118592080703251000300b001034080c0301c41103090001500018205031381c4034a111306000e50059100103881c0d07411b4069604200070b000c1540c1c0101b00d270710f08114605060700d036113950f54103244101b6007a9548000f0a880c850054050340d40030020a29501d9481c8a280d102c19111429003031001c0206e4036000c003261441c01c6940c69182a0b6030120420703511824403605900000c000010a5600103a00b002500c6001d403220303009511031290503a100d986e1342881030183c003004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 979540152 1250 979538902 979538909
    0x3030c030403031d2b0e040e0304081f06090b010503130c0f0b0c070e13172503120b012307060507050c0d02030a020c06071b0906060e030109120f0c060509030d06 71
    0x150702c00d5500701140c10071b140c50400b003010b41d00000d02c41c01c141b91203171451180350460546442049802035840403c88041100c15404150901c005a52003240301300f82d44e2002d41c407038040350703040c0b0000d42d01400342640c0744001d0307026101005409960728030003000d44649811140101d180010b440064034010010704000702003a40e80301f1501d251440008103a04074024005141c00c0d03000c80c80000c0c600a50040d107010f0151002201c0d1001c0c1c400c54120010b8425038003c0340815528410024507114503c1080b00702c001c107848001d075120050706484504d04000c0b41355011403a060021901040051007500d11450b43d0b40c0380d8135540c1e9014081e961030501d08504c4002158800c2004a0740380358041280416004241d815985880701450080c40d01c0d9003040c096003a07480f100d5000201c86486400101c00c86400391180300c11503c106052501341e400f6032002800e0444e0b0100602c08451240305103030010320031407030001426400c0781d680001f52142568000965800826100c503980542c0c858030005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 979541402 1250 979540152 979540213
    0x30c0d020a050a02012303010f03170310091e2909010f030813080f0606040b04021303140a02191a0c1f021b0615030703020303030c030403031d 63
    0x400300a90b81c499032594a4240281000200c40b18041810a421201c621002c0c00c02c52442d102c0da100c50b0b2400d102110313031000362050103544071000785441100c012a80103800703092000102604000c80030f0301401d040202404c09402e000341c03c1c10b5407001445018450034018028120203000d0402c43c14016048020080c450b010f00801040f00c00c2d41031300c0d09000c80e503005c8186512412484516107030203549500c5410503000e007034840d654104000c182944a460304407000c120451041043c40224051a850144020803030384061010410801e80d01544020b900103c0d1009407265000c903280b40b902c140b8916800110140c14850b40f070100c0003929000d0760098101d400c210300c80084644d90003008040d48911800111001d21045041d0101c03152600d007a8503d0302c0550010540c207944443c11907140740b807142c0040c122382c0c8500e8041401400c42e5002802181141c5540c00300f000c0540c0060b208a05060381ca840600c0040010a5888690341e692005440031162400140601d00c11250030a80c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 979542652 1250 979541402 979541413
    0x17040503030a0c06200715020a1b0f081903050105030c1f0908030f0c0c0303360a0611010b01020f0613020103092117010317180d05030c0d02 62
    0xa520000203032504440c051408203809040c0341041380003410004224580c02440d0008003a440d0301d001c1c01072103014844e0151045481201c55800e04a0280503103070b200107036501d85814200d140c4100c0e86a0824010b4207110b00b0f8125941e2100a554041001004414170810800100035010304c01d030781c01004140c3c042e0281f20039081c00200e00741c500110a5500039241441000c1091151300290080c080903000c8039070308c11100c02c25030986d40116807500564402c080c1060094100402559204000c66001e0703510074a01c4001000c1e00d40d095040001e281e50752992070715144c0c0d900b4406078020b2585846064a400e48070b8032550945101002d414150351003030300494100500011744940c00303982403044e180b8281403071004070081d100b0440082c101d162510102000c480030804004c072405860341381e21000014080c60351041580c01d11000e003020700011400c102002d03241d0010503903541030f940d0384019200018001004644006401c0d21550702c0418411060602003020300030b4052640010076 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 979543902 1250 979542652 979542659
    0x1202130c08010b1b0a0c1a0f0301140102030d020409061805060d031d030307060c091505030615211009021c0c110616080f070804030f0e13091704 64
    0x1403500e40184520140100c1c00201c94614400011040100681d24400c1d91170483c95401c00c84038010b103600a0404036021046000d0502420310200c40d07010101d030320400e007140c0c87e01e00c1c40c01d0078407800341c0b070641940030030040c4815034003003032000340041c082200000800b0b030308045021180742c0590090381c0c541c524003414000300d80e4540c540104415414a440c2d43c4071000c0c08410020710340d600a000e50540f20204140080011b0741e040724804594650b2020a4643c3e210741652303501d00c4182c0500c01051081000c2105400c02021032280d080c0c040c80f009203048050141d50541d204144803025004d001c02d403e20807a03c0302045045c00034240010107500b01003100b01c40303404d0300c1180c002280003503582e020318100c41c6015024101c8003032880820383e1401d01c0c05505650580c0d008544c06000190b415002072aa82002d40540d4003c0f440d644d941c219680d9285d8050320010034908030741c0305102411651041c1c0784e0754005546c1c01d140303072a0390118030401145002c0405404e0280704800b514001d11051 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 979545152 1250 979543902 979543907
    0x52a120a031b0528020c0d05010614010f0f03050423210a050d020702241905070b070c030908061302040e0604110d11060d020a021b010210020f0d02041202130c 70
    0x240300380c004c140c6181c08541150036099282c40d001c401d0060704800390603401000d201066000c08100d41c1c0c0070900d50a2032074040300444410760071122980200b444a8a0401903910a034007655000d0310503402c0150404252100d5003100a5400c031082d9a40c0c0401c0301c0343c101554103502130007040d550a040c1c50601d031100f000500140074612214486641c0429503c044d9a100c20060082481d040b04001c268160b076200c2d0640d40c0e001c40004402550120040038071144114220b4107915009003410b81c0710f8a0341401111f4944900005a0400001749004501207105114943c02007180185240d455105071050000b5a0151014130503030340c012000f00f002144600e4616a0340d1002251180c03442900d618210711118941c40c45150011400300380c00c2d0f0085c05590080140107002d8089528010014a26003800c01d0001e1040303005030000340403807007403070480e0b0080d0000040840d5242e080601d44071219040341c1059000010748060b058105042d41050420300070841780868040c0425400500003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 979546402 1250 979545152 979545187
    0xa11070302130f0f0e0303010f0b0429070b090d0e0a080705040b03030403050d050307030623060306010e0904080703030c1437170106052a120a031b05 66
    0x442c0c0702d0b25801c0d14404280b099100340c4402e0b11420040000102c85480c266980d00700340191480d400311060301080303036540c11040d2001c580c1e840c0d5040800d181c031107002c403640c528051118619420207001000014a1204280f03108144607001004038940090000302500314003103080e40941484001444034a0000c41c41c030041c0c0d5001c2c1d8002c0f403042516000301e40b0b10700c5141d00c06412800b5601d41d0542c07aa0b8041e005600902c8a0f540030b104540d10703410310f8480010300600180c140c400c4005e003400e80e03040000c003031030340500141408854409a4800b00c0e481074404c50f01110b00076800206c0e0b07410107405100b580f1161070b00340341519090060506100e10352141414200600d507100148195a50b60000e6601460440311a03003c1c29007007500014202007602e01c0005c8511224100205c2d01c2e51090341920700c082e0000100d50701c4110355502c0c030704110703410148442c01805058140940144075200a11225030240e41c00540c1e820b81e8601000c07441c080d000301104028040107900b200d41c504000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 979547652 1250 979546402 979546429
    0x18030e0f0f2707030203101502030a0c500a080313060e010b041b0e09040f050105040f030e0103060303080c0d0e061005011403060a0b030a060b0304080a11070302 71
    0x581d16031105100002500300b18099034045002204a8104030020303905801441c0074441c45195210501c1d1103c0d4400600030f1100d522400687c0188503a583e0036219481451855000e0000302d4004040381c40c5601030f41e41e40000c2c80921611100e503200b81c90018120001442505c45204494000c0d000d0b907d03a229920614050290400440840c10b4840201c62055600c2e620a40c05c208100301d94a80501804407410f01314443c61600020603034142c54110700744514020399468880c07803100b420401002880281007610740503540700040001903424400d050003503002c0e4810340c04c4070340c051030000c1c1408400302e0b2144c10907040c0304040000980090b01c03150419180000344d51038854035840b0304c008002103001030b40707248105404d100300c464084214038190341c802e907520515468403018980c00b41c44242c5510782c014200440c100181e000050145d504001044d4010895a50311240003080d03030025601503517440070004d00c4405281d003040003446014a00c3c1c019010240c03860700060304c035140061 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 979548902 1250 979547652 979547659
    0x10c0206390d0204060e030c030609071203020c0d060204030c0b040608150301290103061a0304060e0f03070b0613290a1a120606040b16110418030e0f0f 67
    0x4814140c0c000490080d500b04030a042c2045480303c1d80d81c140109041342161210b030080c043c2009901e610b04001c104503115640072401004914600310340c4d12a007001c1c140059045020b191182c0c0c520341ea40d000601d00c207502070b000240c0c645065081240c50840d01c2d03071185282704000c1008020058200150a9010a0042040b0901100000840d0161841c000d200000450508203011089030303030300b039070b070f00c4020b080e6420003034252181c200340514120361580380c0d4000d80500018000490079001214044407035001da60741100c1031000340389148c0081c8070440e01050700c0000c0110034104540308107000b43d80b0b1a070074056412400b0290307801f00443c141d40001941c071040680c809840304020348004014000b0601175a4064482403040c58209018000e044020f00b408284103103006010398007174444035041e50745003540300d140103c40d90300c40d84c0f002c8510a815207030600059440b4400c21442003410700600708090464500142418a03103804144034000000c285101600c0d425138204e400542903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 979550152 1250 979548902 979548991
    0x1f090501051315020604050105061e060f0c03030a050a1b08061e12150105270703060b0307021b092406040504021603020d0206010b070803071808010c0206 68
    0x300b030003081848007030300254040700c807040040c1c81140e0b0000b40b0900c1140940d00030482510703110f0802041c00048500030250480400714a83c0503d40000201405d03028010705500e0704080c0ca4503141035820455103070100e0380c0c0d0f40080124000050180e82000c2651000c00000300a000c4c0d4003906100300600010300681400d044c0627040e40c14001518040d6038018404140c040c0ea4402d445d030341d40000242d07998100c0000700000b8082c18140d1010b001600c00415194071000081c2d0440b403445d500412803000c0540b110380c005241c00801c001940903032203075806044161480c80c2c17804800aa0450814003c810b06010000001820302c440700420240000f110105040c9030001142c40c001c03608100d174060310004802803c0c50000c14282203551281d003d031004065440c1741680c642c2400d100395805800700b080710f42c1c0001d07080b07001164020800c0c1481c100d07804448103085501c10381c41d0010b100a80d036902320b440c4442d4040000c0365103c0480004000c0340106540c5e0600d0348021086010040c0024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 979551402 1250 979550152 979550167
    0x3142b05090a0b0c03041a071a070207031b170d091707030c0b07022b02040e1603060e070902090f010e0a0e04051e030703230c0a0c051f09050105 64
    0x401a8007801070100b140e01c5502e80e0413250269440354041e204070829040c5100d00c4031007070700071401551042500515003042a1400b4040000311410017070804045000d001804000110110884d007804205101c403c4551410a081c00075031064210300584036900c065510191180c0c49000c1c81c0507255040384200b034005c4860004e03031525140d50402010343c11501e101180610301300b00508a2203008503140e1821001e011001280310200200e00e1751845049800d440150416410030300001340e101d0708560400e00b482d030880200c4a680c1c0c0045131030f1030f00c03101c80702c04d105801c03c0501c01a11401804504c0c001204001641d05048031505a05010340703000480700541d14a002100148036404c1e00300b16500d0f26141841e2030307200c4010610010300d402d031005110f002d1b0000a6035000c41c2d0580742c02c0d49213940e1500e8008900340c40b001400d503500d010403c250f100e1505100c03c2e12000c3c40783c1440b08410381840e040184100441205451800000070701025a82c0c0c0001c2090480300203081c2180c1d14140c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 979552652 1250 979551402 979551409
    0x5040b0906030a03050a171602070509040b04020418060212071215031412070525050d150b0301090c030605012c0c090406030308040b010b0c120903031303142b0509 72
    0x182d1550150487d4a03180030024140c0341c1c01c0f02c81034807000903401d07180c209407150300300700001d6401e03103000d00204170b00400038005041a5011421416507a101c00801c0c0326542d580e0010f80e48281c0110301401001c0090201c440c0c1c102180500031045817000713011020150030002105865072102409054000b0f000d200410300c24003110120001ea03005a03030b514620303030070700561740c0e000031091905962a8260f54803040f00070300140019148020941b031410046038550010001020000011f42599618504c00c2c9660900c03904a1051080b08a480d000d0b145081900450381c05030302660f0760141550204080702000b641050403c16000450022601c840d09201401e001c0c00001c660440d261040c0441855081345d01c85100300e20030f401e83c10307003a070f218402102640611000c0403150f41c010b841402400344890043d2448540c00b5089030300700382c8241070708100c044a99000750380d002101888514418001d01420590307201000c40741d0207040c0004040ca5007a418421640c04018010405010556 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 979553902 1250 979552652 979552667
    0x3090503011116140d09080d140d0905100c12060509130305070f0f150b0f0a09020a0201151d090c030a06090201120504120908070509070804080d06090605040b0906030a03050a 77
    0x7200c0485e1015454118054012005e030f0203240040e110b11140002d5281c400ea10070190a400c616115040c400c0100c02c51000d448009070031103080c0210a8480e0380142c00384120305080309203646908035000365590b900210340342c541099009403d00800c006420030040c907204c254907071508e015507540d9418140650008030225004220030706a040c90824802030310003609416010040400c542e8044108108460883e038900541119000b10b04001e4000c407680580405000c07800082000a00c0c040144c5454000790080540035915450000600548000460b4460b000c10010031480441c3c6001030394900c0c00660003031180b901ca20340b0304216441082c00401c0100d021006104504007441c1100243e030305d658640d4001164604001440180094040d04444004d01080c06946805a00303e8281d00000c0c8195030304441045104042c0c0038a00ca0a40100b01840700007849034140410041615080512248611107241c24861a1f42c3c000ca07500303c0107070f03260070016903a145048095800c00e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 979555152 1250 979553902 979553933
    0x1080402061312150c0e090a02120901020703090b040b03041e1203050105010e15121b0f09090615120702010e0727050c03010b070f0b09030703090503011116 69
    0xe0b0700070800000c04076624000602100d1143e12062400040b10300e01004403070005108000065000b4140c1030141000c1c1c40d0290070159410b005450000c09544007a810102602e5942d45694001512418168070001101c05400034800f00c81c82c2c54a0405055160b00000d0301c0a00a0b9008420074054140e071007038011062540601c00c4036000409100103001881c0034811140420f5203005816018901504802010001a00802d0800b22441ca0b0207804c2036000303101d100c00d00101000134040c0601f1030054501c80b4110f101041d5a220300c0c03014854a81c030b0251240c3d0007004160f800e5480455940c0541c0c003003650242e280921540c42490890140c04000401006070050710400700321042d115804036041026070518407141c054551607501140c400b02c0d07205104880901c014000303842d404008140860094099080b841c440707494600d03002c85c050382e176412a6800018182c0806801000780d00c003e0004800070080c0c00c01322030074031030700384203a8812021090302e8600d284104022007030b504011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 979556402 1250 979555152 979555177
    0x170a0b04080904050702190f050c0a0f080c040510030308040204060906120b06030a030f0f1403010e072d030c2006071707090302101e020102030601090608040f020108040206 76
    0x268185410035081c0c940c0025035003400380f4102000140201d0002031400020386078a001606196400e0701c40d040680c40d00501200d99019040100c2103c0d96005031403400b41020421134500586052845480d1120100e1114003c0c0e0030402041440707040c0c070300b040c802c507605401d200005607a2880000c00400f55600200040361400101280214180d04040b030590310582051040b80c440101b09551140d00341c0300100000d01e0405080100d51003034070310520200e8a4104100c000090300c0845490750001d0f000361b441048404100202c05a00807010408400b02007400d076111a4006444020020f00403c0d0405042e03d6014004c083c40c4140c0c86003e5403019008441c0c03001209552450b01c3e61001e84c3d205000034500e81c105560501d1340d000e418041e910540712240800d14542c02c3c01241080403031031906115808682c0b40d6061041000d12120390300b141c2c00103960b071500e48005001c45840343c000b0420410880c0c100800900390442040f5460340909003203c5c581d84520015040e40b084d0400c1148 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 979557652 1250 979556402 979556423
    0x6070222051f0e0c03041b0306020c03031501050306031e070503150108010510080a060b060702031504170a08010b0c0102090a060c11040b010e012a050604200a170a 72
    0x40c004103442c284a8450000c582c100c6090350312803150540010a43e908601380c03c040000c02d000419072010282130380b03a00c40b2140e6087d5a02d484103000c81e0414050940d2903000007040100c02505501800c0c401e00702405c0043c21030501c100840ea4507104400c0c0c401c04040c0308104075000b03040810443c40100030042c01c84442c0c030102000701c6c01d840c60130320a0840da58281030100e4000c0082031401d10070380d201100140b8802c00310740c55075000b8200440c0910b40050b02000030a000d610240215111207a4400c4401070700d0900d49015454003145121946407107a0500076944100e07800700c2c0c0103044445150803641c49c1e01c0440d01c01402442410492a800131141e4000100e09401c07503041d00019005400015880030044188415514844040c9000900b10080c0044960188600700c00d21540c4016036501c0a074551915126196001d806541c01d6210808000400010340c1d510703101c1e41d1503003d054860000ca40045500c0314600e0103210700c03aa0030303070a50f000c5442d4100582d90500b50000d10440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 979558902 1250 979557652 979557661
    0x31704020a051c0506010803270d0b010306020910081302120c0907110f0a0c15031506021b040c0804140f06240409020a14060408030a08071701050607022205 69
    0x3c082c100c0c43c80d411030707043c007801000185841c00441030b140c01c115084c107107520100020088000f1040c1178140c3e1070384100002c0103540412200368803540078602c40c910050341e4044401c00c1043c0c1d51001003140080114042c00c00c401910b003030701031207010b9a060320381d02d05115a219906040108109105801c554504208482079a02031010a000204e00e02651240c500c40418680c66460002003e00041c13041d0340304210032042811500d1654440c0d107000220302d10b8101c2c1c60f0a11028a41c0020016440125260703281010308204020303061040781d013000074911219000d4401c84004201a2013900c07080710090b49520140b00d081107019100060f03aa0501c1e00e056042c0c035050ba00e54007041000f040ca03c049925080501c55032070400d070010140d190340d82c41e218480c0a940085180030750400000c6c031000a400004101800d4202c0c1e6a4481c0100d602d4400710003000454050942c0705042d880710010401d54503924110b90016405860603480800d500c1040c0d0408c000440c1c0bd0800c161a040401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 979560152 1250 979558902 979558939
    0x151109041a0a1e061101020d06090c02010c05030f04030c050316050a0309090203070914060408060a050406050c130b03071e09050a15022808030c04091107031704020a05 74
    0x407150000d00300d80d5001c01036154804401c1000420b0482c1d030450608050900001e4001c101c2e001c0074030100b5002501d0010b0f03104082c016200c10740d200c00d0920740c841d0341c440d02d07058080c01009482d05540c80c18034150304d0034840090580c0c4020b04081c0600890041030020320005004880785c0d000451010b200c0d03800720b81780007503880e1000030342034000410310000452450b00d0b60084071b000d02c4107960782140b51400c1c9980140c1e00486024040d0b0700c900100000100318106200191040c1e11100b0000b456103800e04000d410350704002c111030400d44042040480f281555890501a0b440c10340303040b030301c0b0b41d02c0010980707064002131002c80c02d1428010007080c5c150b6000700b03540d0903500d081d071785030204a6880354001c070031021044840c0d0150300800c0c001e60842c0d41c100c1c6440085903501562140b895056220209140d009440214020320009018851303640030307005a2007511000c440740d900e810f6803601c3c0242407581e0400d00341140010b0b035000c102990f071a8180d40d00a008003c204603040030801030752 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 979561402 1250 979560152 979560191
    0x60329010302090603040809130b18270c12030705030f030a06050918160503070b030406060321030e07050609040207060b030613020f0d0f030507060e06010b0705010b030a15110904 79
    0x238a8814940c807500300551140a01540800c40806440c61301d106150a44050201c400100f1541c451240951510701040c1403600304086940c0880c090040c404909092145007918100440e0b4607600030441c040c0011800012580554003158000e51607841d60340b0480090075480c2d2106900002c914284060a44803000580d0001004000c8030302c40905004624020310040c46160341c5504003001c100000d0070014001c5620a2240a0020304151039135a100300c940d6090130071260082990040a422a1305032090316400050040200170b000d02d4280014003920890320398900032900440c20b04100300e0341c1e410402407040c004041d03030840c0c078007101202546002040301741d118901d0310024070f0850a1a03424004455001040d000000d841c0361010388142d8005070080f15420350f01d245c0030040780c00500c20f5038045c0c107900b1000b544e10103031800d02c5802d4170941c0d000944640c002d94582e900180000c01c00344101000b021380400c4401c18101c248a1310f000d481e9099400a08240c0c0942c0c1c488022200c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 979562652 1250 979561402 979561417
    0x3030f1125050108060f130e0309040e0109050d0201050f06040c020c1005030718030210080405160e010f061704060c02030d050109050103050d080103120e0d12020f070603290103020906030408 84
    0x80351550b90b91004104015401303040821a088661000a00001847c2d9000600405014000ca03858107000d4000b240490710502c094000a0355501180c0040203c00c1c0040a00219507200a0003103042208002d18003903000340486d40704030340d94042c24814034001d011008a140c00200302540030000303420081c001c0d500072038035000012210441c1ea07405103182040f400a494024001140c5154403034000d84102501400070781d001e108103004400800c0e9045180030140c00e840ca0030b032045526286004c1454a09600302e0410320140c201c881c9244003403244d0141d40f16400070004030780200d141c0010b9096102c1c00b503000d81c1142c100000400d880d42e02d0381207203040340d10900480d01640c80c00242254110000c0c0002014000f142c10000201c5118255a0f6035845008181003030180842c2c1c0d031320307001c08090300c40400540c102840344100c0c02424801a801008070b030a0500c0340d02407070101e0040000365410701c9180d00200180e070454503417081d0305403145600d000d8030565490505042480a90b0411135 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 979563902 1250 979562652 979562657
    0x1801090506060406050d0c0507050307140c090f04021915020a1401180303020f0f0403050109030f14090402030a0b15071203060f0b0d1b0507031803030f11250501 71
    0x1000c190300d0b0401004071400c8030354540d41c040c102403540c030b40c441c0a401d002e6141c008009013805041c2c0482e0307040c801401844e2182d043c003111400025883d44c141203a040886104455910030000e1401d40d2100031603110764105d48507140a280d81903045103440c000e810056145080a0420f46101d0700042e1084949015028001603004000c1045080e030780c2e603a2040c00000e09407280c03080080e009401030121035212510880c2490138030041e140b0503402030351041e10300d6034407410760710203243e0000300040c2c410042e4507120a440c5003034003920b00e4a04c0707800840d6001c2d075400000550b1011241c1d1180301003c80c000c10340c1c801c1201d06464039203117070001c2b102178407070300b02801c40c00d2850fa0192203103130101d81c402d80000742070754030381621040c43e07801907105a42840e84601c0740c08103941c0ba6400c981c1038108140c5030282c94030240d08004141c1401411100500010024148040303070300326981c08000445450700c10b00148a038481c0c541080e07001400540071603400030f1041c02000c000425042035034420fa = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 979565152 1250 979563902 979563911
    0x1050313060f061a181c02061c1802150904090b010326090913061b0305090c04060803190c050d0f0e0d020f13060302150310050118050d0f02180109 65
    0xc1c514444e07510072040e801030400088150174015060075003140180d8001e801109031903210750b80100c2d8999214101808450b081d445040c01034040a202c0e5207154000c0b244811071641980d40442c0d04580140005c446418001c20658840d0f52182c0101d1000c650200d1010242d503501c1c0341411140304134810300601010480c4103115200042d10a8990034003000f1314103106501c03410010b0054a800200503030b0720307a49521043e00d83e0f5803004000005940c0c15500043e40b450100916400c14150b40c1c1801d09c914180300301081702c1c80e0b0010685141c1241600004501c0c05190003d851800c6918001031281c081c2504082c8242c0e0010100014140c0760744030001d1260100703041003c00220840000c0d4043c550704c0c03c10095080c140e82000c0001d040500c00115a502c907000540b450346940140e02900700000100070841142d4070000c0000c1c803081c04e000584080385414807601d0b0016001301801281e03424050707014441d00340b411102c030f6034002c0c1c8450110100c0c5842c818145a00b400b902c10840e041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 979566402 1250 979565152 979565189
    0x160c020f0a0f0f1502030c0a030f11030307021b040b010e060c0f0d0e03010b09270708120c010c0c080f1e0a020c01021c210906061e0608011401050313060f06 69
    0x31048561f81c41441d0050100741c9641da5080c0d9060400b10b280e80c0412010302d04070500d0368401c000540c06000b2030340040a08144103024500800e5050841a020398185124101582d802c00d039a0704040700c00b16038441e1110f081c49841340ca0180c0c6c40e003e903c40c038414041400d00c06500b000e03e00c80e22403c02d5009021030720300041841030054095034440d00380021511102d03051740368500030010a07000c4400740c0b41c0d40f070354034092a803616650b541c11141002c2c001480f5050007109200704070050310541010143d29040383c6407001d6034015814903d00724440052074200460005540055a441d42c452690322042801c00003942c030901a001c082c0988a9030340400c1ca0f995080c420030180c02002da80c2c60b058142d0351a070241d031040103c400d0700807507a107c00071500040c0141c0580c0010b400d06510b00340c0d0001c0307945610640c4440c268032213420b104401005121a80c002c040300e008220081c00c0041d540d86801c0e03030b0340110b42200c8001030b060303501c2c0000202c041511504aa800c807110070a080c0c005058 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 979567652 1250 979566402 979566407
    0x50a020304020f0d051e150108010b10120b06030a24150309030912080a0206150307172a010909020f09010309020a090f020301050108160c020f0a0f0f15 67
    0x205480103035115000801c0c0341c2113841c140780c85224151041054401140c2c14020092056011200705c04aa8216200f402c00205480441078010059000240952000d410101c1d5034200d03206034800400c48000d420280c01e090715040135001150140c085c50b980c0c50712100b404001d110b000e5031540c0c8032100001c0800d41c8040c08490405584d0510382c7c0401600348580d00b5402041b11245c21814441d45800010b407d010710552100414040c0c440b02d681c4e060030710780080c1031400c01024003010b415007480303110480e200020010203032041c4402c01101d000002d4241c40c070340b01c0f1481d103a42c126100d0000d506083c2002980010110100380c0b80c0b020810344031821201079001740480015440d07000d00c0301e010658813031b80100c00721600240210117000c0d2141400010707038a128040030344c0950004010403031940d0100030150b0000d03c0401180a21948420003000080141c030003a205036484081400a0303a5800d900e90010210000e10110440d610301641d80c00050500c690b06004c0305003045400b840b030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 979568902 1250 979567652 979567657
    0x903170708010b09030a02031f0c081603021b030a0f180e04121b1406060d03121a030a0506010801140405060a0507031112043507170f0a03050a02 64
    0x1420340c40d540050383c20064181000c0e0401a11a80c0c18850f944140e0050303141400b403084241c032500d08040e6004610f01a400a0700c50104510040081c07110402c104410064401c01d02a019885c025135150208520301c10b2000a4100720082400005007950482d50070140e1000813546a84074240942c01d8070074540ea1032845449403000d1580e2000004000403da48207015281c8810b0615882e100f1080700440c1011907080c4048854100b62100600143e074108812070780400120b5040003035041039940201009050350440009645030040c080720000400c450781c00c8007801404071882e501c41400d089a41351004e100d0340d242c135480c140b10000745041d031450403440713240c0141c010543da4490560050003008000d00314010195102a014407088102c40105084049051000705a0405041011840030b5121440c0005848681d400e8401f11000300c9a1002e505002d5581d03440c0c211340c2c104403600440100d512a952800009c50584c0c22100c071020f409800f000b03550400180d6030300c602040891 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 979570152 1250 979568902 979568911
    0xf07020c010e151204080301090e0304260a08130f09110f0c0c060714060604090507140d020301060902031f05060d02210906061203090d0219031401090317 68
    0x2d2482840308010300f00401c00405699907400482d10301030702d010543d0f0b0004d805032400c0310240400401008403600e01c1c0501341260180350061403030a0324103043d018420a810383c002c3e003414201d5404492909060003142e2075250440380c20399503149100c0007401c1c20001030041400f440407008012403808038070b12031110380313003094240c8900e010401d5584041d581c1206220142c0351180201088842d00d0304000340c2080e80c85016502070303202d1031840e49070809400074029401980352000305000b0075000121b1342c0c02c0315050101004103610720b4011901201c00340001030340540c201035000500e106207500a41c8104080d40081440a218501e045080e6029105131640040140f01c0041020350390350003800e40b41d0280029122a070f02c0070700c185070300400848100d6a16045030317003001128100381042e10340011800c0c01643c03a184111001a138055075410001e4023070300000a251004c101120b0005000d1178200440070003446e030030100d06028064030201100014813a0003c8403c00c40890f40c400c0c0203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 979571402 1250 979570152 979570157
    0x90e030304320703120c030806190905090f010b010f23040302370e16050c0601090b0f10051c02040f081612050709050702240f07020c01 60
    0x4503140c9407511440310351116032110b0b048146503001e4001140d902003120082c58884043d040091440c101000c3c0714402044c10014041703103001c900c2c0020f0b40102402e6000d00211a14940b00d068900b181c60740c0324854100f0102c981c5480248a0651000650070003c5000d5100034084039403260011200450b412000700041141b03414000f840105800d120b0a0009552801a090036541d8000899800b2121200c0c0c1c2c50000c1d4620401541c45849806407140d60300001104910b490002120203066005000d01c590490745020001454822012110714075481802c0f140d055860381b00b041d0040c554000300c18810340c007600380382680f800c002c3c2142440c103050340c1382d96003480b102d0000400e00395182044020542d508000100f55813020341e0180d00076003405402402e580c020909031121440003074000111500c0e025070280000b5400041036410b45c4c070944c40c00310310390311480c20691074003650030081c64050b15001241c954050080f10210701c00d08501123000003a48601c50140c1c1c4032909118000d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 979572652 1250 979571402 979571407
    0xb070f09060e12010b040c05190e010f0318082b0c0c0209040c091508010b1008060904110307080705041a101b0506130201120501061d131505121f1d0607050a09090e03 73
    0x21033300d010394000c00b400c607004a443c61440300d003a905c401455009041d40c84078120b20a245520a001c2c80b540c001e128210301e40c0030041e0070720619001d0420400c4072030081c85904000c1c000f078100304052800d500100f401d00340030b01000001d083c4600700700c500380c002d442585d8602119040c1c80d103080d806003000d00201c4d440720315580d11042e00b80180348100402c01e0b00c17070800302ca08401058504000ca400140b085001420340c40741004100405e0782e055801c0c0c15400880c8084005d056940c03080410a0501641824085245455045041c2100301040a021400f40c0703400c01511801600d2402c401c03d00c01d03641e00d0000020040002c0c00c0321001c1c021040040d002603982410102101008010200010062078a92500316480d00aa07050410010380402c00032001308102d0400d50141c07001c1064403009401d511000001c18012002800540c001003525180400701e005081d02550042c56080404d4907010b182c42c2034090f000794082d034010000100704000008616500e44100b40041150001851 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 979573902 1250 979572652 979572677
    0x120304110f120d090f050f102d020c1005120105090612030c07030b090d2f030706090b180715020c0d0b070f09060e12010b040c05190e01 60
    0x4103598041c0241e80080d20780d00c01d01e90a240801ca2180407074a190303684144141045202041800d20f80c4c071090007003148203031070002d0b41c1e10700d5405000410149442459009007843d071110001400742e80301c0a500d44005c0803490305034041042c112068054038001c03140b1050030401c4845105080c80200c42250020052199240601e03005400420081c190100d50089400b558107540c094414514175500c207610070410041c40c219000e40c0462031601808420441c030501500005114810104810003c0c0e6a0100c02510080700b1100b0624901180d88402552401c4002455400c0d07080e50080e20382d40026540200f80300100c0c14452130000a8000c0c0f03407030103441500c5044048000019030040c812460510788424038032a8030320f4024540b00110741000400900088107016403541086907988085c0b110310740000d1005400441a62514801022801c0c05401410070038210f070340c002d003042c0c1e50b1120550b120300a0107540c8007000344805e454089000a850004250400c1c5021810004424 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 979575152 1250 979573902 979573909
    0x7120c0f022a180f09030f1605100e030a0306081603081605010203070f0f03090b040b1924140d030804300e0a060816030615020109020312030411 64
    0x2034010907040b400c2001110740040080d10070340c1d4407000512100d2102c1c003000400300c4d030a40c141d500010b0b864080e5260031203070000000a41308000b000c1003003007420644981085000c0241003143c0007945410403909840e841034a88039841005070100007428220007241483d00410f02501d842640c0006856040c84c40d910900310341c106082071300000300d06080c04d002007230080c0000d510800480e40e07a21032588003241c000e041c0d1a41c010710384003054901b03106440051040117401d5001500b080c0900840d60390003904c46086045602855412810550b41007100e40603d20004100540600319488064581c11445817240444500740c0d886040100544042030050803015000390180c0c04100039211b82c1c00040c1d94440101003c1c02010808100004019a0216080c01203a4007117407210045490001d000b0150800601401c5048900c03020b0401c01034040d0b8014070080c242c0c1c0031100c90119a000c8007a00900d40342c20140d00038000c50040401e41807590b01101d214036807020a24042002034800d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 979576402 1250 979575152 979575193
    0x3c070f0f0e151602011b0503031b0c0d1806031e090c0306090c230109060305060102031303291003030f14280c0f060b041407120c0f02 59
    0x5507500081c1d500340d40a150440c6400a00040358110707501d40781980383c2d1000408224880344151501d034550a81103000a03804404c507038008004d66216800d655010800c080e00c0c0c451111285070504c030300d5008444494101d000d0401203044418207000b80d5980350701c150305854100c94420129100645040034012055001311001400f6014022480d91255a0a070480313400783c0b003c1c0d9103140301a80400c04a00d004410562803502c07140da80c81085002000a001c0e240180100310925403140300007940d50b40b080064514240103030007901d0010b5940d041c6101030000314000501c80481c00304a03005c5078000c0c22105401b5003ca0284c22a1711451900c00310b0b61100800e8840c4c040154212420301400d0145000e403400011000f0400c0195480c0607110307102c6c00707861800e10305001d07101c081c810119100e035a00c4000544c000750045205544080024020403442c208401141402418130420540c0400c45d1a000c3c01602000c1040700d010200a41d09141103080000050388111b64100d14080c0001c02d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 979577652 1250 979576402 979576427
    0x17010b0d0b0709050d050106080105010b0a0203030708071e0504031109010510080601050f0c01050a0b03070510050706020d05040b0f06090f010b0a030b0a0801020903010f0c08040b3c070f0f 83
    0x34200002c0c2c1d220000a0703010207041d117040d41d242c1e4582c074040c440794030b003840360a0042070640503071890100303103c2d0f01a4032408014482e4090111030000100914050300250f045620304120042e41c7c02400e090103071040e0018001590301041000402c038046c1840c02c0001c0c1a01c40042808001100c000403c0350444402000d0504120083c05102c244034840400b80401800070300001c030b620300d007585020080ba164841c99901c2540190f80400c00c07901c41c03100c5444560741030318125a83d01110b04040b000703440396641c2440c1c00c1e0b00d0b1400708001d02551200d004d00030f0786010700d0413400d41c452004004601c0000e48080e800c414142c0010880d2880050080007a840542004a482006003000a070380201079440b61400365000915501d45e80380a00c0b0b00c03c14000e0108041040034640c141c01001e08800a02c010800c0b9408004516901880b118250b100c0c145819060742048180d140c1c00c2a4240c80307500306290300e1070600841d034464011080f516441000d980c401d071031009910b004a031207201e14031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 979578902 1250 979577652 979577657
    0x2031207030318031e0903111011030a020313080a03020d03050405010e070b2a03070201030b010c0501020d060314010902280503060901020a1b08041206110c0717010b0d0b07 76
    0xd59002000310038010f965440d400b13901c41d00b541946461a003005a142c001200c0108116075005100280c600d200c4410b2107402943d40c0300104007801d10a4590f01c140c0700b5101960712000c9240f060560740000180f0f40003858031134158102e6a038000803582c4804c1000010b01581103030101c010300602c20746c0100d0740300d40140001300b8400c130250021414110241c02004890200294910041e0542205d0f024440e02000072039410f07200d00702019442e40140c6400a041588502000d80f09a100d2500030446039002002159210b86030001d000c010000c44c40206c0b041200440c00040880042c4034008140f0307005400390101c4e080401e140c0046242c4200041c807040b00314040400d05803402c010300b038412410000010790310251346c0c03406001c000740c04140341400001b1646400c009243c09040da0200c503204000220b2505107490800090540001c607020303034450219901000f4200000c01000325403410201c0b450510b40c0c00012426500e1032400640c00c040c0c0e0726420700001e4004c4a402e82d0005151 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 979580152 1250 979578902 979578911
    0x30711061c0605090c0c1e011e090501060504020c060423010f0b090105040605010c030c030e0d051005011505090d0c080a03050c1507080c13050a150813020312070303 73
    0x1240418038441c1005540c480c4140c0d5201e083c416410407040007a000f07050851202d040003902c0c95050f90726000c0d10760030f443c030000506040301d07a50400d4124141442100800000801c0508807503c000e20075000140e410750b00b0500c0018090a140c03080f00c0c0384495100c05071029680d80d8a031421010188170f00502440c0704c0c20440b2283c40020b10031514000940c410110f4010302c84810000b040304107800107441070f482c04a00704166038000c2c0202025030780c142403a040518a505042d03e202031540045504691820f014204008021440301f03003584078020b0410a0f0b1342c940561000c1008420b04140202c1c3c010404448036243c10740350411064400d00e0500310864840f550103081c504040d404801050300490996036a490034000c1054140e030562100300f55141503c0000c00d2105c3c05401e06815090002d1460085c5a0064441e0098a00a0f0000310700c40c0d55a050403414000c9803042c3c1001031694804141c8444004070b900132541d400400504210810414ac0301440c0c0c03041100b1001d040c1d07074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 979581402 1250 979580152 979580167
    0xc040c08071b080438040504050a050601021513050604030f020f0607020c010e030705031006260c010309060e07032906130230060901140904140f030415020c0a030503071106 76
    0x200c030b130b60505d0920780e4030303000e490303138640424030050382c0026100300245403d2004010107a40e000590010400e0a402509001c1e00c481050000c00c0415500245c006c2c099070b000c203c140b43d0860385d29000d00c0f90903800c40380744181815105072126016110440160010600c1005540c80f920300c0c8000d2103802011b5500312651180064900769040c0f25200002c0d40f00e282c00c004484a8501610703400400c0110100c09014004d00b4640300e41014403402d0500d070f0740d101800103220080c0d0055000083c2c46003110000c0c1e48908180310003283e8003004200c2400d416440c02440f05100c00c915018500141c080c104008800d01404080d4008040d0341b40ea0300607246007000d1a03201c5241c00b58400c0c80b401804403003424204103122070184142c0018030040c4a01c0c499410544502c0500e030f6006070442c001201c084d900822a60030702040010220307442c40040740214501685030484080030310035400b01d65151502c0014070800c09150310001d0310580050250b0800300d95540d981008110005051900d4842c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 979582652 1250 979581402 979581479
    0x4020114031b22080708190807051e010c091809081306120506010302040506090411040b07050303060f0109080a080a0e04110a02010b090105031b030c040c08071b0804 73
    0x852803201c0600f504101c01100004910450350140c41c0328405400940e00304504555644811407007920b070a19050140340910014006503080703a51311000382d0701505c2c1205e40c0c07017001c90003551500569511303050194682d28001e5101004456070741891044001116000d04c0080004520a03200f01800b08105440000425400b50140a42e074448403a00c80c82034a0703100c100c900c020b00385818103104100a0100e41d40308002d80c3c4219500b1200418584500240d1361220b003d00c1d031101450205c00319103401003100201c050751007200103465041441001c1401150049814030510045800c00c0c41c40f84085030001c0000d102c44285c90500549207400500443c013240d115440c001c019541c0400c081ca10340760f0a0190b0707000c803035048813135140329414240004d4440da40f445110400302e04078642182c0c1340d2002c0c0311140e01340708014810840e4082e200005800441e0480d45040090700c3c07500788280c81480c0300700480300d69130000e6480c0d08140c1001181e08101652030541b03070f000c401a2035903d8658a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 979583902 1250 979582652 979582657
    0xe0301060f1e0815040b0c1c1a03060106030f05060906011407060b06030c04170a11040b0d0b1312020a111216032105070209070f0513081507030504020114031b 70
    0x9a19001d40d80c0d5417030241003e080b240405480c1c07080c03115041148000b03032101221003e04074503030110001081316003002c1080c5100d0380403000c1a0103018010000641c0758243d4000030410320042c0040c07015030784106c20460030300304c201c40d068040b0701c40812a5843c43c2ca4440035240c814400c441c00245e00c0686400a07246400c229084100c1910004080c80800c2c09200c001005409040041c803505c415982c3d118500560a40c00c98051b40d507640d070b4440c1036907507110f00500c1943c1203ca03c00641c1002459503503041f154640c00e440c44902c6a00071071840d84002034100616400501c1c48151031040010404071005e00d1240f41007501c1031000b0700301c100600303501000086204402407903211700c5402660f0040111414000d007482424042440542c642012940c0d11a5191424812510008905031080e0150a6501c1d90000c000800418070050008804010302016030700fa50403a980c5000440c1a01c40c1110024002070941c04000d8002078040b0145400c51004040c2c641020240101e0301d1080c2c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 979585152 1250 979583902 979583923
    0x30305060604081902010e010809060103240e03070314033114070314150126030d0203060109090501050d0b040830010e1e07050d0e010c0e0301060f1e08 67
    0x1310342031400215a000b42c5c1080c010442804c0080e500d1030413503c00e40d10780c42c0521000d400c0f81601000d900d040d25201c04024928042c0c400204001980c0b40368848d070300e40160340c00310040355801801d1205560b5480036284115000030284ca07441a50300000c8a512150941c001d1074010389015400c000b60b035035a43c080c0030841c136800520200e465030a103c181c40800040e40b509913008607100d200c0305403042c1d680f18191482510b0040c240300c10404110301721903900b4841480c900012031a0000400c2c650000e600515090780c40c040095200d07101001259020f200d050f601000510541002584683d40c46520a005110680c1003100c1ca100486100c000006905407021122038802c88842200161901401200d1000f20b00c03460301e9490715442c4090040303450382d00f0700e8110004a889210b0f20882d602601240000c1c401403084c400b0040c06030803400c11400201d04542950074003410140305030012951040103900c20545411030a05200f010343c850040c0b4640c04210104000c541044405400b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 979586402 1250 979585152 979585183
    0x30f0d110d020c06070306060512060f090403020a120f17130b09010b1201110901081005060f120a1e0b1c0507031b0f0302060912011d0c01020303040f03030506060408 73
    0x60364410416039041c0301d0014451010b047c9842c0041c403d956016087d16809010282442580d4030b030707400010b11200d194405690301100c41020881010b9000c200b081c9035030312880c40b188100108120955003050111490320010b0071840b03d0b104500c6040b0042d071f8000c000a160310104070032603140d1305100707981220380018031380d1204d200e11554101a8a0000401d490314001c10030342040144202c414464a6420340c10041baa02c0410380c48040f010060004000c020185542d8400b44400302e003490b0081ca90412004d91040d0000c3c4051200340071f1590b40c0300108080894621495244000030b18401e1100c0340c120300d6101a11103920160b0301c1d03000c00180108003c1805600d10301e000d8100b0340c4805000c010000300c0c2001000a007010780c0c240401c0d00d40c11603140e615600c00d04085480d0307150b450b141d207800d50b023000c2c2e020030200c84509144086150070700c26101c03505c84070001a81e90f07203c15640180840c80180803400400d1182c0e000c9a04200000c01f82d80c9000e50b260b080c0d61403c0c3c0484280c000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 979587652 1250 979586402 979586407
    0x304150603140c04060e0604110c0a0b15030303090d050f04170604170c0d1d061908060d030918061d06090109050613090503160b0910020903030f0d110d02 68
    0x401d0001c00c15516403040031502804a0b0307003802031070410140d007d003100780225145c03640d4070175003200b44099034101c01d6a813013115040e20103414125520401a10b801240444015050b401e40c1004000c480c031075501c8100404101d0310340d01c2c1c11903882e4003242200c1134581087c8000700e0800241c030b000c045d4401802c4020031309030425003000c616456030540b005291940030044980d0403400418001244840c03820143c0101c400e0440c3c1e90fa407924841d1040394803500005a40146542c0108040c55040341651041103e9891000780200501c4004c0d001d8041a2030707803420010399101e95001d00c1d484130741a00c049501d56440b607100f880d111155251002541c0b884007080914104860082c0c0145814402801142821008580c210403603103001c0d44116116504001400b00030422241d1102000b42c07203c640c41043d0800d5060400c041d280350704107019103451a050380c80756000350f40e82d40e44000d02651070002c40f6494821658444950141c0a5031200100d542142400d0090700640284010242c4e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 979588902 1250 979587652 979587683
    0x16080102185d030735041a27042a1101110909090a080f0c010b04060e0406051e1e06091b07031e0504061832041119020609120304150603 60
    0x1422050980e682d030005a605200c8c0c100494a948078000d051501001c80c604c44403909000302d009001c0c001036200c910004044aa00e101001c1c501111680300c05956407841075210030707200c03400d86101d41c0a20f01690000c3c08440300740d1505c1c03c981138001d005003089032101d0303500d5602e1100a4002003c801d0400d0008900c1e5491001c00b800b40050040701194100000380c01c1c0321203040f03c072030090800f1384590b6540c0c00041c6000d04000300000c603060447ca1021192900c201c400172424450a95000000300d4240442c00c40d0620381034841c05010082c6506407800c4001c201d401e1540c00110040d8104024416544884d04001e103150b51200c16035a10340d03644605084010f06825034002007990310a45082040050107185501494050008420408500c000c0c00201c107000a00525050740036183c402d1f0f151801000300018210f0305500640d0b5400107500380310507602c0c0d41c0110b40d031044a400c50b422001910480701c3c001c660107403291046086039421101c1d50411903056070000c440c03541700010200c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 979590152 1250 979588902 979588919
    0x2030f031e04030209010905070c02180a18050a140a08030708060108060d030e09060402040902030901060f291b0f16080102185d03073504 61
    0x6195698401c0180d510740780c40d690203e5400310051040380046030340c40f070115402070300c0707003a00c5425245c00030b00e004110f1a101c03110700d07e06401aa9040b15a034a040021040701c08d442443e810700c103070414040c1208103410b4454449000011081c100d507802070716480c1700011051f00c055401030019a803100402d181c40000944810300103400207105a005584c0c14000980c8803919070003c500945040003a51201800310b0080e00640d0000e40940380084100000c0c5a41507120704200d0342c801c003410350143da8904110051040006182290101d40c00c500303419403503c24024000b00c2001c4202d492404481c1e0103160501c04000c018414980003030700e0340031406080384a5a400307080301900846c80c0003081a5424203140f54010350500501005280e012414403034102a40050403014a90020405c040342c600400855219a20911404040404400e405910216407505041001503181010b0394907203021040c50b0140e040a0062424400c20009140040b0390052942c40b0342410344580c02c08003207 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 979591402 1250 979590152 979590187
    0x50a0b090f121b060c03340f0b0721020a0315140d0f0605130620030403110c04020c0a0308011203090e18070b070201021006140f030a02030f03 63
    0x450b84103034000d0071800c06411010038042c1076801c0550402e43c2404140001c181c040c041d03000501107602003c06d903698003600702d800c450121030040c5c020902a00c80740d4a00110f064103035a01800104001448000164400c40382c90707080316281c108042e50b607004856004000a00500350b01c40720f038010076084603240d0903015840440c5508500201d0107428001c02510001c044181036100c0e04e100d0f0a214140524440d14801c44c03601f25400b40320510300301401c240d0640382084122842407400c60f11180c1c0c0d00348005403218155000b2001442e6407501d80f400c458000c140b00c1128203034000c1600030320495072035100038078900411074081c02ea41c00307003800c0183c0300c00e00c140d00001003141900b4044001030f40c410760310021b0f00d80f2800d0304281615000010000d08213600c05c03c019502c54008041010001c140140007003600c02d03400c0b03403071079020444468107a8a603445419125640081c0c00c8800c1d1610344c0b0134070400340010b030454103800308680019280c0024000e00c854242c0000881c01000ba440f100b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 979592652 1250 979591402 979591429
    0x8100504150623180103091a0115051c050612010e0d03060b120f0709030507030302100e031c20040e060f0105070f0807030c020904120305090705010e0415050a0b09 72
    0x844601c0d200c0790030b81c0f160641c85022100406124803000030b800c0b6170b029a0288150303c0c0c002c020180102001c840501c0c2e2402c080c002c0405040c20704200300b400c640b01d002200c003850484480325841044564106020b003101400382603001c010a00700b000e481c0e000340f140105200c0c413200200700c2c0201403080a4200e413510340009000040401c190311b140410181110341144003000c1c0342074035503181c4070100c910b01084d0b000108a8050180004281540005c1c807050202001d1806c00400c1c501e2034540e50b40b8451440c44020140581c00410310400065001ca1906091211f4480131207000300218091a03000340c1041e1008400c500c148903040c205006a0150b042007820641e180c55907648503004e01d0000804014000080044d014003010b1294a46502d1240e0243c60000a410240f4080110f907049507100e5002914080000c0d00c0c522000400c201150703010384030b06044a410030f051101414513580700480320126890700050b10749a0011400c010800c00d0f4110351100301d400c00b040306480c2c0408 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 979593902 1250 979592652 979592687
    0x40b070806040e071401051b06010e0a0504020f0904031e051c0c080c0304150207030809010506010306050f1e090420091017010e0d0c061d0d081005041506 68
    0x103d000d032801c006413210035100310050040c00c0304000801241c8030301ca00c0c4800e1040003004503400181080014855042e92750b1070f039400000d0741c1d52482c3c04003150411180a984010803550501c3c40f030504440d202d800c24001c1c07078000301040b040c0307041814400640180740c001030710010710001100840c04508201540c160001d1088100840f0000c1101402130080110000000040340400202e02c601d00391a42e030010080d074890342d403402d002d01003240490307140c0d0055003000c0029007650303c2882510103440000742280c40821441c8203014900b40000c45200400202c0c5080150b0f503a10803a25912032403050303030401044107244030180381381c550051681d4041e0401e602400300b040b1340400d5003c04c1d91181c0c2102c50301801c003100d0319800741c01c1c0d03403614130490b0041c003a144001c41c1d84440801e008a010701420300c401091128103482108122007001407940141140002852164171000e4000c0210280701702550b1f2070740001350445200101d0050801c14210007000305035080a45880c0750072848 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 979595152 1250 979593902 979593911
    0xb1503060a06031703070509040f0504061a011b080903011d07091509020a03090606030c050a08030f07030c020315010f090e300f04080c240a032003040b07080604 71
    0x1aa1500030005554a04c0f5801e21808800142040d103d5000c3e985440002441071226413019a00c110003040207446c16a0103508203a12800908001c4d840021407045c1a0340b003c6054040000700354990a80407411101140100b000f80505c0d03609010310030348604000c000361941c000e5031114921308181940550002410000c0c4161840900f207014800c403a94003402507612003286404070010409120001d00d6640b5100c1e020003400052403a00c0c3c06e452007981d28598451325a181141d0b40e00407003441b110114030420103034001a1080e00320707032152440541200e4110030f003120f02000014090308500f43c90300350800c003040400660301a400400140303401034080c1c0c04071800c000c02100c0f100088050203928121864402640050445803051600c8910b41c0d00d80e52244421901c4010003007010b40b0039000c044410b040d001d507040c5804450060080da43d45000d070221025005808115400b0541d44802c843c12402c00024400a510891050000d00e03203070700d4404030180503208090844c1d030290f40740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 979596402 1250 979595152 979595159
    0x41101020c18060603040606330302070b1f0b04060807081003031205090309060a0e130605130905030706050406091709060a05090406120c080712021c0f0b1503060a06 73
    0xc00602d0781295041e01c107503540342d84030b04003000a40100da101c00855608504000f940c681040804e5024800344204440c2002c10a2000c03003e9010b58040035000d03c0700c43e00400c1d10340031003865403864584000c408a1540b52f4500c5c0300f041a81007607008002040d6404104044d4951001516070b21208500c2c00d58046419610018540d078009078a00201940c0e4801080f150501041039414030000241103a94070800e00c0390040040101010081c00340400c4512004507016501840080d00c0014100a600c080d05030350810181c4603030581620940001c001000110b41c00e4002e01b841140147d101240e0303c0564600300c1030304030b44200c0707148045005000c0c1071060b580d440c2c2259643c01903881c1c4140c0740c10407040002c0040c06554010154004c02084410400042908400480d00c3c6542900c203555502d516031310b0000b59118009502503540c074001030a05114082c400c607101d01030740c2c0464080b072030356aa0300080501507482c034000a03550800200386180c1044200c1d030100c8006c03c148003280c41c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 979597652 1250 979596402 979596439
    0xd0b010f1e060c030809070e01120302071a0f2206052a0d030209031509010c0f0c030207170c0a0e270606092a0306040b060909060621041101020c 64
    0x443d05002010040300c0c00200741c41c180104070803000382150fa2000e12940d40c1d19140d4803100007001408401500a1b80e0b00010320140f9084020b40c803e888624a5291180307175942c2c030646600103818603140307000b4030018601c036801c08503c803400b525007629416580c410a0012000b11221000c4002d105060101441c40098011480748211905c6040268407200e52100280c1032160554450703440d90114000c2100b0808150401c2d00340040c2074844808011740f4200c1201c94041031600030f40075a10070390041002d40300448640d440e10640c10103a41c188040900040ca4011182d0b02c034034010001d0506103c40c0301e2429410b0105660003d1055441d515180815902c0b14070080141c2e210707620900008495a05a0041c040b40750f444800051011a1050030f6400f2a001501e20f540240d02c3d1803841d2505081200840300d101000511004451390b540f01040040c2e03000910840e02081c3d1107102c42d00340d51074040e0306406140b042940d18514003208000900d09090041c1140c45406022828640c691 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 979598902 1250 979597652 979597667
    0xb01030b12100b0d02091303230702010810080303071701060e1318050607030e070f03150506060f0406020705090c120f071704062315010c020d0b010f1e06 68
    0x81400030036085200c500140e04e09200400180d0803061070b40c20408206000c44400c0d070803c2c402d80320310b0300200344400b08011a10881e01981818034003008000701644c00f502841e40d03c03164480f420484030341c544640078150b030000e82d01040170901094583c60b03201e00891005014010318580000c54040810010b8909400c0c200204d0700240c0c1d5905003108814013000840041d070b0400100e6410f410011802401002c1d00045400f10303020700e42020a0403005000c1c18012079411a2285110990800380701c001004080c100326889038040040082008000e00500300910807030b005460320629190174001c04901c024001407101c90100010301044114049460b0000421480700c1d0140c1d4860009a4011248014140c00c1f031f80c040d010030003000095088a07102c0700c0c8168800340301c81d070720340c2c025502001d040e0780c0410718403074a07116034405520501c00304c2c880d036000426444105500782c075042e0b170001080e000344640c904030b40024402d08513017081c1e0041c44005031a1803003410b45001002005c07078 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 979600152 1250 979598902 979598923
    0x30306090203092e23130201210b03120d05011e03030c0f08030c0d1b08011a0d0c0201060609061110051302040c0320091f1701090b01030b12 62
    0x1c9510200700070704035050010540400a0036a410841d24582c2001d8182c04c078035054105c01440c20f001c000520301d20440e1001c0040307640c10386424546030407242245d905aa1410411902d156442d07000001d55641041700c005034114a0140341d566041c68628082580c0d01600f0038206004c40260114180f4080d0124000301c80c0c1600d8543e25801940c50001101005440042c2c031200c80813050110060342c0c140100007103114103c0030449402440300d800c0da11052000b150000c07528290041000d01c04180d6590034407a4007a9031a031814813056802d004840d9640c82c60b0300180e55038030081c020701e5003140c61000509131303509020a090400300101540c9000410b00380101584420201c0c400207150415641050750040041c043c44024200c0200180000150040c40a095003204020195641d04075002d801024182d1441100c2407400c0c44024460340d07001c00c040102007840031080e03178807890000e40a00156034021030402800300004017501d61140080c0d1103106000c40603040807000141031341e241c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 979601402 1250 979600152 979600183
    0x7030b0619030b1c0803041403040b0a050405040c0309170f070f0f0308060102061003110f03030a0c06050709051c0f050706080108150106020c120c04020a05030a050115050412020a0f030f03030609020309 89
    0x20308c03030f10621411401954004410414041031074002c154121018100703854040e1410400200351010403020f80f107003888040d08190070000d1204200c0e40d0b1100404900041c40c0c409403a100f001d036601c0c0c0c40051003c00030b0b228038100c01c5012007090b600c9404070390045070074802009a0b092030601d00c4402c035058400101b404041100310661922104003403d42e0751401010380e0745441800c20301030024421510700b1562149010005000c040c050307800c10b0140c540242c42910a1001030403450b0030000102c2083d079807180780440e9440066000c00840c2c014040903621302006514145145280042400e4401c107401e01081c014000164000b40001000f0f101305ea03c40c1d100030284c0f00302410079503106402508140001044503030980c2000040d800f8881d68042004540c0e658089210400b80303c41074200043c804000400c0703c0c8c0c0045200c00c00942c00100700351103140da03035840c07688651955482115100c0541050760b081c95090300c184401404180e0007980f85142540080f5100c1345c51480c0f0016 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 979602652 1250 979601402 979601423
    0x106061b230a03020708030a020c090604020717070309050906181f0801021b2e0213090f150e010b070804090c0201020921030307030b0619030b1c080304 67
    0xc0c0000c10403110020104585038070501002400065102c842846059025201c0d520340002e072420000102c0f0308030b08035503018042e098415420420f12400c05090194413940034006c00000c03c0710b00005040c160403190364595504403070314000c5e003158450b074482403040709500308100340c0e03441c1d40c040c02c0880510511180d8043c0d40701c428886001328043d0030b880d5604010100071822440540c028003401080944101d0080c2d4624402980c684001042401001115220341d40310320307594800c810a1b18100c0c0c005414421094004800021f0640c08009072548036000003641032001c3c42902c0301c4c1030320445c040501e10b0034840014051141882101c0c02c82400207070800501141c1400c0d078014041d80e01046c07100741e0064400074040c0d00010352044c070401001c8030031220384202165241c039000c1c52101460841d6500141a001020700b0381105030021000c00c0102407007607003400c1c100c202c0710b210b4a000a02400e1842407110701007000714410794038500702160f107020038200d90950740e00a40c814810761 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 979603902 1250 979602652 979602707
    0x210a180f030318080d0e0c03070e180d0206040c0e16052a0601030b0603031305240c010624080103120504170303060301201804060f180608010606 64
    0x2d0003003481d9050080e840d070620b02c105041004800080040c1c102d00700c07090140300ca000c14440d44582009071466070581c8120420003509210b004c889900012000344150a550755243d1141800201c1340782000681280003044200200c030100030001e0416140840b003d0f140c641007102000842c0700c104410b0190100345414030306090507484000040119001d407c040365800755581c0d40382c080c00120380d00d400000005030780d41000819511517000e1604174003440b501c2c12042c44020307203140b9007d12100b04003a009a20f481040070080410040c0c01c00000fa61030b241500300c2400c40b010401404a115080585240c01c6d540045981c1c107681c0c000e000b9031610031401e18151018892a44082010202d05050300704401c0084003440c4103000a034001c2c0403031181e04001600c28140040348401e010350078003114010303003a011120300d0103000107080040e00d15142c01300d0000403540c80e40f100c81820b01400d0381c091500c1d10b50051500a0241000901c145400c1610180846540c0f0000c9606c8521864109 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 979605152 1250 979603902 979603907
    0x80705071424010503250303031104120302100c050a1202130f030c170105010f0315380d050a1e080301030b06030114010503032706210a180f03 63
    0x5120340d0b00d850050030101e104120300a00d03440000d00c15184240500702103d03100c5032a50504a2810840f02c20314083c050440d50158024606000000c0000f00305220200d03210004000001080f4000e0b00107108641d56440114103a400002c1031078200a81032000d48000c0343c0140c40419013415608002d0384511074500a0811080d0b1640040b00c40707900701b1000001d104001c1680c0050760f10b40315000c0080c0f40b46641040c26a0004e101d01091850b0190041002c01d91804903000c094410210206403001d48641d20703140445403607032200e131211300760b180c29441480e42d468205030180f081d5200c5480201075202c407901d0390700c1349202401c1a889552414100e0500e82140101c0651180c003294503941c5908103800d9460089800c3c0d0701a61a000d5041e010000d1990703200c0c125900200198a0010800c0c03134114000c10003601024514140280e0f90429503512000d0885440b100b0082150070305440035035480c00801a0941000750300e811140c1c0d4908080307000c5040c034030744c1001e040041a4420b1404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 979606402 1250 979605152 979605163
    0x10215180a051e10020c031b2b0f0c080a05031b040905010e01050405090714030304050a0e060a15020a080913050a051008070b031306150f090c0807050714 68
    0x802e07a008048185060749400040020900c2e682401ca803200c48148109404a04c2404405402d45d882484800b0080610b142c41100741c0c0c02110aa07510340000c00d4503502c910049207007142c5000d094071058560103a2190b01d0b0005a0300ca440c5c200c2000c1c3e9141c840c80782c0b43c85805103040c10404008002410511416a40c0010b10980c0796404e0307a0307030b80e9130b006000102400e02238016000c02380000001d85241c50300400c0c2c021485880500442884d01d13808420703031034481700d00541600081c030000420356940d890904c0240f0346104c1c0f601091514004020b0048181d8000344880c0a0f5284003101c0c0c00c0d800030310120510740c000e0b0050b5440b6a00d0002401140340e400c050402c55040204001080001d44c014030b00039080055a01041034031200303a2501c580350ba0060780120f000500004102080d941041c00380e441c014080001d0101d840c210340455600641c0006820050081042100c04c10910410100201a00e0110100e0a014000070034034402c1d0b070806400000c424002445601042c0721 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 979607652 1250 979606402 979606423
    0x2120f061203030f10090c05031f0b0403050102043f0807120c0201021b1507020a1d070923060c010618090303050903090105092202032401021518 64
    0x40700d4403480d04d03a1090804240444481c40302c42d44000c800180c2100c640610401944107403506410b640d2010030340380c01c4581102c800c5039904150320340040e1112181e001003000d14041d100160355541440214000500822800e07150180c0e101503443c81684c1c0961203920809004000c1050411907042c865828081c0000141a11200d1403600307101d15046140c03040355038802c0e003e4a5002c188c0c1e541000c01c580f10414565040520508003034002d6505100a102041c402445825442d89541d00c0346102001e08103002000c0c04007005000519030030001d04c100500b008a0b01c6420000305c501034814a2001e244014001c44001c1603050024a084d0003080240141540b00e41480c140c401112024044c114000e60100b841c040104250300c0c00881203038002d0348180c41d01880d1211590a000d0343c22100010940b440005109104125005000441c019203045402c8132120600403540030300088d446c00c001d410355101c1d01418001600e24840e107548000c118541310785000080030040e04156810342f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 979608902 1250 979607652 979607689
    0x60507030507050316030e031f110c060c071703090706031e11091e0f010e010c05060709030c15020604060c02010e0a0b09010501060c0f020d02040603062d02120f06 72
    0x1800c01e034551170780c1101c0d0001d14001d0f910074400c0c00410041c140c61f10509900444205d40b00d00c041104a00603400c07011401c1e180010142c034040c400a0500e00b080d80940e82ca004500c000680401440800c0f640b10750402e501540d0b941c0fa6045c5490615950b5140d48a40b00902d52518940101001140c0080c81c2d141041002442030070704850200740c6641c8045000f920801e2501402a80d03814000d20300f1504810151140d04200055001580c003800340030041410018800030800c001388090080500501d0507445040e60700c0e09519000d60541f81c1c980200c1c03100e030030b0075403840c811540c0018041e0b00940c00c140000b6010790038160407405440c160f80b26400510400040c0070400180c0652248242e407441c0c000c1100d640c8980007191000100700018003036108019401000d4075040c80300c583d00b10b2000307100250f1148c0e203554240c2a14920050005d0b142100202e0758244c03c01c803460840c62030043c1004602d44502c10715074681c44c5a01900307041e601501240020344076102d50252149000c0400c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 979610152 1250 979608902 979608907
    0x709060207090b0f18010312020721050a2003012003040f051e060a0e06060108071215090e010507020d1d0307052d09060109090506030c04020a0c0623010605070305070503 75
    0xa17105100d680080c4021a4400628a03044041620102d00354040c2c0c1d40300c44a42da41c0e007a00500d42d03810054200c1042d06c0b40c0c05401100400100c41500248582a50b03080446103400d81c40300300742c00c40b1038080070f14400303042942c01070300b00c3c21402c0308403580141e02c2014083c900601e41040c43c686aa1003d080d5203c04c3c49030320700700120500040c580d1040401c1e040a0000d0318020707031100d0721890251555804500800003107001d0303501426400002c40c1040d0780004508110b0045070746420b070594030810016a03180960320080000f801120341c006114001411940010700004107051990b98800007100c03030302506080c0c1a81c042c0250001400c0041c803690400164022801d070391070140300000a0070070900117101c014201420030341d1060740d05850300b81e0180d183c0322801c80030b8000140703a035502d0f004028403150103665501c0a006000d895543e844880000d62400c00c0807075100398020350f07002000c0b401482a6a9400580c9030641d2882c1c41e006880e513205150a07100c0b40500c40c0b0061103400302 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 979611402 1250 979610152 979610179
    0x20309070e16020304230a0303080402120c0109150504031a34030e010e1c030c0c11010f020304180b150309101503020405100e0709060207090b0f 64
    0x944142510400101c800464030740100d50525000a81000009600207010801c881040f94496898a50529002461411401c0001350800720560030480100f0300807001e0205604001d02d6184020303030b1941c01040307811007100c0068500102403240c3c1e441d41c0e000c0c000c103201030f40c0700e88240c6000b1584a1120b00340384c040c4282030240d00e04101c40124056446030a20491948452900c1c801c08511645c0e45013110324801084024102e0140b21024942d00c035032085140080810544d40700c07014046a0340b602c0019444010103403001d00c4074010400c46414500004100c130742c1e808503c00042424111220040004c00b6404c42c056540031700520b2021418030300049042d0b40109031951412100c0180e21000d201020301c40d4041a902d5401980c08591522008807041d44050f00340000000b45c40205641da900140c1540d0b000c81d0310404240301c1305410400d0245045403160441518203080c40c1503401c0c10300c000d6807844207100380320031907450307032030b080081d80758851080b001e03020140214901014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 979612652 1250 979611402 979611421
    0x2210c120c121e0304230f0105310c08060907060f05181207170115050a03050a0605131502120a1107032717070902031603021c0203 58
    0x4200e01e02001401a41c00b44560349042000319840080c1103154103034403080342e90340c2c01090b410041084841c01690752200740d481e9644041c0c96900006a4002c00b11300c100241d040d0b00352000548103e1aa1034020110001031411840d01e48000400401d07500d021884d07801c0007110300c0815440011340c2e0155109020301030b2000f01c1c9110a90300da0b5166200412a09075013100c82e4030640d06041c072060725500c14030360240342a50726520281030603401c41d066540c0b61b1078140442c4601c14814041a0343d100708945c050700040c01c0003001400100ca0b5240d05518540358551180f13600900108101d81d19800100d5107408600c65444a0b900032203012950308907060380358025407203000008012045100000c0141c0740d035000d4121a00b0710b8410a07800d2100e15a03082e070b10880608100364025a260b0800f0035500034580880005001e4400b0b10111410f0115641c0e041c01080d801c000503543c010030801200d1102c131107414203030b5480c03031800603070342c048010803c001c84c0c95018081491500000a0140d00f12 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 979613902 1250 979612652 979612657
    0x70f14041508100e010e2a18030f12090603070c12030e010518030a0516020d0506061e0d031d040f050610020307120f09091503060b010804020102210c12 67
    0x250000e940f42045407640c44a0b00c40810910030946002c81a030000703003035460b17282e6201d081c225018a013860740807941c5c41140c486810007444028071001c0380001e907402e40303000c0181185403807440b0040e200035085540d503004548903203911107016540000108030301c54401c1104010241e04249a4100d031031b00c503400203000d0301c0340a40382401c0d9030a040108040004124080340c00d1034204000358a002d40310401690319802213485400002c04d1729042a0150f100c000a00000912402c054a403034a400b000b0014500b0f0960000095004903c0c0c400815031034281070450304680509041e02509080d44290040310219181c8980041c1842c0704a0410910781e003046002e840d0480300e80c050900f0117a0226904e0280540140c081c140c0d040031b40704528011005401d01001d1031904a070401e4a40791444180d41c05185007102e80410030b002003090040604c982c8040280918202016041640000790b6811205d00310070080c00110850b041c6000c800c40072160062021410740e0328000c004036001080b81c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 979615152 1250 979613902 979613911
    0x70b09060a05180c040509030c060124020304140d02040e011a030c0d020d080a2303040c050402070b2e0f0503190b0a0c03110705061806070f14041508 66
    0x707506140208240307075a8455003040b25404040140032a40480082101800000d0f081c10182e0000b0400c1d014101810300150f806000d803004c4528800031104038032808490817004c10300445d0070900c01440b10b4031103507038074a40c107171812160a1070000c010300004008126a0565072540e62078520b041400c00c2801c507c44176500010ad094420702480305041c4110089101c100070f5005034803c0044c40003400c2000506031032011391400454212461845c82d1046195072907440f003842000c0100300c200b10010070042c018200688056003090100d03034441282c0d6a000d008850f0751002c2c00c03c0c06010040740c0c0c82e6803004401040030310b480c0c1030b51404c4803814211140100c60003801003030100f1101d80000304400c651f860348404500c00740c2e03980d840d802006110340015030b0109511951051503000d031050141030315030302400140100d81400201460451142491a90260040400c00c4519034200302039030802201350811018054108401491604c80e81d00720b0000c495100141e140d0582d404100e15119 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 979616402 1250 979615152 979615171
    0x11e0234170426150103030206010e0c09130c0c061506091706010302090907080615040c02010b01080a11040f060e011803020a05060a020114091b1e0114070b0906 71
    0x40d00040c03516140e6900c143e00440180421a4040114a000da5401c10820004400c15244008465204a014030000380d00540041c0d1009005024250504642e140c0003506022a649028030440108503004e01c2c01d4041e5000550b184c040a0296000b5130744018040d600103002c00045044650a804e007007403500400001521b40500810b017540c0403903905c031400c40410020011a031850b82000000b1000a25909581c020110002064041001603500840750b0550503e10300c070070344003072004440c5604801021681040011b00459800148040e00961080e0700403d40c9000c1a080c1c0040d4803441c0d0008040c8034415000103101c1c0d070701220043c05001e090ba150b01180320b80c0e44044441d4125400083c0d40700c06000010000c0f45007000040c0540d411038000400c0c072814a0034801c1d0308410031168941242c00002c1d501c0d81c0c02c02d01000392506440212481640512404050724190030b2030b5680a040c404c008981c5803000c1c02c0c2405840396541d101542c0b00003840c00c6181507448bd00255030719041e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 979617652 1250 979616402 979616423
    0x10050a0b1f0e090105130b01050417060106030e03072409050f0f0c0a1805070e030616120618050c12160e0d030c031d100801030c0602011e0234 63
    0x5043c5420320415040b908018015508020410a59001000c0914080781401001c005c0041c0c60b141d02101c2403c50405031000e04855890800040c040d5820f111500140e41c00421a2038001240600300b901003a1010240d010700116810384000100705801c405040c0748194890401c06860015440c00050200401e84000100080600c80c00d16018080c80054451000e007486003454680e201036444041840c14807e44054400420706008007a5a00c041030510b40003000c001d0341d000f01024541d40d038001002c000c0e407407400001c2000029000000c1c21555121404200c1056000303043d0b5440710758001d072103440303424610b480440c0f07440b80c400300d0000729220340e100c82101e10789211025400c2d501038491030000d014a907000c42c2d405e262034041001c2c0b00744200700d0317001c184c5a80740c1803c00305140b91100b001d00c0d415410314030101c882c2907000b101103a041c5038140e281c8000c2080043d00340c40c94880c01603100d020130004d002120352510340040c03c90744600d080c1c14298600780b1841035240c1c01400c0450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 979618902 1250 979617652 979617677
    0xb0c0105180f030a030e07031a1015170c0f04080312011a03040206030a060906090906112107050d02030a09030e04050115051b03030408091002070810050a0b1f 70
    0x41d1103042c1c58030070300340d103801c03d11601c54114002e81043c2c0002142805072103009407a6aa083c40c0d102c4900350080c2c0d813440c014100040d00580c22982e5026000b504002e1440d07880e1203000a2040c0007a03019142d840344a600818400c03c0c40760180d416407080c120165880c1c42d100c00c6000e5498010240b081001e510074000010030081238011075124100c1c2410480c41d603031344c5809010302544040c180d1512269541e130000f0b80101c1e9441703900050881c203000130a0300c036117a003000d0042c2c0e140c2c005c4c0180546020481c000100400403070880e01102c01c1400310388a80d440300030558441c010108080b10a900000c00c2004c0c01010f980180c03c564880c0d12125492501e010600084600c24040e0f84215410b1892111110303000f00064042c2c8840b109904c08030355410703070001d400c5800c180d40441d200540820029164036001081ca0780d981150700c001d080181ca820748443d9550000e15068800c1039940001c0f0305002c00c0303500800301060000d8040642d020602141d103071900120070b22440020005000c54 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 979620152 1250 979618902 979618951
    0x307170a17060102120903030c1501140612010611030708030f0f0109020a090614090a140a08030f07020415090e060601021e0309060904290a060c0b0403030b03070b0c0105 75
    0x39400b8603410780c002c0c04200380c2c2c40304015290380f00500b41036040c40140100900714a00304240e82880501001c0303501d165152440b64100500030118a03031080c00c0034400d407401507109440385c5045030031910b06000040c0c0302d07004003800c0d0310400710701800500001003084100102181c616000c0d4000706c1d0440c20710707aa00c03181c01e406c80c05000108000100000410000603114540c01244809620070301840d2141001c000f4020b0701c035a03440450051118801c4010520300409000002d007900d401071494113610041186403440b9544009104030342d520100003941c0301c0310036414003030809540100001c0d0752035100241d40c1c0c3c0007100c03558010f20a03a403000484002c8d844019540300c031004003e50038044d00c1010080c068020091260300103039921802c1c88104240785140358400c4130b1400c04a0b81c8014042880789000d0240c00c20028040d45d0400440050040c0d0243d40d8865094580001c06820990009003030210680c48294000e50216115000c01d1040d44064010441d041841c244440d000d000e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 979621402 1250 979620152 979620197
    0x110607260309060403080601050d060e06101b030f0504050a0909050d182112180803030c0a0302030a1b18050a0e0f180a030c033903020307170a 63
    0x40b445103411a901103800a401804940c0e007004d014109035080c09406100d2508540041d4400003800c000d0005100590400c004902c50320074142c03a001c0c0004d01d5401c244181e00481c041c00608110102c40328240325131041d81942c0180000620681c0341c11354462140000e0302c81c000c0c05a807540120f84040320b070b8a0050750f00f082d444104004000140d498481c03405500180e01c20181d0341404031070308050001d11014040110303148551101c0c090320078202c503002680700f8682c2080c00580c0c01041400f0142c5000d20035a100078415150240c0d480d40c49007680b001030f001c140103080600d019080b06042c1d61380c100d1078003160030407100581d10b401c0350795200300607956029101d904880401500410201404041d089502c01b00d0b400900a4200303055000e1072800000c000140c0000d41083c3c10350301015441403500480f4600295610101d00b01c0006039202c3c0e01010002c800310a0019903c20700b014003c0c41980c0195030080c08600c056415543c0c1c0d1307141c0380e00c002c40c0303031b0002102c5520f20503080410100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 979622652 1250 979621402 979621411
    0x51302030610031b14070f0606030302163f081c02070209070c0f171306030209090612010b181501050315102106090e0f03090d1106072603 61
    0xf001c0079134055481d82942c0001d0440190700400504120010214207200c0c45081031078414032000441034514200241060001024041c05a04a8004000d0300b00c025101410140006a07842c0a1203c4801c0c0b000e59404114003502d2503c0e03440b02c280c02401503040c0030388100480c041d00c082c411001d90061a040b440b48180003940f14580c0c0020902441c03103186041c01407440b48100004c403501589802c26003140780840c05400001c0000c158203810195440382000b000076080541c10910315100088240d10001d05240c0200040301a4000100702500b0403600703410b001d0103c4007695800d00d02c00380d0080003102c0d40407501e00007200e40c0d90554810401c4034801c0500203010a043c2d5421400c00c02e02d224900d290604001c1035501c2481d10201410804408101c0c500000034803625080094064401c10760308506c06402c4040d20151802c40441106d0290400302e82070313410180c151070031104090741d480216410220109580c020070038643c415102905166000b0001e0f50a01c00a001c8117100444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 979623902 1250 979622652 979622681
    0x130f060c1b0201090909080c07090f0c05310911030402031b032a040515120105060a092408070e0a110f0702121f0b060702010f05030a0605130203061003 67
    0x400070011480b160f44a821001c7c80303401a18944062606220300d0042a03802405c419070f56204651104640c030703c1582d44120190800f28100034100000101e100601484060351691140f9001c10712a0f00002c1c40e40a0030750180b00300089422201401410340040b1001c0780039208006054101980540c103000346803034002c0080000d201800d0a6060a031400c24180010000000d00c9502a50359806050b1140c04100c0681000c81c040d001000356240039030011904070307403400702482215203501c18408181d605005011412000d6090f2002d046004120400350101800300d0104141e8004101501180c001030100451070300e94030340d28012690341508100e00c10004104465101005102a101c142d000800c46907000011004241c20004151200b45844460704003507100c0c01c0d103612500c03509034000d860b01030a0140c6a40003802400d00b030190101444004000503500c2078141d003011014050180410a032400f9101c0220080d40080da909840751144004030100f06100388980700c0001c081c0c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 979625152 1250 979623902 979623917
    0x203160b19020304090218130b100f050c0111070b010b090109090905100626011803032a0c110409050703080a230d062c130f060c1b0201 60
    0x315075080c900341040385a842580014400002c1144192015104c00c060384808280d120714482d08000300d400400040585041c03406104403440d0300d503a00031644961081c2060504502c1c0c1d06802d0f1880c0c010825489030740c0d82420103844007070481602400b4058401d01080c5c50300e9032107501426180c00350540481c00590021400c000144a07030308600c81d214003801c103450020720804210000d548080d0400ea0351010380b01b42010201e0000b1402d8100d505026008000c2d0b9180625082e10b00044898090101a00c41b45224200003505c002d8084c0d5043e440c0418425900c60034020b0309080f604441910242c8800f81000ca050800d409981e9000d9840400350a07414110b5903840e8840d04100d00503810802200d060000c40c8103030181895139000e040d07050b291208426191001520a20780007100307a140c0e620890010f500304a20100000c5045a10b104030035a40c04544040c0001b0705400600710200c4807a915017030146540c03044503401c10680d5110b001d00c03080072055040c1164060000e0008414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 979626402 1250 979625152 979625167
    0x907020a08090a0e070207080c0d030207360c17060303070b04061b1205010909020604030f080904050f1602060126011506020f07053c06160203160b 65
    0x960000308016580184000703000d9848413100001a00c0031511100964060542440030403410000803090100c00c8440c20324032034891350b000351907a09520410895507003151516a60181c5c1541e0100c61540b8809550b818502e2090140d000d841c2d4890100003080c0360580d0410714001000015109003400740c010b603e00000d9640d4140803440042c015038540303545d41c231802e2120b01070101d803450788032803a45c40114041d8103059040072100103a000b01901e40c031308181d03d801038440c502500c013141d03084100d8841040c102c2c02e06c01c82622881c5061130b8818900300801040b0504c1324640da0140e07504401d605007141000605070b94900b828090298051a41e46508031101d8480750000a00d5182c03400102da80302101c9140d801504054005e5009600072242050307020000f04104002050220341c4201c0800d50408a01055001d81c251390507800204c1c14182c0d103540004040640061000c0d11469030303900004001040301055140481c800e0061054003400030440305015402d86d003483c110345151010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 979627652 1250 979626402 979626413
    0x309060908120a051308072c060f01181a03040b091222050a0f06021c14071109040809030c150306040b0120030d0f020a120510080106030807110907020a 67
    0x8075501174a183e20901703030081580c09051250f48018042e801c14070003505070b50080c00c500c110195405507080b070781500c20050139170f840b2440308165072400c0c01e00c4500c032a43c00501071014807030340c0c010b00c3c4c444403d90080401078080c0c03401144528010030809a41c0d44a40b200d4503198030360b6940b8455983e5040c01091100070f9100c805003a40154001c604a40c59600c2c4042a5400301540c840c006440c0702c1c610801c80c01d5014080304042c40707107051014102c003610042c040c10b800d44040d000a03a544003c81c10724200403403005074041445006110f01040e1425161141c00c541c02150304c54040c0c0a207410089171030a1041d81d45114000603c08a82155580401d000081440541c52410845c00803500c00e600c10280150441c000c5070b90000d103507542e000c1c20311201502d10030315441c001c0c1c40c4100030000a90347e10840d50340e4101060400440c803a25294a80e03006948107400c40d0409502e05003000041040d01801021100e00c82c0011910304c03080b0004202d55030108444000150700002c0d941000940c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 979628902 1250 979627652 979627657
    0xb160e090906060402030a1d0a060b030d080723070f0c091a10140c0313060f1e020708190b074b08090705030f0706120906090309060908120a05 63
    0x147e250348000740644000c0e030402840500c2401c0c00c100c58205140b00801d01c042d6000e0000d031408180d004140702c480720728004158020040441081001a0895904031400310b841d40d42456001c01c0e0682d11001d42e4204801070b206101c034101c0d8460b010040004c0c003a41c450044a0b20807180f01103032484445035009000740440094000d6040048501404000c1c1080c0700c007900005004800864860070a0818030410341c1d5280c111109103d041c1c1d07000c0301c1d40340e40301c00e129071102c41c407503001d0300250020300050b45045143d4111161074002c44050154643c000502c565000303002d8401c0c15a191503901e0241c481004162081d00e401455034030201001c601010803040710059080b15a80f582054680c101480000201074000501d43d2014842c10800402c06180680411400707001d20380348100096a0b00d41d824840e00701070000280c0102c1c03d1050960051002a0304100c0c01e0203280094580200b01e001d05001b00b81c0412442030003c2000c103000a0740100a03414101c0b034a00d40702c903680c01620301b43c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 979630152 1250 979628902 979628911
    0x160501030e03071a0109050702061308071106030717060a050a0e0c0409230a3c0207050f0d0c050c01050f0c1204150c0f031b0b160e09090606040203 65
    0x2880100001c00c0061500c9148990840c1c0e00b00d1302070210350400d50000c080c0c603000792104d4110340c842d205000f03000c46aa00380c4d02c003481d40b18044560300d01072450450305002c04c640340d0303e038440000700404c00d0351900314030404403e042c00314000000f5990b40e4100540c07880140142500a00035200c02d11912903015030054024104003c0c0c0c0d81040c1d500e030347c0442070314204120314404010402442c1e000c0041e0007a25600900c1d940030030302480b0918000388000546048001449610108070805102803c401030352485285030380540d03031030710703e814020382d24007040150240910980c0000e403a031a00c0381811441d02e40e1f021018141c01e0488000440b543e0300201d0480805000c108100028000104900d121040d1100900c81d2998900485c4441c4107101c08201c03814002d90b50701d4407002500c031010b070308034079035050506824000d8420200e2183c43e48c4014000c0c02c448800c5e0500c04555103c075000c544601c0342d80d48500506101c0c6051055a940603134042d20554040004103580785001e40285a00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 979631402 1250 979630152 979630181
    0x711010e1b04020703090f12020a05010f08041106070f11030609030a09060f12021611041e091b030515060a060e010f05090307090614030607050a11010b1e040c0216050103 75
    0x2640b1040525400200323a40001c6550014001c07003c2107003800c0306001c00a01d0309090840e03109911200c09040310b90001c100902110030032a201e405507507050180c48031180c0000b20000403142c40e103000144203030606400c80c030910903840050510680007040b14550300065442c0c3d40034a10f045803c0d2504000381070343c0c0062040c48480401d80d510103101030309003403800c4594404a2076160a240c8980e0420001e081c0c056030030500100280402c03550040324951904400041441c19400c1c103540b00510b1078043c403811842040004144100041c003500070242d0000780303150300d40b00e074010011441c10500c07480c030204e21301c0d2403c894192f00460072a8862540f80c02c0c0a441c0c58032006c002820011a0f400001900c0d0b42c0e40000d0010741d070300810300080c6100580003400c1c00d040415019241380180714a06007001200408410b10075420340000e036030f01501400c02d281c03108074040c81075440f94102401c01e015a140c4021003402a100140307000d001c10001429080c0c443c240300045004c0e08001500044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 979632652 1250 979631402 979631417
    0x10c1203061508040c08010b18040c050d051006050d0c1203120203090708010e0a02030307080328060510021515040908030f09100b030628050711010e1b04020703 71
    0x14040c00b00c00081c0c0000039141d40b10190fa140a00d000c0ca1200f10680000c20b15a24228066806864645070010700c40e0308489052034550742c624000080d0078003600220742000d0840c10749801c104000859080e000e40503801441302907240c10038011071500c0c8001c05000766000071420400031075080580d541450183c03070303c0c240d411340750103119060317910595010f88136a00c0020304101c1a1420b00c50000d4829054016004c03242c459000a0780d00e019044000c2c08282000010070484001c9507040241481c2592826002c0080c10644600030034640c41410300a11000d0241e0120300d20114403d0180040e40301441100d4441c001512001420040034039001a5150f42e204003069541c0d000e18403a000b002c040040f0b61a03c0c051b0706003090b04c6505041200c9091280c061141e40d00400d0455000c000036209502103120030b0075600b4010509600003117824501401d0240709039000000c6180354030008000d110309148019a1603440c080e0100c941c66803040443d01820030320389600240456030080c035000c503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 979633902 1250 979632652 979632659
    0x5040e0a1208010501030e070e04080c0a0501060603050601031a18091006260a081c0603060c08010f1203020a08030a0b1903050114010e0a0903020f010c090905090c010c120306 77
    0xa07900030890304021980d041d004018640e4180150b0001105c01e1001d0040340b444c00218024007000500300512040c004681582440c904011000780700390031400900c8a00d603a03c3c030141c0202400c1c0c8040c0c0c0028144030308020880f6092a000819050140c422111060307020505461007201030701c00049409034200e030216192440c00340c03001600e00681d14240308034040c1880718003542400d02035801034100c00891404200b01c042560101c46902e240003412001040341c11004141c1c6810041883d807510101d1400c9591100c400c9050301d500c0d10018034500e84a117180c00e45065824002030040c1c0c00011024002018800170319040f2094036000b06180320b00c600000c12031551224080f01880300380101b041808070034010030101025040b805050b03941885181c0d8900200104840903654451741d07400200347c400c100c100d120640c108000c0094080d001c070020b01802d86841034800e82e0b810840420140d000103e510901c4a005031100002041b0340d030703901c1c02000c90201020050590b9201c000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 979635152 1250 979633902 979633913
    0x18060b03070f0c171201091a0604030b091905010e0f01020c0318060c1e190f0f0f0804090218090618041121010e07050307051e040f090201090b0304030905040e0a 71
    0x24071100070905d00607042d660501107007a04403071050043e116040c001142e05031031922103808031404c0c0e98004030b80b1242035503075044caa0300c6c00801041400d51900011004001d0140650002131701046210981d4406178041a4880c243d02806004100d5a00204020340794040b1b0301c0500703114900e0240041d0304004400b146d190411003807901c90940745980c8040c205e1640f9051121099021068110f40000851034490720700300140c41c00002c00360a6807022900a020b038030403c1d0841183d00407100d580d40c2c0d0700e0b545444060b400081d0140b441e945101c0c0d40d45041d140800c0700901c20a40600003c115801c0c00b40c041a25840203881910350302040c00b154209a00c0740c850f50302c114020071b0b0040c0c0c0c5000b1181c0c5450308441c14801da02c4003e4103c15014495076402141d03d2044403000c4030b50b42c0074008070060326516855220305056003d840c200100ca140f03801a0041003446000f600d42c840c801d80d80d50031018140c80200e4000b070024081c2034050200703142c1a44402c20001064080b00c0c0c044a00781d454 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 979636402 1250 979635152 979635157
    0xd0f0e0d08070f03090b041e05071512020408060c07170406021f0203060a05011421060a271104030b0f0a0b2209051618060b03070f0c17 60
    0x1400c0010349076100700211990410205200d5019a150030400b80c1a151600b0100400245c402000380d0409510f00014038654021620102d400000340c9002503610205402e10300c685c004c4040102c1c2420410418200c46403007a81d080301d0100001d01041d90310600811400e03031240d142181c14104810764500744a85e1480984040e040ca07400402c042c040f400c3d82081c454a41e00440700340c060040003040f917103403680041c1c4401c036042800c01e10714020f102036010406000d101d03006809660f416410101d0101c548a0303c50103000f041e580c20190b951a540f81d00f58840145800004444038420269141c610a42c440701c80c01c00301e00c0c1803c1c101500c0741d0301e036079a521056481c80710b40c0410805000780425284200c101c00d40f0102c98040f401054107045109080c0e00140880d030a955440c00700d03080c010240b2210700003201802e443c072401d41c0c0f100b4041d00484508000785980f140380c80300c00308040c050038044174091011621164100c11410f50304403540140b409048070081c0031198901400c1413004003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 979637652 1250 979636402 979636423
    0x30708040b180a0518040606180f050702010216171207120c050a020c01260f07030c030b150307030e1e1b0603041e120302030105041d030d0f0e 63
    0xc01c140d640059910070481e00312400480c5100e032118401c01c1100da40c4501210b84648105150341929564a040500040c40b80b039201500e00300e07840c885046c40742020381c01408841c00c882c00800290f01e641c0f004900300c1c001d5150004800c1c0865010501140421400840c2d500b954000c00c3e15010304420294600d0f1016a0300c0c03c0852450702c0c84c0c2e16003102c1405811030014240c5840da00300206114000c1d07039000c1c4a0882414040000c42c136994103c59451060303036119039011f83c0700c114203058084100c2c598007241c200000034074020f032212006120740038a4410003401403e906500380742291046c02580064400303024196121030360790b00d441c0103110030a80c2c4c4e40e20b407404146414804017018141005005d1000006510005074040c6540750801e580c0c00c00d4004580410401488441c14900c8800a801500ca0949030032060030040d81070b00218141c840648061141d588944103030300600c0149180156550014014001c01c02100d40c012548500390040200700e4042889640c2e091024822 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 979638902 1250 979637652 979637669
    0x50c0307050d0f0f0e0f0f030a0e0111061e0a021c020309100c050418050907031707200f0d052a19030b0c03090309010f2c0102010506030f150903070804 67
    0x81ea40032040d0414443c0780e00c0a081b4a000c0c0294654090000c0c0d140d114a00905090000000d4602c1803644604441070b0004001c0084900380d042041c1c1c1110558800c01c68440340510003070000781c5894481c020f403a1941c0700c490826045001140b1810060742005011110500c01c0f06000c03940c84403180510280c600381d0b51a00750b9200e04000e10910042400d041282d0858240340c140034541000040c41c800b200c1d00200c0503a240c08005095009610407541c1c040d040c5140000305501312218611181d0740c41000711200c610340c01c064428840603207141400a00700c0d4200c00c410b01c1d5444030680c02260071840c8104d0010700080f0000019222152441c1c3c45c00640038004410310400c1a4208803540201e405042c180c01c2d8942019000c2d8ac0340b01e140c3e2140e0400510050070070340035001d03209012011040c0006803001c844000321010000300044005070042d030800c0d0215109050100701d007001e140b601c0e03001c0c088103211318224a009d440041e00c0d0070030900c804c0001c2404a41e04e000600702504001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 979640152 1250 979638902 979638911
    0x1e031e021204120e180402030f0d030510061b020f04060b040b13050306043503040303200a050912030909100305010e030307050a0324120b0109050c0307050d0f0f 71
    0x2410100d4540c8410f0400c2014811603640b101e1203580c2c2c102c1d8030484480400300081c084e45c0c0e02e02c0442d042c4070400101401078400c1c40040b18030b07241c268000c0b40c421181020703030320101e50703076030200b1030b50300721513003440380006540c0c081c0440541400707507081031048406000859026591941914180d004d1761201d4410b030000b2401d4840748500c115000014903044008202d582031076110040310404415207010300c00200020f07000c84010300c80505440821100c0300544914090074094041c2054000b140c0c141c040542624080302c070294183c2e00b40c06400c1da078a504001c030401c00d120003281e00d0303109007040c0d2009000c0c401c81039807100240b078030070700c2400c00384620545585080741c2540c0c070a011120003504240100301000b0751000a40d10b46030518a0042492500c1500b000d070170058070340101c6401c1c0c81956012a00c3d4905507070b69076604e8400c001805841e032766106044200c65043c0c424421454080004c90f07080c501c00c0014207448440d01600180745121114101c08071b070280c90030442e946454 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 979641402 1250 979640152 979640161
    0x1060509090d1403100b03070c050d0503010e241e06070f051603080304020f1206010e1807450b0a1e030204051305150f071e031e0212 59
    0x816580c003602503000c160b0b1400c504100c170220124280901901944881c00f00000c0c0d100e80c445c407011407200d6046402d03a41041241d41004196500034002c0300c00900d40540810291602010311110195035440b00b014400e03803d50400c50990b0000040c6a4494441c6c84403002c159681001810820310800c9140c1d03060b88186026030410140460b40b010302000104104007140380340084a0340140d04940040c44000541d000818041c2540e600d42510300c184070010800d58046881b4038000c200e041c204e10300d803040c2440181e954010a00403075504080110030311410748140ca004d8106e5150928100da8072102000040f420340300c1c0d42c950b451101d6191511003ca50800c0d200090280840f210808503030f11001085413002505032100a004940c0c0c3e01c0000c2021003604034041c01694042d098a082400a21311a90b01c3c2d981035070020b903103415010105580600406191001c00a0185c0003004c05000c114280d0052500c0340d072002181000111840110040744010040b2080912032a02c05091 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 979642652 1250 979641402 979641407
    0x1827101d030703122c010507022116081c0f05100308090d05010b030a050114010b03010515030a15060f08010b0903100b0607020301020a08160306060e0904020301060509090d 76
    0xe00491505494004010080200b5886610101074011a4034045910b0412040c04081904c240c81c41e110900240d40c3d034154800700640100740070702c5881d030841c2c8072240450b0b4a110303021200d21417142260f00401c201081c03200740150268003280520081d41c205a10901c1d18180c04000782035021449a48182c101421800c07840382d542c00c009416110b90080342581d07117100d00c43c81042d401c503220b817960001d46401c20200f50020422280064291000049140f070110b000c0c244101c040381541007132400101d008804102500d0480d0380050a00d03000c00910800f82e00d05a10103003001c052a030316610500305801212102c180100942d90340c040200c03c006c2d1005090320010380040036514010003039081d1640d00060100a40e203514500007590041c2900000d2040c86810402074155001042c0c0391400b80e004007a140c492604c44140189012010070101c007180c00c68003c070360211391034805200c100d050903100d003036000340f002d40006000b0740c03104d0000d0320988080340c140d88070303034080c44101c001641d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 979643902 1250 979642652 979642691
    0x4030f0507080d09050a0504470402070201020303131106040605030906090a080a050903100905150a140109270c060f030603020f100c06050f060f182710 67
    0xd0f441c40e0045001d0b0400700041e2000001c1c0c8109441151561520b02c2c040440a99100303801484c0041c4403507400b030f02070314640f00c05445001c1603500d4444071200b104600b4640215820241e050303014500d190766050714503c68120740c40017941c10a40d091002c44480d01d0f090010006001a80c40d00d075101e140810b01030340b80503c010302880741a08410030090026200c2415140c07402c40c1c2d8240241c075080b0442c04a441c280d034074280b0007012400c1c10103607800e006c1d0104000c2c038004101c2c100d030000e0303990302c2003000c0940c1e2a119102181d40c0c43c0764010018610958440d030042c2100c100038448079902044d1800540000340001e0b603500c810300c00300700010380d0403501ca00442182401e06014884c91500054001545a49024090032400d9414510b0134803940c18a02c00b5a40007604100c0742c100100c030060a045c0440d8668007400c50344480080c5d528181d220041c5140d15082808038039515061145200742c42a44507500c000342624100080000c00d005101030448200000911901180015500c20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 979645152 1250 979643902 979643923
    0x1031e080304230109030f030e010b0a03121701060909051923011a031f0314030903100e0307061a040c021c03020a050a03020304080d06080c010e1518040204030f050708 74
    0x160324084c5c0820000307400c003888a5105140b820b000400445131000c0318090507810b45160381c454224031003c03040007101014072846210565465011140d000501d01c201d950a009040100f128440100a4545143c2015500004400011a1820310380350118161005100303600c1101030031501920b0320f1144841618010b04118010101e400c000717008001c03080c40043c2244207134640022200301d0510103240107400071079100340e9207202615140e285039201d4100058051082c0034240d100210040340e4010f955a403400c80020714600304880d40c0e200002d000d15005040c42e60254802c51840344d8aa100300010b4410b40c0c3c000e84607180c0c06130744944918200507224010316205220311031025a0200c1643c0b002103441c14016a00d032681d0900d568a03011705809441c1040c14800c02041e6044045601e44081d9401e0700c0b4050710b464182c0400000064800800014640c20f2090179690f000a0b05802d08d11000034100525040d1251034658028517030420035105584400300c2041844d81c10010300f1400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 979646402 1250 979645152 979645223
    0x1b03061f0507020925020c13150f0b1312031d0d1403040311040e0705100e1e01020606120d1b0606060e03060a200c15070e1203030f01031e080304 64
    0x5038811f0b400081c0e80309010340794401499aa50031050031860b20300c90301c07601a10314864039100d49a41c405d010f69069128542c40c08050040420008100d940d1403200009590706880300041da9040013855207980c6490318400d40e2188406640384049038640c42120a901c90a0019542d250f0443c200002c0f20403846141500403032505074920110384003ca102c800b40e40c01150003281c65041c98004944c0f00d070034010815403041014040a141a11140808005174000e03001d90301c050b51b82c90100001c01d0002d81c0700c01d100c2d4100e000301d1070312240308003a82580d5849620384419180c080e902d41204540c615082200468a60140c031002881e003000a0303030380a4240a4140510715808000b407181084c04065258440408505081e030740106119003101214101c071140e10a16240708000e046182c08280c4134051040700c00007240101c40481240d00c40c8200c40321400c40c2d07074139640d900c02c003490700b01e48501c1542030074121340000550b100008500650003161101c0c0b204101c0c00d1600150740640544101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 979647652 1250 979646402 979646413
    0x80705060426250302011d032d1006090b12100b040207080c0d12060305060c030601090506030903030708010f03020112050a0e151b03061f050702092502 67
    0x8074800d50342c1da407242c03100900030715000700e0a0342c4907520300310760303200f181c2442ca05465555075115a40c00c10300046a000b44d881c0954100905240c000705500300101d42d40603008072000c0780786130031125013190020703100280c0e035030714a1707081800c99087c00c07440c5020441c529110407040240f44103501411041801c2100d881100310507102c50789685140346c07061000364a45030001c0c1e06440d62107078140c4280e140c11550705a56084180807141e15a4034014441c400b14007003104a950400131441410260303a0300100030900c42e1204480d954003a00006c0020381003241c2c0361808a06511600043c40c01040d82d00019a180d04114001900e07131503058210380c0308035550761001c1000d40c0e8041d06010000e600b20000040c20785500d50f03003002a0013011541c90451007520511034540c20128070b034502c2851044010394031031035030520006051000b580c46951040c42403141601c0200a202c10000d4000341c3c0c1812490042035a0200b0b0001104071407040f429404000002040840c0d04100314500036a03102500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 979648902 1250 979647652 979647659
    0x120c100515030a14070b0301090e1e0c0d0c05030a050610230105070614090d08060a05240d0c09080c010906050f07050313080f0f0105041104020f0904050109060807050604 75
    0x280e41c0c81c461040904131060541c0c1c9024141340902c052009001d40e0314032240e0b07a41c0c45a50000240c0940000b0307404604c10601048604500d000480610345050f10160482c400443c081180c1001d0303101c07042d1985112600001080d60342009070200c244c0c440c0d00a00a9440c00003142e00044040f0781c4410800e071584144007001d6256265500c0e410402424071a031603540c1420034000030400200d5501d0042d10040600c11140d10014044400c001c01e41d448800941e0340d0340c18400050028171456410445d40c82c10000940c81300004842440c0c0007004803410000d04030101c1042e146507207490b2012171101c207804d01511105021610f18140d0070300302001207903e8548005e2071481640c400403961200440c090040000600c12603600a13042070000090a8a9515850703d0301d417512901d885922400314131003690138060103854810360b00000660550b091140500c0f020754030242da592070400c0c0c00c004012031b6a40e103224040c041c6c0001c207000036549051000841c507000076074000b039104800502080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 979650152 1250 979648902 979648909
    0x10801060f0507142505031c0219060b011709060a1508030f22030807060510030f03081812091507050d031505010302030105011e02120c100515 63
    0x1411242540707070000480c042198200d401d8020010024410044c84100c0300d000b200010344015030b10000d4082e03400004240b000007840e2107040c03003100e40613088481e2040301146840c40d211408203450040d600c9180c0c80c0b10f0641c041c001c0c407480032900141e8501da10103095920000800e024802002d40f0740450030249003556076590000c00074003020780c80d0001c0c03415010364202c00a0081040c101142d854001000c1003403250b40000c0240c41e0103512410701e01c4200301800007039008880d009220540b4112954070340da000380200914055441d0b07860b581c00000035140882e5250740900a40c5c9401441c10301d11004002c2c8030300d0f09140b0030a640b00d1003601800f000b0b800110380081320201c0341a216400c10170250b120500030100e001d0118042c2c241c0f044d150316050340040c403180341407080021015448200640482c08203000d51800249040300c40c03414250304007608041e441150044440440c00d00d0781d0190f2941c09441d00203a42e40010501c1c089580c1240070300b035009100c02062002400358000807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 979651402 1250 979650152 979650167
    0x302060a091e02061309020c25031106041208030412030e070612090c08030d182406172b0806060a0908030706022101030c14120303040f021e01 63
    0x1010040721112982e4110741c3c1e001e0444503100d05082c010755015655020f480c00a41040d0540d4590703005400c60441526400442800c400101d00c004d40041c80c10b50712054541c1498444040d040801000f01040348244128044d092520980c2d41d03a60700d10700351030000c085040d00380c080001d15052400f5828501c0d0b02140d0300c1c06a802c24038140c40340031744101d04c5070054046080050304841201401080b01036000c03000704007511880d1011f05c003501c44c201944a04290407200903001036100000c0c805d4120121200116500003a179020485e262190340c0c414615490090408050f807006411002421544100c090503030b100d0815141c000c00040c1c00070f0f091a4000b49001d2054100140a5440c036006800310b034050801c141c100e9860fa8098500320000b50700015000d00701751070b15140c0c2211545095141e905a940c0540d880f010715191500c60200c540b031040003507034002a070220f602c032600c800b08007031817084d40903a20301100e80455006206c0d8423800c0e200c070301d0099036240c2500341059800c41c08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 979652652 1250 979651402 979651433
    0xd02041401090e130525152303090f01110306040f022724130b0a0c02040209030c0d0c0e1003030e0607020109120f050c0a0f0e1e0903070302060a09 65
    0x10720215208445ca41142030040c60039401551a07032900302607040c2e89040308598141c86246a40c61110100c1c1e0344190365103501c11441010b9403080941055102c05050041c0d07801c51040411a203a2041c00c035001400d40e2400385443c40c1ca00400300802c0003034038081c061042e5620348034504524000801761448035144000c19a803180030750440c3e01550584811094070b800c01304c98508800d8000c0d40d09801030f242d6000b0001405403180074440441c0f8070340400c08584000940d40c032002c60600c03d40e070a120103500203500f00c907072500844646000c1d54446d82c884c126032901c681e2450742658100340720405c80b640c0c064140f82a0a4881d0804d10001e504036020034070b024401c548050300d81000e840102c4500e041a00485400e8003c641c3c242d00308501c000201030200d1050003550004d92280c0207000c007201881c40b03000e202198004082003607201c405e0500703810184c040300600142155080c0b0381c0d03600d0002d49004085a200061400605a050040c0303500408915402d004445440d10340c062080940700303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 979653902 1250 979652652 979652671
    0x601031d1926071a06031f02040f0b03040210090315051315022805040b0f130b04030b07210e0a0204051008060603060105100f03020d020d02041401090e 67
    0x5215001e100c1402c10718101d082c072442c582d0440c1e10500780c1c0603041e83c0010307404895071460003078030611640c00120b0b010310489015004001401d644000c59a08009107486a003246900f0080031884481e4146e00e0000360000c400c2d6650b90b400c0c1841030041902c0200303209030410011080510000d0b5055046030000c82040002140c1a01d8600003201074080c0d03c40c0090002c0301114041e5061724550700940b20200381d41350068100100c8110145249149040030b10001c0d40801c0140510300050b00500b015116025180781440340802c034001101d100d0340c00c00d56881c170340890100104103c2d0400c90b0f82c030000c2e910703228850103220b120200140c01d0010400190548851701c0c5114507100308403050309160001c00a010341c0c1001401108208000e004c0d18819000300030000b0301c14200060118100d80d030107003030b82d601616160307812112a0014030802c800c1507000c002d420402002400549111203c14600603130796480c2112100062180003809814041e0400c0708001c22070b40c00000c907900240301c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 979655152 1250 979653902 979653943
    0x3140a05130e18070b041703070b15030f0c01021b1c110f01021207230a05031c09051b0d081c060806040b060123120601031d 55
    0x18282551980680541e00800c12824100010709002c8803009900a49070003909540403284400810b44441042c05212442e090800082200b01a03290b41d9a8803410700009480c1011307115596040b03103d6064604103d245d10480e10781c080d42c9400d10030b07840d400350048014240070000c840044e45407189d0b920100e4402140380510080346e110724070000c450b401c000703075040005556442d10f05407122403448400c2c0581440892180c103540009010b100550501c0c01d11801c0900c103941d003048400b440464084286800220042071703c0040001540c0c07036101f13001460b101c20b4660115805800d80c28400724509042181c0e24000c100c0100d00c5002e01c0303410240d5060b03030f01c544901050070b0b401e0b00310000700140d500044406052200403060305000a21040500107266210304065031080103036006402080400d0101d043c030f40c0512591204117641d54110510610011442c025540041c0c0d0794528198880e0100000b5690520413902c05400c483d40641030107104080403641d403040c2401c0b50b036405106 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 979656402 1250 979655152 979655167
    0x91a0703110d020d0f0f05030c0d15060c031b0b27031c0609200703120c030c0e1c140c030706120b0d0807020103200a030b0a120314 58
    0x307030707000c0071411030060031030301401003400009503030324406004003001072100009052102e120718541d1042d0032580d0f4880381151205600018940e11071003180c1c000a940c3c80c1c100341d00c9200d140000008018548500d00101039a040c05010028000c030182851122112442e00084c4046051504105000112007250000c500c040c1a502c02500c4050031a120219002100801c01882e10032151840d91090080c44e0740c0d600400b00340c4400480c84070306441209030003403800002d40082d084640c02450646042902101c0c010f04452109901600080e01c45180940711034004581c005800d5080e5040014807112401d1540364508000740144401c80300c1c0828035850604012030170030964010240c0308185e5540902a01e250214000c2440d600d00382901210310303180803120f400c15550000903861030f11540703070f00450003806000808043c00250310150320b200c0b503042d0003404808005440004526149008016001c2180d90210101907900340c0788100080d488458030010400d1015402c0d06c1c0c020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 979657652 1250 979656402 979656407
    0x1201030f020f030106080a0201110105070503060607032f0c01110303060d051606081008060105010c03030b011b20121018081306080c070308220204020f19091a0703 72
    0x61403001680c10345c203003c00481c0b00940170400c500164400d88030b0582e084804041d060a844044510070301080c418000134106080c601c0081c40c0c2d0340c7c070030326010100b002c40c0d540c0640040c2051110341c0007440c0c070304074901c44a00108441c401025090030304a1008001780d640c039543c0e100042255004501c800c0c4098200706040110f90400d03540e141040044945801c0b0061a0410441c0c0b443e1600c800a50f000808036400315590341070791010303503a22208600c542c07026005810714100e0941000038089a0182904640f40c803c0a0107110700000141c69003514013803903030060480c00d181d00c141c0c211900542c060b00001980714910141680210355001d582d00183d00718902000d0144c03120350001000002c83c00443e6900041da092500c030702d0015111641d0000c4140075041009004c43c00607070108090360700b03001c40302c0020700ca8043c42030302d00d490b00c0d4041001d90304880c60840c1c2080c004211440c64a074450a100c03407155031860300c51519860b00544401415002c00401010b00000450340d06162 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 979658902 1250 979657652 979657669
    0x1419033c0603150b091e070f052713061d250203041a0403030503070e0a090c090503060f060a060e1807020a110111030d02130f0612111201030f02 64
    0x40d002041e0400050040c400c0780044c241c450030103032080351007800041d1b901401c086078440d0f444031034005240d05d60700c0040940303519000d05100b40c1802070500545002448100721190450702d0071070600040e55145040c008407400110800c08103a0800c1020301c2072046042900c0210303601d607289829261140242000c0640031280d68802d806680d0622048464000005000319003082d104603480e50b40114001045005502000340003c0d010000306549a02c01d2040f1804400010308440010f95aa09240d04444280f0182c3c0082015448200014a4280681e0740d110000d40c801a4248c58150000740050816004a4051008503158242c00340c40c2d40b140f14130000301c034100070711460405800c06541d4651400044903240182400c42120354415103e50b00500d0b4184025404c0c140c858110102075007142c18641500340000c5000103010360002400130040580741c4540318030060b00c0c1b00103c103950700c05041e038160031020004580100146142c1c0e42c112a009124101300c520705100140081 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 979660152 1250 979658902 979658909
    0x120603050607050316210c0908030c010c0305061002120706060b03040c0302040b011403130201020f010234032c030609010c0f0c020d0f02011419033c06 67
    0xc0c42040d0402042d65082001075028503405048a181c1c0341e5050800c845140744002504002403e021100804003416004803d00240d5170a2010b011030b1521292851a0062400800269110003100341415098424a9049030040e26500104124100065615a00ca02c0702c2c2940200006001c0309100c5203502000c09000b030381040301e0b41c0381858101000c2883c00740c0000d07071041d840d110b08212150702445540c2e07582820444011f045664009501d10600103214090b4158055101901007400081c0300810010005014410809104035502c0c1c0f010a03424008951041d81e00841d14082038008040c802e1098040703072130310140c24074400032060030084000007135014803c1c03006002c04140190440854180d0964079160400c00188088480201000003c0d405c1507a091880010400b00004040000d00606000d0011b91200d15094001e90000c801c0c11000d00003420a0309a060749401000e41d8924100c105090b030300000c02a130b0309400102c0040036000d144040300422100682d40000005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 979661402 1250 979660152 979660163
    0x61f02120304080432190b0f0310151205070e040f0b01020d05071a090f0f0f0c0901240905030a290705030c13090507020f01110406050a120603 63
    0x9a09080c50043c0d1103401500a00480498550b105000010300c581c506107015001400d981d0750b60600c1d024402c501d881c03912290103c3c0409103012501804080c0149551190980d0a6949181c18200c005800e5940d8000307c03103025090351140d84503540860580302c00e6250440004058032402d4007500c3d80d410306403503030782c02a00344098401142045e910501c00742c502a000d50b0070011051100301c80920404ea8014007405540a80b01a140c1d20190520742c006d07034800c04c4a0419500c20b112900e04003d4101701c4020303030700407050b8644020302405408030f0703542c0648042c606541810b55030300e1103480301c08407840381c9510001550112481280d14030000e1a000d401d0314200c419a04010000344010800300f001000000c1f61406050304500b04948602043d9480034110f0f1900003079950b040d8071491078600c0090082070301044054180c42051b00912458000307200d02d070109a020b9081d03840002c05044904001d010810800307401008481d2049820302c0c242c0c0d5a00c0700c0120400003800f10b138001074807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 979662652 1250 979661402 979661407
    0x11040b0109301a07090b090109090203041106040f031203020a090e040c091a030c15091c0204060f030212010c0905061308030c0105060a08011b0c050a02131a09061f0212 74
    0xc07140c0843d8040c1d402107507182d0b6030f400c4035901c5142e0340c0740c940b06528110f80091b801000812043d41503034040e40e00103200303417000500c50809000081c1c080e00f003600008a1041203010400030820a0b41c10302c0c2040703a40c3c1c14150304000403103801500b04c800c0d42c8100e110741d0200300001001c1000d40e81c0c441002e4011040100001a03200d00a2909401010030050080c40b40b4402c580e854900101080711551141540b913260040d9001480201040903095000303200c440094200140c0e078500614000e4080c0e550760f0543c03246540100142600c044103d5a0540d1401002c210b0f1a40c0c40041742c8107858054403a01c1d07031500c504881382403c10350740d80308040c140804a40c0606070501074003c20b003e1082250390f4070000d034540d5101400c82d003a4028200442c0d039000c04940d10503006003080303c6941c0c001c105650809660303402003000944074240907c0303216034840d191620812808803a010303e6006803404552460302c400401c14001c0500800c920961040d01804503240c401c103e04650480c0142d601034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 979663902 1250 979662652 979662683
    0x9280b16121514090405251a0d05070305100902090111010603050a11090106120b1c0302060f0c130317190801050301050109051909020102010209040911040b010930 72
    0x150910b96038000d0a01c07039100700030781c0303034851130710700441801030380c001019210003064059184040c1150807603803103060715045800540c00c00c9841048201000c03c05c485a80c48501618610451310024428024103252a09024a10180d030030f0540c2038400302800143e589041c0001682d00078180c501e16000366080c40404810400c02007448001c551003844d010450207440820400030640902441d070005102011840690391150843c000e00304000d4129582c4003c0030080c41c070800e035164402c0d8051381c400c00c140f00c4801c0241c4c0075254044007000380a410543c2c81da4400000c10850b22000e442c60252805003c0120820f00403260315a100710302420440780c4030036010700501d20902c5190300c207501e040000104c45400e405520f1098a02c1030030400da00248640160003000c600e441641159401d10503160300c0d4a65101e040b02d424001d03450307040755101c03241c10001650700c051446410407901d11410800c0841c26240d00c000c201e20b880070024001c0c200c9101035000362a100000d8060000c011854 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 979665152 1250 979663902 979663931
    0xf020408070e010504090203030703031503020d060e0f0c01050403030c02180414011103100e0a1103090102070c0801020a050318100c0c020f01170c07051509280b1612 73
    0x1404492110b9000121a80d0343d004000460310041c0000e074041c0c20070440c00001034844d500020b61040122285e29103e9201c0d004038120710ba11382d0341111034a0b50341d08400700e003030000c0298058840000005000802e48030000a0142c004e52100906002d00c41201208640c0c0300c03400d100402d0303401990391032035141508215038510f041000301150f55180c000c03014281910f40c0d049900c83d550320302d90b180f107076031501e0301241200b5230050022103030f540d8600712070a4450400004600410554002580f00c0c0501c0c00e01040d1101541d0100b880760f0710400c804d0803075a800005495200f4490b074541d061130700500740f100e410318111442282001d484c04a41403071554200e103810180c10300a4808001c405403a6006480e07203d4074031180160070480800103064103010100a04c2c0b81c42c89202a1aa5003146241205142e8000d48128520790002d01c00d00205842d041081c1c00d44010604080f070307d80429417940550300b90040c000e101c3c00a035040c0d5000030380380924032040e500c40d2007100800640c1c1158440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 979666402 1250 979665152 979665163
    0x20301050a0b2a0109120f02070503150a0b21010f0524090903120c0301360f02090603100311010f0e041503120203030708060405090a03120f020408 65
    0x54511410600380c000c030b40792030034400f5641000002c9521010500c8520400000001d00200501c2d00d0740d00d03541c007500003a00c41192218034200c580c0710031041080741c440281c00c0c507025070005070007684034009003c0602e85010300c554221040c03c000140031100000411407100c0c0c48074540720811340c2c1c809650010300055000d14490101c11104101a895081c00030403e14800b05180e010340c480780c2001080d070301d48400d0048c1c1006014080700d141100d1803081c03440e0000211a45082400d010004210380c0e11503803e141c4203030b0740e95030466440800d041c210381c108451182591203016614840e07903000b0079144e41111a08080100390399128a410b400703040a00a0300d0204861180708280f0064855009407031130458240982c4a044003824050203001c001c00800700803441e584921080080851001c1102c0d40000d03002da4060355813450840e101a0802a000d4122800341d45001c040088510002c034400e5150b17913242c5068075032440214007200140803c00301d0380c80c050340300040010390f18000040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 979667652 1250 979666402 979666409
    0x705060f0c04031b0f090209031b22141e1315021215010813030c02040b0d030c140d05040306051f12020102010e0a03080c03131e1a0103080a030b22020301 68
    0x1017071040a03140c1031180c0680c00f070200301a030180d12590159114040f414030440c06070f030000d041a14264508003100041c0365a1014008186660b00c8400160414030588151300080d240303903030151600c000000c100048401000040e0702d400301c82e140c0302006031800118099242d038640a54480910030516542c25000341da00c0300a240c802c402c1a45154018808235100d0f00760007408058414007510181c0e115034401e18202c1e802030355034160b40c415a80745040041c249010f661006641d10062030010300007000d190711403200741c3c021004840f03102d5012080310142c9902080110b42e6803100420840e00d1118140d2040811701014404650180f001e41c005000303d000741e00078032062807401c40094840100d10001340002c1e80f0300001846c0026032500440c1c0203090701200340700346480b54403107c0c181d0690242c0300c9100ca001036041c400740300a200001501101c0c80610480c90b51542d91401658420203c88030181500e81c5550012943c41410600040203e003d0b00c5c4400c1000c0030009000354424003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 979668902 1250 979667652 979667669
    0x1517040b010501081f0603020a020c090406090c0e04020a0303050a030209180703110310031b0902181e091609031b091407020c0603040c24090b0705060f0c04031b 71
    0x80041c80c1d0b1001105c5a580201d41004c2d084001420004210065030041c91038106600c520801d01020f0b44640300c0700c0344254044d820001c1ca13540b151401e441c061159601a409809400081c030004d6680c081102080704d51604040d03070b0300d040140044d0080d000310a0520307840041443c841c81c4014060700c0240c460300710707a0b800f000841200c0c82c9240c42c80c0015680f984921400c05001d000103114032009200344122055208129950f6844141c1aa44000341c500a1104030340b05411560400b86100c0d0006010110030300345000001d008500040002400031101b2221000a0510380d4010b070300010107550088134501c242c0e8191414000303152414458007581c41c1c50500406000440001c1d80b5000384515405000910f0100f01000184c0e00040c0043c1c48211150600050701f4621000384000c0d440241a07400c4c5002881001518406041d880151034800801542001a90129a0030350040d2051080761031500c3d03100480c0c0c0c081c0190f410050400701c0d45542035425000000280b400c031103000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 979670152 1250 979668902 979668917
    0x2505100908010e07141003110c010207110109150309080c1b0909061009050a11041202091012061a09040309032d031b080a032004030203071517040b010501 68
    0x100c00381035035134000380715078080c941070112648602d01c0e08030300c0e084014101e4a804121382d000490801c0c00b59024018222641e9070001316101000290864810f6400090038914000380c40c206081c141e511002c590b4408155071000720f034041003203c50540d4801800d950841e030b000034a031240720010302c10740c0b00d03402d21030140b0304000348107101d001440301e1199100c0c2003224241490029010040c1c400500f445000c5910f403101050329000c01030203000141850914440e50f0f00c0c0e18014443e00b21005800d00a0303040741d1000602085446180c0c441c3c0e82940a0300000704e440384400b9010383c0070780f12402c0d10f5000f031b05141440280b40d80000320009403070086080c0d01c544000d1a0355941b0950724044e85500b40c449074241e0a01086c0543c0074903031082a411103001011038155a004455480149080d0100340d4072207040081c181d4a480d08103021610700000c030320301030444d0000b1782d9410b19881203000c401000c410462007144510224071041c84d10107403040c1c4c075081505d4000f440352001d010700e50009054 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 979671402 1250 979670152 979670171
    0x2011101090203031e12041208071409010c0213061d240d061d031e0705070e040203150903090906040b090a0b06040f0f080d050c250510090801 63
    0x107100d4005400e50040c000c5140c1807081200c011070080c05455a07000c030704244003203908405a43c9000f48201d1003125103522680c4030744000707480c55201030540002c11400351003401316000c50310101c903a03201007424240d86454403880040c01500e505414201c106080c130a0000d00015150050300646181d03410400803079503403460842c843c070f44072101d840021a030440280f0490801511200d400f600440020075074072004440b400071050541c204c440e003940000740340c400300d21121a0844110000144103803400c9481c0c0c50b071659032039a60107000002c03281d40010500f196010098030f00c0c40c250800c920038042c5040c004403a2607821030102d9600a03840f003000a105440c080c814100110300051450400ba02d4547c8142d00034100100e0094000904000204110310790081c40b0004000c0400d4041030503041c040c1d01070401962140c03500a1000034043e40c400c40c44040740750485241c801d501d4044081c100000100c00c019154005a0011030034806500103030b90106c8444195940c000c001c3c41456270 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 979672652 1250 979671402 979671437
    0x150315100f0f151d220c181d06040203090c0904080405100302030402090a0e030d02130519081b0102010f090809150915031f1517070909020a090906080304030201 71
    0x30480050a80340d18640c04e02c41c5171401910085040024920704010002d03084840000c5136071030b0040c40003284291200e0a4840c1d010041100075220b1000c0c00e0741d404100500c0c5103038000015100d18441c0d9004070008607002010851004026002480c1c1c25140c181414030b60700315403080c062140070b2044200c030003040600900849002d95800351120707503180e58190300300006040004510000e40800c1103918915125800500741c1005070300ca406c1c03c69841d00d81000380403c05003c00c08410000c1c0c1d03801300400c0d0000b00b40002e010003070392038141d0480d0400340101d005206000c11008114a04403002050280d004082d011108003511100f00c0f4040030721221040780904400a036000521110704804110b84002454111910f042d504e4600383c0c18240c0890002042e400042c0f18540c50b0040803207941d4801d0103503d014555030b0f040b0100b4204100024041040b034000d42c0901e6400055a400451103400410300902400504105007a05c90b24402e84071341c418842030303000460b2000c05141203030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 979673902 1250 979672652 979672667
    0x1e03080a050702160501121e0204080105010f1a181c120242010e1b0a0e0f0d2f030f071511061509150315100f0f15 51
    0x900114000300c090741751100449003c040b0f988018041c2e510380c460450480340490011141e044030203405615241001c4c2c2c05401c450050740721144501e000c0300b04004000c02aa0116030308021508903d83e1a16001c424140e0302c0b07160082c0700c0d000000c8c209548000c0581c6468100001d01c0b90072194401c007a0480201d0342c40c41e0f80400c01340c1d9480761980518041250035480032182021814410820344450345450061800340d0150801414140800c0092010401d42c400090303030017003c541c00c107940c08030020010115500c0d0180503050303001215240d07944402540d18a5039200e881000b141881c1d000f00304a400d400405020644540390940b02c0918005c203a18014950341001800300c14a0b01c50211a1b0081c0190700380c003031204403d082204d40c1418405a84610034900040c1000c0c0301c0e000c2401078444004003003002d1540c29200c0561b003940d0110742e80c0d640b1011601d8030f020399107134580d9107032400c04154000e0f203152280381000100108071140c00340071030781d862850820403100c0010070f44519 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 979675152 1250 979673902 979673923
    0x601030615022e0603110111061902091503100609050d0819030221091b0d1412180306010506070b01060507170f1216020a0303091e03080a050702 64
    0x41e0442c0b00103a400e4020103400b0365000520844840b10030300d0802058041314155001640d1145900240050720350700954081051980b41005049600d0464a02034400c044804480107843c1c00003090b01c82a5584030310403c800018114540c0c1da070522410300800425a4458030700803981002000031030f413034444030042e0426001008580707469850507019042c10000d50710b100900da030a102c1101c2c2c40444003034034441c0540302c511451035802d01d0306c446450100d2030305c881500310034544d001902ca601d07480910304069510803054801c526007144a40d05000c3c03106042103103c400403c1200707a005000c5d58241c4d058a041d000d0744d80e82d03602e810920034a4810028050510180a001000440c0c407810040403158000e41e043c003c4a0400803002016038060368900c0c4946e000403502d0070110307a107000b410f0381200b0560003034410140301c0c03140a519502042c50150030f041d40e812251081c40a10600c6030750341913882800d107440505914010b013500e4015212060761a00e0080081c0240d4000607030782204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 979676258 1106 979675152 979675157
    0xc060a051e120a0501140105121308031518070207150210020406050414010f1d01030b060a170c07030206040b1807150e061e070812010e0601030615 65
    0x4c1d00d1040e0030000301d040b41415046280c0c0e0304801203d107600442c031500c2005035600c0c070380102c800401c840d0240001100108000b50b6105803202120445400c440820b9107400110080011038421590100940d20115060020801160740d0741722001d01032040316040d028004006060784c0161340030388041a0003160901040d155000c80c0880c401c0203280003010106180802410903040b103091140200084020f0031231a40303c0e13000058603c0b03001e4011035540311b50200061142c2802e54201141000800228208038000c80c2107030f10160701a400ac14490303d071383d144d450403680f014101210320030404c1d0756810700c000709009a900a020040a980c501c801c0300c01d0140941401c0801144600b80401c1640d81792211040709000c0000c0f050a11900c40509103411288c81c40740c070b0801e94100c0110800041e20950606d2224400e900c2a641800a543d441c66a101408022084e1801 = true := by decide +kernel

theorem cover : BRFrame.Cov 979496402 979676258 := by
  have h0 := BRFrame.cov_init 979496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 979496402 ≤ n) (h2 : n < 979676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
