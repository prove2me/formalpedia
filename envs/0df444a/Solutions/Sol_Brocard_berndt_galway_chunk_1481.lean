-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1481
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:11:20.382262+00:00
-- url     : https://prove2.me/submissions/2ecca285-9016-45a0-9077-06eeb812d6cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 266187050 ≤ n < 266366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 266188300 1250 266187050 266187079
    0x9060d0602160c263a030c091e0902130b030f06010806061306080601230a0318320604030c05190f110a1502070305010c030c02060a0b 59
    0x2c200301c90b80c0864a015078400240720600e4445502800550041114401c40040354011075941404603120b80083c1c03128440842c0b0325404500c007212100700c00012007007902c00d44200400621a83c5800000203010701c10201b0300700941500003490000070056550031904000800d40207510414480440e1b8220b640e0001d14160b1303400c0918454030020311514810300d0103000150440c40003c01c07e40c806c240c02c02c05034080301d101d201250140d5900d072034611150f95a600c0181c0700c4c025a00e06c988142d00d050f0b841003040000040003401111201d680030301800c2000d032100181c4041c151001096116000036a0142c64140c90307804050b0500403c0f082080240c0408032403c1c100305a90640000c0c40e03408884082c810b04001d10128000a42401000c1c9030494a41c00c65000300010002c3c0401002c01d603510741340d50b4002240003d0447e41d05c501b012a912204041d594050500c0210b4455091451941800f4002e01c06c0300101074031078004c1c00c2c280c1e40d07920307401c0c008003518402c1036480441100000d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 266189550 1250 266188300 266188327
    0x40c03060501140a2c03010501120321020417010518032d19020c03120405030a0314090612010e060603010303120b040f15060e09070c02090702010605030a120f080609060d0602 77
    0x2003c10703d0b19102202505c00d400145429140c0c160480200e0790840302c01680020391224008103206004040c446c6d180311a0700030b1001a120300d134019006044170303e903070602450040d40300900401e080030415103d503081500c81078907409401d6000d00c3c0c0352402c017924038609a40d034175003138940d800005080b49000b10030704050000401918141c00181d000888005031402c040015400c03000c3c44800c1c490500d450400060b641c0d44c03541e50f000f801c0140d030540ca001b0007103a441c152a444000205000e40b0b52410625075000c2c15024820844103072001c00118610781041e0040768140c9801d50f0f20141001c12440480d4050241b00d955183c10030380e514241b00c00c2c1e8085107d0100c420803005040c0151038a08000108100040700046128101a03403d2182c15904901f900e000c0c11b40c160b0f854900703980c40c001c09030f00501c029408070350140206404001044402000418500c40c15200c07030400e0745001c00f044405400c03c90340c2d0b9406c20015800700b402413900040d5049514890400035107410805040c07030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 266190800 1250 266189550 266189597
    0xe1b060901080a0b180414010614060705100f0c0206130209040b040f0606080d020c1509040b1305160807020606010207052808060103110d08030708060f100e040c03060501140a 77
    0x18150340c4c42d0300521041141c25040d80c81340b180700400a00c41140ac00e65203145441c0241c40241c0300e1240020300c8000c04c1014044409207004418080024410500200c00948080d000c00c00c01801908001500044014041c131f41454014000190943d80d40e036440b1a078040c041d105842046c02038201d507002810307a000d024060700100340171f05840d40d8030840180c6464407003012180304e4484101c91041c80c103e000240c1c0c0106204660100f121900c4901088414490380c4103095a00e0420040012900c001ca0310344003411415a030750030482c2c0e2403500403a110350094a41a0060f00941c408006928140150301800000342401400030b0300e4000c00c042300e00155902c903410760f420643c010018000682e540c40d014040903144c103130017008070b075a901c81140b00c018410000e1002c11400f2620070303103135820220318540d4094010b070140e001c44000508048811341c01d042c855800c05030040d2403a8400d000d51000c44a060b111504089141e6a82e003000d904074000440401c16004100d455015402c00107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 266192050 1250 266190800 266190829
    0x20403060f0c0f05040e0a0507030204030807080a17010e0412050c070306050f090a1211030f030403050702040e190303050a0b0d080a0305070912031d040f0e1b060901080a0b 76
    0x140c2c005090101525242c030b503076205824014180401c202500f00916100e070b200c9003401e40010141d44102060f0020300482d000075248090105518040201442c01020702403019110300240c80c254221814a414090084200c41c02c0440003280000e4103080480451440a05040d81814081d002440ca06081c0c2e0f8015075a080e1580c083c4000341300c00710140d58000300100c028210220154540c040c040000429910401982608842c82c410701481039807518000300240b03565134209402c00810079000880180d00c101d2034040c0c500d048280006021418004c14500302824611944054005060003400016890303203070718802c8090307900c0d1021078002c03c0c840c0001a031602d00801c0010220350b07000785601b0034480c40b00402c1c0501021030711801041503061600e881d500b42d4441e0100320040750600711503005070600762840d054080c17903044580e03401111422601c0c20324071090007885008a42c2c0708150031100400403014194400c14003035038483d9078a0008114510904e0100324800c04a452 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 266193300 1250 266192050 266192081
    0x906010903080c0718020309030910121a0f100207092408032a070b03090a0c080304180204120f02030a0b0f060907030c0905010f0201060b03090a11010c08090409030302040306 77
    0x2080c828400342418170310b549500c8a00840c110315003650380b1966407040041e00ca12408045d44a01c465900c40c040d100c050304c031b054506000b180b20490183c403c0c222000141c030310449864001d01824240b680d1440e1159040741c1c02402d070365240c09071850081051a0754003200c0c02c0c1070040f1400122003010b400005051881c02566107003031100341824481002d04200c24100c0040511840f410b50014400059884804080d6507039101c50118925055500000070030082d44440006844003012014008541260050322203100005050030200d128031700a05c0c1c483c3c4511055076001c91181c0b900e0704609817000d0101c8400c40310a80758181518002c03a500d154802001c01082210700f082c0c010710344c1281150070244000c048003600070304a075190340100c0e4104443c0ca540840d440e4402d41002d002080b040c210940e81e03091110965840d5030002c041a500110403000d02503072940320302c40c90754100350007091803400d03c803109042101078401101d06504260b003e20010011400303134402c40e00042030112 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 266194550 1250 266193300 266193313
    0x102070c060e0a120b13020d03090501080705040b040e1302031902040f02040302010c0213021e070605280c0c12200c010e01081b0a05180406060e0906010903080c 71
    0x880208100d00b4280c016000f030144490030040c00c0d13440091680190b901c50104006561003c40c024203d114103140654855100d1031620b05040d045126601a20b000303070303145092a591400103036001e101d2481084002039003008200b114400844170f81e41c11590300c0e13104a1406a054002030b14100140840100300d004400001c81107181070311560400402010303096050a2464002a00e52032000202a0082c0b148010704040005507a040f00c040c1a2507854850070480031070003039540b03500160000c40351613283c8404246500c1c441400c46800f10320341c5007030281101506805c44d010704800084c1c10144511103d00b00c0008400d014110080003181e55801310402c19551201400521906920182c0e08514441c8171640d0744140240c07a461000c1c21300c80307819112580200001e003905500d82c21202d202240c02000d490340200181b890b4182c84074020140540a800c100460383c481c40703a10003066041540d1101ca061503d03085501c20414181080c0c01c640d42c0c3c85014042d8040c03100314000e0740009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 266195800 1250 266194550 266194559
    0x60906020c03010902010516030c050102030c07061a0307050111070e1623030a0216021003050402120c061b0c031605010207091a0f1210020307090803070308010b0c010e0102070c 78
    0x422181c810340400314001d0000c1e010540029241d84140e010581d10f04240104080030706001e0b10719a00030991080003150759141001404440e43c10400b0100c03151801d000411a101c504032048412014008000d088a6450000155400116008800c030140100c00c000038140d045a0281403040d031a4040042c0c5030810090020942800c100701d1048800c18148101d5000c14403000f929031003100e02400594420b1000448030010804000007940034403440001c2060030760540015008030301c2550003c03030004510a81c0d50703c072184400c4040c1c0100d010f01510001e603601102e4406114003085c10b9800008102c00440d052401c02c0d031000c00030030310000f01044030b5641045007100034203100c40c040191801925071b00f4142d01e500c031401c078843c4000c03000d00c0710030340c5d10500d181100c02c03108821103a0801c1b0850780080a900100c94080c00326005190000c2c240e5030120803503030116855070342c000b580d0f82000c00e070280380d402911640200d0341d80d426103003260030024401450468080d2210000c1207240 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 266197050 1250 266195800 266195803
    0x519021602150310170705040905030d0e0a08090d0c0e1501140f032403030a030504020319050607081f0617131a040807020a0b0d050610020703031805040606090602 72
    0xa9800c440d1002d080040112962410b1074030400e5611120002056a00f2402c2031072030b0502e90f403c010360242c07410491404210002000b850010242c180920503884a11071068944054220181001030200aa03030003514045400603201881407944942c0d164854100740d074500320887c1c00b003000080420034a0115a007102c000310480320300e891054640b0944281122260001401501500d02011001015505400d40350420500081d08682c0c8444503213100501034042a00c0580c001d0140b5281d45d28100402400d420240760480028a069120000b08803041000200900b06480007083d52080c44d42c0718150006c0248800e42d212900b031046e83d5001c120445028105092a200380804140000c10541c000103101c2d4403101c00b1141c56546003000d1704c1520600100035480f510321000440c191288ca4044c3c1803081032508100700a036a0b50060160b800a000c00c91800b590203001c2c10800a071084200c1c401c07a00010010390081a640c50103c1c0079a0801c1d004080441c07410a800d00c0f00350fa0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 266198300 1250 266197050 266197069
    0xf09030c03220e18060610090315020c1204090b0a030309030312060807120c0e011412030408010507090e0702010903050f090a05180f070c0b0f0601020102070c0305012c0c01030519021602 82
    0x40447d14068154940003001c0d00c011034500c401080400954800581c10440c0c1d070640e08100c49090540b030180303903070b003d004820307602600420b58040d19040c0618154103040300ea03002900e0381515000303092800c540302079501180b84491611415102c0001003020307442404168014580362242a4a0040310705d4900d21040060300701404c50310503500100803000c4901080240c00c003003070b5440d406010488400c00c1c2584100e8221010780d44c2010148091071b5407140b100c90450f91441c0e401412a120301d14100e0036120041c1c0050700141042c41440303164010200201002c080003080d284200342e0320404100011340141220000402c40d604019511208400c2d440d4415164903120540d02d00a0f510172040c19401b5044103080c0380301c08009140c90b4000d604491909401c4824062407a550b46840d42c0600035081403003a03048200c1003011034501c000e00c0d54039603428507a000380407080c00c500f004500508004192000200e034a81a107840fa01c464402040c0c44c0c06c03103180803402d486403030051010307419 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 266199550 1250 266198300 266198311
    0x30a06080a0213020903030c0105070513090b0a06030c050d091401050f010317250c031401060501120207030c0c1203090614070303091103150f09030c03220e1806 71
    0x70024050a80180e48808407061044044640161510b828402203480e41c040c0c5058000250310342800d01289507000b4014081082d9200048042d098940d4000c01c01d4030700d030303413452900840c10420a010040c005c3c2c0012840200c1032500508004654029105903001c424083e01c2c080c81c01c0140e403000d82020701503594003c50b284002c1c062549595140c540140c0c00901c005160000411b2920b460034000b010440d190340505030406088090b410007040c5065144400c88100d5490151146000010b020b03010031240161240080f414000100c0c50295200081c210204121100700c13030001201440b0310030240c242d044900700803005c94074000d40000c0c1d00b0f4000380140b2075213504111343c010b021800c550302d01d03a0620700414507504a20340701e916048410950741d0315000e042502c0421102c3c41d442607104580d10740380260140c4440756001c0d16480707444003880160b001000310306140c0c0a0790300b01103018010300241c01c3c0c105503612030795101483c0076140c01450140c403006010102d40200030f80c68002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 266200800 1250 266199550 266199553
    0x1300e0c0109030201020d050906040b0a020105060414010506220504051602061302210715020f07140904120c0507030624140d0303020c010207120807020708061b07060f02030a0608 79
    0x100d0954001039611f0300c0c0c2903420400c000000840f902c081d16408240e500805140d0703105611500d05a4019028102c2110183c0c0258580b0389551407602074030044a0403910060300d403030311300508481c0030445020390500b005140f80c0042d4000607562164440d0743d00c035030302046d5a804030386d005003c001e06010740502460302c0e1003a901c0f2a000581c4c1c0d290444100740c07503028580b01c0d00045c0c2c1d1b0307625810484140d2003a640c102602d810300702c0290300824001403518400d003c2d101c0e840e480300c29090305410312440340c5400c650301c2000503002555280078412422a14101094180003550f1194544010368000301c07061915400035440c0380f54401c1c0702000da8800c0655181d82d082c00d21131214210001c0203080c0f03101d0305000d2060b0701818082c1d411038448110343d10007555034400908111100225440c10728000030124800113110500c00304920080d03544260181420792980610320705002484801c60b1000001080460b00141705440740c282d0044d00b0090250b2a450041d2200044510552214849 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 266202050 1250 266200800 266200817
    0x1503050c0a030f0b03060c040906211e0c0b0403150b0d061a12030309070605030403020307020d29060f04090201050d020d02090901080c03060604140601300e0c01 71
    0x19018250241c4601d101d042c0340c0050500d5500c3c00b8400139241c2100350f981c0500540040c8694454518000d1094030603040701400035555550340300d200095200b4840020640801020300040d0540010505203e96100040040b0800c0e813114035814105030300017018800b00141c200208100020b820082d200c03415000c028401e42e440204e1800301d52030000510316990740300140c40c59421899541c54a51000d030644184646984d140d80d620f500542c1c0300000c5e8402e03034800169041c4510200ca2045a05501542c01c0000c1503090010202d03c1000403982203660940d03c0800301c44031002c409000c0110082c203555420144280704000140d801ca00d8000c0c4e017440e84200250740c003d011201044c43e0380320016581c580840d100030090041c0b00d00c1039444607402000044100c0c00040d5420315a8046044d101795440b5a81000202d46a55804403440001031002a44940c0201c982d00d40f40c5080340c0f0314000c00034500340116140154400c0c149080b81e40c0f10246035544104008100c003200003030908420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 266203300 1250 266202050 266202061
    0x91202091611101401090c05160501060b2805090109062a080a03050703020310090c020f0d020a03080f07080c0304050f0610050f030d121a090c04150305 67
    0x264040010001007012540d031015a01d500d1080c040c042ca40503031041070311807105030031652401400000e0020a034000c030403000840c91020b148900d9940e40b441d034503298a0510240d119181114101105407099542c0d800005160b01000c8010103411b0054180b1036003c0406000c0e075159095136500d00d00410109020300707c0c050b600100e0032000d40d46a420f141010f8407640102c0032035120b280c1e140800034100202c04004110348413001c2c0c80c110b6440c0c2c400740f01c280e031225800c0307089000456003141801c1050404112081d40d50f4407100c2c0c04170703541c030650f140c00e42c504c02c0705882c2060741c02030100181d100b01022403c4c5944640c4030380e0404c0c40801010114103007240020006100508a0001d000e000400310b410401e007040501082861081035800c0c5190840e21030003043c4940c4900e6001d044140003641d010315001c00d0300c82c0d20300450b4031001c10856807590028002c221440c01010405000000400a541c0f0054068414021121840d0740c55081c452054001030700c1c02c80300360a05051005002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 266204550 1250 266203300 266203309
    0xc090605041b0e0f120a030302131202030705060702010210240603091a0603030c070b13121205031b040b03070f0207030b0c130312081014010203030606070c0815040201091202 77
    0x1140d4940c121004d032000c1d444c080005a03402d40d42120b0000503c55050314070300301601500036198036617560700102840c0e80e450b6000c003401e1090050095040d00310748014410361a18034003501e003090041c81201c0000c1d0000d03400000710781030b134043c4409133591540107010804a41c00303140040c0c051484d0504c0310956a5840441c40000014405145d02c501c400155007514100190781a940b0124100d0300d50507590200c86500380c0c8031407800b035802d903007070f08003c146500c02031020308103594072202c2404140c107a040101c07450b400151081406d4103c140e06041841c500002400c050a507601e40d031780c3d032418106809002c00100981000c00e6404c6040208003050045042c2e41e402082c1e9200d003980c40c0c50300c201006c100d0155410080c0b014a600b40c3c1038590f1035000c01800c1c4140c480f15000d190213500c03114140d441282111000d4010b0f8010000607050342404005400000c1c401d054500d0120f440b039a1280c24500e401c3e10139240d1040f0f0804010a41d0b070301405803c018020480c004208088940101c2d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 266205800 1250 266204550 266204567
    0x30204050c18270a050105190302060711010302160b10061704080304020d0f11090604060b0409020f0c0102040303170a060b030a02031e270705090402010c0606030c090605041b 77
    0x85104541a2620080c890f880d42204080054001000350942c50140c600310004c05d001e0140500540c1106017034020720f600c200c0158240c82d0001c00040c10480c80c1e540d08211542050107403810103800b4800c00070205041c41010a0003441860500d07090300d403400c0400c00f041c1c1960300c030004000f0940e90711030341d610300501d0998200303410000c0590360b90740b103001080380c12a5901c2e004105001704100310041c00940e204840d008401183c9283c0320361240d204100a41e0000e0080300c0104804010030440030078030340d00921581014941d402d0411a0360301025003285c1090703109901040703012880101c10884480f050340e00c00a5aa010003805040c5a1280258000280740c0703052640e000000c600c18001d40110741518171808812003409113052840440058250140c440c072801d04a0407402d140c2d18042001c200f9a80d018000c0d0a43c2e54a036001140c0c1211041815503216540e024044040340c02c1c41c0e10038028007100741c00400d0703a916110510003121480e00201880da15904d003200103569010300036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 266207050 1250 266205800 266205847
    0x20f1b0105040b0a140f09030c01031422020406090b09010b13151205270604020f010c0f06020a05040302010f020115030b0a020912160501111c050c03070c030204050c 73
    0x8458031880c1c0d001c030545003150717461444d28100c400440c5444805002c0380040a03440d100341c003600d894038006001034041c0e0f2090611a400c0c0041000020000042205515203c03c42c1d40256000000c4540100d011124582c001c10a0780d81c40701c0582c0ca0904141407081e00511545400d94030f000030750310260324204028025002c40c2e0301c000750407c106611604000c500c00604542c1009182072001c48164000d25420102500901c0d00c824540000c1c804280070748a90b070040c1c04607803581400030044800c10201d010441c0c004142c41203260100d84c0300e10150204103050348400d1b54490960001402a05c0700500b254116810a40584810300150105e08101d9500140d0584181c850300381110180c043c481c1100d0f00500341d00101ca203481d4000620703400043e00c0307404c0d007070f411a118001151821804e55000c0c205901c03484c074100c0121107010b00069014143d141841c240486805d1460540c0d015800585008103860024415450b051040ba600007260300c840c1858142904020b01901040c1000f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 266208300 1250 266207050 266207069
    0x6030506270a2306150c03090f12030d050f160e040f0f021303020f090705031506040f1805090d1d0a09060e04051b150702120607020f1b010504 63
    0x11403200100c0f50020f841c00da07094204420f88103490f82012200002c21100c541c46039401040c0800024403010481e142030303642c0340c0910300c0c0442c880140050040700c918580d8004440c0c2d802c00f0b000c0e142c28405022803100034040030a45041881201c00e0882001d051140b0f11080d0046100c3c2079608404e0360380e010b007410b54000c110049110701c00341c010010f502d0346180c400d00001d00500401c04046218056910031100c0e846414048000d01c041c12904550b10004100200045400840b0251150601810090a40d0f2078541ca0302c2900b840d03125582d1099189e0303544083c48851008141c000e0542c8403a0941c001c1c88400202c610050000020b0007092000c0c4028005510050301c0740d1021308041c0c00107500621000d0307a104000c052040045909956502520130120101e94524081000300f2030014010380700e041c64214080003540c80002c080764400040f089c400d200c0c52090003058424401500035018040d207890405003040061074080c05555402c11400055030380003c140c0b800e07a864580c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 266209550 1250 266208300 266208379
    0x7082101060305060d060b0102070b21010902070503160f12050304050c0306040c170708150105190602060c09120607030e0f060f070f0909090609150c080103020f0a090f0606030506 79
    0x40cad00b03050043c1c2110f080e00c213000400d01180c15400b85226034400c4c5060498400742e0765030350460101c1c003420000510300e400800030040020102c054150030315015120342c1c42e114003a95a0403d03000c21001020780807441c04400c001c28003805000b0b03843c501c03000354090051071805a4031041e40103020b00601036802c25070000c101c200e65040100c44054840c1d00c08807681c0c0600b06801141c02c002c01d1150510800104030b400c1c1b5542c403c20510021158150018805038440c1d40e01303075041c1c0d0000000b664101c4d1500a0008603010308016160240e900f60b08d0028220b50140d11081c200512214410510390050b000d01040940b0f28250329403204d00740c81e018080481c1c1403c2220b109885910915040c0e080c100c1401c02d00c0307002d0b070004c0000c40c45419280d8422005803840720548401000c0000428510001000581407005c1841c1350080007c011144e09912100e98104907403c3c08240750341650b980c081801a5078062088a42000b002c41c2c8045208002e03601440d00c421a441c26400c0365072152 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 266210800 1250 266209550 266209571
    0x2030c04240801051006050a08010522142d1f1205070e070801081b01021002040b031b0f031305070e0f04030e06090d0201050c0307082101060305060d06 67
    0x40041d4007100305801c40c08141d49040a50207080c0a0780d50880118624400155550040701210382c0b140c00c81e1925840e50f843e14082100300c4c181c0c80c0b0046d03680001080e500301107585a00c12102441c40c9285c900300c00d4103051011070499402810b400e0480307010003004d04410a05200c1465010f049036220a4051803807003003a03c201c00030340c0d01883c2c00f07031069919401004800f10302107041d141004008081655540001c03071796842c0a1268030306a420800d846520800000310100707440c03106004039801a212024103604030380c4203600c5100c005502009121601601e11124903401c00c200f54080e0400e0082c4100040c0de220180101c103030048085810000c01c00203011070001001e030000e901c00c8a18101c4500c510b05d071411901200050010590303c0c1e0140341440a882040d00c001d810220442015030065807260b0010004554501c001c2c0503000008843d040108800826403c0802010004130440d2800c0742c4103800c00c40515040904204603a140d034102ea50901b50001000700b01c100700d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 266212050 1250 266210800 266210831
    0x60203150301090c06171e060d0804060306050a0f0506040e0907030816030e0427050f0f0c03100207020114070f0609061b08060916021609050f1302030c04 68
    0x80d28105825500301800d030014420f021002d1400c4440588800c1040001c04401420054040300c84803008203854591060071420898515072019015090071080a51915010b480303810a85c01280000d46a80e030034030640c01d00c40c1c61070000b400311060b44070320030341000005500c40c040c501038151007000d40000134dc1490000c2000f02c00a5420120f0345540300c110604440e4501c081c6d140030b601140d044251010241020311908814038904090344103903502d01c1680c3d11221a00140c15195841441407000000c2001d001c1c1310b04cd0b550201c000c002c030a0b0b00e0002d050030f00c032003858440c0410b881030115501507600001e0158140c440001d1003170f0385c0c2c030407880c201000c104104c1001e4122490408000d0821001d9401203250a00307100540a142c404601e080300c1c25401100c21580004100011912542900101084a00880c010b40e0011040c0803401190744507150310182034151244244100400701440a40d0072020301d0406240140d102d801180d031f25803516001e64000d035510808000355400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 266213300 1250 266212050 266212081
    0xf07051c0903020c04141003030813050f1c021501030f1e0b1b04060c0f0611070302030301060f1e0f200709050105041404240204030302160b16060203 66
    0xe4058003040002500c2c180250b5400c3c00e0310005000720314110300a10003100c00c00c601e0744142064079024140d1350940d6412603503640003501004003108034090040001e002803008281c12a002c0c401022900385c4101510b406c21080351202c02076400440d100c0c07034001041800302d8150303a081a00801c41c1d00b42894101d513030005440c0d108584649008080c001c0004081e45035003c3c2c600c00f900f240000411544102c21482103104490214000000010006074501e41651200b40103d40c0021010400100e0300324582c01168100c0040e000007005212054129079116142141171070302d411b200c80c200791541c007819a02c0303001c0d000f8001000607000c170b110300c5000117441d0441380204001d200000c90b20025910b4a950058200c1d00382080c00100719400c280c0300c0d444070140c980c0e104040a44031521200403c040800da07488440c43c8064034000d040106000910046100358024050010b06000071520315106800143e85008204412b00310420b090b003001002039003210006959444c2e11072260794811 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 266214550 1250 266213300 266213347
    0x60f12060e0402030d05180f060f0703050706150f090905160b041703030705071707050613030e010c080a050903031b030c0d030b0904030c03050d15050310050f0705 72
    0x141803440224040c600c00e0240303401548241c04a80c0b505c01070400903911030203514914800062007071000d14031880c0103400102c2e049005000c8a1400054000c1b00313071581c0c040e00c4241e0100f88005203482c200305e50380c80345001c0203022640001c281e40c05c1880607034584040b0f124a03140552500b20140611805000039165200d118080d60090b03a541d1002c038166422601c9046e055829022110100d8103010049910a4800782d071601d00d40036956452224800c41e00350320401105041c01103000040d400c01c84c1c64004c8a10b414003111b61052454014400740145801c0346c104100140c00600040c0c208042d16220200c0741011070710303030400b107000c04d18500510f440d040c5034607401c00c4500b036642004801000b19904120941c0c01001017004150140c0300f001038455041600400043d022074860b02801d051a80300740713003907031034071500210715020740e0121400002240c90701c0c4401c2200e480d04100b003036500c0c4070701e110520062901c9540e10300e5220b8003c00640a000c000940741c51800000d007408880d59 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 266215800 1250 266214550 266214587
    0x309010f06030b010515120403051303050615120c0306060f0f090a150b07120e010302040b192304051905030f03040e0c0f0d090615300309060f 63
    0x1c035540d06150b80d0381502032041600802c1032034809900c006010007141c41c40340000b5941119911959400c81b441d90020f500103059003080380300400001c5060080c20302071040010f02c00c40400c44031040002e20710404122141c1030b848051400c030320342c4005c540e003030b03200b18101c80030340300102400c4c04500200c0c48800b485600c028050200004000d183e8881e450b805d07014104810105c1d16080300c00228411420b0140c0340ca28901071601c4503e1140100240051062402508240d0f4401c0d090f00c6a41000100344c00c807282d041c00300a00c440c0d020f42020450b803003c450340d016100045108040341e01c01c5000386401404400003a9140d1601c042203c8014040502155511700155442136107981140c020448018540404561920510401e41c0e41071081c40461a10b0301207500b40c0600109001c800898019807240909506142d2140040c0700503d42c154440b000d80b28807114207000d150041059042c20703c0100303100404690310144c444150b80c1e1310309241800d000855400d440b0801124087c1000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 266217050 1250 266215800 266215811
    0x12010e0a030305040b0601020601081f060906170d05032205030708030f01080f03090a1e03021302090108060402041212120903113904020d2c07060f050309010f 70
    0xc055140d800307284100d001c1d985c9000070b034560700e004984443c1e00784a201c840303900010f24030707090100e545908001c0721030707a4400254240d80d51901c601035030b030035a00100742c4003401100380d0340d00d403000c1c001940c4440076864407500e50715040c100590f140c0d0b0100e984048258000c160041004000c00842c1e595603005240700f0b4880c507000c1014410000d090062100d035005617aa13210044500000307851a050f030042c07070603014a04020010b80a20442d4410b00080c881c5a0b4001015840340c4c01803003017001c200c50016981e103030307100c00250400038040c0030280940d10401c401c004032019808813901495001450041c040055102100c0340101c0da1041f41c0890714080701d00b42003580043c4a0144190180142c1d241d845001c62841c1c0c1658100c1d50b0307500700c01c102d40380c000780040d164280e022561100610050411915564020846080f00515400448030310840308031b0307500c250007001440f110000145555030504600600c40c41030744c2a003001740070020010a0b0814000c0d08141c5c90441c0c603000c10000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 266218300 1250 266217050 266217053
    0x40605060d0e0709090b06010804050a020d031d0a031707170d05070905090915070c080f03060f150703180308120103060c020106032001030204031703010f091a12010e0a 74
    0x3030140001d00381c942d03ca000400248070000d40110b01002d600501520240e680728401510310ba03000800459003805024007100060ba1545084000300340030f075550400c050b2400f10a405076040c44080d2a11400b05480300f0000100e006500241b10281d010b40a900c4200d00e1806c640c9270304442c0324a030305200f004900d00b03904104c1d641c407140c4607000325955000c10580d1042409107461082e912500f01e50030008424110b500d0f12010300390400307007034501008204456200d444d0150840c0e03559101b0a0000820301c8024034010348030600c480000c0365050398502c814084075200b40f00318003004050150308e48980c40b503540002075010085800410456542061650040c4210001d00084816030718000d0010360213841446000141c81d48042100e5090046080d80c115804841c80003a04058003080701100203928550100c8641e200e1150390364403941400304101442d0881c1d00504c150b64075040d641001810204a65110f000040d50b1100c007260000c41814003406c00130b105050b00744540e80b2400d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 266219550 1250 266218300 266218327
    0xb0a17090325080313020114071b0618030b13021507060f020913050604020f130303020f030f040b090a0f080d080a060302060403080c03070c0b0304230d03090204060506 74
    0x10344080e01d81c001c0c515407440c090403020000140c0501816011082c40040c0400390480b006030941801410050503c43c1144200b02355640107080844040689c0c2c0134498580c4400e007801c0000d0489030401411050320a0024100c08410707100180950541f030000c9083c0c0380545a81c0701c80c06402620b254042801400103000a1f809600c045550b5803829a200c008448984259186030500030900e005144a40c076034000036220280990340d2107982040204181c0142d00003d0115462404003c0c0015185040103800d02c0c41d294640c0416410410407005240312500450f810b176607582203410344400c0018040b40a11000d9040400f5100701d800740818608000100c1f08200c00c0d0396550208203980f8900c140040c1e400c5880001d4000c0d206210600020303003103030042d00061210740c00b103d061081075201d202030204580d12106902d1400014001071184400c081902c00c1c0c60009020101503604804680d0381080c80240360801d982c5a00322800c650300d541008c0001c06009045075191030030034001c0c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 266220800 1250 266219550 266219557
    0x60d020a080601080c09190504020711030d1805010c050f1f060b040b030c16050d090e07030c021c0c0c15031407090303030510090504030e090702160b0a170903 70
    0xe8012405841c0001c62541c0728040051090001740a00c0341403406201c244455011503400f640f01000b28036001082d641c45502c040e00085000b0181900b141104d4414503080c0b01c044102003041042c0381080884030310f44041c014044070401e00e05a0040811400e007075080003000c4032902001d000315000202c40016103001179070b4408801504001e0f5994a80078014184100c0c4118070304400c00f84001044200020081c10040c0c1c0c80c440044000401696407504002c0d00c03e5152011450700c2c402408241c500c5d249265102c68941020008000e520300041d645120032500c403440140042200703e0820f1085180e0f000d4258041910303140e441c0c8401d07145e0012403a40080d440041c0c030702174892400d140e0940c038580c0504800d4807220115821500d04402501000309041081c281d040d000050280092081900c0b90b8040d0b50345480080d4000c08100d1480c8014110381c0456203c802e0450384500c3c800300d100b084540c1200d282d992620010b5040d00d01f04901e81c41e14444140e4102003004801c8040000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 266222050 1250 266220800 266220817
    0x3041e0210031401060903031713051c0207060302030c07200a141f080a05130f0b070e09011d040515010f0e0a050c1c06050418150204030305190c02060d02 68
    0x415081d40c5e240e403001c44d001c18880c48050700080074005507020111807458071940013480d1940800306450760340c87e590314010600e036019818010742090006400ea040c0250320140a40f46410f40c5103080c00c1082800d9400340100c050200b140c0b00c01d8049840b64407400e205403a842c06494034111a540d00c90203007541c0e8100f100c680c050303141d4003104110f040105a00000c40c01d140e03220110107444080e044001000010a240f001100c508140070100e0010900e20b503120b403203040000301a22b890540200402403141315940203030344001c0140500d802d0066021003252885060909035911400c0207881e04040360342041c440d050401c00810b00c140e2107134a20094600da5284225251611501041294400c60b8003000100c0c09000c0e02038400b03420040350f5036810f41d00c540860200d8a031400101140c401c1c0d05642c00700383c80c4d0059641088100440100c400544100442c145880c0d038801510902c548840c2e294040820b121201c40300d80101860310307606030050901d64540829880301002540321255 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 266223300 1250 266222050 266222081
    0x21e0703060b030f1903181401110c060f09060d061214030703080f0c070506010e09010f0b0a03030e1f030209010e0f0d0b0a0f0216022403041e021003 66
    0x1036801d96410001900c80813080428010101e101500c80c100b42c00e6075224908400f0805407006140e440c9078040c01c100064440c4030410007a084141c0005401c0065884101859800c200242c0085603146801e9071100105d03140225a40d12094000a40038032880494041030b620701440841c1d5000500309840032a44a02c0c00611205803580c001d03942c074052664020700007100c110000b88807228480c00603800c50650380c51a820311529035102d600700402604000390540d0b01004110100109000c2c01c2d0700c1d98400e40c0c04011086810000c2140f520481c00080c5c28012140f41c41074a5840e160316600c0c041100001281044045100c020042d502c0b00c50003500041da0024000340c14a00707000c01c103410711030080c000c003591405582c50300c4906500514a41d03825503120351200c0c4007000d60005018240b10a9082940d070603da04c100f042110358201402c0e0500d4402002c041700c0b203901811241c01c42e03007003485a246042e0310b040c0702c2500340c1d28180c005c0d080518601c2191002d5010b030402c40310840b0041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 266224550 1250 266223300 266223311
    0x90c06030c080c040302010f1419080105060a020c0d080f031519351212160210020904060b0a1101060b0f0a1107050d0f030305160e10021e070306 64
    0x341c088070889001d4452006038141044104015802030040c44503040381418095913040c0c40c1d82d080840c9411030440c1310740550320201480901e03640030b0200340c00b40404440b1300342020020782d40299101c070300f010218000c0507000306172018421148151018200e207a244281d0700e2400b104100d05000009900ca4005e800e06100c110103440081c901d01c0c00c1c4c904000c0c0c41481541e41c0340b400804000d4941d14038071095501c18524a00080c14441d0100842c4150802f80d81c5001108541c0c80d08000104800c1c400c0074443c0701000080d43c04039941701d40080404001da11a0340401c006030003000c0c00e0340000040180003c12582071500104c1101c0040b18620080007066940d802b81200c034031941002c045607036010400080b01c43d01801000d9902c204007000c07540e00d0390b00d40010901e009038602d820b0f00c06240c200345032020180d2500a00c2d9000740c0c042c80d0306c00c40000204000d0700c902c400011062040000b100c8042c0c03074610030007080700c0702012a1034591900c2552280c240d140e4626010564802e8280f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 266225800 1250 266224550 266224571
    0xc0e060409020f011805060c1f0501080d050d110d060501120606050f13090207140f0a0807023705130908030f0709030605070215071704081c090c0603 66
    0xd1007032a1005401802e01c0c3c034000c5000f001105d443c0600c091004c3ca800385050041341580740d45000e488104d0110000346203d02d40303900320300d0880d43c6042c445000c881c00e0200611441c64041410f0810950303a00386a510740b21111446030181c270300c400c40140d400002240980c2409200e4100d541194004e032500c01c0b101d0501c0150005172013003800f850012036001c220300f1030b040d21170000800c034407200040280d50031501c0e041000140c0c2d1000324251030940106618a280000512179449151801c2000300080b091580d42c6141d075000340751010b071060822102d0030300108182082d1a42d01e96100310b03003080041a0713a5001c1055151806224003d81c0344035500f03500c80180c0c2c03251140c40c5400440144c103565600618111820008240108001364000d000000074882d00070540600141c0d00a030045d4405101c8114034840d006114004000199016425400c2c000000d142c0052b04802c1141c0d4425286041d0300f14505d45600401c2c40750310701810181484414061102915100d58060081c40c208 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 266227050 1250 266225800 266225809
    0x70516030807090e1e090705030a0803220506060609010c06090b041407050120010e0a030908060703050c162a08010b01050906040e0910050406090b070f0203041a13030c0e06 76
    0xc1711961040d207010780461000307000d0800210703480306000d0308842c001c41e00c80022074108912618121034207070021060000800b41d0901d003108486281c078028001e501c580c0c441950f03c0d040903004600800c3c0015a0000c140d21400740c0207107070381c0c0191042c0181d6246140c042d03048013040340c003038426100484110641c8203020990504861050b5a25000103200345110480c1d2082000401c0c2203641c1e80000354401c1030705214401c22540a5215441c8244c6002003403810298028100400c041c81c11080185103000c0c28180d44180c0a0088004e200c080540380c8a0440e09040030f00c4400150712900e0308420044101079442604c9010f4001d100700460b20b80151424017803502c07696402071060000384400004c1c88100e5502091480446601c49100d500c2001100d00541e030541e5900e0f00e600c1a00d05201c07051841c80e400c8201d41c54240d05000c0140c00003526030240d03024042c410401951803644d0b0210400550329000c189451030000155203241800b0140094459140284010780026515150 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 266228300 1250 266227050 266227079
    0x20a0206061504121103010f06080303011d06091f0302030f0d02010e01061d04030519030c0f0921020d0b0a0207140309090a0b061605010e1e070501030507051603080709 74
    0x3c19032040c01c1002c2c6030368038092031158504a440e0199038074100c0619540c049c1c0241001131920700003440c0d40b541046800b0700340d4444040411f080007006418008503850744001030313034800780945040340310000c5000c5040750f480d02d0f503001950500c80c0081a001e500d801081071000180d16070001c0240013144004642610007070310540e003060002d0300c00040c15a2407040e02c10352052291601520708007402e0060f0703640501910610000035920703003802e035405802c0006000e01221071306080345400e1405007152034035031034458040c0703011400d15800d200710344640140b01e080ca54440003000d5540f0341000d00780d000f900420010b46d91040f2032a2482c095100100440d002010003410f240d42d5540e8851400e00541800d080507508030710304011104060740f9000320000d42e1441440003040c0c4032109220b1a1401108480c000c080030380f200c6040500c0c440000f5020704440d000c3c02c0110300d0f80e0b541c0b14103540700e0191884818060040f00341d188105a44005c020744144510344a81c00b420b81c03500d280311032808 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 266229550 1250 266228300 266228309
    0xf0207120801171f02090303070f050607120e120c0109020303030109090218090c010305060a03050313080105100b1206030703141c0e060313142e1e0c03090204020a0206061504 77
    0x130640446030402103182c008255148000d001c0364949a650b6480300300d0526288820365190b000300c82400b41d10baa00c01000c1e600d0710ba048c04280100e1946400450300e0f464031070040c11032902c0c00174816212090a411a81041e030b002016252070750380d90080a0060328880c4800c030700c02c50b61581e40204402181d60b20601490360b0400a000703400c20345005400070640646a203601c40590140080006c908000a2000d684c1c02c5d10b0702c2407050b00c1c04503a1825204c0c068219450349103c80018454003203104151240c02e40e203000381c1c04654942502007400c10340c40350030142403000c0907116420205000102001c0170350704d21040ea5818825400102c5140303500c80d04c603903440a4200b0100d01601805000c10a10500070052580200d403c00d2103545040e1200c101550b401103c06810b4400c508202e20040c05004a40c0703007400b07060715030f910305440030031070038007080c2041d03038904550300107900ca54000321000b80c0c0030b4401c541d00c0107c00b41c00b2307507101c1044650310b200310b044500d00800b68410800b610100c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 266230800 1250 266229550 266229583
    0xc020102070512030a06120615050405060f06180a06050a18030201170612010e0a020109120209040b070e041109090a060f090c0c0b070f120203010b040501030f020712080117 76
    0x30f0610008840c5070b0792026040034141511032130045554101050325201e0b01e44140c0b00024050714038000480071100d241d01c100d00ca9807800f4208021500e403c6003160000741c04850603030f81d84180c810071070540203046640c1da40080309204041861604240140420321039a09e40c21000c8440343c01c1d41d1440d08035800020300084600c003000b4488000d1008460300b00708010030409507031280130952800c403910007416a000d980400591025942c011542d4009040032903580c80160407a0b4010400500c4044c000600d000d48100016001c1ca11513541d80c0210000104140001203840c203030301c2c049030002c8580f240324550071000b04460703030128420345085400c0003c420003101c0c503000380b2400601d445c81c40321040c0601416034034000344806001501c200c40c5a1039183c1d290b41004070081c40c0c9517003000e44085161042006101c1420208150340c03c503502441d000ca4071401c0040c500001e400340050003404100d005180d03000d040d82141031079050320b2035075034107200800c2d0b03079071346560340d00040609000c40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 266232050 1250 266230800 266230813
    0x150c05010c09030c08030901052b11040518040506070503060109031505040b090610090209030313090213050909030d11040b190210140f061c0f201c0507170c040c0201020705 76
    0x5040800003480e021342d04c0030b54540b02000d41c840003030150bd840c1c1005000301900090144001c1c907210042800184450f0301c50112403901e40d0307442d03642e030001400341d006002021001510583c8213001ea2000b840e40130b44014070550f4403c0104024010907101103441160040000b541e01c04006003d610a06820000c0d20031716180c9021140250302c1800100c1d01400100044200910550a92002040a0320005a072035194001c000118403543e0891072148000c04180141c024000054500030303844a04002031909004e0f04c280e019220385d0703100039545040840e41614241c1741015905e4800030b107400b035a03200c54941c14824102c49450b00000c005481800c08941c00010149080ba404140900440040001c5110452440031030740c3c400c5403400400d04682d010407920000844241600b900515040d0034440c001890004d030100c0071403044000c3c144081c042c04400c200340d40042c0305880f2400e00c40100000b19949510200420700d000c1c81c10011908182d0b84140300f20cc083d00e8109015005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 266233300 1250 266232050 266232067
    0xc080702010804110a0321020d09031101020307120c030806010206090d1d04060807090b15070b040f06051f170606090a11190813020604150c05010c09030c0803090105 73
    0x1098000a030042c2e40f1101900c5036541d46440d4000000080c60140600c59910b151403840c1c44091404a0400c07c11908907145880030150048510000c1c4d981c0440c810320a02e0500c0f004030b00e58041e071040a04282c1000000703c0050341c2040b180e0031514040d90b40c40415956050041e80c0d40c54055803a507980794015080100c600703208032800c00d0b001c030514401260070b11040e00000d09079195900104400d0b006001c0070051260580718000f0400d00c10380b0410081240c2c4414141e141c083d00e440505110040c10000e410400e10800713004089034029410420350502c4100c1c0b07070601c0450442e040004485010204005c0401e442e448500d003104001084a0f42e01c03007080c00107006001d0070711010542c0320102402d01d060a80040e0140b040040c46500e00402104002004080d01901d017000011110700d00c4070140e01d50f403080760243c40800c0341800069240400440762040d024801400715413900c0e261608c01503100301d202c1e08890150300f140100070b4031060481e031a0f100b41d0782d4003404134000300700401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 266234550 1250 266233300 266233307
    0x615091501020a080c0d1b020f062b0c02070501030504050a11011b15060b070236040503030601081f050904060f0c0207050a0807030f022803060902040c0c08070201 72
    0x200d5240061040d40c001c01076950f10b107052504a04a0044a40c001140312406580c1c0109030a45036220058111b02814194000c118030740041c0905900400c00007130103040030509440c1c00310040d1031600c80304c01c1c00410410785000914040c62040b006000302d040c000b07040e40c0b09018440c066034000307001d00305040e0030740e88400d4040d031b05140c0d640c14042d801c88202c0c0c403540450515440540940301402500b048280c541003200c4040e009000c44110901210b409611090b2131103125290599081c1e109880c0d2642241c3c030001e156190340300106210042104101022014600801c820b898140c0e15868001001420401c80c03040000c0fa1074801c80108518035100d15001d8005005c1c1e0b41c001000ea440e11501070a40b05100b400c02d025070700290301041a800c00030b000700001c0c407070503020300030750341c21b5030740d030b4503806030000d001034070032a030300d2603281340900b545042280c20042d9009104d000d0799482c034150340602410001a480f5a00e011408098a40621141700ca000ea21021181c9020304550055 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 266235800 1250 266234550 266234581
    0x40509010905100305100203040201030c05190809070512030c060114030a0f061404060b0a060f0504091d01020c0a15060312030c0e040510030606090209030c101209060905061509 78
    0xc494904001c3c03000002c504d0600509141c00180c410140c1d580c541800090151080c8509460820400300800c0801e980d403141c80b0354101c00c00d49010505510b9514699184c40401c1d0006a40304018840b04003111000000134400c4640c03890548101d682c0c0c0d0601c000b90750b0300f801040c0750540c0058800600046800b0103064000b4440c0c0340020700c00070b41d86150f8080640c1114100c6403117654142c00c14591502c11060320017030410340380c0504046201d8500034824000d5201e00814140c6078910000010300003919460201e40f080001c54486012401160762000c0303065040d50030302000c1d05800303402d6800d0f01034403081e02c0c0c111440301c0402090385000c074010040401c04504020b01c0c400a255960355901032207020741c2e44111004189800d40c00d00b64100c50310b0354445800184104100c41440d00e010420141c81c030400c40b00a1006a444001900c9595032003000004a0346006151420880c0550100e01c2c801c0c001c000f120015070306d400d2150032104044404540c005075020004840000c94a00c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 266237050 1250 266235800 266235811
    0x102040605040e0c040e131130070302152205010509010f030e0f030306010f0905090609061f0810050409020321040e01030b0a051f15091205010c0201050c040509010905 74
    0x1041d140030740c3c920030302c1014075059491f80042041c49401c0402e010003240c031091141c0c802c031078001510540c0380356000c8120400e03114007041d640890080f80030b0081444150f000310340143c042d13415112a00c1c00890a40d1064000c0d002480400340032080d0250140082030035100d040c0c64441c0352289044c01500c01c0300300074501c6001c141c0c80d08460120707848140b1180f52001d42c84001540c07641030050005d01a040351049078010415004001c02c0341d981c541c10f0a90f00028203070ba031440c65444190100324080c0131003628076440c414180c1044030072030784a100c0ea8864200c420109415507102d100704000c1d2a0301c000d01035803681c0301001800c0c0000c001d0070000c6258094580540c075040e074900c0e0840503243c09a205a4400200500304008480b00d0b004250b44540050140b20105810b10740b460030307009450185c4210a484220041e08280c0a0500c08000e00300455105625041c18603120780038141c4020b0400055007001d002c281c06640340004d842c16110010a40341c09613081c424458001d240003041c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 266238300 1250 266237050 266237071
    0x50a02070609030309022103031501050702031902010905010c05030901081005030712060b040603020a09051005042a08060f0d170a05031012080f07050a05030c0f0106080102040605040e 81
    0x6580010748207219000002c0c1c803036203021030018601c1c010000e5034550054141d01480c03000207040a2900301204403a406940c400545181d0007014004890074058104004d4051203601d5100024042210820040714803d1f038900e51613548980c011613074031080311070041080d4000c2c400320034198002d8003055409000b05d801010015a910b0010389800c58680c481303c6003002128854040c0312060103038021100c0c1c180e9051110502c5c0d980401c002103080d20a01345029698404260a509442c05150041100030000d1184055418814080d103038120412052400d01e04443c0601c00e0040100c0303403280000178004101d112101080c804003130183c1604603021084644555a00903a0340d0151000b5443c0350f40e41d607202d2030a080d011044c070900c1d4001c8010480c0703502c111800111f040003101d800348000301541e9128110341c6442c03440d0281004004000c0d02022822901540000542a8500c3c01a4001303118940e500d480c298200d1045008502c0026030410050240d202903041c4990070032401d04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 266239550 1250 266238300 266238307
    0x70c031101020c03070b1308010b0102030304020607080d0f020d181110030f18050d020304050607030302090d0506010803220302060301090e0715020313050616121101020309070501020d0c0c09050a02 87
    0x200103130403c080d031741000c00711b500007007404144040c44400b82c901a2160100802903403d41400203541c84c0401000207103e20f90004540302004015000d0300d941080d07217241448440f00344155a40690030045444800514000d0450000304c2240712007801150040c0154a1900300d21b4203002101c60440d011905168071398200ea1405201441114811182151000060100c519100d81062854038a08086610910080c80f490750f8031002c40d00d0039945030600580d03518021000c2944074401c418043c3c014001d040000036910301c048000c20000480260303540b01180d00301810f01303902c02c1c18000030390010818401448040c901d075000303550b0b460428046030181c0d40d03180491005900c11041c0c21340143c002080c00f8005054003103e40d005003034102c2d0325a041600007140d80c03405801c41c05014084143d001d171a000103a000b00c148078a000d0700e820007555640b80160000307075550f00301d1042900501c103250b08006601d1007044e03a00400d0f41c0c0301e000018264070b4403030708a0240001428940c6900d5080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 266240800 1250 266239550 266239573
    0x42306030f01090c0201110d05090f061005040b0a0e040b270309060d06050d0f0b0703020a050d380a0501020106083007060e070902091c06093302070c03110102 70
    0x11f50141040d003a491070041070300d00c3c01c2c100d441d007040c600c59500701603a84046d0034050400e02d41085523099440030341d8000f0703400610308005481d010855000c80040100c02041c4014080008015849402c042400074905044118111000c8480d2040c189070f03900140200c411a10f4220f00400301050741803000702d0201e4803040040c81510880074101d80300301b40261440204020741607001c0c0d002c08030341400c50074100400c50180507031040006507502280e460f0700c1c086502000340c040b04d900702254170b844e0908030081125056840c60903490b0501c0380d03c0e20540001c40350310500601c41694048806000310317040743c1440403140c41440c1500040b03d06180981c0404d2000c0d41d0140001d40d00803a404240c0101d062a05407c00081d50000c0650700d0040000c1c0040d91079085660140d5968282480c20400c10b42c14103500402481c03c004280c4c4550384802c40100303070300101e50b050140c4c0840310340852080c00340c00d01c42284200780c03004201e080031040030000704400d200d01e03544003201801a5a940c0001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 266242050 1250 266240800 266240831
    0x10e062a030309060106121b0507170d0c230f030c1c050411120309060a0918020403023c0612090304080d05040f0b1b03042306030f01090c0201 63
    0x3c940c600200d80c40130b00100075803640401160f101c4440e9403800c0050084407014004684004101441400742c0003842104020005400048100036499840c9d290180f1080200140c1040c411110000315280c801c69080d68003030480600e001e8010218034501640701340440d4aa4000406400c01040148400000c20020841d0717031580916040780001e40c1c1c509894810040a0a01095405000401051852740d0000400c0760000704088130341c1500c0342d03a44881160398101c5908841c003154010342d000d41e2101c40b10b40203441544c0c400c503500312400c640084440f48442e08904800d0301031080b554090141c40e140d0311305081d1080d028160515000c40c54061070310040060342c0c1e01009500010b8200000d441c144120300741052030340742c26480c1500d00600a00e003054940a0007502200010300c19041c1c101d00110f06a00b08201c0342666121951a00350382800c0b40d0f544c1405490130401003800100d80340444c101c038800c0e0b04500050916134280b691b51002003034250781d10070941d135907806440b228104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 266243300 1250 266242050 266242057
    0xf01020f01090c0e0c0702010e0108060d0c0b1207020f10090309090203040c0305010c020a02030c09070c0506010e0f0c0f0a0806011b0507170d1b0203030d1b020c010e062a03 76
    0x44030501400c92404010711841c4c8001012040c6003041480003400503a4081c203a448699000d01e4081200d0322040000f41b8401c01160000b0991210160300194032080e00c0050614209840301840c8641d0350305506a0311555110340840039900070b0644d60140000c3c980c4421800e0f8001c1c41c00c0a800c54135200c001041f6841a038040d5084a41050b003001000424012000c10241c10300c040c020381d001c80d0713000c29903508006c0e029500c500800f10000300703428450160404034036000000c0301c0140d60358a407040c11010080e20a482041a000f000808480e1000e040350162042400e038580303000c24103602100c0b80c6d00003a0801d4100901b100310b000400c0d18121080d08100d0050000d0101240b0708210006069160300300501d2580103400015070b02600180d801c500e215030303420942440089880028114800c00d030594414524000a81c01050030b108110581c0031941d800301c07079a10303aa107001920f2104c90003d01030340c0400208481e64910900d070740c400c3d01d41d6100c04440fa14006800344160304581 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 266244550 1250 266243300 266243303
    0x70c15050f030f1506091c062703020d0c08090d3314040c030f0602090613050306060f0a06120608030712080703060e0103030e1c0507050f04020c0c0f01020f0109 71
    0x80c3e0110910801c10a4254150740c40a01103a540707143c0b01140740401c0401c000541c900c1590400030400d6402d00103250000000000519100c4181e0704c1802c83e988540b0032528010f07030040c81b0390154140428050441e29003420f41240040d070410002908212004121540849001c1000038440520302483d0130a80d14910070015400c0c2c100404200d080c0403170b421150600c01c180000b0042c80080b8203100010300590360803400300500c110560409401920498607a90b40000c00000c40c80355164946030640281d1718100d0035107819440d25410444018a600340c1c159028003c10020890217000388004103000c0c8035507a001c9807031680c582d2070a0954100c2c04c070aaa00e4103091590800c4103031b10010311a400b9030749040c00c0000c141000304502135000140001414008000750007000c9940e0303640d000c0c0228862104002c0010309616119489809510841d0701aa45050040035145402e009442c9201500c400a040701002007007003104c4000c4281d2504d056005039008980000c1e428000c8039645d9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 266245800 1250 266244550 266244571
    0x4061a030d110d02150406151d0a06080a02090a0c0905090103080703020105090303070f301409030c03070b061c0b070e0609032a04150801050c070c15050f03 69
    0x2d8074502d542034248140360103c0402c40d007041661809074090590a140c03c2904001e0000d2041409480e0250051642e04050007032202195015410411040c1a9108645060b020302405a8a0105d580d0303130760a00c00700951242d0343e280050391a8040d988851081500c03864032110003035070f803004990b00d0182a0801d90710041c00289070390605409004850700056000015451480c00110007800e450b031b400411000c000f600043d2245084c1e11070320510101200c0f03921180141c1c0c0c100500070082c041800c842c00d81591890018481c2e0300040180d07009103850700091840c2140a0341da1480c004070041130180d0101610b600850036894019045848900c9519a4a403504210101038239040d01c0c070641c1e80c8a03034020081c0c3c00740f680340410805204481e4003c400c10520000258007551215040003a070818078101c2c1718a4643c0c015203184003118a98002085692290480480c4900c00c03000040c0154440340c0c42004020000608516210000e2904a0402d1451400d005041d402a110060791 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 266247050 1250 266245800 266245817
    0x1912030503040b0f090706031a0402212409102105060105090403211b030603150605060906030903090a0f03110405010e0615070203011b090806040203030304061a030d 73
    0x100034000d0401e6130403100b40101d120040c40c000c20b00380c0e520b0300d860080c0e904154a07440c4400e13015440c803042c8125507c00401c2951600c3c0d080380c0a0314113035420f440c40c01c00700c103801c00410056040003488650041c080d03041080103c0c49941030016074403020300007250400e150303400000c0c650580b40001184200c3e2540380f200300c8440d03041040c40c107501a0002407017a00b034002840700194120300403462002c2d1200601424018040da588000c10590030071078129020020040110340c0c0c598008404d85c0e00c80c2e8417030b2188018510710581140c000e0300600c0d42000c0e0802601500340341442c06103a2280ca2042280d02e071800c85004104401c0301c2e580308465102400c4000c0c42040080009a01c100c44155020400303580742c000380d0b45801e14040d102c940a106800d2030f81800c821003008403402150080d00a000300130740004070703030b40c00210711407803a00181610070003044041011800c1405150014015402d41e00c95490f07400040a110b20541e0494510203800c0416460900a90000b42825100c0303109 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 266248300 1250 266247050 266247053
    0x9100f060f0831030206090f06132a08010b130504050d140c0106140126071404181e06060903080c0102040f090902010207091406191203050304 63
    0x6002006800ca503040c000c000e0700c10010554446582d0381d00080c9040c0c100000c4203c0d41c40f06150b4031a42208070081e080708070460044c503030001084c0c1e004c0d64000003205e541d401c4041032140c9540055503520780395682100344601040080400861030149012041201e12100c0220345081041d544014582c0c1d44402c00e0036010f1902c144a0000440026003d100c40d281075569191650280e0096105203c1d0352000e0061600c00c1c101681e481d24441c800801c07009849181171040650125985800030f4482c00444d0122019500180c1134103540071105802901c900009840000340e140c803c400c4c12006000008040e075246c0740340e405a082401c0c0000c0c000d400c0301e04110707100141e1200800d98070304114040000590210010044a400c04281500c422a891a07140684501d40c840034405160b0100840c1c040415400080d1343d078808d80894a04580d521440f005594403d41001e220a43c04d4000400c903060120510f1000d000c40420204090b480300c603004214040d070541507002440202c2040b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 266249550 1250 266248300 266248319
    0x408030d09260d1505040c1205070c05030304031b1a0412110705060d0b030703030207080d0305010e01170c030609100605190512030918070f0e101107050910 69
    0x88102e031140c00040038210940e00c400c1c1d0b48600b00b10300c841c0380e0307039003403050035040c44a08802d000d024000c00602a500d00604003c0000142c0c0d58920f0078549043c01091020b8003a412040100c0d6201d0090b508503600c0361010b885c203031122096202000b00070750300f80c40020030248000440c20520b104030342e8242414104000703100c440101c0a814040075000214804100182142c00c8400132139007a951002ca1400c4c5001030180e10120f50342500c84d829010007016000308180d4180c2d88180d0440d01050000101181541e000b03104a64440465000502007030013110311100c4810700c008119400c0b14000400b09103040e504440424064001461031341340204940075101c010032089a090603e074030040050511b0009134170500d84100c020300c400490583c01032054924010008113000602c1c1e62075034001d11341c5241140c0003400034080b81c82c00f0755014064400d40d4045e0001a000d082800c901038011b8600c501c41850088145c807410178002000c0d603640800c1c0b4468402c0c0e56841c0059454000001d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 266250800 1250 266249550 266249573
    0x14070605010806180705060a0306030c120b070516030e0d0c060906090f0e060108130606080109030f02030703080115111906060f0e0c030c0403050604200a0302090a020d020408030d09 80
    0x5203141c044062861342c10900c00a505403d9400440300d042c0c0e00d642c044030680007028241d100400d4585040300c0040d980c2c1e115011007102c6405491203210595604c4011507851141c4940a001001e802d080000441d00c100031114049001601c402c8110009131942c00c01040c5c00d0344501d00181007840c05020305507008550000501d2140d00340e002c51401c2c024156040c4000402143c1046150000102c0c18040d05c40e140c0522504484200b107020384900b149400f0b0042c200090703000c10315a01400b4040d40c800422035031203035015503902030f559003044240b05c0ba40a04002c0c1030100009a6840404c61806202c0101d081c8113061548211075401c0c58160240d41940d03000c18a0303400107c0c1c003041140b03054400280e10141904034103980c1e654000c4401d51a005a801c00360803440707100100320401410401055012240140c04040a0914410826070140d00c0c0802034200381400040380c105d1900e41c001d0684441840e40160815842c2c00c00301e80f846d0818960110065201c4a10700d043c4050900c80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 266252050 1250 266250800 266250811
    0x60d140603010c020a02030a0b060a0b04060e010f0e13051f0e041a04080406080601050f07030507020f030f070314032b0c0f0e19090606050909160804021014070605010806 75
    0x10b17010b018030980029444240c40b40014119007200c90001e0810359850200c00c000d020440036203070301c550719a00c005009902c8051424045650f403000e9001460043c041c070400c2d00760040052140914031004d010103048050b16010700c108140f00d00040390041684a50040c2c0500c1500d80c04a14240c00c2c41550403101c292803485100080040c0300100e400c060840342507881074106055141c07281130040300c90f0b2150a913000e0100001080160801d540308000b0804240203c94000039010b40400705612000310750048031072540700c18000c00000301000c0c0c920fa41c01400c84152801c010001c00350442c030f4030340303002c0c600044d0100d000c1c00c40702c3c5445442021624400f91800c01c11169a940016080d158040fa0091142000c0c0701004908900202400d024114010062082c1d035076408000d0311580080a20030701c42c03c072080010b0039180c10071350030382101c1c1d4a980e103181894883d03400b8400c1c000700701c2c0152030400c1030a401e01510311300d8180041138030b1845408002125032501c0c000c50305000000d0034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 266253300 1250 266252050 266252053
    0xa08010e090c010c0c09020d02030f1f18020d060801060812091809011d030307030c170103140f06040302030a0e010810031506081b0406052d060d140603010c02 70
    0x24840040300005540c82c03401c900382054440c8258a042031108080540c0c061690180001041150030300c0301d80256009480c4003180c408961100ca007084084840c03c0c41006848650300c504008442e068800582d140031200001440d0201104803401503900c02e80010b101c0340c3d1110700c00c0048001c1004209805030b0064400e03030421907040002081110004901c0403074203080c2021565541c42035114045a001701d05405019220703001e0f02907220340044460b000400d182141240e9018001c031071124540f040328012100c0c582c2141e5460328454024800417034140304040394010000ca0822049000c0ea011b600216120800104001d0100048408c00790400c407414040c40003845181d070841d01600c2e4403824140108613440402e100134940c65005407030610910240013140c162210303444128810540307040c010f8503100ca06115081400c9400d140c908100e001c0c00c08201d541c2c3d550100e1a100000b081d4034504400e0480d11001c1d2a40c00c05526081000c25090014503e405d00c01e540c0c00807403900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 266254550 1250 266253300 266253329
    0xa2c0c03061b03011406120a09020307080a0b0604020d021201080102070b061005180102011b05041d070504120f020907050306100905280e09070306060503070b1c060e09030a0801 78
    0xc1000400f400103100780201d5003004c004950007130341c400d01618003030340403410740000c14541800c8020280c0309100050780680205140403401480c08a4102c13082904100142425214107040c80002d610111081e1515071742401110000f03803103114814020b000d4040050303218000e5080c1010510307006000244500a610345154009802c2019a07094810354500310003441603000050b400350a01d150350203050611510030300ba6180d000f1000d80145c40c041e4100d071a40c1e1030324801600340500c1c169401e501242044c031080082001500102c07655501c105c1840595100f55400f0641020056442401180b004003c00000c2d013031800e0000700710465444c0070b01450f4588004030307100104c213850b12a59050620760100802c152019428014619400798100e14505110925128803aa0000301c1c2d259040c00d50000d400e20b000641c11090301e043c1d0004a00d007802c1588098011000c20f0503248510f600c810000400c9885400111f200310308000c00303980c1e2058001401071155105030081c021140300d41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 266255800 1250 266254550 266254591
    0x507020f040506040e031306030b1c0f031205010e0402190509070507081b03030402180c09010c03110708071716090b0a1211040b180a2c0c0306 63
    0x450403104028015207000520340c0702c2c0300201c1c014006030701c059406440001410418498001c1041c411030720150f4040100c00040f100300940241d20884c800b04c2c44181e0701e480b0001c2206445d1900310141301e41041c10fa0b00f50454042c100745e8409034005007184088508010950410406000b0740c0d4480d004940c4880303060000040300303d100506010308001c3d02142c642c0400c004081100c400e680c04c3c000d401c19817050014040e80da0742c01207a00300c0c0120281c0c00741d6440d81c80800303d03c5000b0107503003458500b881c68286c011a8035462001040d0100464216042d06106003442000c001d09117100103000842d00b8900c80610b4115944c0e20005164404040e1160100135401d146003170700c510300d00224050980723400283c0b0070b98642e0800c00100d44080b500c00100440130010500b240310907281413106078005c00403c4166242c6a13a940c40c0000010700283d032030310342507002180c020341042919003504070311065400303001e0303a0b0510704080e640143c1c01c01c0e80500c0d080000642c0004a04417010408129 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 266257050 1250 266255800 266255809
    0x160c12110603090d1409060301030b011e061209062301060906020706090b0a030908030c041d01060206060409020109080d030917070c1514030405030d11090105040e0903070f0c080d050702 82
    0x40c80c9401c0108952017001c1c4544103428412200c440600615180d05c1c2d50b10707030419144410080c0301e00702c02e00c0910540780c0b0001d042054940100e81441d200c800702904000c05d900c1c00740c005100c044071000d0340da00740c4d000c460194110101000400200300c524543c100b040150882c429600038009541c8030890800003c2e600c0380c2028107942d52010050785800b0594010340140c030820303200505a032000f20400c1508007484024004a444080c085480c0902039010340c0000c04082c000c100060300f100c00000d142c1e0078240c004059440c0b040c540b480c42103581c6c00f1500e0a0a0040c2c82d020f0011fa16103082e007051000d00c031261501c1200b525030362031a001007540e80494000d030500c42c019615603007503e0151001e000d01c4c407280c4a805840a030503560700e0035280c0507440341e0019021501c440d00e000401e880103421039041e60f21000301038540e1840d090629140215464006001010718801007083c103000601425104d40d50b039214005d482421030030001140e0800102e40b41c1281041020320088000d0b0340c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 266258300 1250 266257050 266257063
    0xc170a23120907150e0301020409020f1905070c06111204090c0801090506010905011d06031008160302090c0705030d1505010917030a05030601031b08160306030c0506160c1211060309 80
    0xc1810180100017442c40400e01a0080b80d00c903101651020503000e41c4414504010081d000e07075011490131429803a607003582c090050a601a0421001203000c0c80494000c103120b86400c0d20150031102c41c02903c0301d1502d100d07072098000820b4262680244104150000c1e4124058660124180590b10b040b05c0004c1100a46110711410008c1044001da00301c51005203803030198002500180ea28070705003da00550003c3d070311812502c0c1c8102d01d0096614054560007205895005042c140b0740c0d100c030700705a4a60f07002004141c0b11070108000030391000350648609910707481400d105100c114940000540602c80c50751195400c1d4080c401c0500c081c0a0110484480074000d04107140caa80b19040100c005220306003100984a940c0001c0030859904418064411a41c03820b1950b041c0b110030a00300c0c182c50040c4002003c000c1c480c1310500c0310f440e164001c2e200c505142414081920a15200d4041151607035001400d204990780844050001e85000690700d443c0540e03000385103081c010665681d841 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 266259550 1250 266258300 266258339
    0xc0e03120a03110408060103051501150f050c0304091401030b06030303040f061d0d0306170d1209050102070233091e0310060e090d0c170a23120907 65
    0x159034200c0a1024410f40098034003174030460045403a2581c4902e0890303602d07200c1e2009520076034892000014500c40010800c8600d0003507036140203a4813843c910507151908a0074042c0caa6020900000c9000000343c03007502c0640c04500d1440c00c055165003829180040c02501300c501a4204004010204180c0040302d29800d80c84140001e9903043c012f0f8402c60000300d001c9100681c094900340b041041d52580051044d200765100328031440f040106032982c2c900b80e003d20f4501040e402e110352022403400782d00c2210721602070701c00035151004550001d4851403040d4071601e00b11140d46500e0746080680001b20180000001e200f0740340c030000301e00217640c980114810582e4120644082000c030740f0103020040903004980418010607450b000415444007045824105600c610314111843d02d1055846006150308022540c12141c0c481c0d0030075040e80c1c40b10400c90240000d0001c1d20000d80b54070007803003400742820308000392511107841c0c0300019454060131265165100c00c0d000d00010820040405800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 266260800 1250 266259550 266259557
    0xc090c09060904050702030c1c020c09100906031b1505070b060325030b0c0933120103031701031e02010e120d09170c10030e0a03030c0e03120a 63
    0xc041038400141a881210b05003034220b401e0006000607282c001004d040c0034034056064480c0075403884030204145150761940c00042e0300c05511041f80781440700049420142592200c40c0c01a180c0d13101c10141d4041c1c1d8000c503001c1e003100541c0600c1030141a401d0000e03000441000c102240d481400400601a5450150908510300701054160754204903940da150441c1501a030b0156072540341101a001601c4255281c0705190006044400f100b4110785200300018201c108000300c018030b40640210030151402c03901c03100040480350300a01c0c0c02820610300d80c1d0082c1105503040d458020403d5510810600782d06008400501c002003121002c060440e581914111001c21203000403941c1031105000582c02404204003038455141c0403400034004201511032202c01980d4490042003160801d440c03803040d4000303400c51005490001905404401c1920b408100414039004c05030030a80b0030503003100880c0e40c0300100300803580c0156400c80034910482c05000b18030744071101c5800301d1043d03150517002c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 266262050 1250 266260800 266260807
    0x7020d030906080c04180c0e09101503022a0a080313060e031303060209061201080a120c0302030a0c020d060203090c0319170a050c1006051806030d0e220506040b01020c090c 76
    0x4491158030000e0287e00009c0078101141043d8030101401003e5000d011058483e0a40340394044d402030003140d156410740c85141c55001820140c002e51440411038801503401507501c14404210803902441c026141d04005c1040da031041c0c40d000080301d11003e03910ac9513400920100440980c0860719000300d941100c005071340c80f0500f80011b00241310f8100c5000d100300d040350001c10300300c4001511143c07a61140307010440100900030f0541e24420842ca000300164400c00c16180e2080c45101007041f02d62001d06920b022103c2540d42200740d800454100290b0360024182c1c002d1803404000b403c0ca072400281c86403003685213540b982000304030041480d0f08051800920042d403e8419800c96800e1456a0f00b918003004020031420013401291040718400c0355020461640039415a10f55805a80000c00510040301d1403403003034a1000440c1c0320b5540c08001d07903104201d1346052910042205210030300000d014589502000201c406c03034070b070290456004041a020382c5d103410200940100c1703055402d0b600d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 266263300 1250 266262050 266262071
    0xe010605030f010905060903030c03010902070204060b120a1b230403020a0f030501061a0a0f0215130302240118090c03060603150b060405010c02040207020d030906080c0418 76
    0x140925500c240e80510a25001020300c10065001c1345040d441038060320020745502c241d4581d680816503d82681c220200700400064082d0b03801864514805480802c140b5603951032610a40c1020040034038001110381040324040044c803880350601300900204014522203200100032203540451070a6854a4070354941c003060405003520021640108140010b54545c591151840a1403004664641c01c003040480c00e006580c0380a980800a0301c01d840c24000400030403106079003c0c000040642c082d40d8400c05401e02984003252242040c8810354001c40e030781d451b000789013440c20741c0450420042c0401007818014090a568112442c003080f409210807488528401410170000c01441422818000001c10582e6001481200c1c01000da11515280301c0d0f1500c030503589440d080c240d1148082005000a6015030711440c030b042c0c0040d00050501c042680404ca400444000039808612402001c20410340d000d10030b50380c00610801001c1c1841d1070314a950315000324030002c04400686461150f203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 266264550 1250 266263300 266263303
    0x30f0612070b390c011115040602130905010b07110103090f050c0117091005040302030c03031609050d0b0402060a030207080409050609130b010510140a030501080c0a06121d10050a1416030e 83
    0x111f1b0a160101d0640c58101131078020300a50001c20401c088a0f0383c8540000c078804a881402e049841085030309160450641d94650300c000600f4200b818955100c06000c00328184c1000a460346100340d0081805142d42c0740058002110441102025a0350f4003c1000940d00030603101c03c01341c400d100208ac1b9480d94542a801d50140c10000c1c40c0c0f034803000c801c001e04010070410800172a44261129080591281c1c18410301c0002d404002e000b20302420041001401d00d100144500c05191500500f40501582da20703510381e0041c2e100c034400d84c2d1140107210710740c81e0078900c507900046588034410a1101030b030f444641f55581441024800c1e9102e44010350001d01442c0d180386003650341d0220385d80c0d411080c40050001c000a004a2065120b807641da1b01e080d0510141b0312080c2d41c02625009404440c0c20031803000f501000181a802c0c801e04144060288030802103908025110803000c80c4a1420450103000c5032411034964054041000074000200070410350380c2904801864041420342c00008802e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 266265800 1250 266264550 266264563
    0x140f1002071d06040b060c0318121204080d111504150c020a12050c030f160602030403091806120201051305030d110111030f0612070b390c0111 63
    0x460502c1e14081024100c100c12103510340c0b16500c00c030343c2004010403100500c54580645040c0c00640d0b0b004100c540c0e203804d180b11015868580040540741e005c00000780039070400c01c081112030800070011a05103c4102c080c040c8000240700b070f107000d00010200410540d81e41d0a000000c0954201d00b4003c1070600050009011041d6a00da030184440180c481e80290380700703103424007564181207948105e160548594200d6040c0d259140c011401c04440c0080e080c611303401009131035040c480345441440001c00d1800650300c602d02a8466070b04441c5022078429945d008491030001261524001344109040e403691600b1840d0213107482d40d01d444d00c025580c4410355864010301e606210b0407000803041d950020090148a00d91f00003440847e0303881d0450045070209480341c03000941148009050703402d00e0302070782919000b41401c441116603a40c02800003640841c00d0360134154450355418514502d0741416210760702d07603440003104800700d4900303094482c1c17000038845040140804107000015400c03c070300d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 266267050 1250 266265800 266265809
    0x804031407080d0509010b090a0c0e09090d021c0813241b0c0b060607030212030a06060e0102060613020c07050418060c08090705040504081603090f140f100207 70
    0x403039a0361103608100380302c0e41050b1019580c5606203000185c0e03909040c02005501030016007244c0e999280d5502410161444609070410080d00d0b024000880c0e503402c10090040d00020003608441c026910000c3c240105c050100f000c1e00700b040403120207198001c900650114600700b07030604921181c506060442d60440c0c0045180c000050070201041d8154842181d10400308078400c2c05110703104064803181d10f0488082c020150309000103040d802c102c4018400c0310721a2041d45c01c01000c00c0b04514094009656829003965514000d0004a8100c40305100046003400200840e207071000c0010750641c0b003042005459078002c0765844401004210060140c90b0007401801440004104501c4248102c40c007640e2907800c0c16682e502244c00b4074040c07801034000e407014080050070701d4180000307003e02510403600244100b240a00100e103203007940d00c84911954038583c0c0c142c0f600840f40040310150b0008070510000c5078454840d0390715580160036420058030f844880300b030309120690802074207611 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 266268300 1250 266267050 266267087
    0x130801090501140a0603020303030412020f030301060f0206010e0f0a150b0d0b180103020a060305130b070c0201030f060819080702091314060408030c0c010605120a05010501090c0c03080403 83
    0x4588003040019006050100343d90071155890b0340d540c80d03890099524520020303405810800100e0045024840c0800c5208070900480340d050034060b0a107441c541c00ad078070010025024100740c03441e007a814841c40d03005000c54000d051140c10320300d407580c3d4001c4002e4008464159203100003446020302c15003500040140c1d02241d41c50b0502450804c010b09000414180f140b010801150b003036403d00b019480c142c82c0c000e420311012504140c1e00350010840a000e589034a03407c403051400244400cd00706106540f19a5080c03405240307171001409070b8158802d824035903404c00b5024000c17048009100960308a0f09524880b980c909800c03c0c10b0180300720320f0080d4002009a04112101866000308203c40c0c0c8144e03801280302c030000d55500e45440c01a500280440f00400106103010600009481031344080c070000190550f4840000744000c080d05c4048400e50484c85800d800c3c04400e210745030040889079028007049441c01001401414580c200400380030301309001c01c2c00c0c54810305030341401c4003d100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 266269550 1250 266268300 266268311
    0x50a080a0906030605030a0f120306050402040b071407030308070c03050d050c0c16180509030904060603050a0b030109050a0605090f03070807420905010f050105040c09080a08130801 80
    0x210062400c0007078020720010134108900003e85050000d00d1209090b040303080b00c024038001c0c3c3c0d14811111a03d003003000c20075840d02400715003a44c8500c000e00c010048000e50701d40c0c9005a240401c94041084145007168016034420404a600200c43c298860000c1c5400e0303515001d00c2c40d094071280034148001104518010800c01e05000000080c00e01f407907088201c0c0c400c00e1364207809000300c7d031a5006902c80e84404c0c11058481510340e4100d2600031103100181da0501c006940840d0446810741e0000e0002a02ca01c103002c44d4124902c260307408948160001d1000306419219070707545403043c40f402040150b48100042030b000d001d00246151480303040c1900c0e521200e0b4100010036400000044c0c89503007102412481480e000c00400050b02c14950703044490307447c02300382c074480190038040c0c0c03990722500c4981c0080081c000384251000c8290038000065154105411b120031907017024594800d000c90f15406121814000406061899000c101c0c5565901461601030021041d42e01030303000f960070304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 266270800 1250 266269550 266269567
    0xc1011060414032217160509070e031903030b1507020d02010c021018090605010f120e0703060e061e160e06030c0a141801030504060b06031f0e15010c050a08 69
    0x8041c5901710703510007003038400100e20010100d445002c500d40040f2410a4410108030074144642410381c0040142821003503444003501081c01c040840d9001c02e02c131051000218101a0180300c0d44e4201402a9030b04142c0034100e1041048503c00d420020744100200ca09240031a03100300c41102c107099000d0020b00303000500f04005460070143c0042c3c42504500310101140f6844c47d88a480c040b610141c1d10940203101c40c41e019900181c2485c020401d00ea103441c0e141841b031a08026450046226000c00100e0a00c00c007001410403a01a1200c80210755640100c51100303070055901da084103030888410a4031042d9401564000d22694031b0075040000482080011407030342015040501090302e07026042400d5000000142c4a04095181c24117244d01c6090107552185d8015688203100380300c00259400c0c0d000000e075060f00100c0da1103002400c402c8102c2043d4804030303900f0008103031107000e120b0541010440da807051403001407d5170402034800100c2041c01820001c2001284c1c12045280d03a50000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 266272050 1250 266270800 266270857
    0x50f0703050d030c1b05011b0e01030608160b0c07030c0909150606080109110904060803090a08030306061615051006021513030e060c0304080c101106041403 69
    0x1a2109441c140510845400041d009000b8443d041c3c0c0c10342e0380e00300035500d8a1054409135044070340995056683d0f91191810241c0c40391600b0b03480c006a100c90203c0c900e920001810f4840303030b030072210098010300344201588011241031002e45030303c11000b44c0c0302c60381003161524140302548081c184184c03e00c2c00060040720b550160101d207010f071694055400d41700720070600391038003031003250006183c1c60700400c0780c405164005e60a443c00c0640130740c64012241e00250a6034903030340005003a50030018900c000f030310308052144000c0225401960071441c4c440d00180c1303140100d00c000c40404009100300010001250310a001d03412420000704070a0400040418406810b801a200544910100e141610460b2100c40d1721443d9100030103075517801556000c0382e12013882d488040d00103000b80807900e22507030140080d00c00380900c0401003034071045000c20401810790003074aa100344141030b10450084000898000c1c3e206d40c001110764801025540300d5482c51151004005c0c08912620f540c0342c0e030084 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 266273300 1250 266272050 266272063
    0x717010609050a150206070807020c0306010b0c160b040302010e040204031a010812071e020315070512060105180405041e050a0501061509030b09070909030206240a090203060d050f 79
    0x14143c501040036603c82c40c02000d50304440c1c000d07001603400300000850352403181e40226800400c8c0e1054402c541031a40c0828940002032704280605100400c1d08071680508201c81801100300c0c0703542e40700030342c030344140c1d103c2500c544d0001a04115903101078801503183ca4046034020750b80710f694401104600060400080780c28040d0701990701481c0910340c0f043c00d130542907603441500b0401600041c9801d603003041d900348603201c003244c150054a1620411101c500d0003240f16946585070103a60704944400d080d0071010040215050040a118070000d8691806e0803103440103040d50000b42a4407941010781540006600c411900e00da80100a4104540851010b50061164000b4007030b540e1543e1000e242e140f4981c200c00e00148007440c0c1080030401410351180c01007140c00036248525112100503090301c808400a40240e40b04806010038401e02401c3d0f01e00d030134256241031100c07940c80e000183d9040114031518813401c0e00400400e2440d901ca580c40d003012a17011040f40d1444402e181a03903106d10303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 266274550 1250 266273300 266273309
    0x170a0215090d120204230a0308031608090a08030a050411091f12020d15020c011104031101020c1315080321010b0c030307050703030b3a050d03050717010609 69
    0xc401c51110380c800c0c3c0203070084e5025a030200081c12072400c07110b06c91509200c1d001c82d40c140d106014240000208070a50700560044802e041c2c0c0000d0705254000c06064408043c100011a0744101295800f140c1d84038240e0f508106140d6011a99894074207114406181031000243c1c40040b0405009245080c02102404c1407603407007500718466a103225001d05070301c00c804080d4011288070305c83c0000403101584c45441c22105c176401410149000d079500c0c2182c44068114405000005d030502c1130018107108406400c00c0dd00c010302560225101144a5804504408145984504c4c80040c80940f401080029282100841380c03504a600f100380c1c81d1a85413031030007080740b0060001143c1c1c0c0c40b15000302d03017015a43d50011869074444180841c0c269106039401d0f4200355984201034a076a54842060015101c0f1114075000350604940801002510468420200d52400101e00c0080c070b01050300e03c21040e25042c002116030b60510243c6480c00c0711741c0c4c1008524032035000420450b03003100b110703002c3c1c9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 266275800 1250 266274550 266274557
    0x80705010f02010b0307090b01050c070609030b0105040507022503050a05060f34030f021803010b030307051c0c1b1503020c0316140a0f0b07030603170a0215090d 71
    0x10785640c00d900300c880c810009030301604148014000860940c00140803000185085031400c0c1c0d601586a00b032035619000b00e0b0010b5480c100c20414001c460881601401088400700880e050400c0e000e56038a0403034111b004440003c001d000304c00140192080010740d004015140aca400754a07103507440d030328212240da01800c0c010000c1243c00c45402c084808074544c0d0120711800c40f02b48014100d14000aa2034503080540f503001e2502c0039480e600280181080a001c8035400d40905402c150a45c3c50038038025020b9441405a400400c0c0001038144010043c020100b20502d0f42040848200303c40c41400350600c4043c0c1ea6446190750b00b01c00036011900040d0f681c4207040000503084050780324502c0410210341c014401c5018555410120043e51486644403242020003910154181030300c09806603a9031403901152014808a88242b0380e12070282d2030104180c9086584112464810200d003804c450400b003880e4400c607000f007142040000202d509000a450120b0f1650f82e10314140701100c001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 266277050 1250 266275800 266275817
    0x120604050112050a0312020d0e01330311030f030f07050c030703021003051f09020418050c03040339121e050708070b01030503040e130b04170c010608070501 69
    0x415950002c51000203610001030310300ca00640d1412641505906952414658200491000c0c900903208845e070300e01d544000810300710302071140321140e001101d28110154003030a07900d00c14222041810b0040e01e500c0401c0b0034034140020702084c54130038280028201403000141d41c000701c0d10790001401015104104807016a03c27035506150b281c0b030640c40025003001c40c00900303041980c0250000755029821810501c0d4040240c40d180c16041040d40c02020710b640d000070300740405100501514907081c0c0000c428070442c00c00a102600030b1100800181c10494400d01d003034850310207241000c4984243c404028100c0da14000001c944001040013212214031441d2480c0856015105180000425450b06020b8411611b020741c0c242d03101100455a07040c0c1084081c00040080d007416020314000d04c0210b07159410710343d0020170a00041c00460784958801c00c0e5000080020b203d907644140e02c0314194416190303030000b02c1490701880781c0055076542433a1012654600001c0c07001c0c00c6820990742c90740c6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 266278300 1250 266277050 266277059
    0x20909030a02100b030f0a0c14010306180b180f071d030606011b0f08040503060106020a2f100c06050601030c0804080a0203040e0718093e1206040501 66
    0x3580d20403408001c001d40c1014640790301282c1c07039a1042034a200082d095802d044004505941030040d1954103d8a144504c6024008030040c0307480d456040c8800e0070200986400c1a402840000a180e9000c103469154112618103840d060300d24004d0706210b0410b40c0f19424800e003508101c0c070040741c100340003c1890102d102e030300f0007015464142c1030010340908000c2e1200d07801141c0000c001c003100040b1701110741c4c902000941c034100160080340101076041d00d4506060415042c0768060780041c0c21035120003034003808111030b00025000c0208409180444901d1081c5c2d48198270000070040354400800c803101581d240e04010703800d151902c980c4003000b00741d50701c2005404035080420b44000107812440000d0020b404c3c10001c000d0800e030303401201d082c141e6454001e007200c0e0b022580c40340002c0d034000d05c503440054500400b0000c0e12580c00b050041651041443c45071068004c8414042d5810110020380c00c112003084116541c82000141d5072803056102c2c00310034110503900760b4081c0e03240000000c0d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 266279550 1250 266278300 266278303
    0x105130618061a1c0c09080307080c06010806010e01151e020105040c090e0a03030203040f020a03050d0f0503070807051606050109150504060506040b0d0f060315141006050c03041208030103020909 86
    0x16155000b82c0c640060075145292004c0041c0054100c42c03042c0300340700102040c0c1003002c002a00c2d91610032180f280e036480c5403042c46400c0c09010383c05035400340e12110060045030b8180c4015410743e41003491196620a6822040b10b1052140050326600403441c0f503c01020359064100e640310300d00580c80c20081c40d90b0380c8050404c5861110b0100c81a40110080d04000380c030a800035901719014540c00c124072442c80e00002c00100c0c642c1d0044681d540320b9413800b2059a0000310f000240c00c1e8500b059821858880405081060010984800c0043c00078044001c1c1c680c140302c142649820100401841d80c450081d140280005100d202c100c0160b040005501d207020b003e150300b900e03c09800c02d402c040c6051000740c5940c204545123000da940b1a400c420149800f4071803007000714000c105c045102032118101030100d031910814000c419070301e6400c00820300e4286083c6c00840b641d0b03140c1aa40da0b9090700341d01c0c0c00c60095411401b042d044103178900042c8028840a14160b90013180d0381901c0d521510000c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 266280800 1250 266279550 266279557
    0x50a03090209160806190501050c100f02030421020c0f13060807050a05031c031d060405060f0a05060901171014100f030f0206030c1605010507120905060105130618061a 74
    0x1006d05404c80109002c2d5511400107410140e244d28121080c000c0b03101e10403803e64080a2005407010317408030800080c042c1c80100080c4a410a4049840d5550780f114020f444a24603070013035000e91819281d6101585443e040f038000748011583c20084aa00e90031400c0d100c441c00c1c07065510400d000c20000c07466180201d208a1030b01440010403070144000b450a501405e202c0401d0102030940e240d4021041500f400418401ea204001500461902642074403147d08040e0100d20384c2e41c07901c0d080100d00e45074180007078192000d80c1100b8003c0003080c0380440c6841e0b01c19002102860800038912840c1d152020a00e000e10720200d121803103a912410004241c005610000c5c202c2d102401c0c8000140c20603070700640d004440304403002c3c5009211403e00003108841102203034140e64440400202e1039005400c110034440000051000580c00c2c4c4a441d40d803081800340500c12070345001100b007903001a6000100030128403d442403240403000308040140f80d9440f589014a400c5109510b214042c4c9044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 266282050 1250 266280800 266280829
    0x1309090507090c020c240c0a03180905060f040e0309060412260a03020d0b0a1e0f08031b0c090f10060915050c0c0603010b0403060f0c0f050a03090209160806 69
    0x1042e01c10302c030b8591092440c0c402c003803501c1d078042004202c140d04822300424840902a45402c1a0880e00400380c1c0c055034100c0d8007400e410b52034442440714070390310181e0b40104d046044602203501c40092100c5800c511520801d01d500c0030780010000351007500070140c4a0701900907007203600500a89612030045070701300c14140020f942c0810040c1c5505004c0d5000e0003d0380c4002d0710008820840350080b0b1401c06071500400740705151070f43e800700800d240000240141500384002503802e440c2c024000e80d00c0c0100740403044140c07100070030040111020440d41250107001411031002c1d00b800c2140c00c603002015152000e039540c0f44080031038964000d113000401c40c1c0c40d45501400c5040840c104a03041e412000045d4001d00a0316804030b003ea0311080918040c003a0f4845d0305036a5403841c50300c0c008541e504503003268428100242c1000e110340010b0540320b40001414001d50b54245110124000c0c0348104009512120b08014040e46150040f00c50740700314181e450321720303a0b5203c8108204100c40f841c00c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 266283300 1250 266282050 266282059
    0x10b09040b070c1506030b06030d11060a020d0905010504080c0f0609060105151c05090705040b06030c0309070e04111804020f1e090a0917040e06061309090507090c020c 74
    0x205507640e1040f1000310b075040c069000c81041c24082565541a20640d510039100740c51039005204403480d041c03000a404441c0c50030081044102032240380d8940000030000548a51f0200380300696142d10b030070214003954040020000791400346010319180e0401c0c40c04103414442c14140c0d040c507030000615903004d2044d810041c09240c1c0313030600708040140040ba4824401c50103020803811502c909d0038015000c00081404030342841c4c9420006e10781001684060300c2942800316060710740e00d07a04126900207014000b510f54a070b8901481c07070320302401548100600100711080105201900558441c3c0f483d045071205028004032000350b03009142030f100a5807050081c41e80b114545809202220007030f0941004514600340c181c0040c80c001c0e412149240c040c0d4a41401000b04800c2044512500318001030280c2400e09107410103000324002130070b06019104c000b0b00b588612550350301c1c00004040e090024000c0c10403070300c3e103192290418811038109504250351200010300102d020ad1004030301a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 266284550 1250 266283300 266283323
    0x30501050129030c09060a02060105010e04270c05060a05030604050609041109040201031503080301030c06210e030d090317310c0b0a080103110303190f02150a0e010b0904 75
    0x40c100e255640f002d000407004040402c02c0325a01e4441c28003611340c40300190050420f40d81341c40f0000d892140604882c502c01c82c9420034010310101c4041510850f0002413003400072040103841c2071401c000b2541c101a0b408003002c20041d045a600130015449080151420701c0700f0b84521013407080154007610001c00800e144130b510046410100f0905a10900500d00895054501312a80d0180d0360301d0f41095070112000001881030101c001035200050207903140c044020a41a42c1c03170480d80400f42010319005032207d0806d180c2400800030348200c00035240d020400c1c000c1c41d24010707101544650b15042c40c0c0345540e0001f2034103035030244e802170340852078241051035074030450b02c18022505402c01110b4a0085c0d071008074403400c03800c01420340700c4902d40b102242c550540c20b01c0d1301c84010410110344664010040001c9001884d02c0240c00c075503190601541c1d402003514181e041c640390410200b00d01500700200300c002e9400b900842041d40f113010003000700c0c1034904248400d054040314043c182e4001135 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 266285800 1250 266284550 266284619
    0x703020f0d060b1306060212030108071701060308040609090b040504030503071202040e011d01120f0314120a150506280210020310050405070507020a0311150d060305010501 76
    0x20019072200c24401c0d140011803034140d00003d168814408070300c5030070a0f0754420600542d80c040103c40710305400010003508646c54440515542d080074050030030f0410180344041c1c01040709400400c05150300c0303140d01b511541c0b01d00c0c0c01024000c2c248943d48a0a0804c0c40c01980ca00b0148600c60041c1d405540e81895559042c40503210681d580d00003104107913080000148650b140c02e0710502a00000f054402c80100151100c0c160234010303040380024141d034020840010340382c0440300840c0f59040c01c14164481400300800b5880c0a0007014519900c40c0c0c078200251945583c1c031000c20304000010281e40b20743c0345c605000240c014111407202d04240d00b000c2d503505840c42010600801c10910460b182c2d04082c01c041001da8100b40c2d800e0603098640d00c004d0040b440c0c180a036513400304941c40e0244c05c0c15410340028050403031074807000d01106500d044204090710f0f5640b9440c00604210386081c0d48144040001c4000e00d840d2006681551806001082d81c03d505000005514405c0108038503002e141f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 266287050 1250 266285800 266285809
    0x4051002030c090d05010b01170f0a0b0406050405100501030608010b060906090409150e06060405041e0c05060403030504081204050604181d032a030a0c0f240b01020703020f 76
    0xb40c03240104410500078000e0710350b03401d500d00c0e80040c4a8000402c00245ca2400505020540f13040101c04056240400542c4540412180c0e445a1156004108880c201300401c004040d2600308580040c200030800c945480702a40700021164203903000c01415603105440340c01c9407040c9214940c41001005180c030039160040141a0303141c002072002074460020750b0b0304116030301c40418910403581c4a5841c0b08060b4001e010b6294000c00a89062149290550762000d400b01d05008900c030440c00600e0f80c10500c1410300001c405044090603503035039240c90b410007030030300e4000f4400c081c81c512841c64500140c0031010300341d070304540c0c0c082c100500342820f100c60385c41c4102d05910020702655884c00e0504a117003040c1f00d050b03010f280481c080c565607500782d44445c00340c00903d00140c00c131100019909030000000002ca9406041c10300d8880c910703035000e14140511000d2250f000d00400944200c00b0044c40c0a44245034850f40c450b9400c010505e494001a0303164030080c031010354400407420300c0044c603081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 266288300 1250 266287050 266287057
    0xf0d1b0b0a06091d0d05030f0106050304062c010b03010903080402130b0604060f020d030b010e0f0102070e07050406020616020607030507051902011a040501150e2704020a05010804051002 82
    0x7900301000c9500d0740c540c03a1010440d0794903514002c98182e442041038003a08280030000c0d031080540382051851911040030358071030106115403820480c1c0000010f061005640c04204004090ba001c90224490154209010041a500c001e12540780ca950581d1605e4148219586160b141d101d0500640d140e80800c00500c01c1c0c40740f1b40300c60329190464480700ba580d0034005c00146c007103501c84e500007207401d0000034a0403103211210024540b624010809030b83e00301101c40880d0108a40220300041e02c40e0040f414140035070b00070100d000140060084450700400500103a41456085030316681e12010765641c03a5036800001005a0040c2c0b000c1800c10f4402c2c0c01441e44041c440c24864542000d00c24001c040c840b00882110040c0d6440c2d01c481005550000328050002c02150309029950500a500101c48484041641403041d110418500c42d10b8045000f021030000d0000d9044400b404140880b0303407002114203e103c3c40310404003150070741c040c00d2182d00075500f041c0103010001110062800a50 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 266289550 1250 266288300 266288311
    0x20105070f050105092d061b090d0b010914010303050a0804060b0303030f0f0109091502090109030b0a060e18030a111c090e060a05130b060415020f0d1b0b 68
    0x40340c0d201c0070000714100740602c0b409112179400800754008140a088050100e03080f80716030040018100003014130000841c503422001c62003502110390072040103a40280f29012090780c2020502104000b0b0000020f400e504031421182c0600581c03001c241c1d446a0340c1824000203011580c24000a1005842030404030350040c82880b0020b030000e5410b00007132550b001103940180c0780b20040c00300507071072489c241e42a0050441c540d0921603003203565a81e20b0410101d4062080c103076408602c50ac401d07071103100408001c6810040c170881c0750030441c0b40715002d4080c501071034440c2c0f54000040b680c1020301200500d0412009400f85003803070202c4e4801c4408204a00444d00c85200749800381701020340100042c1d40078500703030b19407440c41450081c0d00d1078030a1000706110301c0756200007001c11013500d590f0b031403203070ac005020030000d024440c00d4001007a80c051a00040c0031000007a070019812500000c280a100300c2c004116a100c0c2d80b00e107412112083c3d80344448084410fa5424540050000c0a1454105 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 266290800 1250 266289550 266289563
    0xf06061703070201030f0e0d03021c050c19020c18250c02010207080c0108180106031205070312060803040612180506010302280608070507020a091e02070506010302010507 75
    0x86544061080c11030818030040380140d00300003042c01c11580c06226002c071454480000340560700e4071000302a00c0341c802040a001345500021001d00f5083c00040c601c00300c800e01c06c0100500e007480200d102c03644d0001e444a0210081210f06481031600008a0301405070008161400c82c96501100c6910700e40050304040c51340c840c0c1a40c2074040703800081802142c4d41107940301030305003680d40002031900f031469014800700d03048081c510411740d9001e9403880d03005000580c00e03032030440c01d520001e0060803a584040d00d1741603180c00c0070740005d034007600401302607000350307a505441c1c51500d118104842c80d501ca0000258810842084651b01940610b801404061400155101d01070701c80f5182e56001082280e550f0000070052085140190190080f0326a0b00895610360b03e1a0f00115280001800b405e8144803c010016001d14840c004030b03001503a000d05043e40d1503540704002d102408803650060322540c00b022a03001070380d065100f6101840c0c0c100008003100d07407845e00190350540c0401b400f07a078003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 266292050 1250 266290800 266290811
    0x70311060d14091002070b0408032205070f0501030209031e0c090117070b031003030c15020a031a060a1b08040e01061d09090604020f060c0111091903030c0f06 70
    0x40e080740c0c4510261072030050007039445460010070990400c0084c1080c000301c144103000c1380001c204504007450b401a403100b6420350300e0b00c80c0d5500b560341c895440c0b152200c485405e0104410800301140a8040f1201c6030700081703400341c548005500341e0040008907078040d44400c1d43c08024000210361107060711104c10640c3c0098041d0710205900030b1098021603c45480c01d0b8544003070000c1080580004c00c11000c0141c114100b501c2c1a405100441c070025080011800ca0b40091004281f00b03440b044400250466854201000103400781c007181640005000c00040980a079080c20b6044410340c04035641ca40b864a401c09606c14001c0d51405000c5e20f440d6014040030950595691690380a86000e40700e0012440301c55810b04804511031000c00c0c000d46407481884401c0b03a00080746c0390010b42c1100c2c810342280c00d10000c0341050041e24041300456081c20350040c24401060001c4c519146c2c00d6918601c180300f00e442d40c07502402c032403000a001403048900c020206d803070080154400c500c141f001245 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 266293300 1250 266292050 266292067
    0x61803102c3a0e090106140403120e060307020a060b1c06051003020a170d2109030c0804170712030f110a05010f0606110706020c010e03010f0e031908010807031106 72
    0x11082d0b403030700b05000f01d2500e0608806a2410f1041e40d801880c862820600c841d02d12107141640780a184801031108003101d0b042030f2814003e41204004d0f510103040152a03107440207000b5074a01e2040c801b0f0b18402d24114051003241081e400d42e60f00040c482031081c007011460f0344c0f003e0042c03030700030418011320402a0002c0010f035940c194a400901040f0700d400d0014a020070010b0401c1815031810301400b2101c01d168000708080700e0110507022022000083c56241c500b82601c1c600f100c2d50005101000003c0d001c1014000a8040b40c1c09080c40c0085417040c68698202c0c403010305e5001400381c081510303613420aca5010320400145901f081e910302610304100c80780e0354107402c0d43d60080004041a40f542d005102d02d42d4020502943c54100500038699185003c0c2c000e034607141c907800900d04100f4424422071458600750030840c0705a0315084100050148015002d031a90016800401406060102540000e00c6180068140d450443c0a803601c10f18507a154023250702c0c0d42840f6500803d09202058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 266294550 1250 266293300 266293393
    0x2010b10020d020f16030303020a02100905010c09081911220b1c0b01090f0b0d060c08060a0e0115110d0f0e01021902061803102c 57
    0x814400150700286001c1c0d0198001a092682c6103140b525942d014103045400c140041c0c000e0700480ba01030500681d2020460f00407030401e85005040d280003800c0c03216940403c070307056221510844459907810070281e203c22600b0b0b1a9170070701180c60540c003803843e00000840e075290090b503110240240314209100c40c4800e84000784149801c500707440795640700d03150420300384131004000013000301c508107403a18000e503281c610703c4c041801808043c5584040404403429158000154071200500803e405495131400034064402221000b0004000c500800d2030b50401c04c05000c290b550400414007160709022112010890521008042100342410b2981c006000d004e441c0d0126120b580301c1030700d6003035070300090105068804007504661102440d24580c3c0e2041e001e0500c1c050b411503589503500244030041c2c58030710251454980c503029100000c04810b00326802105044281c601c00d00e02403e0200380c0c1e1070305008480b41d00d5a03e401c1304907001c29070580c50768080d1039200c1e40041288003052103070310f8a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 266295800 1250 266294550 266294569
    0x3050f0a021e0d02010c0c050d030c0212070615050103060e1308090604060c0302070b04080304140303090306091005090d080606132103120203010503031b12030a05150a080c1002010b 80
    0x15401043c60a80b0095080c05484a00380c10340c18002030040451382d807580e0350304150110b2400c05603103400216041c3c0c400d00c01c403070050780b001001d107440c0c40c000d0611000514144020048001c440c2034005040c0d4042d016280c111a103103070500c0f003a070351412450b044002400004440840d030406c4010a1690303194044c1c0f02928480d40c0c1c01840010514002e844c0c08040e800c40c0f00c4030345040c00308201007500002110251514900d00000820112012900e98001c00c020542c2c580a000100a25500001400303e41c102624600303200e0741d1036040742c041d2110042006c10001410110000303025003402401030420003c881016800c4955680c004240c4041800c01c5e0402b0680c07109060061640c00b4100280c401801c0c3d80031031035549404000307940c0303200d100721594449000100014410905102106d40300015050b0300e680d0303245c0381c2180700040c00f04a031100540300348070201e0000ca0400c46201001d40783c440b401045200460300801c100c91581031a0030301150b40b5075400d040251500303140e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 266297050 1250 266295800 266295853
    0x411060d050103060f090c05150d0504061b050901080606031801090b070f02031810090b120709090e0601061d03030708071214030a111b0d080a0903050f0a02 69
    0x1825411494128291207041d00c5400c05c6504151103100414044409002192030440c0c10746840b410304240c5036008d00402e01510001403400c4204414007490790000b6105096020b05d001c00e003000d100080d203041c02101e541900040c41600010134604004005540150301c410040d995030000c01811800e50b910340c80110380a9100c001801407041c1c104d44140700b1460140061401c2a40902610750544080041c062064400e51413281045000d03480e504050035441484a6840c040c112800c410681c041e0303200341c0001c111000c0082c0300c103828440c8080304900c200180c005a46094402c542c2401e00c01c1140c0b80c00c0c0b500d00141807555800b00001d002161040040396190121400c0182d42009049030003814810301d084200744424406040702c3c1d01a040081c00100e1401c2d6140d0040240104800d49031b1881d2840b031452804000002c103c1c01c02042562a800c80c0d5070f1b02c48e410f00513640e0003040200071400501c00810110f45c0d41c0e014055801c0140b040b81d643c142c9005506403002c409144 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 266298300 1250 266297050 266297077
    0x30d0902101b061829010b18010c030e1201090c090504050d0302250b0402030d0908030406050d110a0809060106020109020603041203061802040806060405130b041106 73
    0x140460400300c00080024200d4202459031072003200c0a0389071044009401854144d8440240d1146840c203209400c0403070300300c0c3d20300e014000d031a14040d212824020540082c1e0545038000512210503900710b425021607041c0d9028901400742c0192031601c00040200c0038084080d00c0c90340544c9440070a8038010f0841c00c0007180044141c100302c1400403864000c24242c80c1000200008680c00040041c0b00d24850714006036100014258040c0a042c118111840c00c11f40800b2074040c0800411402d0003030740210242c070300c040c60000e410b442119503842442c015800a0204029060080c07015112803070080c400070802c5251070701d244201e0b80c040c010f114003046d008414020700c3d90040000a024007003900080107281d805c0d40000c0c569000c0100010031085012032543c00c078521a800500c000d103405070040340e82c00c2c4c142c103241010f9045070141c00010301c1000c001601c185024091240500c4d66089540030751680d0f6181e04044900080099640034000c56403482981c40311001444180c21a50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 266299550 1250 266298300 266298311
    0xb130509060d030e010e2205060409170a050405090a062d1511010c0201020a020d110304140609030618010e070f1a131202010e101706040b04050a050f0c03010b0a051b030d 75
    0xb000501108c40c06000680143e00e0446140b000413102d10404404c01d842c040e059443d041034070700c00c0740d02e4491034010a802c201d01c1c0040c0040c03100141c00c0303e002e40c0c070b10103800350f003500c1c88203110317403202103207a0060280b030f0701071041041111164101d52a2160052404600406001100c3d5017034840602c032110060f07600103480b031146981403104c80c00c0e1607418609503001c807001e070444503500d00880c01a000c40e68903660b000862039030358504031101d040000c1e080ea00981b8151515105600025841c00e40c2542012103181c030f0300f1000301d2a0000e80710307401040400c650401424034101d0f40c8003130000c0c171503031010070980d981c420014186000501452845000d01034052000610003c040c40a46028448030b500c0801a02e400003c14401e111504c1c0d55006650b4400340020040c060242496402610700814454500c000b03400c42c3d4070502a920f074620141e16441c01a0400740700901c1250502c14080c0700071800503100300000c00300083d264143e4042c510354007005505650091603042219961035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 266300800 1250 266299550 266299609
    0x30d030203090109140c10020703030e010f0909050a200a0801030807030302120f0907090209060304030c1106070605060406050a0602030706051003120f02070605030c0f0c1002040b130509060d030e010e 88
    0x207007d020300c280190300c044c2c080b01d0b103181d5026001130459110076050041c2c068154808500c43d030740000061402002c00d119501700848043e000f03061310b00b94000218485455040141a01c1080f80e01d0603a460b5500450383e0720310f0b11041101c1e0031004048081680030003d0f90684031001000e40d0045054005007107981c10895509480c2c45002c0c2e212845281c0144640c000b1a034661003540d0340903400d400c201c246034005140080c02540410032460340322402007142401c1c00f01b20307844030b882030798107840070040f02b61518200602041d19224100043c0d000308810f00c00120a90000750b003020b410f01c4000c103140e41740e50b0340700f0481011640c010001040304200242d8164100700c808000e00360b504100f07107035060100c0202c00911404540200400c0000b50040d98003008009481c1c5880d03000004540750350700c0703002d086456413042200c0a1080390314400480c1c0c5141c408071840c00381c00010205c60a021803690165001c0080240d09414041034000e4140c01d40c40304a42d003074500d002502c03e80840100e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 266302050 1250 266300800 266300809
    0x412020d0201051006080603120f07031103070507030201050706020c070b09090a140711030d0606180603050f040b06030c0405070f020d051218100903050301030b0a0902030d030203090109140c 84
    0x800362021a810801404901c2d03803000c0100007034613900c0c034081180d0743d142e00103c1c0c0703004049210350380d14020016154203412281c0015022a6110341c0d2101d000300c0b01844000c3d502d0084050251080e08803040820066000784000d0450030310031103001d414210646031140c14007940e94003808011000180441035807030300b407003078a0b4413840c1e180c400c0081440e0500c1c81610001c0007440c0f14103201c030b80000341c9506441001a00d880701c030f2220080c04400c8d1103c00040104241d80c1c480c0740c0d40c01c0e0900001c44e0560080c05030134442c00c00c00804407604d50351901c40301c51a1002a044a4040c02084816140360700c0d01d000300340c070499164a40030155160300314024548141800d41e0700c20070009220710020b03414140c1c12950400142030482c8072096060300024103081003600142e000600c4c0400c400d00309a000400f075030480c0d000b1200b06410390344180f4000e0a90310302d03080003545900864000d0b08141c0c003070f9000d140c00400300c5d000000c2c0c16006136118441d004901c407800c50580d0042c000c000281c0360 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 266303300 1250 266302050 266302063
    0x80f0a03110109031d01090e04111f05221d09060c09063f070806060405060a12021611040e0114161b0b0f010602030a0203070609020f0306041202 64
    0x20007000700301c3c00700603407030040041940c1c0410b1814500e00c8004441d180e0320a03070081c070142100b416008100c0c109031400200040203500c07054000e01d84000710511004401002c1ca1414200340c42d0380d0301e801501000c06011545001480b80c14003980080441c020000e02c84c8046030412941c0210b00d41d0510070089480c00000408002008000b00b00c405419280e0380c064818610b0801406003a040604d60700c0200344c0703248804001030503d8072a8400403070310301103280c1c0c0c000c4002e501c680000b41c54040c00c2c89480c1c82103016260b04082d082095030721713072442403d032000c080007061001410000c0c4c185440348865102001038070300c14503040505030585090701c203503c00100e41d1303c020841c203280301043c84107040c4024004400150a8004004464040c040d981d801c1885503402d2190f18003d442c00d01e600300d1050707456801da1100b04001244050002007110b541d0a80750f0020341c1003807295511070000d0034880d40102d800200810381200d25131010040f142c00389200c7c0041075030340302800b0701c000d15108 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 266304550 1250 266303300 266303327
    0x10605130510020312130f2f010c1203060b030a06050906060301060c12230406031a032a0402040308191803020f040905100b010f0309050d030213080f0a03 68
    0xa0541038002c2c54140c0000444051a03040609030040383c0d02c0442100560000c2d810143c00d080140c60350074100700c1481c19803458000039864180044490f0341d80460032085010056000c10f40098402e00800d541500005080c07055207800f0071415120742c45510310350070a507040d0400381d4480c04140003600d06913003040e41c030100a480c400d007150300d01034000340300c101e03985005405002d0400d0400390080c0300c1c1142400c1c88016101c161b00034005448c941c0007540c4140320b401e00003440c21002c2c40ca40c1003150404803500d000140105056034000c0004403100f5620985040890220441d100302902c90f400600300450084002d00e8580303002140580701c010300c008081041050a070300744d0301c07124120784101040d01c0d01035600e4201600c503000801d0043c0504407024005108004240c02114172607001041620405c5e83c86500102d80d908080d0240d07100a44018415005220406403451103540074120f5003145954516280303a07600c86460604a01c0b81c00d1382901c0c1c1240000906050b0441740100565 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 266305800 1250 266304550 266304559
    0xa14070f0806160f171e0703290a08060c0403050c03210f0d15030204180812090a023f34170c030a020102060708040602040306050106051305 62
    0x520b0003d00400710b404420a400b424400388852040440303100c1c1d5203000900000c4801d1300c42c1410405c244200c1c0500700c2d061241c40d0405080040c0c00d452003405851110a1540003480c0000c2101d44031030190f10781c150800e03400c00106603000807988420083c20380034240f441c1d000c59641e0304500300182080b1103001000d002e68081c10140703c131040181e9804009000503120385448448104400f6024441ca8840c20704e25400c2250a20901300d0034013008080700d1084808109071010080d1103d101d005049000d007041c1d0f001d00c00b440d418000b450340b1940c0081c004003500d112441d142e00144503101d24002140140100355011121402c07100901c48501c40c9001034090391050751106a0f80d00c0816400c0102080c690300503900c00c00d8070044007040c03040518401c98522a0b1210b842000321a00c024401c0c0d0103108414503070600303090221345410440d8041e4007801c0c241d56041d81c140c0c5c02900280c8102e440c65401c201c0000450f030113214a902030041c0c0d9840559400840f05401c528000541100b4406d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 266307050 1250 266305800 266305813
    0xa080901060510211503050309010306090c2a020306240d080a03150f17070b03010e06011d030312040b07080c0a0c020d02060403030c0209090102031e06030a14070f08 73
    0x3c007a0070410000512520035144003085400030001000b5040c0340d48001c21565841001000300134000c8054401040281d07410400b20b95196410b400740c42c5c0c00020b410101d84695a0709140128192401070004003c0e084c58031504000e40c04a8500081265410062114411204400c01d4007042d1004130f55003c076001c0821902980b81c13006d02d03104604801e424182d55210f800718001c0907860361030061007070a0f040d94009a17506d500044907507a80002d0b540d80c1c011898007040910020081c1e9060381d00003410002a80c1c0c2c0e040041d20b403000704502d452080d1855103104045540c007003009005070b5016042022080c01d06181511004801401000c1442043da04100b200041c050070394490040390300e005040da03206800030580c240f51542002e90810000200030003450703000051a00d03070a2003665865410303a82e20b05107134200d00013a03c00083d01c08035895440c1695a8034000f064108400400740c0d1002401d560740c0182c001e0701d1050144141d0040c405c1000340d1480740c003a07140140000070203440d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 266308300 1250 266307050 266307079
    0xf1202030408030d0513021011210d020f0412081305010309020d0221160503190b0112020f18060103050c0702010813050f06010e22081c020f0a0809010605 68
    0x1241c4c0500844800b0f59503840c1c00189803000079083c1c40e2002a006040d0b030b155010442c00003403405104403d4081d9a11590542440d041d070040c410381340964800324810b0400310311041c0d01019512009071992fa0080034000841c0c40300880d041c401c0103900c109103442e0394559603441e52110300c08550203581072614118210001d83c803003840c0d40d0740669044078891000b014020045924120b10701f00b074401842251071140001c20905848020740b641207049420503c0c0c150141e03041020503000040c120480308004011040805400c202c0d400e200910400302541404041645002c80c008444005d00f000d00c1440029601403040c260081411175400e40b901e140f540010b46800000b0380b8080b001700128031800107101c000d01c50a241c200c030103403c1d2082960b659440403813402d4107542d401d0405620400f40c0d0401c580c1d010b104004d1a40c45001c03e410b2000e00c410701e460210460920201d00c5800b0410362991a51351402860144005c1e10b80d10800e08010703580508451032a0425800781080b000d0418 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 266309550 1250 266308300 266308303
    0x8030711150d05090322050307080d12021303082b020f04140301020d0c1805030d0909020a030e0102040807060327020603040602040302030a0819080118270f1202030408 74
    0x1e16861544202141c0c2e41c42d504084d900e51b1088000b2400c0380303520690804040110305441004581044007210a51070f203c611180d00c2d906141030f032001295040350011001c07502e41d0040e00c020648900000541c070365980751042c0746e9200c1e901c1070340310b8441c0c401031000c1c0c0347d60316020541e5881100700460612050540002e080c1c807441c000c00d100e00d40c2c40b54403c003145c0d6003501100c5c0d201300000070510542d00344100141140342a01440303c049149001c0108013800c00051101e000d400e1a035900c0421850003140381e0083d40701005203010191200c8698029110900060005010010081080a140801c010111618103100000000120340d0f001403890040046007803031a01144c1e00e40e41d9440ea031070818000d1103540d0000390540504a80d4005004003840036103585540d0600349103414642c2d020442d640b40b001d0083d590407440716001c0e0b03060340c2d0066004228514039840903110740d0107200820380e41c400d90300300200d0700e0071030134008203040140c484008d140444c0140000c506260500b003c25 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 266310800 1250 266309550 266309557
    0xc0b120415061809240509190c06140903011a0a0b04051305071713020f0d030c03110a08030108010e010c050f030f0a02070807030305040b07110a021e06040803071115 73
    0xc20240703884c0d01900050104100b00390050881110708100b1001c410030b0200007400c81102c000f1424010340781d040f220a020007401c03254840d4011040d01c0e50504201c01a40ca00c11f81440822a0110a00c0024042e072024840d102170768504248580110410204104c180071480e003115239500d0040c0020042605c958807071958012556001182c996158039044030f90718100000200486010b5080c40948400d012281000500a1380c484401d0f01115080c01610001caa40040c00140b691a01c000400d104000c007000a020300302c181e400e8100b803030712005075070f070000c0c2c00030040d03079540d40d250210281b0244a00c0b0f201e002142015410031101000780842804000c10300010500d1070000510151056411104180d034002d0324941c94030141c1c10000c008110880f001c4684840700030124107070034065144240d1500e0208000d24821889a00b4800303000711903801c5880e424500c880c514070710f68131200940040d0440c040110b868107850306041252040400e161070044d00380c1c2481e0003c0e0580403048 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 266312050 1250 266310800 266310839
    0x150c030a0615080a061208072d0b07031a09040b0606191808070e0a020d0906050f070e040509071208090307080f0709140402040c0e040f02090411160b040c0b12041506 73
    0x5c00f00d5010540707183d05200001c0c00544500070127100203a0b4200800f0003140c0d4016841903504024081418032900600340c49000f90580c02000040054002400b03c900c8507404000980034a003030480c0898000f800d00c4065910308045030440072100e4401d1215202080246441c000911940c1d06e07103c5c1000c4c035004050200354402c0d400181c0241c0002140e0800e200982e41b0601c10400382c6032522801d005440103596100000e002c00c100c0e080103103441c0c01141d0107410300380c024104051800111000304a0044021a015007050281006540e401d114000c0200400c1c80a4660600d48000c4c0c1810b0036101c1d0032425003249419a003002d030900e150203096100354142c80002e44206d0155050750400301380014142d0084c03c1c01c0003880d008504c4d030054941c1500a03034043c0201c5007600c2c0280034501514096044410100781c040c004608105007503600903000c2d4000001694071404080c001d503100070045a00092000b00340300410020020200714511903580030010a402d10b200d0b14803482e00d2155 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 266313300 1250 266312050 266312063
    0x60405040803180319030f1b080c1308031612050a0e0108060127080c0303090f15040e010905180f0a02060a0e0a0305010c11150c030a0615080a06120807 67
    0x490901c0f07400b00104c1e0702c01c078a228200c030140d880d4402d0040140440300300c0c1114513810074118a680343c2c142c4412207400400e5884c1c2543e10340c0d0340003054030180c10851030302001503105c000001c1c0c01c04041c0024482e104644001c0130004404d41401205000d01400b41400c01208000d519078542c0d06c814500724907002442e14851a4484000480c0d90001da5120505400d2000020591a04000c0303400c20442e0010401e841c0f6a011000425840740504a14250804a5111289900e251400306140d828030040307420343c1440c0c1c448041c810300c440260469141260b480080c414541501044036203002c1c0c4000c01004880c6081040d20303202c1c0b4404d08000d000786030208100c10010f000300b501c2508041e020b8140080c0f29641d0514034080c05100c042807011414100d8001940384002c186541e15840302501c3ca41c1a443d19000c0c200c190f440100002035007550380a0200e0b403160460089505540d0507a45e007203a074101124072500302c2c1c0590b4402249034814030311003000143c02000356200540c0106 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 266314550 1250 266313300 266313331
    0x2070f0b030609180d0c0b0912090d08071a061c0206090112020405040c0c0204110309031c020d0207060207060b0a050d080706060803120906010608011220040f0204030b060405040803 80
    0x8840d62184030606154005601600e80c1104071180c0c41b10201d00c0703c0303008200144007502c4040107651500f14258405415200070480005682810101c8460181c03149210624041164990490b03103c40d0902c0000071264000611519140c026000864424907034001d4041101a60000300144038002d501c6042c13141c01c020703c0450003040e606403001414003900034032000b160218024025064008104d11461809011303509901c11030040e031340324500300030041d0b142c000e0f401c20b44082514950100040e40da0200001076841c4614005800034500c40d503000358545096141440a903900180c0c010f0107041c3d030301e82c100316940c0c0f018440d40030340390481b1490b81d43e200039003000d40252280340c00c0107810b13120000308112104210f140c0e00b032103003296109644861341ca0308412202440c0a218610560112056000c0854142e182ca40c4004844014003000703021048003240940d241070300a1900143e000c01d041042c032200350700071030740018103c030200720a1034240e6820003140030181840b0100c681d000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 266315800 1250 266314550 266314561
    0x1104060e1908030a030c080907080a14070305011a030d0c0804091a0a12050f0d09150203130f060e01030b0d0609080705010e06012301020d0e010216140102070f0b030609 74
    0x7680d4001410a01040d6580d40c404520050054a41d03541400c000490316000140c0345100071a084003650140d00c0501407590083d01e0301e40c00e0001401065045009013a00080018000d00c0f4a51410340c801442440b0011564101414103550a141c2c03c01c2c410780500c5d51000406d00780890702600d03030140002651401c2d10762205205400303c82403e400c106100408034811030780ca42d1707802c1c61901c00c7c42140c803021805081641c0302c90206240f1004944101c0041c818140344000f4101909454812a41441d81035003850b0712074140b81e44500d40414030b241003800520b43c440030302d4042d101f0070b003014418013241401289040901500140c1541c2c0e642c0b07058010002108220780805800000912541c018081501e403112028401c840030b010100c1c1080c0d9902c203056014019a481c160058044007910440c2542d040708102480c030b0441c010020040212a20010342d480030701550b2484101802c0c2d003030000382c030300300b078079000081050305210081220072062011268098401e46c2d50a00e6a1200c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 266317050 1250 266315800 266315839
    0x703081f030609051b03072304020702030d090501080c091c060207050a140c09040503180316060903120e030a080a031e050a0c05180d1704030c091104060e 68
    0x3280c2006040302d04060006051010020308040544982c0718242c50341c8803d8802c0603607604161142100008500200d0b008103907103032448943c2e03000090400341c540a116400241001c01d10203c950120b00001000e0100303507440178641d94801d4407840128135098a0100290a004144520700050000c0388000d0013000981d40541d943d09501c2070844036115410320b0b140c1ca10b802c0d01800d14034103100f100181c004501c0c0c1030041502454004024619200291061000d400d04c0c3c6120a50140301e02c031400c2c010052050400070027031034299901d0341c440f404e41c500031248580c40c1d01513108002250a004045039004a48a5140d65001980c0d0380d441076001d84c10b030b0252440d2140807840340d8000408080303003061030300214801c0c04045410410022082026a020301078103400c0c40b9442c2c012454400e0306d081807554216075902505000c000c0e18000c141d180d0b07041c0e100ba0821640d0245412003008002c8103070045c080300350100c201e05414a4207015008190803c2141510311503103052806202c803598 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 266318300 1250 266317050 266317111
    0x3020d050f010e0303070f0302040303080c070f0803331f0e030601090b13050408030a020d20191403040b0a1508240f040303020906221a070308 63
    0x1a1000203220b00800b40c540903880760411241c0c1b03400b040d0b400406d03845c1c141c800d00c00c03074003604da25407241440d94907001c1b5654403641009404896614140e8030040210383c1b542c1c00b41d4490b00414554480e170729900781401c0c89980e44c0c080000364900d0803010340040c0b90b494001007100300d1141c2c084c01e1401c1d00404412260103009040b203940500034a03002040c2d4100d2604200c02ea40d00c01c1d50405203024804640f007085850494029181c2c040610109100030300d1070300204020000490041003000c1d90340800d1280000d2800811103030000081e00050100c02d000718030b05400c0c00c07402c04011414001c0c0308161144070040000740103591410002d0020b50017a803101040300740c4a000c0042041d1150816039856040b030303041e010b0481128001c14840e0b00308000861244142040039200c6817104d6800760043c2d0088001c040e4420b406000c0c4039203881c078601100d9014200b0450300c11001e454490152500400b080e280c5059010400080c40400c1e008564070707421100c1019401034583c081c542400c010707034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 266319550 1250 266318300 266318323
    0x3020904110616080706230c161a0105040506060a0c03051b100e1b0a030b0a02221809020108040308072f0d0314070302070c15020604061b0903020d05 66
    0x20386101e22000380300205001d4600f0030b101c6c21b030802802c0c0140000b11140103140d401c0000526203080000c44078031004c1b000c2d02c41c001c00c54003044040043d541d1114500d19082140801d2451100010045850680a2079411107820351741c0c4d9261200030034009000c0304121001806100700051803c02c255016401c5025500f904030958203100180c005000290054030403075103542c41802c0003009880c00316682c003124004010402c40751180b56658008610340f00030104902c06030b003804200075007103460241c3d506e031848a040c991001d6040100c0708110b0300010750181c116900e003810709001030b6044030b04140c005802d81031030115561102012a0040c5e18450103030964107808010340880600041340d24060311010007911025208180c04070115400d0a0000c0a030006500104800e180a0b038020b00d000d90213034950040c0f00d03417100820315408960944104c0182d210030100010701c10107114440c1151203a440c40005201c0d11080201054114003000c0d10420400d4406010084100b00c09040f00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 266320800 1250 266319550 266319577
    0x71703070c1d0702060c04260a030504031208040804050603040204090203010e0d09080f060c0307032a0e010e03030d0c1116050a0b030417030601180803180901030209041106 76
    0x320344903034801d01410104012860b030410902d01040001e4004144203120341c0c8a440c403541401e1403d1064030300f400d041071980042081c0d42c2079000042da814000482450b0207500e40035950703444c502e800610782031110040b900f04540e000502c00040c040314211030486204450b102e41325100c500020f0003e095148000394190b281408440818002007100b40300c19466884140a482e52150403070340354090311100d40c0a60308414009800222845c02440d08403205181c0000c40100c210001c445410800c010f07020925641d000211200b43c0c40700c01141e410340c0030b29200100083d808017180e0380b40100140042d80070380302d050904105111f21409020014014121504000042d000985601550041a009100000c0702103850791019007200c0c040c03540042e0000454850b070300c4200c072640028000c58100034581c513418a00803000c10386030001d00f801c000955500c01580d0f040007105016032000d41d01500d4240010030142c0e0f10411400c1e44160409078420602c0c01200004805c2c0c4500c0845d07a820 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 266322050 1250 266320800 266320823
    0x50c0301050118061a03040b0711120d1d0715020c1804061d060402090705070501050f01050301061205061306090c0e0105030606061810140c0102031e060307170307 72
    0x455aa103c90464030000c207401040566280c0c0002c0301070000049184c0b201c4d00c2c0400100e400640001c040a03803040300c40c07414100c1079164032415824145402a040d854060208803492482d00078410300115603135a118013500241c0c1e004209464140038400e402c2c2c50004d006c1c2c0c0d47d0394540280320a068003500204190b280070940703141d0f01080307007040d14180c5480f894030300c030710103a20302808042441c030b18043d00421040c1e40c1c81e400c002454200419120400c076040c000000095004d0013854018900c0e9100017000b0b41c142003c0c1402c648442d0f206400e0b003c0d07002801c0c0007144d00440c00310b400408080c515203140070903082071800f4146a03040103000b10014400020030821344007105042e25021402d8440e00c4e16050204403403806460b40d11542d0700000c500c500300da03240c02071081d0f9003000c075030400201c0c25036020000364054003d10820849a5000020044038804040c2400040c0400600711100b40c2084004030750f54242d540036554940c038031030310110000502082501e000d01ea000100401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 266323300 1250 266322050 266322059
    0x901080a05011824060c1403032413020307030507030516120b1f020f01050c0711090403020c030118140706080c0313200f10050315010302071b0302100905100c050c03010501 76
    0x3c81004410a40c5c200710305800800e0309030b40120427240030740c1405584044041c242102040018807140c52250f00880f444400b01451280380040c5103e418030791000030f01407074151400360980e003004200c0d10b0807882c51503800c0009a041aa041a40016a64002147c08031880400c18a02900f00d402065030102010094a681e001031031030a0030b45210020300c0305450b412086813042c003941c10010004104e00103407544da41040e81c00e45a005009104850110108402003400c442c0c0d01c40001e007030000d501010b00c040c0280d954040b41441c08450051030706514003c401842c118000d0b041c2d05a0380d6001000c0746015402600c2c0a40841e0021090b5219a060b41480d601c501c1c0130003841030080b11184900e403018030b0103580a104001498a586142d513540e106445501c940d40303280241415420702142010a48030f04011a840c02c0c100748200c01c15003140104045900507031a002c04003e000401441b880d100e04100002806282c107050310400568581181440b10341d040041d090f40c0307450700004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 266324550 1250 266323300 266323307
    0x20c15040c031a070903020d0f060609060807060e09010303110a080a030b09150904080a0909020c0309030f07060914060f0c010f1d1203060f03030a050901080a0501182406 75
    0x1c003100c2c458480c000343c00c43c000b8609125070004464420104000103410800b50510601290385580f0070b84c2d580d42551816507408080780e41d00e42240c0700f65a43c40c0b000388400c10081010f10701410710341c100041c0020320318000800240381400000c040060482d1002c0d1032060170024410000c1e81b0024460310303038802e07001c000c0050840d103520a200340400390102d40055042d10021040500c003a059051640c0c69445019490748aa009142041004031000421904074805026441c0c4820083c6a407044242d040510701001499800015000000c0400100750008240f03070403141050a16201c0b1020b0f0304c00982d42d405100b2142c600c0d2a000101c6041d84c0c1819402200c0c503086040d010000303802d02c10352540c01c0704500c1000c0c2c2a00d501581040581240ea0300c0038542c0300d0802090089118001004203065400508810012a10200d070005066812031317080741c1c0c07041c440c6004100c59850503041001c04a0300008100c40e050f07440801d440901010004030703c1d0424047c0840f60111754485004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 266325800 1250 266324550 266324573
    0x2010e15060f011103070605090f03040b030a0605041e0c0507080d0b090702011a01050315040606080f0f070801050f0f1e120d0e01050d0b0415090c1e03020c1504 71
    0x840c815003000b40e00003415030054190b105410300000045080206681d515002800042c00c0010b89205d00c20707103081401d004000400160401e0301a1546030b04018488500399003094104520450815a100c5040d00580110401100c06c0b0980403a01c480000d1307003520180704c2c601d0042e060400001c3e002c0d03418056034000030700b481c03816990080b09a850000c12403c850b4003034071072110854165041c4a0755803042000d550000111341d4111a501411340001b000c4650680c0540080f56200042207901c0504424080c1d00034110300000b47c1c903180c24680282103840c140269841150498106a46a140d10000b00014980581170442400e8140360440c0d200c07800d110b41c03c0c810600b240740c0c8401d90001013103080d844140d54840b24840310b0100015242a040b122030400ca550f40d60185542c550b0b15801004908181e1084d880351040c1130580c028103480f03120390740702d040c09034101030009040743c003507005520000c00c2d280050310380d204080c0181c01c04843c50010700d41581110180424490080500c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 266327050 1250 266325800 266325811
    0x190909210e151c0b010e1e150d05040302010c021e0c09040602120109020306040e01060509070c1b060309061803080601030e07050916170403020303190605090a06150e09061002010e15 80
    0x140407550000408005115130070b1b07c920201940e0040840303003641011690f55501600003007030a0300704a5030340c0c418012039900b03d1702500180c1d11074150b124600c0d0140a0503a120032501111100105544402e580d507140005045000b907003800d000030107100555043e14441018001c051856580d150517260180d0030650310548220701d0464080c611040c14840c180407914060410f2001b45c1e03484906440b440ea0301071082d6102c17601c51401485e5030b9001041840644541d4070b0002d240c1040d41400c4048032075070325601c1c030462114150300000c00e03000000203038442c10910b03010078120480c211040c1030a0850744802e810461b210180200d645036121450380c501441d03500ca201c548038048031194284c0b000c3d20060096081000420300403e180d4819406200b890000480d41c03580d0740d004592168000c64017004015601c0006205041080120f0f00e020005440c103840f004401000050421802400407032203156100e2210004500030f400c66001100a84141e80c4814410717002c400481408450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 266328300 1250 266327050 266327057
    0x80f0a0207140a1b050f0603040f08030412090501030504200a21150204030201120e0c1512010f080c0f0a0b0a110d090e0c0702190909210e151c0b01 65
    0x3d8411340703250845800d200300c80000380190b441c040c1c580240041c0e5440980251001a85010140042000c1400450146104020001000014003001840c01c045500040d04040c10001801f0102d203030354110031041c8449070403602f48000441c0c0080c0c1d041503140c0c008441e0b40f14612100d04114010408a1089401100d1044c0000d6841034400104e1003640802800329200d401e0b603490045040d4884040345400008071400007031004005111204200b083c100041c800040c201080c4081081c0240107200c140104107115040c1354a040e15581c0004605005079082c0780d0f565a40d03642c500c02c50f8000c2402125507607555050346001400c00840000c41c003564070880d1030100300d071807265246034116030000a00320100d031500e4050f810b41c0c0d071041c40c0980c1d00805000c0c031608800844a420030043c1101c140004d200d842e10314001e6583c03d500307456a01480c2c040144c0c840314a1b080386640218080403141c2c49d0207040b020000814030301407641c2801c10f4076441d4030426282c0354154080c0b00c80c1034003604e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 266329550 1250 266328300 266328323
    0x14030c4002090a080f06010e100305070b0405100e1c02060d060f03021903030c030804060207050d0206100602011b0810150f032711040204030203061603110703080f0a0207140a 77
    0x36106a854807240c40d1000141d100c86c00420071010246034007500038201007500e0352625a60b0b25007921304107003034110b00c20003d0300240810151801d003c00400c840e00a040c0800601a600001140e11221510800744508041c810004540c0e0f000d045a145203c800403c000e055190000c0c28000e0f50305001c1280a450310b040c1c450f4103100c3c1051a007040340e506640e401c0f8000e50760380d4211002c500c0034000700c50443d003c0c0b126600250041c03240d0511503240741e00402592904080641903508950b00200a40e4900f5220f486075035803c280f40c1035820000c0c10002c1c07071612980d200c803411440550001d44d1100349600220750007548501054141442590b003840b0b00344a104000d0180d520914500442241d0003e0010018200e004000402c00c0002c0005041c1552900400d003051303400c88070440110b111454442241d030701481034080003d000e4030401c0c01c00140765800b0f010343d4005840c03050a0108000040c550440603011203c0d52980041c4848882c0e804141e019a01e1328287c004031004e08407103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 266330800 1250 266329550 266329559
    0x6060303110a08090f06090301020d0c0806120705060307021c050706050c090d150e0a060509060c0306090703200c1501081b120a0215030114030c4002090a 68
    0x5050000b2941000103503203461515400c0000440311245a580c020f0414010350245541c07e10140102c403049142c0498400303080c060003002078030001c1c206440b4154001d54010f105600145c5203042d55820340d0816a207449408003645041d14102050b1300f000cbc0003d5901100c0b6038484083e009480c407680003030045460f02a01c044160094428440c0c2141c0008001004900304002000081030704060008814001c0c000c0c1ba8108845140c081e54030545450a000d00392004000c040e07840183c0224150441c107015001074041040507045804041c0c481800540502e030071140220329400810390145c2d68810304420546501c1c0440c0310302191015034000089408022442c3d0074007980d8603500d20b1540d2032803400c0002c03001085c107000380d07a44109050800141c946102811441a00074406501c940c944400001d0312812850400e007c0e4200480e110410b1319a03c0d044030300e007501c4008001204108100b9100d1400c0c1c81080013444807400e4a401c0072001c81c030781c0244501c12055980040642e100c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 266332050 1250 266330800 266330803
    0x80a020c040c170a1104080a020112060518180a0b070e03010902011e0504080607032004050607062307050307110f0703030e060408010c0504050a05190b160b01030606030311 76
    0x8142c10001240d500980410084600c84145603c01800d003000a1000030017011542c441e005504100000d41c00201d030f5a05668002824000d020445132041c08502d04020105050003c01607170b900705c1000102c0864609103008001550656410084031908a4641006845400207594040c0401c04260404c01c1070b080600840c005560180c44d000c1e08144041c0c9011040980040c9540c00c0240a00021540c00d03024000340380100115500482c8800c0d400c0c40040841480c5d01e40906131406c20881003010382c90b0030084c2d035640c07a00302100103010f1181c4d101d0405c5078a04046145481000e25081020242e080001f450042603076682e041641c241e0078016903542c6c401007220070781c5035000c06000c0000a100c4e122a20184002610683c00d150f51824600d082d00c082e5200c0b1800b04801143c280228140381031032400410302254001460a040806c00145071214040e01c2d1820038005880609140300200e1135101c103030300c0124100c1d6503a59040503030003010640021000200620b40c2d40481100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 266333300 1250 266332050 266332061
    0xf06030606100806040204050a0f05030f1903050a05040b1b06060114070209060d020d0c09142719060e010e060601050a11070306060305010516020f0c06090418080a020c04 75
    0x142149a55a44801043d101d80c50014078031a030244e004c01001c18540c884401100050800a00401c03410303040c00d003050700b40150708800c0f000a611010000d658606103605070200184c03d42461aa50400f00400f00c689100d030350403600d0241800903031070030030030888542c0d44210b6030a041500c020ba180c020045070b080040c0d00072444110b0052110101600d4141e09503a007082c0000c00c02030010b030b103503801318860b080c41240a40d200d8000a808003d1410035004059004213004440c02040c900700001e00740c10400c096488220011290b60701c1c80c10fa10401135540c001802003a213030b0606d40c0030300c2c0180141c201010071118039401c1034941c070400100011410300590341616810708100034010304a03061040580070308020f02c285080080890801d104041c09140608008100b6240040e01d9440e82e07884003240c0400c65005d06039280c1c070f100c0e011038007400c011401c6840c95540c4030140005805054103101707107114a626118003404100315070f07004041a405030f80a403000070a010301000210303003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 266334550 1250 266333300 266333311
    0xd081605090625052b1115040506070e010c020603070309060b0603010f1703030c0906030c120a0f051026010e151e06060f0c0a050d21050135060c030f060306 69
    0x81d442d03281710508074050340c612061b07641c4580450704250741541d41c0407030b80c110559058a081e00100d040c0800164804a0fa4a4500c402c0c2040704c00700c4107507030100301c0510000707241314101603031901d0810401005411000940c1c2c0b004000320344030750310707484480511040c612034449141c441c681e800c10b0303820700481a20301c04d00c4050b040343c0c1061401000e00440f035200421444030420200100c01d000903500e00b400380201150b0303000190728145c058000084031405802040a44d501e0070040000881604401907150030040700c040020401c610f0303950143c0084c2d900102d042c002d0940410381c90780d00300c03000740c4150240e0003034200240d4140713154041528156110f0340c02c641c0030445080c2111140b0020156082441d0071906100300c191070309410442a02d4151002401c07031441216802e821014a03a0000c04410040089500d480d0007140440a04402c8a180c500d220700843e15554440200390703400700d010800d69010f40b40c0380c1030300542307035008880c01c0803100d515a012074040d05001a00c035100d039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 266335800 1250 266334550 266334613
    0xc0d0201052505130311040b030a1104021605060f100f0602030708030403050405042306060a050d09140706031418101104050415080d08160509062505 66
    0x4401c0c440e15a0021880c4500b030b20030f00004002003014044002c440300c00460264034282c250b03009100400007a1044800340380c0c400d500074904540403a00c40c0301400001e4000300c80060b42ca403031504103200520b416030b034050880d01503c1c1c20003c00880300092140314840e4510b43c4002191108200c8038202550700900005910500c104400210040001c54102d030090030150304042c0e6400002d0700761401483c08c2d80911901241100144604030780140e00000c00b200d0340c41c141510b10b03100500c5801400810002d558840007008180000b81c00c004040c0740d0b80d801540e22240c6ca449025000d041004000b0621060b81000101202c0d0304045580040c0e40d200007400500c40c0811140000d08000c1031881d05040742000005040c2d500c41c462400e02020202500c600c0c0740c0b070100030b5410326404242170000c2c4440396080041401e07117840d4060810059040040d02d4403e5040400c5a80c001c0f29030880c0070558840032124050600c840001c080b80c4682c04070b81900b203100401141c10703800c685410120 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 266337050 1250 266335800 266335831
    0x9020f1b0a030831051510060e04150e040b1510050a05090111030a0903030206060f0a030311010b06030f061f021002090d05030307050418110702060c0f0708030c0d020105 75
    0x40201d05007115011409103850003003482e03400c001c84c9000480f42000b21800c1d440b08503240703424059100210380c04042c00c004044000e00e0198080d0411030402032061140e076a80c040c0001e900107682421020b01100400d10000b460103140c001406142511640041b00310042e0555203842c0071551012018201e0752601e040104070700c819940e6802000303140741444001500c170001c00404001404201569644072107405185040c041d040c8040507040e2401418241105070740b0380c0b40d0620f500d0403030350305260420350718a00d543e11600510200000c507500030800018007003070421006155019140c00c8407500750040d0b0300142c4d0404441c44200701c001582101c440200400e150703502800205201805c0b5400c20741c2260f8415007158011552903011403001b0500f40308082d558944400c004d6a404010401c1d890b08541c4040180624040217100d01c1c4000781001d0080740c01e015284485007200d08a840c51500d440580703407290814184201e0350f10440c03419191181c070500415004581500c44404d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 266338300 1250 266337050 266337061
    0x8010219050703030b151b06091905120304050703060501090b010206060103050924150a0803040e0a0204050d030e03010c1b0b040303020f040b0a0207050a0b0a080603010609020f1b0a0308 82
    0xa80b80c000a00980616680e22480c0c00e050725007a48482c0058443c00075950f0f01c460760310402c0031603400d0582440d816840901004000d90300080e005041007d011620719010000d481d0403860f1005038200354082c03800c0841072008018000680e1003e5074400c410500c000da0700c460b40d030000c039a865440035005034001c0022030b0b000d501a620441d044412441074680c0b426000c81e4005400081c0ea40040000e01c0d41c0007045034601c29020b00304580312048070600011441e01c0c1c1000c1d603d0140740030b5401c032540702c1000320300c5002003541100c0017004094036803648904d0a04001d010b9450741d8010900950074a03c01c0004c0a104d000340d140d41c5c40e1820f04111041d80262528904110001c3c01201032590800001d12903000300e00c0600020886401140d5507914400002030400c1150350040f0301810060742c040c8080c0104c54155807000318a0310308900c141d03803801c002078003500c265403220b0070355480041c80e030b481c1d03a285400815201e46868080e501c05005002807aa170f540140c50007500044940000c5203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 266339550 1250 266338300 266338307
    0xf080109052203090909030804050111130b090a15080a0f0605130f02090d20150a0302090f060408030d11040602062202030105100e09011e23040303090203060108010219 74
    0xc000c2e5010b0b01c1c0218115031078102d40021034801c0d031000c1d001300e02520300300810003500340202480d0001880d1054108170404540608225050041a2049001190302c061a4480007100d800429903052010400e9031441c070080c00142d41070321f00226640c2000071325007c0d81d400303000d004102c03000034200e0000c180c1e070080c50000410140e0600e103490380e004c01010b2010398440040b801c040340200070091060003034121000c0d24020710b00d0810300036400500111144824081901d045d92540d08003d40e80780002c0000982e4201d14640315075008030003140102d80294004080e0002030601701003000004810080030006004910071301c0c0040e40250006043c1e564602440c450031030407521903803000c0055900080c2540d0040300e1600c440c0c620b801c006c01042c84448081d580186008008000c0c184907c0c0d50351454040300f9682041054481112405122040c0c01002c400c590714a002d030f000707042510b4020040c00c0c0403042070f403117441b032000046210340062007102c14202021140540554024601b40c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 266340800 1250 266339550 266339611
    0xf0424140c0106170d020d020d020318030c0a06050433031503150b0f2e090e090c012a0b040c0b1602040518030f0c0705030d0f08010905 60
    0x241c10a548500b00044c5080c8020f426044990b100d0001d0020f41c1d5005c2d800134506500c4161160031903000c0344110301c0c03854000c82200c1000e500c160f450240b110042e004640340284030410960400c94840000a01c00e5008029000341d940c041c40d81c0405032048034100301e0101e135001203800c8160460405e01c0c40c0380c0c0642d01c881c020001e80f0780b14117419543ea841b03000300ca1402c916444034050301c1b0800440355107444040055426012208040d4012003140c1e16140a000456034000c40e802105102c40d42034010321484006058040c00c034400d07480c0ca901183d4585c9902c08d42580031491203000031f10540c0301c080502c4440050003500d4100404207031140000484003038000d0343c000c030180101042c18031417000100f080e840c0c20320151480e444c0f184140070032150010042e911224404803004600100442210741011043c0f50f0503072100000800141401210f5000c540d040c4118243d00e502c076600b0550300741a140305c545a0b00c10f9070707982d00501030503035100721048501e500740002c0c05c51080c0d581480740d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 266342050 1250 266340800 266340817
    0x30a021005270106050411041202010c050f010e0a0218010614070309121b23040221161218060903181d010506040e060105030a0b03030f042414 63
    0xc428410100d0781481c0e42c29840014403407565111071081c01181070071701035001080402c1400c00c2c44e15240900140c02c00010040003410454110604030034040b00300106003070b6070000802000302192498145603208100b0f1030403401014007801c41d5007055002c2d11107904030b030301c3ca8803030b00100380e08912030100680c410b00d811001e010034941e01241c0501c0e04210702400750703c5080180740e250303403020b8005011030040d4000b6140c2c54017030f40521481d158140005045a00a0350003503141c2d000006078a00101414001e5810000c0074001c100000502a80004203140d050302c540c2c10b6550510180010f840d002d210201480b03a448041c04000f58882d8070224040d802842c01400d4050752800c0c044640c1752582c4660006080c45000d6226150034002260043c501102d011340b425180c2546103148510041015062010100024142d54103a0700640d41503040241560340e00c4036a059020100d805c039000d80b600c0c11a5202440301594501c540d1881ca4500f50b0302c56030110703a80b4000c80350071540603008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 266343300 1250 266342050 266342071
    0x2031903090e04141501180c0f050702010e0904120f050703021506060c0601090501051002010e070504110d0204030f060e0d080a1e05010306091703040b040204150816030b0108030a021005 82
    0x90084d900304103100940c0c80d100741c0711100141354548503081600448605c0d43d6010f0301c1c070b07080074032212603001009040140040c2c2005130b142c41e41800140c445510340c0007134541081d8a50108400c0000c1c115501024000c2911a25462905510125502e024078103004001d64460441c01d207101e003840009943c4620000d00040c50300000c011083e040c0030702a84140c4c11745072580d0040c01145080202d45054041500c000c001c1e07405540300b51641c2d44118415280180d40e54a052800d00a40404441d22055403c0041d541c43c4e81d03030301d003001c0109140802500e5691514160160700c40000c030b91062500d04980e24001c1c541c0329420180001d10307401103c00030340303039042144c440200d00500541d4021405031900181c0c03400f15007400c1c1c20403001000e80f22075890080041000107024080f040341c01c160140c400041d05040e007101a141028150484060b0b881180500900a0005081201902e101d0705004049998880034103036240100c904050160b04a002c0e03035201160f4551040f0ba000d0032050303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 266344550 1250 266343300 266343323
    0x1218190e01060c0f050d0201320115050f0406080a0617060a1a0301140402040f0e0706050c01020d050129160204020c01060b19080f04020d060203060109051c02031903090e04 76
    0x40d00d2514000306c6109040141c0d4542c20040d07140768840f45000e00441d501900250f55000c080301110621005001d88a010755425142c210003600c190203aa080d00b520303d02c1c40350340e180c442e503002e80509411030381c0601c0281888408150460f0782100958041801c0001701130703039101d02103420701500c401580069801c269003079000060380c00340600714904580744690100c6082600610050307641200300c401141d81011800c8800d09c000041c2e0708203c0320307246032140d11a65901c0000c2d0181c410000011181c0707041400100b60104441482d601401240d40c04010468041180c404e10b40100704901d20105c1d82242c02c0c001500b000d800411184204100000d030f0562542c11500302d5410903280382594244104130414060b81103419640c0240050b8107016451a00c2d1780050406800d90b030380100104e401201040580e40107101c01005803600400103440e1914131014090910320b0400241e100c1d10030008107000c00703405505e13030517541500342d65210030403030a083c6c40040c14100900304542001303042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 266345800 1250 266344550 266344553
    0x4050604061b020a0b0403030e0306040b160903170306040b01080c09280b0a0f08090a06091e030e03190b0f0403020a0803070e09090303090714031218190e01060c0f 72
    0x2200242c82c10010050700c6e40e0840c1001005040c584511f135000b41c1c02501440081110000002e80c00134441300c850068042c0c3d4541211580a42d90009068204a0511100c400244000380d4031a00c2c09403000c00a021015004580151b0241d441c2204072800b00140041b0b800c001d1080070030420142005652106540311408010038680d202e404900c07408200d00200c1544401582c440e01a9490500c1060170951002c5480f80c4240030f000384155600c208134010407d5000256032241959025044103100c1810301a01c0d032080c1c941c815101e0300030315170350001032805600c1024005070054000c071255910305100001c05100a8401d60035403243d003000400141c00c40b8001c5200707108036524100580c1102d004e000d641100903151a103984c00c00e20400007500710002d034920071142040c52120f1105084008070381403044480c0d10000303007640010464242c04008814100491003502c100d2841010761440e5a0302c18031600070300151416000040081ca807055103a401e0040c0207440b600040c8606 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 266347050 1250 266345800 266345809
    0x90b03010b1c06110c0c0402131d0f011e18090c17010f0b09060405070e101d040c0f0507080f0c0c21030a080c040929030304050604061b02 61
    0x10781e0981068456030b0701c03908200003071401104c040000804c00b0904180000107802c0c0c80d0000e052034180076941c0807962000d0940120040d00040500f4a03103040d00c16201c1451650194080300e444041c0300011000150404e800403035428103240039052410880c0c1031088002608954070703100c60207240c40300e000c007002c1007072074247c58010620303181c40c031015008509107203003500c0d80044104541490504000c04030f07142c40fa401c550100c2c00310b0340007801e660390940540e2183d8000440356041070745c903900251156000f0300d40b0480d4010751580d0101c0c00c000324041005503000750620200040504c60850300e501d001d0130190080912480c407050030a40075421412854000c403055180b50341c0b16100303a0545081a086101641b0186401c40041030a090b44075580ca02c602d482001c108170b221400a6544208c100030398028008001c014004c03030198050400040f409101800d0a103844020b650400e46400002c6600b1264068482804c00c1d140c0030b029540d02040009450140201007040c1d4010707540c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 266348300 1250 266347050 266347069
    0x17040c0b120103060b03030a09090914010f02090901120c030206030405030d29030127050703051006051009030b0c0904090213020a1b0f060209030f010204030302010506010e19090b03010b 82
    0xc00c980441d14540c518188401921500d080f00c9000350000c00007070034810350005000003a500720080204007040140b51900e08020340ca1010b000a5103411168021040310740c0040042503001c03100c5d0f81b03036640c846201038110580c112004011607c042e0040005041100295038814059416242040218500c18003590100c0300b503600c004c40c034040b404500d4960344000c851000c20540080002c5003602c2e148400141d206805074072192002649481044402c01102d00599480300a68540700c1500d461000500400c1c0180da2042e000310b034061601500c100c1c0e80108403a0030400303807905925079070940d40e0542e201c10740b07640d046601c83c02100301603104e04070680b0200c24104401652504207200c014006c0e8003850b408070401c540c520b8801d0105140101c844800c13500580b0059540e40340b000000e1901c1c4002e200c0c0350480d40041000018181c0651103188a01400c2c4c0303816006a80f140d0400440c400e200341e0040b004411100c05002d0000194480e400b8481c018000080c2c01401d900000e88020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 266349550 1250 266348300 266348317
    0xa0c03110a110909010509280213090b071e120902060309060a050106090803040b09040b0a03080903070b03060d12052115010e06190e06030403030f0506060a17040c0b 73
    0x40c1840b02c59aa081c016080d6900c180090000c1243e030500301303034050700d66903003000056500d03c08000d44a2011f0407050b50f00307441c41e802440e00740f0484880240748098600c0c0c0805a501001e0000003903280c500501160031070402c02200d08104039440b06080d208000e40d640d5162805039506008001030f1030305001140100c1101c0010b01c06407900600704825100143c00080401210160421426200106403001c0d070700100005600c0d089584086001840d5291059a21040b0141c0c0001400a100c0042071101e901341c095690540d01c8160307480451200351042604000844402c4002c1400515440c20101180c80c0640c41d00c4030100e601c0c134030a015400d40d007080340b4045080c001b010340c040046846814082c00c01c035844407050b40000e252801081e814400d840002c000720f040081c03140001d040e1819009000c541c50742843c1c18010001c100d03941180542d20b00c0c05020035554a400410380d84030104a42d40e20384a07544442c8480351b81d29000d08102d400e1116400041032800c58040a88001c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 266350800 1250 266349550 266349563
    0x71e0f03050c03100c0207050919050414070b0f090609040605030d120501080601060c080d0b0a1d0a0b0321091003200307050909180604081803120a0c03110a 69
    0x4518400405041407002c100042580c0d1905c4d168040003030b00483d00c6803ca4000f03ca40700c07035540c6d0710120780e6035107034180400c0303480140742400b08401c1240000b4842960000d510480356032984451040b582449042c020104940707040c0052a11450032000402030040060408107080380d0301c2000c2441d000c1c480d0040b40114820703255580c260b42440c480c076030041036a400200714035490440040c00994481002406503480060308502440c050380005180c02c40103442c141d407840d40c42000064540c0b084520300c02c0007203054040740c640e42c010301070108440c400401a08030803102c004a1180320408200032040620148000005030b65000b07400c202c8d0400646001c2040e0502136008400c400314803818400d071000500a000c0c00c103500c81c05540301201d00b81d4204117191070340c0da07882c1d000c407101d00c00980c00e0b07110b070350304000400c40c083d0060160016a0098045040141002c1642310b5042e144082e00140042c058000c501d4442c074400e480e00b50007802d0805032500000203290401d04c2524041c1c80380c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 266352050 1250 266350800 266350813
    0x10206040f0203012c19020d110117010e0a3b01090f05010b0102121201030605070903060f140a06081b0f03060403050319050601021b0301240f08010c02071e0f0305 72
    0x611000d1003010310211403c4521b040c034108aa0010300403d01c1c1540141010503808041c500f81c0c0d008000c0e01694004000c5884030f503681d100309002004401710340d41310030b040c00d000780100b500e241414911729580702c1034950048444020f988a00340f5a0801c4205d581e50f4230b0315101c4002c19080e030603c0490502a03800466207d001e00f0004e032421444449000c0300b8003003000070084807840480c500d410340e41e201e8400728403525401c80403180004940c1016111900e000891a82205a544007548900e0075074401c0e94640e54444011b17017115014401ca10081d00b01019002010001101414408800400c0c80045001580100345091407c0324101c0105d80000144000c1c0409007090244804c000ca40a102e6841c14000007901c500701903284400c15541000f06000a550039000160f01c0b010300106107001c20800c00345124041d0051065100310b522210010505031f406005a071220410768004040301392406010a01c019a4103400403252014024041085003941c8040700065024074020f011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 266353300 1250 266352050 266352131
    0xa06050d230a050a0212090604020a080f0a03120f0204081b09010b1b0a061a0f0406030803010b0304080d020a091410080c07020307030b0103030807120b010206040f020301 75
    0x300c030386200360289107150300d0100c40400d01c01ca101c425400000702e100803990751940c440c150b0184c066120007030901041070042100c4103400050b040d2081e4001c80c1c076044580c2d521409a515015000c1130b01905421041132030700421700404404810f11030040b0002121222040e2580072604641c01c0307a91144c1080d201c0148000c4204030980340800d0844500480d54904104110584946522524101249000b00c807118005105a0000d02d81000052100848010085100d56004c1555034820115500081c01d83c0c03c1030301c92001540e5001031031b2491a400e000d0360a413a43c0005004540c81e5400b007140d00c8003070710b0600142600000f00d4581c210250704210184c3c06500c038007807a46024038020040040f0705a40f01864a4004101058846d81c812440c0007003410195503030809440072902400000070154840015071240c14580e85100e2000700155202c801e0700c0300034000354010307805080420301080042040c0380506100400000c0e10b00d4510048045c00300403000c50b1650301d1100e082510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 266354550 1250 266353300 266353327
    0x70506070606080f0d02210d0603060b0a120f110a03080c070509070512070318050303010b0a03111611120d030902010f02030a02060f04080702150310050f100807020304050a0605 78
    0x18400c8110f94054517080d18000030095a0340039260b4038450602074020340140d41f04400b42202d500e0a07001000384541912400c110f030140c242e0403032650003441e0750480014039400f13000b548101960b02182c00340d001910746c1c49415402820030881580316480900010000d0400002402106481406070141ca1b203084c0c2000145c0030010021001c0c0941000400703030a9081210041d401102410001040c102004051101001d144402882440004004508105807001509040000303170740c144004903426005a110b0702135141c50305e000d4244c008802c400920040002220074202903d165503e0341505111440c00564280d00c0b00440e82e5100d4100035540d20031207131580c0e5240342c0000c0d8680f221884c4021755900700113014800001543e800308040000e003e0490300c080d900102450fa00820a0154003038a070710503164030840e0041c2a10000b1030741004640c050420000034000f40d14100c5000d07003603070464801041c010850000f0080070038160b03107041c96580581503551b1100d80f5003610500c0385 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 266355800 1250 266354550 266354563
    0x1120507031116051504030c06110f040303090e010f0f06030506010314040609020102150717060303090901030b01180605010e040c030f1506110114280f0207050607090e0c090307050607060608 84
    0x15446140601704102c046508023400d4408641c3c80311000880ea540c010021805000e0880024180800001d0010500d940020b05d101502c010151001440c1da035100c1000c0c01c100305116013049580a082e081001c1402a0b0015900c418181408a0b45105088102c10074820458040380c00b036640b450000150350741041085442004031200a40324240303000040c01049286034000000e4a88400065107a1000e03c1502d45461000d0b060003819616450510b200c400240209003100320b400e141c20075284480d006510403140e042e100c00f884141781c101032001600117500d4607c1495119484070401c11440d204584079020707007110400f1542d0600303030b0041180701c0020602c030850781498207060a113640c1c6201c0c43d0300140c0f00c1d48401c881c0d41000d15140000e45859504000552030074804000c184050740050003018032503401d462a030b0703445010644030b0005078020340344000c03400c0c00080c1d800c104034002808000c2c07000302200c0007107503101c0028002d41c0c041c26086416981769242001090000c1280 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 266357050 1250 266355800 266355823
    0xa170f07150c172418010503060a020720010e030a0c211e020112111e0c060a050604180f05010b0a08030a03050411041b021006050112050703111605 65
    0x1440f018000380f2050028980c00b801080a24480c2264110940601d009540c007510010340b00e5410350352401800d41508500b44107040c001e0003030000290f98040d032031003201c2c00260700c40d844030b04602c0d4501c0034804642002e08c595050044500c1e444001d81e804000034210381c0e200d06015203529041150542d052a085c0d00300c130000f00c0c8080e06000000b01e0210f580e030301c50300281c074284641d00241c2c00120360360004000645142480e04140445011034a070040c41c84500b900382c1c41001001240c085482c0d0300c5a00d00402d0380fa000140410081c1c0003940010350070a10041c0042005000005010701d520310648040744c034034501794500420014280141d00104c8000c0310701c00e18061910300d01588904c80c1c0c20928040607900e0001904100b00c0321510340c5040d00140040141100d8510701403190b40c885988240580304401c196546010300d400b49030161034040e034840c1c071042604800c1101a0101408180a0603295941518405030001c044c6c0902100d4129555001070142001818003114058 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 266358300 1250 266357050 266357057
    0x3070e1e010311120a0902030c060a020109170a02030318070906091509271e0308100b0406090915030b0c0301090f02270103060509090a060f0c020a170f07150c 70
    0x46001c0350028032819661182d035001c80842c0346d155030304c002030400d581442d48a1344080c011503188034513a4154005980f60340310b21940c00a050a0007001e00c142d01a240d090070040e401040018142c0c2107214500d4601c034404011148401d4894034601b0036038140c0c0e080034282c956202202a00c0303580d03000c1c014000780301d0440100010061031088031000e8005003c2d400c0070b201c40c040a24200102ca04c20158171711390804c078000d1008580c1ca40101000c800b41c880d5081c00d1030100020406c4211407040350212019501c404210501c1d005d8910050841c00e461808200d40114000002c10402d41529200b0341030018000e070b81e98100a40c0508440180d406201250701c14011501154080300d41011030280c80d0103080740c507000003401240980300503041541c000c05110103206000000084081800f8030540092000840c450840350803a00318420200060307106030500780200c1e807415100382030880c17400c7c191440c03c5c0d0070303400c10f0a650784041004ca0310007090500c045044c0340781d44190502000f007841c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 266359550 1250 266358300 266358307
    0xf1f080706030e061e0c0f0403080a0e0f04270f0b0a021c02090604060c020f0a030b0601030b1f051e0307020d11010b1503070504180c02070b070b0c03070e1e010311 72
    0x26505003071748001404d1142d05900021100540070040007604e000b560700550710355a0359034410b4001d00041040314414003440801906403024602400b40a1519001c40c851045440c14805140070007003a034a425502541442103100228200704403007481800315007000740c0e942c0440600c6007100208020001c99851050140714003a80e03651045074210303107091400c1001d00741680005846c1443c2103400310f03885058100004104613000d4169807242100b44c80c10030030100e01c803081c40038011503075000f0586400403030003646005000348003400c082482e40c030b1a042c1e12046818010701030340c0195070f0000540c0c00000a40d1a003640a0001005429000c000f4003111001401207985111544a82130310802d0101c000b6003214072038802d48000702070018811459440441203140104400c00801006010340070010031a01d50100481f03203143e40c0115602e1040d940c02c9004042604003406a03800c014640b282648540d46941c800008804070b00f240220140b0908005001c4482c14640c039015a941031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 266360800 1250 266359550 266359591
    0x7030e0106121407060e06031e04260c060610030603020307030804030b07092106020f121611030d09030314070f080708160c2901060206010602060f1f080706030e06 72
    0x7a2441c03546c00c3e004d441180e01d0b52070b043c074003090104446c903010401280078400c00042c0582000c020b120340c207442c0658400d2403102c5804951620801400404661280000c540a0300f0b1042820b088200c01e845d00107030701038496002070309044541d8802d4402c0381c4081002d1007400303001c26280790406687c3c00d258000d2413424544980002c03402200c00d100030071209803001030204070b80403100303071b0840540b580e59182c2a120404401c148280d031b480c1043c213075400302d90521038090344002650302907002c001e608100e000c140040c05821001c0e0101c040640b190464200c10a070003200300e0055410b40c84100f2a9070069038002c0c1000b40080c041400c20644006005455090240c00c080a900324644207202c11440d09013140f07101308502100c40c490400040c039504d140408100b0700d050311026400da40c0c0c9070340c0c1d549080341d0ba010282d44c140340807403204c0042003440311038018030014504407240b84d4411035501d030310140c02d1403e141c0c090f01c00b02e0341740d11110b55000c906001c045d9000e440301086049403a170b903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 266362050 1250 266360800 266360807
    0xb10030f1e33020708090d060b040f020304060c03090809190f060c030f020c060301180b03100b190b1801021f0204060909090f02060307030e010612140706 68
    0x406006080d100341507215550604070000c5401006030080c0382c08844031601c40140108424480714028502000140030100ea0100d0084440d640c0d00213000301d0800e9109030411400201c03075401122030f2076442280c084076841e00d025416050300785440048e03c134506030030714609580085140f40d0826203450140b80002d45d0081c150390701420142c80c004080d1001c0b00c80c42d2000059500801c0400f4071070350000600650144510300346e40c1c400d07035030200020041942a070751740c0c0729080b2881d40303c181400103100072000d24194a20340e40b00040b000c20f1000c0f05401203802c04c07440b100c0c0131040c5520782846102070706180c11407404003044d00c0c1a02c2ca00341c1c078000e40c0f40d1940c05040300034501204421214982c680c420081d80c1d808005003207001211210f40c8003072000a6202d482000080b410307100c0000354428040c1b041004054110851071140340da643d0030804258401813642c420305580701c00010024409200d40d101904070044c0080038103419041c010541d02d5114050000390380035110a2003002d50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 266363300 1250 266362050 266362073
    0x120a0f2009060a03030f090302090c0901111c1d060a1701050303070b0609070c0b070c060c0c1e03030222090608161715042a0501050a0e040908070c030b1003 69
    0x800d85040844110200030442c0c1f0412168000703540b05040a06102009140301e00070501190262104209010020710282d00c40081426000c1c80e2100402c0303406030300f401100441c2080c06000d214104104404d0300007850780d00021518000240c1146010080301c0700720305030718054801100114282000c580d00c0e0130307082e0001400c80f400750040340081501207000710241c0c1507044d4042c017444040d2410f02da0040c90320000e00c1040d9441c03401c0110b0305901c43d001e003014190440d08000c020942180120000c400c0c1ea100304030845c10581d08004100740c000240d40a001c00b2220b24103442907080c9443e0014050707420740d41120419407c640d140a0a55200142e031400722045524a40030255405407400d003851000f0b01ca40e019042030308108010001c0d800500201003c2d604400c801c925103241080d82000428050346000c030784100001c180d910300031a444c4024517001400450a54010350310b007041078100c0401205c11200020f018410031044c2240340d54025101000024118030310780b62070844c1e40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 266364550 1250 266363300 266363303
    0x170108070b0706090b01150225030206070c0506030702010902010e0303040b0910022a030613020603190e1c080a050c0301050d080c0129010503090705120a0f2009060a03 74
    0x400010b02e032041103643d81015502ca41c02c02520f12903580d44400d100d9041c00000103440040c01000d141142001880240300554241500010103050445c0d00340b110a5008440c141c80000b6204400580340e070380c1c00000c1d4072821481c3d00109e101c0b4917910000d01003080d0000a10702c242c000f1301040c4204542c0f141034400481d411600c01841034180e44040e802c100b455106072072080582c80c1d82201c150601d0030f41060341402a0203c40043d42c410032070f142b44a03090103009602100c00c10210f4080300780c40701ca0710191021294005190350351400c1c21440c1049400842801441d03c0c2c0020301c0c0141c11407038150740085c10724800c0c00710b40303400c03040c1d5007092005001c2d0390720901c09201644148484403058880126818008010b012041920303118031030a242419942404451800140ca500c10425a405842001300a01400c1e00f003100b000341900398000c42090070720608005030007203860001100701803806180305c0ca04242c031340c010102c5801e01522101d4040c05010b414883c46803036081118080b603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 266365800 1250 266364550 266364569
    0x1d030903102f07050d0924020604060218130e010b06130b0708120a050a0f1a090705160308090709090b1303051303081c0b0a15090905150117010807 65
    0x3001c0702c403180b0380c2c500600700040c241d445541c4919411641000031241605d58085000c405000710011016148061041400058100708045030001e90181c01815481d09290100140c2004120108045a0030044a502040d0700c0343c2c1007460040d070038480d04800e0481901d0039440c0500e845d44101481c621b600c200600388900189041c14031a6010995648182c003403070b00b20040c104220081c0c0a05020358920088602c0c15102c0c1c030b11401c6502c0742e003030030040c018580f844000c3c1d11410403075961230003000d0078103000041094074003032024511040c1c291440703030300e4540403400c1c0080c0680c54610311380c01170b00c2c4d00c600c0c04204502045609283c80e40c481e5050105100c80702c8103140884460290040000e405444164088200051a8040c1c0860704424182101006403141c803201a030303101e08092030300520107420a0041302c5555455004d600440c1c140001207a640b140c07030000300c2c0c000b1a03a503070201e40e015042215a6034460070b072400d00c00300c400383c10100f94180981c07162560002d00c9000e01c00f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 266366906 1106 266365800 266365871
    0x60504140403120b211209180402040e030a050c0d0e060f030604062c06040912080403050903102a0e1002011b17100608010306020309011d03090310 65
    0x811a0042c500c8e12801080034251076055406801a80c2090700c81c1400c43d070f484420801041241c00e41c3d555544c1d2640c214080d00d0070010245585010080111051084c030b9031080306441041c11071a840c42c0c0d6907180c100c0080c000b0010b917444070360050322800c01c4508440400b00361000058200d20f542d40180d40e403200b00403c81c0e2000000811040084003401d91051040d03004d2580f1600c68185249400d401100007868401c102c900108000e48406180031a98840f0103e0a01d510740b5101800c80ca000810020704280b0140103000e01562a4845944180f4801d420032082c00c1c640780c034085410030340c1d1040286084100505490380a1809020800b40f400001d81c0800710b40c0f19569101041c0d0a540e111800ba6001078020400c035925120b07145441c044062030308032460042401103548000c4002810f0601c2c034002842840585001c8408907440c2042000301d01c5501c2c40c4010041 = true := by decide +kernel

theorem cover : BRFrame.Cov 266187050 266366906 := by
  have h0 := BRFrame.cov_init 266187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 266187050 ≤ n) (h2 : n < 266366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
