-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2744
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:36:55.731106+00:00
-- url     : https://prove2.me/submissions/a47211c6-2d2a-49c8-8166-c17279a03db5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 493345323 ≤ n < 493525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 493346573 1250 493345323 493345351
    0x20a030219050c0409230606062506090c1814010312210e01140f150f1f030513082d07061a0117070c020604050307060e1903020901030308 61
    0xf01d41c5075031141d07140b8140541c0c1d8041c504580c261943d40c0058040c00c40210a40151040010075201d5400721603070a0300c840e00150121541a00240c42c5403200140201407034100380301c40d024040c1f03002d113990541d1000b80304100c50782420041a0f003120313000e500700b080444140d00100702003280d00822101c0c80d4554208480441c50106414054011070004848050307502c1c03550140d0703e41e09104a941062009290070f005060020411406d000c1c000c0421514520300010072440f5125180d91080345500a03202c40c01c4c1c0390b01c0d090300070320250000c0c6420000071f151800180030392a081d8407042c6541c2d00f0000343c0e80b5103160f05c0d980d0500300801094284028511440310400d201803000141441c0f4010701d00007480e40555281c01500d00240c00999040003043c0c0d030011074140011030019007015250a1501450f01c29101198040c069a40310039814083c0e042e000a07955084020080c111204403402034800c40c000300000035039803a80c000a500401c81c0801400003900a044007900409840700600c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 493347823 1250 493346573 493346593
    0x3070b010e0c180f03121605120702010c20060d020304060c091215020c070b07050c0102010c08150103240302030118050604080a020709061d0609010b09040f02090a080f0607020a03021905 82
    0x100f82940b00407c03030894001c000405c0c3c0c00703125043c0881100d11900a80080c42d140681e00003e00c12400c0b00c1001e804910303200710807440407582d115072000c50400680250b85132840131b01f03060025082103509880090030248204c840c24400c02036101a100c590f60702d54000407250300c407001e4100714042c000c8506942006414581c8404101c0c6a006000e141a900c1d60380341c491600c141001031050416040d681016a10b03103070380c0d4004814641c0720345420900510940c0b1140101c02912101c4001c1002a114040b140c400752030010304001924000e800074003a0441418502500343e14200e009481504200c0c0410005050b2000905405001d48121800307140c8440038441103656540c0038110107081c4207036400b140c500440440d54080d070112512084c0d9031500c6000c14040c45003040091040742d5a84400114000303940c19101040000340c4005d0410341c99000050352200d6006806a40d4170820b030009440e980b000a007054000d0380341e40a011600104000d54050602e000400c480b1800b9010a80c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 493349073 1250 493347823 493347853
    0x20702031504050a120302030f070e040b190f170309090403140301061e02031309020a0c08030108061005031f0c0c0209041a090109050a0b07050c03070b010e0c180f03 73
    0x242d00680c01100909502c030789901e4001c641c0e4441113403401c00d0500520030094020809000f2907408003ca0503d07254064880c400030700140a0141d85990006081303170b100c2c2041102d4030300003041c1c03540c2d42c440c181250307141c010b841c0401c0c0c0d071419a003040380d0040020341454200070b840385d40c015110741407010624100c3d404861150700244c00002c009582079200341c400020f40182d030700010020b40040c40c90410f121008441d140a180600d035251900050341c5240300b8881c280910b1702070f80013420039860307584500306c5903100c02d4203440b280d584200c2d03450081500c0c64040382d82c1e02d8030442401d040700300205840c40b91018101c0b40400f6828000700400c038a0150321005916445681701b01c440052070b0802501305c40c41c1c54005428028543e240541c40000110f0000d46400d01c903402c01804486c90303403010b8003140c0d0b80c81508241c801034080410795208000c02c0640700c90580300345e07501881d540d607110509451180070305030303104408502d507680104203400c22610148040c14080c00741d0ba45000640e80e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 493350323 1250 493349073 493349113
    0xc09020906040e0a0533220f02070213020a091206020721020d0f091a07051501090c0c120503060d0b0115080109060b094e0109080d02070203 62
    0x741200b036030b8079a020002c443c6142142031b1400207101d04105841c2110701d54840210004440060142010482040001a040c07940d0106066000400e01241c04241740a9000e5006444128010340c07203503c81602c41d201e5402503910300542d903607603148460b1030269821410400c600064030002d83c20092500810061980003420002c20313881441d125065100081c5802d01c2201d08030100004540810241684640010119512400305111501c0b0b920340d84140c9205030100104244160220101d003604254081412150420000c2201002084003950402807031240102502c0407640c018400074010400345400c400c1c09042072030311001c1d17551101200b01080c0c02408551f044140600300c0150f02602c610301500d42c0314018400145416244e07403c030b001d50204140318000c40407a601c114403a01e085003507a82c00c840701c050070032a2501d804500340426510701000da004990700c0c9440e071315030500401d4034661340400a9850100540c0c0418000d42104400300c3c5e00d809410064404c003070304216 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 493351573 1250 493350323 493350331
    0x1506030605040b10050907121509090327060309062309010b040e0a03030e19031d03030c150601090f0e010e1e06010804210804120c0c09020906040e 65
    0x4030004460500d81071203c0d550100404000e40858901428006900c811480365002030041c00c10070b100421640a18000d414281000302d2182109800000c88202c260040c044a60083e1126814030000464883c010550b482141642034040201008000c2c440e40c04500c0701401b44130001031100306501c0510205600580f25110010007505018030500c00f8403800030003c500f00e6003000514540c1c00441d0715664500009428541d0341c0900711074600e03092025000c000c000f560241031441c20761502802112071020307044c181c0441454a4803150a001040744d02400741c80e0000c19040b941c6c0040c81407a240b00411281c10451103510000c1c66907070141c0d002014020070b0407294240d60400d01c500f402c1200c020300341c0e0b42d032070400b200e1818003000046009410250a20348618240e03100d00f810031202c0021030401981d01c04481d00d054015500c452994003640c0314013502c104c51250341c04100c0d1040d0402c903000e0060b03490700c041003106141c603034028911010050031641c1000c0c3d4440f4141070f0404115 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 493352823 1250 493351573 493351583
    0x11805010807201e1617120c0102040306200d0509010f1103061003050606030f060f06042d080316020d0503070821040c0603020c01061520010605010e0d150603 70
    0x5070324402c1101d203103001c0024184da10028146141e04100480800100d03205030118088200300e01c200d500c9080c0700e00e400050400d4480d80e980c400141300c240c001d6100f0300c0142c075520701d0680300035502d83e98540080c4011409021503810144541103110003403601a0004407559030b20350400b02c0540503405420410442c00022940382e14040c0244892070040020107000c06141030100400c80d80c0d84e1007626040b81380c01d07482540300d0f926080804c485030800b00810754001808540041d0f0343c01c220b10403030307402c45105055170030313880000d42041501c80781402000c8058200307116148404840c40072000615000618005114206c0d0b1141425a4404102a40c81100008510300510190807840c40c0c02990749941c0031052030700303442d900080c3c03107a40118000c26400003a0802c0341c2e4802d4021a010b002d407071400c0750383c101c0342c07034070151034074100c61500303041d0141510f11389a0441c2c040c0304505c1180c4042c0c407074031821040f0f442042070958200d0000c45501c4c10200602c1d008018502c203000c0550701c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 493354073 1250 493352823 493352833
    0x24120e06071d0603040c060c060b04060906080f0d0f030b06160b0601020609031c050c0c07090f1104030c0e040311060c0912030306010f1b14030702090601180501080720 74
    0x2a10710148000480e02d0705070700861081040c0000075450301c0001c000c451061a0552482e11240b42c10405404801052039005080c41d401144040082d4002c6003141c141504403080280010034541e210000c0803184404184040c12108001d80650000080c5a81c020b284515212165000c05000204848107031082c401c408200038065804100b032a0300014550011414203d02c1580301e040c03110070500300102c40361503101152020000c0410744546003001c001b91307882c1da621000e00800920007518070000d03007414003901180d2011002c0896041e6508040e001d441142003030000543d011000c1c000320200300780c1f0003809503040c5c1c0c2844401c0c0601940310740282c0e110407035404c012401141c0c00380860b030380d002002072120076138010160201840c07040c00d0880a1020341205000c80d160080300c082d05401800d0342c0c6002501010000303012080c8211070490f00e50720341d0401102c030590b4807100030300c000f51510002e01c01c540c001c0300980e6200e007052519551017014aa00080e0300203050705043c04a51007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 493355323 1250 493354073 493354097
    0xc030603201206091c030f09050124050310020a020a08160c05090f0a0c091203030617010204030b0103031d040612020a0602210708040305240124120e0607 68
    0x301c24102d0342c0c1a9141c0040501c0e0902e128000d8454140300c68074010350400a1040c5085406600421241c052030142000310b08000e0400c07502070003581400c8101c00001e50305201c02100d03c10112010354001500405070600316032141002580404254410b40c440c070301021000861720401448000841401c10303075480000e14181002c1483c0380c004c01c1c030429520b010010001103800d82c07a50f00950020000c500300f203c1d00010340b542d940380d821054941c56250700c000185a0150840005c0300d001c58172111790000c04100b050308038060b80c040209100c802c1e1004001080c400ca6003020303201e03404148140c07040b0750f001c00101194525804540080c440c44984029464815442401042035001900121a200d0b8200c021009829001136140d840801c070306050028440503603014552040440740350500841b402030340500c444880d071000c07503140400400d4030032a09a111624400303107450409100c5c030319002510f0554220117030711400c41d5109100c2e10507440401c0002d0140d00355449031101140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 493356573 1250 493355323 493355329
    0x9011b240605031212060a0b1801021b100815040510030203060601030525091e0f06180303050c0f0601180b01020a021c14030406090f060e0a090c03060320 68
    0x369444944690040344c136424a000c051012519030005844d03594046a40780c81c00101c001800d900118581c0a0104420302c036204042d40640001070260210340c1d0028000d003140d640c886000d680181c205001c1100d0f40c0b00e05d0f00401e1a5504080d1408d041e1640c4190070000c00c013104c0040302e103003114440d40782e41002035040511005400007020701c0d05000358a132203698142e4450392200e40c15843c180114143c00e03024030500c402c20150000b0048001c0f012969440c15600708100d00840b0340ba41c02400000403494082c1e0849040380400d406d09449541c035584007601c05410031644076089005e030709490b1405103828002d030784c0600070401143c029070810044880407204c04101ca281550b100c0080e040c0075a440340c1c412040da1035215002034040344a8a001041c2c6c02903820350544600c4041004590703650490315000036100300c2043e0700740041c0c0c0c40d10102c800015141250341c1091480209204007a81c90300010100d10150402190069a0340c0e41c011140340c0185c00510419510180f17241070386 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 493357823 1250 493356573 493356581
    0x3060610050a0525021c0f0201050c0313140f0303070c060807050405040e011401050f180718081f1b030b06040b040303030e1e031204020d020a080a030e010f020309011b24 75
    0x18007103886c64040c110581e21180c0900e0204400f13414400007003244107480000b001200e218590b044c5110241030341d510803103154407a401e0042445912840b07440c85081c1000000d482d1916007109201c41981d00e00380058640c800c0141c040403c20608100102d41610780d401641188183c14000103a00007203522401058481a00018810101c109041d1150781e5825061458a0524030044250f502c1e80d140c151644002212070400b04402820300045862011880078071000fa070a003034648003a4011206001c62f28000765440004020364003c4501078800d9011081508024100e6841c007a00ca0a0411141c1c00551007100065140c06070134500c1e6106108082c1c00700300c000402e440804420390100d4417409a6050a6070880e0050300003425940c072500e1000455030080d011a00041d12103450301d449400507401540418041c24100440f94410700b0400039002081d4003541c00c10783c07109c00440308200840c00a4600c03505120302000442c00306070b4488441d40c4814103035880440f601c0600b070166 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 493359073 1250 493357823 493357849
    0x50f01060603020f09400b04090f080904151404141302010c0606150f020f07050916200c0108010f0513020a031409160503060610050a052502 62
    0x9401400b0303e0f092045050261030035000c0440c1c0b80d01c04840c03079441c412119201b00c01c00b00d08000e900301d40e81500801b41c4038802611002c01509001d50200401840240c4008d501e00400e80c10b071000d03280c2c01141c509006800c030384000400108000c00b00980180400180f0380010980000300e1491011501d882d00c646c041703041746003140c0c25a40c901800040301c05081c03180081c1c180600e01d80441d00300162644200050703c40030101c15024440c04030f000f480101c0030101400544550305c01c69001e01c03070000d401c030200c1d20000c04a10155a8040e207900f0040143c0492106120180440d856504001d40c0408048402c0c0d400400c01400d0f540001010280c0c181d10020600c0005a000d1240791a00d010b150344040d0080e038050ba9400e4441401c400502501c031121080352107103001d111400d00045403850007403410f1000402c0084c0c541c070070075449101c1902c0c0507600941d44000300e0251402800604403500660600e40d00f45543c0300c20a1152148041500c0407190340b0003d02401c52500b006040302e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 493360323 1250 493359073 493359077
    0x309060f07051b240a030e19030c0212032701030e0109050a051608032209051003110105040503030d24090507090b0a0e09090c06070602070204060503060609150d0609050f010606 78
    0x40c8022040304103c58401d10400400701501e51700c80c2600c3e10b0003040390038000e102d0456480702c03100c849e0900600c900d12542c0228411142d03002d2080680c0e40c000309943c240c0386030902c500c0b01c104130756240401038076009003a5814981c4071402d0401b500d00a1040e10303a40c5000704041c01409055103001070a0006500c0c0420440b400c040c424041000008140c608001c0503140c00341400d07500c2c03841001103940c140d021100c4036040004100009600000351000c6900c5028600303a100391050054a0394040c50181580540c0103100d8038442c123946411200d0107000003a10042d034a02d000c8400c84042541d500070070034440c0ca43d010b100c24140e001c0b00000041c0b100310700341810215801c2c2e00074000060903814901c107012400120304000010301000031700540003002291f070b071079061900d94082d400c10071050b0311541c0707840741c0090700b82404036001c2e1186100a041d1449a0b541101d604c030b000f40c030a07e00701e402050507440708001030407510444c00c040d40914007c1160250808540c0e0035146c1a41100007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 493361573 1250 493360323 493360369
    0x3060a0608060106050702010c120e01020c01050a05090f0a030209070f0f0819090614090a050705181b0715020409180339030806210309060f07051b 65
    0xc1074500c0869030300d05440c100e10701140d4407411800126a880044107001e0512450f00002104a41d0007500303020704010f0a0b000d86000c045042c1c010b540c40d01422440b400490310411681615142175070340842d681100402900210ba00c940200d042c0c0841150024040f421150403040c200350000d144402c000c00d90f2418510320300d484d40440d04100e0114034802900360b112101c01f810050a50090900ca05160440740e4140c03801c5100c0f15520010f4200a4400380901500420903041061508200c9030f01c860811490342c642160a0340344150031402e010144505200da030300002c480311014030080c00c0610002d0307161803e003488142102d401c800c07140080980111100c0000380c228821882c41004060812075881e503644901c0c040c500340030134083e052101034041e0070400da00b01400c02d028243c15281e0401e8420118494400c1100840801050358410300088840f03140ca20010240105c0050700d03942484402d617039180c6004400d515400501c02c01c042040c29a0810000032071860524441c031070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 493362823 1250 493361573 493361579
    0x120f11060402010207090203340f080f1f080307030915080f0a021605070305011a03030315040f0b041b030b040b09011a04030203031306030f090213091119030203060a06 74
    0x203035985601d8446c0b89411500030002855850100341055903450045400f100c20805070042e261404043c20004008641702c11300c40504140708800d05031185404100e101400d0312110074a20740c51016004040c100c0341101c40c08502c0b02030610140141c5807107034480c48081401d10ccc800030041c80000ba201410011510100601d071000101c80c950405103140e40141d84039140044481b00d4001e00c88050001d104a0500008002055004207904000d191011135901c038000201070701e9201c00e030b505500c4055102c9940d8005d1a0950004910802c0d448000444001e10400b04044d18200c3c140d00007600c80261419500d990980501d8417101000c031810004140140e0018001d290103000740d100350400b132000302d5517000c0c4840455000e56002400c881d26110030f4140c0f180d00495601a040020742425030701c448040c142d0088071505540140310b010750321000502840100858130040e01d400c00d11000c06041030300c44000444d540040d400f5118035240c15801454035020024103982c10b100c0ca4200e00b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 493364073 1250 493362823 493362827
    0x2010b10080708040c080a030206090d0e060a1805040f090303321009021201030c0f05060f0a120c0201061e050a0b1b010212070f2d020703120f1106040201 68
    0x1d1036020020b400c1008442e02c982c02c20190300a001d4010807402d20500d10200c0a25400244980c0308035601c1045642d90041404212002d40309024600d070414414400d26800030302502401c41400c2c0703002e10341180c05940300001415074845445051000e96100b058105240d810b000303800c0c40b905524001000d108183c0304820703e284014114143c10740300b000c081258010f9541e1044000e01c112201952516951002054625001e100841c1c20304e5509030009540c40c4041ca40808070b500042010f814649210000c40f52a0f2008450204015400c4008500a0141c1c814144188111303400000c1260410031203900c041036221500021004500c0200855030b07426265109450481882c1901d4039152150b041c10f082c20071240c1e00c40e55002007a01e41400c81c0c0705021a128120a50b42d0981146410105036100d422038180144000c00204c03d01001540c3ca18500310440c82920407958120381e0b83c1c843c280d01c03400c1c0000c0000002c644112520107180c2c481151005008450058031490921b5400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 493365323 1250 493364073 493364087
    0x172d0f010b070602070804030c080706030621111f02010c0305040809040902060d0603060213050d020d060e070e01090b010212190815130605030f01060e04081e0a03020a02010b10 78
    0x10715081c448001119030400555405680d07919601c9000145c91340d0716843c210080c0c2089015a403075901c506c2c800020414440d000f850101c44011040007105000d140200108003030010042e501c441c01541002c40d56161804298000d002280e0740481c1f0261649000b4203440120b40003d0400d8208001d21001c2805201211907480c0100e600107800c01d050300c0070500e135000e245514048507142c5100042448150f8000745142c1c80c03120031040c48140c481042014403100442c001c0d4000d0b520300d0303000c0002540c070b03400328030025542e0044500940c2d4982000043d45800d80001940503218820620b1070f503010004070f1402059281e0703280c1060204030702808000c40603842c2c001004100800f040c243d003118000048811070141610401954100c08031011348070710b200b054007910607403038443c000032818442c000948441100d404a291203607154003221350024034410b003148802e00c40111200281100401e00d8a045460150b16488429000381c2180d01700300e8100c0c00744a07040244070107241e010f61 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 493366573 1250 493365323 493365329
    0xc01020d020c3607030b040501120305030f07050c2d030a210b06122a07030305180f06010e0108030a0f030f09080c0a140a080415172d0f01 61
    0x440107903a246101c101c43c814440c25010f05182d440f54424015902c0c0d02d90802030031000c1c103840502090345c0c4e0b4501ea8081e50407648029001035003e202082441c1c0d070b180c0d0310f5504440ca80c90300c42d0910750382c0c40743c06040c007040040040302a140426811943c0003000038803a81010022b0295081c5604010b02905481d2681c10140401c1d41ca1400100645400d5014030794021010700820740b1140707000360010814000f07681041500460004040c081101c2c0b04101044c08000d541650a0844c10390342a409444013403d80b07000c100c0740d01c0c800400710008012402e07140b0030a1005011651615080480c16601a0400d40c2990000c129038420681c000c60524100c0341540340008d0103c1c89848400d00510318000000c1580078000782507042d1250000703143e10081c0c0110b50008881009411255a5010080c0c00404413003041c0001c000001310800c1e12598030149090218181d40028100d21811a0454040525481c0880140b00303107a800c074080c0076155005040c0c031803c1d0401081c0280c072600144 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 493367823 1250 493366573 493366609
    0xe060402010c140f2d06010b04090e250e0c07050304060c0807020a0303020c0a060504080606090601090b0a0507110103090c0515130b070614040c1809140c01020d020c 73
    0x42d012070008030100404003a00340000f094540300d04000042c000b409008403171507002145d980c000c0340c55880011078458100c850000d800f500e068901201d80c0e02170144916081007d005107003281500030152082c004511008034584e103a41810005901c029142c0075210300305440007484004009a000411181501d00c6420b1019020049140154107881040c20081d00700044250000030540c00041d081100507007181c51644a0351903030002c075250700075403240348410340c03264011860b07131b0411580c01c5410031818074007580a1601c07503c80040e81d0340a020000c0019400050b004213000011500041406003403805000c420156204c19041080a0040f02d03c5007224501c0440c00200c1c060440e87c5c0c2074005025690459503690b1200c89a41100c0c2c2c0580d015424006a07001100b8541d18042c410707580844250126418a942042141d0340c0105400620740d444005002054443c0c0b078007140301920b0340003040785120840009040c045507525281c00d40d88004101003060b5200302d0725007880c42540c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 493369073 1250 493367823 493367843
    0xc171b0f0706091d060a0b0711101110051f0b0702180c03180f07060e13110d0c091a180307150302070c0504050705031839030706120e060402010c 64
    0x11000180e0381b403c15442500c81c0000022500c04011204580055045003110310034100317280300000385c4004481c000700c100542c100100400c190a815881a9000381c00061502c280030b0101034020000c0c1c1d010f030008002050045121000c518210007500c2c940c1c1e80707807107001b885400c0544002d90503000150061281441680031600d01c3d450801143c0001c050000848008a0347d401000d0480118105000d018164607681e40ca148803075801400864404170100c00d00e04054001c0b081c0050454000d0101048a0754100050f58484007440007861010103100941c0d4040d540c1c81d810b03403040c12482e4203000f80c1249030300300010404030f00f4a00280345503003809680c6084078500800401c2654001c240c0c058078110512610b1035200c0046e40c0310795469060392946030b48204509070f0722408072200c4940c1406185810403a210b611031600808850b01c40001c9041c1d224100003070a140c1c0c150040310018055422400b00300c11240504140042aa0050310072410300390002044298020f0002c1c00242c16 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 493370323 1250 493369073 493369081
    0x40204051003200415080108060c031317030a02030603010c021209060a030e0d0906020d030506151606060b090406060e061b1608061806070c171b0f0706091d 69
    0xc0030404040701c06203941c2c3d25500d40c3c95460110701600060074030700000c0c104600110302182c0003c0ca90340140409501281142e88e01c070064121141001001ca0314280504542c070400b181410207140240c03450100945ca9151083c2030500f142c00100780402103500c44c4080c03008001d004c0d000c035440d50300700343c40e0b09503520301810f0258017500c00c104003204140310b0307081c4480145501c40c00084c1510f400d0744c01e94075401e0b401a4220250380056410720780c000c80842038915102c0021009041c0e910400000c4c0c5208800d6072180c40442d03400c0c0c0d01107003011038005541100c91502c0d1040901401050400714406080800850594041d002100c0342c12008148440b014140400c010240c0010b03d00c1c00c502c055441d140d40c940c4410090f90b07607191148100707401c4c0c200b0000c045203062246400387c0da240d180c820340c0d072a15001441c641d40410031200c1c080242940b008031108000004000e00001483d011303038800a040e10b04501940110204100e69000f40804610841c0003116a41d0b81c0f012510780381c803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 493371573 1250 493370323 493370351
    0x60d0e01090605150d03080a1104080109050c061306050d18050705100504060e102102071505060306040605250c02152701030623090114220e0604030503090606040204051003 76
    0x410718180f0380c04008100024032f0801508400e000a02c035805950352001c03214184085030082c4d01d1458418503a040041c00554072a00c0640812020440c020170011500901c2441701481c010382038a254110402c14400d40c1002c40381c04000510311f05d841440c3c1071038480024907145191180700d102d0345040001c854010b10800702061b0290382c0c20400042d40d02010b40d200c00a40c48183c0031908030700c4004412182040c58802e0301cac440c94015010b005269616079a800081000400341503d5000c010107000250005d0745103210500e005450704800a201030041120b03c0503c1c004660a805d01089200380c0411144078038480b1b0100c45441070716048004005074040c00740c98021794403599038844040102034409020300f80d00a41625400a039988601c0701c28014200751410b40d4020312001010714092113014014654024210b40009640850382406410030708103440607400100b002c410300440107028041e05800030003c541c1146000e1030b10000c50408411281d0301030515650b1703a04104512 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 493372823 1250 493371573 493371581
    0x1006061103071113020406090e090304050612070908100207030206060402043813140102070627051c0b010909050a02151207050d180807060506060d0e01090605150d03080a 75
    0x403009000946d19141c481c01d00074410007440c40391103845d1810300003040b4580c0c80403045500f900c001401d07040c030309505d0002c41c0c4007900f0080d00e11410480c00600c0041d19a805204a900300d40c0304410141c1e480021b03090080c500100a80310b0f61203984100000c00022000e0303003940040f600400c4006c4031810003507109000300720700c00e00740308400302c400074142d0f18604900301c500082d02d2501c0411302c604049480120ba45280340d0240c0b80100d109800510050350200c2c07401040402c0000f80031918644030000304160748144142084c9524071400e03d601003201c034201303d50142c9007180042061181d561105541d5a0036164064041c400c000300135400c004000c022203d1101d10300c0800d04180c2000702c0f0050443d0321a003213442950b460701030154800c1c1c5807209240c00035074004691500340700043e221500100300140415070300c40000c01014002c2079442c081c409141c41c2d20b400010b51902142040390694030001c00442c801d03030001d44602915581c4d014080da07169094030f0003e910390f40310a0310a00034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 493374073 1250 493372823 493372849
    0x20d02060c0a030c020a06110709050c16050c1f05031303030e0a12020120041401030236040b130c031508070f170a060f0204030b0910060611030711 65
    0x307000340c0541c02e09064120300144030042c4203a8600c01103030340c0d82d04100d400040d10840d91031207805c8480c080080c2c42994100319017014089400c80e16101d911070a045810001c9401100d650708412070107803603454422940708191110414008404c41d000740014058031004001c1207a0445040801040c90720030b5225544221000044070203244950409a07021400d8a1f0704200541c00c0180302c8046000040d19401e1080b00c0c0a4aa4105424071a03c01703845007101c1c0e005410035074280301c529040e6072510350540083d06401100074141e1411104c2c1040d12281c960114004d60600f40100d10b961900188800705984141c0006080b03910400101d01800c1130340d03a02100304510402c08100d890300800e505e021500600d004c58002c80e911200c5503456065030781c40300c00e250810000540801c8461300144241d13900c1690040c40c1c59180e40e43e0b0702000c01c090b01d16101a6010542c01030100102d842560060300c40d9042c0b540700340550f580300c3ca0f0f8034414008001e102c0011140b5a03081512407040d00072507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 493375323 1250 493374073 493374097
    0x61c0b04060603021b0c012001110a05071b050105040e18010615030e070b031b041203111b13020d0902040903050309190302100b060712050426030304020d0206 70
    0x481d5907504010040e40201e17903802281c1c0301040c0350076a14500000c00380d0002c0d906844109103822006841d500d03111607040c0548040d521450031030180300840b0018210040c0d2501d0f43d5856811900b007039158440310840e03507005107140c01e209226581e00702d000d42c0c0c225080c0700c0c6005a540c1d6403091106914a00c4680c0400f690300389900480d429610000071140305110741c2d0100222344181c49042d680da100c511441d1001d0b0b00c200007182d503030055a2040407281c030049a249182c180d8845070141c020312075039000e800084e01c1151b03c8540e00b009004c0f0840702d0701014018800300107500d0010328125003c0d5001030019a00040100c1100b01c950000a001900108104080d0100342405003056008a4065144d030123031002c0d202c030040038140b9401d8800d8055008144500305410820000c182d121141c40d0312040a0001c0380002e141c2000c00a005c030071316601d0980303491605400c000001c01d6402800700e01141c42a15130008400001940d40c07090301200c02900302d070040d001050251144968a1403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 493376573 1250 493375323 493375331
    0x31a1302150414030a15110c120301151d12010b041103160801030f030c030c0203031b0714280320010f0528050408012a020705061c0b04 60
    0xd00715071401800850b010040088242100482059119080000c0051503055032501401d01c009255010441442c0c0041c082447e000701604013074640035060310b400c58240000001400b02d078400f030340b40050100700c0f03003800800485400c00d0003402d0441488000e0061507558504404000250030502065a010348100300c01103d02d18500060f034821180c0d0541030301c4186001184034840c03d5440d048030b07048200c110303c034040c55400300d458100d880c0c020350030001416810409030f50b09100620354400441520303400f00e41a902c15509140069006191070307080e0b4a1008010f0715480b4102c818203884404607000000c2c4100ba44283d030780369410141c07010740840200001e000681182e00c4032184241c8906c5059414054226500e00c144400c03040d0714407850a441000088820070411046024100181416199205642161454501240f90111a10340540400d1030601c00400455840c8041c1406038208004102c16200d51903440350120800e10525020741034541c802802046d000304144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 493377823 1250 493376573 493376599
    0x102f13060801051206061c0f0c09020702191520060108160e0126071502010207110d052805010614030d18090906021207020604170301031a1302 63
    0x240780740c0090103024040c40f2601da1107030f01130070002001c6116a03002072000c203076000a00d104003942e03959004200c8440c040704020f03000207040300d00180050304c0d83c2800186c40c4c103030074010054000403d01d803510308550144000c0c454002e2046100360031907100d08102024150281600074014011100708049001d46c00010481060100381e8042350400c1c00c4074040741d00d403a0608901e12440a11400420341000d142d00c0c07095040a28049110100c10800c2c0c2d26a65a83e0000340c01e0010321600c1070300140d5000078008204541e0f00314803400442c041c1c0314400e440403595101a900c9070303051040300c00303180c01840d003262503000310f2149081e19038010002d2000c1c940e1558146005030200440d588030303001d400c03d8000c8a900ca1002d031954605111170100c3c48034501010500186a0751030103584050f020481001a4031395080e880c1d000d540a0ba008224514182c1002d840790303c4499281c00000303070b04000420200b01c041140440310702072440c1d020315a0320340307103558905200390100082d0809500394200d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 493379073 1250 493377823 493377827
    0xc0501091209060801060c030e060d0903110f03031927030801091113210204180c0501020a0c06030515040f05010806090a0308010902090a0b0c0a0203102f1306 70
    0x207200807441d591540340003a80c44031020303101c03100700340540c00000d03403403042e800082131150b40d148864241c080c107414500b0f048514984290b45500505134045a445103582100050130070460308485030300401f0b1415401c210107086c2c0f485141e080c141003629202c4d030010300318801e0344014a11290030340c084510030315010301e80540074050900c564045103141a0303c840e40c40d0340744400c40340002e401500d103108607030420540a0f07800841b40e205102d011003900902006071254840c024080c0701030705182201246914002e40f6200381070308094119085101000001522101c0b403070181d50b000d050104943e80d400303450f49e0071940130b1420264458244a2113540d07011083e84401e041c2c03094042074841540d80c90304002c0e0348139071502c801400a8034210040003041a0340e4040c2220a90092449818507030b100001c482907002821a0f04441e00308840c0d0004601c0c1c104030701c0721030b0500c0030410f20507141030420000503580028030407480c2c0190340075000030045080302181c034200c49803c0007000c4241c490f000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 493380323 1250 493379073 493379093
    0x40e040809270601030b0f091b04030f0b070c030503280f0911091009050c09030102070302060114090c030a020a03091401090c08160614090d0f0201030b090606030a0c0c050109 77
    0x30410500b081a01040e03107540709000e201c0d0074070030141010700000c0d000d400b400150280107043e502202800ea91518507150a900100020343c0640c0c0d819042a500b400c0404210384041e10b4042800841800701000a4111054960242d03501c000b18048100e10540c0041d00100c1d007000c007841e1890f00b40c4502c00403107181d020000c1d59001740001c03040240e8807000d10070890000e44a1012411108400b00002000c0c0e13000340d9886821b400b80c82e4180703480f15003c203099070024a01100583c101d90014001048184048014654200d51010442c00c0c40c01104d103503480007400c91102d1580000310a49454000c2e04445900d0368802020030711072124030700944c000c0c02c01d030b001180c2c40b42c0c0c130080c00506560001486200348528104180010b441d00c0707410398060740804011305c0d2a44c0f017800003070760a6907522010741c4418040c1c01200351711040c2c1d04c001400c45003000c0c143c51041c0030b040e05100701c80c0c4500013a02e81c0152001d03000100c001c0c0902d41070b10302030b06c007a000500c0341d0700b06401c078400c00c9100b0034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 493381573 1250 493380323 493380379
    0x31210090e07050f121c080405161202040c020109020d0c05030d03020310140d0c09140108030a0c1e0b2401080702060f07090b13080c010c08040e040809 67
    0x1042205600c41c041c0781c94600d1032003001d50007800c07802e95090a10300802c02c101d20320b40c404201c0f9140300c03403006400144843c3c00d90200c04140f00c801008180642400b581841c80325103560f02c002d0900b020210510175100d114064051560f5a8541318a18001d61000d402c1903001002c00e412024140742083c2221190b000b2180039028000c01d00e004d00d0301070f0080c0c034001d80c080350896482c5070802c1d00064118945010b80780e4005d04141d0700001240d048070404001d0040001e0104854501c80c1070305502e006d043c2c6c400388495108000c04810154400c500c000d06607444100440c0042a8449000c0214210540500f004c13221009200203d270300384512048041c5101c400240d2980710400541e01c0c46001c442c194096085200020060001c0b5201c1c1c644c070081d54141074807a90744076007138446c0d0f94000000c200b100e0342d250841440385943c1082010340c0c01c1024a0400b140310410381d40c110480c01a4420040110a4400454104560003007aa6807500f805082c0ca10b03007940c1440640110740d8808 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 493382823 1250 493381573 493381589
    0x9080a0c03060f09020604140103062d050f030a12020102041802040e0c040e01060e03100c0807021606120b030c060a1205130b0c090d0b0c0912030c0a080c031210 71
    0x81c0c0340112594140144e0703686503001818141400c0c681074a2500c403176001020f882c105582d4000104912440140703c030b0141c2c0440c6e814888401d1220240c000d2500b00342c01042c0b1034140800c000180390b9000981c0352519a0206103c40c1c068058070080c5d0290140b904024520a04030490803034180c1641c3c0600101d500f0a18211500e80300c602d110252442103005018040c40140d0042c0402e900840c0b03101212180502203800049160141008503496030480d40b00240100d0300340700d440c40c0c0c10080b11028101d040b00c2c820941e480c02002400005000b5600318042d525040c40d0300f003da40a0044905001d00604001c2c0ea6031405040202804d851103000819140b070003021410800d07000d203211040b20f41c480c8800c1130700d860301612002950403141900703602080d29040240059098440c0da40a540c1c41c0364811f45820f003110030007021480c54503400c5001d80c4140501c11517610300003254404281c02a403500e0351071442c1c2d0509030851290861034040c2054000500c8803030f900c00c0d103130242100c0d1a9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 493384073 1250 493382823 493382831
    0x1018170c04110a050c030403170d0c0206071e09081014090304050108010302010c0f05010c080a1113051009030b0c0a03060501021507050d0905010915060e010b041509080a0c0306 78
    0x82040222003044029a05410081c0804143c4502880003400d00000020460b41800d030b07071750f4944000d248900c00d401001d403000b04851075146190b00401c000910742d8000f503c214070f403025008041c00500002011010400c03140c0300ca0300780c0221810130242424905440c0c4100041160f18082d20b040c0c2d0120b07003910450300004141c004040709550640307405a417860300c1640795800454110402400c16202c0840401c10704000600910481c2e50000341c54231440360707070300d40959182c0c1100e5035003c0c441040f400030000603010b05000d0000500b520004c84808032044a100c0c1c0440d05442140c10051541417036030140703c00c03c80c0c50b0003c0c01d0503e55581e402d0000380e8403240126146c070860407111a680140b00c021514031405000034181c41d05402a00080c0e5000e40e40b00c150a4a800400917680340d03c00a12404808003c2e0107000081e01403100302c0710940d490070544100c1481284212607210180030344514482d807081e900303d0300412084007215210140d034104030141400500c0300300c1d9000d00e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 493385323 1250 493384073 493384093
    0x61606050f04050c01211104050409140601090b0303030105121204090614040603030206070e010513030308010905060607050334030e090907140d060b030102041e06090b09101817 78
    0x306040c002c541003070840f10100170301d07038a01800020b000007101f1502c4c101c00900012070316480300e104d0041014010103030b6800740c0c070514000f2800c068040e0084100941001403107145c0342c400100f202e044441c203a86800200507513509150410300c4540300d00040c4400003e00080d81000d6400100550b5489101800c00100e043e003000b0454a05100c001c0261f04440000b6a50901644094004920604000380f415051500307032346442000d604120042254180140111540b922869074807034819101d0728540103007034070b4095a0780a0700807a100206205c0182c42140714804500300c845400d400602c0b001e2540c13626000d0400c0d044120164002c240ca040001c1d005540010400101c41101c1c038080352150307491080c0210102042400c2d00c0c126128120004a520b00344024001800c140207540440d180000c6c650400d0741c0540d100f401005143c40080c03086422a804407010748508603042400c80443c0c403001d03286e24190342510750208101810000380c00042c40321040c96102000c060300c0344840 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 493386573 1250 493385323 493385327
    0x100204030c2d030f1a010603060f080c09042003060a060e0f01230a0b0a0305180c130b0f0301050108060a241a1308010c0e1e061606050f04050c01 64
    0x7520900807611030b0480442000401c02c001c1c0036441d811301480720715044100701c22042c04505001c0c0c0c816400240d40302010450415408003400c040c00300341c809041c0c1b00d40420006442404050006003000c080190000b44114109800007000e07100a420781e806c610b00030781404024441d034440c0080540c0c0c0d820024400c140c132060070b9410380303520382c1c80f17440318400303145a400b413900c0d10010607500500c03000030208440b1510400391190050a66010910b443c002182001c80149401241e90a500500010341940d4901014083d8280d400304001070605e0402d0021300e625900c160f00540551030280003142c0800302042541c40703070950840c103024a6460b041020001c030400521621480052a028480b02d00720303a0041c00301e148058005420a038000107282240c22140d40202c0341a90b603000060541e43e040b100059190038100c40c102c601201c0c1005c83c9180200800b01d0798070808000810280e07824040300c00f100700c5604105e04108604c0e2010400d60000e20079507041d901803040e01d02d6008158 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 493387823 1250 493386573 493386629
    0xb0d050c0c120d1d07081e1203190e0a0c050303120a09050a02030f061f0e0402040921030204290706090c0312050d0b0f18040203100204030c 62
    0x20031001007014051640c8000c60a800958034800d5044e11154121021035440c80380d001100301c2c62020f010420700d0320312524504510b0350130160741e40c018010010008080400c1c0780301103651950312255030b0364490494803c000b0f040c00000f49480e00d041e090140b0f107080050344110440c804c201c1c0301c1090380c660342015920f006488078080489812400500400070541104410790f101c2c10072181d0401c569800641450070807400c4062581c0100100481480741446d088060050110480d1400341004280511344070000c2010303000b60780f184521010804240f2414003a10250881014120101c41d0000c01030f40c8644103106078118a003400803060124000c80c80b901c0b400c001c8601e860907410350b45601c0500441070060311021915180023000c200402800d0302c443e1307205c1e56603917138501e94011510100c520602181d4041e8121540440b006c0d114900d0310240602c4d2500c91405c80d55452001900d0100510300d01e0030800d0020500204000000f00c80b04e054039000001c400c0c400b44e091002c03010031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 493389073 1250 493387823 493387837
    0x60c031b1603030302090604030203120706050c0403350301081608070506040e091606050913060e0a0915020c070819032307061505030f06010806070809160b0d050c 72
    0x35110700340042000a0003503004051800c00a0055070926550b0340000382000115803892081200000e200c401300041445500e90207028081050301381400c41d100d40c84050100d0686051700861920360790102c800b404a07000001c0058495142d681d07848820003500c409800c1012102d185400c02c002c510800c021810310241d803400380607141828504075001c2014500500001940d0058001c0340301600302000b0404003402943d282c0640d1059018244600c0d4a030b001880404545048000e00c004500c0c1007c07140c009a00c003001140e04141414103044c584020454008110310000c1c8070300d07203a1000b14240c4119030042098411442c240c0700c00d041d0101c0e0583d8024006403140441e000c4003808002198a1a0000d070001410002295522011101d1402c1090090654134008200a00d002c1001c51151007845000c0c10f01e039494100e5040d40c4801c040c01c614140300b0130200041102c2420081c500f0030020500c001180c40da65007010200d16400780c500281c030b00d410000003c840400c600120340700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 493390323 1250 493389073 493389103
    0x12020c0d0f090f0b040f1d010b09030c032401270f09020303120f010f03150b040b1c170a1b231509010908040909030e060c031b 56
    0x19031003440008840c212001c51100092103040701010403515210650301003e44008000c003a6120309000d58641b2180a5a000a01801e160616886200d0799000b006e41100c103001c3c01c541d150307004000001d092180c005580ca8051080750400111070240080d04409a0208032484203a030f40c9825584000140300340e40d02d40c1c00d01c030080c00702980c218568030040b89450b00c0b00000481426550003e82158460441154403142800501071002412480380303004204a040c841d40151841e41d03040d00c00c000103600305a60319622086c82c9030603100c03500064180b010040000509004018a0846940103d032050fa140c07c6001903454226441000700d4144c1904d03602d985504000440340c0d0b528402414000303c5103128918070100b03500090181000c010003645001d480c0211854200105111004080a09030fa0406080c0404200030b54115415207480c0b07000401c0011940c2000d03504c0c2d01d5880441d5821182c002141507400e1400720250402d0491507468161b440203030ba11181c0e1354480c044070b40702 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 493391573 1250 493390323 493390333
    0x20601080a080d1d030a18060e0904140604031806142d0c0304030201082d0702190b01060314250201090204150e07091d070507150c12020c 61
    0x402d00b8140a05802854500082203015a603030240d00c440c400783c10801820f90011801042060b0015030388a5500d41c0c900c07441d00c5042c0b038020000c100c140700e04112401080d44030081414488081c141c0048264103a04a80c0141018070b0010301100c0e11803114201d515034200b011420b0b61280308402c889440c0c00c181d05081041144040249507034880e640e4031020041640341110914840c05071800a180c20091625589940005000680018103440d180700402d01c0c6085100d030302414585103c41e04120f003d40c240c0e2440c10592420f5128000d94442e002d00ca94030b00100922040d1140c10390310655010300c140f006640a02180b003005840c5c0107001c91001c10b00c54a14510045040032100c250320000c2841c03c065008a030480b01c0b03030400070f000044010700500800d8040224140c204403d032030460016490f20400e410350340d60306a100e201c0c5500c00004107550602c9a03007a120120f402a101320305040340c102e808001088001d00c4940030400364460505d1018643c0300791200300082d140500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 493392823 1250 493391573 493391593
    0x30c0714191e1407090e0729040305120702101b02010e04110301080a12020a0f1106120a091e030e0904170a03020c010f09050d0e130e060f0702060108 66
    0x4103010514159001d84080c0c400c40b54800310352030112036905680c095026150450600400c8030685d5009202d55401da88807420404c154840c240c0200085500a9108400e019224030004030a1041d50310140492003a05c0c128188005854018030300c00380308640a50b80e5210004064901c244003003000042ea0300c1055628001d9400b9000d04192950000c1c0001015003511303d85d145c0070b810a804c555195444440740104000044e07030950300c0721280c0c0c00140b23488141342e0b90b841e840740107044c2c0c0102031500207402403030b050301d130101a2485008a40d14001d114034185549800900c9440f400b903801d16145007000e0845204030107039039002a059030303500f034980c9003040c280460117201034021103600140140020503414894050b0000c030310076941c0981c0e1003850300001401d584811100414091400740c481f40041d6000030b28840300c0c1020f0a151700240981000035080340001500108554204007502c58054004075200d031003042c0098107650325454044040713a550600f40034400301a48812554 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 493394073 1250 493392823 493392833
    0xa030c05010f0e0312060d020a03060c0509040e030c061f03080c030909090d0906020d17060d02030106060c030206010b04030807200303070b15010c05071415030c071419 74
    0x11418011400420302c00b040018070340c02c6548190aa40aa4001082c43c08142050600b52030300a80100c42c10015080c01e0340008002c0c800798400201110307a21200114481c1c020819645000b0000f0310400c032000d04056001e840fa0303c9084400d500d40241d80000750403070b081ca0100ca00610082030b12000380c5045940d6000a17070300500c000c1d40a88028400952240c0d1880c481034882e620400c040e00b070000610ba000f43c034402d0150841005c0d508a2031020080c80d03440402228409013142c0180f4950b128440402d460360200e4002a4055090000108171780350405c024500c01480f075422246140e81e140103614490207140801030011004021200c040ac800001c0800d5030b45601c00c20002c0c10400400117861030340303c0401100d05c0000c80d410800d0411007001a00c04095003800c0c03c0c02d00c0601b540d1819103d805c03e01071504462603401c400203107500c40d03050703440001c100312050743c2e038900342031004240a42060400316102601703810780744180c40010683c182040d09281c48400b0311040ca68072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 493395323 1250 493394073 493394087
    0x8130201020a02040606033801080411090703050712150302060901090e01030f1e02090a0e0c220507020321041e110103231b1306030e07090e0a03 64
    0x1060341144107041c980e00240e0303154450744c2c0007044981c50004000c2c202c484070546000905080000540b4440501c0301503100208020440c18801d180001c003641c0d86160014a801004000e00e800c599108108040241c041d800315010320f009498040448540540d4181510011064240c007211091020030050602c9809014207110504201c03026135156070074a20409003d91060750341c582c80d48010814458008402c05440010061100300b004c2c09401140841c2c0025090416160f521303242c0a0b0800c0040c0085c0c40c0d103d000030b203032411a0817400c0c505190000c1081a11940c5460b100100e40c0490001080303888401c2d5684007603e03200b9412100006c00340000b40152092131070150b6001c2c980310b062000200651084107420007040400000604850f00c0c1900c80303a07a0241c1520745410211784400b030681c400c0d05031714429050f0a2103c2d0142050103018a80408502810740216020380c054210004091003141104d41c1c481c4d896441d801030300e058400380b003440d8128034045401702e07100b421 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 493396573 1250 493395323 493395361
    0x905011a0f0112020c0c150d060b03010521070515070b0105010801150305150a030305180109080307020d020301150602070e060307180e070b03090a26090607060603050106060801081c08 81
    0x20758501501e0f00c0003060341da087c03a480b040000e100015401d0341c0300c10580304040142491010407400c3d5810440400c0c49512007003940d040c801041da0041044880411000b0301411002d0300d20039038600440102502a004070b001215140000700002c2038651154101a040f0b80000108000e9600d50340f10aa000b0714010349042c1010040013524882034652954040c0150f01c25075503555030310050031403c13040c01414040a81086401d940400410a00009482c3d8081d011a40c0d0a0407100510000e40141700300790f0102040400082c0c001101c980100d14001101c901001103011030b61401c0425440c3d285500a124040300182089004d0180e5540102c00c036000c40c5007191082c5841d00324102c0660402c695001d160b6000d00103040030880c807010703140504090000c42180e000100e0035800c0c128000c0035150750140c1008906d14080c4103844e00b01c03100540d0404020004581c5401c07009065070024000c1c0007151040c1d030307203441c5210848803860030001100d41d26001ca43d25104510300b4040f180c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 493397823 1250 493396573 493396597
    0x515070f0c050603010e0702100b01020d0e040902120601030b1b0301090513050109081308070f031205040b0706060509090309030a0206130e0c071205030106120b12010905011a0f011202 81
    0x1c000b1549440c1c01d00254040c0caa5a8905541451300c86c030001d1821144000c24200f880c01c0480341c0e4000d9030002085d08902603182045004940e0541c0894001c00102902030f5100003444105a803c41021420740d0507a07000b03051030303101603440c60702c103025281f01e0a544485420080004100820540e801203420541c6030400d2041c5200305c1d1120f0b400d41c2c000d807200356480400000d125600540070f00c800001404c031000505000f5150003040f04460004bc0b2000d0304243c3e01840f940000c81c41032085401410b110005c0390341b641c405042c414010003907402a14011600000030442008000054542c04440200203001d6407240d0744c24414039420000070301c0e0740d0b2825030354003160840c0c4803240300348212031006074503445d103a0360f05100c140c2182083d04030003072040410040c810707140d000145406602c0427200101b80c00c2161800320310b030100d0018845145518040c2d1407401c204040d0071130350002140511444004820408104100c401030b66441d01140c02124240c0100400390050441c03007040c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 493399073 1250 493397823 493397843
    0x150a02031008061f051008010b0f070c14040f02070f1515091b08011809081215190506040e0c0d0c023f0903101a0a0515070f 55
    0x103001c030314507108064030303807046000b991981c2100e041c0124039103800510b0210f64440c61b00c4a001d201074890b50042c000c1c810758410000d00b1868180c801005c4451082e8022030055a299540c071050000071024441a481a400c011f42c80140d08454004d540c0f0458006a60095405042e40c42c420541d494078030b480019030b1204000c41c0c03003400781e03800d420080c81c0004000c0303400301000c07060b954a0300745510024103006c3d003d00103104890b0317000002400940482e50000d14a121810041d03c2c60080c8400c0726103c0000030108040d0444901200d41c100d94191104000113440d81d1120744942c199014442c1c1094042c4010010b0070f814170a21500102c0e0010741902e403038003c45400c0d0907030700d500800f0005a070251880c40e08203e0f0f94a8803a000b9220001010040980c0c4940380c202076503104103078010054080380d4903030250740c203209054403158010710401c0f1861950900b51884655031906510480041e5000107049c2010082500700c0404041c40c0c038604441c0d0742e80c200c80a0942032043c0c0d956000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 493400323 1250 493399073 493399079
    0xf072a14040b0909070f080604260904020d0e010f060e070507080706060603020304021003050106020a2405160f0309050d111f02070605070e09010603050c0c030708040303020f150a020310 82
    0x40c2c0c443c00303401481c080340541803203418054041e040a180b82d100701c807260300040801020480c00450301080304107100040074800d603041226481401094282035010b84005a0340d00d042d549a800240c04415610081c004000c0ea109000219010352065040c01c501c603000003100d0600c243c0041440900c50f015481c101340c0720b82c48440840d00c03580c0200c400300780c0c000144010740c600005d07142e044002c149000d000540c1816030094590001e10002000725500101151042d002c4201e41d408101124000700164170340100c101c00010b07104500c0c2404070b03d070035042c1ca554510900400a54030b40040041017203c0702c032002186d900c00310046080c01405070002ca090026122403c001c030100c070030800540c0300c40350f40c10007904460016000c0420b0111500c0404e8440d12100c2c213090444131107040010f2141d40300300380320240344141d41101c00c40d0b00000420078208840680904243e030300a508481d050341110210300e0303031038502805600b00341d05040c001400d420841d80080d54030001c0821240603542e9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 493401573 1250 493400323 493400329
    0x304030606120b1b042106050a0c0f020a0b060d0602071506141c110619091d060904060b0102030702060d051503012313080f072a14040b 60
    0x10710340c106071071a020880c0c003201805400900290031001c0282d48155141c0401d04501007031150340305881c2031003000f1000070b040f081085440d02d89190002d000b4441c914000400070010620380d901d1034085070300c05035504035403440024511300d0740303505c1902049152516003c001c1409a0581c0403102c49808100290024803121102e078400c84000302d020071315908010813820817148042559016240030302503da2642e11701900240660b40021041700c9004024011030b0075031003006070fa80208407a0490101009034011440000c40b040303100f5201500c11040e0844a10441c00c0e509181e0140d1a02c0c04600820346036400391076491014011070707162982c581d002c20307056004410724424096031942000f100300507040804410001c00c034001c002400c4000e80e40410060039070102001300204800003508207444080c000440d0760465012600c5800b411603020707559200250880303007a4109110303074001ea81c01c0d41440d10241c00291206488504003070b07405a80005000315203500545603003046c200c41e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 493402823 1250 493401573 493401581
    0x51305030a090806091906020307030b030102041418040512030c04090516030c020f06071d03031902071203142a01020406090e0402090a092315090d0807030e03040306 73
    0x1d05962500c0c4001d0b031a00446a0030020010041030304d50300042400700c1e000c400c8001003a0300c1030744040c0040e10b0780c50341081200181a180d21481e0590300c0010f01041118142d60590207001c0d048401d010346910a8110082e082010350340140b5651001c41000400340c0031030082e46e0300481d0080f070789040a6036400900141c3d0415a018000c05076200820059141d1500030800d05240b240020400e04100003a820381c0c801004000f1800c000e084d50f1307000d0310746401c0d20903002281030080c1101e0f05c0b4003441016464403216425820054461054009003484c0950b00c060134554241d1604480460f1a0549010f20b038803070003070f05070030b280345c2d805145612080c90805c00c5100381007400148c40701e041500c090718070755580e0011280748001c103041100503650200c0b12648903045200c081506009454041040d0740e89156100d072a5032240e446200302003002600030a5140461901d100688405e1900354407003a101c08107600090b814400225020b02980141504480303445c1180c0c54190b8075203503d0220b03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 493404073 1250 493402823 493402837
    0x40905240403080610090501050a0909090507051c03020a0201030218030f060712060e0109091b03211d1219150b060a05180301140a05160f020c0405130503 68
    0x40c210a60034802803540c031455407584a41c041da01d10041e409a480b000d040507109104940c10044000354040d5190f11820040000f0320036400c044c030041d150381c5000c54440302c060094a000741400c2c4000344110300ba141d80000c0300c64068001d441c400c0d82c1500114040d52011b203400900803a1505a01c0b41510708001600c40442258054192030500c000002d00304010707a107040ca8080d00380031084c49681d40d244506811218010b1000407402114074150504a444a0006582c00b032441c20020a00a00103000040c0094190007110305c000444d6040d900100c9103c4031992007520b0118292240c240311500202c0b807100e9104554101030101c5240b07c1101e5210001c071035004140c01d021030006840d0140c3c007111001100c0701420451134600c01031443c007500c0a40308400180030300c01d515540342903100c040c03d481400c0b00e08581e80f03028215980a410203035940042c15034440f0030103212070b11580013444056150f074043d04084000908000180101600b148080b58645000d940058000c00080c801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 493405323 1250 493404073 493404133
    0x9090a02130e07050901020d020d1d132a081005060c0f010204080a03120b010c030f050906131701060b0405040207210905010f08060901031e02120c03010605040911040905 75
    0x602d4003804002808e0480c10710744441950b0003d141d042038103411110310100042c0090700c1814403c84039000030892290103440540c010f18069124011001c0100304444990700c5540041d40444010422900340d00d0840b8405d1091800610511591406070024a1031085010490354030745440c2e110340f422644194030046403039100b00c880408040d0405001c1c0c4c1244800002005081d1140b070011300481d00c401d10040c104911170841c3d03101e20340502c05031056424050642a15441d15441d80a60b0380c00d680151034920340043d441300500501402604165810f0103440c604091410042c07002940010108580003210b0342c0100800804000120380d01700c0d810b42d51841b4103450325001614072039148421000304200302e030401c40e0585484416a0440b64000002c10385034a00540b40e0303034500500034000f54400500c605002c00024001001e25000000b14002c0003d29900d01c2000200c074480354008111001e050300710000d0b407829a01100d035103401036040e03400721001184444d0303420081d0481c001c0307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 493406573 1250 493405323 493405327
    0x20d0c0207060e120c090c0c010603030f1e020703080c07090908090f0603010e06010f030e10142208070f02090901020c010f020a02030717040f030b01140609090a02130e0705 76
    0x88500c1d844280c00312584016504d9004118550036001e441d200010410303400340c6902c80200c0c0554a9642c108c5003807440b110003c1105c036440703190007070000c84ca002d00000042d0b2807580541503800e5800b0200c2d040300c801e40041074101d203584d407407660a400240c643c01a0b8000c16000084103030050291840043c814035025694064a0f010040d4080c1000d40013400fa02d028001031101ea070f0b1500c04c094100409017009500302c16400c0d0200c0c05410b0705800804240603040301c1458220071608244030a0101e07071110740840c2d5400e08030058413200780400c0c549612503030000714081003005006104550040d40b035200404480e130003048031071030103030b540c400b050307500140d05030501c0e10a10841e1030404031450150f01e400010b0300700135984d005082002d407044504900c140c2180c0c426030100d5004090109405a200b95203040c003080d000400d2040135072940020341e14028501e0300008950841c0e200514043d0f450f222140281c000b5000a102005041d112840200b81d045510050301e110350001c0e03030340c03035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 493407823 1250 493406573 493406579
    0x1501051902100606030207030c06020309030f04240e0604030f060f0504030207140a03020d060e0c0415080c0a0b0304030f030609150302041401080712031b03110d050307120b04020d0c0207 82
    0xb04450899001504051040c00f01800290344800c40c280d100d9041a00940c81e9105c01c81c01310b04602c1143c40c504050100000d001412024181660114503a1864600701c0c000d10ba19058408009541c5101c0c3d0001d810001400050398a42d4007141203400b441e400a2900702c0090b0307100459606a40c10340240c0e100c01010082040c3c0e401c003202c99800281c0307404080520f180d0115070518680b04000304041d885291148000c8010801d5418a0b40014014400348a000b80c100c49601d404d4000c035040750082c2d50a02115061203010750040301d00f00d90840e4035541c0d594074100d420768803008401c02019161130300006c2e5211381c1d000d004061000f10b01001c02980ca54030401048425a00c03143d0741068800c00100050000854840d04480c2c6004054504000034541111101c0251510303690802c0c01032655014154017900b8a00e0091801003282d480c8000000c090751540001c5030524006102442c812810300101e400c01c52882c28094005400e20015140d0801070b643c0702d0542d200140d210b00010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 493409073 1250 493407823 493407853
    0x80a08090a0609181d12040807060c02060a0f020f0609011d1c03020a03060b0d05010312050c06150a0b0a0809061e06040203070905100c03261501051902 67
    0xc4004110505002d0100d030300e4190350100340c1c440f0001509144d59103032000300382e81119202040c00040d5640c21b444a07090140742241c599000350040290b14400c1c0580851190b010740306032864246c00510071400d03e0b1140c00300302c0d0100c1e01901c5107003c5000700c8600868201c020818903002d280391030008650043d0008403001c144140c00ca071407080b80d00c006040c0c203521a20b625903255182d00c501e4056a200203000301a40945855031251400c007400040024009000c0e500450589100c0d14014101184880c0f0840b06405003142a5000c2c0d04280e0204150490144580d01441e03005030640e001159103260740555504484248000708a01a08100c0310582c14032072554400090011110400c0c180107000c0742e03801d0024403640c00340f94000b01007070703140e03008148403c024017009202804132071107440010020b000c054001c42c0400c1091004080c1d00d4001304400000301b0f8101240d80e11076031040e50175000c0c00001604d140c148402005281700c40d402c10b40e038000d2081035540061002d14551850 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 493410323 1250 493409073 493409089
    0xd2a120c020a060b0604080d11150402090f040507051302070b09011419060b0a0305060102151b090a051504030c0b041401080402040906020c012a051c060f0303080f0f0c09100504080a0809 82
    0x14040216520ac4100030041e038400c08410380002103090b41c40c1003543c07140341840ca00002500314642c0b200d4003174613030148292240c00400c5150703c120074054860725038090650903154183c8043d40c3c1c0f540d11100181c0713305100003003483c0c0d03038030f407072001142103541d5a034684000e9022030144c20000361104100040d558040044115007d0382420044403880c0031401101000d4201d112a8500d001c006481515550341220842c05003100400da41107907110300c1840940d45e88144412180700b80c007080c00007114440c05083d02c00b110003403800340c9680318031040116481c03000108102e0b4080d54841400d00428540d00c0a080e103801d0680001640c0044040f50b00407042090204149008040301d401403d954000c0980317503451620714907000410080c9000704064401600302100440c01040000149a441700016025a200810610441d1200c0001d200c0c038900c22503481c503280b1000c0000c2c00c041d0030000c0b280d2440184c0c80c41e009040c603468032807090400404100c246c0d0031500103c6c07202018070384482 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 493411573 1250 493410323 493410343
    0xf1d0d09060203180d120305040b0f090703021201020706050a05010602010e0118110109080d020c040506190302060313050106080601080c03070e0103080d2a120c020a060b0604080d11 80
    0x511000140c50601c00039503d2260714820220742c1c2e24203c00765140d8403003d01c1100b45650000ea8403042410081d0300800500007250142e800c564070b180881c14182020300d049019140a03070260070f0050640c0c01b88101c46e628201c01120361740d800c00001010031141e100c2e841c013540c01401c0110706945041d8000f402e440c5000842d1500e645086405500c001c4c0300c2042800b42030b0300010383c080588004006854031180c9501c500340501070005525415640401c83c074a0500048800308040d441e00700a1100c140c0b003c04085111444640c0280090b01c5d1240107190711004513440719840340f12568640c0d0070b43c0d04607030042005600c45801402668000e000f40480400103500420b106440d01c0880e80c00c0e03c0040c8006000c40c0c2001030751502800c0d20360840b0b0001c0c07a60340c0202c000d0507465005508144006000c02002071050103140100301c1c0315029000d450300c03040d07004168199550b1525402000041300c0d0551105080000117801300c0280300303050080741c0710744481421034954240c107410115905 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 493412823 1250 493411573 493411577
    0x10515030105070e0906131b0c06060b03040201080703110903070617061f1b140c0a0603060b091c0c0b03011811251e02040e070506091002010f1d0d 65
    0x5845601e41c1c0d05c40004490344110200d60700e003044525004200002c240382c2d41108240303402101c0840076240c01c84020f4050b035120b02400c001455035004000046d00069074024005107200d804240c030a40309804c030745010003000c80b5080c50403c00c2c02c0000e241c43c031180e10460210721000103a0030480d5409142d03503031106058031a01c0307606031180100d110800c0034010a0060050205840d08020482503200d854542e000c5c0b50040c0054180f00d40c2c6c1e0b52040e8400c09035108251005d4080303455442401520100c3e10410742840c104041c0c9010046001041c441802c4000d401030000804180a580307080c6c01002c00c0c66080d582e0f541800762005a021218881c1d449060604802c41d60446000040302c81c100201503012511104103a4441c1c4150b034203650190105405103030002000903107995014400d4800c0700c00f0415180310408003902c42d541071060781c0e80a2400d0200e100281000c03800155101d209200001340d107404114000c04880b071141c0c41c140c90444000b40344604080410042414441034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 493414073 1250 493412823 493412837
    0x90c150f020610141e090c0c0c040e0304090b1305011518060f050d0e1006050f0a050f060a11010507020303060a0909121d03010e0f06100e040b100801051503010507 72
    0x46508840c000b0074080d4024000d400c008405113254012101503100d07050020319002d00c03407d1003c0d030100240c0000c144500540140036100340c8503c4c040c4101003040004101440c01c09192450441c020914031031030301e40001500440840410145c03090743d010300703802064500e50100d08180240301007941e40c00050340d0440043c044c03200740d0700881f103030410759860302d046a030b94020350f40380001400300850703601070074030501c6034010304901d031504404180c45060729160007145500d410007290080e14480e0075080a1300d20300f0038130603050140040100300c41e5818000c1c00005605815030031034800301c0f54a001a0808018800141340040780040108140103041c401c40c0150740b540713a000301c0300b1140c0c0414002d206555401286441ca01d140810310020000c0161403051038260b5164584440c40340014005e0000107030321a82e61b414100c0070b407414000008103d42c0c5568071250400009401841d01e104424000202e401090160758880c0500e500c25101314040c0d00241800d60303202034440c0c8180146 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 493415323 1250 493414073 493414079
    0x5010608010b0712051c20040e0103060c032c0d03020a0807180803040308090405010b03040f08090303131d071e030207081e1e0405090406090c150f020610 68
    0x2400e05544480c4e8014130200320031403118000f6112803160b0249000e03840300c041410f012903c1c1c1030703101e8400c0d051428120280400811883c10703d0303104900401420385403150050010404682c0402c2d10030400341000074a85580e0240740e0840450b12552a41590850034009064a02401110b202c403a840c00c0075820040d000c080500b030001d0081a0070104001400d048552001d9a9511170042c1410010f0741d035559140d0402401d283d12444800d4025424040001011000d59080301c0c0f0980d00300004d030b0350205a61341e810000390f110402403503240c441802440c00450014a03400000e0400031182a0015120a84e4504123000204039000f0b00900080001400484603299406951a454010b0307690101e8a801b030300c140a10300e611034849001400c2e1155118020006100c040c01e519852a00c9064042082d0000d00c03d0707000f0b113900200460b020400140154110740c4401d03120340c0f92402202d80b9030300c0c0c2c2c8248c9900a0007240010710704e4840302c240960144038540e0094140071442c01d040742 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 493416573 1250 493415323 493415339
    0xc0611122a03060604061b080a030b0102010e070f0b0d0204050301020a09060f022803020102071403090a08030309190f02041e0b0d020d03140c010f1a0105030f040213020904051008010501060801 85
    0x2651255209000105030030380c101f8900c0d00c0041d618942d21555807915550302080c028004d11500360f40e18007640c6880d8072072000120000c0d800040386c42042d14075610508280c404112a0445010000910340074400804c540da030a00103010200c906a440860380307880c0200080c007a5603444081000c1d50482451114503d0402c1090380c4040c608820303100514105140480c024803441101800701078690840001011000c0010202c03030310222801c00c0165241d0318803c0c1c8070300c01600c1d0400540e10000c0403240019140c2017444079640220003d203019401074001c5025038080742d4400000b00d040d002d09500d14180d0380324010344c801c82540d080c0042145580440c1044054040260a000c418401e400c0c845005404803001486200d009101c0114405480000340c036186180e090500003e44040000d5440782099a2050410f02c041c2005034545809100030088102e40c660401c1c5e408206144e0291505c2c05607900078054003a5001c80c1918089160382101c0040c1c2054080048540040120030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 493417823 1250 493416573 493416577
    0x9020702150a11030d06060f020f0303011202120115090f1104121b0611210d0e01180305040e060306010303020d050c160602010e06010609060c0611122a030606 70
    0x101079428103a03072021514815140c1d0204400002c0d0280f00c00100c1401d03420b11500a48200c0d591920380d41e403d04000d12003a621010683c100e21450350003030004010141109410320000c0c2d0000d0000030201080000441c2561910340c5248022044014108090700c0395100b60362040700d001400b04800071714002084100d00c141c1c8510300300582840f103071070103001ca4102644940c2184e560703501c000d140e0703481019180d0450340400d40004c0c0034451081c16042c01c0c125980306255403403080c680c90b180418503c10010700c0800d2400c28559a201c42102d4845036245202207506e000f5182d1070f464900e0101c40d0b101d03c000050415000340c1100e0010030003e900003840c410174102e242007081d2180303d136003065454980d29400740c1101580821000032003179019070104a0701021003054035020780c1c1750242514801268442c01002408640c20701000c00c44030340c8481e680303150a4a07002e10f040007002d601d00c9800310a8401d00ca00c000f4425526003035200c01d0f4910082010030210301170a5240500008200d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 493419073 1250 493417823 493417849
    0xc0304090504150e0f06060616020607050708030c161502030319090c03030e120c0307050d06020904020301140a0e060d12050910020f010b121002250302010c0909020702 74
    0x1d03110008182001007810714801c0031008010100700d8a0b1400c1ca030599581020038416003180581008200e950030000116884003140013107020286034a942400030329130180c2c405513280d0044c1c0c140130400f00420310040104032407000c01070a0042d801510519000582c2d03000d03034181102210a02c0d07100e40c02000343c90344800440100180d100408400c034014004407400100a440140c0c1c0100401d03401942c00009001c00799513151440c196052032954590b05100600d6050388460420489031400561308280140304100160078101c0d81707000725003681c1080e04007040c040480340c050203090800382510b00044c5018008600113051100104000c00d05400f4050041415580301514880c0103c0c200d40d00982c02503d41c2100e1900b5080080d2282c2d111160f410481d4240034160f030182c6442d500030b56003016618041c109600c0103807941d40081d40220000b851180340145060a000d9401e285525541d000381c001054683d001d180040c1020000d40140301d1302c510521040b809a01d03070000c00564 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 493420323 1250 493419073 493419089
    0xd081e0f06011b0c06050a08131a060103140c03041a1003020f01090305101a0d020330031006080c0a021510090f1a090402060a0e130203090303090705060c0304 70
    0x6002d80100301c0d050143d6589000fa1011201480001e50703a86c5c8217000b00303075030f10281c0e988401d5922002d040700c01304203984102402d01303c0a01141040b425010300e007250040c03014140050704040b05401e0045141084402d403074568808401c01091101a0b40503410f10b00160300c10180c07a1800c081c484440310220f01000e40620070148010351a80d004010480195400c44e0803121b50b01c080d031081754003030421991342074084d0001c2003a583c1c00e420400b903011007042d8028068511031000e640c1c90001c2c042854806054a1411203401b2510140a07004601508480c00101890b40c2070520141400703402500f4114420b40400c0b0401c04158046040d002c0c07065103030070311111601ca204a00d0145546a00710a007403a00c1c080c040084407055500c41c441500403074400040008030f07041040900c8004403006034104808000000c22107203e0413030040c0c1a5001402c500302038800740d40f14001c0f43c00845403000e2a42c40002800000442000b185006040464649117042d9039031815503143d005e103104003e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 493421573 1250 493420323 493420337
    0xf0e030a09180f050112020310111c061208070501150303120c0210110909060d021503100e041119030302300c0c010f0306050901060f050c0d081e0f0601 67
    0x14260003034004410003c468101807003503586a8038100300c0d60880c3d032002c81c032034464a48560226040c5002e41042c5881e8140c525041401c0042801c80080d1803100034103800740c3c1c811012441c500004240c0400301e0291510f036885004914001d801c584900082e041429080041000002c0c1d0000c10101403018400021507400c00040083c0d1900c0507220719030303001c2c0d4180700d00b41c1e600c00c4895001c2c001c44ad0b0200c3c0e007480d141c1c841406001e0301e0072040c900607400142034111285101c030303072030001d6821200e03c00d80901001c3e55415095403041e41507804603003411364000301c1c8060b45003000130a02000c0ca010740040d2581e1031030303501a40e68034981c440100c80861145501d00f1042d0a5800d001c00041503980655840c0b03d19040315840f00e00040e03801e8041445000e240e00018800c1c411503043d104041d0680895900f0001c0c1960210280c0c113030300c000c0010400550300614000e001125181e604c40c1c407030040c1807c10310080d601d8402c09090542d0464000400c21166130081316007140c00001c00e0800c0c803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 493422823 1250 493421573 493421609
    0x90105010e1f02030d11120a0905070909080301050a081522020a0f03061d1209060403152702030c0f010e0a0e010f0b192007090f0e030a09 61
    0xb4440850011900103550100e024101e100c0d600070008140c0405502820814901c0b1002e51541c503010f00c08000500c02d804e040003800d1200d0580c4003504550140e0200c3e4080c41c0e5640c6564140e40706803104035a23140c00480100301da4203042c0c240c000a018488090b000c0c11524400341d5803100c2005094240720ba5034903502c0d910690b082034140c030020b0f4002c0c180005282c0c40b07400600d4161103e200855103a07103010005464031041680c01246281000064469104a00c20300844c40d0040e4401c40e0b8002c80c00c00000000540088540500030035411001c103071103103009007944110070030349072442c00004252450b40c0103a40c0443d400c1e4604504841c83c40045403040012203c00c04040710342d5800010102380401d054420544190480e074500b41440c0509480c1e000c1c035081400750703002451000c1000003481880d94081c0e40e950320301c02c00400c0c241107104c81008210346440c03050b500c08880a5511100003141128500601014148a200075490900d20a40040038511184200c2c8607a11104c0403034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 493424073 1250 493422823 493422829
    0x90804090204060e090615071203060e07030b03100218061b03070f1e02090c0306151b01062408040609050a210801081c0c050a050109030914090105010e 67
    0x524040d18880e6811900c807a00e502010340040021050300b4420f5001e10002505460203404030600c41303030b00e113904a0500c03059a68440c405441d559041c000e05498040201d1450542c58849104011540d00481c1258942c8281801d241c502c03401201d00b5401044000c040c0b00003844034801c804000d655040c0e41d40e0300452610f084241e22030340108103010005020051120034020240000d000c1d504d04241c58006160b80c40c070ba207480000c02500001e001c0300058140491102550b4048409043e84d200c90001da850b000c0141d0102c02042c02a000715030803518820001d10409003d41f074505482882889114038004000a118043c1010008513a0004040200942200300c0d5503503c40c1c11201c80c0e50107840c190400382800c0307400607014030341d11203000079aa03c500f00f00d0f0b049464040c0544801203150303407000b845c1c2c1c10344501a8280314a00e092440054801c12034503030840e020f5000003854420345d00d4010201c01503540210072802044030070032200e548500103181190030900780340c0309035800c0d074001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 493425323 1250 493424073 493424077
    0xc100504080a0602130e04021c141203150415140a0b0f0415031a0f121506100507030e0d06141305010e0a0c0e07030e0607020109120806060d0908 64
    0x2020160b0700035180e1100800540e500941100d58202d003501d10300c0ea4035100ca10044800446002c0c0d03000ba100b03c0c441a4002520742c1e6152001e000340c0310003461500907048a490240341d40904500d0900000401c00440d40780180e40c08040c00c1110f09100f00c0380029900c00d1410741501451160043c2d0034000c881c641c0d20f02c00403000500d0b40501706034071004450319102c003d402c140700300340c200362080c1c6105046900c2842507050f00e90801c03c04868004416003403084801e882c003216504014240c48108000c0400c22400c0396202d15029007260301d2030004140844000312143d002c0501006128002c006a041711490070701d400d054403180c4000e2000c2c10a8000340c80381c00c1d00303603120b4800e82040c00172007041c4404030161640190000c0c4620707602c003070b6503a40e900e410030005170119420310828440d101c460400c142c0c12181d18900850f003000607000b0b445c28804242c40c1540903079901e0240408020010f8401d05100c07880d41040d40461800f44007140301441034410264410b55114041c104008004003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 493426573 1250 493425323 493425329
    0x210030608070308120c04060c060903021015031b03020a0303030e0705060d05090622020103020f09032a061201060e15160c0e06010c0803040f060504081c0e0c100504 73
    0x412190b041d541c90405400540c03002018002142c000d070b00041411030150100c8080b50015030301d5000819054135008014200034904400310b00400d0300142031a400c41c0201d03103040a2150161142c0c5282d4589180c54600041c1d01070000300000d04208096520840c00c103040760b4141c10045140412100d52605121040d08901d6025070040b95010000341a46e10081c4070300c0b01581101c0342910703031028079a91040580540c1c0300441100f07090714015427003900a002e00661310480d003410010440300090030500c8114660004441103050110030314104100d041e4604015140d10786005079090b02d080c039620050142001307011284203640c8241e152a00b000ba0110f590040d50783c0c640001140a8404c10051601900d20790315180e0f000c103003540e14040690040d24161141c0c03003007507155511000d45400041040d905034248030207960100301f40c2e0003102e00c100d224003401c03a42c0700c5650500114a90f01403951019852405442105c405000070303483c440c2d95000c8413a034114000c1480b0031515842960 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 493427823 1250 493426573 493426589
    0x90c0c0736090506042103061a0a020307020a0e0f0a140703050408070c030503040f1a0a0f09030c09230f15120f030307091208040b03251d01091202100306 68
    0x9020002481780103a0b030300200c0f500c6c499041c08600c0210808509440d40c3e801409804c0200c010101d40240d00c0400601c3c520702c050040d02c1c02d0080301c0d000203146010030341c00038107030380030301c10402000a16003541c140d40036021100402900c080000c506000c098001c00d05c00526503110003190074080d8400070b40ba2a0399200c05018110b9480e45841d0b43c494002e403040c072120340741140c070114511400030b1559144050b031601c4141012803074041200c2210a0140c1501031109030000072020820141c00c8202803c0791081c0440e05d500c551a141113031805642c203250628680c60280040d07801c030000c2e40f41d00540750101c004008001c3c0000164200d040460781e6925120f2a886048280000b0001d5842002c40b40c0716008510358803420300e08070401c00b01d0018203070b1104200a01070382098001443e0404503141002c20700307407880410145407004240e44d101c003040036440054000202007800750fa4031442841c080382510301e0300c0640a0903074240b10b0001d20550024002c04a0240310f5404000100130307003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 493429073 1250 493427823 493427833
    0x70212030a09050108070e240408070602071401050702030604030e030c03010c0305100b1e0c010912020105062d0f030c22151202011d090c0c07360905 66
    0x2070100601015464440c05003c901d005000a210b140208598101c00c00c02070801c80e10f545d8104c4150681c0310041035104803100b000e1101050040c010000c0310045c2c0401e0b0000c107102810701d0365080300d010803a040c403410400d080202c8001601c021803a9a003059150500d08003081781040001e0a040714a40140d4040d8600300b9455652545a000f06005070108071000c0141910340c44982164410080c0c61015909940165010003240c0d10007403210000207030000400031032598035404600f1074400c030380300182e45600901282d46816825440061092880c10750f1150102c2c081c41a080c054141903481000341c071300d0340030180d2014000d004030441c0c014007102e00e9040e1114a41e0340342c51664210036240345058040c1b080032003000d100c0001d490450001c500002c600c0e42c011601e100d82d80001504034000c14001c48225214a8049030003006403000c055103543c400c8800381d00c0c12189912002c94458204c45000300001d0514040044900814240060380f20b06544032000d07011078a4002d001e4411 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 493430323 1250 493429073 493429087
    0x306051003060e030906071e021807080a091101030209040605040213061704021c240501170c060403020d1406041a15030d0f0207050d060e0607050a0e0607021203 71
    0x12469040903244a0b0508010034a0000b80c1c650741c07400f03400980c58105404000ca2008517504a00084001d82440d8040044803002e07804079441a4028603200021314400043c004600d4000340074039440f080d108410801e04c3c5540d21540d00c48840f5400700d41c18590b00040d690003a89554001001400c00a401035648041c1e41c0340e20020502c06100d4a0700007840d0034440141c401203429043d000b260000e014000f1495159184082c034481c0300f0b0101c1d0780e2018540d01d840d540024000c6c0310420600c0003400075996240040d4454840c0341215405c81940000790714035a1542c540c002c3e1010350750159080312421a5170300e418503000d200f400c104043d038810b0004200070440c5400c1c0c1000c0520b1400800a655160080f00010040b115441641e264115015034403840c1d1284010744121180d030310444910b180d50b003010519210051170b05545d41c584501150b140c41e40100440c0d50000ca580c5403071031400f004c4041c0144842c000c1034201d441180000794010a641c0e88100c0068410462004d487c0c1c3c4080e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 493431573 1250 493430323 493430341
    0x70c06112a0d0c0c090b01110109030f0206060d0503030a05040c03050a0b060415080c090a0f1a0a06170103150609180501050109051e0604090c03030801140d0c0501110106030605 78
    0x880008240052003107410b4029114403801c40101440e5003e41240c805904086000780540412001e80c0d04209140880d00000c00c800d0040e070710024080e4640c03034100460881c1c001d04150300105040e02911800303038018000b620010480e039100720070710350004281e21030f8074240760004041d0744040c103a4403d0510030014082e1101d210390003032800316010003c0700384089020012031a28032032078040340c2003486500d0f004d04100381d81c00d078004400140001d0103200f110580088949030300380c6d1420700b00101c141841c2da050000046000e48114204401035a01e5000382c030500b01014040200740c40d04008001542c45200c0e003110b0060002007805018480c09482d40002442d42c604044d04d140d802d0000009100c1104c0c420345000b00d00f804c00d000100d01a10039142420400a040305400540c1c0e0094040072400010300f81c0c0c041c40c4660f469400c95490a0001c00b18043c4150300e151094515000000006003006142c2084400a080044a07041d00414a40c01001540d0002c2c10003130403c020400148 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 493432823 1250 493431573 493431637
    0x121106030711060a0c1706130c0c1704080a020d1406182a06072f0a0e160c051f020904060614030112052a1008070c0611 53
    0x510802e0480c1d10719504e6207000026200311010800c080b0305040903140c0c40c40400480c240c0d12140141c8a4102c02c003940340300c3c504580300c040e91040040e06c030401359400c000c407069010640380106001282094284100c5c682c031403255840c000d00c1032283c0d004134420060080c01d07103401c0b100500251100c4c0e2400504248a04e49840041c01d564020070465100c0c0414030440c000e180108081200502c4500c801070100a500c140030590340400243e90721001c3d60381e025444440c1400d00c0707080c412984040c0c003c0c400001e866130070003002088032604114808162042100030f8034158500780d210f0040170308109017807100420746240100c1e4180700c22080012590024450701c00141d83c200f01d03055440c10129111000114211b040c0342c4108010010120400e400300092030040007a201820070b40c2e000301154910500c031800006640540d81441d4ac900801460300164890405100e24a000300008010300040314008000035980c44900d0403009440c0161220400d40c04e40a41d00041410b00034102c10b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 493434073 1250 493432823 493432847
    0x60f0905190905062203120c03060b041206060b03071409011106100512030408030910030e032106100f030504030306350307020604090c020a0206040b070507060206101211060307 78
    0x10700040112038000744103003170300500c032140c05944440d81c00700a94030300d9014190422a0104050301d41c6000300d1044450402000240717040007241d00941c090340307805020703103c0a62050b02842014410000f00603004a030003004012400f8299179076199070750040c2c401d010000701e807907250b2103940c04002c0600390481c4e4420070350300f04840e000350b2644c1410301941d80b0b1040d801a014150824003002060f401e29030743c07548100c03120b820003158003d4a0b10721103146800400a0380a41c0307408110300f80b184042d40040c142c11007419108040703030451646002c0d01e16221010200105507507031000805161099000ca0082c010142c07507821181241d00741c20052020051001c007240400784244080c0c0b11001040368030300703940074280d50706151518404100500c0c640034070030154084c08030300c0780060f44c460004101a101444d0a11b840f0980c905001d4600005504200150b600841c02d00461008420140c0100c0f015407144424140482c0350440440a440102580051010042c000050703081000506c0d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 493435323 1250 493434073 493434091
    0x905010306050a0b0906030a4d1f110a050f03090901050904030206270a14060708070e190b0a0e090c0a1e18030303050603010b04060f090519090506 65
    0x11340003400810001d41c0040c1e07003a40c2e040d8000c0c1d890000003128848442054074404500340034001c0c2091986c071a07a0065500302581914400142441c69008480500e050b070064584070025041c0d0300030804525440c883c1403080c8502a03060b102a160100041046103500c41c0544460313114880c54681d898001f00c0d0315600c948448000030905082c041801441207806034000c100342e403502045051428940628000310055a40c42a10614001c10008681500c00c3d14540529101c01002c1070420001405400811591006200d403a030350203607000084030011207003c2d45955202014400c4140e0030b0340003404008020850714506500640b040f2032414058070b004020340d854004001c07039407154651613030200320240d070404481003040b502d1440002c2241440010001e0960110001e07240740e07807040780002c0e155010000c0070700302801034807409036084c0c506202c0241801141d1a6070001d500458541d1030b074a40c002100c0401d0740c1000c0714103052110040202da202030030f050f80c0b201011105910 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 493436573 1250 493435323 493435331
    0x60201021b010b03030a1107030b0f07090605120402060a180e15030f1002030417030a09030f050a021b0f090a0b0306150d14070b0d0b040506040c05031308040905010306050a 76
    0x40c0c0700040c06003089100000300690315010701c41c0020b503003240320a444400fa920540074003000140d000201e280c02002031660b840a00d240c4580010304078000750300100c0c02c01c0070a0080030b61810b000e120303040d0072680c121400380d15880c100604460355048100c0700810148030350f500084d2041240702a602038441c1c5065034144030222014141e54540a00a00f84240d01200c0e201d41980d10550103540c000340300d032101c03102c40700782c8548802a41d001035422144480e07640c102482019000040c4a1800ca002e0070041c0c101312184130041e49811607000c00004480d40b07016140055036400d41541e10000c03004010310b800d810300c070308030038020300420041e98082c0c820440030480305040808581c10340c0303500401c51410428241d58503124018440140b8609229001000c82c160b0f00b00e0001d0200100b5a602c0045d0b8002034004002c25281c014080d140502d1400d801c03034034165840750803070758041c11500303d80c07846d001e8174500420107228940c01386c800b41d0b04d1b05002004125180e006107004242056043c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 493437823 1250 493436573 493436617
    0x7122715090302100f0609050103140d0e0f0d080912030d0e070e190603020301110d05101a0f210114040e0303060f040f1a01090b040312110a060606020102 68
    0x1044420010740640542d2007064036000b8080d0540008000d102e0440d004030b440c0e40d4405800040d5070080c0c004565008031300102c99524041003081c048046242d280120b0005050008038448030b030341450301c0b03010b00900078001080c060403504440c074407903000d84100076100d81440c4041c0c4070f03081542c84580e40d81c101504e0914124000401074103070345960083c1c540644483c12080034800c04401c42c013444989800d800005640d0a00c1100c511201c0714044503654203500100c0d901300c600081a51042c12200c9a0510106981c6c410b5043c000400c036250325501c00395080e4561407401a10300c000c2e01d07424110b0501c4021802000002c2c100c550085001a0303c4140b0f504010170346060142d507030342c603038002e10000d2418034104042e00001c0030b000d400082c2d4101c10b40300c0b034001e5a1000503c9104032a1084a06c401964450943d500500402480a003880d00f15560000404403001010b8100602c050300199030075814002e020b10254441c40403c221982c8110180c040d402291b010b44194001610003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 493439073 1250 493437823 493437863
    0x60f03050709060c020f1023040b030708040203120703021b010c03020a0b19150609080f0d030b01051c050f010f080304030f080c060c030f0c04030209071227 69
    0x1a03401129140c5500c9240b904080f8203c3c0d900c04004070603680010030003056115030f169640e400d412841c540d5942c044101c44091100540c3d411038080f03502d003004c200401c2180c0e2100d1000d50b03800c000b20740f0780b000706c645a074000285410a2400c0b2000c40101c00109201095000245103550400c0d0280c00f1100d00100c01c010748802500440103400751300003ca04800103003000c03a09551228541010f90301040200d41250111903001c400d40084814489042c400e034de4000c1c03044801854140d00415036002c1d03240c02a515691040052800c1c5900c822042c0500da000380107030350703003122040e03540343c1540900940d013800b40c00c06a4001403074a140d00000304041c1003c1c10400e081d143c480009524252440e56498002c90000702d0655182900340006e0140300c2d42481030343e00440b02d40a02507240c1c1400d203a991030342c56002d07129591006c410001080181c40740744c1650b40c00802d50030994040808850000081e040e002c80ca803174802c03000aa2000b9034008d2219660b00ea034000c080a4400f01d20316062 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 493440323 1250 493439073 493439081
    0x70c060905030a23013e0d050402060909040506040c051212030c13030b1501050306130b0f04020301090e060603071412010e15040b060f01080c09030106120c060f03 72
    0x90907015040200d400300032481c0d6418000d403003a0100c1552a41c410101012403c40c1e0a40120890201c50090301e04086d20882083d86a00001b51071045500415507040400902c58249030075001500c50001074290755410003510340246010742070410501d40f51600c01c0d2103200403a0304440b40c2d000700b4404105404d101c403003002091074000c010050310010540466a6401c02014a03500d5603040005c0c00c194000d54014100541c407443c0650170a040001c00d100d2640840c02e00d09040010500402010b0b1341c07049401078100722200800030b16480d840c00403d40611007940c58030341060002000050041542c0d1061a10144450030b0314041d403155801c0540350308491040a00f94000400024070902c0c2150000d041c8000c5400001001034480d40a14103200320350b50100480e88001d01000705000c1298002076104a040f2912000c603030340344c00080c000710b8000c1c0400040307080110f030484caa500d00b503020402030306807050948841c44680c640384021803080e0240400144241204000b0240240a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 493441573 1250 493440323 493440329
    0xf07020303070c06090212011d03070804090504150614011b0b0f180f070f14010206040605100f12061503030801120201051209010c0e100903140307051002070c0609 72
    0x1000e145107498541044519040c1c124090741c0d0940d035003a000c001a91000c1030074040c04024000030510614031094070840c60300e16890301d89941c00820080d000504040b0480c3d0a60705076050004064956003040100b1018024440c40c00e1407511002090280d460030001456080036614511510341024a0704106022500c0007071688070800003003100012408801d5070300941c0250648840300c2c100d040d9a180500480340007081c0c0d040440305010132941890390a014102d1404040460101000002d56503440104090080c40c0d458001c41d500c124958004c40040601d410403020068441c00007040e4181c03c2c2c00200e50b0f05103400308210034010300c00c601030f0407245c164440c0902caa1801c6007800314030750600c10890401000700200d2040b0b8a0b1145294007801c840800080c4014211102034131018242c05500c0c421000c03d084003005552101c603c1741680c2e40b1000f020aa840c4082d002440c600038074500900798020b00308488510800c590142c030300d00f4040c004804909a8404040d180c00f400c42c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 493442823 1250 493441573 493441577
    0x70c0e0604200d090f0c09110301082109030a0c1d10030f0602070614041719030b130c020a0309230d03091a0c06010902120105150d0203100801050f07 66
    0x41c4804203112102c90141c12031000998001c144c504131980c90541c00081210112a2400b030290107001c60041803080c514462203600d5464695418011916903904090502c038001800814203582d0345010081603600548000c1c04030307032000c02c191400c0c4486001d24014064242d9120700410a000c1c484e04e15a4021911075505a88903419031315100c202020189080d01c02d65001c010741f4001600c24418050741c0b042d001e100199505041c500400a130007000a01840d500043c0203e510418117241c1082c0c0c0d0512606002448540321008181105c981c0346180502c4c130320b0407014240c580d4020840c0d460136442640d5400c01c19444075046030581501c018166034520106070001c00600700302d400700004600905080007144d5032070b5401d20b0840958110030070000001300342a03440c0303882045803d014016201041d424900c40d05075800523a20305214291162280c0012110828107207400c5503031041103000d0a41d5203203441d42a00604080c2c522030f04d1400e619080014104584544245001e00c1ca65 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 493444073 1250 493442823 493442861
    0x80f190b07030b0d06060e0901050f0619080604060b2107030b15030a11012d08040312140709080d21020903010212070e090f04230102070c0e0604 64
    0x9886a848500000702038a041c5551401006215950800f0150566214203070124042e401c0c0000e481050034050840f01c0c240e81030000b40300180d1400031413903a0001c01521044461610191414084070a030f41c805481400740074180000d1103c0358010b504d908000341e13501c0e41c1111510360000c2c805404102e800255400a0744188000b40041d482d00d80c2003c1120502301980c10040e00113400c0c6060a0760440d000d08501d00c1800580d40c212901040115510100709000c440c101031081d80f041c5d600030800d0800140400240801d030044106154a5505180c20459404042511543e1480641ea26800b15403c8400000c0500d000034920824110329030314840107210130106e603071110111965000f245a000c3c051181945c80920150a00100f01103502d0810308042401806803a05038001c20b003e00c01440801800c0c00290789100c0e0015030049100d5441c00101c80603010030300d241c00c0d445440d540005116400c0c890b0101c0d0b0b03030058610b050300f03c04284d00c0f00c1040004540072031009116105107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 493445323 1250 493444073 493444123
    0x5011401060504030803150a0513051006030b0603181203090f070b0a1d0a081f06050406030320010f050106020a0c060509030d0c0809090112060b030102040b03060d0f080c07080f 78
    0x360503147d0031440503000b401801c0e103803000140d408600d0414400407070395942c1041900104010700100602c4582400c010b001e00c00f2021649178440100441e40c074110000945e800140d08214003000c00c114021060b4807418403c60554851f2581c200d0b03408584203486c03002c20200010b500300c0700244501d44400e4a11035545e07540320b01c81441c2c159030651080100c0030000700c0c4182408100b040300e20010110b22a04400a0a801100c2142e00450702071392030548140000b070b400c0440440744001954485400ca103000080740e014122401c41604001d00348400003501c55000214680e80d0382c0f040302f2408a00e601e03401c040b1040e0103070303080c1198036900052100300f600f402070410300e80701800303170310281d02c0e000180300441d488010030380c0700c40303a0041c2c0000e4120511000b407240201e02101100213619280c58102c0d011400c0c040500428800c039041080740003005007403003248013040da0108074142c9441c101c400071502c8044074804e44625002e46c040d1100d01030f0740407420286174601e0b01440034030f0f545 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 493446573 1250 493445323 493445341
    0x206070c12020f030a120f0207020901030f06060f1409070305160507030917030703020f0d020303061302120c0a230307050a0909021602011209030e120703080705011401060504030803 80
    0x516400700002d500030340f00340c3c02074450f082c0300401810360300341c4035102c02803410f035618812200b01c44500007640f4030501080d00103a4482e00c84c4c1307044039006003c0d491401702e98101040140000c3d440380a23400541d410020b180440c10030000300401007150000c0d903036500c00500358141d9400321f4141f903990811301055500765000d2400307000900e009180000d115030b1250310540001c1e25207944052180e10201c0c0301d800f0598100a010484105000030304088170f503403000650380b408050070b010304c100c030040c81e03440300718070700340c0c1130300c00c0c00f0f81c2c1d0441000d02d0f0030040901420b0313600c60528000004c01c440e0560b0007025a8010391400f030050401014a143d5540304102d41ca5005072820780c04020100d84005440001b6001074103044e120720560200d410f000c3d10000d845c0c041d09000030b0034081c0c2440711201c0400e41000c048a80c03d0425540046c600b012440924203142d01504010203102c008035000c0113204055004c1405222030b12200a00c69032100415902400380e440300600112080000a60100b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 493447823 1250 493446573 493446593
    0xb04090c0b1608160b18100c0e090f220807060b01050c070602030406030501060f050d2a09050a05010221070609020d0b0a0f0b03030d090213180606060206070c 70
    0x140c01034a003050702c1001c1d035031100b455602049210382c0004469201d4024400d6440c9865008480185011411243d1b03610325a2611203012030f08032000e50341e1414000c2c10b405410740d62001000102200d43c245402c0d442c4420030b080680d0b800c00007128100030440d585184800001004ea00460090304201c0c01d0303034401c40034001303490110303040110501040c40000c0301005100c015140c650042d40d112424500001c04451050707200c0010045070391920b44140d90014111822031614500101d00c02c11500c01c2e030780c400000981a2189080700c0c000c120005980842201c090311411074035115010703980c100485c0c0e105c14910360000c9000e0780400f054103031065040217000341d03481407501040c071543c00d800203a60315004c000d050b01d62408400030000c070000c00d442500c440660700d000401000e040580441d50305c0c0501a0421280e564421418040d55651601420344c1c40312034100b440300342c0340c81200c02841d18142e18101d560501f0288041062030010030a0382c0b044c85aa52141207103800c80e1210340d05d070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 493449073 1250 493447823 493447837
    0x504030605060d020307030f3503040f08030709090e2413050607031e0e061f0e070f12140a050a0b210d020c0904110109090603060f0b04090c0b 63
    0x11040840e10005172010303c1b40340001c0d40600440307402c00791141002e003400100406540c4031490000149511070a110300204020b0410181329910fa81d1140b074044019400544050b2035441c0c040b0400901c1079002e030341ca40603203024090500c410440d40c580c1d51b03941c3d080c90184c5290681d0350200311b0040c40d01440c409510450510b1604005a032507140d8a06008090707445100190f01c0c0c2d01c1445201c1450000051041a8618100b040e20018210242c64040141c6841540d02c42180d502c41043c1514a20380302500c11400c60344500c2c100810f02603e081d91001ca08030114070706104030101403405100d0b00d500d0741c3c50341c00044560764642210800400c4000c05003141c01c1d503a0003440345541c99002c0980c21040d400440c1c03401c0351080800c060320745142070002c0c4003190b12800c07144095444e030305001c40d085584126100d5061a8010040c4e805240030340142d00c0b01031418900100f40310319504114815012440c04209080030101840262184103402030541e0850440030070056020100804e50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 493450323 1250 493449073 493449079
    0x6030213090c030204050a0b120c0a2336190915050a0801090f08070c080d030c170c1209031b1c0e10080c070b041b060201060501050403060506 63
    0x1500d071200e1030100c4054659000000340d0200d020f103d503017444042e010140c41340a041d9404d28403d840c021401d1400240341c801600c0c0c1c00701d0890820340c0a803095803814903c52203400190b003500949003a003a0030021188500c643d148040d41f03902100142c0444a0202d03440c40e10a16003404010f120000082c2408440341c2d50491100180700601c034860b042c50442c000e18200f50080c1341c4810000e1210542c1c00460b01d80e450205220000385a88001c1c0b15550360215065403929400e0410503414030107503211602e070307024041c0c9455807264580d003e1101c1e0105038550303480794a0301c0510f070341200004847c0c0c0607560134200b01400815818043c0c0320340c40080101103c5c9809060801c0748090031071600701c844550300000ca24403041461034101d0100c0c440910748030b03000c0401c9800003202c240076280c0304d1081c045203070040b80341001600212070307100e81c011811039114245850404030380c102c1848111f0094100d2400461310034418003580c801c5071016034074a41040d00350f0720744400500c000f51074194 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 493451573 1250 493450323 493450357
    0x11d1507150c20030d062306030705070201030b04060e01080d0305090a110d0620180f060f0a03090203030f0703080f070206072f06010806070c0c0308031810051008010e07060302 78
    0x70350341c003150003001b0240c01c0c085c544460105e4404a2040444807201000d40b20303c600b8001c02c103109a1140070380d03c2280d02460041501e0700508082001881c458005480750000c0e0400842d42000016081a085c03001760360030071503036440441507507e4950b005d00041c5009801c0c0007401051801c400061340207170203003c0001d085246d0819001c1c00412083d41d0300c0051301c01003001e41c080105402c00c8d031301e080000d45440188003940c100190607440303445601d0498180100f2414085446640040409507018048036900d074140407a42c030444d040160200d00242410f0001100b104002180700d00460858005200c00c0c0c54410064072090400b80411701c1a49004a0030100100c108200420780010800908115410040340c2ea0070300c00c3c020081400c0c4074958266000154040ba82d1408403500400c4030781d26622811924114070803284001d5615114036158423150030515449a802090084907455506940316000350a80d003001100d0070007a0440602080b003a4002d40080c40c080c03900841000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 493452823 1250 493451573 493451587
    0x4150e061b160309080f01141303020a0b01140915030604080c121201150504080c010f09092910020a02091e0106020c03010b01030218011d1507150c2003 67
    0xc0c410554182c041c0d00241d821002002840000d00c0a1900d1602a070001e000c603008040301c4c912100d1010b800584040c1c01040300c002454824000900310690000e81e1000700d5070340d21882c142086d0b4200c007551007030100d1300104050030001002000324904c040c01a10181d640c6442e501e88503005030351100d0f928000c84c0410030b0301d660304400070004544060094a102d505003d10080c0041d9101a0701d420300c2401c110500c0714010000718081d201d0402d280906103032070222001c6400911541c05034a54508000e83c1074a4907207221810742c80c416070308244802d0700c1c3c04e1004208100e014041080c01607004600802c01506025030800e0303028400050802401d005a28850b42c4038009a01c450300580100e10808000d103802e000d031000c2d9100c2442c01b0f60038002c1001481d44c0300c605000b080350600c02243d008403104080c0324070383d4625400044c210a10f0700c0405611100a07803103000100c1d8605010a24140034013103501c038007401c0911940d60315116001008213042c404510110716a45440240194 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 493454073 1250 493452823 493452847
    0x3120406030905010f0b01020a08070819050703030c050915091206040507090510050604090209030a0606090b030705040e060c0a020a02090103060b0112060b0a03021c050403020604150e061b 83
    0x10002000319603400200400603003405402c581c064070300e083c0380a040000604480c3e90024a00e00490341020100ea40c8043c18900100503100d400d0940100ca038240895001c1160000c000e4002c01c0d0003510180700f180e0080d2030840301407083e46000c40d80031980404100c5d45030f51001c0a02006a80a48407a500848400c1801e14081e011642195181d000e41c0040c0172581c0f06009468000901c0c0005144041c00c2c5000106640281d0182520040d40030450030301580d010041648951f4200c80e003000742c191200714040c0940906400c0e9402841050740000303081c1800c0c4180524005c141001d4299910713400100500c560002441070b0862042c515140c026030b41c0c40040c0341c000c1d0310841e0b00180b5040400d002411a041c200300300d4005038a440b80800c414002d1f030f02112504040c0e807030016a2140e003403003890054a0749680c04150707541f8000c1000101900041c80b24015802000041140030380314602005440d5504009400c035042170011a00c2c1e4003031124854170f816000300c00c490400b40701c43d8075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 493455323 1250 493454073 493454077
    0x2030102030f010f0b070506042a0305010c090b0301050303040621050c1c0504020f0909030409021801020118050a0f0f060f0c030b030106080613021503010e04120305240312 76
    0x44042d40010300e0004004a02018002100422600c0c2c07403d0b040c80801d440746134507000020710180424501004041c001070b00b2161a00f1640500441e00d1040c0307850b130501600810700030219002103515000e0100b2829949415a81250b6006008610b0710741461011217070781007043d54120000e40052100300c81e4210301c0c015203101e0403660141b9902c41550801182c40180800396034010127140078140000350702c42d8044002c040344c00317035060641c9031a002c1119141d481a54081c00d5202c2c400b04001d001e10170750100d8821400740907030081c00683c1c03000446101c480300e040c13070040150340301e1501c1800107886c54040b58401c9000e5060b03548604144e44650064640b5510710014944c0e85441621103960540700d041440342c81038000f0009181440c11042d510b200207840809074031800d80e1010304641c2c1e0f0a190b5800340c2c4212440c0b5840e9655040c108640340313002e94003211082c06501000510a200303101d00c0c2e200303070300611445814155020311041c2c040411145240c0501440148120811100700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 493456573 1250 493455323 493455331
    0x3022508030d200a020115210b07110d091d190506010519030905060703110901141306020721030e010507031211070c09050424180b1801151806030203010203 69
    0x3040a20395500224030800b20ba40185120104045841c08c21401407801520103c3c1d014041c0c1c0e100c0e450360101641d41c014a12008607491050610340d0301030070751002d1500704440101c481300502564202a82c503002108855207149220038480a2000d260684c00c0b81e50010300c18140302e854114061688100c82c050021054007180d141c140c00b00400a040041582c851044d1500f00300001880004403032910071034503080d040098214840882e50b501e10b08641d09400640c1220583c43c0c2e0700e0902035207520b01071003803100c1041914030350300c0c24001e80d4405c1f1503583d42c59514241003a441c14019502d58101202c01e0b030030401d200003440c500c3d40e214440c2e040504003400160361102100d00d000f80d183c042c3c6400540c040f80c1448107100018220381000c0b00c5520001c0140f48845180131500c40040100d01400001200196419806d024550403114014441002103203060500b10700800d09a0f800390800e002c20046208007004906001508072040c00802c4101103840c5903a500000e0a90700159 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 493457823 1250 493456573 493456577
    0x3030612060603030f020c061606180f020a120309090923030405120708100506011205040b19051608060301200301050f030601080705062503022508030d200a 69
    0x194043c003d141d00410114200c0446100034030f00d481070040450b07124002c0e202d400310200c481070504420002030741c11000ca111781d070a240900640c40b03420107020b460f158007030503406034030031840103c0c0081144c001e40c0e84440d0552912034030180fa03d0280c07002000a1b003c26101c0318000d5101415460741d1210401a14103040025504e450a060820295160007228003d455201d0402041150380114040303400c03441d0081f00003500c0e07a403900103960724400801825019464181080300b0002c84c5c600c454007a48a8008015500003280520b1084139401d0b04c1101000207070149002c1307a68801d0ba23030716500034030240012441918240210140441c04820f5942c081c3c40400113110b10f082070900c00d0308010044005040c2949000b80c1183c54031a02c2c01114021440040c16260011704100301003401c044400d9510110165410002d448041002c446002c011080c1981a2070f62034601414003610401e2000d10314000100350701c80010700450f43c1c0228a1044000110344403000c1002611145142d6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 493459073 1250 493457823 493457831
    0x50603100803310f0b0c070302030f06070201270f2916050327010912080a05060603330d120807020303011a0c0c0306010620030a02190303061206 64
    0x452004021502c80300c0d8402c10b54010358001300701400d650f9440f0030444943c2022280d032800003101c5241040d0890700065007600c1022075130080704c10b001a90034030a10890b03008104080c09041d50001080c6030098044180307151060703500c040b429404030f4400c1d1070b200e5034401c0c071202403090405028071041c983c81c0d010031168404110b0580c8010f208090075401900d0190310394070b0701c1c405030301e201404941103560750155045c2c0c4409541c8250301800840e40c2040c81d43c0c41d0f0800b9450f0040a10800f11b480c13012041c1054013152485c01d01c2400c0d81e00801451103094440d101c5035006030154592106451444a92a440c140c203540710b9200e00d844150080701000d040e020402c80140c10144054034072021540301b0401040707404200d017034580c05001d2650704503503944c8030f0000741c030320302265580c1455142c000c150000500d990003e0f20640f100022070351000800c000d010a094690144010b200c000d41c10040002c030700c00e10708200c1208114480d003000030741c00e500c91624542c503118941003294005d82d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 493460323 1250 493459073 493459117
    0x9070e0a0917190c080f030a0f0c0306030302030f090a0306050a0c021c0804020904080d06180b01091401030209062b0e010c0207030212071a0a180609050603100803 72
    0x181e100c00b074190044a03000c40d240c24104400d140302800410024400c100003a20490100160741040f9480491841d880c26203038201004402e0040c150079000b01c0c8418a460a40c0a040d4040d0207880b040703d405401079801c1c50030f4000345e0102035200703414643d481002c5010220024030940300e44e40c010f00c44483c001603950701495010b40b0340410012615140f00c1000450301100364441d01040d4001d5050f0b5030768040e80c589140030f84e0a80a44100c51340e0441c1423150200e6080607248076a0480d00140350305204540e1070400642c1c02140781d0040301c0070a019021940119400b035001400180300103840e0307034544401084440c0c500c848010144030f00c22505484da403030005080c003600c2c241582001c002c02c40c47c0c101a41c003954480d000e03c8001d014400c4000590781d11942400800014800d1008440d010042d40b00b015400f0b50040b201c07a00440c10899864441c1ea440054a405565a94544820f028144010004a90002007494540f00468900071071404804d001420140815401851621103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 493461573 1250 493460323 493460333
    0x2150903070e011a0a0c050f300f0309030c06070c0b0c090117091009030504050907051606020c0c10030f2a0309060905030c0610060306061709070e0a09 67
    0x101c42d5000b180e8408916005110468404903404107074500500c1c140d40e5280500000e1390b480c0c0c0c100c03030090880d010344449451203900106082c0035a025030f2050400e8030104040106c4540502d034444400554140b0911828102500c0155040312001d41200d0030082140c1110345060750440729080040c6650b0002e50810400301da0094021081440e10303420b060320303040004e00040350725000700300c221040070202e10a03050520030488000a40c2505000c440102d003405061603109120345405008500001108144140b01b528078070000d00b04c448804441949414020350060078509149000300c1032056003580d0b8441041d081204a40c0780840d8a94013812403004603881590070301d82981c1007460010400d0390000c074501445410341400280410241001c0000300004200288644000114a010214005040361252444022600300c1c5d6880c0c42c03044041e90b010307210310700110340a1014140110049125254803070450002c41e1501641c400701026490400d40311a030b209130762890402e003400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 493462823 1250 493461573 493461583
    0x5190606090e06091305030406110c090106080f0907080d0f02010b030609060601030207060f0f0b0a1203020d052107051b030702090a091a07050307030b030c0907031802150903 77
    0x8855401c1400e040d5141c030901007040a00145294814a2201c00043c1007000b850b24002e01e042c0c1240072a910b65403200d00140c00c1c0b1060b1403001090388a00548031425141c0140783c94165000b075655980ca07130304c0310030700320344d078070601070704804a0707008008010a070361100f003211092000165559480c100c0034080040e007161421424135010341c2040c2e08015241000080381600040c00707190061b03449415007090402803d1010780312421070b0412482142903c015005070310034240c201c4040c0741113955881540c0c0d024802980042c0540c112a0005000078021406413940e03501d01d0400c00303610050082044850f0b04100c4010002c0f8101184003042c402454110081c20180f00008528002803600042c96409000f00601c0c0b00d00d490301c0c80034003003000622400d4042082d00c4800c0850707041c03008001e00a500116110310001c1d10700658051603203030009483d03000d8600a009520701d9107800c501100074104000d007500b86484c0c1c070460f102c010b071100083d0203030270001e0002003603d502000c81014240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 493464073 1250 493462823 493462829
    0xb18060d0f0902130c0e15041208071a010608070e040209090f2a07060b06130e09061b1902010b190305011503021e0102070504090b070f02010c1b02030c04051906 71
    0x207217864190300100b904103101c242d44a104a8a4240c0618031102105032440350341c000000000c1048034900400c8489005410701c14402d46c941c0c80d10700d04a00550341e080009101d100300207800700c404150024000c4901c410300c03030400b0b000076160080c100041543c51805490141485407090100102c0216481030072828045624022a00d03460045101c8064000d00344c0103070407984d44c0c1411041076650001204c040280c4880002c02d150baa5040b4002c104c0d0080302c45501c03500400c400602810441030034805080d00390701903e8104040500e4244c3c480700110540403d6640c0d03540c4200c83c80d5151060019418290b001b04070f0120b04600e06035094a5188440041000c442d120900040c0e42e0006420100708280421707014500c01040100d29248440c0e005580bc00e180c09000c42c1800146c40003680b01e0130041e100c02e49003120030a0124221b42800001c078001400d0043c004a188983c003410141d500d000074116049c48105d80002400c682c026101131240c1c041c0c610456040d010399000722002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 493465323 1250 493464073 493464109
    0x50a2d120e03010b0307182a120c05160c030b0112021305070801170709050703060e15010e0f010e060310050a06230c0109051002030a0b04060b18060d0f0902 69
    0x1840d510318020907070381e0f0070502800c004040d03028447c0e0443c4410794010660b80e4210018180c4800c00302d900c00c000c1410002007000050a81d04502c814040c450044800710b003010ba8032980b034030000000049000075210720442d000c03001110000b020440ea005500c2c060641040046e6014040e4070420890241108000107050300b064100100f1640240c206c034110307160030f414004040e81000f81c1d6801d203003031600b0400c201c51078182404541941039102c4016180da000400c0511388030b110a42002c0d81c2c81c103107a50700240d4001001c040c9400c110340c5142c04100181400da03050890900020440d4200311103100d80544185420466480c02408481c010501814200e18090640c2c0c5002c030030886200400f331a2020000300850406025031003030361642d802000361450503c03503c001d003021398026a40c481501b8288509030390580b03814810b440440d1249070350b0303d1a01c181040350310703000c10410a6180d4810010721030084109040d01801140307062401d0b0000d42d01c00c1d80c1c410465400040b01480b14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 493466573 1250 493465323 493465331
    0x60c22030203072d080303060a060302120a020a1211031f1d180604050d031a0607020d02060412111503070522151e0309050a2d120e0301 60
    0x102585000c40d0030402d6071284070b0074200070100503032242040260044c1c109030b40881c038140005c101502102071400303041d048646d4561030342d44001c11426070041c0e09450141c05801008500c01e240c25900403d9443c140d4200030120741d5611f0481803c5440ca0038806400401c0001001004030041d02e00a0490007424000715450f400d0041e9114050b08103007299030101114000700d917081c200005000d44440710300044504d40e2030285003c507114810b000f44400880d0418548441100b94140d2080c1c105102501485c20604540c0820090f246043e40c08d0360001010003000c84c410684514205105014490300080000d10809003c411070070803c0080a21341d00780140030100340e11134103c0d02440c1804007110f03004004004000c074402015030101c0705804a28440105141c1c00a070200720032070822411a22003002040154180c9461803401409500f00d102e4600020b00801c80c44103940801c091003500e00e5034080201c52144102d19025900120f1000c030800080f81d000b00c0c18420f902d0141c000784 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 493467823 1250 493466573 493466579
    0x1404080105040510060b12041104020706020c0c031209091915080c15030c030910050a150b070b01060f09180204140f060d020a030902061303210806010818060c22 71
    0x114186c0507c07482d41c1240c8002401060500081603207603003141d24000c000715035996641c581707440298030403049200307103000c1d0140f0000149000f0907040410f10141030708030f1900c881d28041012030900180000d943d4504024554104205445030384402c14256451110103800e0049185c68420301e800c2461150503980c0d025056101c1038025250003409204a0a45985800e0f125a003010785003071110112507c3c1c0070070000545070300c2d04480461040345518104494883c18002d80600c01c001000c3c0031800c80798010480710b803146180001c814441e1408003440c2d9110303280e000301944180602c00985801190602030744a0491038a00540000c440c0c0904c65664103000c01c0305030003081c07041a003060703020820000050007a0004100c4650007001c4e0340d5912501c0c0190721001381c3c07900040d100d00b07442c41c100c80080d08601b041c141d05001e0980315240c2580d146001120f070f103180285180c640310794400c103644650078100449801001c14111f841d486085c41140d41807000001a40c180c1c078001c40708020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 493469073 1250 493467823 493467839
    0x15091b02060c09011d030c181005060306060a050c0708060a0f0c050c0a06050601201b06030708040b1b031509130c09090318060305060102010c081510140408010504051006 75
    0xc002040c03820411100c08000c2d1100080c2001041c02010750041c0c000d90710840c2541103230005601c03440c1d051118650580d118000c0c4403150204a48032900702c041041010901c1f80070304041c201050b5520115820f481c1c881d6550340c00d0540948031350384410740355105c001d0448154002d0030412809880d203d8144004000c1c21961410710030000340c40346907a040451103a9105200c0100d089041d032072903a40c41701114600700d50b51100c0e84629110700c44c01280024091410008480c0600300554070f060b642e489035100c0702d1140304084c3c80d52582030007030a4903640000450700036610500c0d04026049008902c4024451f4600c0002d00703070a60740340301c2401500000c160040f030b0f109968040314000385507407040c41c0554070040380c1d031100381046059030300c0000c60310b61640010f845040b007a8024013950f41c80d074009540f04201552402d401010811103c3c0460a0464581c003000c0c10304d18114000d03003544000344040e68443d800900e0541d444508100600c6020414074180303e4240d48104041ca103840b0742 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 493470323 1250 493469073 493469087
    0x50409060905030f251220071e0b0306150307170c0702010908030f071104020f040f0f0605031e04030c060e07030b0f0106020d18091b030b0d051015091b02060c0901 72
    0x1b120510019a0405100c2c2c8482420b100ca103140c148100e51081d61078040003505d800020908242d0702d550f00502103594010002078038055403010f450011301c0c1401e80e04450840d04010501c408000b5410031010080c8881580507001d0085640c1c1c5d00c0d41d4104a000062040106402c000c07a00d0340200000002036003008116801542c01a0b1405408964a80007801a20404240300c0b00d2010200700031075865403000c84001140d0805440d40c0d5003903610380c401e6406000448418010600c08080c0d030105151100b01c150340035100340f038081c9100e0f43d42d90300c0c2e4044502c0d00600d200a80c1c0400402c1c404c01c255000c00c1750708069800341407041585000d9009541d02c520313104103001c000e94020801401c418003c00ca00103090343e1242806034800b4070b600000c480c52012004400241071007004c0a06e07043c489040b4070200e4000024142d4499403101c004042d202400704034800c0c80444200180c41001403007081c3c0781141482010100300c45103103000b442d00710082c24051503070170304022a2503942c0e00944 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 493471573 1250 493470323 493470353
    0x10020d0f120b09101805010b040b071b0f06030b03030f040515190518061c02130e0a050901050601050a0c0b0703060b0a1806090f050409060905030f25 66
    0xa460001ca01c0c140504070040c142c0782e01d0b002e030050482d00034007032280c0a50382008203441001440c120810500009041580c1c030a209011540300c0c200f1081c0f00d8812001d000f0240940241042d00025802c030320701201e10003150b40541c100705105d132002e0089a40c9402802d88083c4200c0045042000c0001602c0306446a44a40e0303100d041d1700c0ca801080c0a00d10025181e000c066480609400010764002821590000424040200000c04804002d14040c03065a4194209005201c200000051140020340c407516002c20007071010000002e50116a01d0314070b108072001540030031541031400c4451b0035030300080c01681c140f02c3c040c4004071202d5440200e055440d030b0401c40740306043c0c440c040242e0051042d50000004040000740082107540c100c81c0340101c41e00358040c1040c1850382c5060496542002d40940300040f16401000c20541c607260300041c41140c003d0703000240c0e46905558070752540c0c0c0142c0040210f45004222510381448c604074002c01c0f0194001642d070454003640c1c4899404c40030036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 493472823 1250 493471573 493471577
    0x1308191b050c0f04020a05391005060a1d090102091216090e0d050f071e140f120c151f08011806090c0905070905030609030c0a030c0305090303040609030210020d0f 72
    0x1203024090340b840f9a2890010301414030380da40088123040e080e1616280e400e20085141402c107400300302c541c184944c2c00030407101c2d203588900c05501c407510074141c0742c4030281000407d903400303000300c820642e516041c07048100010030090080c00c08100700070f0190152a88410042450078515682c0d40b6808500c08030340840b2403408940c1c0c1c800c01540f440150141d03130005400d010f147d1030340c1e509400140c080009500e00075000116240c81909086030f0340c0c450004500c0701d90b00006402e43c403401d1480c024103812031044040d580c1208866400d1002540100d5680c041d0741e040c14243e03001507c200001c0c00162481f00001d001c0d0501d0682581d14400481e13800608841e904c0c0144018402d00b41a594050920b00c001840380d824001c0009103c0350003801030510a02400d40800d910180010032101c000103403c02400468249803800d1341c0f4030041c4682074091020401529201d1b40d018030003080608010744841c45942c0c00c0d03005000c4400c83d48462003041d50701401d44070700241e800510321010f002c014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 493474073 1250 493472823 493472857
    0x8060105010f0f17010b040302041404051e0c0d03020d080108010c0e0904060f0516020d05041a07020a030b01121101031a120c041d061308191b050c0f04020a05 70
    0x40b9021038800a030743c03484e141d0803454070b070010600202c2e80d0002e0049078001c44d4103112886c084601c841600301e0a0318018070b2640003180c2e0401106485a0202640074400c00b6a191180054041410081011401c1300140c010385050210107800840850140a00200030031035a5400003001c0d1001084010240c404e0307510358006010002d254102844da490b15100612003400d22042e12007a14103802ca040000d4000d180810003143c0c89001038800301c9103030000390740c00b40e45540744026280c2d001400030703a00842d640802102285c070800c800c50080c840c050020b0f0f1102e086084c54100b40c1d40031543c541c1010b060450740103030b00e13406041c2032041c003204a0302c0c0d1128024030b0900c90700c2e01c000310081540050510f503c8c100d0403141c4c00340c00800103500d003060760a41c3d6540b021851740440c2001c0001d001103028083e1902c5180f100303103041d202c2083e908060410400500321681c0d61104030100b12480c0e40012120281400c09003e04080064141c030294200311100340050a07a00416122000362191 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 493475323 1250 493474073 493474097
    0x12180a081c06120b040309120f021002010905070e06010e180a0b010207090911090109020c10020304021908030703030c11030f0d0902060a050d051003150b04090512040f08060105010f 80
    0xc1d54010001814080c26000031069146407036420802d00321350907030100f0000400001c283c0e84a804031821070758010300f000e00288059007000300c42c070201c0c000c01c011596590381480014404002902c090910080c41504130701c0c0140005001c1501001510301404203031150b00c0300100c0005210b0b4201842d03c80c08a1081500300040303207091016486207a140742000178050070311960b0442801c800d4800c1c0c54000884c0c0c0c0b142d1001c4164410310b40b070000c00b548080d10302c668001280e4007968000744000c0c4680309018121149212002107500580b401e5040007900c0810543c1600c5030042e002d42500b802007190410101081d1680207016400e882540000f4912044407441e0740040d142c46c1d80140400c0c0c444486110080c400d411002c0740004440ca040041007911307103c0d5003824201d03540600f04450b070096952030f16000d800c00c0044240c119444100c0703000003c03020b0041e1585030016500b01030310746250082104001e02c06502561458020200510099070311800464920540342441d00031546 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 493476573 1250 493475323 493475377
    0x2040b0d0501050c0a03060b0403050303160507080f0c011d1902061c021b0f0c15070b04050d0909110f0a050f040807091a0d0b0601020c040212180a08 66
    0x20361100024655440c1204000e03694405501810903c400c540d401c20013a915040300055070711403400054510350040c80060200c40140c810007201c26680d2030280d00344040380c1d8032801c440d0410a11f11604130404590301e0a158000d1281e150262569080d04005c414501142d548603030700721360150303944c0181c01c18603010764540ca000c4540003d03080303c00c0d01c1c030381d2503017401c00300203410510304a000b69030100c070b034007500c5a00002c0e50081420068058142c29045000304100904404484610280d0611075480892852005103100d103005030041c201e031200054006181c4a4181c0149440525244040c5003142d180c00542d900c5178a50316030b40369549113414007a6104e003c2d052000031900350008000ca114440070940c10b044032040c0c8018495109090481d201d2030f51050340f0b00e40c00403107403135800010910810398250001c6060068841803403030ba00c01704059070300c26400d120412008070301f48a0590000400b00b100d500d240f501030141c01c0312a035a1000c1910071311040303045c0030b110310304a82c140c50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 493477823 1250 493476573 493476589
    0xa15231e0a1a1303050c010e101704031103070c05090a090f020d230d23092101090b10050103020a050d0906140708070f18120f02040908070b0606070f02040b 69
    0x104030060300640f03541c0c91401941d69110f412240b8002080320040b00c020303080510032904c1608194450b0b89460341c401f21a40150300b1700070300c1501045a038001070b030a048420310080c000b260240c0c01460145050405002003184040d080181d40c0b440c2440c104049055440c11400c1c03158111444c404164080c00c103003040d40040b58081d480540006014203200b24001600b4260b94410303210701a4200f0300740062140c1010351490403503201d2041005040d1498840d2013040406801507402c045020700d10350700f6007100c005010480b0660f0f2040301b404402808292140e0040c1424a001d40c50b0002914000b0302c0d60090480348410f4603101c498070410451143c0246081030ba061034403805a1800c0e00d402011100207030740c14804a50401a2a80501d10482504482c40100c495071a111841c0c08100940c2422601041c0c0d11800c41012800c010303920780c002d081c0b8240c000d030000c41d11a051402e250070074400191a1921505003041140b00040c20704052204c0c03030303404640c005211403032040402c24107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 493479073 1250 493477823 493477837
    0x180421050a020c03030412020d17030a38010809010905030723060105150714030a03060608010902040609090504080c060a0f0c0809060a15231e0a1a 65
    0x104104005161456212024000141c2142d08030b84116100300d082c50f4483c1300703d00500d144290a002e0141c09400c110404424403445071544009242e080300a03410a41c000b0b45000c06500d07103690100d4060071030b000444507488803003e08082e40800000c1007103c64003025132503a05000107a40042c400d0070003035001510094110b0705a907076402c038a01d410700d4800c032015661414251400001d045601c400035116050300c00142c80d00c1850050800740600d25005001c0444002d14400a1140c0340102440501313190390745a200071580341c0c02d00b203000e0304860058000d20f06461041c00300f040490b911050765411280350303007000540b9440c0c82c01e0000c158440c0d0503030803160f80b140c6002e2094802c550340c040800050200410884191048803c0b80e148500ba103255070168010710215580300100c2d030041920350744081c1d9610010780d8441c9100e200041134164407200b104080d0a03080982010160f84038400f880010000c0321207841e90000e43d45910345e0156020270011005800c00616000d4102c4080c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 493480323 1250 493479073 493479113
    0x1502030c070810050a140a050c0408070f260a080904020906121b0412230d02100f091211100e0a0203010f05060d0b0709030b09060a05151804 62
    0x4442e141c05049940d9010090f021950928260021301100b4003403140e43e114500d18880e002494840301c00c5171003e0b007030103098040121020407000403140d030108040c01c028000c2031810324090f0324009007111008111150058201402002d4803c1c10002141c40c440580d1b00288940e116000280410000d00030407035001e40040300040c80c85864502400f01d14840c0401810404070b4103480b400c0600c2e14081d61240740c0440441d0f01c030440002e1158416a911030800101c0480c44001140006242008075601e010150b040f40f001c2400d2440c10f401180b108031000b42e41030140060310f680d04140040005541c100300081d0000c54200040d05004042d0070008004003030107007a0028864540719526554124825807030010b44808540300c60142c14031825000f00521300c0352035603403240d68021900034035030400c21056410200010b40d4010300c00f805441040000c01451070f000d0800c00840d40f0107000d50092020826480c29176a4030510b10325601c5400000d01c00f01034885241404036400034001c80c202c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 493481573 1250 493480323 493480333
    0x1103010603020d0608010e12090d061118010903020a0509040507090c261b0304410a050304062d26040209060d02010e0a240201020f041502030c 63
    0x11035a40c15005400a15107a14040040c107580300d031854204c40f19401080314940183c41c091038030140d95400f914003000040c100c1d190144044d542d076001c952011002030b000c40340c0402c030900e08030500c620702d9080c00c1003070030310b850050b086400107420154a442164400c0c0842c0c00050200131080c461038004200040c014001d44bca404006080c050118102c18030680701c800c1e101d110784000c001c1c0b0764000c02441e008045006160b0100c0011540028400d0714142d208414103140e1181d06040c080d44899074a4500d0750050040040100402c1c00c10400f503240d501408102010450104c11902111031904055110b251039451040a1010a500d26040c80110300041444a03402042c40f815082c03401c0140758158079401c840d105246001d540203908901c201001a0441c00c0080c0428034650050505404034128500080e0000b10070350455980840e140c0b81481d522241e0b04488840740b03403140025030500c1090f003824500c50150380b0034290f521034081c5091442a00070702c1164912400710701a14 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 493482823 1250 493481573 493481579
    0xa02010e150601022811120d0507060501090c1707181d0f0112020603061302130e06030a0312090804051203120109020a39050c120307020102070e0a110301 68
    0x503444112482d90142c0a40e80c1c5050041c900c09480c070441e8a0182d1400201e140c1c0c9460b016555203030602c1c80c0703402880c0000580080c903010804015121441e544603651091240343c40ca05558040e0b00c1036584604124142c00b4280d00b0000d20121107038031004188007991040001c41e110022242c0445403005032101c0800e28103105081111000c0f034041d0010469221100c0181112909200c3e091440a1021540c0010302d0300800031600400014000d2034170b000c0101080782282cbc08034002038002d50210104014802d0050388542d80044210041c00e4041c03010348002e403040c01c07034404500c100360703854524100304003020081e80c000e0000903040d045041190419a6500d920140d00000101e090000001d400d46d40781c02103c881a0060f903d140802d8414200c3c0c01401280d141c6111840d041c84050283c110700000038580040c0c042c40081010840301c1c010b20100340e4020f0b90b01d0231b17260000c009110160340c00040d0042256140358548903940e039903060100007000b801c81c2d51180620000000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 493484073 1250 493482823 493482853
    0x4020405040612110f03030f0a0504050604180b0108150603040c030503070506181606051b011b08060f1c060b04020304061a0111120906090301092603011206020a02010e 74
    0x583ca00d103100307001c20546070000e281002806071101c2c0203d40e066004000302024900d000f00600300c00000c904085041c1a01d07040050000e82107600440101007100b24030490082907030243e0702954500307007050744035420960401d0455a11450089000d0000000440e0030001d001d00307080015508802620b03202c42c154030304292118815650500384007112078404084800c003081c405e0321011822a4034036400e1a048003070790141c109000e0100b40c1e440320003060800010a0040b0440c1151006550455000e0070342c010f072440070060056401060350008040c03d6032200c007205410102c1ca65042282403510340740c40c001802030910f1541c0c216001009010030895282c000c120842c0b01443c01e0400450198011561b99100700302c1e240715580440d00300d070260b019000003019550001b412841c5005560f00200e429200d40100c00c480704000300e1f5601a0b408443c541104402004501d1a841c40d40b402443c00c0c0b0b200c207614409400c4036400141c10800c0c6000b540300e01010302442c030642e50722400311030304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 493485323 1250 493484073 493484099
    0x705150414060a0b0603070c050114010603050907061805010e030304170313060c02010807030b12010509030c0607050c030406080c070204090c23010819110f0711040e03030411040204050406 83
    0x500d44540c8180c60101e666800140540c4c50143c002500c16030841e1f035030300c004680004401c0700c02c0c0c805542e00c0304caa4a4031640142804c2c0078100548010541c2e0401b001481e281030311690242003040029444d5069203203032016040f0441d182480d20040c0c000045001134113521a40d0f001240c0e0786059030418245103000300140c9200d45036046161201c40d0343d0b200544100150040081c0004c0760880060403040c001e900000c19408007400c000c04100342100950300b152070680d0a40c555178008254102c0c42c2004001495106c0481e00d44107090604141d01240d590041d0f02440c0309200414000811000e50034003951030150300180140300746c0391035007410800340d402c1e405020b5401139030700c002c0401041c5482c04d242a03c10180e54014070755a41c0101d526515054402c012092900d8241502c1d4031440b00014100400484401070355500c814600010304042d8109564010b6050910300c0000013004002d99505c140c00061b00c41d10140040001002031103140c000d00c6d445444c050000c6252291820 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 493486573 1250 493485323 493485353
    0x90a02040f0501050616030e1305090d0f0f080c1c020304060f05010f03171b060108070e0f07111e0a290601180f03030c06050f0c0f07051504 62
    0x4042103035807829441c003410345009020325500440100031402410420f000c00c0b00c0160700030300d4a468019515030001c0c0f1280ca85503c20810b083c1c40e00140b106416050005005d0248242403294158007014006042503080844a60900002d80001194212000111541011000000b6506c0344c03902a181d0029041a00c054903824509090740308941402d100f002d05895a060a982e01300385555074080c134105150340c410340344103800d2041003500c01003900d56418800500c6c001d0101981003c00a500e400300c0c9034820b10100c9244818013034101442150160400b4440c030f40485800403001c030b0f903460903025501800c0c00c291030820408a01d500483c01401c0c13184138050700e14200d00c10784c4906440e844200154024030403100b02003401036000b003441800d0005c000c044010710766600e81d0340704183d199943c000e40118061091150420a06211f001c1d4000022010420346042120700030500c0e0051346190100000000341c202c0502a04100c03400400116180c54000ca1402d40342601d0424a600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 493487823 1250 493486573 493486579
    0x3170a0f0509011a0f061204051e161a0c15090f0f192409060b030a030906050c0a0618050c0109060804110a0e1f06090308160515090a02 60
    0x60085410000c06006121100300c4500d8580e2240013034100b000b0078134410003010303070b80044200a0220220801994030b4420360082010301940420621194000c0e024254840d6072504a01c0b0b08008411039803500c0383c01c1e9122142051056070034001c40c200c10703201c2d40804400341d1160502141c420020600564401c14041c1c003910505100c5003041035030342d02d00052540081d0440290758101900107a00700d4540c500440c60f901003034410350b6500000194480c480001c0300d445e801c15206010071400f520b82d0300c0d20113070024080d41c0416100141105414000e0341c00300000011900140901000030a200c0307600644101300b5030a89a540c010000b4569108a03200d00074006001036560042c48000100c0d070300c94540401e039589565502210405100f002e41c0d1001d8014008103100d81d02e60045885103800000c1411030000d10080e0207200c5189512240420461400c103000059648054444c40002e04218080c1c02c40145421400e1210a08205e503122503800c1c1080a005000601e00814900035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 493489073 1250 493487823 493487831
    0x160b070f17010915120c06081503060a1a040e150c0c030d05070c06020a02010506010806090603101116051c08060906100207030c171b09040f03170a0f 66
    0x24a0207a40c0703442003001d03a2400000c0c0c100100306482c4990008003d0783e400703030107504d03080381c48500140a803142d00d1020750340902c8440707041c00401d41056449401c0142030f64400c1e10a400600000c0d501c0c1f90040c400c0d5030043d01d03000c00f510840340507840c20280420040c028440c13003000c1041c0c00d41e98902c180702c40e248021b540d004540300ba800c8800321050956148051850f100c20a24094041c1102803ca841004207800d0f203078010903c03600c003520060b007407030b4004070b4203040060004002c000c0180c03855100e5100c440601180340e80024110200d44e200400229000c99449040155400703070400b003c100784c0034407050408021010a401d0034408444024142c6160040c00842d40d5640c12614a03400185100110740c2038030f40381d410300c050107000e8030445002503200d558445002c5019802582d0440d10072441600d070036130621030300d450f400c0106003820f140020385002a05460010b40017624003100c0b00c8450040c1880340d44001c40d800103c10350721650341031008541d0002c1c086440b9102c030700392170 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 493490323 1250 493489073 493489097
    0xf0e010e0114060a05010f180b09090a0b0a060c0c031202071d040201020d0e030102130906061205040203070306053103090e100501120b03071701180b01090c05160b07 73
    0xb081071460254070702904156009041000644250000e0842d020a01040442000320341003040500c0000d4184155020745a05d540c07001d12151184c00740000384541c0c10401c030328240b505e030400401d003243c1d054902203400d0705180c10f00382200e0710103802c09440307442d076200300f84512a0001560411191000105600000b00b80038800040009440090040c1c1005060403c05031080000da401410001e0005191505840301408584199808569903030344032141007116541040c1d001d24400f504038014485450a640003d86440050000414540d40c1d0703004200c4500e2108c2d005104081540301e0280c0d10840d610038680c070070b51540000c4001811a01c2c0229840c02c070700e550341d402210400041c06809080c0b40056a880d90016002451180c0d603401050310b9079030400ca01d400915100d0325010ba074940c0100005e00796050071240c1035001e40d50490960000b0001ca601fa81100c02030480000c099144a800303c030036100b1403008848410b09200f8003000c0c41080d1003203600a00c092340703420080c010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 493491573 1250 493490323 493490351
    0x1809010b030c0a0e010e090411010807030e031e0c0709020403230316050c1e030d03020c060408070611031e01150509010c021203030717060d0f02040c030f0e010e01 72
    0x8002c4941900255083c400782544502644200042c1407050504504a1100d0804110100001c0301c0a413520b2003421202c019658100e081139402008515081c0702403505040075640e213224010011281044d400100841210140241c0d101e29040744107964101c0c0d5514034420113500300380819510b054248100c41510100c2c00388140002c2044c4024509200c40c2501c020f4200d001c0710410754141c021005000c400b03640d41c140b034540740d048205c14000d0240c503c0f004d040c03078440701c021468141441002a00340040c00051155441a80641c0302640c580031868028040c00078858541c510720000310074040e8030080d81004240040000c2d4110388180c2c1c2e0340303c0810010301d41d08960400316100708201001035200d0140328035014000361036480141d09041d0280e02d103500442c0e1600000380d48401d45450304a241e038441e41c000c0d204541c00c2d0361071902c80d210491007010901c0002d01c100e54031782010011038001c0d0085d244010360001c080041c1861108090701804c508072044180e5464000c240c1c0c0c005c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 493492823 1250 493491573 493491577
    0x6020f0304060903030302090d290915180f120702011b021012091514090c1005031f0f08071a0708031306180c0501080403080c0d111809010b 62
    0xe00c941ea1044451132440c5c130160f009510403814142c100c2044545d803008075030054a41070a816000c0314803007100c400c2c00c1a10003000b0025004c4141c07500094100a0900084128103803c03424940440c00310703445240000d4075001d0f40d00d42c6103005006402d460070b80d651120303025002850003a202c207a071b10105000c41c03807041d5640c032030002d610103c440601a0120300c1145028464100000300081c98103950b02c0760008146000d074001c904d0b40c0c485082050341c461200d0b0840e0404549402440c00c07020b444001003880640e040741d14100203002c800580d65450905444218000f032109a8030340a0b2620140c00e10501b2a0003099064400d80b000010301c5a4885010102d0040302800030f403d007031043e503038154254005090880c40d034140300588000300702640b04074942810a0340816192680500e440300044407150700182c1489003400420000c42e401481003984013090541d19a50f981900100714010014a415244c040c50081809081511000407250520343c00301c6030880542e0b65034400400c14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 493494073 1250 493492823 493492829
    0x60506131118121e030d14182b0c0f0b0a0e060103050304060c060b1c020111030a1413030c061106130206030a05040201110a0605090c0d080a0f020705150304060b06031e0c2206020f0304 81
    0x204491500382d081c2708922110109604c8081c40c1c038205500c0e2603210300c2c5007242c0d1070800761103d003042000c0c400360a0075486000412450b14000d005a036146856140d12030040744a2242803010b0700070108104849644084561030000b49240015500c0e86410540e030076030702038104d01250591a5040c3c90541c0041511807203010f40d9200342a13640c0c2e6101c1700c00749402410010501825841c00400028451085000904410b0b92400c80b40496041c40c10702d040005050074401c84500c50500015807996000c90307520509004c404a51500c0e64801203441d280341508184050161000307000401c045900f150740a1080308080718018003e1200300003095020303d20052902400700140700100340518120101510640103880a03680e40c2c0340407074241da0900d040c4900040c000001c10040103d03a2203044691001581c41c54118500014a1220608541c40c00d141582038000000c403600311402c1110b0910304d0902d2306140142c021000803451181602036080075002c0c003070390311403592000810355040f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 493495323 1250 493494073 493494103
    0x33e03070302060702040f0e0616081003020108180d0e031624140d060303031505091803041d04020a150804060506131118121e030d1418 60
    0xc0545903a08110150380100012608981c0320300380510b40b10060f02c0348803811140300c405044180f40110801c4000b6060048040a01601200b4804000b00c648115820780e942801c00c1482a16410725424080741c5240e003960704c1e807080741c0f00a03010b10340c4801ca02c070036004158200d40303141015503400c039511700b1240522100300701e805040c3c080400f0341c44090b14281c1c1d0b050170701140030b100c0405018034981c8400c14070040741e40c6030700d010002c1643c544101407508071907100b01c49440381008001132800001030050f5000c458440042450f000041c02180c005004514460344840c0c0341d0303075615106d04011141644100d2000c1e00000f0701f22170340d1a80403480c071910f95508405540d5507841800526000e40000d8114072498041140c90800f0304c100d0011384640402d0641711000c410f060300022041c80e4005010303032034204002983c80c40024201300b00700d03040da05004854840e00f26492a50140d290983c440d203084c54961a030001c10811313028010711042c2c520100c258682006103548244039400d0200c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 493496573 1250 493495323 493495333
    0x2901050306040f1e0803040201080f0601210b1c060b1c060c210e010c030e0a06020d1103010b04030c06050a0818070b0a0e0f0102120a0e0109033e03 65
    0x400a1180010407144511641a00e44c0902c005100b4160206003058116403e180000c01e12086d580c10160040d0312212614001300180350590008081c00240243d4150381702c40040c9000110440744c1203241a0000500209a5001c485600f540e040d66108403d40301140f4045c01c0b51602d0400ba00c0c000c1c0c1548181c451110180910750f10280100031030390390403003000200d1302001e01e03045803004800b509503240900031500d0955044404d08540610140300181071900303103500d080d080301042d41490b05030808030041e1035a00300d0724482c0142c9080d44414501000020022940304041d82c0604244d9019a0400d80f99507120033f41034601d4401d03000c003040460892030000c6c50642c4080b130349107000050f01c4d05440c2036566a907080c001c330b034100b041107501040d00094032045a080500850780c80240900c010040d54451000c582414422894081e040241e805040034899019100c00c1000750303802000c48641540d258980005410450030801070a001801622040c1c0000e0300c0000903240d005020b04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 493497823 1250 493496573 493496581
    0xe150d050103210503011e050907020607020f0d0c0213021b0f070b040e01051003060503010509030909090c150c390d020f1c020301090b0709230108040203100501032901050306 77
    0x7d130724100d034a00d203252680390824041000e48601040d940502c07920340051690382813007403029090909031100b80089500c070700d006181883c0d005105000d4550107440171900c007989110000080c1c031a0008640314400c8003103031207582d0309000a80300e100c200184c054800c0d0a4851092104c580f195100c0c225024003224014450ba03e0030342020a05803c003820300043c01c40e0380c1c2012a081d0b070700486201d0055040401d04200d40d062001c10598041c4141c000781c18098409000500c000701c10408080c070b0018042250400d9400c1003010300c00e00414194596501c43c0d00e024005289460101c00c0c8040320304883d074640c0305007003140c06c8022040d4000d007500401d8000c1010300c010910707024030040403103052610740d10250309c0a00c900341c145030180304c00400d1850408000380c9816003960065000d08042000c81000c5908006030350b0b2404002d00c3e20004985441c00000d03d0162030f080205805450b201c0008104a200c860941c84010300390a54030034490040c00411902800340326050b0581c200320001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 493499073 1250 493497823 493497839
    0x40806090609060c0a030207050d090f0603050c2d0304060c1e09050603060301180b0a0b1c1709041b020f010207020109090c1106010609081e0d0e150d05010321050301 73
    0x85c2c40b03440841d02d0018107100c03051f101c1a18000e071060340708002c108401c0041c404842851a800d0141002d810f00740107504000441080601c14113120542100c800214a45044000d481592250494450954032403e00303091660003824001c070300c240441c905100d000350f207940d5000403509100640e00c030140c1d1645040c0c02c1c080300ba4002044903038955038a00d075058040c05504030305d07400300740125454040c1e0b00d01184d4100490300560304052061002d1910480e0318a162150b40b58801d501c0302100c0c001303071940c9030800101e01543c0740b140e9026013001100405010451410300c3c0d602010b500726103000d15452501402c0307103d0000b0103400035185a8080c46a000e5640207440c035980245070003088030f4502e9945a040c240e081e040708001401002081080d004204580c007086c9070440800e9407604401900d2994903c481d96140382440203182d41d04049075240c0b0f034405010861804c00913916564080b41800400e230034042180e83c014201c1c05011001d036106007180190303805031991491a400c000e10313 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 493500323 1250 493499073 493499077
    0xa0305100c0315030609050705090f0c07030c0b0c0a091a07060203150a080a0b061e010807020f070909050f0102040333020a1716050a030b180c040806090609060c 71
    0x146405150722070580041d4164030004003c0214010100041c29000a140060406650f503006500c00d0104000b88600c0c0d01e003107445642c00a00d0082ca241c0e40704903518080e240d542d02c03010301800c814010410401c481c1800002010b150400761b0f600c1b800342d61a411401c601241c030030f8401074614028040d01000031015401135030040110400c0826000d10040090041a4a600002c3c440c7d0001c2c2004010400110441a00a4022282400181e40e4083c88040502034086041d04010100c80481d0710039000b484142e00c0040300006550741591500700043c05411001400c0b141807180d07981600c1528010720940d82502e620101010b00b4602103080380410500700130b083c03811a01c40d20080c4160608501c003c01e85212552a8692100062007407140c424200405400440c4008003000c1106035100e011202280307801c0c14005850760700d60300418503038143d04030854042c003d00001d02000a0042e40504200c4143c40b003111219525089415102c00341659601c40300c1d8001000709401c0054000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 493501573 1250 493500323 493500341
    0x3e0d0c030503071d151c0903050702130b09090f07051e010e0117091b011719060e0903041412060f060402070b1609050f010215130f0308150a030510 65
    0xc0501030f502c84c940042d400890308081304c5240800052691103186405421400519111108000350b01c86610f002c0d005206a0800034401c44a00a9910083d8050345c010540d1900c050003403101c92800e200044d9a80016403c0c141f440d01c69818006483d283c00c003582c445450400441c820910035042c01500c922814170109410302c800c54034001448001c14400c1c500c10011a401070803645401402520b038104542501810003c44020602c01c04002030b44294000c1d40031502299400c8008041a0052145802c5040c803ca614814010b0030354000020704256183e0301d81000643d0a21006c02c540940170071103002154100c440061026a10300c441260701100152000d03280c5a496950701c106000200c4e5502c002d000c2d20120521f00640c441c5c0110090401590b0400b200003030200042d5481c5030711040d40400090300400108180030a0610588480e40300503104070704421480c002d8000d140c1150520000103d0300d203c41c03030300d2074203110031401c4030b40241c05054299200c50307408001d1f1110360 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 493502823 1250 493501573 493501607
    0xf1202280207030f0b0f100b1813020703080402090604021e0c0c30010c1403040f020307030b041b0605070f0309080f070609170303073e0d0c03050307 66
    0xa0b0001001c03401c56888081341c580301e801c55284920f054500e014a100f0054805074110244000038020246010304407001900344402c130900b240039800005070300b040c4c2d0501030f20515002180c43c800309900029100d009a10071a060711aa0380c0c1c0000f40012402228090300315140c2c004145410581240000c110601048080d2101c40b8108804185420802c0c00a400500701559085404050440d040588084540700a003c0078024510042c048109660340c84070306a070005c0800c00300001c00f40030903122035002e400e5034005503581c00c0040302e40300c0455040d1500c02c03651007c00b21030308064032204180c4196441d06801c111403601c82071990004a90103d0900405200100c0c0b018020000d90045680707500040040c00d0404034010071504156001c0341c0000401c90f088e000c0b880001c42640e501015503d1b00501241a0a203810a02307047c610b100360401c01016000c2400c50403800003039039495500c0f030844201c510060340449441503211405400140c041c00030030055441540c0021800c4460 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 493504073 1250 493502823 493502833
    0x61d0405090a260f0703030f0b1021050405070e07090f0b090105090a031103100b0d12090b040801050601031d0618070305060a020c010e0a0803040b10090203070f12022802 75
    0x300f440c06642d580000700d641000340300802d50f082059072500034114046c0740d080d018031400c2e400740d001c0b461140202050401b40701c000b01454011601002c0f03a0094032091200500240c01d290070141d0311004a4002c00b0103181a18001401a82c01503004200700d031600725052b0801c2c1d160091500c0039801840f5860304001c010410001582c3c1d4610f001c10103980200c842001d0181c0315020145001c0d13454406106150500303000d40c13507a5441c0c031220303240103402103507640c000d980b61030045510a4841e0420f841210b004a0045641d10055012501c6010289c03030401203c030305074941640c0d0200300d185107030f41c80d03202c2c0c0e0006000102054070b94054024140803030f03210030f0322581d80a09250040700d04004065003c0303841601c440c400d000f00030240c0b03c0c9201800c0a9400d546a0403450301c0003c0010b4462500030000c42c0301c020344102d90100420b4044411500c0703040952000f8000b8881c8003d03100040e04851048940620610855078012030720690746200800c04052140040350703240c01c0405500035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 493505323 1250 493504073 493504133
    0x60c0a03020403061a040c090819060209030f2103010323010f0f0213090501030c1403070909050c030708030c03070609021311040e09060c0304080c010e07061d0405090a 74
    0x105d004481c4512030085642410090700d20500c011101030b58202410045800800c0081030340110b064001c0c00c0110f000034a80c540c150030800702070710030341100c250140b040c1c1440104401d0049422144031498024080c10312005084d0301031140028000034011a4103c001d07840e40c01780840554580e404488000b00f0a200000c2101e812100e07658201e03411b6603000108101381503000455000500548407082020394110b03140c60049002c14010303120315281c50004c1c81295a01086101c004003c1228140b219842c0307860309a440b07080c484031140c002d00c00e814000c07407442c00c0882501c8291580d58020f50403d4856202c00c00504110f18081e40c00440000091000c10703030501401440580076000c0b00d0f40d0754640803d90392022030090650710385030018000d10000c2100e88084030340098016441e95107456003060742c540140000d5011480c1442182c800080040c0c1018610b440b20300a200b031000088928028081a02d00c111000c4009400c2011844000346414000100030b4070007103100702501742c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 493506573 1250 493505323 493505333
    0x7030504020a090c02070501080c131a07060f0209180f27161509060c0609050f070602100608060105060301030f03020708070303170622020a0c0b0406060f0e0405060c0a03020403 78
    0x155000e5005070001b540611003035800c40069500080b071b21034001d141403121200c584c0360a1050080c06401500000745e41488917540b4140d880164001c8000c129141c10341480d88025030010441602a01e5203101020110594080140c0309018201c4201c0307096403aa10f010b010f2011802e0075070254200b05c01104c129020400000d0032660002c2004004a402d000d181c06420f42401e41c04820082066001c0c04101d81c0401210441507101d2004502c140c1d8904d011400c240102910301c901340318461002491aa000030741c04100c030f003100300411025031074004a540b50b40c000d00906400c890b00300700400008421b590b62410440c080c1c4142d40159032104206170402c125644107800141d050b136490484290091351080d0404011194002400c80500c43d00000103003c09003c0c0400358003080701c2d281c4501030500500740a41c070a81c3c0701c2140c0f405141980c0104854000e444107001c941c036022850072210400d150140c2d4220000704000d5030395411800544e8403140e914010160240030000c0011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 493507823 1250 493506573 493506581
    0x40533030a0227010801150504050607080c06040c09060819080c24072c01030e01020c0d0504080132061f0302071505011409091504080309010c0c0b07030504020a09 72
    0xf001c02d80c405107210f054100043c2200010382002c018100c82c84031845603107410008541c02c41c2c00940c0e255848011504151946000341044400d0b280242d004101c00c110f10200d0b500c06884000408001254417003004942d68400000f00262070701d4000b03500004109010050a040d0b00312038100da5401c0140010945465045040c0030a10301202d0107002c022908151456030500e810034803c080403c010703042000301310090006038140359907020400d03001c5600f90100d44e005500d40085881403d45810024101e50086c071440c0c0840d460580001c1c2c0c141507003440c0d01c40c4a0080900c0f1203112440000741c070b2042c8005452070ba807200d804080002c5150690240072103c00d080d807401a1141c0850416103c40c5465804035140b003481c1c20010700c440da212418a00b41c82a040e60490300e25500d1041940c500030050180303c42c03c40e000b80401c02042001c4000314801c100402c024030901050200c19510300c0040d0b41e00134034010280c0005080f01d8826840b1076400707030004021030350f403541c0c42080300115 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 493509073 1250 493507823 493507867
    0x106060203030a0e0d0e2206060507020a080a03050f160609060207120206010602030a12140a0603140601061704031b030302030a0b0a0f0b0903031e040533030a02 71
    0x581c001004101540d20700e0700c00d00a108035100302a00321501080d5008000075014640e80d4031810301207000c1c1c0b1020705000001404c4c071581d1602003140c2500d544c4082d1280c0c1209070b0483c41418006401700c1c0048003c0342d07010380140e01d62615030410181c0480010342d0b8204d0507150420280b20700715600801c060780203c1249a014042c010703558550b42c00d14100026a840c109070940d403104d801008410790020844a82c500103140c00114402e489541001030f0491003007000c0c83d4500c2a0910081d00034503802041141c0c0310b203443d19800b540c200d140e00d442d608c0910070034000c150b15280004013000c504020503401031107454118207106541c0c81020300800c5195080c0c00080d80442005411800d074070902400400484000c0f0782d603864410410b801403118020503100c0000881c080c80c42e42c030700b0402d40d4402e0130340c1496461420314001c5900d003aa0017901c40c443c0b041c00c0c08012280c101203d84005043c400304100c1540420a440c0000c1c80d0540c400307810302030b1840d4200000c8040c01c204008036040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 493510323 1250 493509073 493509077
    0x1608073303050717070212160204090804050406080d05180d150504020f1c0f05120406030207050c04020c030712051b0309040f141810110307091401121d010606 70
    0x1941400000103103503054189084d511307080d0202c107001d00c0540019041080c5c4168208560b5a034000507803245c000c00c5040002500541443c26800401800f0310180080c0d03601503c0401c80e5550702e841841c0d503140440104804514200f00d4000110002810108140070190001c90b8801c0140d4030300b40d0400c21601070f4041c1556030801c3c00110325000c05000d141c10000c84840034521a42c000700e8030900d000b040c0041180b05c5840d03a03c0300b040f6080c0080d960b0744d2900d080d000c1d10b8aa50790030240182d401418100c070a03008019441c400c9182500c01e4540d0038503840f00840c01c0000780d6850010680414855405000081c0408211001040010403c40800002460b00c619103035003408259101c454005260504000007561442c00c1801d0080d8044070310444003104001d0700084bc0d051041e44810003401c54100150356800d00da0313030402940180c10690313030761122070741c1c4404020700d85043e0a151030001e2050702c001c55007022290083d065890b04401100c0c9040034086402c0d0131a0301136400500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 493511573 1250 493510323 493510331
    0x12030e041b11070b0310090f060f0e090f01050c0a1d100903030e03030f09061813092310020c100e0f1011040603110c010603141608073303 61
    0x81c410b10240f1400005251043c840d40c111308100e40b40d070480709040d0080e200c070719517540c1c900c1710540301c2d070f4014200801d10b04c1604454103481e00c9296100880403500c803040c84c895a07c0002c00b507681440f509104404034103426003441c4d01a01c08582c522140e0b0107a00358042c00c4040200c80395158521340b0006807150f124460618a540340150081d64036803540c622a0b001404580080e10484085903070032002102e040e5070341c0c2401d66800b42070009581003e504091120070300c0024a040d54019a900303406a0001c603c8010000c4880000b06030b10000c4811640040340c01c04001c682d07540240c9441d0390301a0682e0040030312004044202e0b0f0002890a1445c1c0c4241e03010400c2d141d051005903196185158144060202060103400c207104520038402010782e1004144010900a0241c4400ca080b101c000e1003150340d40e0815400490180603582100c1c044e69071702105241010415208640342c40e0042c2c000245010070f2400c00340038040c042500b40c817050400120a00358450342000821640d10005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 493512823 1250 493511573 493511597
    0x5090606010906020102030f0606160503030106090f050402030601210902030604081305010903030507020607080405180a0524040c11070902180a0503031206060405061303120912030e041b 82
    0x4201c0e0300c642e0f00410035079104000f8000000d22844078690f0050080c1c5115a4800d005100f000307074202c804101406a000100010429503804100041200e400d2844505d1382910307007003040100d10095680c1c0703001c40c1204000b1494141c540c00401c806141002d0009480b001c10b8021a09010f000c50302222003400000e05400d1141e00c40c00c000028050a10f000d005040c199038000d0920b108080010703202c0c0713501140c1e00302004444012203000c1d290203002454002441d24102c1051392081d520352400d5802e040c00150240f0011010407400c480158282460300314481c14000180510a043c07404c020f22101d034207c40352420050340703008024201c801030366800aa51000040c1840c400b0b054850b500c0c40c85d0400466800100303aa41d540040707002d1191544800000030a1031045a210b00e0700440003241c0001c00d032440703541302d904480c09050090404c4a20b0401102e00c0704480c0500083d2142030100500442d20941c43c24101c40b5028100090445172040f540e002c0702c05039415480010b92080e000c0e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 493514073 1250 493512823 493512827
    0x40f110604030803040b0f0108060106030213120302010b040506100e040f021b0d0801060e09070f09080f0d080a060806040f030302070209040c0305161a07020102031605010c181d090a060509060601 86
    0x1540304c0c0e00c087c010a161350408510320713151903041c401c503c200340c3c0215018100d03c44200c4c101c0001c142c0019041800c00350307460003030301030316121000c04d00c9146000001075803410080d801d440b401308580e403003280407c581020480240851840745039042d50078031030550400c1611002c14000d02a090040010300f000c07810081450b00160014010440020922801916054002500b03c40c050420180c1160040000c440d8449035901452152080c00218900502c002c29400302050b11640e8080f4183c0c0c60340f40c07460584040c0d104d56101544100d00050200300d595074044031181c8289800742c038200454000881400c41030790180d8000f07403030040070070030010100100d1006441101e0340c408654038121112400741c3e41078903200c4200301c1c00912078046a1007807044908135011481000714050303c1c0d041c410b0080151a41e150081144a0400e1400d501980342010484442d0602401045c008848020740d07032034042c0121090b403190030108d500003403c038010244246c04a070000c020030719000c000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 493515323 1250 493514073 493514093
    0x6080d03140702010207020310020315100302180613030303051e10180b0f120703062a05040b07020d15290604030f080f0f1b10060e040f11060403080304 67
    0x45003d680c03040200320010386020134405c0c21514003440050b00e0f07650720341a240210040760ac0c0b00e5170140681c030300c0480d0950158003410100301c0e14104180a024000c0034086180300d031410766040301340400c60800c002880b9821950388580c2c10b40d030000401c5524600880e42d045c0a071000f4a0003071900000740811401d01c60454140c0422040a0080b01940d002040d9214250b0794621301a0f010303402200c01c0800d04000b03040081d40e1082007001016100012000329845482801e0907540303605280c002518407403400c0d070703042c3d036003600314580313090340c66802c00280707080c10103007101c190008030149044211288901c0d1881200c4940c0080360880d04102c1d002d48802901c0301c684914001c0c001800450190041d40342015480a070165848451141564807130080d81c3d24070311808400215180b0014480005000004407003040b600e04241000d44d01c002c0c0c54547c042c00b9043c0750600002404250301c0d241c1074042ea4000e51030300f10b000810002090180e84030760010341e001080007083c081040200700d9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 493516573 1250 493515323 493515331
    0xe0d0509180f041421030a05060108010308030a0f091401050603010f15050126070c0b1e160c15020a090f0f0302010507050c0a0611100b10030f06080d0314 68
    0x180c1140c9003141c20204540780142c40544030302c826000500d0500410020754001401041208458105a03050500c179035108540e04114541018042402c40d40108949810390387d00080e0507086954015041c0000e101c214180000540c6070040303a008203c40d0102034071030030103401c00070905240420130b0509681c01c898114040c1443c0c070400d0118408a0100c403170958600740f800800b4001081d8110000380e40b102102403071300c181001070155070754024480340f0105200d804d88500655440c41d000c1c5014460001415501c8406c800040b00181804036071032148000f030400701286070058940c0c0b6603407440c14081451242c0d00081c1c804407580c0001200005080742040c14120b64200000c0c0ca4020f00e003480700a042c0a00400e03940d04201c403d200e03110441402401d510310a9640c3c4000804045410741d2203455030203110452001c82155000c1d40031000c00280a078019078405600440c0286000004810f01c590344000204140009109042c1d14004a81c3c001c22481c0c40c140da00420140054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 493517823 1250 493516573 493516609
    0xf140a0f0c141005040b07230d0908030705030703030b0105070f0c1e080a060207081e03061003020a02060711030706050a09030f17040318050904030c05060105010e0904060504060e0d0509 82
    0x420150100c944c410110b0f015245002480d41d1502c00910f48a89200e091510201191345004240086080300103454013010095564140081c1d81d80d9180710380f2841020b002502a400c100514008a8003a80202c001450185400c40c0761002c541c8801003903800001084600032604c14081040300c80202440028040050f19215514a0080c1c0c45070b803810302c000c0003010709030040381d441c0c14800c40301c042c3c85d00b040e0f01211850b009225040b011540354411594148101c00ca240390348680351180c13003624008091b5400500c441d845080741941c9030024040c60611034401045640b00040b0a405014012041d8140100700a086464050200f15a41d18001c0410800304903803030381900440045600640c050070100c41c1c00400c02034048070031409800854009004000344030800d58424403042810b0f0144065500030790300c4000444402c08024071040d808404c03100450041101607000540103841030300c0c001125916070721000d0910b448201c80d0000b0038400b142104490500a400c401142c0e040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 493519073 1250 493517823 493517839
    0x7050105100f150909050a091209051503060d0308090c04020703110706030c080f0606040b1206131118060c070b04090c020c13020c0709021c060803070f140a0f0c14 72
    0x1210f0003032400c0e50a1144803c2592920041001426903a1001e201641c206010384c2640320048000b400003102172003001e00135100c0720244201c409010341aa4001c00340101040c5103100107890481c0c43c0307c4047c0103800c80340901c1102c41165039a9200510301c00340f003921401022020034030207a042428940c041400d050410100f040704c5548419510740c8a450300c940e0070640c0e10b40b2404101c041c0030f0798000c120707106070004116a00104040c0018130803141161901c5010118000b600d0070748000200c062400c9401b40f0110451201c8901139580d1a00090162428200c0e01030029203420700c19880590700d090b0000c1e06002d80705c002d009801d00200c0a000402449034414089101200e140240204140c1d011500181d02d8009008250040c49099025500d50902800301c460528040000700741c0325103802d1000035030071400300644080e00e03048503000341c00300755a880d14a100620131000030681d01401801400294850710b65042d403a0160280c0c440e8581800d104010b1401c250002605c40c0d000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 493520323 1250 493519073 493519109
    0x60c0c1f08072010140a0e0607120908040e04050d0c0b06060a1206090b030114100501180e01080a02040e1b060a02010e0a050a11090f160507050105100f 67
    0x11115034024400d860080150074a880402c540703003030f108190f89410b01580002d560201440d4100341e9444000d00825101a100c095040b0100c41d02c0010300341c03442c2c2080000503030b00ca0041c003503110600088070012815030107950f2003580d503911030382020752241e5a82c2c041c08203101c010408120442d01909004840c052a0b40b52b00b4880400108460b102c1c1e20001008103405100302480c2c044410000410b22030183c07650b030000c0150a0800155002c0e46c68035805034500700c0f051050502445085c206040c01600b024011919600e084448502960318154000b4807001c040001c02d0003014a94040c0121040d9881000203a481034400840554024040c4a0350b40008060807190020221440355503049500e005034054201c10043c44d03628040e5034080c0b020b101010852100d101c0c41150300c2c14548084400b00f20901c603007528003211241401000a40001004004030b40700040307428102d0400303569503542030940d18100c80c0c0003c410b01882c0b04014550014181e10044c055056001c404908 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 493521573 1250 493520323 493520327
    0x60c050a0b0606090904061e090c050d0302010e1002030f0610020312040c12150f0c0503130501092009060102030a141e0324030712020915060c0c1f 65
    0x100c0214080c111401200100354940e56050071600381c030b080601814403610f89410000000d1440004282842256a400c0d40d0350090710f210348041d2a901240d4400301c2410300b002d01c9490440114200c0940d946e034002d00c4c0e03044104011030081c0714082140035a50b80341c0740004144084015000754003034840400c59046064010082d91203030fa070582030b041a40e90b40d5041204a020860303125008241c0322804000078480124420810070540d032000740540400884810220f075003a49846001500c107001284100344035114403d9028001e600100b0b00708203e458101d034a204410704102800f00e030302129801420003900035980700708240099410300502c0f120203407542c004a42150800a8002901120649d2010650340440c2c0c040c1d407078a8480c50004095a901c00d5910503080c107010500300701d1140d5207000511282611007820351040082c04550174094420006405039100006000d040c00361911034401074122492848014618528144144a052800060240c80c0c2000d030910350a040f903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 493522823 1250 493521573 493521583
    0xc02070509060105070213050a090b0c0304020108190f15061701231f030b011d011704031106071d0d08041e091103011a1303080c0f010204080d09060c05 67
    0x350138200655905030328800203200c0802280c10680e41c0389001c0030710a81e0880365000c88600c0d80700d1503c071003240c0c9030320581901d640000c0f18001c0c00902c2e410000390b10345415010f0740048030440c04001c01d00c3c0c1e0400000c04c0039074902c41c40e04464074118507000c0004540c8070412222000c0f074000203200039410004003103042c030b017000040e1a80b4240700201032819160b0701d65280c10202007458403140e0b01c5080e000100a00f1031021480e0000d80d40164041c407841010b035a1b455080130584403070211101500c904d80301490014020780500c005041c03484000c01d03060116500c03030b40040c0d40c0d04c80c0c1074501200c480d01719a8005a2640135840307282c079020000300e1400c1100e003a510040a2002c0780c0c0300707a2021002c0303070000c8d400522020313003041d0040849100d104082c5046e2039074201c05060348501d44042d800103004285088040008584041000c0b0301c80c03c009000d8161141c09540030500d4201c03a00d8203903849540400c2e00e5900c5207882e5107142340e000444002525880c03500511007080707925020365071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 493524073 1250 493522823 493522831
    0x6171e010902090102121602040623010305071b030206060406081504020f030a080414031203090c0f0f1908011407050d051f03080c15240604050301050103150c02070509 74
    0x107180d0014501c805070703008000020140342060340056544078040c42d50352091400c000228050b0b4140b6a01041e0b041005169201d03c407440c200ca008507521060044000c1d11000e80b000381804032014000c01c880c04001144114039000e9002040b180c1072a9060004481c00c070703404050306401000c0c031034101c92019902d89802079011510000c0384140d42d400242865950070005040d0400064002000400c101c3c0c1901c91074411001c0e0343c2101c05c602070201c0680b208840c81103140d0003282c0743d59a83e10344601040190400a0320011580741546d02107141c070070b0030088194892004000c10410304509010356024800a407201c2400c1d810302110140890140c03d5081050315160400036800d80940c218402d5400e5011045840d071640e03c1c240130005a1103068955a03600540d800300900c0550120382c80d0190182045130020003281442c1031303078614034005005078490303420400090966824090341d13001c1d40c05010710400d100845c0265000b1100c120074200103540258004001c155203e031022540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 493525179 1106 493524073 493524089
    0x1e05090613260a0c09180203070902090f040b09060d05030c010f0b090a050c0430030e09130803151306080d2a06200406171e01 56
    0x102c0c403d41d10050919440c2640c2046503ea40f54060014031042c1030300317200e02c044154002030615850768405a003440d00424440410f14010200c1c040c00b05080760304215581c150f0001c42c1e66948003c007180c2c1705a20380809a8240f046c240100c03000141e000c80200206007140912038000c107003843c0d001380240c0c424070004d00c000d1803074410540510310070140142040d24000e100c00f00c0ca00544440c070907510303141e14bc10507181d082c5214490160b203e038940020b8094641e05104034207000504001030300c21401540700100d00340100302ea40200b01d01031020f110b41810004100620060440d6030740c030703525065000031460307008510076179010250350b29020f0711a0040c8240000001d541c58503030440480166680001c0c0d50340c0e029001c07048451b0315109220002c46040000c6030841da1107200860340c900d11418401c1030003580c6541c4040c1001d000d0f00f01081a451075960f40320305001d40c4034 = true := by decide +kernel

theorem cover : BRFrame.Cov 493345323 493525179 := by
  have h0 := BRFrame.cov_init 493345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 493345323 ≤ n) (h2 : n < 493525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
