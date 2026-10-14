-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2882
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:01:21.181158+00:00
-- url     : https://prove2.me/submissions/61569a45-7a12-45b0-beeb-3d6a79bc7c4a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 518165467 ≤ n < 518345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 518166717 1250 518165467 518165477
    0x318010c0e0f0d0503090303030f150f010503040303090c170703060c0302070515060d150c0e030606061b01020d05071e0f0906121e0f050115141809040b0105010e0d030906 75
    0x50fa401c0c8207103140180e8a4480d4944400010440700c07a861130070303680c02454025040040003410404025810001e80d18990001e0000c0c00010042403094000081840c000c0380c10804840e1100f44c0c4c100c503540390101000140e030180604000f04400d91041d404c00f00481e140840c1803060311740c0c41d5500c54640c0320304003101d24401004584a82d07908801c9240c0c05a00501c81d02c96042c1b5080c8a0000e0301d0701032800300c089900000e0500d001e06010074000c0c402c2d6401480e02d0700d442e004030006c01d1070078100e801c1600e0b290350902026912000500c210344c061000d5840e050714032602451161a5040c10f08d01c4c850800c0201d00100c44051f230000b1441064036043d0610710703140d025040c29100109201c080b5040d018400341c0900d801c801d540c1d4000300008182903000c1c40704d43e07200d4041d882804a8556844001030345a4900c60400303007804081e041c2100301340208002c034285e403000103070303501d0055406851840c010130041109681002407074150341c109840000344441d031a2809806e0710900d104100c1442 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 518167967 1250 518166717 518166739
    0x7110604050a1503230f09010c0f03150e09010b15040302030a0303050703020915040504061706061207030507091a010c0f12091205060103050c01050f090d0f06020318010c0e0f 77
    0x10b40250040402c12011350100503117040502100c3c030b8003100a41c2c68032550814100461071018060040e501e0366490f80d20307407001101c030b03000702180100201010350f05603081182d404211702030400065405200d441e03001003540c4114808110110b52a58400d000e0b15000304030400040c1c40102d5130324031552301801d0001d050707600e40e50306138060700c0b49000d816030200e040030017502808901b0780a031007038410588003044043e440355514018102e0510301645070b50302038000510076207003030010454498040f206940b00c5179a695900740c50329013160820340722a51510301c404140b90f650b04000c40410002d00c0c264400414985941c4408590700201502c641c441c0010303c3c01e001d02800301c40d00200540340c0006000b03002c5c0c0c2082500d031402800125410b004403a04c044441d171240041e142690000c1401170f00e00307000f800130403440500d40c240c21074201c7d41798105500801d540d84043e40c811600341001502c0c07904000c03501421030f80f6086601d81031007211520300e061038980035400c05031060f00356440d400030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 518169217 1250 518167967 518168009
    0x8150d0510180507030b0c090409060608010c03020a140702041b080105180105091503010e1f06090b010503011203020c0d200102071206150302091303080603030301121b0f0b07110604050a 82
    0x503101c2d141d2301680041c20700b59a6010041300f584a14111035506008008200000c4003c13402e070b10030309100d080040d00d48511441102981001000e00c2440144001154455440481000d10b84c281000c0c01090a160041065013802242d0041c560009d000e000204c1d810007001403100d44014020a4144411580d220700c9503c003544401041241401107a2010603840c10540b0b800826030544060b003400d10b6400140314101d80900c0001582c140c680508580c00d01d0561008800703500020340440c030808461203896129080d03410407050003080040f400720100062880181814904c560440d031059400b0810094010908110140d2203500828a00040c085081290301d50381c102a5102030800b0500c11440d8590b0350800c041403090b2140042681d5000806407130307000074444c11405074141c5d04030f41c000039403202c81011004800c07410010f695451304200300000c007080d0004461500d001922005201c0a0740110039600d400300c48a03403600f414600495400c417014400c0180210b00342100c03040d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 518170467 1250 518169217 518169241
    0xd0906051e1815030103120f03151508100506090d0606030c0b0c0706020d35190e010203090309010503100308180f01050c0d08150d0510180507030b 65
    0x110115481040d51141d440d00242d11a9200704050140329119102d10410080c880d601540d0480350000f6040c201419a2101666820880d5a0401c1095a41c0e030850741c0004810703c0d0000a070801961b0380614140300c80c00a4040000a854802e00c100484810000d0b031765a0030482e954000b00f503075141114086841c04c1c4015200c1c0f9000102411885c403c040b03103480c0c1180140c0240010103040b180f455580b08030590711002800100c80001e54003055034a1015504072800080103090003603000c3c0c01c5400c00c0c08070a11407090750040040030303c011541c5006149030140e240d151000000862440c10600c000695038411100d25905104021000030b07040702074003241d400115001040e05030b440d40f82d1351000003201415500d6911072401d010001911354826010740e1520100040100441d06484105980300d00000b05202c041c003288070161121625400082d00c04184104020440e9054617070000c230540724100083c03d40c102c0165004d1010550000d080c1041301c1d080a901c603243e440d00640c07418 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 518171717 1250 518170467 518170507
    0x30b06191b08040b09011806172805101e0911091e130204050d0f0620041a0f071b17030909060105090609040f021b060103140d090605 59
    0x8a000d0300443c000031100c4a40004100b482c0090383c03108000500c40e00b426907910b40034011080007c0400c600c40243c0410000aa0b4200308030303d01c1001014a42c400000c2500110303c4100d85135030301c1d076062084004800c0c000350b01406001080d05801c003014641d410076071685100b050200b0341c840703d07101034a103a80d0301102c51050000d0110380d0791810300e074200328000a00c01c90f101c1c0145564401c1040d800c5140c82038500360340000b0f22400f0702804035145d80840703444500c2c040e1079071681d513039000e1403a40781074040303903a0380003021695600c0f58500101c2c0d1605843c410a00740d80c0746810004a1541040c000c22038005039446290494003480260031a42030321603035041300011030b0646260b0801c07454000080c2c910ba10044a440303a0656441d001101d540c0a04851035070002e0080c0f019a449203000e4100c440c401c0c100d400014204102d04c141c500c05030b00050311603100c03904400d00600a00c1000005104071409040080c0301402800c07600601004061007a00200b01c00850350310f40c01c030f02c18a0307403c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 518172967 1250 518171717 518171723
    0x30402040e0a0b04031205150d0c0b04171603030c02060a030b0604060503180f071701020702060d0204061d100309030210060b2d1801110706020106030201030b06191b 73
    0x15807046020f150841c40000c0688090300490041344c480780c3c030f4840c18050305216400315411300740d0000001c1c0a001110301c541ea002c6800368040b013000f1508441d00c0020300020f0001d018426900000042800d08001c25840c0801c407000c8200c40c00d0000c03940098180221981c15180541e0300c0f20860011030007004000e000070381c807550010300000d1b400e40c4000030b14050501e20303840610a080028000b651800d0f10426020607070000041080008030007031515000e1141b00740050714051075580000d64640c000d651034590f95030302040620100b41c4c80b01200100c08041c591aa680414840016a4168030304210104050b25111254101032092010001d5004de8a40c1031000e15110000c04219030840810381c4210740050115600405208111000781c030104600d1515181c031503601040264040700002e4148032594a41004c18801000400014101d0b5400083c08a0862000400341d0b032038404000d214803028401401d501c0203e4400d07080c080000c1c10540c500f494500310b00325072180342c803a010b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 518174217 1250 518172967 518172973
    0x30a17070606080a032d0305151c030e101704030302070204090609020405060609012304030203101b11060a09021507030c120206190c05070b0a02071b0503030a0302030402040e 77
    0x20300c80e0400034000300e034940301b0b07210340d894080c603c90146400c084202c2402241c1c2802e08403015501e0003a48180c0e00400c003040f840c0e4024242c000400c106100101c41e0307880030340d0516030b10000d0561102c2184501c2600320340c0b005401c1c400540050464048100036160514890007103000c15010790304030b422059000e0018001040c103414030702c009004400c03086c0c1c02541010000783d045e240074003ca5500b0311050310f0310494262010310b42c580c403601070311403007540840400000c40941e9040040030103079408108040344078170f6050907401d4018458120704d424000c807801003443c440000702d601984807890210008035220f4600014079110303480d28a0398404500000c90405260b400310a90940500647d1480c41c0f0407102c2204036902e28040351001580300302040c1040300e8210303941000012404510705076007001c14a03122004282019908014583d500081250401000424048802c40d5080d417999a6a19080c0466180d201e01d20390300e400c050340040040c0c21582c841c3c0c4503d908001440403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 518175467 1250 518174217 518174219
    0x1e0219060b03010509010b03100513021c030f030c050403060f091e0b1e010608100503070f08250522090302060601140306030706110a14011514030a17070606 69
    0x100d60014412650a18025400c00c00042e0840c1d4050142c0c0f001d4407805030003403110100b0304030813400130400a07200204409544043c440036035901102201d00c4200300081409040c510b240281ca11b000c00d00c042c0c414142402203142c1d040c0d40120654040300c0d000040440e411b040c81e00f1000007080041401460036040103a1110f000005030601850544500306040598484c00c410341d160a4411102001040203440144031991040c05030744d0b007010964904152450b260307000203007172642c640c200d2100c92982c12400c0006a02c100000301100705410001407410f440003445101586950007031901400026a4446c0000c0c050221802e1494542e8020450050103160003500c070f003425038066001906c2e2007284001a031028003100c0c040e10000b001060f0440c0303050f00079070303022940b800509250b00070b407480c3d4404110855070306040f00d2103c03000042c1d1404504001ea4800e4010f81250941a0140000c40c80c15100043c1c000c2c0d4064206088980d101e40f200c0b180c0c001840390b00d000a000d03e0511034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 518176717 1250 518175467 518175473
    0x20c01020d23032e1502070b0316050f071208010e0402011d06040315020a08100803070b180a030c0b0108030406021207060b0a060203120c07030e010e0f12031b0304061e0219 76
    0x2080304d090f1803183c1490710b600846900102d03510341c403900400d048c0c2d120403c003041308540145010000880203080c007074140f04001254070b070203400032170302903414180014450003041e503c5084503014140584010646040c0780c0c0000f811003501d003460b11442800392040c00c40d160f0350300f02686d008641c00105410301e9985540800040e400201d81c04e0082a40080840c20301031403400c082c015200d0001c0214201001d50300c0309000c0b024041c002030080d04480c1e542e1070240314203111050500e4025181c1d411100424940b280303406805030700958254000340024465a44c1c0415001c420b01101e003545900d6442504240c001050115611513114004060000d94a42c020010305124100740b580c407651507030b61001c801114807a034200140001d46042022040d58001d401b01100c00802409181d81018401c0205900011111200c180ea43c408242c8500c0c091502080d500b03404140f0001c1c6090030314202e0083d040d81c049640014030a018602c150704012b00c00c0108aaa200c0c011b020a05900e40da81 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 518177967 1250 518176717 518176801
    0x813060b0a061d03030717161a060a060e13051005031507020c0d15020d0f0f02040311030c091b120112061b0e0118030203060403020c01020d2303 64
    0x280480601001c8140f19401460084103a8641e9a00602845810f4041c0030802e049a03022000c0d0795802c0f10a040880c0c0854984171104140c0003101c0d15414044c00c161040006030405a4450001c0011650f07e4502544403240304040c80103000002061f00c0d15a1910001d00d04a81d13041103402d4800c00d01e5240b40ca0f4a20b02d1454000e08140d004e81d00e00800e0340e000c0c00300c11b424645010b04807482c040340418640a041e4014440603d80c2c010000e50640346c149000c4c01e441044403a4074003e0b8011900344103000481909044441c0d00314001c0035040030744004200c00ea0f100801800e00318018810802015059408a42e07440c441c00c150b80c0d1701c540e1038450342030305d50152a0043c3d500070319103e821a0304161100700c42c5210743c1c854a070403142880345401101c2c2c024400d0303001494441c1d51030000005840c20060940220720a03001b0b001e079031403c0d1000a20742103201400c002000041e249a0310984455a00b504022047c40b840c80d030b6a07902c1d0481842c1e030200c45918603258862203019070582899207 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 518179217 1250 518177967 518177987
    0x31e06060a240e01120c050c0c0105030103231501030c0f091a1513090903081e07080c04030203060711100b03030d09030c08030f061f0813060b0a06 65
    0x215145458030381c07039000b88840d0a081801c0c1c41c00406041e1010030029008503000d4099160514000e0405460b901d01c401c00e944030382450a0202d40042075420f45039000780401c2004010a00e030050944d031564032515580c0c00c0d00703603070b1044c400400341507900d40c180c007400b003a40c070404000303002011075035030b480c01442c040182d2043c44914101c00102080385801c1d4010309007031800018690000030b003c0b03010022459680e8204080284042240104031010240750340700502140400281101c00d904005c6d1041c200144508025404c1450b409869950140e0050b000f80061900b28015540c0541d144c000e4450790704040d52601c1801c040202c6c040e888500c1c04040b04542c000d030b601040c01041c007041036403a461200c40c0c0c107070400e1109454144c5698480b0304803d009142c0401c0855070780c1c46294403a441550070542074404502048000d0405000d0313504a81201d15010301c4007045c50704001c2000c00080c0081e215181c9003900801445110340046541c0c1074002d0440031072594500300901034040c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 518180467 1250 518179217 518179219
    0x60901050f060f311406041404060c2609010e010b010e01050f120f070f020c0d02040515090c0901031505030a020603071809020d0b0301090c14031e0606 67
    0xd0000165a652020300107900a40b80035120501c410450000c010603103c4407842c2c0c03948100400c0741400d01900f40c150a40b41c1400100b80022104000903404400041c000c02403070281c4d0818181c103120100d50151258041e401901c0084d900108031011200c0c950007039a00e40d43d44a91440740c00c03840c0d02815940d4000c1000300000c01c280014041140e09881d0340070311140c0482c1040100400d517500440c0100b1920f00340319000c5203800c01c4400800300d419025111004102d41d00c00c00c101c1542d070010000408441d10380001c1558901001c000f0b080c14001c1e210080c004e6440d88086074640c85820b20042e0104001484410180380409043c01941c100b420140d0009041c080303001c00f883c011000c28015100c026002d02600035840e0240007060340701602e40381c01c02000b0001c2c0b0580c0c141c0907c00c07402400c0324050259640c90494804800d036500603898510a03490a50000c0000c0c000ca0019011540e20415140f02504841d001a050103008030208050369150300480c0340710300c1c0210f4003a2040718 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 518181717 1250 518180467 518180471
    0x406050d0f1a06160f050c100302030c040b180d15110309060106080c0403120905040e032b0905060a05160c12030207060603140708070909030203120703021b060901 72
    0x600c2011140965124001918550500b0400c2c1441c1c0e051100040c13500052080108031014003954a050700b2170350355030060303540e604828500c500354070f004105c010860002d4501941141401321070705215200c2c40c4140c3c81c2e4054001036209800c0b114841b9101c40e40b60080401c100c0304020708081c0780c1c9800713021005468500d002400642c442030305065a0040300d514005100e643e00701242641c02403006801f040c1910700c1400000001240c0f200d5124500301030b59500b02d00b580c6428148001d0f04d00d500c00314401d50304140f0820801400c99407007881d00407400c10780b0510b03034018084594000c02115401400a0081004101c02000240c0041d4094544120412078580034044215401e8100e090010181c849110310641d51a2090f005041d80d280180000925941d595955552103181c6000c0e11809800005041044070420300c10b41e001400041028008111542e40007074803840b802c504004448102c00204504520a5050368800c1b00814045200810303a40307102541c802045800c501298 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 518182967 1250 518181717 518181731
    0x141e06210f070b0f0f0f0c07090204030302060f07080601080408130602010501140409030507060515120610080106080703230d05040f060c170703120c170c0f041505070501020406050d 80
    0x1400b07a000704e40c0d1418030b181c401420411044c1501c115036101e1a82401c80c08001d0003d21100742040c0980801070010302c200699442c55031502130304200d402031608564460000411907603540007140a68007500034605041c0075a5240b80c00452405905e1800c141c440d02d01d803021522540551080d03059a026181c4d200c90401d40c0c508000a480c44004020000381e4103000c502c00086640d0090303030b00010315101400d815003190021070611340001d174000a41c0c0d4005004e0010307566044218102030420400203105440c10106910f940c2d00035844010055908446405000007a42222660b2603845909032100b8288040c002480c6402a0080b00d01d968441800010000e0061440e07402079a80b11001c1449c58191500c41406500017190980c24005940745018591005100b140c2c0e40c0c0f60303c4c0d11382c54041100c0138002c2920810090100f12030403030400c1100078200743c1000340c40459503500e03562400d8100c0d4840840b883d0140c450010055800401c02213000c982040c0580040c42e9116420001d81c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 518184217 1250 518182967 518182979
    0xc060c052116030e030105041101080a06150507080c060403020705090127230a06090609140a0e12040902030403081312120b0a0909020301141e06210f07 67
    0x841840005152401c400304051a00101041c5070514068082c1c10a8a400c402c0280840c0c00c0d03c3c0111170861341a42d203281c901c034281da0409026a00070b51030030410458a42030041710690b40560f0b40d0716005209010855500700141d0f04e080310880007103401940c1c1141860714001c1c1d624203031409500c0c894032017200080b808101c84441031380090302044460700100c281d0402540203016990700883d0000120031107804104455803414080c47c441600024142d01d014444030480c2d10a41010440e18103140c40c840c422441d4007269038100481880c00a60f4081c500c09403403602c0c4000410000c803d80c0440c0010780750805d5400346124600039102d042c282c2d500e48880c41c5030010b4070440103040440014429082500c03500c05882c8031035090a001400510030710004101007500e52009880780e41702d151902c21820280070320b1504280e120b8540019085c00b80701c2e6110740c00651030392411101c2d0b801c005121070f602c04d000800000720441850140000304000217803100d07602e04001d48a4420303110300140b9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 518185467 1250 518184217 518184253
    0x303041202182511031201151701030221070303020a060f060b070b0a0b030109050a050c0901031a100b030c070201030b030c0102030f030c040314060109060b04030c061b0c060c05 78
    0x30492491220311010048020030442041c214803103c01044400901120b00302001c200510345681c61203080c0d511036240540d40705400b4844a421000c10510381110500b20100a13180ca0640c0d0307040b105458584588490303c1060081d010440810341300f0b0705000000c0c5600411909002c82c0103180034404040301041550659040c0d214006049108100c1c080103c2c46140101c1d402000810000c540d00d900707840080d09540a050055401c0d4000b210030310100441003003e1401000c007901c00611640c952b0b00e0b5943c0301c082072500c4818a1b00c1c643c00082c61038a031100900c2c0505030351700758103450342401c1c40b00350344c680c0054000f2800719140640c0c0d5001858009030074411100c05900540c03500141d07112260340e03600051b01411612100f400003000081d0440150602e4680003401442a585806000410b45030981d01401811343c040000740085200e00c0d00007007c2d90b000e402e014208103002000c1c407641230807200c4040c180c05c5108101040d007550190100d0001c034040c1041b140c01075290180d90030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 518186717 1250 518185467 518185471
    0x8030403020904020d0317070f1215050d06020403021008041a01030b130c051c0b0f0403020d082a090102070b0f03010e0c040806090102030f181002030c0405030304120218 75
    0x260220b241c1001400520f08040d1042c1741c18420724005007540860055074482480c15260302c00440d04880d4021045680302e5080c403044905918140314000c0781015044440b455801010302544101400000307004032a01110001e60f400303000128441c05000006100c9981a14102e07540500c00441c40c0c41d40c2c019041240c1602d0f00013403070061645441da580c2d60402401401101c000c80713008000999035481021640c1238903401c15005007046094900300c0380c0090000d241950090340c0c40c1c01d020202e030b4001451031640c415070030507040c680c469000c0070383c0e8101c22000c1c000460300700303060710320310040141c018108581c402c0e021030301b0070750700d03041c09000c40d02400b44a42c600c007105000400c124180030513400d800100c01c01c0750500e825150900301c2e0511000b10b8501c4100c1e0f40000c00d01246810100c020303503100c0d0b0f191700606c202c00014152a901d491000504c1e0f00e00d00d8010000c1090401c07180c0448004120080403280d886907036070754104240f40c42c48000d910907a0f4490300c1144801c180481e480c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 518187967 1250 518186717 518186719
    0x40b0d0f1a010e0406180c0923310e0609070b0d020702360105150d0c051b010e010b06210403030219081915050f040b060a0c0c0803040302 61
    0x441881c1c8080011a12101c9440c1c3c4a64041d4540100148248150301c515201203514030022402e8a0080d2002d0284001903204507807401c980310f2082403440126401c02c1030000d04440700441000e02004000000003035004e504403107440907200d07044c40d0342c603603224040f40c07450074096804942d11482e9071038843c00304e8412400105000c209600d400d62041c1c1c002c00e1031a01c010030b48102d0942007050780c0c000142407050580b40b01c02e80d41c42d6141e201031942c800d900424044034001422281c040c45c801c0c0c00e01441c0d6502803465201d60614501074051030989100d159814220640841d00c0c100540c042d0610030021802546040310300c0302c0da418480210341c01c03814020403001032008241c02c013100c3e1000003007058007015824000190480342c0024000c00090f038903a201d2406080858401d1952003100005614841c42c1200032800e024070720344031908640d411288a100d03e0810340108015240100c0c080b90310100016481c450705404c043d1030b81c82c0318012031080e13402c1c1c1e44808006d65a4400c42c0000307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 518189217 1250 518187967 518188001
    0x20708060705090d020604151d0406140607020a080f070905010e070e0d0507090908090103050a0c1e0c14060117010c020c2106180115240c0503040b0d0f 67
    0x328800e03082504d5240503c40c4090b00041c60159140c8540c0b006002e090010300000380702407101c100304074034800f440049a00803102085120704d4184800c503080a60700500c2c0c01000041104002e56403000303440d80040110000342c85101144019007a2100b40c2c0d402143e04480c030b0f0500105840c01107000c0b585c4144107640315140720003031a03c1000540100040211058030a41d0360208140b1043d00400309024468030031181c6408140e0009802c0d1000241007030000c91401c440561460391010356204100d000040d1a03d025201200c12500e061221401400d0400c01c403035082c01103000058224101c44154520b070303c007090754032040c0e401c0c1c4070301c4080000164064002d9011505d48401c8074011429a4030f003801e0b800c4103002c1c009003042c10440d08082d011071201068548a00700380a1101d00042e5540b803c0c4d0114101441c121a00e0298400d401400021807220490280102240c042298115045980b42c40e610808408158051081001040e082c42c2084c0c0c0203681500032841c44406403034030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 518190467 1250 518189217 518189227
    0x50c1c0608100207240f0606021b100201200a17040b0a050a0f09051f090c1202030c130504210f030b031002070303090b09031e0c01020721020708060705 67
    0x641400313500010b105542c030701000500d01d80404032015004105402075500030999107403c01e4000111034285e031040081d504046822980d40d4a00180c074071401d4021107460040840c01c6004900610920a20600c5c0c407003800e84001032151114040d0191194940d11203121108414240f120410f040c2c800605515044000c90029200d98104c1c603804081e1040000301b12440c0c080c480c0c1550380d099801e5030141c0060302070070380541440d0240482c40c078070300724140070080c03d5946d40c001300a058842c0005030b00044022404550302488140e803200320041528095964000450000302010703603080b1007a2035251b080b603072119030340c0300e1510030340b00300352101e0010607851070042c1c01408804070030507030500841da0006060020b9202520581b80695800603809a5514040b0320441e0060301c01201c5a1041c031810040c0d0483c21005400c202c010b09040d03484400384003030903001e40202d020044c11414500f00ca440c080054000f0318080303807450f0742100c1215079258011500e480003076580720002031042203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 518191717 1250 518190467 518190493
    0x608040506061f0c1106190906080c09040b0a0308040e070f0f171e0c090108092e0b10030e1b010f0c05120c07030215090303030103021210050c1c0608 66
    0x760030b0b8030303000707190006501014900041450307007c0265403650009070543c2072401503001c0c0068000d0019070501e40c1450416005e0700205001c0c0b040c055105075122180100280c56000b0004015680083c1113030300c0f9901d40b041c49541c4070085075044001340149901c00d001900c1401d08408003400f98840d241c669200340c21806c6144c0000740003002c02010890482c140b0f40c2e0324a0b90f2031150703101e41410340c1c4a840000c001403a984018043c464603512840403030020005009c1c1c3c29501f0341c0c1c914000d41c81c414442d241040604140a60641d0002501001141c001d400d500111200c101d21820b81c0c41d03c000340c00042e411040030001c4640001c402c580c44003486400340c4491040140600212848000d8844240380c03e5484a2111505c0d500b12140030021414a04040d211004030f5440d401d0825400f500820354a010501c00a40300b10190a04145840c40600452040c60340c561000c0c00740d4a41440043ca082e40900d9805284095001244a5030101c5203e0281502e03c2140a00406e01040c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 518192967 1250 518191717 518191727
    0x1b0a140301140c0c07052202090a090c08010e0708040f0b090c30030c150709050904030806011206060816050405180601020111043c0608040506061f 65
    0x15aa240d0159aa218400740c5010341c28841403140080780715090340d40c0000c01545080c600c907940914000c0c002500001404003560103011071050f0400d0005803502888000103c070011a503025401135807810003039908081e4031401490503155101c804c0000c50311070800803104d6500450b0081e000110040c00040041c0c0c459075015041501c41c001c890030781140500188040082107541c1d8180654165075007640700c0901c11540000f102900550704015080c801c003601d0b0b200003070411565014001c006000c0301d00501e0b081d408ac044c068080400e074030309898098030906d0162000381c04241c2c075010b5011654128081e000950b20940c1d1a43ca8584400241d140a0380d101014001404002c2c08045211b440780d4010620f085003101c0500103906204001908560488408809001e01080284680f410301e010350041008103d01540c0c92030b8400d04084c061003400840d01040441c03c03c0001040c070360040c0380b2401039009805854203a19401c08200f05007014030603807050f03205501e00c1445894050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 518194217 1250 518192967 518192999
    0xe130506010e0402120906090a05030a0f12020a050903060105120a0201120f020708180d020d0b10031202071a040303090b0f1306050d05060f03100207060212011401021b0a 75
    0x605294480003030020010f81607810060703410403000380c0c01c41042200c41c02008100e40000c0e800018140301c01c0c0d55199180c913440303000c0700d410600c451814a20542d41c8107240100f500c400c1ea840c115201c0c0303240710b0b00031f08540c031041c815480b9106040000c5440d107044850f11032221600002860300b14200e034015501c241406005900c0180d41d0214203240c030361180020022a84500d003459a55a4444190019480c00000c482e01800b5001340160040e03e503450310240b02600304507800840d5440d08541040c140349908000c2060801126410310f0a40009010301500c04100903400c4100c2e0303000d000212402940b1010300040c81c4048108144403070f40b401001d10b002c541265a02e8449002c00d164810041c9501490001c0c10000302030000710707910700c42d02d50008011944200e030303866400c000950b659561103040180b507500142c1c55080040560440d213102c841001d40141c2903941b121010f02041512000601601807020348014641c00041c00800c9403800816481415080c15007640c3c000c454 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 518195467 1250 518194217 518194219
    0x50c0c011431050109110102062d0a0e10150501020102031b220e04031202130303080901020d05090c030f031201031203020c25050111060c0a0c0c030b160e130506 71
    0xb0101c40700896028090580414020648600c0711034400300028508000208280980810755032003625061203400c8944001a80586104c807984400c011070380103000f036020b1707140184950840760105460310b810101d4810b01410062040d1a82d4000580c06e0b440101da185001020074a510000c060780407002d000756061011460811011003080ea412101c02a0081034580101600b00b108040d8030441281541c1003e40c8150b08050070741001e03990400060000070244142d000c0012400d4800b50b05640e4041c0e0241c005004d035041250500c1d84400c19008024040e0040e01d0000d07104040c000100d03042c07102c100d8100c1c2c0c042da02e541c4441c1443d1600d184420b0401d42c003001925001001041200b85541d0b500b580703994203141e000300404606285178407140c140240740f0400c1249030400700322540d02c2800c00d0b0289a585a000008442d40d58180c80000c0071082c1e4000003009000c5001c4415101e0121000041c110311006030b0195140b002060302c0d56444646503090b8030303129074250441508840 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 518196717 1250 518195467 518195551
    0x40c080f0c130305100506010302040810050c0c030f0909060405060d330f06170a06090206090604080d0210091e110301020a2d090b1b01050c0c0114 65
    0x5203400d05542c85680c0d4400d550342d600c02070720404200020320989030047d100742011850280340c0240203842305440c40003180c981f980c65000402200042049034021f022400690703698000320703505000e06070410311001e40038100b500c000403000d09291003001c1c016000108050203a078095514440c4918024410411a001b41c030309642c020421081100c440202855010400f405203e403418100c82c3c807584481c0c45a00d928000340c002d110080703010391031960840d101181907041400480e400b840740400d5181c100400040001d40b0410110700c00c480152280d081e01c0358024104408401e490005d0000380407a155140503005904180c1c04046001e0702c141890800c2c82230850000f42280c000c1c0a001011840500c0502011240400580c2c070090038080021a043c0c0c6e041801480710741c00d030240d403c1007000014208038031031085881c451380ca20a24000d0280340750002c0100c8464104480c0f03151598240040c105168119083c124800d00c3d189034042e0100c19840e0f0340400c0400f1220021a11107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 518197967 1250 518196717 518196727
    0x1a0a0201140103060618110a050a05040506030408070c0b030601020705060c2505180f15060d0c0c301b0c0f080f060106020a03050a090e0f04030e040c080f0c 69
    0x1040700842a0007140509400603003d490b094000300c0d0340145094511085140594400e1100f20746001e0303650f1072045141942e210282c24509a641d449540c00a96101c10f02008120802c0741002c0200400c92050449400403581d560b080b07000340c001a0752090150300801000e204a060850140c076a14035a002198254440c11000744004e114840300c0c2c0c1c41d1900700040a102c6420440809c452150007183c01115070700d8018201d07000903202400454480050b1040075072565154026a0030b5608900000c001a030343d100c50180003030105200484084000040c401040710070319001110110809014a13050004a081160b808000e01e0100c0c000e0b428146100000c07880651100c1d02510754064002c070081e08101c810782c5000040d040300710b0554080320060010715400700d0a01e030400e60500b003403034540f81400c2058804440c1e64021903100c00f407240400108010b0302e6103890240d8001c0e25401030030240b030000d210030345046207842404180c0e5031010a55080482010365840003500000f07034208 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 518199217 1250 518197967 518197991
    0x708030d02031e070e0f03030414090403051210060215070507030e04020c0a1b0e0103020120010f0f0c030b030c21010207020306100801110702102007060203070b0a061a0a0201 77
    0x5510507114400042c8030150b50341c0282c1040d4071841b0708410304800850515140621040703183c42410040750181e003a220104d0100f5024005981c18011600f4844503070345002c510500b46c003c864821080140f040007005030b0201c0308031b150103004602594402d450b0103080d0b1401d039988210b091000360030075400c2008905c000010b00001d80842d105d40065007000340c201d0050142074005070004900440103900400050380c2111316203402c1800701d41d000c5841104800b0503170042c00080703125a05a41020000104000309510004001d40c0e561400c104540505041c103650700c1c0e0700244145c02050700e40b11468018504038588407041c80c0320001510303140d030690209042140941e13059140c030b08001418804a14280200c1d40010b8110790f880341010a1500002ca401e10840c01c60701c10b10041d40b04140f0700001411810b40c2d2030512904035445640d941c0b9009549034000234080d624104200041642d0a000f800f0302411501190a0203a81c40507145484106038440090762003950741e10481030a42c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 518200467 1250 518199217 518199271
    0x305011a1605070b120619061115040c0521030d0b06040b040f080601120209240306280908040e0c07150606080c0c07140a0503030304060213080708030d0203 69
    0x500400035003642c0f03444a00b0f0070005c0480c0c025101510803803000f82c0507800940030406d0142160701611306040010364000e090b50810950702c144241d19503030a810041401007581c5024100c0c3d01c01d8648080034124a02d200507441946c18040340785410821004015034104d8001d11116a070040c04103245c25a200310707848566100b54012628030a44410800104200f8420320b4010002240001409413984d4005080da500c020b000c0203e20f4407000d000e0107440281280d40111b4240981125103605102d1251125031101030181c9904010810311a070810103240030780c01049909c80e5200f41400d00f40b544610310b802000700410071211051104c840828a0003103900304629404500180c501c1c100380340202844401041c210491340304000c0c1c1130f114840042c642c41250320440c854400404481c00240101540e0351040764148004401c1c041070100c15802002c0070a059000903c01c035907160840340d1561700d103110385125600144084000035607240c00179980303c0b01c40719054a07000012165984 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 518201717 1250 518200467 518200469
    0x210c0f0309010b030c01020304063905060402120d0824030601030c080d08010506160201020106050d05010633390c1a0f070501390305011a160507 64
    0x1c40c582d140d84100419040070b0180021008081c409189480c1c01c00c1c6018041c40c4441903011811aa00507880c0c00744908002420310780c070001360b0320032114401030a10346c1e500c01098a0582c461202240c034081c44400c00901c0304424a0a41c5031440c095581c40f19070441c0403101c500c1c030025041103a49019841d9400d1144501031880b49154510182c1011900c0f40f41014884600080c0503500005200780da5558099680554032070890305440d9071503100413400f500c01640309a0704002d258107007004100c8103410400980354041300901a4004003184e44620304040d00412100c0e44002c1b0300100034921803942000c03582c000f4443c1c1040c024004503000600112820b40070310f400b440920381020411940102c500070724800b02402c0d1180d072400000c154603c40c1e0350103045618000034104040020a40001ca1048012b00000f03a00d00810081c480381400303540301400c0f010b001c1c042c22081c11402446828141c501c42003204a0482e0100100c1c5282c0d800321260540c0104007c4890f800520b0411040d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 518202967 1250 518201717 518201731
    0x60f120803060f1c0b220f02121204030203100b060a08040302190c06110a02010e190b030c0712031a040c020a0605250e03100b180408120c210c0f03 65
    0x9130712982c2004001e1800107802030f102e41c2c5a02000c103200d40102c3d804094107981001045014011620003d544241e88403150042c0740200482c52813240400b10251003140d00035025105000d001c1c03640700c421118528459035020704113201354401c0314441e000d0160302034824011900840c82c180d408040b144034041040f29010042c0406200703469000000302c00e40d1003040010050165a40e00103440c2c1306100c1202c0d405004901c601c48903203409520000006c0010313003289507036410310b54000350265010f140141c030949860b10404000c2031191060700140c500d0340080b1103810b489241000302a001d01d55006045200c0e440d9203e0114010f03100e954058220184c1102190102d0705039299825008240201400880444070107152004690315807101801e007000070395480c50030700041801c004683c40440340e0b81c98a013040300300f040320380c0100614203a40e00007446640e18264046e515121303c1d40f251000414420700c50340301040c91511560480c0607080c0103820814822050602c40d04115902 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 518204217 1250 518202967 518203009
    0x6070c03061505041407030c020309090108030a0212030c0702150f1b0601060e0a090209190806190e0a02040c030222030b0705251b06050a03060f120803060f 69
    0xe40240102d00c6a548000c0005071030a00400a80c14021a9040c400500032801e060300d40801d0400d0034828411a0f00b2060020440312844d610b03070115075901c0c1c00510400025204403150112030445004c1a2803180c0e80c0c10010302e1800c4103907400c0c05840000b6006d018041d0b0414480324607066156070140011911090110341020303041044031746800810b901400c1400340d4101002c110751118115a41035500a140c0543c0d20084880401d0314000d082c00300000c404904800400c48000204805016000b00081d0f1116080c501425000b12040000c23401010341c060704400e80141056086a00c500c4402d0030018144918901e123540420403038029840c10a0520b0000d004204001c20059044800d518025041907401070841d0340100994907000300020030703084008100001c4c00760b0501c0480031800c0c0500010ba03202406040b540200c80d41e80c010a05012000c40c1031a58070083c002210078803c0c00304072814460311050b50682c406010b00750040780c100f07001e10950b00d41900b40285140e10f000c0d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 518205467 1250 518204217 518204231
    0xd0f03020702040f1a09010b39100c0206160c0204061809032703030804050f0114011415040b07032d0f0206010e01030209090a060606080a06080c130b06070c0306 71
    0x18001d1600350841d251b4881c20013540140181c120400a42d01d2042c1c10455850f60321038125050a140d0010980300e800020000c100d92034031407400701e0040528150a1801d1191200b012400d903202e100803035000c40c8465080455407041482100e0000c00940080d0000615584038419010b0031600c0a01080090f9142d1200108060344180d26440d21420b14240c1e20001405400311010f403001840042e080004040104040c0201401980b50b85003c580080100e40c230340601c4151401c4003441041c680b49002c09030b003005410201d0851001d05840080d40e450203041c00c1a24010750008907090302000b40754030301903c81881644550480c1c08065525100c6815080703801088491859510310440d040500100661a4000040340c1504d90455183c0644ea40d4001690f141520585000d07080c2400c208001900c00d82024980740180030511050040944603420942d43d242801c81a64000704880307103000701c001066000c10113001c00104014900141c80c1c403490a05441c1d0b030400d85000d80e403804 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 518206717 1250 518205467 518205491
    0x7110d061b0302160f03140706050708060d17030a0b03030d0b03160e070f0e04021801090909050c09070e06031009050618282a050306030d0f03020702040f 68
    0x10319281c81482890158540094070301032440c007498021004100c11903948410003010300a40c40400300c81e0280e0301d117549542ca1405c11402070217080da0ba030070104918902069103070901031800e0445a42003101c20100080200884415520080403170000a0352203411360281d40d0b041c0010515400041d4011880b06002c508150420342c000f224a0000e01118604225852203d01050350004007030903d641707030b1140c1c000b0940f0010300d5925696440303840040c0c000210307030340045a4070100000781c0e65204015100c440c080219818800c0141c41c9a00041208035103192820005610000c9031070f22003400b10000d40444c2051f00182d44104143c3d00302401401f290405104180c0c1c44413007110a61154124003403140002c01c07000e08100071518681152441021a1031805400d840392180200302e03559502d14002142080d03006c030b500e500d1a40301a00081c043c89a02500d000300b40017000b410b0650f000642c2510010084a140c0092540030700642c0d0241c3d8a601c5403204551690078089200803440e2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 518207967 1250 518206717 518206751
    0xa0303020115081f0b0102120403210503130b1306060806070f0f0504030605060409210e0a0e0609100f1202032505040b1305010306020c0d031a0607110d06 68
    0x24000c54681d5100e0f4981d0511041e20780500c0c0d00002c80c1c0900001d100b140c000c0100c1c180018070034008c0504800260010412100300350894220840311010030721840c9841d03045039944800d640a5107130303020130200c800200741520091604580d040710480120401c0d0b41d680300a0322100d600900813a0017003007c00c01c8294102010104078032603894a00d410121004d009071440c041d50001404e00341d5220009816500e603580a590803540100d0075120041c292407803030a01041010500c000500320080c1c64005042c442448001e840c841900c000c0d0710394030b040c188a11284020051404a8001503000480030074034903100703002c0d110203202c128001c6d0140c0189032030304652061404030400000040c0006c000701d690510140c0c0c008443c0030610451280015180703816044c1e0409100e403a141c000800c00c01180d006003041c841e210151072a40092035401d0701100c02d155507054486202c0e42e190b144500e850700003000c5461159a0500f401c454001c0441c071207070601c200840e0380541e12807104881420303c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 518209217 1250 518207967 518207969
    0x50d0903030215070c030e0d02150d06060305060609060903120a02070323060109020307030e061f0b0313060902010c2013020c07090b120307030903060c0504230f0a0303020115 77
    0x40f010201410110780050440020050207010800a18942d40305d9a5903003014140f6160000c2401240419a16042c1e4859000e00b801951080c40c10f02c00060441c020300a5030300c109401040c60b8104a41c00041c4501e40e800350340c80d00c1c0e06004000071a50b074295003401801c1c104a050340140462070851034040041444040e291451840f01020305e0030241c00040c0c03180c10344404040140e101e0700d4510065001d4004105001c203a4014482049543c654039492446680d64008094050f5a40e84060f503425100039a0f0143c03114040030303000c4002c0303200350b08541ca0992062401d03407030103c81740d121410304800b4440c070013103806d01c118440041c0349000b81d404c00c01101d011804518000c107001c06203540301010b21030a8001500c400040c9010707035070100990903100100041e03d542d212a840e000340010070f1030004541c07080c07502c85504c162610440585095500c428010004010301c80c400244442119420319406846c5c44003295540d12143c00840007544682c0021401040c030b80748040400710a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 518210467 1250 518209217 518209243
    0x7140109081813020903101a0a090e0d030204080a0f0201090302040c120e010c021902060403080a090303090f0605031f09020f0c060f090d1206050324162703050d09030302 75
    0x45c0801486694080303442c03610550900c800241802003030a900324040e8020050503446208420000750404081d0821a00200c550080c0c900c001c607185000c5c0d0490081e40100202944141026000100700c00c925030311a0740141000a0340790760700d0b400101034035410740044000500c64501c45c80219068000d2100c81c0c0007540007400702c0329a02d14002e6507207901e003034682c0c89000b0070848a400e544510013214042c541000103155074221050300681203c6d0503200440002e43c407043d00060701001c614401017902d40f01d0362040d00e180c0760272100710303269201c00d06d034411207049050000803550402e100600c4413040310004c0b25102e85040b4003050410304000d100c5c01c421090f000400c680190003040e60390b50310f051800d08092a080b840f000000030281c54002c180c152152104c0030001e91054020b450080c0c8944030441c00740d66442880000c1886041c03036180c04510f481046051540c14698220791110707090310400c1c511030303490f2034440c070700a607406440000c241c03001024020302d5414484001c030640 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 518211717 1250 518210467 518210471
    0x7020f010c05100f0f180b100b04060309140703120e1801061416032c0d03030b0f0402040e010503070b040e07081e180607020c030307140109081813 65
    0x794484035103a190340302d41c401207150394203890003001c28143e101e0607520304ca6000400900d02000c42402418400314400c0d6000313412600003480100090034854107540c034401d03089003064039040055000c1e0500c000d0884040000c0c15242940050801c0400e00950240110f24100c40300c1260280c4220b440d04c19035030040829510a071180c1d042003403c641119694982009094980c1003c2c41007400392340c800d00c000d42130742c6001e5010726130702014040c80d00000041e695501d00150500401d81c0b134003000c92a4020340c00591190110b4002d90241504032009041e140c080b01c2c2420010303007240c0c8903400200001c2200c2005001501702006044040c0401d49404ca01d01420821148a0302d0070040c100d00411403500002070701ca0117901510f2070440306032503400d0224201600c0c3e984018007080c104e28040d1084000040c1c0b40b030320002c1c40c5110050050051031610049403617815660b0282c12500110350b4940c1320040016220303000070b00c401208041070b891000c1415040201619040180141081c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 518212967 1250 518211717 518211737
    0x815090901060915050109051915030501090b060a0c0321020c0f010606050c03030a0f020432010201050112080309281115040b031305190b0f04050a14010b0301090807020f01 76
    0x80d0300680c260050f100100c460204610b81c0704a030000498803600050080403003140ac000c80700303070145c21150503075aa400c011b0014048040601c0001e000d01010180003e2044100070042801230400100d0024101f060516a00780c4130f401794166442051110341a501264001260344401e2280d0000340c0a507181030b0b46403241030922690b8a0201500d2040c00741d50301c0c0818407044806a0494000700700c0d101003000132180c41c1202c1c01403a21070740300d890f040c4901e480c901046980b041c4240c5040e07130065840c1c90f0307000c8000d0b21045e03c2904002e1143e0400e00c84d02c04102810101c90907210031900c0500c085206a020314944202100329500c4c0c828007407020301001c0c40004203200309503020341d11600d1041c3e45940d58512010040d0f103943c4005880317409802c0c1110490050200103078100c0c0d003d96107025030707501c2e0359100c1100200200c13009003142e04100c0c100d074000703401603c01080040c4a000040b45008140001908541003880b0031100c81400081c0c6604505010480402c096803d00b4182904 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 518214217 1250 518212967 518212969
    0x506070e0a1e0e09070e07050301140d03050f0901020c0405180d0203030c0703050c0a0c0605030a0b01091202040c1707091404020702011202030a15080601080613050d081509090106091505 82
    0x2910302d401602800042e0000050034130b18100070440003440d00016104540c2098940a0700d507910070b0048010300200103400800a0400c6030b4040300320380e0715540e01c034a09181400c0d1500283c100e1507401d41103006072010004299110300a040c029585504910075840c2c3c0701898910300398480f441902950428010850060404010b40c0c41064050400c95614100f004426082c00d6225a00a04100d48400080f450700e0344840650311841d0011410400f00e4420b200548140400d88510022150181400c000504003904030000c030b4826420816a1107500951900c00048220760000000d03003501000c12030101090002082058242c40840c50101c80c0c1d0002040c0c2d000910a901503941c00001154005030140d001844c08802604866202c640b107180085c1ca8071405c4c418030203e442180e01080000c1c19401c104003d0f664000000d0148030301000302520801c8000340203031140b40d120034602d116502d41202a0744610740c1c031000003849a0070094010115220780b60301c60302c580000c00040c011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 518215467 1250 518214217 518214269
    0x306070206070e060a2a060b010c0c050607060219020303040209012c1906030c18060b0409050c1c0b18190e03090402120a0b040b0d08160506070e0a 65
    0x240c0a819961183c1d03c1041180c1580e41c8840c00041441c0c86c01031540b680000d01840c1e554070300340352040b0700074800407400b0801102c500b60340000241600780091020003031481c01030020300410380f084501608020440b02506035540160814501607000041000210302e045840a4050591900d0298204404e01700204801149036614a60514010301042c42011310034a01401c2c010741c2c1c2c1c1c0c02d000032520384c945200070140c0f0b8403c00521a02130241e200e40714106000c0c1c03009a03034407039140c141814601454440940342c0a4101a8400020000c85010381c801083c5401c003100e9400000c1080007034038040c0911680802101001d4040307040c10310807604003413070b40280c02d81d501d14000300e00700c0c400306009801d600c2200b0f02154032520005200c403028004160b26442500c111008000081304141844241e524100003c0d50000c1e01c0350007100000c24800280901030880c0e0003942454185550f0346150a5055804101007034400004a00c107180c19030700ca00140c404a844248034004a0001d010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 518216717 1250 518215467 518215487
    0x30c0702100c050601080d0810141504090c111c0206131127010e1905090c0a030c09061a0403121e030506040501061e050a0908011a030607020607 64
    0x480350128180d000076840c81001c03000710389a0403c0907101156545c1c080c4036990400a1007200220f0a2180000e621640e403590901c11034060481c030005003611402041084113210702110121401480003103507400300c038030a035542d904540c0c07900c90000d1403c01c481440d1103501072480c18144486943ea1410360b50110780e60303400c5074030b000c5880250000c03031070644070a05904042d00c0d00300e41400071012520707281c2040c00c602c812610200c601d950740c880e00c650000100803078400303422249461901004090710380c040703a400414017095a02c988641c000141d008074117540309680c8881c0210707003030100409510502d8000e2500c00c0c0c1044000000da581700896000310b21001d0101d101c107811000c2200c0c05a40c21103d20052011010385081624002400518050310740b240224030700400418028044d80c0d0180c0c0700012291104402002003a0841c0c8603400b40d035140d810840251400034038410240101c0c0c0c41981c0702c550000001005600b850f01d00b403002850001150300040c10300c005180c0242c42c0e14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 518217967 1250 518216717 518216719
    0x50417010e15131a0601090f060903170c01021804151206020a0e03030d270827040906091208010f09020a1404030b070210060b040e04050c0904030203040e0a02030c0702 74
    0xc01507554400d0200001091068043d00052038135032001d061a00c0c040b160307403042400762200d4151548501242c1c2c0180034900480021400801c3c0a00120f41c6101d1240d00d00504217a101d8a0701c4190682c5500ba6005034407194141e403c0010300c4841407803d4007038000c031844902419401f0f81e00d010402d0007002985840500a2580017800150051141c804420380850280480395102ea20071081001000d1100c041e290740d41103c5400984401c2100c02c0004542c0c10103000c5052024010702109030503090713403103440161031401c1070071000d0322766008900c0158005d0000150310038040c1094910400003045010400032218014418a16a10341d01002d0351449240103844100303884040da040b0400301c0c0c0ea0b0b0140c83d00828000100300d5520125072107044540d083e5034401c0c010b00689810740340c6900414910b00f030b0600c4280000820b8040c059440750250040b40c1101c400103010410f400d000b5079081c0c006803c0060148010000742c1200358100d407000c40114518509040c11034064000c125000b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 518219217 1250 518217967 518218003
    0x7120218040b130c0507050d0309030e0405090c0a080318031c1d0a0f060314040305030a0b060d0c02012004150318051005070f020303100605031e07050417010e 70
    0xc040d20380c1d01003c2c0f00c1850780401000031111091020700300d5049108110f81911400340d50b00c013898803d00601240340d60544480c0c00c44145d18042201504004005009512554840104d640c0e201c07400003006044100c090355480516071018007003824580c1509001f50f00c0002900684103c1d032100004081e01c0d40751070724005420300c4c07200e25840c2000f03001951040c202c0d140824403509440c8100111101a20100000142c4c0c040410460204850180c0840e03c24030001c6d4105049812016980c14010052460310380c4000e0080100d500b000c05040041c3e65840c3c0423819624032904103030034094a171000d40d041500d0419030020101011651004064990a6010001c04203103041c0d03850b594401c003501c031071034800780039000182000c0790581c000410891034107012a00100481e80a07950190009080c0707400e2500641d0207920280caa40d001002035802000f01c2016902114040d82e410b660b000e41e140e140c08410364110412207898452a49803d02c03d08445800148102407504107180b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 518220467 1250 518219217 518219231
    0x7061812111020100b0409030815030106090f1a010516030e06190305070e06040819030e03030706060302130218010e0406050307091e02041206020921060712021804 72
    0x411640c1e841c3c25000703401d216802e50342e02c0b01110404581488241c500b07010800c80e41010800300402c1c1c0d40c1c81c2c00007074041088540441c5041c402c0310064801e190000d00007180c45030741c40c0302d00d0046941503580310103010703520102c41200c0100307481268054142407802030708281c02942d40818001200c00020280000c0d40d000305001d40790542980d14400019403003035460802010054040c0c001103d9200002e4a4030109a100e0320b04a004da80070784041034010030000144504a0f40360216402d000d0301400a5900554000d540400042030814424080412190f2a502c1480180040c1014141840740103101c4221342520400c0c01c210801001d2900e00104103240f00480d0080010b90016a050300426601152412641d041000340c0400a11070307402965401d2074620890280d8015950000c0304c100012003c101950003405544100815040c0d15900305c030906481000d0790040c00c0b199400520401c1010350b00860781e0510b02400c41400e6103401d0034a00002a49030502100e00d204680d1444 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 518221717 1250 518220467 518220499
    0x1e0518040203010e2e080f0c0a08030f160f210815040902011e0201150b070305070206180406090c1101060503071509030b091f0c05040306090609050706181211 70
    0x145c00141d1503e14422403005900d500e0919162450428240e496100325884020b42e410154890707000c41c0c2007a80a10b05281c08854054410fa0090366203038610840025413802255100400441e041e100e104607403124901e005c005100c1d120415940e009212b0a18100080010400b0202c01c1e4000f04440004100e151440161860a441004003500749c1c0c82045a43c5884c1c0c0542c0001061030004140240003a40d600110f44903108845008001072070501681c40181828005454503456240e9000d150a00010205007141d207580c1c80086031544a80c8000b049540203440c92114998800c0280041418640440d40d1103c0a00c90240c0b0604d03031940d1031922038421f1380c644002e55840350b035406aa0405090030740ea904404502128807103c2c064418020284171320410b00350b800691169810300385151141c070001d0802002c180c134034a448580050002c0e000740160405040c16403200d04034000a4400c0e00d00c81001c070381124060480c18076100012403240f80d10000720910440e48101d030807500707003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 518222967 1250 518221717 518221771
    0xa0c1406160614040b01050f030f0a081b0307081c0203100e0c0c01020c0109111002070b032d010f08031c050702032505060a0c050304121e0518040203010e 68
    0x10b0f0a5031542e101c400e1108102c1d842143d18100d07541110400c00d90583e403020540c40c0c0f03403540c400c2c0b10240e101440d01400650180040d0030014080701d49001c000d0800320549041d988001c0c001c0f01c85180000e140c10940000903004108044c1b10300c02142035250007011451840e1050041401100e8009c3c000b03401154100100e84400d042000295140c00080319803902900903803c080311101d9002d8980021428003c0a54002c04040d9005180103031400006800da1ba00c06000810380042d000301c12a03101701e05145080a0800b44000805550326140700ca070a840c05980140040d500100800b00b680005d01080b84159012000d00051395140c0700e805a1031403150f201e890080f200c9555121382411384840c40c5003901802031081e00d480d665148080c204071070928480c0c0000c204144042404140400c0e04965278061a051008103400380c02d40040b03100240610300c50001c0e200040308843c41ca201c0040b00f100c078905840541c00d550411515140d100b4008101001141116000d00384031071401d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 518224217 1250 518222967 518222981
    0xe040312090213020d06050a0503060405030d0903021005070f0e0301021905250803040311190809040e060c040602150103030e090c120c18030c03030a050705011d0a0c14061606 77
    0x140d1400c45d0385e000401210300c0507106511a440c450010110000340e60305010a03998400c6a0240c051842c02041c44e02000041410308d0054085101d0f41802c144122440d00c6464001c481e41d4407982454400544020050088142402d02a900608c0340003642d004500740311800969a080143d2500d450340c030410035a40172001c1c000072000d00003001c0c1081c001003400560040b0b0099030b9406013900030f004615a155207562080a800400c01050804070760910090f00400d02c00034000316a4940000b0039520300401070300e404132500400942003000b80e8041113816522504a20040030640c510b850142c20a164160018040c3c0343c1e810014403003010b481d007140c1881c0b2401c01000e0060400303050561198108254400d41100d08002d0042c0303516000482100007000140154070b0401c160740d00700d416402041c022181592a00f01d0808500e0902c00308000c03402c038800003006c8054190904c0240800340e070f40b0440458116000d448920380300c03502120004864650b21003511f0100f40382a4000b0504 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 518225467 1250 518224217 518224249
    0xb0d0b0d06090f03080c0f040303080606090a170c010903080f0f0d0c03052d06100210181b0602030301120c091508060a06061d03010608071508010e0403120902 70
    0x181c00700740c4003000000b56240840c0340c02503840300500e0b92844101180c40c4180103040f050047c05003c2040000c0c0b245403601d40c000c3e0003a025030304100301c6c14042081c0c130b81140c002e013851012521084540d001c1c100580c0c04a00c20034600400710910350707100d9540318030892450710700c01a800903001d170390740280e4800c03100b41c04c440c2c0c072040282c00400742c00180100010b495062040138a603090402601c00d810b40441200100005080c00da111070040215401c0000f006005600840045526000c85480750341d032444843c0100c10310100d054581707002c0101c8840d00026200d550000b0610180f6400021f4905448078940007580400050403c7c40198140d40e104e400d881c0c0c10203c0e00030081142c40c11074003c4600440c00c899882d218800d14a084d200240101d000080b0400030000880307891503100c0001070b0010780001071164482071602d0602c0101c0d0804003030220b0f4039007060151540320748140d00403ca0f813444640c07103013000c0d5001801d1300b031420b680400058a41c00c111056542d50002070720f61082c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 518226717 1250 518225467 518225471
    0xa02060d0e0a0507030809151c09030e030a0b01051f080403122a0e03240606040b16030206090703020d030809120301090903021009080304170409140402030607090b0d0b0d06 76
    0x81c0d01e140020050303000402141c007402441423864084140300c01036806541c00c06100d102090380c0700c00b00c00000c07c840c400c1078040101d44400031a140d1028440d001c0d0131809491466165030404052140300c3c00301050b0710007855207040038440310a1b4482600341d00b055140c941001a02c641401c1d141c06418a1031180400740010300003102d200c1c1c96600c0702c0b0100121910391014402c828401c043c0c440000920003c401100c1041e40605041c04000255212500400e402e0038031742c50b800900803582000f100d901c4d155000039280810705404000c0c49501000c0380c8000d02c030980c15030303010074682401c0501c001d00b40008400420240241409200e40d0328503103a25450700c0c1d680d039004203170150141680540c054010504078105440941c003403104555041141c0504d180c40e07e1b500c0c510901d8100100c5480d8100500010800b401d4600604070b80c0a0b813072100390f030182060f00401d420110060000c80600c0143c00d410041c2d190414242c074015400308000003490b03248480862241e0321100340c010700b094 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 518227967 1250 518226717 518226719
    0x60f1a071401061d0609010b0306040b06120108010c1d100c0609021005030601200a030f05160b0406060602150a0b0a0e010b0a11060705040e0406090206031806090a02060d0e0a0507 79
    0x11030744e490520040c0031002028001a110101031010008003801514003541c01040081d003181002d40003200d5081000d8011840c2c210080d42901456a082c4c00c5030031103944502c008030000303030b0050358000e0490201482d004a0404080001c02c03c1d04000b2082303003484500080c44044c02900d80c000e18085402400c50f0413002507221004100794001c403030060114140c02a82c6000d040c500d0040162407240c10001c08005c00c4544058400260250b4580c0412070100486076141c003c0080350142d06104210032580d5041c6172070b00300241c82041d040341003158031845e0207400900746e40700380603004185540c0005000e94110080340e072a10007508152140140d81000142e2a05410024070390ad100c1543e8101c0c403804007940003a00c4000540e1014000343c020b01c0180302180058402d141c2081c40380c400000d00c8401a0b01085590300f044034080c0d440700201c03040002c80802031018580c170405030303400b13041c000360345900244c0709006a14008110766a2514011040903007003102003142c68001d0101c444007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 518229217 1250 518227967 518227979
    0xf1c110a092103090e060a0f06020309030c15070b10050409050f160303120e0106091802010e010318060e010605031609061d0a020913020a1101060f1a07140106 70
    0xc0703140740c03060860b0003a04101c0e07041c0d0066081606001998595141e080291424184003444d0801130b1840c0c2e80248030309000508107448140c01ca0081c82c43da0040c5441b100e0000c205401c02e01e1440005000340d5200c044209007856081c00c8a00f0154040741c215059103c502812000a0580e007156400034600481141401800514545611000340494000c020468581903414400b840002c0c0811070400c8050221071b607035040292032032001000000d07215074030420a01030342c1d219203049810844800c01907041d0759018048051011080c207042c0520b1000c090480210a08803c000e4501a6941007042000390207400007001001c00804031050000d44921034025400d1611440c00d00e03034900f6000080c561442e0401000442c008080c4c224960b68015411f0041d5010074103ca90181d0704680001034500c0901c0581000c0d09160360f14541c4507440c0700c1003402c680700d41d0003034405c0a5483c0d4041000c2c02029200e83d0900d0340d070030300700c1d03496840314900b00c1c2c40422001e00d807403c2135003065008560f03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 518230467 1250 518229217 518229227
    0x1120f021e040608030c03032403160501020f0c0a0611030c0607030e07081f051e0f15030712030c050709020705030d0b0603060310110f0d061a0f1c110a 67
    0x3190100d03403c02403107a60b20302c41c0384d8034811040304c075070030350030500000710583c04800341c40f03400c0305c488060115004459000681002c9503100206050811b021080c0000d503810428a58070300c03501002843e144030311000080f95040030340f04100c100500a10700440408090040d60032a58005044079200d0401c041e000c1e02602c0900c030b80340d0340740c480c040001410900c001202c0e403100282e004040701303a070201000d480c00b40c80e00618011076100e04480700003044204070003e61040c020b040d0b0704642070510300900c040384418000c0451195110a1040c0304081000856408041d45414078804903003003450500c0c1021080e0740b0003a001440450388000b8071034040010001003030300d031904000d00d280311000c2140900084d0b03440b03a01a484602652600c4410f640155040c0d410403a02c00d0070803911290300e500c1684144081e1400c1d80c1c170b03048100064074100580525a021882081d401c15038862541d000358010004c45d641c640c41007040c0c50265866036400a060590840ca00c40e641d88038451004e88 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 518231717 1250 518230467 518230519
    0xd14040b0610022a010f180b030a060302030604060c02060a0e10050411090a020c0c0a060e0d1110021c020309090c1e0705010b010f0813080903100612050613030801120f02 75
    0x3006c00c42030f0820b55040742c86045040117121b448420b008155003040c50340c0c0b0a64000030b00b40041d03070740d450b800440940e90410010748201d11646002c202e844104400909006001c3c041d079004a041c588062036124000c15242c50144422000194550b12424008801d514500146801400400900c03c0c0740f04540c0082c81c40305511021075030a14591410310400100c14418540041e00150104407180f6029100861080c0140001d0007040e420743d00083c0c6941004070040c0150f40300240c030143c0c20f0704601181c0000d0320b241c005542402c0144000c24510600201503c2c500c01000030200c01c4480100302043e100c2c0000307030078a03480304920720b0310500a00c004c2c44518040740e81660780b0342d9581c4c071441d959440b171204110000a15030655071410300a4100c4003506905010b1840302a40ca54114482c000003090102c668981c034500340c3c140942008800784c003403c0c02c00111894070003c01d03006000349045501200c0c05002106090070200318882c210000290b015070059141c86201402802d004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 518232967 1250 518231717 518231719
    0x6090813080d080103020d0c0302060d02071a0115050c0f0d080702060a05220c1d0f070e0a15050c0d030b030c0a08060703050403050d0203010303050d14040b0610022a 73
    0xc424541c0714000650780d0a401c0424800082c07043d00140b0044c1030008556032010710a01220401c1902d9500244a80e0081c4801d060301c180d000c10b48005024150200c2c040039444158005040d50504055005c90207a26000b40c052110006801e200603400700303d03089501104070280d0304081d98048004150740010388410700180700300c0303000c204d4070320891082c503000e18008010030944503203000c14121144080c003003d8a006054443c002000b0780c6001380d03181c50050350441c0c203082d440d0007800c0061840020b0320007001c00a4080d03046550b9220307848800f0a44480c02c0c0240c2c0a9030500008035654405e041c0220000d00030615074203412070b0103400152192a084080da2907151945003800b01800c03e5104100060b400b51f004035030b02c41e0080e40241d40140c0203182c80c5240004030981142039a0003a4030441c0000c41c0020300c5090805684500509101001d5001d80282000d4403000344c1400041c081910801180035103024440c02009154944c02e620a0030041103400707003e030303080c0c0244024101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 518234217 1250 518232967 518232997
    0xc100f050702015901140c0d0b0d06020a02071a0c0a080306010201060510090e07260705211602070303120f180b0403141321060908 58
    0xc01c403014018019200e001006100344403684841c11a0324212500c1d12403c410741240001001c2080c856600300c040603110041007148500444001c09421030b117500c0c1682414181440500c010707005c0a10480c0c045514002e0b0103d8810030f124005581e0440240e4000d02280c03000600f1580f198000c03c0754404c448404020205c0b042d42541d440d0194030401003000075541002450000064018003d1900041e040c030000030b84075115000b240510103000451300c0410b0942c0000c0144402207090030754802840c0c81c129400b1624088100510b0000d41d2009031450380450002c0c68640c858015240b884060710b0850181068407841402d0221007628a6424038444515032840140006a68400c1700d526030f550005100f19902d40c0d10061158407480c1920b5a04c4401c210142611140d0612260340641c1c0300f04c40900385458081c180c1c0e1880103020311507040500c580e00800f8420341e00f0743e0444180c14240400c0e0b040020764801d51000c400b2004201d540b4007842c64003403160305c0f00070b40748a00002da45 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 518235467 1250 518234217 518234221
    0xb040210052109010603080408070e0c07080f09220b0406050301050f01030b15030703060203012108030106050d18050a120c050a02100513080c010318080706110c100f05 74
    0x104881c1c0307100b000c50700000d441c01901220300e5000c050318025400700c101030001030025183c0d65900540e86c0f20b503200c80601c0c4d01401c414400d804d0002c000a4000c040a180541b80008540d624401401502a0483c07101f0008c11000c00b50b44818902c0049003c0c609441b5042800354050301004004c103801d5140528034110380440e55041c14411702e07025000e480105c0f482c0e68030f141e5820411350f0008011920601300019010031640f41000610083d500c03551001d80c172581840340b05903010301100135085040211040380408260004105c80c192900361410030703552500c09880101908030021246000e1f5a451002c4040c41030126950000c4c40c802c4141c4030001d00c05c18402c451aa9040801424640000d02118014500070b0f408558070540d82c248a410081010300126012480798480c0140e41c001c8a15041150780c580701300c000c6443d8188040202c41c0b0241c41c0c01c41c4e00e00490100034425640c131405000c5d90b0042c20300340d402c40d039034040464100d1100070010f84007602c01e00301c0e0b6210f00742c18030f00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 518236717 1250 518235467 518235499
    0xa03020304141e04020304020102030d0509030703080c0913020c1f0606020c010c051b0f0d0b0103030809011103011208160510110c0303070f1b050c03060f070503010909021302070b0402 81
    0x40c02507209a0055000302c1524040d1013044000e50000d0800ca041d03110403c440c8030000303000d009051142c40e040010790f40340c010324207001d064150002c0181196010810100c0440c1e540c500c04030440d5030760170600503116045c29900038604008508000883c004031021102041060340000003981c0700c99007034442c10301641c0019641400b80d014018140c4c1c0024600341c0001d4a03180c2c003024240c80c010080d4114030f6180010444254100354140c4203d0900c20040c070074590041101303500031210741c0c001c20080800c3c2d99500303c10300041c0120000504403004800c2030000c2c03141900c804121381c0c010051a03890528056642d2f0b88d0840d2013403c0d05081181841d40244000142c40051803810069841c0d40c2d43c4903001c0340c40795858038050303080c080b111024034452a503070810100340a204d40c0050107007070310241c10149000c0300140010b01c19001032080081d03240d404000e590441c0c441031008103005459200140b01c8400740c0e110128002d1000c19040240010607a4840c0154020380c1c280a9480c0b01c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 518237967 1250 518236717 518236729
    0xf09050601020d0e010201061d1501020d050702190b1216031e0b12030315010e040b150a05041805070e090702300703030207140c0d0201050d0b030a0302030414 70
    0xc44450150700002800c03000c6a002d40c429038040c460501c0002401929162030000c500107492001060041e9074003040107500d0240458010745109000070070f0308003190400241188188140280075049458100d422802310003c064094664030511540382c0f9219824859264400c42c0c080c50184490b48a0408035402480740a004201c4000869081c4640030747d40c1018226070580c160300300c0170904882c3c86034441400030f54014078103d01d0081c02c0710741c0c410005050b17042c0040035900c50307480c01c494020250ba8a11207201880180e4040d6600e800007600b06aa540c02a0f0344104c0001e0307100c0380684540e40341759001d244141640c1d294a009a0030941c28420161411200100580d1185611088c04400844018200c2e120341290502424080305000f00a070440b40c001c4020a40100e540d00404c014010309202c41c81c4040010908030708240005003c40100301d0000e0b0510a00150f0641c5481ca2900054450803000e400c503040403296240c000c4d81d0380e10511800c1080c07a40d08e54944081d14100c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 518239217 1250 518237967 518237971
    0xf0f100302030d0e06270a090510120f062301090c02060711070803040b07020f0d0b0a09032d091d18030c160807060804050a030c020a051503010f0905 66
    0x607005003034090042c0b400b84c8002c680d807042a54001e20522541c000e049404291100388244038403007112070244841481000c4d081c076000b60700c0040c2442c04010003800c0d420421022a9200c3c0c441d10452201420a03086401c1f03403860203812181001a801c49180074120180d0307200a4541c10072020740e076a810444c044802150300f940041c7c014401140b100ca00c5070390b030303a18005502825182c5007540c681ca80d030700c0e540c441e034030004074502d0210317402023503181100302107940801c00e0300c2104900708a907a41701285a0000c09078240aa640d000703400515100d44040e0400720550219054802d20004440c0c528082c6410284000b80e00e0160100d110402424070300e5003841300f10a1055143c895080482e101000800f880b403c0344801d200c5984220820400c0c9541e5140c901c508125a50400d1061418400d00740c002c01c0c00d000e85003090000144000442443c0d003030701450b00701c0714000300380700058001900d941300f60b50040c10359a1800d040d0040c00001c60403244020001c3c2d40190740d07205118250780e41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 518240467 1250 518239217 518239219
    0x121e0f170909060f130b0a1805010f08070303091a07150f0b031903140d0c09080f030304030509010c110411090103050f0f0601050d06150f030c03110f0c01060803030f0f100302 77
    0x10200036510441d001e401500c0c10036070051203200d0940e125014007623a034458050b01c0c00c40136100c00041000c41c2920720454060705108028003480c50a40d02d016040c0c81c01c612428400ca03000d4004003583c081e00c4025211107035030100c2120011029504080003038105032520b058100e207090250909460001240c04103241508428036040071b06440544003400201414200c00400704144840e15496100b0b64112600544071a40098180b90301e6a140c405c84d089046900d90040050102107508441501d65a910910702503521200d2072820107602818448290340040c207200070f14103290191350103400240420f0b6010042c80c0d480742c0d41164401000e6410491003421400410015403240d8000c0c0400c190f40e000c0130030026603d001e280742c000380782c11440c0001184484060207a903458010322440c014145020b00c059010b400619480348148502c00121240010341c00351b4115081d00020000e007041000d1f80e490346003000318010002030403580c2c508805900000188410141041f840690760 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 518241717 1250 518240467 518240479
    0x501170412050f0702030f011506030504050709020a020c0a090614041b1b120512070206090d1d0301021b010b0111060f0a0e0604031206121e0f170909060f 68
    0x100c070401d6a09a10001520301600c60400c50013001d81c130204410801092480000240c1d608070000d44210410340b9003045003018205070610012441c001003210644512090040e51800b04500a926006240c0c4a09401c0f001600001540794503561003407044a601610460080f049001084125502c03a038801c2d034220003600040c0081881a0900c10308030080403040340340c0c0c0b40c045d11110211741140e44008002a40058021a1844034a4030503800483d41e0000340141e0400c02450307601d42600c0a10320040040002001c5462a50504112070040010b03000715030303440300c0d041450307501411009049680d41c24500c240748594494801900700c004d02c00d010b403004d81c5501800104d00800604102c64160320307a0f0116102030350a100881c0070740c0c401d40310300c030014404640c4401565056800621050083c40544000c100000e55010143d0300c5048181006d42c02c034a03001c02c0614240002810088420351a0003a034907010000b809200002c42d010000c07990b44004010416003070b00c500b650015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 518242967 1250 518241717 518241743
    0xf1303170c0403080301080303150d0b06090402031006080102040f0b031006030905031b0102090420091314130b060301110409181e030e1503180313030c05011704 71
    0x340c0104041c1c00c0750004400c1450155a6240d19040b03400c01e800c6061241c1001050000d4200455013483c04c1603001d842c5901001803548580025400c002e110314014050400000c0441d03070144406401911003842c20001e09480e01040c9000b074115020701c008820700a130300070a015a50301c081c4c030f100380c41807007401d4900ca0034181e0450180c028044111017903c0300380b006950000c24800185004d000c607200043c1c68054540801042d50208604841e00f1070035115020641d1850701c00702e0302d00283c03d885602003850380c0036a01000300080500200d101d030b004c00602c1428034400d50480351090080c281018680c580b0420942282d80c0d41400c02c9840c013040100300900060382e00800d84004001c105443d11003016154092842c42c01041410303032680c00b84604c02003681200d01d60203140f20964100009122202d40030304d943c817020f0100c3d80220102805149044000c00840f9011410f200034500c0712a074a03d00320000721113501440b404500f80c16010f070302050441000034031498000d12942019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 518244217 1250 518242967 518242997
    0x20030f011a2407050a021c0201030506040b1e0118060905090c03070e040c02190b0a27020918030a0201060303120203130305090105041703030405010c020d020c040b1305040b0f1303 79
    0x6a030000f5002c5620703018103010000503a64040343c4080c071240d2800b0861136555148001402c541c00140b034240715500d0004d007510592100502c1e0100101c03078028054121441c41c0068400608013002d1b80700c0052403580c04200194010b00031000c0728400d4a900c034107034540a4486030740f030108841450002c1c1200b6240c01c19071074150030a64019071240150360300c4402c0710120061200900d078040d90740078030030000c0c40b10788007062040400f2038281031005d8040040c0d0001c0c10030aa41e10310406403042c2c10340c0b0b021031581c149210540464090799022696201050100039000c2c0146100c01c3d408144502054491800725000b20391085c0d1010402d03204c0788a0f542c0d004d80350b80d000b10300d036941040010701c8082a8400b00034000680821004020b5469240034034001c0d094500c0b1002801c215000a82e4030000c0e01d80018207d500403070116000305c1c1c14246100411110b0950b00c4400300f03094284400c0c4401e00040c404014041c03118074032100201ea0f44c0f42e440003c03c801e04d0700000d00007580c035683d11100d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 518245467 1250 518244217 518244289
    0x7062a021221070903050f0706080c0c0c271303120c09090e250e0406050703110a0c0b0106093c08070602160b030420030f011a 56
    0x9481c000c0b46440c00481503501d0002041481210070001003250080140103201040144506428040c001480c1c228100b110040400f00040c0c5010940c1c031020403201800c031400d01030254041030250a07006809407901c000c45480c1c1040640b800c420200001103885040700c440e03440901d64050300e450750a800018041340040c10b0340610782040142100000c2a00304007405641c084d00344410041151501d801c04240f506030031015503401d06070585204000f100c000031340c440d500c1034111400244a0340c44c082c1c10350283c20801070300c2c0c4d101c6000182000c0c11030340000d04007004a0044a0381d41c1560b80790001600d102d1800c0c0900800840c19200c0200200c1d03242c183c03070f00f10080700c1e0380300c030410b59003540e881106c100d983d00404034681103903405010301603041100804a0007102284400140f0300b403501e0b03107540b001410103030000da917440c20218a0466075000301500b071009070032642010455000359000708001c0c00b40420070001100301910350301d080c80f2a450354146500070301000f0031025201c3c4032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 518246717 1250 518245467 518245477
    0x105091003060c0c020a08030909041e0602030a05010e1509060d05010e0712120e0a03020904022106091005041109091515010f02150103080a03060b07062a0212 70
    0xc00e10a2954012000802a0048003010001c5458003040d0404620400401402c070343c00c030ba6541d078003c0c407006090b5610200c1d013942050b004903200034000e2102d480e00c080c02c18035840181c0654000014007802d80d00513071019049620700681080c0907290200c1821211011501c83d0b5800039681e00469901c0c1b4003400c2c100303a05840303640005403403036075090441d08146035035000d060040c804510b038000b030000954508601229070f181141910300083c0016845407100d00000c0e014540c000005002c54690f0b59024100c462841404508070000e4510a5a00e500403906400240240300d10010a0001801342c58000e9034400d2500b100c6000c441c062040304940140346203143d03c280e8000782d10896916070018012007981408501c0308540000141c500f603040c1001c50110351250300c070561440b020384140ca054030340c01307521155119000b1608030060142508400700c04500010500308111284c0d0000c181841d4050343e84041100e40c440803840c10705645008805038022148440200c200d10f00200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 518247967 1250 518246717 518246731
    0x1e0a0c060e0f0d0311040503070e06121c051c05040c05040b0f010e090c04050603070e010801060f021b0301020d18110f13020319090501090317010f0e0c0c151b0f03010509 75
    0x6e007802d41e00d200003403910080b41c1c012469031030440c007440300c5402c040d0383d98030140c0c1805008084100d104200301780078040e042c840c1d40400a01107410189042e0746948103904410f00307071081c8094100790400c0717045005144150361183d40380c0042010355040101040300c2521058441100c10307020b150a00c41109801015400070401c00c00c00401c075a41c8603005140903010ba980c41c41e03686814400050030766581038002d9003c4c8400c00c0c02c000300d0315078006411150f600001e508002e680108101280c0a80943c5003a0081d803800c1039210100d414400c100300444074010b011114492950b2400c0c0003447c200198540c3d001200449a9044d4180ad5002103811100c250130b0300d211004000d4030340702241c010050071180d0303075101d030756103404d044e40281039a01101c4070200301580c07945008000b0030744a00511079000410400c00c002228401004141e4491800b050240c41e4100300d1502c5801610000b11142e0043c02410800030b05145121415142c039402d0070009107241d6401c007030070401c0000c80240380e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 518249217 1250 518247967 518248001
    0xc01110105091b0a150503012903060111010912020313050a080a030c03022509050601110d032408160b0f07020904081605010509011119051e0a0c060e0f0d03 69
    0xd02c5c0442a030b000c0c4e050749580c1e071401c1d12541800141c2d01e0b80117030000b00c5401c011101d040042d0f020400304c1101d030480800d00b4140c800f82e0405201c24003400382001c000d400c54401140390890035401100603e40c104901102061868a82041024484142c051060158010044003000901400801450074000e0048030710740500040c104261108404c5040c2c600007050408021a01c558010a6040304013402c1c43c00a10050a00c0030f650750005445400806460790001860605a43c0c85000d803001c2684400181e661102103c1c2e9880e801003c210781e880008407000240c04644006030342d42200032100382842c3c80b40320740030040d401001420075109201c1c03c200045c50302c001d0302c40c100da845102d075001061070b00d402441642104e01840090040c4402003280d1300e039458105012020f2903009052090701c030400080101c0243c210b286503809005000a9003500407600b000c4260a400d220300070500880491414141d103c40304460040035951045103845800c41c000e40181c0d094041c0500c203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 518250467 1250 518249217 518249219
    0xe0c0c06040f030311120406181709010206060307030507060e041d0106060f0c0803130305070f060509060709140d060b0d0804091a01021b030715020c01110105091b0a 73
    0x24203080c1001698212500c0302c1c1000c10a04242d05800360045072050308128606004070030303807004c5d000100240014180c6645204500c0d498084c01d030845030300e507081003003c1e0001d4207802550750550f00010b41d00303015108840002d04103144c002007100980f079010028002c0c03640b6011041e1920700511516030b074080d8aa5502001c0d01c202c0107011030988507104c00102e685464100090400d48030340102d203007007003080c2c1c00e0040803884000490340c202030302c02410352040b801e07400e00712028050044010419860701320b910040c408541c0002d4003c20445c0c5c207403041c0780c0f205401074034590524840c0500035111031134266418540020115881c6000b4403000c18022070000001e4041300d0001c07000c6540c080c0100f011300c4007540c0e91250398403d50384515101c11050341c1170000b0307545404a0381d42d014224811a000b08c8103403424081c04005207110202501c070300b070710108003035202c5075100351190020b40485040041c0603814007031b00d40035801d0900680b860301d40c5222000580c0d0f00d400c10180d088685658 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 518251717 1250 518250467 518250487
    0x1270203190609030e06030c16020f0904050f010e06060901060f090f181a0a050d080d0f0203091c1d03011b051e0301060e04050402030c040606020f1e03040e0c 70
    0x20407544980d01c0b8407800503040d901c40c540941041080301c4110b0250000307000308005c0c480703480b003182c010700060b4485821148261000500440d000745107070b41c0045c03800042c0030811000044160000650344001d0086008402e400c0d59149000c407046580b000400004200c030758062458080055001d1801c194015220406662003034180d92055802e241529000b0402039030718421030854250f19102c00d0304184446000a020300303d5406450f10600020782c00c142007003440c9040740c100e44030028080c031510003000c001c200290400c603004a0940180800d480880d202e200c03500a105060382c03103450070f80140c480646081064401c0464141d943c41404444040c1e45c0e55070f4225030015a07079074564075010440101040894100f00c04032000c3c0510052018541243c0d0349501c005d001d54001806a646000003850000b0010080e50001e1401c00045152a4041513607100c8181e0282141d20405042c00841c0310b40c00c5513003031046250814041400010071410501350880a00b00fa11414002080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 518252967 1250 518251717 518251753
    0x10c060507020c1002120d15091b0e0d020a09021b06010312171b0a0c1b0905181009050c09070504150f0f030b240c010e01270203 57
    0x29807104096407001951031801e00e4014030030251500544094800e00212004412440c007841079034010207a102c5102c100c0f01c02545494000a00344400c00340007050b42002c0c009604801800828009400d000d000c403e0f5041031101c1c0003c40fa4080e00c42e80c0144d00d0500c41c60000d4014080403060a80341c10360100800d00b040000303078041e50042400b8404040040c2c0d01a00507245242d1000811494a04100c901c80b2288607498030b2101091a103560349100c0d110864103a06c3d0240028040b11518280140301c4588a14400680b044400100559241c0026000c40d0b600b1002c00c0350f002e41c0c4450040072143c011504176070101d6110b4070440c1c4070607140c80002010440d00b210000001900802d0402c03440040f003e071380b9102e0f855400c090150b450f420300010700d035100384001c01050540380c0c44040016254001954404040300d4144034041045400350100e5911240d201c440d5582071a54041280c6018441e083c4441040913080c01081c2d00020880c20900d080325081e43e2600500c00070b04914038000f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 518254217 1250 518252967 518252971
    0x70302040b0c0f0c040e0607030507051201080303060405090106050d0201030b06071208190207033e070302030705040e0d11190605090105130203070504020c01020f07050717161202010c0605 83
    0x1c02c0140a400d1019000c05103080750352580c240c4281e04003080e43c0030a800100c1c02c02e41052140c680490140c1d1046001d540d184180c50041c41c400400300c000060440d0040301a50161504484c00d0000f512404070035400e0b241c4602840341d106001448090040d8040e501159500364080c0c510f0741095501c3d15040001050b03030301010041604881000031040c006203181c40b018149140841c00c20086490080c040341d02d40005906425005501080030003601d030761017010814415040701c0c149400c41120740c65240e41d22040b8064480c240010030203150074021340084070703100c80080801c031003030310400c84a8041ca1031205801e4001c401d40c101da1100300000f108102c50060401240701d003080140345086a10040614503004818030301c0b0001603401240d003404542080314017588401e07010340103170300910407001e200100401c006000c00c10040085480340444425a2401e4a601d0004030261b8582103080004041a442040240070700101c205005902d54010f04d80000b2903041d03540d90404032002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 518255467 1250 518254217 518254237
    0x60f030702060c030f0103030f030f05150f0303120a02090d0f060b13090c0b0d0f061e0b0c030904020d0e011a0a050105090117070c020d060606090b04050612070302040b 74
    0x100004200e5103540411260341c00c000e504000524528101c2c141008440c3c06020003810441903551840049109400c50b004160b441401002241480441607824025a20010b4002c1d04043c400a20525001c4199200f0000c0c80c000d0032425600c7d1100c05c0d00940c8030315000da6202c0b8411a00380003150a0200c2100d00920429001829950328070420104031182c144010810381803615481c0050100c3c0c0c100400c0b55540b0031210348400314040b40178013a0030100e116252079441c14100041c807044101c400942c0d12608030030584003e0b299034000b502c501c02d04100b40d11561080020340d0f1141032a03402003000c0100008002804030419010f1400e41d0b0800b0780fa551a400c035103500d602c1c02d1900c80c0c1644010300b003d08020b45045c941e07800180880c20501d0354020041d404a002691080c013916a02e000c03603500401d5035604605900d40080101554021000080d14000c0041002c244070012a4190742d03000300b06034241680900c01f10401c000040424080580a010015038134801101030302210740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 518256717 1250 518255467 518255497
    0x201090317130f0308070b0601032711010e090f0c0f1902070501080106020c040e03070501290a0648140a030504051e032b08060109060f0e06 62
    0x642e006015148050300d80161640e041070b4141000005c0040c400c036881558022100d40daa135850800580c0107195070543c1e0f40a10004015070b00007100d00c0680306040750301c00c42d561851101d40400459203d4500c800807900007241002054005a5440b0304a031f0107004101980e00e071401001d119203545e000344010100e506441c541440c011601803000d400644420b00e0081c0e032561424000958840210000c54021940d50740706070b080304030900c00c0780d200a4111000344403420b50700d8007600c07801004080b100d00002121201c003201b0310b42141d260084500654860404038410300d1210326102210082041d18a030100704c0c0103905106101e041c4a001c40240c044000d80c3c0503041136203101d02004110031007900010784001c00290010255410340fa42603400a6010212964240b503020414036456403522a0031a0011070b00c5c100514614869101d44456040c4e44410405540c00130060300d0f40d074007048041c10140216407182c00300410500ca1450710700400305907800499540d038403040c03510050203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 518257967 1250 518256717 518256727
    0x190305010e2802090105070206040b090a0f030309051e220e0606061b030f0424110c060c0a15020301080c09040f0f02060f1303062003130201090317 65
    0x3940551080ba8440c0c4991014110240d911226500b205007411104070107507400f00b000c41c80e6074442c1c42502e540e180d010307000d070382d60b0381e244d07400c4e0f41d402e80000310094031401030104042a01c4099802400c2100d605450b40c8001c14280000c10443c0c001284502c0380f074001d07070f00030302e1442d95415815403c01c4406040b0781060020824002007520300010810500303601000500c07565440f60011201c141c00307074844011451010201e8a03003144100280014180c4c008900455000038004480716100e400a500321400d8504042c151044a5142800c00b5290811505c1035002d040a200034520b400c5802e00b40e404188030350391000310388040c1030410703a1410760100050045d101c080102c012549030440b40703d4210310b41641c480460650b40c02c0300a01d4003080354521011512580155004410b5034200720f901c0b5055003c0e02581c4000510081e10304608240107030f40e000000810b41c000c1000b82411039031640d95241840241144c201000300d041010200001010444043c000440903602644460786c0f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 518259217 1250 518257967 518257979
    0x70609170d05010e1807120503040806090616030605090f041e1109010f08060a150b07060903030b04053c04030903061a0a090f11040f0501170105030c1519030501 71
    0x110600814174000d6031902c546501c40c0740320004080c012600e49003400701150810345401d81c114000c50344240000c0c80741e482030140e626004905584100f44440340120b1514035131030100d0541d404c078455160451000b00108100301d1007600d6031a80203014407403080100605480d09146242280e10540d2540340b428181c0800340b9000600c1f0303004010784811488080e05080c600d5480707030005884100c14a41d60b83c00c40008082c9440c00b0b4004000000f8419204c01da1030501c00c001d004600800c0300020314024140780300d883c00e071003904c1c003134080280206500000119420480c0c69040c20001c400e014402070b114022200c0320035544501c3c42590b403900c442e4614a042400d94a21810180c3c01104102e03400c411525403503040000c4034003401e070116410290a08501c01404030b07117010204294006004600c031106065014129030382a40c3ea9a4122040300e00048011001e005a60789074000e42220704440c582000e228107640c07051142c9628010101044516041d090700f80280802d032148010001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 518260467 1250 518259217 518259239
    0x80c0405010e06030303012303070311120115060c03170103060e0f0a03020303160e030a03050301170309130221010323190b1003060207050606120f03070609170d0501 73
    0x10310b5207003009201c60504100107600c0703020500580e5886007440f40713076000240134280702c1506460081e0a072140c04e41c0303900f003035407405c0704807203c0d20f01684080e900f40250140522400e150680c1040304844000e0401804a803480c400039026010050b03c401052003078010048058000c5100f40d100041170780b858008241800341d101ba0026180d0410514000825004400c44e9441680c80044104074541c00c43c00f80e03058880c80d20301c203405102c0d010062007010382110046068400d0020600d41c4405d5000000e950313840b81654040e081403105030091420905034010704070340000002c400184000c01c0401c0190707858264402c0c0c0c2c21043c04e10b032103401000c0141800700b0500650015145900345410300c00a00740070b0010003132010344408005114881800c01060207198841d50656031071b00203080451341e402d01603076014442c1c1540009201003600004040c924003070801e02843c20404d4a031100402480c0c10031050b110f05841c2c003030b40a81240c000c00101507001c1c1003500050103504004035025 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 518261717 1250 518260467 518260469
    0xa06050403030c11060c0a0501090605060a0303050715060b0a0201360b0612010914010b090f01170705060a050c160b040e090a06090f1a01031106070201090e01080c040501 75
    0x414400208030a001107588054402031290300001c45840213603a5102060b1144034141003240d0324046d00007103104100041d0814031416004030710a10480d2107000030080c4201d49840000d02041d0304118020000750540205440402c40c80c03400a11641d455610322a164810001d01d00140d568411031540142441c441c0040d403c0d01e2000415211241c6843e80098805424007406d00148100000d0240e503030708940c2c1fa68200860300038032131058246451b0381e00414444a201d00b0303500b8080b03001c040c0c3c2030510502e846040f40071900780f40d0740d1806c108118920001c1c01110040e001da02804150b580302d0070001c0141607000d5950310f0351803d049006604000f0213450103014140107000800c0145c0445041e1400c2e41c04040c0c0b07815198864200f4280f400150300710003000c0034202007848041c01040002248410300485982c1501c10080e0521740c00e40c103013400700820781c12a5064a90103402c145014040d400d206040c038a08003070711481e5580a04100f640300c203209900004409266050034080c440c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 518262967 1250 518261717 518261729
    0xc03040b0f07060608070518060d0b0112030f230d0603060f140603030c060402090a111c0506030708030a0e0d0b010801090308070f05030f090a050a110312092b061401030b0708091203070203040902040b0301050a 92
    0x3107186450000c2149038110310d00c035000d48100c008514883c604446a20050045030703c10410003c031a0b880041002030440300200c00704851030900003880343d00703012007105ca56200c0e0001400941d0754540c2000030000011b0b20b00a2120703034901c0c1032807550040b04001e02020245040d0a00340800345901082940e0300102814001d4010000c10020080000180d6170f04400310b00300071580307446030800308042c0501800b002d0061582e032400010385641c19800205114000d076030314901c47c1e460b8841a510101e40d2050f480004074100001b820500c004690340e600400300c9001d5800030f51054032943c0c5007481c1e00c903040e180c01c032050000756000c0c58100001480044441102c03810400641c0004164241030b0300c40c00301040a005060141c264500d4002c0b42d2240d01540400c08451100080701a4400034042110138440702c002181107140581c140300e00c103000c01ca008011640446040c00101c3d00081c200d401948018071010072041c00c18005000503103544c070301e0a034680d80b50004101c0d0544442d8484 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 518264217 1250 518262967 518262977
    0x30a0201020703060c1803080c06010f0b03010b03280f060807050918070f0602060a0605040504080315010509040e01050421140c03040b0f07060608070518060d0b0112030f 75
    0x140060341c001ca03600c011690024400225840041015164118480e90110110441e05404800c1065003401b426010b0041000c031142e40c0c0e01c1b24003c0c0344000503406041c441600c18001000b003007040400a41e4807142c0b04000e00c00042c40180c070b000040701c0b800b0204560586030400c031182040c1c40d100e02c0b1700030b0102e6001408141c1c0391501089010501030940e507c04006400b08540c206030070000c8000621142209264603569000000e40b500400da9400d40381e58105070b00040d840c80d00f40201802203070000703075891458980c0310b07043d9001e1031301c8080d90341071000034040600c59680382c0c031400108204590000c9420701d400d28100e41e00c20403440d5060454280c0146564004d5400240300d42406078180d00f0315501d000c1c07060710710f145000d15880b245201500051103200000c4000280070000d01c241c600b4441c05486015068549046014080d0051000000c06144041ca28100c58001c0000ba21500c4540d2254a03030010000d001d0700030803040312088451404166100c10201900820f40c900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 518265467 1250 518264217 518264233
    0x11040626060c03060d06050907080609060702013804090c12030206061e0d03050c030a031b0f02060a09030c0203060f160504080613230709060611070b0c0a120e0f03 72
    0xa2101c524905e0b001d800f1599400c009240b071441081540090065101120741602d001c2207207503a120703000c4400304019420805445885400001c00341080400454260500f0300d005425070003121310700070080c0c1d0291710340d8542000704c0c03903030040d46024022a43c03000007044440d0401030b140a2004c2e00d11409030340000403e4411400b0b8040c01da0041c00c003102ca50b02d030700700103041c111500e01035125041050b000010348000c82c0c64056200d0003002c4905a130400c1120400c032016030305442d0804500d00035811501c006041c03041d8640c0081e4115200e13003452001c40d26113030042440c1c040101d0b1740c400b203280080c0030300000d01441150240c148481e031501d01d182c0360504174841c0e2100805044070790107a0740014502c0030091002d103007010b446840d40350920540c3d1806a00c035650300c0c503031040705500ea21702400400c0352441000002590081c3c4001040681c0c5800c070b2002040d8004200d80714a802a00402400948551954020b034404c030340d0f95170300800e10704007003000b20361050fa1418400c0d030060b12 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 518266717 1250 518265467 518265469
    0xc020316030e0315011406030921180303090306150d05010f021201170a061107021f0e0301060806060904030201090210022401051e06190809011b090311040626060c0306 74
    0x106d400e00c1c1c0c2c0056803c1510b0b620780141a502c0d060f20400300350300b080300120419503140c2c007541c00350018010320700a00b1904204081816183d2141d00c0d50280c01d0b401c0000001c12860040403011051040a406090343c4821901c5250840b140c06100011140c0c0000300504a001d005030310034050702c2c101500e10002421240d00f80e0391003255190003462140c5500e0325840440c264029100302075005018601404000d40000c1191007076104c0300740116107183c003a2030040c10305108070000c0da000c8000414040d10307028108810500000d0040341159217803000d81005031902c040740440d00c20550000d182d100c1c081c45100c51311000e00f41d0740000d512154001000300c1e9461481c915204012100e4040106030b0310f902081c0c261180c0e01004141c40c0c0c441440380035031644000e0b8070f4850401c1d28002c0043c10000c03d08602d0401d0138181181c0002d0301c0c44009d00c003280300309107050700c1401e00a00000d403070b03075440b4080885001ca58216010b5076114106145180c80c06110103540900c00329616071841c50124 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 518267967 1250 518266717 518266739
    0x60901120605100b1204150c1e02070f0308130801180f08040b0406090e01050d030813020a0b1911060601080601050d060f0b0306040b0a0305071e09110a170103080d0c020316030e031501 81
    0x2143d080d03026201c1882c027091079802840302c100039000142201140c0c0c2c0e02d908200302580d000c00340e40203400800410015020f030040c49014250002208041000d1645856148130076905500030b03910000c0401001480e086607000a100400c8907445804420f031406c09081d9164205070711280c003030341c452546100000d6101d0200d03a8006c4450011800c0d03004540041803607006150005d035506000001e00300000e08030003000e03046081d01d690fa8100008403901029844420503580140030451103c08074140d580143c0c003400380310500000c0011031640c1d651004088265650001404103c0001440241d0400b801124800c03036055070888151491a41da80d66100e080d0310400c500c200011040c001402041c21007480200144d400a1110200d958480105507101c200d10b1030200300b40c180304680700380464450030304994005440fa802c1a920b1150301c0050982c1d8803c4204600042100c02e801404c50620154018020b5440c0e0100600103000d040c905511010300407100c25150004000480e0a2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 518269217 1250 518267967 518267987
    0x2070303270303030509032b2702010302031906060c0c0b1801050307020a080d05060f0a0303081501120e060108060702010225030207180e06060901120605100b1204150c 74
    0x15182c001440e984040c82c06045002c2da00c030325010352342410302c030b48a12007035032000c0c10030244500010890714940e245000b10500d05155109143c03003072400c3e0b4902640c000e43c069a03001e08025200c4403110302d400c03102003c90303d80d90040360100301c0180304101405442c1031144003030310000305190b02d0000d04609a40c1d04410039201141044000000140344520a01403080400d42c0038402a8903a045030075480c0103020100c0301107000d81c1800c1c20a01e0646440011103040700d402d901e03260425101c000300000141540c0144506026400900307400c2c400b103d110b000303003102c0d400001e0072055050500c52424194060504c504585c014081d00c1420315a00001c00c40303d940c40c6191031075900641c0b4082e4201055980300c06414540d020303c001350b011168020600d2100400309071402651030004204c0858428002d813805000f02480d05000101260300540c0c0000b0400711800e41103980f00400320581e480b412440c1c1c0c08004071410b000070050140d40441071220039450600880d00410001040d00d160 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 518270467 1250 518269217 518269223
    0x20706030e102c1509030412120311041d07030b030d0e0a0e0906152d130509010c090e09060c0a110327030c060f130503030a020703032703 61
    0xd62402020420300d10035080e10800074a0030400f070700c100f04488180d19811950b40c1d940e00828094000b6441190110444050760428040d900003881151036a25206806804140505d5503c5c000c1c001d2488810024000500390304010410f200420b600443e003801d80980600185030070404a86c0071640c020034102000e00c030515003404200b0f0000001482d02e00c080d0300000030103030254203200b071011020440c81e100c1e01805414640c4090040140090006400b003501c0905071511553303806455407680d84a105003005107409070602110071807801301c03501a00d001105a40d0340e03201240c000e800c1840d00000f001c1c0040c104403140381120040ba140c9030f00078000c0942c888001038401c010703400307800c80002c00b440707400480e42c861140e00000e07155401120f409591034086c18107014007c7c0780025009544600190825003418940f202c0102c441e04004c2507a0050310240340f0100341920200050000300b0900e5004144c801e15508000d0001c111210180c2c402900c0c007007090303003100e030403496140c1100e034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 518271717 1250 518270467 518270471
    0x120201170127020f03091c0c05060106210507090612060506071b0305060f1b09100e0102070302040f0516051806090109030206030a0c020607020c0a090504061401080d020706030e10 79
    0x80e6005220003440303001340d004103540010040c401240070020f0031007480d943d01c920406c5101040081a180c0320b507400402006c0707a002c2c0005000007482947c4c0d100717100004007804200c041c41c07003000c0d005a03001115807034006807641c1400c01005620203280403181d02020000c102907414080481c0640c461008090711074402107800e080d940920000c0c0314021904541940d40c18100300c00c464007896010b960000c150303074104000101c0800b28000300e846220004006034030a01035060b040d220099600855030550296070000405602d49000700080520003080000da5860706032a04040d03000704000300010032500f40f00d044d403404c1038650380480c8400212181d41d02c2d0340c1000e0040320703603000540001350010008010703c14801110380100000c10801c1e0240d5007140e80f501001c81e9035142503840c03241d000c0c0001104000907801a84015001406500e003c60002d11804025801c10340a0340705e811158044140140c00680c1800510041e280300d150a0001c40b03100c110203580c0f10b0507920858180e079 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 518272967 1250 518271717 518271779
    0x11506090f090b060f07030905100806210f10020720060f030a15060c02010305010806060a030b0c0c010c0f081003150e070812090301060b0a0f080709050a1202011701 73
    0x154514054945011283c07807503654422043c60028524108c5214246c0030341000302059080c5809102d600d44240704c00341000242c80390f003200e810101031442002e6a150f01907078007240c00000e400d0003403078807400c1c0c20b440141e901e44140c50540407041d81081e07509401c2c04003540da020550786402c02c6400010b02200816143c0c4c41c1c80c4118bc00429071500c0740e14070364003500400505190403160030f1481300c2c000d0300c082200da80d841235842e450b0311342140c00c00da010f80c4441050002a1000d08440c0d08020541001030030700301110f40d40741c02c4a03038001e13101703000c1091811104007140c0e00654841d4408111000c0d241c02502c0d541e0b9900c00e080300c1ea0310800d00140c5421050305100f0080150500a062400440e85034a070160803816007a40480700143c000d500b00040403804a0600c4101c0784080112754684c080c41d050324500b1940c0800c06820001001201e50340025142e8030f40c40160003400aa0010040c600200c4c400585603282e0541001c0d40340705590010003480401d80c625842c0f074010600004044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 518274217 1250 518272967 518272969
    0xc0509040c0503031602041406030d0f020f010e060412020c060702101b080310060504352506020c010e0f01022a100c2d0212011506090f090b 62
    0x26071015003101e43c041c440454502c8130306010051180580340280c600304404407184c1011a451003089519039010b61140e040d624040740306045405c0c01040a1056405600c00c0141090950f100072021000b954050030901080c08504000d0b08050714050000f4035a0001d4040404c8040c094804083e100b44802c101e1000040d0040035142c1c0f9481c1d0104881d4003219580c904140381e42c0055030820b088204114000c17400c24003900440e41034844d409080301d810b401406946045203508000300c1e102e200050056500c034031701000b040c07000840400c51944481c005115802c0d54105a60108045501801d4030f0300007a6000101490079030f10079214103880c0194140180d00c0c1c150031755a800d6a40100c400100301c041d224032600f80707000b2401c8500122040c2e410104440c40c840c00d802c06001018514400460003506041022622600031044094040560002035410f2041c21207011103945900604120b03909801000c005420315092000d407050400c0003100340e1006500484810a80e298545203003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 518275467 1250 518274217 518274233
    0x705060627041209030b0907030318030b15030c0a0b03090c0f01050a0f033b0105061302091f0e18010605070312060302120708100225030e042f070c050904 68
    0x1550300401d2894150400304180ba548c0c0b0300d584000d800041c0704803c40798504003001011030440740c000c825220383d600d8080320f0310b80340f0f141c44141c4e0307605101d442489080c07901c44081c2880202030a00c401522132500c40101c80c00c100c100c890891040740809425021a03070801c040c0c071440c1c000f603d0482d114001aa4041c0d00924201c150705428005143d000c1040ba03c2440501c3c80f503e80c11108a41d0060051001d01c0c26104140d4070198071800030030814148001c1036000c0d01c0a800024990400402c2c180540320700103042103074800c0081ca04e40c0741d0b03070100e040c84d0f0700c1c47c045500c4990010f4960f601d8454000c2241c02030000041c1004600031866291036030503040200a5a0002c000d6041c0312085806a40c3e140140c2c45a00510301800c048841001c0c003500c2545c000f001c500da0042005a4039041503259400c9101045042c01030480ca180f4054030745200d00f901e600c40900e07003034400e48007105049802e541c01802d0111001820850040013800710038080b007c42d00c0694034030b4940c2d1103c2c070306408 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 518276717 1250 518275467 518275469
    0x3070f1707090510060215010b0313080708030f1608070e0f030a05120c100606020c0d0305280e0d1e080c03070606091a01090b1c020705060627041209 66
    0x940d50508044c42905240180c400d801ca4800e07400f1600c81c81042014106019000d12590306000e0f018000280500da0548240c1c3d030480c410285d031403414445a6400c3e06a4100b55059025150701c071007000004400520080c15515032030401840e2454002e6005081d00061003010b03000d0442c541e10708201751010040305040f158804141c400445000c400c1c48140d4021407100d011900c00c91801c3c0e2890400ca114400640380329a0282065131480301c18401c2c188a0f09000b00c0c100700c01040070800842c51104941600f03400c00c0150355420101c4400200f0305641040c0b10b40c490480980d0300400035405074407034004282c1100e440c40b0344082504141c04a4002c061401c0010300001841030100502a4000000e888540004101c0e4410104209005414224106012a0215000344082040301000c0e000c07251443c03150040086003010b114040c0d8020200441d01e42c2d101c0018803010b80740c0182d03a825202100c4d201e40c1c10107165a040c1d101140c2020740040c0c446500b140082c0c8405110341c500ea0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 518277967 1250 518276717 518276729
    0xc05010e150d0f05131106030c16140106081203160207050312040915380d09060506011106040609060b09011d012c0c0706050c03070e03070f1707 64
    0x26100e8202c1c0c480c10700607000c00d14148084a14180c0041e11030a4080c444d201c1c02034201901c2c1c00b11194650501035a130f03101900b84004a0410303c4001c00b400313000d0304040345261080c02c00c6003203281c1d28a18107080d00da10381c00c680c0064100081f8603c541c050706040c0c0380d1081000d60300c0510000030300d1042c1e080070115044260180121011a2464184840208100c4d54845410044032044c881e080000c2103041c0181d0310a188403540c840889400d80500116880312080b007184140421340c90072405070301006004612540311141c150510a071031040590042081c2441c54480742c09221098503010000c100a0895940e1030082c024041e02d035101000e015405406c1c84038550b10b0758000d0080b401025050000000071b00004158869996481c0c00d64100038200304982400c9018003031174441d0b00900880c580c0100344210b01c0418524090b49014103207001071203907a4281101c00030410811110814040e600042c0c0400201c4240310102040711540c04400000c2c42152001c1420270b40c0e298422 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 518279217 1250 518277967 518278009
    0xc1e150c0c060b0a030515040c05030a0b0a020a020f0f0a0317100b3f090d0509041e0c3c030c03090219180e0d080720060106090803070c05010e 63
    0x5162100240c7c42424040d03030143c0c4000c02040d1391401050b40d40c1c514450b009000459460119641c07040715000f8207901e18081c01900e01003204a02c1c101d1030306038900819404e41c1e00c04c581c120145500300a0301c019000000318070b82234a10b041d2203000d82400c0503102d50141e0200c002244810308440d204007180081f000ea095003082000544405003407179104500c111070140307990100f6080a00007a000d03000c47c1082e110181085542c82c200710042c501103002c40f200d0702c08062070b510110042d02c20a440d030038441e00d0311401c8100c0007202c02200030f220b00014603842d0000b0f1541c101440610766503038811959180108162603030050840241402410081d0003c808403003c0c882c100901c4074010a85081c40b180c007148003003822860055400300c0d844c19a00340c020805203500c5903c82c80703520764880380c2c070308000024800791a5128104910030301c80481c01e400840040c010258000407000041c002e050003107041100c45d440e00380e002249446403906001c0c88000420081c1c5811500d0040c00540103030b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 518280467 1250 518279217 518279233
    0xf0d0b19020f0a0f02010203060d060507030603060e070f08150f34120902130c1b110310020403030e010c02040e010f05060f06030403080114010c1e150c0c060b0a0305 73
    0x141003a2a00f1584201010401c4c00c4111407000d441442500d2003407200400308803140c0c8107925a07400810740070700901c0425031234800100100c0c03030314020010704240d13000042c41450726144a50034042c0340b9402900d256004450311148120741d01405d560480c200354003c0c442600c444651084080d0b03068001c0040c3c003000d404007500c8030750802070201d9091503a05d4800b03411200c1c44150f8200c034851032000307510136000700c0078003014049540440b0034050a81170021030a000c2000052054200c15400c8a805421104403451800d06000c111117007030340c0320300179401c0c24210794001d00600c4090003564104154030b4108000d641e11600f101c900403c044000b004a0000c0c0c655140c050038045540600840741c2c59680c03012404d19104403407055406546180ba05c2c0d003001a881c138200c4000482d00d0420010024403000b040813505024101c034500505082484400e2500b090101442803188100610703094040b41181e4100d5440b0505540c091000214000d080000070ba41034507603000500b0324460125 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 518281717 1250 518280467 518280487
    0x10512060d0b090f010c0212072d2316151701150e0a0b120a0204091404050c0f01020d110307050102040801061a18060c1e030a09050f0d0b1902 63
    0x100c1c1110b41304180000d110320a072540d000d03030b51071281c0c07450302c50008010803007038010035010021184e1070301d0214614540401900704000254029031410780b80200444040a244d10b40c1c0700e800062048580054104841501146442e4515611800c0030040a00780c2ca046120311410841040f20b0410324201041d503180c1c101140c1454801e2101c2c000f10f00348a021102c140b802400100458007003a074410702d0080c0782e21121217011006012020019020b11012a000c1c6080c0a24140e641c1c2c000400c005918107410031034600240c5401150254051448803001750742d000c101d0901d8440c207400d002e41d030040d040740326519600c5061030250955101080101c0d6901d019000707007040740c01000b1318803410b0020725801001d5201303240310320340421112108070f005410120041c284995000d416a0322205500c0104114640404800b0f0b00c184c100184240b03140d40c0100c41c0401414050750300d50780d03c1d503402021880e941491800a05030340d4190000500d03031100f0089043c88400d800b80d065454840300c213 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 518282967 1250 518281717 518281723
    0x1204030807030b09010e04060b01020f010c020a0b280b0d14010606111b01030b0418030801061107060203030604051807030321140403030e03040b18130902010512060d0b09 75
    0x550240c000900f803000c50308482c80c01d100b809050b03c501800442c59900c80d40c0d201002407401c0c4018605500899444000707a542c20f0cc03074071100080c0b54004e0b00d8030b02c0705498001c501c4c5038002c0070881c4140e101c007860542803d0003a00d56001102080002402c101000005825900a4980285520250564440340503410b400c04812501291204200c0719400312603161621020b010420080c0c410203007010683d8801e40282c103140c0c40240c80040c2c10746120328074000b050285003046d408145e15000400c800c90340640401d0a020301720000c3c04185080c190020340f2440040c0803d4403498440021410003040410036000248503541121300749a6689009040343d00c50003048000c61f0741641c581c0762520058021281c081065125900c5540e40340d030350590040242441e00e41c1103101c18000407650300044801030040c1c06124007464401d5002e801000340c4040030750740c1e01800606002842c40143d0700a01170740c500e0021000d103c1041c0d9221301c0400d0307400300d69080203005030450f041801f08200000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 518284217 1250 518282967 518282971
    0x1612140d0f06050105031e06010e060304030f11010204080a3c0308090601050a030822080a210905090a0f0911030d0908071205010b041506080108160b0f12040308 71
    0x15014424680d940c0015176480c002200d515041c548241e00c9111441c43c6da1040590010050404800568040020030443d0704111411070110700c100400c0d4400980200b400c00041c40360800962a02d81800c3c0540e0304d6004030314000f01208a1049140703160280f12300000c1d80440884550901400d50140b624050901044142c1c0880d41507404610611404501a03040e2680078005107000d51542c1c2d04c07030740e083d8440074405400700380c40210612090804004840208140c200401c2d41d00c8050030f1584201105007115100e021001106103089038000311a1001c03107104942c501090b5980014000c0030f04044454100c40d02d00d8010600204201c80f15542001041503003143d4100500001c01d440c0e004039801602c0e001c2c2e005003800c00401032030a100b001414400d000106401000d103020805807241030020100042c003411040c80000c1d8010003482c011b0a14000030710070280f006078108a0008076001e0040581000104500720440101c02c4a1041110641400c014030302810300600c45001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 518285467 1250 518284217 518284241
    0xc030501031a09071a220815090606060a02190818180c1305030109080405010f0f0806101103070f02091005031203040515100e06061612140d 62
    0x116000340e841028005034a1248841c1e1000b080d8290410398009000080c061742954400410440401c2c4500e85075420b207414800046244200d41c00c0a688038100000c0c803a9484c8120714035001c0018400f000201e181c1c0101c0e05407001a990812440128103240c03041700003102425020b0075400400c072210000784075010300c801490003c84480400c201d0302c142040700c0700d01c140440001185013a441d0000a2440b040081c4100a0381a51480800d0079556031240a03200500041000c000c06d50704610741c24101116440e040803160000788002d86031036000ba00072030080d44c2c1e480407481150b0194000c2031084244404494a0f00c02c00d151040e40c400340c5480c101d0103100500c0108103042c0c0c00031104016180024041c08040c01c144002e25201e8000600c162801c0c440c04408010400c0c24600301800340140e642e40300b40b20760600e000d074114008090890750240700100315010240003014154105541c1c00000c41401c0501e01c18100c840b07000c401c2d166414407030001041c40a102c0c107640720b1030041c12 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 518286717 1250 518285467 518285483
    0xc02160602030c1c17150319110a051c020303250c0801020a0c1709100f0305070903080715062c090c0d02090702070308070605010321051b0106090c03050103 69
    0x65004c00030140640c3c1d20114101003103002c8034070312886600015041e400040c501d440702210040200103460050914482d1b600e129400207540240500d0381c2c0c0f0074011040a8940003200c40c034003404214504100000b1540004d00c0c40245000c560b020b0040b100d4030304418154122014540750000c040302408241281c0b05076404600080000045c000d4800414864442c15110440e50721132030700082500b22a4806030504100d0340315555078452591040c00100d03502c0480701000b5150240803280041c1c4400309118000e0b1042002410040403600d8659200d91201e074030f81900081d200251003960004080100b0411043d000500040f841e5903040c2103120030748401361202d81d40e60f600d425140303c1c240c0c0c000508000c0d4038094189107042c00d400c04507a1048a076910703500c0e1903040040d000320400315211601e03030700100706024048140d19602c8040321000720310030000b00c0c0050641c2c03240b00c03002840e041d075111048959560a52002e030091072000410b201542566000400a29090104462980b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 518287967 1250 518286717 518286733
    0x50318090702010c1b050f01020301060302130b030f04060b0f030a1104061d01052b030507062d0f0b060c0709050c0a0e040213031e02091302130c02160602030c 70
    0xb4414060309075249842c2c1c4a50703004072603880078030b5020140194180c8451160241d0f5068500c024801035009040303035507005807600350042843c044429198030060003003c0a1081c803004034911803642c1d401562081c0009120441607010841c508008010154180222102071003800803100c000901ca4000311020044c03e9102d01581204807480c000354a8045010b0700144482d0070300d0000b100215840000822040c0760f9509180028030000d40214001a000701b601410407a075400b41160940c0c1142030340c400381c00e0100c1c0d0070405c2d510034003082944a88403c1e1001548581e0762181288200103448246d03101c201040c42c41d91601d50784980f0044602d000c0002c0c5454095a003900d0707100003aa5112900c0700f0b0074100300030107034200003118110640c440500000003510305c8410301d12810918104102070328640100b1811260050403440e810400c04040401a500c4080c124070b084403d680000310303401c652108034509050462901c8413952000d00c041901e0742c00201405202c99540d0498001c0d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 518289217 1250 518287967 518287981
    0xc030d0c030806090c04030b1305010615021f06180209030f01050108031603020c060715050c03070c170d02070f120f050d0f0e1f0506060702150f0705031809 69
    0x5038868040103800501e4010104407585000307403138980c12034041210142000d440b51168503045c18103031021000c0c50503001906080000c2030103020010304403a081d41c4105803051074041d484024420354050f0706034031040c6000c070726802540494050001d45041204054150715440000e40c0980c101c1403083c403502030780808249050090905076080540914108584451a4054511058811001e501071080c058015860f00c8014200082c09696030056000a01e11001c0480f400035220b2074070020100100402c01e608040c01c03201c0b0541c00b0140c0c5181c5480080740320380c0d0f4003030300003908652400000c14000303104114a0400c1d03000e000e02180380f11880140c1c410795010b050710340f550f404141c060040c40c143c566264040d06601e45444c50102d509207064040c103050816900800002c00304d201d00344210070016105e0203620820980314145002200d4000a041084e0750384040c58500c0c000880741040e87c0c60300203440300d056008003103c0d100c40746041c03502c0f00d01e500f501529000f440000300080700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 518290467 1250 518289217 518289227
    0x10150f0305100305030a08090c090f0109140f06010f020a1a0f010807051c1112030307030b0a1202040507051e0904110703080411061303050606031c0e040c1704050c030d 74
    0x2c0f02e078032500551078118100025195400001d203403400a0040094480e21a121005107900c41d1005ca0b46040b01c80d81401d6a010444081680442d080040b01e8104410f0401c60145c0070f41061090a2910303040100f000c1c1249094841d03540240320110072051804e0580f624010103021342e14080c0c4a25060fa2103060b0781c2d50b80c81e8a841070a5200d40d1020500c41c480ca100a800780185004032079451030095180d010032400000c841e44c41d092540b0001c1007020f280d906d032240b6161003d0440f09811483d1500c0500304010380f0212000c1e108a41c0e50707000c110050b004504490035034511564000a00b041103102c601c480d042a0110703070050341004004505a00c1e803504541190381e1684486625031169114034940103002d0314910b8019004103c041c506590a0402c41c00451084004098900d80501818100210392440c03901507040d0880d01d401250f001034640800385005c1c3d400007120804c16408a42c8082d008060328442c940301c6050005012000ca85540705606c254102c480410400c041158 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 518291717 1250 518290467 518290469
    0x20070b0f03090f030f0906090a0b0c1b030d020304033309030212040506030a0c110a05010e0d170a151a09090601050f07030c02040b09070c0b090307120810150f030510 73
    0x50f0300d617000c0013a03402902d007600150062410103491144015100e40d0154100c2e4420300101c4526808a9182e042d60703410b10140340705400094002d030070b404c81d00d4000650f890185000c0180011031010210f000549a0300304a01a20444e25031800980c8800703c0444c0100a40302c07042d001801101d401c1c2032520f03444400c840c00c881d00901140c0c6950344410b140e1005041c0e8840c13180401156003e0303550202c0c020016411014011000018200302801e8003928004491401109000c0c0170501445030b000b01e1104181d01510407000401d03070601032004181100026080740c240c2800ca060000e20203d2283e01411843c54291340d90343d41034503450b00544041c060120703006075501040165000091182c15402c0e5001e1020b4000f19000d0000d0b4001416040e049a0600008009140c007d0500021018080e00140d940c4065840d1044079104c03080409401031070001400041c0740410507a8615081d00d0380201700d4101c940351503940c8004020f00860421410320000b0b400c200c04540c1d504003800c103603c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 518292967 1250 518291717 518291737
    0x4050f01030303110a081617010f14030c030c0d210c050c0406032006070803090c0108010902030708041103100e01020a0e03010605030606150708070308061c0320070b0f03090f03 78
    0xc4095a0382904100c40308030080e82801040640306c11284805074a0810328040c1c94403022b07084056003440c441c911092221001e0a10980c403240c43d843c41c1c0d803804a14045224401d0325400200001c81c01c2540d1400c440c07070203e8543d5200015100d001c294450411910140701e44283c91040c4c800b9000c1006480383c2e80800f030001c1840c02c922002062100510341c88851340030b040c46060420680b14070240d0340045071414040e4100719155941c41d030380949000c1c05800074400860560806004c001c0012600034401030004006d0013000001d69401c0010854589003001e0a0100c0802c2420749400303500140003a101140003950351980e286410f004030300c140d41000d00184a00c0c0d0b9908104006030350027000d145584101000028080341890004140c07440c020348070030540342011000d1000310b054408040007807800e00080c840000f80d01c14030078402140b90424a20280780c4c1180810b04114071940055290540018000c000c450040055480b40c80c4407000d035000404050416a103d10a681c0b00c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 518294217 1250 518292967 518292977
    0x1204140f01022e060b04030c0e010501080c040e060f0301020d0e0622060c0509060c0a0b1e1503030d02040e01050a0f0b04090e0a06050f1f05010906080604090204050f01030303110a 79
    0x1c3e0301240348900058081d00103400b0a4140c0d0344c0d6804801c1c2ea000703803c140c03460500300c0350510403082d20810090041200303207043c0791b10349031058060f1505e000d1800f4000707011600c3d0010482d1941d44104034a5840b0b4024001c544d0744c03400d4084c00300108003940c0310300c140d07000316000500960314180540d46c890302540540c80d03400e001d80c0c0c0c034176004001c00126141030190900085c034003074503140c02500050021030020305040b450781c1088520050002c1c0061050524203007040c04898075524400d400c000c1d0800030092842c040800681507020300041440c21a2000c40e00007036010500300320a049610640d1040f04254940f41e808082001c54000c0c1c02c9043c50820040081d526903910615030450100c041d141c0d20300c43c0c1e503100400c0d111309030b234240d44188030300c81032160030701c0301115a0b010300c00444444250a8035210010300408107a103c0c54003488010000280c6a032943d070000600c095009004101d145040d40640707c02c8102800300fa40068038103002d441400801a0031550502d04684031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 518295467 1250 518294217 518294263
    0x60d0207060b152203050f10050108010b010c02040b0a0504110a140702060313031e0503090f0c1f090305100204061b170702180a0e0c0a0f0e04051204140f0102 70
    0x10407813214030840c0e074070f5121911501e00040800c40c20301007580703502c0c4010040e01d194032800081c0000c2e03a00680250f0200d0340741a040d9086a070700804a441a1a410f441c0810944003400010b00d5640041d80301e240c01905200382c0c262401c80c180010040c2411941f1128145d54410b2032018180c0a80702c0c00a40101c020000f042c26515005042d8844602c207152007118103e007403642064030010f03004544007281002c01844041002800385c000040304040003000780c2c0c1c10160005c0c0069241c1050b1074490a0710802e010f0b042845400c00d40c024640000c00c880070300c00701542c2d6030300940c07240c4104000a03406c3c8104141350003d01e0403000d071040d0492003900e00c887c1c48800c40002580714110807030380290f1b0008201c103100600c44526105010400c400036200c1c41c400721a508000f40d44040030710070160300c1000d0041d079965540c800c09585038900f08501039075441c41c0070383c41c04158515a00d02c04a01280c0040c0703603000901a00510641515203a042c58914001a039031624030010180e00150324002c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 518296717 1250 518295467 518295487
    0x70603020d141b03090715020309010806060c070b09030a0503070b060118030c09051306140f060604241407060203010501030612020d0308151206040209090c031911060d0207060b15 79
    0x655040a0f07285c003541e110550718544500365042c42600780d00540c00114403404550380011840c0d501c824280e948625007200c01481c2a156a468001c410b41c01c0700124150b92942c4081194955456110040b01e6844842d41002003411200b1034441d4001050310f1644403c803c0d007004000704603a07120701600d00c00741c2403422020152100801e8400d000c0e003c000403801040282c042d01003201c0140003a444e5505104d803040785040002803815002d00010001005556100542041c99002a00d0740425484880c042100d514082c221501c2c03c0c3d810108174103060004960003541258400d880c2004041e0347d8518a012803001010041d40c006041c0741c007400861300030a906a4840a0350003540c15614815000a005028240c445030065210000b04400c5060203008107403c842a8001030541c580c0d12000683e4800f0001d0584080c4050070355610200805000310745500000100f4035901ca08040000030020b40100c60309448060800c00170b482c16043c01c0e02c0150001c5900f12031103142a240030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 518297967 1250 518296717 518296771
    0x6090608010e032d030f10060807050d2f03150a03030914011710051207050d2307090911090f060402090a1206020c060708160f11070603020d14 63
    0x9113906000c4001c614400000740c0004c004502c2900345240840c3d040c02d14200e80440d50b01030390080c4042c01318900901c40e869803c482a0b41440c150720001081114070000f0a01e4040c0851460002c40e401050048886007112070245204603500055080400403000401c074000400c6d10018002c6105404148840e84009000c0800320350b06042c0660010101251440396100440d200860075100c24000d00c138a19002101d840f005000c4030044c544a802e0100040704a000b0040040c01040310111541030300510344c0d00100b29120007002d0b141500d03034850100018182c000001c4415480c0b40c150a001450909041c50040c1c08042d1a481c142d550038040c08001d500c00506664000c01b041000500d9940800d0b142100910030f40000d41c56452002c0c0140c0703440400740c03551081c0b2100d07100300180c52411550b0008040b0003440c003090340500c000c005070383e045c0810720860b00601449101044543d00b64005041001003110f041107060074012038040e4419040d1a40035401e124903030780c202c0c170030002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 518299217 1250 518297967 518298007
    0x40e070e03100509210901052101080610090203070806150702060705010c0908070b03130809040e0a031103040506090d030e0d030c17070807020405180f0106090608010e03 75
    0x14140042a8405400068907142c4030b552001d034855107403c10042c2200c4207108480c00310300c01142d000e4000351588031804c92400385061044c1004800b003002d54000250083c0c00300c4404403032015100c1941c58212058480d201103624182079840d40500160100691086074820035856442d052070740c03540020030160f902d401e107a030450f98409105a034017594880c0001d000d40d9206d4800000c615850000c060700d804071b207601103481a00030440800c2161200c8046070f502c504c0c0071810300715040d40f51401040c0c034081d402117150072074901a0303640c2c1103100c0060b030200b40c540aa1500a4200703051490140c2d244100c1c001c07603810040c00c2c031276800389042036444915014424200f01145203d084003160501d0480c150a90000b5a859070740750034002004017803000c03000e01c43d030030902d000e450792a1003600e881010f90090045603500006403011079041c3c0e07a035900d01c01e40425168107101c551000c2d4003900c1107020b90411940742480002d4910f40501c500040401c110010318201002114022203c000d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 518300467 1250 518299217 518299231
    0x30a080402210615030706051c09080a02010c020111180111070801050c040f1a0a3b03102a03021207050c01290d031202030c0316020303040305040e 65
    0x11100032602401810031042c02d14901050051400345090260400c1c4d21804010241c020307048440c0138080298800126100c66613039502d0072512480e03007008503008001145016200c548041110f8100c240d041d0003e481c02c0510368020b200c0c0d924007400c0c0f61001d110b0b5894407124031540c81200712095000c3d42505101c104c00300306541c1526070f01c216850039580101c0d0840c48400300041c043c4460117000c1054005045032401c03441a120907110b10081500c40c1c0085201445249803220100115800580c4440400301c2c64016400da0490052943c501c1c0c01c840151090107446583d4002160f01e01c901001214504c410b41c1c14102c00c801c040034110f54480050080540800285024841d10b410590140e502951001c1c2e0f154040c1344645e003164072a809008404250941c031141c444107002031070b10341c00001c881c00c0351a00380b90718050300c540f4041061220094004000c0040684124020f103100e102207488000310458105005c0b0b85921084030b000303002c580240700c1070205d82c0d06141210b902c40b003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 518301717 1250 518300467 518300479
    0x7030e0d030c17070f320904090218100905090717160f030b09010e0705330c06010b0301080604030c060b060313031e050906090f0621010512030a080402 67
    0x41c00c81c40150b03c49003207818101003800354074140303035156004a43c02002007050080f881080c01401c98a402640621080002240007240210080d502d40e1b2000d900c03641d008280000b048401148180d0b28541250500c2e0003111400d000154100a03002d802c1c421103005d03019180e120f050545031405034401040800043c40360340e4210103000011200039018020305442000414a5031038940c03084640180320300341c0f0344d05040b07154400500015400301503810844050030740002c98080c402da440004013100c20351194050403004100001c6000704015030ba500265212a038a0f0b0081e00762a00c000c0c0320392a00b81d4841c90028021074070520600714403522072903012035400f4032080065030640054860f41c04104641900038105608140d0195010030030b02e2002402d80040c03000907045008800105000718030019401c08950b50b000000b01440e20000c140da900e41c0541c4041c00e205440c035400b9480705104e1350300080f545141c0050104d40200903107004600d40b81d4209011aa00710380a40201d801c86 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 518302967 1250 518301717 518301737
    0x50d0f020a0803120a0b22020c030a081602030310090906020d05280507121109030a1a010509040206070f030c0215270d1b15031407030e0d030c 63
    0x1e07503012003180003421918021610b40750414400001ca120140c080340300c007440c051000c801515039003940b01312813544480ea45081c1142e80301041c040d110b11215404903010010780b0400c95034004841a000e41d0b580d4199030244500b2860581c2c0d60720080c1d82003040107441541c104405c802d16080084540e11030003000d0b0800e9500740050041d01c1c4252280808101c505034680005102010303030301c0480b40b86860600c12802d03c00e402400041d8080024410f654a4880c01e410300581d100480301540c60250407544039a02d6801c0400c500441030381c80180d0200300000004040c90182d141034000c42c1c0061003240380900950b076aa440c180c0d44038084090041d60380012016a8070b19044146061100002c6561024141c480100c1e00e08c0043d6845051620410060842e4550942c0d09500710b500c5400751084030002a00700441c00c00f582d00560307441811428022010341c0c1a0001c0e44004589260350340c4c02c1c3c40e002d00540a980c06254001a0340e400707007a05040f2a842500414642401404c107a00300c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 518304217 1250 518302967 518302969
    0x20a09170a02060a050a08160806371707150e0d020a031113060e160908030408010c200c01031a0a0b0705070e0f040f1a0f060301050702010213050d0f02 67
    0x244c01007940700d408100c0100724401119081100103034040d12065020745081a0b000d405400c540010f1700140c081c040110404106c038810141f07020710380d07170080010b02e0341001004d035003400724929001e649100c01c0c0c0792050b41d22050000070328406031146490084507202040e482211444480389015511060104800c0b01688900c4100000340d4010f5542002c105810301c00e000d5059900d4103031000b0117241080400014001440194010000541380b10b00541c11001c1100e60200381c0d042040f05000c00540002c0c00300f415400b5514003c041e071504540303082280801030814008102002840c0c0000b0200b440940c465800940f1001000f221801000709843c04691078405030703001641105c0000403144248a8100250002055105a528428035001051880c501790160000300071404502104081000300e04c02c03541b110380c801e100c4110a152420404000207015900b0307c0c000d520704008518514418000c540408110700410384010303190409102d01401e2941d0300b038403107859148403d001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 518305467 1250 518304217 518304229
    0x1e1e0c060c020105010305010c020f12030a060308030106021b0f03060406090507120c14030a0305070b0a06031e020117010b040e190e03030703062114010f060f06090504020a09170a02 80
    0x69000c0d0342d000041135070540c90020b00b140d0300c0c50f110409542c0314407480c280030b84000816901c03105241c4035464898890032604000740c000354000a025000100000c100340754009001c0c040009064900780a0711300c19000c2c4110f1880d04204550180c205c1400200861078507044072105a200354102c2c0d64940d0380e01e00038081c2000c08801140c00d1404020200030b980e03001400000301c950b08030080c040349582560701030094412600d00a00141e1140005459840c50340c1c4800001d5411000018840c3c0d100c40307003404c00c0c034000c0d042240031800c00c2030407650440800034001c3c103171004134034581d24050400070100003500e001440c240d5080082c1500c815000303481d0203503440014540000b140ca908025101400b130b9543c0d90000741455000304c00c04203440342c0c805202d400c001d410990000710a1814040035014150101c0710301c0009040182c006802d80c4201d200c04101c44444d550301d40896142c0302080b003a8800c181c82600020b20b03004040c8040450b035100484070f89082011608000c40c26404a44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 518306717 1250 518305467 518305481
    0x20c0a0209150102060115051c0e0d210606120b1903081b0604261e0309070503060402030303280f06150c050d0509040b04020313031e1e0c06 62
    0x24002c1a4039450526540c04101290142c43c05960019500301a5000107105000d800c0c12100300c4802c1400810039940030394860400c40740c134030040c0c0d400001e41210140a6291138001180f60000c045070401c400802449540705640543d902c010511040c0c52801010301120002250b10042000040e0007050020315040c006622a828070ba8445000c440b03488407400804180c11140d410070410007001695610182d041c5482d8400c011152003805403071b070307411805500a42207013044000d442c8403011700e040018510650f480e00483c7c80c410f4585091503114002924000c2d05a4800c0c4045080100d60700c070040700c41d4520111a044410241c00c0404c2500c000c419501c0c04c0503660502445a9001a0200d25450409043c1004d801f8402d40e1159564141909040c00b00078000c51058180d03a02e68204c1000c80b44010429901c80c180707102138001141112000b140410f55841c110b60420700003408c160150078040d2a0052074010300b40304400a0724850100c0000c20600700d2980c800901b82c0e10500d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 518307967 1250 518306717 518306731
    0x1031502091e09010e011809150f0e0c0604060c06020c1c03020304170702030615150a0e040c14250606030f050706110c15041521020901050409020c0a0209 68
    0x1114090061060020111040c0c2124245d80d0341980180300030075818960803102846480005100022814104480100e00001072207041c02c01c0070740c9480e034501b078100043d10b541c82030076a0700c2280c001c0c6c10041240700714846c100202d407030380403264013003071a65000d13180d490a00d074140da92500700407a040f42c850f40003901c0c080120740d020041c401400020301c28880d205002042e01460140b0a400199846070300501144660999244455458070744008a0240c0511040c00588503140300202620070f50320503071a00d00a500d0880f00407071145c42104032a481020700300000f0f10307007416041c4901c103800600c441d00c2c9843d841124404000303400d0744100d00095001d898400c815090300e1130860f05001282c0d00c00410842406911400c3d0080855041d58140040355060090380e4441c044030010f00440e0310180145840c0e28881040c241c10509920035401070720f1040301c0780381c02c2140c5503089001d04900c1e5800160103200c20301c0000000d078010040200500708503144206030303900142c1800001c40f808 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 518309217 1250 518307967 518308009
    0x9021b150108010e010c0519090503031b01050609060a0e1302090109020a030b0405070801060f020705030d020106050307060f080604020a12050103031110061d10092912060103150209 80
    0x100302882c803e00c110403140241c54024071040c000307038100410318002c01c400c0c504142200360000101501401c0d2600c01010040c050f80c0c1c450300b14001750b84d020320405c00c5a580070b5013094001011032030000c41d0188910001440940c0c80c60034100ba00c604000020721020560361051907071405655500d8103580204142140965640300c09074000f02645c8142d002217000d1400d08060006843d007210403103054510900d8220f20791044040304030b29000e0340b544001d800d40101109a1562541904040282e500035411126000d95511044800d02500b82c1c05000044800c80070403500d140c20340040c01d1811441c039001004041a1039858125a02030f44120040707071034402080c180c56818842c16040804101c400c1080b5464540210008032040c041106140000c3c000189a84a5901303582c0240820520400c2215084200642c040480003003115443e070402d10140014030300303000040440d800403000341079984d185a03a5805c4c0041284c0000e803405809000b0b40e04143c403501c4410000c941d03072000c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 518310467 1250 518309217 518309219
    0x20c10020408160b07020d14030706020d150b03010b3a05090c0a0b040302040b011809061410050a080405010f110d0509010516050c0a0c0308071a010f09021b1501 71
    0x83c1998510141e200502d445000c0c458030700980d9480e004800001c4d000201101c0c080e01c5243c0140c15445a4040101020300c08214440d50f51000d0f8881240b0303122540c511020a0749868100c01030340001d10962280000401ca01c1c40d0b01192030104a151101000380701c000200c101c40c3d05400006584541c0c15505d60f01d008101d90072400300401c084240301618081c1e1081c1c201401d41816110307a01019010700c0d22110f4440c902e03449120703040480640205e540b80b40c65100c0452401404652140c804035120760114191580380039060301c4540260784d222103140c8807a601080d900058005d01c1500e95550b2280714003180e04d954010303110040410101a0741e5011b00c002808102e0314040c02c103a03201c1c3c1c540420003103814114015800540c0003410041d407190505a2624070741503941c03000414824140500000304101c1e1070180424070b00caa000309161160009070103031007000901c504a050380000a0401100609900030401800440303070340481400803024542c60002080e201702440040c100c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 518311717 1250 518310467 518310493
    0xb030c0612071d030712110a170f12040620030c010c02010e030406020303040f0807051b0103241208120f070f020a02010e0402030a02160501020913060e0109020c10020408 75
    0x1074000040e4444840f003502140c849008250744101c41d01030320300c04421050710507050000b00c0c0c0068240c8640240b5840046889000d446032020701510500e000c1e110b00d1552203018032000c1804040b02d000342248900b040c0c64101c0071522940d083c48486a0300d2980310301ea5001440900c004c14540c207221002003800f0110f00c0d4002c1c00c490b000b032400c2c0741541041c04180220796010045030b80007900152850051245400c00820358451080d00600d80d00c212030b403050900c088100c40c0518040262070810519480d1f041e501e01c41c08082c1200078900540d01001d01c014062620440384140c003800400c0d0410900030688500c400065400029215006081000941c2d03c0122252120220f20141480110a80c0041c0000503c525100e10840d0088001402c059040d4141d40390700b0010001b0042d44040c9040141c003d612600702c240c0199104a56101d9170b02c0b49003c0c0300100c54920040381050303840c01031b03642c00030340020107c02d02501581140d03440340500c3e400600003030203016001c1e04102101034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 518312967 1250 518311717 518311727
    0x2101050c1b0a05100e0f0708011a0f130f094805040b060f18010e040606090b03090c0d1217060d030e01111005060405010b07150b030c061207 62
    0x41d0020300c5684428103007000940049910b200c07a14900700040313100c00141e240b0741d0400070480c801c1581c5200b0389200103401801500f00301d030a04124072100c1071801301402889aa0700110780000d410000c44007804e500100250f0140c3c0541048000c002480400e80e540e15154000621941100030784907141d2218a00c90002d0391250344170740721240e01d01160108241f40745904030f4072500c1d21071030350307168151456107982003203407140b9880e100d5040e664182c02d2274101100c01d80203803031800901442d000e210325007000e00c90841a00d841d07889200100340351103d500311507800100745040c5401100924202500d9004d00c0324051886401000301c7c0301c00300c80c3c0040842c02511001e008021410040c071007a86c03100f0034010280c039058500030b07070845040710040c0d03484911a800c4600e070b40f180401e11080d00e02c40d68009405001d04a60600ca2644d8074180070341d25014074800600001d503030010149828509074090b100b0900b01a054629004002002950300c0c1c12001030803c40c1540d013410040030903801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 518314217 1250 518312967 518313007
    0x1320c03130e160311040e07030f05061512060a08030c0f010e07120b25050a030b0603010308041e080601061e020609070b0a02070902040f080d020d08062101050c 71
    0x209102c88882c0340100d0f400d03400c900c41480700e40030326550340140b511a902080440303014080404d03221741141070040004000b40741c1c501c07440c0380103440c05010a40c5484c142d1055400440c0c10107100b42000032800c0d504c200c44002a00a540c04040403800203070003c021b202601e075812050029180e603c2c041c03003649080da0340c0302c245010241c021000c14440c0c00366111603511041d0300511402c0780c5548040f40d0f1002e0030079403464041200880601440c41c035274410010300044d141643d081c41420214410b1007041d001c203010040c010303081403000b80030356003200c5400e84404590200c4440c1203a5213101d5182800000c0e08442c00103055000b404000c0340340381c01e25400346000c51000301292b14040c0700030342d120b1656000e242e010400c00a00703c40300e03d100700418000380c01c546000b15510313582d449079804c03003050302c2c480c26a65006980840c2640c03030001c07841000c0005a6203542d055960358030204103262060550074a003d42d10b0741008402c087c42485185d100380c07002401207540700c9154071102015401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 518315467 1250 518314217 518314229
    0x20d021e07021c020a09091a09330106081e090c01110312150103020918060901080312010501201005060f03010b1e1f0201140a02070201320c0313 64
    0x640c0c410016105c1c00c00410848840e0600050075110a00d41940c01c4268281030061421168080c4070300e0100108020701c080410602c13001e4050f014105403100748283d80b485150101c42c11004210039801100210f504c95404031b04226200303283d401c0303106501c900359031f040c1460f400b100740324401e942c1160401c0c40d00c0b0b007054010740c01c21481c4001c03142510b00040c2076800040750540000210f9019405032814110001c1801c440f42c6054a41c0060350340713080706d410b441990304500019101c800481180c100d07500550030740c0c00300e80c01c1c00010345408181c02404080180742415581510405202540d514a00000d0200d01800c1110401142d00001c40e0018805d0349003606001c070075541c20401440784180154013041c1c001540c0006a42e01f4210145002044544044408040e5066210408407121540d050803a80ca4200141c0308078002c0704002804691107446800002d100614070b02495901c0020b1514103e1441c0d541c54071581040c03144003125480402e5100d000f0211180c044e020b001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 518316717 1250 518315467 518315509
    0x60212041401120b03191101081b0906190c0501110a050403060915092307050901170f010204060507060e03030c070f3305130506010603020d021e0702 66
    0x1c10704604805450303004540505000e0000000d80030360949411540700c2d083e000b41500d0a1140390007044000e43c203595000c54941e1000060f5580c1503006000c00c0c1d00580f4190b0780f0002440b802c1c1c0d01c04100d90720200c040d95010205108408112007602443e000c03140b015601d50001c2e4a0740d1074400c0c01e6654103040d510082c4018040c0e882020340c05000e4270120794010700701107090700e00c504000085107500b00400c41c002c0c1c18001c18105002084484007202210481c3e0a104420703820711803525040c4600800b80d110400030010880c490884803001d890080c020103a41071880c8180900782260321680c4580081003001c64810144165849003205101040010350702d1071421000400b00c038429003400800c9140284e2824050100c1d9185040128001d42a082d00d4540d04065204801003501c130341140b014103000000d80d1400072502e403030b4501030b4000018111642401d10aa01079000b1200030000c01d40c0c01e00595071a11319041982c03400484c960700c40c42c0e40e48524018004a03141d10286910119 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 518317967 1250 518316717 518316719
    0x30c0f0915031104080d0203030f24040c02100e070911042d0801060306020409050a0e1b151603081f0909032d0e030a0b0609070c0b010e0106021204 65
    0x10044280400e0344050a02d4005905101d82001841d18000d98008001c18400c01c25800091a000402180216040183c0341c815903912540e620b210300da62688810440c6050040480a04240d002003040b000c482c01582c500340141c2da10038049800c1020424102c2c0c0c40401e0401401c6c0142c40b52509a090445000b841c06081080c1d50042c0c00c14458190b805141010f0031403003401c405403025015103c03140082c800d2907500e0510f90081d410601030003510f903151001091040300f02c4d00c2100a0012214080e240c000043d416400b010504010f40325000007084440d42c2d22105208002c281c40c0c0300c6445000001525030034001c1078184001c2100c00c1944e452011074840d40c240c01580c0003181d1854501241841e1a403408131075480d0340070201e001c41c0303050082c5400d0231943d402840007008050b03500e444542c1c1d084010565186810740380602004210001300e001410000341b20703648000c0c103080c00072081c02c2035a20701c081050240d00010290f00d00c3d0f001400210303410b2004c202201303a000300300c0b810300d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 518319217 1250 518317967 518317979
    0x402090c09010804150e15150103022b060515070c060e0a18110a210203010f0302040525110120190e03070603020418090803040201141207030c0f09 65
    0x4030020700081d086007034580502c100c50b103070740c5c000481c0d8642c60407e0782c6034896001955546107100f036030003032080542640080010f500c00e100b9211000b810001405003c482003c070072010382503107801e040c4001e0719248045400c1d16080b480654413449035003103566481c03007803c0480d42500250894800c2242c034400d40741c0c4542d100c032061000e0341c5641d0b89540c10040d030314038020001c01d09080301e030110304804100f05010980100100591a0351400007042c0803011004150485c802405103e440c4002c00c0b2050000d0304260340000d901c1015651a0601071b03182445664400e55402c2404000603400c0d40040d051038403c0c024480400e83e0340741c0040031142c100490040c0386c0100e100013041c82c101c01c41006902c0d4400c40084000304030180640b454035031100002406540140038a9400d0306440601c00141c400310f11a00f00c0c0325400021084c11601c0b15801100c517190150410151a2014400c8030f80031005800d005000d0740c80b40e103000a44242d034000203031803140c040b8a82c00c10700254140800813 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 518320467 1250 518319217 518319227
    0x30609140c0309030d060b03010806070201060b1b030d02120124020615030a0c090f0605010e032107060509031c09020918100203100602061b0f0d0e060f0402090c0901 73
    0x1541c0c1d250140c1c40341ea81d007844a20318002e0246a014680c1013100000d54104082c0085058410980039600190740c1c402082e800d0b50550722070108100410010001c005e011841002030b80c0e0108000daa14248888449100340d0b00b1800f40c2c80ca069407140c00401c102c10054042c0309181468001c41810300080d014040d40310b1000a2610301000100044044641d07002e00c6011600c40d4080d5000141d103440747e18034801801c4410002c5465441c02d03101040700c0d0f02400740a60220700080040904103504114400c2c03011124030505400340b006c0c0700400014101e0b0007160708c210134000040d9103c0c840e0b9805101071001c0700030f210450320700d00350f2858090303200d0100d980c0d84007030801c07030b2040051400781c01a480d20b42200381c1c8070764aa20100605c1032401030464013504861440c1c1c00c071801a26908001880080c01c80b4050010800030070011002030400e01c060090051003007000101c18084000c80b50820004461890040104070200801c6240c00564950001c3c4503802913030505880c03800180c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 518321717 1250 518320467 518320471
    0x20c010503040206070f030e040e1506060a11070801150e060f1504051002062505040911040306091407060503090309094317061c0204020a020d03060914 67
    0x204100000000500b591288030417540e510b03034403038186a41c1060070305000f4001c4004840c03040c0b1860408110300700c08000028800e891425140c00b000c01074032240200941c2c0d900032030807601449a01480c11800e0710082c081000180004800401c2c3c602c010b41b544258140d032500700300f404490b00001c0c085503481d8089016003002088d41d0745003151966030149032581c0030350340c0300b250b0004034614001300c1240e020032000d0046c00201100c0041010000805104204040c15440000e0742030000708004901c1d43c100d0600da40240000c41ccc541500c1c0e40350703501541d160708401c1d5020907110000d0034000030304201c620b00a208030b00d8682c1c00c3d8105404042d0b141c2c4621140c044c420908080850345c3c035058510300480010f002c0c00301d640200d0300e80011b0b9120902e44604604851916003541110601a404080e03c581c1201c9040030280d50780010401403041d0441043d200c170740700c0000c00b00180c0700d501c002c0c10707a0741c2c280c0c000303090540c0510030083c2a03444a4000c0c5c0074450514417a80d034446c0103083c91076 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 518322967 1250 518321717 518321719
    0x31407062307020a08061f210228170609060105030717070906120b01080d020604020103050403110106140a05030307120302070327031e0f0b07170a0b04140106020c 72
    0x3650b5040c503000141081c55281c026070014051b08007030010321000010a00c1c003200a213640008070a0f40d9081031075541108215011042d0304142c1050018640b030000c40c1c52000e0784c1c03100c4120851104a070715401c411141c00c820126038001c10440c1d10380401704000c82c0d1100310301004044640c10b000210303807140110320a018150314002d51201b10340e030382800a44042c102e030240c10070001baa20180000c9401030a842611112881000031a000001150b615441056600140140d0f01d80d83d00450003030034028019810080d00d003010b0242c1e1344080c040c0703c0003000741c00c2360783c0b007009911010400d1501560317001c144030340e0041102600141d6a29030310104041d1a040058591889050581c2c07443c0740c0e0311f000c1e00880b885541c0c80c001d50070014000003e0303a0142003103035580500000070309404101c18038080c00355000f00148000040c0c0310703118903921650034a0825001504142c1886c0300c130005a070100c4041c0c1c1c6803404003103141818444e40807c500003001c0c96400c0c3d403400303034040d403190b4a440800e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 518324217 1250 518322967 518323037
    0x1e0109051012020c0106060f080f0f04030306051f0806010c0b15030708030c060703061d04060c0e040608070314030a1d0103020910020619020f0d0b0d02090103140706 73
    0xa8480c9034041d0310b03030403912020745106541e5281d07094550b9000b01014082d000201c0c1081c10300508142c0b0501005104008140d850626902c440d202c0c02072042d00100111f0400d601c07100003103410b40b50f512b41c1c0c42103210000603a881a41c2e8a4030041c010f680c005101504001c1090922404101001a416000506201805000c50036480800d08000454002d86280d100000e80c41320380c400c000404500c29a00c035901000502e44500a1074110540055481400b652880100d40400c0da240d1040603d02400d0400c803444143c4000420140c0d4002d92040e800e0340c000040400c140b1140c06001104c0c5400d020243d46062014000600415410b0030f0351906101380528541c0641d0280d8110b619a140083c00c510020001c03040081d6076490403035150025824010b050031625400f4026240100c130f5100355941022001110007000708100c001300c80e03001041203800000740c0c55940c4041e01039800f48a17142c00c40c002c040d04030303450f0074043d511850412208464500c48041004000c054884c503440304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 518325467 1250 518324217 518324239
    0x40509010e0c210a0b0901110a09090509010b1903061d03120705130f081b06160206041805160504050a120213050a05011d040b06060310080d0e1e010905 67
    0x10f0a0301c031460802e10440c4601c1441c92070300c04c2c8003111219074801d8414100a0240500c281041034841c0a00c8017000c5c003051b4680824402030000b40c10055201c1c500c000005140303100440000c42500d0010405c4403880f103041000d00500c83c45008070074250340c0c2400141c009904030a2503d03941e11440b22071000101c264004038192601c52012980e4070040318514141254842581303202c8243c15102d1002c180c0708140000d6105018a00c03e4a04d601c401040c25080900010030305c03400c5010540201d0f0b05c00c1c010000172400800710941d80030101e20403200015585080c03100505d02081d01a10030341440414001088642e5a1010041c1500c0342080320007082d0900e84080381030f89540284114809003060100106100268081412940c0e46100347d4400701031001c06404100741a41c02621085541d00000c1507424200025a04008841d480c0b41019544145c071301d0070504840e01c0c5200291222901a600e4079145280c1300d036914400a44404800301c1c0700000c1c00d011081c1c45128000c404404d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 518326717 1250 518325467 518325499
    0xf060603062907050d030b0108010501110a0803060d02120d030b0d050303010603090611181003020c0c060c07080a0305070b24040504020103020d180b0901140a0207080403061109040509010e0c 84
    0x1074590f03680e40030741214061545141c1c060098280c81c0d00741800144d49800009e900e40c451100302c01c25081002c0a000c4400310b5456a11290b40004c105941140481c02c070840161a01640c402042c108030000d0108049540b100401b580e80b45080742c0e109a05840160021035404021a0f044441c10708001410b140d4500d0032001414210002400c4940049900900ca1202d060003ca00007002c43c0c6200c001c407540c800a6080f40208503469800e41d01160918041d4101000100105801003040341c40b4140e41e8074603039140c10203a040440000f01e001c128281000031054986030800c1c04140c1c003100e00c40c0c0440c20340311080b020740d603403500c01e58032800800c0940e406607046403804000d18006000020b40d22800392100c04000f00704440c00240c2c480001c1c90100c0610078510100818021200f0a85032000b0101c0a0f4000140541d6039040800c8008005032081c4280300f00c4010f040c0380c440d1505284003c100889034002d006d06140e0341442440320b40f5840c00310380c1340b1840004a90000d06640300071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 518327967 1250 518326717 518326799
    0x6092103020a061b0f0338030601080f0106050609370f03050f0307030804020d06141303172707050303030a020310090b01050307120e0d030f06060306 66
    0x42030140c070441c40e2114450107099600103c84d003100380e80d02c88920381040134104504980780040d00c091280b4100c51139102040c080c201c82e0003000600b400980c491082d0b840024140b400030f07401400c0d1741e4081d07101e4002d144800c3c0a00402084120781617424041000040740101c418003180c0080c10380082c1440507002c0003a03403006800900451407040f6162a841400d0b61a01103010a4905100324003216801410020072580031641c076980368030207900c03151b00703200c0d4000079440100c0c0c0301d80e10703460180744202407885901d1090000e001155104821400c1c054034044d1b92080728942c03c0031100402c200051109241c006020400c0403040032402d4403030700e8504000d21904801d525000020501c1110030958010b180034120680d07520010340d0303650b080b40c42190b010346c02c0540459000d00001d80154083c042180c2c209100d8600454035035181340c20a4207080301d043d0350300c010a94503c90500d250046208107000b81c41c441c241040000e040811500d02e80108082841d088100e5404400c3c15030007d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 518329217 1250 518327967 518327983
    0x91302100e030f0106080609151302040914010e01050f07020607080609090705130b040e030c060103060f0603050d080403090f0608150a03050d0e040b0906060702090601210e070609210302 82
    0x10f000b0044540c07a86100780c0c40b41011f031445085446081383d80426450100040b50040c041d40307405400c0c080b07059003448040c00a00109403001c80210100c254103010a004513501c05100c0f00000900745003000f81c04140300006800c4a04540c082803c210b00a41c0140d11503402101c2105c2c0200700e5600d4402e818078042150700040c6d000440440346d520303584099000801700e80412035051108280d145003403503480c081c10402c40b0099022000400120b003140d8485030742103140f2000455020341b01e450b414545400074544000142500c400c1000340340d0b212400310081c20200d8135100f15140f47c1b12005000b900c0103440c21a101240500d102125940d01c4a07903002143e01109403699088008009048002c42c01d001a00450070300303022282c10321300704000d2803040f80300920f802d090110b281c0a000355860005c107160b06000c0d000e200d140740d95035600d0b00303076111080c20320001c10402d851031207580c01c003c02039110b501484030480007400700c0f16021f54641d800130742080883d10760b89a6810200e18081c08 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 518330467 1250 518329217 518329243
    0x607030e07080a110301050714031b13180b0105031003080309070f0f0f0603021201170a0203010609150503010509031c0204121a0601022a01030207150b091302100e03 73
    0x3e80e007203070820449003a070810701c4030310110001c001a5480071419035101c05003444d20128803404000051301070860780c180601f11918001107e003030040d118a0100a001d0720b0300b081004410b80d00403512003040e103000d40d0401050a1a142d0b0644c113207400504c240c06c000c0d000041c40c8040100002d000400104040c20050515075442e014942c1d40f510002800442802641d00c400c0c400c59010440364002d000b00c9514425160f0541c0b001d030b2804035001041100d61051004a0180c9820308000d42c5d801d00411002d0070748514001800c450760003003600307000c0340c0780c0c4901c0c06a414101003080351031010003503401c2320002d0510814079003d0507205200074410b030b42040e0b0b50304181d2410003040c0309020002d407500c0300c00b0001401a80d01c815005a0b40c070b82014001d407100c0c41c4080c50814a50b85109001002d1900604016040203841c0d994191540002e414403640f00c3c0e5a411031201d18603004040c00d03007200f2900419007400d44c6070707000710f01c0e144180b00640060100b4031400c0001c80d2001c00500303441d074503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 518331717 1250 518330467 518330473
    0x130203040c06080a06082d0105090105060a211712010e010302010f111e121602040b0a0806060415080f1e0102361206010e0115020607030e0708 63
    0x18051500407402440c81c01100c000491031400210840d14500c036007800c0c1c801740d01c000d0104040185944604421000070f1441d00340c011010541c10400074003400340510800e01c008603862820000340420030403281d210300103c09a450300708a22004810060024903002520001b503204170300c1e645103e61050b004d0794504030126900000b40200c04082c036505882c400d07130310700902d5010204121035403258010040e02c950050500c7d000300d45440301e0300c5960542c0b0b020039070b4540003101100c1881c6400c8034500e10f648070402420001103103401d100f661106903080720000c480c80c1c00e00b5a610350703540d0001c1c00c69019581c0c40030301400303000d10189200c0042c0040b900310351008201c0440c41e0f480d4281d00c1002200c000081c0308880b00c075030040c000d81e29100009410808520240d44050613441c482408c92445051042c50080d400d8480d102c4040320041050001d10f00f40d4546107020528001c143e105840b4443e020b1a0444816808500c40740c1141c15071401080940e84001124100701551380440c05600c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 518332967 1250 518331717 518331721
    0x30304080c120304110f03010f1a040605010503090303040f0f0b09100b0f0312030a0612050307110307060806040f320108070302011e0c060207080705060a090c060e130203 75
    0x50444010014503803408162a600b04510603a10001d00040e24014905401c40f484803000c1d0815036480304240d14020000f040c10f00f2030742c024604a0300b40031441c0700320140000310b10f503042c103141c090782c0d00502c02031034510310394503022204607200c4c04050402001c242481d8000c03402d001107100031984040d04500c00c000e0030305022154541d00c84e41c0620740720405041244400461402c412140484400070b0050400700c2060003400c031403940b0040c03901d040319954213400f14a80c1115501e00b0851440f50004603624082030400c01c182d0030780301d4041c2d4840c0e40812414081f042d0b026414980005007a5400b041c00c480c00380c00b50020b03058030300c010351880000010707002d2510405840842410b442c0e09a609003640c9a0050a0311141980000317404544080035010301c5480384500c90700604807529151010464599807901030340d04c6840203441c000c602041380740030f00c01c050000540003002200100003a000395a03a00e10034005500c00e081c14420007810203e51522542c1c0c1da01040101c0600856880c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 518334217 1250 518332967 518332973
    0x270f150306050a09080a030f14070c03120b0d0f210e0f0109230a0324060501110703110a091d01050105120a17040b030901050f06010f21020903030304 66
    0x42a52006403005401c04000c6010400203124072a0855000715420b440c18000460540241080d0b5010900855855040c2114404e505c052203001d2403195a840c000714520b030400501d000c3c91a640031f85040e00e400fa04c00d4513a624104542d664981c4180955644085410009048001001c841c21980300c9003543e40744c01948070350607221349481100d1603012040064011192900c0ca401070000c1040c444959040e4074a801000c00b01103100140380ba41240d45903038507541003140c800c103102031003c4064580002c0315244e006100c0985020f00c0c00058000c2040503455a0710740c2e82c8409841d883c4614070380c0071070361181040d15009d480b1105c0c00340310002d034064080d5900c03840020041c3c00d07546040e0000c40d032450a0302d40c4112035000e0500030203400501b526880101400310f07030300300e210307030740410000800e803840c0c00c060741c401d030584c5000245501d4103154a1401000041803141084006146070084640042d20203102501c0ca26905803610104d8007840c0080c4565407941d40e052101100700010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 518335467 1250 518334217 518334251
    0x50c060f0405010f020702010905090c0f04061701090b010c0b07020c03030c030c0d0c031403060a090f05070f14042105030f0c0c04110a030b03121602090105060301270f 74
    0x1d24450b10081052001c0d00c6502c10480c0613209009001501c2d00100b00072510380004500c2c1c1103918991164a0aa850002146994043d910070030224988295042d044100014400d004081c0d125062003480b400c407000810707900e91680001c01c04210800030940042c0308004c107543c00c2e58042c003101c0ea51064040100d0b941e802441c100c0301144103039040034401500c100034598007664161914542c0c480c0710141420947c2000744019040020b032030000a405460313000f101140020414001000c0c20261001004505440e01d1071082c000860301c0c00c401c030700403042254222441d2030100302201030840a00f100061021901030094880481c4c25070b03d074424140149003031179503081111900c0109070240010740b001583c03502c051140600c00c00d015180250014058607030b00070192480031141d00d80c500d503917070000b035403110301c000b0135078607000c02c41c00c04100550240508603032540c1150715200e00c5d00d44401c541454450800c040540405012480c3e4011406180d0010b2040c4104640c0301e04000c6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 518336717 1250 518335467 518335471
    0x708061008240106120f09060504020310090b0c070201140a180920030402010203130b19030e0c0f06190807031113090203060117040b01081e0a1101050c060f 69
    0x4280541c01091099451050a4402c03945003140300e414180e18140d02540d03d000002c40c840010340c1c4a04141161600754401d04e58240d110b5240011142842d0040c540350a00295a0700f650728a040c0c052004201d036040b0361540b0032880e4100c1a5200c500d440104c41c41d81c0011680041d5403004145015140c2e0007041c08004100000d110700d21880ea41c00540060301c1514900000384802c428200d46440d45220040d0b074031a0041c01181e10f02201e11001200c60381280d07222021040303001c40e4030b68910b4003082c6901405d52283ca424000580301c107031502d0310f661850004078841d00d00703a0014112520740740305581d941d0320700321207110008081150103001c814048891100081ca41120750050031681401d513800100001c807018142810f01c4003c40095002521007814040e44050b049003030b454005034144114410340e5001455494841864078100281c0118001c4c002d01b03000b599107d2800050a0740d80b80c0c2c0040c04d1044a54500d03006031018860615101c0c118010101000346801012103514 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 518337967 1250 518336717 518336729
    0x906280305010f050f100b070c05030313060801060e060d0e07031b03170c060403080a021c0b0f010503310f11130e030405040e0f151803031902070507080610 69
    0x3102682c3c94075459002885c0803685154503000480b41030201c400b10001606500b403180a01c5001140c450000070728540146402c0480400c0038030041c081d00341d00001ca103005050b24241180c2ca03200420001d4164001d142d0b000c2c0c0480d50b6040030b154020000c0184100450f0803180781000000c3c4109009109407050200b9505000c00346c0750105600c000710203c03015003410350050305607070320703690350448554401900c2500419002e2002e54030910924840820002e07840e00006201e0810f98240b019040710383c00c410341800028000c2210b05190340b01c64880a044030401c44080513450036000261001c945405071050301801002c4080001c101e98010901604507003520340701102d0702a2030291080c20b0040202c0b40c20034442040306040540041c0d07100d0208900b51200d20000450071403801204124400307602d4010024028803111007917000c20045010b1001e07524610b403820b00c14448070134501944520710b40c0022034005006040c0844400341558805451799400c00c4035800905500ca03004a23 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 518339217 1250 518337967 518337971
    0x70305190c0b0a0b011116031515050d15090b0a0e161e030209072c09010515090d110117010f061b050712120309020906280305010f 58
    0x8201128000c1c0c541c2554030303034024003500080d510b0014000280900d88116814410382115040c0507050501040800d10081c5052102e400c2c074505102c101030707051001e00c0052a01c2d100041007511100014172003518401d079442e00303000141d07241042513060307010b00340c407819071a20315484100420100740e035004442c0c086051250242c1c2c080c5c1142c8644ca0b200030713410860380e1030303004000141034000102c06400942080d0848140d4075000703d845002d045810000207006010103000c0480c0e42101450040c4030010503804c40641c0e580407400080d010f0048034800c030340405503c04601c0d01311044130303513802001d40300001c2c103c202d1420320000040b0b9240540400c1b48903000ba0ba0012085113140d0481d0303500c1411800301c501e064000e548102c01c0e0341c2c00c0c40e440d81030010a034001c03410402000000701900c90100d8110509403d040b10051140b10881d001c00d400c0c1014800569511882160001011250310070300050100b00c0004541c8a05441a41c8001881c00042400030640c4441e485d4080e03c182 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 518340467 1250 518339217 518339257
    0x34908010509060a091508031b01060b04060804110f0301021201050901050d02150304110d0f0317041a0c0c0f03040914090a03050904021204050d030e0111040612020f070305 76
    0x400c0314251045840c03a400001d0b2200c20091400641c0202c026100b002c480391801b181c0701e48800b801c42c5d0006141c0b20441410341d8560810f0b02c424801c0b100140713480f940c1a07042906100009001d00e90142014260300010403900c41280d880000345035a01030024002c6544007200741141c03c40c000c0c2441428400c5994000001d000d051a1410240e4668000c01c0900f1043d0512008111504060010703500070f030140305917030142d44408010802c05406800d030000c007403416140c010000700100019124040d070501c28480001c01800401404042c2150350411582d00d80d0201c1050780034425040000c0d10481480700380c001c1000c030003041910481c007010f00c0300741c0b542005555500d10640315440954021852840420700ca54083c006000004001514100c42100700f51246081a1030940d19500071002e0520095050302c6010071013001d00c3c0c0244199011201ca682340d0340205c3c07003201c00384080e580b0751900e07245641c1c0c102d894403031175008803980b00c1c00b031418000c1981e00542040b00e0000e0582003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 518341717 1250 518340467 518340469
    0x180e0403080f0c0d11040b030108030d0c050708071e080427110403020108150405040c06030c03061a070203100e07030302071a040b07050a231b0349080105 68
    0x2d403a2180719400d1031949043c000715039403402801c54805102019000b4032000c9854000c4200850081000b10001c54540c500c40101c0300c1140d8101c40e8485c02c2c00010404c1200080040f0142d41c0b040d80c1060102c40300e6003e54494140c130820702030006001810009010540c01d10b803044100b4509800d480c8454080e900b902c2d01d10494161130042c400040080c40100010b6210303260842d8030040c0c80305a9403428845001180039070b50207680031100d039424402c090000c2e43c1d16218070b000d1484246014400755142ca1514a800b0030350001e540e0303448000041071000e54500b040650b02103800300700c3c200101d003808100b06480c1c2c004c0303010032401400341c075000254003183c004421068660f0442c4152816140110003d030a0340072000c00c030344030b009104004005c2807450302c04c0090003034100c1c48401d10342203001d2010b0070184241c5201030740024800104c0d1107a00c00003140c035a0000c0f959812605101c0070300c4001c0445180522240302d00c0f11901002d03d00c07541e0a50902c084503015220035002ea62100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 518342967 1250 518341717 518341741
    0x1c0c060f0509060414120a0605162c012a051219031d010504031701080d080f150a060c06050c0a0c1209050604062001050412030c180e040308 62
    0x203207182c0d43c0300d4800d22050007550350500d0100b028240c000c00407120704049510300d500340b0180c0704007504ca050303641003080b02000329a00040f4140084c0c0c0307000c0145104e01d0f10b1940f46003010050b21800003c1c81c0c1d80100305a40500d210b180d054031003102c0340d0203c0c050700c202c2d102c00384a401d0048131039016188103610007104000a07965220265164503e08803103a032801c0b0018502d1121f20800b02d50806d401884000c000e22801d40254003039039401c0740120881059a03002c43d0181c4c0042d1140c1e10010204143d69440b070f041940140b42015100f9950b118682d0300d1005500f41c2c0c00700e40c1e001c0400107000402e5034100010101e024820741c01803055035039030103140e180740c01b82d2006100400c0d03a0301c641d180021400c0f4042501c201c800c0c1040c00b026525039022030440d811581020b40810b4883d41c620b07101051414180d0744251310580240001d1074580e4a042101030880503800034141c881c8180b01c94180a1003107007d0680341d07030480722915a680c640420610b01c00380d44c140e010502600124400c0b01c440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 518344217 1250 518342967 518342977
    0x50c0f04031b0803250f0c031101030b0102030a020c0d0825110a030b04080306011101020c0d110105012106020405061c0b120c270a020c150708060405061c0c060f05 72
    0x3c104100d091102440c422175101070350041164681d03400400b03000000c103103030704e50009580200c0802145200f02c01c009006c441a14590b00c2c107551051024001040d80040c403000080002d607820140b0044a01e4134401ca4010403c0c484889402080a510b00c0c1170f1801840c00e5207400b80c2c180c0185075a020301488555007007400007500001b280b83c00640492191001150406010324125154136181c1100c1822a000000d80b0b00d11600520407400c0031079844511001c10980da180204180d514280961803583c10302d290220140c0c4410b1120814844d07140d041ea002000041c0070b85544004030f5602d04014059892007035440f0f03241c074000c042641809000102d172401640000c0085145440400080b44d084404481c0d0707590b04c0c15091800f0650541800340902128040940c45990003600300d8140707c2d040c004011121440d05c00c121280740c2c0703c1e08075908844181d4001900303454080101c2c0d00c00d40205001001048c40c1c0c00740104010384a17160f0000c0394003981da001c0c00b8210300d00b0201c65034420 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 518345323 1106 518344217 518344237
    0xc0a0b01080d05180907050403060504050c041802010f11070f18050c13052215030204060f0e040204020c0c1c33050c0f04031b0803 58
    0x1080380d05008012420040c3c02c004021000b404813400e642100c9201e8507520300814182c40c010b1084401458100900f4021b070314103401c0456880310a044101e001d903180a00b40c032405400f640480c0007040e416076408002c0c0c1600c0c9070031100011429082c28141c0106000040d1000506c003c0c0e00041485c000300380d40003846001200c3c2200c400400051100380d080004096011000d807124042d038004550340a102d205101c6440e0410b00c4207a890041546840456100e0700e210203817903812241308840a00c00c0301c0e00c800403e141c221540c442d40040b00c1900c4041401454a40c000c1c00801116030b080710030a80f810000141e800001d81560500768002c0d44000d018005c0b00c201031180070f2000480082c08807103000c00741805e400000308084d1215270326004130300038203506012110300740300546045407241d450307003000c440d2111100c1356291381c040d1900b4002414030020080c1c48050302 = true := by decide +kernel

theorem cover : BRFrame.Cov 518165467 518345323 := by
  have h0 := BRFrame.cov_init 518165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 518165467 ≤ n) (h2 : n < 518345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
