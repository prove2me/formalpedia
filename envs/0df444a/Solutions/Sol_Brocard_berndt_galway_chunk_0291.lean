-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0291
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:00:11.220133+00:00
-- url     : https://prove2.me/submissions/cf73bdd0-888e-4085-a7f2-779e391721df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 52158277 ≤ n < 52338133 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 52159527 1250 52158277 52158283
    0x4110306010915080f12220f05150a09050603060d020405041203050121120302120a050f01060e030a02131104080313050607030e240c01060920070b150a080309030d020f 74
    0x403203046080c0c041904800d0980304080c648a42c40c1c40000d40a00035169140d2006108c140e01515008001c00180c01d082000c07038a045801e403c0150725103903081850041000429131004080780d4100409034081f0005858a0103240c1c065880390342414625403101034020120380050340113607185189007031080c2641d1242c005018106400c007a00d21460054030f40d09501901c2450751104142042c0070800c03030108556408240a00041d201c0e00d0b800381d9075010101c41135182107a115a2540090002c08018644181c00400c1c5408154001c1200c2000c044d00b00c5090f0019880780b1103d810000d4006055a02004804050b003c101d403800e0900b105a01c00034100e1031600c041602a09001d422440141d41b103440c40f1002c40510650710390744400c1c400780300740a0043c0e8805c40d0304090030f103204100c0401c0401680100e00700704541190506a494803442a010405400e11000754813802400c0712980700c1c90703200c201030800a001165202c1c0c0a1061500d010307040f900c0072013190800120495405004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 52160777 1250 52159527 52159543
    0xc040902011b020114030f0601020c030c060f13030f030f02010e011e0c090911090a053321091c1d041e090c14030c0904110306010915080f 61
    0x20120041c0d0ba41da10041c0c66081c4628040d8240038004000c005511208541c00791183d04281e0954917110410414140d40e0a14000e045a00007800c0c840414000720f160301400c0c2110702d814007240c9031562a00e075602c4641c0c1e0060705400054010400c0841c2980901400c10440d0500d402080a0381404510180410000c6010260302d6100c2808081c5c0500c035000d46800b51442c001c2c01c1014020140703440c0050303423140103030600071100b0b00300000303140c079045071092a03204d450320407003c0c80d0008603070702c07080e000e041c0130048070918003444103610103034083c001c1101010782d09600640c0e9060205220703140ca00d40625541c04d2070100c000501d0015440120141785d250405805480360000d04005009012504060781c0c202d2007803805e40c0207a903030540100d01c1060003004408419919082c0d0071a14000311860544c26a0240c42400080d040900720260300c00d001d414070f2448000700c1c000007410100c00303900103011207840c3d400f00c0d051050805459002030696400070101080c0803545180c841c0c9074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 52162027 1250 52160777 52160807
    0x81507030203040302031225051602190306020f0301090e030a0f0e030a08070f03081b0403081303060212010e130f0b04031701030507060f0905010e0904020a080109050309030c04090201 81
    0xb00c0071804060080040c3d0304944a030209400482c945105000d100c0d08006458540c44400b1101c1e14502600a20480d030025008400600c44070086030240001c5501850700c041e440c580305040000410b160388050900360280c00c15155a9502d420029400d80b0b81c00c005a1120ba04100308084525802c00500c1080403005c2c101041e03202e84d0b02c00040d0500d40c14030005441c00100044080c1000b500700b404506581c80b9440d40c81c07458031024a13841030081150301e58031800d00100010b001040d840005002c024103244801d1841503241da456a0907a0071401038600070451440040c002c12121000c0d6544c000000144c0000c003843c1901d90050058840c200078203c224000c010030180f501c00c504038005500307004111141960741c0d10788185e5445c000c1c0700d410006183d180c2c0d40201580300d01c103004119070b416074034000074491203000c00c256020041c10480c1e1010a0395000a02100280101c0903800c1c0244042e41d222006203007413600303004c80387c10f03078034403403441c185281e401070303070051903030040c41c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 52163277 1250 52162027 52162031
    0xc0303060906030f010903030b0a1401050a0c1b03050a11090c0403060b0d02190602010b01020a030512180d0909060b1303120507020a0f030302240a0c0e1804020a08150703 75
    0x440b80c003c00e0403d000d00142c20215400c1910741410306030150040300544e2030907103403810002d43e242011140800026802da0001d001000070703400141c4280900500c0364094076007402c1c600203100c8034003040d088650003214a9040f881031041801803268818456603070507108010a407400040151f198800c0340001002c06688140095054070f940e007080c4003082e805880d00c00c5c6003a40c2881c0c090040d1051040c90015801c00c0c540c25469440815020340065040c1c403210b0a1080c0c032406909008002407102084c141d43d802949005501001514200c41c0c80d9101e42456a040486036020743e05550801e0b405503100b000a200e038100124003410450b40c11540d40d070a51122017104030307014070900c00302a41c800030501001c200e103e42906040122031180c1c00311011008807034091680c0c00d003c610722490850051380041d00c0d00b58203400490750300c506031600d041058a43d00c0054003151928003529542c100d02000c0004505003488000050450706000b00140d403072984042c0d42080000b00a4400c0603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 52164527 1250 52163277 52163281
    0x105070e210705041a120d0c0f0f1a090c030303101a0d023601080402040c2001140117100b0f03010219080709030c1509080f01090201140c03030609 65
    0x8424030145003d05001401031102070840404d242190007040346907881008421100c82030182c00141e0810511002d03200c101c1003030f000c0d0300d80c00c214402d405810744902c5008454980010b0554607060500d01003040c0c650311905048805d94903240d542d00402d40242c0c010030912200c0700505001004032030880e03040302e0b02501c10082c0c0c14414041c1544440c4100e00203d410040344030079111155005800745260800381088460a0140d20855041c0902088110b00440c0148c20240c0049080c0034190410344026600000e01a0112142920400c41c1e030b59915202c10042c1c1004403098014000035039103e082c1181810004d4980018185007410980d4a007842071701903c44565982c4d201c10010001c64854481c6900303801c8002800400384002446030f03000031f1240d070280c00f07103005880e045040c482d075842c14092804100c500806005060203010a400241010304002103d1469405400840c400c0340f50710014001030350380c030544e801c010020700503050301c10360000c19280d00550031580c0003015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 52165777 1250 52164527 52164589
    0xa0e040803090f07030c0e0c030103030e1203090310051602070510050903010609020a0507050706051303080f130303020d0e04050114060702040f0e0c150702010503011511010912020105070e 83
    0x8061100c40c0c0c3d1003406401400414007905a65580c22262010040b40840ea078200ea000168402408020f01081901003a0b41540c28201401d00860326294201ca140208807400245020201525110304981b81c1d02040369010f02040800c40c1c030f886a00003040094203210000d01950304110343c0700200311011903200e240e07680c00d41000005025181003150b032000f000500419542c400c44080d20340e48500e92001a45510403011a10f03d42100081e601d041411552400c000741d0010b0422078007840f041c4403040f0544160007000008501c2a00103044080c0000000782455803d540c01c0c81c819441e00c8010440549440075030006000111101a510b40b5244005001003c40d4454011142e2902200c1c040d12000016480701541046410614403038201c1908851807003480c100070b002810a200400400060390740e42c112404803414103584504a803d1b10070f00711041004240e890050031444418410780a11881350407281d11f1410307000d081c52a0012504a20300080c2d0004942c1d114017401c0c0031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 52167027 1250 52165777 52165783
    0x2090f090a020904030302030f0702070312360810050f0708060619080709050609060f0307140f0306040c020c0d03080618010906030203150106020d030203040f02120a0c050a0e04080309 81
    0x100780c0c1c0107100c4545410306041c0200250011a0074400c0c2c0b8441c5c80104200a0000880380c04582e0b00ca400c403803060000346400c941c02c0061984100b03000c030051304000c0c001c0e9400d55000c0c4014a1602c54a45514030b00041a403820040c00060500d00b8540024030000d0064036208540c03152250402c0140e41c0c40d04408200c0134441c40380622a10f504500001c0c0546502c90000b900030384850383c82d103404540740c0c410030900b84500f0016a51008003000b01e4030301001401c01443d8040e42900300840c1103000c1c1c00c80c10916912541e81e1031030580001041041501d8184180e12aa5a0390300c002c00d601d004144c04520740300c07074103400501800b4507900000c00c0d55481003c18411410100c100409079607565045401805031307404224824001d859843d62240000306000c1c0c1200d90a40c020b000022a0440c1580251b102a005484402c0b652082801507203804100541c29016000106402c00c0d103414500740114003a0002849243c0c980b8040018000800000d81c0050b0407280c101c7e50303600c4110403d89 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 52168277 1250 52167027 52167043
    0x70c020607030806090108030406171005060a02031c180f06020c0a03030b0307080609060a050403030b040e0618030c0a1b090501080607080702011122180905070e0402090f09 76
    0x540880c0009071070080507804055a40541404d44030420166201d40c1140d4880c0260b0242c40005074031101c0c0c6011075058000441d41040a01c030308005403d44910118045501071502d42e00540e20014550049803d1110041000200c4100810400015074500601e802c48140040c04210401c6924414442c09504491000c59040219403100700300c0e16015014154a01c2110300c00d005603100026202d034082916885402500d002d4006076980084080007000b0141060701055a0b510304c601c421f8075103101c0c543c084240f680c0140028500310b00070740d00724007419810310f446030814018a001d48000064a2000d2540000320b0781c0c100d6400040030810b50340c940d0046a00506110000031119801700b0f02c0e9007c1d05071580c0300d42e506c1c1e40fa40e100740e003a81c0c405c1008200103038040140c80c20046604a242100103d43d01841d00d9032a030b5031303c069010b1800c25004041d45681d404240c820007104200070b070000c0c039a040c1100c3c02e5181540014118010041c240b84041c0202d50016225031003c6c05480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 52169527 1250 52168277 52168279
    0x30309140301110c0705030615100f090302030109140c030f1908070605010e18031201030305030a140a02090f0f060f09030307050d0203130504090b010312030b0d050c0312040f0509070c02 82
    0x39141c80d113a0741c00d50340d240c00c217104050081c0500c0300490085003100040c005204005000110017200784441151185580303085001005403004010006a4007801031081803030040c290004c0c13455500c5805801d0010002e61075101342e00000168010410101d607141c1031000a1103054840510b6083c401654482c101000f401e0389d04d8240080b840c805004001801583ea03002c25201004030f0320310b82a134ae4880c40d04404000f090708001000001d200d00010340e8005140741001c100c408420160044c1d00c2c1b019517010740c08036008601910541480000c4003185401114003038104002100404e5007407096600040b0844400210a001510104101c4101aa0040403100e000105640c000d440c0e401595003074040745550b90740027402d45400c2c003a0481d140d8101c040803c0390f900c0d41d500c820340007007071043c00402e00d600c8200421403981c0e500d0441110500175409400000130080c00c060810400465103441c102c014081480000e40c6500aa010b60710141d80c84411601c40e86c1c0190366000280d0f4001f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 52170777 1250 52169527 52169561
    0x3081c020c030408060106050c0c150c06090601030b060307030b1801060b0706090201080a02031608060102160f03050d03050f0c09061614010c0203041a090414091c0207030309140301 80
    0x41c2009000004004032900582514210f07620b03410b04807807078491120414400c0e4441030000015150a82000f4003100e06404120710340b1140c130100609000302210200301c9508110010028408000301c0d459010001b100a45022030465540302144c0c14054100381e034941503020300d07040c1d02200b584140c0142c850a00d21688440c0e192802601911200707030f0032400686080c01054140e02d6600a80e4000c4003041e50400c2c00c0c03d4200c00480b1900e0300200101c0c11840b40c01d111562800c010301140c0041c001101040a0481c20360801500e80b01c402e0240d60201441c003000c102c0020000c2680d150444140c5410701d40d201d0b0040c00041081c0110b608030b02054044007210713810015991a075840208048000b07100c411240d9200340d840303024520604034440c1c10000805880001e503c0240320992000300005142c4840340b981220694044900c0821503103e114800c1c501d282003a51481c1000b200d00c0209402411036034020001c8915100703120340c440b450441c0801035582900602800d018407044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 52172027 1250 52170777 52170787
    0x9150203040804081606090302010e0f0a0f0515070c030803040f120e13060308030c1b03030c0a09091505010c06021216030e011a0906011101051015050c0703081c02 72
    0x8680d44a0344244138142840c400c001961200d601d00c5421003003207420b9500c48084582c40c540055031000800900d940d0f0141c412804c0c2d400555a003540324000d04191844441181d060a090104041c80745100103031100d01400001d0000300041034900a50740d006131080d40b203440314603000c200b0700803605004069400b26012141103540c4a50290900041241c1c1c40ca02c181444030200708548044c00003420782e280400c001801c000c051401006000124904072803286201a0890b007541c0060b10f1401d40b900f0006050180594407a42110140103010010490b11002d2207028020304060310406041c040502c2c07114082c015240d050350f104640380040c3e04620f103403160103500c01e0b04140c142c2501082c90325280c2c1c461031005114502d0b482c039460728079036800742210313040158003680100503074100013012090086009081c05514020800e186680000f5410701501c803522340d0610045804000050002c034003400c1c00060b900084a80003461150b0300d00304035500c1104514141500c0c42c20701d000141c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 52173277 1250 52172027 52172033
    0xc031713030806120709020901020c090108160506160b0604060815040201030c1404050f031903090905060603060102030d0b031c09080d091203050c0a06050103061e110703030915020304 81
    0xa8030309824400c0d0740c0e41d00c1d10b664000c00c1240800244d5000a90b5038072414003409600307074983c010018285c0500403241c02c03c440c80c0c009207a50000341c00450f01e42c1c10036100d0300c82c26403090f2100000b625040300c565081c40c7e50001c0c800c0c40c9400e2424054503683c0c03408040350072502c42d98800f1020744004425140ca03506601c2c1400e80c2c1d100140c0f004c9000a203850803001405100d0160782614030489031034686080d01d000d040015035440301d00e415034540501c0400030301c007641e1030f104400103034440e442d15801e603460041101e0843e10300900e914025a42001000503980e804002c6518a0450200005150f000305c0d0100b8034040481800b62480c80c40e11901600c80c4c4c0d00200040101d49903041150504004400102d03441a603038400d200191300498403110000c2d02031006070031070309928000c0b9000359001d0788500c000c0c4c1d54207038000d4421965580d603100c40d424030081004404814074074140461143c030034401c09188100d01c0b000d81010b40d030340401800c01100c400b1400d14002c3c540010364403810141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 52174527 1250 52173277 52173301
    0x12050405011d0610051908031b011401030c09150503060702101811060307050d0203070c030f14040b0a03090b1806090d09060e010203070c0e090d08010308040302010c0317 75
    0x80401d000c03541044400a040c2d0710010b106441003900500304959949410103029840925a0b808a2140c40b61180030454003403c10140000420b003000d440c0f0a102504010b90844050b1591260600c2410740180041484440b1100446030340301400a02c0402540e0f200a00c0000c87c0c01c050750500032201072014007a400100501c0c16001a0000c03c0100302d59400c00c00b4103040b0704002018220850305210141c5040000b440d888541801c01d5071130300364050001000c036803084030703a480410300304201041410b50210100b11440628180318081d0100c031362001c0f556003d14071943da0884400245524498820342103d003155034802041d261a040540384030521288050060302244034900018554050004440801d10015140ea002d09410188211910b445489105041d0b20041100000140c00c6284e00070003051140004c140703904200e24900d041c421004081801c0050090041c0007148a407030032203046940c2401c01d0f40805000749411b40740e490f00d04002e08140c48181042089202c644 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 52175777 1250 52174527 52174541
    0x106051c0606020718140a02090a030c0e010e01090507021f06050303280203070b0c03060a080a03020109060c02031804020703030605060408010c021c020606090c09030307030908010e0304080312071205040501 91
    0x1071488170091600044403c0446001d042c440c8203014050000c0340590344039500800211101500c05c801503a1240c6407201d180601c0d500140c0e040d131650004010b504070103090341d40900202c5405000c14144040025aa0b0364a0203100e07101b514448100710304201554003160080001400750b90f01c2da0400307800001c90b60803421410202c041d10408180605101004890460354000c0d010701d4103840703101c0c51444542000f0701c0c1c2d5802c4082a100407401010400c240b61103984298000b0810910f10300d400401da0f05101c1118082d58070030f001c1815440d80d03120281d02440300030788006032070f2021810b00310003804941e4011a0000d60004000c1110003040d0420f500c100c00c1c98089581c0691075030300c0850042d501006100c0140c2040010078007a08c1c011020b903400504000c03405081583c40400a03055078403a00044020882c03050742008010020701940035036141800181d0b0a2a180508090700d034810000f50400d46a4114001242c1c03501401c890f11988080701410051031030f0a01c0d009008000f2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 52177027 1250 52175777 52175789
    0x9060b0702040f020f0a2102070605100f080703021212030702030c060105030a1104050702010605041d060c0a020604140304120309060e0d02060a0e0d0813030311010c05030106051c06060207 83
    0x24640c1c0d40440000394000c881e070701010907100034905004d588040340c061507c0b0308800100102081c0c0442ca03010180054101c0700d001351000900c0b4106402100005003032580131122501090008201c60100400e95804407074040c3e41108a032010000204c1c14000001000980c0000200a0080244e80000a00500c0e400ca40407510142d89030300406a5035850f880d030080007140e000c0404041400d0980105401c10740340d0002285e01c3d602c0b01d000074283c8501e490101d442640101a0011860040100c41d070800b03808118140741060a8070000d4880c500284060325105501503081c0241e04104200c500910802d0f6441d50305031101e180092114031070344101e000107100d1844000007468100b0714880c002e0360080c04680b50038141081617900d030001010700ba80c0845000101d03c0441c80140c001c0100d25038085044171207604501d009086405541120400b40e85848584040180c00404483c10740c4c0d018101291504c0030144140d607121194010701c8151400d10b00700256082d00041c0310419519 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 52178277 1250 52177027 52177031
    0x10b0a030f021002030c030a0507330c14070809150301060201050f010b0307020a110f060d060302031203040c140a0503030a02010b0102010b030c01021b0103020c0d09030501050606030403020604110a09060b070204 93
    0x100101040383c4c1d034000c4202c1031b11190000c10005074514041c00003003400510446a11b078401c0d01c09408664034035400f004001031020302c1c41e41d280d0034003850701c114034040c48907040940d8001c6042c00d1030141402610002000303004001401c403801e6803075010860340c0150309840160780390b8607900002d0181000752682c0019221070000800c100b644a010749104100341d50003042c01400781e46402a0041c106d0404030380140c01e680c080281c94503901d00502c800c04803808003007001c0d841d5205252824802c01071028071a2000c3c0140000540c07480c3c4810200c510700c102e04400030450130001070000919500c1540d25206c0000c07455825601901705215096003600204a0003480d0402c0c19107403058280c00d5070040e04240d0a45810b200d8440c1d1201c0b0102e4107240040c00d010802811034039007001031000d200400c00c080010020030400f4060580e0009042d100d040c150300340799a0103581e07101d0240009207035240b0b00c3e490130301c00e46500030410005c20340c81406104880e07542c8524006944070400980c0540c3c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 52179527 1250 52178277 52178299
    0x9020c100e0d0f050412050102040e0105030c060d05040303060905090f0606060406050a080a1508060f0a060f06050304020d0c06170130080c010207032c06030c0c010b0a030f02 77
    0x311544038003145544850080c20340c491140030200c501c0c07050840703490203011080c000411000307010398401c100140b045000581d11402c00c3c0744001d500805074441407181c0c1c0290400c1c4000d0b25503800380c0719511120303030020800f5101c61a0950161103290003007a1610301c1c040801400010005178074950003c0321003640e0094403940248a0fa074422806944045407042140e842c009201d02c0c20706a000c51804000a00194000c0b8002811802d5900c28859a071114007444002d5484461003600030490b03c3c4d081144a1031711440404a898600c40d84060205c080002815034948031400d50f01c0503032046018065903121b80d1302419058902c43d070400000194400400d00d2074240001c2001100d030012007000000105000d60f0407002e4072001156140000c0c00501c0e1841024005000d0940c400c1e16884040740310304402d26103000b120214808401104150711505d0b4031000216504150f07071801d400c0d5a8a44055150b014004400e11503030043d0000ca4008181325003c08810740d980d00c03c5403442082 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 52180777 1250 52179527 52179553
    0x9040c15080601020c0d06060e0717090109170304030509040f05090106142b06060605030601080a090f03030507111207050f0307120f120c03050103060b100207050f0d0c09020c 77
    0x10481c11103038103026a105c03801c0c0d030060b881c020014031201071003480c0120742c150316140b102c540080240c40400108080c2c1003d0080c030401d0702c3c41280d006441c44000c1000050948a02c200d080345400d42c1c80b00c108002001ca000d0621840403203c81e194040c1050060ba5051640b240060100700d455040a519189020440b9041141081400c0c07e000341900e2690002520302d2494161154500f0034880c040d40700d0100242003070058000500140d141c058407458000d00141c03003290014240342a042c80d03ca0341000240d0404002d0102a800d440e000035944e0701c0050940c4c611551051096140c8501490f80407041c2012000300f460350320035001e507005d074090350b507000b81e5030f0180c441c00801009026800b0000c2030f2044511840c40c251a01e40039000d01317060f101040440300c00c00c80301c1000070340b9900140700f444803c2c0118014120309681d91103022602d95402516080700740145441402100c0e848409607450f0545032144640082903c000c1c01e83c0c94811300000d5010344002c111502694007480780c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 52182027 1250 52180777 52180787
    0x507110f0f01060f240e0904050c04060608041a06030c03070305010506040b0609031f0b10020a051608030d0504020d0203030307270b0a0c020102010905062706010510110a0209040c15 80
    0x441c4e90b617800c00c0384e190343d418075049002250044d500c001c120792061110500e076a040b040900460007007000c1c0110700c601c03806200540701d1540003801070008010070f020018244126141c580f882c20580c1381c54945881c00040d0404400d4801a1b50520940b47e0100901c8010351189000d004111030401546021100b40071041c01105d011a40c190000c0306901082050200c1c04070481840450019940d40c1c00c0380058420185001c10b80014ad010a01800c00c0000402c0010602c245038150703400081e11740240c50745c3c2ca110b42d03103480c194140c0342c1020a0454850684110b1501d0f80141078035280e182000c0003d21804c0160502c40340034401041030300600b4040a20601074a087d030003080d02d40b1401c904156803081c400b07841241159a22084180031590510145000d140c003501c0320b0320b42068440400302c9403c10b816158003903402c03d43c01002039580c1c0604010fa03a40c0c0d1030070b240c035150540300207940c1001c1e10100069040712800c0308100c00c002e4a5024030301a10080c81025a207190640812130f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 52183277 1250 52182027 52182029
    0x6060315050a12060f051501121103010504110d020304051f0606080c031806040524131103030712020d170405071e0803040b0304030206070206040c03060507110f0f01060f 75
    0x2400841184080c48000c00c000003100007a80074400204401001c1c0c1d840904032503085031030358035058806220407c0740da40406540c004888100051020500c40c218a10b00c0c0d100c10700c68144070366a00d0050780c41c041c8003070707003950800c4400c0301045450b40740c0f0381095078550b40124074020402640781c80080024505102e008140e501a9076164040c0d5079403130031030110743c0c00a440c023403985210841c4040405e100300081c9110f10b00c2640903107006045400c8814444010040140c618406030b01044101a124252010155000841146082a0240406c0c02c40c07040c1413000e09110289207000c044160000750100360603440c1d903646140c8500e850b144e07130842c032030a6400400b65000300030204030350000320384d00300101c0c829000204100e951f139020440c5103900c540d02c11943c00740c022040000b416014007403030740d01c000240080c1c5002d03c0c050350380d0941800d503030100908403990703100481d410714410407402e109101001c0c09c8900810b00120031555519900c135051409600700351020890100c0c64a0b408 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 52184527 1250 52183277 52183279
    0x70c06030c05040609230303070c06030b0d02030a171c0603030e041b0c02010509060a0306170a020306010306020d150602030702040509010b0a050607060905011d01050c03040803130c05130606031505 87
    0x404a034142984225144001ea10100c03401b258400400d101c1e6038140020314079548544045801d00703181140c05000c0c3d030001440c00e48194a102084409614041400031850385d00c070001e1030329042c1c6002804154001c00110814110760300d81045440c00d21a80170f80140c900a0b140c50b2041c41c038450030401038940966000d161480380b00d10541840340200d0324030140e81c2c8141442805d100e640001701c1d0050300954032210009455000c06c010a41d65001842800c0c014038014210100250300405d95800d17045c4002050a81d0005881c914034810380d100c03d000e06e000340410b2902503134803c402580c81d000508240e2040d8500404100900c005100350944100041c26144820349840108003041d00065000c2e80c2540d05c801c106c0c00010320a20888860603030b40c0d04d10100f07511003042140e0071a18010070004c41100d08000b4040800e404100366a8030200808580340d9000c01c625020125040f00c0d8452a080340d9030343e0346c6401100d070300e41005080d58043e41e410099164680c0c1c1050510700340744165 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 52185777 1250 52184527 52184537
    0x20a0e0f0403030e0303070e100c0b09030d0b19180b06070b0f0609040209060118030506010e040c0f03080301030204090807150507020c010305060603070f091a04050406051917070308070c06030c050406 88
    0x207003401d0b0500442c289c1d42c0c003000d0b0510711181e481e15168425840340c00c650018441e0000202c0d42d01081c1c0520417104000810b0780c0c1d52076200d0040d444240e090070705029280141040d03942c00410600179420416440c08040d060700d4440c1121310701410544000d5565544a405138030010700f81c1c0c184046001e11590300140556001e48850005403100300c000075242159a81101c00400030510412a0724028020702c4403049091801c0e05040200c150386401c0554424559201040440c4900d0241c0781903c1d0100d5000a00c10050328003201b06100d04400280407903202080c40c1b4140d01a64032041c803a8105809503840c0490308001107084070301c1140c0040e440310051004c96599403085c01982c10600080c10942c0c0741c90307114401006032106810901c5030840380090f0901040c02c0a001c1e800041c48160b030316990640b03010b00b040c0481d003980c0c094034070900070a442404011804100040046410480c4d00b03585000f541000c0c041c0080c540110340109007000741d1a078400303200f2421103045070400c1d910 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 52187027 1250 52185777 52185797
    0x10e0103050f061509030106032009010305073507030201030b101d120f03070c0e0601050318121803010501050a030f030f140f0307020d091202010507020a0e0f0403030e030307 77
    0x40107a002c04503100c000c5813000510030303080152000d100b03440c06540207022001d01e0b0821130303800d111280f16842603c0e000d2240040100009000014494103888400401c5807000e5405094a924071100e40110702080c8030320902d851002801080b13000a49000381da041c40f030303103840c107007440041104411150000f5031030503e82102103164801034120f05000810081140c4034081c0010314006407019401d500b6080050f0b1501000000708102c0020807608803460741c3d42c640000042c00d0b41c00020800060121790707000e9011400c0c400c1c403040126a103810700640e1a4003504542d106c1030010460790038002d40c82e0070b0002c28a40340041100046903841050102c04945594003280c414180c1c5034013105000d0040204e250010001024203010010556542c0d164030300000024584600ca014000500011810a00201010200d099035880c2c081c24040d586600c43e10114035200443e40c040e8003083e07102c0043c414685420051a40500c1c043d9409011b0246004100ea403030744000d8a49401081250361 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 52188277 1250 52187027 52187029
    0x80106050f06030408070206131502070e0403050c12042303030712050c01060f0e040218041101031a03010c050703080106090f03020f010210050f010f08030f0f1614010902010e0103050f06 82
    0xc0203590217480350500380d061240903408500150040e2055101c00380c2e110780180201e0095001c41c40421a0b180f0041c801c052a282da0000759450103000541000000108511040010400013100510640700540c0e595030b14075103403680c1030045400d120310a0040d42e03550036601d0000306840c0903541003ea1069032003115001074505511000c003400b00d55482d05c5000602c401d119141100410340d01e0703e131440c145010702c100041800034013045603460764080c040c000841d06130309408054030b6003820005041000c244074546903500b90402c803a070540c01e24643d010360561041c041e005252190301c5030039a40e40c0303400d402c2d01e01820324040c0c144000c034200030070800f614011010381d03041c42041c015111810003801c0c01c0340586000310340d80005400c3c0c86004000c12556408941e00030266003000d1400c007c00e480e0412881d00c2412800383d0700c07100200c1d000c0001e034142200d40581355403020040c80c00100011809001c2c0540d108142d000c40e0145203141ea4035402401000d01c00c0009201a01d516075441b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 52189527 1250 52188277 52188289
    0x1209010e01020a0602070b0a1b021f060306050c0d060e0f0a020a0e090f0411031f0e0f1504030f1e03090303020f1b01050705071a042402090901080106050f 68
    0x1103941030451141d070040e9070218980d44010302d101401006803d1642c903000c0b2410741660300d10f40a05a03444480c0098140c40b581c0841c481c55540a131000d4022054014804c200c003510460300003a101c107140c841444150496030004008040f4014000e0041c03540d56030203a12428170841d40c081d40e6010701c1c0c002844e00315aa500a10040c202400c2110b00300d06104045203002c0c501300d585c582c1007417451080c441407110080e0314110f883e00840050040040c0c1417000070300d0042c411034505040d52220340411041509000001d508040d500859004d00401035840c80480030503181500802d03a070362081000c1c07500c11300010200032a0740903003500f84040b4190803002040a0030b02a002c055080c800d90210200c024001c3c120340d0350b1a0080300764031041c000d0103030840e0340142000341445410419640001c440c91005820704940c03031040400f0340d5036406c12242e000d924201c500314074514505002500314065001c3c000e003d50950307413050580e072034843d0a4202c85042c046c9035489041c102007181d04bc40c0003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 52190777 1250 52189527 52189547
    0x703091406040902040602010b0f03031801030b0d14060a0b010804080708031f0618080106050a15090806070507030e0102120d15050402070302010501031505010f05100c020904030305060a0602120901 87
    0x1400c20751030643c0e40d10580c400c90b041504201d005035143c560b81b50b480d00d02142404000d03101207014614004508034041620122160301605150702c0d2065030311181e0320030312a5800d4a030800e042c0126500c5800321503450350011070b040004545002d01a0b0300651080b0344140c42260720100c140d1030710185881e100d0700d82e0001850700394900400e680e52895448601c000c040148595100c0e04510b840d010300c81120094682c1141c0126031510004009a55500354201c048419602000e140038200c074000b220074003019000119507108034824070203a11f0b03002c80209a414041e507115041c401c124001240c403200350002c5c1d0900c2c4402403000f00307050b0340d1903071004900ea4194021007072101c0d40c820104003617810050060380541d6640c0c0040081c85902440240d030005440010070040d1f0401d01d044c4e0099080d07024a03030180d4039528819101c18010700401d4141500180200e0b11440c0628005001d0801200c0d928003c1203291000620f06000003812640c40b10054040fa04150200300112254949 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 52192027 1250 52190777 52190779
    0xa0311030a061506110105060306040821040f06050a05060d060f06080a0b0417070302070308032d16031104090b19060f0306050609010c0b04020f042f07030914 70
    0x2809441800003040381c8120b101610402e00c51480c3e0b07914126001d00502d0320800c4420312a410001000650ba8001c50700c180d100e40d00c0041d450311180d1011941c56040301012803d180100d1032070510052021071108041e203148070710414001952421501c80c1039a905895090300300a880d01c070100003c0301c41e0400c0300705d1110305400041c050381d2101f40d14a00b052080c415a00070705c86d6414401802080841d440303001390502c0c50980707002500d0381d000b580c4500034030000d0a20f110200100782d0040741c01c040307420205080712400c020303001e0603001c48911341d0301941c603507191a14100d21205558081e0045600b16a10341c0c10003400c052901c100b0300080c194000480358006001c023603400070000c0060007500a4a0103990740b900c2900304039005000c860842c1c1200e4480e90052083c1e80b031603a80410503821150740501f00d125581c0703c0e0b10118100e9402c110780e5560103803d205510030700c10380c420203e200e058011022282046410041e240480c860b0b1000038000441c4c2500074408a1000390361850000700c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 52193277 1250 52192027 52192033
    0x3050a0f0912120b280602060103030807081b04090f0c020106050109030803100302090702060403020712020603010902130f171908030c0705030702030102040905060f010807080612010609020f041a090a031103 91
    0xd50351000404074149880c01c0240ca080402c0700c10034001e581740c204c8004d450103000070191135065440240000c00003e02c43c0c0704200c4640002851341c82080c0714002114100c94000d6152034a880c44107000c1c0000703038403094001e40780555041c0c0140c0305002d14000c945041c0c460b0ba0400b070640d194480c02d688010190070b03e42d02840b07000801600c4829007a44540302c1980545902d04107031400030b042c40c1c0b45a00124016251080a80248e40c44200300c0341140c02d84440162344000ca4070030060700c00100d03030041e01c0c4c49610301800a1070900111400c1c44c40c80e0807000b40c8105103601e00d00504030520141028100000a000003005007101c0c200900c0024017507011241041e4690740020300b681d20513004409041d0b1114103011450410401c100300d00482401d00e04a80d1501d0000101550002041c00740300d00d9040000c0c00b01101d080d4070901c09001c030080c1c295615880d4134010111580144502c480749240c2014440c0124202c0d800d6a210306402440c00c01c1341461034540e0350b504180a650164140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 52194527 1250 52193277 52193291
    0x81602030c06040b060a080703120327060c030f050103080a0503040507211109090a060b0f040617060c0a0f0e21010902030c010906020a02100201061503050a0f091212 73
    0x6004100e554403da100f000c4920b640e2403d43c0a000b01003516070b0191a40c0e038440c0c0024000034040d1441e180c00c4110318500012540d1080c4400c0348041c8004054400c400709850490341442156080141c1401864409100c2c40c00500561012601e0034840030703100a1003400041c0c02c261042c00199013181c002c50869101c00e4680101003400340d6420b104603d1404140903039002c000d00c4030b00c0c040c3d041208584005040c5001c0040300c2c0c4900203030034000d110f82d5a071134100c0400c0da80d00c11100307100c0344041d00800200b516259540c507403220b05500312185100389030000b00c3d44601082100c5a03800e0541d07500b00c005d600a40140c503a046500354003988034440303610180103050002101d01441000400105160329140189400c00459240b0a41000035120080c00580d800207800e9020035810b07260240300d02c40408040303004040c0d9402c50360784000f2810910064230340c0744e040701d1301070180240100907041c02c12034580308031303444868000d1a5507481020300329401c0c0152411021818560710100f000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 52195777 1250 52194527 52194547
    0x5040b0d1d0a150b010804110103020c0a0303050103200d0b06010c060218010f090b04060809031204030f080610140c0c090109090314090d080f040509040f0b0f0708160203 75
    0x22541c0c032024401c652180a80500b4400d0704403e19991001d01c40c0100810481030300002e050b034400030000b401a0307008240480444c1d1182e411a100f031800b1506980c2e0052052074001d01501e801e210550b020490311000d880007840610303046000d40e40c01024000d42d8166940c0d11880c0e404000c08080c180014000451301140440c00113204010140c4400ba0000f800d4200141899400d5103d0204002495500f8403035001e031403003200c080d11141d06010324a81d071034a18161845c81800c14140314070500300140000c26400000e0800151040d450380c17042d0b6500c0f241844002d404c00e0805400141114041c040310700a4030f40104000c600d21800e650b0310b0402d200204076a0701c0c0030782c40307410f40316952700035041030551148601d0030382c10066450a00d0310403d440000c02400c50490081c008080000e250790320305c41070204440c000c0c1400381000b9850f15160a043c0d034140c21425040d00c403545403000148641124102161250509132201082d0f42c580035600c4840c41c02c80382d100700541c4000c10030210f01c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 52197027 1250 52195777 52195811
    0xb180d0f1403040807050120180a09022101060e0906010e18010605090310020403020f040b0a0801060e061206040c0605030a090b010b0d0606020303010806071805060304111c020105040b0d 82
    0x3c102d001c1e20030030b9034419a82c40d21a0868403814011046200c1c80b42d04850700e80808000c50b0540c05881d03002c103e104642c500000c05c6041c0b60b43c411503440d0f00c00106a240394442c440a085c0c3c0036455881c8400031380c0d0760141604c1103080c2c402e04030f600459180c00a08550301580d184043e551014002c0080d41c42c5a00681d440f034002a00100d01103500407600545510f8204030a007658001694154107103450341d0b0100790300c0400501c08a00ca0b83d114101e4101548a82c1d02d204000e2000c0c10007882016603900f0344804140040d20028010300321418894860100007a090b4011076200710401c0d2698a42602221036800140c4841c0c45192501205008030b00b8000719203002c2d04070b0118681d0f0b07a2940d031071607108a03185544031000395042032004000000c40801c0c002d030701c00007500308640c83c840d100d0425078105c0700b5500050351200d4044280424007050380004a002c04050381c42d1061100c10005c01401541c864100030b0004800b04001d005403000b40000e0450540382203404201e0002451420131 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 52198277 1250 52197027 52197031
    0x807080304061e1505010c020321091305010503190816021c0302060907080105041703150405090102120c0c03071b030609030f230d1d01060b070b180d0f1403 69
    0x1209480b0780130010307800c083c068904010207013421702504030741304c035408030740c480840081ea080161900c1a0b0b603107500010398101c81c05020010001c4580c00340301502140208802e000d128003074850040c40d000700c201c01d40c603603031142500300c50aa0b050a005961110380c0310440042244c02122000b5880c507500880515060700390b00c070360003400c1c041c0f401002c024a03000690303212141d903070304101c00d0202240304014400303d0350303404a0b540d540c0c0c0c0c4d845101700d04201428807820f6030498a0401007042609040d80640025440d28407807503256201c0307194000141c01040c080b40020f070000c0000300001003074500619480184101c4581455031380b6140c403011204081010360210306103020046003240c0c050646201c0b484000a2452034154402c00007555010304030f524100c0710b0342ea1100d01a00307813031680b01004454006009010b45619035100780314582060708122865210080030030300040085450194115480c030042101034a100f108a0303a4969900b000b506205103da00700c0507035102035000f54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 52199527 1250 52198277 52198331
    0xc0204050901090213050f01060f0c0c09050106020f01060302060301050d020d050609011d010228030e011a030c0609030307030c020d1509030e030606010818010209041b0813080708030406 82
    0x90940303d5801400820125807401e25500c2e440d01041060340c0b4000524581507801500c1c0c0503030940f102903416103101145000c081c00944642e100041d8110554111038140c0f15150b096500045c54003250740c1c265406400029030080c020720041c417942c1084141100381030f0000f0021a444036181c0c0718681054010344102000380d444c1d6034a0007000034070b1119400c901d44920001c51503c0d0000180c41c20705000855038248026030845103188281c4203400c980d4940942c07400030007403c96065400c00740ea5a0704021607021707009041c90f40c602d915040302920300b00400940990310313104007580c00700c440c0028100c00300d0b40030710203040ba5408100000000104241c1d60f1500040720402824040c104428506225120380c3c454000c0201c581d0740807000da604402d211880c3ca0b4518624600c00340039020f0403900c47d400c030b0b103007064000d0650b5100515100450440d103801102c0d44902901b840504595000580384070420092500000c80d400c0095034000d00440340081e1031030091521040c0500e40e000c1c81 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 52200777 1250 52199527 52199531
    0x1140d0b0319050309010305060409060e070e06041e020c0111070602030703050c070f0b04031112070b091501031b031523010501270e07020303040c060e1305070c0204050901 76
    0x32003581e09040000700000c0e101c610071020340e82940d550f000d507284140c100700c40c101138613400401c1c450348440e080030080f00d0f8030100074450401490b4501d5642d03081c511503801d6100080c03001c0707009401c05200b07400741d0b10101605201140d070f11203401000b960250b0140180c0390344e180c41140500f207030900945003041c400e180c0542e80e41402400101550000391522142d010100076030b0b00025000a8600c02c0c00d58440d000c500981d580782411303981c844120300046001e000b4042c0034150345032001c00a04650344510b003030a6094640310f01e52507845c032001a820200920759070051020801c80e009603d134400e1071022603140607859a035120a2250030040d07080d03500b502d50180341c2d01d046140c011120301407032203845845039625160008003842c146170f0407036140c045803440c50034010303610420b802c0c00b42c040602107620a0900b000000d580e076208403015554503000380c0c40803610b14801d01c0c4104881400404032803805581034940c0d401064082c0099043c41448502c60740103854a00400e44184404000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 52202027 1250 52200777 52200791
    0x507030b07110607030c1728020703081311060c010908120105030c040b150f0405030102070b04020126010e07051b0d0f0e090406150e040506040c060f080406050601140d 74
    0x10b030350f1070401c01070502428581043d003540c0405074001400c400383d14080003603003030b46e40741d042041c4086031000c60520407640b4042d00050701504150000c00445100b030303442425076a910414600d06110380c0c20000e1a840e0341030142080b0746081400b410500764260000075400c83c81da40c8440080d0700070741808a41c5c42c216001005180307420f003c1248e41500580c0d05002c9080d005000480105840001c0d510f02c6c0300100f58525690307038039015a4003170300c0c001e0b00856640e10b25050000c11540b040314128005070498504440c42c405407200c1207664000100c0280302a420446014200c00c0020012401c02c002800100c024401d405c02c0d9610382c080040c05043c1c0ca2804040c010203c07176003081410144900300007040315070b03111001c0a80d07010307130000c80004400301400d000d151141c0c0c042d0b2100c00200e1a441c1480103011001c11001d000d24843c0c4800b6001554404040d10144405c25550f808030725902d001030b0219100e600001e502c00e030145400c0b9000100f240c0c0c24a0030340c205d030324142059507407100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 52203277 1250 52202027 52202057
    0xc01060806040209091c031104050a030b0f0c13092a0c050d0e03031803010b060703030b040f0e0a0201030b1224010812220e041128060c0507030b07 65
    0x1143ca4100400d40090310105030100045d032141b418041d0840105951140c031498140c503042e00780c1300502070041114050716a01d0410487e5940203442c0e180003400c80d0004202180303400411200da0400342d44c02e03240300307518001c003450041a200c524080c2c2d2260049042001c1a000f105400e640309580d10f40c0b0f00c1e04503203802d103280350002a01c00c641c00d0040001c11400c1541d00001034621040c006501c0122240c00c0c8400f01c0c1c0580180e501d0b0640050000c1401d50415400d904085140d16080c0c0d003c024031540021040242c403441c00c0184005c1e004408000090352098011814400010304060f018810f00508903140c0100c0310440c0d545401c88028003503004081301c046134010800100208800845130403009010300c03038101c0c1d440358031500c80c1002e000c040385001c02d0002040c01c01d00010440c641403e11880d407011906002c1c1c45140482000e559003007150703264049160000c0440103647d07041ca102036405e01c01901059500d48500e00700040052984028140f040c51655140038044100c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 52204527 1250 52203277 52203289
    0x9050d11030c0c09090f012c01060303090501080402030f1b04140403020d05130f031a130b060607150c050903120306010c0b060111010e0c01020d050705030306150c010608060402 78
    0x164031000640003049009141c0c000003401e1070721028211000d0025480c3c00125030300d003100e0000600c0302c1c1e5091514501040c07903400047d0040704d442c01c2c0c0510380c0480b46440d850072500c40d80001004a4500e490500c0594170400100e6400742c405406c8541c040880414603140000e52000707200210050300f10001c4500345401541030300f80100416a085082c80e91380a5101d40202c80100100200425404942e02000180c803004240c8041110f459684a040c80c01100d03010340b11002050500d03101140c010310580070030511041e08030080011075100c0004001060b4090081510b4169544280301c1d00000640304441c3c00c40100d4a45959910820082c1424400c2448401d03e001c6801d03c20441e207079130824001c0714840c3e80050042c0391036032800c0c0140e070000303002684211a5842c0c030200265031003000031880700c801d200341c00311403da40a01004035401d21445400600c0da804c140301007042d5081480c03500000101ca911010b0506a14005403802c44425600c00c2c000c1c2e51001090100f541404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 52205777 1250 52204527 52204547
    0xa0b0103150e0604050705010503040812010605030402120607020a140102090303030a0501051906020c0d030c0b0406060e0c04030809060a0302070f0f0c061407020d2a08060606090904080d06030609050d 88
    0x8040940f050b40b03415191582c8802c0c1c14440c85050100002c0041c080040c010112034800055090380300c56543c507824010080e400482d0120f0003080b11000d1844140301c009001813184c50150300910200b0101c0ea03e802c98000380189400184d9000c0c800302070ba6580900165100b441600400181d030b601d444200030b0700d45006c0c2d1a4000015000105000c00c2e40e000c1105202a6800c0d00d45503005c4080d4070701210240c031401030142c2046e030400700740002c02400360840800c98280c8255510107456007201d500c0c00b8031580c8402040d0100c10003d01c200c50402801038881d03441d490400508100381605c03000e803056000c40c2e044500303c04032840c50080040418944014010301d181038203c1744000d075071142c40c605c10f54101a214000040e0b60208001110614260a00a55400c90740c400410300150102040301d0207200107600410000440d02c0c10700406a0b091840028040c80442e2560b480f0180e65038000301d4900c1d241610741d240400802c5840c068035035154440e0300101409000c20380d00030202592 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 52207027 1250 52205777 52205801
    0x61701020d11040b0a1107030803040f0c06020616031508010e070608070f121d030c0d11060c030103120306080312010e070305090303070302090102030705010e011d010501061b02030a0b010315 84
    0x2484148102005007050b0f820034030070b5091841c2c1b4402c50380b41c0d440ca00b0398994030060011000100f088104105520b449005a126400e0020031580f20002039071101012907010643c0d0294100c44400d035407194010030441041d031111096070fa500da4900e03e003076032200e4000d03155681c0400410402d896004041d0307684100249000b4050440c07041d0010001060070016916554651141c000481c0c01c3c02000c0340041a114112562071b18400816910741d401ca01408000c184038031f1a101070a00b020032039074800c004025240e850f6030308590710001c844255a81e81c00416540c1c2c030010581441c00c200400380610300d005408155032604115610800303005100c98101810601803095501000051380c1d0011250b060158581c400307400102c0c81d5000320103001d0400c0d8200b0b0b0705071400c0c14040d402242c112810070344008400b040c0c400ca02c1d082c0c40c1c0030b1140c90b00250b501c60488085400010382000741c148000c050b940842c603281c44004500c0ca081c0c1007510101440840b5200c1d026041c41118480c1503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 52208277 1250 52207027 52207061
    0x20307090504020f0d060311040b0a0503120a111015080109050d030c020118060203010807050913060b01090806070f180806010e0a06030f0807051e1b0103061701020d 73
    0x1a1912008044444074822140125004294091520010030a0305c160003184201080500c0c4d50b400c180804002c0f251300940164070304924000740342882c1000405851014004090304880c628042000703030b0081803041c04102e51616a241c8412003030003a101072001c071400c04100c1c160300c40b4284001080c2c1364802c08640c2c3c074002c405030020b00042142c0c010b9030b000303090001e0002c18012050b4050b102d12208008856a00121241049070b1a0b0140d810394540700c04440b042c035218024480c40c040140d0b01c18400c400041007100000d0090f80280d003010394103150503044180d071280310b1813501c0d0058071000c001c20b5034403000305a0103900004980c41c020515840d00f80301d83c13810b444540c07244030601031060700d8598100003403004883d03504058010340e03000002400c01a03050411081c550440e00044420303028082c40b1442025040c40b28007020200c01c0c0143c0000260403800d41c410454804c1c505060503100c480c001403c0f000104642494022700c00003503074900c5020501c0c0f00711030f0050303401040300c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 52209527 1250 52208277 52208281
    0x70c0501030b130e01110403060f0b010c0c1710020a0c03020c060f0706050c040f0605030109060b120f06130c03060509060910050913050a03120b09040b060d02010e030d020c0907030203 81
    0x41d641d403000741d006007003030744000481100d400f40c80c41c05020a810b41c5080d1b0300d800100001000b041b0390140c00c2c2c40040c86400c020f5102e205004554010102070050320b0b0f4410a1418030503200d95043d155250000304003100c00c12405d2409103001e07604446040c03000705038a1009a001c2c5a01032100d1040204101c500514000340c91900350740a0080c078070041c1c0721540e01d100050b0844601030840f40602a01c0030009401035480c8402071a582c800d015480340a800e100e4002980715440c0155051014240c000c01059500d40f40f490703442c0f0078000c0105904c08050400b110440c0310900c9070600380b850690700030848038100f10510916038030142c4098041c0204004109180803035028640c2a100112001100f68641c4044031560700c2c0c45e580c2c09000c07402000c1c604d0b0304154000031061945002140c00744402c80001e0200b08811908950292444251200181c2c0030300c0c00c282c80300615403050400c51013102492021034a0034022280c880c0141c1c1c0014901e038038514040c2c9801d0f274050603900e8254558 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 52210777 1250 52209527 52209529
    0xb0603060106080a020717040b13060c020315090a0f050705040608060c030a09050a050f011401060c0c050f060d060b0309010e0a050d0c060207081218011104030209060d0512070c0501030b 82
    0x440020800380c407107176022074000d0030050509141642480381c0c070030300d1f42c496869240f0741219a000103055003108043c020002442e601a0480403005038009020b4119039410926000315188014904a0383c0e02802c1180c0c40013987c040480c5503591f0040006081290521040c44100d034011703080b81c2d40c9540078400304001000c0b00c6007280c0d4051080c010125080b02c00e4030300a8a45803110f800241389000c1c0c401480722070401588401100341c0381074400c1440e80d83e141003d95030805c440401030f00344c285420080c041410019561070300e4000c007404880c5041c00d0f4803407140807104603810a40090344000309205004000b4051403141c2c1020b04040c044040c0c1c9603940c40e6071441d0100245d4140409441c1d10030034040c080d41034800460b007110080c0e545000d0000c00d040e881c0b500300da19010056000340c0d4510500e005100d01c0c41e10781e60070740307185140c9402c5400b08000c1c4d10004100603440459402041d00042e41440b43c198480707450b082d115104d06041c50302c00040d0440750485410185400710f05041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 52212027 1250 52210777 52210787
    0x102040308071e050f1b09060904030e0a09110c0120070b0703020d0507110601081b0f1311070605250c05010e060702030d061508010536040b0603060106 67
    0x4a150710261a0b18032003240c5400d00404110f51401401c07a018102001d41c810001107030a0034458480c41c04691700c801100c2c10081d89040543c1c8603500000c407100020000307030040c032005510b88801084e040c0b686a5030200c41c004e55403400c0b1504003d00c80460f441022403401d004d007481c0d0310381c50300303554252420606040d062809820005080d1a80000100b0841402641214102c403156036003801503190407034000c0c00140c0c2c0c0280c005540d03c65400001080c59010442c0881110910903007148401c451080040e0284852006c0e60f000400011400030240c051080d60403000e0b018a140d5100e120509241c0211480141405031491194203840c0c103251801110031400200c9017040302e043d80c03880c1029401000842d0701d1255901c141401e0240c2a60000003506046007801c4090000c592142903002c1c003180004040c0010030750306030050042d481c0c0b186055a480e2000c20010455940500009540350049111140121801410720042c04141c0540d558020b0094005208c41e5140c0030000f08 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 52213277 1250 52212027 52212037
    0x171b0703080c1309090308090f0303070e19060f02071a0d0903030b090f01081002160311030f03190e031e18030106030501020a0908070f03060504030e030d031d0102040308 75
    0x801c0200c0c000016100303076500070a40c1d0402400342204103200d52a016980b006003c1068143c010905140000d24a540300150b00c64000701140e0145080d500c0d00001a84c0d08400c04405d6139010f541c01080542c01000355001c1001014680d0f5210304400400d60041e04007001d82d04000720800710038081c100e07581b860788212105045c203d41c0c0083e610650f810104c004086000d06254041d5281090000b85040d813103089040e01d2412007500c40031070f890b040d40812480b03030301c1d65440c244080c0f0090b800800e000e410801c012110102c250380c900b05902000562642c03046404141e00200c03200590b6180e000d0340704103a80308482c1401103141c0b03105003900114400030080f40b007001003030000b1800707080c01880c0001c1d00703200c0c4050002d000c40c40d00e929119000c3d41140c461200081c015280008820100040c071000300d55901507a4004a03055449000c05000010019810320041c1202c0d08600c0c0c50802c401c0040da000c551b0000f400c0c2e031043c06040020340005010000e980c0c0180700c14400715161008a075 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 52214527 1250 52213277 52213283
    0x3030103030813050a11013f0209031905070f081903090504020f040302040506150d09030201090c03080304061103150d060e010606050c06010b032e05030607171b07 72
    0x180180d0348040c02102c0003c81c0c1d031001010b81c0500b045030b100f0090b801041000ea030300241c072400f1801c4c404a103034000411801e1011481e00326410307020511000c00f041005900004003c001d8580064800464505401a440603022440c0300c900031040c0801070111030007404001d0710145185142050840d584c1140012503649103044000b07a004144c003c002d50320040c0b602800c01c0d9200c51100428070190381292005901079410500011021b2600a01064940149000b22030600300816200340081c0200c0408500b50340d40c48003000c0224052288d0003000b0b40c4241407095036880e09240400036a10a5041031ba0301c15424410300081003a070014920b029001940c00d6224000c8a05000000c0d00b1004200c0340f03194079142010030395070741c450000c1ca030801500c0111030320369a80b080d030420340b80701c110f9001e0503e000800381c0400115075020b08081e010407582e405100700d611500001d00340042500c2081c081002d101d2800d02c4c4c002801c44090303000c10040d03064a01c55607550321006051050381001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 52215777 1250 52214527 52214537
    0x2010e120c030d1205090111270904060615020c21031c0203010f080c030309060c010f050a0b0f040501050a0501031d160302091f0b0c010e0604080405180403020303010303 75
    0x460420300e4100200c0425003001003c03110300300c0f010800945807112284860204c2410200050007880050042c0200005003401c5607242c103028504254445402094520b03803002a1039207064143d6940e4513050007640100800100c4a00d0400c1c01501030107528002825904005e1003c241580c2c1d1407802004440d480d12095284502d40c200207081d40b1800c1400d240700f2081001c5182d141d0040d034083c6040c1c840b682540305611791180081c95541c1c084c502071a6050b1310802800e00e0604008001e400e13500c02041c0045035582c1604031480584038111040b40002d99594281205441c05041d01224090251010084c1e541040080b4600500500840341899210300d030ba00c81102a40c5d500c14049501002030f6030b80c1d084d100d0350a804104180c44149d1103003403040d0100705185240e020215070901080d030f04150b268500840700d5103641102140c80f095550384c4c40101900340040c025640300c0c500c20384042d0796807810402040003003c0c0d280020b81c040300300c3c0c00c1000b00003500041200d0540e41c044c103007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 52217027 1250 52215777 52215799
    0x1170a110f0612071701080d03020d0615020d0e0402090109090b060c0a0506010801060b090108060d1b090b040507020102041512180305130501020c0a12110406080303010602060901050402010e 84
    0x840c1c21624003003411034000d00e001600c5820821003d40d240e00848250362400e400c3e4140d1101c04002982c20700800210340c000300c102030b20440c003030350080240c50b540c12000306805595101c0201d1250702d03020f505000d0b81280f82191592030780054880301e010b00c1180d045080c02943c84c0000c00041c01c2d40203884910381c0c0d407410015650303903103000d40e00394501e04022903d00407040e1600c261190404c3c0b24060083d070a200303010407804070706403d03214904410b0b510314190380d41d1082000b012141c10b88003510801da0303e110301c401a0000b60700a10140c0012100859506048400c2c4403c13903900410720011a441800188044044101c00710310711080303071030190540c1c00b103140c0a100900311b0310000b0f041d4401d410503c2c030805802201811106610321081501d0035a0b031001603840d500140304003a4400104a81484012000c1c414000854015401e4040072038414002c90104d95403900409150f900c003000400070541d0400189501003a080004e000e03030f04156001901402c800c031081d600c24542026 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 52218277 1250 52217027 52217029
    0x18181d0307080d020705070303021509060105090c0702010c08040605180904020603240405190c020d0e060d0e030a020304030209010801060302010e132a170108100b0a08010e010c0801170a11 83
    0x140c85e86150440d0a941071245c1d24079001e540c860f508204515040030101c00178000440c0401c1c410304861018202441d2559400400c0c042c0f50b01001041381030010810944e00030642e080b018001424070b6032209aa04d03140c2d8805600b42c0704403415a035200d88844010440161956801d603030b04030324003001d111400341c1000c409020032810403448640151a1000f00180075401580719100f420314107070208241c0051110407030311100d1580120740441c00311001d603a030f01e003060001012850361600c130020321075856114560940d030010f5440e1005a10108040c810340c9040854a401070501f40b00130041c951860740040c14403c60440568801c84001405041034649030b0082031031480c1444580708e00b041c0500d141c0389421080d000c032000180c0c0031004041d841424280c0c81d41070f42c2e0010b00400203e004a110071000c3e040102c04140c011a110f07100144003c1e0074001c0e00802c52501d8004144900300100c014082ca8050f0311013802e10a03441040c0c4030403030011911541103600001c0c07040c08544408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 52219527 1250 52218277 52218281
    0xa0507080703080712020304020a03080a0203040915031202030a080c1c050703050a0c020109031b0f0f0803090606010903080d0b04021611100f0206130318181d0307080d 74
    0x89405004000001141410076500030301d00c0b446296a0b0726200204640085038000f00d00040303400031f400000c0381805001066880010340f501c0a0548109c9140ca622414142d00365080d007042c5200d07411141a0520030410600c18000100c4d070307148011400c20714050401842e1040260082d0101c400003e5014503112404100c0781303074104001b00074801030030641c10080044c0811a00a0141e61624100621051040c000c40550342c0e01596680c42d40d070204807110040006140b4200c0b100216400c2d81c0c1d00080d40101500031450103084440d4807803034009001824100300034012410071101410600000e0048001d0761410764101030002882101c001c0800d000348902c2d0440e440f44080480c10108200424146412913202074928900106c00c03020300f0b40301c1d6520441c3c041d0260308210000303030350a201c00810202160084ca00040c405d40a2800c1c42c2d075611094000e52642c601070344100740c2c03540590040480d03a594202d2034041c0b4201103210192a402040c0008102c0000028110b20940d40b80d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 52220777 1250 52219527 52219537
    0x5040204090218091308090a0e0906071e090303030f02070b042004110d0e0c030f0706020f03040f15030204120c0305010506030606030607030b010c0c06030501030c170703080d1803020c0a0e100504020a05 89
    0x280c207909d8940c1040b90400c4e5490300c04444010001e5406183e054004d00800c6010342c12100d15200c045c0218159602900030340200301c0c01072403896092003050080349000c14024010b40c02240c0e20b107040000c0c40003022142d11614000d0b4062428040c2c07980ca4000040c00321031085814000000702814610180c5081084908080e5810b1103240308480a02c000440c8020403940750b42c08884000c9a060000e50f1a8012441000c140a802807410496030110748444420341995250040c5081e4455031200e492409170b03002603d158450701030174002c0010911456400c40412801040586001d0300003d654200040c040002c064075803c00c0032059000e01141c0e0b100e15442248640f020303407070b0200280100030902c01036841c2c16245100103503049100445a10081441003c0c004c2e15056845402c001d9002c1040d4002d070941c1d42c031030903e281100d1911444c80070310913406800010450000c00c194400e140e0440b1101032184024054203440c4284c9410032240e0550740541c942c0020f0500350740b0b40c014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 52222027 1250 52220777 52220789
    0x60606030703020c0a120207080709050f040615121109090109050c010e010309050a050105090d09080309041a0618100e0a05040510030f0804230d0303050a0605040204090218091308090a 81
    0x8410b041d81b04454001c10700d07001b9540301c00201d86407555122000400da440584000413a0036085001c20085a269041904404501c0442151080d61041080710f4071301041e400740c810040a0880740440c0c9401c003506900844041c0081c00b42d032015444071901e0309080c149442c1031200c800013036101ca074002e401070414190130005440e01c0c14814140540a054110380c0500d0b5802241c07c401d541c1d60040c012001603c0903074000b075040c03082c1002480028800d1501190500340541c00d415865038943d0010025001a0f0764044481c20f4403505215440710b0408031a018850600041301960b100c1c0140e0f078044980844000c02c080d11950703101070b1420341580005d09800050440700c0240680c0c140100b00300c0b04107501c1c09480441031160050300015000c0d24a07444850207100001081c400e8000c5500281c0240001031150354903030008040740c0c0187c0c040381001d034001c03560841856500141c3c031104802a2130202030352030300400d0383c1d031344c00710040740107140d0b4a0100d460401c0c0e45444102c000034001c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 52223277 1250 52222027 52222043
    0x5030d08011d04021908010b10020a030f0305072a05060906011d060409082109030f0403061e0e0d02011107020a0608090a060c0305010509100303020309060a031103040c0314060606030703020c0a 85
    0x10b241d60b0a94048c0001462040c002c0e05403110f54113903075200013030350098550542e890b1503075500703101011409414003424480c20458140b45810420703030790500796903401d01044080b2150780341e5403424504064000780111403e8000d00010840320800d83e902c09a9001c904e4104c807401e6031004005401015110380240000001082c2c4480110503d10b8854002c00700b40c0010003a075494408080d0350744541a1030b60f150510602c42000000d100da001001050041895114103046944240c81166400003580a1641c091448001002e80a00c01c0c40340000d620b120340740c604005900414407001701480f5550410190300000b803400801440412070155001c4000c0c8810003a00c200100544001e01569100c3c00c420801708622040161103001100d90640281d42020751040400c072158200b880301c5001d0503150200070320050325990045228074411103c00d6207050035410169150740395040c003040349502840900c5240e5031400180c941c021800c0c03501698440381a04a5420300103c40c0005241017 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 52224527 1250 52223277 52223279
    0x21f0609060b030f09010e0a0204020703030b030f0102040603060501030216030e0324060405070804020901031205040b0705010e06221b050310050403021002090a03080a05070b0109020405030d08011d040219 90
    0x500a0b100640c060140040d60352200c5c0c40f0390400e0340c00c031142081c0000d8594042c0d0400c000504098002d44401c0c2d00a080008482050401080c20030200c0364003e01c490b50700142c10300002c1d41600c5410050034082c6000c50030300e0700c2600fa072159108400c0001e01400002030f480e81e2540e90411200070051540c00d1300c000e0013410005d04450780e0308140c604c1c500c5142000c0008481510074003015208030380080c00a141d5920307588030324455000c0c01062504000c020000030800c1c1e52040c00130300c01031348144c0c00001d00b518404642c41c100390010b00b511414801c0300d41132100c510440e0b0814000150010200c04110707801c041c007512880d005a0202c0d030140241ca1500c20403000035441355107d18001e0302034468501131002c08000301d02c1071020f13443d03010340741801c00d00103d218034016050540142c14440d03d4901523458001003000240d200b031091a0f000201402207013014020511108810304007048594141440c02514400451000090300740810021b020755855407603131000c01c036110040401d61 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 52225777 1250 52224527 52224539
    0x1f08030a090501080705120403030b060708070c0509040201050a050a0c0606060806011218030503090c0a0305060403020705090c03220b0c04031103160512070305010510061806021f060906 82
    0x203600300c0c4640ca008240305540008203540540c03411442041c859440525001e4207150b032001c404401f400c00d40070540d54600c040c02030f0b16800014142c02c0d00907000320b5117a00c2c892904480c504020381085000c2c001c44020301c40141d030810240d641001007414101c4c0c0768001038500304c40300b501007040a018541000b41c005042a0480b6905000e80b10a80e80c0c0c8044000e441d0a00c82503c28000031042e80d014a0307442e075004079104030003468002c007110041e22440103503000041c0001007540c01c04e480c150004401c2c0300c1095010031003035000300700c10354403415285000c1c46a21114080100303600c03c04581544005c1e041c4040c0650101c0c0c1951240106816007004088402c498016002c11280d0340c0600c481402e60745400144110301e84013075010454880e041400303001c140c00078505002c0c5180315101006c00011002c0c060a803082000c8806501400c0c80e0000040a85000703508000401e80560401c1c410345a0116030b502e2100d00c3c44040403014404900c0000003488a82d101b1046689400004519 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 52227027 1250 52225777 52225783
    0x4030c0b0c1c0b06040501030e071205010209090106080403080a09050f0d030c0e060405060a030902120a080325080f10081009030e0909060103020f040605041d071202090a051f08 78
    0x5950000d0008400800004081c108903010f103180c0640c401401e00c810001c9610a030040010410b030750050741c24135595014080404a41840210340c80d94011a08186505001d400c050041101d07182c4076809050a0700c01501100000c2c10410f042500c422070f81040c4401004041c4940d0380c09030403242c401c600c0702801801850722140030000509405035034000e070f243c2007040d101954030003801d007850503034807a00a138005d150322081203800c64442c03240d01e2610101400040e01d01809480c16654924003050700800010b400d481c12802c1c3d40ba44000d10003078640c4001c51652045034044140100d41b00c881070100000d040707034014681486242d4a02e1a0200107400000c0b6140c440d4880f90300381e925802c200200044100c9030610941d1108004002518050400c52840c01014000081894440c80460306030781070420440c2800003076040d0305489140400100300100070854809004980301e5001a8200d0005812207090940701d801268000b251100a80c0c10030485480034090182d840d002d10351 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 52228277 1250 52227027 52227037
    0x507140606040b0105071703180703150c0801080616050d06080a0b0c0f180a050603090d170c090d0c091b021204051c060618090203010f0c0e0904030c0b0c 68
    0x2c0070b00d0400000b0b04195000d00300360390b4100e0784401c0c1e0b10107040b11400c000501d03420040c8601d1041c101c00083c00e6800c00e043c01054040c0d405180501080c040701c3c010740b07003030765400ca03101001c0201e030500401280c48003294032a0030101c21f6143c10011209108201d50500800d442d0500301b516141d0009110300f800200001c0e43c0e4480c00c880c1c5183d941e001e003401c0d014098910700180980381000340261a000c0304191031a000c10007042030310ba0f83d40b030300c0200324180c00844200c80c3c50380c010840b445490350403502045c8441302040c0c00e101c1500c1d00c900c0010345030181d21411401a410f03100007900b0814248100d00240415800c1000256868134100c2800307000103c0e00c90141c040c4120503507141c001e040c100c6013900c4015040d5031107804004442140401d00c0201921000d07560305c00030801030103860f90007a101d41c02e40c0d40414551340360300401d030131500004018012640b9120349034072001d0b00658a90020302d0119003815032561603080a49110126400050409110340200300c041c5102d903000d04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 52229527 1250 52228277 52228279
    0x402210105030102090d03081f06030b030f0c1c03050706181a0103021c03050c0609070f0e0112022205070f1704020306040b1b0417010c02070605030105100507140606 73
    0x48400d980e1001403508038410500c8079600010720a40d00000b1a00807005030707070821100e848402e80b0035144100408008980d8208030006038448906282c0c502d4100300141da0002280050700100c1903123000598076100c50341c030801c03103c10026511410305001b60b0907954a035801030b105200030782051646214002580d80116540001c038101e01c10080344030038103a0b05070bd0b8003409411000c1103900172200c1d003c0160800724100103081003003813410007051110728001c0244200401c2c21608007401e0448004407500715020704070522004100300f2580c128050025038050303640c0014141c0294414840c6030a401000c6812420300b000d100031541e10803880b80c1d0350001595200c44c81800d880081050704000d403070195142d80000d02150109a400e81c825811900d4061001d010121004103011a0f0b00540d001020145840007400d82c250800e0143c5030804c10144003802c44181091000307095400103010300e90250810441c00480180140c0880d8880c94101d079018600046005600d59212401c036041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 52230777 1250 52229527 52229587
    0xf150a0323060f0c070f081c091205071109060102010b1002030403030305063c0a08060103020405010b0906040308070314040e1005030106060e0118030b0108030d0506060307090311040b0402 83
    0x2410022203d064107009079071410140d46010100d49403e405030100b404140d5070382d0410401a103190644169402040c4100c41020681007003c4c02c1ca0100344108140300400c0c0203040051200047c240803460503076450072141c045540d1141d01c0100c1c0140201c0788220380050a01052103400340d00000504102e078801d40d01401a0381d00d00f070030701c0341024810b80c240341e003540008810800d4042a142d11001e030220000900445c0a00000103403a00307495502610304e54100400600641c1000e00841c1c2c090402851020700e41443d200c0810040e100711b22010b040800c0208502e82010320a40d04101030002c0390300400e440301d848111405030300005031011044190315280000d09428103000d00300840d42551580c094801140300152998220400c0c00720380c1c1c84020901100141d56408442d020384040e0000f1a141c0c07861400c2081110741c003900840c4144410b0003048230075070340801c0071016254401031034000704ca070001c0840d010709209403805601a0021a0140b0010100d0f603907605482c2c01c8504c0c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 52232027 1250 52230777 52230781
    0xf03010f05010504030b01150c05030f0904050a0c0c0314040816090c0206070509150f030a0e0609121b0f06090c03010f06180b1c0602090f01080f150a032306 69
    0x10f4586128070b100043c8003010100c01000800d60092031031011440034100245109412365407281540d00c10440c0300760702000031076201150304181c429160b12403824241000740c2124042d0103800e14981d0907000b0b0030003d0918080b501c0d010140280c50050109404948001c5640c400a180b051003501500b44400e1038204680b411038400903503607000398810f03110146400807582c14000e0006007076030400d031409400c0041103400301d40790000314422606110001180c005080c041810480040c090350a641d00c4110b0007000002003400321100000054298200c15a42c03040c1c8608140040c0c8251340603014100030030a0b101004100414150000c4008011103003035648890100d50460007140c460b11408008405a40c42c198080350b520b04008003100401c034200400328002c989040800c64a05da0042015050380c00c00d01700c400182042401d00303a000d80342a540703a4540400c014a02c8a8045503044250036540301e600c031410145400c909580c01182041c602c1c0b01071500c80c1d54084506100d0400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 52233277 1250 52232027 52232029
    0x11070f03030e03061506090409020a180e0a051507090305011406101103030c0c0109020d06060302091302010203070620040305030318010509070b0705070b0c0d020106051c0f08040503030f03010f05 86
    0x1684e58030543c803484442003034203030790824030a03140c004244954003e41d40d40e0300c1c42d0240c0d440c000c02d00020720400d400b01e5001c0c4200070707181041da01041d8404010f644810020400541c000c1200300d140000420303c120581d441007412100a0100d50001d84294a4160b0142480d180c600045105440c1035a422900b807000c0310003101d07a800114400c02498200f8008200d800215000400400700b0ac1c03000071400b107900d90001002000a14000c589082e6503603001c0003103042014056920119500808182040940000c0d4030b03485100c4000304030320707500c5000821813000c41e4000c2402c135088030b200544490312840c000f682c3c1d510a07904495030080e14404c1d900a8003050141c14420301071a400f9040c00c0f07250000c2a4500d401441d4222004e000d124400b2612060a601800042120070000c0c000006404006801c6402030740240340289140000340903140901605000d045034880380c0a45036408a09245003680141e800c1250705000c0000c140401400601c060f42c1030301c03a07154510480c1a940c070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 52234527 1250 52233277 52233283
    0x1804060b09150109140303071208160203120705070501060f17070e01030807030807020102040801020d09060c020c09340f08220809060d060902030109060902070f060b0111070f03030e03 81
    0xe0344140010780d413090900002c3c40c41e03a02094a00e40107012203080c03c038a907448104080300300c260760340064001c5040040e02d0701420070724030f0075907030a0011f03515010a280d04030607031480c000c0698080c45000101401080300035070280c0010305040c00c0311181d0545882030300c1500d0500d44815a02e52061010205100c2d9415509074100c039407004040746483c0c400d03039055407824030051040701555424040000c07100340c02e00091941e640f00b6407000581e41200d02c0d10310101e648000c0143e003150300141000c1442e40340e4510b87c41c1c0210f000c010f0b518055130f10f03d2400344d206d070441291303554198000311600b2585802080c03000c89001e0945540700e480d52400c0e544130800310074513808020440f04c0100d640120300442c008004509000c1c0c800d0745004142010b050640300380f5030010502c1a4008010031080005201321781c003400400805501d843c0e00c58407040d811f682620806031115640c0c0400034080c1c0c0c0945641c9102c603400d10140c501141e52104140c0200303c042c070040d40070826046d40c1604520b404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 52235777 1250 52234527 52234561
    0x6120e0f0304090903050c0a030e040c021605041a15030405060106020a080d0b270403080a02042706050a0e0a0c03111209030d020708180301060506030c03061804060b09 74
    0x10314010360410b40343c03482c0d10b40546000d04080d403e0040030003c01080300014441400c0d0740d402a290065900d68100611040b246d802d5400c10464010036661814855074034244002c0301c4c4200c4000c150340310a07800962003039510b8110380350703c01c6e141e00804c81c810a5000145104600682c1a00e50b1607903102030503a00c40112910003405144200403000c41820b03642e01540706000f009d05400100d606c901a0028401d000790300e8034013845a44006c2008166220719103543c010305c003000c00d5040600e80300400c11401d01849905c0500c0041c3c207440380c04441503a1007403000700401010f1b0100603075a000b46c120511030540e64504035600b00700800480328064001c01d00700d031016407a1035190510890b40b5050794000034026508038002082a00e030070501500103012214065410707180d80380c2017a01e03082d0720701a000c02782c01e00030790400504012980c0c0e0301040c8e80e40001910754040e5a50754000004454034840c840b4021615a9034042c0400d10000754046008200140c2c3c004125848442081c0c441d070440c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 52237027 1250 52235777 52235803
    0x31c020a050f1f0905030904050112121817010b060a050408010501060e06091903061b020c09040302070b03100b070303020405040c0c020f04020a0c06091a0c0301030302030a110a050706120e 83
    0x8649515010040d030240000c4c60107002900d08103003c0344001402c1e16001e81c0400440c1c0b0060403d030050080c040503040007040142401150141e690441c3c1c020088a44540e8118542480100d0340841d007e4001051a21000b0b1600c1c3c0e40f006103d030301405c41d07040b6014201866180c0030020480e6405825595619000140001d0404040c40100324140ca000d0741e10700e4020b030324002e001000582e06e0250200381c3c0c842c00f554060001c14150001d00e012206040144141045400d020220760089a89816036179030f00c010943e0f80d610b03210074801d91065030f07101085d0b20380001484824143d066014205556085406004d0445084000c850181903218041d50012000020b00d540749030030342c010f00741c40186050503445000c2607113622b011500c0900059400065007140790102e6183c500b5a00d41c0a900000340034219410b40e1002035070b82c001c4240c52001c1c4005121034440b500e004204541020340d0081c101c801542d00c039100244036500c400340e007810b214102680d008a6844c04034480e854450 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 52238277 1250 52237027 52237063
    0x2120304020607050307021005041404060e0406020a020a05190c050f030d0302030a0609061d01150e0108060a17070509010b091e0d020303040305010614040c1b02031c020a050f 77
    0x40300c0d000c00103640d001e854100c4007440108038040041c0c90307080349608600310380d49880e52240d01c0c003124814004048a941440342e49020741c14083c94104010b1582c105800680041e25403d0400040e0314100c14140c1c003a100e8414881c1103e40301c4a84250b40700c14620494240b403601d41d481d0705000c60302c5a080c1d920b03070b810f030021214500102d10a60166500544030340c0040b58060b03580c8108000ca89268000880500c019100b1000c400c0c040490140100f11600c107880f59824212001424003036426081d904022802020031581d44c1c5031070202010b0a4a40440d0404260020b41c8030365a403480c0c42454010384100000140c0710b100c0300c01756107208130b02500c0ea805010751058003c90380d1000944941d4070441c1000c0100c0561401c0016101562155000056150420500410701d850403007289105500713103030f680c1ca079880e4011a4124065038446682254180610002c2e0800668951007203c00484500143d0010740c002009003440780500240c5014101c962a40c54031444d81442d80c440c884 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 52239527 1250 52238277 52238281
    0x6030303041209121a07140304080726030901110c030d050a0219050c070905060f01050306030a02060309011509020c1905030f03010f1403060f0115170903040e07021203 74
    0x185481d005550300b150525001d044552544103084007031100540c00e81c1c8216001d542141c03d07100c3c1800030380d08000359042500341c4180d1480c101e9040d00c00284000c3c2400004540c01003000100030341071758180180700140692110305003a8010a810843e10180b03a50700340b0078044102000e040c200c0d28448a004003941c5803160b000760500c05840d01a102d941c0c1c2c1a03082100410201d42c544540000704250740d14244d607690142907a510b0201d050b00b0420b0b0f03013850413003401104c1d52103550045010300282070442d201c2d030b24100060302b421842c502c0690001d50000801040d101e041d0302510030040d0031a925001180c542c4081d400300c1c06400030310756459201c2d10100c500c02030101030f0040000e12860840341740054414507400d29030000e078003002400000001c28449030500b0403c0041184040d8001c4c8020319100c00407800e103840600c9a001c01020f0341d08010b0b100c9109000040c04504403803044c00607410b04103030316652070b0b01900c20a5624a014004110021700c0400c2984003c0c03482c8040b00e080d9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 52240777 1250 52239527 52239533
    0xa080309010f0506090c13031a07120614011103070606030b011503090510110f0f0a09170a150f05010b071b1a03060105043609030219050c030601030b09150603030304 73
    0x6520900800c0c7e00c01d292407000100081d83c42021903603d4038a5440141503050850024080500010203074041a0820070180600e44103030110044000003464507040000000001c2410340c032400c0c402508207810441d01005200404c2180c504032030804014400b024600541101214100c0f40014040d400800d03c0c640c2100072908024540002c54900b649041902180300a042d4010f40168001c804007040061a040d04001009c00034400e00c500f42e041048699100794031032804074801030941002e68000300140105500c0100740040c200c200b0004d958480012104581104004070740110710b038603100443d0a01070350320004642071f407556042d450790001001c0c602900028502c50400006100c0060266143c40b481c124590074051060480d43c000c108145c2d1004114020280081c00d0944440001e90300090ba007861010300718200c4800011880c000c2e00f070420345074000b50305209460011042c010303d19155402211201c0840702040c28110302c0c1845000b00300d40c2242d16400c10700006d008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 52242027 1250 52240777 52240801
    0xc120201180204050601110609100515061e0904020706020702150c2a09070c020a060201020c070b030c071a071b03050a03090c050a06120e0f07060f02030702030a080309010f050609 79
    0x4d0504010507e20b80400c0d025150210072106048550b205040e640205082c2d44501c82e0041400000c00305008480c001151184c4168810503000f0103000c05a441c0640006013607a0000400900c159624a51801c080c0080d4200e20302c1a441500d10201200310540704108640d0011042d001510b0480041c846002420040301c0d040c107040080303480c3e03940e0680e48903014180b2440c542d4481c0c0881c0c4a03140103000d101413194020905581c03040101d00002c11000845030100c0f003010545681d0780d81c0301020f2a0346800b0b40b410013440b190940c20680000c0e08034603442c501c140150b544170049440400c0e41c5002500a03c41c01801007030b000c06c80c02c80034900ca9000083c82c00d016403425160f0a90399008181194140e41c80704000076816048020468064018040c0c0c040800c130061441d180c00c43c5410703840c1d514a20454007440500c094603d1800d0080c0b003aa0300380e54000b410b542a00c8601c3c2440c040903401180c01d006503510300141280f80c690b451044c14000d08015007a25501d956403104e9101c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 52243277 1250 52242027 52242031
    0x70302191a010906060f0e1c02030a02030703050f0f07050a0b030604150b0901020d05130506070c09180c1d0402010819020301080a0605060907050a0f090e070c12020118020405 77
    0x10314007441c00c88102084809090540c02000d03000b0300082c0c4c1500c1d280000301410070450340392040100c13103d01d4458550b12540000342501515821540d800745a20001c0c0c82c0104c80900250103001e4003a00105010010510440c00c00d030940544800d101d1189141c1e894681c28043c4070f42c0150080c00511481f29600c0140d50f0110300a440025162a4020600300c1d911484c1c0c0085180000011450110759060005015011117030500301d007800d1290002c01c124080f00c1c003540d80900000708005050004080035080200961181048007250399245d20718069001c6070151260b6140d40c80000d481280340700c040755484017034030040c0441e403210390045424020240500859120710000c40e46646401e01c0114000c0000c10000d04402c24646450810307070318002d1945108014050410001507002021a48002d9482c42d04448000c07402009643c268220380001c2600000700041241d056005200d1a1100d8003d01c58040e518032000e504909903078802c4005842d072045181c0d00c40050401b500419 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 52244527 1250 52243277 52243283
    0x606051c020d0f0207110a1a04090c03090c0e061f0e09150a060c02181003030825020d0212180f0604080a080714010c0c080901030e0303010b0c060c07030219 69
    0x1260b2030603c41460820303608030400c00d8070f80c10306c4a90511814070300281000000d001581d88090120b441005100603070146201c3d039002d460b1142b120140031131081d446003031055486880e841c40192070b038a01503110401224164000e031185450310014104191420501907030941e9500e145240e0f00c0d00307014001c0400392001d40c2804051003241c5880d581c030303503007040a40b80030740d6081e01c410500e004003c84100a055000c0c04907264006200c0ca01240300110800d40390107003002030141d2600c40d43c1d01ca14101880039080740000008506182980c0030847c2c15200c102030f421200c01c0d0b24940e41c80390051041c6c900d45091042103803601c00301c40c200701c0700404291030f00138402814103640702c0c007131400c05010040446c1d0b0300900040791020056004849940340e42071900030003907141c0246010344400e54644001e008102c000c0b4036044281c0c401d03080385540615500543e500c03960348107030113016504000c0d46480507014181c0091281c4600409491005415a00808604144058004010009410a03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 52245777 1250 52244527 52244531
    0x60903020c09011701050109090503030f0403090e07122405011407050f0106080d080606070308060d0f1518080304020103051b07080a0905040506011d03012309010606051c020d 77
    0x50940c0d10b66010343c0c001d1441c5900794241c142155110703406c44078142c01c84d0001600c0d01d251000480c0c40041030341d6200d003403c1c80c210407949590405031949411035008805543c114000c11450030341c401c0c00ad0903101c00c6084203000c03404090704070030100041900c1404d158100c4200030001984180041098100c05016040c40c04005407a01800d040a0b000458080d0391603030305c10810444104401d8034a0000741c9090032640c00c0000c0000d409204441c80a0f00b0040b89002240d110f030782d0000301c428926400813428035840f85510b00000100b844003101d0034070906d001c5d02c1d002a110ba80800424041c1e1000c1c01500c0c0d96255070055004080c013404000c0e640401000450501003094028210f09024866031038072400c0e4010002c0001d50740384c01941c091030030705040c4001030f40c0004014000382d82c3d40e0032002c045168071300480d00400318221005450100c0070466038a26800e00d20190140c1419002400030585a400a032070b584034003208811007146051890203101031581c090b0001c00400140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 52247027 1250 52245777 52245793
    0x703021b0604050604021c080301060f11030a0305060901080109030206010e090a0c03050c030105150607120302130f051008060112090317040503030f180d110c1c03031a090406090302 80
    0x41a1509100302d504030b035541d1164003800300b58034099009040f08000344018140328162541c80c00c41d00c3c007040c46001e003846036007a591001c1030300a64548c0344441c442802c490702d0384507440000703015202c2642c20600484562001090003001130254091084d0141c008000a904c0c0c603040c480c42d0785006007007031180d0094003002e8001442c00000300c40158051070003441d0303403c0040c00b0107007185c03c00f0f800001d400d81402041c01c2c0c1915508146c3d4030241d0007052807514000d40d050300360080d01c1348035032540e036004140f42c000c1070303036030111401000b60b80c01940c20420704a07a401041e14188c1c02510038901190850510346403070f00040e00102c500b14403d03d80764042d0859450000460300054504940940022081080c0740c0d81006525522007000701070048540702c900d013641c0d11224400b0292042165820204011007402c02c95081d0035030003d070540681542100305210036150920303049000034207010000040c2e01911581001451008020704075075125a40d400e4000c1c9581d800480560041d00c40e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 52248277 1250 52247027 52247077
    0x40e0402060d020c03040905070c1709030a0c1701060f0605030c0f0d0609090218010e010506130f090b09070201111204020f100201060501030e150f09030d02070c050a060314070302 79
    0x241c13441442043c01507031240d080262a4040d50700080c521010011080c2c0d400000c01c0041c01c185079400548030321180e54906100100341003004001001d0200394a05400084002d40e4840034812010420020030920752034003c925078100c07240c411200000c4040c40401c4000300c0481c01400080842c2c2581032400301c1074801c100641e00540d0001c01007550b9111443c0c19402e00322400f8450065510305100d66604010807410300380418090309000d102c001c2428030101030f4004042c4098140c08160710300f19641d440c01d0201a10308404118000c0f0b40840220390490b0050080700f5505c2e039919461814022941010350b2103000042060364000050580440661100790220b03038405e07171a900210f01d480c00c0c0000034007603ca0300c2511104c030760302030b8064511260112402c1600646584040b120f961a40300000d4518024000c618840902c00552031007044051401d41e011180240c800d0500c00b940c51405a00b04c40d2510b500c4100e9514200005103020704c00e90092552203030528126401040207a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 52249527 1250 52248277 52248281
    0x10030606090203040c0506070309140307050405090f12030c030103020409020112050a090b0705090f060306150a050d06090c12050703110c07080106090c0c0308041502120604060f050105040e0402060d 87
    0x19205003201e030341c004248070078041d1800f04c04004d00000c0c2c401da407030080c01d0fa800500d94603a078410b018581c2a10303000b483c130568050285000a110060050040303047c809503103a21001b566110300c186215000850f190303140c2400640340b10b524400681c0f0309681c603540070300028000e0b5403802c9041148029041030703800041d10465004507180000020141c140386015070328070001418400034040d0522881070700d0b0742c50600c1441150b900b55680d90726038803240e0105110301a4100b91605002020a002908079030000182044c0682d0000c14481142c0c0c4010b9101280c1c6120451800502401700000c07400225400031604500785103400994092074551440d0542c008058a4040da00708510030010b15070240201c0c40a00313511181040548400c1d00302034000c0790240002010301c9082c40003d002e006150120400841584009640c0c1d0001d0140c094030300007049400c0c1d8411403510078080b0f00c0e8000002401305864041c0c6604e03180c40c3c01d06481920180d4000c0003280c3c010410414917115407114 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 52250777 1250 52249527 52249529
    0x1a0f0a0206060a090e0304050103020904020702091f0e070c030c140106060201150b090916090b030403050702100903020307090f0e0f030a120509060c0d02070b010e1506040b1210030606 81
    0x1680c05040281800c404110400810754030114083d41030400303519000e0303400720460b4211003003402c0041c3e40301c1034100841c019000f8000c0103580101d040f010000c81000c0089940d003108074401980b1100b5032200e00b005824241078440200080c8001c5069000900401d008821a8000d0421040c00d040007291030782036400d140c00030310051351641e825500894460001d0310180024954aa08050540c00400c0140c070000b00301c2d050b90803113003140c0040a17000b1000600a00a8a19000c0d44d903e02030502810691004d10200d00403180d0007a2110028030034030318107055a5006002d04100d40c5018400000381070010752401d01c1ca80d441c03d50b468210010003945039181c0c280c1002e103446140520029048000ba40003542c1c110307092100700680c011001c83c21540c031a00c807c1d01d0a403100560f0000c0300c0240514036008104140c05400414180982101144150800c1070203100c07112001003400024002c903c141041d4640034000340390700c01800000103902004400307454401070780c0c07a180c0300305403442 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 52252027 1250 52250777 52250797
    0x105070c15030c0201020429040902030a0204030c080a0f06020a141201090b15040b070804180b1f050403110315010b0319060302030606010305102c100e011a0f 70
    0x4802a00001c5070342500441c0c0c0180c4883c0001c5051518040483c0c2104081c103007844000c900d100c4404c0341400800041c0d6000d044c0c070740c0b811074480c5840b100b440029481400141c6069108900c000b41120000800d03801d1158001501800307295581c0e580b0000c0d4000314106010303c5143c03141d0300c05600c051400b500f03100e00d400c0008102540340c210840202d4014202240c0108107140c42c0e9403250561a040b0b5040303d107103610066490100e07040525145c0104c1d04503285014202c0030f42c48901d0440d402402c5804401c032480b4905003c620508101e00c1162460b660205030240820030200f030b01c3c1070b84000071642c05019030340100c0c01b081c1589d4504800360003104d010703c00401441307414800e4911038508841841010130505c0c1c25500008e40c1c466004100d00d0401d62100c000640d00b44460354072000a00010042102c80ca0450054100c1d2102c0c16604002e40b189450000b80d558006d11a44011101c03003100e0340c01ea40e424441d1017900c09a05942c8005041c40820070b001d44c00c90010004c02046030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 52253277 1250 52252027 52252049
    0x61205060f1005090c03042402070c0503030a0c020d050106030210120606090e180109080a050a030b04060e010509090102250b31020307120318080f060a0b0105070c 72
    0x6403010000841c944040d11640085400c2035042c085a00c032480019009052140303c01d0b00e0303564030714003841c201d6229041c04100501d685a404032100e420780251030039511030f08000780d0054448050541c0c0f40144d2a1110004070060824400750501020051040b0700410020070f00945a40108900c4601e2084850020b040000d1503a80f05030648120005040c0d94038102c5050303483c1c107011905c5090068031011004803158003444260b0000d41c00a000a54080000d9440d0044008080e055400c904600c01c082400c0408030001c40c0740c244106020341e0030030b03120004030740d0030001440000c21005021a80c190340c2040200020709483c48482140c0c0d415601d104011040d0303240a000454020784a00003050f0300010040c001c00303401c91560106050408020002070381030001901d40060b541c0540086c0d06000080b00505074800b0303080d01d9540d070f403519008805640791101ca0382d4200711000045a40c1001004c22030b80b070704d144c101014941c0140341560034564070391102c0c1c0003000302e0342c40845401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 52254527 1250 52253277 52253281
    0x30f050607020a0503030a050a0e1002180d050a06240e04020f01110c09280b01021e0c060a0c021f020f030a0806060d091a0103020a0902040302010f110106120506 71
    0x40030000c059100340c00d88064158220107680c1c0980d207000181c8081c410075241c034006403241c040f0354003c034040017505003145d0b4842c0442c00c621001354000e84e00c9403901d6590381c2e6001c009090411110550340d90041c0100103401640d100c000041c1003800d0740245800400b8a2580183d0114074044003500c03090307040c2c45440c01c09d8030400c0032200301e80b03540c14141b03c4583c2c48841004004140094a108190380101e4240c1c1ea07400030b0420382c909a044401c010115907044031002049501c11785c04003400ba002c940f10048000012042c80e44500031f91000f50388032080000c42410f01c480500000041c81c1064601c4556030b500090045802d06100003008100071b400008059040000d0840d0068a42c043c5d80b408604401c024100c40c0e005003203078022000000c00850507003c1e94480c0c14520380040c96410f20700d060740c00440d111142840143d12501d400b40c030115600b00c051088a04a0350f050310b07198100c04c3e103601c06940113091415640782c55561444002991781400140d00c1c0300c81d202c0d0f009407081d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 52255777 1250 52254527 52254533
    0x20c030c0a060f0b041107020409110d06020306040501080604021e040219020a020a0f050d0602091206090d110d051204060f0e0c01080a061415070c0b0705100506150d0f0501030f 78
    0x11042c10b013415206a09000400c1807895460b0201c1d5200b540544020921450310304120b03d080420729840c0790072502c04c080610601c98150f001e9406054119000d02c030a036665610f50740c1e41c03607040d00d01950203c480400c01076031910001000e13041c080c0c0500701604188040801028a0024002840258000c8600b10381146010081d00001d400e02036100c1d210503003480040350740030b8000d203070017442d55500180312046030381d40c4240c80d04041c44074001c0300c9484c03800314155626480f00e40420400704c2e442040c00100004003280b80040a102075842e1410710515000800000740007030000c0d600183da0b568140c0c8100400d005400e42c0c0071b2514000c16040315100001045908001c00342060300c3d10305031092140c54030392810a5801c00080700e081000b0303504d18840c19260710800d13000911502031550001045008600030b41107880c0200c0694109580071000c00d0b007a1402140d00b640d2145010805554600d09000a0b1000160071000004d0009601c0707840002c464007a0420784120740608910410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 52257027 1250 52255777 52255781
    0x90819180609151107050103090c09060803040f090e06150f040906020306010906140406030c09080706091401020102070506190204032307050a030c140d0b1305060604140a020c030c0a060f 82
    0x30b0075440c60304d00e011043e2803800f0354650303805028880c1015124001203003400b04040c0d04e2400340c11145801c00c10503945008065580c0e01c01d06c6144d4281a4440c00010f681c5114451326101f0307812880580f543d507950443c0e80540038040808983c0c003024640301c0e2070298503640302d00d5007840c1c0b040000503900e0400c08000b408010311903001c1d9041181498070340d0715803140c0500350f0703045841c50308021400c0b9400e002c040e151011a50030020b02c512a07001d0001c0d51a41c0054000100c80501515000641e03e20004a080c0e1150081c042d00d00c1d48110003141819603e0550417100e8010a0001400c040d1255101001001000440307091807640a1100700406001d203c004003c2074111000003650780365a41c0c040d030360b1515101380c0082200014015580e62101c544030145540d201310144024901903001148000a0f1581550300303101e4131001500d5410944100305610700c10742e130700c0d01640d52010100c070f01950140070700100d54001400f01501ca0441049000c444602c1980c0100d0f031802c2c0503540c141 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 52258277 1250 52257027 52257059
    0x3090302092d1515040b0d02040308070c030b0a0b060702010809030d0f05010f0f06080c07080d05010b0d0b100c0f020315010f0e070f05040302060a020a0206030a0f0b0301090819180609 81
    0x100c1060502c010901307024a8804a074226140c03e41141d84401c22203458400074081d035070020b00405800205001042100c1c4814004c0c0c80c850a420341194441480789000c0b919280e84894001070100058400f56000716003150f485000780c0f007100e1821200480b8041940d891283d840200c1c0d440d100140000d039401042e1602400034241c84c010b41e540340080c0209186005450307004003040002c2c203202403002403411102c140641a80921641d651014180310940c0200c50006c4064a0034440c4038542c9814440c50440b868a0381d09c2e055203c0e11a2104002c0d0045483c00300c0c3d151003030303203100088400c001b8441d50003002ca120511440910f41900c01491820041903901001405aa001c442a4000d0150b03420340360150303601078130b40f92200c03410f82c5090301140c00698800c00200800005040c6504402c11200c0c0e011010300a001038041403500341c5a0b1030382c0042c4480b000380509483e0b81002001e64030502014901041040c039000c2d80d4114040343c5800c29000a03051802c14440c1d03244a0111203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 52259527 1250 52258277 52258279
    0x1080613030e2b0302010e0c0a150c0b010303120507020a020a0504020a0302090d0609150204030203190201050c0105010905061206060a0e0402031c05071e02240f160218010303090302092d15 83
    0x10251008e51800520a929107010740142e030101c0d2030344c02450601c84c0c0c00c1450415801920441d142d6180d050240c020700026a94504050070200000c2d1668801300b400855540d014041340e4882c3d09100410029400640560040560a01c920301d250350701c407450320152a00a9100184460031400c3c400d40400031460380d00c0903240104000c10050320f0016505130980300c040700804e002c1d122b520048601c2d12401e03c07000706030341c2000004510044160700030350140004403407005505294526194880804a880da0b6002e01c548004011084080d60301c940e000b0f10040503107100306c142900c00f00004510304214400910080340040030001c501824040400b808284064000510b0740080d03c07138441c80b60100705001c4460700748402102da45d020340d007041e40e140c2c140036281c0d118a0070000100943d254140d118034072282030710407600e00c0c0a02080c142c0e6055540d203102c50b42103809001e6101d8000c0e2008110807005a460301032020440c0420180f101881d5080d509403c0041c0701840c0b00c01d40d01c2ca21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 52260777 1250 52259527 52259533
    0xb070e0109080703020405060f0d0b070905011103090909030c1203010911032202030c0a2705010509040303020c10051e0a060503030706051005100507030801080613030e2b0302010e 79
    0x24441c01000207039800c204c1e681120701040d190b580402061072000e105c40d0180e0400b8040354018108110155020b2003000136942d035031180c130341c1c407001195a4450700501c521250410448481281404505103a115824400300c1340341070207103ca40b921300b0b00d00d2140407883c86404801881079404501910b0040c00c1d25a24190460038424088510524072040308511030801112010864806000c0d2046040d0001e04c402c84041d9101d50705041c0c031500800900101c104024030000e0001c0302d01c1100c1c180c40e4040c25100440d80d5907078041d0700a500c484490b041e10710911026110b00c01584c00742c14499541031400030050866150f584540e040d002e09007051040c108581480340352000010b440d04030390030060100c0c00b6211001c00d6004600140c000a81000d042003008102980050082201901c21f541741c9105070390780c4130310a441d144180e40c0f40a140300c41400010120b0711441315a040b4910050890214109801007002101c2000120602d8800c262001d401030640a01c502c00e000180350000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 52262027 1250 52260777 52260779
    0x8070503031801050306010909060f0302090a0501060c02090c070813030501180803071b08070308060a090501050a060809010b0405042f060306120708030705071502030a02150901090503070b070e0109 87
    0x1c08028202c400c50a8104040400003500e2070f0700c6040100d00400d40c44204000554440c03655503155101800140d02640101c008079114003c01d1003040d04880a5940368179240d1116401c1208181010f072004840b140301b402103a0100b00740c0802404c910300c41030742440781d06280d03203801400d40c0c40038603540c280401d5959441020804038003c8030741c80315840c9040300348075440413801c3c03811005000e800361000801250140805420440003406804212103034044c00b50b544454000f0b6030824041e05400c140f1250b0100003040c0100500b5401800c050000324116601001103012100c04540558206551040042020016a60003200026406175070a21001d403000800c120b40b00140c216406121542601404601c0900042c0003804000d4282c03940c461880c10400c1e03a0b210103000b00c1c04400c2600d10340c5ca41580c000821104c0801d1603802500030030081e0078801c80c0c0700c0c20042440f6920f549400e800c6000a1041c002084030301c1c403031241003080d41030015009000c18000b02c000c45c10322000c030748 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 52263277 1250 52262027 52262047
    0x50d1701091407030b01110616030501240507060204050315040b09120f16020613080606060a0c0312060825080a031b050118051b06030601090608040c03080403050303010807050303 79
    0x103040b5600c5480b0b8100480c2440844004a8040e80501014506401510b081c060101a265400c1003109403541d010321051341c880310800014004280e00e0704c00d4047c04048141c84901580260004a0180d240142055a610086828440703091800700200d002c20040108001d02168500d4109142800a240780500001603000600c2000e260301d0502d10040f880401c0c0c03074030102d8010580c69018240c40d0302c92400c08041e048030582c41c012901140640700001e007803410040151561100d143c0c3c0d940000c032959480c103403825000842c040a5140c0c41c1c1ca00440d15070410420380380843e207a03014001082c0b54000240021400c660018590b0f074004d0728003080425405190020307282010b030041e0718a103040340fa140c0e0050110224a202030b00b9140c00000511101103480b1390500300140442c2d000394502020001d0900c030807104a401720302e030100144a004d01c142c440f0750740303d4800e42c140b00c0d00e541c8079114040c0c0c0b900309600480f15a40000010300c980c40003484042c00501c0b0681c000c6040003c810303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 52264527 1250 52263277 52263311
    0x120f0e0d0f0c080118030306090b090619050307080c1c0302060711161508060103141303050705030f03040c0b0a020607141309051608090c0108040f050d170109 70
    0x1000107456203120150041c00d102e10501c102004100840082052405045c4a0600301303110703020550200c1e10f0550005600740a034006c01c2c021160040c5444101d954240400103003048401800c10344554400b40800d07151001c0080c03002400071100101110410320080080440c0b0b26070340c500c40029070440042c0080c2d000038072642c000b15141800d03074018084140700703490304d5105a484c03280111240400654002d011000d01d04000443d82c454140b65240001034058416841d041603080c2c43c00000101a11106910340352030600c079282c082c2c600401b03503e9092550304002901000310f8000014401002401d02074070008040d07840100f4181601000c0c0a5203920008194106108407a014010240c5400040b68070359094500c260071001c0e118407070000200400c4401155a96007400e003407200b507006141d603601c01c1001400a002d6103d0746801100c44c240040c00c00c541703150403d2009800039209100d0b19224510545d40c000f05e150b81d44814004100d4103070b000f03985080c540810101c4810f020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 52265777 1250 52264527 52264549
    0x325050a0b0906030402010c06060b0301030309091b0e0105040503010510090b01020d05090402030a060e0403020f0d05041811070b01090504030f0f02060708040302030d0606030b030d0306080d08040c0302040207120f0e 95
    0x120b4002c4d84a03500d41c00144c812444a0070000d05203490101f010035944a07000265041c2ea0091b59000062912980f410b4100c0304030f6600b05100c203448082040050b8402d00071905e1421040c90003d08280c2d40e0310109096035825201505a400d4003081400307501d501e0700c10312098140910007071140f0b0500281c0079100d8070070f000047d4041ca400200103508041c4a07000800281400010f00c8158645410025240e0281d08000c02140c00781d01104058540f182d000c1e41e003541d0704401140d009a010360700f00d1000340444801082c051105021650114544102060081c230102c580030995140900c2c0c01004515510004002e00041150080c1c00641c00160b80754000c00f18104504151260700701a869800f60160300b028082c204030010a107150325822550300d00c0750a50407030710452008181074040c0c454a0091801e1603000c030700c28011081c0b04e460103a400c240194100d00f402600d030340100382a640210800d0722601340aa103100007481c3e0015552444901c40e15148103003a5030300c3e000441200c2c80c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 52267027 1250 52265777 52265779
    0x10b0d0c171c110c0301060506040b031504060b040f08151305010b03030310083f0705070b07020f010c050d120b030304060e0a060203120105060c0307020325050a0b09 73
    0x1e40c40404903a9601000011219101003191000000a603000100492000081c1846900601010078460b0505008020030388100800d85030500741030090381d4825820040c54040214040225003449444600c203000282c00c1f891100d654075030030900c0d07100706e40c0c40d203502c14111940541c0c550340050f021640d07202d8011417007800e16000c04800c0d00300715014109003403540e41d02d80400414420050b04600174241150020740c191100c140c5d188100044113103641d08800e08002440045008031480006102500400c003034180d03040ca00940c642a2070031205400c2000d40440000d030309400e500c1c0034260015940c40074a03080c1d200b008160740741501da1400d500400305104410200d665120f055400c401c4402e0005811240c407a9039640f0010803885449004900940072400c0c003190440c03002c011203c07554603143c2241466480c01040c800160f100a10840080c001800400c0040e42c09110781d0440c007107003e0301d94549203495040c0800d100c1c110750004c0e03c41ca803545410400c1d801d40005071804028 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 52268277 1250 52267027 52267049
    0x30f04060903030f1d0d1106270604030302030f090c030a060b0f0d0503040501030b09090c210303041a0108150c09120a05010f0513110d05010f0e0609010b0d0c 70
    0x1031070305a0180100c05801d1803180e0401c042e52825082e038504045c01c0d9296141102c900307014160064405e10b10344030300d0940d1500f02d0b90004000c12030b5046c80d034070308050b031a00c400d003a510122119030819800b41d0b01240042c0d0000180482c01601d81c100d0b0350401e06850250102c10180000243d803800b880300020101c0307444804002996a9907100d40d1983c4034054090443c424040c030388191031390301601a00340424130340003c5407000d05000385070505c1514000000d0194840107820001c001d46403000003001401c3c40811070305480e81c1440a07500492003141c0340840142c0c0c08200521200050704140304a034400340040c1d0046400300b011a408c41c01d4502456a501348940200e178000003406c00443d840c0c403803d4860010410305611110400032200030400c1162103840da8005060700d0b03082d02814030361480e50601403e103402c07290980501e10910000560a10605502007030783c2d49800564956008042041605a000e0152200c081811110b0300740717180c17070355407640c3c00e20500b8050541c443c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 52269527 1250 52268277 52268291
    0x1060e10020124031406010b04030803060a03120c02090c030c22030501090b04030e01050f04050103181515092a140d0207020f0405010f0b09030102040e010b030615030f0406 76
    0x81c1c003c0d407010344000c21085500f284004103100040c00240d82e80b0080742c203500c5810180c0c40c0d041021071810b05032240004103a01c1d04d8519110340301a41c102600d4580e00c180c1c0740c20000001200c084011241c2c1410f03441d00c4400000c030303004004510000514555540408004000194602200700c0b00d00e45000000c0c201c24141c2140842800c85c0f4640008042d50b03c4e058001091041510b1070b2840b5031f10940d603040303494104000444150181e00c2c08220f01c040c0500042c061580240c001165210040064100b040e82c5610740c0242044500b00140649550703500c04c1050100c02e144050103044030110034402c025842081242501001841d030340382c41c00c0f0360b11000c032291181d00d0020504545041c21030301c03071020000110096101000c00c9100315008200c01c822400c1c1406101e0482c0c42c03c0708030000d0103181c4040c40030654801604140d26550801003c22506a655452406031000d880080d840c5d00e400c405000d400c2c1d540401e6490150010f1007004511105030b0400d0390704c0380c0e002c41e010440c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 52270777 1250 52269527 52269559
    0x711010905030a020618030702031902060702130b1002011107060902060706090501141e04060510030b040f14030c0601120609150b010306050109050d0f02030c060304030305060306070801060e 84
    0x502400c40024424040060054a019800100c4078000d200050340e4000031220a02a940e40388035210300290140c02039642c6400c040a45221004201d0000d41118502155a400291902120011004819070f50300054460b42440218900750304900c0c002044840c0c0030301782c071860354000c85600624060300c030040c0c90119151001503510382d945c480b04c2072005007002d14096000c1c10554000b10407000560300015161031000c9a081d126103081443c100d07003900d90391200009028010001440b02400190000020320301004003171059000d00003101a0480a18140c0881c08880401c07402d05e51080c05074001c40980801c0a5044428281244060000340d2800d10050441c500c4064002c07200700c0d4070010190510340101d020514243c1e400c00800da203c40c010341712440e0b503025107504141c5081f80400000c8950301c10b85c2d456400102120f511640c400d0019800e0b038011201280080d4560f4107106044c1401c2106a800003101d007885406581442002851104000e0b01c03140f04444403c0b042c403030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 52272027 1250 52270777 52270781
    0x30a061a0706050f0403080412050417030c0105010e06060412110604080606090606130b090d120203130b030106080a0c0c0203160503070b0a0e01050a09050d0f1203050609071101 78
    0x40c032411100c500200c201140d20802600700300e10075200203040000090100c4030030341099114681c191508091903d850f211000c24250151011007840020040807442c0c0207a8194101004104e1004603a04c2c0101b6071041e0a40d003044e0700200c0191000303000c0c07069a55400050301c064030078010412520809174100107081030700d00030b844c40d0410030009000c05c0d4040d01160ba00d11454090307440ac3d4081e102c2c0800d00c1014450010300c07244840401c01c0500c400c48900c401091061720050000d401250192207290465404e11000c40142c2d10004401e070310300320083c010000600d4002061030031980b5202c006407031500700a010f40e11180da10f505032032100cad0058010030b1006801078102c821b034a40d0040b07802c1011711036018840c0720380b183d182c000510381d0300f10003120a1190700e41e584140170300856006440c150401c01c0c041c0280108141c0201e4551144000e03105414081c2030711050880c40b03801c000703540c8001141180201170801c810800e854840140c004e80041d560701e0401100c1d800f00c030364640 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 52273277 1250 52272027 52272029
    0x1050601051c0f050a0501060f1107150203090a0b0a14070f031209230f0f0c0d03021507021f0905150a1d1501060f08010e0a0f0c09081902090a02030a06 67
    0x3c02d51500b070500078030f4802d90740000d040e03031101d4645a000c1100c9079001d44074403d10030300c0f000c0c05902184050040d120420540f000720346107401181d0814100b80006900c00445800c000c4041c0000315001041c2c0e85c0c008200d01c150070048210303900e040034035142e09044041d0081d015091102c0c0c5075189083c145a40d000c010100d8100030703000d400c1d44140c0046503029459840b0b46c0d040c1e1140302c0c2500490000403601c508080041c4005084c070101c040180002224a05001d07400c2d0b002c0c10a080d80304c004025101e51245001354080c3c01e403a81041c00110000390110020184580b074410340ea000180c0c00511090a0311314501c0c41d440300d90300c00c0c2041c0d02400c2c02c020014034540303400d000d668240200181d000b10059000e40c44204980e01e80350202c698500b8444884002138a8070010050700c4141000907400450b41c071b002050b079642c00c03206070301512540c090440003d06100e108003c00442445001203041c21140a900e04403001d400107151811b0113001040101d0740007012520030259640040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 52274527 1250 52273277 52273301
    0xb07020d0801350a0507060801050103021606090203030f04121506060210051b0a020304090501080c0d0602030411100203121005060703120207021c0c0602030a050a0f02070b1303060e01050601051c 86
    0x28071104c0051902c0c0740c031204680304102c0403446900c00414958000c0c0207844420390744002d01116007050340c481102070010031400307a8050008000c032561040814000b40090085d0040510b050300003460312000d143d6200c0c4541541078589802480f00c0c2d40d021864000343d1640d00c002291988030032030000d00c41075010041d031844010020b210042160003001070130803219450410405d81c4e036504950768030341101c040469885100301c03160400250071680a150898083c40c609055600550049a244040d1200d8800543d002007843d80c505081c0d04826a4012401c80315248114540070101c1d00c04d0040e01d0004040c021005c8000801104030360644248503002052410001091200c90020fa04241c03025034409014600100b6810300000444540c0421692903d1810841080854420150502d2801140100140001c68200c600701805101c0c040e10035541c0410301e54980344084404817a040380082e4108420400c0d113030b030000242d0b02903486445141d44d0565451110300003c02164040d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 52275777 1250 52274527 52274533
    0x12250c230105070201060819210e090c0c010b10020705060a050f180109080604080f0306030a15020a09050301060506030105300109020a06020109020a15090b070b07020d080135 77
    0x100d0f1055054200c5401ca41e031400a0b074003600511401840d25081c2c1d480003810f84010903514810050000001d0030002c0c5903403400ca0381058004000500740c0c1f00580f1010702200011a800c0c100c1c22080c41010469542110502d5904141d8000a52100c0c490711803d44a07101c0400e40b82c1015020b1002c641400124401455640500c08000780d1a07442000e142800100401400f242c0c0d40c1e0002030840c0a00e4011140c0d03401c0a0528446070f0950344018031a5400d40154204040050303401c2807030240d6110b2248025807902e01c009001050840aa40054845ea040c000d04100c9503c541085074191030301500c04070400a0807080110040080c0b0340300031161000b0311206e8502d51070641c40b10781c51034800c0300e0003501270751782d10400c9090344c2034440044d6200f10b881e1000c002d02420244451103003140c0b8240a00c209580f80004a81070700071801c290f40526180003042036035907041c07002070050823075402c288090b03505140564a62030300030000303e00d80c001c02c9104c801c01105040c1c0d00303101c801e40031411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 52277027 1250 52275777 52275781
    0x4090804030b040b180709021b01020705010b040e15060d05190f030810150315080304030803010305100603050a0f0c12030f030506090105010e040506040f0212250c230105 75
    0x41c1c400880444090303c2c000d10280105d0b070304c0310f10040015448103c21004081060402895a000350b00c000c0c0c00030203500c0c0b6244140341c114001e0014156850140c000050900d03280400d0006070b814141c1c02c4140e640040c0c103005e1017140c00324a65500007200b40c0b1418452105c904d480342c0382618422802400c1210307900010100040b4000302050b00740b00e95210704141e201c4103400e00d05113900d809052100302030502e4400c0e04501c20b602c05049088610702142075196900c840c81d0950740241c0003651070200020040c42400070801c04aa81042c0f000030070400d462650703da40303480300a4004c00810001c40c955645003440820142607000d091007102e0052150319516001d03203120f4401c50000c010a06010004541d4a80308007828100c8406840d81c1c0c40c0307a42500100310060800070001684555650711440103007410384050300500420f030710710520f1401c001c2d402900508080c4030b6465102c0c04a19a030101c40e622820382200d80390301c0f03400516000007406c8520f04217401444240060742ca0002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 52278277 1250 52277027 52277033
    0x3010e030406030b01052a070e090d140415180b040e07020609070503031c0f0c0201020c0f0102042301051225020705060717040f03030309120305090a030e0409080403 73
    0xc0200202da00984003000a40c0d104401518140544680204503940c0520582d000c043c0113150f19800c1204c0b03c080c2c0303c0c40c507100c003d280200d0800341c50107a00c0d94001c4482038115034028141c0e0a83e600740301b61544c1824641075840c0c00d40040e102440e01000188091026540d10001211000e08003801c40d0a07192521080d0085890a08841e40350040c400c20011420b000000300c0d4180555101070041c5181012491411110b080c8001d6281b03001a03680762160780419951081d0100b2080c598000340e0f172000520740840c5000a01c4c0713440310700741c2d104105c208180a040c82d983c1403441c40042c9420080c4c4c0e046001070b40e09001d040101092003890004004044507464a04805070300004d40450005c4445c602c200d903901241d01940d900b080c1e04214040c0130440394844a0341d0310044017040e520f080c0c2c80396486447c080c1c050307008501007500c0e0300307204042141800341040b024480f4030b0100b00901d080c44195640c1c07600301d00090207000003e80701c1c5289440d25040641016004440c241e038582d641c0c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 52279527 1250 52278277 52278283
    0xc0f0803030406060b0a08040326090606030601150e040b0d02190e0106031406040203040203010902132711011206050d0b180102030906040b0c27040c050f0a08040f0203010e 76
    0xb94200c031028505440420502c40e00c10661390170f50f01790f903140026a030f0f840d5000c0d00e0056401310400c00f41404500075078003200d80181c0c214440c4c00c203180600010706120007031624060042e0030840b03040b4a80c4101065083d400b1400000000c1c0440b000f08504c010000410034062070504060b42054600c03a143c1c1d81d0712482c03924201201c01202185000342e0340e481c0128100c8800451302c2041c08012004600545040d40185800900080000071650740b540d00017140110140308030310f4015251407103002c0c0384508040b07021510107420010303c03683c030b0b0994402c021040700c00303040f03814403610001056100380300b540008080d101c050148044801c0314140602c07054801c650440241e001c08062604452060003a01c1c007076081c220052001c0d45441d521a40d051740010981c401c001014020310079543c4804010b400114195500b110b00400d920301800103031447c10360b03d01d0074000100080381e2900da40c035003142ca040880340740c07100d41a00d07140760200c030180c0b0600020b5815800c01d10200040b0341e001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 52280777 1250 52279527 52279531
    0x307020105070e0f010210020309071d07020d0c02180a06080102041d09031204080d0209030d030c03150501230403020406030c15080f0f0705120f070e030102040b0a05070c0f080303 79
    0x6611416100f544000400006103004500c1d140140c10140d4440c4074005690040c68011030b4240545442c680ca44818804d0b990080304c00c00380c58440041441113150b01804540b0108280c4d01c1c041c08642400d4012a809400c0348050001d01e211080c00150034034403c0d4096009410b4a100070365403547d03074403011400340b52201c81624410725000040b443d1044000111106032200344072200d5143d480b0f0b241d42125410107000159407580801040001d40ea05024030340c41e603450b50303c00043c03800d07000c00c000701118001c9003102e01c040c0c1d0314001440f00d60703000040090143c81c6440045000c040402c2c104030382d40502c1e80700a420504164021040180043c001400d5801c08258859000100351040301c24150a079400040c07401e01002154602218068480d400030040c18010328281140c2e0421715104002c0b11404041d2000c86c00b03001209901c01e000c182088000c0300254101424026140118070400c103400060200c00a000d80810207044e0440000700001d8800009155480a04c00c0d240c1e03200b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 52282027 1250 52280777 52280791
    0x33160f05030906161215140f03100f15081b0901150c020409080d0609060b0918060d0b0411030d140a0305041e050307051509120a03110307020105 64
    0x642444a1184114103032442220660020f040320340b1803400c400d02804a07030610400f00300104015400b42c55007405000c00005030221241c06803403030a0820451200f408155038030400031441d0240f01030358001b030500b0305031010100020320170075103824003c0105a444100038004040d8400001c80c014045228111a00f000d81c011300025014030400040e41c100f4085c440b410103980044860051080040b0300419101038400104d440c196200c0da00250000740c1000051a00c401d030038814581a409a20000c094840c485814101c4c42c1001404464070000102100e0244000040a581c2d40c04240120603802880301a5181001d003000258142040b00716400ba2040040002100340718811039049100e19210003400d015000c04110050b05002d0020344030b02c0042d031b02102d00c1150003201c44038414411802103640d10403910b030003070614071103050b0580350210031400c00c118044041144511fa0b032481030605d070358118400e8282c00034409205103503840d07400842007280039601507010b00d0017180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 52283277 1250 52282027 52282037
    0x4050a030b0910140c0f16050a030e030313090213030614180d0906051b1b030601050406080a03050304080c01020d0b1906050412050a02060d0203040c09020c3316 71
    0x70a0f8003100140e03240344600141c18082070000410360049000070744004603c80c0c085c00e2600c1e0841c9050306050300e201e18140c42c0741c0c002040c0b400170140c00c00b42c188013564003a4061824501c3d00044600c80e01c059104900010b9000520501800c014082030740255900540412030784c4200090846001d03401c480540f810030f546215891620230000d41c14003c95071a51312901c405051010854843e00b0240e00c0300448500d01000d110003402c14002e001a081094010b80c0c0081942c0302014a410010390106004924014080c8092400850705100150309801c0c1241c1d80c2d111031402648500c103c0003905120751000c47c107010304465079005040c0340c0204880691684400900c0c02e2503a06440c443c117000700750108410050103580f2000001d060b40110280c032045a6540c02107003d5a1000e100e18188590000c100010000240e10380c1002d40b88201045040c1704040c8140d40c0e03544041c9807840c100e00000b240c207132007100b030444400c60b0011030304966207114201a00d007a0841c1ca81c01e14600c011030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 52284527 1250 52283277 52283293
    0x2060315130501080607050a110d0f0e04110d020c100f050a0f05060a0501030506061e09012a03030207021216090b0414040210020102040803220902030f070e0604050a030b09 76
    0x641d060140e00c1c182c825520160105403141c001c10f03a199884218210240842c00d080340703400041c14005000202001e84078169030110052000749149103800c02070344564640f418040200205005842040903a1400141d07603915100b0064a07108407045440801400c10780480b003030050341e402840c0a038100380c80c00d110b20f00924600c203059810490b0000e4115641d680204090342c030a410050304210040c003054039008001224443c00070606d004034001a05c00103130b2100c40c0d43c0c040c840001e04003000e064030038081006c040c1c00d07912101c40e12003c4c0c1007580100303c400556840da806110104204411220f00c4001020800702e07007040b80c46515411441d04a00c4150350a10b40250000501188190000307541e4541c00c004d00b0350f141c144401c04540d404e01c00800c02e0b000030070051501c11109e601c1d400310080072810650980c141500300703d407100e0042c024003041505696801d81c00810b2402c080e1f68600100c000702d404c90007250b03c0b1306d500255152000050101985006004066410a4035041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 52285777 1250 52284527 52284559
    0x6090d0806090112120306050d05060610050a02060708091e0c040605010815120f01090f0b070203040e15130c0507110306010303080103021504051801051201060e130501060302060315 80
    0x106609100b01c0c1341d0507240c403c2c070f000064603c003810081c541e04d605002422a0710f6402181001420b400304440643c000350074001146800c404c0c91041003114545103240104040000b902c81e00c1c054828000d11081309c0100d244814148040903c001e0000c1c1184040101920788941e01c05030b401b080d43c0034520b420000b043d40d51181090b5403086060059911a420082c410321040741400c5110380c0315070040792000041d802c002e010b018402d41c02400940c522804500301003144220181080003950300400c000c201e24601020b00a038025400e00c7c00705011100d0201103851062881210b0513594901401c40d40c455070040042c0010f40d0086d4081e42c0c0e00005007060581d101c8080c00080c3c0801c05060042005103041c4100ea801b107001c913001d160515680d04007142c0031001c2404203408105803030b00144150300b055000280030400645c024081396103414100c070b40b601400b90405400f4409403074031505004094000c140110341c0908016030b00c0c5090300307520b4500303030f4204020f030710911403420300c0700030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 52287027 1250 52285777 52285789
    0x8070605161404052701030501050f09030703120b1c050715030608070b0906040803070f030f0305060901051c0503040801050610090803091c151e090f02101106090d0806 74
    0x3441079100769140034102000c100030001188500d8075490b2166000806025519030b45c0c0d8000c42c880c10000c81c607414840a21024988010031407445907009110302004650300401c010441e145811000512444050125400c1d00c40321340d000d4411501480e941c4c0400100081e8107045032244102c0a084428209080301903030328074451030030941d00c13105080c00004e00c14002840d0880000b0045071030301e0358943e04281035030011841550180b0841104400f8140c200c07883c00440c80b00ca1130200124035103039000400c9414107000b0076014008200c1c03007110188044c000f42081c15006000c49444a9984490706c0c00703070004030340448c060b01c00c001038000c50038000d41001054074004000703503080162500501030792aa5410308240900e0814600102044100001c01e00142882ca804600303414810511601858020705442900b40380410381c4000c02c3c40c800b24004080e504403030600503002c01c07000850711108180c20020740b41c090340040c46006500062030740b4020b510743d00c601e46a65a51000c00034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 52288277 1250 52287027 52287047
    0x901080309030a1203090c08030a09051f03090201031e1a03030c100203040f06021204020103060e070e0411040e0108070e070203091c0614010b0409050a05072a0807060516 75
    0x9050f510640c4028001102c0804d6110651643c0c80c1c002100d00103602c0d1844000f14a5221103800c1c0c10000c0c0007000c255110802c4c0c0b010f00019a1071410301031500700130110501401e0200340c10160303500a500110383c4280c0002d00001c403140440c3e03001035851000d80c0c00030315008843c601d8903000c0520103000d5040c080207803070352800c0c14800340080c3c280301e03580d000113548000d100325850044e215003c07001407a82d202500140110a01104842c600f500c0050100d901c01e40244ac031900282c0104544076904c61b65140c0303100803d440c0450001d00c84c000c503a4160203240c100d400d03d10068400441d0752000040c1c01011a0900d142070301040c0c41d4544140d07128400d0000054000d07002d04155840d000850261648091007050001500d120750024008842c90a030401c0c00510300010f0304000c101004c2c05450b403c84500041013159040280c4040c11400c1c40000088411104440c00d51600c0312081500349460f0700b1003041c580d6049280f900d032009010441d14411251644000200703071a103e100c40074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 52289527 1250 52288277 52288279
    0x6040503040e130b0a050a0e12180a0e071e0801081c020f0106080d090501140304020904020d0c080307020a06030c09031410230f0408030103060b010507060510050901080309 76
    0x15180c181068240d1842000040103454501614025100060b51a407200c51088155010000d00e40c00d1000c855026110a40d05110095000c011070700002e041e0783c4211000c50701c08ac456000008009008140e20100c1580000351035107505003000641a0070803602d80a4000d40300d202c080300203070304a00340c0318000c081c055500c070355201e5000c40c02c01c200d07075140212174160b00303004681c00f5406a24469007592050f4200d022143c00265131143c0450700b220784000500b00900346407001050484100000d0b0200500c044d2003100a0000324081d926807010503403c558004140c04030140d00c81403400e84c0d03548070841c22402516040d00000350340d8420701c165a00380343d135175940141e0140340d41c4820038090440b60800040d03000d0600c1d4030340c0b000403d200e510a030058070b000361405562a80e0000808900c0240101d858103044010840007a01d0750080301e05480d4040c0340052208030140049449005000c0000d10940ca054140001c1054501140741160009c6858240740da0b04c5130200750312400b805c900361f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 52290777 1250 52289527 52289533
    0xb06040b04030308071e0306060809010c1205040206070c03050a02090a1a010804050313060c02040c050c0a03050f0f0403080903060907080a030e0d020603100e010504050c0f1303081305010908060405 87
    0x740700003413141500300e07040007051401138030043c3c0201d8981d001c03112520400d40440c0d65841d042110035081508a540180602c00030043c0e404030a5000d0480c070b4032007100c90490f0b80c5c0d0300b001804640d64201503510300c64000a0030b241030313034a9240c0655240008076044c1d02c9141ca000000e80c04c40543e0050601261054610614111010380152295403010344211828007080c00b540d42000d43c0003c0f103500030101942c039044034400d540140012075a041505000b0040200000500e4440020310310604c40d6151901c1a51a0381843c0000c6a5000b0840c8854275080700007000018000c40c030b0007034040303080d0480598046890b9030b10700c160780da40d1500c14071050781c015045500210b4041c143c00c1d031452030041c00c22002040d89a000503903d42c41102c1d09400da141e25401031006030002155140940015242002141804d00c00d040e03180c0540303985255040c80002e00c504020320f400003000011540441c3c100d403a27544640c0c540c407120382640a142e002401d0030304000b51482c000505140900d03000005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 52292027 1250 52290777 52290779
    0xe0307060e0910090f020a1b020a060c03120219170f0711030f030703150816030206030c0904060306020c0d030207020a09050711060c0702010f0c2409020a080606040b06040b04 77
    0x28040e00410040c90100c40e03c940c00000120b0410070f000d03014a81c40c9041c001603403174009003005000c0002c13200088403503e0040d1101801a104c4014080c10ba4242d418211032800041c1703012180a0f01202107854564000324481d00038011450b02c10801894903103400c4400286440e900c00c0c00202180c40d5158400c0c040080307031400c0e01038501c0c081c40081c1c3c7d0317007941d181c0712111182d60043d40c0240d41a90019940c0c01440d665240c90f0b80c144400360407440003800030a00a484541e18140d05404041d10a00303000001c6040d1103080c408a032800e0001510501080c0d95078100f10700290030846042040740108401c40718590b10920032a503820343e004040035662400c12001500601e4000d0500c400d029418035405910360003001840d110350780301452155a04074500c001030172811615103e0003808440b4086200080121400105494a004001d0894040034135540050900c4070f0002e0b40182e00d400004c1000e610108807140314030382c190b50512a06c800403061101501c101e2250481c0300200b448 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 52293277 1250 52292027 52292029
    0x7060510090207051f090c0807050103140c0316030605030109030c0308150d06020702060403020a03080405031501050319061d0609010506100c06020c01150b0702010f020c01020a0f0503071b060e0307060e 89
    0x4191241c00600c2e02c0b0028824410ba511f50700f07003a84035007119510b40d0012000b004103690500031668074402403a4903c2c1035040500300c50403107000103070074500311007071158041c96000e00ca07500207001068010002e04c020041030074058641c8002c003205034002002e900004460320480c4007945958900601b203d01000740544891009400c40c10307049910800412000000d40d0302d5207002000b0b10300030748400e580c852508040520780560b8000039070203001404010055590041451503142042c6028942828883e18201008000801741c9070140142c4695144d481440055494400c50307505000308429241e9000b0040300c000088240400154180070000005801d9005825806840e02c000b0445d5040f4415248401c00141c000d041c00d0300c03011510388295a40a11651840c45075070002d4000e00d8030040c0000e450f644084405060303000840e0040c0c0030050704208940c900c07078200d800c40314030716401c0c005480849041d2207030100003148400b070f4696030b10b0089030010032502180c40b100515032891b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 52294527 1250 52293277 52293313
    0x308040b1609140310020f0c10060302090411040f1a090901151518060f08060d1104021606051008070f0806070e0105130807060f0305010807030f170706051009020705 73
    0x2514098045c041c2210024003407070f241c00034100c1c240b5175200f030f540c40b800d44051280c6000851103517848500e04203035081025131992a207054100f90841420b4901c001c450000c85c01404500d18118400c40c980002410361a820074035480c81d0040844401c1c0c0e0301e8890440240c01da80140c0300c16582021503840800c41078205102e21b4140d00742d142440d102d00302148896540c0380c040d0341d0100700411040046a02c01581c4081c40c036030310800c112240e940d0b4650390388500080042185155015030360000740700e40386601100c242030b02c81d60322001c2071080703103810002181540802d1045900f2031241d05004aa5401800c880f40250b4040c80010005962821030458602d10144040b0b41448000c1080c4500c00c1000b0044034042e240280041241518090000f0040c40e0038030100781c1003618000c0144100c1030045076150807240c100b1850101c19826040c5214800302150f401d4030400070000300e02c1c04000e129081a8422034241c520881965620303900c1200340d218008009140e90086056a10020060 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 52295777 1250 52294527 52294559
    0x11106040b18070306050f1b161101020f0102131406030c0909100b070318090b060f0f0405180a18020906090c09150c1902010f050f160308040b1609 65
    0x51012209595601d0f100c0d01c00b110810380c0c1e040b00c0701e1040c4080040050944041d408c1000c0f80680540c540880e81000440180c00403100519a240c034841c41507050703101b00a003050400558000b150b0350741a070304001030803240b20b105400b00241400018441d40c0740c1001941d22403903003501550314080d201c00c204aa004d800501d0700119400c44807020410044c05000340124900c20380f25000d4018081e450188072100551001103418140015080c443d1580e1066600780886080c0142d1a0900315005c403105018a40140c6e0b04954040d0403200e8205800b90400d000c5d0b07404440401078203a1441194a82e41f00d61a0040d412048070340c04500c483c10007809103a4004540b040e1070781083c028030002116003287c0609031075000b00105807000101c00511403101260b44654032890045aa940003800303440d2035a04d41000d11a0100740d41c50103004000031a014401d03120b071a1981841079150203094580283ca082d24206440400103c0c0303001c00d2811003120580940343c190149181c01014008681c031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 52297027 1250 52295777 52295821
    0x4080406050702030307080406031418030706050a02040801020c0d030f0b0d0f02040b12030c01060e060312031009140106180503060112060f020a0801170a030f030b030a0c0b09011106040b 82
    0x42040700201081d441005840500b0850b07802003201521514110a00c01010344440e520803244946070362100d2000dc03c41342c080d51b00803030216a55807603400c448024042c5900440c455400002c0f02d003212900440c2003000e0b01842d45041200c076200759102000c903500e4a00c102d03004900d03030840c1000700d100c2c0340c1c218420130b00c01400440e0309204100403809042d0b580e496401c5961005c06d4000c900203080c0076140c09058022410804ca01d070400001c0d0781c0f0700c468491038540680000c0440c83c03046500c48a0005032544500c1801001c0c074103441c1010300c5400344174000010b025401d25840d015404080030044410085c0104110390a01001c0c0880341d080c801d04507801079662407019044242c50001d000958900d0f1101e2169624098450040750200b80785038030f42e81c110109c400000703a000f1000151003044ca04d400a445200b180220b032401e40c00c440c0190a20081c0c072000624114248000d0400f4202030781c03010000c82594082655034001618010201807410b000503664a0450407032a1107844 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 52298277 1250 52297027 52297033
    0x20709020405061b03310e04050c0405040f0803010b0a09080a12050306040618020c0601120812070e0915100c08090607060603120c02030c011b2a121103060408040605070203 76
    0x406441c1c20000b40c000c451171041c0321b4100b00030200c0c440c0d0311501400c010640054902c242e40740607902d45807640e10201c1250301c01da0391807010900b403100108502e03002581c4a40c2c8035a50303503180c403100700498110640b14000030742e140340049100c050100d90b64545552100e8520034900500d10290b8540d04001d00700741e003003030741e801000602144c0348160a50011120100581e2500c030403400504180d0140c10600c10945603e0031440010700752003c83c2d00160400d030501069884a00003101c0784080c00d40280c1d40070381001c00748a094070001c400001c46030011900701102c240e800d0802da03611400d821010307086480031301c0843e43c00e050190041103107911900b0009011502c0c0ea440d024880309000d076000000e28404010400c50908000003074080c0e000f403d00144880103d0303800031802f120284020032080c0c11000041c2c1c41140006480325582080412005082c2c44960390401d20080100030344095051038012490b0741404280c0074002c603000f051041c03910b81070003001e880c81c0d4004001203030948 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 52299527 1250 52298277 52298287
    0xf060706091113020d0f0b06180d02090906090d0f0504170102040801090507080106060e1c051c0c0c050a1508070e06120411040c0206061903060603080406020709020405061b03 77
    0x3d81c400750228000d40030070100588035020310f1000f03030469005081c003220740351801c1e4140c40030713680320010340703203c913170500e030200ca84203400004600d14022901000750020313001c2060044000c0003055042c403910034402115031503040a1011608040c140d0410004500104014848403110b0300c00c0440304140b140000d0718041d5520541d500f100d0001c4001c1d40e05e80c001c100f043c00404428000c01c001003c40340750806203001190000350f0041c901804051490241d24581c0701008003c1c0005442c11441c1d1007a640704011070390b40540b882034000c1044401c01100c11002c5451300d40580e5490135624a550300c80600740c216a0140c1d200340c0054001c00a01c0100b0b0b508131515a1000024010200001440ea016082030b20b842007e0448440b8142d201700e042c4031202507190f40c00180700d0f9000c2001c59403445d840c66800d83c264403a201c07139013010340910705040c0040f00b4450004028800c50350300c2d50880e4400b5a845030b40c0c50407400389000340e56106e1020411117002c1c10a4002d0061001000c80c1502c7c94071b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 52300777 1250 52299527 52299529
    0xe01090f0308030415050106051209210319020708040504050403050d0204060504170c010804020f0f060d05060108070f020c0904031101150302041d07090e070e090c09060f0607060911 80
    0x409541d8011109100000104002c00032100c4105240240b0048280059414a03070045c019000d00004880c80b008440c0c0007526481041040a02840b0808110703200001c03c0c180c6070180364411070300c41e40c609400e1090a2030b03000c81032080b50301e69a00310003141c0c20942000308000140c100600158100300f800e0004803c0703190180300071310051089071280c580d1185000b0035000d000368a07580303009031070304202801c2e103060b44c204408643c800c1d070442e008203e12110f200007d50303810703800e03003040d0f0800404130700700c444d00075035501c943d0280c0000d032200f020319030750054125440d1040c1c0c622900140c01c03440208000f0300303210b6031aa030010300c0781c14992651000f1001c0282151482c980411004491100c2002582424454029071582a000b0056440303d901c8030030f030703664803203220380e00360301e55102000c0071580410303c040b0020f007003440c1d040c2d644d40c2090781c0116590702c88184494824000315000c5011442c0200d14a0030034100649410b0416580d602c0f00002420200d400355407000c000348804c0e000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 52302027 1250 52300777 52300799
    0x50405060307030b03010605120307060f1b030504021801031e110603040b041b1a1c060b0d05060306041515030b01080a060f050c070206130312200703120e0109 70
    0x11400c1d1583d4000303410560401003600b510f1065000c0381c01600000c1c1421310f207990100844d41581d410038004946064500f001c0002418907134801c549055004200208542e03264020034025170003128201c00e90040510310400307182007072000501c040407013005001c0b0000e141102c4031070345006039504000c02c851000030444da40e1040310b00b2600103030071004110030003003000c10200100c00003405c1c0200190815000c07a004030354071000308046007004140d00315008c07015040d8a08000140c0014820a951414947c415405c0542c242d00c0280c1883d0019105040000b801c9202d40d03000320509181c604031160010041c8840c1c2401610003009402c044041903140383c1580c020240700006211000e50790804408070384c803100032070340e079141000c041c020342028200c2901e03010307901114003582e10070f0000034660403e046580000c1c0210a4404000c0c0542e4014104580c11035490405510400d00014070341d4a4155900005101007003c100c015005032040780c0003d00c100040c1031038410541c40700c0924103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 52303277 1250 52302027 52302031
    0x30c0102030412260307030c020c0603060d0507180506090109140c0906070215180a030b0411031f0605010e0301150605130f090b01030e07151d060307020c0405010506090a12030504050603 82
    0x40180c0d0001700380322945515100e40c80c10a403551002d080002000700001d030a40c4000307230001d40324076006142442445800e104940003004405041449000d2250111025110403618a07205180e24400015a07806501581101450707585c807450701a644c00560328141d800800707140b5001401401804016140c0c40f10541c41007003540310890302c1e200030002400d50201402d0038a405203400100400014807881e603800d400c2a03200c242c600c2680d1034640070929141e5a100c1c0506880300b10f0300c80c00c0403824254010020341d00203a80312111501400c0070315080c2d4002c00c1e1455a00700110000b080424884c0c0e024005200891400c601c410f0b541d48079540080501c1d4200c0c859081e41c0b003084002035a01881103200c000c010364040c10000e850302401e0000081c659190b0001e000c0c5100d0107105454421480c0e0810880040031644c40c1e003400300300296070b41010300202c0c0c00341e8075000010441e450844281d805804001b81031a40712800c0c01c44000381d444840c001241440700c24040401c1503510708003d0345c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 52304527 1250 52303277 52303343
    0x605032806051c050606040203070302120f0405330402010203040b04030b150d020901091104030204060e060103060b1303260f0c1908030a1d1006030c05030c0102030412 74
    0x1c0784541c201001c01c1160040b035039003a07059240c940071850000c2c0c400304a61758800000c0300c0051302c83e659000182d0213841855441d031403008181c02042810b283c1c0460f82c0e40030358040d00442e010450720b030a070341c00011298440071481040e8803407255006105203450b1940301d44180f058a0509036250320204054005400032940b80c2070700701c10008036515405500010300e02c00c6034801650301f0290007160011806014800f4020344941040c3c039084c040c8800c44000350740c041e20810010713071b50707100d0307404901010784070980021f00309400081c3d00e1200700300b600c0c08250300d00b200860032131443e9070742004070000a000e031820164803501214002c921742c014080c01d40341115101d03070382c2c040c2c140b00340d09010b0501301051a40b8030007082a00440c240e50300b642e612841c5000c0014040c0c110211a41c02a0360103218070609200754584400c8205a0360001d0044030700c12203c55401c951a10101501c4000ca803080c41c1c0140e0062004020207802210480401402208026242459100900104040801e90b0b03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 52305777 1250 52304527 52304531
    0xc05031908090a03081b090604030605070e01020607090612060e070201051b0711010509041401080f0f1b060f0c03040b07033203090304090509010501030501150f06050328 75
    0x2200094000210750792015103000a0903001555079005041804094600d030b814441411026032440980000c50390300440003000c40b07803620b540b4a000c070090b00702284c1d4103000980d80103160240b54000144503009600c1910341d042002e05006c022940000e0b103000c5214020384401c8001000040c42803600d0041c0b509500101e43c5140001c440017003040703413280000c031390303841046420041640740301c5c2039003071580c2440e280d030391208000002000b905402100652248052000103224030001079605441c410031410740750070041c18100303143c60b203c00c03603012524400200486103c038030380b0720005d02441081c00211401c0c10400352805181d80c210781c0116040b01400034048041c96001041e62407101840c0b61190342d00c0c800f0600c00d081d0300c0c2861507065030308200403002c58110a405c0c000c3d90060315490307900300201e24254008901030b00003807006480315440c0c01070040d15681c00b50717182c40550b000d1f140f07003000395854848215103c0c1d000601c3c20350b02003180503000c01c02d00031401200d056400d101d040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 52307027 1250 52305777 52305817
    0x40b010507020603040f03020c0102030403080d051302030d080f15010507081308070e041b05031015090c05040f08030406020312220317090c0a05040203090a0816050c031207060504030c0503 83
    0x1f01a140401c5c2a001d41d05661087c00b040001401c0c0100703c0c0da203040c00c0346000c1800d8030346000210307402d65001c0d0003d50502480f045400d9280d400483c03e441803000e100ea5014949801d000e0b100102e400c0c20005000450812680001c0380b10f10300201203700460007400d87c0d5594601c42c1d02c1c1040015082004890056000c2c4000d1100b90070b8009404030b800c01c5083d0318103142000184e550041c044080504a850ba409c00d0b111259a140140041080d0310701846100c400000007042c5600500a00a25050444010428200000694013a2020350300110b15044114120b6110541d0003400507542ca1780c882c0c1042c0e0180c180a0141030305134841e071114400030312041c4030b04189420040c480d1210740d221109103c02e40e0f0b039508240b02210005e59005a0302d1f114022940c1c10183c02040c09002804e000880290b17501e010810144018024000d5551819101c02050b40b00c0c0100c0c2c07003210700c4010901100c07010030866800683c015109003040501040141e868604503001203582940c01080460 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 52308277 1250 52307027 52307033
    0x408070c0e090c0a0f17100f020c011a010905090c04031203021c0b0604060c0c0503010207030908060f1b09011205040605090106141807090306090b0a0c0c020906040b010507020603040f 81
    0x10f4034400040845201c001541020511514990a0300c40e84c1070040009541083c41391042c040d00e0130f0030045240034001d40d44891316060107540071002012081d0f10b810001c160928508110080000050751515081c0785004104209204040c201c1da1019100304800400503100464000c44240691405a00c0e020400b210540c5001ca107003000382d4840c10402c00f00016030b2007004443c00e882203800c0c4500d20302e0301802d203041188101d800050f003562001802c0400d050b0401648005c85582104442041d6502501445145c6058500502c80388458088001c808017090144c02c4448044c5846c0c0c119500d45145101a1075003510301780c5519590720305205180c84280a040007810001d015201c2810201e4042103644e114a8207000d4100c0c039050203e03040900c200c103240015038000c5810700c4000518240720b0701041090f10f964801d145040f0f9503403c1c05d03024150b2100304a4004004012a980e66014030000d4006100c819040243c00c211590050765200061401a4010155001d00109a103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 52309527 1250 52308277 52308283
    0xb04080706140a090b031008060405060423070306111204061b03020a0c0b0a0e070e070318150c12020d0204080c040209090103031107050d03020102090907030606020a03080408070c0e09 81
    0x140100c0e5602d2010803803540e4a90700700c0f07806400c81e4080ca030390540e03036500c90041500451442d04404590702500083c0424080c0014101c1c0c0554016813243c0b04202030fa902030401c85103501d55981240c1c00581042000c20710507401040340768050348565180189000000039481c20031501124259960345e05002001c08000c40345541103a241411450000803401c050f1444100c643c0c01040c0e451611f001800d10710b860340000d0121194182264481c030780391013150201503011100b85001925103803801d4588600c0c240e9503071000f600b10b2444d0183d0703003128110b88007800b19001e042041c03015000091914a00d280700600381202001c03170060f00e4600b000981401e26194030f12480c0b280b801400310714002e94079080c1c41d030704403036050030164044901001e0321400c02085034480c035030102c6801c8114091540640003000101421607900d10039588c0c8241c00c0e41203c030720703001d0900140e01200003000020300030300540d40c001d801406034508010941e51680080303086604075042d00242c0d28244800140d0030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 52310777 1250 52309527 52309547
    0xc030c0f051e030604090f05030c0d0903030e130608070b070303050108010204030201170a0b03160e09070e0c0a050c1002130e041a0402041b090f05030105010305060f060303040b04080706 82
    0xa4500185000c0440b00b20001c050b02e542d50203040c81d1400404100b1954941e032080203010384c08001740701700346801e04201e80c0b242c011101003a46030142c900400c1ca090301c51a011415207a0644841c0400407c490030b00840d0380d070902d01085c0d5075695200100300d032801048400010284001c4140d40e9a005203070003810b4601c10b0348104204d0707006010510041c1e0b0014107074407007403c403101c007005a1303036840ca80c0324060301841d011190140105030100c5c03002c20411894000365030214541c0c1d07520f500d90254441c2d40f02214403a00d28a428501c01084100440f24018812880c90780381090038850f4000c41c0c1810025134180101d64681d0000c0c1c0c00c40700745c900c03650281c01080302c2041d0708036515042d00c03181c0c00008010b444440c80c51004002a08641d210761143c6602030750741e0000d4450325611b0744060030800840c09460002c82e01440002094601401007506980d03201025080f291614207020b02c0180010701140d5050009010116880c0d1124000c1c7c4000d20405004210003858403401034101503079 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 52312027 1250 52310777 52310807
    0x1060801050f0106270e0103060e06160302030603070b03160923060a1709010b030c191202011103130e0106030605091605040b040b040503011a09070f0309060c030c 72
    0x50008101c010100c02c11401d04403500c0e8100061107420a5001141c05030034460213204543c007030880031420740141440c840c107992054104100e109402d0a186568840403500050b41d03c5c0308100da404210303c03036006960018006001c84804544034030048079141c10407941d100300e108002d0b0150441c41d070302c091510300a20949100d00311004410741484258010341603414090000040e800362150300c22100c440c120300200582d41210f040089001d80a003507a0707482184030740b04102c0002d816140001c80759030640e01d4080c030201d6291415080141440c0c90750001e0b418065080c4008404840600003040f15448a03010046002d083ca495a6544c010607041101094075090050013140c5a00280a420502d5a80780408c041002c200c04c8031244141d812282020f080460001105441c4a02401c1a100110024082d040a0084041099041104282d80b01480303101164000c3d00400000c03800410528021600c034030991280003d5409500308000080c0e60740343c0d401c406a5201d1240410121 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 52313277 1250 52312027 52312031
    0x60406140a0306110405090108010902030105091207140c0d030c0308010b030c0703180801020a0c050c190510021c080114100206060114070f030e18010308040b03070309060603080a0201060801 84
    0x41040d010601d1050207000080c4615aa0941c03101e012088605442c0207100c0102005481d6841c2e140b10b50182400f59000c81c000d40c00e05010521040c008500050310a074418141d40c00d00d061500c404100618502426840d40900d888002070341e00e4051003135071994000d454482c02441546001810346005a000e01854a8240148039a501181c811107041c1c50309403034400c0c1c2920050030840e0b00b141c41544038110355880040c03442da403141c11400d11b43c1c01d98060402d641010580750b0501014444100d500140359440310418041840d215402c03041020051048500050120301a070305202103001d030040c0414042c500400a459025105608142c01a43d0907000061200e002a559603800303000c403414402c541200c40302001e8007805446425400c01300c1c0e101c0d658244d04015002d0301c0e89a04c101d01502d040c1c549048040c2c01c400e03000d0304883d4018501e525140ca41180c01c2c005800280c02c120802d030b11060b80c507002c6012801464040c40c00ac0c00c1c69607490412001c00307400c4440c03a0f030011030964 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 52314527 1250 52313277 52313309
    0x307080c0607080306040b10120e1204030620030a05060f030a0203060105010f0c051204080106080a0f02060d1113060806040606020c1005071203050a06060c05031c0f14060406 77
    0x41c49071820341d02075075485200c6944a40b200c90021b0094a01c40e0754454203d034201d0141094141e02c03811405945030580400c010404800c81d202c1d441c1e1503020788804014904220400000e0f05a912100098034003c02d03100034501ca40320050001d9000fa11400d15064980b41402924580300e905104d0561003200206420345080d0b000c00c0d154201441181d0620400ca404803032000e014041c480000c55202c2d081c0c0d000e001079407c0c0b0f41055006030207004011b41c46e01c84040b5062000051101c00c240d04541d0b00c816290850307081050992002e04083d080b640c952008840440d14180a4101d0740d600010b8904064103092009003101401041c1e584030380d040c1441002100d4021400580700f0400f680c005164012b000d01c2a40d10340710700403004140c0c0c0e40040c401c0800d02c0d8568000ca00840c01c03c0f00a0295a940344070484640080640143c0603400c02c00c02c0014401614101040000642101184c0900040f002c0812902c0300014519444500750400c40240740a10406001d0008480141400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 52315777 1250 52314527 52314529
    0xc0a050108040f020a0513050405060105060c0604110a050d0302060402030d0503100603110708031315060303050a0e030f0106080c0901050406060807050c1515100f080c0a030b0307140307080c 84
    0xc07200580094003030880180c0740c40a40d100c90b594039010f0400074100042c3d050030b03034088074001c0a040ba400d641d140a501c1c0045480c0c6032410032581c02021380f2006025588a503251030307154060120b42c42d540030912180000d6540c032952040043c09009801030821407400e80149810100b56086610409c00100100f144903072001c41c01da0103443c0305103400503581004c03c1c0b031042c452280c184044e11170302000c03080000a44210384050446449002200d003d1011641c00c4400e4900c0c5001c003e002c03035420300809450901c24070058243c00401800c49849400c09124107003100d645402c8104141c10581c600443c074204900d1300e41c014001607804000c0c0f40d203490001402400d01800c03040800c0320005580e00c0e10841084a8002c058420700d01c50f0003414101c01c410490780074030301c06a014122000c02c5200c00e500820f40c0030403c07807041d280c01b001ca51754a2101941030340082c03150003e140c0c0ea414454015203007003000d48050b11210049001d4808400100b500e041d850ba07001e00c0d0301b07502000c2c950020f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 52317027 1250 52315777 52315787
    0x110703023a1e0303090b0a0606090b030c0a030e1011090a0b1e0310031505010914060f01120f060e18030a05070204051005040e06070323060904030e19080c0a0501 71
    0x1030300c0c10041e80400e142c00c0d841d0450250843c84000741c00840080140440b8405651008003141c0781500c403c140b161b42c1e1842c80319140002ca42c56090700c001808032002c2e031800b90700810b42000d494820340c3c1080d050200e40c10200c1d4005802170003100d10105651480c1e04001c0007000151288000040c2401000f425916031031059040e2504007201c00700100786c2d0360282d00440d5010b1031f4000d26a24000704c401b0241001050244254604c0509200a589003800d0000c03409016600180000e1850325600c001510561000c440e1903030703140d907118040e0f00c0c181c1c014841c1102400715078400c80514181003801c8145025200c03c940200e42003000b6240f9190340080403a0202a810b075070105180c0e545410841a000403640501d4001b418081200f50410300400c0c8240700c0c00458a0401c070304034881c410942c6181e496078810706103a820300c003c584c0c549030a00703040c1d42c030030300c6450401400c00511000c03a01c2c0c1e0030540810401100d083c081400300c800c0a00030500c410301d060b03800c40250340c80c140000300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 52318277 1250 52317027 52317053
    0x30c0a12060b060903030703050a09060306080303070804051c0206060f010201270f15090311010615080408090d080a03060614030c0a02010b0a0b09040b0607050c01110703023a 77
    0x1140641d02c08400c5420746401c030541ea1a074500609507a11100c40e400d000c1c0185d4402112900010f0010380b010510500030b2046005035010140110306580e14201d055619510140060b42c0c50f1180701d4688180d051144c920b001e030090680d000d8486070030880144481c144d501511b16066905120080507600b00d090b20289401d03107030310840d0110000747e0400c02a1903907800c00c080c180521704011030720b400b00c4980103052040d119170b0740c000040240700f00700d600300c641a02038842100b85c015002491980301c0c0c401c0e07a40060061860500d0004200c001484840e040c140c00c881806010400300c06294152003104001c01c914105610103601980403480280701c02048610324060100c1e06045c0c5130310135800080b0313440700a01554041c1d51625910031107900040c0c0c085100300c1c2442007080e641e0812006540a441c0d12000601100e0342c80c00056078031074843c1803020604e10a02c507001025a4031948040d81d060038441d10380d103411040c2c2c80101050800c2c628406401c1284107108400900180710500c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 52319527 1250 52318277 52318283
    0x106080a0b04020d0809060403080306010e030a030e0d06060b0403050a03020d03020c070303080702030c010608060a0b1801090902032109010809010c090b0307172403060c090d0c0305030d0b030c0a12 87
    0x100140802e45003c410301c0c006c80c01803d4000744041404800c100f506002503003d0b600907240c10001007180010150344900380320009002816082c12060702e400c204940e0942940300d2000854010b071140040582e0350480e500a0f0f81030f0744850790f020280b40e018007401d0391007180c5184c02d40c507140082c07000715581d50781e512004040181900000314030314402e00585440400d818000e00c4403503950410207a4400094030000071452510010000614090307014030002c4003400d03035009a982c0b81c000d248009180313a07081a40c05010301c0024110340703450715403040f4400e040300c0d23209d6846010600c001000b0500003415140560326203581c5500107500000310800311490300e1200369076a81d40d650102c4403c2c2d281144000344e80806414864020b5407024196043d10310a808108149420000c141e40c60000b13840101005404115190301c41c1031188944081602a0314410451956540c3d030310304d1540124030030149a03a50f600340914916081c000450541011681d440d801070a01c1c0e4520304849c8124001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 52320777 1250 52319527 52319539
    0x4030c0e0f190902040e0a1202010e0c101b06090b010b03010302090f0601120606020304080d1701090b011b03081005030303061305040203010e1c02060a090f030e0316080d020106080a0b0402 83
    0x202d5030b1409a90040c14a055003d001807200d1000c0200e443e0340c400b01a54102c0e04040340a0445c02c0751481482490482100040180100c840440c1841400220760031204100302401d94106c00c002042c40569410511502c000a5503006034104800c41e00e9040e00b0880540c103040004001607a901c03905103401c83c200c0307100102c190b240c58005a0f44200191500f80380c290920744002100e580210150048441c0d40301074039510294801c045070386c0b80703401c8068440329a00400610600c0d0443d070258000617010704000c00c859400c401c40d104d1841c1b250900310b0000700c00000300301800c1885200c41c0000c000136001107046080a5000800ea0105241400c02c00d940e99800a0f0540d034094100e04200754040040e11a840904900003c005074244444009481200c0200d179031703003d0354800e903004c3c29007021081001e41d0301582c007281d1024071142c45c246d01d8400c0f44100400341904120b00401802c40717400401e070703150140c0006429aa1b084d0300070304c031329006010040041049003e60341e80c05030781158a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 52322027 1250 52320777 52320811
    0x115050105030a0e060109060905060405040b0711120d02030105010f090b09061c020301080102070201020d0813020d11090a0204051c21050409150e06061c0507030f020c0304030c0e0f 80
    0xf040000e000c40c583c070031041e1059000024408445500c0101a260809820300c040e9490f90180310580b132b010344005000b00709045c0010400780c86110f0462001e011481070300c0d490038050250030107940023481c85109196001004100f5503801180c1882c0c08001ca0034010003562410500480c280265000e4600a0718001138400320b01c03a546a003404042e023085d00440d22561110061b03030007034102900890240c40b031000d0032000d0700d02851841d8410f080b451215a94519664240320b0a0341c0e55000807141a0542c454400c501c0e500d65000358441e090214005890754946004c0050541001d12102c0c405800c48440e0000720b50740c41d209106070840000602d0000844903012150f612440d40024102c614180710402e1080350400403400722103501301c1d82c0c02e0644501c020060940714821038020940c00081c140c180c80745868102942c06540f0707043c0001d041414080160603030f40031088000958000040510821620126a501410364901504010f03e000d01428400e040068110050754080c800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 52323277 1250 52322027 52322041
    0xc02070b090609030102030112020114040e010504020a050702040e0d020105330a18150504021c05040201021f020712020c060d0b04110409090c1e09110f040806010e09011505010503 79
    0x886030741c900f01030001c554035a541c04010540a08050040780050108204c11903d000220103503000c1c0d807070402e00200740d40d1034203003000025400041c0e0328040c0070060180030007690303403441010440000c05010b0420603400d90002400c450300100264541181d022043d016040400303038140c000d03141c0500c5000c5650223640040c21401140e448000070041e6035041200103600d681210106007000350307482496035280c030208001da004e80e61061040210550050000403941d4105503085401801a5611100040740403625010403280b01020f10350001484810043c1950602c0c0c1c0003000c502c003034403d4200600c00a1020b00c104040000c0c003540f107100b08503103036545500083d254154090102e40c0e540d40c605c0190080c0c4141c2d04159080100750000213010190801d03054495268405820b07200c5080c030401000070f100d500c2c0c404500f040207010078107102c0c078480002c001411654000b081150b01d04440320302280d40c010031071005a4101100703241400f49414100064900c00d08100e922a40c3d142 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 52324527 1250 52323277 52323289
    0xe150102010e0708120c07240f050306100e0a03081902070906030b011205011107110f030714060d0207060c09050306070e031506010e0a031401060506030f070e031002210702010c02070b09 82
    0x140080344070b004201e0b26240c9401c1c04448c4420502400e45942ca00b00b50510b1065441e40000c0f140c407508401c0007000c4299044c4030b82c400d001082070085c82d1811040c1c0b60780b180710140d0030025400001da001010500c01040c1c04010070001050000ea00784483c038210780d10304e1201503040c40342058164055980c2010842e0079003001040c5010500c249468800c0c0c3e06000101c1ca0086004a0040100c82c40d85001b42c140031441d001521044040300c0c4034000340c0801c2c4030459018a0000000d00e50900c910340c0061014000c011040b900740d9280d42a4034208402c15042c44009000c400600032030540b686c255480204884601d80c500031008a0240c0e502401601c4826004038465880040d5600100c20000c40b100802607002c10341e0001c0050756218000e00c4414072040d5002070864402c80c0014070341c0c0c0d105101904104101a06907401a0150384d400b800f643c0283d030030507149803480c11001403d024611225940030400b03200134800400740d41c402a403101024050301e520303000c0000310702c04c50340c40744 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 52325777 1250 52324527 52324529
    0x809060310151806021506130906061d06060a020a020d060b03030c010e0d02010603020a030210021f0903030506040203060d0204050c0c0a031e020a0b1603060e150102010e0708120c07 80
    0x60784000752900000100074440242c1140c00038800f6980f80000c60110b100056901041d4210080701000d070f1583c07000c01240220282031088010384030030140b00004c0380e0340583c2c8000d1809040d42032603040d06854541032050000d1242c1e02030f07442031000c0c82801d540003d201e24203135015622803600200d541005d0019004080c041600340c0b000181c642000b010561114011158050541c0c4c41c1c0450028103c2c00d81e10f1a201c069404452490284058074060b810610100c1d0640120351001c10140c1d008c80300342003207215000c800c0d030382c4190712410306801d8000e0030b40c000d004035021881d515001d00029103080d0a044064055a80d91000070b28081c540e004460241100340d04031000704445140c01894000d1030043c603000c618001c0401d2800c2800011000e04084e0321070301301491035903042255445000e28840e980100f6848100c00079202c4c440003101809024a602d001c518204c00d640003909649458180d0141c4e6440400e040001032030105041108440c00d024440d030f554a400f00c03e40c540801 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 52327027 1250 52325777 52325789
    0x3030902030114010b09030105061f031d0105040f06140103020108130303090503030901090c0b09010f11031315080609010807050f030c030d080402100804080d0504051e010506040609090809060310 86
    0x2e0340c3c0c004600746250303002070003031410114000d00c86565101d00b03004030800250820702c0e00c1c0480c422060308450207a00003114802c0040c0c01d01a004201140040c2034600a84055450041c00c50980080c482d050252689109580b02c40d0191540b460740000c01002004000c1092503108200f150205032007034228542c9150002c0480e034480c100810b0441c001e080361201110048005203002a041804905031112228140c540d243e5003d00104103459840780c00000301d00c280000c000070360301400c5070051072000e0070341c80100f001e40c00e4405d03070050301ca440c001c0d14541c800d040c441d004100250780050b03403030306a45003910002e0140300440042443d10440c0ca48040d45802401e140081c1103038080141c0d80726a0088410440c0301800709001d982002c401e8501410f01002000114061220384c0c01032500644140101e820050074607005c0c08242d070055505448507512101401041c0c034190141b10003411062904003c0c0b03000c50780d100525485501c14003800b0721008000a807041449906003002011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 52328277 1250 52327027 52327061
    0xa1a0c1509070f03081204031110140109020c07050f030106180203100b0c03070b1003120806120304080601120201050c1002121e04230d03060801060e060102030403030309020301 78
    0x2019140e0000c030641110114090311030041c0000700703c04600600310440350050501c61400c201c0d41815900d0110081054040c00803094020700004000c0101c945a0b02c080c180014012101401c7c2c064400c02c10380c0301782c42c080e0052140507000c0f0000f2032484101d81080f40d0250394010000c02081c00341403160302c039840541c800550428191075a400440c0b00e000d4141da272030a499158807040700355014500c3c144d03035264400d000c20b13400100d00700d140e140c100107a035050440040e0360760341c2c5140381d1100380c0b0084000ba01010601066081c4805c0d24890400c0140c080c40c2800e08040f880c90f0341f01414450b01001040031000c01041d64056011903540c40480c205036800ca00b141c3e241c61011b9400b02c04401c03030844094000a9420002902030f0f4100d00c840c14404d10140c882d521200a0251142120f520450400800400c44141081412800d0035943c402080c8240b80c00320320742c2103410a9105540c400d0402d01004801c0c2e9001c021141900e90500300010900080d0000c80e004000005609800382 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 52329527 1250 52328277 52328293
    0x30a08070f0e12120c0c090709061d04020f0313120f0507030503060607050102040303020a0b0604060b0403030806040e160f0e011511210912011406100e03120702011206050a1a0c 78
    0x80802e0030086d82e5001c0d61444120f44540d80211041e40080c070424000a1441e200b9030480c0d1903018545d00601d00c0180007605052511030550b03001e900030ba40155484411000e008200441d1070900c6e845c0008500f00300082a40c442d0f000340251040203802010040000b0001d481c0b035860340305503150150800c0003151240e40703a1802955800700b0540c2541c1c0004c5010001c1d90524044c002c0005550100603400c0c182032956505544600c00500002e91040c0c0341e805452074550b04214a583c1804071000280e0301c1c030700e0114034102c0c90404c0d411100d8034080c150010720140340c02445450301c1d9900e0f4074003400034002d000800c50a1401058000110b03400704c840601d01024180042c00d51840222840c49085008215550881d40041c90001206c41c0701e000150107840d103210b2007507440d9500d080c6104d00490342d000007420103801c400032000c01100462341ca415941c3c003003031445684802c81402c002d4141060300140c003030100342c030441c8030b5014044141d02c10b121100c0103403480c03034041c10300b22030001d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 52330777 1250 52329527 52329547
    0x10e060c0a03090f0b1b0f0901050304050c040504060b100507050c010e1809030d06060f0905040507030207021302120c030403080f04080705030c06090c0307030b150d0b010602030a08070f0e1212 85
    0x2900b05a856054052000d0080803120b5154001ca42030307c158000d44d185024203800041d100390304000d10030303180c1d40154a0705060a444c0c81c0a2144100c0c85a20009650030035201001801c107205c4262004010081c44514004cc1001a5803d032910742424002040154a800188070301e40748041819040c4003c402e019013150008060304155a550764180f0100762141c10880d15a1f4040d10700c0c4001420107227040245003000e6200d207412a001d4030b0054981076640e0080b40342402160302c0d0000080e40000c801c0d0841c480034203030710703040030034825400e2940c105a10300402208014001c15105c410100114042103070100031a2079295200081d01c1d2511703075028141c0c0d02c031103003114050014001c4056510382c1d0301d1b02050342c82c1a00e62252111501d40c58500841c03680170410034405800080380c1107070700c0c0400c00d0540e0341802071009500540d520310543d07000070b02046016080c1070620030182d25003c4650b070481e07040310400c402034070100f16000600e0034451824820348883c141c0800b0002d0900c483c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 52332027 1250 52330777 52330793
    0x1090b0c2503020c01021207032c0411040513061a0309101404020f0405011a07020a081906060503190b0403030615020d0818070308070c0305031305040e010e060c0a03090f 75
    0x1081d03200340c080d205541f80e5014040e0103403080d9131004000500110010090750a190390040381d43c12001044140d200f0404041001c4810b1800200b1682074003080c108080e25114001500746002d4400c01c0c04040e18010a00e50814520500007031208000300002e020480e00f0055848104901101803140d200084040b00c5000340030b07141a40100c2405040c4810760900d401898121040003402d1801154020710b90300150f0001c100803a4070403035109000410600c200583c000d0403803c101c0c1b403c1c05504078034091080714007641c401ca000303401c489034182800d105000d0045400d42c120b00d80480f16605d0b41b030103d00400e81600031941a01080e11860001070340003964411507107460f02c031008643c407410700740f0590383e0040c085e0b020f9640c4124402c1c00000c1c02040070704074503441030203000350302038417651010304540100c0002505052407032400c001c945010b0080b0504614220001c0010300d17201c0e030321182c80700c100802840d105000061101d1070140700364400000c10381c00c20101109840d9510301512 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 52333277 1250 52332027 52332043
    0xe070506071109070e1504031e0c061d06040305070e090a0201092606090102190c020d110612190f020903121606050a02120708070807080a180311070801090b0c250302 73
    0x140c27501603200c000000c01a0680300440884e0003082040e500e5203000c00484046170522100415030051403184030b1152180300c0a000a188103c0140010904140070b510000744c006111a0080e07004c0c41c0b403400580d820400210907184445109034007504a03c441c405013000468641c5071610400042009006040d0701078003011103080001c0c8207030724034220121707080303090204040d41c028161004400007034220300740c00100e000050444c5040c000710100020501c40c00700d0380c0001c444c06c951000981d15030136120705004400c040c42c4c11410304041001283d80d414220103203c200a00000b041584901c1e6103d0b48058103034040d005104031f02e090003450001e50010006031480c4918000440c0265008850151240030141c0d11140c080d07480500c04c80d10f40001502c0c102c4a40d45e82e150440950300f1051112002034080c0d1200e860640d0100002460041254088105640361980031030003e40100c00042d0040b89620a40b40c0314000c1100c0742070403040e4400d90000c0c020021501d82c1c200358010030f00711 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 52334527 1250 52333277 52333283
    0xe060913240b03130f0203060a09051509030307080402010311160b01080a120503100521060c03060a0302040b1912141504060e01090c090e070506071109070e150403 72
    0x140044840c410601c21200260080b1040c40c1018000250ba46041d03a210708501e500804030304c050241e00345c01080c10200300741c0700801d1058031100c12900b030000c10001400d83e884003100303001007490305192a42d100d020244c081e100b0040000041401d5a1290b007101000310300d000c40c951f41e100200c030004000d014041c6c004a0304201060700026400202041d400b1a058101c03161038058084100102e8282d4402424804a501c001d400800c0e00e881e45200e0302205440c031004ae16848030b5964030301d0700c1e10718010f000904c0340c0020402c01c0079a84804164800300c03681500c0201e100c035131100000302d1a0030189006500001c06950004442010300f4034044090700495000c0c80c14041030401541340c003d041401c0c4c00d5a224000414005007a560240200e807da034000010280d296035a4080c9180550380140000d50300c49180400e42d15083c042d07440104070484516140000c1d681c0d98091040c117a10342c49201e4450080020b05180c000c104c1e1082e020002490b100c0481c200b1103030201240c0040c0815 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 52335777 1250 52334527 52334561
    0x20f01022214150a05070818031506101103120c04030c090504030212070618050303070906080105030c04020c150a0204090f021c0f0b03100e0c0d0b01060e060913 71
    0x1040007146040d404285000b8200c20b1541100300d00000899020702d13461401c1200030041100405c6040c800fa10100441d00b1700c090505034180105441c200c10000f14443d10400002842400c0d5100c5000400000b86420003902d14810850480d08500886014510142202c420801c0d010807030b5000f1310a40c2d1003415400d09031a2604407150031501c04031070060259200c48000200300e00490702500d88580708030000700c1d210007075244040a409244038201d401d41d00c00f0080c07000d40c5401404030b4000c2d004500d015140c66240600081d642d0341d100c860310780216800150108009014081c003004003010500205e000e003001c04010000b58051302c5002c14107841c0075500c44d00c1c1d28190017169604c0f8490444000d0700001c0318014801401c201488554442d81c50088181944081c005080f465030002000624407a2036070121382003070ba02c00001441000700c0e10240b00001d4114401c1410340f221454178081c0001c0b48408108944281c0a0640e400b540440420300400d609800c2090f40c12009405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 52337027 1250 52335777 52335779
    0xe06041d070f050d0207020a170a0b0603030c03030c0c01090b010303020a02101d0f0301061503050906010e01030201050304030807021204081c08010f0504051306020f030a060806060916020f010222 86
    0x10842e0100542d50442e000600704000c01c0b201201e258010b4810700c0d0004281c40a956552080744081a03c40c9c4240e1940340c02011650090106040ba40341d44154181c024529006001c120030342c0f0703232000400008102c0c030701203032645000d0300035401014000d5020006840a585074280a5590500c0b088101c0c071030848041061101e074810740400c1d001c6030000c01e0b405c0342501c089040041c2d100000203005d82540d84c5403030004150b01040c140c16481d01380c64800003018200100380742d00382078050700001d02c12100e20700100b005036404000c50394426098940b122040e10784c100224181203400c000082d00a8012134042003040010031402c2c207c10606405100024070000107907144102482034000780c15106c001089182001e802c11544004940038040e15000c250b071718041240c221404038131203d80003004000c0401f49620981001e05291030060081d45001c0c40024903c41004000904000104c40c040d07410303500801c10040210303000c6009548540c008070707428103107907100c0c41409202c180d1420 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 52338133 1106 52337027 52337041
    0x1603120e0601120201030608010209010219170a08060907080f0c07050709050705071b0b07021201020913020a02010b190b0a020f071e0e060d120e06041d 67
    0x50f00300620380407800010201d844c6074003c09460381c41000042d8103a03030001420320302002d11800d98142000c640c03a01c00800c81c0031541c4003103201800715103841a42c0e0064012031181c60b044d20750022681da040c408442946090f01c1d52181c4e0300d40400071890140010000303088a41c0124211030040d40d85600080441d903044401c40009030011680ca000c0219100810401494607070a001e6204d081605602951090120007072066041304901815010290196680844000c001011402240d18900040d50000d1200e0005510f0322008215901c0c0c13030600900140d41004403601e060381460460351280e400000e00d136040d80b0541301a1690031808001c03d40103445041c11214550100c0c89000c5801a019081145106010010000141c0790107800c802c0507034111101c000e40d140001d0040e500c1c10102520071fa0062400640802d002d045502c0d100074102000a40345035503aa106 = true := by decide +kernel

theorem cover : BRFrame.Cov 52158277 52338133 := by
  have h0 := BRFrame.cov_init 52158277
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52158277 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 52158277 ≤ n) (h2 : n < 52338133) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
