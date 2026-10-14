-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3362
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:26:39.049992+00:00
-- url     : https://prove2.me/submissions/191591d3-6a25-4a35-a4f9-a95f79849455

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 604496402 ≤ n < 604676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 604497652 1250 604496402 604496407
    0x120e030409060803030103110102010c0e09070e040c0909050a02040305150a0902030d09060305090105010608070509120625020a02030a0609080715050a140f010509091203150f060304030c02090912 86
    0x50684020002e507048a004403184407032341c80040c0040e42a07440085c240400207050050903072452401d00c000343e80000d13162901c8403113100c107280401c0031181406500408034010010030000c81c02030740140d550044082d0029030600f86540d840f00da540c68401400c1c4000d06d01c010029096030b0756940041061134000b02200e4605d1000300028180e01428080e4400003400c140000301080414000caa049907807559a100040e591914100c0e01a006201c1da00da1042c003509034a04016400c004281c0a54100f2500c100055050f420600c03280e48000c1085042d508940c20400c0503a03030124004848035042400400d1803095071800d001a486801002003800c02200d00240c0080c0d03007588114460010741008008052a10b542002044412039814410526a0005000da03043c070401c00d642102c07044c01210302c8000030300c00d07400b00c54000700e928030700403c1c104079030441520380341c40d500702041d0080c1d49051071828251030041941810342c0300a40110602c1000c5242d140b000c000c24419521040c5e8500e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 604498902 1250 604497652 604497659
    0x190503040e060d170304060f0515010302031b04080c18070f030f0906020304030e19030807020f03240402130e0a06110c0717010b09010509191401090f0f0c120e03040906 74
    0x804d2500107032001d84403d841e008000482d44040d1149900901c500706074850b8903190f130401140a0751004106010101010340200340807004135014002402160300074020080002040c08808503440c0030342d6640c2ca0310715040c899082c3e00615000101e860502d13000c00d8000e481c100e080058200e210008290501c000200010706512400c0e02c45003082c201d500c3c10f150140700072522000341e082d000242102c002000740d000146061000c0e040685406410780381c0b42c5041c41942010100f00701800e500d4452100b040000314a071500c0111000046103c0400c001c1031204081903440201000003880c080d03860f4480340143e8908030a80306a01241d208403045680c6a5140c03e101c4000c8110700941d540c01d000030b802261030030581d524180d440280040c0c166541e08149055042070315804120340b1aaa500390120350210707110302c1806007a03000004101c070310f0701c41c0405040b5143c503120017000e9458401c550f00010303030019520000e0b030464103012400652060380d5600354400c561001c04400e18104000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 604500152 1250 604498902 604498943
    0x1206090105010503010204151b020405190c090e04080c070e1014090106020c3606090a090b01180b0402070302011b09050a0306020c030702031e190503040e060d 70
    0x52044a5000003030180b82d0741c800a15090340100e024200000300c107103003003480d010b210f12015000b40c0c0c0c07518070824401040e90003160444c2c0701502c0c502ca61640c89c01400203080b03028011148502520f2034404c500d07a2a00b00e105c0310700c0b0401707071004000c0100080c44040300e4404001c0c50003d0600801da1290504003040184407190716031040d000142143c1e003180c80140703014003059040310707038580203015004403030001c1064100214003961051581594035504491b40c030901e00c0024807443e05008960b0030030300104051800001c000548850070b2240c00c200007604a04190304480802c0c0c900c1d51104a440c0d8540060184594419041407020070310302c060650540100c100c3c031006484a4050340d0801070200c030501d501d401803030340060300d5820400c0013039400d5008121b5920003d041e20b00f000b410340c1c0083c0c205150001c4810048100d09000c0c185003505000020500441c6c082d140f050721200d03aa01070b2240201d206248641b0005000500703c4c7c4c4403210417a05407039100350701201e4080e03e0203c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 604501402 1250 604500152 604500163
    0x2030d090317210a150504060f05010e12010c030b0f040905070b0903010b04050405060a1508060c1c020a08100923060102010603050d02060702010605040c0c0209040201030f090503070210031103180a0212 89
    0x1d882e4002911740005564141803194a042e20440981e40b00c1150400005446a00b500d91041d85c120000c18038858407000c080c0705201c039202071560046100c8000800b00300840c4488810103101d036150441c0e100000d2400540601120941545507485a54440000303005080a0580f540c00070f0403e0b00b007004000000c51039511515540004000800003000700d0354101c0100d024441a9600101c0821140b802c0701c1d01030040c41c12864bc0074808010702170018400d903042141c004000c134110b48140711391108400f401101038000e4840803c15500341c4c03558850003621520345116561025800308420ba4400e41041c8003868000089031204803844d10005e5407000d0071585000154a41280440c0c45c1c5824019003006421951303480c40704480c60340810140ca4000341040741070680d40e05a00240b4041c5024401245004a0107582c403404140140182e0490104242c0101440e1803695041e19140e141540d4000c1c0d10500d18600c0b044202507200e01e04501020003a611401c2012924441100000d6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 604502652 1250 604501402 604501421
    0x6090509090105040b07120621031103190c081905130e06010806060a020f0d02100510050a0b0a020a0618061404172d030402030d090317210a 62
    0x124080c0665411560500b01c03581036500030a22140b0358003203041d07a8417900c05101c440c0b840c2c1c40001683da5a409180c4c09400d03180c00300017814482c9a81c6030080c5600b02100c0d0902d0303502d0102541c540507a98000d6401c11003900103840500c005a5140d50500c0f950b20180c03454814034001e0030b442a000c0d040c0c0030b00356401c000b250b102605039600d40400d840f0340c1c045440e4010745041e1039008054a07203208003e41a040b652540e0218807a144124403c03032030420101c2d0310410300781c01400c211501030098000761040208400908064480708108030780b035641c0d6010407200d2960701c480d10b0b461540030483c00e0801d03c1c24003405c4641012800384a0319540480300103442e110308020485076071280b002907803040040324084c00c1d40803c030f41d0082615020030020000040c40010f500014201d4030078000791581d0042150708082c40200404c070850404101c0765991103c0c1c1d040c2117614910b0b60740e40720400711000d0b00d5442c1a940114a160507000c210459000d82404040340260714a080c00703030103009120044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 604503902 1250 604502652 604502659
    0xa030905030d06031514070c0f02030d091805250513030b0105040501050414160c0507090903140712030c1b05010504200f0f120a12080601170a0908090307060905 71
    0x4005c003c010286118200903118281da005031103a541c80d1055462088040c0b06896015610070307988016070b0103000d21071403d82240c5519180e2802c0040d042600407404206c18201440c10060006c6004010702c0040d5010b02900d159801c1d1000031011103290041d0315070700c601ca1507913803004401c22640b03848060580d40240d8007001140c4c0d84104100903181d2a205c036115100041d0080780c0441220b2107003c18280580c20f00c04414509695958648025544020207080d40c1d880c84c0300030181d00070380c58003c00788140641b50810780709072600018113200070141c0c4103269683c8010f400040c01080600c014825650384450a11194240070b4040d0004650446001011040425030140b2107070f00c0d4201c521028004210f111303421018440c822a01c940100ea1111541035080c00847d820440e60455a1262082c80b42c2084080000303000240003400b01418413074803a805c3c60344481511285603201c20135800c045420340302c80c106034509100d00c800b016054010100d02040c26a041600034003141d1055 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 604505152 1250 604503902 604503923
    0xd030902031605130504081303050609060105030d081603060f06020102190207120206092809051006050a080a090819080c18060715060620150c0a030905030d0603 71
    0x19055582014407034020194045040303071846404d2480c55000c107a11600c034a000a1500030007003e0300700c034510a54030458041d07101c00304010000105012403030051100b03500421240300904000b91030102c0080c402608400b032850880c921610a4100b4070090002850601003035460380d80c028081e44c410494109003000c00c0441074140c500c001246002c0b00c06424100b60340202d2a030801220340e0007800c0050b88160b82520b070840541c40ca00c0d1102d0003800c8002030328807252500d0f00100c2614801014896404008501001206e03004030495207160354a103004401c0c0ea480800e0303a002000c04d2070016120203000300c1d903c8031440083c039603a00a007801d03032107401c20b981d240300202e84148114002d42c000c1600c42c9840c2c103da828010050540c8034404d20017455045a11600e22040303802e642d108000150301c0303a83c50700c15490303e642071202c000826030241090380b14083c1503c4400d4000341c5245c0c1c4c103a50000f40c1c440300911070f511501a240d4000c090b6584d0712140d650074405840140015249030010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 604506402 1250 604505152 604505173
    0xd1b050a030e0c03071202060f0d06050a08010218090405160e01060e040e0a12050d110d0b090402030a02240d0c0806180601080406020405030d08270c060f07050d03090203 75
    0x3c1c2500b031030800600420a241c00e0407800d110409541030226045141444144440b00b00316020b0700000940042c000b03200b41c900403c001c500d0300030340d11424a03a441004202036a5881384481c6080a4042e2810107442c1c58510f0118a800c00c10081145a02100390020a44e001c65141e018102c6049a88500719140c2171810042240e00502100741c0d0342d4007120b070120010300c0c01c6031441890409407d000341414007010135001940c04424060310140d1000400c25452079580c46a07440842d02910300e01c0c43c526050b40440d40e00d03407900c00068450444101040f10040c80469210380204078220780c90748400a05030401d01400303d031503502000ca0852400200b0500703200b1041c0b0351041742d501c00d5030241d448140043d1007001d80500140d034025001c01c00030415490030890300344015034030f50322203840e450100c0d420410740301403100c0c01c81d41200064040403200400560b0f05100341c001c1307503030654481c0c40c03c070301c0e964622407080004c6c00c80c050411448141c50f01540040e007503d00a03000d66105040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 604507652 1250 604506402 604506431
    0x20f0106170a12030e07080309030d0806090a0f020904020f0705070806090d0810091a01032a030b0619170a050f0a0e0703170429040303050d1b050a03 66
    0x49500c40c1c071070580d120060340000300304018030b54084010541000140c0d21800e03102e01d8140003ca4116111541c0005070303814250400304412043c41c5045d00e01026a0b041000002d0607654000e000d044901d03031114603a23404000c650341241c1d50a00c000300700310346d81e01c02515224100c0e040788005035000c0c0a5590002101d5001141181c424030a0902820344071400e004280da800c40050100c1c40020400c18011400070305600c034441c4030100041041d0b002e45200c500045c19280c0703a000c051400c80b003609400c1310524080c15100300030302d000e050104200080350081400e0740070300100555000180c0c004a102141c200540d2651030440402c1508541d5034580507030b080e208117551454154188000044c7c2c00c0c171180d4840079060340d15805480c001d42e1307251100c0803221900f80c8040e01d250800070301040709101c280c144c500003658408200f01030308021034108038a80114030002e01404400941001e540005501c1501101c0c0000d07042c9078031034240d54000342140c200300c082d4000700e4580340d1040c2a000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 604508902 1250 604507652 604507679
    0xc1308070f1d010305151003050d080108160f06120902090c04030c170a0b1f060806031905070b0702150c280507060e010311340f080304170a020f0106 66
    0x380c005c1d0042400c1081040c000e00d617105c0c01821078810401c2d18202000052042c846034505103000e9843d01c8003541000314070303420100d24940580d03042c80c0203d42007022410801ca10343c200e60003400c000568600076101e5101a00e100c4000a6019807238400b005500b02495000d4401c2d28000c072002c0c0b864549421038400d441107000740881c8298800200b04001803820009a40d00c000902c680400249220b0303660350728400f00e6044480455100010042c1600307040090400d0044070303400980e00c50711581c54064440310380c1d008285103142c000440600f507498500440c1c00c0446c2c0035600725940c11205c03943e5030711096030745050403080c2c601c6803041e80390000d04a40e0203000c80e003090240203c14544402941c1c50704036107606070305164803000300e0b807032211a00c000351682d44002c141c00c007a004051014045c0d1a81480040260702c41020b10810114075400950461075900c4209a42da0340c5450400d03070f07981084041030070001a400500490565404108520301e0700c0040000e2004540b25200303092a00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 604510152 1250 604508902 604508909
    0x150f0f1a0109031511040e0403090e07020c060f0c010204050a08010c0e010806090a2012011a03100b031e010816141e04020c0a03080711070e0c1308070f1d01 69
    0xd2884061030406407843d5001c25420340d0084000c074a1b050307650089081c6c030178044a00b64007040c002c890810441d510706003e60b074099468409466400f04100002c1d1590181c03002680d0300c030b10b010483d28040c840943c1210003400000f05807003161543c0d01c1070580070b000d9800c090800141c0d00b107142540d55014108490044800070304c90000769590000d42c138010a88441c030749040040c0604401010380c508401080307030030700740c007020811903040189900440000c40c02c42c0070080010010801091442c24810058074101c51480d079494440b0130409a0740140311205044440115000080c4414005070203400070001c00c02c1c03900c0d0999903002206485c2100c10b02c2e250008041d01a1b11102d8050808040100350020001801e01c40025100d40c034014500070101c0200b039003542401115500a106210034402e0503005210130740c00c01000c1d041c2e120000e1300100111801090082c0c40a00040f1000042e054450849818076950b480351600c14480d4490341000083c0c0c00100b141d0303580300e42c4420741039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 604511402 1250 604510152 604510163
    0x100b041103011e0e13021c1e050106080d02030712050c0615130605010503011e030506010611060c0301060c0803040807150213051206010b0c03070b09011401080d020703150f0f1a010903 81
    0x5170b5a02d41c007409980c2c14500c60981942e9002100341c0000b034500c0001c0031000f20060100c05607140a071034641e00b143c8494002d0710141d031010185503402135000084030900d580c08019002e0128040340c1c02d4a140c0600c0b80088454041c2d1001c010f00030342d000d81d801c084640100c401100c0fa010300344844040f20680d00400340010000c00043c0102c00401d100405c00803039a1411080f41e669907240c0f42d003845000e82011002a0b44400030602070b0204000c00381c0c11495001a152840d4508040074100320040c0000a24440e404000201840f40030000d41e440e01d03400c008560b00d5500e09040f210000d5000218840d4200054040071526003000541c83c600741b480600240100d900707103229507145410000c11071120740310820540c4006150f50305a90b01681070302c000400c240c0900098800d112038140c200300e81a9128480c1c18000c241d0009000088076009004405092191403101c0050987c200c101c101660412105904206540e8801c2202104944905025410300e8004448070192407001900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 604512652 1250 604511402 604511431
    0x50901092705130215131703030f0402060c0d0e0102060903130b07020d0f03030c12020903150703020412030e10080108030a1110050c121503100b041103011e0e 70
    0x31903001c5680415081403140c400f03810700309030907400500d0b89008510b051080702c00108820140100c10003440c00a8010102d00800103000e42141581e01d0200400ea04240d00100c4081410b646804040b55202140c910940350b0002e544507001e42180040f0072503600500c251000200e0050011080c0d8401d10304088032505024903240c1e8a001a400990050f40e00140814a00c00022103400b42c4400051003500c01150304030b03011901502d00702c80d4501e801409401008a0095503a01064080b40034038000340100003078848203c22802401250450b03011041c490f5010424590448182c112a400443d2000f07940b0304031400072100b004c07081c41041150b900030304c45017900a002e281d80c000f842403040111508036480821080644405030386501400c03400140b805540c0c441d149070345602c01c101181c011803a141100c04a507940004040d0350142c02d03a02c244050290369150022290301504516a40d103958640c00041842001c1c0706151300310018201c00040c2110303089503601d12800e0301060548 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 604513902 1250 604512652 604512719
    0x90705150703110c0402030f10060320030a11030114040506041503030f140a09050f040e0d1803051c1107080715110604060e01062709021c0305090109 66
    0xd4048560040310151801081c4c0c801030740b17848501c0030b58891404032440071041c3c102180014040b1003150000e00426040079424150201800544102490b219106d107580703586500c0c103100181111000e24148040000000900380708a21030703940e801c0c0080328104260b8981c0310401080368032140d4144030781c101c81d2200300086030207091a00c0608000342082c929800d60340d03030a445541c1c000346545d0302059003c0c80074011070400485030120303444d068404000b180308a00400781e5401d1080520400c00001c0c2d21100c00754502c40040400861f84403048400c0d13503d0007031400300c035100401d204a001550b030300c0090b907040c0030005002c4101c541e000007806030981003240c00160159580e400000380024054030042039041002114400c43c00743d00c000039800b000005c1c40b0b00b07541d40c65100380b04040000015801d03401d91079400c4101c008411a00240941d031030301c040351707288807081f0010b010014000885070506801000414103580266a00d95505441c1e0b80002c40d080b03082120b94801240d400c0488 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 604515152 1250 604513902 604513907
    0xc050415030e10151502030c1b03100e2b080f040303021b070317040501091206060b030c1804110304230a0503040e13030210151a03090705150703 64
    0x840450b691600f07442090364802100000d0301d49110b11200781580041c0d042000e4000d1802900303032040c442c03018501c0c00080301c0c50203aa07403800e06062500c2e940b4410100350309507400c0059290021001d8001e01c10021004c0d0150b481d02e281c41c6912602050300d13500d058180390003c8800d600040141c4900842c1d1301c0d25003290b4a40f420081046092603800c02140fa08568680c082c6005000e0880042c54140d045113810341641c1d85c8405076070b20401c03007408244001e0781c0040ca50420ba031708040380d80e60b40110391705240028243c154403801f28010700105200142c04104014540d00a0810014000580440912040fa0310402440241c01d0040c008240040c5140c200944041c1d40c0c3c59503200d6010138034032000d0900e4204001260b1651000408112510651034600d500440d01b0f98a1007954555032406905c4400080b0003448841d42c56900f0000301a0060724040038141d43d150030013170218070b4040d10503941e01c20364165685204800002a940c5070840782c104a5032807031440315080603042c0d60207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 604516402 1250 604515152 604515161
    0xa0609060f050f0d0e0307021f090b03250203040f050105030403141c0609090203010f060e130c1208070b160905060a02070803030f010f06140301031502090a09020903010c05041503 79
    0x40011216082014410300e0a817801500c40d2007103c0d102840d076806c014810400382010300c074802d4401c003000c8038095a8050300131000008440728081c009699070f484c4c0e0010080c19019844c0340520144480380b001a0170b84c004054400e89142c03a54000d08551640c0056406000880e4002e000443c056107200907814410b02403d5960300010180c0000348800382d800040e118540c00800041e0354801e48001585000d0048850688003168100116400c040c605085140010400c5e03400413005c0303800100304501141044010301c000300f9160901700706850300e0600c1e1381c4491425160742420401051503502e41c03015000c0a40725035129200101d01e001c00344041074212203400825405480c40001d845d15080c40254401c0c01c1c2007440c00d0389981081c3c4c40300350301e12103500098108420110501c082c00a054100d90540c4c1d0841001116260703502d813114003031b200d400e0030036412041141c0000b07002802d41c1c014000d21041100240042d403d049030072142802140308130a400100d01002000c140d000b85d11 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 604517652 1250 604516402 604516417
    0x1203121e0c030207140d140f03060f0a030f080301091109030c0f0402070f06140c1e0304020f120601090507050702010e0d030e0612062e030507210501050a0609060f05 73
    0xb009030504010f61502c00b0300882680312070345da5400c07103c0c403c0700d1180e01483c41120000001c05840c244041320f0040100c1e07020040c80c05000e00110904910a0340e5180380700750085a000e042c0c3c82044209141503100c0d604207200c1c103003d01d401c1400c0b425189580d01c0550301240c0014005000c81000340d010007040b0760044c04510707000341e401c104060118401c0c8484c4190a801214040f80450444186200001c00104081c4610f0310600140d0140511007000307811021004203110340360b0300c2e60b0000550015003425050f40c0301806040c0300b40d0100022a485041b905601400c211607030f0b60050940d80d620036050002e0000c4c2050380500070300d05c0c3c06000303886038a0207440c01038840c00c0340d0000f00d5415489501c0188a078200030040258a103060781084070095482c42d108480b90040404410b518a0103030b0001c402d254880c00000c1d0620b108026005159129075440825010504030090041c9420b00466009042c02200441e4403405200d01108450a5036550a0040c2d034803281180c09401081c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 604518902 1250 604517652 604517657
    0x20d080a020418150b070b01030305030901020904020c0f07090c050906030406140711010c091202090402181f0503030304020901060807110703030f0e0901030503031303050c01061203121e0c 83
    0x8400f0440c2c004104050141482610002525a01500910708408081ea000f654658800c01c0450300140b00400b0f1641101d41c541010350326916402000382c0a40628550180c0140c4003189110101100080e2002040100011f0345c100d981c642d14800c060707500142e810300c00309508002841441c1401d400860b8003a0041400049201504101084425064909500144d60200e64031003100d028403520075407c00c541058101c0600d00072003d10241541c18010307200b0012000001c0941d03c40d0100400d41c42c42044444003140b40401034030142c0c9025140e020807403c40080c011416013400000ca038003403030700100b0900c1c86170301e000400c59140c00d00410180420104820a0640e420200500d2010b14401d4a030030980d1104080001c116202120066208110000042010510200860350025035200309040b40a031b250030255001d224141c51407545620340200051140601c01447c0c8015120340d60700e40360b0481070301464064401c003132443c141c51541e4805181c00305a4903401f0300407481050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 604520152 1250 604518902 604518907
    0x60f030c032d01150e010e010f0302040c0203090a0b0310050607081b1606020d030b220b21010219080709060c1113050601081602030405090a02040e0103080705061006020d080a02 78
    0x31011404e41d800740414440708590140d0900c143c1c2c0e410103c2e076000d00f581d061803000c1d41d854403049110b1101d89120190041d6a103001d20b1200b20710910840e076008501501d0408070b582d44d040c48440c9940110f0b101405079401c8040807506142041c1200c9459402c018094104405100500300455010b0601c0240b031292a4102c240b40b280c0021010080441d6009046007000c404006019500780f814078502c1074501303020002549441d018205844601c141c1e00085040f080000326070150220000e06000c0400540b40d4040d05005400a014114001042d40742541805038217a4141c84245c0709040800c06440091065030300c19200d00e04041d0044140d600d9074a10180481c01c0d12080301c0100605a0301c3d201000f0b55560015405500300c0c0e600918030800a1260000940f0f83c02203000d030741c0c420300c0036201068000c80147c054074040c2802c1e41000480c0e50307492910180c1ca44c825034080700c10b030040c0d01c0001c0703600038241001e41c12966150050412600100000c4401000081c50030710816803d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 604521402 1250 604520152 604520233
    0x909090a0c080a02040b09060303071203060b131d04020603190f0e1b06031009051302030f070305240f04051203070e030c0409050c060a05040803070803060f030c03 72
    0x440729030070700401545001c0e1181d820039005200c16920b00d02040e034002c02c0f001003844515100002214881604031b031041c184040b02d85011005030001c0d5100c0d0708000800720311400c4003242007414404442c5d082c0050000740311705020000440c60210340280d0700080a0001031040b00c158401001050310fa9000000c0d40305032a511001202e000c9006501141d20030f180401301516031000e0700000303040c00ca41e0307241145801c1400c0c0300c041100740500000c030fe85502c045000f440d2543e4000d0140c80e402010f071050b104540c1480c07903617998144025645840f0b020b216a1550004048840144c00b805940311b1582c2c0d52032090b10711005000c0d001321003038490901c080d1600d85c4000055401141d007030b59940781d400644d104041c07410f00c450030ba041c412440c0401074800914001681c2031001d5096410b6034840300d200f078043c3c03041c0c0035039804001c080c0000241038080010301d8008510075001140c1c44062440414285966202e01445aa0709648281045041092000180c46038064218000082c5620 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 604522652 1250 604521402 604521413
    0x91009080703061a010305090c0d050a050703061b051c0b030c04060305010b1509030c011b08042709020310050a06051801150c0b16091d16140909090a 66
    0x403070361080e12081d6813044200020807000c0754045070000c0910381031201d4201404490784510000f4400e501c20103503404602c0408c08107209441103281c01a0540b8016642c0341080005816400030540502d400e80ca8402a440e004401341c3e214040220503171548000b41c400800010030304401129414030450b43d95070410b175164094540510310560001c182860a04140320b2102e03030042c065000c1401c02e00070545c080d1400140c0810010003440c250002d500000d40c0554180a0094043e148100020300810201c0300301145003100210324061210f5a42129080022194410320003945500524408100769010382c0040b40c0041c44013000084607a0b895002910351103083d0b40315034280c00b50314010000407050444150035908a4248195240140d6440e00c0030070340024002400300807504051790449115034050f0010741900240c51000b6036090400303000180048410415528800303600011051084903155041950600b045040041d61000c00039001c90003011640d45200b401040b001250 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 604523902 1250 604522652 604522663
    0x20d18080a0f0203071202150a141908060a0509160203090307090f0b06031306020d020d0f0509060a0c0912151e1803050a112112090d0509100908 64
    0x920501d150341d002c4030303070344103050a1040c207038014004100d60f00c84600150b19006200402d03441200e01c00c9588072100d640544a00500e0b00d420100c20102084640b5072405103c52002c1410903030301d556009555220411217810f055004040c0c000745d05d070b40840c0200c0b00f401c00c4961001c0150046e83d04224250020070f02d0b02c0e10b15403003600300c0341d1030b01d60800c850303040d62150740e0100d1015600c1a1442c90814403460580c04070306001001d043c0d001516916240749a81560382c4681080014400c482020482c6000b80205855680d040c0c0185c0c070124080c4640c0d8441c00b840c1e407407152200d200c2680340980500c03118221400c282c820a41c030b02000c00d00c1604d86d128099604240140f00b0b01b48545c2d4017980021100c54642d0092003180103503031000481c6d00402503030396195031490304803092010a1105c034101401c00d104c95810703076182d800d078110104103140682041c100c2e1841c051244c2e80c0d16080e0035a96280c9002207004144108080e00e143c1c03c1445185059114a007400c0e8801560740b60b1041c6400c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 604525152 1250 604523902 604523923
    0x120603050616080f13030c030c0b0a020301170c090117071a0c07060203131203030902030d09062606121203090706122318030408010c09080607020d1808 67
    0x790040c100b0b054920340c000400a0300003c01405005452906403986180411228405000d001c40c400c1842d0826115507980726001c0c3d80016101c42c2824842c0700e14003e07400070301030f00070b000f41c80c900f403050010b400241760b00302664010040b241c0303646405042c200030260300c42c1000e660300519802052481c042c0002140a54404115a81e5451605041401d0002a0304100110b4204201101e04110030b1038000040e5226400c0c3c1c0d046c4101c80d860305800030310388420020f4040c007510301120010760b0410080702c121000c1d6141c42d44101c449580211a0907900c051054040c00381c600860361904203104122140705111045602c411080091a001504120341d800751a40c040d05062200940c0000070780b2080810b041c0601800351461030411103240c4803810310015041c07450005466450f10781e180704401b004801030726903c9881d500d51901a2140301012008500e800c1400202e0346800224184030f00015405000303490000307402100e19864580c92400c6121100c2d0010542800074400700018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 604526402 1250 604525152 604525171
    0x207020901030b060d062313121b0501230105010e031c020a0209090f120415030c030609241a0a081e07050909010b0a140f12040f0c23011206030506 65
    0x103e1000001000f00d02004005441f2403641c040b2070301c0000d014201c01030901140741040f20031100502901d40802c104010094a01c2d37003007000101100c8105a86111142504041e22550380c0c1c9900040d038a040b00178001079055400160107440b800c1c000f4107903004214480c17054805224407500019500f403401c0c1d0348000c46800040b90309140b00300401042030410b1001010505180c6800c000d083d41c4065050140e050684400881000354405d60020b8084c1000b60030070804014242c068007400002c04840f0030402911200100344000c0712400007580c1c00754100e1041c5024410001200d0129014000030785490801d007a00d1050f0b40d44901e264400c0340207a460341d40382d0030882c0420180ba03038182d0155002c40030800c00c0c2030210798040d240402d460046103829030b888450f154a000c4510030140c0c202c0300500000c090100b0820300b0074101c64141d024010000074a52107030300002d800c1b100c402c01455030201040290000394050040300320860143c01d00052016030b2500ca0605050048510144 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 604527652 1250 604526402 604526441
    0xf010801050a0513060b0307150e040b060f0a14090301020a030c0810030b1611100e07140603060904020609040608030d060e2a0412050d080a0207020901030b060d06 72
    0x4546424403810b98407003119101804241403101020b14402c0c4501c8024140648408201c645034800308001001006600b81c45000b00448080080443c0c9840c20002e208608200600001c1d00e03049099510030801c1000702c40c42c140f102c1c01c00b070303030f030180e640e2030b2054510300612652001d0340c0c0070f1000d404038428584001c540320344011001007200d60b0060012000c08608802840840c07401d41109603c0032100a00100c01c6145290603503513211401801e40e1988100350590303400e1150b070340248040107882e034211811140c03203c2c0900340c0c800509070030755086281440007c0c100e207085092260002d00250900b850f29201d54041015a40d00b60400da400b6400020081d01281051080c00e0041c2a040c0c2c00e0541400d204030325159044421440d8a08041d0200348486110701354401c40340106000603502d00f4064562800c10b40b222034a8481d440800d00c0c4c04006140307022107000b00e40005ea0700070026031b9280e0869a4400c1c280402901090308035840c418007100061031403148064048008030186c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 604528902 1250 604527652 604527659
    0xc05030a0c290601051e1602010e03070806060d060915061e08060109020a11071d18031912090602040f05040204080607050702030a0209010b130b03060a030f0f0b0f01 73
    0x81286003101219490b14030506680041a022007a800d0b00310f4000d103801c961303030386004101da910010301011031914950009076110f0303a26001206a8401da1003078136085542d802c500708054580b10039204000300c03a00702100007103ca207013040c620422300c2c0c4901c0000400306c3e510b44408500f8040a00401005551031800780002020702c500c1448024840000c40c4800d424446110341380d940610821400319004030703c4030319860042442c0c030500d0380d09100702c0b00b900d6502c00d048003101100306031006124282002007000e0403000c090075803619040b40011460250908102c0507180b072a540b8080400991840b4040085031070b018682c0c0541c00b07410003584071400e20080707114140f01948911b20541c0b0400040003140d5010a40707a40c000700c142003a03a20b030100c500109050540c101c0009500c00b03948000840c0c044610341c00b4000b4a6503a049003004d0700e03102d81c8403071113a01c01515000d0344021312201c1000024400801c0c0c035500c81c0b00d60b902c03006850b0a0b035101d4a064000362020500b41c1600f40062 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 604530152 1250 604528902 604528913
    0x4081e0915040810090819020a03030510030c030803091f0b130504020108040209040507031a1e010305120a050c010911030615060403021e10020c030f06061f0c05030a0c 74
    0x49000d0081d14030041c6024a8010920307528241441035034201610780e42d007201030020000035a00250005103510300883c43d447c10007500e03020b00f04022404a8940400b08001140000d12042603039071000d1017607280c1e425600d400405070801040504036100e0300341c0094072182d65a001a601c41d1500d00701098010b4074904005825070894040c0e0b02c0303140b8280421000d40ea0004040d50480e4040d00ca0031040d480302e041550504100d5000542440e800f528800c0000c0d1246101c10710943c3d02446d9401c40f41c2c1006080d02800000780b0002c1c1c401d0b0f0041103100101144e8a000b020400c80d54140b0390307d0321030301a86660958200301c005648c0141050219002d80c24103015840c2d1207081440040c8076501e00c4400680940a1804040e01071000c0d0300407d915880c0300484601111070082108294244041000b95200e40c4810414001c1c0102200c500e80443c00280180c040d58009003c0c00342d00400d80d03548807405040e0040741042004410b11900030901c10710081c0303014403680d62500b0080328a030070300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 604531402 1250 604530152 604530169
    0xe030d1d0c060310060c020607050303090a021309051005070903020d150e070602071203030b1c0210020a1104240825030206180a051e090c03040c0e04081e09 69
    0x1254040c0e070b000c1040045014103429003405032074080c2000903c0071101c1c00401c00f58010ba00006006120000234031400f4000015282d680c18821180214014465101c41c0150381494078000d240341c2c4280c0711045c2441a0741c00a82d4000040d141551000c2c1e50b0b0303000139503841c3c0765040949400302011702c0680c15005500801014083c080010007056240c107400070f42e03c003507038401c030442e10441c0c100380d404062180e00041c9050000078148507038030b0f6918204a80c05c003100d410491103040d00740b00c0c503c4200d00100d41000c84e250482c1d02d060301e8451040c01c1c00050500c0000415000c40ba80350f100d1401c1c02034075010006002140c0c018405444112200300c6090b0600c0301c580f03001040304404000507991801110040d03400054507a80181740240864042e03044c80d001182d100e03000034450301c0c410040b42c00f41001d680d422561546951203040e0810400d21050750068040c3c0c10f003550600c41000d80c080b2464005124036221454800d074201e5401c0740f20451140d49410100024440c05c0780d1500135803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 604532652 1250 604531402 604531423
    0x190e04021f0206010b0a03110a02030901020c0a140910080102030403020312130807060924140c1201260102121e0106120e030c1006050310020c0d030e030d1d 69
    0x1001c4190306041c0c880650f840c2d105200b0000c0d030080000d41110043c0c440e4000c40c0b18000001103180c4c566043c894040c0d2290448054180181304913210b82c58103180c40e01d101402c036011801c00792015280d1070244090860000c0c50b28070621070700307400016040d00034401540b00d02d0013a400342d40c840405c0a040069004003401c40200d24415034400c03004590881c088034100c6074410300c00180c500351427400304100c00e0304060303800c40ea10302204400103a03095600001c0056040c1404200380c1e41d21032084c0300060041049100c60103156a005001d144c42250160302401404500e074145850140001c0d820f83e84000c0c1c99a0041d181c11041c4032080051801000344032040d00e686840560500c04018404800c802c034041e1841d807a4640301c07010460a1003211406544101aa6031001481c280000585441d2007918068401c0507000100d0740c40714405e0742c00d80400440503192035912172004802401c4580301c0000c03540010004225460312a10039400d0300580025030010741c0340225551820004000c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 604533902 1250 604532652 604532689
    0x90803041d0c030c3c04091d0309061e0d091e0302060403050a03180b15030f03090f0f06070f02090a110304020d0503040b0c06160c020d030806190e0402 67
    0x3050041e06100d100540c0c50820411488142008002c0705c1040b410601c03072080e41550b498040006050721000c0000d00c02c1c0c0380d840300144206014088504408040896141025001444203500c989050b20007850101e600b01d01e01840d403113011100070182ea1100b03420440301e03a550b090841c00c0207405010b41800c404010010044e00c801c540b40a5290034000348001c0c00c21400190400c0351501035405030005c2030101482d11500c01040c074180f0041c51058034080d8586000d8540f2013071902c0c0000d503c2d001c104040024604011140061000344c0058441ca030b80c0c040682400b0340440d8980f0740144c41014007680041c8150703111030060009403240a01154051070420b4401074003103005e402180d41041d0306540114444000d418128218016a00103c0d85550b0008428814540001710f0a0041110301d6000040407250541641d08544084000750040c0d500210380020a0007040d0540d4030110282804411311940848402034403001c0e041149010400010703c402d42c1061141d0354804000702 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 604535152 1250 604533902 604533907
    0x26091905030d0315080a0510050603120418020910030b090f0c1b010603020405180f030304200a0503030408010e070b070c1809080d05221e03090803041d0c 68
    0x46620751581c4119001859100c600013060400c02d801d81200034103e00d02079a08002142c40e01948031400b20f100f95800501384008909140703070101e100300c049070f440b61816281a25084061603800c0c1101e41c0d001d25182e0a000c851015102c000c001c000c0d650035a900040c0c400044420000c0c0c4100c00341080f0244050072041140c0d02c42d60800f121441c41510170b02600103c2c0034107005000d8209a00b00a420a00b040188110402c1078401c10300d581c4648016501000b100b4500039503680000c480c090f0a8803030307112107d074116000e217450a0b2980e801800007141607032a0b501081c610761060340032149586d558945942780c3d11082c00070308e01504824151620f84001a103900c42900054016001c41c00072240c81800800041da009500055100451948500ca91030001c0010141158070082c90b8006400d000b0741c0e0481200021241c5500003a03507140e407440c402c02c0b954100c0d601d1104901b480f400d0b0310041000602003016000a0812240312603240c0485102d00e20b14100103041c007020710009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 604536402 1250 604535152 604535159
    0x26150903040513090519023109020439020a0c0501110307061806050601050304021011150a05100503030406080c0d140a051b0c0c0904260919 62
    0x1104540403240116000003c1041d480100002483c0007800200b0521941c2400d400c00340011101d02d0311240225554201007421444410b4041402216200d501001325000c0e04011442d9215155560000e032001424210300703c1000004540c0900a54100f007401c0c00f2030203030942c4d04841c1400b040d154800350000c1083d0b40d40f1034694604038050740381442941090a50800c2c420420b07a10550340150003031001031070b410311440c00d807440810241d071004c0c1040d00054580d4010f40807a406280d02030300da03082e0780d444141c007241c5000142c88070009a01401607521501c40c07107089014003507403c0040008050070300b404500404603c96024a000c1c0c0c00c00d01040010b1b0307800c88001d50340220700c0005a652400901c054000406134a02590071060908017889180c0101d5444144500c0c02800d070101c00251945490185004010b0750709441c0d40301d6140f2441d941010066a0380203440f03a0240440030100d040d9480080d01c1c01c0e4404482924007191780c0245183c071a101c2800000c40798030b01c0700543e04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 604537652 1250 604536402 604536421
    0x50d090605180c032b0516080a020c0604030b06090709080a06020301080f06010f090b03120c06060907031503021507060516091d0a02091f0e0a0905010608040201182615 74
    0x4285c00300103524004465440c0850180d8201c444111000700c100b241c6044c180b820002c1500040c44000052040703444480f001d04122048a05a0341c0180707100030141d0354181085010040108000d08000322410000341d0814108280320082c0e01c1500c2c09070f100d60400b0307034191800020040030407031680b0200c01003100004100803141621881c070f0000c104e00000c0c3c00401c0c41c290105a015414080000700d480200d84081040307401494100c600032034030f40360408101c05455183d06d80040300d8485c1c000400c014500f40c0c030403155070340305000441e0800895807115006c450048804100914414a02004443d44488880c004d008244042e00c640e541c06440c1015074000148205209603001074402c000350740341c4202480d03402451815160030780c0840002094204444161406001c0e4641c010a4409050107001e041c4c40785a980e6a83d00e039101c2d00116112500445819141c0d013601002051044407c250b0100185004041d000c07507a4040b844103140041488004d00700f9801d210902204c0c21 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 604538902 1250 604537652 604537693
    0x9051009062009010807031b0c030f031104060309050109140c0a0b13030b04050f1605040c021c030b0111030403060204170604050a1202010e0f010902031501080706050d090605180c03 80
    0x12017868100c559680710b40e820f90040000c1459101504648032170305140a5203e11b0342000c0178420342d5000380d00c0508400176005c0e114028600c0b480a102031005105140c429840a1003480c080c0001141d0300341e4640b40c2c1300c03181d04840415081034000040500990400709c03944002800d41d00c102519083c0b840c400301240341801c0c0402003060008001003414000d0821a4007d89941d540a5891040c0c0d047c400c503001c0581c6229141c011401d00010b001401d0000c14500d070048060550081ea07210604800c5005086881c0c05d5814800102044455850100060006548a00c40060b9030790300309101a1204c02c0c0c00b41082040c3d50107070f0700300700c000341000c80c0325045950b021403004082e80f4155003e0740035089040e6100700900c90381c80c5a0381f500c0d10542148004a0003581928070751603c800350080c1440c02401042c0859110010401c501d51144008003070b111400040000c024426540e14029150195500d82080079400c004444201d018400703406d41ca01d00318020003044020083c000c00c0301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 604540152 1250 604538902 604538917
    0x2202090408070203010c2a051509071a030901113a14150604210503090a0e040b0a02091012241703030112020d020103090510090620 58
    0x1960110045401c10008006541d0040ea0080080c060b54040810041481001c0c1e002c480303400044d8030318215074400a8198118150b005405451000c1c0341c00d108856541010b80030110134440c403e800038404036594000000c0b01c0d0300500d082c0c1d80c1e0401c1e488860071f40b403001700c286191003010491001d0781c0d105c0801e0310300d04185414444900c000780003a10001c401a035181c14046d0350a00e50400f45d0b1074030b45e083d580e108100c0e04d88940c140851580610011b4011802030100c1080301e05540c02003003583d103440d01000d501c62801c83e45005100004200428004d0b03000880e41d2400d0010f000030042d14a400c91760000c00e41e00114200600c100015405250301049941401042c0e018411044041e402c080710019800c0c0440c0300040a4150a8443e0315440c41034500c003039440c80100010620200840b4125810508400d0070030b0029002c000040319210800ca061680d074806144c00510140b03c41a02e003119290001510415401c1c0201a5250020440300404510b0506243c00320340500383c4200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 604541402 1250 604540152 604540159
    0x120903240a050708280908040f03140a1a1003020a03111201150605071110050a080f0402090411030a0b07020714011403070e12100504030f0e0901090c0203041e05092202 74
    0x200c5e00410030020000000040e02c60440001c0110352110225032071000c4070b20bd00b0303801d080840035107082902d95808980003022845401070060307428400c1e2078250381004540000ca4a021782da139000501d54105a07204840108035010740c4031891900126030001e8444010003031003e12444106030441700c03c18018442400404514101030060019044501480181c00814044c0d03a0000c00f070001e401264400b130000d410b07000000d010307400a08020303024079400781a0300d075103441340c2d51030240c0220281e2005406104500c940e00100f02c52100c540d014004613000ba00d40a03040c81c5c41d40d62809900e064007414440c92680042010352940c0407285c1c401218581054480b0f46000000c590754610b5a0f046c04920032038041041c0440d0642c4078601652007609c659007038449040d4282c07000300140b00301541c0640300c800100312030040340e00304960880301e51040d00d1425403911010005a4405c83d1001740d24603c03042c050040d030038090003054104100321034a41030381c5100c58070b1b1000080081c0000b4007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 604542652 1250 604541402 604541461
    0x3030f02071e1505120f0a020706091406070302070b2a04080318040b10120e0a03020f010c0203090a141306060809061008120903240a050708 62
    0x158510070300c445000307090740380052000c00240c01c0929078a05118002e0f81500b55070b2941031402503003c0c104030344c11541d00101d481030a40d03030842040401034000b000351607003640801c60500003070000c0c0705440e001c501c00c6650300c0c035501064180034503000c00203040d003082c1072040040d803001c15240d100496022104c580300403c2ca80300c084d100c03a80301440001141c0d130070402050120b900b40740030001c0c00001840c04034444422000200f0002610800d00a07a50416258014590303a6031081a0fa0240d000003168049140c0b030000c100d1900d4101c0400054006070491110389404c85030078003640b0754201e0144021824204054001840309915105203d403480304280b0f00380c1e06445010b051610b00681c48000c02103a50b0380c0c10040c03e0140100c665420500a00307001580304c03042c0d03031080015150b5120041c090340208050030282c0764804254036915200e980d21316031000320b01c00c0382c10b00c02d03890503203003035049041080d2410142d030303030141c00343e001c0c040c001e8200400d0007404014009a100c03503080600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 604543902 1250 604542652 604542677
    0xf0228020c360106270302150306120706030204050102010509030306030705210d0c15110f222c010501051e121005031920030316050604030311090a0303 67
    0x511001000304003406540b038000c000180c00340c00038982c3c012541c10552600a117950740e150484030300c41d20300000354002050164403000740c020710050350b80b1800c090201088250000c42013803500c9902d5101d40006900040e040c40f1550382030040320f4004c0c0d40c01d03004604500703141000945582650107079601420070f440380c40e02e24201d4860480c00a100e030006603114400341c1c070f4000300902d4400800781ea00100a03c45007440324040d11806814040d030b140d040d0b04204543c0e07100e864943c40000c1c1c07e150384c0404807000012103c07103000381006220500703c0b4840141c2d00d860411080d8116001d407122480741078010041640c00c80111440b1000e141c48518440c424004400c030b19024440300182481c0b035070420451000c960301404019150220b08445c0c070350f8880500c501075429100802008004032002d50320421440c46046403031300200509a9080c000400c64a6800000740071003540c9070303406030f03043c0b10a154141c406e1941e05e072080b844031440c22510740c01040b1004400d100050800c4070040000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 604545152 1250 604543902 604543969
    0x2031311031509060105090c070507051e09010e041712060402030403030207060e0f070b130b090307120303052203020c13060f0e0a060602010e100209040f0228020c 72
    0x4034103070054103a400d003181080369445031344540900846028000540114290b06001c005031804c2590100c020301c0a582000b050001c0b01e500310046a41500385031441d0310450755002800b81c0646861000c2c10468903203820002d07038407085000c074410141000c1005034400c4000e030034a5030703000c4425107002d692621b0b54070b0103d009115400024086520707007809056070b01d0010510070003c3e0020400c50740000e40361203442c0c02c035100300e004030000c0c1c2840c00000c002c82d0190340d01404440c50000e040d5909942e6425080306240b038480c9003200007903600c20802c00700584200107400c600721611000e203103032449039030080d42c1e80f40403505044c424100d540c04040c01c070a10b50000405806502c629400d03103035450080c500d01200c00d50304d400009081100205686105201d1901c20020a600900b859241291808003d60208982e103400c43e844010200200d05030b07000400041002503071065000d90848901d050a902c84e4075802c04541129540020554400c3c40074a00354415941c0d070a048440341031003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 604546402 1250 604545152 604545163
    0xa03031505060c03071703070903030c06110c030409060f0b04051207051329030a080309160b0a020607030501240302121303021c051812010920040203131103 69
    0x100b075218030002110401d40381d012000e055030707500c1a80607802000f000700b54040980000c507513880016560881c20004680b00b607604006150084000040d1000d00750400d4110741d0140d00c1d1a25a9400060308100404180c800e0360000c0c244a40d034500b0700e5042c80d10b84100c5104034840c1e18030032441c2c880b0042e00380b2024400d010051400a1201031030005001d800c00c06450f00c0d141c1d00422428050f42001e050a214510303126040009000d00101c100d01d5854001c9504064400b2410b489800c0700d120075500d10300d00d510040c000400600352070300040d09000b8035200b00103040604041c200401040a160b1041c010b50340c81101d602c1c4c1004201b80180b01328000e0040340c0c00c90b07646107000000c0c040031803c0301c04007424441c001d50070b80384401089006945240e500302d040d000080c0e01000402114160751112091150004140102070b14a00c041035003554002c1d0400d880e55000401c00c0c400301083d400020720700000943d0198254070304401103010141d10786034003800040070055011003c1d50305029 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 604547652 1250 604546402 604546409
    0x240f18011406010e0a08030915040806090c090703020a0e0f0d0b0109020417060106140a0e1f0e040b0a05041a1f0f0e06161110210c020a030315 63
    0xc10103810304641c41000c0c400180e82c21408100c0e40e24000c002c0f420202009001e5401905c020351a00381a1001d002072610600083d50420b18280408141c0c080c062103214000d03481c840040c00a805244104858010042d101006052042042000300303138001840b4070240900716095041c56180070b003c6088010020002003400c1c400d0740020074103000c294043d2064410514554200400381404260b44003828010714001c1800c0f8101651a5030b103503002048a05902d191042c0c0300c1103ca804900c0c40c0d040c10056040e0107021400f60310100f540b107000b04090b83d0b13080386c041c0070803010700010910302c4000c1d01034180102e80301d041c00b040c40e0695050504100c100940400e1f54245450940440151095030400014544000c21800395100b10110400301034000e05840c03a0000c40d600940707200782d04080844200c10b500070502e00b2076680c6090301655803001d40310030000d441200e24922950344aa085000c01514000c091214540c3c0082e40408099040c10009084140b21801c08240b980380c0c0d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 604548902 1250 604547652 604547701
    0x80f0c0c10051b09010c2904060c1d0d02060d0e030c0f060105100801090f2d110c070e07090906060302040617011a070f020907090503240f 61
    0x4070015410750007984007900c10350100301507114003d40302c403025845104140070341d40045c101c08800004100500d0340c1503004242401c0a00b510790352007015080300c4030304850590342590b4880d0a0006a82c00292603c1401240711440a4030700c40f40c800520210100a8003901603903001c9059103040365164407180c2c22121300000c41b80c85400c0190b0085d582c1d44040091410fa014480000a1608200c0a002c5080405d519484102c0c1c0c00c0040400c000c000399400c1786d505644400a48a10703d0b99100c2411030100304244600c003500220301820705452904401c15218082040b0004800e01c0200e00c034000d0347c201c04a44c8443c0c1d201d02d0000c40f81511a03804c00c4090b1440c0110019072250503a00074012100d980d02c1e507660302081d08150181e00c17a4244070301c8412400d02c6500b964004078810003403180b00c0c4a06801c0101103056004110712940444410002c54500070007484946000c010480000e00100c07000900e03044214250070355148082d014148140103030b0003081c1d0000420580c1054184040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 604550152 1250 604548902 604548913
    0x320d0921052b030618020a051e090a08071202100c050709020711010e0d020103111204060507140708070f0201050904150e071803081602060705010e0c10080f0c0c 71
    0x2460010491401034920400b140181864000b80c042d0180c0c0080380d08034800e03c4403011144a02d0700c082e50000d2002c01c10800d08000d410b1600340d50041d50303800c500c24288090f4440c190a00bc0c00b00c440715a41009410354010714040289400c507101c0c142d0407660540c1d40305c2550300310f41001d407103403804c6503c010302c0b6001e0a0004986690650301030480180108084150500e80c40300543c0d4107122403540c0c680041c214031a900c050f5010341c06c515004035504006624020420320701c0281c0c42c005031342c00c560f12500c880a101103958003005280043c0c170721010803454500310b541d8480692180131801040c0c0c003480c1882009580c095429211000f4001d4020f100f20b41c2082080315141c0740b64080c9007001d00c00c11000c030b01154030584001e00464031840d80224a581152186050703600704142c03a14403600301404260041c0c48100240140da4071410012a40c2c80c0c08401441c1004420f0758094060090701003005107560780807005980098014000007001c1d15441c000c0b00c502d2141040f81c092a03c2074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 604551402 1250 604550152 604550173
    0x4290304060902030709110a030c050c0f1c030507080a0e030d23070504051e030102070c0608090613020619030905011a18071713320d092105 62
    0x1140c0011152a10880a0798a925286c401c2881160200782c0c444840900c02c1c03244078600c81c026403080d895248141400c60418103e92511440c00b42075524070310458002100d080c40243c65030b581a084c4070102d0900380524940b440b0010100d1400505c05134511b82ca40050110f903642c28822540040c80c8400144040400140318140300340c03440307004480c00700409002510b81841002924281d9030000c110000c86081000203168802c00c20540d2a0305560800201c07000540d1100002c0c0280342c1504d80c04880c0c40c1082c0b04a06014004001682d05216550000010f81d0340400712043d10f40705880c4406940d412403012001007401d980300400f00c1d0319007040082450340124407a00c1d000002c0302c1c0741c025142043c580b0355880c142034600c603011900d445070071039242944051441d80308103038500c400d050b0f012645034501c1004643c0c41d50300d03a201d0310b0328048403010060800c2c0d2421440e0f070b4000744101e2914030402090650248140568001904041280d800001d0000c000c1d143c0c0001c1241c1082c0301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 604552652 1250 604551402 604551413
    0xd0c0311070f03140c1302090307120c06080c04050307030f1a0903041505091311070f08030a06050d111908070b09090711060f1008010509250b04290304 67
    0xe40000d5652418030044c43e024843c00190b035202d01407000d0b12806000b010745000e00083d40080700040c3d4140035409000c981e00b1150404440c0c5140074120321004145000e27005000c1c00d4001c0c1c80c40000031401c00c070a00998400041c0c603812298004031101060351182003001c0d440c0c900740d07269008420000700303000c410140003024009480d1007610100c12410700c0355086e07409100d02d041c42c0d500542c1f1450451140c500079442280c2e81e110300300d9001d00c0d0103040da80b41020000703064400c4072025004418080340e00070303a100b081d019050548014418400315100c0d055080f50002c03240744200014a56011266811301c903102c020200001102c4526072034203540c8005070040d410860040381c8410000b03d070303540700d180100e03455200100580b0700341c0c40f20380c04105071446c01040e01c482081d00000000d004c810034812a4807e80070034025141c1503040901c099550032113900122003500e81d10109010040380b10044034115801880c070140b030b20000e4200749481c5881d2144541c041399000c01084148030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 604553902 1250 604552652 604552679
    0x30c07170d0e07060504052803051f230f0c04050a03060902090a0504080a0c1a090a050c040516080a090f030c1103060c03070509031c0f0201140106020d0c031107 71
    0x35800e010703941d806444d00700446040c080c0d4401e40d54010012007219041042950070300c8406400003080302c041a40f65202e841ca0280815284044030b10f82c2e0790140000c00e00381c4540103448a903012819085403d50344c2c0410000e10140c00e000484007034001142440c824072084800901d4003802c80e1120aaa90801038004c0c103003460164052110729000038a40103103807080d1803080f5403140381d240c20700d020140b044455458141040302d50040804032498503900d4000864460314580004011040e0315140090400c1b2418030798038021070410b001d018036551401b6800d402ca1840e0700d00000786030b440c0c2805001034441c0d118003070040640c0440342024141e1044002d503106004442405005c8504824585c7e5072900b01c030840d078185000d101241e0140e05c11802080541c10050864110640e11164040e10000c803010101c0032800ea00040b42100c0c0d020b004003004c2030a0445581460f61410300007130b44800c4000c519000b00710004580804050048040300225141003089695203034a40c41c050004a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 604555152 1250 604553902 604553921
    0x6091207020108060a03350412031d0607060603050d030b030d0f0915021c0e060a080a02070b0708090d09030f080913050c0d1b020a14150906060103060f0605030c07170d 74
    0x2d81f0054030442d0b040b15040f1401c545006180000e02e19907920704036501c21a070306070035820302840a1040519924107001e0170b0441e001d028000f40041ca9494400c3c42c02b043c1810502c14075007004030401d0785540100e4020200348860400d00f82b50860803404a136000e9841d0803c0402e0189181d0a4002c02e03400035204800721391400b8a008102c24062098818141481c040e47d880802080210300276403082140d1500000f00107805030030540e40b59030f01c40c100c2404a45031030016458408010061404000c40120880740741411804d03d421034944140e01d030312400d40039082050009012049480d81ca032a60002141d202c002c100e541003461910030b0541c091100100811305013402650100c0346040700e4103407514190004c3c0402d00880e0340f920f0b20004166451281d6020f9841c0300d03e201144951560300c1aa004030240c0458a1701100140031121a40c02c041c5e600e8801e070380b0500c805c82d00441140c1c1c022044001c500e1300c3e81e0840c0341c005040c0c21484240700b40a80003061100a0003aa030304003e064 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 604556402 1250 604555152 604555223
    0x1020a051f1103090a080d02040b0a021011090a0312050919050a05100e040906020412030909050f01150e0f040903050325090303120e120c06091207020108060a03 71
    0x6506451902885400144c801068a030082500c11001540b140000d0034250b00068001d410300f40e5038030740041a9004500b000015030003800001035030503014803840190441001c8541c2c1440e01d000049a0150024040140145100110026100e0190054454a00c40104850b002c0902030844012107035282c8280c0b809a8416007012800d464001c410000c0070344a6503d020700c0e43c02c07010802c0040c2042d00c2040c0c4089508120210f1000400301a80e100e4a003c0c1d150b41d103c0500e85000441204d80040c035000080443c40014402d82a02c1d0075148031909451900b000944800c800040d81c007103000041c1e0f9032140c94100b50004051b0004060340c410302800014200e2000100c00400805800491b260b000490060041c00042e02071410300300d10103240080081c960001800240c54510203900000d10340d00041401a1440b00030401e5681c840d00c030354043c00b010000f00c906692a8054841c0003414014601d00140303441d01c40380d020314005c581044407001c8100051718000f2010503281200c659 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 604557652 1250 604556402 604556411
    0x1e0a09020603090d0905010c030e0d150e0304080c0a030c060f110619051302011e03020c010501080a1e05100b0d02040f020d0b01020708300708041401022a01020a051f 73
    0x849600480c00d440d01230b50192141036403003841204100651102d0303c41150701c180d40b001d4050000700c00e80301d00000c0200d00e41c01140c3e04c1d400c0c5140a803402100781045031240c4224281440015113008602044071018144161207034510070050707420103d2300c483c040561007000c007003164019881047c3c642443d62a81c1c200400c0e1151000101e1440f40c0310806808209514000703545a03c5210b07002c4200072080c6001420060480f550500b036030020b900801c060f0f44541d010744140460311405a0250700350000042501556559035070311254070b000c2840c603882e0b0315000c5066580300e940d80318904036801401000310801540d8020001c2d00040480ca6030725141440c0c5640d19400010214244c45404000700510b81e004c80d03216070b0000d444070300c5101c64030349608034032400d0001c50050725050740b0a1410603280c0d8101603158428003410950700e0f04551021386240090900b84422a071002c0c0a050010700c41101440140d1910848150040c031901c00c103040d0702c0301e4100340720007500960a119010301 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 604558902 1250 604557652 604557659
    0xf060402070c0506090d020d120e0d0c180204050607030305010f0803070b0414150717070305010b030a0f1b090306050601080f1f03020603040302030d0c02061e0a09020603090d09 78
    0x8224080c046009040701040780c010300992428401a108440005021101e01d480503070128071484000803085032082c404001d204900768018140004170001511215040840707a1104104c7e000c81b032140045200d842400c00b556224150100c501820001c0d20035940c554061038018028042440340c411710000d0000b0101d8905000300403a00c8041d0003a80100b1951100e846282030340c1c610901d40f0740a03204103002c00c1402d0404a035650301c6041141c68000a50704102181d01600400400d00c0d030800d89054014844902184d090300d030464140e003800140340140094510081a810341d440d140b805801c003954403a642d01044440039a8400c00041c81280c65020040da94100262500c0f65200d4982c00001c1d601d29000c0c1c0c00111003c59001d5a450300d41c3d07030b40c010a280e5401503505500581002030b4400148041d0b025840340c140c0144020061072400c4420100d80c0100000150240600c40020500e4084913030005140f00e03170000c281541e2428060481a035502a907455140843e03034020002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 604560152 1250 604558902 604558909
    0x60703020c070320040903050d1a150919120201020735120301090903022a1311030c0406080708060d0809010c0506070201050601090e04080a0305060d080d02030f06 72
    0x40c0e040c61456001450001c0c215aa0504d840e462491030341c0480000000d001207581d518002c207500c1c0d9001e0340798035540d91500080c904c19118000c1052042403490681e00302552640f403d000e11110840002903158480e02000410b0900250f06410061440e00408507020302940c0707814400314800d800319400c00f69201c0d803022654039503200c0c0413617005000d0300004400ea071000081000e0005d080030380703a807603901c2401d03030103c4d800c2a0000030f40581e40f480c43d1402c040e010007003049490740006644000301044102040342c5030251000c0c0d405000070049102241600e908110f0088082c14030540e141e28140c8030004a80c1c01502c10790780003440e4003001c1452580500c10b00c5004171006081255004015150420758ae0300c84858541001001c0e00c0c070701c01203801400005e0250000d5070004c216404d110000400d80c8840b0740100306100040300602c40010b0b228811200101914100810700d40c0e10900001c030720301044e0350701408020f40003030614142203451380210320440f0048401d02e1a51208004d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 604561402 1250 604560152 604560157
    0x1d0a051e10151e08040302070e0a0b0a05030102070c18060f121205030c040605070312090311010b0f030303040b10050a0312091505090d020307091e05180303010e0709170f06070302 79
    0xe03003c1d0010380000900d0f0b510f01c9120384035441070190040300c01f800e59468510184140c100e80c0c07044100e5850281145918001e84400c0092008400039070400c03c46482d40c2486401034811594140b05030108545c00907102e07040f681c001d01602c000c60004d50381d070b400b68210001c10718000300c2d0388841103110048e10345d0140d8140d0740500781c800300c0c0d5801c1600381034003038445920000c015403d111a101c91045403e00c24001c00d440288641c0d0351f2182c4001e4040a07a003524003444625104a90095040382551000001c1d00c1c0d10503040030042145444800721545400407075041903822814801c0013005000380b1004500d00c08500e0340e100ca24555403031800b94500d1a8900015000450402c404c441a01d000b09803c1d06060009040d227542c16a03070ba145000303c1d030ba22030030414402c07a15008010407403510f21482c2e6002c24001080c0820705501d01080c0c1e141e2105001b0400300c141900082640603100702ea080c0050020041025012195050190782d0764180200b081e40ca4424000041e100718880d009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 604562652 1250 604561402 604561427
    0x1303030f06091d0a170309030d06080c0a050307060f080606091c05060f10050904060f0510140a0605041707031e0210090b0f0f220e011d0a051e1015 65
    0x185d00420400ea410200950300c00b0f407410403144400c1c0304c021070001d8a40700e214002d10138040141f007103000c0c02c0c2c18004d4507803140d84001c1c42900309076420404980c000b0360286d100b6040d49480945940c0f8000060b485010705220030340c122140c40348800200d07101b9618412a20f024600700c03180b0303a40307440b412400d21604840406014411140401403424000031180d040740c800c00c0040350501841e1804d108542c0202d0300b903208030414940c2000644e034082c0c018202e003e0262217002e20207040a0b0054000e205900c9030070804a15a00305120122041c40182c010319840499030141030340d0300c0242c45440e0f80d1900140c0c85442c10030503c42045000302018800c5815800405043c56040d001d28240340d040407080e404092402c008c0f11f820761599601503000c0c09200f4903145002401e100550b080c07010f0507045a2001000c41d00d0040d111280c40f01c81d1540001641c0c804034080d42ca61341540200e042440c080b6000810241c1030080c440a055000c2c8282c400a80440c28200010300c02183c1c02c601d440c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 604563902 1250 604562652 604562663
    0x6080d0207061101291f091701020310120c0918140316120215090622050a02060702010e040515091b04090b280801180b1303030f06091d0a 61
    0x58004d2003c840a5492000c40e0300100302d81c16129100200d2080c01b904144000e001420080b400d210020b00300b012110f009802c1c0303000b1429464000e01c1c841009045024142282801100070720030014000c160f080a081c00c0d08003805148000071a150104c088000e08403007591102e0f5040c3d10080c80001542c1000f14004003481039140c0c03644400c20740c1c1c1000314102d01140242071170101c81405c162640c40c021180c1c800140001d2a25070022400b28080441c43d1590301035076192500422707000544000c90a804803a01075a808007480143c400f6010403524541290602c020008001001c6a00341c0106400750ac20001c0340d0b4644401c42d50459250b0421070142200340020320a10046900401c3c10401c0a030100600314060019001c0001803002d601f101c414441005118008081c0100c2c900102c0300115458a989240d03181044d03004020b2010715014514014401407510a810480342403610705001c0048036140c20080303010f010400058800c03100780030004031030440001001030007140c020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 604565152 1250 604563902 604563941
    0x110a05090411040b0a081f0f06081009050403050c011413150e12210717090a021009030b130f0201050a0302071b030b070201050c09100306080d0207061101 68
    0x384100401080450503003008428107210204071030094800a080000e19a104c6001510f0718120b5800d00c0260b10250030030004400c4010000c0c810396030200f01c29070b0040e05011146a0350700f200301d5010840c540c1300d0540396007004240700a050308980213100d05070300c40d070081c48031307418074107500f01000300640c0c0c1040c4011a03650b5800100340300e40b0008600c0160f4032004110202003c4203d03103044481040e516101000040480041c101d46245160f146a070310009001440c00400240c00c845100140c12000000c440c005a90300354180490003115034000c00c983e1074001400e85c01000e8180500081340d00d110f01c42e000c15200e91074282c252403040c1e80801c1030646081d407503004480a810540d00f0070181034007400030500085850f00503a00e4404c584800842c514a50f041c010703540440a007100c82503900d01030904c08003500c5101154074102066a0030030b0301510402c1c0071801000c4a07400304009016a1812004650380400d803442150116a9912130750070348142278074229000d82111a8a0b100c42 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 604566402 1250 604565152 604565167
    0x120b1c142107050307050a08040e0a0506011e0c020a0e15060309030910021501080105070e04050f0a050c0909100608061005070210050712020a0b070912081608160204110a05 76
    0x702802040070510460680307050a250f5502c1500c1c0c000c000c1411661034a002c01c00b8000b481c20707144059440f1850120501c010f091003000a0042041e07200d418482102c0390078989860780c0070304101340560b030303020340701ca0081c41d610780c090301c1040e0f415910480c0d010114072036003405d413070300b0340039a03004401140c069882d00c0c1c4920200812400441e007074800350b0040c069141c0c1090038440016008042520021541d0310b0040c0000704120310401445100301e2804081c0204030508a020691040201c0f03800180d0b5180c003111103801d40107842107154001804400c000e008040740d4940c06c2129550f449581d665165041001f1100c54209482c034000b46041c49840054074082c0c002171194403142c1400d43c9050f2017500d40640d074082420080c1d0260740804080b004108030040b200384d20160758580106994100102000d04281500000d001d03100d002c500c0c021040c000b210703101400c0ea80701c48025a00c07401081420300501c05214240d104519060555803185004411180842031541d1420f190064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 604567652 1250 604566402 604566463
    0x90f050105030c0a090f0605041e0e0a0b06040506180a0b030c030406050703021309091203061208030901020f21011a04050402160b010b0d050c040f06120b1c14 70
    0x219013000301c2080030000000412042c02d00417880034000729030361580c0d602d04050107522040050f00311700e01c11080f4164204155240784240e103411400f00c06011403041c000f0f1300010214001c9803c03c55102900048400701414609401e454609081e90911aa00d030b50b40122200ca00003101c442c00c03407100800002b030018000b0303440540d2003286410300504208096101c4100c20b070241d00f04600076640c83e9004d0040c820038400d480c1038152103180a1000500f00f6036142d00d0702d0a2440300410400022000c035180c17500a405541c41d85014105090312418a904403040c22003d02c80340301c820990342c0c070001c10b1441c4955052240040c0b00c01c09140b416241005000096024107a886410031900a00d000040c22008000e0700805ea005815074075942d0ba012030f241200d02c0648564402c41d010001044600350110040c401c94209041803150369040d608088060704030442400d0b8441140101052028104038003241c1d01c0f4000e9100480050810a00c070b40e03101d4000c010000d21210b481c840c14180f20707 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 604568902 1250 604567652 604567657
    0x603010606140a090b13082109010509040209060f03100e1303201519090c03020402070305131203030c11060c030c0717180105070f0605040c0503031801090f050105030c 74
    0x641407501c0306040c1c5c0d44103091111500110329078041988410001c104100082020340560b00c110021050b64100400e9001418498002c916044c041d0215030101183d60b0f0740e05440d410f400191026039030341454080b0640550003250700c0048113000c9039010511540540105c1d00c00e90356004c1c05040c40025841c180c1704d1a4400346c416a08800f500d20751204a0014854a00404001c00c044607140c00c0625414001744500c0c24080c1030b46140c400b803a0b0200f401468210308990b01900c0040c2c1d541d08906044806108030344021169554142e40010308110111601c1100e900980d0200300050940504982000c40b0800102c0543d00600102c1c0703030340390750a00854208401802242c41c0401d81d942d980c140610240d07188018010114049080002c281c00b6805450803d10b04186880c25982d82c1c7c2d00b81e6a03000703c01415450342c1c3d80006040082c03580b41e00002c0d000080c1127941340d41c0e480064241d5083c101c1c901500103107004070005510f0024650920548030140c58247c11947c4c2c1c0d085640f580d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 604570152 1250 604568902 604568917
    0x3060c0207060c230a050606040615020a060507020a02180108010f0b10110c04060f140411031b040504060e0a14090c06131e0e010602030406140c0106180b09060301060614 75
    0x6000c59100440000c41048154070f417502ca40040c3c07040f0300d0400e0070001220096400191003912401d8501d4200e0742c0811306040881d801800000c00380c56082d07081740340007d0014001c7d08a0600d02c114607422401a1049040303d04120080c0310030340707036403041006880c0e4038180d284e000801c00303a101c003d0038001c42e104d4400e885802d007200c1048130b501d0001000ea07801a071048001c8500f00d581400318900b43c0b141c40c0300c959006d0b58140100f40d2201440b00c850300c401058440081e0100c48207024150003c4100c0d0000c0400420074042c1da511216071190b00f41056895124031031505041210404800384c0e25480341d0031f607101a04860f04160140040ea41c030805200001d010840408541050156180314020441003d440415820f142401203c140107030403450030b40d4024001006065480590245014808a80252200341d406880c1d030152009410036202c0848800e0010782c40c16140d0b1040e6407200f02102c11001c0c5407a41d400341400c85001e0300036040050702901e480600a14030300700400c0714 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 604571402 1250 604570152 604570193
    0x1a010f140f04030b01090c0206041b0503030307050c0105100608190603020607140d020a050601120501020c0f030a02010c1806030b0d0c08160e060f12030c06040c03060c0207060c 78
    0x2910015060314503550300800030710301c003428081014000d011440c0242400340003e924104103203480d403040030f036544c0c030000e1000389052001c25840704600282207080005100140881ea101c0c00c00c1003002d007040d0884600120198a443c000411440d6114124000c40340301d51070b0042d1175240d01a0160102c08054030704095981c86500000042c0c803502c0040611602800140d0004410300e280142451900c80c010001c652007070810b1404254049841411200c2161841140c4211482c040d8060301603010902d00300c0c0503204458590325000300050200e800154020081103207114020340c0c0c020109185080b200040740401d201c0b0900a500107841ea03a0003c066007010f0a040e030314a082402e0a0b040304000d50800e00c88003054000000e104e00281441d400729807941e25104010404107c1c061034960b21030b8000c01003000d1000310602c102c0d0070040100056030424a4a4180340d444400544411100d20740750185885e10320f44045048026038403241c1d502e080400e41078444035000102410344452 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 604572652 1250 604571402 604571417
    0x210f1103070c0e100f140915060a171006080c07050708060c040e0f07020c131b110610050310090218071d030d050a050711060a0804060608011a010f 65
    0x205a0b80c1400d40c00070801c07003000003118030784550410702e240c04036444950040a0380c107007031000e419200400c0345912410386126803d544c404140482e545d054030b10450304480d001030740942c620707400b009200f1302000824009007903031103908485414080ea441030100003007007007011480e1460f1140050003054025400c0712541030311103c115081c088280e49002c0c000030002000c0000703000001003034ad80300070807c0c0640c01030b02d0716800194560007074010081c410100035411030552101c1e540624078100003558070000d961281000036080d1500200203080074410b800019854581656004d025680060003410161404000c1100034281d40c41080741d2011444509002c1c101d0031284603845050300e0307030310100038250400c0748403443ea44042d0300a010383c21420380c2c0200c0c4c0f41c02400702d80c81e1540341e207000c6a4404103414222000a18050302542c03211002031600216540912030318000c50050740204021942d0360990703400c98a4101d10440381440c0700000d111558014485800d0294243c00d2442 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 604573902 1250 604572652 604572667
    0x5010c080f060d0618052a0307030c06030b0a1a1b0a02030d110a060c08060111060411010c020a0305010e060f0109050702070e07120e1b030a0c030219090f09210f1103 73
    0x7c0c18030018400074a044081d09a001c2d07680842c1b000b4a944107001500078048803815034480076544211402404141522101601b80586036110490001c00900007031052f68250110550340036030003a40145a282c0c0d41a12810008401240074a400c5600034000e000e0348007030400690321115448205612802849921004212607025500403140e065407680194900400007528020b801d00209406500c40d000300300010743c044400045aa00c00d003010301044107244001b8030002944c1c1c000070030039400d1000d900300c0d0001c0011900d004001602031794140c3e80e255020b62044a00403141a001130340030440400c18624105421508640c035894a0081c0d8452108200148e4000b14034801042d03208410740e1045500c10038038091580c40231006880290b0f1251542d541030b403c0c80c00040d1007007018106000f1140000c000942c018125507070706000629080040d10300070017004c1025100c500300308000d01d001b00008500315800403c0341e00c541100d502007041c1110b188480d84100a4244030401052 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 604575152 1250 604573902 604573913
    0x912100b1806060d202d120f09160801060924050f0a0302030628020a0c1b1a12070306180504050c06130305010f02040b16060b0a0305010c080f060d0618 67
    0x406c10511110198040500d8096040032000c400b41c0c503400c04000d080c010000d085905066050700314114501d5440c8949804104900300360b070806c122407242c1484400040c54143c1900074104441040e0f10810400142c0c1002a20306943c01c031030060030a4104200340000e280c024400c003e5064007032300f4018045d0700c81d03002ca8508481540c0f00118181c0c008002c2c041500c5005000300d4a17402944d003542042010b43d00500340c3d0300090001808508800008108403044001c404010000200241030705145082000855888005000e462504071000501440d0003405030b601150b210740300c00f1044e260b030001c16000800000e40121054003980e03000c00703001e5840b2030203800c00d0300041d4510080c59203140380c01800c4800b01a0340c6d40381d90740140410800005810b0075568102c40c0341140c10403180301072601e1002014050b1655500104036640881442815402b014100c007140c1c0303d078929502e0302c00ca15104c84c1400c94800e5840980d000c602400221650000500c4020a403004240c3e00010750342c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 604576402 1250 604575152 604575157
    0xe100b0d02070b0a020c210c0102160507090506090c09040e07080c03100c08160306080d090501170c0f090a170c090f0606030c0912100b1806060d20 65
    0x4900d030040d00402c010052040420040d5000b00e44403c045141c84c1e9082e030043c2e02d861501011240480da04540203091159582c01c4a04a106030002150f0303a4100c000c2c0c1304807215060109440d50703c03454002003000b039854811180903080c002d00320451640d45000c03407482a80f1111304039801ca902c60801c000c00300e00800400010b44403000c003030701041c4000c100781071401c038000c0941c2e8107103402c0131402c0c900f041d0010246504001d6044c614155184856801e030302404581c0c1c00b4100501c503880c2112089035000d00c1100584009a84084403030783c21100da104203050503140342400440404c061015079400a005088805010f001c501c000c4e5610042215140c0494005201306c1c0c00c9400c01c2225841d055072900d07484214050084594104000442c0306404014410308800500003546201c0d5035581444242e1641d0b0501203568180034940c01c81c001d4000d07100c2550143e11440072003950801c07964603a074400c08014000508001355429848080c002400d03c1e40f07038401e00701d80d040443c8002c1400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 604577652 1250 604576402 604576417
    0x1c09021f020127020918070e1501030c020607091e0801050408190f14030a0e031308010b0301020f09040c05040b0c010203040b060121113c0909010e100b 67
    0x10f03800c0301c02100e4800c162048841c10090091201c03071030700680d140407105410000350f084205801a031002d001f4504a19074101000c0507002c0c0e0b00b00040400b501030f410746844800e90b020b1200d170b0448030090340d5a813025540c42000c203240c80710901000f2061030114113406807034075041022540d20b003131090840740260390503141404009040da00d1386406940d1000020201d00e440d581e40c80c80f80000a007003214014208041c01000004201c0481c00e540145024a01e407005407650740001320b80c800a0281c29225410b600c1d42494402d4520b0300d0180709590084c540b070800585030210f15000c20008110a68002092140600000c00c4006100b0080c0c62002c8441c4001030f40c0e818076040610a04400402c02410401010403490000c5440f1500501e50501c80390003252a003140c501c01140c601410002e0b0901e07030001a01040c0214903000122020400450720044100c00c08e001c01040f4414098410303000b07403100c00100312010b407000007c1c1c2e00000750b884901440c0d40318458503085038008031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 604578902 1250 604577652 604577657
    0x30203061f0525050d0f020303180304090c0c1115121009240503030322020a150f0905060301030506271207060b01080f0703230106030e060c1c09021f 66
    0xc3c10350042050411400c0700e0920f00d41050007016120f504025602c1c84000e009400300c3c401c800c1c00203041c2d0000c005a40140500c040180200e400804005109040c0010181d40d00c100c910300d03802407414990b03c4400f1050040b81090b2410f41d1401e0903c503880c2e0054814030121040c000300203601e1020344a031310306240202030310300344123041d010601b0442891900014481e400400c00c0c13015042d004150b407001c0441414206961220324000680081c032603a110070340c8040004604c0140135403024465010060f5603e48005098031a01801002e00090200410036803085002c6905141d00208403192025803c1180c0c44510418030940d051043c406048180540301041e40020095036000d402c080310030a00c2e0034483c524140d02c040f07481c6080501480141565410500c940001c1034080c045102641c2030402003c0d6940c07800100244060024180b0602aa8011442c0661200700b103904800c40207004140360f000c12900b81d030080c9442072089900017124800c014140c0e4520455002590094 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 604580152 1250 604578902 604578967
    0xb070806030f06101208070c090e07090902090c2b02041d190e0307060e0a170a0504091d0604050f0f0a030206010e0a090206040e06030d030203061f05 66
    0x20028185040e401c050400e00b2604941d08100d21040c10b54108801c84003141c450001c010f929040c078000702d124071540035100a1613140045182c00305a00720f0400c1b4035415003110070701c1d550b4944c4070b0708844c8008030080d840850b190100da141403250014240b8038111000320314903900f030242410071181e0f2409020207619001b080400c0100300703912640720a40d0148012882034035002558500c134074481481088110f40e0784095202d030200070010340c0c081c50743c04102000300c08501e9500c9656402d01c81c0c4119080c45a0010322910480c404054a4104072245c98013401c1031b09141021000c2c0c818a21842c0340003003a491000645902004080d02540c021f07009090980764030000c60b070501000800442c402c5d4040380945d40081e078001446811103170010382c1d40c0c80c541c8510201001911510b10007030340c003071408100030803690b01c0704500b0303401144201c0490b2030009401b0400c1d030582c0811540e903a80301d5800d00030f012142445c03500b00300003401c5c18506107190a2114003180d03040729030001600c20b10800b5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 604581402 1250 604580152 604580161
    0x906091b0c0a0309170307030c051c1d010c15051902070f03141309020d02130305062d070309020301110d0e10060e01051c1721010b0405040c05070b0708 67
    0x13042451028000841030201d00d9680c40910301d039244150203000341003049484940051140078051108031040c1110f4007082e40ca0740346401050001200002c54402c004000865159801050900c0f8459886410380c1c3d0721000c40240b00e0004e0000506102d020340b8080c02012803111a4030007024218031030031609103100800d0400a00e8160420102d0410810070840600010030300b4002c07008070b840760303400586d0f6510340407045006070040c0d1a0a02207056044400b204200010901d07a2003541d05660714030307207600500e09600c91030451b900c6049002d107003000829440c51003600a00318030f6001800101d8041640f16481c40b699000038851407031a5550b1244405244050220948040c05414244030040c144410040c41884c10f00c22a0311a41e4500b07a100415088e0700c28200e2495000098018100342c41c040e114095403021607003541d00d85c2c205c0c0c00098942c00c00044541a96032905c58503041608001c02c1c40003c02c2001148800d1280c1409a200000c100b0450350744201115955462103080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 604582652 1250 604581402 604581407
    0x60c0c010c03050f06102d0f09060509040e032b0605010311030708040311070806100603020a020d12090c230306040f03081e150109060903020906091b0c0a03 69
    0x4041c0301020141010203200074003403640c01083c0c1103c81113552175004200d00310184c40644900500b51850448400d504814604202c00c0b440e04031070355202c0404201740080c4c01c85002031240240c001196040c4180c164900f03166000c0c1c007142c1c02c0304c01107a15103010120482811581030290451828555a0ba0849028203008260080c02c081c01c2c188184035a01080c07491600008000e2000c0180d5040081e01b8903125012921418194105690900d82c859050750f0f183c0c3c03000c44480044c1b58450b400002c0c401d100e482100c901c40542d50203401d0302c40710342e8402ca07010a40e50030725520b510303261a00e100102d8807520100005004203115821000000c210354401601c1e400300c2d8a200350080340c208008501802d4541180b01c1c2e0500e0000d80c665204040703400140342031803440d500515481c013005180c4490307400b0940196000d8071038071a51036503034034112014407050000075004004240840c00604104400e0394000403489031440c054400074240c40003d4012600c0840d20b82d0000811801307264 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 604583902 1250 604582652 604582661
    0x40213050310090309030209090a020d0f0501140702030304112413050a0e0103080f161a090f030f0304081e030a18020f0f040e010e16090204060905060703020f060c0c01 74
    0x90300d44140054495500c024203017003064400039010f6262440090b003009000d0105480c03084d4010007524a41e003030b1341401c58440d820031a04640307643c0f070000c200e02d07804c2c181c0d030b0000c1c404e0881d64011465982c031951001004d0103442d883d540c02545d81ca102032510798595154100310081c03d06525200e1581c042c2c54170104885501c090701411400344244065074408103d181542d422104096803107500003c00e002900c11042c5c00704e41d91500c2e00840082003030304960008091002260100d15440d40b8078415203a9038005020a040e80c401c11200008100311005180d126002e54041400c20340c2d540c280a0380c0b01015007030b1103042c1d08004108604000503114001003014201807408454510b940031a112104000d005813254440c1012040305603560740280c00c40a0380705009020007400c1c80b0719582d0b03664020090035001c050654002c41d0842c0c141c4240c40c201d90440c2d07200d40d002403400061102c290f02c51002070301140035501017505030010401956001e000c03601d0100d031761146140c041500310b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 604585152 1250 604583902 604583923
    0xb0f1201050603091e150a0912030e07090c1407061d0a050c0d02130c03020a020d05090a0312140a121b0c081b0a0515011d130305090402130503 63
    0x118000d02c01d0002c4c41000140c03084144d50b805421001960101010b07030310380000c01da401820748000c0000c2118508680d00a110740320310071803641038604d40c2c001040d01560004c10450351107500c600300c01c124030f9041d9080840b02c00a617080c094000c0d020500c0280b42a03000e48400d445068551568601031540001d50840e0b00c0c1c130840141c1600e110646e52192202c80b2a480e0314410303408450310000355500c10144800b0b8250445081021101490000d0069040120401c0250003860035011505001d00b080368041ea100502c2000c0c0340d8203641d54400d090507070b403e140c42040301d400c8010542800e800010110051103450303114070034080c82c9051055a501c080e4641c1d203003011000c4440c14682108454500f2031307029008540f81c1740049289001c450351102a08a180f00d017401140501201007925803502d0144102220640c1c0c0300d910107030500c0c00314500c00c00754851040c00201200e01d114000d10302d60f8882c1c42d00c0e52921054000003002d0f41c001452114542c17101d100200150f1404000120703c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 604586402 1250 604585152 604585159
    0x504060b030706091a03060a05030f010e0118051c0c080c0c0a0b04060807030c0509030304060e09090a05031803030702150306040e30090414040605010e0c0307180b0f120105 76
    0x711800c16040c101c10326090a40d2500b90305e8044082003181d640c8100c52006480041c0854040140502c000740c0a41903c0c002c500c099480c5c840a50341d02c50940d5220104907400c400200781d5884600e0302c002084540c00040401c01216140750000a000d000003000c43e05200c0c002802d403c5140f5041105101c12540403a250f440104410800190802480e40c0e2083c01c40c1800160441c1009007581c1502c1844030300755250000080c0440c45036042007071140020300a0b100103041c0c0d80ca100c0a543d076000601e4014103264801d100b80703900c100a15904fe40b8a603c0502038904050856001c01c240c600420120341300d944001c004c00c0301d241060301c00c080444101d10014065900300d440e80c0d082e040f040c04001017110350641c0045503035480301704c02c803040c0650141080054a003207844d10607d8040a07182140d00e1410107000154584600019a00070781ea00d140040c03443d120b0700e400f0f9030300c4100901d20a10440a00c8000204884501c016101d12071414000c1c1c0d40c0c409120174042c0003294140c000710310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 604587652 1250 604586402 604586417
    0x3011715070c0b070207090c09060201110f040b0711042a020c090601050904111603141c02092403150d120c080417010b041802010c08030c09040504060b030706 70
    0x480c070b80e0100e85068101d400058908068a82400807420401940c011024040c2024055400c1c00c0d40400c41c9011035221b503008101680005100200c2441030400c000c070074410900081c040d600e240c40007841c0e80c83c031480d00550512031714004103080d901540300c200c070000b0140850140c0350309042400440040a840036050022000c030018180c0d040142180e4108030010601c40100c1d01c680d070000c4410250310340c0d00380d00c80e168028442a861038401d0100c002901c524141840d070904817003036841e403114070170040f50007841c240d800c10029004445159031115121000406100812212203070a24000003501e64910300300b0481020484100c041c0c90080c9400f582d81d5001c910303000955800c010035841c0c0048199000d00304069032307000300d82010701150604010440c001c00158851000c02d0410760b801d00c02021f40c60150040b8901010001c1e010640c2d8150540c0000e82c0200207503400840116118100049840481c00303d131811103045030129510003191006250802240006146a10f028031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 604588902 1250 604587652 604587661
    0x31d0706080f070c0c21020301091b0b04032a0e07020703061505061206011e090503120306130902120d0e03070b0c030d0510050d081801050307090b091503011715 71
    0x44140410f4401c520800300e0590b85003410360341b01036610781000d400400a000726903550a20b030f55105000702d046181e514003030078002021340d03015040d181200d13002105481d443d100b41c01a0000c40c0d0076680e6800540000c3c45012460101010001d40245259070003040c0781070643c80c0010459144008036100c2d90360a100400044d036810040f84c103441c200200310020b94941c1c1005035194a000c7c01d080d002131a407521412101940219002d0455008808440c0f0b41c007448043c0400910042d202d140c1c0080030250b0810399090140c00c020302c407030310251680c0c0b1400c1032a8001800d02105a8264001a80c14144840c20b4a01002010081d140c1c019000303203843d280c4000d859407441407251200034640c41d20006020130303000011b03030b000605000d4060a0342c09414580034800e5402454021020003000700c1c1000d0fa5446541584e22580c02d41d01d400ca900381c00d02c80000c0c055002090125801002028880c0a2031380d01da020f14002e1050b6a400300b404081d40000c3c03405d00000c0c0010f46240c0302240c0400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 604590152 1250 604588902 604588913
    0x3030302090f01180909140303040302031207030b151608030705090a090b0307050d0c050306010605030a1a061c02040f03080403020a09111207030f1401090b030309030d031d0706080f070c 82
    0xc1d4221703100960006030648052610100c2c01482c421400031601020003040181900030006020000348814154201e40e03c17960160210f94802e103d8541114442d405444402213050080c00c1c152101020b8001e60500c2e940c481040c1d074000c4401d8000600c0102d0103c25504100c51420054001c00c1d030140051411000031955594084c403903a0701ca420ba01c0c0702c0703070144040398810308040c01d400390503540d02c1c0d81c40703078005000b0364030075100340410600c1d0900700c40c2940205003c8288600c4018007581c07401d004100803210b584e00c00110400c41039400c000005059522101e650b00842c4501e181c80d807200d20718010085290155071000300d14a003019020103000025404480003028094660b031420b890f094401c400805001c0c0b2261403480c07511107802c1c1c201c54400051f504a408000062000c8010b2905150b1030340107060229170980d101d900203804481c0a600726207c0440c2c1902040709001020f5040c900e442015400302011034851410300507520045104140e20040381e003001c055a40e103d9442 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 604591402 1250 604590152 604590197
    0xe060c06060622090902010e0301021c111605060109110f030a150801050a0b13113403030203040512211f0306141602070e090a0c03030302090f01 64
    0x4442c070400c0d00242c00a1044420115600d0001c905040903952a884022541c000c11648400341e003c600441e000000519050085510481c2825004034016001f240590081e109102d141c024400040c02000d101d220b00c1e400d0014800d0203035005142da07526142c56a0200e903c0306c440c480c80c1d04030811030380c0c07200c8101e00f0441b9004107400c10005001d9003c00c5c015070840c40990402c0203035500300400d201400c4c41b242c0001c005241d0880702a40310f98040d0608400b114071180718540e10000c207100c6060250062185541500c03003008100c0f206c03031010881c551b00e5a065800072404a5404801d100500000708840031461451015062030007500b80d46035807408020b0f8403000c0c41004601d0015606414141c06c542d0605801e43c0180e000c940c681c50705501602c0e0030718004070340112100000c1c010290314595010303076075000d4010f0001c450802c02d9803114104001c0c81d0b0704541c0310b0010075500107081c6803810001103000399001a261058042000300b040740380d6107168104900c124080540f943c1c0c042d60b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 604592652 1250 604591402 604591411
    0x131d010501090314120301180b0a0f0302040905100c050705060604050c030604240b0403110402390307120206151320070b01082e091a160e060c06 64
    0x400d0420801c2e001c01303145405c0341c04114488980340031000041c00c81004c154001104441e045c144140806c040078082c0c03c0c5a0f500c5014868039801c0340c00c10150a05a00a0303603007e015034140ca4076014154410b8094444200000c000551300040a00900609000d20358001404480034022400c2c120308102d09800081c01c201d220780d95520100c0c209080001030810f07695883c4241a0303160760340e800c00b080d00f504988030681d0f021000301d524241c01d00c0c00388200ea00c036800764281c040c00e2207074505081103401d000c805104c00d00040100b840419020401c0600a8140304884001d0341d503404010003801c01c18042c04140e001e4240d0503280b0700c259039911b1a52000c05240100040200d480e6020a00c1c002e0898044a400d5100150820a000001045c40e041c0d405480403209011101156410050300050080c5513142510f62050000201038021041c0c003401180e14628002042d0500c051040050b101404811000d00b071507801030ba0001070044a2650440b01d19017051403400c010381c2c46200091 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 604593902 1250 604592652 604592663
    0x1110a050307170c090406060806100302130b121e0f060909071802120106020a1e06091509050f030703051b0307140c13061409070e0402131d0105010903 67
    0x10000b0609032150784900291900411101001c1c00c2880300c1a42a9005428450040f804d00c07070045517a034015031b0000c1c0104030203002e010070701080c05804c030002d4204951400e40744291801c00504062128058a000d00070410f403200305003488607071000c440d100c004c40740f131002074000c040141e00140c021641c1d6012030241c0300000c00303070b0b52818241d00b414a1508880d2440c411780059080e0100b665025120500000b0701124076640ca440e000e130382d15400d142004141080e04a503000c1014079800d03590302c20521410010454002c40d5a0f00300c0080004c2e001c00a00c0c903596800102400010894101c1045100340614600780582d00d008220b841416605941c240c1200e00611850404200700c815640c2c024044039111500181e055840c0c40d182c80d0f43e2440303030200b002e80a1421506100749402c542c198a01d840c40e03103250a05219014034020b00c00d2050000c4420300080a44850000b4480002c00d141100d010a040034150740c1258410b060b000d140040120061002e070b40c12900050650740c116 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 604595152 1250 604593902 604593907
    0xa0e0406050a12050106081c050f1e070b0c1806030c041214010e061035010903021011030f041b12030807170106141207020304061101110a05 62
    0x4008100038009030707440503030000314110000455001015412201c188500003e001081c1d17105459542c80303405d0942c540801c8011062035201c607014800401d540642e00c04501d0078500303104507a803e0b010380e0034000040a400000c4540c01c2021800c0880d5004802d151941e0400c1c1c01c6410300f8406003196900300e80645400004510030b0610941550020421440170301c0c10003460740f4040e2220050701070280c1041d82010404510000003090084c401e4888514081140d4074008110b081d000f1480111103104a020a107001c02611250303201030320000200010038417204516000345002c486800c0000003c1c80d22407a4900c0455120450340c2054001603442e00586803401c00001a007010b40900071000400c6400250b05c0b48010b000e0861a406500c52018580e00c201040c0c0e50b040491007a680d5a06c8081c00600905004810000640c0c6c1c817814902d040c00f560403201400390600f0f42d22900903034070216040240340e0340480800c1112807298001c2c4110124034404c001540103030540d500c02d1100c003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 604596402 1250 604595152 604595177
    0x30c0f08161704060603170309060423060907080c060412020d2906040605030a15050903090d0c090c02030a050f091206040605091b031209032b091a0a 66
    0xc03102c11215000c80c031445200380c101840c1c007100a040d28407049801040110241001c610082c00b038a00c21400303072000c0d02131640c5558480000308800c442c1d1085149201e040c110400300c0400c0043d10031400f0300000e01c84141880c2000745400218030525110310000c0109212450641d600c480020b6810380d60003141070383e140f400c11454270300300849250b5010300300201ca0b4498001100d0324021403007640d04010f640d4442c0c0074943c0728070982c18041c103510484064549129200c3c1e005640c09002c400940341000550380004050303146d03200e002d45803104c4020301406104014414140d00c0ca06034001949090b04504001d8264010390080005418001c2480c00654031060811a4110400b4050350503901d01460708900074907042d43c4552103441156075803049421040241500308800600a001c02d510403051ba03030380c590051800c650140501d4a0175841c1c140c041d81c50030201961000d40030344070080c10000604030002e0307074805441c20031300d00e0804000a2480044980c95180c51401c000600e40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 604597652 1250 604596402 604596407
    0xc09090c05240d2403030c02090405010f020c010e010c0c0f03050d0b0a0e1006050c03072405010e09190b060405070306050a0b040f0503030702060306010c140703080703030c0f0816 79
    0x20140010041c0440000d000751105074952013642286038450b020266401014a904c0d03605489000060101c0c030312009000140c50b20625560f1700910a0002152400300d50740100305076048015500f07905c1c0e45410300065154030a009940507400c3d1494200d0340100c05403240c00581c449a00f000c0c0c00e01000044e81000134468de002602a864040c186120300c542d075840c1209184011115482800140c89001c05c050340300d082110324031100d0b58011410000141c403000900e8004002071700078521026003030001460f841c00b580f0300803e0515000201c5281c4407042031700f00180b000b02400007a880e0040c000c001010b410100d074103d40140d500140b01d543d6400140d00600031900003642c054220480000d0202981d0001e0042e80d694500d00c43c00b440e9510305040e0b8900401500075070007642400000c0321540328000d800300c0c1c030f070042150401c0f441c13a000e50070307040201940050340c11034400030b600c109254043c0924843d8000d20318000051541c001001088240c02a000d510303541e901d070320000300643c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 604598902 1250 604597652 604597699
    0xf0207030503030c030a0c02010605010e010f0302090405041b0617181504083a09080d060801020406030b031501140621011401020a08070b1308030a090c09090c05 71
    0x41e404400c0b039070340c0d04241410744816081120103100f482d0074003d511600520600466046400c10b071103c242088018006482a01018030401e08050342400b050701282d40e43c0c0500c9001c1c83c003424200a8040c840c03044500c2640e45500b008081c0a151580d1071900c5014a0340e060f4803040300803d1000c2d404034022085d00b41545802005040c2600d103003480b05010915005001800c0d40d0324079240d940e103400241c8002c0d02c46d03c01003001450605001010b08030400d40101116510410341c4610f008400d00a070011122580c2240301c2c0c681d4081814406150540f2404100701ca0450040180c8489004020940e0805004107031450400811034a400d03241e000c00e851021032480310f204002c5401c0d480500d2900c000340715000510070440d40458803035002251421406030050a014603100700ca03103d0384180321002e4000d000c0740c00071958076070200b00d201c40514020a40d01c5008141d448203030400b201320340c2998120b0460b0038035044040c000030b07002101180840c0d00903980025030402c5136101c1218203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 604600152 1250 604598902 604598909
    0xa15030503031f0501091a220e061005120604111c15120c090905070909030e090a020315010e031510060807050a0f1805060a0306030506250f0207 64
    0x510010060103c0034182c032805844810f1880b82c041c0800361380f0b030011201801c041c81001000002210840488600c0c50000c101170301340c010480031081e44804d0382c0c510000c035a1380400950b91100003802140d1812075081c6d14030301060300d00309080141d070104e12074101c80c000e0240c501c80c6544190751b68110441c4004c1c1c40806d461800c0c038041300c01415001d080500304840c48291683d44280000c1a15501c00407940203543e0031050134214075050002e803200074038240d0020303904c510440100003400c400600808840c948a90390711b038800a120300c01c0c00b4240030040c0480791300c2401071040180c101507460100d03550307800900e04940c102010b900400d0400010b14090603940030070f002000602c130700c2c038014507049904aa9420902d907a441800300c0e0346000700b07844d2000080301d07c0c15010b0014801c501040c01d403074000340100140e50303503000041c0b000c4c0d0141e4881301c04240c43c0d500030002c1c0003040c0003c90380302420807a00000040f80e094811070b4101c0c6152000d042c0318500003010507441c400c10034034001d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 604601402 1250 604600152 604600163
    0x6060e011805040f02070501050a090f02100c0f06062301230405030307111305060f060705030c0609010e010e0313031b0f06020303190e151503010207060606030c05040605030a1503 79
    0x751144c907003440041d50144600303995a41c01c0401082403145c4c54410004190380040651080500f036900704102141c00c0754402c0c04210810070a4004a46002c11400480f80b1800c4006802c610345a1325030522444889004c0154052540030016660045d0322144d000f02503504043d03022904140f8003003c1d004d280c011a4051001050390000c10000c1c40302052040300c1115640d410544046951040e100100c0e0310341c1d00402c5801440d025810104040c0851600c210b081c0d82c100280b280d4030600d00344080b590f40c0303002d80d11807500f912001020b10440710200801809146800c6c650511300d00c800c01c81e40f100919100c0d40342c032a800384080c030a034000c018100d06156017486544d41d5200a50340d400590b2180201c0000700c1413a2518015031062125998040700a080404100115040701c160010603039141d848240f104030302e596030280700411001d40324000001d078103414010b00a0499505000344818002c04001c00c0c40401e8000040d1790f4040541c180100d040d4040d226417504c20005984014607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 604602652 1250 604601402 604601411
    0xf1e04090c0f14092b06060b180d02040207080706140105060c12030a0e0a0510110301060f080621060a0e01060b1c0b1c060c0305150f19060c0b07020106060e01180504 73
    0x210507500c400b50005c3c5500850041c031400303840d554107071810701c40c0400c402d21620708110650041d0414102581103e80000c200605202c0c49413140c281e00c0c0e0110b20212840d580d158009003caa42008981d4050070041d1200c070300b8101c41510041e500c200d210034134820028040700107401941030380c1110601031400d40c02e0301c181d0269450010b07590030a0502d0316240c2d90400b500084860034590a80b41201d8281e611402c41e0308401c0c200307a0300380b10003030501da8020b0305440145c0541d80c10640e40076643c1c4020780c0144442d16219814100710341840383d85400503414000c0410071200c2040c281d502905807c03481e10440380d03e000d003140080510562302500642d00304840302c0c180fa4070b2200d8a415901841c800d204070381d1400d00c00c804861003242c2da44da0b1402062240200c504000010110120300034003007200c000444609014008000c1d4400703400101510141010003c0e03940384560050100d0000340082da00380b0801800c1d40e14071208550402c904a03600c0300b16480b070504001d00922000c0e20400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 604603902 1250 604602652 604602709
    0x80c011b080d0e0601080f150c030415060611010f0b030a0305031e0a0207111f050c030c031909170a06051e07031d0a08030402060f1e04090c0f1409 65
    0x1502c030542480f641683d03024604003a0301c041402303d244904a444039640a0041d82d40b0381e0300c14941c0d04041d1080d1003041d190700d00302d40501000e22a03000500303903684421401d1107406550509544900f04040840384c100005880561400034881c0880c0b9850f040060301e90b940c1451050040c02d582c000b00c044840c11509001e2081160360060003142d0041c4c0220380c2c8a5400800d1200741030442d40840c800e4000c016080f0f0f54a4455805862007151007410b8138a0b00c000d000350b06255070820400c0803403503441c111032100025088a5540024110346e440380c5030120b48200500c4d03d40070720741c00c0a0f0a9585032800190090308070851884070081c2c1d500c040f182400c0c0404000d00401244040c80c2e00320340281304000884900250b110b40d8190b00501d1546940d42d0380e030030b1081c0b94015200d920101d07078091101d804141648203580b6040184000302d00c0c0c40c1c0e45490410410ba42c880d0101000744a11070802403143c40c1d1200a0011035a100c080c031b0b0750303207080d0000032807100be41d0f503901281a81e003001004d9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 604605152 1250 604603902 604603931
    0x16060501062d0f030b030102040509010e0609180c090711162c13020103021204031d0411070609020a05060d0509100b0102070611070b0c030306030601080c011b080d 72
    0x16030900074100320900010040c045060030b42408401c00408074141008407002c403840380d040252111400343c00581465038480c0030030f00c40c0038207070801d10400c01440c0800000c4d0801c010116031002c07040510b900040401407030302d5200e06004ca1400c1c090780c031400001742c02c0e501031642403004440c90011100f4030440021094541c0744c46009440c45400b04480d030500c1e014001c0341090300010901c00351078080c0c84414800c0007c5440c008100e050540034440742c03102c0102c1c0f190240c884d40c000d8a0344480107080c00320340c620544a220f8490721481c9450f064408010340c0605030707615030ba4014400103484519000060071844c41307502c42640071100040c940d07504005078000c1402443c0c444220340d00e030421009104250388c00300080c540140c0c06590108101c0d031280498040340040c26040e20030054540311480d00303551000d100100700b030b44000240b00c80303030404201142c010031039800608500244000024010b24416075058644004048400c003400280c1044860400e03140c401003002001ba540c6c1c1c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 604606402 1250 604605152 604605167
    0x40f0b0901140405280330020102070b070e0d06110a090e060607080307090506180f010207031e050c120f0727022203030503060a21081606050106 64
    0xc90000310000d0046240000d00000c0d902503c400a01c801e08006200d81d20910031101614156190916a040003000c590080a081c0710004891020307064030f07030344c550003054145003128800110780c410000712000c600c5a0780d5698100480d82340400c0d040e0183c800040c1c401801c0140074282c81e203442c1d885018040b4140083c003d40c583e45c1c031560328641c0da07042c40f04640b800132610346400910411164001905107001036502021a08203081c1164481c404a10150000c80c08028103440740d100c0c0c819030303242c06219880400e009200a202141c15135982281b02507c4842c101c24034a00f401c14901042810712003c2c0c00d921001d009030f07800550a050180c1d5542000b1400030880c01406008150343c1c0c1c040050803d0b03081c000071a403010080004003e4000c0d07010708130a041c6c904908a441245038000303d002d000031070080e9181500c070706229041040c03610b46c81d400651443c2900d02960051190020309100e000e42241645449045022160716042c10f2410024042c6141000109519400c84007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 604607652 1250 604606402 604606417
    0x40f060c0e15040302130c090f1401090b2a01020c03270306040f0b06011106090607030f0b030709020702060405130203190c0203090f031f020318070506070b0c040f0b 73
    0x40c2c90701d040b00081801695841240006500028500e0800e00c1040007904007184548051400341061580d9850420280c0c0c843d412406844000040503840da40e4081c405001400d410603c8901c0c0403410341d8600700042505104a0a600200c42920310b8120203505032401d80c46000240d81d55031083c0303940c01c001103000c44100b420390b0003000d0b2503415a080024100d84199482440702ea10411284c40d100303a000d400130191410440e06141c3c0f1840307401c003480f0550282c8000402048a0b080006000c0c0c26a0020b88941c583c40d40340141c2c855040e40e00040d410100c921240c001aaa8070a60010554a11443c2c0009801488410b040182d045450380198401e480c0642080380c000121071080050351030307107045500180e0091101610626100c0c491554400c0001c1c04c44038000600b9a20851404880440c0240703190301008205008a03806090603a40962201800d0030b14103040025045000341d9201401c02c000c01000545e49440100c1100e0141400358420103410703544118100c4a940074a1303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 604608902 1250 604607652 604607659
    0x1701060305010c0c08040b0f28030c231c02040314010e03040f090c0207030b161b08070320011401080c09010506030c09010e0a03050d080924040f060c0e 67
    0x3d0340340000e44108030018529503c50120b500c0e161a14224680c19000009070441134181017000911404400c60028140c0e401c2d58007418242080030340141c2107031110384d840d006101480c0d10304481031071a96500301c4819103071070450b81c03101da11a540c20318684000024603c0144005400300a206010f1480b44c03a50041000a00511912030000d035100d020342c1c03141c046003040000082c080418a40c001d004080741e648111140d25540b919045003104c400d44584051042410403503461036480740007819001032180c6810040c0450b5965112980b140000160401014602c4c4044403031242c1c240d100080c800400078003a0320900050307400e80303903000c0c85110b12601ca24607d540c036900f080d40c0c10328100e6800404a40c110740c1e51450710b681030b81c0316120355810071030080c00d401c80e542d032034800003c040d40c040c60017058a482c1c4200003920030400030304000c940d43d0025410480451840140074614114800000c0d02901c5601c2c0004180c806030000070040c81c01c0c201607941e85580304140115480040303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 604610152 1250 604608902 604608911
    0x4030b100503100b0a0302010e22020904061d040b0702190302070e0a09020a1e05040204150905031912050d09030e031216020618120f011512030e0109170106030501 72
    0x191800322581144081c3c1c21810005c0104055030240c0030a80501c0d80181002c821044613128180310b400411300050900c42c0c0c04180c41070036040a00c02c05000e0030303100743d002d2440801000102d0b892140100020542101ca80002e00c88038130a00c095210310100100d00590095186406500c1e44207038080c41c1c00300c0140400180070703010036000d1038200c243c0262044060354201131141420b0b01c615140030824602218000800362103e100501c000c2c50015101c50340000c030b4210042c41b601a980c0411302c0b0380d00050188a044c00c503048080d030003e0340f00d0500300016040140035207050081d10f844000d41480d0008880506030001204620414101d05680703068810418050050040800b0780917013000c22510702e07006003040b50041c800c0e610001c1a0080c12640e440029180e0703104424030000c283c1050342d000300f41d003109015010310401c002102c4842035040180c000c2a5000d00305010301004440180d2000b0f030b034010b00c2c464000d8041ea0100c050400b540007002d5000c0d05903440f04489540c47c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 604611402 1250 604610152 604610173
    0x30c080d0810060c02100e0a03060b030601300204090b07110708030a12050a0902030304030807030305070905060a051c0e0d080907060f0c0606090c030614030109080d1104030b100503 80
    0x203007030000b09803101c0d92030f400081c88042c0c007030100c1c00c042c907103141060104001d1840081d60f1500742041c02107100703d80c00b2a81d020030005040c03c040c8182e01c03451400750503441149244207080391000300d500446000556008032400018007a201c1d030b20002d01000c42c800e0a1040013940070f030080c0a0400341d03208030744c2e40542c1c7d107400d5136581c4a00c0d0103081c001b840311000040c0b24403182e084540c01103400f24020464070116000a401d560003580101e901c0200011806d04042d058020280d0003225814140b5055107040c01140e4036200740c02c9070b44d041107400a5141501403080d00c10580303810680d442008200c0892450a5444c2d501c2d016200114402e90300180002c80c0020790f0303a040e0742c9140c2d19034255690007941650452a00c0d501152aa51074004c0803411202d107100d0b45c2c013102e040d90b07004210585440c02594001803886450342c0664100350700d40001c0381031a412920021071040c0c000648281905205549004075080101a081c0d52000d110103039641d600300000b038920480542d0102d060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 604612652 1250 604611402 604611421
    0x605070314100506031501020111040e040302070f0f21200f1c0308270c0109080c010915050f0f04050f033408030a080a06060302070b150a030c080d08 66
    0x6140b0406900074000c00018403040c400d40512078281b0300600000c552035400c043d0482d01504107401464080c40210100014180e0400c6148001d22507070710310300380c060305111045041042078001c0c4c881082d1000000d5108c03118409613400d4068110100c0c1c5214400e4201031016041c04211052140f0740b450705001c07040c0742c06419000c1990048500c08240503071503805541500009054155054040d000000701c40440d040126003000340c103016244c001d40b0074001520038103060f000036080e13611540040c00166005403c5c4002e0701e8480d0902d80d01d11400c8501114030b485600078030b115480002c1034090803008110041d000b0380d50110707060301800703c9050500d40c6d22559030650b03030001120a201c190000440501142454a60700031403034020340c031444114503560024000c440010401020021880702e0362244001070605480c0662130003caa4640e0341d101500035080041142102855010940e103815852008690010050320810741e200c2500c0c0c0c50b2151940300c440072801030320010f0072188 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 604613902 1250 604612652 604612681
    0x12050f19110c1305040503090312040f0f030203060f0c0d0c020705040c03110d09052803021c09170f060c03100e010b040e070e040513051b09011a070605070314 70
    0x3100a4107204800e14031030703001d101621001e007094800d17007c1044000034076101444500d03006100a41e5081e41d407841c5c0908480d40c0d20160b80000c500105850041c00160b0b408600260010780481d1280d8154580c0f4800d10344611039106001c4032189018150b004080e000f003410021034800b00c4d01082010030352001602030320401c503026110b1000800062141c0341281e0700020049000300c088a80c441d5030b8200384220303010051002102c561b0900080000c041d4100441001e2000d00c0303040e00305041081e500a030004c0d1550144040c43e034000342704120500d0f000c10016150388100821203e80341805186002c182d0f1050320603081c2010861408990840602035043c125809502c1c0c1c189403504e045c0512070a801701034940303400c00042500c801d22aa580b0300800b0b01400c0c10040300c1c040c0070031514001340b420b003190b8204501e00f48000c400743c42550312965164116061046000b5010461150035000b502c619040144643e01d00307420300048586c181e2204400044218594031941c994610a01110 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 604615152 1250 604613902 604613923
    0x60b060d200a091a0403081201090c020109030206061c20090108160509040206070b0702010c0e0316060f09240e030a02130b031002030108010b04061d0412050f1911 72
    0x1085240100180e0300d90f000c0e14900300940f0074401703080c01d40300c0c1d44040e200c1d4001c5003446044d102c910010b01081c081482403c5800c000e50000300a50100c07a0303806519400d00030300c5a88680049840b000801081400d20304bc0d056100840108081d2100c01401d025409251098081c0b0004000821040300020754480f006a13401a14500300d8584004c0020883d0001c00c12600080c4c20b22031640016451007986002e481d407500042172051445e20002c02001e0210311883c4654003001c584c84400c1e81c240c02410035101079103030951601c1c00d90741050b682104560b0014400075410241c072078145541200c1c00302101500d5440c2c00035000c03640100350752840891806540060120040b2100c4030b010b50004039070780703000f9040d41c409100c900c0d481000c0781c000b640041d80d640d44802c001c400605d000c3c465403000d406001d0baa0540c40e4040b2071042540b9134001c00007880b10100504080c10b0600400596060b60400190140d0b1035181c9642141e0400c0c07001222008a8045030700b83c03141480108100014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 604616402 1250 604615152 604615157
    0x80c01060b03071d01200705091b04031e050f0c0f0406180c1b03091e060804030e060409051608090102041518030f08030103140613030507060b060d200a 67
    0x80300d90b0f12034130708a0a8070301c5410905101a0080030358081e13140d03c822045048422020b00b410324030344410b2003a841c01c01400d0b2454015010f15814040c201031007950140c1e908a18018600110300c0c2e684c82c0203603081500a0810f200e075104605a0100004819010b400145c8100030303000b405401380829507000d406280c842074010346c0b680180b00981c0d0700a212617401071404000c2603000340000b100b80362900c00c050303000500d9194103105403030f403003d564054959080c07030388134200349400d074000d04130200580024100810a4943c19195681e002a100640804c100401c0346041c460f16021900701d0400c41000172500c1e2000003075007140107109440c02c40d49000ca820b92426140d00e4211150311414224545a500405020020514451601400611070407a031941c950550901e40c4500000305504200c44c4d00070402c00c0721030491082103407551603150a240c0d8031102180ba00b400030b040162405074010001065400900090342c10160f00e500440a1850390040d4007400001c0510510490310007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 604617652 1250 604616402 604616417
    0xa1502030402090406200a031a030d0516260702090612070b07030507140307170921010b12010b010f031103040201050c030c0d0302040f050f0a1e050409080c01060b0307 74
    0x4070b170782500000c1410b07803c40d0408800304010189400640c0003544024002560350004080030010f81200036081c8904400500c002d00e80300310700410a00c9003002c0b15050810301a1000104a04201d50290036101d944c071201e5042080068101c00c0e8201d460b069105e080380c000032420f00d0819440c1c0e070001003003120140081e1828140301189544c84220202e00b0000108121004102200b510b206c0e00c075800b6014640d18205070400303504444544003228150300d4104940c40b00740c0d8414400048140d585805a400b160104046500419500c2c00040c0c0100031030100d07800c0b502065000d007a1081c0240c880c41c0300b030f040c110401c038121071351200d48500e8103808002103170156001c2e1000d0031a202c21241200d00c1cbc011150300c01d90a20098003013030004290040303401e011500702c1c2d41404000d410207036042030040c060b40c0d0000c2c0306201c441c45004040e05000303400b00300d440350122140c2c01400010f841808186c0540c6803041542d4000207c0c11510351802c400810403d6404089074091403190b40c0c1c004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 604618902 1250 604617652 604617661
    0x10140f01030b0105091309020306160807080403350903040b0301031b0f08060f070f0518121207060e010501060f082508040c09200d021b0a150203040209 67
    0x4004002c2441c000381130240c280304004560360307400513003541c0b45008100490796074154030615181000141108000c6180b0450702462194091359255020040d46080c24803074849040c180e542450701c0b1a030000d900d000d1812039402055080e07120280751501960a1100d0b654070102c42d40701d00481c0290107805a00308010030100c4d07808400300c2c4200c00000b12800f03800d56104c00748c17130140019034009900d6822400c100b00496088200180c1d01c440301f0304007104001884003005000d0720030015503c0502e4401c01940c01d054903084509030700503154000b144d1081c0c410920040c001e801c0b41030111912800e002c6000752601060144504135085610348078040c100200060761303030304d2000708034420100700c40303001e01408640e01c0c002c107154141d1601c1c0e9502c3c904080c1800e81442d4559000384940a00700b001c1e00d007400e00004500c3c08204800e0803070340c0d10fa01c84214070340040d00c181032081101707415030104800100c202041e00c1e8421485661130891800e40e4500c114103a000488011798030454050000307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 604620152 1250 604618902 604618907
    0x312050c10150521070305060114011b0b1b0408161401090605070f0f1a070c0503040603091a07050408150712020d180b060130020f070501110310140f01 67
    0x500450410380800300d8442c124000c2d02d05d45181580241c0b15039003c807004210200c0b03005051a071100342864210040807542840c10302403c600480140046070180000c1c6107590022000c54001400c00701c1c0c00c5d5140e9549a504c1c0da40d918000a04006008180000503640b00310010050007013410b0b120728140701e2504100303441360381200c1e4042e40c50502d01c0e0102070004491203400301c5400d00c142040c0756000646d03021021045002006c51041c0002a54400f0208200209446c11601e5520700070030082c1c400d1030301001426142d00301c1c0c021071100501340059160807030040e00a440c0c048007200d0800d03141d02c41c59900c80c0d600741c0303109011030340307541101110040f150000d21941201807804603203482d007009901106200114281c1700c501c0858140710540da03000c0c407001e000055a03910b103000302084040300318000744d546402c1c489956000962445408201054078a43c035000700007001444070031404a12103900496080c451105000808180d07420290f1940000384c138094081c0c070408c0701000c0103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 604621402 1250 604620152 604620169
    0x6010219110609030a06020d0903080a0e0a12020304050a0e01080d0f0c03032d06080d050405030316020319030906140a051209030412060605040b0609130903090312050c101505 77
    0x1160036001e04401728022032400d00080628075241040056450002c0c207006106000c003031700400906041c2400340707041100010b521001d00d50042c1d81843c045042c401e0592035441254086900302d544003000061102d10440b88a049611440c29140b041002000407103a00d0307013210103600071400300d00c8a4004280700760700c50790161405081c01c0e600c085034000500410004280c1e1810010388640003445402802c0c0f00c0c0d41d60383c4000c2d0800034206400c000000780c070b9008414040707440c150010a04d805540d81048481c440e0b41590003118540301c40c80c1030040005085004080210b0800c111701660300d001c030004c550040c3d0550351765900345001c20410401150b0084c00804144c84103000101d8460300c05c495506007203228a100140b840e1804081c8030580700c070640701c0d070b10031b0f42e050100c4501c6031902032a150580d15000000034103510186010781d040d0f0002e8001a0104e421113421f1110203400c08024002807040c041211019502007074104243c84011030480900d003d90396040002c5e007048040e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 604622652 1250 604621402 604621417
    0xc1f05030c04032307150c03210504030512060a050604090f1103090304051c03440403110606011e031107030305010f0b070b0708070e03070e060102191106 68
    0x11030740c82e01e41c1d40d40312040d10f51103507120f24071440940c01d0308414140c1e04102c260002d007401040218160280340000c0c100000c080300c09010306c0030301016180d41c242000b140508642d048003042003942040e0034010203503041803030103001001d04100818960725003644164104c030b0000300020b207014102111540541541c0314024006902c4034040200500070902962140d07141c0c600a60302c69103800100044602d900e400840301681c040403400201b40e0003185c995000d00c140900b0070003008145828120b01c84068201d4448140703040400440482d40112035020318002c5d134800b2040c281003510030ba1280e0b010707251a400308075980c800960740c0700703000360b071050b00001070500061103207401d0580800b60780720180c01c0703000a964000600844030000c02000103009031689160400740360340d40e00c00341020301034118414400301100007981603105901012003414054152071031156541d5218140d10b0090399000d015025059200021048504402c403486410440d84030340b40300611300f880b4040c1d10024 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 604623902 1250 604622652 604622671
    0x30a02041d070b0a0201060f050a03030f021c0305060a05090f071d0d0602030405060c03130201121e0902010e041401210221060c0712080a06050a08030c0c1f0503 71
    0x2000c003000765005000c228014480e150200b50380d28200840242100c42c0394000c900040041c07078081c45541c0b2900071510a9980c141081281211384246c241e280920074900c0c3e80c0a503919401188000d5890342043d40034403c184e402850350382d214003c000201c8801c4030f0540c400d500c40e40c0000c208612440d204140c0c1c41d0260051140058810041000303240504000d17a01a5000000d000800ca4200096135001611410060460038400300d60401086841c502070704210000040300c410030f28584c0302c803690f00c15000d2020b03041c9080440c6140a0801e041c800d0b40400c3c654401001c4c03904142c0551300300b61107500041c217066800d047c449012500c0504001e03940c0903925041200503100c1240a80c0c000601841000011440c0c010862901a00511900c0c0030f59091111000046d16100710504070001800d0926240e521001404000e018941c481b5a011565140008031900084000d140003c02803007580d165010f03030030501520040c2c802401c002e6080601c500109a88035402035070b00411410b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 604625152 1250 604623902 604623941
    0x20c190c120b100806010303050f0f1204050a020130020c010608011401030c080d1e1e0c0203070e0105090610120218131b18120f02090f0402030a0204 66
    0x2000c1c05a040c03005410300319034100145003480001e04105000704001c040b0300c03004200c55030566a00411602809001402410000c58500442a00710040d0303645025a8141c1c06c40032710b854141195503009000059001c2054054105a041026040c14074070320a07a00084e00b00d0299881440000d51101c4490740343c555a60350040750121080c000c41222094030700c1581405d50450030400f492802980c0b001d1441e5004600007590143c00151910b1081140e240d07010f90300850120680c1d809441c1203032024125101c2c0301d03001c0c409400014051401740242c04544000e521100c541d8001602030040551254070035002454615001801214501c030518043d04000588281c4105a130854082c1560082c5490250111800c00340304140c60301c20170101c140b00300d507030b1039004540e500110f0719004c040101114907103403002a070396681401070503e03244240850300c0c00d081c40d0b251007800d904e04a118020003000315001c0008500101c1c0125002400340446401075401c11004050030320f4000380c8071005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 604626402 1250 604625152 604625159
    0x1214041208040f031b270209120f071401030b1809030d0f1407050909071b020904080c2b0c0204060306020309060406151406071b2304020c190c 63
    0x4600f19000852003281c040c440902c41080340c00c2e08140d503800c00f8240140410208651012001d18080c900300001c0700140e64600300d40200e480c1c12400c00302c804552140c00c059401803840000c003d011120354104c40302c450188500110251480c204225038807030381900c005072807070001800d00d9420603001000c80e0702e001c0c503a0000c5800c0e5039440c3e080402c0e0640d520700d00009401c44006075a804a443c1c0b13080c6140c00894000901360300c41c0544518104a1201c800c85545402d120b40c0401c2550000e16000c12854149001c881c1d80c2c1c002e030520200b5000e814007180da40040c0c7d80c40071200b1810902c130b0511841c3c84c0401204c0310301b0548001d076446904d8140c00008209188011406100300d01c0241c86149000e05001d01a100d90030454000104000000c0201d64005100180b02c04022552940d0352222805d25504a03011000005910307c0e07071250001c0d1070b500d01e01c60a5083c40012007428038041c44e03c010001280240322015410340c02c941c46008880428921210b446480b90015501083d00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 604627652 1250 604626402 604626419
    0x6010315060e04030e010206060f09040b0c0f07420f0f1b0e0108190216061401080f0607080f27010603020127051207080d0c121404120804 61
    0xa007543d0560105015500d080b04c0c03941c1c180446036114500b0b43d452424104070b000850701d9508024005040c48101d02c010825113110102100d1400020200a5445503003d0910700030544841c1030b2aa407990b4010070741000c0b90065402c844280028007811101d03003220005c0e44000e0030b00e112158440311354604148021504e80e1141ba10b401200b200001c0d000d200502000e0a00c00000c4040341c1445840c0040042281c40001d656201c038003011400350b21241e00c01c1491000c47e201c4d9400070826410038541500c409001c40d10700e07040320802011a02d1410b51741c000315032200c01c213441050014049900096102c5000a00980c10016080c080850700da200c1080610810000d070001010342d45498041081d50f0707008900d41d951100c91144130310241c0b400c00010002c40d40074801c050040c80c070f5480a00340c81c0c1062103000001e0580f10180ca1042016607402499040052070496804142d0400d051089200d0001c103124040c15112103403406040054442d46c1000c5d580c81110090760410002c204001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 604628902 1250 604627652 604627679
    0x91011060117100b0a05270916120503071211120901090501111c14280c02030a02120106170d0318080405060d06030623090705030601031506 62
    0x4400b01c40d88084100b0309504a08102c008040c00352000c0c140b403d0003003169280790b00c01084400c02c42e503404010703d0b10404045100c030031038901c1e16000c00500800c40c4610011031044004010020304030100c0c0d4503440c81c03409418202d40060700ca9401801b02d03d00088000361152100e58142c01c19010349201462042d00c1c00808000c0c95149000c0030911011030358100054078050078007420702c4614120112110342e59101d406594101d80c084020103502d516008605132002414003c55850340c2c2c9480c04990040b020032042c1d20b0003c0059807480c2c03da0a03100e10000044140e0050103081d081c5aa5001c00a003140da024060b1840d5586017000196042e020280f02a0b040c200d50180c1240010150302804a0b03048000300180c1c1e0000320320601c0052071803011102510003c03907003d604c03950f4001248004004540005205619116101d0b800511611459155030344c001c40550b5141e0310031134000c2e1240c03a2481095055400340005000040c640c0301ca91045400e08080041c10b541e0711008500500e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 604630152 1250 604628902 604628909
    0x142e09020f13060e07020a0302030d051b0703020d1b05060708090f030409050412080f220204020307020109061506020307060506060d0518070815010312020c09011404050a050403050910110601 84
    0xc0d0f40e599402c022491450803c964003226070300140c1201101d50701d02a44134400c1d1400b61840f1651107000804d4005000c2c4180c144039079034010143c03507010615003c2c1d984c1c400b411410002c84c520880040044085681508c401a801300c043c1007070b6203a01000f5140ca15018091914a000e403034101001810100f01501c000d265420000c581d6083c40d041640d040941019000200494030040055151586400580008407803c254010007550a610081c900c1401c0e0000e5101d400001800345c05d9078150040000c550082204100100d2003034000004402584a0303280941c1003401007002040b407070380c40300c0d40c064000351200307240c400b00840b000112070702103a0741c1020300064081c1903030501c000c00c01c0001406410000300031103403003001304c1400b9020510004001c941110010148207109000744020501c01502058030340d40c50700846d140c200c0d640d0300d1942c00360345004009581d044e0b250050600603601515031501d05072144050000c44001c110090042c80904014402d01030000c00c40b00d07008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 604631402 1250 604630152 604630189
    0x6030c063212010e09030316020c061b0c030f0d0f050f031611010203130f02031f060501020c031b0f18040b04021314010e09011503142e09020f 63
    0x2e418000c0035500502d00181c0065400845140410040300c0e0004103ca80280101c0210700201f482690f08928004102d0041030300000045040740c100b40f103481c40b15811503030b50400d50304910304060505940b804501c3c0f015103640d00c03081c18499154040d065000b45a140381c6456480c0264201c4582983e520030f503068111561242d015544c0c5a41c0f200e038900100c103c0000a51960811a0401700b03510403400002d03012400e2034114034215034082061345c1028200840c900e4103407800200c0b07080140310500c00c86016010301803100d5068900401c5c41e240040c403901607031407910542c00601c0398110010f11103580100b2000684c1a0311600c0c80c0700c45e88079920500c0c210303069103440c0c818401c1c2481402100d0b06007504159248080c00c07040d424050550350800078140365581d50042850241400e0051524440490480442444405030314105820500030480310100d42c00391114075080b00090210030060010f48040481d05c03507030b0700482c03101e0b40003c09040a5070001c1c400a030300208103441c0c0154 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 604632652 1250 604631402 604631407
    0xf0304050606061804050c12040b1501090803030c070302011d060103030e0a031109040510140406050903040501050d0f0b040f0f1b0c030c0f2405090106030c0632 71
    0x1003040400c0301e00c0c0c0c06501910070342e04280c0c400d90603160546100b403030b0b03074411502d82c03000981101b41401a100021044e881020013418942000504000e0984411414040105944003554004c821400455103444002c611b1036560700000509030b005400118115525500211144030600c10b516048040c1d000152803554550301d405482c070119512a02e008025810341000803d02e0041c1e00b040c1c0000170365400c0e0b510354031490901d0400103094071032551a45002c4440c400d904540c09418440c1c0d104010802040d2900042141d6a000d248115800208108903841114a69402c181e4200400c1800442e400321594006002c3c1d91341c80c41c3e2900c00aa644120310311604c81c60003090000b181500c503012080d0746c11280200458032040019081c407001404a900f001000200d030044103412480000c00d00c0300ba01c600d83c0044070040500c1080b1410140480c140c00301c117114001c2240d5012428501c02c620303041e8251941e0b4800c11a141a05864406e40080d01707903004410191983c0080b20583d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 604633902 1250 604632652 604632661
    0xc0807020d05031b07030b04080307110708100e06060a050105070c03080409090210030b06091912080702090a0e060106110c09040c05040609180204020f041706012d1403010b060f03 79
    0x2d00310625413000242c40e510917203040000c10350500d01d0580098200018581c0d03a641e0200694030007051041c0f1540071310440f038000422000209e204098412525414400140042c0e503081d5201c0003a40e0480d8410308001003085550b00030401007802f02c2c0f0441c50825019540d03150100160400ea0220524646503024942180342088178800317500114201040300005013404210b01d401003030f8105008020081042c0a031450300d00e80c038801000051640009100645442c030f40c039400c984030490081ca00304004c07030700008290151400c4000c180c00103040e50782c030f40304045a1180080807810168003c01d00748000a460703603071500b44981d0003803020110041c80d05080c081102c2065100c03008040c607100c00c0c00403115a030004074801540403a00980c940c84030072500c5034944202d40c0300300c1881c541d420102e01c10030b00200d800d50490300240c919001401c076001e510000540300d00d031003980700109000300b030102511408020390411000341c000600141c818011030155408002500d814000100400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 604635152 1250 604633902 604633927
    0x1d030c150106031a0f060d0f020403021504061202070f0203190309080d05040b0a0908150603072c181524030a0f05010f09060e0105010504150302010c0807020d0503 72
    0x25005002c140b5041124260704501e50a8081300d81503030900ca60b5601300d01c2d041695400003a501c4100b00020108680441d850214000754058442207002d490880d82ca43e21140080c410780d8122000c0d500d40c15000101d45034664001d47c0274203401c44aa94410140da00561003c0051100204400c02c4841e49940641009443c650a96000c46144d501c8107074003031041707a80101544c040f05c540940d02c0d0f880e111245829184401d280e0807800044c403801c40c15040c000d40c0c0b104640d020382d00980540b1403850300e4200501403d5418040b0740510800c0c0d042d400c174501700c92a401c5078000d009803800310b000d41000d43c07103a040607a00c0d407200700054200c9007030008140001c194000d0400c4003c2c9409212044080407070b464001002001d420001520414014458290400441d035410528100482581450140c008001c40c40c46130440d50700c0d1000114980c20a0711803181050070340d5842d03d8190346113900441d01d100760101c0454951000340002c00050312010b58070180c5501c544040d54903801038800c007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 604636402 1250 604635152 604635193
    0x30b07020f010c0c140708060c070c09020406090b07020a080d0507050106150e1012060b0a030b09072003070203062a0a080115110d05030a06050910091d030c 69
    0x1801c56649018510080140c01c20448681d45a0003110281388a051407000d5091a890b54051103e500905041005072200c03000104440342c85810881d07038440c0c48600358000c84c011400340c00049001503006001850012001e0124144000c0c030900f001030710b0761449418051158400070209001244001c04c204082c003c0c1e0001d0a2080d13001041046041001881041d0402455000341103038881003041500c40e01d02000c1010204509200345aa6018112203641c054110280060314081040d09107182243c0308500680080d5142c0918084c01007481e104000d142c1034050061204200340740050320280500e034400c8001030000008001c1501c0840981c0b2060300c100183c0d18020440d5071000c6400400c80e905481044180c0412038402250aa80c80d04c04071074070b61218852002041c0c241c81e40280118429190b0300011b12600d540e550600c2051710095404c10f40468240d501403041da03a0a9101118807218040103070f0708040900040b50859210012584003038011420b4140790104417001c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 604637652 1250 604636402 604636423
    0x1141b01060612180206070f1b03020a060f0c11010203040509010b07061d0d081b1b0c0a030512090d0b130308070e03190203120c28120c06020d0204030b0702 69
    0x1413241c0d0031400d031412040150441c0080c4919030103c7c1240610042c4c00507000c0440d48580d6480c5100c15949489142c49130700c2c40b04a00c240d50101012a9452184e9403d1260380019103481c2c0e110b20341669403d00f514254550f09045200c1448000342e203582d00e506050080404a102d903030f50714511b040c02c1094481c2040f01c0d402246d001140c904695900284040781e005152078200206c1c0c0b114142181e90102440d0782c00607042000c2944000346451124144014000504548450030400d003481902500d034030024200340c103c4000113608510030344c0208040080100b95111805407503071200440c01040c4c95145080888485107001c042c1c02804881c1c00038540c2c20700f4014461010006a5203604600a8101e4400e804500d0000c640b4108150300c0c06451880c1c401da140e842c65001342d42d981c100b44603069401400d080081c4a5104800000d07198a84c11101c503150316082c080043c0c480b41b00e91030044805036070030002c01d0500000b91010b003001d54030400500c4400d00380003038001e2030a0b00300074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 604638902 1250 604637652 604637687
    0x6060d080d0c03021b16090b0409060f051501030e10090503131d09280303060320090615071707081803010b221d01150501090608070e01141b010606 65
    0x30310b51035081c0c03041b80808088400010000ca240402440840c02030000740710001c044c1400e0800361410b28806420170707481030b08102d66461041d28000c004406440761070907805d42e26080005056001d03285600b0491006000b0812280f620300c0805009104640b81d5005021007441340200d80c42c550208101c1d1508800200c0c01410030750f076411031083c124000c1e0982800d000ca2061208000c00d4081e4101100640d00302d480341051101e050007500d00031034088910f6209458182c0001c846280442010462030b40480d41d5a00f0002103540318400461959452032408500b40402c0c0002900d032402004055242111040d04900302010b050035643c2d0710f1501c0d442441d44c004580c03138022904080c203500c84101c3d48046140501c03c0210411f031100903055031619420040c1c8201c41c43c0c1c108010104417442a03030307203117026541c0325000c80b90160250381a000103210141d411220398400c881020f4001410746000d8034103449080c89907030310300f4403008080f1903035100c0d14100515501700c611410801c0d0010b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 604640152 1250 604638902 604638913
    0x1518100b010504050112140f090d020102030c1204051903172a0f0403080f030412020a05100c053603010c021c110703060f0b010507020306060d080d0c03021b 69
    0x60018005010700c0c02085e040160104d858130781002140c001c84102c60301d01c2031443d01c0c2e040c142104080c0d11030450301d07100544540703200785400a10510031a4410021640410b090002110114494038406072083d0756502c1103003510548400d1190044c500e8510070744801400300c2508410301202c041c01840020062040b002c0c04100b5429144080030700b5003010015569841c0e90b00f400300860142d41c002404030b07100429841c1000b05204003c0d0b010302e0145680d44000300c1000000c9a03113034103d0b20700800c550087c82c000c951420303190f0440c3c00200158200141028100b82d40c040070005034485c02055031140703080e5540740c0d11a01014400300030096000707221150510780c000e5942c65101e044440a8a95040415007240c0708448030241140081c00780c0c0e501d540c2d030741042800f8005807646003040e02c0c5040ca104141d513001e2403c689aa550140190a5039500d4804120170080480c3c800d44001d40b00700a41c0c03581401903c180c225201164400607103c00300d0700c1c2c000840380d1010102001d6a4000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 604641402 1250 604640152 604640171
    0xa0302100c0519030306050a0812070b0901020739060c1707061e05061c030503090c040507170105030a0512030727060e090115050903151810 62
    0x21229500c552204504018101c00d5552912529051505890504110300040380350201941500207030211101111a500b03507540b545ca50b603880310800040c28818403801c120f400d00003814200407661101c0c040c8001030600c2030a8a608a2401081201c014083c445900101c100300842500400c0d4084581c0c1002b0100e06044c0f01810f003111981000e403404603040340d10301505034035400701c17a49141e11410610803034140000b0524a40c00140c1c020600c0b5051000051050800c81d1601201c40040c01c054094505030352401d60b0b041e440903042d288036010728540795005031502e015450160180b99604070300981800b134071a91420041e08110300c80d400c8044041c0100d4000030701c1d0007050304130100040d130302d4851080c155a40f010301da4000203540c241c0e419010300854001c803000d00702c44c1c40f03803100b503001c140500030000c1681d42405407241c8807032514803520070a03101741e0240c0403070940a01243c201200c4a0f41c1a0f03a10142252460681c0e80c040000d410317042014820682c0340c1e03101000a00c0080781 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 604642652 1250 604641402 604641409
    0x1090c21031d04090213050708070503130b04151d070501020a0b0105010e220209010305010605090904060b0d080301032607050d18150c050d0903050a0b0a020906040602030d05060a0302 81
    0x10b1040420341d8100c00e0209109940b6544200801a401001028920980307042c11006d40005c0700c068000c1a001000141d51074050000c0303a10900410034510030b1100c480c1d0341c0d080c92100241059800340321015400760600203038481c2030110814100d0940603c9210500545090065000141113410a049107000500e15503981c9040d80d5013400c00b2200c03102800e004c90096140e2541c08224207800600c00710110119034001d100d03480b02a81c1c18440307aa03c1c2c66003a5011722070f00e00302d031b82c00001e00c0300000c020030305a030322500e90688002c0880c485078916464400e51500280c2007036800a83c0011850715490241005440c0280390346042e5042407480c1c1c40d52500c0e002420a003102f130000d00d44e1645d1600210b8100c0030058005400b200950400b1244000c002d00044030b0211500c0c420442c82c005d4040c051340c0301c401201d50000042813925095600c0c5002c0d0403000c0c210b850315a80034002c41d6003503a240c1c4007800c060081c0358011a2110f85860412090300e1014003454010762040c84140003584 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 604643902 1250 604642652 604642667
    0x70f14060315060705030703120b0a0e0411061e120708060303040e060f0d0b1806090709020f0405040c020a1a04030e010302130e0106020c1908061801090501090c2103 73
    0xa4550300310214211002c0c04952584070780d42e001480e034000090504205500a030300340c21000e00300a41006115000b1041c003000b40018020358078840c6401d000070b40021038088402810a5001d01101e0030905040e81c6468a441c0c64841c3d241d080c1c2010505426001c0201c5111340c2c0801a4580600700c0d0420901003616481280100c403410744000340040c1c16900c9616101c404024064030032041915142000d841400003502c0415284428114055000ca0000b40440c024400c0c036010305201858010703440000c1d88491854105140244000221a45c035031140d003603018036680150a56002a10304140c0a0008064403d580d000d8032042c0004aa440b10001244540038200165250b1808412050302c80d000e51181c0da02440d024008100d440e800b0800d46c3e04d2010907a05609074040b0860300c840c013112140a1685103602c604001045440f081ca21901c01400840000442c0806600c5d03143c01e42d074907000b0542c0d034035010700c40070800d511588500700e512240c40c0e400d600740300545075801401304 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 604645152 1250 604643902 604643911
    0x52e0e0a1e06060b04091d06070f0e03100e0706021c0f081314011d0601150f050c19020f0f0a181d01051f0602150c0417070f140603 58
    0xa99080c1d4030001080a01c1d0300c640003030040e50000b65200c1d17076507900c01c4010303207003052185140c20102008111a404009409030103015a5220391600074096082111905c41c40c0d8180382c0c0c58482d0049410070403149108040380b0310f082e007016281881c1000c0010f072404400c4020000c90340c41d440b1000151a900c40c00c0d181d51a00c1a240042103030b120340300c051000069008010b032000764101c80b03000d030704c030f00540c004012260070001c84292161110442503c030a000d1140051107403c00341d940d04118803030500010990114200b0604006666207001c0c40c140c02e405413643c0309080004040d042d85403902c80e102c000380c0d08031154011901b8a034040354180c040d52140f01020101c003c51030030440032075040f5100790302d240e440c0421a29024007034680070740b105076018945044d034590000010260040c880c2c0a440c5143c00070a010045291500321180e0000d1210032102c10600c00810100d2583e284541096003000041400301c0c1811a401400305255114400191000010000a0700d400b0705803680b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 604646402 1250 604645152 604645193
    0x5100b010219260c070e151c02210f060c19080406020904090b06120102030912030405191202070803130b0c01020c0d08010914060f040207052e0e0a 65
    0x50444050b5420101402c4180c0c01401c01004220b6507400000003418500306c51070040b1610043d11048a054225405080032641000032100741800e8891080c010320141403014050b8508082241210b0301010b0408800c415644c002d024260700c074100400040e80c010b1141c218982c81c0c04251040d41308480543c0b800102441170b520002418402c2c40e80c140c802c41400500103022610301c500e0720a2020ba0100d40951044030018140c6180e981c051081d02c2c4107800940007805c85002d10380c0c03010316031303003000b482100d0b203204503212400090001039030322981a210310140300c039600760820003904040c090380020020354400d02c41607070600140b0015504a88000f9009560307070b26070440c50303400fa22a005031404a40f24000801c0705040e84041c1c200d0403255400750400802e01601200552450b040d030b01c40e940a03d0703200c0c2078207881c0392903401003035020300c00d5080301c00b1500300320060b1000c80040c140e010038080c1340c5131868107181c0050081e00c80228409010308840d12b01540c1d0352181400828440c0c54 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 604647652 1250 604646402 604646423
    0x21603021210050a1e14040f08070512120f0708060d1a0106091a0c070e06120f0c12070e0f0c040b0304060606140a08160210050405100b010219 63
    0x14880040c4900789108140341010310103882c09480c1d80f0064005010302d04041402c100b007100e00c1700a1842070804208021484400303070389441c1c0361000a014902c605462045017042142c0005004100564860fa0050b5211303131a00e102d21060060450010450020396155000300100c2c164450380080e4420411580c65040e00581d041100c00c040d600c0c0c03481103c0d400785100100c3c0080d08505840e049a0444100c110f10500c020a607a0050080003100080c0b40d0051606100704000700ea1303001d5200c0c0014024400114241224a281c00c040074880a45a0130200f001c4a4508012001ca103480c800301008003c0c407460140600102d46000f000f002010842c280420200601407003150011b00e0120203a81e10f9042c1420401e000b422a07110f1100400c0103508491009601901900d00501c07071511840025034520700e03440030080052000c1021800350f44501d4582840d2442290300690150340140000d141c601b016208072942201744078103640c041c441d050354550310060b0128a1a0b4082281d08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 604648902 1250 604647652 604647679
    0xa0e0702010f020301090b030c1906140f070f06051302030a06090204020c0706050309070e131506120b0901050105040612031115180c0105030601050403080c0c060c1b0102160302 78
    0x28010029503182c80801400080005406443d03034210f02c88a0704104d0a9448410201040080301854521b0700d140c02401c0c0c000402c0583d0040b01c0c40b80000300922000c0c2d00e802441c100c80b0f0980d42c80320008035900c0c0300b90b03521082032003c01d2185a80c811001c1520120080f00d0381c000039510903007210000c02c540d48a484400840d183d070b8055600f52880e8000301c03150b00f501e464024000742c0003244c25045034420480300050307030300d42402594003800310380741841240065030303d91541a00d69100d0855140ea264400054240359640c1c601d520345003c1c1d00490402c0c14810200b500303507841a80101c0c851414030806014400000f0407401c43c040c0d00d800c020480c113084280045c00c08d64038202c08110101000100015070818481c5801d90740c09980c251100d8030b40410040d03074140015104940080c1041c031040c000203460000900100300f0010448480c01e0000e40099150b5020400c03030650b40d0810100d2800400d20012483e0b1010007d00182c5002c0c40722001400d6090345501c8064410880843c2c2134 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 604650152 1250 604648902 604648907
    0x906060f151106070c113c09040203300f0a0f090308030105010c0302030415030204030506010608042d1205300c091c0f0605010902090a0e07 62
    0x1002004580d8400c10103070390358901e000e0007000050044011030800c0a07654501400440c41c613114040300d0300c07034003e010940c0c2c8415202c10341205900d6080740d18035156054501e41e2080d80c032800004106101d9003840051521018031010b0414240074091030320600c00180c2d40410007540d80380c181039031400303202c00206c2e280c00c5181004e941d80500d64000034815140341c40c05c20003046411441d4907000a032400220084401d23400c94030014204030070134001800346c2e6208105c80c1c2c010354001e2040b03d09040e15a45d000001030401243d400200b0b9000408204003c01030142500604690504a1480c81c054a45000390850a0940d080d14820701c920b4911403262058051900d941200751640b2a0341c005038003a0459012080141c070000940c443d80d10040b00d0310401d0b2801d100703e02c5510016880b60b40490069421012500758091580504100d4491a0303041d00300c0294090490484010490b0500908031a01078010100480c01080f181041d9182d01c0703139030812a089220b03240520364079880304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 604651402 1250 604650152 604650161
    0x30b19140a05040c030c06120506060c0601090230010303091e06030b060720130608030909100503100f06061419032904050603151324020a021c020c040906 68
    0x500e90310010401041f01607001e9141180480d85040401085d29200208505802014102c80c6958400310060016502a4002c3e2125002500f04080c5e400120f034045c2421080c1c107034068401e43d0400004005069100780120028035152000c208410010b501000c9500e120b809001c050580724104494940c41c0d69049a154582001d0594a1500110350205c180e80c0420541c6204d082300400b92800c0a070b051080400712401e0300000c500d00010441409035014000317041c0d02481c2c0240b00000b5190300d080c001c0000114204400080e4a9005030300da00440d0050b400800401140d803500c4203405500318111100000f221000c40005030760f07800b088014007250380d28008025441034058005410400c01513280c10811202032200e036503020f060540d2a200d0008040c0d0b0b1800f0100403031030040781c3e141c4c0c035040e880c010500c110302103180850300b0f041c00c0d4502c07440000d4a5400180400400e5041c003502d42003100c000304012812204240c0255501d07030f1980c54074070a40c0d03a0803d42e001c0100c2d5a21 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 604652652 1250 604651402 604651409
    0x30d0f09030f052407110d0504140f100c1406070e0d2301060305010b0603150607050a060908030702210d1a04090308100b040f0b0307020f07030b19140a05040c 70
    0x1408084c50b0b1840003450118081d121007010031034003189401e051034003181a289400e8165103450900703280800c0d810b1806041800c40d60482c0c040780040480791903602d4030241c461001e0312600505070082c5410424442640d100003d203800001c2808242a8000f0544507585811502c101000455091031400320f0010400311810441e01d500ca04181c03031064010b40201c074004c5008200145000b020f014051100321074100303191100144224442c9030110152030614002d008445c00c2440c15a620700807940854010740c3c98040110402105a42c1000890019000c7c800408401525a40102d0307003406404540e8030032603180c06500f459481400c2c6c491980d0240107009101c03014141c00d02030500301050b05c002c03081400086010947c4000c40d0100c078219005440c0007441c0c90f02e0a415031117650400341c035507411400b07880507445c1c0da0715080004001643c00ba2018035440d0424840c420302d6020000020806c081c20310584911920085404503800342e0000c1e030110b81d603941c41c40d0030b005e04030b071541 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 604653902 1250 604652652 604652683
    0x105041e050405100c02060108031603090807060e04050601031404060203060d17120f01080c3709051311100c080310050301110906220b0403050c030d0f09030f05 71
    0x41c10041401800070f0361050404403220200180d40c0b074070382c1c01c91f1103000c02d00075400d42d9441000b400034442d503030700004540c0301c6c06481d00d10100d90f00d600c070803410701c03003168840400217550000e0306000346090b214143e00140d007400c0070411404041d04815030b03900004c10160509501000048881c1c6800340d0307105035503038000c100784140c0c1d1001034402d440d502b110b028001003641c00310010740300c096000e50803410394000c1801061032451400802841c41d80c1c2000920301d00c4402d80385085d8030710712240c20b20182c3d440d403d44050f460741410300d154110340d0024442c2c62142001c1950344045100501001d41d0744d4410f41d00c05d000c20301c0100044c2c907009905403005058550000411610036841c9807802c0c283c9008400a03c10500520300d40d43c00c6004048034558012420000e158041380b4481e1038a9410894481300d05080e95280708051060304160710a8400d0b070441a000303805440d083c840443c1d20080d0b07007800d4400c010040f100600701e0115010041c81021b14403820000d0008c00c01180011581340f4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 604655152 1250 604653902 604653911
    0x41b0e060904090807050c0906010801180f0f02070b0702030a0c020402090a030b09060117070303090e190608240c04030f05030d020403060605131a061b0307121409090105041e 77
    0x380784c04a01d59008a10646041c00b40e141401c00da444d01e1282940100700580d582078091b400c5c03100c1d040c003005a410394240300f15604c4003502d8150ba05ca00544949603003c4400589444c03560a02c4a08010300500c0001150400c00001c15242e0b0032012411001c3d805503001620340310070340041154400c440e000507102c4404101045503682001603140d0681e030465040c084079254501c055503490105e0300004010a80307031607050101100b82c90003141d00500c1075403078908040d049120402104c40030707004030391a50000440a20081100101889602c0e821300007502c40d49043c41c08000c0fa40594000204041c0f4450307070140c1403210400541f154141400c20856840b682c91900700010038061142a004807c41c150014403115144905040791055000750341c0251080c804119142e0303c9410220744a203044442c030780540340c1c100301600c43c2c148181c0d81b003400503800071005455240b04401d01c940504041200d00d126450300c0b125281114400e0b2408516400480244007480c0200311440d02d000c0d2030f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 604656402 1250 604655152 604655171
    0x1d0102030411130b100309020f1305151507030309030228030f020a0309050f03100608070819030c080f0c100c030f0902010801031b0314030406030605041b0e060904 72
    0x1490111514000840d111403c4400b140198400e4801501c84290b20851078404d90b00054060b81114583e00e100601215442d802000010240400003210b4981595540d00304a42410305041c4111680c4044400c010781a4030400c50450310b2061441c010308250326855882c0c20180200815445020405692582400c00414116103000200b00c181c00160108515161450008c614a54410703090368a00c80401e06101c28072443c1d034a155400c64051040c0c0c3c921440c104002c0c4107040280440001030031100e0f1404980383e1411040251040342a07900500000000750001c4407044c10b0340d031004c20b10381c907404241d10504032405621210100c6000b03c0d207807582030103010361001141c10398039103081040d4103001241c1c0044400ca40e00c005e0100e0864401400400c0d0741e900c60300d0118030480084401c090712503486070f01d1060100961060355001140c28070005804d80529405030209460070007e40f8050130540c00b070b0001958400c0207101c079111244420f0707110b030011102c554070007400c1801054034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 604657652 1250 604656402 604656413
    0x1009053d03020a03050f0606030f1005040c0507050106050f0916090323010606090b09010c15230c0a0509010f030902060c1005100f03030807030b100c03080709050303030a1d01020304 80
    0x303c1d100e01e00281c94000050080070b40e80c0710160207801d002d04540d0640c1d0302c030b081c848031150003d03041c54034610601800103603a5035140107001044469548043d22044603207001c50035200b0300e4010758441d5446016142d043e8071000000c960040b0108660340094802203000c1c0e0b00e1502136040506848600c0318a48000860905031103500c83e4500000c0003840e07510a02100d5110a6008a280c194420001e103e025807150190828540c0038030760703410000710401e0030340c02162078030400e0341d100b0b0745031240505242c0100c562450740003403401202498415000c900a04510650314114140503010161030f0020784290702003000e00b50f024014079620fa54440a56982e0b021039941d683c000c500f0040003a080d49500e00040084a42400a6441e640d08560f02500d90510051840c0b08060b5a040d8100e01c950b1460300300d0b54075003025100c100080c0c070700782802001800c0086c124000d00200038800c019640300041100d40c0f201c00c0e07900005130301e8031488841001d40e4000301421075544c000f100b800309220 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 604658902 1250 604657652 604657657
    0x8270619020607080c19121d10090203031605100f0f060b0702060307050306010c1b030b0609100e1305011d07050108040308010515271009053d0302 65
    0x125000c8420543d5000c0d4212107a501c1211070340401401440220b0310042e98505070390844c4c1250a02c103141411400703170001240c144511212420f40480d0761424151400c0c08851055480d80c5c100748401c8501e900441c1d0f8900c121175203501d8a09225100368140320003401101c44200301a0380038040c0700b10896024001d00454229502018a84030000aa808111044503162035014011608643d9040020788490308010125814003c122080302c0010f80f840c160202a121001d010100d803a00314109000320503801884bc6004001400034408040d03010207481c4129443c00d441c80140b5a6030f500d5440400e195a071000700303d582021342d00ca0a884c0c0c00c08041c01d203030b400c8008564a8a40c0c40004403003854050700c0c058041103071400140510b041681e8120340c9034403070001080c03801909004032141035140c0c091003803403200313104190b80d8945007064200200ca4081e00e07000240501307200009040c800610744424002c502112548924512414000e64000741076810300c60b0680321120140296 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 604660152 1250 604658902 604658947
    0x3030a08090c0f0a0902030c0403080406050715141512071d07050316050d02120a020a030b060c0d0c020f09040b040b01080d0905040c030b2713082706 66
    0x3030040903898902ca0414224007031141500402034100325140c642c6460007584080c140e4181d0708010040030021034001001400100920780e1016a00d400c0c60070004008030300070030b070b99027a1401c0410050f2000540c02c0c2041c0c210707144041031580d16038840c0001d0b0320355034002c50400c070754000d0040005101c84405000c0110740c800d150b02100130f64034400e089074240f20031260603801c4480740c11a04125440b90300901400f4901c40d40c014603247d0810310161141504507030f4100320b150001142600e00d80d0602440d9440f001c252141070420722880d01003a106d4071601d00761400c03c1102c11000d410342d640d018445140d0280545441101d04190030b201d1070720801180c007541d40c0e05040703000240c40c4200140e05840c1c482281d4540280c0b074241401c2202030041d002196081540302e854402c0603075181381020412100049850566601660314444a00001840114042301c0d440c1c05402003030a0701c04460b11018152202012a01d060000d62080090700584030b0f000313000801e400c6042c012001c03c06090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 604661402 1250 604660152 604660171
    0x923010509010c0f08070c020402040312120c053106081803070215211005130626070801090516120f0204020d060503010216060c182303030a08 63
    0x19079440c924035074240c8510066540008000c001c944199500c640c190035044012403900075003800c41030300040c00b40c0c1c000350816212107000d069880c034040d400c51604800e4600a18052081001c681d101500d40d00400c1c0034010031025914041101402c201039000301042130b0550100d069446010041c01e005007140c40920100a81160580c0c1c03030800000c1d00d09007580108146d01c0e24116003000411a0400e220081000d111141d01d42e50000340280410310445c1c1081002e80142d2618003000004040c1111501d90203290039820700401890700324946080380641e9103001852500306500d4070b0107080381d101541552070200b45504102000c12080803d072200c0009103460358407001e9000c0715200d62800242070841c0c48940000505140d00a840e1030007485000052042e41c0d4030100382079034040b0742c4d291345144000c0d2405003040018420006c0691003031030480070300e41c0350b43e2241c000c00d401405040015a0206184020540e00104808000f4030107807e0ba03480d0054030700c0c044d2800c4425502c0064 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 604662652 1250 604661402 604661411
    0x603110c0a12230d3210151b050a050a0821070503060d110a030c15052704110f0720060a0503090c0a030503030a050105010503010f0e060103092301 65
    0x26240c0c1800307043e000000d041c4500c5140c400403003c004000e2024503410350100e100b07020302198010b040d040c801084841c034080110b00d4030380141601d15001041d001281c04400000030702e02d01560107008000c01c1507040603100c80700809820401d28250f4900e400030402d200d210960000c00020002a282d65100c0302c281d00003200c1c05030b50544001c002103400100040003440007480a1402441c0e101c04c05008400091403410841d002c100041050780080c0c1e0015202c4004006a061001e8000d4118025141050a00c28140f0f04210390440944650202c80241d24031400142d5540e4480d9800541c07850005a440f14200d8414203550000f4805072610301d9501c1d0b500c81c0810588811080050008242600d005200c00c0150740383e0b04042e114a105220b40c0090001d1916103541681c05140100c00558581c070f0803508600669105030050350411900703100400014075103d0801003601c1c43c940360300343c1a81c0d44d01c004178010480e48102811402c041c0801c60036070300704c01030361a1f00311901400070322 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 604663902 1250 604662652 604662677
    0x1b08031806221e050d0201060612021809090f061003020316051323010e06030714010c02060c0c040903050a140f040306020a0909020309060f0f040203070603110c0a12 73
    0x1003080d40c0110700081110808403030400070302c0341c4080f00400f070380d4850400c020507402d03280c15141006500641c40985c0d0341e410188041500081042820b0280440c00c0d0b1170010025040740c900c40c201c0310700074000c0c025140400e510401c24024903117244034050449444e0b1526048210242c0c102c0d1006901034000d04041507038043d55200b400c0c05440d03010304000c1d207a60103102d2610082194448440203100c4050071180a800741e2501300c0d0003866000d10309000c07405c00c0c10405040c00140d078806100c0c40445d0200c0e58859070883c0d6000d00709901100d200f515554003c1c600c9060044c00d00c2141c0e4024507145c10841099080009410400c040359160313065491460082e60891140e8001c1c070004000c2400200b0000d101e0350000c0c001c1880d20718050194a40c3c0305000c1d03050340c105481d4201c0c250094020007c000718440c05540d40304880761188860350a280d00440c0d1601881d00a110405460b901c036620b140c00508222041d04030f2050848075290b015040121842c002d40c017440e00000c11045049 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 604665152 1250 604663902 604663921
    0x31e0706051f120c14010c0204051e0f010f0b0901030f0504151a03070b070804032f06040e06090a240320030d080915090a0c050402191b08031806 64
    0x3d0310302d60080c54403019604018480008203c40700100341000045600240143c40310300502d401100f0348001250f2802190380600c81c3d80100800320f251580e00c0300010404101d500394902c04507021406501d51321100040100c015000380042c3d10405800c01040c0400c200041d01110291520803204020400312800521808808213105c2903141d400490f040c42a256801c0080c0300346407040e13040525040d81ea40e125283e030944012281600048041c12082c00b061264114030611001c5400364500ba0400340c3c8075044031000f030040d900940d0040d0000c0c01a0700c0b80d62194500a48034401c14401c004a150400404002c03801304071070144206041d4480e240e03224a40e21400e0364000c1c0605a041d503485807c07079420400030600d880c02d01c20204840321111080100718020285803001e408041440d0801c070481c11039035401117001d40d00c10816544200308805400050a50314a0000041414001240751b0a841030340090554503000080c480c0c0903d000c0b00c003108d0f4140c418240c0310540d982c00040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 604666402 1250 604665152 604665179
    0x3060a0f06080a0c090f05010e120601170c090106090b030901091403131205070501110c1309020f0d0312090f120f080c0702060d050a0f0606030209010e040e031e0706051f 75
    0x261680450711106c180100e6016041d1070440e00e201400844a2252900c100d925240d000c0e8007242c40401440d0010010750020b11007804401020707a100a003551501a0007001c0d0200c03840349910340200800031601c02502908403000d556042058005c80380881e95034a80c5946c8001003800c40d811107180c0010754115410034001e00550041d02800e02c683c5064010744012444c0e803003602e054041c1c40180040f564440c05801074090300302900003030f01141441441018407048561501c074114414803040025881154004038102c0b03200042842c0404d403410400c0900c907904c000300456a00c4004140c003d0780006c0c00c038174040e03076a81e03040c00588030440288400e2280d0b140c083c0d04810104001d03861080650802070b08410600030005d40e05440000b01d40840e6100c0c1c010b900000c2d000140460f040d0ba022521207500c00c0112010040e0349003074410301780d980c840d034a15a0345140b481c1c01c441c48100d0418041e540d80c217400c240d041c086803400010408a0314408001e0300400c001c881000320340c0c2c416001c1d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 604667652 1250 604666402 604666409
    0xa0507092307030b060d050f01170606030d030b152d16030e0120160902090d0b101e090f09050307020d0c091401090516020304090203060a0f06080a0c09 67
    0x80c0007480d154600704801500c0d0000c8401c2e000402003054042181d003c2c46201d00c07400f600c80b242c11070ba5050511400103001641800c486540c00001030041d0344d07038040340769101c2d50b100303003000180070150070041002c3d1892040040c448120104041191265603820300850301d207004a411141412010700c5450743c001c0440740c02c04403216040d00c1002034010440308030b02c00014108003240411240701c40c115110603582c0089960003000350036080410b080502406002e41a00550900e500740021540070002c41e040580040103150105656203e80300550380508220034030319a440084807800750003481e031803161040003498032501d19050740144c840c2c8083e555000010b1807900f039403a020804d1380d0094400030f480880700c0e2040010302c0c40b000d10540c550480c4d60044401c403585440001d00480300000d12018044001d803a1710101c056000c0129400c0c2c1d031180301c00603103e80300d540114032144000d401400c00900408404114190001482c031f1040b19140420b00c1034082d2401c00b1100d9030084d11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 604668902 1250 604667652 604667711
    0x1181b0807030308060301060f08012a020a1502040e04080a1701050108063a03021e0a120e040f020304060b0414180307050106030b04150203070203180f030a050709 72
    0x1e42880024450002c090f08024000e0000c03581d940c4400d10058400c8003039001c5034440c1c0d5100c0070b1b428420790080400500303000846000748034074500d80029480d072a001d54021f0054407180342c101c40b040c116a041d00e014000340a0b00c0b5440340341a1820402d145c0c001c140c0100071508042007000d0103071100c1c401074166a81a0342ea1031807522580240080c03c2c94405094601800c00e111404110880340c41000500ea481c22250800d05000d060290034610b105142a00001340c0c0e240f04070700d1107000210100f10700e070321000a000301e48140c58101d0f80308500c540001d0f072003824800d10080c034201c00e40155015600402c010401e000018082200b00d070152244a82c01006400020b2880704000e81c01c094400c0448082c1c03841c0003141e541d82821155036810403107111005406000601642c50040c0c40e82000c070000440c998100703000040d5aa0042c41011002c10758071599400035a2110004280c100402030200c504124240c0303007182d00c8110038000c0b05141450700000b1014020200045403101c400c80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 604670152 1250 604668902 604668913
    0x1d07050d020f09153f060d1205030406050603011e0e071d01030302070e1e040311010e060a1b0e040b0d080703020714040c0e10030e01181b08 62
    0x3111020390041c102400b601e55061010302d0441d00c80680e01c01803004081c01071551030740c405041c507007290300c400751142d000355282c3c0d40c0350300b55080007403500000b6041804001c1203503100720002e2172903160303810010140c2c1441120500c0c0980c00001941c003581c42010148501d81ea43c0d820305080351444004224010704c441c10640c1d45200c180c0c001c5d20080e6196041e11041e50301c64072011119280f8501209400240c4401001896810b01096000d0007514a1084c800d062080b9a010030380300c0c009081c0052900d09001c41d04150007002401c03805440403000380040c040e60881d86482c0e80c0219601c44286040440d00344100c584030000c1c910882460303c64000f0b0070311000c10300c8014003a103260075402c800540c0000c13011803644405030442d54842da00070100c2c11f080c0300410040f4403c3c0459907000300e00300805003020503000041d203240d40c103040e9916105410a440100c01400400e41c4031002d5500c0c2c43e42007120a4120102541c05e913003e0050b44140061004407580604158811403200c1c0e00308 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 604671402 1250 604670152 604670167
    0x606120d030903050d09080d0605030a21020c1002100518030a030b0604082b05030402091914010906060801240c05070510030c08150f01050a17040c1d0705 68
    0x3584400c01c07aa0013440d2250400d40708110040403a04002d50030780d04020b0100e4000c988c90380c9401040060481034000d001c1400c50b40ea581c0d0401220708016031460001081e07207190ae20301c00c00c04e40003c60700042044040041c8207001039265510910441100c40c14540011242105528460484081a00194508031240c03508070000e19901c0f20035580540200000120360b0820016102d01c070140000c5001c041c1020030950014083c01200d03c4103000c018401c0002503550300303103c5548404d804c11441c034125001000351000701740016640d501d11116200120300014140d01c9013064030050340783e0741314990701e174013107400c1c191078000e41d8500e103103404404a203115219080d05100c051083e000c50b0201c581b04d0340003449080358100441d000a541d0b02c07a00c03039040e91001400b900800201e0b29044111482c0c00400c01101800c428241880000200340d051580300b40c001c000d00c1c0011002da482c09007010b14004000d0350444c450140c8003d00110009048420702000300d029040341d4642c81c2c5404c81 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 604672652 1250 604671402 604671407
    0x22b09150c031503051c0801060e040b1804050606040b0108060916170c0928050108100305011b110d21110a1e03140a0911031b030606120d 61
    0x260700010314101520340d21042c80b4482c1807003041000d0b6110f07101038898800c0c191810b03840c858004a20000704030380000100300c040d80240c1e0310b1241440c103aa0214403400441c001c101100c50301000100300800c0300d02000103104020404034026541124180007014211780111a141403d488060307101e0341e1400403855460345c15044c0b0740700c04010300307144103504550b01d0407515034401120480b510480006043c800c601c2c0002c0340c2c0180d1074074001e80448003a000300d15612464007500405040c0a0a0720110b078080160741074074401164000000d101d64224403840810f1607107071010709404102c054615a995400c0800c1c0000050300c0c60303a1314901c4502c034204294050340c0300852a0150b079605c002c800c0d2103299400040607417403902d8885450f45070010084a030540c000c0072841080614140034a00390500100200707400100035000070415503c2414071030300360801d0000c100da0521601c80c140d25200007081440c03842441c214141e500729a90754061240003403000e80c410700c0a03040a4200c0700d0250 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 604673902 1250 604672652 604672661
    0x1030c0e10031103071205070813060c0203160f062d09170309060618070e04050603011127061204031d03010e03121503070b0d0b04022b0915 62
    0x1c9585804203618640c9000300c501a03000f580da12002403030351443c1c01c03640041802105c0e000007007841c11758203a1804200300801c4140348003000701039603242c40c603500d034031031081003a41c410114110055142c0c802c1032a2080045180c00000c0319028100711100c56410030380000c1d14510140862801d0802c90b648540d07100512180200700c440d00c0d0340c5141400c0c40c0ca90003000d18410981c1074014099400c02100300240894555a0745905502d0102040000c0b6070007040c0c86501441560080f0b640c0d101c0d07100103401340c001610345401101d00800c0c950407802c1c640251b5203510190500703c0301104625010707c5510321408a07403003130701c3c031700e010100300040d102d10800c40070041841001c800704d900f50710003c0e0944415407910f101a60020402d03646081128220540104410317515000b04a040e202007034903050144606114100c0219000a1004040d082240040002001107640b140709150310a10009003041c400c9080a40e44400405d03030b03420f445007443c425084400038040c09a40c00480c0043c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 604675152 1250 604673902 604673929
    0x807031b030201140c070b030f180a0210140f19120903020604030e04090507080601090e1626060c0304120c020a05040b0609041107020f0108070c06091e05150601030c0e 74
    0x140306d150400101c4046801c00703580540a851400100c40c209100c0c11001c07a44500d00324842504081408401030f40e44000244a0550a052000c404070007400c494105020b101b08a0801c03c900094400d0384c0c10010034840a920300c0d9403a01e07400b494036031024604071303900d07843d0041c05680024003040100740034903100c4040c0b0000a2000c11820320325034400342020019448100c4079885200144248015402001d015003030940003000813062240356120402003510801d0900c0d4000c03044280e6401050a4455800100e0000c0300c0a40c1030540c041005580122000e484034070842e0801d01c5c0c243c2c4115800080143c00800764100181050208401442c105d41c0d0264458000c0259011548490081d10641d219400b040c546817501e500500000d501a01d5589042044c4541040885504100d0504250380c000c0d00010300c0180e03030303e03041c80d00304805280c032400e00456118450411200060101d1054110711001607151101001507090398811108007000c43e1459021141c1405d00705401d0210 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 604676258 1106 604675152 604675177
    0xa0f0e0f0904020f030a140604150e0c040507090906030803010504052a160f110102070b030105011409130c170717040602071403040807031b03020114 66
    0x18850041c4024031421052040444c40d84003008038141c425840702d00e081000c80415400ea60301c82c2c2c211401c40320150044800d00740050240500d12031040320303400403c01801e6481c10800500402400c141c100207001500203110052030049031700441c01900141d42c0c0e94104814032003990001000f034440303407290440610000f4000c4d0f01030b0400306000c81e250354441d00070303103140307541001d0015001d00126281d00880f02441914800141c41180076000c803580300d40c0d20b884d82c4480340000d2107200d010900b4200001c1c10102584001c16410764020401d02d400c03d4010714010844450442484c0001d041c583d122013910b07003000c00c058202c02c83e800c10740c10303070115018484030700346000700010082d035000308254042180014016494801040650384c13129210342d0496a030752130a10043c2ca021281400c0c510030800200e0b500c2095a030180c0d00c01845000b1111100c1d00c0d41e0143d000e0000 = true := by decide +kernel

theorem cover : BRFrame.Cov 604496402 604676258 := by
  have h0 := BRFrame.cov_init 604496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 604496402 ≤ n) (h2 : n < 604676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
