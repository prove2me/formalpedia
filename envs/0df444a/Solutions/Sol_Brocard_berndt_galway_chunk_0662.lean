-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0662
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:59:52.056453+00:00
-- url     : https://prove2.me/submissions/04ebc6c3-b888-47d3-9ec7-6c0ebda7b965

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 118884892 ≤ n < 119064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 118886142 1250 118884892 118884911
    0x120a050706140c030a080f2a0318060c031e01080a0f06143c0619030c1806210f0203070f090b030c0f0901120f0c0e06130c020a06 57
    0x1e140c0180d008400310f60000040c2c1801d50342e40f0285160081c415260325207040d44900703c0e0348100001c2c0c03508120300c0382c003091100f880e1a29480c0c0034690004141989191150200c0b002500b040307411075980080140c08010b001000c18148501c00b00344c00d41040709440c0d541010001603440d8040c04004004c01005100441001640d0f000034a004004002c071100d81d0400d01c3c0d0321000200c00e4be030350035400e14a290000b2110580300403200e04211425001d80c01c1622080d042c000c8080c48041c10f04a80c001c0e00c800003000034803500402c0c0c0140b840c00019409882c0030003100c41980c260f60300030801111590210b0a41c0401e9100e800c9140d0b5010800e071442c12180d2020034185542c5901480841c3c00010300080d903401203411140341c09400720280c9410241310703000c102081e5024410981c01070710100043c00191702400c01c0b40c003198040c43d4402d000c100c40c0e07510b01003100380d42c0d004100e00510180a01282c1c0c2004807110101c240b90840500c00001c40301c2c0000e503900f0450001801c120380303e01401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 118887392 1250 118886142 118886177
    0x21e01052505070c14100e0d02010309060b0a0b030703050901090215071a100f09090f150603020415080c1f14070203010e0c1302030c0a08150904050705120a050706 72
    0x8400841d44042000d1311a40e80d081ca51709007066415065000c0e4065210620569100c1c904000702c40390b00810032030340c0342402c2d00114001c040c058401c071540c69880c800f15400e95110f4001c5c41c01440c1c826031742992403814560041c242e503006042d00d000c607030520b4034402c0160380fa140d54100c48081807249a0b11460030f410410300341d40e02006600036100d01c001c203014140303044001c0311040d902e1b600c00c418191b907550050344040790103500000d0240403100880d84001509501070f4107011500303660105481d0b07141c0d00000c0c201d0350007100f09144040000c800300400c0303d041c0a4400404000c4076003950b0000c1c1e100190040c102c038450032108014401400b000a080c8440655003040e4000c2d000b0050301003220020395480041e01209442190036124410715005a4000c4a1090340118034031810044440d500751042e40d0041e0800142c2255011040c1c0c80c0d0701c41c011014461406140201000b514000510243d100840c04c2c4504640041008202169000495008842d00c906e800c508211a40210 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 118888642 1250 118887392 118887397
    0x3030b0f09070527090103020f06040803030a09020a0914040602030a140a2a1202090d0f0b1603091e02010903080c0d0e010306060e09061c03021e01052505 68
    0x240e611110020a00101c00d5001002e03000c1c04403010346040003080901c13002d0390350702180d540450740b09424800600050912003100a03200601500c1e5904203600c50078041d0031030b0030031140c0601d0140e03602c0e10f16083d89400b0300b2001c010b100541c0100081000c01903050007401000300050f00c0d0540000109900300401d0b400b45845451810031501e0500307181c80d0003000f0303091b040c07980e8095410020080210724071f2440002c010042c2da8487d101c07407102441d0090040d42101110303551054250180f140440c126000030070290b8415107058680c0c1c503080d0503901e201d40b906a6440201803500750518000b80041e2580c4007118000c1400c2d240e0400b441c030040b11460f030140c00052411030045440311000c800028440096401a246c400306804400c00440c04c079151f40c4a110005580b5901c804142c2c1170a01410b43c203c50013030600301829220008880d4281e140076030480042c1e1011140c80038217070800d103801e54950034003c0240010309007070861140510189689005000850401b031303207158002e03000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 118889892 1250 118888642 118888669
    0x91809070b0c06100501030c0503040f03140d200a140c03040b120a0506030c0a180b04060b0903060f01030b010b03070302090d030f020c03010e03180303040302030601030b013003030b 80
    0x280d682d07540d40071a10140e02c455054a452514000c2480081055030180c014140c9180e107640d0303214150340c3c0b241c072805000c2c440d180b003e805000207034440314048003456000302110340742c05101048031103582c50400034203131503240096140c0300144240300d00d095000b6241c55000c424505020340340c964803850a41503200c0c0e42e00402003000e00050710140360303404060351481890302304400c01042d5210018161034060a00701c5a91028150340c082c843c2648171942c003a00082c0c1141d0000300a1529000b003000c40d00c841c5c0103207150b180046101d05062404000c0d03103038000b200b04001c0039594035650303542c0c0301c159044c000c000862801200107401184690b05403950300c0360040011060101d60b0401400e0444100f205500600074214502e03124241401140b6036090104000c5240c4040e400440015a40942400e80d05000c02c110000141e80c2c1085617a01860146241200e0b5515124a2270001821541411624108400c0340d514003450b11010600741da0f010304002c9040000780c00052096201d488 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 118891142 1250 118889892 118889909
    0x27050607032c12060103051c17090f070801060308090409031403010b09010306050301050f011401090801050f09010501060c11010e040204030f0f021201020705070b070303020c030c010e010b0609180907 88
    0x101030794100d02c50110761100400c0588000340c04660902c50240c40741e4090001403c6688030360f1b0383d07005110410b400350580560740e14281c8400b81d944280e540800b00281c803117010343c0d8046080140c5000d010701030319000b800c450008110051940d41c0700507041c055101054070135980c600d2040213245c01780331030a211901c0804101c0c3d82c1d40e181d006c1040150080d60000d4002032034400085020f00b01441058040d190101200700641c0c6001007880440c0b0706214141c0c100603164100085c905400d00490340039050544542c605813625000039130858105134000700c1008240c2c102c60020404501d24609c45e01e2003880d10b101601c0040e008a0b01030b02c5242c0c80180003000b1031490740c2c2800004441620201e1003101c1300e045903150110001d081c0d0240b030b00c0107007250704009000c0246280e0321004084040c440c0c14094100341d180000c060942c0c00c8484805944d0351904e04c0b07850012020b02c540e004440e0304030342407401d008446000c100500a06480200324075519000b1614a141c10440c4100400610 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 118892392 1250 118891142 118891187
    0x120c091503061602150106050d0911044d0903240712051506091f080103050c04020304080301060302090406090e1e0a03020c091801050c0a2705060703 66
    0x41000d044140324203c030410041c003607180032007800c96050844504880850350750500307040000c26500014000620115103900781c54055440380c3d21389000d207190100c02c8038240000703500d054007a078642400aea0600722132201c881c2c40c0b8408208443c1030b04030313070382d034000040d65190b100803008245040c220482030107040c82088445080c00e000140001d11516659544059804426042c042621400d844030a00007490b4020400e07281401c10151035107001c020b08440c0c844d60010711516242c03541c00300c0200000c2e0000018004e000003080029803181003514114035502e003580780c00742d25004c1030281d50304040d00000c106003e903446422150280c01e80f040104540f00d82c12440310b588480c004101018002000c0a200c0450300101320320100603050f401400040c807600c0104842c0307070001000c203064510714181046640400f440340c60b101d0380030500d03055a500400200a84421201601d2040b0184044032903200103c0c007500b03200031100103640a80d144c840a1a00b629000b4024901c0e04004041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 118893642 1250 118892392 118892401
    0x80a09020904060905011d0706030f02130f0303021902030304090c0e0406060f182301110a0308010905060603040c03030509031002030f010f120309060e06190f030b120c09150306 78
    0x80d900c00c06401740b0038030003008007811407a1a8000c03424500d5054000d84c0240c0401c00199019410040149512140051074500701e00c0c0301c1e0711612842d07005610b95000506060082580401814440010007030440111a0b80d59000981ea4401c0d4068080616151940c01c0c0301346000d1443c0d140380410043c024007805071140b100802d0310f02240f5881c0000380c00500140604035004031351400f0f5910101c5540c1900d048213001500c113604400c01c16040040304130700000720b100c041c041d42007818403e50303505110354585040001620000b52006220740e108009000c00100c8406000c0c1c2240d070f15090950300c4040000000f42412070702e40c078084c0018000000c00440103030005209050b1124030144000068554601083c1204000401804144a1101885014024154880c400d1402080c05160951081008550240701d942d494081084100c00c104520b4060003070805401090f2005815000c103010742560703c078464210b041c00b503429040480c120300039003030380d40742080300c090300329200340c02c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 118894892 1250 118893642 118893653
    0x30d0806030601050d03050f090609060d050105010e010504260f01090507030203120a0518030c120606040e1603030c020a0801050c03071715130608121b06011203080a09020904 77
    0x122129403080c042c100c00810140750240c1110302c07191701695280d0230b0031503440f40038250b544220302250303003c18140500061961050014a115034041e0f0004c54203501d00b0001501c40f4010a200b20305010050009000013440b603440d5a21120480c1c0358044c0508000e40b10a04000c1c09078001d0440d0b500388a01311060090000e5007204807403007582200d040e02036440f011001070050080d44c10000c0c00c02c01c5050f510045111003d0002000102a900601e25000004000c04c145250078861900904200101450588505403003881c00d03001410546a540c28903861401d4030307000003070078040d020be0407c042d500d42c1c20701c010103054100000c100744d041c100c060100b95001102c2e200c0010b40c03150310442506580703070301d868001d00b03403d1800c03101d004c08403040100584005284000c800c0d696000001d00340810008154403400c03502d0659a42c410361128807038200075403095400c080d0b0182c001080550f00c00d007034080c85560503140c038000d991528401c00b4060707e03280b240694000724000510081c444c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 118896142 1250 118894892 118894907
    0x62203021905150705061b04080105160e0114030109091110020c090907051005280f0e0a0e0103020405180105010b030a0612020f151605010c03050c270f030d 69
    0x910460f000703c1d03080c00c1c0610f8048240b09001000f00203400c40c0021441e9030b2001c129245c2c0c3c05d000b90075030606250b124020142110821584207220031201c4c1c01c04401d613500044200482182032a200d00c0c5400d40c2211074105102c10310585140710384d80e00b145014011703075000324244c070303203000b05180908044c2c041d001f50390b9041031a81ea4410711020020488441c00003038200c04035203015110b41d101c00844401074070306400a001e0381c116900c59002180440c103030341442c40000b0304640c4520185100f292002080300520307400c05030181161410602418076030184485c11a64100ea011695585401448014010880f00002ca275030911002003150f400202c0030314840c00140e1070800000382c3d29106030400340d054140194120b01e00d030001030700c541420481d003803d40003407a0303d203890010310307400612031180c0181e001d03202030b550352142005c45c0b5414003801b40c00400300110b00b428000c110305a55100701196004000700040e5864400343c2d034403203800c454032402e0003d05440c0c40d01c0c0d0170180030340041c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 118897392 1250 118896142 118896149
    0xe060a080a050616080906010324020d1a0103061d0601050702030313030b0a09081902160b120a020406020712030306090617060106020d0c0803040f051606090909020622030219 77
    0x50303000340320051245115945d1603200d902c0c020020641a481d50b2513800034070305040e0308041c49000740402c0d100b840150380000c100b4003540c82c100203401400c001c4402220740307500b0103481c1014100038041040d01090071001070b100240039121002d81d11084016a00d40c440c02c0b40094042c0000f01e0441524000c000800e400c0364000c00302c07460b085d41d070b0151040881c0d043c2c41004051010512003003d40e000340c0205070003aa1040c4c01214808501d0ba0101d0410010340c0e0310000681c20002840e81d10741401400300303a0090f41c05c0009508042c10000003944501c1140201c1c40d0016603410b044092501c030b078000400401900d50100302503500c0d0380707200c0b05031181240940c07401e1140500000d41c00d4800501c181c50848140e44440d80000d4a60750214154400380058030288003008041010640903c52031300c003080f403003070b80c09843c1d4a0814013500300160360b0b2018041602d408000000b58031650100c43c0260588c040300110b251021607200000346032600040e4100070507900d0382a50192714880130003034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 118898642 1250 118897392 118897411
    0x10822120201050703090803070806150309030705010b040213030b0c07061401031101090b040513020c0303130507060c08031306020d050a0c030b0307050609040b130c0503010f12020306010e060a080a0506 89
    0xa503102041175090b240c0c120801000c1e541c0800c009072225200d84420b98010b00018000052001641040e2045400540d018000c6800c00100142040b40902c12502418010b03038041d414410491906148107195100240c030700e004150001c2c0c002c03003a000448941a520040c100186110101c0c0c600d00d1000c00d0000300c55808806c0d40c0c00c00b00e50b004500f070f41c3c215102280041d103800c2c104410301800c003c1e0500c5071001e10380c0901c074410042500380f01851148031000c14500840390307581802403a0a8059001d41c090111404140c80403481d0b03074007100d621110251032000080d03168641000244500da00c0100c1c01494007082c02070304803c50708551031500b243d03601488206103040401d034982030148502039000354204150174141c02d0036000343c041e0610080c0302082d00006620040181c0e00707020f118000150740040188610500304078118050440c2171075600291481c0d9010a503030f068180285074940305200b000a8499540c00c0018000d0440c40381a1603851540b803038110b13510401036918202 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 118899892 1250 118898642 118898651
    0xa23060d1e200d0b151309050606190f1e150e031c05031503011e0f1518200705060118050c12040201020a0c0b181e010822120201 57
    0x501e440c2841003454066001301c00440662601e111000d0b500c40c0c0808802d4110307803444c450300c0e44c43c60700c0d1203201641c501a0000c7c1c0440d1800c60100301070341031a1605c96a4400c0c41d001d043c807000c40d48075000710540e00040500a40c1c000010302d01507110703003030350710080000d64042411100d16a00003190300c0c00441c05c0d402c03140c800d181c032456070394035503c4103420748000380c000d20001c1c00c01c8408a408124643c0090000140309210800340b4080c00343d11005560720329154810211340c40503501c205c0807802030000030700000908100c14819001c2050520348a03098a882c413100421581e210300041c0c0c8140c1240d12540c44445140840d222007092191891420041c2110034641c001409040d21442c422104030340b828a04101d22901094050000da04500c2502c0e0850300040341d8565560240c0685452140c5600f000552404010440307024580110030702070404414219042420210741c009082c500c45070f070307207140010507026164800e01d0044207403e00c8a2003440000c440003071500d01c0d40da00910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 118901142 1250 118899892 118899953
    0x51e0c0f01020c0a03211d070503030301030206160213020307030b040e06060607080d021303030905130b01051e0c010c0507030f05030c0a05031504060801050a23060d1e 74
    0x14200c3c0184000b030f40498001c0242d0784002441011030b000b04a0351398100e01d101100381c0000e80308403025450840f400c960101c0e10703010a00000c1000500404003240110302d1076041d030340411000e00030080c10030355180500c8200e408658441032140610310b503e140c11502da1a08903002005003800c0da101c20700440c50314103000240c100201d00b0910901003d4a15807030034030540d803000f509a1140411218803a42030000d024140300c6223240c400114029a55403c0e41402c04040101d00d01030040005801450420b0b110781b00d0360003a0a481802e0b01c0340c034805405d00081804143c1034850544002000c0d417800d0b20000d8459041b10107410400d010f03035150820f0382c203c0c2000703840d584410381c0d00448804c000d11409d0550307442070009541c4005003900d07164041918501003029102650485600c40e5180d00400c51018800e00c5446a91380c008841026012503090002480c120064210b81c01031282220090522512071400c008081e43e201800d406c0d2101d43c2040124070304a81c0d1114440445c10301d40300b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 118902392 1250 118901142 118901173
    0x1903020301091a06120702070806010609090509011a1c0203010f09050d02070e0c131e06030e0d09050603042d150b06091207080a110405010b0703090306090201051e0c 73
    0xf42c0c42040003820507850700305d162105284180d0000d0007030046200e803401c04543c5a2090085500a0895442d004a1242000400ca05a42c401409065641c3c58809045108a4500500c0c803d000c802d4407414090043da0360181114550168069059800e103001110540d0050780612a03250180081e619040c40241049840d02141d20600c40408255000314401d0340f1841d00808008014440c40358045540b22136419064900c411103821120090b5400c000c0c25815024813100f55a0080241601d84080c082c0504007450f9401a14090500800000c082000e090b40001c503260451450580f00004010303284c0000c03240c600700f1521541c3c1201c00c000c0806160203010302c0441f006054600700040b080034040d5030804c41c2d103c508940708812001810702010303c0040308171401002c2400c40310071410180425944180e111041013a8108904c00101c0d900980c00d600341d940c4400c01041c160300034001201d40740140c9201444400c140c1e1340800841e40010010040d42980c8130941d00404e80c1440322 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 118903642 1250 118902392 118902431
    0x10f0806070c080c01090b01030302010b030115060f03051503010612060e0a080702060310031b051c0506010e090313090b0108151003020a0c0f030f110a0c050114190302030109 77
    0x2800410404410707100091500400351016052001c00014400c515481f6404046020303030090340581d5460220140d107003400c1c0500000120b510f981d008000786050700c0181001038070103507403080540c2e500200b0f07440d95102d01020310f0903c005000b1301138241c603000721107400500a0f801f01c0c0c605140203c0e00d840341c180454000002a00b1a034910b0602d6829000c0c0325042d07100074458690341303c5949000c4000f0b003954190107810b508160207201414184000d0005940360300c0540ca450200b2014010f002030300c0050b46906690400f0000d40c0d03c0d0b11001081c518602610304140d0100300080000b20711054654808201c00b54243d8481401c2d440e600c2c9100000c0b0785040c01d036900107001069410840b0b000ba00200342009503440c2c0200e10010607100c10506040c0040c0440000307a100a000c00f07030340c3e8099440c001034028070014101c900400d83d00c0741c039800050310038141403140d982c034900c21000e040020b4516402c80240700d40d200f1500d5000c010025030090265000c25803a051400f01c901544d620f2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 118904892 1250 118903642 118903651
    0x405100213121211060f0a0c0c0c0612060b0304050c0120030309031908060d0201180f090e1221070e09090f0d020a0c0902090a050a03060c122904020c0706020303010f0806 75
    0x1004803a07d0b141d20002c05402c3d1000d00d041484a042150b000142c1c4040c0207400402c01565420041c00c10711170008195501c80c3e110030010542170007400040f84001c992401c0d95002420000804507001580c0c400410740c2d40e904400501021041059500c13020008004480e41c4030f01d0582c9022400b141620070f24000e4a01c26001016070400ca0b0055000d0061240017903001818400030541e41c0d0701d0007240080d160002c502260f10340141c9a099403003000702808c8000b030b50700003904010540300400ca411400c1d00391004001c00000c00300d40314074014020f07445580780c040c100b12030074502601e09650311230061680035414031400340ba20a01501c0032079023201c842e5008400b0a0518541100c03e0040d4000400315907000070900000546980d450340d07040c00852140e02c0205407a518018090b100071403503003442101c2410720810f00580020300c105010900e01011003e4400d43e00c100204000740225141501c1920940c2c0d8007140d166000000707541203520070701640001580b035400c03460311100180c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 118906142 1250 118904892 118904911
    0x602030a0309030203040b0a020a06060b0f0304080702040216060b0a080d02032a0a0b0703050601050304020604052707090503070f0303090e180307030f0e09040510021312121106 78
    0x410140e40511030b411445040d8040e10449092944074222190550311002a900241e44506500c0e009c110440c000d0100405014034001d0401c541103019200b82d21004100030101000014000e0856455038180d400500040d20100c00d10302103840c00074003c00307850340e241d84100c0c50382e00001240100010003d80c4202994007450401c0c40400000e01008000c440c00c9566851400660400038800c01001354030754041e0302084d1103400e04243c003600b00c860203000d070b50401c40104200005600c0e141d0455084500a4401c8200440f1038a0b0083c1c0ca180c8010810940e8500d800a010707a02c0c0e44042081c017903403022015180401d9464014180c41c03081480000c001ca0b079401c204101441601d20015404001e024448911304600c982c12811540840300c21804076001065600307403594000704d45444206c0a40302c1800e14107064450359a14211a04200c0c16190001102d60408507481c070100c0003004018000398000d0b49600d81401103d54070b001600c00114286a0240d0101001403218007810184 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 118907392 1250 118906142 118906147
    0x1a043b15010f2d1803030207030308040303022205010e031903140f0d020d0c020d02120307050d090b01030302060c130302062107030603051b0307090e07180506030610060203 76
    0x8015914600d54207690020312000d0039280002206103461400f02c108202c500710040c0f4040c01c0040c00c0560669609051070900d20b40500004e41c000808d101601d07050709111500341da17145030803006480341e50048440504c50036041c0c480b110000782c1c141c0989009132031f0030901c0f42e1440c05041e41d900b0909102880c135403a424042c00801d0242da21009400c503d02c540038645a06104000c00035803042020800007a07000602c3c81156009100e140340280b450300c09010204480d0074001e6582c3c85580700840d07448000004506018090320807074000310703020344080c8405100780c2048401d864003440305030b0140c042c100000d060880804220f84000b07407022030100311141140c00388180350704205a445280c0b203000f00f420201a08441d00380340324103d1070b980854818194600b00341132a42801d00d0000300b10403403076003540980d00491480c080e00c10f10380001903c140b0b80c0d0b2800b0300e4160b199100d848004800d0703a200c045552903401003481850140c08490403900c4084240401e02068422400180c006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 118908642 1250 118907392 118907431
    0x110409020f130b0303031e060d02030a030e0a0510030609060b09030a0b06010e0904050a030216141309020d0317060913080a09150c050609060f011a043b 67
    0x20914610301110050000103d449546001c2890b40c1e2040d00d00000740c1440d011b400c0940030340340e039001d035102d141610f103a9114806640882c0c0e90764801100202801500c245105803030b2660742c2030a0042c0002401c00354483d1390000d000d00107060724010644058104107000c038580305aa0b08969a2034030180003425103610b96111406c5d1800d000e0b05071030401158000000aa0b60398000c4e10703006901400103811145024640645001030886542c002c0c550259010000c4a842c5842481800d40946050044c03154484103000248659540254440000ca0645050540c040f00605d03414000607508042d0b42c440c00100004041c084030380d541050440c98000c4001545200501403004060902000103038a40f500002d00300d4020011780001045600a20203001e8104a295042040e6901601c3c441c20306c002040d55100c414041c106100f40c014040c901703503030503c0c011140203200c066040c50130a8141c0c8101400c01c2e44641601130410000350f103240392104070081442c00381020100340c0d00c95403034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 118909892 1250 118908642 118908649
    0x305010f03030f1215090219030507080105010c020a0305120301080706090503070b0f130b0309010c050309060103020d050703120810050306071d150d0209031603080d05040c091503110409020f 84
    0x8110303c03a2480070741765504a1000f810545910700601001c0b10b0140e2505120303403005403c0303291040d4000425007000144608603400030b6030359040d22021f03c1c04062011300c41c008103281100d00c2e40005c00c280300d40615641030083c502c010354142da8600c001d8481c21aa00c00003110290b009010385035050b04445420007950710250010f04c4100007009000d0304004501c41c105418245c1741d800b00c400c0c0c010000c100488013400784513101c170814242c2820741c11410300200050303903000e0502009002d071800d019200140311040207100010f680c000d000d49482401d01340000c2c414007040d16134040e44034860702c0200f0245004102c4a11800296540c0c058090000c600100403551900340a500040d101101c2020303500170100800c80108413030400b590381c880002c1071625200e1000d09212192101e05010b10008902401b254444076105a000c2440e0300c890410640c81c0308968014510b007460b03c2802e000b00510140454104d13130041c29400031118400b821720055a58102d030003540304402e11183c440524 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 118911142 1250 118909892 118909907
    0x708040b130302030a030906030c030908071401110d09050706111005041506080717010903050415030b0a06020c03060109050c220e040b0103060e1507050c011401150305010f03030f 79
    0x440c0440c03240140307660ba0700840e06060407660305800042018900340b11698040c042c0b40015107aa140400200e09951079048a50082103002403c00340c024513a100300e00030075001480d000c00d012002075034034448a41058000c1c8408081102c0c1801791000020b01c2d00d000361200711076412141c000d4820f41051002c00d60081c4001002210b00441c030802c40e0703148510034410900034080d160700038801d1506004552500e00b20262028185a0405503140300080d40801a1822101e07111300c0b20090110511050f405031440c800f44a0300300707180000014020b0303400103003800c0048040e020340350fa40e45c1340c5455100f540c5085600700d600c40b5040003404820a0304641d2245102c00f0002c00d5040b2640340c1500d086c0120007960280d82d4810241c00500501955100d4089800e4400c802000d00c0d00c001c1c5a03044080000402031400c0c400081a02d2001080c01c0d00204401c2207a1000e849075917840c0c1c142908200c00040841000034600740002c1070000d1004007520640f0f03019115034a24241041007183c20a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 118912392 1250 118911142 118911157
    0x108040c1e061b030f080a0603050616030f0605031b04020c010f05040302070e01050907030b030f0105090d0e0d0b040f140a0f12030b01210e0303040f170708040b 71
    0x44000c06030000e0801960301c00051540c0c003407042404802c0c90030030b00070030a2034003507200312010980181c2800041d4100e0b0b480e2402d0314242c10300b40901ea0b105100e00000340701d640c0c4080e0450003443c00704001340c641c3c440726244213446618200301b000d000441c01412210300303003d0300340c0540c800c4550440200c034030041c0d411204801032003d4a0078003020000f50030340e00034550540105885009000c101501804240068072850300d140902e90300d000006800c0705405030001040c503650b00c05455041c0c505005ea2268090464000d1107142400c0b004030340c1d2030b511030030310b680000e61014040d496460200035000b1151340185104c034040c0c4480d19140d56641042100301c0f440201010030f0034441c0001d01c4828565801803e911101e4121070814030201c502c017107102c0e01003519000340b40240381c2e0404914030051070000b02400e01401034070146001484800c80c08080361001104000820282c0b0f040800110b124811f48c5108403c44801500180115070300140034a106200a000f515064000342050f03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 118913642 1250 118912392 118912403
    0xa0302040f0f020c0a050c011d01050f0408011404020f030706090e07020106080a30080a150504021305180402090f04030207031205031e09031602131103011a1305010804 74
    0x8002c6402c9200040740d001c0410900543c20038804d441c2402000c0c459005654400e0910f90384c01c000303100c030300d20081006030307101414050f0205d04901010102400d03034000d0010b0b8002040100c1244100c400d0001c2c080301e04074403608660051178103504012801c40704a414545581c16280d003044003401e00071a0043c107007001c640da00c200004440c401000b5041c001c50054110f4441580442507207a014818250780420190407500d540385040c0d4084c182c5a03108800b1000012505101056a4541480c41e401147c0c06070000c5910207190070340401c142d0456000303c8910902c0300d000031061826907000c40c0c010b503112542100040310f112a101c0555072140c445e01c180c40049441c0c0d61003000d80d071100b100314000505c02004015405940c4001d021300c907074409001441d546030840001e640c80c840d06205a40840240c0d203d0411920b42e000c0484480c6d0780c05c0030900102520580590341a0002d205030562050f6100601c01c560700d4910440b4403d608403204005c0030f90401d001510203003009001141c6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 118914892 1250 118913642 118913651
    0x3040602090a12060507020a0b06090406150906091409030f03041a0103060e0c01090f05130e01181a010b03010b0a020f0a05060114090f01060e0a120606150e0a0302040f 74
    0x500d81d40b0401400c003c0c01c80d1140e03500c6100d015080c40f0007143d600030404003d65108404050214105401c140da003c42c00b102d4640b115960b6190250180c82500c000401624098a0100d42d1a480e0780090b07003030320300c80c5408100c0070740c2040b1504449002a5441400c54004001c00c1d050161443c0042d40d1180c05a4102d80300504a60007408083c0b00036030041c1c8886e036a40c08515444c60040c0500710b00c8000903c1c01008640c00d10b92074200401c110b00c21544a0090501d401c41d0f005e88a030494441d0215071002001a158104d000754445440010704461070282d41080c1d040c01c80ba2204194182d0310b102d48100c2c2981e08180c015030323480c1d0201c070b096015440f4070300f802003a05204014949055200b94080d2541c4e500d0881581c0b10303074092111440c460500700c001c002440b640051100e044900f140790840f41c81211a01081c401d1180d90807031092500c0b2900d8600500900790426021207000190048644403032020489030200d00d0400580d01ca40b00c00010400340c07030513403c00001c1d10350340f10002030b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 118916142 1250 118914892 118914907
    0x15070c050409241a1806010302030702010902120f0d170402010c17030a06030b0105030c030a02061e0a05040806010501030c02150901020f0d1406060f120718031a07031503060203040602 81
    0x10b1580d800604140b0804c2e259081d4030407091200c03400000d403040c02d1395079044840040140545110005101504066002c400203050034400d401a90009402802001890300c0f0036424984031087e44100505c1d9129080349040aa480303816480105101071340c4c01c0a00740c507550300460741c0c00e10912054405484030b8101421401c5510015030250185082c00240540743d850034207071030030f0141d000d14031a4114014810690303c010030903a2015a044035020b03030320f0441d84501c41403d50303142c2200010300c0c0041069201c0d04d402030300070b1060794100b1040399031607a81c80c001102610303e81600c80c00182c0129404011402c3c8032942250030a00000015003084554209280c42d40c101449025165440703181143c1e07000d80c07880c800d9070050010382c0c0346450125030710f1b1580ca280c418074071241c90180e071140000c2c0465208046d081110b00c1152110101c4135640e003001d1030b0402c0710704402e240c5041c03808041180740e0f00a11440394000c00840100d1425499500d0388e90003904010001c5d902c0d55002c00c00b01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 118917392 1250 118916142 118916183
    0x4050a060e0606180613200c030a020c040c2015072604020d080a0203070807060203010509060d0506011403030405030d1e05030606030402090a0f061415070c050409 72
    0x1500c107840300c18010210340c9010020850801c41d02c01038414160268000d11030603442c0c5484c01c03d4003d1101d40f02040081002c103c00030070381c42c441240360b212000443c00070b060410101c000c0103105010350031604c1001403001084110f0f1009104440881d0448020700a0540d200c40413603a008105401d90300444611802090081411541e03440040c490031a0301000c0901d10100491b1400d0030300003000c05240903808035114240a21000d02000d40104062015920800480328400d900085003038451030f2038a0200043d41080c0900741c0b0401c2443c000411b64203041800d1400250082d0050115900c0c1ca181c1e41e8608151a08558250008010109190b1020889040c6041c1c09a0b5003400d103500c00d559040404420400141c1005000c100344207007030341d0304003d5039000380d011100500a80c4402c0a100c00074600d8421807036005040160004600b210200640c3d1990015503d01c400742102d048424004e10803507a008003031102c0110240064249a031020f00c249120700388421130a01e0f0b00c80c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 118918642 1250 118917392 118917401
    0x2f0706051906060519050c030a0c020a0b0409140603010506010c0b07030b091311010206070903170409050f040b011d0a230907050301060b251104020a0e04051f0e04050a06 75
    0x1d407010400c00145c1c40f00314518004003409840443c580107080c00e440c00f030362580703a00c42c0101010410074807148102c00c0d03690746901000280b0404035016a1607507030701080009400d184074000c0036122410300090b000d081c10f016003403050314160740c1c80d14034000d540d841c2c039a400e4014080340200f555440e0300068036200c4000260081202401020381c0188510b0b00e18010081e204071641150088000e01407002e8105a41c401501d80c0034007031005140f019882822f65000b194884004e00d82003070144641e500e10200c070302d40902e0140c258200260f88541042ea4000d108a81c041d120300c0045002919150866000304407100081105503d0813005006401c0c446009031108005078001240810261400340b05640c000e09584410b0742c140314034034242001c3c1041201803103005c004240101420401c3d010316503d810f502c010000c6455401024000b400d00742c0070040c0718045c629103000708004c2012440391084004600300d441001c0c50400074812005c10001e401120319208801c0c00c1c60000b85980103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 118919892 1250 118918642 118918649
    0x20618070f0e04110102070b0d021804110703020c0405010b040e04080f070516050307180f110f0703030f0608030702060c0c061605060f0c040504090314030702012f0706051906 77
    0x402c0400c604003400c0041d100f107420800c650655101c0352041140700729400542c2d40e01021141c0060300c40400c0b43c40825141044a02e0315032291070b0a03500c009810540c00904000c50081e030803111402010420702c004c88400f8050804107420500042083d1601e207800d555000d84126001c81c1404503119440300d07030790441c540403180381e004099820f004080240c4010b004000842c02031075458603156010760030046680c0c00006207600e41c80085000100c6030040c0751003144031480c481e600c0760b444030212050780110004800080c00c01c3e00e0752441a0340c0e4003449040c1c03000d560285190402070b50810036540d1000401a54034000c02507628141e80d6004040c002c8032242000d2810500018a040c506107803004140b103003400c1c20041408140c03946003050750300b0f450090324000b4550506080645001100c0c54211154890010401000c150f040d080b0340c4010710b11039000e5420265540c071110300b54242c8a01015000c2c824895100401d00d0344d0400e50300300016078400c040344020b0644400a80d1202e81 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 118921142 1250 118919892 118919909
    0x20307090b030d02010603031403042103021801030207020616020d061b090b0a08011401020709020c0706020c030d081506070203030c0106050325351606030c020618070f 74
    0x100948450505000c8403420283c41d1000b000740130300355a0040c0c80032000060b422103061020001030104401c540101030410b820700c0b1180c4201462070720050181d889860700310082510302c518100340794003a00a803503405c2d500030134917410000541401e0f1032260840c403003a030340300c8004810000480d0340743c4102541c49424491500c5501c0300140d002e0400401c40d4003800440c01c0410802c0c04590f4021083d07419540020402c01d00d0061050040313150801a410007030aa51001451007035444c800520b00048818540a8428041d224030801d5107403041940840b0110f0020800035103200f805001d00c65894200a1055040c81c0c07058012030301e16005124113009580d900c2c1c41c00c0c849490f01700501c0310300380083c0d950608054482d46d15103000344002e208480c10b10744580300800007100491920b0460704541503a00c0c071080005048240c2d9401c40350f0303448000e080c00e250301141140c86070141c030408000c0340d0020921615070302c2868540d91284000c0e0b00390380c0a004004a44a10800b446900902054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 118922392 1250 118921142 118921151
    0x3040b0d090506010e01030f110f0613140303030112030305100f03030c030914130b04090506041b15051614030a180e1501050703111e011407081305030702030709 71
    0x42c41c0a034a001c5041c0c10014260418500410004812044801e10b03241c1c0b1016070290a0034100100b06441c00c21040300d64400d101040101a84011744004801c440c213030885081040d10340d0090584a2000b0301414801c22000114000481c0c040c1e00310542008045070024401a568041d80703852040c2900f089000500f1410b50005141e4001d404a01070591a01c100c032000c204100003410043c880744c1010206901d510154085941f03a0b8005074250b40c00000792003840c6004c0c0380041981d031f0580100000c110310b64102003000e034050002c6210404858460790f16014141c65641c04504252400f2075101c503140790400d0000d2002e06c080c2544001603212902d001d600007907210b8100c1000d41200203074200704010030441d9002c0005501e81d080e0282000c554170307412030908407849004c0c0c009510f407a00c9410b80307203100d12450340d02c00d004600c1582c000f004200045480344605001c280d070b903030001821004c0401c9801018810000e0307194864422a4a0f20f00e08da07000c41c0c140400c940c0f1824071260744 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 118923642 1250 118922392 118922411
    0x1c0f060c080a06050a05010e0f0d0503070c060503040201020c22240501020c090a110c060f0103060b03060402031f0609060b0d0c0f02190f0b180c0411040e0903040b0d 73
    0x1140a078000c07140360300a03c281820140407400c02000d40c851141003100b0f4808100c1140c984000841440b8805010150707603e5250034115603945c494502203030350652800380011400c1c82001900c1c0120b0317050b4080c0800c0040f40082110001c245480140c0f929101108003449170014485c041c000c2c403010140c2c036a400d4486006420021007a4401819034121507102091541c42080e04c5902c8480d030a40020f09034081c10703c80c03c40b4042c02c0c082c4041e44c4213840078801c2180c13007068441c2c1200e01c202400c2c0030101c4140c092680314501990000e4159100d180c1401140203860714624500b00c500d2000070b449030303407104140c00b90381e0664031071543e0800c0050403400d80020b6006243d500da00c10300704149509214003000707540b0100480c0028030709075401041400c0010410100307040c140c100003d030b4181e080000049118980103260442c0703509c6a0510003125003041c0c003c058003150300341c00c618186442c1c004220304181004145030780c1070004200c081540314000015040440c4400000a1002072 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 118924892 1250 118923642 118923647
    0x40f0c030f0605030304050117150d060b030c06160201030b030313090e0d170109150e0a02030a1b021203191107140c0906040c030605040c0507020f100e1c0f060c 71
    0xb5540025000342c000700414840390b40c1100c07017500e0303003000e60303a02076210750310010140484c0842402c1c5541c050030001c0840c0510403541c0207128002012410354100445490800c00581b1801503410301c0d0803201c9111708050340c001e40c01a15009400340070b0b2490b0400034182d00d5004d03d5544c1154801c0d583e10801080040820001b002d810440c5040c0030020200b80356000640c0501441001003071034a41090341d41c0034000d0302d205002413000746682c4015040c0003008201070340040316426100d915143d001070158800c1042c10041c00c1d100c1d001f030618052a40201d200e658070003808000c8404001c440e803900e100c0c1500c07440100d5000040d6698070b0320715074a040303240c40d161039500ca8003541c4050b200c0e00c42036848070300554018200729400110a4919181a005030080b644000d90091070644001103e03a001002002c0c080c0c802c4404200fa514848100508000d9006421001a522610322a0503042c0721001e03600106c5003040340c07032030100a680c0e0080d44041e421011550780c1e0300d90100ca200307180c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 118926142 1250 118924892 118924901
    0x709020c0a0b1b09120a0206070b070e010c0c0b070f08030a230105090106050c0f1c030f1e090203030c1b01080603010c020a02060319061712070b0c0306040f0c030f 72
    0x83e55206140802c1c1c0f030010303041113014800001c0d00c030300344c4000f030522901d00410002c161282d0241205450702080d0070900a9510304075140030100b010200420b01e103602c40c1d9440924150700c149110401420641c0200854114100850350b1130907180c44d01011a0380c00b070186104110422002c1071190800040e48007400044104800c9070b00b12000610141c1d0701c45c801141511500c1c074105032284200c08403585824400d5024410500907001d41c03400c0c01c01107010f03c2020700300f2038406200c0f10310728500b040d04540c1e240c8140111407042d01070400f60412560040003810b80010101d90510360846140c074208212a030440c42d404403c24100b0090356004220241e001c94124001c01c5080d01440340079444d000c000400a108510000029074031680720700b2900c4c4a001084ca0401c5556103840035608034010282c0350007142e124018402103002c4284084800b80d550004058407941c072020640c0c0784580015000550184d00c8074507203001103641c0d1040d1140210b1668010594240c0385883e0f90032078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 118927392 1250 118926142 118926151
    0x20c030c070b0304080d09150203092803200a0c06030504021801030b040609030504080706050d0e06010b0a030207030203041a0910031a06090a0302090f1b03070c11030709020c0a0b 79
    0x32505100700000b00d174540e015210340e001850340101e0107041c103240c0800c2c000c2082507110781c0e5a1000c02405030020000a510b224840800c9207200c4d4040c1d48000d42000c20a20f410090000f003141c034001e0750704840c03c84403c00c120200000c0354040b1400b5a80c403880c2d14129044440069910404c00c015850219840c2c2d80405848192141650454480c1d8111410080c4054182d82e250036400c0c0c20984210103d0b001098800103a44d200340d00d4880041071035001400d5581414100400e118000c800415418120350030384904a2411824040590207900f08a005a080d404107110009041c1024225003513010a01094940e40e460203404004000d10000b845030201442e0600000c0d034842a1102a0801142160129210f02405002404144680d00002c5d0000d445500f4031888a401260341c0d4000d06410040000003110881c58462034081140d01c640014100d02d183d00c08260441c0711415018400380a03100601e461b09503000c02d03a03101c3c0d007514146510080c02d441c140441c05804070b400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 118928642 1250 118927392 118927409
    0x10602032212080a1103030108071a120103030c03050d15031401050f07110f0f01050403120b03030a260118110405091f0e0403020106030c081504060b03030706020c030c07 75
    0x103400d00c0d1031a0070312000540b004224036000140070188a00411100e15a07100c40000c072540d80d03844070f500f2901d40401e80b103421000c2800c000d09034960750400701542c1c00c4040a07031a0482c241e01e50b8030300325081000c140d0140c0602000b00111070100805008518400082ca034180c82d0366413440c6000c072603a51223080340089a91600061100300d5140e0b94140360005283d20344028400c0106079031504015480b5020a101d00c10000030b909000c5040d044148554025150341000c48001a03c0b0016290010306056064004100b0045e48078044e00c0d50411000c1c140c400000d1070b0062001ca056800400e0300701009820f044140625640814081e10b0074800a40c1e00141c1810720b0500490a010380c003500100840746a029001560010820342500801d10540c031030032541403604019000f4240f901041d43d035603000d19800300c0c1102000909003000c14031101e4034a0540d846490304070041c0302d5040d415506010400903140403448600140c2050606800a9076803400c204079664501403036076001002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 118929892 1250 118928642 118928707
    0x50906070f050c0601050f06090310060303030e070e06090727030605071d100c080703090801050a0606021c140408013903051f0e07080604020f0a03090c0b0301060203 73
    0x80e011004a5211304407042075691f60f692044010015609008080c1410740600c2441a40c0c00d10020540010046038040c0d00c041008083e4040a02d840f20014080c6103050b10010f000f16070203090030245207601178003528088458207059107038101e4080d060901c400700c00710f5441c000d00900c00c480c8580354105000d424000400500100c54440322000c0215243c854421101c1d9038407254040d9403c1400d03590b2100500e41d0f504414a405000c4d51214014101190310306000100c0381c80303c80c45540103807410343e0010240d84038160400c1c80e600d02100300c110200145003658442308040351004c0d1000d4850000041404015083d1640b0030101000c9580c0310071b81c20000025421150740c5215450710028076003c50b03540d840005004115074040b86032441685a5000000c0d02c803503242c2228007903025683c0e03581c0151a104204000d074040e64414584c440d004004504480c0e0281c0d01400341d15100344001184280c0d500040d0205070400d921200140c1c00006481d8104520310b80500d8000304004117440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 118931142 1250 118929892 118929907
    0x150512040828020712050a05030a0c0c050f0a05090406060b0a2601050d0209070306050a171501030803161403040c0f060f0f03051f031202010b0d05060c0f070501050906070f05 77
    0x25640e403141c0c45000f20440021001e170091143c140070612800b5003000c11aa07480c0d8182000500415007000d058443d443c0e41c030703008582d5181a074444180283c000b0b1554030311505000401c16060310181040381d11590b1000001000d156110141c40c0d010710341d03181c0390400d0041d200bc4451020b42e18841c6091240110018132050f92250b0241424030f4041d681071580d96240c070015002091290442580941105000074049070303141d018003500c0d034850058603050031000f40d064200e04400e01000380340030424000141021003808803141d150036a86031028011100d0340004207158020758003660112031001c2c0c02e100403940f01c0e2038100100418a05140d401e850700d0001880d411034180140200768440b40401c540714414040411300c640b02c1212442e2043d540d28014100140060340030025500b020080c02c46883c0c01c01007106c00700d4000001c0c0c2219a00e0015500b43c0e5440017904492882050000a0100e2003d1180c00d2103051780780000c00d050704095002030103844000f540d000400c8800c01c10308 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 118932392 1250 118931142 118931147
    0x309050f0d08072901030b010f0b0c06010b0903150c04090e0a080d09030926010c020d0905040207021804080c2a010809030d090501020d150b0301150512040828 70
    0x224062034000c200b030b244d809550f01c20032608950220806041c40c803c8000031091146049019040f14241600122065a500300d161aa8010016500c40c03942014004000c2d0041c5100106245880101a18066000040f071980201025103850504140114081c003001003544100e0b410344007950014981e03051240d5030140c0510407121010084ca0f111baa007442054000c450010140c8180d0840600c1802d810b036144071009481c502480203582400c0c920b400c0c603400400d4014070401255240d441d414200018440a58800c038001c98002c0075846103040c806603400308843c01144920344960343c440203c00d64a00d0001e0b0004c2e910300714113801140541e040000498858819000e00301020380d0782c2d903540700354110b01074480031024180c2002c003400708000e41940204403480c04a0010001e142800542d01e08241c07082c02007c890700c0702000180a10703142e1010b020f0100000c0e01d406440d255420140c03040f01c0000355000c43d50603902040f6601010020b4100c42c100021130400607030010400c1000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 118933642 1250 118932392 118932397
    0x22080706030225020409510207170a05131a03040b04020d0203010f0b010311040302032d120a0818210705030403030206060a090c09090b06090405040309050f0d08 71
    0xc1c0d0101c240e4241e0f40e041191540d8203c075101d04d40001c0044590022481c4004804030080d0015075144001c401e05210080300300651200f280100012144014002003034800a501460040e03507585513000d54104250f900000500740000241c0d80d194840311030b050300b000400d4040d00603c1c2c60140c0440c1d011490401c03441070383d9000342c000c80420002d490358000304002c10803000c0080d416500340004801c07180710350317082a601e101e001c0e6810072002112401490503401103000003035054002c0c1f544180440400d0494504265500032a11010803882c070300c41c0e1500842d03012418904d24040340c0c48102540104885620082c0160040c4141d4545203103582c448182c441c0000b001c1150800400d20600b00c42e003502c40d03083c0e01804503aa640d4036428041d507a00405c84105109000140011551240310b00420b902e00005459107941d150408441e103010342407100c0c03640d0b0419410f01c02d1714025074a40c0201030145000343c941d46191745c2400c0030b12840304480410240500c090041c41000544640c04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 118934892 1250 118933642 118933687
    0xc0901081912050705010c030b0f010c021f09210c0905130201080a0b18060301061203020a120e0d030e09090309060702060711060403050615090402011b050102220807060302 76
    0x540082c0445440c40030388980c040c2280c054440e40c42c1400c1c15403c540c041d403000d0b614640c211001c884079070b23007840115080021400300075084101c003a00400001c4405c080e440c0d24464034245005c1441d2120440c0382600800c40380c24984000c895600820310000c5199100a008182e80c140201d02e000d03021110710140070f002c001c0c100101c0d003000860f000c00540c04442154401040c002e001c006a00500001801c2030750300a1295192810014101840e10190703080161306402800c00003105448060251242d202c0c00003d11516140d150813655620411000c0075100b51034007070740394031664240b1148200007007524000340d0003080342d84c103181d490704250744003e541203032000e9540820386000d030810300c1c0503201c803500311001040201c1000000300c0c00314421002603c0045801e00c41d107003000403094054070046c1c00311f103c5803000304e4a400407940c600c401d00d004100161a000180341c0d088009440c00c591440002204401801140020b201e0a002403800e840c0070341c01e1181c54241481d08200807035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 118936142 1250 118934892 118934903
    0xc0a08091009140c060a120b040b100206040317060a09020c0a0c06080f0604020405090f04050a081902070504060605030610020a02031b0909060103050c0111010605120c09010819 78
    0x15032090081021201da00c2040e1010700003000c02e841c15501c80e10b201000e040040c02101621000c500b00342c81501d0030a019503407031503030007035100000c0c50040031910302c11a0019241c0c0c01d04070007038403041c056030000c40e59680100254074043c28010910950504503841941d20304060100340e0780c2d4802c1002c01e4568400c00140e0707410020411a00d0985200c0008240c80031254000464541140d00c06110b6101c4240c0342c005a984c9002b008102c0c804d0f0302400e9448078640020450002d00d031140c85078840e105030701315102401240c03190a03ca40004800c00e00341c401c0340303120403446a070501c0002c0c0145810341d018001c541c00c0c400042c1841c000180114001c412807841c01140ca8401c0100c180003540203800d17500c2c00c1e030700100e8100600c1281072209028030b1180010030214900000c69504a80c2c12501070440f0b60540d10044880440c0c030414000d041d0740f00d50010603d40e54114264401c4007400e00142902c143c1d00044c4201c001d4141d014000316001400c21a170384103208034510080e2544034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 118937392 1250 118936142 118936157
    0x509060c0a02071a040e1003150b010302070f11040c020102090a0303030902031f0501090e0d0903031407050105130b1014210d0e040f150e0408090319030f080c0a 71
    0x801c07403501e0b11681c130200c080454001c0c00055102d010700180252400c11340ca91800f0f41d12541400308220b0381d0700c001840ca290703114444402c1e0307681d90b0003060b09210500d0b015290050702d40b40c03c101a4018441521100186076001c806031810384211340e031030711540c0000e604184000001650400707252101405254039125501e00b1981e0520005542d90074401d40400300d030801002d16801400c09005129019103041807660788240002215414a4445c3d550103600c2130a5990468069043c004801c124060601c40300700000c8003070060f1881018403516180c840340050404580000c0080c21010b41040309c00802d21280d01c1c104041d40c40c448055230302c403c411140300886101c4414840550805004454400c2d51080d8406000c80d100c10089806201c2c2032034149000d02180c1c3c002c507480031500c550410401840c403500500c1c0790b01070300603041c450400c001c0102284c01c0c020340380441c00c8650b0040c14500c08140e000700b203103c1c194000349040051f9141400e40282c00c1d100d410380940911200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 118938642 1250 118937392 118937407
    0xf07031104020d060b0c0303040320061503010e0a0b04050c0a0815060303070f0b091027050111030405060124090b070c08010e031c0c0219060608010203070915030509060c 75
    0x21900208001c0c5004c0c40c00551b60055202400d0b101d0f0415038040740060380324661910140e540d440f42c0d640c1250044041c1040352030700755054020842c07051103150195214041524504030034007445c03084900072a4203042516151600f141011544018240305121801050010420000f038611502c0344901c841080d541b01c000000b03246000783d450080c08285884019010443d0403086a4014200303442202c5c5846140100c1d00c00b91000a848905078000d10381c00208a014004800c542d814050310000400070700500300290340e548210780580b0290711040040141860042c5110000603181d150005201c903990300080c815071081c4503400b04a0804030340e21003417001c500e40001c018420100200162548003441548a0700b00c5031150902120284443c51000a00d0017840c60300390450340a004807044800d03a0740842e500170b81d0140c8800b5980d00001c80e1800092004502800325915001c80042c0350003400c84918680710035046c109820801413020f5050300040c3c0c190080700ca0007880791aa101c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 118939892 1250 118938642 118938667
    0x60e03071a0a090e040f0b07081620010609020306031207080a0c02040b0301091235090f06010902040302040b1e010518060403060207110916031d1b030f0703110402 72
    0x109030700468030131140744091004128482500d065202c0c890189154140d6404200b0740d04c2c0841220100c0315100c6081c41110307100e129400714490559081c560042f0f02001001e42030840340039402c20390701254000709104161504000502e25018002281440c04203582c1d101085401862401010310980201c0340341196165000300c2d0300480301500800c0407040900300420840e590102d10004100010103128200038080305006502401d0410400705000701900c0d0000a04000d0a070181805148040111251700380681e0b070003000c1105d00562500c0c21801044112601818101d01c0360301c0044e4034101c81d0b5848040c2101442007401c1c0261180b042c442036028840964002070351000c6c0002e0084108007440d8060700034140a5506a50785030300a20610680307a2081d42c41842400c4401d41c0c41c61098400d030003140c0c055511002c040d11a01003540c01c6440c0c0150050810072030f00c0d001c2003060080c01d0801884e0316454000d0010410b003880d544074002410345e1480068005d80e0009071140601c2c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 118941142 1250 118939892 118939907
    0xb010b0708120c1c050106090b07020a170c031c02070e010303080708070e0a0b03190b0303030a020738150105040303030b061e070c0605040b120601020f03040f060e03071a0a 76
    0x80b5145101c1d4803213141c0250000090809028840201d0811900819040c914105582420394040c040e0884c060500c6058001660501c1911200340b007040d540103c00c0e141442414841b4502c18044811528110300107401e003035042d041307629013403d150010008681d20107031480d0021064140000b00b525244d4040300c0741c0503640c00703031900510b124000041c0844084010343c420b110f1034400c1b030a51401511b26405450341015500e0341a80140b02292294890303500624111317109258065008081d01041c01c900d144105c82c40c2410302c1008650204100300340c3c002a031018205e140d280d464440320340041d201d402580009400c066584545007003507156103080f14038203854814911200740b545005200e480c0d000c0030b0100c46c09001c20034001200780c0990150707400c0e40e10300c1c681d0030f0902c000e0200f031151418009200c14114030559210340300ea00300038802072005d05496805100140e08044000e048407410500c498040da00001c0c00304210034001e4940d5240100c120b004550f212402c110440740704 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 118942392 1250 118941142 118941157
    0x6060504020313021207080f030417030a05091306030c060f0f1719020408010609020a1e0903020904050a02090c030618190c020f0303070203040e1f050f0126040b010b0708120c 77
    0x18450280448e041503000409441144c4050328a6000c0c2510500c803c0e841c2d007d614000804641c0600241c0440e25040c01c01800c1034400e40400a6019a02d44400c1248009070b0b11035001308146440040c005a40244d43c4003c0240504141140040744140030038083e00081c20402041540415080a2030203901150010411a002880342c2600e800030480254041d11005001c85c026071403114120064601306ea0f0100707a1a10f841f4007541c40e640a00c060503d00810445660003641d4070040107035141c11b20a030041300b0b01e050240e1645400700511280b4100c82c5c88003600c0c00300343c41c00c1000743c441c40c2e18968884180c003400800e034010075400580c980003807805602518000441006003940d40000540222848502c044901d0f40342c24400f2003d4044100b0f031a041c1ea07070003a6003401581052001812000018900702d00b410b8a00064401243e007500c06041c3d00e40c034072000b0302c03003403209040c240c41c050661004898035000d49603035009442c1c4210000d00c10082807040c0000c1c4401265000c4c0e5004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 118943642 1250 118942392 118942409
    0xa1505190b130203060d020307080706021615080606040302090a0903081302220212041109070801051011030f12010306050708060315060102010b180711060105010c0201080a0209060c070306060504020313021207 92
    0x192070303cad11030168407004240103031401031282c041c41d14441ca07031040d1004219400544000804041c506046801000042415400220410000005071210403005110344801000051520403501e401052414042d109c100041054460f5501607921030b074084caa080d1044040c2e98440302001ca62101030f0081c134500000c2d0f54409420882800a070484140010030308860031041541c903071100b59005202805295084030170005491841401040000590400c813001c4070305002044100000603032001c0d19541000c0e00e103100401c1004828003c05421008506220605140c4500481c1d500c9281384010b5200341b0751745020500c00d034000e6011150441c0c000d056000d483d0954003028111020648031040010000300980545034030205100b070694005942c1c004206146030011225030300c025190a104507420008009540c0e6100001d120707401c00400170300009861400c1500c1110440e40c0402d00503801001040060924489079041d8694110342140062000c05180c3c1d14000468002c02076 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 118944892 1250 118943642 118943653
    0x1d19050c0c06060907090b070c03080d06030c090b060a05130f030f150c0f0c060f020309010c17041e060b090a1a120d0e030a1505190b130203060d0203 66
    0x450384580c4000d201c01155201250203603225601800600034080b5000d00c001105640140070584e028070040a2090180f004905040d440b912015601d61040608412095440c00c0070008c1208400184008050300c3d64200110f035100c0000c1075043c4911a440010400d0000d86228801d503c00b05c1d0303401034580c1c40042c06e072058482c6031800c0041103405095856822080941c4266081401030081000701982c3c6c441171000582425945090a42411284603465124120091816101861207a400100041014034030010040c262028034281c964404075900c040002061000010104e0203210349502426100d5a040000091041c61581d507448401c035010300c0b42d81c0826402c5003100010b82d018060703c10404900700100011a4941d05c02c0319080000c1c036071089402400da1961030769000d0142e8050303e00c25074540f14042c1d051802100035030742c0d9400f84681c0c0307803151800c5030454030010810060014080300203600c40d0003101912101c107400100103580f68031041c0315800c0d0158050101e41 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 118946142 1250 118944892 118944901
    0x9020406090501031103041a1314030d0509030406141303061a191424030403020307050606010c030c0212010609090c030501050c0a090312050f070803061302041d1905 73
    0x1c104000380d1241d82d00282c10f10018601c075109290442c0d01032648280c0c012021803801c000464116801002e900b81501d4440d0f8941c00b113840300d511070412100000c013031551100d00601c0c560803a44c01400c03a142a03841071000b4800707260002c030312a0100300070380080e50700c0b00c41c0c03110b11402c80425900024401410301720869521003800740300707842c14042100c0203c01607280c048542001c0c1c0c102c0c41402c04080302d0340b43c80d445070b06005100155000c0030000294010001140c420003e40c01030310300318010380c0000380c104103020007405400d0b00f2110034a80b800d203074121034500801e90014117002a01c50b8450044092880809501c00c000420003000c0a125202960608200482c4c2903c400e840c00d50800c4c0015249510100446059511030b8139803050440c2180c80d11039030503103802594011302c6070030085003144601600140c0042846080301d5a900e2520a091040c2c2c1801605010855801800207005050790380c080300803a030820710750b141c0c3c2c60340d61107480a001001c8540d5140201d40343ca420710 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 118947392 1250 118946142 118946147
    0x1d060a0510063f0c050c0a0204090206090a0308070b06090705030a0f0621030206090313031401091a091c050f090102010b041d15040c06050f09030708010b280b0c0709020406 76
    0x79003000c1c10b4004000644001c40117461912a5140c00b0005800c145c00440062078594040b080d214006407025003014224030101d510b0412035081170f2810031010400601f0070940c1d01000340d0010050f00e0000c8a401c2c000d402501c68007010b02070003030a80d200e000305c08031881705074049001462034a560102801c2c04544a46580180c0c0c8004d40050184900061307900100104440240344207104481d015840e41c0c4a03a160950030b550041095504c441000020a43c200d03545550a10301c860500480e01340405810b00d803a0849690b42109958010f074443e0303054100081d102e8000d552401240ea491905004070300604c0329221496109260005043d002210050100d4601d140310040301d40d40d0400009118103a40110350040c60501c0d460000c2c03000390300c82c00190240b1800e56401509010300480082e0900c2d85c990464030240e9521080c0309a0391621480640c148000c40018012946c030b4140b44044900c0c40303004050030031000040c1e01b000c82c042001200c005140909046480340d4a88200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 118948642 1250 118947392 118947497
    0x105070c0b2a030304020d42090b1909050601031b0803070c09110906030405061512150601020a0b0103080a0f09061d01121d060a051006 60
    0x7042e6500d0a00003190416411104000103440d01c10801035040d80d46a0f0700b088880440b21100701e0322440a60031100c43c000d0403d02c84003a00c070700f0400c00001c950208800b1381860b0b1840050041541c2800040c0d0007160076000b40540043d21a00e100003820404501d500203090400740050442c46500000810b0224000c11609030498605082d800c0c5581c6003111030f81d034010910090000180d0110400400005500083c1030300071845000d810100410002074072a042180e0649450b00300e90108030f859190a00c10742c0b0100001c403030030f0100064880301e040d074502040156000380c01402000c01d5840c1c3c020801a0300303ca5100b0348101c0c15603128a400902900040d0740c2e00c2c0810b0395030070b017800c0141c0902500c006031840b42d580e60490030310914002c0f10aaa40401050501516951f0100d00801070700811a4142c8016010400d029a00510751300e001e1000f00004101881d10040c045486c20305011401100e120b8509128005c00c0c400150240591186042868010050300d441d42e00c0a034414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 118949892 1250 118948642 118948657
    0x1150303120f18140c0a0303090e190e0a05070519030b1503061e1315051b0a0203090a050a0b0723030d0506120a050d030f0b030a0c03021e01050d0504020105070c0b 72
    0x90341c410108490030306c105400b45020041c04102c0550007403080c1c0c9100d1241c603902140910300d2000704403224030304000f120520320114a0b183c100c071000348180641040000700404042d694403d5000d8540d0107072000b0312560100500c522121404500140300ca06040c000c0d01c0c2e03004003584d6072410400c4091801c699684044944542c0ca140010322102c0ba4100d107030007660300414082021101041c008004000013040035040161060b1000e00d070060000182c00101d100b50011940e40602108020040846500091046140b27040a0020b110f84c0d50a940c1560390100180100b0300200e811034002039a51495044503201c0130030b860340d0154540e000b0034000c0344160750580600c010040816100e61042c0c102412681c400d01c01840424829400180071118400e40010340380009800203080600c00a01610404662030080c019890005038041c2d00c500d400c0300300d050902130307000081c040c1d000b01d004500038166034200240559000e181250102d80d4040701c20005541c844130040080c0c2c110b40e5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 118951142 1250 118949892 118949933
    0xa030f1b03091e081227060106110609030d090302030d050a020a0f0f1d060909010905061219030e0d083103050a02061b0f060105010201150303120f18 66
    0x8407515200c00c0f0380840612101e40102c0c8003407420808502211150740c019140b660014032110401c58500118075000d40009407940140205501d03104004049030440003020046030803070303014440500c00000c2218003031804600003087c80452810107a056025040305815035908243c10072111102c00c0d07000300000d90030358803600720b843e4090400700c5000c5008103901c40410081070288081c04141ca61070700000c44010840c91516540c00c020480c034620a07801542d09580f03038000c3c0021842c02c007208181e100d400c0001400c000746210003042140d00b04c02c00103800d002020180c58101c0c1c803260488407180e904a03105a6850b03c1c000d401c4c07648079810340c031048011807100000c00401498180f03003070200c90700007008124140b41d075020020203501080c0a80c1d500d58070052100450001803251404030fa00e000c000e000198541000a801e4619403d41c400c14015824020700010350895a80c00045010760000900e240c0c2d0a4030802c02030401c41800c03880e40c041c0035085403c100c03000500007000007a55 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 118952392 1250 118951142 118951163
    0x30703110301050c0913091e030e0307120b010b03060f0a0305060613022b0b030706020d120c08010603020a140c071403010902010e0108040804050415090e0609030a030f1b0309 77
    0x1c84c1102107401030030341d000e074085601010b41310001540d803ca50005070240c0000303e8142210070f102e02e01c2c40410786d011000b2034907200d00f2034040e1600707205c540000c140f2440c81d491041856a110003050a0501a50041d402e0110108490b52a610144a10100082d1801c44080e803a030405a545500c2100c0c05440303081d800303010300220310982c002d649180c5104400455003401060781c032250704100909040b007c641c0d0740864101c5030b03030800500c0002c04440d0003800c0c0003515810001d190743d02c9a0358054055003081e981c2402a030303100750414111402da16005031202a041e000f112031000c00d004046450030302043c3c521b21044086004001c4808280d01c5c04580e000030400d15080e81c1220388041e0200e021040d6402040d4012036020350f0003486a61403a203031030b855030700090456000d414070700f00c041c0100c00184500700103031141c9075420a0103002810103203040740065590303100c2c00d5610300416417100e000e501e0440e070320782004c1041c010804403200c2c01503031100300a0040c8a40d002c10354141401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 118953642 1250 118952392 118952401
    0xf030605030d0963020702011b080702010c03050705010e030301151704060b1201063c030201050c030f040b130609030c0603051b0d090c05030f03070611040503070311030105 76
    0x501c0304c0898003003804003012144004810143d450106000310190340d9a00e1a100d40c0104090300402ca50000a40400688a40e0179000041035021004420000001c500e034845022a0504003036550213542440c0c000c60400e0b491808547c0380c06200c0c070082c40c0790300382075695551900100241d4141c601d04003480b0380c60b00a0400c05c0310a10341c4401415081c4041c240030501086d07007a04a90020704001d4034000386400680841401c44281d81d003d60030908215010700c020f030501c044225100c00d04102c024400b0b2041c9410700c50b401c1440d200013410301c40700154864081d80188107507940341d6400650681c4640d80c452030741d001580050450010a241c40300e0104601d4052081c0005484d00029554251424040c05900600e4060624040e845090044000c81d08a10005240030140300c00c02140c03080c01e0307107000f040d085003a03000b80d4400d4003d071140733452416002041d07a801c0790b00301001051002c80130091841740d105030380101d90180910300c00841800350107090841040360950080080703030385 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 118954892 1250 118953642 118953689
    0x228080603121e04080d052a0c09150d050105010e0901020f0a0503040206090a031b08060c1e0702030601080708060a0203150d050f03031008061503030a0f030605030d09 74
    0x191802c00008400c400e00c11034140f400e543d100c09003c11540620700349000e40781c00b0098503040c40200300c2e50000b4800103a894258041c0030142c2e030205001d004402104ea1145d04145e182e68009584e180101c9100c80000d0401c003801034090701583d0045c0034030f040c031529801c10314064182405100070300311000c00414000340c014404c403126006078103044d81c141050064215010360001d00240e81c0604144100c1d060366480400007002540300c0c0100c0b05514044e11a0391a02d0b0a00d036020b619203030000d2081014200302d604c1102d81e21a10345c400c4180303203a084841e1401d18040c442c4081e40612030440081045540014070303c0643c0e01c150111003007035031041c0ca50402c0c0d10007203840e48200030340c1004041c2c05040503001d42900a108609584022111442091450700100d445550100d0017140402140780300f481a030340c0011100c1c2a80c2501c00b03036a404030743e480c42140a40f204001c9840140f4400b00d100c2d0b80b0200142c034008007628a603200a01008103003902e58001c40c0240700c0d21120310f50507002e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 118956142 1250 118954892 118954903
    0x20c07050315090304031b0506040b0306040507090501020c1302070b010303021513034407090602030301030206120c070507080319030e070e07030e07030507060807091d07030228080603 81
    0x80d0006519013400e5555034845000701800101d003114000c0e00125240d59200e024000be000c14040458030f900d005c00801c001c3d200f01a1806050004511040c031160b41d01103a92410004283c80081d500d2103583c000ea4000c2c401d240019000c0c10540002004250307001c03c01c00e03000c011800f83c280c80ca89a941000b1f21084544400030b005c07414107401201d0800d40150421230401440c5080d5401c40714800084000c846c0c002c401c81e40c4100140d080140c0d0b680c000c81c2e00317005041703544000c604660540e40440c1207880740d05203020b400c1441c030001540082c034131021101d120341d02c44142d403032156444848541d65004004500307113006840c0c10b07000e40107102e48035592351110800000c21990b4078186480780d929001800301010907403552032114914a04103c00c8000b0b520550061074038a1030f01d940103103451009440d8100b0080d51503010041000502c80890a80302141d045d2206034841400590091082c100042c1c2030410503a07060300c1e0342c600840709542038041d41d01d40c8840350396800100354858 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 118957392 1250 118956142 118956151
    0x210201021204290c03031f1203082406070302030a0905092202010909140115020607021002210f0a050f06031b04061a0705011a060703120f020c07050315 67
    0x2e03d03004907100b041c03142018010500080710307216035240694100c1094203680c02280ea2400203a07001c1401102c1e50011116240103103076000c903032688003c0903a00180805005009265240302c900c0301d0000c4040040d61340900d006005040c2541c8100c5031038041d4032500070151440120b104d001d000a200c2c10842145849090031840d1120402c84515640d80040311034a41039042265414010601c9a01c52103203030070744002e080c280c9409602d03014288140040040b03520086401903800c2c040c01580019541403550b00854000d40c940e603241c0d014034080c0d00c0c40580302c01e08220442c01e000b01e15400403812800360b941e5040c00e10066a82a00034110306005a440a030107900181b41320000391000404003054040050010031400ea41c0d50402c0c15a040840c2010360204000a000007000780904c5000045600c141e00a41d0001062002030080d02921901800340000c142c4c20059441c240c0e400740382c08624004045480c2c40c13003200201ea581c0e106001e494000d21903916029241e029100c400c034481c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 118958642 1250 118957392 118957409
    0xc080108011b120f1d071707031205070311100203011d04030f18030f060e0d0206040803010e04060209040507021e210c120c0c0f180c0306010207210201021204 70
    0x94612420b8a032004040d152030940700300ea41c0c5c1d407008200d1220040700444084100008104580c24031040300200a14071034000102e03030001104200040700c3c3c0c0728a1003401b2660030881e8543c00ca40c101514009403e07600400d03540140061021050307080d902841c16140c80c1040d007443c5c0310201140c00e052650030f407409804282c1800401c644a0300c161a81048080710500c4060469540d5581d00003540402d80c0444007561200b8405888140070071800c00c051100d0b1008001c42d05254944003e1480103008440c1e0000b0044005000d00c4025011101500b8024004001519200c10000d440e2502d603200d10340311042030100c0031416040060250344040e03641b082e400b101204403910200c903910682614146018034008190250b6503400a000c24514004c043c200c0b2002040070009407102c1142041e129580300324003c4041c46003540301c542d00c444d20b00c5445503a40c89110040c0e14240c2c1540c001c1801201d03047c409614207030340c4500e18001c14400c0e000c91740540344070343c03002c0264011030045110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 118959892 1250 118958642 118958657
    0x325050711040e0f06011d060904080301030b070507020d03020f0d030b0603060d05070e1009050f0f0609091606031a060a14030a090f0602130602010b030c150408010c080108011b 78
    0x1186072a07400488203400803c100d90610050781811400c1c40c40c01da2001030b01d10a8190300d0044181903458881e80200100d0380b0483da40303402c2c0c0d01c24040c0e00041c0030181040c4003070f0300050341c52809074045480c0c02c0e030020540300300e070b40c0c0701e140096803039001c805449094090445123a4046009001d043c84c0d00000038452421640c6050070310045414000381a5a1403151a400080300440626054000c1036a8034800c914503007040010b1090b40e6018004000340312080301080004d0090b00d82c0c054001c1822503644c0250b03111214141e29110035540400341c422000c040020f22740f609036009400c07429410305070920424102080207a40c1c0110018140860b401e140d0701c00041a0841c0150340c05202d1010000b004400d40d200c0c4c030540c0d000c1e00d1040b5440c07179001440321401c0c02c16a030700030010451480244a0015140082074031090b11408442c000d000044030b956042d6802003ea40c05060000000c120f0340440080080810744284202070702135180c408a02c0320604d103080d07412003108043d02c8400c1c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 118961142 1250 118959892 118959923
    0x6070c14150c0714040906020f04090b0d120c020315010603020904140601091a0f0316020105091f09050304050303071101260106050a0507060e030301051003090c06050c0a0803250507 80
    0x16042c00c05091381e81d0040e03903140c0c114005009440505040003070704010a844904081244044840b12200070340300d5400c2d40252400501600415800821240350001c60102944042803904003102240514511004004038002e40d15030701410413101c044074140004910100210240c42e0152102400103907041d1050160106e86081c45080302c444044403403400141c0100c214003608140d031002041601c00140042d01d540c240905034112070311034003403c4e49407020320040004140071030071058495169011141803010500540340281405810f4941d00c4215203881e83c0304208000c0801d0110301000e602000759814038901c1e042e02c84027103660b00309a900b0200700352016005203080b001004400c00c016170014205014208842001c68002c50703c9504000c10007400d502c60348800820145000c3c0c40101082008d04600c00320348060a1440d40c40410704c40407810b12100c2c42010300380100007c2400b15a080c030000a04802d0021003449101c50100042103446209540024101405d0072500c0d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 118962392 1250 118961142 118961159
    0x121a060c0f010507021501060201020a120c12060e0435070f050d08010317070822031b140909030d1d0a05030904060501030c020a06050606070c14150c07 67
    0xc01801884030219403400340020040c50941d030044810000680003034415070810030701e4421450152800740025030400100c000000c10400320002003003060354541603074540d4940201501042c00446220601c802070b2a00703010b8010110640d422224002d009010b42241625941700c1c2e0300b004907401c50894240c200303c0341001c01e600f20f500d05440c42e580c081c5140000503402c0182c080c8240c4d80d43c588841643c0346080021850321050084075003e03000b00704a00004c2e1040c42141c0000b003007801d034420807103001441e0400300b00641d00000c20300500350f015103d034038040c041e9000494510000a40c2075440d41d40900c060186e041d20104199070040c066007081c0c0c0415003180c000707402e01d5266190719040a00c100c1d03182122040c8241c469810008000046040501030b44c4007130b03e4282800c0c400036091076030003547c0e40481030b80030300702540e030310045001d959504044400391504400e616031803e484d5020142d60700c85101c4070b14465920000018411540d1809481c40c01380000f0181c00d50500e024110f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 118963642 1250 118962392 118962397
    0x11d0a0309060e03100e0105240105090103020318060c07050f010908160204090203120904060f03240209030a03050904150b0406050d09020301050a09120212180d0c03080a121a06 78
    0x28680c1c1030081000402d100040c922035801c1c010811b20000c60503060841c480841d650b01d4240101030301c8908810b000e010f98001e41220340f144000c0c83c0c0140c4d43d903554020b59000707881010f070900c110700980d000c2c0b101414104001e40f410303e000341c01b95041c0d0310b8010b2a581c01c80d0403541c0003c048507400c1c070014014070020080c0400650000c0e01c0461810500d0340045e007003c02981b00d00d8809000840c00c00150b040a101c1c05000d40a61090340c140039055880b00140301c03400c81c540301c13000030140a03014500380381c94040d40c030500c8020742103170300c11059468064903981100c00c002d4040d500d80500d441560307102c02102c50465551000d8185401d09020044640c2d5001e442c0200207a038481c419000103840c04d00c1254490900c002000031040c90b10b152198041d898034030f68008641c42019240c0d200449030b002c41d10032144116968013000007400119940d0700c0814005030840c0c049900020078440e03440000c20982c1344943d41c00c044c207100c654002d03040b01c0040c10740e000d20459280d04c04801c1d0030440300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 118964892 1250 118963642 118963667
    0x3040e010303030e010e0604140f010504050a0f050a12080f0a05060a06050a0e06040305070e070203070b0105091503030307170c16020d0204060503190506130b07210c02011d0a030906 80
    0x2184100b000c8421521f40300090b14125503000c6000b802882e4281c0c03e100f0a0480486400284400c0c1056101d003a03a50060700405080301c4a5001801c1c100901000880700031a44001c4403d49032031781203c0a45194011290003940043d40301c0040d012011038032486e0300c280c200502e002d14050405808407075540045052605000d05c0026400b00c81da038841c0a000114407902c0101041403c0c800c1450b076404e0040d08100640d8414410300c0001281c41140c0c0341550340075a001030b080d0b51148558009445248022174150000005001206511415040c410840c0601041541d00d0700010707aa03080c4290b0302c011410049070507500e001854030980f120140303800244007090741038907000003e00b00b4111401a80c00c561120304942c080120a00180b98030079000c400000703103800d20f41c903084400c4400500c00420010100c04401780c01d01240f0803001c824100110820041d03c5440e80a402014000d849030050b640b031031500160201c0000d40d41d0341842e89650f852130114a050700a40e00a8800300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 118966142 1250 118964892 118964921
    0x703090f060507110f1c050708160507030209040b07030e0d020a140705060f040609060302120a09060905010507030c0905150a0807050717070201180509060f0a050a0f060206070203040e01030303 85
    0x13800711500c0104011000c00d00307400c200075201000d02007034045410000e2568400c1484402d000f500d02003449901600c810782d00031440d050300c42503a0300d446800c0c86ca0746c0c2c10085d444207111040c00280b08d550100c1b28468605a101000340c0c0c0d28132000c1a0769800c0102910700180d1100101a0001d20b001404501204a44040380c0110386c540c0c0c00142182c0100808041c100e80114041007403503401b140800081a2504085207411040c40101c1000314005180c1e0000c0d6460314080f004011075135112050454204000f0031080c100803500401030080820060001404a50003240c64902003214048080103410120b203040f101e0401a5044000102800f090150a000140210700315081d11014841c411040e1507541525100261030b50003072102100036280f0041040c40207071604003225800a80448090500c44118000220100c00b07c1e00120380052024000140c03502060100905640003602645e441b07548160782203130b5138003e134401c00e03984a04000040010078040d6011132030221020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 118967392 1250 118966142 118966157
    0x5090a0503060702030a1209110d021810180b0901210c030c05091f06050d06082b0804032123060a060f0507021c05100905060703090f060507 62
    0x140300203410000126003500144c5c0002644a01043e0701c00b070068440b10a489017000303803100d6a2540700c050081c1d0b00c115801030008074000340c1550350303a511400004007901c107200031915102d101000000601d00c00c11980001d540344000c003201242c040d541d54180040c0624825a103020b004c044000802d1071200d0345c195408076a48042447c507480c00d4042d6020b0b0110b051550315040c14406c01d000c00401c180e8a4101811901e2056001015580c0860b14549807141d15000d40d101c2d444010002030b44031040070300c10a840d4009034214001610b0089204501031160444045e0042c0c1d1081c204480040000d2101e030150107050000c061010b0044245490005160052684140c8a40e16002900004841c4101049040d02d0b0002150011303201e41d01e03003da602d488002d000b8060340502140244640207225103042d81d10000c88045481c20340001c1250b411116006030780c0c0c001d00f03480109581a010b41c400154101d40a400780081050740200301c40031030600f58860074010310b00036101c0d40810200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 118968642 1250 118967392 118967399
    0xd080306010e060c070501020727110408030a02101404080307030207060f020d050f07230706020d1b1b0c15180b120a0501120f0f05031201050f0315060105090a 70
    0x3558050010388002400920380c5e0350400c0006494000751344d102e070502c4602d00011440200001600301c9201c51550030225060184c141c2000c01802950003000c81e6100c04100b01c3d5646074000385c40d80e000c19074500e003049859141c0e0b4041c208150200c03805003001000700007092090340719600600125001d0900000d0750010420040d050f80d00141f01c890000343c0f100140100c202c42500303c990410f10303904041480c01c0005002c40c1200c0da60100380000ba803c04100c0005002040d0100c4151494130401081a4590b0380f00120b0011514101080002c0c15141c1d4203003080055504920841c0d080013584101529180201c402c41500b007016004100030411710010304140d041801c070280040c8104507440f40f03010700f400c40250b9030050031100018145001001600300e2124600c55680d0042c10041c0f40d4045802c0480200586100013000c5100005605190b00c00c54002d15050310421108080130213520f008241c3d0343d58070b41540441041080f004903a59600443c0100a00c803005024920190f66 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 118969892 1250 118968642 118968649
    0x30f02010915020721120c0e030a08040609090605032802030a0503030910180b04050a050f0706030b06070b010902090f030111030a06270911030307060b090a0b0d080306010e 76
    0x1403502d003901a140c0208244080000640d51007100c00010044541d002d01001401070100e0b9456241c001c11035501d45222103407611400e03401011002c003408a850b499401d14002185d035100307208500c0010380322403012486100340d006800840307800400901d054080365903c0083c0c80300042c407142505107115244001a20207225140c0043c1c0580061034503442c24400c41070070880c60a600c22601071400d40e05007401c55240590b401c04070341080d4500c0b056511031403c14600607298030301400500c03841000c0e6984d0b00c0d00107086000c0d69896581032203402004803d03c03c15005030900148800d44c088018828000c095010f000c045200506290f0003090f001d02180c02c480209a03040260306001041000d1020705004840050440d0b00c90305003502c0d2611032130050f20f0043d5a076030b03010644850001040c0108080e00f400c8125004003035075a1502c0d146000c8000f000c00a48040c002c1c2c50241c0001c0303d00c100e5201c1e10810319006842451401c04580c1c0d00c04090340010410f234140107812811300d00988 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 118971142 1250 118969892 118969913
    0x3090609060903090f0803070b1806010e041205070803130c05040606020304090b0f06030c0901090e0705120702060903040303051b0105070c05070929030a02090a0c03110301080703030f020109 84
    0x1d014100002c1c403a0641e00b80244040516008042c20303c44000041000b09800030131607501c0c40c0c20185540311354440301520700060b06008180d103002d2041c40d0000c15042010120389003d1880b80700b82c1c07040c13464071200c01d440d00e004880b4041d04070746040c070010385554003200d90318840305d129042603a0743d0b40d1680c000030112110b41d003010f0010791002c502440009602d00c0b6601c50010201c520003144016440010b50b903220082c81c0c4560301a001c2010100343e4000c2984001405000e0325140d01481c240b907000f4007580051402824104440000c01d0b034450011803a24002c0d10080e0203940303001e0030b588090341e665024a0303801060b0300d1500d0050302820028411390b8000c90142d42c0f0000000c070706050151511800b6080202d207607140002c401c0764100540c40074050107003111860340d240725800e00020b0400c8520031019400001810400550008030751180d00e80d407541e0b1300c0030031042c0f205240f0440103010900401c0d0b416840701c1400c0c0b012900039002194010780d107100200307101c1c0c2183d4403091141c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 118972392 1250 118971142 118971161
    0x15090d0e03010c320a021b18160509030d0509030d080906070e0a0f0915060e03030306010e04020c060c03060103060801050105061204210f0e0d0308040b06150c07030203150103031e030906 82
    0x5801147d80c4450346010302e0541040c4400031100220425000e0350001034110010b0051892400340c00708000c45a070250040d2181208000c0548481c4404150080c18640c04180392612034090a140122124011100c0501030350f0790600230b00095803002c20540b0300103c580b40f015400305400c0320010701c003400741c441030024001e07010002c0b81c1c50850171280d1046c51580d402c00000d10070b0740108048103450001c241c1e80e004000346440b064028440d40400c00034401e5491000060283d50200700c9100122401540190000c0e2b0301040580e41c1c90054034201c0c1d00038021994000c07010415000360210900c0450b4100780200e21407021491850f85d900c1d00d4004007107174007001c03e842d080c4e1143c1042d007100895400306000d07101c0b00c0355a8072030354004003018001000101406000b00c086103950311441444080380001140c442e036207661821006540301a0780c80124803c0c4200c1c92807114080c080e07000b650480c0e500d40c4410040e81c1e0000f540f00c90540e0b0090400c800c1540d12001c1002081041c0140c0208 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 118973642 1250 118972392 118972397
    0x515090f0109120f0908060c03100504022d0f0d0b18010305060403120605011215050d08030609070207060807030216080d05040c091b05070515090d0e03010c320a 71
    0xc0c3d205400c05444244560742c10402c1c42415141003001c200b000c98080e5120840c841125500e5841d220b03580f9050407241c0080340c00030b20100300140c495815549a00241449001416070314130254000103261084124150000900380003014041c44903420140745060001e048002c00c500c031001c13451a03568241d0040c4c589a12510500090541090440b240740c10100700a012490901c80040d1488041d42e840200c41991800c03074080c2d01502c0c02c021000f13040003e120507036601203810940c84a4005462480c450040c50000c22940703400025003401f103d1070780d201c904107a501e05009900940007001c0056104202c0c0f1a410001a0841c0050411800000c00001d19041c20709203814000c0943d04034407509842c0402505800c4c40720720340705c4441c480d0341c6001981c86840c2e1500905100c4040f0041c819084c80000703000340c4810110700c05012103810340d02c010b103e000d650b0030035080c0c0390200c80705404a100e40c0b01031358142c0070b544080d11100400059040e030300b0b42401c00301c1409038000c0d240d4100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 118974892 1250 118973642 118973663
    0x4201030605090309090403050903010f023405060f10090f0c02190506010b0d060e0103061d07050d060209030a050a061a01180b09010903060609020d0b09040515090f0109 74
    0x3000302034420329410074a81d1005504200c141e01c00310300c4106000d0000f070305102010454060b16a42500000c90313002203000c05540b14100b080f80d0454013040003e4940c00c940da40c3e032070000b20906203031208008a40000042845444011008055402c00f41000d600599040804590701040d030060400c07607020172030700203900d004090000b420180288500c4072100c00b0048000302084c000600141940c0710a620740d0364501c0c001d0b404800070207a0741d00000130b00146500000521985501441d180000d0b104c015100c0c0e03454858058444501d80505a44101c06841640120344903074080d00010001070100ca103040841d4440d00c0c94200091800c585517600ca4481d500c05d00c2100b80c0024462400307092031480c0c100640c03024001414240901008a1070201d48024144e02c250300d80c5005680040c030400580d501d032a84180654069000b2517542c604044000c012410f240d0001885960020040c00080c6489001c1d0448008043c2c20040b0034402d4201da0300a41400b846107060052103004940d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 118976142 1250 118974892 118974899
    0xa0b2403040308090102070309090c0507060e03040305160b04090f0e011a0a0801020a050d3207090b16150f230601050901090303260702160503030a024201 68
    0x100003c1c0020075131511039006000e40000681c2054040c0e0944e1a0404081180307100c0300e1084810b80103114001d00003078200240086404c4020004105490181c0140d4150744440c0300a030440e0583c0384a40382e42c8000820007040400007591010301604800740380810f1035034112a843d03081d00d8034103c0000c0382c0030400c400810b1074036100c4507000050980030000e500f0f00600d464058114055081d4a204d1030340c5038030010704808080842e51001c0001c1a07400700d1090200504607424840480340c1102252080002007294071606080d107990b04218030704041c4108440d55a060b502405480c2c5858080c1c0f40c5001c0c041c1002079000e00703034102ca580c00041569401911481c0405e20005d44614140b24041140703000d40d0368800d4100090300d4050804003010183e403402c14a0b600d880a101101c5020140c007840600703030b40460350303e1240c0380c40c5015001c1e094903081015102d01c034848081d805031b8030000c0c10702c04d8150200820007041425141d076001380e4410724071401501420f02183c004200030304e030050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 118977392 1250 118976142 118976147
    0x7020309030d0f0c110402160b07030f050103020616030e04020a030b010801050a060c02190305030d060815070801170f0703030f140c060402011202160605180111030a0b24030403 78
    0xb06407400d22440e241e00b00100c8204080d01d8182c0e100e4001c1c1030011046003900d22501d039a011503042440302d02600141c020715080200c0c44460580383c0c1400242012120303000b4602500072a07044c5d03074005124500d002c03c81d00c009003842001c080110306101340040040e050f90340b1840600554072294501082c0c040342c200c0010804101600701607c00d83c4105e0091141d10f60168084d00b40782d5040e2130402c103c58040c030010540303440e1039200400901c40094403250305c910f40d4014408858081003201d0540243d00020240d8641c02c41701e850005040c00700400a0881c0c4080300080c643d0540e050b1141d140320152024103004d074541040e80810040c440e01c0340d4007030344099409032403640c2420680c00d1869054000f62901400f40010741040302a5090811024040c4e044407813580c075207030740c03c11116110308c1c021020301012140b40d00c03200ba0000d001c154114042c0540011952030210043c81d50381c6440300c8200070716a0000340d940144904c103043c40c0d040008440c440501045128103500e0f8a02850300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 118978642 1250 118977392 118977403
    0x1060503061813060c2c04060b030f061c0c1d0c0304050c06030601050405040905070e0a0b032a0a060201020c0606010c02011e1209200a08190204060e0702030903 71
    0x10452030b02e00c1c1070100040d0b6545031207030020440c1c0c40340e030124800e48881000c4441c0701c03042e40d9000601c10780d40e00707400013036110105800c5000000d072010700034284e990440003141d0004407034265004050400140b8586450100c4003400110701816041e444038a4440c1586034105400c10283d50040510b82860340ca072208915030320410070010b0900e94901036a5042e100c11541040354000c850100104150768011025034010704170260080180621030300b40641d81e000300344203200c10003900c000480c419060030300031401c07140005001001501303030074552000d27240c001c1c10016104400b0000c115040ea52280c080e00000d00140d8005a11842101030b22410403030302400103414440480c403001e00503600807102c03540d030b018000544c09100c0c2e83c2c00c0090702c60f018403074143c8140600e003c0429041000c119039022111961002c104031010807502030002c070940038003a4150b40c0e400001140403e450442807402c41d01e101610114920303660303003c0034910310029900740016130004601c2180e00d0408000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 118979892 1250 118978642 118978669
    0x4060b03070501050d0e030d050705070606060504061b05010e03030c0c06070206040213020d0915090b01090501050303070f030e0a0e040b0a050c1e0c0703030302090a0f03050d0c020f090106050306 86
    0x940400d6242c500003070075030312806440c0b002560302d44505160b111414000d03a01c440701d081070240118544800c0040841e802020304480491800c4e0700424820303c2a4244d900b62000e90711641480b000054503850752441c4102c5c1100d09649072518149050001c0c4007031070095901034941034540020360300307603401c0ac800100300b04110340c052000c101c003503a17400403180e0544080d5007005139508801000c05001d010a55005445201040140000c00c0455800702655034000c1c0594a016600d511240d030585800307200e40303549603105000724030104110f4102ea082c5203200c0d007800c840e80758005020941d03001682d4882140300716042c08000500103130000316940142c040c002007110b0b1410036000c0325113014600d4603440300030000b1640c00490400004a5084801280c11544030b15a40c1c40d0003402303503106407109405100da0030f5000811140e80d10f001002d03641e025010303000300c0444400490b94000503000580e071000c110310010285480350140140684442e80e10301d5507912300f4505000008c051182c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 118981142 1250 118979892 118979899
    0x90803090d0309050307021002190b09010f0e070614280f020f0601170a0606091505060f0f07080f0309010506040e03091c03170906040309210f17070b04060b 69
    0x703c5640004030040110340c40301b94111001e40c1c00c0714070880100d01c0d24001540e901074007640c2030707003040900a40e038191500c5500850b00a1004100907141c0c10240c446002420180d9800080b00b80851070195400340e52000300c224103241030400700c600b502e400310382100003c00f40c00e102100b05401c079913002903980d03000111800100301c00410b00c0040c81d5540014804d45100380031180f070004035218140a150202c0e60082c40601410351a0104580240345480b42035940100d684c0002615041140039203a00095110f0300605010000c1c3d40400541c2c400340e0110b820600402000c6120b00f0380c4030185000d140381c071700009003526180050108441d03210065040f16403003407020038801c0c0d9824071104c0b03415040007204030803030006107010764111b001e02406000e401e44072030800c17480d4180011014416402907550001035a681d000040c01c0b00703440005200035101504001020070b020300710200c1c01c1c500ca207402c0280c0f003500340c0029074140c01000c4110f5400140105210a00c0f41e240500c205240044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 118982392 1250 118981142 118981151
    0x4050a0e011410051c05010806060d020109030b070c02041802030114060d08180a030302060f0f04080a030504020a051207031403030906130510090b0105010f1d1201060801090803090d03 81
    0xc030321a030603500c00040c94880d0010000021080340324400351003aa0480b00d8905046201c401403c0006c0c020034003c4103a64400e94000400340d1138090f61131400300d80c068590101080c1507440c0e00700c24841c000c20340401e104c0c0c80012040145c41c0e6106110403015004103c0801060030b104050a45841424141c00341d00300c0700500231207503541c58010100d0780c2d0100c68175680f540406451040d030081c01c43c3ca00d50040146200100341900801d0b61803007903803225603584269035914002d84011f8800e690242518000344060824503001e5445035402c240024803001e03c0361b0b52030b030014401c01449044c410b0380d500809010010400018882e90240e0300004c040c506501c0d000c0384080c3d44082c014006c001801810b80364000f4801c090180140e5100740139028400160a8240082030241c20b20030f20340001c908400803c10a44103035007501c5a0b030300500c0c0900000303020704100085c0c40000c0707041d880c15558507030000581d1403091040b074150030311900d911034403803911403941c608101900c0321400616041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 118983642 1250 118982392 118982399
    0xc030405010c0f0e01122301050108010b070b0402010c1401060b0c01110f0a030506130207050105070e0f1f030608030d0b0f011403010605070c0b03090a060b030a030e0405040303150b04050a0e01 85
    0x80003e203840400e0a280c01e000d41403090268002500d41da00d660b405444101a10040c500d0342c11021f10f05890081e00c480940e0b903641c540007038141c0f0502001030b080e00280d80c0400c0c01988900303107880249000321400040300c40500015801c4030301a03840001c02907400039013404054028002d0600141e000540c09007042074142ca50310682c0310f005e0f4440105662240055019520f00f14003408030200030b0b004544809039880c1450003407005070342c903c4c00f080d510b80d0300e01d04a1400081c40c00c11500044c3c9115000d4800740c00740c2e00e06110000c00340d0180354648001041d0a18108080c14403c080c0307460114030f8000350010301c0f0400103c0c8244504001c010008a4405850101202e0441d1050300e089950354100303040c00b00440b1103d411000e24000000203000c480c07140040da54401c18003c110400910080d0403c040c2d403248940d4005000c02d420420b4880945001c1d80420740c0280241004030702e0031500c7c0790303010702c20445400000d42c60314007080901403410010844400740800c41d00c428010b504 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 118984892 1250 118983642 118983647
    0x5060a090905011d010b0306030f031909090b1c020f10020106030b010f060801060c0510020f09040f0e0705010c060e060403020f0d080705190905092418070513030b0c030405010c0f 79
    0x8140500200000008045007503510f0400405010441c0302094940b40e03880039401d41c00c339100b00d46045c130000701c50000c0400d059000b84141b42c0601402800409402500003c0e212045c02c0b100b026a031020903420703100d4550320390b5424060081d0803580001082c604500d860203807024107030008900380070b00340340074010035030000c3c407860555a15080c02e074030504051034000e2070300031090046100507002203002c421039110880a0003080300111000d100307491681d401c1c042244c0071006502c3c200d038001c080410555000380382a1040e03d00624010a55600d01c48255103407a1059070100d006a101607000d101c1c1e080c0034045044124954601078080d401d0040303001300315010b0748003603881c2c5d4030007540c540c003905004041403401414040c0c210003e5180081185510850074598071405182140b41d861036480c0c1880c03086075818100c400c440e080c7d16102c0c401c80d03064202c0da12a81c1a40750304140800412020507a0300d01c00d0801c0d4211955a1506140c118251040e00c8030340d2040c040b5082c2030154554 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 118986142 1250 118984892 118984949
    0xa080c010203040614040302130b0909010c0504090c090801060611151e0a020c0601090509010b0a0b0406110a140309130c02060105060c190507031b06080408030a0605060a09090501 79
    0x21010b02e440d0130020401701282d0124401c03075100a511510949121204800c0e40e042a0000401100c10841c04c0ea1400d07a201d083e00c040030440f9001610400c410b11241000303038800d42140c1020b140942c80c4a486201403421581c140c4c01c0039012031400030303000c0c3d0804810401c0c4184400c61710b110a88c035042440781e02d10085074445048421140100010f0403003400c0e80d040e0ba403c0100481110f0b41c55039141c02100080c08281d40d2403c05509102121415040c044105002c44480d4070314545424070300402103508801060a1040728022800340c00c0104404150003c50a44c00c600910354a0906104100c19400c0c910b041d03c19280c1810350321120a90041626030441d0300c1a80c078107984002c2040d20f51304103e41c0040003894001d80c04000300c00d02000150080582e8442c500681e0740358446d4100c1da0031602d051040c0d80029010310700090010fa07000380615000090107502080c0b036511040001d100d42c0200c040c0c00d001507015030301040030207080e0013001e00500c00500c0c580b02250400c2003950a24 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 118987392 1250 118986142 118986149
    0x70503030c030a0b0d0f05100e101805060901050613060b1903021b0717060919080706180c09230603070f03030f090515190215010f050a080c01020304 66
    0x10880800026940f03142034012580f022030081980d0704c142a5803130050140d84004406807858443c0c41030b49100400d041c4550142003030310360300420343c840b0030140b140058803102203076540d4400010030703240000d081000b417035009502910000c1400c2c40e1100c10f004007000c1c041c0c4400069410302d0820008041d0b80000c4481011503000e54542c2c4441c490404d0f0080e1151016071903092804010748010b80c40b01040e980261401e100300142e1a2410600b01c980c0d400042e034100c819600b02030901d032905404c480011003068410718842c0d04049664032000d040f10b009010209010b5004070b0b00104000039402c3f18000b4103000441004446006034401c02041c030801060300c082000c2d18041600c954041001030700500d001c1046041c800e441c2d02c4e000b0030742081d006981c000704800d560007040c2803405213000070b003448007906400e0030080551500c1d4181400407500e4800d600801408020b000c50001c00c003800b0b84001c55145005070314101c24052100a2540101040d0300090038099141c1e1f404011a42207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 118988642 1250 118987392 118987411
    0x309060615031f030c06050d0509070632030705070311011a01032714060106080103020d15020d06030c051203040e0c030709171e03070c03170403081201140607050303 73
    0x4200c0300c003886450071004d42024120101c0480c0c0051420350180040c40210401501803005d502c801030700e11394030042401a074020882d0510060110001c18022070403120b01c1e51741024030403443ca130f40801c5503401503a80c03c0010780001803850516803c45413405030000c0720300c020170040403260000980c44180c0c0c0801810151920401e10841e10803400c048856501c0445010584040307141580081d014045680c1d6140141d000004025010300c1c08141266000b8103483d910f010103a40302e003075940040e130381d42d103550780e0038000d40b40d003411356114040246219810309000c50341000c00b00180b03003003140c101d10200d0b0320400060040c08441d1a41e150002d102c400b0403a00c90310f07512000e4680780040d40011b4120b10000e00c4040825000140021404264441c0203441c88110f042c4981c0720721411802508074440c107503040002038002d109410407250414107176401d168499490100070f0f8001304444484000783c80040c000340e115000b03860202001224868549055650381c0c0d501e900006054240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 118989892 1250 118988642 118988671
    0x1080606120a0209030c0a090606090b130909020a0905040c361d030d05011e0302010f080402210601090621060504030203070f05010c02060703021c0b0d0605010b030906061503 77
    0x40c85e1030401c446100504000c003007403802c81d02c407602400145030754401c0c6400a00c2040c0001800311200c02120300105c00701548c01002408c0003001000b60040e0b40040380c203e600400b00084a0b0f0191180601540c4900500c01403585403802c90020000c803501c40c152860f0f140020b102c140c1b60038501d02c50348008140404140d25444504441008861000e5401d02d400001000f084240a50b8406d034140c5449095400d010f034808034240c48402c0b41c602009021604144188042c1401500c5080d03126100078080d40154000b0301c2311244580d0b00e00d14106090b407100380103100c0d1a205002d420b02602d1007442104549085c2c1c00204165849854003400e01541c41c000700702414401d10072120319035006401141c09111a2810078020140200b02c0001400b0f80c401040c080780c800e00032140c40c11256035189030360a410b5440407000f84050f042c5e0590041440c40a10f0005685006a5000f00003000710240c0328540b0340c180b903007040e10081503140303d0414001d10415081460003a25005087d8810061 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 118991142 1250 118989892 118989907
    0x110f090c21090a0f081902060103030909050118090f0c060e040b09060f060f12131509030e04110d050c040608070503040302060103030e030c31180201140d0e0a0201080606120a02 78
    0x210346c3c41120746091030182c1080758109400c0c0c000842a0489200307a40e45512507a039071000030f0494400303010b4903040b10600000c1149aa80c203420044440303009142c80740c030003d8196201c01258074564084000f2038030601c14045907103010b2003580038460b815280e6036001d1803c8000125240800c0080c54130401000c0303072485811111100f518a030004100300341c0301504010544d41c0c1340681c0500225500c4299104400701440c45025010400d40e00d922682c148051480070070014003615414400d4242d001e01c80340d5442e21141c007480c1c0c045c90706001c02030b99580c20288000e000013070007020501800410024072000070340c00a201030460f034041ca000c2480b03038810f0340002e05040d50354070388a60090f4605c82680d00a440001d10303075030203042d0303140001e01d419002050100742c4090802010000000c2003841c00954000d1000b904008107801e44d003490300c0061426401104e01e19405519140d0001c80040e0455810100391340d007194003102c0c140e043c50f041000341d403022400104044071458000c20b510 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 118992392 1250 118991142 118991153
    0x60109110d0606050301050405070f0c08181c061503030c02040203072601060e030c031009020604051c0203010b010c020d060b011b11090a060b07110f090c21090a0f 72
    0x3200951030941c0c090003072a0b51044000d115410030700409114038681008214036074000c8583d8901c0030100d07201d1540e2070300300b43c445c18026081016001e110310100444400f640c2d46506000d1001c1050f04140000c20301a810a54111070340c5092807a400c1c450b8400030700101c0d800859901409504035400340e502e0307a6a40d412911055400952880801449042030f10200c1c0e044015045e1100313542c038550380c126040c04140e44c800a501455425401090b802c010021451b00f00d0301c555400a0921440c09503251b000ca008a1102d070b004030300c05018408030004600d03003070040c9940d020702468031181498690300054212002001d00400c100d60305c0304880100e9010703804000c49100c00001c3d0b00b80c0c040150501a403c05164500244903d84001c0000c18215461050600f07480e03e5a18140c20405540e8a20b1103100d0a0f05403240e01502401c4403080b40e070b84103c01c052089411400c81078a50131020719621800c2e0f00203910070740c08800a02000a05100040d00100c8560003189400d24600300381044e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 118993642 1250 118992392 118992397
    0x402030703060c030b280603020304060b1f0e150301090507020a061b020c060f040b032a0405040c0921030315030c1d010e0115020c0406090b0f04020c06010911 70
    0x18034290a00eaa0040f4081d01a4000300b000c50064840c04110384001c0c00e01c00e1881414a00c040c84172030710b41800d000301c0c1e02c282d02841c0d1142c803404000543c81020000600d41d0820801a1001c903100d6000b160920780d4410150f139120002500c810022004644886105000c14003455199660f00e0000590b068420441942c034980c00180c1001080c20540000030003c0124250301e02610a2840ca00040d08001d0110b0b0b030303140c9407034100c24217041c00c0c42d45100d8a1fa1020700030184802e0300c8140080214247c1012050070b40491241550740d074580740c10f01003601c0c2c800004c0c07418070041c01300410828046040e000662041003606111015aa28080e030080504103092680000c4151000c8204010f8402400070754044150400381c4003401c0140d030a020302d0134015502107081c0c0c02d0041220f2040e148860308460f441340183c580c141c81c2d0001080444185510407802c0c5912000d03190201e0511100c2d0111000c81610154903294420381150303030b07400f81071061040143d0b9a01510305540c12a805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 118994892 1250 118993642 118993649
    0x609020d06020306150304020d02060714030a080a0c0f17070203040306020c0609010b030303070e10110f070f050301020403050307021908060a05070e01170f18030f0c070506130b0304020307 83
    0x440346202000741001c40c029003080710040d00500001d0100c03066400001e0076030b84a00d0340208a003988115982c20710941d604030007400c4480d1007264180400c2c0c3c1d002803020b0044401240d941e01030038901054088266294a5290424840410400004941d0080c030258490742051503034006616160012859031240b54405860544046050100c4840214000c0e00a030a03400081c002440c6184c00c0548900c026149000400c81c0f40e40301105e2401c0c200300502110445090a114500b183c0000078203020485403180440c1c0c000325821b2008405180d500300c05041c0550085082604654032503070b81c2d200c0c0100191041c080510000403c0d1541250030002d4001c145c11350f07445040c1342000d0400f074001940c0d03403c081480b408260040e54440e00820000120280c880f40c80c645601e012801e809070058010351a85c0e0605000181e00c0004100800500c030701241c00c103039503180b1000c0d8582481d4142e000319106030020400c1c0108181102d100d60240ca240a4407191359032114400249028120351 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 118996142 1250 118994892 118994899
    0x206030f150a060302090910180509150406020306100207082a0a08030307080105040b09220602031018050c2b06090204031b080616020a0c08031e0c07030f060902 71
    0x1440440d07504c0e03260b0064070440000343d6108450351151205100b808156000d401e2450017030ba605d240140c18950030050b040030382e42058400c51004420040e03400c40040b03030240c07025a000014041c0e5400c045041400c4c8090a1024001b807e08000e0790a840d5100c80201823640e5040d07690301400706011680803801034600408032009190340700a11074982d0421142000460640c0000280c0c90070a400b4080300303101d0041100c1c2641d55046035400040003500d00c40b40704c540c2ca8032803002c00a0729910045001e04209001c0d402d0151803d44600003040149120300b10a0381407000f4003540071814015903181d8070b110b41740d0716203500c15a0828408244280359284005091040008003138589500420036a070040600e4060055020100c480581c20351083d5a041d81c07010700041c140052704000ca408047d00d0b4410b4512103a0540c483c03800c141c000e60020080d0b0b0b00006003441d4900b8128101542200106e0505030a0140346100182c88616030310001d004010340f40c1c080713410000b05900000d40703d03078000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 118997392 1250 118996142 118996159
    0xe0103060b030a090308010b03060f011b060e0309040b03010e1c110322090c08061302040308040306060501030c0801082508151f03050705060f090d080c06060d0206030f15 75
    0x200c45803006400c035204c040d000b08403548004998036101030b00301d911540300034203511400d4a080d4011500b141d6100a000744298a100d00c610000c0c03964000c5540704072104c0d00560721001e4001c1004110b490300200319200e46e2400725610b5203100c01096000403000518110207031b40c04135160903078604401c045405018000000c0c54500680c501124040c0c00d2154a00c0340b41c0c0e6920758030b0740f81c04c41d0219400e031408550502d000a030039240c10000341110500c403071800340c20b00c0c0e540da5a020303103500603400c122589030320344034148683d580c58031071034051200701e00e0180c2c803a52605041d20745511031002c40121120207200004900030602d80000c00506012045480c8040d0600d50300c803c030f480035649540040c0e042c03203140c698036038104000e1082e60313041005007440900c0c01c0104440c83d8420500340c90160700038005641955146001d45158902030440c155640711346030703101e83c04c02c000140300d644620034514014015841e100e041da036002034000030541054607241001c20702c94075040314a96100300e10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 118998642 1250 118997392 118997401
    0x70f111503181c0519020c0d06051603091e110a030b0603150c340b01090b09190b0a0801110703030e03090d02060703050906030109050115080702030a0e0103060b03 72
    0x5140302c0c1803107403180c8141c4071030000c0303c1945840c0b4540d0a0160001540500c4070403500144441001103d800320300461f900e141e00e00021520030100208180d0b402079448041144010320400d0b4003503c260131340350412030200156074a248442940b01c2d008028a03081e4184070401c01030100c2c00c030800034024641d144040c0d1b2454103004000e000c40311395009000b43d0249001c0301a400d42401d000352240e040280c28043c1c41000502d15a0f04031250030f44000341001c1c0b601403442020040f0300c1032802003000490710b606106e040750a035240b20040b2401101e240c410804144001c030000f504440203900041004c1d449c03240020720000c02c41d00f20801c1946062124011104000010f02c0454400d840520819440414003038036070068200c50307034002490800705030051030840d0050101038420b082090400c2e03004408541150000d070000c110aa46e9170005020038004007550801c0300ca0741f450701102501e45900000d4490054040c2c40d4144050100340500caa80242c10841c01340040c10b1046881c0e01e032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 118999892 1250 118998642 118998661
    0x204090207020f03010b130c0917030a0206090a0b04020603041a15030d02060103020d020f310b030a2004021b010b0109060801080624030d0207050307060302070f111503 74
    0x104801c0307100e901c00c0c0d250707540310742010300400040795401421f058202c400c1101d41c00c040d18002c070951003004001d00010900140c0c00c0d1030302802d030610000854071102d0019019103480c8014148054035400301c5003c80c00202c400310b60381da0155055075083d841b41c41c0e034600342111031a402902581d4030026410080210f424158001f02c5d08401c6086400c10f0501e544241c0c2c9480702800040d4000d000c401c076550240c2801d0100d00180d42000d011040c00f1008104029481d82c029000d049080300c4a0041c0e100e000304034040d071822410300f00c02520074205a95114a2107154440c1c080d201e41004111000c1583c1c1e40d130781513074070b14072100f1180c0a00d5480d9080c004d00030001d43e048180468015070011408510070ba5015050780d03440c100500b050b4a40c242c00481015803000d00402c4048018003100441d2814060b05401424a030010080030b4100010913043c10b00640120307040510500041e0081076a041506c0200da0304000c40c0c21503150f03002c0108121108158810b031141d200002840368402 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 119001142 1250 118999892 118999897
    0xc06040606060309020603060f010c020d060b1005030114010806120304031a0903030705070305070503041d04060f020315150f03040f061a010c03030b18090d020622121202040902 78
    0x34400e50080040c0754407103400350100e846010000c0e401485c18070002c0c0d058140100d2244414105040c40c504020701503002035038104003018221481516000c4690751030400c024880700030045824501d0071076040059403072600344c1c4044100d040020100106115440b401c01000c40015081d054071f0740d40f0f480741001104402591441890321404a00044000b070000c011f82c0e010340600d40e1078528022041d20300b1a003d821900c1c050b65540801c000000d0480c90220316101040e80f0101c424400389080e007081022602101a00000c00b801002048040845900c6420040c102110998558001c0c281c0481c028010803a0100b05e40341c00000b400b00340a0002217049031907100308810700503140311100003d1b20ba0342100340c003800310341c00352071140010303000b50070230481401c2c0500a01c58000083ca00940ea00006561811860300815416404d4550500281e46e100740007944060500402c165003d41215542501070505080118900b0b220340c031440b800c0601c154891030940d115504c4c1d040c800000d6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 119002392 1250 119001142 119001151
    0x30708060d140102131a03060112020409020703080604051303020d120f05092505031005040807060606080709050a051f09090515040e210d060902030901090201030b0604030507091508030c06 83
    0x408482800507110301b014919000701d52054401034250b4907075a00555a5958406160110716028070012035109100c0c4044c103030f0207000750398143c00d07810410144000c98401070009210b004904003200c0100340c002034070426080f41032900380c0840c21800c032190004c00d9201e000100b004d0618051010a2200085103031001c030118400319003100a41d516481c2c001820700c240c641542102125407071102d1243e10440e07005005181503031400b5400d5907414112411a0002c401084601007484651035001040c4009840b05442e00d807001410140010289444006400c91103c90010080c18140c45025140020440031105020718140041d0b00340388480001d0745e050041c0d10300300401c424032100051109205036400b06409982c4441c4950311704a5020218641c0c070702d070b00e4441c0020070b84220704c0107510420305c0c0e000000704503006200040955104031078030340c4203100c1444103201107070340491440110b505032040020444104204013201c0301c0079902060003800040342d2841c9502e408941541304 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 119003642 1250 119002392 119002417
    0xe0c0702100e0f1e0f0108010f0b0a0e100206010609090212040b0411030a030c2619020f0709020d05070305190e12040312030608031305090a023a09020105030708060d140102 76
    0x5070308400c004561040b409d00c600910044585001c010181c0340900a1091400602e81000344110a0b408101244a00c032900320040e4485c00c01000800d5003c2c40d200086c201c1c441040d450306048800e2008900341c041c2000c1c2100d21a1400308007042050f404914850102505542841c0740030b04002d00510400c4405840a031548000c0814901c140c13001c802130740b1a282d081900b440506456500112079090200095124a80081030464000c001c601c008045481015a440020f00e05800545002a1070709e001c0c1410305083c005050b2805096846072690104001401410421024074120804550740c001c03003000100030041c016550903103040310145441c113110560740c42507000e40c1da11032040c0029146c880508248036a142c208840c40c1c00100030344001d03080107804a50100c024095180216000035820700d031100300b008810001c00750141081c4200030102070340e00080c04a10004121400b0040d10320002086581d4203008400001e411142c007841d000c2c45003224038001e50092a50406 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 119004892 1250 119003642 119003659
    0x9030109080a0f02010501050114071403030c1309020901170903040e042f130903090902031005030f0105070c11010c14010b0102070806090d180308070c0e0c0702100e0f1e 75
    0xf2a801400b03190304840301139581d64002c000380380d11078003250404442112181100d1a140c0101e2008001850089500986d02036850380d1018000b00f9110413940018103207801800111050b071f0700b02090360307520442c40505000d29507600610904500c13071a04049504254107081c081030010482050011510000ca8460b140c54598080465403581c00d524560082c2c140100108610f0190030500c1c5040c820709012060548513100030081e60012103503001241010b080c10059450100505004000300f20020801402c01d200010101100c01001030808403840ba00309040d81d1160540403c05608048003c0e40c0501c44404c841c0a05100508a8010301c200d55000c540c10002144980c051500400100a101c0d50004190307482e2b0800c8440d044a000902d20001c0403403044401005824842ca0841e00c40d075080220b00c4d9020ba03006001d01120341018024000141c60b480341900c0144994203101c0340600c016000250352440c001a0180c10401d50003e04050510f684c01812b4105000c4a680f034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 119006142 1250 119004892 119004917
    0x20106030c090504020f040c053010060c110f0d0c0e0c0f120907050d030f020114070e040f0605060d0501140105030609010e09030d020a02061501021b090c09030109080a 74
    0x10668030140e6020754409010011000e45242950020405232014240139003001498245851251145c0b99180350300f86030f41040d80c070142c20082c3c000e64000c424100340c2c01d60a082080091090145000c01000e02101c580181607a60700c03030700051500c3c4802480228000c1c09442e00718440300f8035114613409241c02e80e010400c014200030584040c0d2040040081c2092003000e2400144000600b101480c0e0081c41404107540d240d01c180704030460301946450001000304007009085a25503198030701030171074001c00e00c448564001da11a01c7c400c01204c010130384045146a050042000d60f1010350b00c03800004846481c0911500000d0494211803050303070b0010b04d498010b4416100840b460b0303070304c124a8001485600e40c44c0da4603036080b0900100302d03810003100d0f4010b1412640312104042c09a0702620030080010001c0d103c1d43d82000d800c0c80507182c0300c5404500c84410f0640165254411070005001031039000900083d554420b00080080c041c02070300341440f1030a5480440b8410004036509900c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 119007392 1250 119006142 119006159
    0x12c0111070605070201120e030415020c0a03031205090c0603090106030c0503160b0c010b0612040203010c0903171b0106090c020613050604030302070f1203060807080a05031e040e010303020106030c 87
    0x48110380c403d854040c900340503980110382540100f41c03041d03441d5688070030080184000f04040c201910844000c0048500045006880d1200c0000201c1c45000d403204280300081d8403036102c4a01d941c0d820310220f02501c600020904000100d410076420070b00c040108018036405400010403207010f800707030110054540080c1601c4e001000601100d20000c441b00b004440640320003441c25041c1e210000940321001c0d400103100e5445080c1849600c5a50410300c81540780030300c40c5805c0080300e4204060b00b00e03d15a24041c140744030306a01095038502048540f0903031728140035590280032030300081204503207450107000288180c0540800612440700003444101510100d04181900100100015a9195409c4002c0d621520088a43e0400106046d0011f0000c00a1610120054402207006414503d1440c81e0030b0032a40251071640c40300b40310f80089200401260312038900d031600740080c0d10000d0342c0e00a1610035030b8803040c0d000f890800002f0a0540c10750060041da0310a441400840d03588a528 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 119008642 1250 119007392 119007403
    0xc060f07200a0b270d0602040b0d0b0303090d02130e0304090213050108091506180f0103030f051602190302030a0602040f0b0a120f0b0a0305010e12031308030402012c0111 75
    0x100c91482c056440710100d60412013403407049104020803421803202141e8803142070b608103034000205000302041c032008010a074003810b502d10f0816002541001000c01c0014011003941c0800780c061490810b840d0310540c00390708125040001d450441e0350341c1e959580148000c0d80700070740030030082400c6d11010900390b10692100b4011007458000705240742442175030741c20141c00504401d0b07100494a05629501400b001900d12410010044515540c51800c0113410311505040c43c2c400c2003020400440c240c0f082d100b2840d602a010b130b82001804513628540c4d9a42300b51030b00040c0d407511950400004000c8135800410550f8400d403c94101c090761020030a40f40d0003046e02ea5004942c0310018026402c1d440da0042c8518a010b040100303c0c800b00c90041088119941c00aa61603510780c408880b1183e4100030101c0744a4017040741d1851072410003c0d2000c21260a000240707080d40000c0800d007968801e0b1040c1641d64410340400d1107600c1d44810103039645402c02005801f01d0346480e15081107a04c08101c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 119009892 1250 119008642 119008657
    0x29040507090b04030b091005090d08010609050a0314070b0f0d060b0405010906031a040f0f060e0903042903180f1203010909020a03050a0b011a0c0c060f07200a0b 71
    0x31036003494116905c240c14800000c0038100c0d030b4810007640d180f11052a0041c50300070b030030460141100098002e002130854005821440c10301601140401040d03c3e1081110210f9812016003001410552025400d000d210751226071940d101040c2080e500c0000303001884503107400c0308200407660740e07800d4182c2c0c58000d07480340b533000c5131260008100103400703078205010035000e203075461404003203050000b401c643c1c4480c0304081c100d0340c1d4400068002458032401008c0c10b03103080749440b2480d04207191940c0f0700c21401011081881c200320038141c0d8a260008420348140402015201d190a0b030001841c0500003411040034407500210340c0003140040f64000001d2824401646980c0c2030010120241101c000e08981000c41500c001001c140c2c14800020140c5c45000741140b82d5140011480c029007008980210841c01000852120000002c04040e1440c0c19030303c458540000e1243e007800341c090304030090045003203202c20850340d064508449c46134030b004a5887d2001a105c4101d019035009808 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 119011142 1250 119009892 119009909
    0x915060c02030303041509050a1b0501020304080703060e030418140105060711010807020a0204050c030601081b0304030c020a0b0a120c0201020a0804080903031e0408010c080c0702040509012904050709 88
    0x440e000c01d540140c03411450b400301b100822403041960320781b480c0c5024030a095413061903a400800c1d41a6128110038000c00d0240f00a5042074185044551900300d140b0005040342d0303554003c0c41401c0c0e014800c0d03030020280f44601104034502100c04002400a014120b4030064888001003060301c0d044007680d41168000030756600000c80140196a50f50300074005a05622448143c100103079070714054a4803410703074034213400e445e8107025001400704c01c00908076801c000150303262039940803003001c00e0f40e0384103400d40340c10b03407000e0f14500110b04248182d801542d0301c148001156101039030028980240506003220402c41c14030542800c030b00701d02407444c02c00c002030b80070b5021802103000f030130240880c0380c4014283d03854040c2d02d000c1d40710b03500144217051150600214080000c4e240a1240d011458a6070611b0226480c0c1100d054400d40b0807404002c4c401d030f6880c00400e00c0e41d5400d42c000c4900c0c1003000391200181d038218107a440400c1001d0710940c4241e0600000550840c410481c1c64200c1e40c014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 119012392 1250 119011142 119011147
    0x1801090f032102010605100c120c020306070f1407080a080a0e0d030e010e03130807050a0e0708070c051b1207050a150c0609030c020909010b061e040b040915060c020303 74
    0x81c00300b2902481c03148640c100710740d05d92802091660795a00a400c482550f6121015003240034501050480b154800050030300486088020158501207885903010120307203032032005070300344060036602c0001100840c41e802d400481c0250411000714020598ad40039615040b0241d0345110b004816205102100c1d08035421041c08012424083d0300054100e0780c901c000410810080f82865103550459016241d600d24842c00400881c042031040c8000740900392841002e081c203003001c1c1040c0381c030042c2281e404c0051b4040015030b094800d401908217650700c801907454800c00501c2c981242c89a02500b00e00c501c50300310100725254000038408003122005800c007103c051070801c940440b40203245044007400280c800c40000075403039110340030526100351100c000300741c2030740103200713188000800c03c40e21a032411540b010035581d072406880c2c01c021042d0020320000072019200c0e1301401594802c038071031070010501081101e440e8004210110940e4407540e8036070740d01d000c201c1d226010000042e4058004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 119013642 1250 119012392 119012423
    0xe06010b04051210020c0a0309082d1c0e01020c04140a0c1101050717060111070e07180b04080d050315060d060e0a050a0506030703051c0e061801090f03 67
    0x24407212036500c034200f02941d0441080a04140503607100041107401c2c0e82100800204040d081412800603000d05001410724030b5a07401c002201c43c0052500b00001141161b15051281081201c0000541804403e04000c03d100e00060082d40010301c1e8240580500703075154455003041e124240140c0b010068011194442481a40060501428200c100100000d43d0780c41d000017409000d006000c190b0720020300703464001e0003a03e2000054005810803107103050a80145500003000015911042d02184450b25070400941d49822030300240391800507100c0c40000c1000041f00540100d8140c1c800b5102c0c150741442c0d04581d40c0c8000c5a030807200f9501c8007402045030515001910341200b0401e00020900e403514803c054a090449079001d9454480042000750403070f5000d8560086003e0307005080050640c0e56440d294000c500300da400313540c0090300140c00c03284104464491700034090070140da6040c85014403995a40811a03107030100744000c9001400c051402400c0c01140d40007540100e00850 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 119014892 1250 119013642 119013649
    0x20d02101805010f090b030a0b100e040c030b0d020112020d150806070c2102010f060806040615060c0209040501091202060f0c040b040302040b040f0c030e060604020307050708030403170a020d0e06010b0405 90
    0x8050070300c020940c1c9c0d0380781000a6441d141025507000c2141d445840c00300800340100010790725003105000405081c9440e001341038440050b40040e207a42420a0030104050b038040300001e0007000c07080c1074503506080c84441114841200142035800c08019503030360b582e07650020b5844a0940c3e80051900b20368002c10700718241628200c1c10044d02600c00454038226003900081a00d00c00e4102d200c0c02d4000300e00744010816184902c000302e00860000f42940303840c1103006012400d440c10040e004501e000005420400d00b07500620034141c2c41302c90032042580038200295509402c81d001784120b40c3c08030100302c2039141d03241076a00319044a50701c0340c86c2c00c0c1180d0a10003c0d08946580c40d4020751101081f10150f0018010b091a842565030002580c1031180d0000e403078000044c01480c02640304006001c54031390301000301e0f01c0c45034009201950ba80c44600d070441e840d01603405040d00718081c4d40148640b40819030001e05286003c40d80510018081504468490780c0c00c0c03040c142950001c1108004906 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 119016142 1250 119014892 119014897
    0x60a0506030c1c0c031202010c140a2006010f0302090703090b070e0612010b0a03110f0307050702030f190b0a051e101a04060306080a1e020d02101805010f090b 70
    0x61844841c0b03c01e2a0032039941d00000c0382c4035002142c150101c540140305141d824402d61401c03210503e0881201c112040c0340c0041c41c880c02916104124450709003000e1b42c1340c183d40300c004c10342c0494129403066035503504442c80c0e14018041240300f00c0c0454007043c0703614424051004025080b07081040c6907100e6680c25100401e80030451904074200780034002d40307290b01200c1603000304255a602c0e6950b00c19044000c085940002e804840c03031070244090703001c80030110140c030707404081400c10b2a07845140e400003d00c6c194207441c0922440c0f00360000e0000305240c51000c00180340c880d070720b0401103881d182010410780d481225681280c0c1d01004441c81003400b11303020035420908100070f12002c0c50700e50f80388003400c80101c80751707052021000904005641d810f105040040081c2005003040b0b850543c1c400e0614110b0084800b520464075100f1800d55513a1280780c040158000c1181404281d24400504002d6100180e1000340620701c00000e110b5005820700040d102555131001e4006062142510854 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 119017392 1250 119016142 119016169
    0x5060702012105010303141c0f062408010506120a0b1c051614090c0d060e330105070305031503120408060a022a01140a020705060a0506030c 62
    0x20181220a1030301c1c1e98030b118000c400302d0600002165640c1903082c080d000c4200c81104040400d4100800b600180b440c054001c3c05010080010405905180c03070301d009403a140d0001c84c0701c000030381460011040d600c2c0c40201c4654981c3c0340c124040e81d881007081154003608480c0c0001c4503155001034280c03c031544c00141d00380d000904502000302c001c800004244010078003128540e00081c2c1c292030400f480c0c0c00ba18000d10003038110f0541000c1c40c13404660744040182c4800c4103031034081158040d03c4100e80041c009002c00754415086071604031000040c00b404c450f98134001c000d189801103020b0100c8018a90040c4068441c1071404000d90f070b080b03a0940c0001c00814255030400d04e201d25594080c4074a02802e036883c0001911a0b040c6510141005405440d005595104005440031609401000000c0203202580804000c1080410b203002d003040c03050991082d000c0a080140800d01a405802c003580204100c4905540b42094041142c2060360481d9241d40b20a1511089240111012000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 119018642 1250 119017392 119017397
    0xc030111040e0612240f061f0302190804030f020610140d02090109090209090109030906050a050d050103060617060f0402040209120109061a090f040803070513080c15040e010506070201 81
    0xca850a202c4d2400c040382c9590041c07444000c0710020402c0c6680010b03917500041428008401814000001104071000906040034401c3c440c01d1801074a000307a060b200d5455040e18034003c51440741c080242454011101100400e000c83e42c40405c20707200251440c4140504400c0b524000e08001c1d0308001c078a00030441d02d60101600c0c10640040c0c8440482500078a0b0104002c40e65401d07610401040e0b000003420070996070b141c064503602003a4040d4510702250140c0c104103946011900048409114540018450340d062400003c2000881c2d480ae5085405c000d02c6940d0a080c0c00301415220202540c0d08202844400007080c007600d040d60081c0b0b100100100540c2800802d082c8150941d200c9080603110550b417501c98207040e014459500035030813400c441c509014609200305a800030800350025019140200024102500580c1150031800c180010801002e681d5a0030a903504200310103139018407014801c00027182d0003402541c042d00c035030813101560f0b60b003005d091204903003000005904 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 119019892 1250 119018642 119018659
    0x50d090f050a03091d0105060310080616020706030212010510020a020a121106070308070309050c0d0501060906050f0a180f02040902120c0a0512090a021009080c030111040e06 77
    0x18000d04504005148103101a054165075800c02034103500c07007075108402481d03400d03000080c0403c4561005040d50f000312502501c1e529048035010214410381c204200d241304040600081500010b684d0728415203550860f000140c80349012003d0b4000c0305044141000f44d540144101c0c03078a102da9010110141c81128041c24184c0c000030360400c60350b4089042c1624508481d0184901c040e80120700d1081178070f0b260b10b09030150360b0040c0300400003440a0205540d0301d1800d01080414020400e0080303005010146004d0b090601c640206446d2140b030601078904034001a2a080000700c50414500c000c0c1602e103468603003244e43c4069a0700d00000c0a91a546580000401c034040c806040036012444c00161035882c054862a02c0c04001f40a450703200a0510420825035842f1085510800c00f0868406942d100e00010030301c2c000d1101c00c003d6210342c40c00050400140e1005480f4105d6485c42c00f01c41e1031031005000d02d070881d410150044a121020031050029249000300280c0210b0701424092 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 119021142 1250 119019892 119019911
    0x6061314031c05031608010f030f050705040608100b0405070801030201080411090a090308060d080d0e1032071409120709020903010c08060609040504030c140c011403070e01050d 78
    0x4500b40045489502007a000702c24000410021500c4511041a9040801045d410701403220122011444010001007031403020b08104081800b05100500001e0000d008640c1c0301c00c0c03140e4861860300c0c41d19003403500e0310303407000c42a00c0e0038091140201d6441c0c450f500140d0840e0011030f0200170080c026501045141000145070312410641c40c442d00c8104c07800030b90313501e007450001d1411030080d181034807800101018101203032603002144c0c4080d004241c001085980301d440c99003001c032000440d0380103e1030b025001084400c00c000c500c00703c0400c40d0820000c1d01380b20b15207030002174080d01d540b40012800d084061501c0b0002009160b0180001d0419404078607007800300d4a022425080b40341a507402040111440c202400703502006c00481c2401290343c5082c10104481d8001c40075520321540d21000418181802180c58500098000050031524140d44140a5484425280c07160006401201142510221000b070b24010005551074400c0d0b03d541c0001110180c100c02042d054440d07542c070220 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 119022392 1250 119021142 119021173
    0x4020f03071a04060801060302030f0c0a0c08040b0403060507080705071104060305030304060f050a09030c02060915120403170402031009020a090e070503010c0e030d050a031803170606131403 84
    0x34210400c2e80803485540703c1c2455402030000304182e02c08810301d4018028082c1010000440c0c42d032288130800550307119880d40c0c908035080c140324040600703d0310b0001800300d600b02400d03000303205807405130205005070340320340f541100d01e8801103034008000b8409105110028451a503403990502c001480404c1c2c8540320b464031405c550054a003211826640c0f1000e4648603804d00891f81e1003040114200300158007500d01500702c000340340c0001c0c0303d4000092694590750b05c0e001451600000d23001e44940f03070042804402c0342c40310300346d0381907021030a5615000300d0452480389079445180d019004d821110310514281e0301034011803004a81c0100d8940011610718031900c29209074455250041c48140d24080900d421251421030b000100090712801d09410340300008c901c1000340c5070f0300d4016031b15002a282100109a8801024410402e0210540515601c11380c621803040c01d0003401c2409031242001c01c00c180c803640c0162500304e1380e242410003145444d195154090f500c06429205500031103240c0c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 119023642 1250 119022392 119022419
    0x70809130509070812070b040c0f0b0a1b080d091103060a0b010e03060403080f1902040e152b0512030921030c04050d050f0d091d0c0304020f0307 64
    0x20300c1103503592000c104a904042044800418400000d0300284580382103044192007903110290a4106080102d0204840e0803808401480e00b170700030064054a0300b00d1100143e00c0030760354900080d03420041c0c15859041c00356039064168404030311071801c1c82d0801d1810203007920000039200c4000110301540d00ea28207110141c442c2202c44000038441c001c0384009490f503000120740500a80c0301408202c0001d0300b0101c003d0b08a400d10303c002c1c04650750000800d0205c03282c401d804500d2400441e0001d00791b004000b409005200300c600010884161400b4000301c8200b0306120340411402003100301c0540721200030a03180d940201c0a465070240001440c100030fa00c20b844110640d40041c80000401003510715032101d810070920300610794180250310f218a40145e0159500c40d411194441040100c10003010480045650544840904000c2e0241106402d40301d244030421041208100500343d2280c040c0c0300e1211851201e0454490341c00f8014407441c9222040d80602ca00c400100e0180e100400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 119024892 1250 119023642 119023669
    0x703110f03010f0203010f09090b1512030a050403060e0303160503070e0405040c030302010e060c220e090601080f0a02011d0109170c130e06060904060618051f060f0302070809 77
    0x80985c1c0c1c0c0d49012426104d0b14280e42c80300030341d103150080c003e0002c0c40f040d41d0142c009203a84e10348501040c00303000080108100700b503082854800003904e8019a40c2103005401224010300007000181700c42103e160f201d100c215400c0321a02044811102c0c5240900041c42e01b0054038508480d00596610108085400c20b40f82582c00030132381c0504000705903090003003020041c1c540d0090002814080b0107580140950840103058005071003c510304c0d00c082d14081e8000b001150290400c6007803412082d501c0b41401c1c00380c000c55000d00c22622590020010b00148426410707580d0090800d1080074101c00001d203003240381d0410400e48400280301381c405444c00e06440a46010b005a88241400c12840c0c922450258010b02e08180400c42c444501080641d4414415038150150380e0311031402800030041b9402039a0400107000300d40c281c184055106d94440c070308a881007030816040d01e4441c00a40d415100704030020701084005950030340309801415445124403000d509044001d000201580c0400b80b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 119026142 1250 119024892 119024921
    0x8071e02161d0105030a150b0402091804020102120408030d0203060402092107050a0b16171303030e091b16060c0807031a0604050f03030408011a0a0b0a020703110f0301 74
    0x10001949101c2c444406401050100d0040940c084c02c0c0da90b40c8104000d030342941c104a0356803203103241d841e03e450701201c06c2d102008019080c1c2c1444115410f075048000d403403d030b005100b07480441010760007000c02c65080e60040390055040441c00c0c00e88201940c0000d0100c0d401076024421141d442d120300401010b05a842601e2181c3d84c940d40c540741d85001110f500803840741902d088100030310756850040381c05003031030551044208050380c00e11158a920f9030310240295400040c42110800ca000c1d849420340344203a48400810294030204a2012029610301f404c00c0b01b64440d042d2180709020050207007030946001c1040789801c5850340703012545003100f0303d804601c00300100070240340c0c107201d00c180301820070194401c180000380c08607115001c0c1d402000e004184400c1494250342c0c003007090380c00038410f8a00901881c82c1000c0c0c0d026030f4801c04252103015290412000c10a01d040006444484000d41d0007010000c0c6541c07101c001c0e054461520710340200d491164402d00d500c003802401031061801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 119027392 1250 119026142 119026169
    0x24060b0310150c0210030e03070b0103060b1203070c050918030a230711040507091214010c05070b0c0f04030803150102070504090506040b0606040b0d05040201030b0108071e0216 78
    0x30b01c0d04401000c2100807101048410074843e401a0380384a0900d4010303020345070010340301a4144006285105d41e1074080c280442046c0000100719803500620500a41901c482c800c05500f80354550744e0f400350a034020503071042040e0500260a18403125039000000c00c4010b060351034828140c5041d5030056110000280d0b0340d644414002e0283c040d441e01c600d400d06151858100305032145403090030380c42e010a100f29101c1021880052060054001800700b000f2400300f42c0050386804402c9001602005080c2c1d401c0c8130f56155150b0040d016103400a805c0b0f01c442e521503480400301c0c04070780e012503010307050507800744000310103d42e04101461007a645052200b400d914400000381c508032461b40440e1103281040260000614042261a00f240d0300030029115030311380c040090154029508914404003010441c8600c02d4010341205000e40d00030389080020030300301801115400c0f0100c0b17201001c038401480503c5041d02142c400031125203d0320558420002d44000b00003031054a500980341c44004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 119028642 1250 119027392 119027399
    0xb04030201110c1b061309060305060a020405060403240612020f3c091003060f06051503150a080c04060b09210106030611030f07020a24060b0310 64
    0x900c684129128528051820034407003c89555560114610649044107403524151040e2900e0080c0c40c1428102c0d80d1003440b147e02c40c603034000180054031099919104010224400c0a424421201981d00291500e0b150605584440e0000d402c015000e40e01868200320f41d0010990520a4001030559260311011700ea0450040001d04200d04620341d00c10f16801d10f0705401080c040d04080d00c189100d8240301314800c031200111084100b00f20415402c503000c070007000b841c0c0808095007000e41c0d00c100030800616100000c1c00d001c4a840e0300440340c00c440508002a400034000f00034551000c5c55103074030320700c11640e14003107813024686601010440e030003d01b004c1c20380d10302409040050029581101d0414031102d002440c000c0e42880e001c400c101170701880d809000703030a41285020f1900504203109140190091460350340c411160403082c0100c05011511303d40c07000c54401206500582e564140c0117103545801481340f640c6415118895545800049208007040070350700c1202c5520756100c40615 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 119029892 1250 119028642 119028647
    0x50910090e010e03040501030e0c0303030f071404030b190b1201020301060f1b0201081009020309100b01030c1d0301180f02010306080d090b0304060605031c0e041e0e030909040b0403 80
    0x34031590301c02050341001142403541d200003055804035042480c0c00705100005410843c24045002803c0b60107001c000f08101030101440711381800703094540e460200e001840ca421007014040c038040280a800e15002103040490b844102012501484c1d00000d01d0007100e40005003c8240d04682100340e0b50080010440950040c0050750720382e20f2420701010b03d805039480c0d09400c0820000082c180b1207541c0104201c4101d0032440c0014000c00c020440d1380c0d00740020a666207900001d80070081a04001003210194400d0003074140c400032946030300d11030341288414400c0100009101c9a015982d548420300c61203c080149505280074404070040460180001000e0350074541244055501444424403802c0d40a00310900f150360300d076440d580702d440d14980070010b4101c44c5c3c00150326109560002005105c0000032050f250310540b900342031070813248240816100d6002080040c920383c50009169802150070018904020105aa00e071010000014040307c000740d805a40c1141c100040008054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 119031142 1250 119029892 119029901
    0x1e0903150f23130803010909080913050f010f03050c01080c0c0a081c020301030203250302100f080f0603030904020d090807030804050705090f07050a0207030b09151006050f1305091009 81
    0xc0f55070000740d0350810349442d008164803041c8108003080f40d5500f10202848003200c252440c1041c004d19403003006010143c104054441600c807840102c2410000045402d280304005d07080b203901c00042c10503030081000544a03114010094941c030101080802e501345020700040154911071040e01f602d0b203099480d1844203c03109410b060680e48108014005603070001414004c1d45640140043c1480d0007280314258060242d0009400005490b032a0300300c1904583c03141d01c441d0469860f1040c540e00c0c0c60721000a54416509a601a08200805003203420550010316241c030482a000c608104140c2d207040030b5a0003060140c00290307c090601c400c00c0700600c542d01c02414119008402e904000d45403400b0404041c144505000c8006244e501050007440400000c503041012010249010f541542d1070b85020000c161038000c0080c005100c401e41070540c0740603602c00781d8400e800c207480340c0d007000f030154070030070101d000301d9210a000182983c550b01c8440c4507500c850071410301985440200800d40307 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 119032392 1250 119031142 119031151
    0x240f020405061c0e0a1a090c0913020d08030c030103030207080303060105090103240801020c0c0103090b011707080a03020a060b09070c021909020c0307031e0903150f23 74
    0x540108401c018656841c0c1c2a070700381e00b64100c1c1007542500c0e07440ca454018481500210a039001d6166142d0a2244104200d034100c01d01501151182e501c43d80501d8076007551400c03040d846608900440d02a4030854224036000d880034107491410f446680701c4110070b40044a4019082d20000014800c0540c140207400c01000b100b0015411410140b0029041d4000e500b492810160342c0da150b074842561210450300070514a9203540e80203a05c0d031001c64040e6011629000c0f003442510307444012540b00b0301c80c4101a1740c002c1c1c01803100780d091030192848104451110001403080040108200c90f00f40840c00401e0312a400404100d0380c40e150250641c5c0318000401c0c8111107070390400c6010780d00170000c440081c0c0d049403509a04001c06890a18240c450307042001c0041c8007080741202c5000010050034131a01940302c50b0b165814140d150104420143c1d03000300010700103802000024580710510010300006500407401302e0702d02000402b250b5140d20612101c03800d01b041c0d48100340c032060040b50071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 119033642 1250 119032392 119032421
    0xf03110a030509010e04020405040213090e0f070b0705010e06070908010c08010602061306061a0409050c0c0a1401110f0d05010501050a0c150603020a0f060305010504090b0f040201020a24 82
    0x10192180c50140860140320f2030b16051000011686429a80c4d90341264040c0000600440d100e0000c00e510418880b1a805201d444a240504040d000d42c4009124242895242c008103030403410302c011412141c01c182011030b265900c8885610400c4c43c103002c803921404c81640d988a8107450130060306d0035244e00c01210414081580014404541d011076511346c844010f00705004c1900c083e2401e00c0042200764400c2c4600110440c0000202010314001d100f05c07484124140841c1d2506000a010341c8503d0505000382e602c0145140700040c1c1e24848180028a1000002240c0f03102c4200092140e01030100d02e03a102c036001516440c0030403180300e20390151000b8a0214203020350100d01a254034075031031016001415090b0070580404041c0c011101440e409845440c403a03a40305003401003251f07180980000309007041d0007c160740c10f21781304580c0c1c2681c00201c500c180d034540c0d0304105e40e50640030300241d0441c0189400c85010502001415070402c4a22000001095100b43e036841101e1303005405920703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 119034892 1250 119033642 119033653
    0x4030323090a06050307141b0c0427050f030a0503061008270115030305120703110711010e101e08040f12050c0d0e1017010605030a0b09040f0311 64
    0x5503440c2c12041505564030341c02c00c650741c1e032102002603500000c904410980d50400045403480c0e0043c070f010043d9145460411a90320446840c1080203443c2231038080d0809d50481c5a180303c0a01c2c2070030443c40c0042c09001503038000f24005002c41c0c1107034802121070340402c000005100d024240600c500344808a1032400203c541052224500740d0b420b40001a40280314050030620403420a50000400c0c0b0590102c401c5055981c1c1b6000d8607035003040071a403440403124000614428041d0180e0103d8000307a40002d40781059075643c9045089681d002c11f41084108542d0303c4007619002a03805e00780681e0b864491064180b0b044950501c10119406400c01072001d0a200006200c4070003900010f41c821048803044400e94800c4a8500406240b02070301d100703400c00d201c010b9130050015014100c044e10b400014940030501070ba140c2122150740e0254030481f10042240d2880b078809035030040034025000c0740c401800c070001100407900f41c40075620310120b50859020107400c03800400e0070a2071280a1300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 119036142 1250 119034892 119034907
    0x1b0d0807081e0402060904020d090b0a0e120a0c0c0801090b06030c06070302061603090b0711190807020904080d02040b041805160809031c0b01020c03070503072904030323 75
    0xb2420301c0900001e0280001241003651130744c49805540120340795002c00c20007100d060901000707469040d80c0080003240b61520f152401400032503c22036581e6110b034164649030300b80c0000c48000008100540d032840003200c001c95211270a000300750619005805000c0c0d82d003000f60405080c01c9030620020300c6044200082c00c0003d8011031160343c45148903504e080320035a9030034290050401c01c18000e000903902c400300901e0350f802c80e42c09030074080c00c14100c5030109202071480f40c1c44800300f28050714150b02880480700501d8401907143d442842503000b9420900c50126604c2a6000340d00001444140814188440480c00c50b41c940e0304c0907042701c01d01003810010013034260070520002c1141081f003a071303000890340700d01002120a5900c02074a03903000040c0c101c9810000304000b060042c0180101d05c178840300b91400042440070f0700c2c4014007a02e8140d280040d000d0480c1c1020040601d803020400610494104d500003900096000351601c04185c2d00c10400149040398820984402100074025503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 119037392 1250 119036142 119036191
    0x60e070905060d0b0603040803040c0f06050f0c01060b0f090906040204051c030c2306060a0e07030f1803030603030215090709180506070e31021b0d080708 68
    0x200456209603816943c80ba041d140c1d840150038948550758105000000340010064548004d6100381d008056a17803881d80c5034100124041c1e4940301d120000344040c00004c404000420003001207150359000001e11071341d07964140e4078a81051004401d07003407010444440c21705007000107030761140c81101c045140a0130100000d100d0b2a040507241c4410b01d4403000001010f025103c40e13010543c0020140b010f0300c01d151091004010602d0316000d042c014107000c00e119041460059050381c80e400a1189140d4680b0000c4000b056240300c10f40c1410385506140d0400c5c503550008400003406560080780841c11030074044d00d01a1104401141520302d0350401c04000b03408038125040e25041076001c41d552a5000321403141c00d00301200036004e0f01503d424032621030382000700d881403d402500c1c0b2a004910031501c8131080501c0394806400100700d1101540d8021950340241910030340b103000e003800b568410350954a4036502041c10b20100341c205050101076600b08a00503070010030b04402070395500904051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 119038642 1250 119037392 119037407
    0xe0606100309021504091a0102191506120501021201081c05030402060d0f0506090114130b010207080610090f0204060215040c15051206010f0933030b0103060e07 71
    0x1090200340c1d0b640d616034210f40d81c04e940e126201592421840c1c40c0d40e200d1420b8401403001082d0200000b1001158071044c0d400803600041c50340400a6028130204940c480c00802032402d02c00da45da5580d00e0401003408400000c1100700b06008070300040e11850b0341c00c888411310f001a001400140d000000844494000400d42d0712420750600d003540e20b903142d92000c500d66015092071a91010f050950421803590164031030341c0314240490b83d554050748c7e0b8040b03541c132015510f083c00e03400c0382800c0c00388146c00f0381541168420140c184122800c0340e42e80c9403014100a0240c1d41d0110420031800308022405041c0520142060030310403c5241600d0f0810181d982c0b42c800b034401079800c41c418001400e02c14240001c05c01001002c1072200c0308115400010036075840040301e001c29140800202d07203d54842d00540041520075110741029038100906980e800001c00a101c03144400b007110451400c0241e01c0600340c0303030b040352004a104801040091b0981c2c1244e0004043d0210240400c41c206510091 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 119039892 1250 119038642 119038669
    0x120a0e030f0c0313090b03060a0c140c0f0109080c0105010515180a051f02070b04030c0605031b13050102060a110313021201020408031e0705061b09090903030108010e0606 75
    0x103071a96a19603008031038214011111000366110000b0b500203103004042d0404900d2071000c609580d07a698030044c42d181110841400040060710341c2d450805443c1c989002440c221142c00c0440d13040c0242c1c42ca5460950f009840d04546030a00404c410060303880034022580501130440303104d43c110303101494003074140c0550001008041401d5241800540b03d565802d030161001501207d8404890032021801d500c580039114014407032400c0004519150105a41c1a250b120110101032440c2c058110b40541010b413510a9280c0040d49000300d54442c48000d00100301c2034001001c016203050006424004000d0000081130300348107182c13620030b070b8000451360302c402d411030341c543e003074616001080102e00c0508100c544c80d0310008000c1038411001016040d80d82009c0700309003c602c107444184100b0702810000411a40c010004111005a0004400e0130480c0c000440c0c1d0500741c05400040e03d0388070a07204007010350400001031145030380038040c0b5600803448ad0000c00050400d2800326800464000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 119041142 1250 119039892 119039917
    0x2150403150906091a090c09040203070e22150b060901020c1903050a1115040b19120216060b04090c0512071707080c01030e03030402010c0204060b040308120a0e03 72
    0x1850b0800b000a907601c038114403a080b05100388060b40700d11501c80c840ba800d450590152040310410030f12443c042c078880380f1a0744d016000d000218901025200c030114090100f42400182e003440581c4010401e84850805d0700070840080c0c51903010800f074040340d40c0758907154021001000f5810490740c000805c240304503000ea414aa2220055070750345080c002740d400041c52806003901076420301020518502c24040122482d01c41100301c07810091040c4102d10a501c002d860601c4000c0030980d01f51081d10401c003450416860a40e070341300728002207034400503908200404030b00c10344045c80203a11900600d00000d0740d017040741b01d4103070302c1e0310110700c02034403c181c416955050b031010343d00c60520110b13009111455031101d40704100c202150721031865020b1074000b445111815501c2e0342c0f19018080002c03d4440c061840c686440d0011501152000d40c00e98219884a80010709080039070002c10082d03001e50640c60719003059800d10b1450b00000380410907010f05016400940d9000407044908210445 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 119042392 1250 119041142 119041151
    0x21201210b151e0411030403090311030703020d0501090c060302090a090f2403120309030509061602100909050c040803040501050d1506120e01050708160c0204180215040315 76
    0x1000700a441540ba54001c185032450b00d01c803003401d50810846030001c9500788894504005007080300e002c101d8002c0c2c0001d250003810400705480c03000b21642c801014003598001510f0b500442c0402e0154482140c4a0307641d04c20150070301c0340c0b5100390b00c0030304254502580350003038400000c0c800031801e00600c06016921204881210001c0c8d105500500c18081c0010060300044416440c02155200a070b80c04800041c050011714402e200fa14029540354541c00c1c1003c03500001d2210507003200c50a10020600b81480c880560748030080b00030100e4003569019140c504068051090321070180014100050922060004200c080103440907604207203480c40c0c555080741c0006000e001d400c1170002885840e084045440c81c2d214880d42624100e84030140404c1ca5210202c5017203601c2103810000041c00400410071a03d07181c66102d556200501e45000056046d070006000c07100040a080072211101004000b14103005051071484c03800914211b0400d442d580b41c4800c203401c1008854012a542c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 119043642 1250 119042392 119042401
    0x1103010e1e100504050a020102071a160809130501080f01110d20030a09031d01090303080a0f0e010606090509010807050402160f0308040605010807031104020724021201210b 76
    0x401006010b0021440c092180b42480c1c28990b89030340324001d0590042c040e128010920403580d04a49042c010300c2d5074071500c0c06292423407400d00b4403d541c10884803820204810700e2a56100b03400e880b21450420340c00074083d450140c100c1d1070029220041c3c0302a905180018031440d8440060f01c0e28000f0749000420a4001c14210003501103100c005e6840d8044003105005101003140d00c085901e910075100d001200100310905c4503010702c05070800f030018080d01c5041c8000303440f500c003c41d080702e144213010072000e0324a008441501c610f80303400b0711580e540e05420441c2660158503030005000a8920200550420072000d84130200d03401001d0050740c00055050b8482d50202452100540001d20088a01d00c5d518005000e82030640f4103036410b81c24000081506030022803040f04495000b5000c00241c40e14009204c06504921419242c000d0310208007104004050454041c8110241c001641d41c032a00031150131540040e04406d10501048140034003200004203003940c05a00075a52005d036595 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 119044892 1250 119043642 119043703
    0xa08120907180e010c11061302060c0d0309050712080a1b0b010b07020910061b062d050c13050118050a060c0606080105040201020303040210090b070b041103010e 71
    0x1610ba00c0305034020701140d0750500520096011508040d0000000d001c1e81c4c406000031610071104c0c02e10000c03980c0041e0003140c07041d02001e02c80d85440303101400090034001609403907400c01d090b16145c0c80200303881340c1121b010810240008c00c042c00180c4d0020b01d42d1000c9460b072a81a0180c03030b5000050002c03100080c50409041d442c60060320b07602800307022a40da15110842816040120100d008544407400310f5260174070b80340c21400740c40300ca0703481101c150304100c0c000045500c0c182d41510410780d240d0311511154980001441c81c580307200f00700d0112540300345e2100100d0718000c008020f3b4800a00c08440f0820a030941901212000d00e42520a807840343d00210400049034045913200c034450100094881e00090041e2200b401480d041041d1951418400d003640c0c0101e0b0700030700580042000400500d0010740400b54400c0c0361030810f5406440300b505000c9617200c140c0c140e8103003190b54104800c208041a100f44101c0082d0700a000150070345807295650385108240980204926520703051030807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 119046142 1250 119044892 119044903
    0x509090304030f061a03010c1d0d0209040f031404050307050d081b06010f0b0c0a170f031311040b15030a0e01090c08010c1d04020901030f022101080a081209 69
    0x1a0003105400f010a000e25088000700300c0000e062185090801d19052a0715040c4295611500e058881c100c41805400601a90428281d00c2a034400054414000540c44403201c051040384503007100002d001702420007809140e01402400050b440c1000180003986010a500041765000d82d259840c50000c1d00d803411103406001d92141610500c40703c00f1000354400101c2c00d0403135011000c480b4040d81c8642114250307110315004c0a6460780300d502c00d00c0000395000010b08a1085510040341031200b1143c45c40c4541c1e10076074403200420750003190070007480f20302c42c05201c030800e0454080240f8121100030034000101c1d4034102084007004400100400c1140e00301812900680c2c00070010702d100d61400e070b004403406000384041f661030410a08402e501a6030704441d0210301d40e100c00d03988501882000060341c40b44180c241050f071100c00c10341d01d2100c240041d045403040321115403401d030400e104114501c0416400a5141c0d40617000e00b0340441e0010046540130000f1f0f40700310303585950b013034000d62420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 119047392 1250 119046142 119046149
    0x1906081302100e0111010e03030105130209030a06020a080c03060d1403090307031a0108030c0303130501090b0a0b040c0207210204060b0c0604061514010305042a0e010905100509090304 81
    0x542c02d070034030b021641e010032143c2c3d14040c26202d0a0482c40e126400314221040010309211582c400c01c01881320741381006588210103880c0c1c4015280404040c0424117019040204032403194000c40c18039038250304800303615409094486403a0940c500a000101014907850010f4918412071004201900703061048030281e005c09801c90381401da90303240040160810300d80c041e05201071080082210303000801100c107036010a170011801c5071681c60041c410b000c1d03000c104a4956580c4d1000310005200760301d0b058480c0c1c008850005c2d180c004a401d1106503a03600450780b0031034002c07207000e026050102c1c180480e01210300c045002d28a0301480031a0003003202c1d4010320380c3c40c8001302d11708030010740c0010014800d0f8410300301442a0400300407012000c1c0414050390003041d070660460041c55100358066035216000f00c007441c0344080407040044064a0411a088204034208814007413500c0048049005113a1040d04000750710f01010b03d40044800d90085030f100745803c001043d1030440400540d40503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 119048642 1250 119047392 119047399
    0x204050c04060201150f06081f06030209010e030c0310110904050a09030f030b01020d050304031206170f060606030c07020130050c0712140c0114070306051906081302 73
    0x46080c00c0d0321103103040d00a84150401982083ca100083c034200848410440e041c15540a803040d09081c015100440000d118000c400342c85110300d070211104903000001440c0603240180d44020b19400185441200f40c0c038603000f81e100388141034582d00c0014140550301c0000c94001800c01117100b207401c0c03a116901200c0c0e40b241c00c000502c59005099809900114400c3d10b0700109045d80c1001a4140d500002c0d00c2070150308171481321000240188021340d4460700c01d03d02a220034000c02040c1c0d04990854024805407048400a0510300e03030104a000802900c10f0000c00c43e510705280064000d10000300300c80b0356980c010400700116402201c0c0042000d00303411803980c0c0c10b9a00c16a04108090340321a20203941e0402c1d0200d511405804101c2e0307001d6401555100c2c1e41c0c41d902d0310648441c440140824100002088043d0b001c40003031042682d03003d009041d1020b20b0800c113a0040c190355068010500c504040700c002200c410324281c01c8030031588203003441d01550b41c1d11040004804500d42001c3e40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 119049892 1250 119048642 119048651
    0x706200106090f0b0a060915120c0f02070f0b030105060c070806070e130204080a110a1503151a120606120103050a0507061407021203040807060206190c08040308060406030204 77
    0x41042454211042070440382008201c0b0a156804109000c0d00d1403085201088147d0f070188461b515805d8001d1040180342030103982000514205001c4a228003070010001e00c021014a0702141d0605c000c400402044034034402c800d08148461520f0320061052030710a0000181060014409200c52001090010141d0348140341921000e4400b0080c04038662042a00a681000030800f6100340c4041c0da0300d030030045c501c0002035034540000548010b40258010400c8000061104807401c8546903a0900e980106018186003104c000244181e049110343c079014901c0416408000001d40b42c020306110b00305a19600c1d454041170385803040c4288041005812800401403000c00600403446910034070886074503e81ea044100c0d8034029617800f10b01300441c20407100000d071500c0310403404680d4808040e240f03019074401c03c075407408079254011005604a00c08000924581c0388882c2070301c0034400c0051122522803103000b080070100500003407c0c404003d020a0305074131982c0c8100c0c00395030b02410800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 119051142 1250 119049892 119049899
    0xa0e0f120d020a0c0602010501030b0402120109020603070f120516140412080c06060f060324060c06010608090a0f150b19051003020c030708030910090b15030d020706200106 76
    0x2920b40c640d444041d44d10120581c000104a4814840c15040300e0b0480b0780141c0c207880780c2d0300b040707070003002c94507012017640d2500b12000250b034a13400114060030813074540740b840038607290b000b0b85032603986402c01001d0361805041040314403500302c814440100c01d10b8011845e078200c60319a102d03401035030482244100381c90642000c01800000402e17403000300740c084401a5481d1030802c00320041d07003500150404428404903070403040c00d02c406044005150401a103140140012030055007066a022456500040c010070419030400c03601c0b034114440340003801080703019450750002e80e81c1c0040e0090817100d9500c814441c640c0d5a51101c0304046009102c2c4400340250640c094228880380255403042c1c00d9110290000e0340a8402c0b24280c0d40f011014504140440d164254a5040203203541628014120824894003684c41100d0095201d22000b003503d00709540c448200216511091703020b9072090101d82c5180381c0000d000d030129055440d00514540310880c0c4480c00300070048a410300e0750300301040030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 119052392 1250 119051142 119051147
    0xa05030f2505060a0501150c06020f0903060c04050a0819081605100c1103091e19030501060303020c01050c03031b040f03032c0d060f060f0803070312020a0e0f120d 72
    0xa50184e24004070078001e0342d803156014041e40f992004036a0101d48a2000400021083d801803c0702d49881c09245092012900c04a8140f10b402c40790540000390020f001d200790301d0320500e280c0103016403c00800c0074500110003a5403002c1c08100c054058040420010001001410003d0b1301c1540710041c3d4903440800e542e481c0c0604600c3d11a803011a122075920b0000c004004196489510f00600c029122803043d000d0704140c0a0440405421050f400941c0580052203414038000707511900c000a1006d15604000f4104091013400c581000020400040c2401c00041903a400a40ca841c0c144801c15100040303801a00c03a582c00155040c403c054004140350300040310b0003140015619100303c643e2500c00545071802000b030150740c810391414101011401d01d0340f22248212184c170b8005469074407502c0d520b0000c0495400164940d0000607070008042c4d1084245040189450096040211841c00989014140f080d001d000e1500d4001d90005c0d82c5c0c0d03464085140a04420581d00d0141207501c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 119053642 1250 119052392 119052403
    0xf02070506040501050906100b0d02091f0306050301020f0304060c031b02160f0e0c0a020a051b030c0d24020d0e152404020a02030d050c03180a05030f2505 68
    0x1070ba03155107840009550b2440118020344581080c4c05924402c03420b20112700d13240e401c42d822203060564248041400c40e1513409200c58803a001c01b03008954802c10f6040101610079580203107000c1d0340184100400080407000340ca810641c402c402003040c04c001c0b081100144006403d000358281d640c05d108142c2d17500440c0014040f001100b4140809456000300714050401d441090702201444000408030000c100c0500740801c40d510546042044580300d1900e03164800361400522012829000309919003000800250300013603c0e070352040d540d580c0b207004884140038542c0c510000e0315126001d84082d6681190304a0403080000c0094803511805180d42d80f1141841410000f07a01d07001ca402400294040c500c20890012112418150b10046c0030103074200780105015807009000250308400310303000341d603c907903001403840da1a0316205900c5121a000128490b10300d400c142580c2c40403401c080215002c1c0d4801191496403005a404801c40d0704000101d0800c0ac5c5099000040c00c12902081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 119054892 1250 119053642 119053651
    0x50f1507021e21061f1a0307030518070303110106030611040927061505060a0f02010b010504060801030b180d0314060907020a020907021c0c02030f061b0d0f02070506 73
    0x11404107080c84401804042110a0301e1140c00d42d10044c0012540c01888229055601c0d0388a1541c40c815550100300e001020303900e910b07080c195008020046101d506125407548034034402540790851840350b6000f40c40b007403280405001c000a0030758290000d502504000c0081da0300c030000b006000741006045030307160040e002d0016913504003604886000c50540301210f200e90300258200104c2220368408004150500c14070001c180000c5000440b0b80d10600900321070607003603c07258202e03000401c000f800c58410491a605002051106018560303101d1021415664850104103a5440b4004441e206075081c4c000101035116802440e4a0aa8103400008000c04641700203061500e0310310401500f400201d620f0001a8045810000549020b12495810007090300564604118014801c00c42400220303240c0e000c611030900c003400b103080c100080f00d9407640d070343c0c060321a80c185043c14a00745c83c500311000c41c481c035012544403c80c02865204450308080200110354840300d074079100e91200d20454 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 119056142 1250 119054892 119054899
    0x1082e03030201090c0501080601120203100b0a030f0518071403010e011104080105070c080a050a12180b0109020414090408120a0c170103050303060607050c0405070c02090a0204050f1507021e 84
    0x5d500260341e5019035180c1d0b004000584607010040410320501009410003800d035961142c640070b001841c21841c10040690000c0c0307940115600d03002d1402c1105581c00a808100c08004041c0c0300c1383d01c960003080d10304c144c920000c424074500c0e04c0c00001a001d460b09000544255203070542c29070050400100a00407204080001d02059450301e000340c8941c910f034100900790900400c5040042403140700140711015560400c040111030101c80082190880e00304500a10720b2426582c0600120f00c0001c5d0050410503010341c80c20b810400c4d42c1c2c0700c02d507074040d03c0e5004030000004542000410b00a413103c0250724098071180303260544082010b003086c1c15a21002c903c0f81c40416850040c0d90203c5030503a504103009501d03548402c5c007448410390105109031103d0140a15070f1603595664000c0c2030148980e60f4030821526242e004010301c464010b08561301c2c40784100001c01154848084c41c0401c000e0072a03040c9000310710070b44081054410f44400960144041c42c904a40c0390040c00e15010604094 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 119057392 1250 119056142 119056163
    0x4030819060e0f010312030506030a0f0303180c090b09060a05150d0504050d110c1e0f0301020403080c0d052502120607080103030e06040501050304060908070c080c03160501082e0303020109 83
    0x801e1f400c4560a07a004c0e600340d0008501800401c040b03e1036540084c2c460b20b0005031501c1194400c000604814008490941c4025020000300c9242e014110b00c6c4101100c1d400c089040c0300001032151030162054034080c28102c0d030714841d840e47c0442a210103081b2840c06205900e044e240c01a203d4003c01100c00210b0070740003140e5801d41000036a0003070007001400c0038607540b07039128041c0c5012014014040c0e10940d96000d0302d01c2910f00303001a10007140700e0303032500e41c0351048180400c1c2014000c61403c0d0420500384031180d6124000e10040c91080740c51441c2d40880050343c00400c81d26051600c984d2001e02c9a00107011a041d84248903904032130280d922291040040010080c1c1d41c41580318a80c00100c0c240080380100d440b5610900040d8070401d4428a8410242c0e03030070703010401c96403065009070002180c02030b99007810312002000404900b41009240d080c1400600844005040d10400d02030718880b100d8040700308002da10141500d195580b0b5080d580c0e18009019040c5c1d48011910030005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 119058642 1250 119057392 119057423
    0xf03040221030d05060310060b03060f22020901050702100f08010504051501140d1103040606050f0a06080a09020a1203031109010903030f050f0a030905010b0904030819060e0f0103 79
    0x5280110740e00700001d402841c0741c90350042d022800f03800c0107080780d6407600541044605500461143c031005062007140c5070f849141510411050701d01ca050140d01400c0043c941c44d0032140055205010420303500001a00c031111940122030f81d00421100940080b2105030440999400c0350b0050703200003403a50f81003466038a681c1071000b51101035a05010301c490050381c41c4100e40c02540a4600c20b82e02c00c59990805040001c01c00944200d01d0084840c01ca0010511090003135a00070301c4080c1c101560b03900740d641e0baa07002165a2803124800d04c81000007180101e0304011086d08500c201d0381d0010b000c201404d03114000803d0010440e80c04401092801505c3c004c11111001914501c040c1611100c0030783c0d141d038400740c49840a00c00c008080040401181da0501d1403c00502800720450360005103030020391401e01e0031203c0301d0b116140308000160070080020742c8024555800b074034191a2411b1500006000030144c180703600803a04450205e420041c0440c10602014100c90144004d02c120104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 119059892 1250 119058642 119058679
    0xb03060907031109011103070b0a0b01020d09080d030209010c0507060e030c0f0f01050309030408010212100815180a062909010803030a091703070c060e010c120f0902060f030402 78
    0x141c40360341008003205000301c1c1c0f01c03076000d51b01840c8407a4002c4256032400d01541d844800e42c0204840d0245115078907884040d19503410017444262440314141070003c1402e000c011941d50010000100405400054688103a445902e13401e04095104044903109600e1700c40c00b800c4c1d0040418018000d11400804030414170b81301c00180122034000c1c0940e030002c0c1c02d480045429601c018807a481c548003c10000424040910082200d0041d011001c003860900200203041255035600001c2240d00420701070030904c4031a0700d0107070003034513418000d400310016032000307410908a801c000d4812450318000d541060380440403401040c40c086424107499845030200300c0d04903020701541d0441e900c14000202501c4155008506281c000e403843c08820381c02000340c581591045500f500060402c0300740c5020030840303000e10449103050000034003801c050190010b095840c2d038003030041d44030307103d840c1004100541d9200c088019001303000180c0c1d80c804001c1c00720701c69000351400c038060400e4407060200c042c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 119061142 1250 119059892 119059901
    0x10c05090a030b0c0c0d090f09021c09060e030f18090915060102010902040614031002040b1615090b190c0503180705100207060201050a0e0c060d06030c0b0306090703 73
    0x40040103500ca0505584603100343e850004c1a1800f070507401c010b00c811032201008880380d81c101c0c80e9550840242004013100340c5003801d40c80340c202d290040c0140001e038942d0110540041c441d491740001d4440c03490403c100606105200c424060000060305140001d2141c01004002c11001c80609202c9698003070101c0000f084529550b160007806407010300a0440c001223400c58070507c004204080103400150403100075a005450116a05040c40d4a41c10b01740b12400c01d4120b5054218201860800400054803600002075004a0350038a0709081040340941880808900c0300e080094074003618014504a805640c43e400d40903c1c8100b10384210307058041c00412410715a03a0508540702c5035124000d4410300d100c914024054410041400e895544e0000c0003140150b004184032854a04083d08448020340781600c820708000441d60b0505000507030105011060300c806995000d00004000204000d4100070f0041c0100800012041c0c0c604003d140541001c0b2500760700380d21411010390484 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 119062392 1250 119061142 119061157
    0x13150204051c050c360103020909010606080601110709020c0c0a1211060d0b090f15180103030810080a03020312060d11150d0f0207031e02060c09150c010608010c05 72
    0xd51050120380340905002e02003160800042d4528910a00740c1c01005c03581c0c040710100700c01e400f1010303401041540b602440954020002c80000c000e60340c00c01c04003c08982c0c1c000c1c081c506200c0480c8440314501c0302040513000401340004215191008407140d01e03180c5240b06901032042144c5040070079001c50702080207030744030707400008110b810411078203008003500b01c000200700950f40e6401800e19900d50601c007a20810007012025214901030318020424184000d005000720900300a081040e01d903c00007605503038040c01c24518603581c0548402c600e40e010740080030540607001d000c004168000018020000407030300c001e070303041c2e5420041c400c1c00e03026010058650484203510311481e0910708c100381c9070380070075100d103500d0710189032142010388518a40221846500203047d00505d036100314444e084140c80c8040007920f144281000355102d00103403410350b049900082141d0980e8034408105400e42c16620703550f4888002120301c41c000c0c5014803130320440b5400c00d40001801442802182c460 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 119063642 1250 119062392 119062403
    0xe071805011407062d091109090102070c03050610091a040f0f06030c08060609010806150d020907020d11011104061b0b090a11010c0803040b13150204051c 68
    0x419160800459940502c060204800c040410146010840074040d50040b150300140c04940460340708820340d04400070308210900d5510301001100000c2100503c4900e0300d4080341c94401c95140c070141c8074020b01c0384242c01400303821100710010403c80040792240c0f0505c03885100010540e640c5d4030345c4003a10072a0048800b000310031520000c961800b9404108428640c0d000016609080c245000881d02250825108556405000c0203030f00c504024450348101e060399040550b501d082c20056440c0400740224040d0054040402420f032202501204581c0ccc00920030072007410f20001c040d4942507407000580000320b9441e00d520480c601400703100106842c01c40850700d80380c6411000c8030001001001c080683d08091180c4000c911800d00c400d0083d000d100251103080d61502e0029090b44e86a42200e06100c224001b03400443c130020143e03903202c0d4011175850662f40d280202c00e61000044071000b030040d0481340d141a48401d16501800c103843e0300780c81c800b02c40313440480c0110f124810301c1d100624 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 119064748 1106 119063642 119063687
    0x20f010b0d0507030b04050111070602070b06030c1302220b0a11150105040b061b01020c150408030705130308040e07200a120c0605010f0e07 62
    0x400308044403030388269115540d4150300c8a0482c40041c120b91303901c00014007072140c01c0d000045040040c801040e83e82c0150710b0980020340001c072056545038030540001d050303410005201502c841004007802980640c9403032000c048d5004200f00304034040d0720000d2105060007006810050110606a0360b00c0d6008840018a01680010405466402000ca0100002015120303e0560340c4c03d0702c02041c2c6180c40c20105405100c4e10300a001020036076410b464000206502814215076203000352480903c2d088031490440c0f01c19280900042800c102050070540183d00600e4a02c17100c000c20382c203142e41d07a1038401580c1c002c7d9010010954482080040c040d80c03210b0384c1c005071002c0000780e440038100401015640c40940d20001c00c04002d58486030445400342052010045e40b02c00e0610a540e1600b001c4c41e03d0340c401e03105101102c4500008a2201c038007404c0070310b8410b0182d040d230340c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 118884892 119064748 := by
  have h0 := BRFrame.cov_init 118884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 118884892 ≤ n) (h2 : n < 119064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
