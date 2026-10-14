-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2534
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:59:17.870647+00:00
-- url     : https://prove2.me/submissions/1e9c3004-0f7d-47c1-bb76-ed1b804ccf07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 455575539 ≤ n < 455755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 455576789 1250 455575539 455575579
    0x100b0702030118030e04061a0412020f0603460209010e0613030519030f08070905042a0c03080a0c053001080102070c0902030c1e0d0e070e15 62
    0x2c503042c1300345da64402e008011420f120a55009a00c161b4900851040c6400050848419203007581c4440f05c109952804d1800010724203d50341ca09190008400014801958407070b105020320309803051217a074842400e590b05911051041c00d0012030894a44160455185148d002090781240500d011859610001e0016509a004103040503082d41c5501c420400c1080900071481c2150940c003541c100b83e031054030040c00651707400001004000d04d400000d0421401110440040c1038080e004010340054181d42c01c80c1c50603006184030004000c0323500035562a02c00e03694025031941c10b0382c4100e125100d0075003800142150780c0c001e60501c40f0621008000c40d110107405c1500c000c50341e90f00706021415450512080506070050b1600364010402031011031021802c40040700e442490050f50fa43d81d02c20003a09500400444c84070256017400c419030920038480281075181c1c1079100070051103030483c0080c4c3c0d50300d207d0b1060307113103107c003240001b00410f2110740c02095019018003641d07069407881111031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 455578039 1250 455576789 455576831
    0x18121c020c01030f06050306040f140d0903020f04021804020d0204030b040b1605120c0d06080f060a0513020d080c0c03160f050a0315050603120708180603100b07020301 74
    0x1000592203807401c0c50041d80e05006811501c3d800b68010465142800c001c01c1d107828004101818018010440008000400801010310b580d0707402910100050048000c2c4540130610090748a00d5030b8469441c09460f003442240c400650b0146000400da00705820300019410001900702c8040d82444000046004404400e1243e40300e12903003180361922404040e4840c0c64408001e04105040c4244001c03e031402100c203810654582040ea02c0382d0b6400d2400340940003e4001340020700890b0701c030000c210b43c00900140903429807141402541d4a02002c4040c1940110002c0d50000b43e10b0030801c0494503080c01080d89894060aa5000035401004030b071406801092441010190300010422200c9424090018013000c89421b0145851600e61503046442e0750800a0061f41e10000714a450b60200726004400365021145d80d00c4000701c2c02c260840d900304500d080180204c51020201c42d241c0101160311400b0850180303e4400e0401140c03a4107a0010f80b0104e805660340e0410a0519803008446 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 455579289 1250 455578039 455578093
    0x501080415061a0702030d0207030b0f10031203020d050f0603030a120609020408060709052707090e0903040e1f03031d0406121101030b010806150706050108070602121812 75
    0x83c40e81c2d1902407062501c0d04000c00d45040440d0400641840000d001e001c0b4280c210065140c074482130740f14580c000800d0541c075070000700301044a81e035009040350550042d100890030b032181040b6030364a4055183c0041011580558582c008200c480c50850140c0301515001c801c21030300246c082c0e05d4a035a10102d920503000072415611400c10080c006901c401e40c00003803c0c05541c00041c543d5100e40d000080100c26569403404500741c07001500082c0f241e82890000d04000f600701c041030905401050b12580603001d85510641d050f40000c444030056080c0e640e00b00091040301c011249103840454920f51503007012003042c40c401120721065aa10301590000e04500103115015401500e0040c0311034004030f030042c0c1498100000300210baa003180545501c07020544072004164a0b44484c84581c0c819058010555441e01e40085580c2c0c0e000240b0606980750358003101c40301c00714503035081500e000320352540e210b2401c94a00d04d03002d0700b00142601c0101512400712603c802d00c06c4100e0852000c44160 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 455580539 1250 455579289 455579339
    0x1090807021002030f0d090f05100c0f32070f0605240a050f0d0c090b0f03060c04090f02090904030f260a05130b040c050910050108041506 61
    0xa50000c0d0718200c0644050408140003c0d0300d03041c540040740300f4501030400c0442c086c0742d03203402032024001710780c910b071144940c070006490021480340540c0c0700400a040c249800076180d075902d059503078007036003084500740d14403190a02401c4145c070300350003010004520507114a4092184d980020007100f1585c1c8951b10880021641d131500c14241010640f0090480540341001403140600340c80b001c0001c029039400b07803032802d00e02c0b00d0100404d0b002607080c0300042451a041da80062440b005500003182640d003220301d0390301010000209a0303210b000752400383c0882000c04c402c00c0940025801036503540800c0d100542003000d40400940f1024003100c05a0218001000c03032180a50301403d1100710b4038191409800d035107081072050845010081030b40c4081036580010603a02c80300d0401d80030b515540554149150302e4503291044041c1854030035a40580350590125601c200f003604c05d00142c0310103946203051035603551914a0f290015010035006283d8800c008680000d0410740c03e0f512503101c0f11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 455581789 1250 455580539 455580547
    0x10200712030c03020a0e09090106120f020a060201020f040e1302060703180603020414010804080f07120e010504052b0804151701030f0807080904050106080a0c0f020d0f03020903010908 81
    0x80c094180c2d1054a00d00d01050302c1017003001c80d907036001103481c030b56a030040d40c41c40526907030300115074014910b5400c414484c0f90b9403400c1c0d000f0800b03050102c52050744280e456a5956580b43c6043e400c3c2d028041ea0304503120001d020600081d51050710003070740241814a1058052865000700c0c44581c045003050b00001e4004600300c1d22004101c1c15500108100d1400314501b0386044d14561680d04c420b4001c904004000001c2020720110710182c850707140702082c81c5030b60703010a0b01c0c1460032003100c01240d2020503607400317491800f0340c000c1098804a500c042d00011030700c0c8061100404c5c541c003800140c048048606848001f0501441c080c1c0041e2000344030007981c80f442002c0c041c01d00ca250201410031100e00705d00500000c3c031005100c1425551141030365071110103d00c0c10389414018041484e03003180c0ba05000007440c541c0700d40e03640d008081e06030742000300c4a810391045070512500324240002d0b900c407038842e008880c070412a4484000d454580107062408190000742900c480c0c3d0b900b601c031200040303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 455583039 1250 455581789 455581823
    0x31602060f0606190c1b081911060a11010606020c031608030f030915042003010c0914120a080a3908070b07110705040e102007 56
    0x8025000a501280080c85140c6080020158491088201a0718040d130901d803480c24058409500103e40c00340d0903840c010340c1c008810340050840c2c07248202d144640d81004d0aa001d0000c0d858115603005018440c8513012001440780c01d5000555000800800e045a941966000e124103400b40521342d010b0a48044076000b010320b400031080c1c1c00341e00710703406548c100103160b000011038180c850b4118090303840e40d07104c115441c10441807480c5024245c1c41c1c00c04120801210102c07002c01021803c0710340110302d104800f030500304c4041d0209507012614008052018001c2d81380c0d201c2141e0300041c64054401c5000c2c00304c50409034580782c229243d03000490b03405286604001c1f10b442c1c40520109005100c2680c01c0c01d03902071132201c00710800c4003000d0165402808401011610991b4000c0d007009518103103c0c4c401050001c2c110104082d42c022505c021500c0e00e401c0c020f05102c12154001007101c0301c000c80514004280150081403024000100c04421090800c054032444d8050030021104110341 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 455584289 1250 455583039 455583043
    0x2040f0c020601141e0d140f06010b07120c060605040c0203191704081e03180d08070c0b061309030513080703080706020d110d0b0a23100c08031602 65
    0x40c2c2046507280c60054118001d0b40305c040c6030182041051460b07824007548807011070140003200d42c2c00b80054506c62039100004a001030f40b118a281460b045504981e41c4001e4041700e8095114000c04100030002c0035002c15200b05641091540621400240070360340d0710000d030845040920300009a0000300b2035402055480c000360b44201043d0034003d803200d6030301060054001c001030004055030400300e00c0f030800c8888448080107a07240000b4159a03800e2034803901006100c09640d400e00c6209081c40000c03968410703c0103a025080e0340e124030003154010b0351144641c000007056507800c141c40e01e51440c0004030710301848214038026101c85549001c581807102c3c070310300c281d002214103030301800c01000010110800c50b8080e940040c401601d60001c00c1300c0702c020701300c2120003401041011a02d003c0c0b0b032402d42d10408820070112040c010041d5540383d410304111411035030b01c203242d5414842c40301c0c03810300341103400e040c101500d400203c4c014643c0d6000701e1504141c840007603001446001a2600e601 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 455585539 1250 455584289 455584291
    0x1f02100b09041e05030d150e1e070c021f081806040807060b0609040c0f0314010e13031206061206120213021b06010e0f0106050c03041401090302040f0c0206 69
    0x105070340100040c6443e450b031145001c90b20400c0d038000f16048240100340a414026118120a0001c052000704032100c8040d88140003805524210359441000c6540d1804c480c2070070702e030400c482502d46899618548140c5441c00c0c5100241c2e006051100401068281d049002c1014103040e03c4810050401c04d801c1f08003d41030030b00d21001c1d54800410300c408104600140c400d400c3e0b1201c0c004c20f00401e02e0000c41c180d4001c0324100c9800c14107109480364100c3e004441e050840b841542c00300320030f510103c1403191040e42880744004030074200e000718482c1d03d6280c0310084514001d05003242c51345084584c1d0001c464079680071100007081044c0d02c054400060250800070400e01c2c055001410141e00020559400c6481d0100c185038005401c0e042c0c50515550036603d00703009001d403074581d81c4d42c01d1014a503c0040781e10070302e4022824000300d4564090420b41d0031504000004505060070140c03001100300c0202209810b00507051030010042c1e07210f00561000c48000540440c2001850102914200c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 455586789 1250 455585539 455585561
    0x5090d09030309121103010911040f02071703070513180f060315090c15020a050f0601080604080d0609020f0a111225060504030203121303080a0b1f0210 67
    0x45a00003000403e40c41440c21040d26840c9041424031142880d00c3c0b2011003108210030341550030319400000f0b1100019640c142c1e08030640e000e1003c07040e40308644c2c00b00c3c480c03e00e00519000042480400d14600503001e5503000301c05013045403802040301030006500c079207503100010b18215104007682242c028014206514001203040c4122421592510010030031885904042c45d83c0c0d05641003444105101c0c80000d050205008044204080000351541c4c411802a41c5a02c500300c0d0802d20800009501030480da4403201401141e200c50b51065413940c05040c05101c116180c0601181e43c1c00780e44001c00c03402052422107035444400e040085c00d501d5403610f40c440c107504092a40d00007030090b2000c403450b046085299501030700310f1020380f07000c0c401d4410001e4102460f2000b000f080580010040650300c6042d65203110903550226140101c8840c4040140054000380100390780d2500ca0304107510a03680142890300a0b10380204d480503a540d940000340060740011550352011109210f1002c2e128 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 455588039 1250 455586789 455586797
    0x30f0a1b03080418061a0406081b090d0f061805010f050114010309141b12010c050f0d090f06060f0503010515010503040317270a120815060304050105090d 68
    0x503146071650a03007405503200e0050313050380e418008102da8502c1d43c0884080c3c516080c43e030640c080401000109500035026000119907400c001c101042104040396020010074001c85280018210501a406610310030071140007038002c2107800024440e0203410307003000001a0b1040c0032032080c242582580c0103004211440741c9400010311180c20100c140da41450020300b07010511110b94a8080801c40306c0580714200303070182c1d04940c0056000301c080886a40411aa01120f11000c402240d003243c91440840c0045031007003013128007031003c5002034088405501c0b00091002a20f40752801030700308030740003226502d030340784405d1201000c0140355401030042038008115a1403c5403004100c6440c800c5014107100020002804240c0301d0030500c1d05007898640c26a03001d06040e800e800d0904190f40b0204c44225080010055461001401103202500030644196001341503d0036a003040d07001d058044601c07680d81001d4415207502c3c0040d400750380b02d01c0c000901c1d03251284d401420b1001a02c40e000c104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 455589289 1250 455588039 455588093
    0x105070f08121f0b1c0f0203010305070501050c03041202150703032f04180605210120030402150c0313031e021012021e0702010f0e060d02090f030f0a 66
    0x10049040f1029200c00da07200554844c5000a000c14a400882060b000c503402d08562855501d20b07038003e581200d1040040710030440c0c48400544560040348804a1198418081008215500c802180480d80043d11541000341c4541140260b6400817906401294950305a84840310130b00e0b4010003406800d000e07001300400c0c0c1e80b441ea1544e10540c814070310410308040b11902070302c41c154031220003440010007801401d80341c004c01012036240941e0725001e41d4a0084408c0022903c1c0c4c40044419002c081042e03d035617241d5007080310002a5101003c8828400c0c40014425103040004180020905040e941360604c2c51070240c8418a44400700710359084079a49142c01a110313042840b014030101d00340b5101e030f400501c407480000d0042407204010b040c00c0c1d601161144144000a1140782d0003a40c0f501e20300c2d11120403c1d02c1c66003903940d290350010b604104010320495154003608200c01c0c01050b503000144e206001a203050280c00440d5201d8000b24107041c1000302e00c902c1043d01c1a401d140000e55 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 455590539 1250 455589289 455589331
    0x151302091315060b120a06050306010303020d030c05090d020103180b0a0207050601050d0308180115090603030e010206100909110d080415080402010804020f061603020309010e030318040b0105070f0812 88
    0x3d8014043d2280341c0c182c01170089002903020f900008041d020181c100d984035a1f407400c0082d82ca0405081d020003081c40c1c400001e05441c4907104884100c580642401c0d800511940110001c140021001418094103a905000142c0407280704d03005441e12f003c0542c0302d1000b414068141401a400b03d44920380d811074150001e608031060a50104114522800c1c0e444a0001d55001d0b001890990001c642411408260200305a0102c810740e07020ba99235100030120399005a82d15101998064081c01c94504108a0144a078000c0d8014a00c50104444244000c00214a0740110034004540c401400b04040c8000d02c2000340c03e813000b802c20328000e400b41c01c040c1c002908407000a04081c0c0200c0c058607091845407500b004403500010700030301e038461040710323414002c0d22500078040e040c1c00141d41803040746492070004103451000171145100b0000010030820040144118100d0905001e400d0003402d020900041c03100350780c1030040b6001d690759007820325440070540004004910041f00380c01101d0f1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 455591789 1250 455590539 455590559
    0xd0203060703090c0b0d1b030c0c230f100c0804030905150c030304060b0f0f03060a020c0a080d060e0601031e0c1e020a110405070215130209131506 65
    0x41c000800303050000e48290942004001181c6540241c3c03695040014081c15100182d40031a07800e0400c1e1106d03403803010382c0d41400c0f000c0d41c01003280000081c030404031010102d00a40c1240c000002d0042400c2c0302c0b11013604045060010307207041e04000c1d400c407400050f0000d095000e00c040c0b10707440313140501f00b40c5030640e80505405401d000b000c0c02202c122100380405448041101c0c41e82d5038a03000c0340d84901d8a0718200c8040d10301c0a420a000340c40118061340241809980483d075074000a01402c3c0650359110890025004419040e0f1948600c58100c00070502d0170b4010300d4800f514890100701903091082c421600f0384090405410146002122071102c01e41560811940a00c1c00700441c4070f00c5103590840391005488110501c032030081541d40500381e00011007429081c4240084403525040304100001c17640201c4024000d60411900f001c96644542143c035404200841c000d6180107003500851154007046500070751200952004005000f4181040c1c210088003500500180d820704003800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 455593039 1250 455591789 455591791
    0x20c03030c090d0602040b07110411090105091503070206150f06040302010804150204150206130305032d270d090909020d15050618100b072613050d020306 68
    0x803030705000104101c4038650f00c1100c0a00c4458016506544482d02c0d440813490a82c0072160485240300d6012560f4a03078140b0f070042440d81030a0b0320440c1e0805801000556103503001c810581d0741325100e541c00702d40c0a40c2d540c02650081d103481d07004100c64034007020f442000d54002d510292040d804c85022101c20754880c41201d0549a084c0b038801b180340c4503450075170080c0008180f51030f09640007182c0880c04542c80c178400e070320401341a0700300c07081c075143d0500741038810383c100307c0290005904200042031007070a241000e00300c03440b4004400c1425010300303804003c11415034000722050314008079210b01c1b170402c0c40c6d180d8101c45802c024000c03618141c20023804104040c458182419240e0880e1010341d91403080000400c0e030011000c0c20030390b0b2400c0c000002800121482c1740306045001541c3c400c600700d140c04501c600c1140a20070b40290414404240743c0d08240c10403a9002100c2245041900303094003e90844220001c0443c3c5482050300c40048012454220a001e441081302680150ba0001003403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 455594289 1250 455593039 455593051
    0x9020d030507080c01060623130e09190506010501030b090f15120a05010e01150b0403020918010e07050f4603080406180302090402150409060303050d050901020c0303 73
    0x166034407002850902144d02420000c00b4641d40703010400140160845440d81d0060b09048d1248030180700f04100401724000d000f090320066401d100c0034000c2480c0d440701c1d9034125211004844d4034114035280d4035506c0750755040c1160142c0009004004558244c002c20500340030481c0d401e5050700c0d0001c10009222402060307034000c0c1c0c5445505006039101d041100304003200000503181ca045c420b041030740c040c2c81034504940342507180003524114400030713503101c00950381170dc8000c520b401d2858080103481c0d000601401e010894200d1485c041801c01d10504940507654405482045e1605082180c00c554140007180a21440d403d0071182050344200540e01116200b405102c100781540619040d80616040030349400000e600481800100e1020707008030b550503a0360004900c0700d0075112140481030321009400019842c04100189098125001e05030510410581459941d4401d8403c0c0c4a0a52054000c20400150341c4400d0f0214043d0562051a5030001d41c9401098462999039100041c41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 455595539 1250 455594289 455594297
    0x60a02040311040908161b0b03040b0a06050310050a291518040905070302030f100605011e030b01032a0206090106080a1e1b05040c020705060f1b0703060902090a09020d03 75
    0xd80e4200524800440c9035075000061f010708071626010b810255600c02d4400b41d40c2d400900e00010101c003014040c40e025038401402915075074429078100e1014280c0941100020381e110f02c40b40114003590314141b5010043c1c0c02c42c0d0701c84400140184034040b04041c15140c5120020416592010b4540d61900e03440c80c000d440005040b9120300b030960800c85160402136040c001ca200292901400081844452140b000204003142c0c0c1d407401540c02c000c0c1d07081d042401c0c85600314044a4036020b98003002942004ac100419070b1110401c6021405034200d498031814032601c1d600c031800301d80c10032400d039000701c0400081000500b0710390240d17501c81041c08010300c1d00c1c0100340460100070a02068a103116400032030030b0250b5240c10801c001d03d036042e000c0c05004a181440300f02006100003200d00c01c442000d002c4a00c0e14800005054281d4001d200555071120070301401e00303100c601013049000440c000c1c03000054003001441041034500f40a000621100d0030405940003581d1680050000c469150030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 455596789 1250 455595539 455595577
    0x315050604050f1c03030c0908030a0804060b1207030c080d0804110405132906060a08152103091206100b0306012d09060f1d0f03060a02040311040908 66
    0xb0000f6201d1441414130383c088074064815908060b01030300b101c0d1000e10b0585481a00320b455400480d5030340100044440001c010f0700200300840e51303560080b92020b0740170300f01001c900050507455183c46a2540102c1c0ca28401d800c04111500041c06888184205440c1c0301d565418280c681e030b900001e10400c028441c03566800410071003032401184901762688042a154012180059190414200d01c915243d01c0c00e400000740c03640c5860001c90f519142503071541501a10b50403014540500405580d0b0b400c80c40c20f07040b24003c0401e1610402d981d200140017150744610700e0003480b00010103910380d801c0b180c0c00042400303106c403040700c800e1040c0c4155031601ca0b01c80e0b44460048032510a0b064003025080341103410f07070440381461401e90b007480c511030325080d9005503a4a42117031508428140580001c102ca08500c0d40310090001c9481a00300040c0445641c1c080b50b03001030700342001a10800049540002c040003040103601001b0844041242c0401c03041c0b0b005c1d142e00e4401c0c850b1511031007a03401400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 455598039 1250 455596789 455596819
    0xf04090c020a0f0c08010c0e01050a0c0512130f0504090503160204060f1715011d09011b050a03060504050610030e160b07050601050910060503041110050406031505060405 75
    0x7284455003070f08401c0c0c2000e96000d504240503541034a020b00400e42d400c0948030701d491801008480310b8200103940d00741c608602100200c8000b101e08404a456002c0d011000c1c50003000f4801600f825003201160302245468241082100e000b04e40c0903038062824058014080764000c03081c0c5250107600901140c20b001d50f440060b000705a1500a40048001c1d41804a4844c24004010b0403000b010030450b003040c60111410340c0102c80901c60000808100d06881c3c10f181d8000b503d15400c020720b4800410380c070001011213003d80352251900c000189012907524071a41e814000c0000520080c1c0e4200040c0c2000360100319804520340d02d8406141d00c4110f5101c004100b0070a56195140c5c80b0352030500e95132220360580b036690082d0000d841e0791285100108151400031002070107075110038100c038015468580c0503945a04000c01c01d07918500d518020140d107440b242907a40500b80e140c0c0d5415a550308180f000750840f6144100c1094a003d1440d06101c540c844100700d4094410072200c48240030620 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 455599289 1250 455598039 455598043
    0x80c01150f030c15111c030b090609071202070b0f040c0f06020d0f020a060509061806010f03020f06130b0d0c11070302190305300309060c1b030a20030f04090c02 71
    0x301d2040305204421b04105182c0b41800814007480c074542d4280180300d030a40c100b0010400c1514a55840700c0040b02050781d41d802840031003405003074900054104002ca8a401000d810100d0b0b940c0810a264401c01041010400b5560094108035251041a604088000303580e041c000350002c040c00509405418003a008021241015a00a806000500c2c0c16184152181c0c401c2e1200241403080810003c41d14501040d098140c490f001440b201462954081203455410070102c103801170000c2151170301c88025600c03010041c00502034510b550350900f04282084a4a1200c44000c11504600b903540850021440900712501112081c06000b51810b031400c102da504c5d840248107204030003514642281180c1c1c034070810700b80b960806168888411402080340700856401800e500301c600018803c0b102c00024103080c0040c181d91203c0c144000e22401c1c03450b480420702c400415440b0301501d441038044200303000c0121542001c0e509018001141030818050340c059511115114850340c00d04502c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 455600539 1250 455599289 455599307
    0x80904050c0d0c021f0c020303220b040c050310060608070f02010f06080619051608040c0e07050306031c0c0b1e011d010801090b01031101020a080c01150f030c15 71
    0x21220070400703c50b900c50007030342d0350007041e8400b08400306100030b070981c800702403164070070421258028503d5070b40c0300d16110420485030b00821007480414403404006c40c0d0b100702c02610541c818401c0c3c10380181028100b500e05081c01e03680c030200c00e00313151080c00720b5030f480301d00d803500b184107410821424101080c06a016002e5151010401844c0800019031000005500303800303461000c143e1030705030f8030100590b0300f0780b5402c6402895103c2c2040c508806248111107059200703000d0355030048450345400d04000f1540c800d40c0c030800040d1011050006a18040c009090400c448807000c030160b81079100c020700880070000c4040c000000e0750000410110b800381460410355015180843d1540e100da00340c6031444911540d00074003078043c03000401c4003c0705100369000341e508416140120f03071035980d61107540ea101151950441c001c0b80c0018002414400181c0050210880045140c05045440c007903070000d55449584212404501040440ca00980000686ea04000e4200b200c0113030981c00da4000207 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 455601789 1250 455600539 455600557
    0x603190203090705010806060c030313032c0f03010903120e010b040903180f050d11060c010501240504030f08070201020a1202010917180f0118120309080604080904050c 74
    0xc00001044900341c008250203007a030710240c0351017299456242c02d101e2503010f059403010f4550302c04c00103c0d0310401d140c58a10311442c86494800c03a805425401c2d5000704005c18020310702010359000500d41c5207400c445c0070280d50f1040d0001c214803203458400900c1da0241681c0b54440640d10103200d180618203422400200d0000f0300b043c448100c661500610081c0c01e0028031514800403140895024111003400d0f040b59001801100c079a40c0c0d80e11182944d110000c0f4180e0700840821660254000a009160081074800307806214890180c0ea188003403425081c41c4410040100030a00c002414021600c010a4020340d8240d1076201620040c0e19241505101429103060b40c2d50019540b0f50541045520034070032012142124010101550315009403192181000c03040740d1041501d0400c50321403036030a001403405094101c0d400060420343c8403203810259010001c0e1181c48189604401460000c0c03045000034511881c0980314030089004031034800c3d120b15110b00100300c401586100781c4074064 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 455603039 1250 455601789 455601791
    0x902030108060702012306191d01090c03090b24090c0309150405030910050d06090b0f090402060412170d090c050303030105060403060f02040305031c11090f060319 72
    0x541c491801503542c2004940e000c0042d03003003110b0480c2c3c2004000f4240034903007030200d41c0c5410351a860108503003504c40d40745010303404000704400200b1402200e0503407500e90351101e0000655040020017030a80d00c1d0414070805050600c0c1c210400a0340b6420f240b58000b00c010820707018403881c0c4501100c164081012035520041910512080000c07801c01140101c04900132a022802d1860a0031150b82003144c0140880c0c02c01d2000341c4003810200740c0a400c050540c507003c4c0c5000d038841c0c107000441c0c880350444440c807681d40105031040c1c101f00442404070740d821260303890035142c998000b4050740303d00e01405000740410f240e4001003181c065000e04c1c1950030011565100d20712100b0185c003c207100e03c0161480380c2800f00001d01d034200072044a041e10300c041e181515103401c0d9143c603000f0380b000c5d1070004500ba60800002020440070f0014000c581c1d034040400c4180c85054202a00740d80960004e04010761f000c10414041355160b20b2152200203041d6100d54480e03481e01c1040d0901810041c81030815 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 455604289 1250 455603039 455603041
    0xc0406030c06032a0507321005010509180111070809460b030a06030507090507020316050c0d0b010f0902070206031b1605100e0114070f09090203 64
    0x90840280750644105a4040080e803410107180305541010101c42d0100380d88102c1010100d038401c030000d041050040240c1082200c807424000214540e1400c14250103000e9a0012039100060246c4200103d5004007485103504081c0000e6410101416450903d0a030b0756110f42e80e01c6003900b06107040324084266580310000ca06001d0a55030204807444c1c840d090810056940d1502501040702d03c5045540f07504c8208060407a89080501080e0705d02e020134181200020004204001541b20b400b0503400400d0700c601d541b506038070300321027a0071101300e07a802c200402650990010564919082c000c20810200c125410900e003498402d140e0385401003800c07481c1c00244012104c0300d604a071403c01924007200d541c0c001c4c0c0022030282001c002d521000400114000d440c181c420723400302148031030036103150510081c0d03400d045803e5000200ca0f641c01c201c0f048071001c0d40502c241700302d24811800902c078000b8002040c040005000b0b2890341880202040f0080c100d1041c081c0b140a0701c1c00884c11952 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 455605539 1250 455604289 455604293
    0x717041a06031219200624030715020105070207060c060207240b031002070c1401050405210c091324020409020309060601390602070b0f010f0f05040b030c040603 71
    0x703080899443c3d002080e20145c0c6074140a203981c1011403001d40b26000381c451a102d4480209006080c0c0c01c0c0d20651a004254655060f603007400548002d2000c540c00700c401e40381741c140107420f43d04000c224000750341150108010761504058141ca202e9404500107a948154ac81c1a160030007490103803003044600e0707000c070142c0034045600484c00c0000407811582c12541e5054034500364443c883d0000e0000114081c10403200311141924004100141006802c15031100003040d580c5520034407440134402c080d000c280c1d0a03102030100440302d400c01d4407009441d14021800600ca07400200004200065024a111258080c03150013208041d01d041d00355981c6aa95008401940044d42c1186140c0210b01c0032422640c01100035003440910289008010710100d248034210074000100c40d0b03c0c40d1010a600e00008042d840184201e62186203d44118149100105400001600a407001010740b0001b80800030354009404111201103901240300f5070b41074003190500c4500b0010030b030042d05002d03000c82 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 455606789 1250 455605539 455605567
    0x8130c08100f060b040b0c070e0f0f01050603040f082802070311030307021f0215010e0106021b0906220f020301060f020c0a230310050717041a060312 66
    0x1088210724070301881015660442403045a80b144503860321301c001000704003c4045900042c1400760102c90549001a503034a65400d0364070000c6030800a620041c00811405070b000c103041d030b4050441a02e00500351318003603030340d40103411050340050a12000403031303034403008090220040000308029413548026803d801020b540d45609010440f405241405d6107442401c000050b0350b80c841c0c0061114600440c0e80c0030f13015013602c10b90702240440c015203600f240a91010029039000f001f0003a40052030750714028000b0700740900e20001007031035400c900300c100e100c0d600d25100301d4006900b240c101d07000c10320720500281c208641d41040a10781d070406241101072500303640030318104c4010303444803444000051012602d601c0442582c90b8020040c02e4103001721507108184102d03143c0c0b00e02c0d8111034284583d0000b454408106c2100785140e49503420001a81e604c000e10b4509044000b0408000382844e9540103110082d50340010b00400240d00003560302d0790104001e00c000040707110790565170400da8031819 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 455608039 1250 455606789 455606803
    0x318020307033c03030c051611010806010318170d0f1409190b0a090204090b06010324030204050c1b0109021008241201020a020c0f1002060708130c08 66
    0x18550320b540304014410040000f011006100440862482424003a9811340041500c010241c040000501018005802d080e1091003218014500c01c40ca00080380e000500345a40140854105030405000c5544250f0f4654108001944003d002c641ca4022000c80724907401a440318100250800101c035410b9040e50307002d41200d00000150140307079562005c00f41ea8440c90111030307c01ca80d0031007090902040c800812650420414000440d50070312540000e800d81d96800c1c0c0540c0c080c00f400c2c040c00190744c0c041c03040c64005100038141c01580001014107072050a0584800b038011071300c0c4d81c00500480c10840458804c228200e03070ba9400300d440310107614003d00801500b28041d0703415180540e9501e0040d00000d10968111010712101d000c0d9080074441c00640005054010003003120011019100b8000380401c87d00c164024402c400341d03202040003640902142c0d50242125883d2040d0403603000c503009034003c0c52420480480c0e11011400c0c40c8020301d41d8000760000e404c031803001c50340690100f814 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 455609289 1250 455608039 455608073
    0x2e020d061e0302100807020106050622090b0607030c020604030602030412020f15180c060d0b0112090807030f050408030f03090d030b0109051908010216021f0f031802030703 76
    0x45405a850454031240c0d0701e1900020354410610028a24803500c103450981e80448248004100c441d96030010444a0700f04c090071b00e60007103007180d1030b1100301c1414484c1d000504102201703022061a14000c04d825104c0c14001904200000440100707540310f8000300c0b4000c680c00302e8210343d203203401d00300720000c070710f101c1014801405400c00280d1400c0d00091410424291044c4500098840043c10000e1048925811049000c0c0d64030940701680c440004e85181c031000030003c540010f4006c001040500c5101c98000319614012824000c03980e1401038400301941070800c1e8103225040c2c0c1e01601c0900a07a4171114041c48009500491009618080e6000d000d9102c103d50010001d276400354103484400104078005800f21204119600e081c4461031410710030039400c680d003161903503615405d83e84001c0c83c2a000741041814141142024507401d10182000301e45060075003a25540109001c072880c00304810552107000190015100e80070755254254000e0440ea0380b07032303170f646002c5004607510300314 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 455610539 1250 455609289 455609309
    0x12010e0706020f060a1112061809070602120f0a05090d060204060f08060d0506220c0e1005030318010c060617100501050d05060a020d0e0f070f06030e2e020d06 70
    0x103d2000c507507034001c01621844646e000350400b0301050900840d004000c041c213520548241d51556040c8008130094060b44400c4050700d42c280c00c10b00d02900d4400310b11400780342c40c0010020b290084105d6070030341d8401000e03454500e80c0c44504400280c0110f24044020b82603a20000b030015055400040d40d0001d00175545411b10a0b40d503010401080d0400341e500a4400d130085000100200b01414101e5501002210440e01004042d00d038060b800704070307404c403d804010940500103120700e854030900080004070021850401d051340d0b015038403032402c9041c81c144075031181840d04005141d0041c01c00f80a02c140300e414001d5040c0c0030786540d14500030312006aa031501c00007081d06d05012031408a040d400c0001031655482d1414114003d500001d080d68240c5d81d6118158007005090150202d12040407004151260800900c41c11010b0b9a5100b041030520303010324949441804142d4007e040300c1e00b401c000c1c2140702d21400c1e400340f0038050340030990144005910440681664003400a40394413440f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 455611789 1250 455610539 455610541
    0x501030c060914010e130e010f0e0c060433050307030e01060b0708070f12121a090c160b0a060609170a08161e03110d080612010e0706020f06 62
    0x1c02d5a080116025201112408400691503035003d034110201400001d000d0454468060320a10b00311501c1c1c08090b19941d444000501008005000310745246050300c0142000411540010f8282c0c42107220700880780d0170301030160451416a219410425151019440b81c0c038500042c01420340e441160304034080303460000c200c140c800f414410394040d03c44d6140c19a28149a6850304040c5400c1500c0445803100706a034040002418880e642a941011b41c645200c80c4c08001c1c44802640d90f01c00c4248000b074031940085071640d581da50701e5600080c03a0040e40f90745e28a90110441d04004005016103403500002c2400b076002401c0d40040e04880304c3d907441e100643e13110350000400c1c41040c900ca9000350700401d04070010030030701001445010100c0c000300ca80036006544e480f084241d0703641a144001e030860081c4090580100002005003556805080100724581c005000b0310405440a4081c04240101c003484032425440200f076040e07254125086103941d118025603070b0068410108590182030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 455613039 1250 455611789 455611799
    0x306020f0417060903030114150a2f06071d0301050411130e060708100f03050a03030515130b03010204170706030c020f07090207080d05070c020f01050f070204051503100501030c 78
    0x4100180940180300113980385929240c0110301c03858010400070703400624140643e00c07406080e07002b045546e8107515803e444000908403141e10380c001c0f5040e00c20280e90103103c103107003160100b4282d501c040c0c641040d5554100b0000703103000c60320b00202e1440c3c2540ca89010300007484220240700070356030170407280c001803070058031003100954444407000748242e072011002c0f800d52805820a540c0c06007a07030400c4654503960b000c04003e00003a59000341c40c160014420b034828142e160182d04e80c4541d01d1300784000504140070200c1c129085100b803144109c0e03600e8030000c455a07429011a401010100d10380d003000c000890905880b9a2140f141001081ca0000010380c01030000c10011b0160201e03102402001e0315000781c03440a0f50010b4411a102d410400c00d0b8550320446104441c02a0016511400d5580840c81800103644030580500d041c01000c1c080009001000802c8508040d03040e2404291616003452010318106507e80300b41d4140034800c104080c22800380d0000d41224080d0b1402d1190565078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 455614289 1250 455613039 455613043
    0x9060318080c0723010504091d070b1314060702090604020c0703081c0c0f0c0501110c0c0102010b06030c0d0b0d081204410f0706020f07050604210c0306020f0417 71
    0xd0850503000c24070a101c10000c8c003895500607400d406040040c54451485000998140a503581081ca101300021500070302145d00041444040c25500e9601c0c031031541800f00083d82e900038000c00a219528034000244580c84603010f4446c0803008400301c030742d090744a1612500da9002500140c03000818021100c1c10000c041c007408501c058242c5642c11041002e42c030456110301d07916001d030350544d203d00f801c420149107000144480d5081d40c2c082d1041055120009094510404e8100d12411060081c0701140b045c00040340d4501d07844400004049a28401040304c824040784050211003010421844001816034124869403042c00c645040c0e110000c0c80d10040300d40002e01382c0103822120340c5140790309215a1500c0820426000b01d9a0700c21405100c0b500c1c01c08140c0022005070460b89108880103001c00221010b8402154114281070402078034041240c111604d00005c40e0b42181407600303101c03007506124050358010009541c0c0d1105807a42c9103c59225118000380041001e40202c101000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 455615539 1250 455614289 455614349
    0x9060509130c1205030f040f05090f190903030b030601080a03090e0f0402010804052e0c080906060f0d0f0c050f0108151306050a0e1807030309060318080c07 69
    0x40848845446030610303c00724103c0b2412241114036100c10001160b5640ca01c101800003011001224448981400203000100d00b002e4903c1e2400c101704401e100003e0091400b03c41c141c140060300080030000c90030110054043d6100346034241c000c2d000003003407200000c40d000c4c008a009880c0e0760282a5034030200300300c68108a603e08074620200e0701080042d8490401950030501030000c43e418905031030002d01e0045200151500c0110071801c0b0012030103198002c0c003507644c00354104500b49180010230551103039401401070703100f4060080850840d5607580c00388514580c018a10f0600280c181c90a8940114503008240c0f082800c840c1003205c40d03100c0d51009201c1c08400d020b609841d44400144200c0d0016080174070941611200041400e880f0320240c8002444100010390140c1040214502105d51211030104140c001090620120340c2000342d010440300c031860b0002d000903032020a9010b00c208403c00a1000788006640304001c0303000520201554001c9030384d0116514a44054054002d07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 455616789 1250 455615539 455615543
    0xe07022e1d060402041509020d06140102030a02060112021504181d0318120a06090c050d02150a020c0a03030e040501270515090403020f07050108041a06030a08040906050913 76
    0x1110000060060030b1031b0b041601503a45545a5000082c2c403031003c4416038011031501000140e0b149810000b4894207143c1d1000ca0b002070000d0752800c10818002500c8160500030550a000e10b41a0030b801c5469004451032240c000e080d145480d9505e4003070300f900c00e12940c00104003060608042c008601030a1455000d03030381292004620b808000020585071201085459503c00c080ca2040151208244100f050310b9118000009250304a498aa080d0000ca604410300a40410103403000507140c103491100b0152020030905d88035800020201e103481105098140c01c680b40030f10020815400940c21002c5d4002103405000c40d0380c030340346102000141c0501500c4000103102c180c2c2c92034441644056045071040103000314104030040840c0d046441501c080b401039100c032000d2070507000705001c80303000b500b02440c00c0106424203032610b40050701c100d1100c07003510400d6404590705940c20030110004581c00050f0b56200c5540e181204028011842175901402856000850308548103600c03a09041d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 455618039 1250 455616789 455616793
    0x160c0f062001090803090106030201110c03030f03100515120a0506210a060203040b190b0312031305100c020d03020408100c05040f0306050a060503030903070e07022e1d 74
    0x1030100e4070201c080025101018031555030301c2000030040b50750207005621901020700082140d40c510310005000da81c07001e880120340c2d0007050030000c0a542c00300031684456511060300d901ca0b2036904143c100c40308903620031f9a0003011007a00c130f5150f4050002901a200101a510788217a582000300c0b426210106c800c3c69001040c24011012035401420481000070101d0440d0000c0da0a9625001280d1003980c060f100e011840040041038000f074405440950320340e40050180803132403c04250741d40002c03180c0504907013003c0b000540304803035842ca03881001e070010125801c10920186400051994402102c0180240380400b82d03864000e008950454904030024440c4034090440c40d0020104040c401080140030000010314400050b102d40203140078001c0000d1a0804512038000c03502c0550040d0f0007a0800c4c001c1906d1607234080f450500700c2c0d041020018481d91118000c07400c20400c0000503000d020072100d4803002d404444500d030130144071040d04100442030301c04014104115890210800c1d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 455619289 1250 455618039 455618057
    0x6060c0a0210051314120a0507140402121f300317040615051516081e030105040e0a0c090c020715080a1a1806030a0206160c0f06 57
    0x40c02c10511082c1800e6003450124180351150901ca019140d241d071140c4003480c10000c0c0040070f40703801c0103107060825140c401030500800d19034030306444a030203110703644400d1318070f250000103615560121903a290405d40c4800051800034650102000904404015850301d41000b01d4003082c1041e40341c04080d80004410390590141e01003c40d038000c84603048007046140041203c48900602c80c09010700d1007004c1c08943e807080414040c0d41c0c41d2a541c80648281701c01c40c160b558041481d0211100c0c680e241304203001014050500003001e10a105414071000c8254924144004844002e11706a40e022a4280103564051645035514164400003512401c02402d04009103070090f03101500805c02801030301c0140355a01111b001c031000030341075000030540c01c0080001e201001d124407a6060021050800070a5542001c13446011401d0002000d030b00307942000c0b500c1c17079404120388803802d0344c020301e0140d40d0003c1030000400b00c0d908110484441201d0140407603980903221100041d1000b03039a5200760 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 455620539 1250 455619289 455619293
    0x405030d1a031005041e0302030307120c0507030c14031c05150102060601120b030d031e09030917070b0f1b011103040b041b171e0709091b03060f0506060c0a 69
    0x40001620803590017542e00ca84043c4483e2400c054102c0900a401275522450068405000514803003000c2e00b8417407502e446800107540040603a001c080d014034100c0d201110515200d20300c0c80b051001c1420502c008200c800404d0380c400110104040c9016040c05541c9071f49911580c1801e031408010b000d60271007000203203903510400300b0070f044106440f404140c803035510000c6030505c0b0f00380c03500000003510780c2110030000921606000c646440040c0070800105c031030710f006003240c40728001c1c0f40740002aa2140713008034400300112000351080c90102543c3e10360540301c200c459400701d41060f140615043c0c9068241e1418811840080e4150711401e103140e03030300c0c0d5401d25603100041c41140d0401e50401c0c10a00c1c03001e8640d188000c1c01c1c0c140b460003128400b41d41c21a14141f102c0f8040c0c03840187e602d150300300030f00c000314110084907817000740403070340180340d25000d1040d0b20041c032458000584000c001040c005d41d07421050024034000410032554a44c40c2c24010644100301000799954048422200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 455621789 1250 455620539 455620541
    0x1406040905100f05070f1805151b070f0f0e010509040305070f0b061c210509061909060329031f090b010e0106081603020d02030405030d1a0310 63
    0x50550721900a590000459a00c0074044844200c6036205940d91030b0304129182c1c0e0170a0300c041034030740c1505052540015100d120309a5404500800f4001d000911940f600000600141c8a09080c407c1040000d009502d880d03594845c1c05d031054144040e403468000031103c81000030701c4240c900c046103a10442c1c0c245401d0040c000c102420031000c00c13804001d541c0c08500c1d4240700c2c4450034450301c0c0044107801c001c0200400f85680f8400c40350303803c0c40003040100003000c109003c00c1500383e1058103240400c4011003500e00e07010f90340d03c85e0b800034000149180700c00700e60802180620b4490f11011803807519443c0450449001d000340b0300b000e0901c40368840f20303000300003100240f02c180182161800d0041148003c5401004203290050b6078071030311406c00300b00301c450050307000d00b40c5510090410340c90000003c15121015110000500c90b942802092620940460b410210340c480c1c20b5560b41440e2a00d43d640b9484a101d0141282c500301d00344581c400c6400071071140304801801080c2c0030f0700c840e001034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 455623039 1250 455621789 455621801
    0xe0a0807021f03090b010e06010e1c1e0312061401050304060b04020408030c06060d0c032009183a05040f03030801031403191b050105010801020901030b0301140604 72
    0x1c2c1c0d000941112955000c040818141d501101e25074010424138a54a0098038100040c0c010703600084001d42004910f9030300c0000d49800030400c84101e10b01541c1c2c03100150342202c1c07946025000921000d03200020791680c0840c42d603190300c00e82d61007507402a04490b4a00702d80b0a80590340000c400e4030616581c0e0740c407840c050341e0024054100055007416190004080b40d001d6400810306400200d01010840c106004040d8004026140c99060f00f50b00e03a40c8030388890783c40c04024a0b110402c9890060f0032050b000710244604058071031640c608046403401c440002103255140944540030503403c0420804c0200e850616180c1c1400d44550200ca00801000b00c1241e45072040050601c0001102e401005080c1c00450090b00c440d00c865045081100380e44d200c0c04070064080d8000c000c181d440c40d00c03007585140307010054517200d00c019010380740341b1a002d298407001410795800c0400110300c1603010f50040100700003d880030410502600d050500b0f03608800f00d20b5000380b02010015145007800d80200d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 455624289 1250 455623039 455623043
    0x60608011a160507060f05090901330c02040c0c030804120201091e120503010803030406180206030703060f1a12060411070501020a03061703090d050102190c150e0a0807 74
    0x41810203020550705040b120103100700b03481c00e51100c1c3c03040003584e410000801c9654060310b020340c070341140d13400469030741403040c4500d04010324400210311300c0000d25089004d10304100314803982d804010762402084003000410030b0f0312403031801003407031546401008442c3c0d48c1c5a06448034203050740c480d101d19640c0302e10090030400307554807841c00200050700d070451036072514555030300f0900e60007842c20321402512500c03a0020a2090805c0107108a004c00030035070364440e5004602040c0000c0703122103041003030500013000350041d60100c103001d016901a0402d2068622880e090609140d6600a01d64080382000e40c00103d00350801c548501641010519580414060300120306038a0b0715080304002d81c45010107585595011401c004003a45c50700400000300014051443c4001d1920039841e100d03c100d03075001d44110a440b074000100b05c401e40641d40c501e1300c00d14840c03180200066018003807003c0e84000722441da01c0d03400c105549614a10882640320b45517402044150700590360342c02554000340d01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 455625539 1250 455624289 455624339
    0x50403030e0d1b1d0610230702060c0607020c1c0b0606070b071d031203010620010515040f020304030c1205040e07052a06150a08010204061e020106060801 68
    0x760f089822210005030703006220408070b04081c8102c00d696100d0040780a40520711407508a150f40c1030b01648618003000d8a804070504c0c1e50700e4548071464141d5842107410080d004a0007256020741c6d41c2005c036510b44105035980075644550425400c02c412520840648101da40c1c4411202d00402c202e0007445503c444054070980c42c062007600c9202100004450704400121004e504010031540c075140c0c505041d03c198010050281c100c0c010116501050065600304040c4807201103868074541e0700f9021071045880200000c2c10301416109030b4804034468980564200f5201c01071440b40c51003201c4c42140c044d69545840c4115035611005400d180c080e071801c000d42800081030318005103a005001d00c00a0309c1c1c081c3e031040b08110700100041098a00c1046250441c0408ae441501191032030b0f020904080e0800c0282c0b04000003a14082e6070380210085620104010400c25044260300601e4a5081e041280040d04180102c2c281c0300e8501900c0005400000100f024008608600c500c81c07039450300c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 455626789 1250 455625539 455625563
    0x501030c020c130207030507060504110a1a07140c0a090b150306060403020907050f031501111b091f0b03010603050112050d0c0602071208070909060501090b070203071503050610050403030e0d 84
    0x40c6e00041d01e90075038033aa03407911140e41c80507041c035184803044010b000c00b4401c5860f44240800b250158069190f010702400d031100e0300d11074008028442c00c40341d400018440110f407511140540c0c014171211050328041d00410402c416443c0701c81c41a240719210042100307107424115803d102e4100c001510484c24050148400035950620303001030341c171903001c1d40d06e81e80708082c0140006085107040040c030072a0f50498004003955200d24030003003001400694401907141c8030034001160760080340041545040d5800c10200ea0128140c0080d4103c0b50665014007107079032250a656118040c4150040444d4401c0114400040c0030b4143d0131030303840c000d100060510300640c0300d64814640f10500c4000041828041002240c3c01c04102d00107000c00c0c0c0784c104541420b140020b400c3e03810710300a03655008008504034045640403c007201c01350441003c48181e00b049a4400340152000b555041d01c110b0091001a01007072044003514200d030b40540c0c501c003002e6103c1c01170084074032140e00c0965007807118071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 455628039 1250 455626789 455626793
    0x3031c06030c03050c04290d14030414030706020d020d140f04080a03030e1c110307060212010911031006050c010e060106020d12050907030b090c03160501030c020c130207030507 78
    0x4820100a41c018000b0340b4899030145c1c10402100e4441a10901110454244011880e0a071000300c500c15030940c1c0c220345565041c141000a40324010070020715110004d4080307005006403145d50a0b1036000c1d030441e182e0f0340e168103050380c03100030410045005a02415a40360f40706c3c80303540303998a101001e0700014070b00040c00d105070100d81d2082c0c1145c0500e90156150008045e0b0603c902d00c00c00c1880c40c00741c100c54000803c41c840d49244a01402c2c00c1018180481049010500480340c016600290465503240c680c50500d211410911604401038a090304509101e02c0c0c01085070311030f20321513042e004101d00788501030740c464210b03984850086d9030b00c01c10020514020845540603291640040140582508004101a44c2007080c3d0f1580c904040c14042c80346000a028010f0f40d80c0103605003141d60781c01e44450718092001d4011a414030802d50f0700b12803502550f06050580c0d4081c2d805000c1311184802c09d907601c5d80e10400c00d0340c02144128081113640d4541c1d0240c55868440d2800520f000c0c82d907 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 455629289 1250 455628039 455628053
    0xb030424020a030605030d09030507050d02030309040c0806090c0307080f0903070b010f092a051c06030f1a091b040204081f0501060c110f0d0b10090507050903031c0603 74
    0x2400e2400402d5584c001800039140030000140c0d40159403511002d0241541d40315615044544100c0b8003950420035500c00310354041c400e6440400f0081d0003013040c80214030300100040801d840b454010508107000c205a050464122031103681582c544000d2601c83e1064240300941c01440b000650100784546400204003108542c000d010300c00e1020429800c248142d000c60300240003004440040310841d201181000d805a0b00c000301c141880e90b111251041d1140c4610440c0140c4d852081c03502d01c001c030811180b50224080e0502614480305a001172409050706084162000b140345e92150504200e0041c6500303010746c01c40710141c00541020f1f922540c0500c3d2422403e40c0070341c541031400c0080b4841407944201c0340100954900030f100c41240e0f446914214038454401409290099084052611059241088158449001442481e01520008506060703004105070310f42010003042d0b460780b1030010781f002c6240c02806546003900c0c01c424400041994400e0312121510742c00c001001c038980c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 455630539 1250 455629289 455629297
    0x9020d05010f05030118020907030204030b04050d140c06041209080706031b02061e0c09130207060609050c040501050c010f0c050c0c0604031703130605130203010e070b03042402 78
    0x44004649541421606981070320b86401c510302903032521132041210304801c8003850040380c0503500c200c00c03034407241001c6000c1c0c403a03600040d24000d060403d000421600045074400685a41d641c26602901c04039400c0092040c507050010750b0f40400086000725800d407461080010860416103600380d51482e4450070300545038415030220359600c0e031171000d495140e070454121203184e1002c0c201e145028295a20301008080140f910030074001d0014002c091588215250002d0003410a000482c89058290107944140001c560b00b82c01c00342c0010f1130441e18060b150013090b0070901d00d4241414500110303506c0d0003c40100c01d080d92640d80918696050b0301c40d140c40c2c0d450b99914a43d4440b40000000e207000380780c0840e64000c860400041010500b00c103400317034400c1c1c0c03d284900e5407900c4950401000e51b06036070010706014684018000b0f46000316110024242c4247d00a2048a064101c070380e840d00300d103115810600c1020400180040c031005804080e038014000403058000c19030780804200d0300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 455631789 1250 455630539 455630557
    0xb0a0c06241205030f030901060305030d1d06190902190b0307090f0f06110109020928020f0901030528020304060e0118320601031106030c041203090902 67
    0x10581c01c14425040030039000d40e020300046180480c040e030b1240d680340c0c0c0e284100e4000d05040b0b1070102c08501c51500079081140256040021644c55201d2803440700014420000240303d08011004a00402000450410311a900100480001210709400000600845441248c0c0219a80c03040f01b05980c000710341c1d901074000030b46003135144d180001000d022071a290b04a201c2410b10751004000c0703000505002d80070798089284c1560030125400c091130140591850095011704050108011942c1c8802840d118541c4265803a400900d0307641010101d20541500700c40216003040444140c0d40030782c02103a00200400ca00821a141404541022003584482100f41d980c00000b400240080c03401102520805100204000690804407a900709420000185540711030305107100c085108011a00e40800e000c0c400004a843c1302981c0b5480e143c2c24001121140354061a442e150f05249045d20f201d019006041c900d0941006500c1d404480c0301c4008404102143d03c01084405850001c0c005d440c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 455633039 1250 455631789 455631821
    0x1804110703020c091b0901140a02010e120f0409091b38030723180a060f08040803090304180902010906020c03100f0e0a140105150a0b0a0c06 62
    0x44401d28009003802d100c001c1291240c2080740c140a12018582c111100c68240850002d580711900001030380c0e64076410041558a04020a000b034601d40c040d08504248020341c0c040c0d680070700030141041128001c0400d1607030307601d00c103210500c2910b001d940400340050050031740c110402c0c050401f4031070098481d0400d60703042081c0e03603440340d401d410b0700e002e10101c1c0e0315580c440351850049000c001d9540001011581000704d9451580c4480350250008004010754900a5540b29101c12181031020540540b0901800c290040090518810200c100c20220907960f141100d40f681d494060755a08080d10800260008100000707135039a851401b001702c4034a080020548049500000d000e07000c145c1c1c003080c190340150394001002d41e0b0200718001200142000041c2401140064100603c40182140c2051040e20501c5c028400c10808480155003003000031300c050b42d01d1100c020103c150701c440440c0c000c15020000c4c0300c21103280303001c2d0002450710301d842084056242c90b20380c10340c0c0b00c402c0d00751100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 455634289 1250 455633039 455633047
    0x80703030e0603060d06180615081203060609210a030e1002122d0c06010f090902030703020f04090c14040c0806031921020105070801140307050105180411 68
    0x140d048480e01d0510710382202da6a046140003000f25440c24219100104516515240c559403000c0c4080544e180baa0448010094004c0c40460b2000c254901c1c000d141861251030f490710f01100c0e050040764860305014007e50305160176a028000308185d605a2045490030840d10070100342c0003080030106184c041da890603d5400140c0901440c02c4c4d402d03814a046410059490550710b0a100c04c0b82c00c0100c010100529a082400151a401c14200110090440005141c01d101a000078590703041c2c03500a82c080b9015a0b075629403d0407100b800000a401d6007003201c04001510305240e104200305000f810116840d509613507846400f1156030041c0ca91102c2441ca19201400d043c800d0300300c2e4520b5810422141e06100000070350711049403040105076080815070004200300c8041c0392491050094800300b10500e404c0010307002e08001c481c00b900007000d5000000c2e4190120059080709a00a006030941600b09801110b003940711080c1000c0000c1080c0360a50107403203501c036094055038076414064903 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 455635539 1250 455634289 455634293
    0x303090a11040207050c01080c0903010501080606100c03020a08031b0304030f0e0604030b0115110d0f0e100f032c03030103020f0111150a09081813050921090604080703 74
    0x41c411084200d401284180300c004001000003618856084003420003d00669881102c030079030b441220356503900740d4206400080c5200c00050b615000b840111050f0800d0040d4420131224070004030750240041e44207000c42004503c1c0b0074000d54024004c038000d040040607249221000e070784266012400150000300081d0503650140e0b200455505c101d5040e890b0618545071401d480c20180071b81400c00003203040918a403401490030840008116055824000c1114000f034580071441d03001d90017140e0307507447c10301c00d6203040d00d800d00d20f1101c1e94440f5603180c9103c1c042100204844682c600b121000d040303140c51003500100000e1000f40a00d8025a560760461040c05490780d10020014140070740d0f045000d05902001c608181c084491800b00d445981e00e142255016003d0000081d00c2c0030030020303c02045089407204013951041c280c48100c12403640d01c01701821a1002c56204610350440d800b2240c01141241e03659a04142407841d490512560000281a41c0c3c404e1784008007a5005240400c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 455636789 1250 455635539 455635553
    0x405030d0b13050103290702100e0f070b0d0e0c0d030507170c070602070807060c0f240902103f060b090102060907050d02060d0f050a0b012703030c080c0303090a 71
    0x300c440d8105a828915041010b00239545103440c0130003801c1151074540c00d90400d40104031080f02400c01104540c0d40c2a9182d000341d489a008000c00042241070842000e142c4400041c2a40c0b81800640041400c0500d41c80440e65a049800102c9500c120488980200f890030006030004607a1240500121032a103000a481c0c004203074031442c142e8103d100d00304249900402a003807110340101e8550210142840d16142e0f80d030030946010514001043d84070500011988074030f184078801c5d5003110500d4958581603d82c0040e03000241408542424880c90f868003059280b60020036140c0348602481d41039111100f5107441f0b800c6007400f090041500a0390f5039041110a4000503a180900002800c24001c540780c0380c05040040d00407000010541d004e405158040e0840c0342d80e01404110500741a160540a409000325440c00901c403140d0100a25065120300300c2458860189500d5141c5903560079039001426220540c0c020105200c50301c103400007840298454602134000e0403140c642454182 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 455638039 1250 455636789 455636843
    0xb0d08180102281b060c060606022b21090c05010c0b0f1008010e0d0909060503030409110c1b0a06080411120718060e06090405030d0b13050103 63
    0x504540c08182e10a48000043c541c59070b8841644800495081c1141030012000c9151060800c6103600300743c0010b0402e03440380341102c120b4460f1600340034280d590241240e561100c40300e100c1c0d81010140c000034028003003003c0080d4000e100d05140035154030180b8035880d0718030421410701006403190100170801644001c0d0101030002400d00140001c0d46072215204140020150004210842c001c00c00018048a08800800303100740240035400c19103158a4442c0307181d103808004168000303008250805680035070000c0e03400142c010b41c1403500c5c0541d0100034001140071a28200420040000b0100052003941d079002642d103112031040c4401814003030081c40980c0100704100c1130006000014401c0c00c4a035881c04011580c2e8031303c031b8610800d450b00344038182d404200e041040400c900308041c056040181100c0b0600390105c01544c584060111305841214010710980080103c00c0c2e03090150f41c400b00740140302410145418110924020071581c0a07041940c0303004042c3d01306481038103556188 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 455639289 1250 455638039 455638087
    0xf0610020a03030203091504060f05010506040518040615150206010e040f031d061b0609030a0c0b0a09020a0b030610030605010e1017270102120604020309010b0d08 72
    0x29084a210160029100c14104a00a04068000011625810b001c0001540030051510003082d40e041510300b45000700b200351031034400641014000034152401030291003c03202c000e030520b05005a0084090010079004108039025035484e102c2c1041c5030540c4644c84050300582c40102001d24240d18083d1405005a020702121042a42040005a5840c180111859050a24440c5040309101ea001c110445454103908101c010800d0489080d002503c2260092403c068401d1b5840d03512259031070388110301401010405004000c400691a415070303560246403800e0000b10a007003540000e6100c80158403017a410440841130180314544040c05040c0210107007006c006051500001030060942c010b81c1342d00c84c50040c5154111a401500c00821008030228610403d2070310100030004100211116028a48105490045402e05100f103c60031140003100802d159120b90401010b50303c0202800019525120020595222246a214294850b501c0c0b41d0311200c0e140400703c1c6042d440405 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 455640539 1250 455639289 455639299
    0x1b180e10050f010302091005040f0821090d0501140a060909020f04050a0e0f01090311030a0e061305120106061b0317060a030212030a2606040b03011e050f06 69
    0x510462042000c0400100c40007691403502c4844031500680007401114403e681010b813684490044503070080040060302e07118100d0700302042e280c0060595131050802c00c031103034030000640071545091181c05004800001800301d81d10200560f01d6500392080302c0b1601e05105844410301201e80258096000a0001c0817410004c1ca504c03500002d01510713541d8081402550740e04041400001d1580149440261100485001c8240041064003c0c45424000e400080703040350b002c40c0c1c5010100440361076000c0f0785e4030503440c1280701c0c003080b2166000c0351a003265400c840307000241c251501c0f92900c02000010b800005c8103450140007a101ca44511894010328a12600882c00030b504610b80c48440d0783d055100d46896500c00000c100e11000c290406980f29500ea0402e02d20a6400001400c0041035681c624400c0b280c3d4900c070044585456000d0314407507880b18002002c2e82400e078040070030381a0040002c90030f0307040b0004a4025104c50341414039000d40395000c2051410404450320f81114059070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 455641789 1250 455640539 455640541
    0x20307020318040b06180a05060c07150c0c1706160203070618020411031807030c0b0a0306030c0906081b0904080f0405032d0a02010519031b180e 64
    0x64000c1d202d02ca5071140200c40d070b0000e01c81c40c200361100da004001c00070000d401280d0310503003904a02e259800c0f00c0903141c030900322900e0116550401c0703410344040c0c01d00321000300001030900903028900820300004c0400c00950b000000040303170f60035074030702e005000707000045614483c0c030007886003480c0d40100007503001c0c07255008070400c00f58000102d501994004a002822a020801d40d64440d001c0c0c11010354070904104042199201d50401540a0310b411941c2070340c0c0e030a0400e00035482e01a18807029101e03850000080220700b401100402d8043d00304e240008036a51070750380e4804100c0480d002500c0c0b080da038440c24043c583c4108403804080c0c90307108017041c0d40c101d103d0000c0c11240004200030402c060118000e0032415503681503901402e40103050b47c4020590003501d88d800c2c20000894035007085500c0340c040b0708803004952156810f8040c2d540e1494084000d11800d01e211444403d04201551000d2040040d00321141c1882c285000e55540c1100303450180d40065602116081b0141d0149680 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 455643039 1250 455641789 455641801
    0x6030501150b031501120606080108071202090c090319110a06080108030a0507021f030b0a120507060509011101050906060301141515091306080f150c0705010603050f030a030c030203 80
    0xb03800d4981c03003070080c1861500d41051000482e814110803e25a0106007055008103070990000b0b18907068503a0075003100c08595a401d4040c2589644500280d080342c140400300e49804182c000402d902c00300070b02112005a484054280f25450908082e03416082400707004c8858036003404030300d000b002d203454020042e50400c480551680306e01e50300c010600400150139803c5488072503e40712400c45481505000041e01c64014003c1d094480321140304100030716012170040d110740940c0c044e1b5a00040100740f0b0b01d040c50782c03d545580c000c0154505203e107624548418000074017074240709024140140041b400c18805160075604800381d00b80036602c000341001218546c884c404242603400b11045610a00d00101a481a204030315038181c0003190102c003508141600d8204070b04440054044582600780000d03d40d03100c495600a42c07000c01c50303c9011814604c0524054404a40110b00001d2038a40e0399503150714103218950304010b81d401c04981c0c1c0c8051901445103030710a60103810107519618042e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 455644289 1250 455643039 455643059
    0x90106020c090f070c02060f120606040602150a150602010b0906030607140703050d0e0307260406050c16080a0308070c08030115020c221104260309130603050115 71
    0x1822690310483c034500150076144145100542d603a00a49006c1d92440d00c9100c4204550220310900c0254044002151144c20321200312000c503141c07a4050b020520301d0b040c03025035641c03000d084480c03c1521130002071505150070145600030711180d0000140048010240641030800900b542c0c86508902e003008080c03070b00013200300000f422040b481c0b0741e903a03410720b030a80c1c0d180030b0420500c01030762422030201010480040100b010501401001a0081d04007246201103c100780000b205c10311709010400c1918051b0000e40b0042440d17a041d0380b9800e4640300d20b8070710840540e002c2c402c03541c003005041c0103258000c940700e504031040d850708441e41459516040c096200c184101d01d01a0111040703682ca90b4401c3c0408602050000c240302803040d00304600008500760542c05000706c61500c1c110449191007841100c0031960000100e44ea01103100381c3d0b00350303c0c0008060361005800704202c1240d044e6600e415442c4581010742c00091f6080c110300702142150038404040b0075003070a07104248035000319 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 455645539 1250 455644289 455644291
    0x31c1a1e04141e040317010608010815040314090402071709091008060412050702100f02070e01080d0309020109031505010e0f0f0c21010b0a0f02031603050f12040501060302090106020c09 82
    0x1025250f0b161940d19080350080c17030229200c114021a4070000c202d15600c040703803d0481d20004201c5024002d800c40885000ea800d41d0010040b4604841500c2004082006010002c50090006081402a0f2921440d5048008203000d04100c0080c500d46d56241c44070f22035400c410310001201505091540103613443c4006000a84819100c1e940f940c0068401e00448000d103030301400f03d031403041d280306010b02100d0009003c4805406404400b1030100c1414184604860707003040100640c142509041d03000706115841a0304102a503c004804603e51240b00b04030304d075440b840040c0c01c0d81352018080b5005005005045d5100e044001d124501e081d6607201c41d005030b218a600d5a5130100d46d9100903040200545000c8031001d110000911500e120019062110885e00d8440882807801e504a0301c0741304041c400441952119a20004070b81720300d01925070307124070714a4280390900140030407060b003004803812180c6a4640d241070045080511400340100441d0004042c0c60350050000740c00410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 455646789 1250 455645539 455645581
    0xc0108092406040f0e010504020306090d020705131d06040c0f080a14030903070303020f060f091908040b0f0c1203060d0f05010b100203180102031c1a1e0414 69
    0x50002042c05070740da0b54440c500c1118807072000c01040d051044450302901d02114103a1081c0108400039003c04404031350f07811a0a0954040d0101908102c04c011404401c502c40c2010356640310300049110071400882d110f00000b00f0010042d0385486d10746454681c40c1c40d040000440b507007a8007007020801c00281040b6090b40a00882082c50160681c5c610f940546120182d1510076035400006050b00825404103600d484c40603103000d59205541e00114036000e03201c03000c4681c0022011001e82c1241c1e050b000400340300e21070031464071340d46020100080c0c101d216101c010010014014152010800501d410f049642d12950300b1843c0103800034068842508002d0071140c420b1440d002007050a512216401500401d03250620300c5800c80290b60f508021051002c402d0050115000d56000000f0b0381c031802c00d001c081e00c0164523010b030f001024122050a003945000105804009607a54402a0000d01c404000c0c0c2c8003940c1c50f8000700026500000010b0341d01a9445081c40342c1c1d036450b4961499005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 455648039 1250 455646789 455646853
    0xb09030f0a120e100f05090d050901080c0c1b01120b01120f0f02070309150c02031c110601030818090613180c0305070509060910060305070c02030601080c010809 71
    0x2240c0d0102c0c0c800541107140f5401c03101c0c02800c199500110300c1d030388a000140805481000746988120020303a803078403201ca65402003002441081240d62089543c558800704038000030b030130001c074150901c1c64181e0803211110b010b00b100540089a50b408030510314004184441806004440d20020b031000e81e0b03d58115a03080c0d100c08445552044941101000c403d150104564a1000741402000c0e20083c0c002d280c81420400c0c4c0d01c0090078460300e4440c20aa4000700079188034807400020b243c07184403003170710107050103016541b800a01300b080c0b06840c0254013504840c1c0d603032164146500300543d00d0020044c4901481001d01420307880d00200e550030b9124048000071823014200806444a00d1100002d092802030400801001000305190b802c445082e5050710310790315007500b0460711000441f000076904660100070000207209401113a040286070800c0c0005200a03004642001c500f600032070782580c40101107084c2c6503842030b5415489144c89018000746501c1144035502045c6800d044145c1c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 455649289 1250 455648039 455648057
    0x40809010918060609080303010812030a09060207111309051e12070809010e040603020105090d020a05151e0f0a180510080601080a020f040303051606090c030b09030f0a 74
    0x150340645181e00180003600c408003080c6503400c50070b502512050042c00d00007280c0e03ca0008240f40004141c90603654030074060b0984441841100b0250340005217070072502c076252031001d070104406100520085024044910002200f0814000701c0180d100f03055a0003443c025603070011440c00700c3c925100000024078001345000c600b07400d40c507140d6802e81d94039000000040800c1080901d43c020850540281c070f403c83e04c501d0420800084a115220103170128200300b0001c8624a021701d038006140744000c05d550601500c810228082035400d540d00400302c200081c040d8421242c94102211005c0b040b03050a00d45928100400280d0096440b000b044c44a040940403030502c000b04201c02400d005080d50851141d03d0400078044941529040d01251454010446052042c002c8030b500780d0041c6d5040c1e280c00d245036411140c0b2b80c464060f0684000b1130300940800621507006172000385018000b52503146040d0300307240d140d64101500344900b562040001d01c04100c1e054003610084989030815202d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 455650539 1250 455649289 455649307
    0xf0c0f030705040e06010e07030b2b150914071508070207120305031503070b0a0e0d020405090601240f031d120c011a03031603171e0f0403080408 64
    0x15041c0c1d0768001d5a8014180030f100501c610f800220241254114030800010740c5508006404540500385e0040c1c0040748002030351b010528001d49a490004090307904800d044450301c991080d502d105031038074101522850008280070441e03002100018a080203020500d00e00303c4d0b0b4901400c40440007006020303550001400c0d0900a0107540001c013030074000031007080050318009160b80e204484500c6085e840403a80990343c00d001544400742c40002d00800d180101d003420564a42403c3d041d042c3d80981c004240070b005031294052280a10085402044a541003400140e0050030050036040750891105024106981c842800d4500360144e08000074074a40082400c0e401c5e41d0562024444e42c4510405026143d00f200c0040040160000003002541407145120300140080e00d01a81c1c180d20500004c1e0300d861000c940f800010340700f41070400440381c07080304013031105400b215540e50003421034041854182c500c910883d4000311030056200586410740d805010300101502c0504419008144424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 455651789 1250 455650539 455650543
    0x30304080d0f0f2313050613060f05030403170c09030114040605070c020d080d15090e0601051807030b040b040f05180d0f03021303060212040b090f0c0f03 68
    0x20103003182200341c414141c0300007800750440d001030020342c00081141c0302c1e112145100b250140f054915030f000081d400400110380701800e4200401c81030155034819000161030780d0300e800030200003500d0321446920500d4054050448240b40b65500b09000c810010400029442240d1980d41d20340d000701900980c913012200b15541c0100341c4110b406600e0503000007046004401c40f10300c250f10651050029681e040800c5442400f10a0025080140ca124a200044420015201c0010344120000320805240030100c1800055848690785540d94482000752000a1054602501c419201d000b01c840110b820041d011400170700c00000c05980d8400c4c0030703040c0d0703c54220405000c4010000d000f90324448010800070141170390302d000031101c0300c0b4010840d480080b0301c125040f520381e05d50610a044d05041034011350301c100d03d003030558180340b4008400602c00f84040d052448000d80300030454903003803400c0d401d40d11000e0f11498540d0700c850002c4001503c0010004020700064804203942d10b501c0000c64 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 455653039 1250 455651789 455651797
    0x509030c19030c1a151c0b151c06060f06090504020a020c12030430021c020301050f07030c1701060507080906030a021c0b0f0d0201051b030c0705031501030609020303 73
    0x60004032a0110707130b002058000c0405000e02d0402001141d640044810444005d0740d44102000640b81e410401001c9054100321a5100d5111042206450509070000d030300c1c46203100d0040d81c0c0b020400d030030f00c0a01c082031040d5000340c4108040d0104260400034040d0442206226840c42142c001540d0402d5a00c2440722000000b40504401c6030102d401e20056102d81180c02100c0c9c0c0b481282c00d0b5048090440340e0760511601e41c2c442e0281c05140340f5024001022480301811f01488518031088005840912400c1c0c4203484000c03084c0024142109d0040503102d811040608020340d0b88034008070300126004040c111006800e1595640900340f401c02603501501a82c5a031041c0c01108224558085030002d05000005903030004000e0420b542d107030b0031183c00c4060315400000c0c1d140102d2190820002500e4501e005041860500a00b40030b08112000c040c03001901381d40000c180b1114040d8200054009450110003910414245140181501c0014400502800d8a440189065480a200311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 455654289 1250 455653039 455653043
    0x1207030f0c020f0d0c0b0406020c030c06040b0a05070f021f0f1103040303110f0306010e04110c07030c060c211106040803100e060d020f1c03090503010509030c19030c 73
    0x14801c400c00d90300c01a40781c030290f1003042c8290090a40310324501c1c1c85882c440c0896544038090f00800d4860341c86143c0250800c0c01c8041c06444204107030021030508201030341c03103a4803410121007545401a02d400540350041e0111080c451002200e4403001c0d000b04102098002d5480c241d040b1600c1c01002201800b503044240d081c5c18a0b004146103414883c80046218030b000e078034144050014032a500d21076114403000c000c155031050011456561007a220146c06800003007011400707545a10840d9071541c440350440d4010b41c080c140070000c004030b41000d84014000350501c58803107291a2201d0342c2130b019442c0c503060490030020b0320b00503642c01041815844031925080324042d14140c50200c1c8070358401e0b01c904004402c02d110000d4489a00c0c0e002e0b91181c5000382040b0280300180d420300c1400d9400015450f8425803088060344904e05000541031714070301036a684c18006140800b4542141c03405800644950402c1103004950040001d1400c174008001c0c01c00760442589040840700e0940d45400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 455655539 1250 455654289 455654291
    0xf060906030111160c0e010302030a1502091201020d0f0b06071b0e090d1101090c061d03030a030606031b0f0c030207180b100207062a02040903020a140c061207030f 72
    0xf06180c0c0081380c1040f115414820b5400c0c000d116120406e8043c1c81c03600740300080d8580c0c8607543d00d07400510704880a03140d600e643c038405420400e5078800108860704030001e0540d1a1b50100c0c446111601c01c0c05543c0c8062032a550802c218000b68020071103c1c03141000283c035040085096209005803000c03607000a1400d80c04640d03003070502409d6240c490a2400000c000240035000e4004200c0301849544412980b040d0100071b1146003040503640551001c2d0201407880310782a5128581d05c0c00d1000340b030495881e50300000c40d03e00340540541204d2031090b410315001e000001102c0507a4209616001441071810480c81e94906860101e1404100e504152607400d05241c03604001c400c1900080d001039011a8208500700d0409004c80c0e40d0481441000005080c07801c0814202410050052121a00b94020b01c00c0b01c24039000315068440b00320003100164442941c0e4024804101e00203c40e5442c02000340c5031001700c0000280c0e85000707231004d80c041d40c0c041d0340106822034040e600c440003640200c0c0c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 455656789 1250 455655539 455655547
    0x1a0405040e03041d0601051b0c04060603230c2d07030c1202010e2a0405011214030c03030c090a05090405060a0509150103080706060b12010f0902030f060906030111 72
    0x303040d80c0c880c0c22601c40d030031607030304e16440d84040c410301d4036070240c8078001c1030b560310b0f0400e10074070b81c8041d803000c40c2d2811101501030005410465100d07070007120041d004a40740407551807034418120075445826200301082d40300c50300500c401d03066982c040701d4011f1403a606048000e401ca803031800d1003111040c0c0a14102e04000303425010150400c820b280740c1401102e02800b6542c402d1030070b9003640c440701581c8101340c10809014503010040e580807000d095a40101c030480700c10f80c01c081703002c4940a0300441901002d040d0740d20200140580704040c5a00204095824120100c100c141e481c00041c2011280c1c031404a44038242c0c5d00ca001c4181e00810f4020601602030a240c205151207c1090342e000d92194103200004617024070010307500184020070042001c140e0318646410030280c00c515022540a0307101d400000d00c1c800070380b025180c0d2990b4030b0058030041d40b50403503400d062160b03640f255403598014000c201101568500e01035001c60103a0301011980e8664001a00602442c070b07441c0c80106001c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 455658039 1250 455656789 455656811
    0x3150f030618030e01030e07120302031c060f06350f10080c010516060c08090d0201200903070f060314090c030703030c081903091a0f011a040504 64
    0x5640502101c1c040d8000b00082c0d500c020420452500075000500455007040c000384655101e540628040c2e1680f1b41650050354841e000c800c510804600290010390020810b216200620360320306001003030820040111501e0150244103583c0140318000907c01c078140540f001c003068000070008003010360301840d03c1000e0111a04400382c0161000045401d0310400a444580e82c4511002075400043c01082e00030000d42c011a00c0358482c01c00006159501442540043c03014010807501907181d40701c030005880d02c0a4028580044129013808580c10501e0705440b42c0b0018a04a40c0b160700c10311041d0740c1e03d03500ca02191034070805130f001c0040250614000a04198140d00c01c03c40346412050207407031502c0b81a0010307076071450310b000c0315810b40060500b0000640151501100148030708005814110315120100c4001840f81080c0b01107a140c01c01c0394100045030080c200440c0b102c00c041072090a15810004140390140145414030034004407402e411070160068800400b401031081c0a40f00900e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 455659289 1250 455658039 455658059
    0x60804030e0901210501020714010605010f09030c06030b030a1203060512010e03030c130e16110313031401020702031e06010b04061d181312020c1507030315 69
    0x46405400046a5804540080ca411066241280c66040004445902c05036921100c3d811159049076a99401c11004002401c2d8054030207000048800000300d95150400240c18005843ca8000c10001d60703080a000044888456105076052440d0008600170f1403030100303182810b00100038221032050260500c030a603140c0c10100a48000f07031942c3c0002c8040d001d005080e940480383c40d8050f50018000162125034601c0906442d000d00212040c0030f0b5038941b0b0b0a148a40c080d00c0700c0203c084043c2c00eaa0180c0e030080c00c1d0208004440c802517141000b10310405440c110180002803c3d1070607051041ca051200f50150b45044d90014143d61000b8000c0c3c150010368071225050346118003590000080c04640c9500b518215581c40e100c100300442c1da11500c0600e00c03042c000303659000400000042003900022601440342004006280c904a110300f4030070120701c1141c0381d1604651081041c41b000d525811842802c2031400c4d118261200c0c00c40c5000d4000d0100640100703000c44030280001000818 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 455660539 1250 455659289 455659291
    0x12100c090e040606052803080904021207090e070504081e1f270c0e0c0d09140708071406030a06050402070f0c08030702011b020307030203010f332d0608 67
    0xc135841c507907928541c606e01510000007110300c894055240c40404c085500107000f442050303c01080185010800840c081c800007003034400b100020b80241050040300d040000302c1d60410958201141040c0c60186400d5a54403c140c48016001d1040c0c400d030000d00080140d02c030114061089100c07034002c1e2403071820082c000214100d107201c01c1000e00700c503502d46407c0007401040e000061541c10030f0400d2000c1043c180701410040c20140704200c10100144c0c00d00c9000c1e9601e100355008844403540400f010b00c2d2540a40013041d05810204c01006100b03601e0110b40c581100c03d8503001e4680d503c9040050050a00340e02031500b0500005503001001510707418010380a21442c0c40040e51038541002a1b602d020b078020080c00300700000503600700003a80c82d4000c40007034402411907012a4403a03000c42d0940c0c41c0f210101034100d0302c07a1000c0400c007003215060401c00880322203551340920500c0312019030b007403548108400c80780186080a0070b51940350000c0320a01d9081c541c0c1010682d2028000c1580e10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 455661789 1250 455660539 455660549
    0xf03080706111801170906010e0910050c07060b0910051c0c08030901090f0608060d0f020d060203090c040207050d0813080708120c16030503091005040f0c0512100c090e040606 77
    0x71000303140c800d9981240381c1749800384012000a101070380c01d00070424215032019008041c04d101c0d0b000fa404051a0b503008451144181c4541c49841d001d107442e01d081642c0404041512034840030b4100300401c0d00c110b19950440f0703412511000500c44d008940d6a408034540340103400c0c0761f02e68502164115002008120380d40c07007a40c50380c0400313079544041415005980a01c1d000204000d000c900e01d03260a180032003126004202002e030f2000f8582c0003a00355000d451003202d00355004010081c0c4007105001050304814144d506514010040d5030703c2d61500c0c1c15654403010701c040980402c82e1210f450340c8a40056034480d0590b5620007140c01e1520b2a50404003040e00c10342e03c8103001541c12910300d02664241d248044c509650a002580c003616941c100902d0041203103d000107807090071900740100390041740142a003105821007801e20b141c43c440260069405000c640d84a103250540024122005c44007101001a0754965940211100102e41e4441040140043e043c40180001644000c0881b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 455663039 1250 455661789 455661797
    0x2f0d0605040b07021902010e04020c010f0c020721170405060c010509011508030a08041401022a031e0c0c06030a0b0906012102130308040e0109060f0f03080706111801 73
    0x3a89a050132a6181019481200b044079810103140041d4007451620740030107401030000d030170070444210a03130849149005051100c0e8032041d00f655003035010701a0314040d141d002c84c000c0c813161807040045103038001180c00a10b000c42e41d520b02d0700f50164800c140c80140c00011700f250703030341e002030b1800d103000c0d000a0fa1451019440c0c20072100b102844021000e089481d84006141400300d0007505448c2c90b00018000e503210b0100840e042140207007032004150030f40414880c1c46000d44040f00d00749007003074401c04107402d40e4005c2046580c0488840001c007951164000440d541d0b001a1103840c0c141402c5c0c4080d19009140803051012641c0035400c40710040805450002e062350320341004481d041820b20f42c24000450400500c0c848142a400400d0f405a58140d03050714203030359540764080c660040e403005081000a000502041109001d4080201400e01c01d2004903402d2044070710861041d440020214100000d0380301c100201904032a4025504000725501d81400c011000104e0184012542c001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 455664289 1250 455663039 455663041
    0x180d05161e0c0e04020901030204020a03090c0b071b24020705030717061e060105070203070302030a080304032003180f12031903020705030a0804050a0804060203090a050d2f0d0605040b 81
    0x1070f58140d1100b500c40d5400804c4200d07141d02c0d640900000b035018403001d008050f12034030702c80301003803521840c8030050030240041c1c0d580b54200d08204944003094100c400880000701801c000c152070508a18158118840d10301e400080a01010382c83c0c40d059500194041c00350520004085c0240380310034500c2d040e2481540c10311b580c1c050884541c2c8000200503440310848601242da103503c80c0000d4404a031001d02103444003903da800103440c2640c09402110a800000704020400d81d01150314540000380740386200f0b240c1c440c800101d03103a0052072b010743c0721001e410b16800304c25940c0143d0408025805400381d050380c854a00044c1c3c8039845598160403200d18445882d10700e0f442442110780c0c190b08040914200f140e0b03080102d0358940090300c256040d11400360640041086540204010038054006582d10407a43c414042444503540c001032240076034640600108032080442d0702007424041c10010307031240c0005500c1c000c0094208098024100200d007108100850f40094000e5004405000301 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 455665539 1250 455664289 455664299
    0x10031b0303030b04020913021c0518010e060709030609031b0c1403031303110a0b0d0506040506010801081527031812070b0f0913050f180d05161e0c 65
    0x1684141b0742c80c0d903046201408680070125195015007111035560551192160082c0f03c190141d4109a03100d810902c0390340b00e154400007003446411419190070002d0015803400c103401070140517940c8001740009813900d001c0810148503561a00700c203003581c1a0849618224240085580064000c1d04c01090400b14051003620b03001058a0341da0b1141c0005540f441c1c15907403000d0048002c1c8910a80101c40d4030030125600030358a000c0c0141c2e4102c104000761303030701e440400c12003621000fa08060500a018005000744400801e8203c000000c00c500303c4841d80760011300b01c03200c25000d02c036008058507610050012000200003001400d5001400c414000840010010101c0a1482250b1070380d000c8a020021981880090f059901408120750705108039071002c50031a01701040c00107101c951740e008210280802203100c81e000089540c40c80d0f807580f41100b801c0d40e078407a04015041482404650800342660304080301d02040d034070030500850540ca2803208032940318800812195508a4030020074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 455666789 1250 455665539 455665541
    0x200703030f06051318020603130605130305090d0f020a0906030515010815090109150905011a0906040b0310060312080c1201060302030705130311030f0f0a080310031b0303030b04 78
    0xa852000300b4001c14510850000c04c002d2040014000e0350758000d00105015135166005180302e50a07a110001040180d49031200c03c07100010072807440240d041c4030ba1004240e00c10305540001e0b0043e1040c0e40e9801c024108007515102100b0b000358884030860000c180406030741c10810840b07200301c0c200c07000340961003840d45800c6030900130038a01d6402035440c00180c0c441700e075015030000010b070000562001c441d00c1e40325071501e0040074403a0481e11150401d0800c4401d201700c1001d01c1000307044000313000c401800034003c950050603407881140c0320f5180c0c83c8150780c28010046024070001040205665130b1514480801d000b4503408045284071001070300386214541150542d140300c500005040e82403144c260000e4002800e04010890240310001e4003166685c215806940100740034051840803400301458074645501541840e0010070303943e20001d20010760015055400944c1e40d8036555491070305450607410740d1000c3d0011410344a212141410080e100c0141e80c003aa50600800a510301484 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 455668039 1250 455666789 455666801
    0x203150909011b140307031d06160e010804030804150e01050a0e1203040c06030213080a14011a090f04030c080304030305041502070812040c12030905040b03070b0f030a200703030f 79
    0x15481381c04c00c2001460f581e10030b601140e00106915080c4000303441d000f0046103000b000303c0350703085440c10060207001480c0e0001d40e0315000490904e060340c21480c0658004100c0d42c40503100400380d0750034800c1060203800c070b500000c0c110030f01c2c1d01c0204110b00d0111140c0025188445200c2d695001d0b01c1107108a41b00c0c08806c40f48240c1c2c01030300c110030b007910b000c400314025032140050200c01c0c0041c5001284024062000141a41c001e038419250000c182c140355013101c20300b20303070501c400000041c46002522030004d4958001161031200c506650f5a003001d40c1e0100d00c1003002441004004108070070190143e100f9802540940e1b5013120304050000341200f20320800d5006403407003000340264070415000d05031a645c080c1c450b00c02d2046166440303603d03844420301c16070110003041c42200240500e041c148038070f4015032070440060080c1ca10b0410209098030a61b92a05004000080010407040b116000b001c50003813a24aa0901c0c120f80201807002030704075110880000741010401c02c2208403c4c000c2d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 455669289 1250 455668039 455668067
    0x6060c0203061302031c051809010f0e0406140f0912070201080f04170d020417030f03010510111203010608060102011a06070201091a0702031501180203150909011b 72
    0x1018103483d104040d60040740305400032070341031055011200005404070030600303402049880c1c1e40d40720125801c1c500c1450301c48405044c09004064010810031070b00d404e82030200c1c5e1140c3c09100d2148c83c3c80c00c3c03c6024001d0715034810000e001d00c00c240802d00100f0400d06201da0320030002c0e00c004054512001403648245280a40040d100c4008504034640e021440742c0c2281c8a401c15004408403030040c4e03e86500418036840c6141d40c041405c02840850011903808500c51001a5140c2030303079011085135500060140d58001d00d9040e1048003c640600e940300895403070001124014000341079102401d0b40240500000940c0140108031203500502032040390041603e43d25000450314420301aa80d001083c060741044288100090b60a070390900055030000310314901c680d10120350040c1032030050a011400d45840040e001040f1000e43d10408000480c0301e01c002607901e40f145403948401244030030941d944019000e0900c1300e00f2405602c010072080812600458514006100381d510201007204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 455670539 1250 455669289 455669293
    0x1801061e0507050d2606030a2301060305010c17060f010e040225030206060607121b05030d060315021201150c0b18070f060f0c0501060816050406060c0203 68
    0x64440811845030100e805003040d45005802d0441e40d450b501e10785004034075424042095810030b40a804e0700092002c3d640034140004000300d08102d808a550365080140181828039044d0019150211aa140b41d02c100b0407000203000503601d0b030900c1c5000300f1440510360045140e50a03103580d000b030442d0b201d501c07442d0020004040700101c0001518924141c031410ba44c041d60811104100300c0195110340c580e2410741442c2c1c1c0009046140291070400c01030100e42c4900c101340619000178081001443c6001100d01d0007101040e2010550041d8042c3c0500003040390201040c8086250b0071517100800703ca00680806442c071914801d1441244a0f1803440031200c1d480701d005015007071801a042294410781c0c6085101d10b400e94440e140812820358a4000f14180c841c100c0802000805c0410090907270350221000c4d45192140240124800741c10b9030060045414829040c85020361040000b000e4684c00d03034054480303609050708810458007a25101e1840c080780440c10601c00c002c0350340a241d001e40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 455671789 1250 455670539 455670557
    0x1d07080114010305150616021219141911010e0109080703060515030f070e0705040617090a0b0a060807080705090c030a06080d3506040207060213060e180106 69
    0x114081d1138020103003815004010044041922035a000300b40251210600c080c020186104000603602a04204070442e4021214925402c50650500c040140d110084020141103511752500b440f040203030b544004140c0c00d881c1418003686100d824180c0c5002d0fa103100101e140072005645110b158041c0200c5030703202d511b050000402035488030b50440107180c44150f050013041d00180c0380c80b940307642100e1a504500b80420450440c51105900f0014a04142e81824240340c4000c00082c0800002c1c0201000d40d0040f60900c0c0b000d025070380b0440d4000e03692082e20700c0d00c2201000600894800d2078541d100e150400128180c02041c008240c6400402014280d03d03560054420b640000c0c02010440d541e503140050307003000c200103c844010007a125a000340c0d19211103a000107402d6058803104074903402e094940c0007088081651701500031100142c960076030781002c10080c040c03017074410b0369010040030110f40c46820120400409100b01e614000c2103035000940b4107107900a105d0740001c80c80c905 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 455673039 1250 455671789 455671829
    0xd230f0706140705030d0b13022712010501170f01150b0f3f0906070311070c140424050402070f0609110301050c0408060c160c1d070801 60
    0x180c0090325071000c81039441c03c00c000c580341c003411036010341c0c0a900403d039941c000940f1418140001d402ca0801e0708000c41c245010401c448814a03c5507080e00e143c03c5840742c00320120313610420340e4130b8000c84a00080050390385500350306400b8101c40500050302c0c49080000f1407107030814020304aa1240011401c2e0b811803400b00c090016030803441d21034030702640510010381c03c1c0380300c001082580c031000e501115038920781031075803080d80440e81c2840c4001c0c02c9a204000c0c0041c3d0001c1c400d03030800da00d0b02d000902d40f0490050620103004011006240400d20307800080c901400d0b54940001c001c1c09c545c2000090200e00ea000c0c80d2404174041d2156200700701900700807914166014180710b07809410006603101066448034200c50110354200d941d0000140c5540103400d00740308403503220580344903a91505007080c0401d80d0751180101a15416000010804041135240307009501d805d0340543d00360401629500303800143d000c41051521001ca1030301c009640c907841100b64904030784180c40039503030f000644 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 455674289 1250 455673039 455673047
    0xa0b0c07110f0d120e040f021206090c0904020a0507060507083d091d070812090307081207060b09150d0303110f040e090a020a1707050d230f0706 64
    0x4071010782c04000c5020800200e61200d84c1003c9441c12603841c0c0007031100c0c0000704400c03188080c078030039500c42c4180100005c1c1210124841e07041181240c00b42c0d0075685181001c09a80f04099160350804d001140c41040660414054003806114141c01c1c08075680e507003000c9540326400c843c2104c50703500b603c00800104075404402414050101c000e100c00035038020003d1360000041d800481d01c56a10510301d442003920031000031050b82c180300500300e45450801029580c030f01070906c505888034000f50b154201d60b400c2026070020728040e000e80e66030301640060340304190000002074804a082660100b500c1c9040091580301c1e05040e0f0448400000c11402c2c40b00d0b14a070400c003203040c990350345200d01442c5c0040e400317081580302e0702c01c20343d80c0d0f1401c0c910310004003d0302400d4007015900080c4c110006035201191803096851001e035141c0c803c0399240d0494a001500d601c8941c20140401414060121044003442d42c410798100103001070009102035559084100c020303403030542140609000003807103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 455675539 1250 455674289 455674309
    0x1104050903031803160c0608090f070614130306090311030703080a05070c17030717060901060e0307091e18050d050309160b0d05070507031b06090b090a0b0c0711 71
    0x403012a4100350141346100d12164800406a440311b003601000c02085d5070000303515034422000000b428480e000d010209a84806074080d020070300c51b803c85005414074003c0250b800d00e103505004d002c070140c2c0d00c1c1440c2000701400c88040d000502d59400400c007440c2c0010840e540198560b561740c91307a41c0e85165007030007400c0140100c070030404e410800c3d0000c904880301064002d4007010443da5a803d00792806031010b102c0410304010003a00c401040300541d9880ea02504403101410400c3d00052a0800a81400003c2d008101c14619004142c0300740c1c0100350f42c0c40c0c08911542030801945c035404d0414401150500c0000f49140c0c4a446010300c03003031048018542052884045600c421440c07411041220301c0c0d5040040c0007a8040345070440030b49039000303580d0007000342d080a81c90181c580e10300400c1c0401c115140f44102180858000800015a005018064000300700310340604000300302c280c8890150400ba0303000038840f0046501600030700202d40b039040d070081045090101100c02d00c400c0b101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 455676789 1250 455675539 455675581
    0x409050c07060c0215060315130305130e0907061e0c0204061503050f010e010f0603110d060308090102060619050d050a0203010903050307021b0d110d02041107110405090303 76
    0x280038050040029071500541101c103e0740d4025245540b22200c0c40f055076a00105900d1096100305a1854207001c55128540c000030120811b850042c028201910588141461664091201c40700060400140c0d000c0d40d00420076401a2101c46945030400c540340e050351031000313200701040788001e1800c0c2d0244218601075480500007150150303603819003494030045c2e11903000100741c03030f841001310080b04960441d002d4900714204010b82d50405100100c40d118600036a01410f641c0d00d142d00e46800041c050b10040403000c0d005201d995220300e8031205640009960501501c0785102150940c588a251144028100c00e1031808180c90b140c00c2120038040d00105079000d001d010300c2c0e040561401e01808500030700035101d0656a04101c1c3e00285005880c51081c50802e4401402d01c04c19500e101000036007036003200b5100854008400001c1f120501008020760040c6814404440c0201181c003801c100303801894900440d4448000b03200c11755400300c0782d940007504100001400c0180203514200408 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 455678039 1250 455676789 455676811
    0x50f0a110a080a051803030a0c120c170712112503051509070b0901081501020f0703051c05030103020f0d05121201090c0c030801030b06030f1b0108070c08040905 71
    0x1050544070002e8a5000181e82400110002200007007000d560003070415546060300103528080c603800d402000101000e400401d8101040b1141d2240c45c403030031840040f140c0186070300309026940d1000414a40c4010b01c120f480703a82c2c0b4004441054001c140c0600002c01120250005000c21302d4410000821078500c0e10f02011f1248002c8081013040104141590100740440c9049c24104209481c01c19103501110300c4010800c0906803690b0700c01c1ea0540c202c042078501c12060151400140e040040f051100a81c900c0380507000802d01400050108401c0070801620703502500e01d01e41100e40c0d100c2400069004000840e5400e01400c1c030740c8540c0036140c004d005a8100c4c82554090520356403112010819040c4190014041038140c1e1003141d500c1100ca04220301c01010a0f03901500c5e400c030511002d8681c2c00c0210000340591014040e245440c134228055605420700e103a48425450f421680150005c0c40660002d242207005941d501c040302d03003004856003810300e07150a21014007001890700c0410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 455679289 1250 455678039 455678053
    0x80a180b1305011e14040f0b13021e0f010309050c12120a0306140d03080609280608240f0705040302060d0506040f060510080a110c0d020d050f0a11 65
    0x2c64000e20a070808615100441c242e0707155005580016590483c0c40403151416140600c07000450229003006030360b038007a1001c3c1050f075403580f1440001f00d09900c060f41201a6058401c2c04154054107179440101c2101c022041c07500c40780046007100d03c503510003411640182c0c008682450489a0002d180700200222030780e040c2c6090b07242ca0990001e282142c042919800300b4402c0d6204034510107804002030b9684580301240e40c80050400c203000e41001d01030907603200810140411904001045030350707040c1d000d91440400c105180103050fa40301f8000c01d8002c1d460800c86284864186407141c01401d0000700035070300e807050507030311405000d0085803d009040000100688440001c1e20140c5c001740300010792840c01405000c107603402c40e05284119468010180a0b40d03441e810707001e000d90140c5c50803c6050b03440909403402811805141e40160201141030349070300c02c0005410082c1c0010383d0075951507a641d8482a140341c0540302440d50304080c01d000d140c10180c454807041c80c088400104236114 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 455680539 1250 455679289 455679293
    0x5030705013e060f060a0302040903031103010609030c0807080a0803090a1a0f06031c05090409020d111804111017070e01110a020d0209040f081603080a180b13 70
    0x440c400100da07842c00c41c5203001091280c10000c1c0034041d0301800e0031401d85890314100340054000780480c040240300381e075101a0b56061620aa2250940c08407102d4007555a5842e4607000e00043c01c544070840d02c0740500000411400380100d140d0003210f55a5008000b6100b181c0d0703440203c0e410041001403507200300740801020808221510462100e00e4600c815141007001400180f520010a414002da0166200c1a503d0400c80c4018008240304d16149864003000340000300541110600030303600181c1000d91b04248042102c120010a900325051410b001d241020048903210864014121640d00c0b40e00303c1036400c1c4a03074007514104962511541662213842c2b0740032328003802d0b14540c0014452080c02080b41d60842e401c14a0b040d0b234407009014030710341507001510344c52101200074020311201001c1000c20015450000000c0e0703200307002540b601046201b800c942d403080d44058000034840c001040080400748a0b0107821041c40480d80860000c80c1c0356003001941c058507201a81d24148500c0c40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 455681789 1250 455680539 455680607
    0x7030513150c110606010c141207150b0114190c050d080601020f070521030405030a11010807030204032f0621060402030124020a0606090f0609060503070501 69
    0x600c003054401c00040504150320010000469180900000e5011400740071803603070400341014100354014010b034840c60b4000501403d001d070721140907000ca4804203007841000a24004d451090500100c00c010b16074030354004441e441710840041c00c82d00000c2100c240d24450711003c100d03004015091880c0755100665400d850000104120000140b209003400070300d69060091411543d030f264000c2c9840707824a00001c00d1903c02c80d0260005000114807592140b405109450080400800303031004a0102d090205030004150030450016a0107800249410f0181c42900c0c103481e0032420b44110500141d5540d80c07030500341d00444d0040460641030240640d9900001d00d8031121010180007107000360030020415a4014005500c04c50060005101240c20302e00c1090007180c0e140031084004021420603401c003044144090003c1341000310203d0100d241d038101003409402c60204001c01c80d40c038200441290003a00031190f0640115000300019071240c540720000c10341e14844000340882c0d15985c94 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 455683039 1250 455681789 455681813
    0x10050a03020708040617010902091e040b0a0609030c0909110402090a0905090a020112053106020f0301080d0e0102100209040f05041101080a06080703140f0105010b180604030b07030513 81
    0x54001803404035174482e02c6c100c142030b40d8010202c814003582070012150018801c0054203500d011000414000c51845079182e4005104100d00504210b11607a200c1200500b1004103000964501c1c37001c40c000510644c1a00c2114102504103041036410604034003004046e5111a040941c4000d120b6000715112602e886800d0280c290400244140307101440090150300e911b00b00c12803c0c503c0e0404201d5112154500943c100e108100d03000300d02c1b05c1c4843c00d0007507900380740000342c50f040c404101606c2042071000158140c0c7c0841007101c0310070300c45032000c42c1d100040d1444140140c01110440d42c403d42960090100e0010003040802c00c660044c0c45c2e00100c4400b10b80a40e000102c805800d442540c025a03910b400a00070700e020300140d81070640707065590019100c01070112032888075600d50603500b80a40601446040024006542c1d100c1c03001c21641c2000c2d4805900c4405900098001d01e0b00e90120390441e50300c18030018032030362801419402400000d050318a00c025811541000030b0281c5502 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 455684289 1250 455683039 455683049
    0x9061d1e030f040e04021503040507032003070b0901020705041e051f030b040f0f060c020d21020d0b03070306140a02180405060f0a030f02091510050a0302070804 71
    0x24148184404080e40c29240310154180c800d400800c0410030442c038000443e026198075080c10141c548031440865601550124040e07240039000c0240820044c011031201c088a0049640343c0950000020000c07100d8482c0c2041c940c560710840c002c000703c411800242607564014015146e2503603840000c40e0603207013081121007108004044c85812190907204040c1c0002d0742010311005000860b048a00d580b14502015140b1929240000d04001c10000110b91056020b180d814030490030f8a040c0002d0701d05c10035a00050302030002c0108129109022100c51038412103641c40d4048103a810000c0207500040c0c5000c1c04c05d80714988090780d07890410655004511601c0001034100480210411a100242503040994010400300541481503240c02985940c210b5002506e511100005a40112480d50041d082041c0c41000001c0c80790251001880324000c1d2100c260550b10300f01c04800c010f503a103c240d540401c03000d0b0b40805062040000c0c0c40da050031400c00601e4481c040c0c6030b400703180e0080d0b801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 455685539 1250 455684289 455684293
    0xe0a030201140c03010b040306050c04090923030903030423150d0b01030b01080a0507030b030717010b030705090c0a050403060203010f08010e060c030c0708040b03010b0304021c0507050409061d 85
    0x425103040b01c1801c20725a000c007005900606550428419005038441c5100107030410340c507400818101c240380070445004004526003000300d2011480d000c440c80003543d468400842d01000c0e1000c0910b40071088811020004010310b181500700391440058109410500810004280c0030707140c0e60325101c1d5006060035050306102e40380c1c24420800c405862100107414109414244038107901e0f44c10104058020030b100c8808a030564480c07204070010700c049a0420b03030500c261b4400241c61681126165420402440240000342d006414140d441030320303116040c0c1009214001440b01d880700d20140c041e90000780740c40c0b80340941c0c0e038540c01c069800a8100e00b80005226000708600700091048014081c0e042c17001d0500c070300d0b08035402c1d403c0c1c0c000203003101c000140000d00351040151683c12200a41541c142c059141d5131200741d9100c6075042103404902500a107403506000d0000808101401d0b6070100040c0901c5040405010141c4881c00c2c01f228100d40701d2440c0b185084008020110003d03440380 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 455686789 1250 455685539 455685551
    0x708100615020d02060f0901090f0602040515040b0306091b07030216091a040c12050a0c180f0302150d0c020f0111090102060414030c0a06320402040b040e0a030201 72
    0x30700300c401034000307031001095510000d4003c03103542d00802d06580c424a00e501140065842103141400351504200080c00c0110001d001d030308202090340640b0586006542500c90515110166980d51040e4050401d1000f400cac80001c8103494100c034440d078441c09030400f080c240d213001c0b41070103040d400103201103004d45c06c101032884280301013401c408014480203030240411441e2031000d815000c031980000f40a1510351a45070300d4640101200c60504400a02c00c0003503240a50005005200861103071002070741a19404100091040032442a10604190031000904e182d0130800c1c40d1f480200f40e034010070018420305c0f0b801001403282c500d03d840315802030141c42811034070b010f0844460010002c1d80c5d01c1c080c4224038580c0d0307000450590040c0d11051000710303000078002841c603602580c20701074140e1003000c3d200800c11115410109400a403407031540c120360342e030441c50024440044910407019007420002009850590810072103000301800020b1000d00204145081808a04041d000750f91500c4d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 455688039 1250 455686789 455686799
    0x20405062418010507110f0120100506010201020703050a120615170907120b060402070c06090303020714181b0309150a0e0604080703020c06030a0911040b06190207081006 75
    0x909058202d90034a0b00d41d00c0d02003207540e24000c5484c1c2d10398260290780044002d00e46640901007242c143e240d48081d40d0b02c0700320f0130f20704d031552104c0c020b45c140c0c1194107150114040c0c2d4014025204950783c1512090305002c003021049843c003c1d41d84015004a484480000c0c00c401e02ea440c84103040881c2e90f540312014000c411000010901a00c0c1d11000c0d4071640c2d04120650302c2520400980f40d000e0700c4072070700340c43e00e0303000801a0140d41d40180c00b003400c1700000540c0d140c0085d40e1604480c07081d001d441c07600e540c450400591451005805800c4202502c410450001016655500804000d41c100b40c0360340a60388288030b41c00807101d80060754420200c3c40d4540300350944455000c40085001c0c007040715417585150b1a000090002042c280703000c901401054000d02042c0c0c02181c000d03110070340f20301d012005e9401410034403d05403442e1000e00302c0764090382071a00a840d140040549040d24140c020120140c80e4003251042c1801c600484001203541e2000703100a07503000300740c44004680d2038140303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 455689289 1250 455688039 455688067
    0x70c0806100b03130f14160f08060a090206070515011a040b0a110708011a18070206040222020d0b030106050d050c1311070b01061202040308070204050624 68
    0x584072052049502074100180380402d421603610480301c03640340c25410100c0c581550a96124580288185038000004003a400c0004a90028490840c5031103456135031007104200081c61401000410381000001a49500320754002d10041da10150502d4a80300c040e0320703490304009800201d03000001110b0300400119820f0215189074000c9100c84510706440c04c030546c1c0c100d00c42d02150714148441d2074900855240144a100700500c2c00c4030083c080801c44800c0c0c03480d070412416241c3d00c14084010031a40e13401c0f00302e100501c0781299400409068545400300b0130308451047d600d03040f804102054140003101030000d0001840c12107030210b100c4084100301404e440e02600260b001c0c20020380e2280220b100041d05000490040e9003402121624500d82c07000703440008114105140c0006000702002075200303e0a0484a080c1d4400300d0451800440340240e100fa44400341081800341f2041001d850250300503600036000a18503c00d4000c6011120740e1f0642c042e02a56014070042046030380d1000c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 455690539 1250 455689289 455689291
    0xd0c090507030204060519090509070507121d220212150607020d3c030305100f1a19020a060b01030216240e010614240a050f070c0806 59
    0x8907040070f50409041c001c00170083e00428000020030782172400155000d5004940d600050300015015641d0351400342c5000e0240c1e40a42021141c14640001c900c4000c1d111710000e1091900181c030000b0200d29000c01c004c42d42004024282e140c0700d0341208022088100d00c0145032030101d01c170354507800749000c1d040c140260a031400d2190140d18108802030059503268100e0402e20380c04451400156115140301182c4003418040622500101140d40d0b0000d680108036001c061280e907040c042aa00d2a5120003030800ca0302c42c1c4403081420030024400001071646c0d000000084d4888281428580fa14218840c81d42c0300b216409604400490824842c0b01c1c0140348444800382030652400b520f0001c1540316008121014020060110302c07000d940b101c1d1107402d6104121480c0c10f10111903880382d818024002442592803010540b510a20305003043d820042000445803080088611074420410266204481500410400b000b4182450702d682000d0f081c0c65008182c80d40400c0c0c00c20b01d031035141c560 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 455691789 1250 455690539 455690551
    0xe0a0c0e0103170d1806050105090a06060801060e120d1701080607090312020a0f060b1e03031207140c011506082401051312030e12060a15050d0c0905 66
    0x8041001030000c9102c500c203a004160000311026550100d1150070001040c9030951090311001d6040801c01b03121840d00304505030b9000300c1c0c404295072980640c0d60200c3e0300c0c1d0f200300404035150303200400009010304100402c005014100080d490145a402801d1200e03140036030021801c5036145169a072801e040040c00342118800030300060803c03000107407000030b1912005100d1340d45041035101c06403083c8011030b07100d640301e444180c00020070315110021b4020919898040c3c51801e074507501085117200c000380685c82c046c018602d00814540c2003155020002e00c00d03428809240c60f25100c00300d0800c020b002d030071b49003800001d8249858100410346040b503441640ac01041a051105801d02203840c0101040b403003107400405000e441c0142c4140c060426480003038840d101002980c0120300c6c101c900000d00c40d0780ca586241c0c400c041008540128603c80d135889030320010020754024643e03802082d4441000400101440d5210000703100c100d50640d0444070000d0040c4c0401c0f10300094014075030846 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 455693039 1250 455691789 455691809
    0xe0a05070207030f11010306080d1d0301110403201c0c0e040201020309040c030e0d050c010c0c0c030b07030b04180303060e091f0b06160c0603021201180e010e0a0c 72
    0xb4910388840710308006416005e80484440c400c0300020341c1c02580b0150060412405441c0c1600b070080c0060b02401742c800000c0e400303c4124a900146180610440d54170254056906050a080d42c40c0d1550101400c08001c500c8000308552500f190388610801003d150100342c00840c0c8407441c0b500d0190340038103922500801092805000c0180e80200940d08070003820f41d400240c00048482c00c502402d0704900016590003501c4000d45110750000080505242c124020b00a4414181c0100d661441d50702c0302400b07454840b5814000034611300c1000360001c1c0750b860003260200300b0320f0024003140e41050082d054008040c81003402c160300b601070348000b0280c20b00c40904a140100f00152901440c00c404c403038a908030700032021640c0c0194011099808041d01460b1030314006203070303180316034034440c001d440030001480c000581502c40d0003198a110030640c840405a407030301c044440b005c47e5411030110410307101c00c1c1da026242d101348100e10440320310742d0090000c0f004c0d901701110b035048540c00481d181 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 455694289 1250 455693039 455693053
    0xc0606120b0a0f0209150d060905070c05060c0a0203042723070903020312090114160c140117042307060f0c20060d1505090711070509100b040e0a050702 67
    0x51b544409002101c260141421540c1d21855090f5000412413504261407040c070782400d00c8601c540c01401203078502d00c20011240f4545802040c110076000726401c90b0b0040c0d008000601c0031001070900c021000c540c08501c4266484002109002e40b1080d0345c4d4100400314500706000c84a2800c2142600003040c0d04029208906580200342c44007031b0564180384204000489551507441240c200c2c010b100046402d58944421a2130304003400403070102562000003035240456410500d03e921282003905840c0c0039860300c045603030564110001001039403991440c2c2c0c5103c5a80503c1e0b903400d81c03800040d0b005071800318104400600810040360400c01000314041950000401c096139500c4034801d250100d0060411300e0000a50a1250501d4162104d081401404a541d04804030070207861045840080c16564a00c00304c4072a504d02c0301c1080c3c154440c3d10200007604180c41890740041d440e800507103c164680c44c0b0030b407846d803086d4044e90917180d0807010030945605503c155074214a0a201400c04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 455695539 1250 455694289 455694307
    0x71d0405070210020f040b0f0702030106050a06020319050c060a0b011d0609120109080c0f01051b0a030c03060914040c0e04020d1118010303180b190c0606120b0a0f02 73
    0x83c5a18100c0449642da50000321a411001c0d007200b82c0d0010522143c241e5555481c2c07031034146041d0031104040b4000c0d03080c80800320781d500d000f1020700155102e0f603008505054040e800f0300300501707100c5850340900c48104030f0582d01000a00507588624004400850302c0d0098038001801e10344c40800844c4035000040c06000d440e519001102c0902c0720441e6034500c000540070f2124010070340e1901c020001070000489950034140410410740481214000704442c1e502c105100c94005888101010fa605080103810500760191f441115140a1480c0004000c0d44640900c03007124104c6c1c000c2d05201030604104010001b03180031000142070144800192810990302295a59504500c002d004008006500e1300640f102045170005112100d04003c4650390303400c003e8103041ca40100c8082103038400c9404140e82d00c58034102c508801d0b806003018045605040100c8120045050440782281c480900058006400b40d1021001e8001c0498100ca428224150021070720241078424004d8014403003025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 455696789 1250 455695539 455695543
    0x8040311030f04030602280908011802090c0c07082401050d05030703050304111305061f091412030d0c020d0e06040b070303140124090515090117071d04050702 70
    0x4c40354010030250b1103c01741034485604040004c8241a42c81caa5400c00c855154004551401c44000600800010007100510f1a6600300281c2c06074010308280c01042c0c81c0c0310540014080d00001000365103117103440e41c088074101084581034400ca110500c50300507581034050003480c01801d0465a49184652540c0c80307541f24000e0b080c002d0700b8404084002001e0152038015082c03403803001401201141c2c0005009002040107449541c041c41c060008000e003d05040099030010440f41c0301d03503081d14a42400c040f040d1018500e11074010325440c082c44528dc204201411280c500900701207907a0310030440003880e00a50743c00c51400c10004a44800c0c0c280c558400726000d0b245a420050707500c017103e040c2500038000c00208141c04003020400011001c2c0c541070040e00310000008504400c90900b8801c81d900ea5140c0a1315500170380042032490f15440d900001d0920307035810305000003166a03581c80509046000ca40001c0820107190218086000c0074682010301d203012a070800040c00c1440000b5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 455698039 1250 455696789 455696797
    0x13020c013b07030f050712050709060e070e06030a0207061401030311070f03080d0e0d020d0813201206040f03021606120b030102040f0807051305070f08130c0608040311030f 76
    0x18040944c0e10040703400f80705d010b20006000e03044a4222100c401c20519043e40e031030f401071048c08001442c100e0301040045240c0081d41c06200e056035440a80d880240030030045a00207850756901c0c42d402c00c44c003400513000303006004d482c0c503c200c80c94010350301d9810080d01080300080f01c5c035100d4000e91b1091000700c0c03041c4040c03000e0701e4004000944680403140920010031440c0c030380c46414480c4940404000f41d000030101420f8005c1e540d801556111603034200c502200f039120041440003400b522031098014a20740c140d0411009000c1c4d00c0d00381c0030418550030400c00b9681581c00c030041010074014150104403161240d040100d180d1551483c0050040c841c6428a5000621580b100000c450565094060740c0282580d210701c3c5540c035564020711651818541b041754020601038000b0380d4052103600c106403081415440d200350071610410202c41c0071030024100d035820a41c0c007036880c0224140b40003403c048e000d035071601c5801d1300b0700c0d0030f024202c0540198002882c1d4410440300e2240d070b0b00c0e40c3c00ea07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 455699289 1250 455698039 455698043
    0x1b03030210090201030b0909010516020303060a090e0c0604030c080f0a080909191a04060f0806041b153c0c0f080c070f090203060f13020c013b0703 65
    0x408502c1c91004078040c103c0c102d802a030121a00c2c0a0010000d8194489401804180314180310440c10030030590300c0b0301044886ca130707001d01541c2041003100c9903900807034415000e00d400d851042190800080c0250042d8005894030f030810700c030501a0400070041182014400c07030042c0441c51459541c0b01c101d11036239030303260f0040d2030f4140850807191000004003481a81840c0600030400d2a16900304020500d00460f03101d58280803001400d6400c41ea80c1d181550a801c0144c5090b644545400044000b41050054010380214000500741800700402807681c40c40d43c0c5e0440131100700c1c104403047c0c03d800320782c000e0102024040c0d1085610080c1c4105070300c100a090400c800c0240d820001e056001d0781f4030144c544040080c0707113070190314041422000d8841c85000c450045445145100032070008481031034109662810484c6d4901d4a07510301c80c00c000004201500d880030001290342595002512140da0001080d50700030140c01410720f05d1491003892101441c640464001140e03a41c0c0749101c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 455700539 1250 455699289 455699291
    0xf03070b0103140f1515010509031b0d0c1206050c0c0c040c0311031501020d0f0806060d090204090b040636020117090606031002030c0319271b03030210 67
    0x600d034210700e083c030000440003102415218a004140345d007031030b071050440d606500c800c10034040802543c0aa400d40b448250042c00508088007901160880c62031145955984483c0c0c0d440c01d04001455068640007606c080c14210442030110300d89175054800180194018000a121012404038000746030f40c411042110301140e0112004001d82c0140403184034401003150010400c01d01146c601d60341d0810f89c80a0382183c000311003100040320060008002c1d4000140c0c02d501140c0c8130f00d13240d406810724168170305000400e120141e000800300c41c00c110048030015095002c0105000c0d05108065118054140502241c0942d030340110300404102028241404040c03150300c2903911800314a50b68985c0191880b840f402d0a14000356110b81c00c0b5030f440d111303100d041d40b1301c031501e403160080c0d130b000300100d1140034150380710000c0d81031504240201344001a6900e0010b05142d200e1070707402c2d0141c070780c0e03010034404a1221030a01d1000d031402c2c400304445070b1031040d1003000001c0d0300007141580000c507020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 455701789 1250 455700539 455700563
    0x12060608060d0f110604080c030c100906081e04050c03061f030620030c180d0c05060702150a030c020c06030601020d0c11030303070809010b03150c0714030f07050f03070b0103 77
    0x10700401e13078803c0780f03088503040100824045124440060324249041c2c080f8126012641603004020070b05150031001e60000f81c00800c100300281c0610f40c0c0d282c1111051101d0201000c004645038408501102c05941c0b9a000351440200d0381814400203411207070340402e0684600d401c80c686098202644001003040c0d580d009a4104480203099030100203074ac0040803541e034104450004074580281c00c0300e0702e015807841c40b43c006914128940704646030b40b080042da4114500f81c10802a60004401681c0003005183c80d20030514140c0c0081c4600007142c0c50001e0a0480c0d9000280340589418020380107081c2001480856a00003442007590b2016283c00744a02d0f09074904001c120f12541ca10340e0b0548008420300000325048010903128201035002085045000003c0550f0f030600141c100d420301d0303080c0b000300f09110f030444008d16865002e5032084808a02040402d032071079105800b81d031095900454441e04002d82840200300b00c4c00040300032350401c44241c1341d024203060180320060820821007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 455703039 1250 455701789 455701793
    0x90e210c011508010203100f0806060418061b11060c120720060601030b03210a0c020307120b1006121509140405010c0f020a02100311070312060608060d0f 68
    0x1420030300c82d08440425900340540d44140050217900241c4042c101c0c988204400f0540c400070028200480780288014429500d540c401e00000f08449480a40031004200e4180042892402000a13654003840310151946800c000140701d1019903588003210b4200d81c05111285200a061380e503184031b14800101252a07115040d034140c0040b46606a00450312a5818240000072900c41c2c402c580a80b8203014000e41c1340c1c1059110074840c03041e011030420819850206180f1040980008010340c10002016074540e00080c2c544485584a0300341c9041e030107203010400c5016a401074001a00310b11802409042c0a07001e000220140c581c200c6a558441c5890101e003092030981c0000d000400041100070022603003415589030848060b0744546c2051004940c2500c207904c0da2001c51081d40c0980100c0025030300300720b11180c003100c8400c2096280c40c02103d1040e06400207040d901e1003610f5030302404080c202c02001b0b0754890390040301480000400c000c01d5440346103090300306540c06440d800070071001d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 455704289 1250 455703039 455703041
    0x10207020a091805120904050a02040b0d05040809031902030c030a05060c07150608060604110f070303020d06090608160602070501050417010f020d060305010f06050609130f15090e210c01 82
    0x1403031000d0185c1c40740d0350310590340908000017440601d4007618180440d5482c0d4618409070f00c030f2840b0780368410383d0401828101c8201e540c0040d40182c8a862000c1c601500a0002032401340007010510941001012600851804001001c070703111080d8068100221152200d13503c7e004010007488401034001124410806c001a4021207503c080100300311250301e58005075941e40d81186c446000d5864070130310030940f856610956041902c265003440c508402590210041c0d00001c0c6410100380e181c0b6008199100540915009010740784000d008409200e940d0b0242d43c0301d181d2001d0b080d074001038000e000070f0768007008a60544d402c85180908170122542854010071002c42c02311310305440400c00414400b001c0d003141044902900090080004c00d4809008a441c2c40c820690302100030000d126403401d000305280001c0d01c0901e40010b0b254078034000c800903507046020715031403910060340038061080355100e03580c0c1503984000100001d1202c5c9540815582481e0b402082c80440892030088921003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 455705539 1250 455704289 455704331
    0x4060521160c03110312040203240723070317010b1c0203070203190905010909050609010302040b0a0b0301030605011508190203090c0604090614030f0712020103240603060503010207020a09 83
    0x6002c05c0300d0350360724010303074a40c42c00b08140c43c00c034404e00814a50b40603942c0281c5000050010200c20008503854250050346c004210904060300440907024110042050030041c002c0a4040e0325514580b00002614058070441600071087c103c40030312010a403000b040040140b0996107120040c3d59440b64001645103009030021800101c40101c038440c2d84d15800350040040320001c0e00c540e1002c0d9160203000c1c040d90001c035400b40e00543c03d00c0040000d850250031040c03100740b025101d00344241d21040c042a0a6000760019038410b604c9000402c03c2d44100100d00c03e000500d40f40c494100c1c2400445800140d08402c1c220100365004404509036281c00c0c49080c030f00c82c0d40286003540d115540d100d183d020701481c1c42403115561655100051609010400c1c4c04100f05850240040c50b040c110b40c03452203070b0100000d0381019a82c00d41c18008200a85060505040c9821084440307441e0020040c20780e1030a0708194000d90040c40071200589682c800c050584455140114001501c0000d007404118 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 455706789 1250 455705539 455705567
    0x5060705060105010e043c0e0c06070c03120203090109060302122404020a030504060b040903021005070201060902030415050903040b09040b0d050105041a010e070c110409050304060521160c03 84
    0x107001c1e0149565050011307107a0301c001c55807c0e036a6414825220900701140d1030b01c0c0040c0001e4201c0035040c4000e150200050007100e2042d105c5490071500d03502e070b0b088503821803c40d001c050390000a441800e50703044012400104aa4902549010600582001a041c3c058142e08030611f41e078805171104100345454100d1594013134001c54403201c580800170081c3c03a060390b00713890345894400342d000d503410240500749045070035400920b000e500025080c0d0003000000c2091086541c0c1d43c401042c588528001103020b103001c3c0c024903040c0000100180121580601031080300e0340308002c00c01c80002481b05484079000d007110001020342424000c148000e9184c50010300e41e503e014200000c106415a01300101403610074007075002d0783c8074100d000800c4400d0718208041010303013001c02c2c0010b4410340504034121001d840861030101c03680d50f9500e1138100750030800214034085aa0481e11030000f102036400e80700042007034400c0c03e0180c5e4004011080428080070010140091410b15000e40103840c4005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 455708039 1250 455706789 455706821
    0x50402070f0b0c09040b041419020d0908070b0a1a0d050c0301060902040e0a06080a0206090418080d0b0411071403130305030a0f080708010519050a030c08060105060705060105010e04 80
    0x40b0b04100e0060080d0f018100807131240346002e0410403203040611450391070804054012340e05480b2802092604140c04a506804a8081000490490141c0200004107110f80d1180ea01c07140145000030016600900c503920300b501c0c0001c0012202d0f9800260498050141d48403127002907541481810102050701c0340d901503090090015030130106c0c1e802001101c0b01541810304a0300c64684100176182c082c07282482e964080f41d8110054540040201107000000308005004444803003140890044603905403149100810195005070141c003451010b503d0843c1c01300a10352120b14824020300905002504844001a0340408410208121021068416204012607a4030726240781c0c3c030341c40180d01000007441034604100d00f901a005c002d000d10320944841881d6803c040500c21051031052031203c0116040c400050540c441546e030b003002e1401500c5c120700242c148035005140901c1a0303c8140102400c0102c04041100401c1d501d064540c00d28208815019420002d8040c1002c001041102 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 455709289 1250 455708039 455708041
    0x30531140a0c1d01031707021206070905040b0904060203090111031006020d08071706060405061c06051005030106030f1b030f143c010f0608010e010609050402070f0b 73
    0x445000160001c030948507a80c01101c00781c5982c1a00c100555102c03400060743c4a800051001860640f95600312400d040744080c2003480783e8000409180d10b624500c1d6003030308104248140f03194000c0e0858090401614140300c040d00410200f42d0300c1e0b0000300090221540030001c0385209801f9084070610000c16454a40c60741808030b00c0405003041c0e403003041702500c111a0744d0301c1114010b40c0f43c03070300c01c068603142c5404d00d0a89140403254440000c2420340e004008201c081003a0b95000060201607030005407032008030030110041c6c4100c8040f034020b9445400c0307840200b202d90b54040222410b40b0154600450741c103ca4030f00d020054840c03441c8041c0d01d68a20303410b95000d96410b620503402c1180601062002020851085040c0b0340c082d40c4900d2a04044070303c0c14003608503c4507003041d100c00701d90340d90100c0c84012541040e06500786c0040e403102000020401c0003550100549024059111225900354903081d4003920340d085034803420340103071780101c3d200301807110342040007903401e412004614039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 455710539 1250 455709289 455709323
    0x10b070816122601150c0f02030607090f08120702012006040f03030f050103110d080f030112032003030f0414060103150c0e060304080913110304060b01030531 70
    0x9140c90b0341d100240152002c520002002c00f15448070750490305c0c8000180070b461912081100d60b803045820075520507400520000044c1c41c1001130710310540b15079a44405031810509a10b90031032003030b48100040d40c0f1103840540c0c01007054080f2035180d83d0900b0034a18140f4003018242c1c1228000c0310284042c0034001c2044240150140f00704110f40c401d81d4200f103210111203082c0c0840701300780009888100010240314041c200503041042042c02004058241890380780c0405a0380d000340c0021803200d0010080760708268000414070a00103640003107004800c0003280c1e55642e40001440100f105484101243c1032100d0114013283c0890402c043e01d009685904210301e038142c1109551120078a01a4690401446004200415a0014005440c0da00d540e11102004d8000c11515540510f881d030000154100b81c1c030444079505180891540c49141c5410604121007920482c1070526090030208074000011460100290609140c1503c400c1d5040c4550301074007000c0c0b0300040c6111042031319505 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 455711789 1250 455710539 455710547
    0x82e05010801090210021615020f0f010c080c0301030b0c2a0a02010f020316171b070509070e06072a030b0603060c190f0210050c0702090906010b07081612 68
    0x8030b550017510002d001400040c400ca0340d540b03a61000c41040300102c1010b2040c0c00c9000c1b00322054110760701c1282e14403c0c85a8a042c10a5a1100c40e03400980d0740c0c03072407103901c590445165036025041e01500c508542c59501c800d104075a000b4101d035134000000038a84040c40a40c8030780089036561118448041c3c5a45481980d0b40d99070072800e82c0400daa0755802c58120780b00004444c1002803201c444008109a9a81d9540b107450030641c040140c6002e000060725414034070400c040c40c0c00746c403005200c001d1030401441070b13032040a804841000703400380c89821961611400c07198140e90101150f050b01e100c1d40c4041015a012150840000e1241c0400000340140001e030540034200807001e8842c03e4a035200311514911403201038090904049002401c0c060051402c4243d515040c0165014a600341501a0450307004071900e401c00352010072000194240511419846184100207021950500c0c4044845004140008015800015080204110403002041c0c0240e010709075102ea142c802d60050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 455713039 1250 455711789 455711801
    0x71205091e040f02180906221a15071208010f030308270f06010e04020a050d2109060e03010c081501090e04050109020102060a0b0f010c061e0b04060f082e05010801 72
    0x14804e8000e080403806038545190f1480f41d0b5580c05c14000603448e030740680031010b03208100142e13002e091101e1080500d1384516108040c82d00424100f10355806091800e8110343c066116400200810000184081d694010840c0705484e01810315075004d40c1d50111f03030180011940c883c641a60b07012211298002000074411401c00c4415080d03032a20380e210642681c400204450195018406050400003070034201e102104450042e03511950181c0303e140e1120000140070628000500180300410409501038180e42c5082802c0300240220408583c000340181d0f809002e004100c44201d5001c036403603024904d0800140103940c8030507902d01d000c1c10014000c0081d11020f034054000c000018248000074070402c80305800042011459801d06c10046a0341e40300d24078200c0314a959514003d00b5600c080002e200700c1920420003041000d0740c141808141d404540c400740c6041c1c1103050500403120042503030720344020b900304102d27900d20171f49084050300c00e07200ca0480392503450b00002186854040d0040e0f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 455714289 1250 455713039 455713087
    0x1b1609061503090c090e0a080c07031a070c110d020409061407050304120804060f05090109030e0a080601050906041103070503060a0b09010f0c150c0203071205091e040f02 75
    0x3144185078082000e4040e2000100000c000584131982800032001c9903020000c1c119503181140c100610a607510031060b03000c410f4000199106241c100b00300640c0040c6140c00d4414842414924204240098810107448000400e0300303040da94100000c1d1102d00820400310740041c01804010720904201000b0841e002500c5901080f050004006500440440c0d0190b41d0104038207441c03000074203086445000140c07003180d1554030f40d01004c0c510300f081d0040c58001c8a40d03100025504a480c0750241200c0415104240074030950002000007020128600e03045071000c0c0d49940d52540e48000090040206102505034984c2c08400d004020b079002025510602095400b81401911105851400e005810304c1500003805001181c4920744540078401c102e40c420181c1503c42018411200c00780c61090f6520f00040c0e001060342c0c0e0a00c14040c020700034040745420004d1510500300003041801c2c50391204000c0c6103d49208480d120f0315154000e0010110f914000c43d01c80d503507481d2000880c3e510b038042c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 455715539 1250 455714289 455714309
    0x5180a0f0c0e0f04201b01020403050d260414010c08060a05010806030a1a0f010f030809010507260a030b06070506040b04030203131401110c09070e0303070209070e1c081b160906 78
    0x48031b89501c405108442c10359411200400001e00c50000444e02d1076458864007000001c8074103a181c505c0c202c000310324000c911504003074120706007200406084504040d11941005461070500020703403501c00a94094410a182c000d100e583c51001117464043c110000510302c03e5104140c11003070294840c02d6000b4550701444400c076990f03c880280d140c0c100c6020182a492040045006a40c0a03000038441644079040c8070700c80d0101e9a040c5146000c0110504201e294001440080c0581c0b5100e00d0071151000c541207404d2440c03d84401d82d8568000300001d02a941440106040c140200103883c03a10740d0070804d41e203490b922400d40f02d01c2031019050442c0400c900641002442c42c0100c1c510705101000b40821003140e451103000c031040f00d82c128000b40c142c041004040e01507102e0f10f1030a40b0032442c0b925070850841c282400d0000c849a041200f15000080b80c0862000404540840344054444822200c444115600403401c100444281c445008408000042c400380982c201d00c0454107a011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 455716789 1250 455715539 455715577
    0x307050d083408092103010617150d0218091b0102011b03110c15011707030503090409020103020c011a04050c0c19050705180a0f0c0e0f0420 62
    0x9664004100c1c1d4081c0c209001c800c002c1d800d085244501c0c0700700e61000003c000c0b125003000a100c41200c5a9820004c21516500000140020b82e01708483c94011450034080503500c0ca4500310540010081032038880c842c480300b400702e00c150b5490100d08800144040030b61013903402d100c0c0c40300e41c1d40c05224190410f080c5615038900155801031165011148400280d51400281e03403034110002c1442c0d1454004501051114138807440d000c01c8070f810f012111008403c0607504000d0b40c000d113814464060626588000d409100144020040e02c0480000740d1b070124002460f8401a4081e00441c0705c0d08205620f80340c45020008007401e011910600700780c40070420380d02c0e00c00c0b030000705124000c0749540990196800d081c14029251800107610f0190056810094131900000c980c000405849001e040505040c008402c0440c428502002c0302008108010090a5405400c000742d20b0300700e42c450f041c4d61601d12150341342e03034103c2070804034010700146440c62501e000340119000710461000310002c0744 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 455718039 1250 455716789 455716831
    0xb01030c0e010e04050711030c070e090d14070f080705010209100504060c0b0924011503060f0506030405070f120302070503072411030424020a020f040c020307050d08 73
    0x2101641c0002069503074100300c0f00c8000c2400082c280c050203c0c1c0030803a640c8003040301e000062001e0126072001502501000385003002d504218a8040c1c040011a00b010701007680898002041f501580244404941c550382e041c104586a0000e003000a001c000340010b6440c00c00c8019801003010140c1200e030384c400b0401030001202d040c041c80c0540004141281a103c010901c0800313540e50003c9203000701ca480703500c10000c0007240c0c80c42350805000c0d00034240060100c1c6011070341307000545c280740c5010040c26240015201301e081c810f03c40c05005420010114081c8801807103000040c0c189244550703031349036603201020026044128190010b009007800840d240c500828008110760607642c0644082010419504506080038075440a1161940d924003000f0070a00250009106404000d80c2c8018241c521950a1100a440c13800310340141c01c0d880010b0381c1e142081e468451065800080c07400c141d20041c0d140d031080703600180880c420b81e414804c00c10b6002d040540300d02e030300707100c0705001d84064 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 455719289 1250 455718039 455718047
    0x60f3c26100b090106200d0306031e030207050d03051314041103090a02040507050d0e030d1b0c060c02030913020408070807030b0403050a0c0b090f0f19061503080d0b01030c 76
    0x4603120b42d21145100040000b9441422903e00031b21100c00d45500c0b084481d074400e490107041c6200c01000c261540401c01c28407841012407820540c01445130202c0c0c4c695617030002d4035030701c240c0641d0b4410b0283c51810024035100d24203454079001c4098015010544503402c0c1d103100180d8080c0da074402c0f070401150225114540050720f000d180c1031130040141d04142c1e800c0002610004004c0c0e41001001d1159500181c503c0c06900c1e85d10b2280c40103950b44050180140d001c1c1c41c5e001d003142c40d459a00f05240c00302e4550040841e44250b0300f1030f100180390501240b049040d0b11a1400c2140e0082c1c08810451008160358010400c690703d00080741c42c04d40d61400e115031184400e10018003844804000540441d01590040444910340c5c40d0501100d440c5903070310b0a4020b025988490907034004600d0355810f0b0b4ac00c021440380b41c1950300041c0303140c1c40076084204d900424000028103280d10340c90f002c441d10b071a40b003044002d140e11801141d01c50038a040140c0c0103000e1405e406000038180402c2d038400c6409 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 455720539 1250 455719289 455719301
    0xc050a0302062409061509030604031e2d090b040902090a0603150612060302060313030f0905060a110708190302160b041e0302060a0201060f3c2610 65
    0x281403022655140340420010001c1c504039011006c2d000c019480300ca650600045104511070348940003010810f01c8000080036120780c2604c28040f0300d18000b020071a2590f5690941011841e0b00803030040000c00c1114801042da2251031801404078011907004100c4d00a0f00e0003540c2500c10310320281e0740c2d45084090351803540d4104044440c4900500215128005001e40901c10110210300d155403039000ca9100c0d80122102d10b4000a076008030000c0544c0202c1c200309841c09807419840e040d05001c0055040e1081040c044184141601b00060140080c081d56000b440100c0c180c0e0795400302c02140380301c4915070000c04c030011301840038070102c104407480c0e062007a030b84078801c0399082a0a00c15006000d41e82080b90b608403d0741c00200000682e01c500080c0404451a03001150861030207100c0c0c00d607208607401485060700c400d002e803d0310160310b1f584c130700035000c0c0703403404120602d090b0b100c0001c605a99080615030201600c07026550034107182d03140c1d421010350000c441e0038003c043c0b00700e411242 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 455721789 1250 455720539 455720611
    0xa0b012919080405031909031b060503070302090117070908160b0315010302070f1b050105090306040f1e060c08090a0203070e092b02060705070b01030609030c050a030206 75
    0xa095040000c54502c14146150311078840e1044914100b800c1141880c0c4100000b049000103c503101c0910400040c400542200e000c41c1d9003070b1810b01d0605a0180150200922010415138085a14a2a684502c00510700c41544015403d03484c14864070041c40c1070041d0140010f5845a0450b01c00c03481000c0c9440d8048402c01c004d2a41551100b0b80d4560643d07090380c2280b8105902403200344045403000c06403113101c40c810070002601e2400c4094114440d03940380e100905214040c4068807603600c000c1401d0ba4019845500130348100828545110327912403901c011006c0c401140d0000d02080107651101e400c0342440c0d02d46014a0790b0b10200c1664801c840b200094058000c80800c001d68003058a110360804084d4043d601801d00c4040000c59100000c05100780031904035158541058050001581200013480d006244c0b5405444413201d905040c840142a070382d540200c0024181302c0e0751451034080d13100e0b0540d114081da5040c000e50b61801541c0102042d43c0e0384012504c0a0215a800ba030060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 455723039 1250 455721789 455721817
    0xc0405040b0117010b070f05031201170f030414030319050919080d0c230106030c06080403080f09030d0c0302120c0a0c030503150303040f0801050c03010b0d050403020a0b0129 77
    0x103804e0017807104442c0c008000440701080315a030041300198007480074002c5140c58001c1c07080070703614004d2815151004c200040e00700d82c0100d200303000c0b0450080210340c103483d07451080ca05801e541c0b81c0072a10794441c89106502071039207468140303000c80c3d001006001001007101d0071308000100500512a40034148034144040d0705c90040e0030318540c0100c0c11a41c03041d0045a084440b606029482401d60041303440c404403a955070001801041040c0c01c640004d4640c3d49065200c914242d03501400d29240540740c00081811040080c081740c1c800c06c122004401244e1003485440d06100010300a500f01e20881510103044c10f001500150000c0291055207015030781700c08400e5007548003601d0782c0d40301030002d414003070f001040d8000320f80301000104000d15091030116200c2e803a000e4842c3c05c54401900d812684141000100071285078030040e1014583c144030000b90030f49a5160aa03d00a01840020320224041d000060f400902d04110140d009200807244044002c0300000d0f032140c440c0b401907240c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 455724289 1250 455723039 455723041
    0x18090f18061e07110706020304081203060907110102041a0306100201110306040f1d0307150c05041a130806010609090e1504142a010302070203070311010c0602030c0405040b0117 78
    0x4081ca840001d60040e8850918003c0030810b000e469007401d001d1b4000c032000d40e1000404101e1108100114940e950748050390314110709200001584030200608107200304250404486500f0341f0a41c11a0f0043c030054942c2400011602d03140c40450300708607112403082c2ca0321702c0709109141c01030103480e0307044410050191560380d0b00c40402000b403a81913400b00c4025030b103901000302c6440350b003501030340188074000450b02c991007880c050b9590396403818100800c1e030900c1038240c00c3c40d0b0080260380079580700412554074042c4162010f0b4550080e44c00701307400394050050000d49030101240c003d05950260780c540722001c0c0c44181c903400340c0e2401e400f408995401409131401010200c07410a411070b02c54503819548004074100740d460301010040902e4130304030400042c2d03c00c800c0d40c031a100e111082130030f0950034002e090b0002501c80840e4070016054004111940c41144c0c40b500350407000a5002d0030454036400c009a50b01e40702c0c1c1250185902603031403c0c844400030360141c0c204408030411a85400e101d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 455725539 1250 455724289 455724331
    0xb06030702060a052208030a15060210112b0501090b0607020609030f0a0302010e06070c0317100803220b070503070f080702100201050714030c040b18090f1806 70
    0x2e00004110380b60314144202c080d0398128500e1740124803580140c804584a04140c54420101c880a41e03600a4951030861308101441e0040340b0781040ca0041e960000e504070241498100c1480344102203646002c01d0320686c81c03101c2540d258150f2078002000100000c0e80ca0b8038110044401c6280c07015031162090049800610b800c80040c1154500a0141c40d11201d00302d031481d181083d92a401c50150351580c1600312070500c1003000c5544000140340400078400c05132005041081c5142854010220320350001e6520607402095000420540c81201c1da285010012160035941001440c2365540900304001001c10036102507a20b410f4000c40910b1824059945081c00c00c80c0001040300c030341c0d4050003201c0240c0ea8400d181d40c034101d03040d000400c95140c1000024045506101921401602441885540980182a1000d940d144801c280da01c007080041020110010955981d10100000412120f4950b8000d0507010ba00c003003c40340380541039200c41d2034650000300c070503002e0f502601c081c84072 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 455726789 1250 455725539 455725541
    0x2070b091e2d070b0417010506010206010e0c03150a090c021009030516050a080d0608010b0102011a120f030703230c0a0201030504061b030203070e1c26120402040b06030702060a 78
    0x100c4500c80208590a03e0750325900d008042c4c0040e480110071014100e0144071780c0d10701303020751680820b0910140803258144a207084003414082d2000c81c03440000300006203000d0b0900c0c5c03140110040140030808141d610f00008000e081c0d500e901a0040c011080b4001c2d645a0b10f020703409400d9450344419040c501d0341034034122100a07001098400b0300c0b0745c44410700030820003002020010b004c0c10003c10308a0500f0042400c1d0383c5145103e41c11603251000b0711145468a0502072803644007101c0c13040255400c40800e9282c03041a120344102800009548020141c1242524142d02c001d6046007079076588802201031540180301c4180c00c1034100526000043d8807a82c007159026124140008009190062044520105015400c0440e0b4000180300304150000c03016102c0680072546001031424007245052410303440800144801c2c528071019080b900c0041c02d0200c561300304880c0d140c403005161381c5405034180540302680a030b480d168880d051030a00d0021207110700465002420551110380742c1c04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 455728039 1250 455726789 455726863
    0x3141912052115040c050a21060e1305010c0807140a0302041d0712090809121e0733120e070603020301170706021f02070b091e 56
    0x6445254112281108030240d0100385003e0901d00040c61000c44030202800119050286610b09126050014240740381e882003901034000c54500030186031220111210700604407130741115082d00481c1c400c1051400900312440082c1d40990020300240715103401c140c50311282a10b00c0700004941c00b1140001d0078402009000d045058a001072505584500c6442500d0000d40c00407000d8840005016401d82d22030341c80d00303c50b4240c5030200030440803075451340c000e403180c1200d06000394400d1141014001060000c050074020188000c3c1d00d44041500158980296009007440051440c44055242c44031412101084040540e000900e81c4e0b080016903900c00d40c0c03c24800c41503151005584002c00a204034002001075440142e180d504005140300748040c80e18a08038142e000c1d80007000500e40c00030f02512004040e0254419811a0001d4000644210000036000051307540500c0044c03000040e141c02c00502e040b540e8040030150b4141552510220190241d503206182e003117100400b1f20342455 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 455729289 1250 455728039 455728057
    0xb0406180b0a03080a0f09080706020c0f061e1c1505040b150d0f060504021603051e2a07030b0c09011106010b0301080d08100b090f04060314191205 65
    0x3003003201c1d6913030b60391484039801a441000020441d01c84032804039004102c01d405001c0c0103014142c120f0520b840250b46114580c22540310300c0030f400c08083e06840b41400c89811402c00440e40c0d9920000b1501d1807a994000b030803d1030400c0c0030082e91441c0404038801c02c00c1c034586d9008440c0590b40f4001c1000060b000c4101c0040d4032a418035450300c0f5440c0b00070018220118542c002090480351548544100d82e81a44000d0055004014850700c1d00c0c107020301d001040381d05042072521202c0e48030045168503554000c0c2804c4000014201d642084481000342c03154540c002d501850303001c2481c8050705c40c3c15510008041c0004640800c080003548800361002c100107140602c00841800000f5140c61002ea1001e4014100000140190315051118a441001500701490f080c1002e5080d107c0d42e1556100b80c00d0104804940c1b55840d5447c804861520003004105201c0e40d40caa05000fa0340300b01c2411442014442c07240e10005a0090b21443c09100350004030400f104000b5040070766496201102d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 455730539 1250 455729289 455729299
    0x1080f07050d0905060106030b030f030f031f18062c1803070609020f0d0b0f04030507050102070c09150b1204030e090702030c012306010f02010b040f0905010b0406180b 74
    0x10704540d420140c072422510b2401107004217802e502d44800039007222107450314640a9000f1603405010400c001040b1044580c00204a580d0390345d80c10003d0301c1007003003100c10300420380f00680b00048010019280200307801d800b450401003195500020100700701c0049510020212078a405107003454620f8480341c0c40800c0c103152020301d1681d0130300700741998402c06c01152117640d206000820350411501c9410300301c0e001c0d511002e00b400103884c0c004a4844c0107000040303140d004800203040501ca68281e88000b0383c000700039034072200d40b403400001401d11402110b440314038100c100c4481d0f40c50030510104807001903d42500d808543d40d403094041d14000c0064040c041181e90020698964035885c07441030545502540d280c0c0203402c0c140342500d400d0020440315280042c0092407450202c10102e4020310b0908002c41080c0110300141d000d040c5c80070000380c3c0189081c00f80c080c50318258000d408800e220b54004c104034540b9504200840d6424058050210f5802114003028001030380b0554080b500100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 455731789 1250 455730539 455730547
    0x10050405030412060f20070b040512041403160b0d020d060b040f060201110306010905220c0f09050307080606010c0611031302040b01080f0c1c060f1706010501080f0705 74
    0x12005044a540c40c4080713903130594034150000c01a00502c82e8405c14196042940301c030300e64022080d0307040e00545101400001c00540410200101080b000354145150526145c031541d41c1d4203120010800a0306450290141400104d030702160007281380c00b910842c441c4103041140c0e00400d0402900080384024900d42d591f5804550050340da4050002071500510f13841955061840013400c0d101c0409a814141c101801401200e030380000c00c00041d150140c03040301030501911b1070414045a028500d61046c0d1400c2003608030640d10440030103240a450b01c41826403903a88090581d81c19a900c1400440e402c0100480d2141d827007404400c0c2540e005031400301d1055450f29040f281540141da80e81d5500707112111050450500c0e001d490003104090a20300c26916083c0001005860024241c42000c00c0002e10404410310540c4800e280060403a0b04000d0349882d1364420b032082031507000e09044181d40d0405444030140c0014454141c42c41a503424001d030b1a110203403009960094031410a101d4140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 455733039 1250 455731789 455731799
    0x10905010204140a0906050904030807022d15040506010902090102151302090f040f06150e0c040806011e03330b12010c0e06030402040608030408060114040b0102100504050304 77
    0x40058070140c084034620f0441e428540080010300d6032584e022a03191410f01c2c1080050fa41e90003074031603107d43c05040900040da20702404909219001d50310b40306140018103411401209440100c1e000b4409104403402c014200d1520320016201b210000d00c542c7c00036005114010b640d03006012340e01410b00454041d418518500344004104558914807026041c642c0400d5280a80b1010741101c070000d401001d50400307403030303c5102002101014240d580c988941c600d4510042c00b00701c0003844456200501c1d82408880d010155206204400d86c9100e05800892039078241d266543c0d60074510f40c0035980302d51071540d8041030080114515514900c01b60300d06642c14030010390054100401010001c0c002c1844e42c10082017124102c40581a68501746081c00c080b5000107146804080c01c5411301e0f225561880040e01400d03c03500a6000c80c040418002100c3c2000100c580c11ba580c90403001c40c400702101c040c042164028040c141c01030b03204032108900c1080c0780d88010b41250282007540c0c6860307214 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 455734289 1250 455733039 455733041
    0xd0f060b030a0809100c1203020c1002090618130f0501091a0a18020d0f1d0c0109030f0c0510020d0e030d0f0c150216061404020f0918060709050301140403080109020c01090501 77
    0x2071450b00d0100790002805049030102f409807903104c0e64583c1045003014500b0001c1050750281c0703541e4440b810750005801d070140e5608107181d500391082e6081845510310151030b810151400380300301240c1508013080c100c814091202400141e60303000d03100894240c0ba005000300b01c2041d01c81e103c4075441d0b08001c0540401064041d0051315051150301040030b0310aa80d184084c440041c921282c5a00160096926a0380c8200c00c8001c4035009078400d0b004c50300703034100400381c072030704c1d600059000313100780d0b41c1c10030440e0045040700340e0300e2803a03c80b004440300140a15440785030800ca2500090003100c2000181c60058201024260040d002040c0c036221000f07140d01244e200c074071807005040c0b51541c110301300407d5000381005100380c2d0740505154285075011484a40880424130701ca810400300080c4c118922203415590032070107108681079401d0100c00506115194022907020354204244100744070134112445001c1c07a03140d61400110f81c0b8000071a402500318081400a55403158106e5000c5242 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 455735539 1250 455734289 455734313
    0x1203140d0c090302090609240301060801020c0c09090a03020d0804030c05010c052a2815150501030b180925062a02040b0f0d0f060b030a0809100c 64
    0x240342c86801c0190b0860040007400030004020301d00c80c065290404c1085004004840c000107603072550102200203100c002805411550000744441d80b01050054001400150078014010b05440300c0020361a00c40c00c031615030710b1030309010b000341c0d018000d154112880b9440c0366621a0080c500b490400d071140c0d90389801e6403801c0c11280002600410342ca65403815030746d071400c40a2003400d4004041803000075401d40f03aa609141d941400c91880300354201d030700e04170040c507000980e0116407541101c000d4218140104145012940740420207071008c03442c0d500900c149081c1e100014603106060b1020450f06282c080010500720460291103084095000a9010011030482c1812045145802c1840003820fa44ca004480a90070010540f0303040c01c80d00841d031004030703260103840c04250441c1c20000308045002c0032850542101c405903110040c13101e01c82010030f072035210303038028800d865960080560360990b903031003c2c0c00300ca001c0080d12031928000c1100746140e102030420b08002c2038580c42c0d0007003102d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 455736789 1250 455735539 455735561
    0xf0510030209090f011e080a141606112406130605040e01020702030606030d0504090908090a08010c08070503060f060d140c04150c0c090203102d050a1203140d 70
    0x21300040144402d25040019440301801c1078024601c4502e005a21a03440b580120050440c0c0c10720b910f9004019000d100844c0010300c1c003000d82d40c0c95690780d2001040c440c0d09902c07400c0280281481e09030040385d10303444010728503441003840d4035a898201c100031018000b010078817505580d03444005203503280d5008920726042e8040005850b03400e240181404d00c84020940c034403d4001b607003602845a00308050382d041c0c4840600c00601c2180701d00c0c01c06014410402216070100a80c100001c014605400c6512900040d5440150715144c10406440c24001901d0342a48079210000e0f14409090043c0580311803240040e0200780a12400004516030b03100f40c1f00d29060410010b42480304e0100c0980b1030054502902d41590035110986030841e06845900415103861340000218024070720400c2d0000c040d242c0c0701c03285260341c0c018139500b0008031584000304003800828400082d02e49424000744088454034001404d5004031a94121001001d0507c08903411105000d11060348545105400c80c4078 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 455738039 1250 455736789 455736811
    0xb040902040608100510050307035d050405040f0612030315060e090601110109020316061d0604060e0a031e0b060d020a0e0601110102070813050a0f051003020909 71
    0xc003404490a40c5e03401001c0c6041c107251030b8001c01807510001400300450b60801901c10394112001100c90390259603040c80c0205880312688030780251081004155001c16016108040d40f54158400c1c180500099050303010480500041006040c513805c82900c4140480c3c3c0001c0d195100c00740742a0102e00e1351010340000755180084902c009801e13400e10050010b42c24130312041200c0034006400780c600104080d0410001000781403a4100c25041407035007030360040a6a0b4265104032103129801101c0c45140c00003100030021409248581010500c62580038003101d1400d42801d0094410312048e00d101c540240b202440000030440d00320302040b41d0000400714140b002d000e401c00d502c0802000c1c1c4107a00c1210312000302030060741c9a1010000700da0b01e9505024482c0c0c4c4600050b10621030b440b60502c51540009070040030031807108000d11502c54120b2011141680b60401e000c0301d81c415002c2c1a0b243c180941d1705029a1070320700e90102c6149298900580350a4010300441e200305001c0c1c1d041d042074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 455739289 1250 455738039 455738053
    0x203010f050a06090e04030c08070803072f19030513170105010b1206190801020d05041b0317031003080a0c02030c01050f041a0702030f07080f01050103030f030b040902040608 77
    0x340c64101010b200904052a200c0182400c040220741c90300c4029000038107110707080b42c4a00c1044040015100b105400c2000360303440307150030780010300b00c600c03a00320364110b075642c8615000c05210100c042e295040c050900070103c0b02d0000f0004030440b0208030080c5c051000c1440505848615420808054850702120f61103600f10f01da00e060946006801080a441c0140010325411007001a40344c0d02c550210380d02c0c0910b041907030001c5000c0300990007040482d4000240f0480c0720449421483c003c0344100030044c0940c0c40b5050100e1000c00900005243c0c1403a00200407004003c40c0140d80c001407070140303000601e0750340d94466243d6480b00703e01c0e074049108504007000f58501403043c0e40d071000c02800d10f980b602600661000b180e10890042c1c00c200c0f8988010300c144403401000791040d00760702404130358440341401009a41d4505500c10440c6c20300c1014840e806c00034060042d24100d03075042e1180c50301ea01c100102900504407945486030070507681e00191015a8079030140c40c00030009113000d0030704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 455740539 1250 455739289 455739299
    0x302210c0a03271203240e060306040209161106010906080f01061404020c012007020319081206030c0301051501030c02150c1c020c030a0f030e071a040305010203010f 73
    0xc1c0d8841c00114814283d1400302c00d41c82d00344007050f400c0016031190a203812502840f106070700030244508050f11004240b8100445501140f000e1001e540c01120000d4803a6a00e80070035949501c2260003d42040c040f02c0852a0000f01c200480c1c000701c01420302c0d002410000c08014600102644800c9145c0c0e20f13490200304060b07080c0701140540170700d00c00a1100504101001e1f1800941d020340b20b000790740c0000e10f1019040300b03606c100c001010842e2103001320440c0182d10303403ca401ca400142d2083c020020024101070a1440d41c080550380040900d003412914004502000c10050140780c060266104051140d036080c030a807842210804491101c0a000c180010226001400210150342c8060f2417074001c1044061450340c4400318035200b030f64507400340e2940e045003400340e1804040140080382c040d19228010000c1c020301795036965441c80d243c00114048056511008000401e90404403003444452480b9500004c3c18120314105803034260380b81c1d00c80d82203334000d07809102e0b1036040ea902840 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 455741789 1250 455740539 455740541
    0x403021501050f030a0318090624050a080a0902120f0105010603060501210b01050c030a0c1101170f06040b031608070609240e130902040509060c07030302210c0a03 72
    0x1002d000142d8218000c2034a11004c0784c2c0c1c40082c000082c1c14800a800980000240780362940050300382401c1c1030020720358401c00740e1356000b0380d4440d01b0b05c0c100b0042c8079030200c58440c40580350891100c1c0d50b0140b83d40c0700c03001203100403c440b003c107a801881010a4101c00c8c14200150f543c8854040d0001640350324040c0c1c01811244c5c150401410080c1150140181003030f5104c080006c0380e00c1500000e03208a6410041c3c1c1c0710311070807000080d0b60201003079000342c1c00d410a154540d5140182c80120382c8510200045981c1c4440c814032204c807100c00804900b000d0005400c0070781c00346000d070000904145d13410000c0e207041d180b8840703050605c00d100c0c001c0c080c0340c906004840042c000390803c0510142030048000400390301c06d407186000b10030808821041e6201e4001e420b10040b000e0081e42080341d40c03a0030740300500703548081a4010790401000c5007915000203100d612a0020315a51410092541d030101d0182d4000328110311045094400c0d1030002c01d80113100c41c0610700c4865519652484030401038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 455743039 1250 455741789 455741791
    0xf04031b050109050f2b03050a08062707020a021306050a05040b01080601080702031204061d12041e091109030f0a0c0e06210f10090206090111030d020304030215 71
    0x30b0400004000070006611482c0110201c0d01044840585400b0030012080402c61052a0408803000e8a18100305160300400105002046980d41c0703960f03550390600b1300212009000c9515621070722a0035400100c400e48466642000c19032066445e010f1403900090941d400091406a0040c0e6440080101e80307403244000004180540b0203004a80d04c1c1c000280014900420040c10701401c8000101d05500c01d200700c1d01d545000c03804022050400f8104200100802e0005400d004075020b00e10040f4040000d081a00301605402d40e45414240041003101d13130f0b0180800480a40350a00104018481d40120305400c680f000410381c444000300c2c10035140600040c4910b240fa0003c02d02c0c0c00204001c030107141c01380c441500e0480000c1d103c0c100881d03500d84003440d20440090005441c0158080003140c0c2040c0c5c10400d40403070308400c4a6042c240102d031034000d802503001008001028195014981d130b480401d41c298140ca041500c182d01910581c0c1c001c80d000c60043e040240b0401400441012407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 455744289 1250 455743039 455743049
    0xa02010209121e010920060408010c090f061b1115180a06180b2a0a02010e19180204050a080309090a0507020a0f051e1c080603060406090203030f04031b 67
    0x9015410b1646c9030a00c00654000900c03d0310400400d20380f10903115107040f14010914030000b04800060880d0040c001207440c0502c0c07045501c1050006001403140c5100e43c40c101d036004030503d0a07006541e80081441d42d03001802d812003c5944981c004183d204064141c40c074079150000c2e61458954108420349400b074011000380300c01001103030030031400404940e081d0b4044420441d40c0e060f80c00215840843d10840c1d0000a1a00ca00f00d9509a007000c0b038000c0750780d8802e8840000d00d200541c108042c44c000030703e2424042c080018204644060155078440da02e80c000c1c40186815142c0c030200e100d4180c01d0300011207a51002845c070100c3c0c10024542c80e40034181080402c0f003410001802901d400e041c20001d004006d2070445841881018442440410b103021900098003050040441d01d5080041c407080190814041c1440264094070744a40b0402004020704401d50380c603503c1134000c000030305099030584400d00100d10a060480003c1002c0c50042c0000d035105000000381c2c1080c2140d80c3c100d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 455745539 1250 455744289 455744291
    0xa0f03140d0809150a0908161709031908120103081902030708090f0112020a120b030c030705010c0c09020d05040203010f0b0319021311070221060109020a02010209121e01 75
    0x3c021502c4000310b02e5a10300e0070318030010042a101c07503000c0809400c8031800a4220310f4000b9102811248980c4e0f03c400040c800d060965081809203698085800350340d00b96500340c2c03c60b800c021f014444254800680511501400341094040f60094120304001d81044075000400070702c549010201604000c466403841c0f00442c54601e00d82d64a05150142ca4034807400303004c0764401d070034543e1300403a002c0c1e00401c44500c00715111003c1d40e000620b464401040c0c2d9045529000e203003087d60801280460706040050f0042c034081c4d00d404011108003e410509a400100360000480c0c0c4100a00081c00039207003ca1001c1881d0619004140c05c40d4203000d5002d941c1c40c40c02c1c054141e191000324552034080c90038202d10714228680c3c0089021250b9512440071004c0c030f4602034140c1d08921402500d600340c02a12460b030b08003032072003614149003081c6840306c600307a104900400c400c1a0ba90001c110558003480098100b00d41c89010554480d000a54100103401502b65142c07600c04074401844810800c01c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 455746789 1250 455745539 455745541
    0x61803040303030b040b280f03050d0f12020703020c0f091006050c0f01060305070f0b0703090b0d020405090f060102012004120c0b1617040302010219020a0f03140d08 73
    0x65aa22851000405142d241c42d01100036a03103651040b011400041c00d81210f01c60702c0c620007480500301e00407103d00d441800e03001040301c880d8850f0000540390b000c5e004040300300d00c0720000d070341d51141c48503218104142007010b010aa051400078000d09031083d00107080c096034900812a440300302c0c1106a02601048040015607401c0c040301000320380181c00d00d140c0c0c448841c0100c40c142615103001c9512582840c100004102d00010b1560807180d8101c24020050f8484c82248128401c02c2c0b0003500007240301e4424001d2a9012000f04404c013000e2a005182c90741d11030228040c14800c5546103aa11100c80c01c10001d56028024401201405194200003014540000b40180607900502d840d4000c10030350f0500304002954540040e20036007440e903441d803020844070303041c0710920b90302110081d1801c20540380300c4000100795025284d058001c0e00c598007583d03a0390030311a501500c0030703a400f0001050028504034042c07410f1000e54050b14051440c212144201031900d00540c1c40101000010b81c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 455748039 1250 455746789 455746831
    0x5010905090a1704332d0c0618060c26060a0b03091b0a030314091801090e010e1501030b0c0903071503050603120d0903051204050d0206 60
    0x100e1880402a840035004480c031010382466030650045401c1401c80030004580d902d80031421034040c1011410185542220740171461013142c070304503001e8211550030604105028110510380305584041c81d2450008592205a110401659001040051400409001c02d400d0041d24021039510f0516820a03034401105285524152100c4020070210000c8040201d02c030303070b0b0395000004024010504415140d00317088a4236500d070080b504114a201091075802d4081e0708044040500300c0e501510303111030003681c2449200d6568030048003203500400340c02441d0303641c04440c000140a800300c2c94002408018080b01c6a00312400110750707040550100a440da0318464a40110b41503030343c48000030ba443d41714000407032143e01a515410780c0c50b000c1c840010880c43e00508805030743c50125902401540c9401c1c0c18181c035050340c85c0001aa4400410143c1102d07012500301c4601d451091030319074a4000a4800081f002c0015101240c0c0c41e0818200d12035115810801d068121040c8081414040c030f0714 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 455749289 1250 455748039 455748043
    0x30305040209100e0c09010302070803010e0709091a0402030a0b03370203060a02091201050408130b03190c0e090c0304050f030a0e010c020f030f010c3209040213080706030501090509 80
    0x384070105c2000c00244092107079110344c060318625035204829039106d5860342804050f2030001c0300e120380001c91007070002a0b40f1545005e400d07100203c0601c85581c2011000a00010b03500007041d62034241e8440184001e16182000010300d1716401d00e01e220020100e00300074106d01c044807031014100660100e003076400b69a001c183d894200b80b0520340103070342d0460300d00413171083d44000103c0045035181c207081105200c42c04008068852208003002d201c1c0341ca40b11039040c0d50000b5603818031200d200d8a034185002c00e8942c080c0782c50311040d040444003100030301c4c00a0f4221004030782240c02864084244800c0007010060000011681d00c06141000d4264500400007400045c004d030420100505030700541d12a552940510f01001d002c3d0b07620030304265802e0b8040d2503400038000014001100b450380e49194900740c403900048a850781c00e000720682002c0d0707070700d900281c0596500650030000b518856104103803c0c40107080403800740c03100c40d24000c80a41281e905030700c015407a03814002004082080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 455750539 1250 455749289 455749291
    0x5040c0e0402180d05070503010c03020705150603031905070203100605031203060406030f030f08060103050603070306020c01020408070305070e060a05130510172109011e1209030305040209100e 85
    0x5460060f218822003040707400e041292642c19410420300340014003800070118040c0182d0b142580244140d5104400490485c81050340c050269041150003126003680082e80700e1300328800508070790070b005881e010324003405008502c507408100300180860441c05c0c10300c8014045c3c088080200145072612020a442d105620b0313483c6801c130400400030b120b983d40c56108201640d004800035492114518010f4505c000c40c5002e00c01044031138000480c00d40c070078000c0f00d110703202c007901424205240d607460501940080b0004542c65400340408034444000b00b28581c0194003032001403000a00c1c0103092505102c01030070746401000003820910880d1966441c3c54114110f04c7d40000b9240c0c1d9516280380420584d4002121110070844451100400055900540302c002000700070128080414a5410301c44c008a490200c0d058516841144800e04040d00c41b00b65503003050a20341c15075846402c201d842c030b20804ca0129a90394140819803d04041442d80070852610380d030040e504000ca4000c0d2208 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 455751789 1250 455750539 455750567
    0x141e030403110d0501020d113106260f06100311040302011b020907111018030c0201110a03030c03050903092b0f060e1203041a0408040b0c150105040c 66
    0x112840c0c0750400130254110380b403480d4464020400d03444683c0407544c0c00d40c042210100b800002c40c1c4804c0c2e0b40400d1402c1e911080b18034041c10076030765182240980300080049030031800e81d000581c0d050248400c6034034091180f2080c99403581c3e180b611008111080380380d1a4030204141c50440c203106014032040c01c44080d02d4090a201c4140e0900b41140c02c034001c03031802c0c002d40040020086c4210280c1120004110100d031200f507070610b819901903801111010030800595003c14001440030134003444100c0c0a090040c90a040101401902240b80007122001100040c0c2e983c20081101a0305109e495040b04007007010318640705484000800000c0841903100846003501d070074940c104031740e83c0e0b140d1039103900000950804540c0e0030403100503c3c202c8001d00e490b020300300114201d0841a4100e910543d4019449592090310b140080c0003c000284100e82c103000030880800c107a201c207006400c00400700307001010304060041b551001508113a01c040d000741e0030300d0040e0b00060380019000140d01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 455753039 1250 455751789 455751799
    0x100504050f130f150c11070b0c0c0402090402130b0c010f05090d18150c050c060307201e01050604141311040902100903051207020a060e0409141e03040311 68
    0x5040e41c01c1c030740103600c241501c1c0713a54103242200741c0e52095086180403560700c41040a4030724070b42d522600a1118402c0c0640000784c0d8000982c4070005103000c0c2d020340446a0041c200505101c01070f20f59241002e16034001c060f0f000c00225821051400074041d82c5510f2010000502c16810b10302c0086d44d480c000d03100c1080a0000d6844a0707141c1300d2000c115100189400b001100a000040d10090001106d0007401c0e111401024500c000c54240b185c00c80303000e803046940b4818640d900240500180c9011410a0030782d01848481c24442034040c00b00c019401150320000a07a42040020030085031181e07080707040040014020441e203043c01e941020711044c0c10200f05885407440300b0000d80284068140250f008a0a00000d084554080604e03020f980c4110b085406600c8030a414848e00d0144407002036100c1a01e0ba02408841d1140fa81e10302202c101400c0814031210710b654500f0704030000c081c40344460f448901a09d2800b024030220368480c41030840514581b0341142c03038101e60300b8580c83c4a5400b81d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 455754289 1250 455753039 455753063
    0xa0b060705062e0312020c150705010e011b050f0c0a06061503060302100c0c051002071a0f0703030209010c230717060406050415050c040e07030c020a02090a090b100504050f13 77
    0x201b0300030702c03294a2078030000303090401d0324042440340c8891350080300c01525558680204600590070500c1107a0400d6645210032100e0381010303c040b02e05620541000b4152002400100a2400208140440c0502c14400450300b2420450b40240c107e1149001408060403c1410805a04c0344245400b51203030381d24224084230f040d42046000100c150f407100c2d401182d40e5005081c01c3d41d01240010507541c1e6101020410b0a248180c8000c40c0102d41c521140d0080400141c1c000a000360300401111106050404e064580d54071800f8940e800c10008441d9418403d0b0301c42c0e2010001d022040240c00c03a24030400304240300d00c4502d5511400100000d000c81c3e80c41000c18144004030710900d500c0c0340c0130350082c011440c00107491013554010740300d400520400800030500b100d0280c00340c0d0080c2a942c1e070062800c0f042179003c01c969810003030000d501050b80e1704042004a00082c40c0c0511404042c0541c556440c03900050200300c590081c40100243d00f2201405a8242c0f10221030355040c0d00640d1442c59 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 455755395 1106 455754289 455754323
    0x60e0c030a05101a09040f020f0627180a06290703080705090a0b180a0315020f0912150106081e0a0b060705062e03 51
    0x350441c19020f140d803801c507801540d501d180c50300c845400105580200e03200000c10b481c00c1e07400c003c100071000e095080c540c0c8940500d6005940705440d005800d09008a44480c1c0312520118aa6102400d220f80d900c000098040c540040c43c116044d080110244006144a1152102c003440199200e910707800b492000680c15144001914a4520303141d504a980c003500030828001d00ca0300703000c000c000c0e80304d030209071016000c000076159650003500032540e90680390440a034801e20145c4400d00c0040c20302c5280011040c0001e07005a1510b0705580042540d006070303540c2d2600b041042e035801c890711400107420000c08800d0300f024109a600c4600c03c4818250841d0a0b1012240d038003042c451001c20094501e90100a0b40030010b550b12140c0000740840d80040d5007900e0550002c418401d102504030102800200c401035450700c14001c00d038440c8104405488003401024071480c0d4900 = true := by decide +kernel

theorem cover : BRFrame.Cov 455575539 455755395 := by
  have h0 := BRFrame.cov_init 455575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 455575539 ≤ n) (h2 : n < 455755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
