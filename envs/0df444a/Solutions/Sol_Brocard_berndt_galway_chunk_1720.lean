-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1720
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:25:39.951844+00:00
-- url     : https://prove2.me/submissions/88fc904a-7fac-47fb-96f2-052077e168df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 309172661 ≤ n < 309352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 309173911 1250 309172661 309172663
    0x20a1805041b06020d110141040b0f090709090302060a05010f08151807060c050c1503060f0a05121506151e0c030d091505060906010c05010f090f0b07050408 69
    0x5482c0d500b030300309007500b1500746c9042c1e4050600f12081248000c00c00000411699040c00000c01f841616600d080c88199407120800d49042c0840c1c1c09440c0c100d00c140400e410074084000580d10014a1060714400b03a2980d4840040c1c0c0c0b00801c00341d00580c40354050082c400708034462503005041040940c1c1d29076103041d54450b2602c04020380e00340d0307600143c00003035540ea01d0440800035103600041980c0d0071545825000d0600d03542948140ca06110f5106804400c2c14038051514036280d151603c2c500303555401c8200010680311030080e9030007442c601e00000701510b4a0303040c000743c084000054034020001c5000c040c0380e102c00a080030b109030302000c42001f81c00c022a0464001c18049107028814806075116000755226140c0c064007640b00028050050090950000e650301d44140e1601e07206004a0041000b681c1e004c1c0c42003a404150500403d03000d41c01002d083c088d0510bd040086111000448000d045565846082e01c1803851070010780b0401208070381480e80000c4500b043c90401c0e04110b051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 309175161 1250 309173911 309173923
    0x11132a09050d03020f010e0307030807080105210c181501050f0702040b030708100603030f02032106010c0b040605070908030a12110702091602070609051c020a1805041b0602 76
    0x40780c01051060a61028140700340f08100c0e808410340024055012180003c0d59654002e035005d500081826010509251081c0000b5049a00c014090012501d0b11a000c07141c901c10181d48804501c51001d19688540320805520003091302c030084c1c032242d850200e015190741003004005504110041042140c890842000d03180f81640650b8006420140f2002003481c0c0103035600302c0e040912401c04d003400d1614203a0000400e603480303540d6603035080180c0441607941340100d07012021920b84d2010380003200650711492540c40344051400341100d09858640d416090340c2501c0c19200651100104030701103802c456501e0081c500b481c021071030040803402c000c0880701c0a2100c0c0b008141c0743c03a41d1025000c0d9100590f010103070000c02000c482d0500901e03011449208140000242c09150030010340240102109421500d0140c4444444040805038001d00d500c641c000301e80c00a0700c644041208030885c0711611000628010000300c50500c0e0904024030b0760440b11042c040d202000049c40869404101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 309176411 1250 309175161 309175169
    0x103051c051c06050303120a0c030b1003050405030d0f0605092a2a0c0a050a08030f09120a080a090504021801081b03100303141e0711132a09 62
    0xd2840d00d2882039402e1070103000507a01c1543c2c035200c04250020203003070360808030f4098181c0c802c081121120921041d4103480c1003043c0340750300c000e244070a11706903406500541c1c0c1c401d1007002681d242c0303900d510403c4120b5a56444040c500c41d80c8e500148811b0400500040c0c10903130304100c0d4119500000b510b032015030684d00d8204100c207004100d03072005003030001c403140000ea442d091556000740c142130b40b1641c1ea1088150075101d849106400146810049060016100d141d4080c502e00b070795502c0704000300d0340040310554000010100300910784c0f90a0080c01c0c5a18400e0540558503070441d40d0040c240d42c0d541e0000d9210750310400890024050610056121080c20b09241100780d03281c10310035400031080201ca40603c6400010850000d10002d100e200307491017030301d58001500c7c4120b11886107004100303c04c100c41c42c0340044200155114005041403074455000401e0300c1680002081008502d0f0002280f030381c3e264100c0340701108420a4454048050805282d00d0144c01c2000070000c1c41d1500c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 309177661 1250 309176411 309176437
    0x10b0310030f08130902090f0f030d0f0c080406030e2b0f030b0a080319020f0a02040b0307030c061e0509011218080708071106120606030604020712080103051c05 71
    0x2040e0000c103c1d41000780c40c98940d000b54060130150356444460003a511201c4800c0c45a10040000403641c94801141c001d09840a002030032500034882c801d0342c50300c681d2140072003848002024440058911030003031000c0c00c0160340204003078070224170641c90050304444100c54080ba41c0c034150b00c218144221940c03008814a40f0800d50fa04240d030990041c4080c1c6540c41e0084403814020882030f400000800b10f146007403014404040c1c4900703081340c03280103120400c05a600710f80303000d078050315007900168045c60004040c1c0d49290760782d07071b18020384046a902c40d00c0070510100b10782c1d20624019540604030041d44c24954a481030701c0d800204070b10000e09240020b1640c0705030003040c4181d5100b003100c6003903201203207503981d590609203c0440d402c0400201e500504a001074180307810141d094403200403420001c582c29486000070060560401018140c00680c288040310221703519100307151040c5a9610303403441550441c100305042c00f41d40c0500d10030b4400402124090140c0c06401c440036030200304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 309178911 1250 309177661 309177683
    0x130803090a050a031a04140613030f03020702090a0b1f020f0105070504120b0c0d020c01050f06060705062e03030e0109060302041d09010b03031306030f0b010c0308070210051806010b031003 83
    0x4548003c47d5028900f10762014800c9004020801240004040541e80640c0300c40c2848084081d084050344115440290070a102e2404074042000706c0d0400004100d0080c0329450407400c0c081201649442c101036140140c0c00b8038103c0158000070710a0542040310352070510310300303410038654400c8640c0c5560004c0245014070000b0b030307203030901005980c540208082d00b996149441501030707020384400c0d0b8004902d00040004031307900b4078000b8211010b07264032002520340c3d569045c004165200c4800b07a47c6100750140c0030800c1f0010b4000e21804040e502c203032a0300e5502460b410004201d0fa50607044581818410002444101e403c04c91811841030000f00541721651502d0b6079070b0140021020981d0144000b2682440820000d134040d410b54400e580c0c10065090300000c140213640041c0c05e080c0c0400da41c0c050b000c000c44c0c0314a84a99000c96540115902d990a03c0402e4085400468424054401e16418190b40c0c00c42413200600412184402c1c03400c50a00ca01c2540a080082c4402014070f500d031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 309180161 1250 309178911 309178913
    0xc08030603150a1512050d1103090a171005060303030117032107080703020f04030305032a0a02011d1b0d0c0e01090e0102070302120f130803090a050a031a04 69
    0x20000080b032071030701d030010b40036a00302107076041d0103418880e11006254113410004541051030302c071518016a040002081c040e0064002650407116840f10400d0501082009010b40c0d21207041c540010b14020000c1600c1d0911505914104804180001e011038200002c5c00040d03600001901c0c1511080800c806510074032405449c910300c11030070561020708004a24114105503c40580c2c0b080300f85446041240c1d5030318401310700300c0c4107100c01842c41c0f1409200c140007080c801c0c005154481d1503940e40f911031001d41c4441c607503841c0c07580fa49840140781c00620f842c4c059074203000707160812404440b0000c080c580303101810740b5000c580501d000e100101c251000c0c0c40e5500d242c035203000540c101647c11120350b2240300c6804e1044090080c4291382d8184071030880702070414401c5910f038541507400b138a0b240c0031074805021a548502c0c0c0c82007803804240000906844400c00f55401842c81c10015035484440d1414841120001c0c0e010a01c603d40744001000442c0e04040d00384240f80e501d2030b1f0402280d5031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 309181411 1250 309180161 309180163
    0xd03091701090b13060c020303011203050a110a2a1404020724091b0b03191d160905010812090d0c03080307032d09020a1a180a060c08030603 62
    0xa42007003d462011040c040c030502c00407a001411246020361428084a1360b142c1080c0e0341c0c1c0c8000e116501c440f0035a50b010360042803040002d041c00c0c82003843c0542d440003c1060542c5000e407055000e50704003d254140d0088241a0b00128128582e00070700c4e211700034500440304556469241005001d10307000601c0da002c100102491442c20404444e80030f400c0400c20022600a0220610031180d40f95405000b070b00c03030944030341c200d8115042035400921707550b542c10b00d001c0454152501803807029110400581001c2d07410baa00c0c050310031424014846045078110421000702039502000c09130785001e0052204600115034080400c00c1540d1381559051501d000c00c110501404c070180064039500340c04010440034100843c00b40c81b03190341c14403039030b4215401070b21307525584803080030740c55082030300b040391001d481d000b04100c02d0000b0312000c0c804d035450310003031054100521b10840d600000607000b084224442c0c210141d090080d59146030803400d21102030030403800c0c0c110113030003035101100080890f98 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 309182661 1250 309181411 309181421
    0x9050c040e010f08060105010203090609011110050129090105090d1103030f030f090f0d0f050408030f0702130501050310091b03060b1311030112170a0207140d03091701 74
    0xe03081501c1ca242d81c2d16840c1800705086401a04824000d900c00040d0079840002921150100140264600030200005440e81c030b0306000300c19210f00501048a00c0100a4411315000703041c0d07141030002048a8240801d0901c0c00140c007500c4030803003449045441d99101c03056843c00b900c1642c502c0c000d807071a400c0900d11303480c030000b080c1d506100020740300c1c910301c00c4030015501034150725048508980721154420b0b229944141c0038200c03940103100d9030300d1192280c11122005030031070030704030301d400c0e200e407c6a0b00b1035200c80303420340380c202000840c2000c60911411404402c814000300300140c0d41040c00203038480c0c00c403281c103a0701d490702c420100c0c0500c8844c000103200c0c4a40b01080c809216500e04d0400d001e441c5140070107100e4070305031540002002c8503002d001d20403d10000c83c145581e08082c10912170b007540907411b8402c10010301c402e1310500c1c0100000c00c01c4182c103030001d01000c2d141c200400b20350546240c00900400d0072501e41d03400207821810740b40988110350b04410903e5a0b001041d40105 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 309183911 1250 309182661 309182669
    0x30b06070c140406170a080a050d0e0109110102060c03010909030e0d0302010506190e040210020f060405030903160b090f03100f02070506010902030415091109072705060409050c04 79
    0x101040d07001409100d501d1189422007810b9034248a402c4c0e543d00381c0010b4000722118001d441d0480041800010228001019540f450b030130f0003410001d015207000110b403c401c600d400e443e035443d0502814800d01e42c10b00c03909850700748003c1c807082c9040341850405000c10b00c03441c070784152122030301010903000d0380c58080000341c0549559071888040c00c00038082c141c2942c445000c0d035440d10090300c02003440701c04c007002d03031b46840c050008075111642030004400a40d5155011401f841c2040001100180001030240b40610011a2500c0c44003003014280ba0584940c03160f03440700e64404101c0039061806650522100b2540082c0341500040448c0c101486000c052107403134036014000d030011459601902219010b00100d1b03106a0725155004100e100580300030b032210146001d601902041c40e008481000e03c15001c0402000f800004609494070941e10007002c600d044c0b5103121000b90131400c02408030000c1c080444100d00e400c0100d040c0344243e0207402800358031800003d65108103801110010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 309185161 1250 309183911 309183923
    0x516050312160f180b030a090506191103011202060a03140702030a14030403020a020607150207030509121501170106080a0c0509010b1e0c19060203010501020d08090a03030b0607 78
    0x1501d801d6100c0d10a0702030000440c0b02090f00c2d4a40c06201500c1641c0d1403030313403020b48501c0d8a05642400f00e04040ea400080001e003069882c1c490000014000307103c0035000d03410f01803c2d45006c05000c40c0c0301e0f050f0703030660040c0070200c1c00074001003001d50502c10351110041d8052390755036030742c0b03827598002c40151a4054000346511650010320641a41c00402030001c1d01c41075490b00e03094500b0403408509803009036400f41c0140e0201a41700301624150004003010780c0701e41034541226050100d90416608002001c1e00801d6000c1018080c40c06c03d2685809046502c0380641060f03002c4058091035004180546001560b02c024000b0000c042580301c54007814a0400b00c500c82e254900e01803030f04903c0d9000301c90007400b440c8000070b0712920034015210005003000c4440e014000d08214a0903a82210031112031034803820110011026030102209110350007220013603901d42c108800686054407400d280010464003000300b0483c3d1401051800c0320741e60520b0b010808074940030001d145070203248005000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 309186411 1250 309185161 309185197
    0x180b040509070609050117010608130c0b0d05090a050d031104090509070501031b020c0d0204091a090f15040210030e06072304050d121b11120d05160503 67
    0x10000b07415411184560340d0b1100268480b401140c2500304240214500040d2000502080c2e004800c0d065008503143c02c0742e034003d030f500c6d12040e84031807503584005a12080021206602030241c0502c0b07a00800e148020003103800d140e520141d48400d01e1441b882010f50300c1c004280c240146408070b070300904070198184014140100626118a1140704c0c140c0844c2c1740c1003180301414448150015070003156000b0b000a8001d0030709000c0301c816001c0b802c070f82c040c0e9103890800000e40c8029070000748540c1c1000c4012985801d800307451800a144948190341d5101f103080c41c651118117440c142e84190705844004480e8203244058002d4440c10100060a014010030455200c0c0d06c000c000c07200c2e08616a48400301c0350406500890f600c994080c0c0b9421000d15041800814040c00242c5801b1401d40f80c0036000d188040107605500428180c201c400021301e51400c0b00038505010400c01d0041c03800d0240c11020140340c0b0190240c031424000581d164602d0b602c0d04184402032050b1002c04070084d0b0080740d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 309187661 1250 309186411 309186421
    0xc0f0906080c0f0a0b1c020a050703090b16060b030102040b07210c0c0519091d070b04050603061215040809100c20030111040b090310110301180b0405 66
    0x54000d500840400d84110004620b5920b002e0003c6400903001030070310280941848034000c0c0540c00309210081c0c0702e00003075884d4030401c20b0744028150200255940740d2589024034000300710030341e5036000120400c001d01509400c2c0410510346817589610210005250b00701c9804240607020310750160424401c00b09181040c4000c4003150000d0340c0d00300c1000540403004000690b100b00080c0d1018018000d0f403801442141417000e58400b008880c0c43c6080038135503903030344044141c43e201980b58458011b900c00303000703011404003e000302900035142c842e410281003030085070030390000514042c03040500310b40e102203424041c0040035001744010038610707541c84c1a040550007917000c07031506070141030304410400d80103101303100c0206802c2d44020f1850313401c0200c986042407030344d40f40703190341c4c0c0b5540c0e03503a201899a006600400c020003030080f10300c0d142c030110320400d1300309240c6815004026041442007800c5000d078604a0b81034560101e880640c040f10803141400500d4403500382d0b0307040782c0303000306000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 309188911 1250 309187661 309187679
    0x30a0b1807051b0d0203040306020a020a050a050f120909070e13050f041509030c060b01030b0d06050709050d030f03052d06040b030d05030a0e0319030203190e190c0f 73
    0x1141c00681480202d903410601d900143c0d135064802c00610068100f400309000181e03481d001014840720030300c1290405495a00c82c18180b42c00603101f16616480304094120401c810321503190340c1c018040081c0d0130310b8540b1001c20078040300188a0343c100104013443d0656541c882c003403c0301c8596101010030180c548a04d503446e038160242d4094550051100c80100c100c0428021a0241589981e07105022481a91000064043c1842003414151a86031840c0030307440d458a10135105004410200d55030801c010041c150a8845d044980981005c15030100071a41083c5c0c00000407000380f0b80001d841d551010303150070700303520644000b841401450000c5002440c15066900480c0202c42c1081100f400004240d99030b00c5841d0b02e40c021030300070320014001441c90341c007400b00840544140d03450804140401039280398003044000c08a0750100502c800718000311241456a4081c0718100100164110510398808113413281c003c0d001d0070035550000301720000c86018000d1010125011025864680c03035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 309190161 1250 309188911 309188917
    0x20a081209071406090f060c030d090606090606170c0f03010303020c0a050102071214120309070306050f190e010b03030a031a0a140d03030b030a0f0323030a0b180705 73
    0x48a441c4150700300802c829031110100c14031840010400380c6005c0d840c0c03003070003013065058002c550b1110040c0401d03004058184001e000794001208001402a194074001302200c0343c0340c020040c058900380090154540150a91140d80440d1050142c0c565411940ca4028403403100b2217a49410048000020190006840600994101c0300400e60907241e400480e640c81440c8100b00204000c0b8140c0004100c6015501f48000660401d80707103041d08036007843d007c0f0f5205030f41280761640494001c00600020b032142c07a8000103c00b4044134103041403200c1224082d0011001d60515a40780c1c412074005800754050707949160060207583d1a80448c40c000342c020107410521741825100004c2c441c280c1d14080d0b29400580b4007141d070348484078800c8001e10a288811101c12001c0c543d55030001c1c64580d400b000020085403085807051441e901c945030003400c8014060410b0054501303940442d41071031208040e03da00c680c2a05000070503e0040d40043c00070200c562080091a5940c400e01503202e60100c02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 309191411 1250 309190161 309190171
    0x40b070f170702040c02010c021e03071b031403070213050915010305160614121e09011e09050a0605062107080c0a080a061e0218131515020a0812 64
    0x201700440c0d89800000c2e4241c400599412005811906194444007031900304481c40e00300300c0d0100da007002d519584408009500450b01003000c403135440c041040094501c200d03004046000302550400d5031650110f000380b00100719900324545c13108009104010100300c545919014190b25120950b5641080c540301c0b40c0404000c0400c001d48400414454064803400d00c032014070b00d0b000740c50141110a040110003000c3c24042d4008101018100b540c461201541d0140b803255000180c5a11400800d0003070a01a1103040c1d802428051440c001c40c80105a03074124503000900840e0796a5404001154003417400031500c0004c6059451040c4010f000886405903681c9a04486203c1e400f601001030042d9035100d06003d0354810300280c40020b84e507070028500d002c0840d03002000546030904003001e030b07048001890b50302c0205aa01010500e0400c0440400f1800b0460030403000100007a40101c40480d4000c0e541c1c0c99010100100d0600d00c00c100c1028255040300107070f501e030102001c4140c401c20003620 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 309192661 1250 309191411 309191419
    0x601080612100f0c090e0609090102040b1902100b06070b040204060b0c0c090702030306241e0304020306060a0506040905150a030b0f01050901060f030c02010f180309140105040b070f170702 83
    0x48034103444c600810185064400080a03a1131386e03559041007201140700103200f900e5954090000040001c01c00300603000240e00c400b00f04500c0d840bc5c2c1c00c001d1510f1042000c107850740e07041c41d61301a210346840c001c49010300d03000f090900302542d40780046806070000d0340c0312201039035001884818000c4042846400450300320742d0f880040e02c030540201d1380d0740410341d0000e40c8401c0c40c21040d1101a900d802500800c2400c82195040003035552000c6001d0306165246680700400000304002c40ca0248011940142c04a442481c140d0505020915602176802880340e1107a50b4000b04030090222414101d00d40401414000d02584a1510100001007910b0a0385000301043c0041035030714020f0006410f0320416942d001039200c010008501403c007186030002955a903441d1a1000c1603580034152442081110b000440709171443c0080100074541c0c400005002e0501038000c41d603074044c3c126800c03110310410ba2a02c2d80c00b03e081150084043c201c00400001b0104040c4035103000d0103000d0040d0074000c035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 309193911 1250 309192661 309192671
    0x8101e0f090f18110904050c0a0608090c0409112b0c0f0b0a2c030f0f10020c1207020a08010213031218053f070b0a080601080612100f 59
    0x140d8165203d080c003500040c81e000d203103036409030385080c18080180e02074003070000c0350820360110012031072440d640c0e04800c1c0011000010801544403c002c00f01c4014801c0d80c082040022a8a07446100b22000d65402e1080c01091401074646007048209a0550031060841d8202d070001d15206508401c0c0d845035101280820900060210344181692408042501d1700090316004080d000040929088004415910322403c08926241000a00002d10100000300246a0305005075032901000d01c0c004480f19004211700b400c418800700705504501e0300444074544808080c4009000c881d01600801000d6101044c02c08d02206078101300d2023102c0c020000401c07101602e98040307900e80c0b801079500c80010b01003c000c102a041c000d0405d8807900954407103000b00c88803111070f402e685a030034404030700c46590104154002c035801c1c00040018840b00d600b0030310740301046c580074201e040010050341c18400d10800041c0d8603150074916951200441c42601d100c00b101d00c40d940010300c80b0822201d01c0354030700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 309195161 1250 309193911 309193931
    0x20d090c0b040605030f060604350304061403070c120201050105090709050d02010c080d0c030902090a090302100b01031401080a1407080307020402030c040f18050708101e0f090f 78
    0x103000702e40c00d883c007590b40d407403550b907035600c2c21140f03000098503080d00440b003000001581d01240d000c0c076025140400d501881d12000208600d00e00300075100315810b030703002044204409500300e20070207009012403d4943d00ea558281094600c21034100003d459840b14440110380107a041d4040380c181d0350704450070000e90b01d41d04c0d42122021403502800e6000440005d1040c05036011380004400300c2d118001e090f2401c540041c0c41025904e440c1640004240c44609400840c03070811412a805106074104100002e00307628029512641c1440c110034081e81c440d046a0181d2103500000c810420205c102e89040d65107121141e900c4003000402c4d11883c00c1d8000007034003100702180b41c0080720300300380c000c606050250f020000254406400c0c0d01455200300300000d401d80429592a00406100340100d1882ca02c1603511001d445000740040f04002e00399081013090300c8514500d2054400005500100d00c41c0300d044011418640d4000c103943d0032200d0000124522070f80c10030f01a44644110a00c200307864 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 309196411 1250 309195161 309195179
    0x1508030c06010f0b0a0e040510032301180f1407030606060e09090c010801060e01091502070e0c1e0c030c160603061a070b0c040f03060b010f022b12020d090c 69
    0x11748124007001442501a40019142980280d0313046007030b000c10500b0703040d074a0b9601600c800f0007181c0c455101c2d807414480d011044080c400c014480b40c0000c480c81c0044040d64800c90040d01b03000c0000e0100000200c0e4542d43d060030005d9074060f6900007401c2240d56202c0c6c901902030140040c801d40704a42c0f01001400c4e01c3c501051b40407160b0342c1a1200c1203140d0030480c0c240d03600c031412200303141003040b0345030002095008140031916410658025182050034604440307181c2c0c000408008051804105807102060044010300548150f00000b42e01c5c0d00e4030362903060840c4650744000c0c2c0c030361107280604000d10001c1c0c0c140508951140d101088416514024445032001841000203000d00921003040443c0c03003010856480300d00000000d14041c1c965010800c048403540082c1c07551075584070307080103958201c0105502d105c09070000700740300050a02c07440344a1904040c00100e8840c0d0038081052240034840440d00c5104006080d0344a0b03020b884403800a140c592415203129514000006950314 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 309197661 1250 309196411 309196417
    0x3010906170a0b06040207020604030605101a07032105090105090f0d0219080c12071e0b0a1e11030a0f0212040f0f02090f0f01271508030c06010f0b 65
    0x24081e0040c120408050312004040c100040810740c00980070094100181c2c1c031000240055441401d000426003004070b00f00c3c01036036842c0c01c50040b182106c44081c0d01d044119081d580460381c10b1a002d008030485888540c54100080404005d490070941405480700301034019510800d0450200c0e448220703c80c032826034514400300b400d0003503000305050010140c210401c1100b190b014040341c3d4501412a060b0610344800000009019800451202c0c20015401d0304800c840744402030020154a650b151107041420103441c0310f07901c41c1da61075000c0d01d4041c5480b012040c80c0084a00304503202804102810580c0106c5044e21060b1070f120160101414910a840405100b0301c003460440d62265030320b9040500d856000e549410f26560004d00503070743e100c3c0591040c1098030402c0600d06000c6100325500340c06801084c00d00d001d902048810b8a40c00c800034100c40605800452800d841214481c85030043c4c1d00044018040000c840880b8080000d01030b041395504904c01044075620300846917140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 309198911 1250 309197661 309197699
    0x506030c18060607020a06050310090603020609130f02040b07021201020703090324060f0302011704030203090114040e0906061207030c03080318010606031a030a020f100219050303010906 82
    0x842203451207000c19820345a076405600030340960310707040c40c81d000180c2c403010310f600c0f40000500c00810840c1d48003400c04100c0052200020074499541140d00103006405880d030014080c6140b01081154805940c1260340d2400c4100e600310355840e22040d10725507951010000340c0c000c7e00c00d0800404460030502c00c13602c070160140c1d60489034a003584e0304ca4030040346030100340c6601050b400d500c1a4000ca20b00c40c610081c03609003105001c641c503503c005060140d8500104081041303020401c40402d40120844070b01070400d203020348000a0104001c259070255402c00901c8417034580403c0070221002590314040c81003214002d40032120100c1c90366984880c2d02006040c2c0d0303004941000004c00840c050368100000d0030501000800d00303201d00307084a42c140c0c040720000c0d07294441c1d10881404601c1180000340c1c2500540700b0010b440d004500c421001403021402901074109890813603200f0300c00c4041a04940214980401c0d0500342195207400238002e0149207450040d00007203840301e0315180b40f800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 309200161 1250 309198911 309198919
    0xb0109050a0305100209130f0c0f03020a020607030b030f0111071e080702150405030d0905130e06220203030318070905070206070f1110061a07020a0b0a0207090f09060506030c 77
    0x3071300c2d03e00d0f100d00207074225408403074014400030200200c000e4140120110384804040002e846503540400501003180001190300f81072040045182107176011800a90000c0e25060104580b40344801092400b40480c540c0003180d40781050440c0c7c45448034005200c86c40c01009004800b00103900d04554205101000402c0102d0400812006042c21116411404609010f0a0a00761303184042402c05804404480c000384030000f00f07024610341422060a0741640000030030200b07500d1803040303941d100080c02c10400400380c0d60401c170f06000c10200d901c8504da8060b00383d130740328242051521101e500d0440614000d0080141c04500d2040b60310800d4443c00d20341d07004101546601e141a40c5080e20100041c0400101d020700000d07640c42008211084100e4081c00104946401070006400c030b803032075200070415400c000c2c1a015030344180030101030716216810079036240d09100099240400380da109181503400d011000300203040503484081110b005520034000c0343d480c00304264a030b915003101d142e48 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 309201411 1250 309200161 309200173
    0xe191d0901110403031b0804030b040b10060f1b051507020106080d140702041d0c120d08040b15030105070c1109060a120620030601110d02060a020a020109020a090b0109050a0305 78
    0x100b4850046000d11103220343c6c032510a0406915120107036070090300b007581e180c01014144020810002c01e00c40e80161040301d462400e5003071880061500659030060000c0258850b83c2140510310034283e1507415601c0812101c4801640310340301c07184401202d26202551a0030400070342c202012030078441c0282a56203107110303001622083c8050307400040b07081e41c005581e0031440c004002d902c2c00418485070b0f98002884580516001c00102c0c4e088200b00580c113801c030a061070382154118202541066104042c1100c0350b4070540364120110070b0314140c1c2d905600307200500013003681142c40c5182603409030480701140c080b01c20a015481500340c0301141c000048000801c94860510480400c2d144101c00208103030484500c00340300311030b60704a44135481e4000003c0c442d456820041e420340345440c1d840a4100840e40242c0a034981c04020b0180d0305a540000d01c030202c251003036000c10055030703000703024090942d101d004070001400e00361009400706040380c2c40030401e89080d40c111000c40380c1c014000c3c22 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 309202661 1250 309201411 309201413
    0x906021c0f031109090703020d18020a05010c02030a050d0903330c0912200307080a08090f120f01050601020f030702040f06030209010306020d0c1e0e191d0901110403 73
    0x100404480c3e420314034031502401a80450342c0c0700c1c1c1089000305404d603000350300c03406250900c0003103a200140300c1d04040e00c03c2c0e51580060b11506240c0040f25424244504150254000320b420401c00c0c190060060285400c48030406400c1030381541500c0c02514017048004042408841e0005003c2c010030b0441145881c290003510260810400c90905180420195968a69140c038450794100211a00460700e14400d5075103a05801d40240c40e10120700408800b86001e04050703d4180e601000340810704005481c480b9519903200c0c0b41329504028100084003103200041544541e4403848508095003802c01081466200080016541200001442c079100d016400c000040c0700704001d035100f2648420740040544c2c0c03951880ca00950280c4005a035500c000c07503401e811550cc1281c02020b10900040d00c14104450000b102564621400c00003c046109000a4201909880111804052422b01045203c2c0788030300810003110302d9400480c03d84605026600780c40030064544426641404104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 309203911 1250 309202661 309202667
    0x1e0702011d1207080c120601030b07050f1908040b1b04060305180d12050a110904050a0e01050c131410080c0408100c08060904020a050103020901030e0a030906021c0f 73
    0x860700c024014920000c2100901c903807418820b0f141e201100b81d0b0050241d142c064240040c0d19035441d0300c148083d010720760450780c0d00c0461047c00303861401004004520804448026021909046030402441c0c844900c4024001c01c0c3c00e45c203e0301281e40e2142100403a10503031808040395032041c0000e80982c01d04e414040c0407801030030b00500e01c4000f00c14115920004800600a00005904940c1c0f002c417842e8941c0000419148058001100145042c4480c0c021240501c141c51100c1012200403d50380c884030070346005800b08a00841c0d0a500c0d11062209078001c500062122002c004044441c0d00c1c1d5410606540a40c211120f5800591441e4040384c0b50707202d0745600e507211b40d00c0c80b01e582c1001d441d40122407500f200e8507610f03034404d941c0d01c80401800b83c001440583c000421075042100b032505501155020b210341c420103041c140c0101c0c904065a00035040801c2c800301340001c0f030b03600c60800d060050080f0841d104042c05805110511001c900352404281c2c80d0780c505450300e0f512400d1444040f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 309205161 1250 309203911 309203957
    0xf07030f060312111005010308040f06020d0507020d030302070204050c0309070b030910051012050d12020712122a030e060903181f08010807140102060115030216081e070201 76
    0x2c12070501a4802c2c0c85140f141707501ca01d5000e180100c04140d200c40c20200103e111590340c0e00404e055501081d0340002e0540d0140441d840b0700d40c103035040c0044044918040e80640581940294407030705085c20441d003000039102651240901d00200d407445540c0d08076040c198802550038501640000d000120f140344590802c603046012002521110340e680d403900c0f00c0d01e40c05564101c071590804181d0145041d84150112180500303401e046241000076502ca0801d1002d079070700c4105020584c0c86441000c0c00f41d61210903481005c5900c4480c005403d0101c0581e00007440a81d0046807501c1c60380548400006252031254100030000c524003440c60500e8002c1d03c0700c1080c0346a00604c015040d440d404a1481d4041c1a0080340d229001154140454a1304105058124001540444803820020303a400601c080c1120078210320144280000101200640b00d0340b40a5001e030202d81d0030a00801500c200100194102d51304051031945400e00e602c00c6602c600c40029001803107a03010301c6c0501c0100340750 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 309206411 1250 309205161 309205187
    0x30b040c1b050c03060a09020103051503100f060b040314010606080f01090b03120d0c0825110705060a0c050d0306030c050f010e030601080708061605040b0309030409050f07030f060312 81
    0x120f41080925800003403505400301d889021058450011004650309401020340082c00088100d03491420b07a804280d032618071858200c1003035120348040410201950100d8003130003c0080c807542e030319101c1c03c21210b04812240b900c071556180c0400010340c0740c40354090238020a07040d0a00000d80e4a4682c044024110a00302d10b079040c00380b06c40035003030962a440100400080444017080555020303102500c100e40040c12612114155240c01440c040a078450f28015049401c0041c4412803641c071251408600e40c0080d1f8120000060035241140c200c012804414444c1007262000d4898540840075140c0038407000b4030300700701d003501031010340313401668031a000300c0c1854190076103401030380002d103446400c1e407285030644c1020809208140302444015400024903040060340c0d001c10308000d01d68422403095080303c540101c0850041102801101d00910400005000d03a003401941511450000e40300007000c60310b08441c01034685060b0141c00200c0360060302140d03080c82c4c0c03501c0642e40c91800c0d0031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 309207661 1250 309206411 309206413
    0x90906060f09040c0809010b04110306010c0f08040806011a070f0807030225080705010302120a0903170a1409011416030207210e0307080a082116030b040c1b05 70
    0x2007030b0a0b5a460350301c035050246a45560340003540c1051811242100e2000092502031030130080b0204a41031000b00303c1c0d401c0802031905024486050500c480c0f8100101001000000000340000340d0700c2c8000b80fa03605960044602952224584c03006812a02c18160002c112031104d0080c91301041007400a03120b001d009005541a6015084000110040c1400c82a500824010381417012078020011040039100a08003185052513003a41401100e4004208174a501c1c1c0f41e0240400f01449031011001740b0b129003c1100040c2440d10344180603000d2100281d5543d151000002c3c1d001c0014003030071802c0320000d40600d5598861038000131380103401c00050010f041d000c0140100048074001d0301090391408042801c105840120003d010610121015100303a1204809000400e4085050030703420ba07029a095655002422a00d5035040c840001811080c019030104004c4526000030070400c1111a6020000301031103004003c211101c0c07210200c00582500312440324011495054101140900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 309208911 1250 309207661 309207667
    0x5060d02090607060617070e01090c0309150501081b0d060e0f0a05031905030408030c09041b0e0a06051809040c051c1a010518040309050a121502090906060f 69
    0x700102e00160b111007411202240c2d00c000c200700d40d0030600010403890384480094070f00a8540400c04680c0c59060203010181650f590620041c203019501040115610280511900140c41043c00c01448240304440c420300890b0300c1c012004030024101c5020110003040103c1445864589000510540d44811500c3c41100518410920100000c1050342c0c401d5005668a0003503c88111440c402c1074011804d0041c24070502c00050300d400c06480d806030982a2080d2102e0314100001c0c09040c052039200341e00f0310310f8443c468040e6440140403280300c01c10745007000020796900046589204030b40d80b25008010341d12448101d0b04d000c0e154a50020b00440307402030919150300015400748035007100f03580e501182c0c8903070008014078044d40e0f9040c01d0580074903641c9036242c540880d07815011074001085c3c4100d00d4000070704141c007802015025180150024042d140c86244d10700b44241c4401c3c043da4821110301c5041071405181c000c03503600010281110515464500c00c2c4440f40d0040700000740030708824 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 309210161 1250 309208911 309208927
    0x1e03070306051c03021513081c0f06080c0d0203031e040e010b030907060f090501050f120906190204030f24180210020f1b030a0b0c1207020708060105060d02 69
    0x2050344941d41c14007003500848050f15207806032038206c84500c5070020319010810050302a004400480107150086243c5d0350b10300da0000700107400c4406215040743e013850041c00440c0a01580c2c0035005644000080f01c003143c3e008000c03c440003415050080d415401005508030710722440729014008402c2d0a039031802d0580300d4411851454003600140000eaa0101c104030810b1001c014030030003403109080080780c0001d0b1000040550880703002c1c00d414000d001031804582e2070403604407940c40c0b5000d1840103140c00c1054a894031110203075000308a42c10043c040300b00009140c407c603411203a005d902c884074000d4980d1490b500b4004507040c0b49503070b04250610303206c41c8180c1c01854030b031f280080c00742183c03100d49104106d0958810f48400045620280d401504c8017030024001804540c40024803502ea444580040d142c00d444000040444409c00c060003003441e6060054164100c01c2144605a40d490751000c903522011440364103c41d5010000411090070100c00604002c40c07081c001500d003c0c62 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 309211411 1250 309210161 309210169
    0x4090f1707060504050a0624060f09050414070806010302090303090906061b0d124a0102040f090507050d0510090525020105060a14120105070c0b0603031e0307030605 73
    0x20413103040d0740396007142c40100d0800005101d00318410828851003942e07603c0641030045024624010442400802000c980095000b1a0020001c060003002841569186411415615004c0c0d4081020440e00c80200741e9641c06070003039650040c000340041d030a050b8508200950950040d0050740c00640400021002ca8088154508102c244c1002881c442540c0305c40102040d0a048413004114507101c0070b401402c0304640447e40e221203016814078524144103890110400080b43d12080ca0044450030460403819005401202c9216500c01e15095850062a003036800c211015000100c04112403000e20342d82c0e5200320b401130003024028086030f4540d802941141c0c400e079202c10340703201c03113000c00b001d480c4142150108013402480280850305142001c102003a5450180001e182540002c1c1001131b19019040a80e68041100a014604002c0c0d0017034054080c049040c0d0f045401580060454140001201e03641007285034008842c46503400100700940020b0825001c0580320680016207547d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 309212661 1250 309211411 309211421
    0xe0108060f180103210e01080603150114010305150303040b0f0408030403030302090906010c030f0c020d060c0306150318030c0212010504080d0f050103021c1509030e0a0504090f170706 81
    0x1184a02c020020f50540c04c0c14044201c810700c0c40c00000740307550901140b241c4e000f42c0303990280da02820104c59640360040024100082c011b900240c500401c8000039141e0b64290001d2a0940f0a0301c0c10400c5440343c41c441c003c0d0300c0c1d503031886c15050350040104008290b100c07401880d01070f807203140c045d080c00c0c3c071403004600b90350003944258002500403400309000d144c007030400c42d004542400d0012009000d940c0203001e200c5071403200d8042c0032481045000307540f00d01151074503540c1c0c461402c100349880000040e0082819004000d109500e040c00415030900074856030002c3d0001610103480026103507000c860006502d0000c030780051010240c00f019850900030386001c0d074854400e040d160341c4a416404101c03007110010b9140b1604100040015865542c1074000ea20420001100d02c1461402d00722940785030034441c0e82d449813425551205041d4031641e86d4a402000700c07510700701141c1d108104400d81d44526005415002d040104c04005000361003e2540ca00b089405a81032005a8480343d084503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 309213911 1250 309212661 309212689
    0xc0a050715031a090403080601050f03012301050c0c0621040605011a070206041a090a0f060215060f0d291b1c0903200f0c01030203070e0108060f 64
    0x4403545900700c5402c2d00b42c000c2495100d40103008034001104a8002030654201a0002d0103200d0305801069203644624102c55900040c402d80e1590b03560340d00141005014440c40d48400c901c0c031401070741c40721341c4a00b04540540d103105004041c00e21401003004a2680400384824000302030791000c240103021170452a21407409494002281d6141584030391428920004182c030a000c1001842c005035200c03000c1d1026038a4503e2860308510400240192070302c60070003d96442107000310005802030401e039010303058030340c1542500c83c036240907000140203c0e81942c440b98020b001c001d4280c0d0500b0b0178a4220740307144c09055130048148160400c0100c40303a5080141c003a4103078442c104125001010551164250030030f1016150078580c00304e07021040c142c4000000199241d070b203140f003814480c000c00003015400c22050104141d0080c4400d544102410700c0c816140120079402c0c02d03541c000e200f0f0342d205040c0c0c1e869a0381d40e0208070f030045820301c500800865003e4031540110005840340030f034070b801d84 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 309215161 1250 309213911 309213929
    0x220e120a1b06051603051810090c03050601032006121f090203360a0308042f041401030b16140a32042c04050102040504060f1a0c0a0507 60
    0x1d024850001001c0c2c1b10001d1400d800b0b07a01d1a08021708a0500080a21070b9072131200300001d00601c50318041c0c81d075901940c009001803041d0000801132001c80100041426102400540040491814031886010340386400c540c1c01540d9002400701c100310b10181c8420301403e1180c6e030310305455507110760407a0030030703940310030b88034000600e50000440e03c1c07604030850103030b600f02000e155030550081c598860303605400070304000030100800e04000419103000310b615000c000201c884030101c5620212801c40f004151b1246041102c01001e20800703980e10ba060f690844805601d0742d4440c00c4284440c0c90b00090001042150a142c500790f082c081c01401030031400365034008064800c60810a40c5014031840360000c0e0980b030000120652105c0100c9040340d44801c200e060550481c41000f040300f07680d40c0c5841e2030a1001b0200030070048194018001d0b41c0d400c8a00300240c540b518605d00410341c950040b081c001d40ca141085401c24a1400230340350381403503c0202d03180078480f42c2ea0b082c141030441d4400000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 309216411 1250 309215161 309215191
    0x31b060105010f02010608060112030216081b041803080603250e0106051204170409020703030501051311030604150f08100f05060102030901030c030b220e120a1b0605 73
    0x1c0c0750307440001c403002c01c2d009100a112082c10150b0083c1c032110306108400c0e083c130100e400102014001d010031307070f030313404100395140c029650ba55641c94840b01c0965100c441a175080445a00a00e049c0c850660204210102c0c030400c0c02c1141e50542d5040009004290306105c0c1c0503220045007000c81c440149175610600408582e4078002c2c549100e5407061304038000780300c01488200c9502c4c5a0000140d842500610442c010a507908640c403002d00c00c60700400030702030000641d942455010b070400c0d0704881b01614281c2840c2c1135480740d1070456240341043d100d1071804001013001c601e8140c205d5010454101010914169548901038541d0a940d20002107500110303d4030407854802d100b004d40400c80311406010130316000300002c2d01e0b0320500098505040d503d440101c0d242e03220740d2049800010241031047c1c4211580b81e15000440702040b0545a2820003c2c9100c886d000850034802c90918200803078108804d00340142c54900103450241211a41c08001e10040396241c001c1c0c03801103e02c000300c03c2e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 309217661 1250 309216411 309216419
    0xb04090c030b07111f0207060204060c0510050709090b040204081e0d0206130204150807060c0c050a050a0509070302091305040210170a180503070506070219110402090102031b0601 79
    0x4002407000f4002c0c0c1c00c0c01818101d40c03441c588040360b0003010010b1312907904154008400c04000038010000f01800141c8023003004100d540e0004014110305025500b117070f200007102101c0500ba40c2041311002d000401e18041045400300e660029401c454001b0400b50505854140c0030345080f80540c00070010946003101d2844101c0240003c000c40000c1e0b1001d40102e28007501c0e024845540c00344002c0c0aa03a844048031100c1200300e02e1070001c1e00360718055075403450350303a10000d0000504000546108440303c90020b802e251907411081100c17006060081a6031420b001c00c1080317480100800203040d000c00601010356209a907014031f5100c3c0301c10005080c02c10b40140040d180c01100110b050254800101c004210003500c01076006842c2c810103d40444405002410829201c8000300f03240b201180d40020081c02141c054440c1a03ea1f007250f0a402400d12070521815501d44003504041e000c854400603030819800800d0403003010300490b441c002c80b031895543c170301c01c004030031040c2a0402e00c0180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 309218911 1250 309217661 309217673
    0x100f2111120f1006050703020a02030a23010b0a0504180c09061401020c2b050303100326090402030a061805040c0812032202060406050c190506040201120b04090c03 72
    0x150480e040381d000b1045442d0007005010110500e01442c0e040c04808280801010b20802c04660141d90107405e0316103030009441c00c40000c0e04410304c2c54203014002d610521180c101441028640304008114401403403900d01400000d006011820000034207240180c40810403400c03901008141c04d100010f52076152510700f003424043c0500d011b0440d00070404140c05640c411800410791005080580c0c10600d804000c5a0400e04d10b10008202e40000302c10800340001c0011400b04803070203403456600320328515643c0803851000e02c1e1960160801403042005034242603000d1580803501120000d56543c50307031241d401b00f601c0c85202d03d22040d265030400041158103007070342c8010605500280040c8107600c1024506001c018140500b004c4401c0510341d00104908625a44a0300941503965464495000600303a5002110540541c4138441000101100b540d8541d0034143e00680030307104644403680119802c1c20600d20240246480d00007010303d40d43c6506c00c02c0c00c11742c0700c4c030070b80110f052842c035040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 309220161 1250 309218911 309218947
    0x90415060518040614150c010603030302090405181e19050307020f0a120f2102030a08070507030f2d050403020112050405071502030d0501140f100f2111 67
    0x240b40218104002040010205c5000e207100305422105002408a955050000c07030254104003503083d070800e50004185038041e0300070320300b0703c005580a00a80c4d50b0101110340800c030602e40300c0c8003030b030003081c0025118111401c0e07041c007103140c02d0a4816503100c04403244000caa40e04401da803180c0000910208500d08030707292582a143c140c4101d04070300d180207043d00c1801240c000190082d60441000401c002d140c120700d10142101c2484a001f1444002c0000d40d00d80000c40e6036008604100c0100b68000c0c025010303182c00c258107540700340a4011140003110840750740c0c40b0b85081018204181504120300840360422403240359900c5884034590300005103102c56586000d0841881c0c0700a010100340d012070450b060f6000500080317000c040700d00c000c03403542c0304401d0300e207420900e84000851980802592004200d804a07502d0301140b00303190030400003040000384980030810b80003824030b9603400b5440c11000e00f068180b0308128a4407140d03a40d4242c0710a4140c0b001c070b8210008490050014032161 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 309221411 1250 309220161 309220207
    0x9170309190e070f09090e03190c050f01060509040f0f05060c0d060506030105030706050702060708030108010c1e12151212090f08030a03051008010e06040201020c10020604080904150605 82
    0x442ca007010130020b070107440322406001e80b01d40191150f0303803152022410030440c1c000d810021000d443e410410400200918508801100c142c09480071042000505008100659200410120091316143d88041c04048400f070300b1544001542085c0000c903800b80561440f0f100200001640c45010b4045801210661b401880c4600028001841a40c800103a500b040c0c03005802d02c180d8880d038074000144a4000d04200402009000002040e00034064010240541081d1680c080c0b6000a00c1001c0000d207260001d0000281d032140b80304500100b070f812012405404007551440140c9440114a504962400039203d2050b81e150b0035002c1071384940046c0062181901c20340000e0300307001d000742e00c80c031030300c3c0031007040513101c0b40030030b189082c1c1404400c000c04481000b00995144a48051745038070080b00e042e4098014075280b0300c81c505101c01500030a030000c2c0d018020540d1641d441260a0f0000409141c020355039500041249400ca101725011749400e45500341c980c03c4900d914841c41e5032901e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 309222661 1250 309221411 309221417
    0xb030607090806040b100b04080c040c0c02010c020d1103031204120905130c0306050d030e0a06080c1209030c070806040b0702010614061e040f06030608070609170309190e07 76
    0x24104010030003c544550016030158088002da11110100c046a000b140c0140d4159000050700003400310002610703d034150b205480c2030003881c04070345007910403606441d0003a022804800c0d40600603d080d403080d00c0000d00c00e403129145854258017282ca1038121600d00655824800309020502410b000c40a002c18207034074000080da8185004981104c500d0780f101c091050301c1e0030024602074000c2d000207014040207844111080c5850034020304d1006084c1c806402502d040d240460010311035820540700b40064601c0c00d1401100448800c08c07402c004004620b140014021030300400c100b41701040042104400415007410309003001d00c861100a0291410346e850848108038a17603c1d94400070001d801151282e80b00c08800c2d00c401820900c80f42002140c00c00001d001c1001541c2182c3c4005948080e94208821612100381d50b07501c8210340541da010a072000800c20a001c0c101d00021515001c01c02902e0400452801013a091440c01c8401840c102c894101803000d00d41036081302c1d034040d03041d09e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 309223911 1250 309222661 309222677
    0x20a14030741030714030f0109140615090103020918041e0b0a050601051204060501080111040b0d11070606030c210201170a02271906090e0a090b0a0b030607 69
    0x10030203490003408481c0d42800202c002c0002444203004002d00241c1e45082403585a8030b1400291f000000f0f8001d008903824039103881540075540b1f0700002004c2c851000a44000c0c0c0c20590350f90150b50303070b4001c0c2c0034113410550200032030852a04d400a8120300c01303038079644021203420145804140b42562080340348c141c03481c203003001e004950504001034100c484400001601e4480c400103c81030310401c004100e1802d014001c0c801001517640c40a81200c036404001c00904d00c0b00c1c50741714441c0c4181d100e03242c0d01c6802880500017091060f40b08068804081d12018030f4103200b9a91002924801c0e4015605500119401c016004400511001c41c00c01c4203902202c0000c0313640064998203220030380760141c04c1e10310002010406543e04590180451481c200d11140d5002c0c40e0300b040400800441c2d004004100c5000f100500101b0342100380d130360355100c002c2980c1c2868050450314074000c000464680c1c41c0d000c80c0012844640f00c26010355000207010420000c0c4030149843e002c005444602003220302 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 309225161 1250 309223911 309223997
    0xc0c0f10051f05060706060b1603020d3e100906060603060810050405011107050c130204080303071206030b09060f09032b0921090621020a140307 64
    0x1a010150076184111368542d12142c660910000170b11154010703041c12200000d036a6040d82146248202c480c1c4a0b500301c0d03070f0240d08104100c0d030b0b891140052400c3e100502e040c4030550040c00c05490844c00714080e27100608021034010a24103142d00340d00f4141541d40303a503c070741409414001e2101a1003642401d200e4145480000d81c0d80700c0850f4016070760503550741c000c201000020741001c004503520340070060300c0d192281003c548815003d425240b01e52404508982502098000c3d0b400b2546414081d42c00c60380c2d1114107480954210b5030340c0301c085648150210019043c42800da004031040c400401240c50002c03007031040110702501c4102e0a50041c8190b540284840c0503204075007100106000405400300241e8000d42000c002c0201158000c0d60705092000c212807400c840e88019940b8010429030b28141664030000341810341d03200102c1100c0c9008070400c01c0e0020300da40b80a070320b0f21071452206032030311a6040c2c00c00c2c0e4500000031081000764511410000400180c442548084002a0f0300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 309226411 1250 309225161 309225211
    0x90301110712020f161809020a1d0a0b030703020d11060406080601020f010e0304050d02010309080a0302070209181203191b030605011707080910020f12010603230c0c0f1005 76
    0x824810400b2500e0300c2c520641c034503580c0d47c00c5040c01a502411020390551034628500c01504a4403462a0051142d00024854001802011101100a0013501402c0d0854080c89003814062009581c40b0800400c150031075100c0c1d1008100504c682d540300c00311401c0050009050840700071080c030303045c0c1c1025000e6904d044040304803000c480c030071903d01d9000d5910b4030068001c0c0c040c2c080054805200030070a6001160180c00400e0800d100700c80000d9a076440e00d0041c500d2401ca1450004103a10402c007403a501c00591005542001240f280740c400c2e0700c4c07103501b10001d903487e00b503003510100030418012120302c1e01801a0400342809081c40182c980b2951516130300700c0c074010000000c102002d03001c1810700c0c0302884007102d080381481c400d540c0e99400b510b002405030321228985110551102c000205e080c806d10601d000c0040352942c2c0c00381c141c40e48281d00e80a241c00303813902184078010040d81000d40740400500087c01c80c071708060082c003682d00c11fa401c1103880040100741181c042d042c5485000380 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 309227661 1250 309226411 309226453
    0x3040c06030b0312160c05270403051b010c120207031b020a0f0e04020f1f0e0613060809010c051207121b08060f03010b010f05090301110712020f 64
    0x3056140018001c156000002d103032410b4811221030109000a0048482c1d2071426406951401103400b454240d99500501c030303103400d290350540481250042110020040d003000320390028046d280c1182003403401d40c42c1c81c2050540c4060120a6903540e059100ea440d081042682004d42aa0003141031001d01c0d1000f030600c4000101071706801e0102d1241004540c1c48005a1000e00600052010083d407500c41058030b16106603800d9210300b545840c010240e141c0070846044c07020084c2840810318a540030700766501440401c0c0c15500c190184070b84450200100d41c1c150050600c1e030b030340c00042d06007108800e0855030f190605600b04441000b5003844402c201034842c2d008103003480c1044100c58441481001007044a00468002c046241181102c944c050040d6000d010212171044000c40c5c60402c04d401c07202050f1b041d03800705412241103142e031409000a02010702000e0700100707000c06240d07a00c04080c0d01800c0202d41c1d4072214144000c0e600d03410403071245204d622100500340301069401c2690420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 309228911 1250 309227661 309227669
    0x30c0c0e04300c0f061e060b1e09040b060f120f010518040309240e0a05311112090609060406020304210e040e0a08070f0201210213050603040c 63
    0x100303043d060821804400c01c0c02c00302c1d0411010811800414246c001400506000051482c1404004201140100c0032108038503d0083c18800c0446c012800c0e405507040300a61aa10603901c2d003e106c19500c402c402482d41c0c100c000c005c02e81d2640320180400010701d000e00024001e074248001801591518000804202484904d0000700d550364a001c86002e80c80d60403a10b0480540c0080c291008194400040c20940303039260b43c84801502c07010300400d00d0642c40307215404043c11050351705117000701d0269150000e520004101d1400010702c0d601c1a180c0740b2111000030440018004881c0b1541c5208036001407121000e040503040101a169640748040c0c03000d0000c9038004081340400c01c3d00c00750208460120004040d0702c60070000041c1100034103042040c041e5003070985400f101900443d518003560340c01a655810301d0090344ad07000100300c0220341203040c0481d140d19110364084010b130000394a00d603540050781c0c80c4006040e03c000c0c0c001030b0b40301c180039010501c140300c006a50b00d5410000e035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 309230161 1250 309228911 309228917
    0x20d0f020c0606041119031d0615060315040203191b020c060d020706092102030a05040308090f090a0510050d05101a060c0601080f0304051c030c0c0e0430 68
    0x95580300c2010b11034440d1480140b03c3c80b018440c00c0c40798540503002049148c1c0340680382d141035060300f075005880380c404880086035250700401101c4c03c1d240643c080c540180020a040441102c0346000c54102c2e4400c1e282c90f8420004c0f1030200340d0403241d03401183c200c105010304d44006107140310700295448208a9140303102d15008603008210b441168140c59001e40c02c0b20003070040651a0600d48030306803880072507204502d07451140104150000046a5680010b03a84e841c0c5814655150000d03aa040a03281035400f0f141440142c42a0f564003240c2c0f07003d2044003000140c070303040100410110150070381c440d6000b03078a150342541c00b088021540d985918040c0a003c209a11403558018240074910000c40c2e0000c0049461000c2d520700040a41c141c0f1006421943c00c20001a609039590142d03101d90761703100e5070101411506101101c0c3c1d02c2061440f0341400d0000c0345841e80c1d840202d040355040b020302d4030b9100701044103111400f80d002c910003002c400d100310448050030a10400d400d44240140038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 309231411 1250 309230161 309230171
    0xc0304030311070305071211120c0312010b03181f0b0f040618060504050c0307120e030414100804030e04090503070f03020d020f07050a0e060301180501020d0f020c060604 75
    0x141030080d000b02d40d090707006004082e960f90b02ca25019180b600460025580d0000c5a8090b484690051002442401100006111241007400300141030741c03000b0070b03808a5000602c0801d41551014034050701811f240340007680c580c9440090384104103440703445241540c0c4401c081800001e0b40c0001200c10100e18036011a0b8002d484010580f2120b0b02001c45410614002000650040710b5401600d201d101d16011b1120390341d03070001c20059600c00e4840c43d0380791200300007040d10a400342940c146400c0004401083c1716110024080c02c542241d071000100b081503048142c000e29060003d4a000d20103410828424142900d0080200781d420496500859880300c10700e041c00800c01c159440305178890b003540c0802c80c0c4c610b0000c2d255034210007910094807441d242e0b140d201d400070a240c2c00391900580402d581c649001c0b0008000d12000e030032181c255596041c00c144a01d40c011241c00120700603000981d5541f8050fa00b40100c984800c103002c0e14900c140030040b240c00b0003142e07007038004d6070071500450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 309232661 1250 309231411 309231413
    0x21206062806120b03060f1f14010e01091a0a0906031503080c0c03030f04170303011202040f0b180708130f0b07090b030109140c0a050d09051c090e0601050a02060c0304 74
    0x6100903c4c00e80c5d0715100340f02c1001000101d5034540c500c0f4000c101c8442c1906c1e21810f0b000c0124040d240200d44060340f4004901c5899449481700790784942051601c040d5007541c4004140b621460711b98404512a000285c00c3c1a00d50025001e000900c1a894100f050500f40003034008075429a0100401c1c0600019000040b80010011010708900040c2920360f6208480380709007141e0300504c1024204031003604051000c885c0441074074101ca0001c095445100132683c03c00009000c4504200743e507550740e07040e0507119140c07001440103002d9241000b03251800c04010103072014400a100d10040c170300034410035000800c0711504440c510b070701c0790105503e0385034044140c8420100f50000c286042011000003001c4005810481d1075020003601d10160340c4418045c651144500d090f078070f000c244100a05c03071140c0819071050302158021004d840260f00d0916900200740a00c1d1583c000280072141b0502c48190054400c5401c54004d00700549800000031000c0d458820080039036002040100c0014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 309233911 1250 309232661 309232697
    0x90a061107200406170604120306030b0a020306030a0f060c0206090601060f0507050c031f0c050403021815030f011415010906051b031903051308040902090409021206062806 76
    0x1501502e1038607070151704615032030001952020708039819100114140c4618651901138880c0c14103503500130380e900c12155522000318002e580091700d019014400c0d00d1180c80460f81c24034801c040a4850b07034010548880c40e440091034032001403d02c85494005200410215410080c00d4003800d1043c1030550b02c032038980c20403604049400100d1900340c051044a8400340341800ca190040d411082e208100246026100b21a903004500000390002e06c2034074070440304000d10204503800840351000d100400c0c1c0c0c44000c00c1c100035036290142c0711a0b44a1001c5441800088035485d88480603484506403041f41200003045201c06114100078803100280e80740e00142005100c0070b00e02c0c812800c40b0781d02d004c15504003040c1103110f90706100007450300d40840c1d08507106607070801750190400c1c00e46040c0740c00c05d41d0b040003e501c208a001e9002e0399403501000161603845801c1d00781d205050240009140c601d061040c2441031070300f242248000405840242c5210002c6442590117a10305028640d000456007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 309235161 1250 309233911 309233921
    0x6120c020a0b01030c0303020d14030a0b0d0c170106060815010809150c040e0105010f12180f06090203010b090709150e03030705160602033609090a0611072004 70
    0x1508050b58040044240700340d12a03c681124420707800c079007080300c20003c00c0f1201030f151040c40300038550410224580d02c00580240000020060540d48881d44039626040c0400742c503800002814403811040155920a1040100030031460400b90340c2450162010a14188066816418041d4a078003055200728100003085009099420a044038100804514000c0d0404d2080000750b0b0314100010501c0e51050b242104c0041150702d40f0800600c030800070a01500c00700d031144d104004501c6820012074501c09048000501400c00011020601d006040c02e403041d400d52680210401d406000075154440c2402c42102e40045180002c015901e104132440300c440c0a10a5242c8808101ca0381405004119030700c41200300d1041c1078159544040607a142d00807600d454050070070902c104810000040003811300103110805102c22b000c0d803140065503026050326402095071081d01c03004100640741c4078a0602243c03e40c141824900d80d6600c0c0440301c00c501488220003d40b40c2500621922a034000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 309236411 1250 309235161 309235163
    0xe13020f0a020616030b0102060a09050c06070804080607020a031704020d1a070807081003031103041d0403081e0a360b0c2d0c01020d021c0606120c020a 67
    0x1069a810880c20000d5403014103680740032403241c0c4e08160b804442c0c000d1082107452581a0042c020542d20151a680240028001503c8502968400c81150f0ba9420002c010051150819079221420b103503c4514000380101400c003503510001da004082278008540c1c00c42584c40100d141041d540364030220350a40321034800104190814005103400808141100b80304482d00d075500017440c1d88003081210394920070b5070a503503040054041403001ca4450402720320540c0d82403003101c0c58155150a0718100d0f010060160000d0714140d4144030402d94070681b09c3e504804138004034510350701c0940071410f070000d010306200170a0365502150350081c800490582e140e04411111072485440564804500118016003210701c0449500040c1d814400f51003920820640d8018900e2195130f44040041150550510705846050a0102c600e0000703090005011003d800180981c035442e0300d80c850014141a841440e06040c10100c3c03e0000350b5019413500b4031820146000b044c011000702c0164144181c1f204 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 309237661 1250 309236411 309236437
    0x812031b16080702040c020d05030c0d1b0207030506010911091c2001022104301a01060c0b0402040b0604030f0c17071a07060e060f06010e0a060e1302 66
    0x18821041c4102480540a05070095405011b442e0302582c0407a1180240702d0840003107101030020606000d4a8405040d0a02000000003485c2030b8003000000b0b00b08446e1103600041c1e011650030b208000c424014280180271405040c00100c00810480303070030380645030145000b0301d450a1034507500c048001c2214412500010f00d1200041020380c180d0034030800441d0a4058414081c010f90048016450f054504c4c5881d003480307051504200c3c640040861048040203891820301c81207031a03040c04070120450a1144010703036a100c020156a8102501c140d0180040c0104c0d200d800011920381c0024551003941110002110300c00500040c180f03000d19000500034580406c400800c10041240c0c11080e1118404402143d54280344010381e07d060034041d0b24118103065000158500041c006020110311a84000c40d031841a400c5039842c26a0880e01071401c002c004051001c00c2d60004800d08500d41d054030040200d500b4107001801940001d071842c0e0081100003e502c06171195541514110034100e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 309238911 1250 309237661 309237697
    0x30b070c0305190e0f01050a090909020301020f0a0201090c1205031b10020d020904110708040e04110d110a08060709120807082106030c09010905090109020a1e0812031b 74
    0x403000401107080a51610302903403845c41180c00542c000c50907035a903008203a480314116420305181001070a00303a141240c042d9020300003036154850050103000b110406900001d054406400c0c8200030003070b00c0d03010804c0758015210b0f401c0840c01c0881250708181d900d19106840018080b41d00c2c0c509121100443d02c11440426a1a0044e10540046c440200300710340620455804036285c20f400c0c412100e00502e400000c00040000c06440b50b1a02d0784940140c1466503101200b40101d040d050418404540314003034109030300c2e45840c0011282000c3d140c410001c0902c1c7c900f042c0042c101681c0c034003a28088210301110b00c4100840b1204444560f44d1151805440e41040e842007910b0301c0f20001e08040700e10040c0300156490030002505003e1400091840d0f040c2d03403030161003100400000d840800d02e9501c0300002c00268440b5401d1758014103090a1496103007c2100100381c10140e01c0d0055801c0360426003041807400070350410340c0d410081e103c0800190351403500e60200c4c50b20808115002c280c80e20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 309240161 1250 309238911 309238957
    0x2070305030d0f0b09010807031502070b15120c062b0615090b09060702010311090a080705041802031b131b140702090f090f03030c0a0207050a030b070c0305 69
    0x507070800c3d03070052074015091095803203690400c1007500e02401241125440f01c4420404102c0501c0389610300c000c5101c00600e013a80c2a00ca801c032800d02123440c4544034401691244417801c0c0360ba0312203004840d80001d04440703580701f800336503948501000280c604580c0070202d40c0d0046141c3c205001c203401d08004010b12691880c200400014140310100480c05940700003c05a4840f801c40f184500f0041c030b002e07e08400c6038010340041885c1119102030640030300030f1501c207844040b0104080c2c0744040061170020715002c1000300341c410a00b20005891042c00c003400040e10002424120400c0c5007115410040306280410000c00a50141220300c80c20b00386184000c00c210203403d1101c80107603031078a5040b814540b0f0306645100e6618000d400c82070103000161002c10f88141503401030341c05401c2c1c8040c4c001c450f00c020701d150004d803089081b117a40003405280d1680c04104010007803909450903109079185481305510340398028950030510201140140c03c041c0310700104c9201100381c8100303031a102c0c09 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 309241411 1250 309240161 309240187
    0x307030e0f1215041704081c050405040c03360206070f021906081015200307110a09060612050a2d051807031506080a03120501060e090c0a0207030503 66
    0x1041d44c0c10340c1c0d11000a0030700d040341d02c1c083c0125001d6403150f00c02400c0a0885078400320b25a10b170b80100508015050101081e10b40c1c8a015001000700c4903500410703613410f50090b400c4008113005140c1d0305040c0007070400404810101c80100d0b0942c04849603130326500d05060182144481100c000e42c00300f0303090000c41015000007801d80a480c2595207200d100d550f20490f00b0203c02884c0115200002c001e004694558821344910700070500106502c00f00c101d2804074203140d9080f0060403203194402500900b0507003000d11092008050558052020303070f14012000d401d042207410030640d007030384403c001400b82d00d00750041103d0030f5034072100003da107420705000310f032250310b070980c41036030714280303008244900d01024003002c900d0444801b421a03185580d603020341c03018458001081e52070703d0b00c1000584035400c2c010200034901980700c101d502080c01c0c0d40401100da05801c403000780b160391074190015440d441811503101c240403844a0385d40084d007009a15080e41c0d60b0004110b03100019594812500c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 309242661 1250 309241411 309241453
    0x60a1e0302120f1b0a170a02130b01021b010804031d0a0311040509060403020c1215150a0b0c0d030207080d0606050a02070f050d020121020d0204170307030e0f12 71
    0x1c9200300340e400103404602c1c01c80c0c4140a1400300d84d844285c004017440000044002e0400b480c0c040030407140d4481d010707800329070000c0814940c81c40c281d9540350301000e00d5070103101c81c075000606800000f4004150a002800d8240d000c0e201030100203407845045499400041c81080c0a8001803041c0c0620ba41c03031412290400114018074001d904020110b0414400019032501499164010300b1200602009220001c0e51103100d070120f512505e080b0382200b2145c0d0780c4003405420301f04460020003202c1c00601243e000c2680c000c983c8104204031411941c1d00110b080400c40d07a40b4030b0007585c0d408150402d04091702400b80e92044a40c070380600016060b030860002d10350101c1396000c1c0d50740641e403031900032010030b41c80c071030035400030b91040b074030001136205e86034000c241d43c0c00c40c0440b17000c1440c0e001c450b41223810000c0e22022240d40000c05110341e051810380e420207890715400840c504041641c005141c100c5400142e8019524215082c42030303610340301400c1c0407030500d0003250100520000d491003915 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 309243911 1250 309242661 309242683
    0xf0301051003020910230313111912080d0e0601090f020f030c130e070203070501050f09100e03041d0604061202060a0c0f0c06080709060305060a1e030212 68
    0x28800420750215400780c0280d600d0458000c09034800410001002d507000d51680342c44c101b465a000002200d00c4140001542c01000420400c0340070b0401450102c141d403c0c00b5a200d4482e603100070510503202c9682002d00c3c1034564586181d040c80c0c1c19442e209005000d40c001078001b150521604c201c1a12001640d036040310450b40040c440300307269180300d400f00d120701804031804000c10000640d00c03410040c010501000d1230103240c04025911034a051124202b0ba86100068200043c0d03603062007002d001c0e580d0022440c020300720180c184640c03040e5540403400001c4da460b6072032b00040c044003181030056400030054200c51071000144a140072015a00c100c031414490b40ca01a030202d0100558034084a4547c2d000e0051342c90500c00c07031410b40321411046412210000c0c04806540082c014002810081c1200e0b140e00b021400c0981d8082d1201405070095820507142c0b004000c01a034802c140d4000300c448510300302c40766001d0044410703024409500081c2d006801510303032000c07040f400644480c02d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 309245161 1250 309243911 309243919
    0x4151e060315050a180b0c0403050a0c060215070903021011010f1d010b0105040b070f02041d060a0b0a09021c0504110909010507050f0901111506100c02030a030302030c0403080f030105 81
    0x40e41d00c004892044a481d075011884900f040843e68000501826a07150000c00c01c00000e81009d80d26034990b8500060014110766500200004000c0d0980422514410342c1c262181561185403103000105020180c0c403010307104505152400e00c0b06070003044040b95200c40f03000240008601042403102510100d03c80f00c041d019004041d500008041c803403c3c40410059485520307007442c000703407207503030b074008805c00c1d030302c0814440e840e40040c3c0c0c442c410040e0b0802003500c080d9215664030501814104014940c0303440310704040b035800155943c0245d410582e0300740fa03c0180c94560b95512401490f103483d180700c4100d4a040e09100610080003030240544504580c01c03042991522981400d07503c8c152800000b142d000c3c400c0322500c1d035207880034014226043c501464502060082079150000e600d11000b05440c8542c2403012506103107001c030b8080403032402c207040940e66650229aa40801100140400d907010010a031f4291007101140d00a64001595584402c02c244031480300d50701c2072064500c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 309246411 1250 309245161 309245171
    0x1c020708060103050d2102070b040c08150f070302040509190509070f030312020919030b010503010b01021203060409020a0905070807030e0d0c020a0b0c0c1804151e060315 75
    0x1a5200000d0703003a05a80c1c0c03100c042c0c03000401c0c4080c01c1c0c42404035050690901d03504034144020b07951651001e054030f20b01030000e00702070382424184104910240c2e0084142500701c1d405100c101884040000e8200107030154074840c603610120100c00034003407a000350703a1201c01417051116040720041c4030000c00d829627008211f103454403c202541d402e0750380300360003900c0c02d0148100082b0740500c41c2e948020440010140c2b5000e00880042c3c00220b0403d4490361546080f5020700030300c5201da206601500065000b003000004400c0040e540c4c0c1019000124440c00000000d60b0b1600c59410440700e07141d0280c111203104e9100c1d030381d0303601a10040b05c0c1e460015110200060000748a0300071701c0600c011140c0944041d007104102180d000d03588440607604404c4040700080d403444030b40001d20500903100007070011058040100b1841001c1c2e45c00036076850682030709200100c4d060840341034086084600009421500522240ea0450000340842c0414070300701000090010002005245040444003082 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 309247661 1250 309246411 309246419
    0x30108010510030b150103230702010c18051c050102071415060607080304060b030313050109080114190e1203160f140a02030706180308070306030206070f020d02031c0207 75
    0x46102510004d01a04405000f0611690068003d45040c40c07040c54040b980c240102c5080000180c0b2224000340801000c040200050382845030500100d01860b01c0f042401c0603008001c0001558000d040c46810030359941b801c80c401010000c0b07061580403009648a111506001e110001500c030840b03501c4c05130b01899500b0740410391410344190001403115050480070b0707c41d0f5215400050081b14040d594080010b0700b6581000903200340c0c20900008442c817410f0000040029050b9444088240e041081c00100800c4000c1d65035404025132240d04014010390203c0350141c4584242449a4042c902a0024054250f8010740c49000424010a041d0040f05030840e800400078410b600002c141c040c0e03149922100d040108000c469600c1242d0808009440b800b00300c0b4040a0200641c803880009a0300300b6811502c815440f000f00d0404000162668000c43d06610039113000806a51420001e9021980d4000c0348126580d006421207041400002e0003111000c40041c0c518091300c40c0c258006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 309248911 1250 309247661 309247681
    0x606080c03040b01030f060b03150601030e0c09070e0d0f08070b16020c01200f06150307080703060209041d07080c06091f020a0f030504060e1c03081801020a050301080105 75
    0xb401568001143d42003a860b58594060b500c2146104691880e203880130800300e42d80400c65120304100b84000084141402e00000d002c50718400c158800c44d401c4450f180000ea92034520003503011045041c00409040c03954001102c6038403201c001414078894041400501c0101e00141120b284200307403c45880d11b4070035071488007155442c0c1c0000103a00c030302000d02071548103485404000400341d040c210b40340c4100d00b2090a05941c400415a40d40c0300404012030104550104800340c642a4080c1c414241040c207925100c03482400090484c0c0e400060001346a00c455111001c1c004c100c4000508500d141100c140d02e441c40c501c150347e50351094642040c400e2a121045034000000117000b510288440c01c640403100050421aa0540c0030380342003100414034460302c0c50351440c402d41d40c403591039041c4032000e0144070f4540c902034011460644000107000b1840880c00c526901404d201485960700b008020415100085100c40c550000c1135413401c150308003024605841d030041c0203001303940c0d81c614aa = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 309250161 1250 309248911 309248917
    0x212030a1a0d02060703230a05030a0b04051603150b1c0e060c0d090618080a08090327040b03031803060a0905120307020c060712080a090302070b0a020304120302010606080c 76
    0x2a5000204100d08000203008407070003507e03000403c003511401c0203072494820403078010302025804600000100030903503039240b02d48041c80c6800c641c10000d904122101d410b9406001d4407100906990b1440b065140501d003440000610f1090400c40d0385000c0c404c078090758401d1041119440038240b0340395000b031110204c0c2d541d03c40c040c030b50900c50620201756480c1d0050040c800c010b0310b4142e924040e16140b80d04030061a04818001d000d8541e607481d11840003010902e000b02003903000c1d00709104801e0300d10701c4002110449180c00001200c3c0030b449400280041026440b5107a2620000480d40d0703203030003001ca020131405000c4054519aa441c0c0c0b0700401515528200200b441d081540241403d4171181c02071a0007151320302c112101d082c059408288136601c604002c2d601d840041441d0802c0e80d50000045500000b82d55061040c000c080c1c0d406507a400060042c66901c06002ca0660003941c82013054a000f00188402881c000d03c1c10304000e4000d004c18010b400004620b0800244904002d10031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 309251411 1250 309250161 309250163
    0x5010b0721080c0a090801020301140a12020f010c031b060e07060c020307061115090109110627011202030a020405101e0507080903011a0f0d0506060d02010212030a1a0d 74
    0x40c000c565a181e070b041040e41c0d8010090403041c8090304d05d0103e14610300344003840c042c0c01a400c4110102c00b401c0b00b0000000b24070f07440b4a40d000e651030300e984016141c0459411000f1800c0c00c0c40c81f40740030a4030b003d8031801ea0700e54800d503201503103c032100203004094010300340000f03011041d10080364680f00200d0315649207010194242c2d001603001c0080510401c01c0c001c42c081c028040d140402c2071f100540c45a84000c0c0c40b41c1d02a41e4403184d401090150044956420f003004584c02483e0680d003644511580f0140400d40e00c0c014288140316107a80d00130050b0750303003000c1025000c55803442c0005600000f5082406070600901808140200c0b490042d0302c00c054056042c5501e03156400c4485003126164010003041b10712101c01d0001d01d2854800740a200f04e00709800016000ba880301c4001d1041b03003105c4247d007500c166440c50200012460200c3c0c442d400c01d5090713401000420780f84c00180c0c9004099150403802013000010442400d1440e840500840154004617983e000c0d8203003004080343e42104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 309252661 1250 309251411 309251417
    0x15090b010203091905100c02031501031a06011e05070b0906010303080a05250206061302031504020c0f0a031e080c0301090207020307210b060d050c2205010b0721 71
    0x140d00101c0c07400d02415942d00e05181301000d1541d403103401060781c03200c0c0c4540e80c401207080940319500f1440c050050b20191039541000042662540c0c89002c1c0c0110070180031a030080000b008591117901c560041c00402d150200100501070690380000c1007644000c0054805140903070108060880103d000341c1204c0d010f0303603409407580300c0c001c0c042d00408024007043c81d00318091003c40c0b44183c1400c900142c4c01d00307640107015585800c07070a0200740142000032010681c030400030003044001c5507120742e200c51800e039401601c66040d013200c21b01e06611806014a5403240c0280a82010b41c081f1600405007400c02060b03152515400d00be95a040043d1515029038109100500c8482a554090f011444c00103007200c83c3e40da9207141d44c00802622003521a45803078080031035070501c20000715158100380280c40c0603400b00389507140c15072180c0c640740b821407145081c48100c49050742c87c095001e4030b00110715010411960754055480c03199008200c103c7d689a40d0a40842c07050b050f181c52114003842c80d403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 309253911 1250 309252661 309252667
    0xb040209090106030b0f04030e01080702030a0309020612130302070b030907060f12050901020310121a0606040f080d030c0e01021f02120108060912031608060607050a0615090b010203 80
    0x9420000c516000600014082d0341e61031000022540741d00c04540105103944440149041c182002000385540ea00614180f01007030080c01001ca6000046440c0000c0e1440c0014060a440c80010014402c01450943ca20320100074030003c1c0046022442e00144280c0071201030075600e02c821130450204551018203501304281c204803044c00b40c040c485001032039246c25021f14031800003d4044520545038805960350100c2040380482c2c5003030000c4054007007420101c000843c95a54540691030343c3e034600b109810503038045522502c4120960f000381450f0326600e411203032141800396644904520010000b0b00f0300400140c21030061641d0300400c80306a01910004d44407004100300c00d10400c6920b2031155080081a60a46501c0780c01c6028041d42406008541042c50b11107141441e2003c2c5d61149000810a01c00c0a1440000d040214400e0781420705159a81c4400506a400380e001d010348180103402d110030410440341c1c0441c1d00829404400d001c042d4a9021117030032904c0380d0f06080d000d80c2c410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 309255161 1250 309253911 309253913
    0x602090a08071a0307110f060709051909180f0503030f010f21080c010f06260d0e0d0b090a0b0c041809020d0c030f1709100f0c0b240405040b04 63
    0x1071001185c0c0141e00c0c3c101040e012980c1c001040c0703441e800d044030982ca0b400c51400d0050503a40031031003e000740b6084401240c20305111030550805982c0d4030640c880240d990784059801d040030284400c240750400010000040c0c03034206541c03039a00446011010844c070b0f10010030f0700000d21401c6002c2c0e80c0d10b01440b0f40c04412803030071078010b5480d0803020350b030740c0c0428000c908002009001d16203a1080c0200301180c0145808050340031216461440d00d01c0204050b080105003030b0000300c600c0000440d1509508141940340030034404110b51001602c03a802031020441c10740b8001813402c0315540301c5c4080f4005a61012001241d5001c1c034001c2c12000d0250520b0648510010f400000010f40003c2c080c85000c9280ea071a500454501d500c121350642501032608103002071094020001c100411510345068040b03400a441150a1100300081c4001c0d08211003d8034030034422811a9540202a0b90503428070031a2a40d05210340170403986101c27110701e00c49065007414000e003401954003081224603601e403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 309256411 1250 309255161 309255209
    0x501140a1206230112020a1e1b030504060816080105060901050906041415030402011e020f0d02100b0301150501050912060a020a030e010b151e070602090a0807 70
    0x4003240c07505685032280d40c0481c0842400042401d9010703030380603040168480d00d0003d84041a84018403101a02c1804482c051542200d10b031a000d0f5502d803084011680204001d4940114034640b160030700c01d490020008154201005006035507a5882d560081c0d962400c10034400c0149046850010700e10400410150502c1409884c0b0804141081ca051001120200b2502d0b08141c0c0a0076402e403117052a200780341000c2d4286000741103059050380c44c610741600043c000d40900c1c00c131113082507256442d02d00c0c494400c3c001c5a44100054003a07400b6100c0c84000250b0b01e400e00851101c05a03d401c000350a0341c038051184004100101500680881c0b5200040d0b8480d0080110309410002110f40f00c08102e0701880001d12444e100d500043c1c45002d4200010b003204d43e11064101d8581c9070001003001e0355a008444040348030079108541c0d41d040c4458449040306e034240000c0c1403503200413400e034080002e40e0f006010075180c15540c02d00b050b030340c544515948813814440d100402940304007240210603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 309257661 1250 309256411 309256427
    0xb0f0112050a062309010509090a11040f09061d0d020c04020d09080a0c060b060705150402010504080115150905060301060c0f02090a0b040609020306130207050c09040b010905010501140a 82
    0x21400021000e503114401e1140e0300c0c1d6203030600c0d00152222590000d85c50181d500d6809050107891034100c13458003600741a5985201e00003d8031101d0501100742c6a80e03a00d4008084002100c50180881541464000058000703440100356503c4100c1c503c0f0210840044d00074501020340d4000c0840b011044280b20003584204191011036448120f90404120584010700c031641c91542e40100c0202c803810300c1400c860340c1000152042c00c0801c0940f021400002c0c95109020300044c4000381a04c0d0f520041c0d85a108076032105c0029401e06e41c0358401c0c1030003140040100c0750305000c80505100c0b407130170071580e40c1b1090140c50fa11100910043c4442d40c4560007082465100d600c0c00200450a9000200784040440780a6401601c1c0c2c20342a401d400c103800349000401448405504505003800041c8030502c4d280c448612055020602405011007081034034440ba0001d4001041400c1c24101041c0c150401d001d0f400c3c105007030a00001c0c3e1540704a1458820002c80c01849091040354802141e05c04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 309258911 1250 309257661 309257671
    0xd0f0c080403170c060601020a0209010b1303051b120f060c0d020d0f0b041401060e0f1305010e061c11090a0b031213050612061c0b0705040302040b0f011205 69
    0x34009001c048000381c0500003002154610940140c0c4420b0080020352404100414207411500700f40b0f041001619203810b040d06642d03641442e2074640c011040f407010040010340c4003800314428034094000d0180352419680d0180c405841210303c0e0010164100e03520203816001c4102580941d0010f01c0c602d40e6040601500030b054003000d45407080e24007901c02075619100d038081d6000d6a40000201500c0c20b40704416240c1c0710051000f119605d07000014004010b07000d0118082c040440c5080400d54031820341210310080f01070304104658454440c5082280b040b40d00074028503011107a4603413848040602c0c0f45060f40071015000d06070402041c413001d850081c01018840c1c1d01c0d14054040c60b9410310001c000d0a20018a6a46402c102c076201d441e0300c181e50b40114000c110801100052040c0080320580c030041c00c3c0c4800c02c40081c00c0c2c1a0500381095100c01078040da010300144000c6540c00070040c82202c2c0221010700c8080d0300742e0300304103889191850190114040d100000c0709112660040c03540a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 309260161 1250 309258911 309258923
    0x30304030f14240105180c030703090b0c030703151a1b0105040b0403090f061d030c03070b090a211b081212010b0412030c020f04110702030f0d0f0c 65
    0x80358541c1c4215180005030300d4582820503068828003c0034403021143c40c010481181d14000304210090300035121040a408401c5042c400800140c3c1240260040803800c1d5010350814118a000d0504000b0f0341c2003910544002828204c1c204001d4410b5400c40c002c0d80d11600e0818904400d00301a1000ea52250b0f0722000c0e4100c4c455604090001c081c0b00d940d2059000e46003100e900d00e480c0c60010000411500020210f000c0040148080c6a20412008071120005003004404c0c03803030780000740f80050243d2010740c184581080801d090007a5405040310000503680f80c4500c544030802510942580d00b0b40d00310241e58100e40802062400401840102d84008548092504c1b046e0981c02d21000051301c8216410001d00442d00d0760344401d032280102500c80b0414101030a1105241c41484440400780c00c025100140704c00355925946000740b1294010000c100b60815411540007680054505034440d00071260004040e1101207000344000301142c0c0c80b80c8038517018440940707401d030f0140002d07621 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 309261411 1250 309260161 309260183
    0x6192106060b0a0201090219060e01080c040b0a0207140a0e1909050601320303190203090a09060320011b11090a090b011403100f18120207060e030304030f 68
    0x956180b6001040700e01c078103a001040c292210700500c11400844807411b9512a000d010405c10a41e01904000c0200824030f46aa155110004000140d0240384c010303513420600003c54078029900006c03d0b1045030345051040002e07d15044c10412001d50910803d05c1d01d1680b034000900e4001070040b0900d8440c0712100014090b011a2540351500509030070400300f2203079050205111150b12140c040003601208080000c0c148813501003078880c000c42a01500c540c90b041021a121402482074854041024182c1c3e051256618060000390056110648524841500d440300d1840403840d010f10031131046c2c4486000305021804543c1c1d503a00300f0030235600041c0300d801c2a1250703a299000035004039000f42001c501c061540c18a014140010717030001c41390700403801403240c10b0348000c1400300812200b85400a0f483d0903a020403806482d091000d4010074070035070355140030440c0c038074030039014003e02e070b805c0300c0701240c030781b01c2c151740c481c4485082030381c1548240010400103000c081d110349420b20403512510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 309262661 1250 309261411 309261419
    0x5040207050f010507020309011701080309090c040e0403020a0b09030c0c0f270103021008070e010503180d0305010906050f06090d06060b0d0b01021c08150a05060706050619210606 79
    0x42110025a00e40d0016080000c40703848c1580e001008100586610342005100d52610744425500d114281c9014042c0c03243c0030000f11413614000a82e0000c1c00b02038003a0442e8602440c0094544088050441f5440e00c1c8502080345d40f8400800d40358140504402482080d01c61000c100e03615819074190b0354445104110554540c1403c1d4440202c00c40000c400041541140b0402000d442c4190b00038040103c1042000f42e81a405440080818020300f086035417600e8481d003500c400602d28122071803600c100070368003a2a6038103500080c101c1d41d080c03038104100b1340c441040002c904036401c40d05a01c81e1013808000110303d0305440e0051200d10a06001846694071108200f1980100030b24004607941e900348803441756010310102d8030724141c1103030038542c140c410701010b000250301821200d10042e01d0a00043e040d01c1d880f8100303001d01340061800382c517606113241100241400300d450602440b040812030b2580c0d000d0381c0d400d406580544e00e00030464201c64040741041183c1e40d00941d2060703100d520010b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 309263911 1250 309262661 309262663
    0x5181b0a150306080d03050603060a020708040b0403052d030403200a060f0905010206071d010e0915041107020a06051c020d0b0102161512090c06020607020d03090c05040207050f 78
    0x441180882d44000c82d070940340c4980141007480b49a000310038107007003d04211950f0b40c0440c000b035021101200040e114840c50400100c903003c0ea030031000450500090110078400c0c0018001e4a0000110f8a154607082c07201e084074012000d0706105005a01c18401072000400c8040d0f010341d074039107803101c4003401c801500015030301d102154046c8003c12865a000f14140e81e2201040020b40307c280020001400c0c5007400406503034444405d22480303110080d180c60309a02c030720f405030101d490040803101c1500f000c8a0b804414094102610310492070490381007580c0c60705500340e601d01c0d81c004202c490800e25180094804e5481a00c01084031441d44c20b17114962002ca1002d049681500800006c0044028001911302042d110b008050010b00410410145580d206810890380051424950510103c801440680541c05004200d2500c1c10b0380402d100c0c0c0e00044140c41002264200c405c803182d0100c0075400ca07a00380c10b0260141c080000c0a104509090f001007584906c00d070b003242d0301081d1501a40b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 309265161 1250 309263911 309263939
    0xf0519080714030c03070312080c030c030103021302072a06080103110105030702070b0301030b0412021902010e04110c010f0605010c030915050d020a020d09050105090a030b04111f0305181b0a 84
    0x884140309488c00300d07402680c0c0044100d90140601101618604000c034540c40719000501c0000e21410240c05a203c0d1b5044c075806549031943d00c600c3c00007000c041c07580c8118040c17452298030b0021440400002800520581600b1704807500040d0180c141e02c842001100e95502c02003e240a601c205403000801101c2c190080d4001d40c0138002c5a600b81c105494290307002189007074150215070090300a9030707030021410314603142980d090030802c09080212001c5000b40c45486e0031403440600c08207600000d6141908080340021080d0402c00000342c4820064408138105140500021002a42440504855040955010387e5401d01d0707401c00300d1011450003664042e17aa00e40058024030185c4c0030080c1c1101c800b1016180900380181032003850f0011403d91706003848041c0c20442101701040034840800707c07082c1c01c040e000e48002d080400703494290b0708425100901c18006860300e4001252210440a0741240d07030300c1c140c042c10f2100d90442c40b060041c05041c41ca503601076044d01d0005001d014010403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 309266411 1250 309265161 309265163
    0x304030c061206060c08030601030e1009030314060312030414031c150605161106070602220e0f04060e100f060e0c1926010f0519080714030c030703 65
    0x40c00d1560340c41010342005075440f6a0050040c415020b0366100040c0000084c0d07a8441000e1038001a107882d08101c1c64030f001940110501c0c5030f4034080b100f1060641c0741d000461221001a560780258441d5014960b848442c488a05000a000d01c04203001814500303c4400085011003141c1c00e0120481021600d100703000d005001c0e0a503140301c4040740a0140c000e210040500b41000c609140041c2688624040d0f03002006200788008030104000355591020b880d0340701d41044007103450341c0b1000f101c1c8621842500860781d25049154000801a1020461074814803103210071604645031556494081c00d41d40f6040d14040c000c0c9190250860850320072051403201000c000301e05a480c00c5a0f040048030051b09a2000d6807040151840207500c0f98406441d6104524061104124891106c001803c8841c2020607242d1424000031320b2040007070000e829034000700c0c1c1044245004400c6489148064402c1d050560455501000042c0305200e0701e0b242454081c042d245015555800a4108105604 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 309267661 1250 309266411 309266417
    0x100f0c02032406040603020f12071701020403030206090f07090902010302160b010f0605130314070e160905010e01020706080703140c1206010804110d03120e06060f0d020a030f050304030c06 83
    0x180b0801c0e1260203003a102c1e0051010703101000303407600795008100d00d000c401c040c0d02d014060000c15920450f41c05c00080006043c4104922000b04c943c003134040c040d500a220a0307005102c0c070404141c00b2940850069800002c800050912510300314400014201400099040c140d00744034502224190400c2c020109101340314421385503040001303110803e01c1d107420140411038284642c40140c5424840030050340d4200c61102071801580c01410f01d000c0054111005204540050141c2d00020396160041c01001c3d0700d4a801c2e00b0344403001102c03044904050b00340180d1202d803041100703e01441c4019004465840c0c00319101100c031003807400c4503506950001441c8000611144c0c000349000c842030308540e017440d02d207000d07040c503803039140360028800410340c0300b40c61126886007098000d84074804640302d082c07024002c00010396051902e80b8000ca6106000301c1c000c40c030485284c034100e130425464a500615941005003075448443e8201043c0104559038032003040f0100109114802440051074a65 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 309268911 1250 309267661 309267703
    0x9020a0f0305010b16140703081207030b010e0d0b06120a0311100209060d020a0302210403090602070617060307050d0b01060306080604020906040b010c0b010f08060114100f0c0203 79
    0x200007021140c050380544003003601480501c4050748003050203440507411a50140030220100721382400e10002d540014142c420003da903800300d0b0341c4402c03c01d10494060b03e0030400c01d0100e00040d140001403000309584210022690740000e091010703020f42014000c0d000c0a00e00512100091525800043c00c1c1d01092818502001d0414100040050390b00b03a40340c25030402d40c140010400c1401082a040c0d40c00343c0100b40c0c4480310344a035041d01c501000c5e9010708443c10000d42884c8000d004140c5090740043c901c1d03e0003107071b4a800029103000b1198907584001901c9081801d0b0440b10001a0540354140a41c0c400051180e07140c254906c1154000d0001c01095450460098200e0307110382d00059440c1c00070390400016079039000c05a5407203d42078801040080389d480049604840c0b4000080282e00d644002280804c040000f40b000e80b0509002c42e00b95980343c40f003d003103440d1081c140c075501000d403483d405041d6119484201050926080458140c013459000904100c13211a000b203d4130011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 309270161 1250 309268911 309268937
    0x309061104080a14010908071e0f14101e0b0609180f0901060302061204020402071b14030106121103030d020a0309230a0b0903040e04061407260a0609020a 68
    0x2030f030001300410b08400204a039074442d50307490348140204603000d01090020990702c0f2104100b0301503403500c2a4042e095010000c0c0514000b005000c803c516285184150883c55403c03003840c0c424161a480f484501d00f48000d555007040000d0400d001c48190007400910400400d80c80c1d00040003503000110b07048104a00e001d0758007000c8244000c0c01100a6030400c2010405070700c079803044030f400542c0703004480d00c2d680e01d41c00400c01901c03030313000c1c000c010000e24900a4000a00c6500c014180c54129049907040c115400405083c7d45090003181c4c0d0886260120200143d40700507001c2c00315001905880c14504006294803c0743c018882810100340c581d5029030401401d0038290202e0380100c065414101d00d00054103588040b148001401030b58198042a0554800c00c00d6500a14030781c072102c20245000d181460113019051342c00c0310070214000106244a004842d034040040215404c0d802c90020704001700c0017058042d080003159540c03400085161103580c00202884c0081d9210008800d1103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 309271411 1250 309270161 309270173
    0x1020114090d080c031014012708191505060d02030307051507031116050f07030f020f0f2803020405071707050c12090f040c1106010609030b070309061104080a 70
    0x4010039943c5150020170412000a00d40c0010b001078611407540820410241c20050303c4d52021402110040890025014440000c107118102a107202c1c40550300d041d050031040820300489180300415800b80c88010760b1001056900c1103074060742c000d0007580e070900c081e008241543e00040042e20141c02500d0200100c40c006224160040c0983c5002c01029403070a1290561307000f05031070003c0c045c00c09006001440020007445407440c1100c1f0564005c82c1da44d151001140c00c3d122001c03400f0701010784000350b03207140104480d90b010001600182080054082c60b01d010941c80341c2007406500110b4012026854900ca02485440d50b40c03103035000c1c171758000c403002c441c03e10042182c0301700f09080048250380800070a03981d600034020508d507510341c0701c00c4000400c00c1e0240b144650f0014a0111160090b5134091044222036400100391005070b600c4820407907100a041c000a4411040e18000c078240364400e43c024250940251800200c800301280684080d500c954059a000da01940c03010302405a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 309272661 1250 309271411 309271427
    0x50411070b040813050f0901091a03010c050408071d0403050d0f0618050a0501050307050f0103020408011a1c030206060d2f03070815040605100e04121202070201090306020901020114090d 82
    0xc100c9820b07100d06c4984002401640050045040f035540f5042282000104402e0008140ca401002400b801d000700360001c14a07045840341c6214ee00c03c02d00001075072008030001c52000e11828101e80e240759102c0d1001d65481c1e0003c03858520556441009000051540c4104400751412049034200b801040180b20117581029090040c1903240c40010091564009072403c200d03401a10140008030080340140d0007401680d1022409508144409a9001d01c0386610804164229607c50400301c1801e00d140f64070381c9040c00280940d228a01040c0245408175096100600c19101c4c8440c04046503640c20110f41c0c0c80040c110100340b010386d07089091405105203800b6144c42d000420780e0742d00070054580c4464014201909043e40c03080882d224105482e4524060042d96601c0065401e0900d06542400400f0072003000148500d411040701c1c0e41d81c2d00840d80700d039405940e0300b8251800c58031014003e6114084480c1599030340d104030421040c0703c00d1114840c1102c0006040522250403015007860 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 309273911 1250 309272661 309272669
    0x1b0c010203041a1003031110050109050718150309060207060c0201090227010b03090a0b070e1f050a1d040c17060f06030a05070215040602070c0509060109050411070b040813 76
    0x83e0b100801010b1818a807960003242c0c1c05103002c4a410540c81d2599081207600500130a85074182000800c254000d5017100b4042d58240d9541880703180d518000f40502e42c0340b4018000c0d404091510009d28a12035086812600e002c0c41c0014a009443e135130b100210345002c15070b140940d4403a1445001e61400d034040ba24525502641522421b21040c0a040c1541c014021b8500c4030b07002101155040b1010440d1000c0161320074181c0d00e0303604002c8005000400d00035801d40c45221001882070b4988880c4a074aa00515030b501e90900b0a81d089006407031001c400c0107081d01034a09480f07035600c00e60b164002c0d402c0c0460582c48402070980c030040c8946d02c8080c01002030780984208499490b15031501c1007182d81c0038000da0400541902c4902049007803000d005000082c241800041c441800415801050814801c1ca0b600851554550512440c0601103544031b02041000108011a0030650082c07200c008040400c0343ca01902540d89450210041e1003c1c3c2d00290046044400c02e220141000050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 309275161 1250 309273911 309273953
    0xf080714041d10060903030522081b04090c1809150b0102010b04050606040b0f0c030a0509030c04150b1e182d040b010507021e0f01261b0c01020304 65
    0x1801c08101070249500741c84021f00b045400100d8600102801f910580c00c48541900060040e0b51458081c1e6580380903200102c01c0851003100550b549018420111f28aa010104940c9940f400740b01c0e600c0d104c54507900c030401e1071b160b800d620f0015201414800a0b02c9e030b09500040c502c440c6c54002400c55000601c0b860050f1300d005e0501c071056461605950031500d105180d19551112501403d94a01401800d22118800480e2030618107030040060318901c08103400726880300d08150b042005881c442c584d600440f5811140034040d0b03400d00c40c0104006c2a00c184503000e0b8208107010254641e0000c0c02c0140c42d00c80092001205282910b5804024141908042a017440403410300504600e0303615a03038402c0760349802c0401240d00590641d1700154005007024440010b41e200406a40c0c4203507110b602c64503415070300020075801010740601348240c01e140e10040605110760a080c29501401c102e40500c0151034403000c85201c0e000030030440b51802d0015840f41000c0ca80b144030007a03928850845 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 309276411 1250 309275161 309275191
    0xf0f0e07060e0103110d091b290304020f120c030a080408060106080108060720060f0a2304061d030a0f1b030e10050d0e06180109030f080714041d 64
    0x5000e030b00101b6600303240d80552000074070411a26098904000c08094540300d07800c51400003403081020030580c0312691004041d48501d8002c4680d40c000e42c07100711002580030120350705640c00f6040440e6003019522407581140c04190181c07002914240c5841401c0381d05080000d824042200148851401131080382003c00701d43d41400c40d8140c9a02c0014101380403c070034200e000c440160090010f21207139541c1c1041d28080d04024503c110306100c12510780d21030030b00380100214208a0050007030700021942402c85c43c942c44503500e0802034400b00c1898049509e4030003500e041044280001d060310009a10380844140b00d03200c01a20700d20500da411041420f10b04038441c00300c4e0300106803000d40d0030103c0b11901401420042501e06001c0c101520070124a0b00d0350400d0b1140c0001030342d50003400000152040c108199001a0903181034060050015200c0000001c909004a0b011504405542010b0802d41504080c041c0181c005178000311912000360040e601d03003090900740f150005035040f800301c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 309277661 1250 309276411 309276431
    0x4110406030f11031f09020301060e1302300303090105160504050909011d01090308060618210d050307030b010905010207290f09130608060a0f0f0e07060e0103 70
    0x240200c02c50342c01520690310120003a400d0b54040c4011244404030301e030100000c643c054502e40003007000a03c200e000e5840e1090115006e1141da00042c40740c0900d02d08030421820a41c244a030300c3c012141400504446403001c40030408d00020305510007071400000b59240c2c41c01b03052160035201c000d000d1201407050307101089049130b881011582641c0c000e607400d1a580d1518101c0d00d0051a850301c1154000590b45401a0080030640040c0c20080c000c0d9103008083e110002000002c1c031070100c405002480340307880820307142044680802040202402100c40b01410085581814060110f010015000008100d03131540c052040d003d0300360082c640030020740d0406001070741e504d42e18051218180c480d4110526407501c240701010131654001d403480d0315480b48103c0e02119170841c60099125442220b941307a01b443c0c0c40c0c406d01d42155041802880345442e040100e00c028007103401d00180054503400c405096018034012000700800e000010640316141c0b0100816522409410034101421314200c0c50b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 309278911 1250 309277661 309277673
    0xc0a0b043003020f090d051f02090a090903090b03010f0f0e040302061f050d05010603050d02121206010e121b04020f0d1a130b090a0b100305060f13050411040603 71
    0xa04004902c2c01d00690b1520701005011071402001001d0b58041c0e0b10050b500100100843c070001020296042459908024108a41a40261480241c0154541c3c2d41001103181d25007202e01c4450081c10f0200c1200d0b1183c1403c401b0368000d0701b2a08614070507800070050600581d507148010904c6014a110508082c0c0d402526448050300b071452529542903400750308000a01043c0042100a240070300c000e595103061070103801719100948036070241c0c02801c44014000300d84040d40141c0c90800764589145074440008051010305028100700303d010407090181c0710459020300d1700075848010100341c1580c828040c95201f421031064003440c018400004250b1040050301c0b0b12000640e008600b2a80c00c171000f036407004802040c10790085900114a801440350380c441002502c080d90541c125031303190030250003514203c0c0480c42c0c001d03000d480380d0448213209601042d0003000040c103003800305500f2400140e480d001380000c074905c66512418441081840b44034040d51410654042c003440e482c6468171 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 309280161 1250 309278911 309278993
    0x20114120f06060c0d0201050603060a061d0405010b090124180e060d050607050a110d0507030509030c03100b01030b04091a2509031506081c050c0a0b04 67
    0x80403440161038041020b603680c050581c3c0f040001d400c1281c2c1c0b180390038000280070b868190340d058028000c040c04940c218045000784c0080c0c03200c501624803141174072540d040b003e44004000340c82c42e55a881408260b0b03130f01c9140c918000e20180c464080c2c5000d4886112034450300d0343d410721061000b2407110062002034601e0082c01c991840011040682d03807007020980e078203601c1c0c0c8001c08038003442c010031200c00d8000c80a4020b5860030350f52421880d030341c205582d541c0d0314800e9044c008070358188080300000f44101c005107011b20703018081d030340030809820100c0c2c03a000801346d142082a45030407c09620707580c144a00c002c0b10404032003d018901564844c05400415001142216010000040e4170f4459408803443c4060307014442c21b1303640c80f89800040240d2170501003280d00b009410318032079800e44903000d0b960603940741c0805072288941c4241805515107020f9414000d200003071100c446141c005000b440b4005001d21071060b203600d03051a00c4803415404084e207004c006e507900c2d030744502500040c2c84 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 309281411 1250 309280161 309280171
    0x250314060d030504050409061401060801030f0209070219030306080f03090d08030403050715060303080c0910032c060702071d0a020901092601050c090f280f0302011412 74
    0x40558141554281103c951081e508131a03001420034030500108001ca6028400504008418030010798a81d8011580b0b01820310010f8a103188800f1400e0240c6050410207070000c5890044881e540e22700d1030035800f010303007081096010a55903c810001c52000380200c01c006a5644081c2d0325000505c070006185020001007d414284c000c8001820580514119000c04d40c02c0030301501180c401601c1c41d000762195000c1100005c0c3c2101c04617500c0c84111040c6ca414000c000c1071864100300c8444102e0081006101d0141e010b60341182c001240120102d80f40c0b0340201c071001408152801540107440c0400f81e9210741c0c85500c00030180d4034140c080031a134942000c054030000d84d6903964000101da035510039402c00f07c1052503a0045481003500c1d0300304010016005c0c402801310b40c0d07902c0c540d01024050341044580104654030500350381c1c0b900481c0d0b03e46190400180340a00507084011454100003500891409a2000300c1070043d90f81201c0051500f10100180503d40405580a00f02c2a600940 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 309282661 1250 309281411 309281419
    0x10c08041701021201141005040b18043210080604120302091003052703040302010311160c0f050402041503021303060f0605090603070806040305030705090925031406 73
    0x44214208290111070380520140e0403810a541c4540407401e8800654144611804000002c00551801360066a04460001d110f20341405080142103420401c042d83c43c0d0350cc159608100541445aa00500000e10440b18124030010303025101d000502c2d0090840031014031101c0c01001602d400041c1548d026602011440020702e4001050b80a405480f18050340101d042c45500b0503e585903004501c07030007030001500c0303503400c423100520380d1501c1828030900300790801c100030701c00365009403c8a21001030f080b07015454800c80035501c030075044101100320f45061141c203082140c854030300280006401c04440c118074081c42c24401c2000c0740506001e0304241030f00465094440c1c040c42900340021604148180003414070481160000e0120703005152080038100e0120f0110700740014800240c1e0128401084c55442d2510305a40036040202800100b00003005849502d0315400101400390b148098003201c1240c1c1c106030198190b40c485284030030186012152045892200d003842e410100541e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 309283911 1250 309282661 309282689
    0x1503090d1805060708120a060302060a05130905132d2a08030310060e150306060c0106030c181b080601030e03190905010207060206011a04030209070309020f010c0804 73
    0x40d59200d07124507141e02140d0300031000300300030040c850554001e10245030258850354260351105200011100517001c080d400c08000c1c80b00a00083c054002840441100b100c03030414641e40d80d5a01055501c00c4980512142401104000304104080c0d2105080840f90035a5141960150320842900c103588025140c4100e401c1c50f1140310f107041c101040d40805041c110740c0415240ea46003070341d0380e105075103c5d10030400c140c1c0f000404038031516540c00c10100041c00b603043c1810801c02049280c102909070703a4032203c00c00c400c8184050903c1420300440c4104100d5001c0c41c6848900007c40e0501c07a1031800c2e0034288101c0c0c49000103c0f8003840b4112a03281086441602c030303d0012002046001c0d54071900d4030001409060303106402d40c03140b140300401d0f0b56500004d40c541004a032581201d20036240503a00103c0103005421140e1141034018200071252401c0aa0700c0e00010710421081d909000030968541400c406e5003400c14140b0031401003820052070505a075a142e69040c4a603200e40d0000040c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 309285161 1250 309283911 309283937
    0x21206190225050604030e060702060d0b06190c0c0e090c010c03021c0905030705120d12140c0315040501050d0201030b130903020f010f140406091b0b04051503090d 72
    0x22050b4400d00c801418485003140003440e11a998040039a4140c006c20000002d1a28915184080b61542ca501a2406090880c50a207581c003400c0410003056200000703000a000d50301150901c1008214159107080c041c50300c9003404406000150001d6010340020410482a6440058202c981c44c80a00c2d00c43c55400103410101d040c10784030343e129012034040d0780741d180c00a80d114000a00384d4600701c00380c07440503a5650070000d103100c8480345407106420940300f5680607030044900c4243c020b056a004208031002940104880e4412502001c4030507020051016400446500510821703040d101004154100f1000820850b4200317802030406440f20941c5003991940c035540007441c228001c007031000244501d40a511100c95040f920001e61a121640c400100340c1c2c0200014201204028401a1100c1d182c2002412400205076041e00368020400d0719800000c20000041400307600342a101c900f00020480052510030314101d00341d209009100411202240002d201c00040c04d14400110f08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 309286411 1250 309285161 309285187
    0xf020c060f071104110a02011406090609090a05070e070f1106160e03030c0105070f0201020310050114070b01060206011404050103020603070c02150f0307122d1113030212061902 78
    0x20034100c41e0300541420717501d8010451400c0641265840341c0c0003880551a4003200310851202180c1700c540c0401101c01003003590a100b40c205030044807020545540300c0c1d054890900d0103e40b50b00622040c00d0000820110550001000c000c0390704034501065031000340e0311600c1d5102e0b0702600d001d20302200303031f2190f6220382e0150303104001c80103025003a25240d248c0c84034a94002c5c0421a541c0e40480d44201c101c0709103902c188202c0388150041300312192014100001100c0c0d803c868000350040b1407041091102040740c001c000c600070076559009040350340c1480d000300340780319413048203c0c092401c000c01480140d81c0c140942c1d9100c08180f0300300c407070720b030581c0006071504041c000c044440c808000748100c2118041c2d001944a00703403644481100368010725502d411101c002c5d80a20710040e135403807001c14400a030344d0b40e451071402c1c0b80c4001c152200a0080100c0d03da01c00c0310301000708400d130340080045082c003400403a0420400805403820746090742e801c079105092020001c88660307001a2454107244 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 309287661 1250 309286411 309286433
    0x3020601060e060714010b030c0607050604171b1c0c0305250c060c0201090e01031203050408040f080708070605040e0a020a03090c06030509060c0405011d0d0b0c03070f020c060f07 79
    0xd0012034107520040885c02041c001c00c0030300d400380d02a01894001c1e1402e0305201c4102c51000354080001c14865a4585542550400049003c05090420808500c03a201e5800b081030704011100042c0543c1101d01600c811803242d0400002d090003800b10201c1c011036080402d444621034000708650b030310403403060030f00005400c09d04004c010900c12000480c003994032901458805200b80c175454910340c1c880c940d90025100c00d100c02008860b2007912241402e2181d000550414444c8082d00d04081d220360400308543c400340c12030075603036020500c2004a44d00c100484070013002c050600c185090300b042140c004041c1c00801c110600c80c1c0015100686074404e80c0304040c902d40041c02c90b800c0790b48034400180900001c0d1903001942c0718070381c089103400040d90b04030303011200305840d0740700007101a04d40046c1070502c103961254404020980500810079030712506100303a5008c00c0302c40e81c03880c0c10304004d0552880b804c5200115030216403100c4079911103508035440d414020310b40c03644901051601081d000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 309288911 1250 309287661 309287663
    0xf0d02060406170108160b0a030e0607020c1503090c010807120219020c01110304050f0a2102030d0c152f0a270b3a050c0703020601060e0607 62
    0x9400000d0000e07a05901c6001090341d0700659041043c1a45e81d040b0395a07072942020042400402c07103080400110b01079000400080d506070034081810914400e5041c01c0170022202240940c105000c52000e51a0903101c40d10800c009080c1d150450500900752a61000041c1d005030503c0000004580514000c0210f02860030700b0003030540d03803085e131454800c05c02102c03a0144070152095016401031036000d205406402c200c880011420302c1d180000704004155040d485540001d000340000c03586200d00109120106442e402000e50401107105051812581e9100c0b0020041d00b02241000201004010540e041d00c00c00085444075210200e103003110b42c178041c40c10141056419a4006c8030110700031b040b0f0203505440d554112013050480032107120f005d407001050109003600a100138032441c002b030015401c0824081740c03004c0300503c0010080c4c82056511184200d04031020140d5050350140c1603100300000c06440c1000c5c2d0075540659640701c18001c2005005032614008030544909060711103003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 309290161 1250 309288911 309288919
    0x4050c0f010215090d12020304030210180506010305010b011b0c06050d02041e0510090513110f03040c0e13030219030e030d030e06010801020406020a120c0f14060f060607020f0d02 79
    0xd00301000a04d41d61500524168007140988001c1b01c2031003c5882a21b1140fa0180c000d4500c003801c00b0000d40041040000e107070713030440b100440300c000303d4010031005028610075000000d004000f400003400141d0442c10300d41c441c10380c403800301c40001c41420740b00c1c040328441d05065840e610340d10304e284083c8c00740da08919541c0e0710010f24203113054805065001102d20a079100070000c01040da01f210781030600e010711a0407620890f40244010101e601045092001b00c0f03200741044aa010903203001c0d80183c40654034000c00c2c1100f800503103004d5000c0c83e00560f08907000742001c0700e103541c046d44815072400d51202440e5124458018075010b2040e009040340c0c001e040e0380007801d60b414094014003889410400b184600c000105074084144215415258560010443e1030b22507619031a502c10098480010040c407481014002001a00d4142c030340343c45401c251005214540030f141ca407020040440061a11103001d0090310346500040b112101c0c3c0507039071058510101d05c041401300150510080d04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 309291411 1250 309290161 309290203
    0xc0d150f0e0a030f020123060a08010c26070f0c170f0c07151425030e01020c01030c12020904090803100305060c0405010503190e0f0d02070e04050c0f0102 68
    0x44a2001c1121941d80c1c3c42502c91400d01d03002488228202e40925144c542585410020081d9024001d0b8800390301c518010b001e1038a164407204058251502c401014020440107a244c2449459004d07411844000400c0c44404a14204000a05420305100d4841c141300d4001c0c0f0101c14003031640f854132800c5400f202c00e540e031500c1018055205600001d00741c04c42c0c0c0070710400401c1c00010309191144c07400b419501c01683d000308030006001c0c0d90242d2958203541250041c1452a00c11103a1707210345241c02626000d0303072034200b800007900302a19450381d41d04151511150401c0d41f90094169001090352741d100503101c69944010800034144201c01402000002c801c00810b10100c00300c84c1d041d24401d00036641242c544000550103030186019041c04036205000040340c06000550742d01c41d60507012400305820303440c054520300b40720320015483c4d00b0390040d00303120800d150100700000040c0130b00f0381161480d203030644030300c1d80301d031294082d4a10603441c0c0d03130004206038400c2003c407030100020400034035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 309292661 1250 309291411 309291431
    0x40c1e0c0c150239060f0a0e0a080109080913140114010507050a0b3102040b0a03080a120b010905030c04020f09091003050706170403111e060114030c0d150f 69
    0x2c0c041c1d42a405420b40480f101360000c1424170806440c0b020080c03ca92034101010400242d0b0b040b0b200c90480c0d0b030001d44035580043c00c22424000d0045e040c0c010200e150340d6012a00c240002d000748141e500d40c82ca41840d0000d002c22219540640c1101d0200c0761492020103514012105803160301405010781c4680b00116080c80003400845000300d00c442085ea120340d00031503001d03002c80101d400030b186c00c8000d10084030150a01e0b402c140a1030748000c00399651191a80c0d10301280b60004002e0700c0004102c50800c0e2066010342c8640205190709091407078605103087c0000b613503460380c089414003032900800c86078000d43c0e61105881c4130420081224106103001c110350004800e0354841074405114a4030000303007440c041c00b0340805c01d80c15148540450342e42d98030b00340c0d8040016001c01001c1d01c18401c0400c186510080c0400d0122800c5001e809154035061050380030310a4840c9083c400c3c0c01218000ca05696451092010680c3c04103091481c28101c00c0ca00740104251071004071900d052213145d41c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 309293911 1250 309292661 309292723
    0x3051b0606040c0c050d0c06060902030c03060102010c03060812070c21050c09011409100e10030203010518030a08071b0605010315050103150e0a02040c1e0c0c1502 72
    0x2841081d0598042080705402c00c4112401041104c015000e0342281e001c800b03c00d881240305070600b40c000e50000c114556110100001c9074030407118502c100c0d90100c20302006680c28042c07500c2c240c0039441c040c0800c60502c200300b600c80da600c8070310f001d501c04001200020000d00d00180e000034024100f182d02c0d0102000700d05803141a076000e0484040c0a000000100303842e000090b01d050794518400810394031031010501a60750b40241030b03003090010050b000102445031400170340c821f8100041c0c1d05501803641c4140b50035514090060f58540003007000300329414100005807454042e592600340c1a40c0c4070980140c50500c801240d07189003000c5004104280440b41d000b11707049034400d48650000c800d0b00c01c01801141c1d0207020040c0b1845594800300c2c1403d41035041103512188000c01e50b640c140080e4002001c40300004281004980d8806079441c4109441d0021000e640c0c1074100300054226a0b541c02d0301c02075040c000e0b2058010080741c424841c40c802c001c0cac4003010f4006403007202c003612002aa0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 309295161 1250 309293911 309293923
    0x2030306090915130204090203070f08070602030c151f060305070e010206070c060509030919060807020a08070204110705012301060e01020604020d020409050a1a10030b0f0403051b 79
    0x98040d00d242408a22a400c000854060f0100008403d45658840c03c0e80c21240c0d080c541802e1742c5c0107890f00c80340d2000da9428008a4000c00720021a4250f461a02d41101d08086096002c0c20946d0000e00c8149a2040c011408101d804240c40205030306660344a0b2403940400441d5172080c1c0b0344504030340400c0c6103805a100318000d2035191107910488508100482e5115011582d500c00112003070f49000c000b42540e00a83d802484800507241000d018001054001191003100b580b0b401e245882048000d81016003203400259510290580005540341d0310340b280f0038078000a00072076507501d00c8662825080251081d19074000002c0c42044020741c4551030143d0b4503030118042c81070070310000a0135030090034942d1078400180c001c3c040c04d544d281c0810000c030107402e50aa030041c2d1501403000018100b8080400d11a205070061062220b08289015018000903d40c0d04001340420013800480c0809400c240c3c000700007120b0040c503554500d0121854002e61210030206003811100030301da03400100f03003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 309296411 1250 309295161 309295171
    0x3270f100b0a030210080405070b16060605010206060915040914030a02070b1c0b0d051c020613080f1804051806060a0f18200a031b09120f020301050106020303 70
    0x1400541c400e8030800036000c0ca9840001d40c420050420488501d00404081d64000c0c0190b0071b442089646030b00041c1181d0007512100210f4032129120410440c1520500c0013030301081c4010a003d240c4000458140d400162a0310200005e0018480c25a0745582108903425801130000d0343c00307045401120b640740c00a55003c1c016004020009c91013607001010354488600f8000600f0b405801140c20138000c041400102c0d40080c40c2d10407050200340200b0413018103540d41001302d106d100c42d01c64000e042500280c003607201e00000030012000300b1420750940c0c612005030203056035903840880c05000d4032510745080503003160400e003c11880708142c05600c011240c0c0d00f01560001d6a4401c01c200381e01909008607100803249900c1407000d00442402c807031145070f40ca9000600b4041e1a40d044144031100405031a00100010302090358941c940105100a0820b400c1c00c007a03039112050240031059a80624074000d00184500c03c107024110a805d0101070b0050000c000550b12500700030f4803039104840c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 309297661 1250 309296411 309296443
    0x90307021c050d120f050903030c250309080d0f1d042c0712200d140705041803080105090a091a0108151308030712020d15050102010c020303270f 64
    0x15001c5901c64041c00b80b10b07c034000d1035024600d15035031f688280000703401c01c5090f15074003050403040b00701129418600f0030380700340a511800e0015180400d21864054607044101c10000d40840c400545a04005a1000c0c41c543d210100000d10304040818028034800600c000c00e13401c2d032400000721b04101980c000100070f0b4901952441c907291483c0094486030110020400d04050780c0e003140540300701900030780404005010900312150340c0c031f414541d00d10034034000c100382e00001d000b0001c2e450144280440040c2c41251000c0742c000c00d45015203001014400c4038020b500440021741c0981c240e502c46540d241c2e0007178000301c42d1019028000ca004409001d414010b20446482c9070405100f102d056210f41421a150300840380d83d40e07140c07a610382000e09910207201c82e64200e8500306901e80090b041c2251001e5000500c1450301030351441a095641c415419079140c0183c0380b101c0d5a003c01102c9d4000d081014917103010500d00848100c0791014000c02c0f20b85d000f40402102c6041011070743c0c144114000c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 309298911 1250 309297661 309297671
    0x40f0204050603070e0a0905150703022203020d140c04020706091b0305030714160311014e0501061d041a1309170406090e090307021c050d12 62
    0xa410f156854580b0700980300301414030740001d110b60082e40c1114661758403030000d403030204500c095401100c02c42610654003003600800c881e1441c4c11401149180c031120694120381c05031444d0003003070700d40c100108c000c2c106030300ca141d80e031401010070002940c0d410030240c01103595010700d0a010008009106040390001e0021355415921320318410204252508200654982200d664501c144000b8a9055410798012a820300d490142c0c0000014025070250a00012403e681c1e000140312600384480d0300380032414440c543e41003000d420b00748075054013a4105940b04250000e009510b00f0300403012091220b04201c004501d05601c003031401c28240450049880c0c40e54070004200985040124281840000806941c054940300c40c2c14042070101290004a00a003910b9000203802d90024107460310a000400f04405a80f01d0101802041d05201c0d442a50074901183d50310f0307204042e03003c2e00c078690740b82c4a4003c043d00458100036841e44041242c8400c11610f4002c1d001511010540c3c0d461851720b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 309300161 1250 309298911 309298921
    0x231803070303020712060603081201090b0d11010c0503070209310b131110020f0f060907060f050f0408061503060906071b02150705061006020712030e0603040f020405 73
    0x3031550250781e4950042d104203411701c8241d00c0d004403500400c0d04c1486d118000040410310b84402086c0c0030582008502640d03041c500c5400c25900c02c450400e0146c02140460004540c500c5003071440b0710800d00c2c0c9481c905c030003801c0003440e50041001c040d62102200741807180c0501b110710034040300841c249000c112100d4000300380741d02d5140084082c065120443c0007a45500e0740384194070400e07100c1c008584c684010032000c503410411444001001d6441a209500c200390100111590385103058001c02c081e00d05604920303294202c0748104420720062800314060240681c09a404200c011030007146c0315958bc0300107950706d4400380c0d008034041c0ca001c028083c0300c1c100803800503c202da04100814254a95040c103d420403010020304115150700d114007001691014502030801802d103043d2034840c0300301c0c00c10a0404e00054007082030310014840810465030045803403401c407000c50020f0002001907040603034400c85091211580501c00004200801c8119104490361500a550400c11a911 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 309301411 1250 309300161 309300163
    0x16081305010e0d05030304030e1f0905150c030405040b27061f05120711070803030a05090c130c05120702100c0509030705060705010924050c0a05090d03231803 70
    0x41c100c3c010304140c000304002808240210102d0400c41406020145071918900840c4100c90b41000781c40000380c440da40400042c45d001500d01c46800415003041d1800b4960301c14140e9038881c41c4501806203840344000011541c4543c03203c119104011020706c00c03000c07107240801d917151003207510900c1140314244040504d41080007001c100f44032030700d60fa0301e0828a003a5600b03010300014008400c01420f03004681c8030310814410107000300401c42c0196103074113145022200b82c5200800d5152180c0c806203604480c0c0d507038505000250102101d00041243d06114212164030a002c1c609902006020901c10712503400035031802c103025810b82c1002122050042160035109e1200c0d8154180d10000042c04240346c10340080110764461400080d40d1040e039074400d881e0088111680c1940d6030401848081038181c1d00407683d000010f100c51602e016615403019001d8040d010b007090007045120003890415002e03418008903210345600d07410b002c0403807095144950f40001044071450041d00030b08021418 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 309302661 1250 309301411 309301429
    0x1060605031e0612030f0405010809030702010c17070c170f0a0c060e04021b03071703040c03080c150a050610020604081608040902031306060501210216081305010e 72
    0xb210000000b0002c4400b50144440d1009040a03620620101c1a55408081000200607040344e001d4030584591500c0b00160074890000c0256034980c0003000084010703030b44621480e64103a03000301c580280d11215104502a0b009008000700b6a06e038000011504228640700c1c10608801d50f000c903800012407400540d00d9141001c00149852060300c0c041c02502e02074a21040389040140c801070a100e1f4480c0b880c1c030113680c90300240005030800145030041c40941807507034410000042c3c0403491818640c0d075030070300c5d030500d844083c04112000c21104200f10040c052051441034410a12200e0b041407071007140288404e90b845841055044c484504450000c2101c0b07110b650010301d164204003010694040901c422402203480b4081000b010490300d01610117140070b444400001d0b4160b544500d0844120f9034560130180c14040400b84036020341000c0d2001c80101800d4400c0581c1320130800c034480003040d402000c003c240700008210031040404001154081300c0c0e003603a4403d4144400e41c280400c2c22 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 309303911 1250 309302661 309302671
    0x601110a02010815060415080601050c0304090b061c05150d0506060d020102010612050601030204060e15190b04030303090506160807030e0a020d20120706030f02070c170106060503 79
    0x604180c144002643c000c0103000c0c0d004440b12215011540040001034032940036401c21103413000900080b0040c1c503400300070154820001c0c00c10f05e1800d102d105590341c0e00d001c5c6104440d116505e0b84259000c3da107403042503c02c3e14a400540034640841c501e0400040d100c11900300c0c210703094000070b02d11646440320800c00c3e00c03a0420098501a21000c09100350003031550070a030f065640301d420020f5070514039404540c40d5402040544011b505510420041c0c4d0307080d5000c00b00580024050080c60707598500c1f003800190040700ca80a0211045d141d9240401c1d481c0d0051418081c0410000305154058002300ca110784660280c84150b030325515102d10340e0002900d9080000c0320030000905441c0698072900f1035400e0202240c803148103a0303000a64000c0042800c442160350b9090000b49002248042841d5a5086a64032020a081d0009944e65242c40c400c1c0c0c0c01301500c500c2203440704800c2e41c0c100c0700c0042c0c0014040d80440c1e1a4003485d0030303403030700100805041c0d8030700a40010380c2d9200d0010ba2b8018 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 309305161 1250 309303911 309303913
    0xc020c100302031015021c0309020906090718060c06060f060507080c070b0708210606030c0a1b060e0d1407060902040e01090c051203090a09271a060111 67
    0x10059008110002d41008280460280c00001302003440c0b4010f404070701d041c85055004004170440402e01920403a00c0c0328000c0d05143c180310031000141d4a008000e40c2c028420345840e802941d90020460f2100c241605a0345101001c010106142c0d40c08403402c5c018901840e018811503603a20219116180c0601c01e590001e2014801200001c55030001800307000b1921044401c160740710030b5248079540c0720b000111051000054444a85280c0030700d174081d00040b0707104100c024a4050040b032101e10008001c502c1c00c0c0400a55039840600500c2e05020030001c407041c8110310413040c0f505d000104800240400c0724031800b418120018441d941c00030114407003103207103802c10000d50b541c034001e801c642000300e070711031340707070780110108007000d100d010312803405170100000841c500750510a010030400b0300c815880d0420070015103141c4800c1c240800f2a04540b0001883c032805686c544420100005500c07080c0c2da2948610003070040103401c8585842840c00c028807591504001510405402c540e00c000d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 309306411 1250 309305161 309305179
    0x20d060e0d050f0d230c070605160c030e0303310e070c020d08250c0f03020607080d090816030207050901060215060109121a0603150f100902030c0903010c020c 70
    0x903034610f98000d4650780d03030080403540c2d1001c407401746000103120440d40004c14400100c0c4617803d108039030180c103810580020701c5881001694000510074059480c0c00780c05c1c0f0800601601c035507201001154000d24807580a091170140000301130040c0754100c107800145803651380d0b000c14001880b2501740c0c02406d00362103003600407045030300f071242ca10311427142030394213980c103120f8811003a036010008943c403d00e14042170240b84951914800c0075940345c004803202c804004041c801038035944111481550003402c45a115610150103c014040d5064004c0114401140300e801d140141c080d0300565170300c070b5000c1cbc64600c0c0d158014403550314002d00c45e5000603440280010544440000280e8008006150900e8015107030388400420204201085600301b0480f4100680700b2030b8016040d0b00103074118082c113041c20300302001d00c4520501034500d0060141c0000483c1094408002140c000c0c81008402d644914202c54040d000da080441064040d50800303800e42c1103030344046600c4181c13030002004115 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 309307661 1250 309306411 309306427
    0xc0906080f1009021b010e010c020a1b050a03050d030e06040308010603020d14090f061e0615070204051608060d052d25060e0604060c0609020d060e0d050f 68
    0x5544000540b508800303410081020400307008070700051404002c0d5280303040e20b000030840110f08468180c00e0151640c2d24107111583d00d980e010071842240c580001000140c591b80003031072100c0c6a02c42c0d2210b81c0c009040c2000004214000c10401e1000f15651010001420465005a1100400c403001400650540010b100540c040e40c0031b000e408124a0002a101100ca103001c0480401511044410750120140d8108420304002065002c03140f400c8010309403008140c0844c01ca80040c00ca58850b58420556460303685802003594a41c98006005000b079044c01d03122406071001030514140003580000c0020f030b0500788008481175a5030300c8001015600807140c00c4110962109050000c0400c4000b8901050082000001d490748941e6801c01b150680c40e50751280306864035402017040c4410a80c01d4a00c540d5482d0544007115002d0410407080305582ca0804010001410002c0d4000c410004120600107203a10170f018007410742c011074410b03042000c02503440e4002e9140703600212200300590b079 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 309308911 1250 309307661 309307681
    0x1617060a05040e010b0405010e01080f070b070303020a050d060b0414180604181407150801060207050d0f060905060105120316020d0c03020618040507090806132a090c090608 76
    0x5010845420000417005072550004007900c0e001c0e4042100d24100800602030301c08103110358000640380200400310549483c49104680c040e020000c0e05255010620319101801001141c0d590200900e08101140d04e0312007a8256810902409074040503034100c803c01400e250924000c02716008400c4005681e030ba40422025006104c14007403041d0318014a6400101383c2e002c44100910440b02600b180d5003010051005080000101000c00180b074004100181d00800d101c416554140d400c001c0c2000036080a010107009480b0041c00d407441c0206220a2100100d44a41038920842c0e04505054040340c40c69524060780765030605014012241100501d000070440c1c1d080740c45401840c100a82e84d400240ca0358105c5110348242082c0b01c0103110345840c2c06d2094035401002420703d0b00b074460418108941e01c4000810348101442200031550521a558550650000c0c2c82c08040b40f40340000c8071a5400d0900510034006c41c01d0806203040042c5000318602e4003034442a940e4480c59980780c101103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 309310161 1250 309308911 309308921
    0x120503090a0b0402150c0a1a041e050319030f0609050c04090b04060911040e060d240b0a080c01020709050c07121115060f030601030c0b1305091617060a0504 69
    0x40341e0242c5c101130201540320b040742c060410140848094959208581060703421004001c1a82401c500322108220024030304d0035008030781d41501c00c24031303054041a107446890b6200b03481180c40300886240c000e00d0800c1d40754000c00a03d41e0119418441e00ba0365403ca01c0607110251000c071000e07207080c041404001c0855000008082000f0004182d05554640078002c440c490352012003000c400180c18400703602000444ca4001c1d1042da0608406803064844441c5180c501003515001a0300c001c00012000c1e1a820a054805004140315220382d07507480c03c00d40e41d050b42d520550160080c800001910f1820744a550300c1002846d042c10b20781041c80d5225022582081e000c00c09101803800c403850aa50200041d41814020701c0000800381062010000025a8019072038401d0344000014000203444c00f4800c0220388005981d903854182620810140c0403140e0003035034019a060041200310070f98190410220062901c4881100706000f911500607141290f04540240000c1380401c004c1c285507000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 309311411 1250 309310161 309310163
    0x8033111013207061107082109060610030b0a0803030702011107081b0a060e0c010e0f10180815070305090d082a0c0c03060603030903060f0604060b040603020403120503090a0b04 78
    0x400980c080e4280d40713074440c5d9008243c0c1902e50318400f0031030340c00134591805d481e82c0500d4843c524200524050303c0503566100020320341c40c0103044151045d50514041d410200c3d100c0f1b001070000181c80d450700c480c99a01c2d0411a401070041d8200603506145190290440e00d185401041c103c0c60030003d030001e4000c0ea40b50303155001080c80780c41300c0d140c0400c1603885110110802c541c0508200318041000500c8820041417491298001d81c0c0c3c810016034803a15401c4a41810b030611a03145100d440084041d0015603026030400c0c003d0340c40c000d030030040201c041c5e417080c6800d031410003040c0c407a54826692060340c004c1210104045a011a80300000d0040c01419042541c04000030702c400110341140c9a0000500e8503502c0c4e20014440f81146014092941e102c10b0035402142840c485200103984c031140605040b10340710780b1102080b0162207981108001d0b0521421842e5a0381d0341c2d0200400a5100f8442503a0807400c0d090340c0d5802a114a0480b0300403507000c001005565055180c04070200c0010300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 309312661 1250 309311411 309311423
    0xc030b0d030c060e07050d050d02010b09010e130c09020a02160f0620030706061707090b150904020c011d16181a040507120f0908033111013207 63
    0x1d1b41d82c4e1070048041449202c0c201519090881e000042e0035103203442d00b014803480c2030348014050042103005990340800c1400e103d0720050501d040000c050a0740740c11114216000142d003803401da07000111062108001010303409400d46e0364604040002c8039016500015031001004100c41c0c4140c0080d0344050f4000046d00d140c0f9925544071000c075605c035807108900145501721700d050b0603000d1000400610603500140510b008440000306900d412011701c1d19000c5006c04c0d22030043d182d65065030a1320100f84002c111104911b640150b4084498055241c20320440030140400c01990002c8812140002075911034041e10b021008083c04415405c4441d8020004c034459030755681d401407500982c01515125a94803100840a081d900d04c01601e00146060840c0e00e0001986c2c0c01c120380d4016801c034980110743c480f0040101c00300010020000704580040345d0001448503491413540301400c241c850b047c10004081000807001c142024000440c26060f00c0c0d0850b5200400003816001c0c071440c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 309313911 1250 309312661 309312673
    0x31b06381005130b210703050610030903020a0206040e04020913020f0409050c0a03030807020c01090b040b0f0d02180f0909150601021510031407140d150f0c030b0d030c060e 76
    0xb602c0390720243c120b401880d02240014034000d0b61341c5215014646c0008647c5404c4c8010310303001c40441c0d43c1100c00184113040555400c16002814400d2040c802043e0340204200d0352a0360381d4120102000003a41d06031320800300000840e40a08d804060300640342d90107001210300c03040c58400c01c00200701c20f410585450086100030060341c0d485400c0107001e148642c40d0024a030034182e01c001d20302800316040b00d040c452800c0742402000c441c0015601211100c1190560700c540f40369811801d03004007503541244500200d032071000d424406040c242803e42c00d6500904802c0100c0c01c01c0312600080d1000034868020380405030010701070b000850740c011b0040c01201e40034007040e0701c561060f900c21038003d8083c130359409041c420094a040308007181c1c840c060040c04040c0c1440b20848006099800c0e0302c0c440c081c942545c60800021900b141c4400c0e00e501c0b0704020714040881c42c3e00c05004030019038800240303411802d242d903282400440151a406a844038102c85450761064020300025a188082c1e100ba0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 309315161 1250 309313911 309313919
    0x105010f092708070f060914061e040b0a1503050102040920030f09010209030d0c0b0106050f03070503060f04020d0506090901060609050103090f0203011b11060c07031b0638100513 79
    0xd01961110340d08c03071001e0765a001410002a41010405449c11104c0c04860b512000c01100c86c60141e500250030045c408200d45803000060010248d9031404440c040400303200000303120b01940a40304a900401f828029180005603040c2c2400a640076519076030310034000b00d1008a00740308076540c40301000000503d4083d0b82c0000929088400440100142400b8642c008002901e07004500501441c00d15a09002040460600c3c900000f403e42d020090701000250603555581484541403101400455070f0352460f207110006045c0c02c0b985140558400e101060350004140308282c1100c0032507449d6856039050400450151617032240a071040d019201e03054000d03035030038464003182003201042a019803164040c0504480580c011b4101150041810007640380f00301004c4400b1141c0c14600b055481200c2d6226014000341d0010290070646006600c0c1010401401c030b051401d00400030000c1d00c0c0d524520303082d2104a0590307042d604001444520240c03d4041c002900c0c0e0106100c1910b407030591a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 309316411 1250 309315161 309315173
    0x30516080c010911040c05090910030c0303091401020d080c07020402090a091d0102160b06030102070b1f05030a02100e0a0905090c130507021c020705030105010f092708070f 76
    0xc0840050000e035902d180481c2002424008080300c1d11007071300d0500502d80c038824047c0c43c5000e041c41d100c1c00340754500300055190408016090107141c3c00025034038010340300d00b0010142e1103203004004002d0b1140c0229503e640c0000341c03406450b50303d40d0f2403610655a01075140302e240c00030030040340c11680074417513450995a86180000a41049440010395840882c082510341c101405020310136441001b400042c400c110320204406500305890320301d00d0311480042030080c03140b14409480305580c1001d2080312a050803143c03a11600402000c0740c2592207208041c0c03075a0b4130040003540002e0200c2d038100c41d54001c0788004078605c401800100919a210344140a0350021120400582c01000e51540e291404403a22500650302c02000c009501d410600655a02c82e90400c0380300c41010b1030075100e4414401c0080001500d000341c0244025651264401000c800f14082d0b201c0150134a0300b02c505c1000c10301d41c002c100b5082000c10045070340e201d8582e80e1807a0322a40782618401030b1603545c0004500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 309317661 1250 309316411 309316417
    0x9030921010b041d01060f0e070309030c021207030b0c04060503011203180e0a0f18022e200c0112021305100c0b070207120602160f080a020111030106090303051608 72
    0x200c480e180100c0c1004c0f094034642103a459411040c12294065000e10510306800b01590340140c1c00d09001580030b820703040075a65132101d24402580140340b1005c03101c00074400b01e0700800b00ca2203401da40489490301003181c204c030302070b43c02400001807090004100855005060640041c0a81070007108140c09811032803a00c10203070480c1c2c4652887d1410b0211044a034031070300c0005c4403c00c000700300d01044900d8081c000e286c11203001e841446404604001d001081040c100f10310250160382e00076850410000d841c5401c19034009184a070304154414036958081511101900140d4440705500b4044580f0380003904034898901c0c0c500002280070901c0d03110100304582e08c034170503198840b510740c0c980b0706071a44031002446042150820282001140030b03021211403155031048003d42c441150303400021082ca01414060310111000e9506820310078a03c0040104c0b1521344c0c000c2c8818144842400300e076100a2003011b0004000510810100c0c1c800d0010302592031a001034049190840d481e01310b9160 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 309318911 1250 309317661 309317681
    0xf0121050c130614040e07030623010e030c15030406060f090518070b0f160204060303200606130e010b150406030b0307210507030503031006030509030921010b04 71
    0x2400581401c102c501c04a6100c002d00c074501c3c051350740c100b8024503103000303014500c1007401d0981c200010070000380c003980102005d05409000d04403070049501000340007104080007035012a00b211005446420f0110b9034840010001e031540c61f0601140006c045240c4c801001a00c840d82d4490011604400741900302000300140200801ca03400c1c80715a0300d8420543d4600d4016503449900100146201e5100b900d00b121074040c1240d45490344141502254401614001e600c03a1078004040105600010030400c202d06804541004000e6098402c2d5141000d0f50035a51194034008004940d0001d5004041d0b10480c0d200086050a4009c010800c900c04e484080c40c0300700004a0700b8020141c1c0b6215503460148220000c1904030324200c44c07486081c0949407600c40c9481182103400034407808014400042d035018084aa1b2441d000700d140a0102c25030180307200190502e0081103a00f0000015950070180040200d14200c90074840d0100210381d455050071603549a60300030140f80d03a5441200420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 309320161 1250 309318911 309318931
    0x201081b03040c030c15081b161a06030a150c0903020409030905150f160f0b04060e0712080306040b01032304050d08072a0204050c0c010f0b0f012105 66
    0x4113040d40343c00740e140c11958110140300d550020016441c141c1c80b44c0b80c0e5411060302000002d05125160822103548210013034080e41c80a080c0481d0304211900f0091100f9407503000c80d070425034840e14101910b07000003039009481c0c5030b4404088420369a0304c2d4400c43e800d00f00c0c1d041c0540380581c1ea07030104042e16004241076001c034806107000c003d0381c14611021142c4003112039100d03182c001400da1504181c0150f01000600d800ca400030f4001b000380200c2c5800e043c80d080404880c031440e10385045e002915449200a80c980030b6040c00003500b806241030b01c650161301c20400303400c541d2003a007480000d1181701d00003030400d034403414103c03140c140c0340e00c48040001030784c40d6a0710903140c01c0c1085890150300c18401d03020080320380d0805c14840e41c00001c0c8207412049001032040540701003201e0044c00001074001e54004c0c6030405001c250700c1e4000081c030040540100074400a920740b00c048c421112500b03191030300140b05100340b00315984940c2c0024000d0b281a05680d1450021040030011031768111550440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 309321411 1250 309320161 309320183
    0x309060608010c08070329040204090e061e010b0403150f0c0c03020f060106020307030807110d1d0114030612010207062c071d091e030406090618030201081b0304 71
    0x3004e902068090740400c0609091011820407070030090100a2130083c0c4040c000a003101c01c00f5a5104d40403540142a010030074058102c480c50142e48914040e6400d032080c494480c03d404000c0309400b2800e048454a0403200d00b41407a64944c0c0a101240d030302c01140040e924804008038400600c140604102c4540d100c94800d0482d14010745048a01451080c80e9032043c80100a00390b8000f00300c0300c0c83da86c1031622402c562583c00301075801810012241004d40210008580101d6000300003008403d00341c01c0b50b010705040d080054428020400020454002c05c00008001d070070b0070865021400031480006140040c00c2d11810110b810342400240c041c596041c0410101c00d05540500307680d22a080a407040ea841c01d12080503000201c1410a01104214001010440140a00d107050b104a10f0602c41b180206882d094030380e0b101c1e000c0c070720120f0102c100c049802d6100d40d148403a000b5000000070b0001d0b0071500152180c950080c00250b15a40700820045805018805940514403500c803401d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 309322661 1250 309321411 309321431
    0x120c0904061d04020609010c0512120a0507090b1c18020a051813020f1f030c030e0c0904110d08130506070203100509030c0f030301090606020c09070e01030906060801 73
    0x10036281e5a60080c40795032554040262003071070031199660003a904407040d03540c5540d01001030311700840a24024159005d2007426901d403052110080110b0707050710500181741e42e50703c04010100c400a0701d2501c0007540da24030900c4040c20b4000100490558441000d5410f08410ba24000756000c0340e0100b003480e900140610f046042c5540e03464040e0502303c0c2c42e1500c2c10880c161201c1c1607540140b5881c40c000780031100c02c080d03450365150040d059001030024000190008103140070042c2c0440c4c5040040c1c82d2007504441948688210040401440f005d408c0c000c00b410208051060050015510030121f02600c6000d84e6801040d418990300c15010544c031084694010501c40409a00ca140281001c104000059034081740f41500d004441c0000079140d2030b401d21440c91400b4086040f030441c4036064034048007500010140d070484001e020140301464031480226111040d54032050342000040d400b003906580142c0e500e1100d01410301d00000c8035499501e5650036110f103580000100d9540300b030011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 309323911 1250 309322661 309322669
    0x5030f0309180415020304030e010e0405062d03010c020a03030b0405010f152a02040b0315071202070804060503010302030d030605033013060809070608010e0606120c09 74
    0x11018080580a107081c2440100403442c2c094805403811030440c9900c000404001300301d114002a0a80704134215103900e0189405800e062140c011039002ca61400000d0341146000c0c01080d01c60080030b010315084038460800320b007002e046444000d040325111402445191803d00c20a651404264001d080114076400c0150880c0d61181c00c0078011801c0100500905019030f1700142101c03404845079002d9003603200100e80b80108050040102c00d00d41010000e249801d2000358030103402140d040088500140402d41e9032860750880c0c2058005003000991014050401820614452400946031200c1c90781c800556901c260090400300c0e201000620035030804000040030b01d81e00c0c1c20300300f00b01414a070000f503880900d0381c43c080d00070a04440401081104000f2055602005c0402c00d842d01440850302c5100580e074040da4001035505c9002030074010001070020200d44898441921990034902c654407840d8004140f42c2d0003000400400b996800345486651040100d41583d5455002010402c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 309325161 1250 309323911 309323923
    0x90b091c030605060406050c030d15081515040c0c0f050601090b030a050a02150f070804052416020a05090901050a050a0b0f040f290f121c120f060503 66
    0x304200741c070b0040c041c083c0b034440208503000d440c00d50808548510100c103c4500d14410502c503c009030f410700d0000c54000705103550a109071500390b07090303618134452140d40e520b91803000c0383c4c0c01d0302141d406c82601501c0d00700f5502c0a1103144081c035084100b1005a22044c003072030f00d801b00c06c45240d40080010480a180d0b8428203042000450103010008001d48500fa03585000c2c1c0406803203a0005041c0001034049401200e8a078802c510002c4e03100c281c5420030f151039422510510b805410400c2000d49201d1503140f0b8850141030347d80100f0704081c440d47c80d60302c03039039084001281c00058680c00803030b00303580d180c0b0401c0c4101880c10011403a8074054050341d0685002812000700103040c00540182c50740c89030f50100304100d041c0e900164400c5031191b50302c042c106029980750003410101c8000c0c2000461006081c129600341c8003210452039490074440120040c42c07400030345802c03182c0c0020300b011034158010b811860300e03e082c818611140f09468122242c0800b10003840756910350810170350606001c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 309326411 1250 309325161 309325213
    0x3050d02060106090608040303052208070501050714030f0a0b0603040b1008060615030a231609030c09050a0905060709080c0d03050901050309010f1103040b0f04170a03090b09 77
    0x880815180383c085d02908840014000030181501e5a0000f00c04506560250300b8003e002207001d00707004401c0c01c25026590003014181c0f0070303500f00400100441d006140d401c08032450b4402062a5545548101d460614090100140143c40d43c1d90410300ba9108009103000340c0c05031040c02c80c903040c03010b040c04043c80241e0003004103030420020065640d8428001c07004d2203000c40e010780d6807036590042c154020a000545060030380e214500030003484000c084264480c45410000d8120b00e0b01040301a102c0100700d00c8010118082d40d00f0034003100da41d580007503420401e2441c2c04a402230706a603406040510484c0d442d40005c0c44074104010400c001c0000c02b16004060340c1002c8500c20641f0014518881c0180d414103221340003000c2460b110003544000828508100100403405842c103001c5070642c0151000c1d2072000d4010301080b0a0307240c13103c900f0701640e84084528800c0f0709250040711a604030942e8142071660f00c1445001050000c15030f18030400d0600c01900c0040c40781000c400805c165121 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 309327661 1250 309326411 309326417
    0x10204090605130504031407020a08060a0c140903070311031009050303091b09040201081f09020406030e010e2104080a0c05120318152502010e1c0b100e0103050d02060106 75
    0xc1840f010030b070410b103411066102800d049079100807034004038504a24032fa02c008454441e90f0300300f16103288503602c0b135590088141c2d103120f51207052000c0b614241c00741c160700d154180c1291600304000303142d0501c0d0441124010301a122402003154080088a56809003a9005d81002040000548007880403104d80c01038070361100a0740c400040411019907009100070305000c80c420200b03503601c0f0828500c44850f03140c054440000381d00c80700c00344040d41081c415400481c4c00e1084601c088101801659042d443d0f6400034060b10380144411034445100001e81050440100030110b0180c0c000d110b6106c40798002c01620088514110900144400c1940c440d4001c2d0020701458190090880d006216a21304442010070755108450001043c4581070103502704203415100b16405000c00460140c615000f6212942594246000d000820041000c083e07518024216a500060203012055400c07910000116100d00e88030310070200e034000c0030380040e152917000d000c841c0c0c8143d82c10031800703001d80141d00e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 309328911 1250 309327661 309327671
    0x131e0905060102030a05030a02070303110c0102070b0106050306012c15070515190903020111030405010c0e01110304260601030813140604090e011b090611030a0806150c01020409060513 81
    0x5e400207145000c007901d5120341076000200c00d01814400c0d00110950200b00320000e6960070660b1003030303000b580b10501c104d4240c1d05030000017401ca4054025a13105400607103d142031041012040203024000c4090700d400502081c22400d50741e01c4044c4c0204000e84660560b541e02c400500700580781c4007907443c0d90070054202030100700c0a640320700320f00388030b071500b02e440450740718074bc0d1800b0303409820180d0000d0790011010013000706101c01504520001d104a0300e0744603603081f0750401120b0300510180c0851607580108400c01c55103a00344115a00c00100203041c1516405a68401c2d081c10420383c400d80e05942c021810301c414000d4001000018891001e05425030817421020030664010761156144d0300ba552480040b11203002c0d080074049401030003035000c035848034200180c01010705025107000a80e40301c80002c2855030001c111075407000c83e51600c0f511030381c400e0200a50500a030707100ac58080024420401034910900141001c2c0c01c0f00e0502090950900091140c0ba000c0301020030f400c00d0400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 309330161 1250 309328911 309328927
    0x9080f031902120310030b1501050a0f0212031e070c12031e0f05190608060f040219080d0f030216150b03070b0c071502030906131e090506010203 64
    0x440e00803103810420071800500c80034040c2c0c2002d40d0b15241001d206800020401c114001455001c1130341c0c4540313084c0e000f0b52140381c590000300041d5410140800c0040081c2d00705103020b000695841d10700780c41207818540c4800d10116103600300b5984003c042d4291030003100040d250f100c40c01d1b44a0118545800c0c490f941d5120132500001030000c04e014995241550a040c0358499280342d0380d02e0030003400381701c4411360b184480000e15045808009840c0c649000c0741d007000b0540514400c0b5a202ca0081031a51614081c00325424805003049138060321815420060031850b003583c8004280500180031010313080e03a80540b080800b44003070400c141c070400c480d01c024142100740d0b02605030044a0b007641c800044070305000501042c502103030300d44201030700012a0414100208072030468001500c030a20b40d20303a54602c04ca9600f2000340d026030014405041d8904211020f42072099161083c4000c60342d8a0078041040d512028003105200d200c00c405001b0b05149001c1c503900440284002d616040c0c2c6c1e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 309331411 1250 309330161 309330163
    0x40b1c030e12010c0c02040605040902030a02060d0b100903020a06082203120f020310080c01050f0f040f03030203030711060705070609050319091e0302060d051e0703090309080f 78
    0x14582008091080000700c1c8403094441d104410301001c04180204516202c8002c00303040310755501c50482c0b1941c01d004001c00d480c1002e002c5c0790700c50303036001d0024141140503600300516500940c4500c0c1c0b1a65980c0d2a001c0180d1b2210349941c1042e90315151a03420743d00b9401441a030765201d8010348180126078060002103c518400110381d14204805041d40030150700d0f0840e021401400a01c500701c0c2030040f41c0100d6a003d0b401103002c1c1d1310301c0801864041d903580764551a82c41d243c0540e030200c1e0083c071002c244038040b10020010204d054030301d02d02e0b103600c8001981c12031400380c00640040c3d0000c0204850b80b6041440b058080c840d04005244920300403070001d0062080c47c0300180200c0d101c107401800c0140420070303105c0c1004007480ba4030300003904020003030041509101d001400c00d10800c4401014482828003003e994001c0c0440c2e2a00c51f003c804440030b4203010b41640010a55011000171080d00410314070300445603aa40400d600c1e0a5050040c55000385400000c1c8941001000e0103c03548 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 309332661 1250 309331411 309331459
    0x51203070503070c14010516180b0304020d0f020d0605160c021e041b020a1b030203030403020f1c060b1206060307030201031d0d0309021503061315120b06040b 70
    0x8492400000d007140d80d00c5d00d05000c0b20042c172154500c5d820301c004d110f89030039901ca0000302110f481d076030366004480c2142000070084891040d24001e4402300080b80c003508012700680344540c01b80380c0c400406952540810070401c01003006aa4040e921001e11546488070403502d207039440c987c50202120480394000481c0d0110305841d01e0541d036210a1011203946480e001440d1450341d40076496901741c01010081e40310340070948225803440c0884030300c0d90b01031203202055040da0b4004d4000d50420381503a00b40000c0844d50310b03409600074115040e4005a0131600e101d1a5441e100e4040030a0a192203418000c03500805400280305030000700400906440c001640c608a0740c0901e0003003035038054500c1701288000c0316580702c00280240c1441b00745098040d0084400c85100343c03040107000b02d840044039010301041c5d07089a070014640390a203c00c1d02c019001006011a8000d066004a0380e444501c0340e1643c0c00781c0100c80c24400c1008000e440d181c5841001d006000035120b102d0089844108d00011803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 309333911 1250 309332661 309332671
    0x1b060a140415020c160311030c0105120610033308010c12051e01080a150203010b0a0c06060503030d0f060906060f0513030807060f050c0414090406091707051203070503 74
    0xa42e020a0041c102d00c010003080c080d140c1721403448011039446e4104162a4010800f80324000d1056419081065110304201d840c82507040d040740926480380346c00c11041d040081a0a000c064a0b02010381c0e03a0b44003401c40300984100500001c00601a1121451102d19558011030050b407412910108594001c140c10140745d40441d0300240710f076201481d400010400d42000c14226030408008158002d00013000d0345c5046c010b0f941e20280707540403ca0b140c01da00c003d001d01c0074108014005003084501540203400014403602000c034021362100b01180c50764012540c4d0120345612148060418130280c81a100508108802409400e0824401911002031a8040d03c20000e0010312000390440229402010355481010103503250818100540034098250360142d0941c50000451448a1180c085078115501507800419801170841046800240207109844c91600e4185407400074041c50307441d0364031050b001c0c20719480d03a40c4e0f03081580c50f1100400c00010f0000c001c009001c040d42e0020705403a404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 309335161 1250 309333911 309333953
    0x715050f0309031803210f04030b040c030611030402010e09070201060e27030a02070608091609020702011e0e01050c0f07090c02070f05010c02060711030d120b0102030f0417031b060a1404 82
    0x201d80c040c81c0c0c1f451900c1540d0010348098440028032041040c0300c03102c6d10807a4050354060010300161040f0010324030007510000d01184139014031450604004030078607070002050000040a60782d50180403020740b812102c03145442039001905c180a61821415850700007030000450500c1c0000c10701941d2110306020b1481407049500028581c1402045041301c10305040e060050410f5481e401100a034000d031100b24085100741c082074a272000590b03901c1d005e8000d183d940c400c0d10700c43c500043d100e682c060b0010b46164029005654000401000810300811355881d0000c1c0800300d4060003400d2000f42c0c1c00502e481c03e04e07407008001c680e81c0722201581440c0c04a41c00ea903106000d1a0111a91403d550b043c0c2d0940602100a81082e420110303c215240e11100c090002e4580c132401241c8034802c01c1c01c40321003020b040c0014407003e540007a9000001c2d11440480c1e16008000c82400705140242d0f0807841c080d4881d03c03c0112010043c000c4400c21007104030036400505041d03880c80d54079401d40250f0000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 309336411 1250 309335161 309335167
    0x303010e060d140a0503030109230105010302030a2d1103091b0604090f060509060102012c0a0c0b040801060b03071b0503090d0803060a0b0c0715050f030903180321 72
    0x7800784007a81840f80c50004412a4028101481d00603102c1d0024482c0f0b8605614204480c0341c41c2c030000d51805509420003003001000c2e82082e0064000350001f804410003c5c1d955107014081455800031480d00c1c8040180420326001c150f110310040c0c0d0041d540100f000304003403050020f180e00001e2440e604071000c0c28440119803600000c00d0150180c0d9022605c41d40c2041e403000514181035010710107883c0e0540740ca210701c0d5100720041e400d80c2c4060001c401c5215031404445001035074013541e246038480750402d0f209680c0301525000400003c0d60001200b0400009042201e22801d1190000804424000d5415460141000b510600c09020072010424054080c042000814000c0321800070740200200e40700141c1d428207040342d41044a899019540e8004d002c90907030040740503035016501a00050076103e0404420304940c291a600400501c1000d1007100000c05155001d14031441c22400110f480345920040751282d40c121a00c002e000ba04400810050a507249400400682040c0d1b59155 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 309337661 1250 309336411 309336413
    0x9080a0809040b1f0503190501270c0c02040504111002060906060109060906051e04060c1b03210e040f090b060916030c0905030102070804062a030e0111060906060109080303010e060d 80
    0x7c4981c00c482d402e4071703514505800450003400010322000c01a0f140703c41c581480411074444412540b896095070301144040241d000145860381209610910603084206070020040c00b007030040d000d401050004d03070041c030104000c0050800c500d5038003c40034604004a2490310001500b10f201c1c07800380c1c45c1080b4000403041c0b5034090464901d4680c901144441d030307403140e03106e034000c0c0016030145048035042c80304140c0840000800c0c1681e01038035044000c90900480d9892a14448003048800000344001004900b0b84d0b651640308107071951004510104071550340e0b1401040100c4001d10403882904000c00b841850314048894040301e9055040000e2000121481038844130800d522403a0b2542c00016840e081102c81006003003110400c0c0c40305000c042400315880c09040d100e4124107001d0742d190102d032000c039100e540c6415050f0418180030130030000300300721301d42002004c0300c0e801c3c4958004024401c035540d001c4d40726002804614069070843d4106501800103007806065580b0403d042807600e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 309338911 1250 309337661 309337681
    0x5060d02100201090c03082a06150316060c12050711090a0b03070b0705060f040f0605060f060316020c12060a0e16090b0103060b0f0306040c09080a0809040b1f0503 72
    0x5500c1c5d000003001400c1d6540340340844c080e030321002e03500d85d20103180e40c601070005844448400c001202d060103032010f0356a000084081070090002d450341845604900b8810400c018244409050590b072209a07124060504500c0c03011464800f40801800b0007664001c651201c1100e400b4074001c03256841243c0310034010902801219122951500400c078001810070003180041110f03600c6403040d12607e80d91440042d035420802c45025091440c2881c1040000303810354816a0b001e0b5006003801c020700034000104800d50801c8403450804040564000d60841c0c0401c20520043e100f02c4294940307072503445200340c4a40002d0000703142d01c1c1d1a1464807411130001c0c0010402c0c0303c0404283e0094560700d5580c200501091040103011a00c3c0000108440d070440c41181c03040000803101a2030364842505100c01840b07206035041c100012102d01040d4000c05002660b0900e01a80100d070301d40540d8020001100d001d409075520609615000c400604824080600b001415062036516941c4004a038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 309340161 1250 309338911 309338921
    0x6011d0d03110f1203090c01030903120207241a100e0415080307030504030303050609040f140703062301050609090c0c0c03070e040b06030d02061b0c0a05071805060d02100201 77
    0xb00318091042e500315030881031030145201b400801c0859551080c1c5c640150210b40c10a0f0014002503e40d1828280c0b5003210380051418600c201000c4501203023200c1c4130b0031101583c80302c6417503254403200d4000c4002c00162880700884c204441680b0901c1828401400303910302c0b940c4c00da002d180c0321500700566003d0425040001d100000c1034a984a2241c60010441c1d4024042100444d1a00002c0b070b61a040999000e4800c55004000c0b40e82101c40352902c0c603c0e40e078488035010742132003000d0021002039118002c0000742009080440d00503262280803100d42c04d4141c114501a08040c045091641eaa22140a0f0480d018071842c81c0d44040c8514560f041ca660000c1003501031003040000140b800c0307602e20b1503103d58080c410a0496032100c804054440a9481401d030059210701c01107100340d404100c2c054484440c00141d680f07445800392159041440f450301c00d5800750014142080810094a02c5005800040d60204128036022002503c108443d0030040d024802003030202d102103001b5445 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 309341411 1250 309340161 309340183
    0x8070309020f060d0203060306160c0803090a1506081b0a0506030606040902071a070e03060621070321020a0f03050d020408010504050a021e0d0209090a150506011d0d0311 75
    0x303039564640c103130b240e01c0000e9031043d18014041e12440700021409543d4031104541d000403a034174580090a541c032003100540000c0d121168500406483c0c9000911007501d012069107044c50104406142003420740c28160440410406075024610f8280b40303503940c110000036504c00701e44040d200e40b15030b00418454090758001d00c001da03200007290001d02c100d8a0901d80700c100e60b064501041da82d00350301181c9000000c000140c00d60b100344041001c40c80c140790061403400c840c0f10b07070542218400c2c0146240010580c4282d4401e555001c0c0d01c0c0e2840b0320a40c1e58a5424a140002c0529089a030380711a0980c528440140c1000408555044a0046c0360100e600902190b002808030b0308240c1002c0c0d40350080100128801d850103180307105900203080ea1000c20f038500030601a500140383e02440506080101408858042d6000603400602d402400800d80c61b92140000340710b03d403100c0090508001400c00d050001f1100400102c26691615000c1d08039a0515184031131000c0d18074080e01e45220000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 309342661 1250 309341411 309341419
    0x1d0c0412030302190c081b010e010908070c050609010903030e06090a080d030c030b0a0e150603040f17040f0b0d270c0b040815070e0306130201080a0b0108070309020f 73
    0xc1640306065254000e4a440c41214107080c50000c541102691500313542c4000a0804100303001c0405540302004201c000c2180c140c00106100c0110703100682180d101610840b03046d18040f4854092281440400c1e01a040a035629458000690006465055180320041c104a8400a0600c0700c1c0c6802c0265a00501c000e00b50418458030360395990b465404090178440047d103008660701507144a4007940e015200041c2001d80c069040c0307030300340384c100400401c07030f030341c01c0b0303460010b00500380c036100003c43c0720300d001d040f25000803551468910f00080150034400b0800074180070601500c4528016482228880091166284d81401d0f030000640b0742c03031030400000c0304c00071102d800701030b00620500d41c03072441081c03042e10594071076440e8561800b0300d00403840c0c180d10841c41c04184c0740411803001d0300489281003921420200400180c0750040c11195285203045001105045503002100b00b0303017060b0010000d118030300d0f00e0000204044002030000041640355810b4209540321a40510104a4094 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 309343911 1250 309342661 309342689
    0x20609100c0f06020406021b1e03191a0a0c170403120f0203061c170717030103030c12050306010c02010e01051b010b0a080307050c01121409010e0f01061d0c04 70
    0x10801100a4026121b0385002d0f000d183c14500b0480c0d407100c4200d2203900010640c40440e480d94000312401406000c001d9018459074451420741c004884091b00c00742d108402c55210382a1441c400e1034038050240000380114103100180040070b0b00102c402c0300c1410718441003840360340c85080840f803400e0fa5903801083d9500e015041d22204030b468005601c14030007905d010700e589038040e01003c031111202801920300101240c411403014451001040086e020701d100310800544c1840059071580281d10450102e00a5840728082000540301d0751410900d80c11b0050071031410781d001a24402c0d1641d4002d0400c100f210410507a80e02807400e54600c0240130000d072510780150700300c403802489034440180c4a010715040002d442c0600104407075540d039004014181f640652001910351080c036800449030b0944038050450300c81460f0900e540304a082000100d41140b00e05a0302e0b05013499030b25004180c0e418000309105804008446130140d10800c80400c004d940c608482e50b0f9180141d0300041c004240c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 309345161 1250 309343911 309343913
    0xf1101050d05070c05160501170c040305030a030c0806011103030703050402120f0a0b09070312050903010914030304061a010504062d0f080f0112020103091b061d0607020609100c0f 79
    0x12804e9110741510402c1116903080500f6010740001c03045118290005031800c80022452070402c11080c1c1160782400c4660605850343e0b5441d0840d00106203807400250380780c1c024068240d20448a07500b240c0c0030308007040c40540024070551280300090450050603142c0e0003207002c5445050040072229411810340b00c10203c45d60215855068910b4103949100301d00000c02c400e010003148080c222540418030b480f840caa90740007501c60741c00c100349040e450356a80021031301240ca1036080301c100710110b0000c0c60b660724140c0b07080c0e41122040b2550600310200c0f0f508807115030360040c0440c0c09403022424041220300030300340d802600319281203030031091043e030525400045d0303000100d00c0f01c2e40f00a40c0341d6940540e544400c200940d8801d105004160031001c10010241d4041c0d444040064041c01600f040350007100c500072200d0f003040c1d001e90000f43c5040c44d0600035000b40107803c0c0101e0405c0b01d4041c640700c429000a8414040c20710300a10625190300428409401003420003050b6601c41c0900c00102c40c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 309346411 1250 309345161 309345167
    0x1e040b0a0e061617190306090c020c131e060303020a0b150a06050c03190e040c020303040c050910080712060506040516030e0c0901030f0606120f1101050d0507 70
    0x4016603020105410a203114140d190690a030307030000081603040b0345050f065460385002014650800e8601200405c0006000702010f03070005034400303e5440208086140c801204100d8003040300540454211070542e29840d903d003c1c0d51039400380078250116400165031000840d2140c0125120100c0d440d00900004054002c81c40c400c8540c0940c801c524940c1c3c0c0e05550034100d4013129500c0340c0c4940e913004144256400380010f08200c1514904613803d2209050504295140005046003c140300c2c01c3c2c00c0d1003525007400740c030701400228030242d411800c00d50740719094080e09000d46807040110f10b00207503c017250903100c44010a42202120045a5100c00c80911207810f00d4058950074146000503d19091500905004050706041c3c15a504c1c240c0e00128002d000701241113516001d45049071041c2d80d109d602d41800380d8050145586a80224a400d0089034032560180000c00444500030f00402c01507401940c0c215042003100040110000040b2480d101340c0f624400c9040c90302e81849525a4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 309347661 1250 309346411 309346417
    0x11040905040204150e0403080c0c0d020c1302040602060114030c10080403080112111306083a021903050f1b0c0f130207060612051501050a05151e040b 66
    0x2c001c0d94100089082c404040080e55040e028400440000d1008180068400c85210794803400406000e800d00700702a810b42c3c06c011000c001d084c01a88103451040e01c52070540407540492014060461409203019406522840140b0840b0000090101840d372645c0b07050001704c0407042c00901815241c0d94084002d045504291019000110580004a9402c101d900740b580104e4100030014402c02c031140401440040081c03801d8081a2510000158030208104406a80240e007411140c1894641103040c40059000302458002c40340703214490031543c010030311a035160941d0315601e001c00454101500d040c4030b688050300c0c916000081c2c610305040c45181505100380450b0903036a20386480f03c1082807140b2901c5825034040301d00050780c0013507446540104441071240b000403030817903662280f034910404035103000d0f80d080d0450229500d106580d0740c0c20502505085640102c1d40d41420041030508440034820034102c0d070002500a05100301105a000080e40000819621a1600d4031020039070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 309348911 1250 309347661 309347663
    0xc0c030a092c010306020a030902030d0f02010506101407051216030e01020f060109090f060c0c0b070c0506040201121d030405010e040908030a1122050108010e040c09020d1104090504 80
    0x103020185841d14802d1010030003580c007030380780b41c0d040856420750312105c00940c420003905003403580c0d0305c0703a8400580b03062180c0480e0310441c0d00d444801c905050406401e513040200394a201b106114032a69030b071038024000407148401031403200c0e140c503082e02c5c04030b241005541c1c41d001341d80004144150019004072010030078600c80c2d0740b40411148484016a640d0110340e0070401c1c4c0d80c020700014041054254050311641c0c1c000c2d90402400700950319400304640410300071a000078060300300340e01030010307800030070b60080d4284c50907180c0344c5030766101d05498840241000b0704022040e40004c9000d4610303001480a010750180c0e0309804007404c0c0844c1c2c0c1d258045c0c0314060104124144085251426104d169503a54005806924550b1400070b40070080156041140c139030202440707030061100140c404d0025104480415203c1c55007410005418914168403168103003006400300400070321105460300c215201000c000d80c07904980b0303d400025003858002007091a5010800142c610038a401042c012 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 309350161 1250 309348911 309348929
    0x60109050f060a030518071214032701030f050a0501060801050d03050703030906091a040203060a060e0a02090a1806030b01090516030c02190302070f0905100b21150f0108100e0c0c030a09 82
    0x100100180142d124058440c40000194150b40500bc03000700c8c000300b038a504581454005000c40802150204807903098441481280c1d0701d07001480b20541001c03100d4090101224400865181c0c1d0790010001c0c17050150003010552180b01c69410010381da0860a2020340c041c03400c42c526408495192044081200c0c02c2e8402d01c180008100e031400705104400c01d9966105c06010703240c0c0d071006950040e5124a400c140c00c00c852440c0014040800155407002c1220044041103603403550414405402060b040b04000603e000c003801900030310b103c0c0548503002a4140401c100300d0344071040e424603d0b00400d44869036001c0c4003000401d50b0116440054402a075413205400d52243d210341c0840d0f0040300c01950f01054240244807041601c00600040200e031390902c0d400c5001c4a0a4222406068402c00d02e181d00000b01140300d403602080e240030002d400e290515080c80e2040300301e44032090070300c50012101c903040081444100d010781219402003a51003103a0b030701c9041110040091140c0d119412031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 309351411 1250 309350161 309350183
    0x12010801020c06180a17130609080c06031603051b030109020d05010e07080609090c04181202150c07080408010e0a050f0604080d11090a0e060109050f060a0305180712 73
    0x70342e40707003522000c1c4e680744500c01050211201d41d43c1400580002c044180404014000d402003510305465090160400d83d07905000c4500e402222803900040380c0f17400c0c0c0303c0d200c14010091a2201c40c0346000c80c0005501c1c010940c2c0d19440a204032282c840d10344120704010000001c181090548c00038000301c206031030304108581c0d80e00000460340c501031303641000040d48040403a503945020f81499800c6600882561850b401c45400031b4120b83c51300d01040c5c40400e2000040c810302c4100204401400700c1c40c0068807044543c149500c00c0c08000901c420303402d050104410090013440ba09441c06442090001c000119205400f10f9866201c00c808451500c2806d110344118140803e03118061984207540300c0c1825120110748000c0d0107134040c00d416511080c04418000e68038000158003c000e14900d030f15503170514800052541c14603070000750042d00780d51a03159081d12581c044582001e00b9280000350f40e250b803884811007044be0740140d48907200c0e900c40462140c00c0069404d070400d12032120145 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 309352517 1106 309351411 309351421
    0x5041403302101051005090109061b0602120a060b0a080609180d18090908040902090102190b06090609061008040c1511010f090503041a12010801020c06 67
    0x20390b01c0d40080100202e0802c1c00300001c4211092608030f180c540518000380c1911510300c2008200044403000314048115070f1592040654040000d660703550f0106090070002d00c1c20703141070450510701500055550b024134116051300e032071030f02c071a880b6a5800c030400214001c02812000726615012554039902801d12000d00c1100c1c454942c603c103840c0b2103400b48403400c1d498010341c440500d003c4980300852414070075242120854003015171364000c0440102e00740209000949040043c81c0c0814003041062000e00e032240c0e04c199007507821640c1d20320401a4060302662035507084000198844802c5204480841c3e2180c0030355028100156103134201804001d010300c804000405030304103151801000c1c05101e503818914182031015185688a0540703e2040348282080c0c110724100501242e00c0d840141d810001698000c4070156070366070044c6010307521468082a0310300840740018 = true := by decide +kernel

theorem cover : BRFrame.Cov 309172661 309352517 := by
  have h0 := BRFrame.cov_init 309172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 309172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 309172661 ≤ n) (h2 : n < 309352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
