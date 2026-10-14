-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1504
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:17:39.152549+00:00
-- url     : https://prove2.me/submissions/7cfe102b-30fa-4ba2-8da8-5693dd6bdb36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 270323741 ≤ n < 270503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 270324991 1250 270323741 270323747
    0x5190305040209011e05060a0c05030c0d0809120405040b1206130b131703060d1a040c1406072d0b01030b060904020904030509180a021908270309090f16 67
    0x1800760312186280c0b25500341051b0602c6151380c0050500410301c011a907a00d0b00280c0c0820042240c00311020140c240722280c0c5401605000c0d028010140a80020400325000c1240744140e5049600883c1d0100390743d1910404075030180754802c000341c60fa002d01c07020071420409440d56200f1040c85001e07005840e81d901510310000d05c1200b0b0f001000034a4010b01e90640b240e03054055038010340300030071213541300c0c6182d511181110030205180700e01c00b14240402061003000c0d0209802441e5009000100e41040700028615110b01c0d0001813501441c2840700c0d001c0710109295001403455060140508642414068603410b400d10044940d880b00b50002021400c050524500803540640301c220940c5950750251581c1d04120201030f00007108206500c100d41c04020418001d14040000690b00c9043c0001885440c007501e449109100c0080180041c030612039040300d068614902d854190544440c0d80141103100390b44045510900c034070700344520050b21500320f0f4012203100c41e81c007082d8442c911042e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 270326241 1250 270324991 270325019
    0xc090609080d030b1f020615091003081605010213050316050303041a1603030507030509011a01030e0309360601090306020c0c03060703050a060e01050a0603020a0519030504020901 79
    0x144650700081001d2031218080e03000031480c801300500b0907162209010726619000451000f0200680c071a0041c04801e82c0f81005000349010242c0d2408580c1c039040c5804840c010300d9100040c04c9039000900b071058651802512290554440002d541d01c000c201054048510180a00c07032003801810882035800154000d4101203c40150146040c1b52600301d4420b059030300d2148140215404102403e5044031480041620b54465100082c0d281030268005084690041c007440481c3c1c900f1304035000380b0b1190210302221000910b408514030400300e40c000d086016504c90745420901c01c4000c0c0c03038030b070803401001c03001803001200040c41d4018008034410300e40c0c019240280400d44100c81440841d105030000d1003003503481412181c2109510380440e18120045a103a40043d41c0d0f40305000110344c0d02d0082c8401400348c80c5d42070f845541407100080680601e031044000703250340003031082c1506000c0c1301079aa100200e0b02d0540460341d03808402034013408080f10104d00c2070b85080008101ca9524400c6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 270327491 1250 270326241 270326249
    0x7150b0d0c05270105040e030403080a08220209060f0a0504050108030a02060c040621231f0305030d051e0709030501150b070201080703020904110d0e0c030327060a030c090609 77
    0x1600c100c44e40b8110901c0700030071142141d601c080c0820000800803130b640e00020081c650090351804050716141110b008071440000c1c080600e000304201c203802580c2ca0321071294100300100c90b408082d0070401e0006030303016502e91103581c01508001c00003c000901002418040080707400381c44036680d03040c10002c5c03144614014030010940104841904200710311441c0c444401414001070b5070405004903613400c01282103074120402d41c000802211520303c101c000740105040c1c407084541070071566015228000d4604011256a03104001803c2c1d1074100448505008500700b040c205041005000b489610103000503113482d804c2070f01c031151400c039a50111048881da42c50041c148803207680111004207000d0103010825400b4422030ba007036501c62040d2071140380c00d0380c40181d40340f00703000d0f50606840250030f110085400441d0f4400c00da032000b1084485d00300810754200c1200c01203000020311600703200c0ca8690056004200500d041ea05940302c5449150161a962082940d03030900315072440071805 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 270328741 1250 270327491 270327559
    0x140c1201060509060d1107060b1e0d0204060f080a0c050117040201050310090e07050112090f0b040f1203091e0503190201020f0703050a090e06030307150b0d0c05 71
    0x410540c0d02c114090808144010103252411290b00c03049802d880301c18a200090b180c00082080400c5081d1080c2d000d403103802e4490201034142d45014011050030450100d01500e14030b05403000315611580118090101c8503004064280c466400300e40d1360800141c200c60102030400040707415030150f010501e0311201c0b044100159a202c2d40116161741000c1d010850102c0d1021011400c03526074064070100160250041180e207142c03100040c00700460219940200d4540f4082c88007240b003000d407190b0a582c1242d02c0003400c1e203a92410350381d0718604007030107860106402490198241d0540048000a0250322031514460400711a8104150043e4008040750300412501520403a80304c0c1910301119076000060a159445401280302c1d401210b04800007280040e00481d40c503001044080034000b104035041040c50000c000c01d50381c0c82040e1014110081c02840032081c0c043c4c41d004001c0303054001e0140d0300c2d40b910742d203040c2050940c41d00940c1e200750000255a40a803003001000780c82c0500e052 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 270329991 1250 270328741 270328777
    0x80c1c0207050f060c0a0f080c0915071b0f080114061311040914400f050601031e03020303011a0f0403030e010806010f0507110111010f140c 62
    0x4050000a51010800310b0307041c014031802e905081018006030344610700303441d1400e41c2c03101d00800040010a04044040030b0043c040b05006a0702c65a0301500c1000c5030503a48450041400e400d45266802031701d80050554281212401582020350010002c696028002c108084d03192402c1500b0781d8103000c2c400022102c0c8200013241490300000c91248000705c0400000c076582500d04004e25540141c12140166441e07641ca030003000d0004406503841158085084013180c600d5064040e0b01c0264410210560403402034000051100e01c080000d00b0789c00407038011411480c1c81c0981d2917440034442901c80301c0324134101e41d560f604040d580071801c0368168059451a0b0038200c0307199091610b1807000c85400400d10a040c01c04141c070f00180099800ba803101c01d080c041c0c101c00141800001401c80707040020441c072895160307401105889805a00c8100d0b82c200f10f1801c0012580d030100612800003540c241060020040306907809a081042d4409040b2502c1e51600aa541c941c494064403550141c0c0407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 270331241 1250 270329991 270330037
    0xf0108060915040b061209070906030f03080709090218030111030105010e06280c060e0c0a090518070b071b0b0a0c0f0204060e070e090c030a0f0b0315010501080c 71
    0x802e007007141080c01400041d003900d408010400d550403c1e060010001d52010911014030350811100c0003c216820040c41410b0456848d001505030582c0020184422003000c207210501032600e01d4083d2420030006c644428020300722070704c44060303000c2d41c0e0300952074180384150380104401164103841041e119084040486014442c103984501400e0303000e001c0e1464561440e447c510454000e070105942e800e4201c0c01181020710868801516074000d590154001d007000b51926a40c501c103d03401190005069500c40901412403960702c005035001d80101680400c0700d24880c4064800c5600803007009010312000081c5803216180f41c002d0322689030003409411032640c400d000c4003040741d104a0310701010300e8042e4080360640c1c2a5400800001300a18104900b403580070510b0f2030fa86a08544607101820019501c104e02e22001c2c0c03841c8411919240e01211303404040d088461000d201904503100c0c1070f0105503c1e16101000c1c01600d00081c1c40700003180080452400b55100c95403418082840c031214 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 270332491 1250 270331241 270331261
    0x110f0c0f01020309151b03160b0604090b0a06081002090d0f0f080d0c08091515010513090c0e01050c0601090f0b1309051014181e0c0f01080609 63
    0x11101541c1144000c0000c0f14070358560050820700014400a081d031502e0080070b41c5a503040041601302c10560080c04164042d6200e008001b042c2904901e29035003985801000c10302601480501424004202051000512241e80480126581c00090b07403828140b2900c24030580c030805034042d510a003120005404500f014203500f11540c41251603000101c85652000c0d40c0e50002020343c1c450a40e240d5182040907001100560b020002030080c0010000da8a5042e40041000c0e10403420f120310b40e0080c80050340504c04440c6d10011102041c403030320750380c3c050050242c406041d0301400a01182040700403940107200ba5541c1c0c2c6010300c040e2640c0e03030030b02c0c01040c000c11400d02c44452581e103d808035112602c499039000000d0041c1d0710003140100b01350510074900414007000691661826017401400c0019002c1281c00680d602060b41d1980b440b40d51305460480d00c425010445030015a140440d14000544014030702c10644407050030803000001540e07445011500d46402c5400e10f0005410294 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 270333741 1250 270332491 270332509
    0x3150a0608070b0d050f0105090a0b030708150a060b0309030a0e0d12051314031f020d020a0f0909231b16060f050c07021002010204080a0f03110f0c 65
    0x126428009411652428028580000c2e903024040d190700000d28146805482d000720b59001030f1502021001e54508004940b034014014000303803200355206036824295406004150043c070b020300071688140c05e400642d83e941d80054030440c08540ca060000a010354484054038840d405050142d802c0ac2c592074000d072400b07091207a84950202c2c5a00f29040002c407000b407164418052640c03525140c810191551290035000c1e0044a2120103501d0542041e941c001000c910340c00711490318890100301080e44a01078081c041e18141a14000305001d0040356024407102e204440350741d00c4e20300d031075541c15094003100c0d10410310300100c81c41201081400601209010380004150080c04d076000b800b000d024586401132060001094425045041806002d0160000d40d140401d010401803c00d100c8410581c42140c000038050b403601e450f50400c1c68001c3d8140c4000300341d403005a0b03103009450b00d0004420061240d0880c0480e0b40b5502c0c24151180c0012507440e4042000c00800403110000300f0400035038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 270334991 1250 270333741 270333751
    0x302060720030301030b0f06011d0f030a0f06050405100b03070e041a01060207080f070e010e100308070501021c230a0e01020c030a0906110316080708071b0f050315 72
    0x1c0c00840010480581003005600035070190140502500700005c06041d0742c0b40251607103040003096420945442071043c852151000c0403101d000a407a181c1d030100381403d82020300508010310000260007030240d540c0221307100750303c600140c40c2c910103020750030400c503a014140150580d129482c2030003e011600c080c20b4110380108c000103101141389004064958098000500507044100100861181044512031103025030340981300090500d541c0352611401482681c441a4260002c038000c45060b4042d00c01642c2c0003006180d4030f00320360819a011b0360003058014440038502100244562480c42800e6046e46433448403a0801c284843c040d40076030f005408428030381d43d202c02494094400348001c1050030707115800b0355201c1c510340a0180110b205940454180031519040d2648110f01004442084e1414006030300703caa420b040c00d014a004460000740010070008040040c041d08050b940901200f5510801a103512420340d2605d0222030b10440f40c165000d81e80146d4440c01c10f00019500c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 270336241 1250 270334991 270335027
    0x2301021c0c060216060c0306061e140306040204080f1c0e0d14030c070306271707050106211502130501033306030f1a12070306020d0f050604060303020607 68
    0x40c5904e03482d030408681130034440501103680c6030f804200c4140c004030304801e0000148003140382c051038a074003d0300a440020660780d40341000000182241d8440e41654050040d80c001c9600d80040b288025070340301d034003041d4103a4050b149008205e41c14860640c40f404220094041c0c46240410360310540d250b030400866160a000038841248142d0342008007100450117480080380d41c00c8248000760440c105050b250202900381070264020410758503064180c0c903807540846a4580982c2000c50041c052900408032402001042d805524408403041c89203600641d005000082c5405025040b441405244038924154945c00c001d59800f0354010302f5030000301c5014002340004403492810800c606032019030416840c20081c01482d42c180728902d5000c600e40003c1100d2101030030248205010814081d00c01c0781070802c00b828028007030006000855001209549405410b0131041c05402ea1050006585e480d100000d001450140500000c5036016000341403191100f42c8101d6412410304101c02030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 270337491 1250 270336241 270336277
    0x31e040507053006090a33020d0b0301091101030209011806020a050613020a14041409030910082703070c090b010905190608102301021c0c0602 63
    0x8581c850342100a02804246564051071040f1410340b6111120303048507850315400300c8200801040001200c1d0b8007180c0000950728908143e11400321002c48000711200210310380f80051205802c184c014140d000c0c0b19843c14048001c07403000349400c0303c84111010700b0090300b0b600f2200081d40691700034450030302c1c1854005c000080c0c1d041c5194000300c255009000507840405003c01303000003030042640180802070302d000804183e80004045000e940141003017400c100a003068a40d0302c950203d80c60780400340303001890340b90030a201074070703030f000000814002c000090101d00340c28852040d03035200c2e42c020221303002040d01c4c108914a0302c86012030245464441013010b4408248403250740310003000400400708261101b0700005103000c9550340614019000c0070f03040c1c1c840080b01003041d03040d030312140b41000059995003882005100d03540c0c004074030303140024130000f103e025442200d00008002c1c1c0854800403070720060514030482030281400016403103036036040080c41540080400100004d58401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 270338741 1250 270337491 270337499
    0x3020a03050f01050606070b06040c1704050d02160f0e04030201090b041b1508061003181a150108040f1a070e04140c1606060b0c0f12031e040507 64
    0x205058680e003040c0c401c0c2e40000e0402c0ca00e04024042e840e440038058560318206161559455221540504000c0c405d1f03407104036002c2d9031403041c0034801c0c4400b03011841c2065418541406500c500a031940c3c0c40c010300880c3c3c083e09142400701c41520884d01556580120f4524218055094200160003101195210901e00012580386100d0a00640c0144151000308810700c90b960080f07122507120980ca0b441090361101d250344c1004010758042d8041d216980142080f0f13000b14020410151040408022001a00c00344503000c500050754501c2c810901000384c60350740d0b401002c00b101d003044600040301400041c000640303d41c16401c120303104103054a15001301c070900d038141c0201100c89000042420410700308a203072138040c850b0540b261911010590400380c6601200b4400e545a950401154007402d0041115592142c0700a00c0c100800c1c51b11002803c80450302c40341d00c00d540744041e1055498400c16004003000b240c4c0101209148014004094031003d214030800410544040c00b502d0fa0001d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 270339991 1250 270338741 270338749
    0x609050f0304061e180501030911040f2403170d02040b0a0c0515090601090905030d050c22060804020108070509040c090603060f0f050d02061606050a052d100302 71
    0x60080e5899410042401d40504c0300d000319800e004034104031494107855000c0c844561110306581007881c0c045813030843d42c2008550b141002c9502034010380b0b0905041840c841d942e100300754241c1c02282d0395440401c820342c1e000c401740090201810110a0f15021070580389100c000b0b040104d100d02d805800e182e40c1d40c101880c290001c1d8001c1e0041a441054a000c0040034001e610800070141811710b091f003400c400c2c841d640c03541400b41d0700e02a41d440f001d1005202c0e08006903241d040783c00d1010701c51850070400c0841c841e00002c104141071142c0030036140104035002002429500d5070f5072aa426550342d40c0045800d2403014081c0c0e018814200002640c2c0c0d201c50088042030a01038030390311481c0e440c2c903030001d08071922903100050091450131b0a100000c0054014012500112011040310180d8000214a4801d8819903802c44043c805400704004007608814841c09034a2001c0101d40d079001c40e03098a4620400c2c1c465260080305c0360240c0910760b040e0810390088008070700305400540307903404a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 270341241 1250 270339991 270339997
    0x21206040b220302061b09030109110123091903020415170d050708070201030e03040e041101031a2b0302010e0606040207080a03020a0507020402040b0901080603190609050f03 77
    0x35207204010300304001c5102403011110400240241e42c20b124864103880017500c0300d402030039442d030080204001c1001c1d8071180b0107407040620014020040c0600510b840e510b000854080300c0d02050400c404c4a03010082c80104003c1c0505c2100520700e806404010480364984c0038002840909950343c001c005600e5501c1109456520f441d8030059050501050411408000116400340e900015801c0103da50200c20f0700c01c955403254119807200502d00c0141c0107400c0c601a0304505200c003241c0002c00c0e080c603240c0c0174001d0380100c0c048500c00c2105070044040e10000340302d10f20300704042039424000703042ca040b40c40da00d00140c01040b02c1d07075600c4e0300d0001018a0f880e0300980060391a000c01c02e8500c0720500400b5081003040328110300d0a04e05a8880b2407501690285c0c0080c1755011540140c200d014400300c1d040b1036801032003155a00e03287d400c64070719900120308041c00685100c2c0080c00500340003840402c481d80c0300c3c0482c203198051b40d44e50700c0a4841a6003c89450168103080c0341d03109820400307 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 270342491 1250 270341241 270341243
    0x9050a030f050712030507140c07030305070503041d1f061d03010f18020f0405100501050307110601061e090308090d15020d060e0c040e07120b0d12090902030108060c0702120604 78
    0x1010860b0708047c0001803202d6805100c0e0308011008011096500c040007501c50103d0303a01d410700703c0e1140c0b0782d41422825400f8aa120740c00440405c503504565600384440c0520440c04c25440c0d20403109042070034101544c0a0150394042160fa181c00308040d500107541c0c9121100040010400c898540c000000f07132000300d00350f46c008040b040742010451600034020350401c1c0302a5000c0100349000c5481000904051180505100002000c580d1941c4514540c001145007941100d1503542d4916000341803860b060004078414503d014038100f1180b0968807401203c0d009030445050080704402c1004800103150222a020762a550341d162422803800540300600c0c1d00e10001a0840c605485a101070000030b050101c140b008001c140008004200c0c1d80c0e4004106181560214001c12000002030410410442d84905c0d000c154000300701c0140c86800d10800c1c903070344000c640d56544038010140e000a02401d20309810210000d80390414000203032602c14001004c0f44181090410f10608210090b68 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 270343741 1250 270342491 270342497
    0x20f03100806250c241d060606161e1203111303080a0210050c1b0f120a090b1303050f07032f19091404020f01030c11100501080c0409050a030f050712 66
    0x246081001e900c001103258180300340d001400f60f40c540307000001c2040c4501c1341c0902845030b620414000740400007080740302080356004950690a0036013421000cc55008880301c0009091200c0000c5003240e101c16100c4022603000000301184c250b507561551a041400c4490451080300187c01090089000c1c440c018050301030703d9691041581d0010a241ca00c404c04552107510101851401041c005068500c203e83d01007550344500c8024021542c80c50580e0101c2c045250120309402e0010f41005018100e9118400f12109550304050322038540005100240c101c00a60b03a524502c901260003030300015410f400e4282e0140c000f0000105c0e44620040050714030400c02405100b00d220034800c3d6510154401818042454580e000072551404650018100b50301d444a8000c414010403008403030010700400d1fa803d80d03481c45040001000f00340304003a0b013803040c1c1407008110b09081c400d0400700d6810101038041020207072020f035100d0300040020810840200100c10106d04030481042c102d000b50784e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 270344991 1250 270343741 270343751
    0xd03030e01020d1a09070206010e13020a0602030d06060f020c09040c0b040b0a02060606270f0301230c04030803010618030c0e070215010f060c020301020f03100806250c24 75
    0x1080c4c440c5421021034082c002c00030070782881004d98000070340d2411250b03803001d012032075994168400800d40c42400002c1d00501c600602040c41d43e00880502600748400004000c200da0301c00080313940003030520f81140507030445140252582010140f90307900c40d0082d1034400102da40d622580c00284d00646c81042640402310352802200d170705000070b94110341c0441d4501d08050b40d80c42c0c002a503410034a07152582240c403d50300d42060b21007038030101e43c03808001e008001e903511003c103c031040703014580e440c0c100d0384003540000c0040041009440503650050611411a0708081d070548030218600010380c3d0301070f01d5220000c006043c054a0102501c0104103074001820012000f80c0b410704000203034210034446000501c81120006914000c4804520b0706440541e91400464020303c550383c40c0040744e41000041241440314040e01d1022505280102c84c100d50303070808407011071311700d040c001d0b4001c006100c501d0070b20b544910311340d585150013a04551301241e140c035091500074904140e0448455103030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 270346241 1250 270344991 270345011
    0x7020d0f0b070f02150a0b010e19150305090a02120a0f120807052b060f0905061002150115090824060105120c07080f030903031906140d03030e01020d 66
    0x88080400030759034074001081030040a40c5440703179000008040034103040e59940200380c180c1c400c40122000d0303040a403a00c04840ca6006401241a886005040c60003401041082d03104d803003841240d102e400607401401003101035500300000c900025201c003041d031107035803940008152000c0828aa441c401d12010f0030743d242c0d405020f817020300000c0000062003414004040c60180c541c450801806c1441d1038100007030f40c05d1407220014003254000101480403040c02140541ca9648254062072003110b144064840c18030003280e5883c40340101400301c080c4c200042000c1d03e412031100c4c1001c48541041100d064584140d18580454409807100742c100f007401c6005130012062142c3d402001c20300c0d020745800300001107041980b40151a054254038009030107418400d17072409850f002404101c00a41d01c2c2402c005a82c0d42e50004c0d0380a81c58550b1019075015502c05510406088451321076030544103080880810143d120390150641c289501d842d050003c100f42032000341880034074504006940340320 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 270347491 1250 270346241 270346247
    0x6260411091501120504080a030903140c1501300203010204171011031b031801060f0e01060309020f060a12020423060a0206010e09030906160b060306010b0a030207020d0f0b07 77
    0x42d0700040549140341c171061001041d4804200ca003401c0740340c2000f0510b105a49011101443c91064290240001052020034000c001c64004441114104100c00300d90300c95880780045100554401c0c41c0075400c50000301c4181e41301c03482e0344d0282d00003400142016501c406c1d862800340010403580c2140c10103001c0758800c129074400c092812000d42031241c118600300c9098500703108241039200c0455008800a05941d40101e03007441c500300b000000303200a50b541c886490318500701c2e015a0450060040010484a01c240b0070071340400d40080000b03404814040500040d0340c08a482101000040d1451400402c07030707800100010104c070040e0290442141080407030110032203052920032902004800d01c03c550005201e41559000c0300b1106468449140080c5103126404121340c0001c0301181160b0109540c000c49002180203184286550740c44204068488500f40600c040340032041c003c4009c060302c03030b50140030340701d01c02707050084002195112010070058110040f924001c000c0200705610354 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 270348741 1250 270347491 270347507
    0xb1306051305040b2a0d021c090503250b18010c0c02090619030f0506060f03011e11090307030501090201030c05070b130602120f04060606260411091501 67
    0x42559410801400c2130b5550031006200078100d40003d1105108205025a9081d890090850310445c1966510f0341082e2000194020b0040b40010000d66650350811024500464003180c0c0d11401075450480b103041f008800024190300302031000080c003007641c00034204500c01800348080210714080178500d4800d142c01c0d40d610083c00c108005000e1504001a1165415960048000c890310690600c200000841000e5a40d002030808485661042d0501101040701409580150b07903078001001218240b42c02d0f5007043d030250030310141b2076003090b151480590000e1080760100768103926040d00440020314104176a08151404d0359508040c10456030035105e15450104141081400c1a040c0e4030b6038a24102c000300078042d566008140ca0082002940c1143c01000810546560038140341070301120f0001c049a040783e00c280b40800c0410018012031400b015010003803d0480905500c0001da441d580d400f4108588082d030ba081200e030b1030350b283c0110510071604420b01c071022a103451b000502c101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 270349991 1250 270348741 270348769
    0x30f0e040f0f0506040c090504020a022509151805060a0f06090815061c050307020406030f050606030f071403030d061e0e060609010e01023f0a050703120b130605 71
    0x1c1e1038007610b60b041b950052243c00841304111001a00c0d03800003501a1306200018000c10343c00c5212121f0a9244030854211606450140380c0401540501000c00702c04059a80100c00d4180e101000745034448405801181e4042c002400790940195102c83d0210000b240e13401400209a002e0006d00041508021611140c680d54150404504010010030350416041080d015101c07103012215052000c108100c8150643c041d008020b2a43e80f420902c5408014040490f510300035800881d109150006030301c040442404088c00c11580380c20f8003402b10241e20313a8072079058001413154140ba0b2095110b0f150042c0300705050315031000000080f021255425400486000561905100f002c1d161030040d1250709001b030811000400102c00181d2904402d0f0864019400030300c04034600400220080002c4500c1002512010381c3c010018030b02c0d1805559071400000d0011300200000c640300d00b8500350010b02c00318001516488010200d074006920a019000320707910b50008020034146039501c00000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 270351241 1250 270349991 270349999
    0x50403030305060a03030c02090901090206030a0e0606040e07060f0e030a081210180f090c080706030f0207050c100c08030c03010609050d0c051905120a0212070e04030f0e040f0f0506 80
    0x44c41c110395019007200c0c01502c02a0083d020500000e070444003d5002060322a00100415100d1511009000151030f10004551035405510085441d50038180225800480c010015001444c00e000b0112240c031400c2c54900100010f000741080c0d45c0e1001d1207181105406030f000541d55507400f0303001d01200300004c0c1c40c4e511180d5000b042001494031005112a2408841402091a040f0344104030007a111011000c0d002d440350300c40021329458001561400c4402d1a10103021103140908032008a0181510180054000d01103e20f81d500d0b0440380540c010802e03051201c981e03540d544548240342c0040724003000d2070000000502ca51500545100c00801c81240d1403486903806a0366191404510311810340138608140b109510b40501714044805004060440140550001045541c4194a074400da010382e014000c1c0103c03030407000c0380100595107041500f9005484036a001c23207140d440000c11800700300445610004c41d03038a90046840e804240c003000b04e421140c032814141100d00142080b845 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 270352491 1250 270351241 270351259
    0x108061303170a0615211103040210020a08030403030b090109060b1602120102180f060406080f15040501030b0a2f07080f1c0501090b13090501060503030a05040303030506 75
    0x7a5201041200281400d141038040392201d9030540c015101e0b942100c2c0310032080c040005102da40c04400004414a1501220111445800d000080b6600384549030103d40b4200002130160400c0220300102403202d01c100c0e4400d10980e20307a001d45800c103980480000752101c9443c42d0514003124941d001d4003041004000380b51600158503818420381c0ca0111420110b08010030555a07003105804041455038025580e5a02171120b188001c9424002a88103280040e00d0a140f400c04105039000d850b026103440107181c58004114010700340090041c0d5068017805140203254840d4002e5500851080d04645107605100301400140c0b40e000184002007408144010b810f4802080c0c03a00115001d0032480340e0701c04050410607560f21135030035104a00f0000003044283c00402d03c0481d0030070042900c0400c2541d880741140000e0b2041c901a0550180100039006003030340b1542c6c42250214426800016800d90300d00c0403c0c210340208074804003107030022030200f05058041c05aa94040300482e040341e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 270353741 1250 270352491 270352493
    0x305060105090f040b09100e030d05152809060b03150d05070b070804031e0201020f0f0a03141c02030a0c020a02150a110f010204030201120c1202090a0b1201080613 72
    0x61103c80041018100200200c007240f52040d0512046880007c2010240b000d010840519503803517014054007850030707141a0000e898800d5845141d200385070010080c1c04005010f0070b1030014914007602c200e80741254002c000170b03c1d941c07910407400100f07801c03900380b510703132074840140c08105651200346401140002070210014401040a2003035031014030000b92106407900f488580340c007490f00000c20000c40881b2140b000d8038400c407070160a5100741c0c2180d00ba0740652269030b858915655540110b54469101c1c0c0c0d00082c0180e1380d4110000b4403214250800506200083c2501c2b540c040f1354801550000601250080034007441400745040d0008000300e20030b907404520729001c5007500c83c64006c0c01003a2515080d1098460300081f00310242202c819200303410030a4002d60051004a0200d1518004c40c1000d0205010346d40f8242c2003903d84403600f0300c0a840e2800a54089448682e200c110004080b0740d0b40d9542c005410b4814074801c01a409604040000303242c54005000c00351800038801c8034030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 270354991 1250 270353741 270353761
    0x6150302070b19090b010e0108070803041401030b04020c0114011712040308090103061203111c05031504020c030d05040c0e06030607050903010908071209060305072025030506010509 80
    0x580085500056003040040442500001e180304c0c10000c040074050000003030360304401c0604a06a0303554509640403161b80700105980ca10844c0714903400d101c001c5011804540c0207074008603894401070009031404000344040e42c01c461201242d4141d030303a407501c0144840c21b08890450301d0803505100400b80090b4006514503903029a200041076030000142400040e4482d401c03200c010b110100202000c000c0e14980a44245100340b141c1e80e0610a01010880440000e0001c080c2c541d41611402e18541307030385160707c0101c805c2c025200e80154082200381401001040104840000c0c8000000e60307051030700d044440102d40b030340507107121074041c800c0c0006070f9404141d164101d01c032814426594480200401c0c00741c0407014020700b0354400440d0382c0b014030291901020f4520307125075071034508584500381542150011785807400029001c694240810340010720045c844411113040f220158042100424520071400014018041180b0100200f000130050b01d80501400c03245c002d030030b00c2c1900850b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 270356241 1250 270354991 270355013
    0x6110307091a070f080d05010f03110f0a0b0928060306090b060306090417070b1f06052a0708030405030d02031c0504081b07260a060b1c05010615030207 67
    0x19010044c4105000d00f0820760404540030300c000300388140f185695403422282d0071f500c10321054031034120303880301e0460030703c0c1c800c0c150345c20008002c00750240c003410600c41007940d812684a50742c20010303a4103113400742c944076a11f100094240001c00c0130998101000141a583c01c2d40c002c0210030304207030360a4900c0c4d403414240c0b03a102e01d003030b21002207503522070400c0d9001d100b030a41e814801490010b0100e081c440c00c500c2191203a462002d500010440e2000f14070401451440703903000142081c000c03100c100d00181ca5010300b95180c0038845000c50b00000041d030a0000703903880641c4c40d80c0000780c104410300f01070050f8100300e50350380051411b18240c0d0742e00207010b90307000220041203659800007030100a00c860554041e4070b00d00c5804030010200d0442180d03526014040d5101009503c54407100e03042c500794070780221018200240000340003559500000c0c06a005505501810b001680384c110012040c0580c4100d00420000c41c802d171416036030302c4040c0c1d12a0050b00070103004124103800f2a90100e54 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 270357491 1250 270356241 270356243
    0x91c0b100506040f090e030d02040e070e0603060102100506010e03190303061d0a0c050408100605120a15020a0e0306040f12050a020c0d020f061b0d0e09010905090a06110307091a07 79
    0x100b00b5074006c0007024154410a83c50007030707103407010034049205140e801160340303d29003a40321a40d4080c6480100201400b0484136039005900c900e4000400c0401c542000b9082203040c101310703070303143d080c20b000030300b45217026501800b031800403030b03020040c90b502d8001c90b40104602203075012020800758100140f100003c05d40244241c82d0050940ca051281080f41c0003451200280d900482074240750501505445c490103119101c84919900f00000200e0103001d6542d000302c181c1000040d40c1d05400194010003443e0061200150300c0b0002d50310300b40701041c1300d188652052031075000700c2d15159444030701c1707050090104201480740511b01d6030001008004121b0461706041125098030000e05840d08400480d9080440480c02a00a075100319101c410700b003503403040e2607001d20380440c00c80302c448e00010b040354041045001004010b240b503014940000b404426603110b15102e899000c2521a804174158400600104104000390702c001201c0c00741024a2a01c03807910908080c0000ca4007034140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 270358741 1250 270357491 270357509
    0x60d03110f0c150a0c11030a08030f0a0b01050a09091e140702010c020a030503070c06060b1305120303060a0b0c0c041802030618030f0906041203170a020309070308091c0b100506040f 80
    0x3002c807200e550204640240da41d8071030b2015038ac82c60101841c007441d560550ba004001c9050017085425580584291124200c030360f564500b5142ca864402800b8250180e07138510b183c03088c900b40703000809030707401072001c4c035031056560006c0c0341400701009007110380c401039040841d00030b820340400280e03001d0100c0341c1080d9245048480a10316041503001808654002075110b03030001082c180c50741e10f25039080211581100d1085d00b0072040c00040e80c030703444202d821581c0a400c0c42414441c072074101c8042d04a650040080701c0c403000603d07001c2401c58034503408403405100880c1d944411803904002d855031150149080d09981000b081c0303043d07503c3c05072010041d000540816014550340f2040281c07030040c1290700030101313a40200d050141c40c00340341001d614600d8000702d001900134041802100c0c0101c02c030800801d28146140c455040340d4001e050300300d030301805c0680c002c68008080942098001d0140b075080506d420440c0c1c0301c241e001c00d950710050003000c0500c81044a400480b03280c80031500000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 270359991 1250 270358741 270358763
    0xf030402090916080708070609080325050a0b0f0601050705100f090b0a05100b0711060a030f0f0e100b09040605280b03010609060e060d03110f0c150a0c 67
    0x300030300d82042d00030700e140e15548080d00f000046000700060703580c08079600c2c0702c2031b10780e82c684034071040b0703068149405500c2d2607a008114005010065106140c0402d003d0084600001c403aa40d81d14101221140d01381e420102d80d44c14010080f0022900a42040003420003615213180e9030764990300c49245603003014805070754002030b219070025500140c020544c8600035806070f00d8502c07040001024161404c040c0305985c8a00802c0061244040b154066082004c494100041100700702040d4030890025041603100d0400002c44c0460b40a05452b958005c140400c04442c4507111600d002c0940305503284e003038180050404a6204c40c20401e03007058110401003026a80d10200c0d070040c030104000e11001418400070392001d00e1441d8085803000230200d00034881a659100c40c1c509490032030007036010a10504002c00d00a280102082400368400d017883d08400001ca0480d40c00c04803d051403100700e0304490948189460000903c41c68020000308103401d2410080c8010144c0d12144c000810320003800c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 270361241 1250 270359991 270360001
    0x40203070b2d0f0d021b0a0c15030b0409050a05060f33090c0c061005010503070f090302060408030901080604020f040b070809130b010f020a0305030714070b1e010b0f03040209 77
    0x101044400403c0d0b4003001d40c1d52000000e0800c0700950003100c80c810300305841080c411130381c45c004c90141405500301003030824460034001041a02400750503800c1c00d06680da0811541038646002c1c101e182c0740290080c1c4130900b03150812906144005100f079000280d26070070882007800101500d40390034400c0410080201e40040c0d01c5285e0541040c1e000c1d4460843d1041100082c0148018442004400261501521158007015074075a072401014082001480080e40c203520950741c0740441c00c0149000740c0042d80d01d40120308260f00542010140360000a003045503541c0184405811840a8130214034044281040141fa070141e80603807070580d00000b407c10284007070841540c030480c0008100d0069529500b03416002050003130314281c0400c441000345a142400880c1040303015070180c645520315510320328112440d019070301030305100c110b0a0200001241241d0910ba100f800c0944180036a400d23503045595603c14164026003284c501040480005030a031001e903034100354180d4140e80f2580762 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 270362491 1250 270361241 270361327
    0xc120c090305060117070807050d0803150909031801020318010c0312020f0304060605040b0f09090a1709010305060a03080403110406031202070e1602070e0703140f040203070b 77
    0xd644040c045104810020440f02c1d041d22122003480443e800b00e45007036550b035680d55202c22440c818580e0260840302e001c80441d8400c1d0041d90301101c0030740c1c111500c140d180c00240708102c0aa40c0740007250310204d840529410019812400344400b4001035050900c58500c101100c007110a450341040b00c0300c0003030402c06000d00011b0042c810180811340d00c2e65900c0b07641d0038041c0c008031800c0d076481e41002c0700000c040c10244204010803c029041c0f290360121038040c80000000503002040f07a100300302c551000310320140112201043e8442400360384251450006066640c0a096103210304210300c41040055021000c8408a030381c0700f0342d074590000911001034001d02c034960000c0c0016070640214152240d02044402c203660807803551341c2c002d03103800060311280c40100341c030100541e009240600400c0d2b9000030f103d0b445681443d010840e100b0a11841d00c1d00b42d010340b02c54606a4060061001314030b070500c91480a0700c0240c60880c10440a500711101c2c601603240402c0d0791030a500141440c2c980 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 270363741 1250 270362491 270362507
    0x306071d0301111b0c0a03050a030306051c06050709080a0f050601050a05060703030b040b181f0b070308090c060408150108010504081c0b12161403150a02070606060906120c120c 78
    0x2c4020031b0104030a551303003003090301e4044150741140042d261942c081341600c0d00700e9070815a1040410000c12043e101c3e070701d082c01404080e0202007401407544000418038810041d02a40c54841c9c036171540400310620300b242c0350500c1030f0402c1c2c7c030407180400e00780141d4841c0313015501000d0b0107160100da50b40141000c10300800000c142d4540252500500d0401c1c00d4a64140d140140f4091a08010f282d4107081280c3d102402809070546d40c040c200400800300c0d202d020200d8007c030360b0506554486001c1d50018909501a0340500b82c03a80100b814106588840c4030700342d00400b0b09400a001a140a590b4401e4500c28000c078001461000640b101e400e510f43e078400c0109850243c1004000002040203e9640e0030754001d40d01c0d2a0007051000c140700d0035a40303580441c4403001d401031034004011100380c008030034000c14544542d5400c0c40808040741d10350040000800140e113503008020b08082005090000c80c3c58203030045400c3c5072406512030303886100311604290032000042c0c02e108506080700c200c1c1d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 270364991 1250 270363741 270363763
    0x705032a0d09050f160603020f0f07060605030d03090201051605100501090614010903120305071e0e040b0301020915090406080102191b0506070311090306071d0301111b 74
    0x10001040e40d04110101d070380042c81090003842144c525404c52020a6955080c0700444000741c54030b19420004180203402510840380300d00491400e1030b10707203500064507421100003030b0341180d203030841007165040a000c04070034028589014401520182c00192541c41104a001e40800e20040070000f070120501030400c2540c1105824840c950351401b510300a005240a405404800942855190344c01a011101102d034401200c0b61401160002680140070080400c020b1041515482485030078541001003600d0301c80c0ca40ea0340745280075007072000b04d41c40b0303285d40782c02607204110200c880d5030f031099004a00c607034000319980d80d0405a00800d002d070495074480d031203d40c00490b07003981c0d004000e40001c618001c80e9540c40c90509091044000c5002c8003440582203401600109034407500c00d800c204650320151031928603025007034020030300c0c00008445050004580c40c2026580000c06203100c007990380c0c220300038454840c1001c0c110070300d4440c03500d0050b039450190351030800c0700c04280b00300f07600c003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 270366241 1250 270364991 270365071
    0x209180f100605010203090a17070506070c140409020607021002120c1c0302120a200c0618010c1d03010609090f0605100e04061805060709031a070503 66
    0x244501449903540e01404031005181e800d00c0800300b41c95100000341c0f085c640c00184130001451030040d00480c1030038414115181400f40e00000300302a111a030090264034880d9145c800b04034548042d0441d010200c11409108a060500c2040569190700566160b260101d5000341400c044e001c003a4640409101052651140071038010001d001c0414400007004840100744180c0102c06400c0f42248100314413007a010013201e0104a003860103502c400c0810700d0502c90802c83c86200514155903030801d84112020b584200100050040840e00c0f18040000d040f00a120080faa0507018010385607e0260410860318402269520342e000d400c42002070290b020100051079444c1403501400b90141000d81d8074070708107c04a001c1042c1e00702540b04449031000e013038090b03488032b54461000e080449200c81c00300e05036005810200b502401030324040e05480e11061841d51540c40c084031005050003400100020305070410403525089000c4a510040e40c07030300d1042401488003103000300502d4140412038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 270367491 1250 270366241 270366253
    0xc030308091614040e0a050d0c05120f040513060305120f04120b0106110712030804021207320d03080603070b0a0e090a05041101050c072d0f030f020918 67
    0x25040107980d901551503004c0d141030101c0c5003110b2416a43d0319144a004250b98400d009000c2c015100b07450080f00c1318070075425194401030010242e5500c0d0000040e08080550000c0e081041f42780c007819600100300f403410180036552454842940351001e003d204090000001500440450f06404a80142860010300890980541001e0815801c00d0041c440811003c000300800c3d8940000c4a808075094240c002075409402d640403102c007a8041c10482c1c0000300d030305151410b80010b00560b0064203200d14118080c48250841322440c40c0c3c0040b40054403030030701c0d4403002c550300e444d0f00c0581c403143c141c10004c1c45510f9140201c0d140016a40c41010300020200d60424002d40c00f141440190f00c00b03d03a1246c49803034825003030742100c10aa034000d01018980192010313a500500c00740c146240c000080d0364410355540c84c0c0c1c45405d609940203104444618400b032003001c0746426150054034004603500c08050441d80c0300803803e58400c3d0064400e50300c00340042c5000b58003240d0101d242c0b03080d005583d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 270368741 1250 270367491 270367499
    0xb01090b040b22120f0305160b07140a08010e0606090307030308070305010e06010e040b04020415050702030d09050a170c1507020a0e06060d1d0d020709050601030204030c0303080916 80
    0x1d03440e00f180210b09208551100800d10010b2059142c03001d4400d04813682c6843c2d819952a1005000840400c03010b0160074007402005880841000e038950b4022034815036189032449006060090481d14254100020310040c001150b20801c500d042d5510020286010388031800003075228011000c076154544901c43c0003100f007582c400a050302510842d00d01b40f28698a501d0525501d260855500d8006401c0241c0c00302d9629081d0081c004100c000f4200500c5c250303c843c605100401c1d070074a50000308100007110821424200418204d0100d18580f0403002820500040d00b415400c0c401c0e599200b07414809400a146c0078400310800c00c40050411a13110344c01154200b46402c0f01006038460f140b4440000780c403481c880307500ca20510009008130302c2e1207503a6041b032005100199000c01381a0501c0540707291300000f002404142040e9400404015161003400020754100814031410036005010400c0028030fa02d00e0542941d5060905100f156144e8400130b140c40d2445101d58020000800c00007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 270369991 1250 270368741 270368759
    0xb0c0d08221109180105011d062101050106020a1401020406080c03041401020a08090c090403080a0f090c0b07150b0105191205010f060215041e0c090f0f05060f090403030b01090b04 79
    0x54018950318000e001a03a40c803d1000d600840300380ca400503100c0101c0008070f142ca802001a1040c941c84440ac1034502c14100040b800c44400360041009a8401c1030b500092202d054100001400d0030320080d4585810141c000b0121000500103c040220100100c4c08004101114241d1446410000c6403100170000005101705410348480c0880d0140c9c0005e0314032414134928407445107401d511100e50036104c28005000900c050711050510542d0f440400340001d030b50a0214000b032000e0107203c0d0311a946424207403095041140f1202e10b140ca480e860701420b036003080540b007402c1814006030000d400a45401d07600c41c00c5201c000f440140c41c180000c140301011840003403d032605035003242d155207580b210000796150306039009484191014640c20b1418420307403811903000d100c1d08c443c841ba030b0340e03644101040c0e540c42034201000d5500da1000002c2c0d24000d2080a038046000c4801d030354508400d0340810701e0000c01420181c1015168507903100d00e0f0340039801d140e00900d070404419a0307480d541c00b010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 270371241 1250 270369991 270370021
    0x90f060213050a05030a030e22060f050103050603070812180d05101a0a0902090a0305031201050f010c02060d050703110d02040e180d0e0d0803010b0c0d08221109 71
    0x41c52148403d0180440c2d01d040000e201d082c0c959164503070791070424001081081c5001941005160074080701031030710f010046401150002c042c00440e840a0b00d0034513001400703654005102e039002e072b8015403041001c1036001981d40920210640100c1d6604104d080e810765007402000d41507003080c00700e0746503002c0040003c0c552902000c02c100800500213101417508035100400c08407a804000004184034000044c2d006046220004201100403540e80d5240c0381960011410100b0641c1c400c001000a402d0542004002500900e0712085140702580010034600482c40310201da9991040050f201900076808072052492240e5025120301d4a40d0420000c0d510074080c101c0251a4000800d5071920440342d6110343c003030148041d00f5441550501110145400110564421075504036038000c9000c0f040158080c000f003001082d039440840000900c0c0003000c11662040000200400c04a010840200300c101e001700320b0f0029106050341000c8055041c00740c800c030f500200260078414009000104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 270372491 1250 270371241 270371249
    0x304050c01020106051e06070c060c060b0f010f270909051902060909100e010b0405040c08060604171507030c090807080706031107050a080d11160204090f060213 71
    0x44030300080e002001242aa0600d02c140b07500b12a50700c980d82c4110388072407451a05444003400060524820780c40300d00c46c0c00500d9200030045102000004140841d5000e2082c404005035003100f03580780c9810001303143da00746022400030054081034040803218207900940305904a089032004c16a2215440001800002c00c200d509104800101c1c80e8015230114614117190010122410f003640344c0c05004a2550051040010750300d20800070419500301c0114602909051051980395404d100c14481200c0444d400728083c01180c0041003460758880c021a4140c0f00e580242c1d021410340000110724148540300240041c08540f010400815410350040c55070785142d50303030b015840390703185021900c907201402082803a4202090500040b40030350040480320000102d290300d040c1860311264144900b21000302c400304c200203280c51080c80e1500400c4c5003800c00f034220a02d005e10761107a0106084042800900071030701c44aa840600c00b40c51503e032040d50b0070410640d0b0302d0415840c2007003d0b141d5805 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 270373741 1250 270372491 270372493
    0x20619142d09031b0f0106080c010906020c1e0d0602031305010b15030c03071e1106062d040617101b1b0c080114010807060519030b040917030405 64
    0x10341c402102030403525240c0180d861602443c07500b092515030030005601d420003029580316881e800310710030f0400d01c40c1e000101480400350400000400004140c01c407660700c604119445015400c4003035680311000b140c40f0303030000350351300000d8208004104a098008005844140b01200b002030b50200c40891620242c4070782c0081000e5103a0004218141000e0780000c4500841031001a00c0c01107050b0080d9088407050030000304550b01e075195131490301e002c000104001000300c10030b81c840100c104625900240201c070b05003900c5000c50140d591288503c03804403400000c803008480c20740c540c0d51115011f050b143e940550700000c1a10308585c0d5075220503040c07441034a00401c0e40800301d407610207083c01420543c0d451103940c4c21800d10342d900983d0080141c83c40c5d0034165002810413801d00c52421817501c28422a5015031405030224246916684460284401001005040522003000780506407040c10000ba00305502d82c00300d00140b641140003490000009084103010480402a5118500c180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 270374991 1250 270373741 270373801
    0xd05062e06050325090e1b041214070b0909221a0a060506041205010b1018080a020907050a090801020d02090f0a050901060c0302011e0905150702061914 67
    0x34044112081c1c0320359101e000200740c00750510941300c035081b035a604003492240c1542501e090b4168041103601c01d5200c005024060f802d20300c108669503044103441c0d21004080e2492074500303115805144900d80e2005c1c401c200d03400004020400700c64290308800d82ea440e9495005c0301c680707005150705607180382c00d1201500c0d15000a900501d42c0c090310069400240c807990400d0300d0191034582e07840035817030201c8681d500c54000c9919601c80c07010451b03800301a80d503980c3d806c043c0b000c0d608801c40300700e80114007242c018080c0c00e400b503102c007000140c02141926140c0d9032240000c034100c038402d41940010046500000c0e91003095803d540103030000700d0080b110a14200c04070810000da0310002d06c40c4540014400300100401c500801541d0400c9000b40008942480e802094500c60000100402003080c0c4e290190410311000b007011900d10703083c408525105082916001c1c0d51442c000300030000d61443c2c0c8604404444080e08103440074902000f030113400342003d0850141c08002c041e0221003840000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 270376241 1250 270374991 270375031
    0x2070902030c040512030c0a031809020f0a05070c0b030c040614130303080903091206070306120312050c09030307030305150103060f0306020306060906040605180d05062e060503 78
    0x1500c00c80c0d024106119071a407400c3c1c0341c00d060080740d403610f0400565a0005002e00c00d600c180078001c241480e4402c0d61860720048214030805020711450300700c20b48161052140740258500c21003100c4042c101030034965164800c81c501001214096048036481c080b000c01401080b00c05203020b0001e446040d168003d542405100440042c001c4610114101e030300c1c00780030800b09006207034250308440d4084c240e038680b00800001c20307019288041c11411503070055082115941e0b05202e0300018041d40d0940f9a481cbc200e1b1348008118288841c603040040340c4e00c2001c9142840c005084031040c0c00080d054a1b200c410078240500108400c13680e66903032030b2201003900c800b58460b2180ca01960180e0310203000090a50f02d0b004000d400091540e90031480400c101000c0f036503260050002001160307910755442400741d048010804031140c0701c60182081992003800204082507403640400c100b49441955640401181242041034540082c4840d5001022443ca98401d00440c03150a4120805107030801c0c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 270377491 1250 270376241 270376259
    0x8040b0d020c1b010c02011808031c05070201050708150a030f030201024b0c0a0b041a1905042a0305061308270603010f050910030b06010e0a0806010b0a0207 69
    0x300c1c0d140760700091300b49205c4c1c0015070144d42828402001225091201c0c4d480f0300d419480d507032100740c03c0ea0303402e45080d4001408404d03900170786e6840720700b0384020f024070b0405100241400c0302c040c100150b40001e10501c84510703299a55050001c54000810078030420031404d01034002d6004003035a903014103480c14802d203066000c3d5450601c160410989011510b024007404d206490140d8005040e40800c0140b0000403004000701a03510313000c1c05e039140c00c506042c034140b028896201c0c0b00071000c0c0041000c12082d61104480100c401031200800b18060f070700c5141c211001c016525099820580c5092480700743d50360201030b40c0a03a4450412101c040d20b4041d103281012200d1503006046003010040729020300b103406400100707200320700c0001800c103800d500003c0058000b600300c0ca189000506040215203014001580c022200d0485030070000c0c2140c860740364010004241c281030003410f1458501039103440c0c0418001b0460f4209861295856a002943d543d1219011070010310540c0310200d443c1c20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 270378741 1250 270377491 270377533
    0x30a0e0115061e03090b07030c27030f02030c04060905010f0e13140a0c090507141303031832011121040e16020f01090302060a050408040b0d020c 64
    0x1640f14044140d001d40080400e69148400c18802c01d51680c2c0e8200003c2d05403001980a4100d6480100c0c2000c14048000d00c15231441400440700c4a40e5802c045220070325403441c80c02e4a800600300e4000c04c07194001320340380a5040200c150050f00c0d0030000683c1414036070000d8180e0b00c1d1040003141c840c0d80c44484901912095a00d1480c03120041c4030940010807100c1c0040141e07040006983c1040000d07294001c1c80c65150340701c003098680f90380c200290103070701c503641040070710a034800c46061040980d019030304140c0a0100034144060281072561510030814507a0090132440c600e01c0c5004805603012003543c5a1440c011803402c03200e0700c82500d560007840c0944220021100400d180380c81e100d1041001c40c0d1200c0082400303c410000414440070442446100e03003041d854220080c40c50b400000e10700b0000584c00f200b5649084811400a0f5000c60382c5500300900c1c05000c110341d2943e0070b19425074800c60344103800c241000100b00150040380d80190950300001d10555000f0f081c480c1082500c02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 270379991 1250 270378741 270378749
    0x181c0905010c080313060603080318120304030507062028090b03070302071a090a0b070206090d0509041b021506101e2a0215040b1608090402030a0e0115 67
    0x1810a00c00034070480703001120400110b001b0040814456942d40340c030703500e07a0300503035560f0300c01d0035591580003408004010b1922046442c0030309070329500d01501c000f06203000b1200001c1a80742c0b00c040c0f820b040c00d40c9401d2040d190449448041d91030b50308806514001c51001119004490f8541c201c141c424001e140310390403201808185440c0d40d0322160100c00a501c0210221088020700480007150070740c030003035180308202110082522900c50305005d2010b8070700400c4501154000820424a018003042201c0c941d42241802030b103440c1910000360141c4820344403680d21010b00006980c04650029010032003042d4846035554a4407510103000034102c5001143c0c011850f180c1c02d219168034032040e0904bd68401d0310f00140140007080200307808990120700040c881c181c00b841d0105510309040b1216207600c00761103c519051810780e20300400e002d00c00036202c50010840d401010705c07552100f01d0780000c000a204540d20324000c02038200500d41655040301c598600000410540003010102c8103803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 270381241 1250 270379991 270380003
    0x8010909030c12020a08030c090906040507021e0708011401050a1d0105060714011b02120405030c151209010c0f1112030a020d1802010201050f0c12181c0905010c 71
    0x5441d42c0c0e140c01900c03d551514000440c4a00da401102042140c3d003c0c6004858111105546078480c0e07040203039005010300880e00c80c0c6d00d840144013259400158107450201c08648025071003507904a0705080081341d6100c10612350031304e2072594150b250528017038140c0d001158106045512100d00810b801900f2001080903031841703005011526140307002d044001d01c10450204c03016680c214032400e660005002150100980104524158062219080d0306503504292414689814002540e0703403038010111f80034214480c2d051032003403000000c65200da10b20000b800801c0c102800013030300800c1d6052101001440320604c1025180c402d0680c810001c0c0810f00500d031150045170808000e50000d0701c0c803c0706507401c00c040c0c1c128100c0e500a043e02d13003401140c0094001d265000180c00d5540041c005841010b00000300901660140c080d65010130010300c6040300366940c030660b00d94100e56018004130503c1107001d105070409410398024070722846942c0703a040c0d40d9540d00054424004601c2c0080103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 270382491 1250 270381241 270381257
    0x618010807060e120d1d191205120307080103030909290102070909050a0b1006200709051501140a050f090a0506070c150203190807032007030801090903 67
    0x2c944201c815042c814401070140070300c01c05802d1405d10b003034400c2c5510404224043c03294420142805c402d49001c90f4140ca0001d4000c40c001942d015407000390103512194503036610504280300c000c0042c400c400f03000c0d14003642c0c0c0c1d0429001c06886407500344800c0f400188488004125020240503a0481004092016000360300228440a40c812558020f50440c850005c0c0014004d0117400781d000f040e070044c0060091000641003c0e14005001044458079001c03c080c104040e0b54404001c18402c80d440720305142d6021341c040307001e00f030001c0d17680000340140c200342c1400f40c802c0398107005080014007601c0e4048a03010350310f0001c0c110300501406501041c000e10030411030381c0040008103000c00c0001c0c5046181d40e101d000080c4103800400c1e0075a807070107200000b40982c180344520078040162500045007000c0c074083c1c185070414a40d4100408002e404000708048500a420150006007034007510182d003030701e000c841d4010f40c0101009400040a660000800304154410310464036016600c3c940 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 270383741 1250 270382491 270382499
    0x9010806010804020312040902131409160c1205030708071713020409061103160e0306070507081614160f030b040305120907180c0c02041104080a06050618010807 71
    0x18981da00803c2a41c060055081c80241c07903500c500144003a011030400103031252003582d04114061255007002600c0030b2100c0214500d0380c0d031402d1107940804103040340500407014400c12503c41400d0031004021005441707a00c0c400302e4014019500c1500e083d0b5031031099684181d002c6a0f20110741481518039035028000c6201c09c1811203411101341e00141000c00c05562680e208070490f40c0303000c1400074141c4080300340900002c00e1060b00e45099003c0c030300740d40c441d11040c0000e0785621000c0c202e0014800300140401c104100c0078169050040300c52200e80c0c510005040c90480000140b58407112801201007040401d80d808511005231460080780f40807440c210b6481034801c84000d0801d0b010b00c0801d002c10145440807980f03040c400c0c3d00d01d10161240a2601c2d2400880c017000c0c400313180b0600d050041c00c0440c103900c07100800746aa0111000705e5027400b1110350031428407031600046000c1c003c0300301e90024040d440d00801d0048005403045020003150341d040d0b5220680a000c0e0860302d80040100300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 270384991 1250 270383741 270383747
    0x1a0904080a030e0f010606080f0f0106120b0607051015030f0803070507021e04050a0218010e01030f0c03021201050418081305060403061a0901051c0501140910050c0901080601 77
    0x3141c4815810300107040001c2251491400203400c0740c0248036910313190248041ca40c040419904220710704081201130a0545241405010500030407041000c6031900754111441500001c04000d009400ba56850140b42071440d00c5000440e658141c0906100e00740f408441c0c4003941800712500a2002031011944d565400207591029203036804010701440108050b85d01c001981c01c09048004541600b18500340500040d00c0004046580c0c091040c0f00301c4110790f0384101c080610403400d281140c401044500160700806860000f6180305260030320416232550158020034010042403051031090381c0e900200826070b40c0c0c1d903840c500fa40514414010001d540c41d40680f020907068032003e07074019183c0c0e0200307195400c564000c0d20f1254455484089850502402400d94281555406015030400300865065841c0944040c114444000803105100081d8000800007040b40190313081824100b80440c1d450151030102c103140d42c58180800c0300500150111081c1420603114040310b0b594140c015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 270386241 1250 270384991 270384997
    0xc06051312050c0c010e0a03030c03020f01150311090412050319020f09040b18061005090d110a1e0302060306011b0309090e06060901030809060d020a030207061a090408 74
    0x1008461038251154005042010408005002580e41603203032281d41840c1803510708880402410301040300d4a0b89076540300c1a0909090741e825042c014982030841c81c04a141c102d010304001915403030810880b614080c4810500c0440303000e55906d103800c2500d00c00700403400a05071001400d0b03d01c03240e00c2400407030140c030146500c46500310841d0080112a41d0200599028100c1700350512400619031809261034030500000346004d90b0b119244100e10a00008103000c041c05007485150402c40c0090b0541c85042250340070711000e0070018902102d40b074080341d8801070701e1a41c0d110340c418400115000603060392150400150031010501d10b49540c00740003050b40003400c500d0412a0b4101c000345c10700f0038184507001e558480d0b520046080e18001c0c100003100c00040f5034480036005281405a542e0312000b5060540390803d2401c1e6a5650300303000030b1241d11076515204040c0340042464a40d450300341d8007038011a8013850742070040d0702c0e1542c405450400000720302c5a00540c00300200303020940d9680a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 270387491 1250 270386241 270386251
    0x1817060a050912030106080f0f040209040809040b180402100206070206040611210f01050a030305071103071806090c0801150e010201180c08150702030a030b010507140d080702030a0c0605 82
    0x1d41d410b0f1201c8826101095000360850740126680c0024032030301401400083d0352286005000912030b0070075a0020704140310282003d0f02a0030080341c440d8140e80c0d540c1c001142a00003c0c440030201d4081d9044180c42c45080b68281e1003210241c1802d02c1c82400810080d102d4403447d0f000d404c0740e540d169541e170001c014061483c618000144401d82c900f54644815600c100080400300d012031510a80405c40100305804c0f0f01e02440040004000003504202900c5520b03921183c1301403409809008a032130003610741c1c80f1034a561880c045440342002c09038010f070180c410007007003400b462540d04030564030110203104007c5d0240400e0084940184141d441001c01801403001140c1556080c41c406105800080140c1d0601e08000307007040402e00c2005199100043e00403d01c0c07681c82d0460f80030b5202c0c003508a881c4241502c5203180c1c41c1d076038850800c4484040d84844000700c50340c1c550717030841d030355101010600c001b107410980400d200314000025581c07888900d035a181c0d131106840e55144003410303010704 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 270388741 1250 270387491 270387493
    0x9041a040f08040915080106050a03061107060222090c080a0c020f06190614150c0a1205210f010b0d06030203030c03220513180f031817060a0509 64
    0x503a01d00000c000d14001d20041007500d502040003102041500c0588059602441e4541c0c9460410400390300c2d214010b00440b608003000280d54070569868910764800c100005103481c0c40003515852081c040f4012050214001c40c1d44200036403120310714011900c40c51288404900e40c0b500140c54441070341c0080ca0600c80900c1039400c00d99a1040741480d24030242c5403280a20405c00c0c004181205a1151500524100b202d00401c800710300041405091680800c642031a030004e0140e104140070004050030540c0702c540c103d41e0b00c1005074020f03c290802a018894100300041d50306280e01c200782420f002e40c4442c00c03540a20f918100549007140e010041500003192100000000f41e81d061000d011008a400f020f5951012640e800c4070340c00410a05c09018038006902c10301c0a602c0310780c1c4459003024101c000103034414402e14040c504034603001005040312451702c2c03c0c0007050f61080c0c0c4d0748900c40078400e05052503516031700f40f240c81d12001ca4510010754010000510806682c0c1c010300d07013241880c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 270389991 1250 270388741 270388763
    0xb040905070309051b10051312030c08071b0e06210c0303040905010906081b060d09061e06050f0d1218170606060403050a1205090406060207030203010b09041a04 71
    0x1944450170300e40140701d04400c0c0122100d170450305040642989040043d030b4a010ba01c0c1c5180200c002801c030100d8002c082140d840c60b1380460425008200109000b40c01c80c02c030f20b80310f039032034503080c402c03d0603181032601c03150a244000038004401410ba18020301c03004000810403d6007512400e003061088040b810316104030701400303a02e520140002c001034a540c12006c04c240d07041640b06d005840c004d0340324105640c402006016401d0025400c005070040c00c4402c1d81d61502210010f10160840040140250303141815480d80050710b0701c454100c01309540002c2c0b003004d80d03850401401000c00c000c01508250300203422400503130b0414a12052074031a013400448149030300c4025200d542140c003c1104802ea00c20104c10452080140c1ea44c849411229203140604554170f107600c41c00c06160013041c0340030450120085902500c00d440280b600900100704150707603210001d65a403180d01c4240e01a5181810030341e01410010091841240c01c641f88034044c001402028510706d030700038000c2c0d60588c3d0700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 270391241 1250 270389991 270389993
    0x306090605030a022412100f0503030307050a09090c1e1b0b040c03080c06100b03010303090b130302060c15100e0103020d0305160b090c0a030b010603090303140a0c1101060b040905070309 82
    0x10400780c40c1081200c00706d400d4600c0c081d11712443c1c042454120900803514000c0800c03207640c000040b01c0d0b1104162401a031146561a01503079072229940044240030f040074440300c2217a070f0022a490300090706450359110810000c2003074440004008442c40c0e0303407903000305034000315800f400c0054110303202d00e04814407070780e481e210041640c10050a140c1990082e00074000c0503202404184068001034181c2031455140d80e8000e00382059922403048013140100d80f25860300403080c2420b001b5500035007201c4e5200004004036441e46000550480d4403245840032030803800400180d607060301c201c2c040e40c0682e64290380030820a424807000031400c00c0b0041003042c403081051005c00c03000c60b115004082480c10001d2405082a030400e120340d0250284440400200b000b110546045503818100003402220038101203010702076021007000852000000d0114404540d40301185121541c0d850007019051041d10600f81c4140f4810340992040034007045c400880a64480b5800052901300090340100e5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 270392491 1250 270391241 270391309
    0xd060e0a0f0608030409090c03060603080405240901030b19170f03090f0927030712020a050a060506030f071701050c0c0303010303140903011e0c050403020a18060810020a0306090605030a02 83
    0x15002181c10306c07008a001c11003420121082d060301440212904303030030703150400f112401d8042c0d513200d141095240c0c3c19268440d00d84000340c00d48961103410704a03241d601e9000707107000c601981500403c984140103050300b00d01c00220540f2201d4070300810780311803010480d080180c03902d0003034034821580718041d40c0500000541142d0308042410603000d03544030102030506030001815803440300c0654108094140019101040601040e81e2107040003502e80c403150040380c5040f1841c0f200e06c2103480340000109259254001d4192080204002071141c2c0c0e4800c40311180344c0c01000316142d49640309200501c00240510900d4110180c68014507007001020302c002030a4071508001152040300c0c0145904031b180060242d04503086d000d041c0305181c580386601041c01082e1922400e110114101c0340850081c403140c1080d4014014941190070408021180702d0080d40300511180100b40b03800c100140350801c4d40100c01c221070004002c1c1c04180110b07000d000b094031001049403071510404402806401d2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 270393741 1250 270392491 270392501
    0x903030e06160212090d14030912070f170a150f0606030b04050a02040b070b1f0602070e06030d1e03110309010b01090e0f010b0706020d060e0a0f0608030409090c0306 73
    0x4804070999070000b066840203030804111130f01d000340100c02007140700ca007521260042140c0c1c5501c140d1000180544600b41c904500035190500e500c40c0d1240c00d030541a440000d100d40580d841482d050340501ea42b0030380b080750b59031104a2003540f9008001c42c0000b05003103666440200340060380c00300e054505000c0e40d07011151140c102501180c4d55880f042c0c82070600d0704c5400c2e404041d200d411840c03d41071544540e110b0040c480000d00c02101c400002c7c640f400ea404006100c0300001440f401c1060b01c0f40302c081d417034440364014010032101020002e0b515103000603420060700d0042e00c803028809000c04101404502c80c502a1003815200ea00c0794200000300d800131845245803c000181c5004d07035600040041031554130203014040c00c4800d11852204208041d030444420580644d5241002d14120b000f901a80c200c0441da140340c42e0340000c80c26a181280751040c074101808115210510000c8030840c0d00fa40104031055000380400d02000b0391a84c00002003d028806003141203070341e940e440701915 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 270394991 1250 270393741 270393751
    0x80406050a0806010206091b0402040f0b0403021203073206010602070911091305061c1a0f040c0302060903030f0c1c020706080403031515020f060a0b090a0903030e06 73
    0xc0d0000905509a036480540e81d90441000d1020340560f003040031079160b81d1110342401010f0448407081010f19552581d04440c000d040c0303401546403407640d075822441e03a60040e100507030140e4181182c40303400c010003008540600c0d0303101030398000d4000c290f210301c204100d80000b868031310040c0100c1d900300d129041100380d0003494654000c20002d4107240c0c08500341c1c0c40014604481e41c80c180301c1e40c103403540c400682c048110020200010365a59500009005900e415542001079107110b0400051159040004541403000f0301c500030329444030f142c03042c000d0404580142c85000d00082c2030005281600040c101100c000b800c613030038000090f5035005275601a2105046981c403640901c4480d003200411840d03030044600181000c3c2e85000d002418016000f0300c024200b5a44207206486041c0c26a806006400800c0742004003005103c0702a581e41202030100d1140d1041c400040e400c50301c10f0250610403c0060014512070322560540b00c00307441c115600f20305044d112100342103034a1040105034821 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 270396241 1250 270394991 270394997
    0x90312161b05060a0e070b07060b0616030e01020610150e190609050306090a0c060305070203070b070c020109140d060e07080f1f060509130201020a050102030106030b1206160f0c080406 81
    0x641480c0c04100300b1502203140740501604500e004002e0340300f014007900d01207031300710401040030740d44ac0c0e0000300c441c46501021425080403120040c2407503032049018180341005c3e02224110340b00d251202c1460032107882440c8007000d0700441400070034810880c0c03800b060000b81c00c54031001e4169031107250714212500b01c00005401c0704401c1000f0318003084066080030700310000e003204c0c1d011910342a83c801c04c0360050109041c0c17280c1c04038503914400c108540d06503400403aa0050360600301001480800004826070000b0300c403560100e41410f100608a00110703004000020b05035403a9110300190859680079601c0b07010b5a04005585030f41402014040e4040002800009500e9070500103040050355083d404540b814405001607160040c20b1030308039440350b465442c034405920040740352861280c0003c001f9400400005140c41c3c064000702030000e81116440d4500f0020900c80340d440b0000c40d9100040391204800d541403600481202c000740d0b04034a0956041031440c4c5807a2030540c07140e4003007000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 270397491 1250 270396241 270396253
    0x7020a030213060324050c070b010302150403061a03010509010c020d0c0c0806280c0f0c210503060f0103090507050114120f07030c180608280c0206090312161b05 71
    0x448074a10600347d11020710080c96040c400c00e6212402d41000c1408000d025420001070410450f08110035100110740c400420b00100400b20f0300c003a40c070003145030300c05d01940c02c06010034030216060182000249050340104003004117108203d42003117007034005076003050704500c0206200c0c10900050781b0900d00003607200708201c880c004288128103070040f030700d40e020b25242005d03201a5211b82c041ca041505450101c5008860303080c25141490040c0c14940820210142010903a07040409107109280c1114441328030100c100054042d58039a820080603504400018070107580646007130314481c28100e06142c241100700042c0788c04040c00f990240e090320910800c00c9440c9a01d801801c02802403442c04521040c0219202c41c1900d80310700454040c09810300000e403400c2a80342c00600303014060921a04078812074101000104074104101c00180a806c0000e0440000002141d0143d82e6010012549588954000d01c801e1a101d410f01c040140342c0150250800e62181002400b038010806418 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 270398741 1250 270397491 270397553
    0xb0c03040f0b0403050304060e1c050114090a030509100c08130320030d030507120612060e030a02060a0f0603081c0c0806030a0206070614130303050a0207020a0302130603 75
    0x2100e15150b4040c410080301080148002507001c8140c0d01292064205140020709030030004403640b1490303110a04041921031030350280801500118010300c10512128026150400c0c02900d0744114040a40460b40401a400e4281003142d0090020601d42c540020502034030b580342d90065001c2c4000742d4405070050420710603c40280903c0d4410402c20710b49000c0b185004010a40b1380714010b0162050603035482c00507444c10f0081d0f88080c418151480b01b08001d688410844208000507103003600d1241c84c0080b034080801e80002107802d10708050300100599030764420340314040d0005004030314285460340300000004624001415071344021000e00c003001040e0718800f000b01c07071a400000d02080242818000c5c10780340032400041c1140c0546990340d80300e0b8641010f2018100d0303801d9134243ca0080800300b04503541c2d1100075150f8544240d400f0320040e121004541c040c1c1c000c042000c1c1d8000766040c81000107181c07451a00c0340380726400074040f0341d40303075a81c581524071403a00d40380500844481f95449 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 270399991 1250 270398741 270398759
    0x60f04080c040c0806010302030a0605030d09080c0d0b01150215010f290a1103090603161b0507060f0215071d0102060c07020904020109030b041110080f0c0904060b0c0304 75
    0x201a4802507604200100c081c20000b04002405131245d4103050f4000081041482243c00c01c2c8064180501100c0c0241580840103240c40d07910320861903140920b0008140d1031a005a0740f01d007403038003d200440ca03a424141d8400d0ba14010f1034030701c0c1c1588140c0b0000681b061251400030b00030480440c9410204d45014400400581c10540e0303440342c240d21084150500c9086800e80e0190350244c42d004054503202d0000e04c0c650712494000e107038402008402c10980c04084400700b21761040719502e18056200b1986100c0c81c1803001d043c000c1041d04a61030074812070f88591404400032045204840e808005180c11509640e01601d101c000906c170426051082a45070140040310242032008100d02d01e040302c0507515500818800910656880c0003060070740e803150740d040010b1504110076030560308091500000301741c20000805e008030015412a816240030300b904074464117020b0003d00d00c5586091040d24a0b0703102c0c0307503944d41c065610400030502d4034030400035041d40c0721648011355856050403044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 270401241 1250 270399991 270400003
    0x2b050624010f23040503060a151d04032615090c121906030c060306030210050304030512060103060816030b0a0b01140901020c0405040b06120303070c0b090c060f0408 73
    0x103030600c10a050b8040344664400100e448008022440d01e03050720184030380e400f651080354001a07151003a0b00520a618513541d04c0b1081039201c01ca641040c40e42d0303401031040f20719000302e560b81c072404007200060301185c0a2100f1040ca070142030450b07145032a1802000741d50010540386101207007207400d99480f06080c843c10240d00034400c144d1207400e01003401d1503030508510043c541d017a41d0107401540d4110740520b8000d1005036502a040054031038075484001d004060900c8181e1240e03015218049005000d030007100e0289825550302e601c0c2251055100b02d00c2c04002e07000604042e56034030b0003d040101807014041c01c60249400c840340744d2942c100060041005841d52040c0e0b450165902c0c5242e030020300301c0710b001018024090301d85102500603070400414174002508141000100400c10040c5500c091041000312040b13644850b904800681c1c0703000c00ca4180002c107000d4103262000c50751555009500800150407540000301c0d14002c1261504030520407029000085403e214001d0203100b8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 270402491 1250 270401241 270401311
    0x190504030e092a130305071e12020f06031b0f0723030403020d03031b030608150606041a0c01140f07020c0607060c11010e070f0509062b0506 62
    0x6940d0b200e8100600c610010000b41c03507003c07034540380002c2c1c504564030802258401550801c050f5540103a0322040c1c00051020442d02014a042c100d2001c1004070410007081030494000e09409000d038001414050644c0c005400a00e504200b408000c84502e040002000354407200700c240c0d82c442015140c20704054001414041548440315281002d11000006407030840741c0440788144210503c1c20150018100d42c3e03c0d000d04d400e0b10640c5142c1154040e00304000308da01c0c0408403420b0801401c9003a485943c1901c440c1c4d4403a10800082000852010500c00c00c1140180900e107001d03d034204070b81c2121181401d00c01d503170f43c0810410054602d00c011055000c103150015128140541000440b5440340c0400288a1603682d00c0744600d203403081c80140c00c415510b02c0208000c66454941d26551310040c421401648013940c0c0101e42418480395079401100c024280400c04201541c0d0b5043c1d5a40915031400b03910540b498041c04510b081100b01d0180da103244110480da00324608141000742c0004da = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 270403741 1250 270402491 270402511
    0x10608012909070305041a010e0403110114040204020a090b040e011e120b04031709010e0f01090317090a021c030207090e211b0124080a0b190504030e09 67
    0x110031072076880c0c80280c1ca41c80101d624000070641d980d89880103810103080c0d8101e0380c4800315800450360001c0c5c0e10015000318041d86079505030010100091b82030f5010030b4140e0503907103801c1021800500342a0041c1c500031060b400c05240b003640303c0506610a82041e84128481083c04004208064a15440000380c207112545d89a40d207003000d80d120130f41e03080e0f20001070125040f20001414180302c2c2801014804094a150203281403111100307001c1c0001e840070005a00642c2d22420031000144a2002455455190800100700ca16207056038204002c10804250092200a100603500d015820141443c1030380c3c204604502c605000385000b0080c0c004040c4c451070800c0b10941680001140354002a10714101c1482c0f9580c0018406a4000e080610b018540f4062040707080f028117421100f120a200e41c001c000c031503c00e100c0d0700741000d4580701d0740400d0740201d0b00d02c0005c540300c89081d540c015922070010724101c981161903400c8500c100c506900183c44210070b000c8926190fa03485402c582900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 270404991 1250 270403741 270403811
    0x1804320f1e0304050a0b0c0c0a09020a020d08060109091512030504030312050f0a20030c0a0809070506030f070504030203100504050c041104050d0f050115030209090607090603051801060801 83
    0x1001706a4042d406e0103080300e101000300791f45d4580c0e0401c0144061204001d8180895166540e1000c8003030340040c401d420250007080700e0446101d1141880714440c8005030342c0c907a40c1c5890445198000c0150489100008805d03040100e00141013010811035107100f0380c0c8283c0d0302c40c40c60500415803000203024803403250414041c400702c40004a030b2541c0113020300c0c0000501c100d50104004c0001240d81c00f144c400c000100402c10b5030400c0e10b025140300c06003500c500c40141d0768030b044203445500500409a00c001c2c01e0006c681310b450030601c569800300b15410241d150a861fa000a4039110030148512001c50311142000b0070420107110602c20f00c0000d580a101d10340900e4882402400769000c1c0c5809038420000880500400e003c8044400360008000c0191034142034841542250a0100b0381c0070b508440e01003130700301e00c00003101ea10400d440d5480c08401404c0500c00c40280c14043c010003101350000c4400120342c1c00a2081c07200030040c6030700000e91584100795004040707510043c00d500881c519 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 270406241 1250 270404991 270404999
    0x10305072112020f01050411040b01050301081203061c15061401170a06030803040f03030e0a0503030402100903080d1a0a0e011a0c070f03021804320f1e0304 69
    0x4090410407082d4481c140501400002d0000c9280440b00701000f84150308100034042880500400c09242d03000c250b03000e010408a8400544a0b44420710a0312450b51204503800003c00c110409140c101d00010625178103148240652481640e034548191004038000c07828035104041842510b00034030340f202607801c6501403600041c00180c0034840a0310303d400200006064905641d10040140d540a0040350300c070708140c20704016050380c544080300800c1c5810f0302c0c1d040e20300380010100b410b980d000b401145180c0e82c40c0c0c00c0c08040b1140d0564a014807240708070110000780020082d00507111800340002d104030001600c44421800551114019a10303000140300c0c1c1c00d42084c00c3c9041d50314070f001c410500d0001c102141c68a01c1080c088001d940a12580407a010410800c0da034112402101c0701a04504c403091011804042030301c004140d06c0300340300c200c0f2903511400e42c50025581d000b0903038090f4020b41442ca41c205241d4010b41c2d4126040b58503c200c40c1701441180580c5440c84400450804d424 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 270407491 1250 270406241 270406289
    0xf0e1c0b0705131701112b020f0d05060a0e0106120203061512040b100e180a14070330140d061d09010c021b03031308030301030507 58
    0x20205010384410403a40001c1c1100d07001d01e049603051011903000c1c0300e0300b681da811403190f540001c0a07030900725400d040d1060b4510a208090f00c5054116401e404a44048080400f41d8142901c003103d01c0c040d000e016441089690902038041c40f6103480000c01d89103025010400c901410303070031114211f2542c00040c0426640986e00f9084541c095600503601d45501c40010340015084400d5041b11100169080c0210b80c8841614051445480410b1031601c5100300f40c40c4420403800b900c07041c20050400109040082c4080c016440801c500f61095009a501c51005ca1a503481c2c5400701c513404070324100200000245000c0170400040640b848481e8000a4419040750200291040000901c0314030f40d04842d0034200d800c25440d56200300000e5548880d044105011000008658501c4000054401006000703044070000154080c0c0f060400180c00070120050140709140c051109020300002c1c03414540505000e0319108008688940c59031034041d2800b9095007084420b20741d07449481c00c110403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 270408741 1250 270407491 270407539
    0x2203030b0a0e041115090d020a0506040914070e15070f0b0a06080f011407030c050c010c02010b0406060c020901030602160c030c05100f02060106052107120c030b0102060f0408070b070f0e 82
    0x1000c48825031481f140e0700004544c896140c010591040b00082e000a6010791544401310703441c0382c2645500140e6814000b03a82d40d1418501c07117500701076a0203c1c0091001c41800420344103100e9581030000704443d4032164043d0500700e0750086c000c2d50740e04041c0100c00081042c50306441e401c00c024030a0580c2806804065080549002c040c141c8842d40b04420302e010306e0903644500a46002004100c0102d580203001e0245101a01e00035490000d01103980761081c00031103c1d558000c2c03c51700303141e483c40d51041d000754400303049809400b0795641003400041c06156810011406400c1001da89402c00040200d000c5421214005029481940303603005a000318016045070b0b803904099071150b850340c103080040c4e11402607042c045045d01d000c210031543c2001403552000d10380902000801d004200640032105d41140c0c0d6405170f80040002024904e900550580c8180300d5404a41411300f16030b240814080c00761074003400308075000300d0301d146a588541031468040c0200d41c0070075425444404040341c16 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 270409991 1250 270408741 270408757
    0xc0a050603070212180109150f0e060c070303020a05010b120703060b0103020d020703030e070b03010f170a122601030b012309070c05010e03032203030b0a0e041115 72
    0x40c5011000404007402070000b010418003107203210390b50301c0c4610703020440b89400e01085030104060201c0481d0035142c069600c1c1540c03c640d107520b403007100d4080c0e00740c6000c81c00c4c10106034820340400204545041c00d1001c0c400540c4030b42c006001c0440145001405c1d41c401044c0c00d0300811a207031441c8501000090b03014102c6c0d402080000e039041c00200101d010784103919031603003014000a4058201649a440001e0520f031003400e480d0317601d4440b901d03d210b0380700c01c0c030510b09000404402031000d114034422405001e0255021601c030103549a540003595000c800154010550b20541c1401280401080610b070350600b1001602c5503045959200e51014180200c0c1c004035043d1103032250124200d01c4540c0c08080041960001d440c040000402000a03078204652550811141504036000081543e006803010094514040c02d500d81ea110898400c00042c0c041540366000c2014a80300d0140c1c140141101090b40802841c0900b401884015207207103c601a10307201d15440140504942640c00329 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 270411241 1250 270409991 270409999
    0x1050306060f09070504030b0c0304060513110411040504050709060f0203040305070e06010c02030114060418022b081303021018030201050912070e0a05070206010f050103020f0f03090c0f030c0a05 86
    0x6813540c031070480d00c030300a0741c000505490030365007400610508040a107101e684209000e1056a4031590207502460554038010710403851520407264a161941010410b0624240030a050650341c50000d07003920030545080010650141c800d0060b50362088507083c6141e070a0004501d810b186a4802c2d6840e03d6610400b020206100e0204d4940d038410007900c040640c004000b4070121070902030842d030b039220549115220700d250042800350402280407411000d50000e0aa146c1c607589081c0e0f2844a040900d401c2074104101c016040020b603000000d0b000070409200c0b05800b45041d0303c1440074040c84903496105100202c1d000e008103407950030340c1809a130b03030a20b2b049031960011008608281c4900200301003d000e504000300700c0d51011940d42d882111014420b204030b8803040d03011398884600303000340c010b100c01401d800e02c01540a5001020b1249c0302085061405c0c51510000b512500151503d4609400c03400640e4440c5c40c0800c4001e5141c5000c40280156143d208000780b442c5200740720346405 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 270412491 1250 270411241 270411259
    0x31803080a180516080705040e0c04090204180524150f060409020c01090c0905063f030d0f1802011b06052d06060703120e0d030e0601050306060f 64
    0xa010040c01000a100e58020112202890b140381c00c1300c0315091034052001c032446685d01c00112842c0c140034825072042010090000b0100c03c00902c00078001044003683c20507214124000e9a9068003403032400d15003d14040c00e0b154504004508900d1031103481002e840c000101403141704120888040080751080755943c001c8040d06002c04c1180c0074950000350800c2c07002c070b501081e00c4019041120207034443c0050055a50f01c0703140b14801c80f1002c0d17401640054a9000000e850300e81442289040842545102a40c0c84041c8c8200494022940004059080400e10b14101040c901411040d022801e4050050070500302410404140040010741002408021180385058884041e281903810036810b01603407074240b030107c01c400e0110310314258030a042070a0303055114101c54482c3c0034245c010b190519200c0180c90803540003207402c40c013010040d60b03000c040c142c0c8601000019800092600c0c041215800d00201c6070400c030059001c0c03070081c0c01c100c0c1003045039a03800364248500f540840f40368074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 270413741 1250 270412491 270412511
    0x60904030e0d150606050901080109020a0509100311070c05090a0c020d050f0c010510081e100902031504060b01030f050c1b0f07180c050a080f1e0a0c031803080a 71
    0xd4216a0f480750b1031110303203070410108440c0d9009000b05119502070300c5112099030390303240f900e040b4072134a0070800000f01c090000341040e1402c0000b4410040d0b5603c2c1c00308403c001c400c00180d5a40c001c42c0100c46000034075804014a08202140d81d510801c1c2c920104404880844081c2d101c0c07960b09454000c0000000d91502c180301908162803a0001c0d1358002c1200740f0349400407007000c42040c041d0390382c1442000c10120309090082d010424180c51a4090a03200e1341c240c8002d4081c2c0314541d0101d0340360180d110240101c440201c14188503d01030b50010130558281e8002604407203d1819880c1154202000c114002e42c8070400c403100c00381d5081c5881c0750250b014504c0350404040707080e1078040340901740e0001018042e07a1a007090340b001e03d84040084a00c1d261341a52507101350464400403d07810310005000725000d407450780c6d00800c00388400c02c851802e0030100400550466480e0311499885101181c03655241c85400604100dc40b89a284002d060300c025119030001007a0101d075940300c3c84445 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 270414991 1250 270413741 270413753
    0x30a0909051317070b011d06090907060e010306150c0605010506070215030c091008070206070f020c010c1401021b0c030304060c060207060b060c010e010b0a06050711030c19030b060904030e0d 84
    0x15112a00f205042170503585580316101410a041e140c0e205614040010030310525120b48490701a1001c4801080680c0c42c0103410b071545503c443d4880d040c550780e4040000d4980d64003020810f051110f9907140388101c1d003807520400b200c4043e04418021001030040c0c00c0141c59419111503034501c1e10b40d05a89990720701503950f03004c0c0300d0f4041c0781d80c02c5010301d807991044076040080140210026001d4a455a484a50850b1400c0c032540d01d26006902c0a05142d51950140c1070701c0300d030a409180e480b44141c1c1003081d0603081e60b1241111000f20844ca0b451021010828841d4101e03030f5100724069881d1a24080d0018030b210041c00d409000954000b59040808c1441e6200440d0260090b00071500c1c2d8844c0d0300d03550300030010060084815420300403d48501c1c41c0404100007a140305885640c10841d450b11020040080302c0d90081d014410b40110180907603074001c00740114203035004c3c070030512403e600e0803808030000078103240c1c01001503106100c0000c0c0c100c0c441052031b9005840d1024680e5890800c6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 270416241 1250 270414991 270414997
    0x9012c0406020424020c0613050d1a09070503120703210603050715030e060c04150302090402040f0f080c090103060e1f0e070e16030c0903080c030a0909051317 70
    0x1009008a2a40451400d0401144d41654041c60b03800b80ca815001d910300b8405280300e040b0015103400000380c802d2009161082c5000300c1c0c140901001c640d088040302136015819800c8d100c07007049500008042126180400c003d440d10340061205500f030040e01d079005480a5020000c18428401aa50b41024400c055002400650308403085411483e0b454a01251038010301050800007410300091342c2c503030361000aa0b14003400076244101c0c5130520b0040c19255100300802d1013002c00d502000000465580e60000c2c0001c0c10701d031146c4e21405490400781581800c01c0d03511200b01074000e1414035505580320311000f030450350041e401056090f0740e0946036042c4075020440d411005405d0200d0880c4000c154815480030600300c00300d503600303038a641144142da0404c54201d1384500461080e4030390b80d4400e411075081510070781040e005072a102e03901c5d12016040f849408483c1d40c0701155021030641d001440318003c000610341007049080115140b40d003c001520080c0c00c104a051034145100c00460031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 270417491 1250 270416241 270416249
    0x7141011010c0f0e090402010906211a030105091c200d030b0319050604020607110a18140903091e04091b08120403030c020a03020901031109012c04060204 68
    0x8114034080140043c1802001480e8807001861803c001100743c00c094180c2405160143c45101141c0e1810004907503540828202d0250b10f480c10441030309050700c1e400b5040c040542c20310707404804080c42040c5400c483d00200712041d1688040e40403d074138421036103210b4500a4901c0c10000d40c00c08000400b817500f40c2c03070100c0d42c2c451044100351541d040d45a84a4600ca00e400c4081d07548030640500d081421080428003d0816000f0801060040c603004000b0a00f0501c140928211100690009540034080354007100703050034118482d010b0400503115051030344400c150b0702c8045080140003e035a0b4000c2d409041e00a402c041c20140c0050a07003010300c80d900d480104140035031025407401d40700084c2d40ca032501c0200c00c10010040b4801001007424120b174926100c0403424640f55440071144500340e04001da0308600b05090100c05070710b0301710242d40654011007100000c002c80b503042c0300d80d54030305a011030101d00c0703458a6606001180c2c40c12091003080d03202611015210390400400a00c69940 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 270418741 1250 270417491 270417493
    0x9090705032e0315020702030f120d0f090803180d1b03050a1202130e010f05010c02091503060a02040311030c01020706030e1c080405070f050907030c0203160308160207141011 77
    0x114013001d00e055400034401148250141c2e4500e040c1e00c501aa40c42d09500c0f070382c000800c4d040c0180e146602d041d0f13005081d07807440510702040d121015202c03094194003d56805202c01708048074189450400c0191122910444c07408000c0d4400c000600c070507010080b0b6008042000c0001d00c01111440303601804440080403404541d43c5c0341c80c83c0200360303030703401c40c0b02e550340401d0900000554a5040101c4608441040c1c4400391100c010703034200083e200303009110b08600816074038666050345080103202e00c02e0324800b40c010303956410f60420100f15084081058466840b0b411243c00a99020650808a41c4030f824082808020039041a081c8910351180a07115210801e104006d00d5200f60058084e078061070503280440e445410142100c80d240c0107094000030841c02141d1000c3c0709038080341c4000700f1807050742c0c1400d212034148104542c2c054010303000140f1100a102c0b10303890360039428014804900060200c1d40c6017005d000c490f00d00c42c130002845500d02e40607a100003806444005443d082c076170 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 270419991 1250 270418741 270418763
    0x1a1e09010b210705031f0e0a021e0a0c020f0f1323040807060e0a0f0f060624030c0e1f0908071e050114120a020405120309090705032e03 60
    0x11030000c045400807585d02c11b0b00b40802d4180c1d1200380ea000c0d0181b0503110000202c1c21599249541600a036001303510304030200ea5080d00303503075035120264003401080640ea60780f0300c0f000e04a801000349c011740340c801541c03091140d45088401c50392108200c00c035501d9184070104a0100415031951044802e0159445030301424040104001d0724100401c80e0511854040181c0450382c0c02c4e040d41c0d402d800b01300414480703503c61200c000c6800741d940c030a140c0d40b00705408581103407030b4500340c3c802d01d441c0800386211611484040c8445501070040c2ca40c00e40061030108022034080b0002001c045650340c0741c940381d05680380030180143c0304511030805030043d0b5084510035a965404036021500050369a6022200c7c144081400d40c4900c480c1045075158003d010700301244625646520311020b490300c2d40c01c6a08100008040c2c44105000f0b807680051400765450b503070840240400e03000000d011100304181081001003071244070940c88444490000c000c140c10200740480a003420035070300040c000c10a91 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 270421241 1250 270419991 270420001
    0x4051804050f0604080304060905030405041a01030b0906010e13140903040305010b0f090a0507030929010f0503060f130203030d1e090c050d0809041a1e09010b21 71
    0x1a160003248500d0844030015000b020305900d990059070000c00e050010404030700810215005998000d0086080c0ca242640d034400080440d541e49c2d4001041e51050b5030500301e1036815205100604001713581c141000d01d880310000381400c200d41c00c0c0d98483e10814502d20558889907000f01e03010b40c5400c3c080c403a036040c811384550b5a604988001c48242d0f08000008055080c48044103206020103000e0355000d03190403001502820009050a04141e034030041800032420780881008030619810a10038030300c00c2ea1204282442d030503001041c682400880c10003058a0014540c0d038030401640150400380c4905207505c400180c41d0038003135814440412074000c00880c9a100c0d032184100e4607510346145100c1e8402c4010b44100c0e1001400303101c0105410400c509080343c880318158803441c2c01c646001d1490001030101d40640c40603070769002042d24604190304107203080c0b03640c450a10b50007510210600000441d02d0105004240d0108004103440000941c2d0000b92801404401c071400c043d444d01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 270422491 1250 270421241 270421279
    0xe0309060d0e1207050615190f060f0905060a03020717041e06020c03071403070503011d01150308070609020a080a1202011b09120302030f04091e060510030f020405 72
    0xc08006030705203000c1c0c0f8140c500400c2203d400c503041254494003400c0b43c0c2d643e98040105888202d100c1e0383d0841e034800541d80e0101d00020b120030140280744a90030f0940e0400b200104035401e003007001003d0160201040c0400e03922081540c0442d00f1914026a54403000d103003201c072000450900308084d01c40481e0200701020099035400042d440c4a950f0340083d035903124101e0382c5200304458181c154101071000d200c82000d80908501054020f4111203140342d60388003103821a00001803e42c4500f030015017206488034203000d4235802920288903c0000d504640b9030025510030380310020311032035554008808540701c0042c6100102051030954614100c142050488860884066801946070045000c065060308074a46c00900081c0d0b035001901d0305102e168000240e0100d02130b82984020300030094074090260040c40606030300b94010400b01504401c400d2201405a02415a1030510405100d0350702c40b03143c0c00c01100f4403454040b48406071100e680c4003d2081d1740040c0d07040321002681c00d001c555 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 270423741 1250 270422491 270422501
    0xb03060412020d080606070b060103380307051503070318110310110a03020d0e011812030603080d0b010c08040f1802070302120a1e1205180d030e0309060d 68
    0x4440c0d026200c1e114640c180840d1300900c1190000e61018061050801142c40e0359006540000c0605000030b000c641c024000043c040703120a00801442c1c048045107520403140070701c0341c8001c010360007014950704090020f2007082c001d8802c0321000d900400050841032107500b201c0308130755032101e0355110031031103041000c200e41c0c245e200a80070380b15080207000c868841d031103081555001c89410383c1c2090060023040380a58403190b0303d0301089441e11420008110284207d60b558002c1341d00b0469451403510380400103100e00303850401858502801003000c55040c4040310100a030580000920302d1034000103803054116100e020380032900119000c079040c002c1002040503211140500034184407800c0840c0160b20903108000d0041e080b006900c0040c1000c82c01508040c5103e08280600d070382640304080744209030b4182c8030000395031990a180b01c18014450150080d004401055a0000400c20b071669809210100010107541e24103201000c1801c0c802d03201100782c0104078990350448d0f00c0d400000740c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 270424991 1250 270423741 270423773
    0x1308070b011d01050604090903120204081c03020f07030c0218010303090501021207050705150714060f0a1a12010905010e030309070e1009051e0703051603090b040b04060b030604 78
    0x200541044500d184450004a0304844008000e285000d0070100c411002d49158036003102031082600072442ba10300c003070000d013020f00010030050046c41c01ca0203010a03422042000202031600c100a11a00c3c54105e00440324242e0300750401c000003002c0c504c04150702c88880003848440080e400300200825500461110480d0401d17801c441408410500b200594410010010041d41c0314400c104102d0411020507850780880400450400341d05445203040c147c0a4400c450721030300304404010150080300111a0801440801006141c1c4107a107107405200b1070102042c40b420f0f000e40071900b040d000750401703202180d0100080c0b01c0c0d4000007103819941e0300b0503107055019010710200407607050001140a84141c90200012414a1400300c03050024407000e000c3c0340c042604240403441032001420268000c8041ea1740009807072400700486d40140320043d00d40002c05082c40c000001003501201d21540294124181d5034060b280c92030020000c0c840d00c24099058003a0b00200010b00c0801d002803500b075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 270426241 1250 270424991 270425009
    0xb1e1021140903090901030b090f0a080306010f080c07060506130e070305060a110301060e0105070c061d06090d02040f20040603050130051510030c050303070314031308070b01 77
    0x1d0344440c01c40c240c6038091800c0c0d981c0c10a000800410200d400e042041d81c000c82101c090302d40ca2000180c90900f072000900041c0e401a20000034005d00f03583c40912008040301e2403034500c649007031030041164141725100024201a8a840108400350741329495203042c40900d4008124400c4624006a220815480255114001e110005030596a24042c520000840c0314041c3d00d5607080180030394115498406950411606000601c0040e00703400300c4101a1005072500c3c1000012118440c0459100c00b0103103014040a00800e0300a440f00c004031030425504540c007141c035242d01500b4200406003a07a605a454000c4101c0b40d451b6204d0200034400c1e42e00c1d944d8144500c1ea03d41070a03109800c40c5c42c065640c2c030140441140a4500c030203400d228101e00c40c4003590040c4014541c503807905030f000e84801e00c0d210810a01082008448040e0078000c100940156041a0690701c02401e41c181000c000c288920000001807191403824464023002984400d41c0350702c401030390604e88260007007401781d1070300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 270427491 1250 270426241 270426281
    0x3110c0a17340e040206040509100b0a08090f010b030607120f0c0807080f1302060304032c0102070e040b06010c050a06050403020a0c050405270f0a12030b1e1021 71
    0x400480d6241d0f6621071074001d403030b040c5041e02d001c06125410000420b440d041c0420500041303040003220000b0003055042d43e40300e41160030143c100380d003440c25142d84500780da0b14002d0410616100858503560080c1c26082c60860744503071940e1710025111018600309060b01e4081104501034000307440c035028050380c1d5107000700c40c0e840319138200040300251038084001c1c140180010040c5400780045170b00c10f201c3c1c0343c0f031200a4030388100d80048003058800c0e007440c1484216546200c5d641000242c00802154a4010140c141902ca680541c480901a0750402524035004000e102e801c2051600140d48040104010329050400941361030311442c08441c1118610380002e241e28180c054207000e01c00c40050165868904090604a044020741070340080c000c1412094501605020304241c8030700901d4a1400c0c1d403403820000341112000c141903841061251802c402681e1954034144580106403090030050015034025290307820881d030200007031001c0c900b400a13000c403140c10240b544844a22804070b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 270428741 1250 270427491 270427499
    0x30106090509040b0105040c030b030102120612070e010504090501020408121c020f0a0c050c0409150c020115060c0203030d06061e03020a050a0e04060f060c03110c0a1734 75
    0x244480b0160f40c0035000e40030020043c001854030b588003211750b15842c1400039091050340c0c04642a0f0b00311260b0f5070850303440241002403504080304550031030712000b005171400d5824000b4803401d40030113000e441c1c0602e980b1f08461003040000d40c11503000d00243c40440f150302c0d14801d0762810030340c80b0140307172282107d40002c46002d14055000b59481e01c51850649070400380e2500c0c0440d5420944c80042e03440788a4101c2041c0309803240e2250381d508a0240200d8050300c42102d60ba0b10643c0d24400c801401c680c0350a08a0b400c512107295040c00741c504518001c00c507070748036000107031840c02406205002e05141580c0040c0458000800c01c4601d203a0340d403a0140c11408103816003c034043c040662002c02d0b000c00206d001d582c450310b41c914413128010800500e858a4286200d11440c55070010400714007114801010b140d08001c028075031182983c000c0404211502c04110100054480d01032468213108001c00c0b509400d010f00a0010a5644a0f071381003000d02401d00e04c7c4103032035441e0550b8502181400700e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 270429991 1250 270428741 270428749
    0x11191512021204020609180703060e0c04050901030311030705030f0301060e19051309050f010213090c090306050c0c16150c170903071e060801081c1d03010e030301060905 75
    0x30ba803202e011041c2441070b0f41e40350207004132a80b001c800d01d907129401c0011040c1054403816a0345c01024655000101c09041c0340100d00050800f40082c50300700c6043c4810480d03650b40c1d0084034192a49841e0070301c00710408030600d501c0c41c0a9100d0090144c000820200b040484100140d0304840d00355407003d0301c0c0c00300e8009200c070404000b0700b4040c02048842c000d00a9041040200000640e6468000348072280c03922501d04002c104600441c03280d40014241103204688800c600107801d0b42001001040360b801d03805000100c0c83c1c4002860700b625140004c2e04d445220007510a901c1c40c44041d101c02c4094450400e0845c043c5028030100c1113840f9041c1c6004511881100340300d650701070040b0610104205c25031081341c101c041003d42c980b103002e10200715074414005068408403c15014801d4509059015150007016000044150300114240000c4445602124491010350030304050b000c00c2c402000c1070111003601e002c0d41549c00c091070303d84001d0b4000000c0d8100d603170303666501d81345e070303858070200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 270431241 1250 270429991 270429997
    0x3051b01110714030c0303030a050103110907021005071205190c031a06180a030305030406110c0c130e0a030903120305040804061107050d0b0703140c071119151202 72
    0x44041e41c0c0445010f20111407022071101d00c0d200010102c40b003454001001900e907a01c200c0e00c5052480d101d800400401c80032081107c20703940c0c01c4404460916203d00c0080d0354409840003c6c0307205844c2d00c0415401802032910100c0e1410550007406285080c201c0515170030780300340c0015851494401da048100344603124003a10859107410007132000c03407104200951904800c02c0403100040800900111b03a0f106101c41000310300c2508d91680328607007421714000305c03000c40c0b002802c41d82d4200003c00703416101142c09200c0300d20407179403103100c500c5141c5460014804081c003001103214440100f4103154010805000300c2e03101c2e4140301f2203a540010228143c420680d4003c12125041c4003e02c1001e01600409200700f510a04640f4010b03520000641191100c49056a0400d917020500c05669454010840750102d1b0000103a220305180e603111044c2e114103003024101283c0f0002d0551290b44282c1412850500d80704402c0001c4e0b1180b00d26150341480e10311060116a22480703030700411616000ba = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 270432491 1250 270431241 270431267
    0x703020a090b0d021b0601061404030b060d1a15030708010902060405061c0603030c12021b06090303071203060509100302181f03030203030604060603180201141303051b01 75
    0x9041620b45014000b61198003d451844200c2d9003d0203079903090b03205204208088082e0f03800908180d40342c100081c00c3c075200b0824500307050404000a00229840c5800540c10450949400303032140c810342003110003446454081d01041d038030030041c06032081c8208514001220100d042e120120350b2030035000d0807143c0b6120000d40066040c0010030040c80e144015149110700e01c070070800000c4e400c225000441d04140c000b2800f1070030452843d020310007c1c80c0e00d920b01000e107000070000b030103182c41c1c4034111642e540c610b01d01c218030000308101039850034010f5070001790740b1000e81d081441d10300d04040c1c06000c0387d0040d02c0c01050060b0010320307540055044241202d40241c1102c011042c05008030f046000c000780852007441a060441c0c803404001e13800000110b00075800380d038403828050708010903108554454410942000083c600901700d22082000346036090810000c000401d074005200c600030300d0000a98000303084000414000c0224400080d50008600901d0603c0b8590064541d0070741a01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 270433741 1250 270432491 270432497
    0xf05130303020307021e150108030309071502030d02121506030412030b15030f04050d02030c030f07031803060e060c0c0307060c091205070e010501020109031b020105040906060f080703020a 83
    0x1080824029401142c015031540306076a07400081c101c1c1e001c124940c58402c510780d5072004800200540046124901503c00d101c095465400c0c40b000003039840c030f070038041c00c101442c1e40700031004218000c000308c514422014200b5500c8140d406920000c803001154008400c0000604140c40e0740b8040d02242d10844c1d02c010444c011607440300d0300700c0c0180202c000150304410749183c0010741d080d0311000b4600c140c405aa200c00c00e450302d0b24104d0300b42031103541000f05561080c0103000e011031011003591181100800728545032989414115070149030743c0e0704410952a680c4000c07003070110a40105181e41e020800310348940e1200003c0002520070314080b5481504240080e60000e465500302003024606490040c40300341d240c00d500f0340b4218010000315070783d80c03081804104080200754050b006000034002000701007400d45002d40040e0102b0003d400d18003400300550216030142c1d080e180030b450126410005180c459102a010400384802c40010903400d100140ca013500c41d008407001030300d0580e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 270434991 1250 270433741 270433771
    0x1603020d031206090f0c020d08092109120f0705010c150f060305030c0129010804140109050703150b0d020a0504021c05070305040219141e031506040f05 67
    0xa10708480681c0030b800b125030301c40e4541400291094060045001301d09403182c00152141c04101301a1420040003c080c09000401d0104081204040303040c0440c040481c2d030000c40c10303204015854035403140c1c491855002400f101100c1d004900002c6c8003500d90030034030032203c001e80c8410042d2043c14510100a007000d0303070080c0c1d58072940000d8101c100140503000e4089500c540f42d80e80c042c110b4005203070000c0940e44d14004e115906180302c503140c5180a500411145e030041e00000240020170081010f400903803c000801c14403402507029a50481e0403000782c48900e600c0e417521403086560700b56404101400e010f0001e200e80ba1613480e24520301c1c0d0003071440000900e82000c0c44065040009110680d08000c0740800d10103030107000d00b510411083e50006540e190501c10001000d43c0d6545088a090310300070140040d4000e400c040000f40d070104c40d984c44101f80c40700d85540071000303528110b405025030601806500c040b40011070064004a40901c410001505081e04644045600442082c044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 270436241 1250 270434991 270434993
    0x9030c061804050103060209040b060f0d050417030405012a0c030305090a0605010f061e05040504050c090d260a0203030f0c0405030d08040303050606030906061210060906081603020d 80
    0x1803401441c80303104200c00110820900c1000a003150700136031003070303c0e42a00001c5055440c0780520540d614140d0850b001c41c01c029224814411700e0007000440c0e01442d968802240600913055403404070b43c012a043d195072403909141070381c0a082e6a942d10036040f20190100319000e0401c800c0d0180d2201c1c47e6030340e09400480351301c040303014010180840043c2c0c010000310708045001806950702070904d0501000f60700b803400e04000c0108840b9030f5106400c50525441c2c404040d4440101c40840b64100c3c0e0100341d5441d40f40c0c00300d4082c460410007580c4605105022001c212000f4170b03400d0440d50110f407504240c1005150341d9428400d41c801e9400503001000042d0341e960340394200c1034001040c1404c141c11b040c0c039200407910b8031424400e04004103a2072010081056818014503901c000142d8010b8158101086120364403480600b0803441035120600b2660340782010004181405a03040e0305101440c0e40360241002420f041c000c0450a0141c0401480e00002d80c110050450368003901a580d00c01302c2d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 270437491 1250 270436241 270436249
    0x12020a120e0112110f0703051305040507120510051f1107060909020f09030d0215060613031401110a09061403090606010c060603170a120608070b07020409020910081209030c 76
    0x82543c0f0704004041c00e0100d121543c17050000740180038440d0722102c1c1d0715035070360542c483c440506521080c8554100710401c011a03902c15000d0342100040200401c1c00d444a52420002c0e2580f908032030303000081c041d50003c0040c103202c1c0280c0c0b00c11060700c0d4000c000c0d501c0c1ea00136854003443d016910100700d81c80f0b01000382c2ca11030ba00400061134910409414000c0400009042019074113407400182e0004103c0580c3c0c840306c0c2402500604216101c514240003107811040c00805440082c24104403d02c0d100d404c80300c01e41141c0c002c4031405100f2030796080c0c0303003001901d002024003508000034109810a00f14082c18001c40740590540c000902c15661560011120801c04260448080340c5400c00000020b04807104200c02401002c0042c1d02e1f0150103e000742010614012400e85c6401d0030030400c030640001c030380b50080d50031100e0703841d540c7d56450011501511021000035000030250040005119130401910207603411001980c6403400c1c1440ba804960240d030034000d1349038020100603502498 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 270438741 1250 270437491 270437501
    0x100905241311030103080c070803090a030809040f0f1b030b13180501060f0e0c0a09140103090b0108060105030111030708010e070c060509101d07030f0c0312020a120e0112 75
    0x2924220102c0c0349080d400080316590400c0c1e20489a03050702084401c030060052210744040c141c00002941030480c03410001d0346880342803001501d41d41000802d90303242d4866802c00c50320450401d0b01405141b0080a40400418924888a41c180c650002e502d800318400d004610004500629025907502885103810007016140c0a0030040c00340e001290000843c280110402491810210724065280000c01e80902c4001860702c0200306040200340c001c0b0360400c00d06806d4510402c24034001024000c016401400059000f40c5400c0b1940000a00b83c0c00c0052068142c80702a002400b80307080203104451030b0f00080d2074010124200200510a80c01d00b440d02a0303012502d0b1800038043c24464440600310380042d58541e069401080303012681140074080c0d8828001e44400280b10402040d4409854138858080140011011404002072206103214900510340101c05140000c4003008003958409250390100c90320801d8058440003640140d0000742e6514040e140c05281041c0500401e0040c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 270439991 1250 270438741 270438769
    0xc0804080f090306090105040b01150f030b060919150c150506011e0305040c0b0c0709020d1b0906030b060711012d020a0614090c0105160b10090524 65
    0x28401d1010100c650f400f0410180251111800052582840c0c1030150040a05030007a00c0c40a18a5140d5520680d00910000c5211500e1900165122032280003800030710034401e403103520044050000340c87c80c0300d40a21100311655060720980d440294401a030f8078404804002d4015186640031505821040e0003c5a10207414980005941d01900c00404072030b1142c8c01d0500000d40c1d031320400003004024031401d0040c1c8811404503040a03118209035a0f034000a004e25030007281c000c2032040301e1521641101d095103802d81d20a080b0348c0c2c24880001c10200d4644242d0001130708008a107541402c00310103c1d8034030364201009080c541d4910006540f00c10f89010b4120100f50301810840d411080442031042c0e01c0a5503028000300031080c01d01506491031020744800b194032120900c0710028000900b000c0410013030a025894195030010f040391402c075500c0150081c1400b408004580003035602d100280c0300c08810070003143e19020341c466a243c0c2d10241c83e1074505c01d45216803801d032904091442c005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 270441241 1250 270439991 270440017
    0x12030415090b06040e011509091a0c0a0216030807060b061201030b06040f0213260102030703020403151815020705011d0c0d080915090306130b010501030c080408 71
    0x28180394403109045422104003500e44641c2101803011500c0d05018401410290000a01c03824a03e07043c400143c001c18450000110354032800242042890f094880220717200707030005102d9180084030500f40f58000c0d510500103009c1c6a40c40b0340078000805d84002629000003019060140c01e03540c0b100240548044507610404c2480200351080d404079909020303521541c1d00320960709141e82440f00f03451881800da01d0060041c402a80aa520713907803072408651601301001ba503a01c041c42103100d10004904070b0764071075000200f000348998068004208503442014000c1004200801ca03504990003040c85020307401d0180c015030042003000104c1107900107000001413074400315943c3c440c01c55807d4000600091083c1100e0824003c09201d0407020b40000d451460b441e0196a80b800c3c110310803020361621614403000c2101803402c4a1080d509841d80103412204a0f04103600000201c03288070030203d584a01348400401c265100b4064111303808400d4a80c01c070b00b070300c03142d480c207226030028034080702d50b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 270442491 1250 270441241 270441263
    0xa050a0311071202010c0e0d0213021602181f060503070e0402040914150a06050301151209050a1502180d020303070515090f0d0804021002010b150c07050a08120304 72
    0x31070010000141c0016813a00005404da00c0070038094000100310340c1c501c0c854240d6210800242c0c9482000303e522a400d000c00599a840c020b003420751042039460b001c1e42100703040308040305031280700003841c0c0158031044a0984140798070012241074000303801440b00003102803001c20200d03400785040081e8480300401c050308140c3c844042c00704940c401660042c1081600050003901e140e0003280540c0850191031403803010f410400f02500d42d101c103115200700600c03120b034a0308806214900c84149007903000801d100c1e554050411581d03403030030300301c013030300d101c1b038080c0b02121a400503100710b0310089440d01061100e1000101001680d045c10391003aa0540800c001005c0000c20511443d040b015424251000700e080000c0010f10b403141d80e0a9030301c0305a00401411000c5c9400482a5610950486400b01c1001c0414022405000031000c115008085207503a41e8003129140c0141551012460803560156502c0c410040d4001c4544140c0703e00f070b00103081c2100c1010740d06005550084c0142900c000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 270443741 1250 270442491 270442493
    0x61e0d0b0901020d05090c0109032306010608010611010507090b0705013b0c13110c07182313081209010605121b090a090609050709110a050a031107 65
    0x2000340021034420700565400100e9500c400c2040c0f090642000b0f018005144000481001034860003181c000504080d5011000c101c40b01703500e0141070b408000c043c083d1109540d6803170000c0c00b81e44080c0200408a01010003402200300144102482001195161017816107000502070013076010321015203c0d5502d41d4143d00c05c08241041c3c502008c5910b41c01040d0070b0078060f41c0000e420404044011941e00b0180c00c1c0e58540c0c0d1014501078000789010000107000c2030a06514005105051900c015402201c0c4001002c0e26510040b41c0c0030586084280116030144407180860321a10f000a2150740354a0081150100d41240c0380da03413039208a80640c6001e195040d402001d12007181c0506643e9152407042c401400c06a0042d038511400c0b13002003a000e1000303c181180000b0082d0b1050080404100081d0000c1071034020465050f04240c0412002c185c9003882a01d40085005159a460810300d81010242040f0f0481c0c01d035140d2581c6440c03d141501104030050485607000c0140c620007484540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 270444991 1250 270443741 270443753
    0xc060204150908030309060c0f040909060b0f0409151d0f0705030706080108100b1c1b05030d05192001020c150c09040e100213061205061e0d 62
    0x310281007141d5074241e041200d001c000b00780d6103850b00404441e070010b000784150722400042e502c1c2c00641140d41c9603280d000c405c4d01050f05003d9944141d604500385a0141c041c00450350083c0d00401095440700c001203000c40501c0140c0f908080010590840707110481c01022144d8820808102240720865070300d0811420141750072092007403000d2681100a0800c46841d08000d00d00080941e4141610190f01d82808203491f00c0104070f0b002941912031300003801c0c40d603401d0321250b00070f035910303440b01490080e90401d044000d0007100410110401004085041d1a000402c0f10000c0c107070395511071805111050003c1c1c0400410010010f0280c6403500b00e01e02e41c019030340704140a401a00042e1a10031000d00a4a0700360340c01c007056100c6550340c0c10f21a1016100c41220a900c105890105010b01105502864103400607514a103c0c5e00c0861500c0f038004c02003e80e00200c911540c0c540001104140c2900304851060b035185038006000c0380941c00e941a02c40900140f50310051030504071078540d80701d60b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 270446241 1250 270444991 270444997
    0x5010302221706060904120806011101050106030204030215040506040b0c010603060504080a0e0d02010801051014070f0c09060608040f05010b1221091011031903050609070513060503070c0602 84
    0x8580b040c07003041406841054104902680400105c400d880305050507103420414180303000710007081016410010300541d01489550300e8051885000700104d680d40d0f1001030081d0400d010032803007000008000d107110402c4105480644000424040c946460110300c0180740d80642529221952940310000101d1903c0c410f042c030031400faa1489aa550364401c0c020440f10001a44611541013013400b440540d80c40030441f815240281c40e022144202c0f0744007a0740c403807052020100b100600203080810025051030780640b251040044230075850711882032105507423013400b9a41c0041c50340000034022880021841c410175002d84000103800d0221804500100749003096070400740d01103074188126094080c2e207144040780100e43e00f03003040c0e2a90001207681c0101c00101c42001003030f01075130000d10400d104862a0b1704051035000c00b03050140c0001f401600c000c075503092045c41c08100150400d40190100c03810700c007100302c1e405c458a0600a060706c0540028100004000410032a03174000703400c500c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 270447491 1250 270446241 270446249
    0x5070b06310f0e030c06040b10030c0b040306050106210b010e030d0c050606030d08060d031e03060f05060a1b111c0c05030c010215191b080a060f0501030222 69
    0x700e00b00c4034002070182a00d445480c044a43c0e441048900f001350382c0803540b06d82140d17100240c0380c1292107500c201c0200c15410741000c0d03c41c80036030394001102c8003540018803c691041d90103020583e603d04081e2000c4c500c01166482c5114107881d05003000020780c2c05040c0000c814105442501d043c00003091420091007915001f0540e10304010060140401c58683e0100e0210300800ca20001c2c6074008146920241c0054051a0a41d0041d0700f014001c559450104400b00d03080840801d14035001070240135a40f00d000031010801d00b020410741043c43c216251700e88152a0001e440c9080c08110100c0f01e00103030150784160040420400aa44400701010070408503d0707034030300109060411011079001c9601144c1309038441c40d0a003585980201d44d038030103042202c2000555580300f0391051a13190140c2004403085280840340344000465260040392002c83e542c1d9840640c1c0c900da00d03c82117502500551200c02e4420310701f002103610a03001804407021540022a03501a0b50b25085a00d1205800c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 270448741 1250 270447491 270447589
    0xf120c02030309070902160807060b060f1210030812070e09010801020c070b121603140c07050d0906231e070b0a05040b01090f020909090d020d05070b06 67
    0x144820f100c0204600d03405031240b440f0462a1030142c0595120f0f8151005004000780000b203522014800f079603000600200002c2c1916507a000580400b00d5558403c0c40c003000e2030f96a101c0030540c080071032020641503070361026501d442d0508104910044400c010850300410900795906c02c3d0036116078600340c0c000c0108100140e15500c40304001414100c0c0ca8000c868100410b2000048480c440c9401c15040780c14410302102c000921081140605800540e01622000ca54188000d1034010001010705a018800b81d0351100301c086003c6401c403c1a10a00340019507044202d035000c01c0030528841d0901040c000c47d80f0709222000b2420151101070403803454000301092102c18811026609079100500c11000c000300e203425984e04c6030101d01809500b401f9aa646465514003100c0c0e070494000001c02040e211451506001d1161f5491410500b0701c010f00649101901840c00b4009070317084181d01c40b8120301130380e40c0c001c14001e1040740411203c1038105404144035400b443c1100c3c0700d1100308a81 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 270449991 1250 270448741 270448747
    0x306090103021216081e01020f07030c0309120b01050a0e09060f10030f0f231b0d0f1103010605030a0327030b01090b0a0614070f020a1512050c090a060f120c0203 71
    0x10340045840c451b42d88039150b0716401006103070b1180c0c01c880c3c12104095403600b4040390380c4445040441e550651500b04c018134900c0c17143c4a0080c0140614154103d8100300e60400e01e035515107803000d107040030030742d0b490b40300e60701401c04a11807640300f05040d44c0c0240c2e10714500b541160b1b42d0319400c0042540c0901912606884d043c40024450018401502c15084049442c0d8a91103845041d0350340a41180720155a54920800407183e0345503290b2030340d42ca800030021340703450321030f030901c40c1000301d2540c4a07621035842c080d4006524100412003200c0641c05888030000c0d01021500720400586a00c2031400816403550007000152454003442d0180001078400503a605481003071000054054100d0810f2101d4901e0711503804c10b4010844a41c3e640c04200c0310300c401e91620200b02007090a0308400a01040d4002468659134081c050304400c51481200340029151411101c1d0144100c118443d00070304041c0040c00410b014903074802c0c8903100b40c5040e20802e1401d1503420110341c2046880e00040e0000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 270451241 1250 270449991 270450013
    0x7260a030e0609060606040603091a150906010831080c030c0705060f1804060b16060605040203060303040b0307050f03010f0302030f010e0309130e07030f17030609010302121608 78
    0x8201c195800b00110005000c5805d03c0d80021314240aa8802c07002016101c03a48402004041c4c54440d00d401c880100c275500504140d022082ea0348411175109006548d171030005002c1e507108000d0980503071902040180400c4bc9115200c40301c01c0918990441e0700034202c450800100c1c130710020540440c5d444081c607141c1846180e600c0c141060b561025101e20400e112243c3c468200341c046502429441c50522191540030380810054401c59200c1519000c02048900d80010703056100108244507102c100308643d210400c01c8100c3c041540d100f90154814070051000c103c01c04011600301050b814000d09003200d4903030703a03401a03000f42c01c103683c80d101c0c1e21420000c5007000c002601d4004041c0000380255051420841e42d03a01524514502c90030080740140b030034841c150b21118202450b9420b4402140d2241060301510f284400111901d080b09000d0b48603100c1d0944c01d4a0182400515001e0351342d01e55003c1021034000030b80040c0040c06200030490001c04801c0c02c0e10b0050404901404541d010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 270452491 1250 270451241 270451243
    0x150902120f06030d05090319050102030712021905090109090911040f090b24090405010c0905010f020705060d0e16030303110438041404060501050a0507260a030e 71
    0x80581022100d14508050182ca5600402e11107034403e82807810b9a11203045e08002484c06c01142e40c0344221071004a01101440307419002544214181d40320140000034000e6444100c0c840d4120100b520f510400b095003266109400a00c82d4020500d40402d240d601c600300ca004480500c5000c03900d400050f40f080640b030400b80101c2e071502c00410410419500e46844445003008000c1c603c4500880718040b1000b200d0108102c000741210262840b183c914291400c0c40c001c01c8580c80d10804114201400201036100310718200c9500020b6026007601c078a08414042280c0148021840b034588810b0040c08181081010804421195103446100c600e1030070301400302c07102c0747d05403100300e80100310a0101402140f800d07500c00c5100c511803170001840610611b90000000400311844500082c0091180c0b1085041c0c3c000324000c40e010040583d66800641c2c5521805103020049001071101c0008250003110705100b250f582038040030108040350f44d000345680154115004030f0790300c554110403000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 270453741 1250 270452491 270452527
    0x2090307060e011b050f01090b0105030c030c011d04200316030522020d050d0804050d180905061908150109020a02070b0a0302041a04080616080a090204150902 70
    0x1824000b00c00340e400070008240305820140c0e412a00ba111151400308071040042004a161a1008010210861401800410007031244921900c9403618104540c640410340f41c4a42a050f11980c1600b40b00d5003490204100314064194040e80e41c004100e101340400d10210000060891860f50f01c1c45c201503c115280c02071076005080500c0d240c00c111500d86083c4501201c02085204403501421a1000590120300c0e400003e1090050741e2101c40120f80241d2030300c1c080c610a900313544035141240310403141d031000b208410400303046400c000c0105021551000350801005040443d9400c4603082d8020000101d5100070880c1c0e01a44103203408241070510180034040e00d80056141001607040299641e809000d54100408001090400603000b541154010110340380043c04a024481c26a0398a4000d031103441140d000340000250400d120303070710101e40500561681c4006450700680c80d23005080c000800c0340c005d542e5408207240c004444084500070a05040702580c3c50001a2088e04610 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 270454991 1250 270453741 270453749
    0x30c04030b0f150f030304170703150504120804030203070b0f151507110d050109030e130b0108070e0301090503160c06021c030f09020418050d140d02030403021f02090307 75
    0x445000280612209006010000080110fa007207003a1000341e030001e8154440e544c80a410740e501d020000c1c8c400725001c0fa2403404c60b4001c42c0104248940138000d2015200f013101c0090400c0c49807144c035001d09000e075040b103401c54041e01c102c904098a96840c925030348001d07600000d01000c001e0030004051106048804c80d4002a030343d5200ea0011136032000d00b00e01030300308010841c2b2800c0c92104074503195003a68175002030300800280040c0d4000c0c207026001d0001c20803600c0c010001084130030360f07114040c040d02034000d0040e56240340c03580d2402d60450380c9010000142d40e1554070b842e0048003160041001d4402c0507100390701e80c000010f00e460a0642410310750f1101c0c00795081106581902c0c0505441e40e1041520b82c100410040702855059005100380d03840298054600314810700c0c603980c6400814180c62003001201c88849070b003c0103490b00521001480c04072441000341001550054001d550003d109004484607141c0340c8504410140801c04202c414640c00710b01d10800e40750402040c0024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 270456241 1250 270454991 270455011
    0x30b01050f010203040b09030109050d11100603080702090405010b10031407080721150305030702040f1823060c03040606090b090606070507050303041202040506060f0304020d0f08030c04030b 84
    0x22001c104000b079140e0140e8840c14413088000300f02404c40345c60a400600310103074040c0503030394070220002d80a40080166080140f85102e0f8159841c81480b5600c82e5200f926048507070359040c400315030300f0000c0b110001041140c0c03e5484044040c2d85469030340c92044044101e48000c5100f0720544542c000e0342000804d0401004051028042c3c00707604071044a19038103010020104010101e1905400307801d202e400002c1d03503802188008107018010014115091007110140041101d8103203000c16100d081d05124a500e003543c01c0300c4001040385042035401c0100b0308121090032078050381c80c3d0070304c18102e0b04032203144000020881000064422800a00b501c0b41c410014603052178041070407458001c4c452402000001040070600ca410007406000b810000c0480380d41c3d5442e03407260751090b20b6500040b03000d94207150104000e450484295003407001d07041c0c80f090940c2d541d0f0702002488501c1c00000d0b50030640340103500010505000086100c0c44c1042c60300750341e80c0c0ca98a0700050703514000b4000145 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 270457491 1250 270456241 270456259
    0xa0602040f03060b040209331308010e07080c1c06060b0a0206160f080c1306050a09050402070b04020622081c021605093315040605040504050c0c0115030b0105 70
    0x10341c2e2044840514000c1c3c0c030b402c114020410401c4030001144210803000194804940c0c0c0c009e110304503040b2000e85800c18024004d02c81c41d05845030b580c40c9036010305120b68000e598500443e0030f01d0801140c0806e1b01c5842d003843c050309a1115003c80da050340000b40382c04400111140e0140c0c0402c02c10360842e01e008440c2c20a4003250f8001024030001a040074201300d481c83c0414044d1009a0a981c06440d600b10500e05c6141d07a00e1010b0308540c0400c0300c0b0000316142c40c800040a05d80303842940c101580101007400d055445a080180039400b610310800c6100d0003c1c0030010807071240c01e11501520030307070005000d9039589104008040c218911040d04662020008000c81030010072a0800c0350000e0b111500151036001804445030b40d46450301003100382036000040e41260700d888181c1300040a0342c0308070a043c050204203101e48228002d48000c10020801045541403d0340000e50003001150450700786408418810309559031004280031100c6414000c0c0144416152407a0051604035400c41d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 270458741 1250 270457491 270457507
    0x215180603010806040320010e01060302090a02040315020903070f09050708060f0f0907112409030408030f0c01021c020903010605010e031002090411070c03032312040201020a0602040f03060b0402 86
    0x30344d40000030b1004003003044414010015150400d06410040d00c60b400922100044c0038845e4004c2c01c40703105c141d11510300c14000ca02c80c440c4900c211070640342c10506d070b40d0b10004a1744d22074010307500c00e01901342c2606c5130b103034000b510418501c09100903003401a40410203003030540c0000c2140801801c5039101c1c07500c081400c9005c0c1c0c0e5154003070031001c405840740c1d68642d03180701d0240c4580c503210395508514002d01050070303c50030f018540d0982d0b4003d9030080590079125030180540e80d008a0084040d55481001290039284412019014059040f0005032401480041c40d2080403003000c0048055034010030390f0703000703440c1c05e00032400a05000c0c03030315180044c106000284e4440e403080c05481042e90000340031a45886a03000b10781d080084182d010350f01c030018034201303120550070300c03041d00025204280b41703440784030a400b07002d65a01440d644504000114148026511020300200d05510030658040000340c0f0b1030002e0310042607484580d200c500c4c6181400002d468806081c24413691041184403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 270459991 1250 270458741 270458743
    0xf070609050a03030f0908011a181605073e010305160c060f020c0303061212030105060c012c1204030804031b0b0d0213080a03020d030e070302151806030108 69
    0x2c0101c03070305403500183d010781c008400d4800e5101600803411550034042c560700c50a1500840c2d00d1aa44203481c00d52002e200d800701d0182c400340a8411008204005881b5070078030781318001610103a070080803060140712402c812240d03241ea50005101071424000e103800140b0100c500302004201c3c082c05c0901ca01c0c54030070554028500180d207a03800b0301040c01050800d01c80340d0b6209000404400300215030350780b0388000c81a0340381c108455881c07103140f07403606646000c031021504e001c11108070700c5da49045034244010452941c104501c6a0165943c0d98a10400072900c034640400a00030681d070901112140d03643d86051500118550012003401c1008100103800001210200c90b040f070100c074014078a1441081501c0303026413010300800302c00301d02d00c11040c0c402d500030300e8440784118400d08001d07900c2c030311a0346807948000040d016030410300000b02c030b02c0d0080e04064802c00310401983c010391348035800520031140d181101c1d061604c0100d0621840c14064100c0a0344070001c942017411985031442e52 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 270461241 1250 270459991 270460009
    0x10060e0a05091e070329060a15031d060f0108061032030d05280c060b010e190312110a1209050a0e090105070315140604170f07060905 59
    0x143c00c01c0d00880b880c0c10b00e28401441804081c5900101c0392000302c02e0f8142c084000c00780070805008680d19400400c00c5860600c68103001c07100d40000b64807084162203400e60090842d86820011054543c1c1518031502e010b0100906c10203a0540d141155410180114902200108450141801141c0610004c1c9404145034541040310311400e0b8001007011480106000301c802c19501407107030018000507260494003510030007985203249242041544e00c4808484c0405650002180501c50340c0408150160003001118106041c000c07140a4002d0105901c0700103100c5022000005070014020040c0404005998940501d40221003025800d002a141c020f45000104580d000c4080400c00c24010781503c00107103001003c1d00521541c035587c1a050213022035444142d0751801e40001d40e50780c0a48030750104d000800d5141c0e00c1c85400e0500000110004100855005400b4040040d074207901c070076142520043c900c0034241c1554001c1074140b4180c1c2c0364110b542484044002030129840e81050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 270462491 1250 270461241 270461263
    0x15091513020708040e090d05030105090f1e01180b030d090b0c15010603020a0e09010e061009030503070f0309120f060b040e070b0c100b030304170f10060e0a0509 71
    0x60241444030014600009105191000700500c5010400260445e03000c0d0440d40325800765816240700e400c1c0c40030105c500b44400d002c2c8a41c0088000007080d130415903500a56403000003505204a681662082d000591000340d2044d1111801101c1045450009024158043c0c00542c020442c8040d50b480291003d0628024040c14540c0480d0804040300e04004482d450070000c201d2442c55611410020069800b81c0b8007400841c000801c1c120890074840c1045040300e20814005103a030f200d180411840e031003261445400c0003e822008004a6806e00003040303818407441300c0300b40066152a000d000442030707500500c80810003000b6400404c08107800d40c060300c2d50010000604440d6100060002c000c4039804241504c698003020401c000b5010041111724050011201030701c2854500c002900c0d1312400440c0c01d90130610041201800303841410342c2c0b01d006481511311601000c4d080780e20b030044040301d00841d0381e20b5000810a02c10950585a08108407420511140c1741c01f20019603202d148443d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 270463741 1250 270462491 270462499
    0x2040b040909050a140703020907050a0e0f0310050f01030b10180c0309050307030309050709020f070f02211f09050a020d02150a1107060302070f0813090c08150915 72
    0x4482e410040280180c3c5540c5a0040744c03104800c0003040115583d8130716010881c050002030002c00c46a90242086e16480d804503903813107100b10440e005200070b101c503500d4590f8151140c0c41840000a0080c003e440c804d01030200f015549625505040000240c058135110200c0f0952005021524550211100c6a090900003041c0303032441c08800c030700074090f0766405400d07408041004410140d064005c0ea001901074401c860095440d111007030220b118152606405510401c000f500040ca00940f844c0d840e80010188140c16826410a004018029501007210317003040031417181c801d45000e803407140d4902d642c01c01c001000f41c5039075081e602e0205210280c85001d00303010340f000b10758502044d0614080845a03031a12100d8040020749260700d508141c0b401c0d405082c0010610314400d00c00d841e20203810150a09407624a1348504565a00801c0030080c01500d2010104150606000d50002c4034000d681d0365555160280740c00300c03072107143c1e403100344201114002d100c00d000c5102d0b050090094111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 270464991 1250 270463741 270463751
    0x8040602070f080309010c030b0f03070612020906070f0c060503060105090d020a08100f140708010b0d0b0312040801150510030e0a0c030321060b03010b0306060d0510140402040b0409 80
    0x100340b0b1504510a51401014850004200304040c107040d0044415201c40d03071000e00c9940300302c0c4200441080c010078041d0f00359100c0d843c100902031181d00d50f000f59082e42400180340140c0714011800940c0111802d9031540c006030701c0038040050059a6200620f102c1c5402e5045003021400203109110708800c05104425141c10502035551300c0060307100800c81c07882140c00000400d00080050b0140740381c24200e481c039113014a240d941070325070400d210b841140d039920f44a070300b01040b00360260412086d9640517996082ca400c21b41c3c504114801c0b03150705010704540c81c0c0d03107040c0d925825100c01610425a0140c0c00ea000c200584400009840310050360401040220254400501d80300452401619900c1007032400001c1c150407030745008980701d03114a01038108407210180740c00c0e20380030b20444a0301081040100120f001c020003958110390010881403034010381134100340c181c2d603003541c0c3c400810218500410a0700c0100d440840740031401d413010350526103410b110807140d0140e480340301034031381e214 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 270466241 1250 270464991 270464993
    0xf0102031504110d050a051006080609180a0b01030b01180e1c020c061206090708090604020409020d051623060306040b0a0803070309050f091515130611010f06060804060207 76
    0x114207451392062003031010091443c01c00c05440207001c081d6911310400f40c14200200d0b100d40f040603c05c0c03060341c0c0601042031684410321199550044601d1790795541c003c5102103070005d40c00f10f440da4021400b81408400d40d50400e0780a031560f420711090760079581d00e0080024480301001c51400c4211150120114035040340307050603414800206401c0b0b0340140001a20022800c5a58030540100c0c0e044d95004120780d030303d002c107070340c46141524141d92070381c04800003030011714140d0444140148090207a407040305013a5a03003071034000c882c2c0720407a0000c01c040742402034074418140b0b49030001d9640c0c0c3e80162071042a0100f0380034032025040c00c0c0a56160710740c8211035251076000000410440c0d08482d601c40050800030b02041c3e0b01d0055a00c592030b0050103444074900750700500d0140a82c0803082042d615141c04100324422014010140e0082c14041094062800c4503550000c017034a85426035400340d1380800da42142c03003480030800064908901446901d50041109920982c000401139480e80c0d5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 270467491 1250 270466241 270466271
    0x10c030e0a0305100f050403081308040b07030503040b0601090f1404091205030712050606030a0b010c0b0907030506010504020a0f0f02030412060204090f0e0c010e040b03010606020c030f0102031504 87
    0x5011209a08840001c0c4004100540001e400c928249048400c10003480c03c0c00c24201651425100074002950480100c2d106280303900d000958070b48640d174a40c1c82e03e9a80c20340384003650800304056010410100800041c03002d01040e195000c02c003480c0c03d92000c0d08201c984024154140034640003101c2d0007081e00c000741c940b40c1c0917400242d0080d6040303512083d034030b90007800d541c41100d002c0001100f09549401a1919024260007030304010300090560381c9040984000f0070000e0074290412240340c900d0000b1424030304480d4069240390028060080c15070034014500310040c1d0010780288d20411404002030385c0280f55500c81800382c070340100c240d00c100030300328a5401980c00445802294001a000b0844158001c0040b00d046603002c1c4811040b00145038101d654071754030350a481d00001c031910710710341c80341107240a4418001d10020b1084000d4010908650182d008500542d0140c2154405407804019206028501100962844c6444080d16280d504a1004c2038000d5880c0d800c1690881a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 270468741 1250 270467491 270467507
    0x60324030303180d050c1b06070b0114010f020f07030308100906090c0e1002121c050c07060e0d09050907051b0703030e0f060301030206030a180f0204060e010311010c03 74
    0x80014200e94403410709281c40c50f404074003070099628611400e9070300b0074814054030a031201031407550090002d18030141007001c2000030416002d588030504201650000e02510409806840c1d40e00f040240301039900c0c00507003444040d190810a5500c0f02d0807200044030700180c18025658189800891904c0b00380020b907504082c0d0300010085402c02c04003042c8403100340e00c00c0d0361034480380d030344c0c10480720050040c0320b0040d03200450700300141c0204400340038110030f00340200303003200c00c110341403c0c00c40323540100b8000c5420a0799448807902c40002d40105101d0307580075045656030f104000d850f00803034414002c1c094411600c1110701400003440007807042d43c0600c06480705000e0502c00c20522a01050215440d01080d01085003c202c03080e0541d800b500b0a4401649000e9000e01094a10b0f400c58081201c81e03080102500c400c81e8903441e41c110400031417541969054400e0030401c4085481d03104000990b201c5801442201c3d2000300100042143c20040341c00649003802c00c00780c409440d0a0032a00a5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 270469991 1250 270468741 270468811
    0xc0412021c05060a0c0201060515030f070908010213080d322110080105011802070c1e0905010506030402130207030e030d0c0512040e04031409040c0e09060f0603 71
    0x1000740f03010801e64041503008034030800c40e25402045026103400421444034000011120b00704014400aa4049506d030810f54000440c2d0500b050110359407040a82603a120b00c0381c90f00c202c500d8003030401000d0b500f00701443c030300600f0741880051951800d00b14240000100ca43c0980b0841d42641f400e00c616001d07084540c1412940a0390241260101040713007004c00590b05080000051040040c00c604188a000d040c1d4240e500020a580804558000a9000f844042e12400c150707030302c0000c0c040c80c1504101615a070071300e90b84040602c2c4c8000c4000310381d4141d02c03d9018120400402c80140e032224210550314004140c0140c880e000d80c10100e03628028030401c15050b102e103441c26405c0f6a08100e041140501c10b204580c0ca56040d901c180703100740039900c0748101c900546000701d40068041c2981c4200701302c0820440d03007448144000034003660100d007000d070045000c0e0b401d420106d0030400c0350341c6d50010050310100c0c80c006401c00410b40364032000f031580820340c03081ca03101d1520080c490300c2c0c42040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 270471241 1250 270469991 270469993
    0x414011404050a0b0c24070c08300a0e03120a0209100504080c0a0f030803060d0c060e0f010305100e0a020408011d191a0403050d020a090e0c0412021c05 67
    0x3194650709031303039003603404000304002c1440741d80c400600c500070100c05071075a10b00c080318101d0a0b441d581416101d00500e08022104018240a44020b440d20102c1030500c5600c10b84c01083c840c0407400c1c0d40510301c0f41c06007120f540795060800940b031a0800200b2183e4210350f2080301c403442d94420000e58000e01401c40d5056025070031140008405621402420913075003414150b9185100080070020b40350668450001c1c0020100010008200c00001641c1e224034043d00d01d09582c5615580d00c0c90318001500704074045680d512010400e07061a90360540f00503000c0c242040b607418051184170304080e0320311904046015181c002007a140301e6805a800900c180402400440c049142e11025500380c005000d40621548031780046000d07540d4412a0901d80004c155042c030084145c11190030080144160705005040110f1908200f03548020400d851041d66100d00302c038205039140c550100050b28605400605000034083c1101031100c0310f05071b513412118000181e034a000c0300003100100a2014140b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 270472491 1250 270471241 270471259
    0x8150f07120c030b0102190b06040e0307020603010306061526041b030b190203070c140c100e030607030606090b09120717010c0203040e04031101150605120606041401140405 76
    0x266035010341080c0c11a80c406d130240c3e05021000c201e0841c41e03150b100d2005e020180400c02084041c105580300302007948910f02a20718150032900410030342d500a074012140300740e031000100074680812881c1002e44070146803250880c50300c50102910700d03d11140c21100d0a1012010501300402c1c00c404280100305414541802039581c01c0000b9111811a803007007000000440f040c0010010b403084a100f21529203500300c0142e1642c039101100c02e043c400f40a502d209a030412202581c0302d000c010080155581d0382c0d10114180400c0c541403c1000d00094145401d03d40c043c4445600f010001302651844500251a60300d46000240360300b44170f0054501602440a0100e40399402c070216941c4001100000d00250040200403230380d80c855071040040117000c14000c200000c0c8181120760410340c0c1080086000656104910b420080d60740c8001e01040c0d0006106071101410890136501031421120a42403030b20b0040c9884003408422009410002980d10403600700c0301c42030075240035000140c94191 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 270473741 1250 270472491 270472511
    0x15010e030f0f0d02070f080d23120402011205040b130201090b040f1502060f0f04050a02030105010e070306062303041b0f061103070201270801020c0a030908150f0712 73
    0x52502d00f502045030040c005e01602088400003986003000700e49020f00181090940804101c412201181c28200c100d81c0d002d0f048451401050090000c1000d061580e1803e410144005400c40b420b00b481c880c41c1c41e060404000201d28a81105580700c004000317031301d10880c058401259030900d20b41000b584a2230110300442c0c9031a03540003460070303241152002c42444011020a81e50354200310fa120210f50042c00002d09580190f03d611354007d44074500f03c0303400302c0c070301d900190940390242c1041c00207413414820404030507410300448004124a0501a220051140183c86041c1001e0ba4000c41c41d800000460104081120304446074070701c06e0903030110b00e41c94415822601000307105134800a10511905145440080200d585142e816100c1021854610703040b2000d1002c81030010150300002080099000c3c000c2c00100f0360b810100c0c000c0d2900741400d00e8082d0010701c1e0b0350040c3c0c0e04c69014103011610603132030520850300800d01003000c11981d13490040464501055421550312582000c40f104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 270474991 1250 270473741 270473743
    0x309140d0206131e030c0f03030f050a1401031202030717040812182b0f1704052206030f03030509070806130609021801030b04060b01030515010e030f0f 67
    0x31044440e429942030391607000f0711035860804420064842403200b0a8403020003101180604a2446414148690306054030360703040a503140c41066012a84a02c182c14105081c1d00c41c207503122030404000c00002c3d08005c41d0440c0000b05000040404043d10210050a4020401d40300c0807548012503002d030031404100d501d42900b041c41501e520f440703180074031064548004181c0705450a61410514480d180342c0030018840f021076008140704503400084416000096031039100d0038041c03481c08c22039102d03518245261714020740c8510030080041c031050090b48c0c0d81c1c134480700d10740014400c01c040c9184090302c9500200901d03407000344100c180441303240400d60540c01440c42210340406503030a603580c0c0e00200e41c031240102e81c504000320b02d00880340e000814030360011502c2030010b0305503da4820148485000740300300713070030640d078410f00e2500704410410f59028260f1a00b50038030b0300384a00d080c1506032240642400542906200f00324000c1500342d1400c0040e9002c14620800320b03102c25014030181 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 270476241 1250 270474991 270475003
    0x301180c0306061727010902011b0209060108180703030c11010e0102030a110102130f080f0c0d02090a02070b040c090b0108090a1b080f030a0f1106010302060a030914 73
    0x80150142455041451903001e44684401c85003151144c01e006005901c00302d413904401007911282111480c03408181ca681001c02404100504c0000900203440d40009820308035484c16202040f2800c15101006841d643c1e00760350020300031308100ca095100c030101c4010300c88000144541520a1800010034940d200050b03840341030003481c0101c1707924984801190785d10204110300e80543d00c00c001c4510100d200d4860b40c1d004143c20000103040401004101c154021598802081c0705c4203580c050152034401d109210040051800a000c408110404101c2480d4640c1d00a44036240d03210024080002c160120381900341d10112088803454280307032000c10050b040c001c4070b11651a201c04110594015116503014240c45001401c40c8400d581d24078480780300d2a0142118018007590000700300b54100121030204503908041e41e22403010b0740c07004004081c80c005140800c403041c0744503021920041412415240c0540381180d8a1400360425400351034a104024100d009103118000b0f901c10120703030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 270477491 1250 270476241 270476279
    0x90109030b190605330c150f09030406020703020105070c03052a01020304080312070e0a0803180d020f3604020a0e3102090103150f150303031d01020301 67
    0x42204640303d4040c82060b010213900c081100301c1422140301a0558686042030110200c0300321480c051444a0b0346e4209000100030303001c21074480b014001001e00100030103500039000d900950600c1c0c6003400c004d660f10b04500c0042d040c0600002c0c01d07014840502000405140c2140844100001d0000c401c1125886192440c0c02401f0f01c1400050a610220440c0c00301e4501d88010b40c01c10700e0014905c07641c080003030450418841204905845616030300f082000031315469010750f84030840e095090000e480c1da10f80080c401d001203541d030001662030a100104001080e80e450b005040d5030b10034004000228031200c000003050b086090742e61081130303100340d105034401e0b260503203802c2d0384200c4440c0c0c10100307032017113984509251180320f8002a80342101c0031190100c1c16541c5924555004210f60207001e070000d5862914403101d07907610800340e010b09541886560020030414120021107641c0c0446400010201502d8000b400c0e03441070354041d20046954040000c40d501e5940b01c07209034480000e624 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 270478741 1250 270477491 270477541
    0x1215100e091c0516031b12020a0c08010b0a060f0908010e07030302160b040506030408120406021b07030b150a0b0a05190509060301030b070309061b090524090109030b 73
    0x102c00c00b5120350300350350143c00c24403c1d400c044c0e8481c1d9030950300d806180c8040710440400c1542000411280401100b0308240c940142110018a0414194054268004500b01d0303040003035a05080c2c070b0310881d40342150143d24010b8000c10031701d003040300d400c0d806500c45020b56003404480f884040f000708120003101d110b85c00310307203407903841c2c8060610b082c0c1c05100e0110b0070001404200960300b40781b030003564030611920400749454541031085010102c161030503103030194089a00c101c12a0315650505501d440e0304002c0c011985560385601d1520030041201c040c0b8812101d1111154032200348010207003054000c02600c03800e41550081898001c640408401400c150094020303600940850b034403900060800fa11350380c2103072035880e0f5034100035000800301030340c2d0080b09005c14014407070749200e2402c0c01215410700721813010080400500f500450310800304860028011540c5486d00c8034a1401400310546a40300c1c0b00c0142c031120076a0b4030142c81c02418408200d42d03182d072400e400405000d040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 270479991 1250 270478741 270478783
    0x30703060906050a060e12030f0310090209131824050601110a0f15050a0b0a09020901021005040f120f0f1103071106040503011e0b1215100e09 63
    0x303034050042c2d0701c00340300e0b2542048002c41d06010785480340c4242c556890000d060720700d1400540c1030461441c0d0003d03580e040d0010010050100d500145601e0b200140502c003170660403c4040000a0380040c280f11000c004039039070f4071a600c4204489118410f4071604940030710102c0884202c10003810000440c1203403d40d1900000031750b20b6000f100902d10704040d040c001c01e005142643c0d502c1c0d85441080081d98a0600c50041500200309401642e2042e1018400440c105044505118409043e40c002d00ca03201c1c0188503000590364000b99404101d00c00d29070128680d1100c1c185100700c00e401e240050100706101102881c0d07290031083c2c28031b00744040e940fa0039400400c220101c410030501c02c08469181c10401039500800d56140d040c803402c08001f40003074030706030b92680041d08450098400d001d4000b030b43e03800c0ca00408814811410b9072001030722660034007441801c030685c40e602030283c214007118601010600481c0c402c01c0d00c00c050407041442d00014140001015610080361b9050b00c4810440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 270481241 1250 270479991 270479999
    0x105090c03070609060f020c100518010302040501053016110c0a0308091219051b030703020d0614010306050402190311060d15030b060108010f03170703020a02090c03070306 76
    0x107044403c48000d665800f55035802c3c18412078240b11084059021481107a0751942559103d40c4e0b02c40c482c440c2616602c2d600c001c2c81c811894a141c40c201c905c2e041c184103000420499810208944501c440e425004030074102e41600d00c4c00000d01c994500c80a410107000700002004001c1d8800e542c900982c80c1c11a1100d4212040c55444008182d4503801626070041000010b084501400c90094000c1c101c0d020510105003031403030328000250010303d00d074080002034107208044c02407500200c200f15030720155401900c003080d616402c40c48028010540c90003036a050054075407000480500c1c00070103500b40e580d00d080c480c02800f07050303e00340d20583e015085034100d1070100301070301304980c1c0c051319102c1c0310784101e0100070041d040701c0900e8010644441314417a100d0345519400b40554803a03002d100050622100061441005800808035a0044402800031848180a4482603803d2074061990f07440d451404a003020f508990081d048030303041d000d009072210204040d500c10380380342ea0200a09a52 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 270482491 1250 270481241 270481243
    0x90212090307170315030f010c0f0801030f0b130f2d02010c020f1507062a050f0a0c0b090d021603020f060705070308030f0105030c04020406021b040615020105090c03 73
    0xb50340380040c03e11140302201078211404001856211001040d0078001082d007801090030907408031000041c503550f8400030300520360070540b05100603070700d0300e0155842d41c10350f518030200490700385001d404000c4070f0000815654008001da4500759100daa4001c0540c038514106541c142031914848401c1c1c0d8601032442d030b06540c0742c5600800c5405a44071150241550280b010614903100702541000c0060109c041442032540146030a030301c20400055008039006200c26035a104035070101c41051040c0b140d41c40594850142d84a003141c1d2018240c1d2030302c8a03d001e4030943c41800e00140340b08941d03410852410008100d030b84031380403075030241c40f00c010621440807040481d41c04025070001203281c41d09010706081000c0d0800320700c10350032145c507076480e500c59804540040b03a02914000c480801440356050501007903c0754002070f1819414241459030107922050050310071a1580340765040c0240700c3e640e9070884070083c00444c0c00e19000c4501c2003c028043c101c2114101c1d481c0c85604485034150030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 270483741 1250 270482491 270482497
    0xd08040e071b11131802040b010804020306010303030f0912020a0b0105090c071722080d140901030e010906020f0405010e0a080d11011b08011701050f01181103010902120903 76
    0x7103610390308106a5010fa80385960316400349121a0030880131200521001d0942c0300d0300350500c2e01501c10354080c2c1c40c10320420098504000d41607042240050170300006071000954181501d80c1402d01003440c51030f0307440d140001c01e100d0384003508a0b02001150003800341c01040c9071003403c5c01031039003031540d070307210001c0c0030b0030380000d03620301441d00390030442040420722204490704a01040b00189183c415406182c1c40c0c0c80000015540c507a190400c03040048102c01c00108818810714200316007049100140280725010f180070030340c141910740015400c2000e0a5100c066038551003030085403650421040e00c00070b80c0042c000e907030101e805e01e804080c82e483d0906c80d40c4121005078004081454001c002107540e84465800c0b035030990748550b640c0c0c07510105c0c824610b01204850381c89080a40c51325030341a000c0c1352035150058580c0d260800f4454060880a50345040d1407203292103d140d4a542060000180360801818a240704040004118510650000d0440a443c100e02101c0c031380740d64407c00d031644 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 270484991 1250 270483741 270483767
    0x803040f0b0f0a0b0a081e031b01020a020f0a02010509042301090501090605010c080a0e06120103060b130504030c081b0304090203041712010e0406020c0604060c020d030c080a05150d08040e07 84
    0x54400301d618140609401c001d010b11034850f1068a05100100c484c04028000215a270031459401142c1c80180c60340c1000b0303041d41400c0d080014000410180c001070070701d00c6084283ca0040ba00c80e8680d40300300c00020720008a000e0300742146c24856941c0c1011000400c0c081c051002c00e241070100010725076100340b00c009a0030b9080060302c1d151400415040d1540c1c905444000d030482024800001d00c4070b803084a0600031401400b011640c070700490f0406c1348c0348040c440b8280e110b0b480c080c24040401c1d403081c01c1d01d451039800441d4540e43d141c0001100d60107000018010301c0343c840042c0100705214983c010718012845581018803603502403030f121000d03002d11011004803c1401004004101a4044240c0c002c2d016000c014500405203e0190a1403c00c44007a1040c0d44c5401d070f00002d40f40d0411054003410414601007241460600b0024035002d40980310078031190310b4501103a042c403401002c4e402c214000130a00c201c0940f2030700d444d2110f50050300c50800c0140b08400056480e03800b400e2030305014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 270486241 1250 270484991 270484993
    0x6120209010e100929030a0b15160b1305150405010b0a06260106080a020702040b040e010504020922020103090828030e060f01051009030606290405030a0803040f0b0f0a0b0a08 77
    0x6d6616182c090b030040c921296425441181001c561050740180d02c02004002c4500c038040340140c02c58203048110b540050001325056020040e50f80c0451070100e4001c1d040c00113403c404003144c846042490142c64003038015580714026800000740c0c079070024621500d002e01c001030380c0074a004105449410075004d114150114440000082e00e0032101c0d401070102c148018400120322442e003000c02d08075001e00c1103a0305c0e035a550354207200c1546003100300301d6402001d0002c0451005103018a0303070110004000e009050603160302d12001048011029150f1000d81e500d900c9403003c032803440301440e8503084102000480d180803500c0304042408101c0f18410500c1d0b01220740c1c540d10340018440fa0390156030300f140070012112400b000185050203442c00803e03010309012011022061484c40341100380980240465040000700502d44003c503510f400550812102904e075619410700d18900d090307858004212a029108100101d110480000e004212088041101032803079030134030940b112903004031409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 270487491 1250 270486241 270486247
    0x6060307050108040f05010204180b04110a0315050303030c03010e0c03060f0f031c0513170c0405060303040e04030c033f020c071205010509060106120209010e100929 73
    0x2254003404a10b500a17201e10074941310501c4680b5403500b2600584c00189081c01c1c1c642415a413036009000e0b00034054001c65003000610303a250120f41407813040b1190300c0141902d5800e00e40e2a16031010452009040180c2640d66a10380780c00d41c41c200707a0090040409100040c00891281e089584c20b481c07080c1e0300500400342d081d031010100032030b1500c0c01619030303454031910300d1140501e1002d500da0046e0100030f868903504d0300c268814034404d050190b0461900410220388250350403000244603046085e0540e030000f065100e001c082420352065801c8140f00300d00c0e140034002010b51000700550041c0c02541c40411a030404500b0000c100c4c1c4103d11036159115000d08481c40311000700065608108414005151647c4001e09504011444c0d022003c031200083e01081846401e0003855070228500010b030180e581040070140c03030a01d2084d410005103a0201c2c01d0295a40074220104130070400034002c6418801078034004229075000d010707200c0d000c07041c0200441c056019210b148440d0604120340740c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 270488741 1250 270487491 270487499
    0x606010309170703030518030705060a0f090506010803040501080a050103050a020111012009130c020d050a051303230c010e0f0a03120c0b0106260a0b0415061106060307 74
    0x251001c0e40e0240c902c40c04908002c00650190001850114840d403800310f001d1500c03d08428081060f0407107e03020390010080d80c400114082811980450190000120416544464001000d40d030400401c94410300e40045841c8100101400445000740cae2021800c0d9100c0e24048141e0f0005e00c0001c1160744a011007000660051042c2156003880d4030000904207841341d0b4000d035100040486403080d0030b00180c24942410030500321859054100300c2444159540e41c4002d55441c04100c4420400a0109100c1100da1040c3d0449540c440c0520020080c01c1d00d03070a160118094200c15040346020803401c035004601c1c089410301c104d01058480030644040c000c103004000c50090145540300310368203008000590400030307089220a40d40d42d00800c00b2240d20340708513a103e06030083e03824000314403040900380c00b28501076031044c000c1d840703d02500c1e20f81041d00300252080000c0c5980c050306012031000c0780b42e0842006001c03200c88e030f81c845c15042c229031901502c0704425120345400da000040140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 270489991 1250 270488741 270488747
    0xc05041403030a21090206041401020f010c08071b06020d02091806060405060f0c01020307050903070e1003080a1142010e060d0807120e061908090a050a0b04030818060601 75
    0x40070300710744e80f00c010903d00c15683c0020394039803064010f5008801141507121b66560f040000c20034030000385008014032400d270400901010f000030411340c20030a03003a200140540c00c080740181543d9002c58159191144454490003941104501900420051140082103141000c4290182c80050301e054601420a01840625400407051190344401003000e512086402d100440c401c82e01c81c0d460b81d0f2030b86052000c050500c1c9480d844461300d160314005104682104c540d01c3d408170b80c0d00c07880300b540d00d8607250400d490003008002003031214000d41e00c00c20300010f004a20200c510501c1e01d40245030325151104114820080c0c99a810315000321401803100215103042c454102c0b00003000442044a19903a03400715a014503400c03156411a000d01035002c540142038900400411194941030003084000c3c60000c541015604003003007444000b141207400705009070504107400c042921444000e82c00c001140403801d80302180082d4032400041c2c440d4415103c84041d5115240180c601d9855080c011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 270491241 1250 270489991 270490037
    0x50a020f2b1a070e061e070b0103030e09010e061c060c020c010305010f0b09060904020412110a060f0f0c03090506040b0712030b0a17070504090b07170c0405041104090c05041403030a 80
    0x2426109041c1d0700d41c43c1010b1b614002030107913107120b20b68080745503040d4940205403402951115004000c0240140321003407001243d150300c808150381c080450b420b500000c03810b08101e0742c009000743c1e10304518142d0b00c640c0404c004d1811102030f00c091005984c1c604c0351040f40c0d03a85104581c0701c20341c1031107a000c20780303000402422180c0c8004d001508054035182680c500154403081290049030038260b02d2400d0404450300401000c16040070140152084409000c801d1505858030400c0290108981050f0149401602404024140d50b49590b20b609241b615540800000e54250390b040c8100310302d081c0f09000320752144c139000c0c1c509200e151411401d940ba803950102000c5050188800c0400e10340c54520a140c0024010401440207060001c800350184d00c00c0c56151002c407013103a04003e007015134582110102c0360103560000d460450340410b6010340c083c0e41c000c00d1a0390b080ca41412a042e84c0507010700251110814034012a8107200300305541ca2052401c8800030031105a0350040c030200d00014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 270492491 1250 270491241 270491257
    0xa030b01080915040c1a0403200904020603060328030e040605010905013b011d010518030109060e15010608040f030e0d060606020f10020304050a020f2b1a070e06 71
    0x342455054558406d1054501030154281c0d052002040070000e12590518030410b40000514241619131107001084500c0e0700204080c2c003500d0000040341180d1820404580100c1c401203800010b40340036111051840000c403015000143d80805504251400c0d200702022518141c640b0065181f4040054410820300340524a402c900350720b600d40c800d920313000c1d0444108004060041502582e42c0058568400310f401c260725035078000f124403045d0340c0020031184005100404924444110310000340074000880b00113041605100d11800c07540d0340010100c0801145043e0500ca030780e2164002c4a024804880240190040c4a50400420b005040d20026040050300a419201c0c0c00c1c0ca80806070b8446a2056006a00c10003c0742c40c45007003803003036080707201030304805620718286a100c2d40e03503952a042c000792080a80c100321003c581d945080510000321284100030f0007846840b5011034204400304181c03020441d54821000718141e00158a01c6541305171a50b02e902e1382600180005900581e403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 270493741 1250 270492491 270492503
    0xe0a1206180b151809060c0d020c07030b040606121505150303070b180c01120c05120a090c0501052107020f0102220f05280f08030a030b0108091504 65
    0x640801068081416900c0f50100c00e0401c07909072080c0061240c0e002c85184081005141c038028048403c2010503115000140030300c0c40350f103070350a0000c4940284074002c3c5441003885240c03400010807100601030b038442e0b406140e0402401d607507543c00c1007400d20341e0701000b0500390800c0000e86038482107501242c1c0015181c40e010307054612000100b0700c0c6501842e0309544a0301103400b0840110141c4000c10030f444c900c000982010869480040d2258040e0144140c540c0c1d16100a403140c07601c0346d0242c1e02c403a00034880c0300941d82424a80c14004020b10300060707a0319105c0000c01b050380d502400858400b1403920464690000301d8000403000c0c4030700a062003085004040c1c0c01e0007031880c240054086075060b00c161140d100c0450b00d41e80600354543c1c3c01004030440000e030410169450220050f00100c801c000d900031800c208046550f0005150080406030740d0700540440c01000006c054201107101d038038104a840310050055417a4801120b01f2080d0343d10000910b07a0808004003149d23002031142d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 270494991 1250 270493741 270493781
    0x30d020a081611090c0d05150310050c0904110a09050312031306091209080f0601080a0b070e2d0d05030a050a120501060c1a010b0306011103070605070201020301060e0a1206 76
    0x3c0000345421010b4034140182d0f0b6011440345910800e6110f020f400403d86007410800180210100b61a81203000a1070011a0f441c40010825441003080300c4082000034405c01076001142c4104806801c110f2031030300041d00002c1c002c02e503030a0028080e40307040d21640c056411a940c201902e1500140d007c000c60322a61202245000200e01d2038040e49240c04030340b50038040754100256285400040d4076031800703552008004106140c4081001d030701841d0000d13440640355079000b40642c1c100c0500d00c001900301180b00c2c0c030880e00724482c09208802c0342030041813a1882280d1820043d544003001e001400c245c001704400f80509009100034525919542040d0102c00f0724105500104c40d402d80c0b1103404140080a40e908001800d10030400308a88100810110b50600710040041e000060280e41481001100ba126050041050b00c8039103038412008d0040b0324103008000d000c2d41080c4217207004102c50720045000f900d004112982560041c9140c02c1243c030081e215240500001401c4a10003d030103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 270496241 1250 270494991 270495023
    0x20d0213090b091911010e030f07060f0e012f01060f090902152d120901060513091e0201140301080c0906060a021c050c0714030d020a0816 61
    0xd0041c201c10303502a0506100c540340000400d810500c0e082a101d08140d9100002c10002c2c00e07070700f5812000007082c60307c004019002c002203807500c05c224941c019244100700000494692180604c41b540c940303641d0f681c00b001450340043d203030218140040e041400d03442e4202021039012031045114002034100100e005070351500c4040c030703080194100b0240c20307443d4134408041d401d0200c034140014506e1461320b89459030b01a030072010751100b210904241810148a010994504002e59807000011010713050a07040241242c0c0c002c110364412103001d60620000040965041d1282e000081d030000360b016040d11001c21001c100071030007030007203040c02411180100880c9600001e940600303103240052039201000010001c004400a00c0c00c0d1140c0703420400100d80d294085420b146090070000034080d035448080e0191558000e00300c0c5a02e0a208542d0001903541107180c0d09000c0d003506405a804000541108a880d4508488054000701d0200020188265141066403100e80180480d10144c081 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 270497491 1250 270496241 270496279
    0x6060c03080907171b06040e0c09010903210206060a0f0308131e0e0604051303030e0a02031903090801051005010f02030f0f070b061f05090402090306040c0609090b010c020d02 77
    0x340701e140700b0b04d99001850588801d801c144251840c074400310786a505141c50642904068003008100c40644500460b40e075400d64040d0000001a41c0d10907821040b100c18400c3c01c501141950350707050014494000461110300f84205d50784240d0342d0b8040c841018a04588900b02c2d0795100c5140d03c00b200300740c0c14001444041318180c4d0b043c080c1e1022181807100c0d25010039600340d0070010f040c291140e031a2009020300001a4408600744c903501d0305022881c1c041c0c0060907410030000d507102a40501642c0074042d020034680712941c8600e40700352150300a8946903110745088580445070103100780d80f0301034240a03d6000b500c141010605d184126031a26421140005294100c0590b100102d8001b080f650200511001e080e0f6004804fc2c50000742091038410740c5c0310302c1d48414102828410300042141d1203468580484520b10741c0a001c44050b4182441c20b0b00e000022840b4030300010b284400085150171440c0603051071250145d40d0840c040556800b041014070001c0b00807644401918110151500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 270498741 1250 270497491 270497519
    0x6181002010204061205010f05131d01020903010e1b09100f06020106050f030a050c09100b0309030a020d050403050c01050906070b0f0426030a0f0b06030906070e0406060c03080907 79
    0x41036001680b242e10b4120058100c3c0d00220960f000039003410014040d180001d68190100c5404a0700d50880c80072040c010341c02042c00c8140d0910800800700c4801d010380054008100d031241c150000c010ba370880c1c000d4261100e102c860070300c220300d8020034680b02030720f810859550000100010101441d990f1040201a0501c9500007400351f510b49908004500e08908480704007101940a07104224103940c07015214800c0084c80c0d4420031806011030000c55401198801034226880200d69a041451846a40742c115032010740051290b0000e0780345a0348074106540890350b000f402010303480d80c40320055920383c01000100b2f400000c14402d410200d1903403000f181c015226500c03003c0d40c03818031742044012092030200301480c920070158071801640c54202200e0b44490030590000318414100c01c0a801380a05a481a03480200442032000d61746003c00d00c10b0152034580c5820360f08130b0b50042844103482031841902c000c203844031801004a8060103446501c818070300165982140c4030f2813041450300d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 270499991 1250 270498741 270498769
    0x120614040318120206030f0a180b06100306080316020316090b0f04020a0f0804050c10020601140a2d0e10061107080303010b0d1b03020309150c090618 66
    0x2580c044000800e010744002d0314005000d0750b0290811406031a004504241300c090400c030350b00d03881940000c98841450740008510040219188506000c2d4101f42c05198000e42d280e41c400c28070a40007240842c000c1c03040b001103481c81c82c05141020341c4541c066841c5038005109a03050701a140d00d0184661040c031141e401780070903c2e800a0042e81a41c10b02c60252501000300d40034920420400d502c07103811062445400b4528a800d908980d52807610300d040018102100d80c1041e180b8034142c0070742d50040740f064103030344100040011200c201020445441050300c00c020300100740b450381c0c41c0d00881d400c000d61003601d2035410017004076076681d11701c07000c5020032110481da1071481481030188582c010441e01c00c01c90050010715006040c801700780d40300c0c4018890001816800111000008196042400300e032100c03144801503c5c06485010b40070b540700701d03440d0b1110701a40c3c0c20301222130036201c0d202c0e02440300b01c064641089415010720500d94080c011540e80e4241c070b81c0c0440c00c955201e010a410304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 270501241 1250 270499991 270499997
    0x51b0a050f0d020c06070e01020c0d030203070f03080609070c0c09180b07020c0118081b01180e070906020a030801210203060414010c020703050c100909020d06050a120c1206140403 79
    0x610243c0401350920501514420400021000c0d88070181c2c0c2c001054012804103c41d4000c4010807440d040e4654032500718010556048190004241900700d042207100320030607200c4074155540c03420102d0302c48080c10802080d541221805100070382c031075400900810142189402506915150543c1d010790840d020750042e40640d0034012696403000e16141c0101d081940f000f0118140740c2c1107501d0310750703502caa401e6841c1d42e80ca0b9140d09a00c0341050040c0003031005503050090b41c95102d440c1005004886500124900e5000051100d100142c0c504003d9096520070046900308501e8200c0000545003031070342d28011941e9100581d405111903806580700e006d8114807410904e036083d0a40b001c0d0343c035910030354212001c20808101c0114000304804800c41c0d007554020078404c0c1c00d50b448070ba150844d00c625480810700402e10a801d50007042503810032160341c1112a6a4400009a0781210078014500140b42c0000c100e007184806807400b01c1780c40b5001c041203c8140b00c0e805900c10f9002c6400b5000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 270502491 1250 270501241 270501247
    0xd05010504111c020a1e0806030d08070e0f0f06040608041103070803030109090606091a040e07180905100908031e0c03040b06030a0506090d0909051b0a050f0d02 71
    0x60785418402c01d40340031601148582048200c50203140c03002003030394142d08490340005400524a2103816022504482203012604040103d1030003010080700f100c21902074801c280004500a0080b009244984000d80c1c40c200000d5111080c4803501c0c1e080c0c00d0b4183c101c04006800c003801e650704c0c07000e400a465681e5450ba40c0746481d0174010802c00b00340d5107180c0282c00c034040c203002d40c0340040110f9064800c0100049682c2c030750703440d01d4001402c403a40300b0082c1f10718145400084d603e0001d040d00c8e04035001c580c140020750420061b02c0d158040707885000f01c0c80005c3c1d403000903440b4407030300b10600c540d005038196502000011403032019079070103500459050b00b0010800c100105440342c0b9440100340d8040c42c60580ca408404c0600504c0050f0000e0181700c602c10000d8400e81e010400100d090764031409440c03103424a4050140d9843c414020000450600c540c0440c001c2010b1064038459010070903442c2c1d09400b1208404256403000c0d01900400c10104000e03000c140e2000f00804c4051454400183c3d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 270503597 1106 270502491 270502499
    0xa06080708150a12030305060405061c03050d06061806090e010306110705070e16020105040831080a11010e13150911030103050d020715080601050f0d0501 68
    0x54001070a20001c54212600b20039181e41398400d407030510140d1030340d00c02c00c01510011108550004d030300300d00c1410b50303101c80c40c0d9003034049000703040851408410084100660b0300c6038002c4804940808607058184409281a1004119030300e0f0000780e15003444002c0844010601c07000d001540c07142829202e1480400c221510280e01000300c540e01ca9803841d483da01d81d001110310928441c043c03041440070500601a035807149501090741d5152015040312210b0140c1008581210b80c941908060200044404400301030b200307420050090b44c1e07440c5081d8180c01c105072220341c10020106416030702c50f21a1180840e200c06014004110300b00040150500784541d6070000d44254103105030004200b409100a505070b0f4020000d175031341c44610103801d0f40d44403c240704204409221072081640706124801c0d96801440500d040c034505039148010380390a41020901d020240d6803800104 = true := by decide +kernel

theorem cover : BRFrame.Cov 270323741 270503597 := by
  have h0 := BRFrame.cov_init 270323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 270323741 ≤ n) (h2 : n < 270503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
