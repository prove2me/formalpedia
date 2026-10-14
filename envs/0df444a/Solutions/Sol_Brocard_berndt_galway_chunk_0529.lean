-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0529
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:16:42.925929+00:00
-- url     : https://prove2.me/submissions/e328bca5-d405-407b-8cbf-540b903ea3ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 94964029 ≤ n < 95143885 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 94965279 1250 94964029 94964039
    0x1e0f050d0f05190803180d0c080d090206120402100806061e040302030d050421110f040605031c0809060601081b0d060902190306050618031f0507020d09030c 69
    0x14507840d4428814400c8800c10f41084418011080c0c10041c2110450800028002d8807540f0b15164041078111070090000701c030205038050203601c0c040c1002000c8800108036000c4e03003906070f0b100c0418980c006c1d014569030340c120488041020002c9504a110b2410300e241d40304560701c41d141c114803440e0050995450502d884411485407445054042d0a2038400c11002c001610305101040c002180b60301c0d81a1524107049500071a409104489000007241d0500320001c0b49070741c0056283c100c2c06880d01c1041c090a100441c014140d02d4020300d80521510544c0411420074200e00100c00c0c19a80d101003035511105140364071102c09941d0b83d40080e11490115400c442079043c915406d03000c480945107846040307091402625440d03130295010b26400700f20200d08160140d220440400301c2e2508000a40c241070004c1c3c500e0007901c400d03020801c41c14440d076507207071020032064509525983c9059080224a2044006403908880300c0005004180306181d1860280e40d14006403544540441c0d4130343c0c100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 94966529 1250 94965279 94965293
    0x101104120204020c0a0606030218100603050903070f050c0f060c0703111c03021c0507030914030f0303090615030d0804060f06031a0912120103020d02030a0c1e0f050d 73
    0x144401d0341e01940c200401d900c0620f007040100130441c40340c0008a244d034914010008070030100b00b0007041d100070030070400040302c5400c0c1d20702e82a10f00d03078100041d160312580c008078590300440100030503025900d203801c01070180c005a07441d0030082c00ca81c60000c44800c041400031a000c1d81d0018015580601014800241e14601324038015001a01003001c101165000b1210390007820340c2500942c100d4072406001e40c40b0300c0f41105400c08942080c500e0304840395002424029548160303040464551803d2600e960144000d2a01c030701d89004032600ca0a081d20842d40b150410340c1e2074044c524260408d41118180032901804188140c2c072040b07802c0d42c8a8030342030080d1140c0c4144140440d034860004c8000b40c060080300322107110f6400e402c0014507020002526004e90421040c0302c102061088088002e504800c1c3e6040d80e07810b80e1800c854034141c1c80031030301e0301500c240018803603500380740041540c0841e00c07005444240d2301c0b81001d0415544001080165480d8002c040d00104941c2c849008030b02da0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 94967779 1250 94966529 94966559
    0x50702060403020405042402090a0501030207080a0320040b09040507020706050d090f02060304050a020117061c08040b040b07060c0e0f040525020a0203010b0a06080402010f050f0f0a02101104 84
    0x3602904000190a87d40c03000800301a0100c0c2c68280c0c0c0480d122825080c0042200090402802e003185046455110840d4170702420f01944105a04c65044440b41c0310710740d40f40310036400c03c0d5210b10b440300d071180504003d5421010200e4029413a00e0b000801241c4001016400c03103c450300c1d82d41c9003004030303400c8001400d110351056811400e8802590700503114080198841c5005801500c007106151000500303440c0c06003941c1101551020910807150b032a03607460000c02d181c02000710380841071850294014040c942c0401c0802d0ba01150019045a00c00c0050034110312509040140d114014000d0701c0351f40d0b800c08901d800c502d010050418508260748a240c00c18090b03000c110303201d1700d801d9140d1076010302140d501c0d0060f0040e420b64000c6082c01d0044582190088440d441443e080680050285000a1000c1d04011010721030303107400c074080c000b1540280d0043c900f4543e50000c412003a491503024003001c8006200c0c604c0e00844c44034461141d028485801c2035032134034041c80c065142c103034680 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 94969029 1250 94967779 94967783
    0x8090106030c060f17040206030c1605010906090c0b0c0601090c0e0a0303031508010203040b071404030501090b010f061106070e01020c0409060504060513052505091e01050105070206040302040504 86
    0x9640c0c0e0300840810b104103980c0000301910341c4c0301403c42014500007000e04007140d01042c43c4100704028040180d032405c040d00c1e07202c0c101901e1161030340b02041104d10f41c4c0251820241895103421218824045940c002c140c21500400504c0226640c4070410001381c490011803010a8003c1001400503c00d035804c0b90000816915005101e1000322000502c0310b040c96008a0103c2d80d00c00700307442c90904c810300140052400030000c60075403409413910202e00d24000c2c1813904100281e50b0911a10030800142c802468000d00208925000c1e4505015130704400e000c1c0503511504248001500c40c840d410045403100c1c00360180009440340704058a40d00800a20340d07055001c1d88414000c40e480300c0c0700c1c1c0c51395940140e601095a06290a2680c200c80380a4402c4c00000c0100b0303103c1001c40c20000d4001b00707020340b03003030106200403001218280141c8145c0015500c4840c40d407d000d0480e44400948120500e01d242c40d001c0d03130b640d80006488501c241c400003074000e14140f00410144c50181e1155078458 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 94970279 1250 94969029 94969031
    0x3040c0303031a0301020c0d1103040b030105040908040b041205011506021c0221030417040b0a05070c09180c050103200d0204150c0c05040504031403070c1709031b10080901 76
    0x1400000003c5d0982c0c00c1100c409407035174030460040c14090342c82071031070b4184c1031440d002e1858a401c14252044601c41400346602850b202e2045100700480340c0d00311001001c4030f01c00b40d0307215610340e14041038a200d00c0c641941c65609224000070300154002113181110b43c81d030004d200d450100c14500c000c90305131111140960040422074101c0d03c0319114003503004048a54a1a034a2505140120380c402d12a500c01955000502040c00300511080461750308240e1800c1c000d4481e5881d00c1c0024551185030040f10b00366052540c040300c252034981400b100c0c035120f80c0b40400002e884400442c12110304d10300906001180c51007c0c14020034500003006601d8154102502d42034884407101c460103052030910001030488000b4000b03101e0444080000741c142101e00b4092410326445c01804030b1130f00d0300041c05400000010901c00ca006000d4040c110b940b16510801151100f5a1003110790001080d00c0d0103800b034070303c5110701302c07040000d4440f400000905988568a0036141210140701c0144800025 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 94971529 1250 94970279 94970321
    0xe0f01030b130507170f0103030e010c050307020612010306051302060f16050d0c021207051e030309101101060e0f130c0f0e040311031602011805151e03040c030303 72
    0x10040d9000e0640314413566129890006407950208031026802483c290448403100010300002c0c4d8440c2040104980c01d1800349284051810000e085104035000254813160000d551195000036200f2035048900522003003080340d460300c45a01122080400c001c0d8080c02c1080b092424a136500f000e0528041104014030b1046030542c2c46918042560703204002148a80c0050070071498481c1c20341940c0c10b102000303801c003540707460301043e445a50380e460090075a01501d500b19007a201003050700c01e030f04001882241180060b1101410401e8111040c103240d50070320402244490144040c0c80c090060f41c040040d45070781d201c0140d00d040c8455003048403034525030400040ca400c1c10000800162110901c800440e00701450064000c3c110b03155042d0040d0002d000f050030b0070040300e100d43c203003940a09045500816140303101140c9012034000c603504c60481d071020381d810780482d03019001107100000094030b51402c030854a043c90004503001420741e42d00c50414400207109801a0b2001d0030410596170078 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 94972779 1250 94971529 94971559
    0x1006021507030c0c021207140a150c060e1006050102100e03120406060807090b04050a0501080a0b0c0d0f0204090b01030207150e07030b0403080a0c0503060d0611040506040b0301030308070e0f01030b 87
    0x40300441d8900f60b206c0b68450030090200c60341100301580400d00c111884008546404000004042c8003c3c80a090003480044074050200d40d421172003400440c4416607200e0f10500320032000401060007080d0051058510304864015584618201d2010300380095040101a00c4c1f491101c4030010012170b0141d48500001403454800c1003041c0c06040c6501d00032503621142d00c107000c1144c00041a2184050030107004220306500440c010907003a812200d8808151780d005c0841486208200581307890500c0c0480ca8400e80e806039018000360340c1404c006014808030000110103a026000020745201703091041c0351007109050f07100c0e8404521020981d2000d40d80d030340714001b81040480c0c00f0350111702484200108200e03144900f103150701c00b60801500314200100800c03070144010070b0042c42c0a681e0210200782c04c0c071010a54000b094010700d203503a910303116910840a86c01c00c3c03000324007003071110011688260248026070802000640040f6003a01e50200460290458800341504100d03200400e0072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 94974029 1250 94972779 94972789
    0xc040f05090a180b04110a0e0a050a0b0a0b090a0905010b03180c041109131a01050a020a0f14060703020301050612060609040f0606021e0a0212030415081006021507030c0c02 76
    0x408134002c2000f01103614050602080c3c501045400d14450021600c0c144400c10313091003c00d800a07070141c2c00140e95a40d00c2c0c7c581d0002d000084050707901c4003414034001143c510460090030200300585030041102e55a000d45000d40d40c00b030140403503822003400000d0000710400712002561180600f2180940c0340c1e6404a000c554002c41b03241506400001d046449040c907101d09541000004001c00c80c124401000413481030f41c450303030316040010008001108901c204a5841d001e60001250002e00c901c5143c00c0c20060280619020580152000139900a01a1095138100c5a01034092481e202115403a0208200002c0070264014024400c4d440e003034a85110329005c0c44000720340000c8950902d88040c1c075217294454000f807860704001008244507070218105450729810b50b44d000301e021600b4099811805560000ea00302803110560071b0701c0e0b50340300c0f038640d00500d842c6c00c4e5611240d1b110801242c0702c203030400a070000808003a0124904034842d50181c40e00e6101450121040790303481d40014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 94975279 1250 94974029 94974071
    0x70b090703060b0612180f060c030403080601090f030221010203070201090605060a051e060f030705040501030605090705190e1306031520090402090d06090b0c040f05090a 75
    0x146580100c1060042102d1403240f680d4040c4115981c40c1044c4d1629851308028034002d1019614100b107030b0011400407410810705100012690a403007251614206112a54200f10340070f0f00050a280d000c11203e5014045a000b45e030f0700e2080e8810700750305580901800441403034411100420310003400c0c08221007032000d18011481940085140d48143c00c080302542c030054419407007070520701402c0010ba61001102c803080c2c1c0c019200038000e55a06c40002d1014002e000c00c4005c140000010081d10b2544480100160380098a08120311900c440034405602000c5500720040b50701002404421082c4d80050243c1c40a2884c0c50301c0300c0581c880100c1c880d444035003800f9480320740302d030014400c114031408150302d458030a15081000d020703803d0b00c40501c1e591224040d214104d00082d2240b454071507404a4000d0600508141d8850501d45403800007011622820345900401c030010a01c2045002c0803202195003005100300c1540c1070408002c00302c08040c2410310315a54403094100384036908020a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 94976529 1250 94975279 94975291
    0x3030c0210060308070201020f1605010c020f0303030106120c05091c050111040801021e0c0706080a09020904140c0306060135040c150306030c091e1d1009120e06070b 73
    0x43d5298145c0e80f001928289030610000350035002810031444120b82c8140f854110750003482c140940c0790560011507520700040c2c0c08a501800008000324855400451a8a1500900c80300304006005135004a40e00c0c0545203405034000f621a101c100c200c07510012800e8094000c0000003082c00c3c5661382290240d00c0340d0b00c40110750350040791441d500b151210801142e0030400c02d07000d00c4d101900c42240d887d100b680c000c1000f0b02200902085004915501c4141000e0b4003910b01c070040d00701800d1108a0705e440c04e00704c007050701c07401c01d217400e0038280465050300504c1c4c1a103440121520003146c5941c010464010b10710074070f5140f1a40c9103281c1207610b90900035806854031010f0b03103003081380348101e2203a0f44140c10185803c0101c1040024544040c1c5030840e900381e0302c005000280c1002c50741000000703400c0308030620f081c0045d040404908400c1d5590b4414103400300c034990544600202c0903070300705250180101941c10015400d05014509958040800070440d5181400e980e5545004c00425645 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 94977779 1250 94976529 94976543
    0x903030507030b030f0a0206070c080604080403020901050f0a030206090d05010908040305010b030604080f0906070203010c0e01023c15010e150a03080a03091106040617011a040303030c02100603 85
    0x7404480380d0540301c0d0031500803095002d0f001d45510b40c48815900e2482d01c5000340500300c000740140610020848440c05802c01c40180e51107030500d8103000c0541d410500085c4d10800b040800000c40389001c4007046002c0b100540b2980080d0301c3c503000c020b00d0760080805540c00004580810000880a00c035100202d0b1044030119140c0d82541405401c55451242c154000d601510a20003ca8642420f845034040c4082240340d07140005000f040b0795004d08040250190b080000c0300589035000f00b42852030131401c2c0e080f07505914240b6403046100010600d044420b0400e49988101440800082c8181100d500b044034082001201030341d484c03c109910000b9000140000c1c02044088050304080c000001c940103142982507468210b8a03114180c821028540d46004007400c2003184900407445410091816032100d9440c903014208544000c100d008400030607001103415404004501d0b00c2118980740141001d0840e0350680042540200000035071040c000b0801030b10006000c2c00026500c10a9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 94979029 1250 94977779 94977781
    0x5240f07080c12030609150d020901090507080912070201050c01020433020a0b2409270a0f170706020a09030201080a290d120206010303090e0403090504020f0c0109030305 75
    0x40e5660500c0da9603000b50143c0b03501041406003503503942d24140e4000424024101581c00d0f0f50001442000c00000f00942244e0580e0000400034aa54800e80c881c2c0703419140c900c026a6611062915107036401e88071844100c050126202651040020340a100c01c1c1e0301c001841c2c56216004120710306880009401c686000c03a10b071304407084a00d030304603a284803280004c0540444558451510704002444082c100e100509004c50402104c4d4003c44812030103030084040741040712454030110815603402121081c030606400580d940040e84a44480d04039414094400c0740d0fa0b0740c0f054140c080d40103498408010301000c00031807941e100030310041c00b00d620f84880040c175601c005815040d004051768000e500d85441007810824601f01840c1444180502d9100a0b07039040000e02c0e00a80024084e000300c117010b0413a4801c0380c0019003981601e0190f11011a440d58890b03e07807082034812500140001c8000c402000b05007000e4001e0328185004400190910500480c694215142540b0942c0000e13100c1d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 94980279 1250 94979029 94979047
    0x14090402040324060e04120c140106050f01020c060a0f02030712080411010302070b0f06040207140f16081b1c030e010806180f1f030f0c090605240f0708 67
    0x43ca4281d002205410180502440c1079842200800010006084a04e0b03d82d0300d500240e1080a02000e20b0354030982914800120000f464004c050502500307020b1080c084a140c210360000405880161009000c14a40000084226a1a01c1c40205c0c28150b00c03050280e41c002482d640110b04002699031307903a441a19003800d128400b1400840200e062610400ca0080451021004298050000820405a074958001082c003e04c070700310000e01050303280f81c1c01130310f88403001c21140b007002403110480703003071003140c0c2040407158030240710740c408540c000c002e1510340179800208940d04100050507071180101c52a2007100b41101440124001011480c0d046019138001a543e0340180066500008003440702031060742c014400b6000d27a80c00c03421b08002800916100180013440c113421100f00c20100c1d500d281c000d07140346105004a48480705002d000c07415804030322680c021178500500300031180038490b10175061051100d404840c0b0f00300030082d600c3c6c910004401448164404c0c1c0c8c0c16940d845410b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 94981529 1250 94980279 94980323
    0xe030609060f1303020312040215070c05130509150c09040608010b01020d090f0302090406090c03030c05060f0601080103030509030703080c0706090b070503030103170d052d06060406140904020403 86
    0x5003c00010344400305842c001c26400030680c1d11030328404801c1a20354a840c00069003c04e410042041826400a00341040081510541d0100c1384140c40e050000c0080001c404243c640840f2604000d901c90507600c01040100c1d002030740c20030380c0c0320700c444d103881540c0010409070343c0142c00641e40c40e03450315800d94a550f410031005000c040380d464a40101d501b80f07000a030506285100107441481260302041c1844010382c8000500340d8440c40c0031416a40d61b00e000303024040703401800d031a140240c00000f481c4401590f002803082c0016540d0144984c00d59405a650b0f41019401c2c039018811038001000182c4020001d200410200c401401202e180181c01000c00c0074a0700302c2d20440a081c0301540c005040003081d241580e61042e200d04a00515550003103050180fa01ca003a48a41002c0070b012170041004802d10781050000310f000c65a1820681840e0402002c0e5117032a01300b0b00402081200901c98000703c074010340c05d502d0b580c1c0342189040c00102a07801a800644000e1010460180710841c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 94982779 1250 94981529 94981531
    0x31303110f0112020a03022106010909020c0a150b1810080a050c010509270103030e0303030402030a020111010605180a0e060f061003060b03040c030507080f1209010e030609060f 78
    0x111015014080d2810008084400c00d090f1000420b401240c0b81504034081c0d01030700c1c0480ca04200890000020309040400034130241c0320140030462000c030104402d003082c002c88806510b204018041c84900d03a03540711541d4828121144059540c1c54402c40703950342c0700d05000c2c0b60b81d034011880e8450704120301070112050b41544a1340265010303580890000d1808107000f000100c0908180b0744030310781305020071469074020b8540d100d0080250b442d460107103030a81405040c2c030701070b9898010305081003060690f240700503140039505602401a040056228016060050000e400017241e0325640c0c00200f881000041c12200d01c250015041018810507840ce094000d007503000180080d00b0310501d0007100f00d1000d400c80b402840500703805100f00d402900400018101104415078a140034200041031070410b0004440f40d0040c480c0000390007030001103550030900030a026000301c00801c0300c032002c02da1280c60080d041c0b0840501d80c29560790140509842403c0c5203000e468185040c1140815000d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 94984029 1250 94982779 94982813
    0x717040c090c05131403030415020f06060a1d1909030c1a06090403080406140108010e07050a181a04050f0708011a0901230a030f0f11071205040503031303 68
    0x3c02070002c0b06420000303520030403c0300e035200c014103000185440464258881c40c1c06c00000d081181c1300e9504aa0340c002020b401405914082d40c00035110f080070402980002d20600c0748012581d0010080751402c0d1560a40100c200149440d8100b00d018980c0181d4512070f1081e000b0460704461041440050b48800d811000c1014284d0358918090000840700000503201400700980b000c0000d00708560340c0c0c03102c140c61180d014401039541e51740100318040d0101e05032440c0d5501840c14001040c1c00c0c010910419500140718800700f1a1b0b000384100010b02c2c4810031030000301403500c20708869440b42c0c0f080d5405042d688081c041c161a203501e0190803001d040e4811421440340c0041d10113070b50200b40959003c2842440c290042c12100c01d01040c201e550300e05032501d21f19000400544aa405a01050101c5800c480c00d10503408880e40b6141200d01c804c0302c2c0f1000b030b60100510f0b4009150843c1106c02034031710342000b9007425202d0740448c0c950380181c1002528510044c0f0705109008541503140300c124 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 94985279 1250 94984029 94984037
    0xc0b120f060d120203070c09060513050f07030207030e0d03080106180609090504030203090411090301061d04020607080c16050405132d0f050703120504030503040605030717040c090c 80
    0x41407950102da210300b40590054039040008046a540341d20078411034800c203030840520f10310203840b05018002840613202d20f510980c49000c050800d014070b4043d162280811800c0707a1125651224241c01960050100301c4c200007000c0e8090070315074bd44024410100d0b0184d91000301660501801800c01c2c200d448200c01c580001c410304204140d84000c0150644440c2000898503071928542a8514082c228540341c1c81420f02c52a14041d40082c00544041002240284411030307449607c80070308106120920100d480c0c080c0000d0141c10640c00030f0114a1041804d03038a0004080315180c01c052041d109114046220b6000f04030621b06801425000141d4500a40690356a5a0f96100c01c8400034440052021203460b0810244600e0060041d82c58000c1d0380803440070070515200d0344500190108071442d250310341100300e24038800c0043c0d03419654840002d51816060610035101358200070402820018644881106650743c034612a010b544200d0b40910805d060110031825600304081c220204 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 94986529 1250 94985279 94985281
    0x6010e1203090d030c02041802030c0402092116080a0501140105090f0a110c030706150303020d0507060219020d02010f1e050a0603060c05220e04060c0c0c0b120f 71
    0x21500100854000d1441203c0180821429203401d0358032076006440a0762061400c1d03044500011070008800301075108030181c9029a0301c1d0310800c0700700d0007000b003042d4114401c0b20740004aa100310154200400018003140e05564080001c0554560181c00820f035a030000c849090400a027402034161411a00e0300107035066040c0004603100708002424035680004d41800300f4400c003a1680700ca60101800040c0c0341e0b4400500020555990081d0707c2203840320325101224407a01c00004010041e6541030307010700943c1507800790071110f5402c144400e03034100b40c0c00c1026808107442c811040a0f603900d5a0090680c270740200d50040d003100d1181c000841c1d401c2c1040c0b105004070b40c07a07520202d88180f1001001030251a00070200c001015180c200401030351500c180c4030341c0cac3d5402c43c014004080000c0c00c01210034200c450284100c040398810402203500c1c00d40070500050440c0c0040c181078083d85010b4211128035158070f00c815066a0060f140c52070300089001c40305404240266001001000c12412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 94987779 1250 94986529 94986559
    0x160e0708070e010c0b090d17010503030306060d020904150611010c050a030e15040606030c12021003051810020d060b0f0403030507020d0b09030306090121030819050f06010e 76
    0x101210081109081002d20329825525038041e014051110303070808004403040c6040e0a400c0d50340c481488940000c15610700c0b154050340e0444c06583e0590300c010b00a035045803140b00a02255800405007007010326001e01040020743c443e0311811074880b20f40b04032004074501d455006003c001c00070729100b0450341070981ca8880c0c680c20008540ca042d51030f16000840c10000f140701420002d148040c0ca10f002e86540600003400465048101600e00465100300a141e0b580c6416468200b1000c0094102c1c08403080d843c0040d019500c501c1d4084520307015003090300c2006661038200710140c0c00341c50a0503408100c0008a445030302c520380151400b522211315040d4120074407540f50040d88401002c000000588070b0031510f030040e80b4004a0b9010200b41d0183c10240c40082e144c2d04201d442c2d5000300c03840000003070702e5401040c4198110b80c401e0f132007541c031018545003180c2e2200010054070152400b40c80c1180d001c02c09100ea284140b80005450206007002c0c000180f102040e40c245511680401030b6030742c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 94989029 1250 94987779 94987787
    0x405060d050d0305011706150f06070602040909051c09140607020d050607020601080d141b031321210504080f06010801050702030301050312090f0d080d2406080901020d090302160e07 80
    0x230401d01c0442740c40c2c007a5440100061158880c14000a203c00e0001c00c0008858000d500203c03051441b401c01c1c0c0d031a0348111143d0404405038a841040000e000f45020400c0c1000200d149001e680b02a00540ca04800c0d034020403100c110b031400880d1258000c4e0b040155080d0306114060240a4030b5020300001c200d9484002c0400364019182c1c50065030000e501c4452100c1e03100954110760309101500c2d22521482009001440a07204080290710801d5404280100c41040075144550201400c51340104040c06014804e60300300d405d0301406010000032420090421100081c1c0c030542c00202110b40c18011105d0030b6500c0030344444107540c8244010b02c0142c3c1c0c0419016510460b1107841030300c541001000810001c414000942c00603494007064080c8070344040148140791009400b0301108100b200c0c41850104800d100c03104082c0d080344148442c510954516820694280015051400702e0080304102c0701240011805a0300280900c208818034500100061021510800091400ac0c0c4094 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 94990279 1250 94989029 94989061
    0x30717030d1a06090618090708040308090303060a090b0d150e0705090105101211030c0a0f080705090103020c0c041503031b050a02040c230309010b0f030c0405060d050d0305011706 79
    0x13600c03500000c2250040b50500c0005900b2815004009803d6030030421805001c0c800140d43c1900000d8180340083c0c1908400000c490050b80090701d9400072a181103681d500030070704c00003072aa2203003040c60038101240700d002000c3c41134a40b000000517161300100d152403610785107900880c0107045550040245564054550380c14152608103019186518560080104810546144141c0011040c0030345056401c010f4160795070180c03100800308401d11b9041e00c00c0f03803007102c018001440c1080510021f512a8000e0040034249a048480103040340d00000d0640e0040f10b03100a4418282008205150340b044a0f003510701e600680408046110741c0720349460f500030307910180c002c80c1c03503820035200d1900c0360000d00540304600e20001d403403459521620800b6401900c0c0421150308060303a181300380c0360500000818902c010010024103019100b07010141070003e098a40c0725490b486c2c410080381090200716074400b80307a9000641c660505c04004507482d90072401d20301c40c0d84048200104501908820 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 94991529 1250 94990279 94990297
    0x3010902030603070b0406120605010c0b01051002030c0733080636010608070207050a180e0312010e0a09080703030b0319030c0b0105061306050702030717030d1a06 72
    0x1603030320b80e030b102e021901d040d01c44e901138992001c00280010f001c50b40a0051080c86070b1003003050007030a568000450303025008600103807420000d000104030382d28160480080f10303030050040e82d080080611100b8142003542d809280c8402a2007a00010500c0480c06007180f11907080c0c00c800710452614008001580c014030076401904458070311070350ba80190590b5140000a07900c00da0302544c408591459418080c450600414901c41c00310703081c240041008000c0d141c0c09440e0f00301051400181001c401908010b0a0080f9921881c10209070f40034001071000c000e9889030801c00d035251036800300720404d00500d00c9074640d20784100440014552001c071542c2582510300420900050000282412402ca03800a00c0c4e001c6440504100354014411100309400f8284188480c3e90340d03800e10019101c2e200b001c1040c4d01d400c003c140302c0140900054032100380090704544016803141c034001d07629602044110181d40c00800c0070301c0c410a6a00502d0100c80641982c20707481c070718840100c5c5c0d43d40200254 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 94992779 1250 94991529 94991531
    0x3070807030b0303040e041103010e0606060d0b04060b03040302070312050a090e06010324050301200403031b02060d1a040905030d090204021201090203180309010c0b0c120f010807050d08030109 85
    0x1401c9120342c3d0402c20749028100035000c1d004542003030710700000d00200d03d106007030181d4200720f803c501c0003101140c0d15202c0c0e54040c041a10b4052100101401045240007481c2e10079507c1902084040001016511852098000700307542800c0d410040e15480340303803426508210080004400050b405861070080314400f180400312600c402c07006901414101011521a004544040758002c408047d0309044481c26070003001480c2c0e0411078540741d01170754108040e55110400c000c00009200f100d034240600514003030b401200c9140c0d800240b043e80301d50700980302c3c181c5812104600c18203c00002983d40021a01080707200c0840c0c0d0750a48034012240c801d640590b842800030295260340d01207640e030300790389020302090390307142c0f00224001e40007a1400746007403048801c1d144490b41d000045500d00241612822144181582d501d014603d000303200c4100c0b400103005135a02d082050034880d010380c021050314085036040c90354640c030300407440e4022072003004218000c0c001308260034106d038159824514 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 94994029 1250 94992779 94992791
    0x1e03040303030911030a230610050913080307020303060a0e07020a24110711010504030510090305070f121404030b0609060a0b040801020409050f01050310090212150a0c0201020307080703 82
    0x40030303a8003a07400100c0345e400d0300030074000c41c0c00c0014810404441040000c69850034440380040140d0300d080841d0440003090f025a414003091a00c5042c540d0f020324400c101c100c955483d9501d904146d00240c603170601503800841880000d1600821030340140c9800e1255a60302d02e41000003d54410421802800e00301500885580c0e20401541c0b1203c2e00a008505001d5241c1101d11a01c060f40f00c20015988004072544101c0300750310400450f8116038001c8003e03e0390507029840c90000b0070310310341e0440c1400401c00400000882c120820804180550f058144544100d4009459184130030f14283c2c10800400003480010700c0c00700340c1500070078241c03010607580e904e50010904249194010203481c00001c60300250150301500144103071901c0c2c00e03050103e07480307071585403000309020f0007250b5154010204211500500790300102e00203000070281624080d808203080e08003044a6124140003c0143c00c100308030702103003d41001901c1c688021459450821001000710b003010b410101095100c1d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 94995279 1250 94994029 94994033
    0x604060b01020118050a0b0a0504020d1e021203030402030706020636011401150f080f19020a020307050606030312072d03020301050f040506010e131b0e031e030403030309 75
    0x1501212004c42080c005144d03006560130896990482d403070084030b825201c4000544084610701076280983c2d405002e030380c05254551f5a85005d41084440201003680403c1d8000151341e032141101601c11700d400185030b980c1401c2c0103050404003150001000e6501180c14044522075030100307081c2228989a024000d02c0401d11046500c0712041d032864015805d01d02e5407400d421550308010f048890302480a0400c919405040d10300498160180e0702050b059030004480200a450007640265a41080306415940943c0201240c01c140000001644041040300801000304007850304103401302c00440c109400f2440340024680010040d0b410481951003410441c4042c002c50000e0319200300189101840707100e00203009402c04d105040c850302542984201900b0f041c8240c5000314010313983d110f01f401007030062100e00345050031400308460b030307076035000311881d007602840e039140c00080d60340b8416450740c1c40801d450030340802d00c44181c1c5110b0400074216440700104036422290305040104540e65a8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 94996529 1250 94995279 94995281
    0x24230c1e0408030a0801080f0a020307090506130e030306010906050310031403070b1501080a1b0f0207050a1503060e0c0a120b030610030314160204020d0b0d060e1e0604060b010201 79
    0x80d80c0071142d2407102140c0440c14a400c01c0d41107040e42e13400303401c0711001001c16000716a12600080d0280d015000b0880034403105e540e54100e5a4010710281ca40d040301b0000450110403541d4900c010140c07a0008800e22130343d0b40c1c1c80050760000300582c0c81c00e241582021620301c14507481c41d21001700040840341080508800c144165110341c1c0e00240013500382c0c40d10303100d00c0d042d09245d902d02d030707001405440008150036118407400342400c5e101414005500c40000094030340c0b0381001d900320158400c401000078140d0701e0742c101c100039110341c107050341c44015481e201400707613810b41e08180183c500d0281041000000b1000340c480c00c1840749070459001500110f020014018001c446816020781010400c080c403428403904110380c031a80c1c51045465102e031451500d40102c440044003040450511800740c50183c0140103030b280d140800103801454040002d004c44480602290103a4440a4030540c0b10410300030100039101c45500078403004400d41240d61180c0000b00000e002c29504c102592046e407003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 94997779 1250 94996529 94996537
    0x9270903090b070b09071502030313020f03010906020415090b0f07150903020a0b0a050105031906110a0915090f0504020d140c070b0108150705030424230c1e 69
    0x40c000c15501d10044c140074020050450302c00201340f292110008115844401030203a02d44e941c0c0c00766047d51103400290308070510008050707a00030b4010020f00030396a0b0030312400d001c0c03038811500141c1d100e01c1c05044134403014406220038240070320100c081111040760012142c01000c82c8203407035612003440c681140d82d4508101c0b4511304900d021915000c042c0c001131180700c154040c2c8a44030721569144429400d5440902629170103410814402c103880b40641d042a050f1440303007401050300380b01a010003901e5000034092500142c91072000b00140700512149889005451802216490514003005c100801034410f0600550703000568802051b8035174020152003180c000905d0207414441040041608200425204201f0090000420410010700c01d805c0042028507200e00707581c2d2038025583c84d04002c10a5800b6003c40c0405a50382007001c42d85480d54421000010b0009a400095142059007880c510030000020050068400007542030312420815808007520603078405508040f2030003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 94999029 1250 94997779 94997789
    0x2004060215180a0b06011805030c0409050c040219110a0b15061b01050106030b0d0f080903030d05010305060a27080f04050405041406160f0e0a0e04030f0927090309 72
    0x900031480d030822130303004074650003200c09a0307400c890640a00d0170261b03446418810307550b05512010200300c1c0390074150041603000c0d0061060b24060446840801c0580e0300c88034040c0c000c0d0485001c00b50a494000c046610001c24060040c00512091382e0381070030001001d80b4101810780316000b000c2045d62401c0c00c2f520701d00c888040074203205c55184030710380c0a01400c1c0102000300c0d0418400c80b01c3c42c20828024581a0303006414103103044029180e4002e25485012190741500040049010742605030240030b00a51051000302054581044284104c80130749203a0840c0c1649180d4580d40c03414450a07003500365800510035aa94170f090544681548560703480103402a043c030f0100824007200950030f845035510007086d9802691082d0b1100301880b0070704050408130701d8803038204030443e10941422640740c001070821040c13561200404143d0b00421101100043c1580ba10020140d51120410004140002c0c01b4a5507210740300503181d1b803c00000c5e01b154040e0f40c400f490001c0c540300d5440c25000380 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 95000279 1250 94999029 94999033
    0x40f050a05010f1802030303010b070623040b1e160504081209030709021323090112030908010c020304031712090a03030b03030702060423040f200406021518 69
    0x4100c5140090107041d4007414810240e1600b9a01c03d40000800e035941c03001e9034010050340c80e603802d00104040b990040c0301d00f0360383c0350340d40d821121925010002c0c0a540e0102c5075100040380c07505140202c110306000b81866403808088442084040a04c2c0103a608410780c001415100303c071919044416010310f6105000d0703071090440c2d000440c0925801494800000d405403004540c456580704140e104920300203400c0003030180204520540e11601c0d001d2148040e50040c0c202c0c0c04000010750070b00c1c1c20f8200c80700c0741e481000c040301015003104481c401000ea800092250713484003100a074032401188400390030300c0111000111010710b100c0868040c0000c46815a08905003240b8150307403802145800c5020a04d014409405494004140ea00c0ca03503000305650702e801d080400120ba000c1803c0c10010992079090706141c0181d0b114001e4048000e4082000100c1920f5803509070695904003980341c14240c0d04010034819298040f070341c0b060800400710b100001d40c451036460081c0116120700c0c02914 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 95001529 1250 95000279 95000293
    0x30a0b011103030703240303020303070c08300618010513020c0a080307020f0105010e01031e02210d03060e16110a06060603060902092101020d0905030901030507050304050c0108040f05 81
    0x25174041d4054a03084000d003071105644182c41d8954a50941c003800003402507441480020441e600c180c600c410512710400009040003101402c142d104524075161038580011000000d1900e1454005d09074001c1d0210740c0400f5900030786050b50101d083c180200c074011154118a0280300942c0d40403198240004001c4030f00c001c8030f0307080a00ca1604244da544005015031500401c485005018050513184403160390082a4a160388400c0b00004e0454a841c0c0107400c900d80b400541c1e1444113004070b5640c0b4080c1d100503d0091310640381484001c84910051518100c401c0c031514524a1355140d00000ca0002e4103104915050152442c00c2221241802d61050f207124004100645d0006000c03074003e07440a01c1001c0d01e802802c0d00364000c400c2400d030050020304000d0140c41580d0214090110075500051411012034640c0080c1c036090300781607403030741d000103010140c0307503458428281d00ca070030343c0b81c030509600306aa1001e895402400e40715040201030400701d810700c03a4140c480c0c055079901104403008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 95002779 1250 95001529 95001541
    0x1c020901030b1503030313140706300507081611061b0705030d09051504080a030c030e0a0c150f17060f040e1b0a0602070306110706020a0503160302040b030a0b01110303 74
    0x790280c7c011044038420807984044190420000b01c010540d1025180c00712171009070441c092b1414218180d04040d000c200c01c035860441c0951241038062901640c2c1e1a125141c8074115170f201107090340d005030800c808501c101d1000c003408038001e508410b803042d46020090380480710740d41c02d0184940180c140c0c040011603941c2e80249030300148011380f00350262040d1382c005204116580d1011540508191010401d410482c2e00c660321010031030595040026004420400c03207403800e0300310b02040b110701c00d41200910201903c440d1762105a0428901060404003c8900401800c000d0a410001482c002c4c0030948540d14160b80003503d58000d481000040300004076a07640e030ba001181ca0256200070301076003d0038104400c0180035201c854000f0b0001d1450b5039100d90050140844600000d041449132200283c81e034001400107500c1c40d962140c59041203083c501c40070341c0152420040c540b040204000d4050f003082a01e6220400325400a4000c0c0f141c4016920541c0b4209001c680e03000000801007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 95004029 1250 95002779 95002801
    0x7050a0206041509090c120903030f06081f05010b0403080a0504030204020d1a0114090d0606030b1e070306052101021201080d030c0302030c0706050403110f010501051c020901030b15030303 83
    0x2c500f0b4450351101c004e0365403544100100d40d1403080410000d1304c0040c120810701080e411408051b0720070b140000c0d9a040d510301200458600c0e8204c061036030041d0b80314120f4594002010114090303000d03030401095150110100681c842d0f4400103040340404a00d084070140980261001035030060070035599110903004034402000c0d2201c1d0400552007004285000754410000f0511702c1940c0060140b8001940d001c00205c440800802c84026403034000210002e0b500d1810f46000c3da003118400c001d4a8000c00ca04400044014101410545000b00410140d611420031081000c040c200101903290804001406445801459042c03221080000150b04400180034503010711159420080010009012010f901c81550800c032800740a01180020a42c2c0380d0006800512070304100d184403400031a15807c20034882c00900443e591400104494203081262281c0800c2c1c040400903030300c0b8103a0028103414010301000d0070240d0341310005245100e01e40d0a6415904000301129140e1809050000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 95005279 1250 95004029 95004059
    0x7081306091202090c0c030f0c0c1206070207030305030709230a062303090c1305010e0c040e070e040b1e030c010c020913111818030c100207050a020604 67
    0x1030014000940002d9503144014400000caa4014203040190321607414007005071700620700644950100700081e400c160342c81300040102610b204040c18001d0300d103104118542c0b650110b0550a50840000c10844690200b0804280d95140c100301c0c2e100d0b101c001c001c49011020381c21025012103c0710043c1184003d512360840741030400c550750361403503032a501c1c11585c0340751452010400b0271401408a1842ea10040038580c00030070501141e100030100c90026400080021500c102e155441c401841603138140d440040c0e00c50b81141c4514985860160010a4007400425450030010100011100c507a0b454101c0c2c0b4454600908035803558000d41c0405198025030305c0708034800c6c400d03a00106003030350140c10340d4035050360010b0281e40355503601110102d200290a5041752402c2c56038058000d242c0d901c06401980703054464005000b40b4111040714030861005031030107283d0307000344800002c40400041c030301300700f0990040c0962030741610b28049180480c000c0f0000d50100c1c020802040704100d8041c45 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 95006529 1250 95005279 95005289
    0x4120b0417160305091c0c03050105060a0605090f0a08030d0e06060904030906080403030b0603010b0301060e030c061801020a1401020a020d0306120b06220204050415080a17070813 79
    0x2100e0398844400c841e00903120341102e405004500c50400310100c0e0041028102d010030152a91542c0c0c81d0b1000c00b039251003a8840111079442e00003405000303008007441400c3d0f10030804e07142d003c10700c1d0038002b002c1c003036005000c00c5502c00c00340c1003c41d104540718501800c4c018003000c000c4944500f81000c00794060038400c221105148500c000107013461528044041c00340e174246e106e5854041c1480070850324000020029018541c80e20b0868543e51a50b400a48c002c041c10700505849504020000300300c900c100b904540700c0c0c0d21800c546034299980e0310807504107411011a0203c02c1a0520060b800c011803400040c104840000c801d00c2c1c400d00640080040e04119401d41c0d0f955501d008013501144e1150042c0c480c00c12101e414076000034100303284150005801000345541c2c18a0f022a10001e44003c2c06060346c0980200f020000c9081502520f900d03071010000044c00300e8208659541d4504600d400035001707d8103140b180302015000811a0350352500210344951300c105481d2500e00e11207086c031070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 95007779 1250 95006529 95006543
    0xf2e030e1506060a02070f030302030403030836070909050102040f061404180b040c020106030b28180503030a0605010207120816060209060a0c020405010e0903070308070504120b04 79
    0x24040c400d00840c1840252030791010340460350720b070714040c00701d1a04000c00300d4040d442550000300b900000c64088000451182e0700840c0d441c1c1c2145801003000102618071071100c903140a6441e00540c00c501629900500b07a6401401c00f103450100c2454030205a00c40d000c42440c142400003030201c10340040055800c00c1d003091581c82c0d51514110b4001895400044148109020612604400081c4015442c0c10300c4e201040000007000094102c4210040c00009070390b66050800400c8506a0403a40c001d1420f00c51101000004101c0d0f6505517110f20124203843e9a024002d282c075059031100c02c00c1d10703003150440e500d92030700c0726503d0002c265900485004d44124940099603801d014031682510b03034400ccc142402d19802a4400c8607640c03151070308481207a020300c4030320059102d80d40502600680f80c2c0d10509850f6481c01400300712501a04082048a00b0004008442c0350002c02c40300417541c9868481d0040da04c9070021981c1c0c0c003664000315031540c4001c24210501040201329401a805400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 95009029 1250 95007779 95007791
    0x506010903020102060a02070c05060d05070906020c01120509070f03050714040c0905010e0307081b04050114030607140405040516080709030201090b0a020109060e0a2a050f2e03 78
    0x1592491500d10000f80181d00080000d402d05d807441d0085d000307203403180702582c05903a224000900160412891550b0881e902c04c200041c481d803100c2104000c0c682400546058a6950300007020310030480030110950780c8030b40c00f00e025000c0400c990001800210b1796030f51541d0700e0786000d540b81c1c0707054442c006003803140340042e181c1071605100310018941503856240ca0780386060b0054820050f10308486905019003280001c80142c01d0049410003041c4404030401c40000504110458106811000d0148080c002142c255140090aa80c00c6519400d0904900802d00c0380345080e4466070704440d8006082c03009201201001c0c0c030034011091540c5d25401e0b85650395100440300680580700181c002408880d00b0030280d8030030401410a0031080c030000c2114402c036190b01c426944240307840009a1b10036904c50040c005070030032804154958044c401c912840c11028000c2040c3c950080c144100112002c51403940d451880b203440c6040881134036060500c00240c0d903603414510b01c00207408a41452 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 95010279 1250 95009029 95009041
    0x302031309050c1801020f060a0506010201111611130903030f1a0d06020c1501030f020f12061909050105150103061d0406050c0408120c0d050307050919050a030c0905 73
    0x800303007622801c0284940c600b804611001c2c1c013180b448071598541036010300c88000090340810f100c0948904541d400100e658100389000a00f160388600d003a441c0240180550541d591036000c07941903241d00030f00c88110009032280040d011104082e00114901c1ca460a48010141c140e00064407601900c0802c0280c400345c218141d548140042201d0740c42030301d058480e0002841d81d0701030543c0f0304c1c03048100e030890141611250f42aa1080e08240c8070a92048c49010840c40d000c03000070b0349844241c030401400090016619546c01e0050485e81c5001c03400703603e400403044140c0c440305855800200a100c1d0341020348518039008082d048450000342809000304450017502804130700c03d0003125040503190b40329100d01c0002d02c40036224020003101000b0000d42800b08010000c0880c40c0c41d807031543da425000d42c0007403400c485814185d003800018810030010a420005030751100c0310503a442c05090101c900d807402010002e40089622132403008012007404511404142074806c0750000b00280c1d1100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 95011529 1250 95010279 95010281
    0xd030b0102030d1a1e0a08010908030a0504050a08040b0d0506040e0a080d060b07050706030b030115120f0605100303031a030c0123070f02090604050f062b0302031309 73
    0x20501640540d000b00a245074a80584e0312420f401d840b8414180c1c860700241c00000d0005407030b42a440d445c0351074103940e15040d00c0c0100c05280100b031404001c0100402540d24140340f400014401d0600c40d1f40c90001905209042c003402c03800b030358030001a40d5a0790702c0724081040c580002690144c180d02d000c00203140d5091034400c81c28511000f50040c90b021106035180085540011404080c60307840b5500065145001d00107010128880e0740505180e0741800303401401c903540c1084542c4030340c1c1442d05041703000d01c9a0410100342e8580b00c01540707410700b0b81d04203100e48001d030250042569240c07204011304000c82510321400d80e4801d99040c00070380e020000404442d000070460542c16003204210311041d40c042c1001c003c1c000c1041401d0072241c40d075107503518907a41010300140c3e0f5807401c580d00203003149011075445d0f07070020040318104018100f03414400240900140010702a41c2c0c4100304a034504510100100d103134550468810010642d40750082d1a40c108a81000010611050111340a451 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 95012779 1250 95011529 95011541
    0x703050915030106030b0d150c0207050a0e0601141c0207063305010c05071509090509030301032904060c050702030f03090405010f080d031802100e10020106060509060307030608070e07020d03 84
    0xc0d48000012303c81480c4440240482501481503100e02000001c141c1c1303a0091072001080f54004d88511450160009400c11400040076100041c1c2007291111181a8000c00ca1081c070300c00e400180c4518040c0341c40002000d0400380c0350b910903213100d115404402c00100c1d02d03050b40601c0040254043c2c1d1040151032100281da001400c0d50000903090005102c1220400540d00d0076281808001340d803800804110303001903030f13498041d400000061003071010a400b0b041c01d03090011215062610f002240d07050201e80036100a2400d03071035500444a0324400e0098030141900242a2103503800f1745c0304802e41d26401840c100c1c2c0079074201000000c0e0800d0011001d400c982d1106e002c2c1203510113940301200200700c11500400c2c5c0d11111003e04000d612a028081003181260700c944142500101c10403d030f86c0010b540010441e03040c083d06011146e48070003a21880711064030410f4607078035604800d80150145801c105071504c40c00d80001013985080c000e041c0501c150f0f409881c1e000e40340350012019540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 95014029 1250 95012779 95012783
    0xf040203131101031512110604030501150501050c0a030f0504050a090b120303160e0409080f09130506030706030b0a080307030206041a0708132f03070b03070c02060703050915030106030b0d 83
    0x3584a0704000507040034405910240c0b250002940340c21f0701c10000345003900207810a8540d80e41d1340343d1860b800c694240c21400509404d00740303036042a503c8040955917825040004040141c8000d01740300d614054800d440c09401c0040c440e40c40d19407110780260083c8007100300103100e0f0b0041c40940908090200469025090083c00c80b071840a90980980d00c13004810301e80c07500995140c05c1d01c0085903182d000380052040c81085981d8a180c1402000050913001c000c076081540740800b4495280c4d0300091150464409080100748607a01400250543c80a0740c042140c9000000c6c1500030590f001c9a070b28461840b480260f4030010300c0652a040e0300c04100c4d04440031070030070000300b0a80034400e55a0410984038080d402c00300c21200c95003007480d81c68001c036120400288214800c03540303818062070000d0110480554110f02d80000d009003074403030a12001e80503002c002154001e0511174001c4401c2500c0c0030340782441035081004103100740c0d4424401c40c00003034074240404409140c006c1a00140e01d13 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 95015279 1250 95014029 95014061
    0x209130204082a03030403120e03060708160302040e07030504020111070b04061b0606060509030d170c07030c061503060c03090b04030e0a0302031e0105070f0207030b060f04020313110103 82
    0x94001e0002c0140403c0c0380c400c08140c41101e03018070740303540c00c10051020707600c9010f45048940c10003101501c0c400c0081c0380507101ea0402c00c100480e03d6844014140c0c0b205500c1e481d001c01c62101c0e0300030b030028030594000500030f50b881c200f00020160960400f6020380c1c0f00703a840030750340d200344c40e00c031a1075104500482049503c10401001100d121326031101c0955401440381c880c141013944d0348411140d060b030090011440200f41c403000d920303040c888182c9041d280d0a240104a42c401c0b001e10760000000e04900c28480b01085140500d0301c5041041880d0313034004801c2204203540d00d01d240f0507403501e210484d54141401070300360142e4883d009071044541d01440071a40c945803a83c05a4280041c603101e20b41100701c01e42c0c000050703a400c01900c0b1002441030380c0c1e1418043c118103c0da080d140028810030a21119070178624140340d0000300703001102d40201c401ca130140c8494002800c1c5010301d07040180d100b40088148015403038040144010544100400b100801da89401541a220712002f0f6458003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 95016529 1250 95015279 95015293
    0xc02090c03060328230f06091c0e06070c1a0904112703031c0506040507020f030a030e100c17010812090f06070b0705130e101419060201020913020408 66
    0x107145d040e00710b41e20f0080502032040c480460701c01d5a190080488081149500450034005440410b000e05400100c404070b28030b2041e02090805013040e035400c40060301600c1c001030008140402c2e1980030014000b042440d48540e0403001c202da10350740002462a103d030f442e150b401c0200b1401c040841e02c00d250b6061031105500510311400c05903c010740c501d140c150104200c52180d000c40da8045400c2551200800a900d00780300707040c00308444000f0818415507005041038012440d000059407501800392074040f544910004c0180c1c11b014005401440343c0e401c100d841070743c858201c0107900a01e51003810034413040c1c3e03030303042c44542d00c0410243d01c80858034200701c0d403006801e05907050714042e0f401038849881c1181d00e0366402e003400c10403200580050404201701220340f550402c8000142092551a15541840c00f040314800c5e40c5442102d401c0c4583c04500483c07500c0b00c0110038107500c45040d460385095a40c0001a000c2e6200342c0c2d419101d058510400d000503c20351007500c068400c0c1c003002b014a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 95017779 1250 95016529 95016533
    0x60809150109050a090615030606050a0518070c05120409050f0f0a0b04020408030301030b0105031c020c0d0203010e1c0f020f0c040b010207090615090e04020d030f0c02090c03060328 80
    0x1081c3c040d01c510441c50b15011103001181d46800b815040d814507944070318039149182896800c40d8aaa0402441407500700000c0003555501c207080200c01c0b00d038003415800c0d500d81340816034807a805103000400358010071801c07041d10070340710300500101e0398400424015907172401c902c1070b0075203012a04450b1a841c900c0100e4490030840e409250150381c003520041c54107803144081403170754000b64811124103541c1001480241024008880c607038034580c940014080020002031348a042c045c00b150700030004201001e0640d90709400407000e07844480c040c2c1c2c03620585207030b1032a0b1a16907d0b01c220081080d075001412642c0c800640e060803441c20b480a81811660402000040d2001d0002181148074400e004038907440c4c41c2c8694801458440741c44081e41c0743c90352014141c440c0700d41c0305800241d89402004050707207692228401441d0700d8038280300c428090b403005450307034250214042d4208030740004001c41c40d00000300950017124110103e88113902406001000b246c984445200d14520304003203040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 95019029 1250 95017779 95017781
    0x1103070c031112030a0203060111030403080703050306040b280611030d090c0e0903090103151d090708010c08061807020a03030507030605060c100b040e030406050c03070206030907060809150109 85
    0x1810755030b4005981c000355046001c290281c2058034540c1500350f000007401030701d6070004000b5425280510185007018070f0342e100c2d41018091044003030300b8000000001042c5e903030756a1091100040003810070f124401c808000300811014201c1e0310b4040c51502c000868864014150132140600380c00045107800f208140c403d028005c000412640d091b142080171444019003907485124000010045441e113800c10001402d807040324030300d5901d9040d106000d004080352803940c401000c000c911406c0c03058480c2100d852400f440ca43c1b0084a0307520781100300c0b80d00b0f40e2103080e440c0901022a06030043c400000e4a0282042e010f880590244e0b0014a548000034066001203501c0b0905060015110340c0d9a404105030b0b034048540c20342c242d0800c010501c4801000d215243c3c8105084e10104480a030440c42196039100f00e02a8200344000070410459000041040750407865001c2c005948a060442210341d4488aa0003154007207001000062070f007090001c0d00c1c49662040c013810305016440d210b1048 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 95020279 1250 95019029 95019047
    0x30a08070f05010e15010f050a0303050c0c150d050603120306012a0609031107030327030f050304150c022b05010507020c0307050a0b03011a070606090f1103070c03 72
    0x48018442858079000716400384248551020701c0c1c0c0113011040c2e00708140c003403250300c144c100710001d0607542c00900c070316100c5205050603690305040a40d40d400c050a40d82d86842aaa1007450780300345080192081002540f0142c00c080c10b80c400e00b400140c0b03c0e5020961602d001500d480c0d550101400000c06962050b0022086e520000954950b041c46503030882104000e80c0b0021341340161500700d01c404150b40000313008a020507440180101340d0031a64010042942c0000381801030010546104000f01c40802c41001142d0010300900c01d04480c0c90826129045403162003c415074001000c8210790040d0101c03017845500401c004800000107002039001c50010030901c1c0040e40460318540064024441c450281000d900180f41110b654001c05140c00b0381900458050070320700c01c04001036161a01980e066500c040c0501c114450038182d0ba100c94000c80c2070103044941001e500098100310755100d454805000030050048082c020400741c0745100c01e55010000403150070500011900c60300c044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 95021529 1250 95020279 95020283
    0x10504140609121207150e070306050705040b0316020601060206010e010e04140a030207090b060a0c061a180405060606120a05040312090c080c0907021e0709060612060b0306030a0807 80
    0x51004540c01c2c244013032505122010007a0b0700340000622405104c107540038400100441c1100f84070600d0109100ba4030350859110081c8081c1e1144041854103020708242c90140080d10303c420b8491801d00031096403070107070303810805c0035004003000070500f03e00c0490200d060700c841401c0d6889591074205032034040304004105680c0242c141c58101c4800c0700030303c806070035240694004d000d55410007140c0404c407109010120b01c2010200700c03074400709400c442e600714541e4211800045032050b4919135502591200c00956103e000d4028079034040c135a0341081d6010301e005108607511a6550000c0c818a4414281c410954000100000c1c0c0d040c05560001c540c0903109240c050b6a000c1c0070030280058031034a0b2401c03200200c42c030005006000d0304014411051300111080c0306541804a0042d4a030f10300322110720545601d1040b2259124010000b0000600d4a01001c12007244d543c800246403100c020440a0f200e81007880018900c0c1c89082940d000b44402009054240c140ea51660900c3e84603200c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 95022779 1250 95021529 95021539
    0x1205030706060605091801140103020d2307020f062203030b090a14060423100f091a0103090209070302070c030c1511070e0610050d110414010504140609 67
    0xd4480024650300403540203003055100c85403a280c543e810000d00e1680031000a101180c0b0000401120710a990f900031105420b00700165180d1302e101709000945080c2c80415614100e0100380c09800c09800d1003244078213080d03802c3d6503511401000440e102c2c00d0545454484c0300d007440820144034080c60741a110b484c4039040000f1101c0c441c1303001c50f00500c0308490600c3c41d140da0302c40d8400c4007502c01c1d4510303501c244d003154100b107040c59a4212540c44003140086003600d440c41c0000852000300240910003a00c440c11007034507102c0ea01c00002c0080e024580b110780b011241c1080e0800194001e00641d0b100550041c00301c495692800d000710020340290400740d9000801c144008003040301d03d020074024192004242c0c3c0900441c1501810600f49803a100c81e02e5485040c0c01c0098898410703043c0e800003c2102c00e0f28084601d0102182c003030090102040b8028640801c08100c5061000100101c600d14641c510b070000c1d0000066490340294840c5044c8111417000d850340364a07080000f032440707080080c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 95024029 1250 95022779 95022787
    0x1030f02130b090307080a0b0a0207021c06020d1a0d03081012050d090f080303010605030402060c010510150309081b031210030215190807020321010e180601120503 72
    0x18040380390150940c440c9605010000f028862424140007001c084c1500d03500070075030f000403903a40c2d281040c030007441414015404980c080440d0390304a6502c0d01280d01703000c41100c5164600780400258040d00c100e00d4000d2038180e101040c1c4409410541d40120024481406148a9201030b6a03445000b4451144c4851100d4003107050103100c02e250b5186030180b030090180d000c0c1c0c01d4019118107582e41046280b00c03a04042080017440c0042100d042d14a146070960701c9132514402310301517004405050b6040c0d4204010009103105603419a03086031110400c400e0000441281030f0110b901000000d0720942d0b081000382c80074111400c9000c40808820f00b00e031300d4040829076072001c0d800c3c2542c01400b8560100e01c10030551804601c02c40c0351040c50b118040c034040f484403403039032000140901b00c01844095400a80b11038005c2c01614641c20b001140511030300050716003600340c0d000034000c0040d401d094a0200e500b0f00b0403500014070807040d440003070000b6420003d030154001c444500c1240c180c40100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 95025279 1250 95024029 95024047
    0x6080304030c030c0902040807120204021c02030a0b12070314030403081b010c02010b06190c020406060507140304080a0320030a030e010b0102120a050f0c15270c01030f02 75
    0xc0005500804038291507074114a0003101d12070056224801e42c0c1d005000903c03001401141410171101c135108000c01c3d0007403520210700a40030754411a07006812540c904c2196400c1900190322a1008000401c542c210801c2000039165a09520140583c4081802e0000072840c0074031240940001d01100d040654a42c0e40844540c0928940c180d070015000c042060b41c6070074041e180f000601070009004070303400301c3c4c0414502cdc000e0b070481c03120781c9030042421803229002e590000c1c07180e0740141061101c0e0b13031034410150556101d42c404a80c425100d00001440c3c14010086e83c0a0311401005402c40031050f44045480b01d00521000011801407002a03587c980100020982c050880e240415000d01c17a12105003140c20f500780090540d0480d01180500d0301086d0111100078060342440d94481c8108049030700c0c640141d00d050101423240c03613032000540139078249240c400c8e000d51260307060413500c00f111121640820b0000589542c01741c01d00f60301a6000341c00601d4008205d076001030901540c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 95026529 1250 95025279 95025283
    0xe011a060a050f070c0f080d02060c0a051306110d050310050f150304030206011503150b0a09050d15050c040e04021c02041a010311181c0b040b090d080601050712030608 74
    0x16a41110030351002c205c100288000c4242240c000c0603020058000c5000160019483c3c0310024044000d080d80002c201e00054080c409807286003900114080c801d0351243c4020703020302c607103a4140040748901c2c0c403a8205c544c4610200c070f20070744280c401825040c1c0b0700014407405170784050b2069408815400080039915410000c0d520480c060780c020006d0b0351418044040c183c002c1202401014242100f0700d00c000d8202c10004202c07800042c195644100c00da00499807070352950401980100381078625801e001100da5000c1580300c1ca2001082030341c0b200d0890301142d1080340b0071840802500400203025107003030301c1c0071004026407582d240510f5080e42d002130304a8403441d64140441900c060604540d5078580728020001480303c0c0e140e86001c02e80d4900051078100c66069900c203005a0700035500080b003082c00319000c50703400381c000034850405141c40c050583e02103403024039602c2004240780701d540c46194000c0c080d01e8180c4885140940301d8403044251543c036103c040905441d40300020704d41c641 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 95027779 1250 95026529 95026537
    0x30702031c050f062d15040305030306150703020703150b0d0609031e090e0a020f04060206010311030d050a0516020907031e1a0d060f0203010605040501030e011a060a050f 75
    0x511203001810b460940503e800b02040605143e0244490001c3c11143c200d41041c600d500660707131117144040e12106000100a0070100d400e00f81c080401040000400c480007000c1c6000e1341d4100c0f1803800f603510407800b0768400d026001c4081c0040c0e00c5070f07000b0000b20f40c01d028204030407071142d10041780c448228004a081c0301e005d02012910281d80e0790304030013859408100512400d01c503503810240c510600300300800c00e009900a14141b442100e001c584003070003071f504441040420b00850781e22165a1040070f911440244026540c0ca020400310010394070f03021030403281e4182c1c45d84455081c094078440454907500042c035481004500f00d03c600c80541e6541580d144a2501542c0100f011812082c1d01e2010340c42400760f06d1445404c040400192a9a00c40140700d0f0405c213540340380e00c0394903905000300500035103085417040c188000b001041c4141d0090050055950a072010701825040e1440c0b1800ca45690300b0300b401c4210111405a007500e0942c00400c0c900d245840d00d1303400c1c107010000a84190784 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 95029029 1250 95027779 95027827
    0x3172e050a150e010801030b070509011b06230f010b0c0a02030111040609050a030c0303030c09170604060e032701090504020d0209040606020d0203070813030b1e01050303180603070203 81
    0xb1600d502c280d84154001e0400040e01d41c02e1810440e55403440e6611060910081c4c407440a0050209141d142030b4400c034035807559418a65803102a2001c0342c2405001031032400c000d040341810360000c0d499464580316120f8024441000403017090382c81c04038440020703000071341d2190b10760083c000c0c504056030b42402800b00801e080844141d445182401c0540480d81c0781c3c1c8540e0003858880d10810115071106004c9040f00e40505020521886030713402100d02040780e800134004a85224201d1402c0000010006e00ca9449540100880103484100036a0303406801d071512490010050000c44410042503418030070704040c148803800350703201d00029080e0f03001004411400796010500c031420340b901d401944010056400a00104045110001d4682c401d100c000740c02c40e91300054184041a0040683e030080d50004040d1341c09007003400904202008044000d0402c5580070008255481c0200071a1a42448610005542c2240100b403186a420040ca190158003003484041100d0407081156901d0f81 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 95030279 1250 95029029 95029049
    0x20f0d0c05090606040b13150c03021b010c0b1e0f0423010e150405070f0315020306060708040b0c0114091504150c0f090902040e0a02030a1b020a03172e050a 69
    0x9410404045c5011800070101c0040049c41c04451002c240c010030082070303205040381c074500202d1030080141c5100b00c484200409002071081040f40000010031102407001c0c50f0707811403641c1c3e101e0102010000d0019180500716481d040c0d503050201110703c480724543c5812000100b8652404c2d4101e90500c6000340701c051500e55071600704000c2002c14030884018150300d0740d2014405045032500e12000e052640c0b441c0342154004003040391030780c5501c242c03980c7d6503111290a64441d02c40030846101c1e040640030302810344c00c1031040e4040c0705a103070381180301b019007000825070814141c9200641d84006041a070f88184010442800703014a80101e101c1c184941d19119074a094441c0c0040240039180c1c412078405205000078095810051151a00701118010140c3c0360f4a51205a0b4020411003090318034801c1514002d00250740c0101c0d41400c3c3c5402610f500205010380071001c0900541110484a4081448201b111041d4a0700d010b640510b9400d0f40350480c9500d40c8040fa100505a4115910203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 95031529 1250 95030279 95030317
    0x506161112070e0603030a09050111070308070623250509270f0702070501030e0f07180f2003042402071419061a091003020f0d0c05090606040b 63
    0xf0601d5020090b00424154004e41c600300d1500c42c010b000d000303503000c0d83e0b04000c0c0790305005a01800411080c0d0145400c05d00076a9980c0312480d0100052038a41c01c0164400400d042c60a801c0c036a000041784a00344a40c07010410040d00b0114801511300c81402d4814000280400d054a0f202d00080122904103640c0074204c04c440350f0780e485070b03164009000b000c101032000c0800c41203907404105001150020309010600c00e42c1c501c0740390b007001c03c50079807824244103400c800617400d511002c030791003580c0f4400720402c142d1410b03c075814103640c003224451450340150b803c00b1440c5801d80d0700850303010b03004142c1c2d8004207400d0b071000d00c4100384041e00c00c0c941c2500800c01c0310a118500d500802c2d9111080002d040c151090048034130f601a513040043d107440e0f03440e40e01d14503281c0854a9202038000003003800c3c00340c3ca00f0480c080d0394040d01b40402da0088044007518071480c00c10b5541301e0700e03c940041600125034508000c0200e052002489550445000d11001840300400d80240012401c081c000c0d4000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 95032779 1250 95031529 95031539
    0x180c0a1101020414041d28080a0806130603030219020a0e090604120806010c03030915230f06130c02030f030a090b0c27030a050d0f0201050a0501050616111207 70
    0x3c0e10b0040006e074104001c135081c641d01c2030500156100d10b40854681c841c0d082a880c081c8464076190604001d0b00c130b0a00041c00c0001254040409449918121802c1008440c0c10002408072280342c000100540d0000700c44118480b040e5000c48080b85c80100541c14441d103d520007411043c041c0c400c4070140e400315040c00104949074042e2a030000a902e8144054540400020070a0241e44000340030305940d1000402030180040d0039a0442c102d00000b0b00102180c408000c10b80484a001303402d07203004060110f1183c0080410860054100509a403440103112500100070407450311820290311080014204201038034000d5441000707a4400050410400d090000c180c2100030280802c4403401c00402c1e895401c0e2070f055403080c545259441164001e45404289809000f410152040c41010107450300c1c2c0d90300a1215484209640c000d008079112034550000340c880038050a9403101044c0540e95141c4049103880b40b4450003041180c2c640074192021903420114501120426001500203001d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 95034029 1250 95032779 95032781
    0x1207050a180f0203060603010302040e0709050c0c0105090f0a1502041a030103050c010306060212090a050306090624060702060a03090b09070609170307020937050105180c0a110102041404 82
    0x41c40a0b0401c4003075203545050400154140702c14040241324550b280440c080f4214108034203c0603200d80d9030100300506040c070b0b03e29140d80010300c90001030760130540000c4110354040340e034a803141c060314018605030880b655801e0741c05510080c41070003140c1c2804000b55020640c4070262503c80300d442e85603940d5056090940c10301e00031680813418141030210402000354000342c4210505400304103035407250070080020703003440c86560201c2d90502c1000207010960f54082052801141c907038001c610001c400074a00c0301c0c221814017845030701031801e11040001d410000010805807000b4034000840e19181e98400c1c00000c410744212800b50310480080c080c05400002e1880580b03006049034010320b20240346990b03a4400e410000340254144400b0400e484440c407070300e5403102100c800080c400d8401d1140b0b03503a003802c0c00c60901038690400d000020207040590105580100c3c030006003440b940c40e2405070781150b10104a5104001c08803030482d04415080c400f0f00040c0444d4198850f5000420003000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 95035279 1250 95034029 95034041
    0x3090f01090b010303082523030f0a111c0507030c14040513060e0412120b0607060e0705061207021516030b011806030f061a03070f0e0414060a08010203151207050a18 73
    0xa00301d040e0410500142d580d01cac100441d8801e00002012815100b1160090740600809520b08400c090700091070f5006401d40e0445442231710282e90401542000c840211100b804280d58001c00030002c000c10310540c10b01501014990310014070100303225507262080c0f2903034441181c05640089000817030114140d4480548284203d210303c09100c0000e10f013000031810305c100c0b54000e001d03075503922401843d01c1007800150010500108010f032134215070b201207108250111021401805014100002d0702951580d50303004014030343d461401039850510640013070040c401e0039414000300703c00d41d4000700e5400d161800902580d40d0041040510786200c1415110b1907088038444079181d403054141d4004290591368041c85601c2d0403010700460712016500102060300c040c1d00301e8200f41c03000340c03822058030b80a0b01900003074440340b42c2650f41d14030305030817400180d5071402c140555040242c1c040c07801c04441040d040001e070950711440c6e40c5800061240525600801c24034260445401030480e19201e44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 95036529 1250 95035279 95035337
    0xd14060405011b1b02040b032a18070c14060112060612080a0c0317010e0f07020a0b13020a08070e090f0a020907030906020d1103090f01090b0103030825 67
    0x200368070888054054240d4120345104c0c8522155004d0079962141c0109407c80c0d0060107550140d440060038107090700307010b2084040c078200b00820191a080400c0040309020040c50300036000c0c3c481d450101c45490542c0b0f010342c1c000001114000596009000090003011516209c6110354545d141c4401600c08691181e54000c0341ca411071408105050201d40c07011400c1c1c50095040d10140c5415581d0300e84220790301d1010700e010000440d945c0000c9003098061010310311440d1507551100d85c1240d9031408110000d080c0c0d014a0041146541400001c04141d44001d0882c1c02607501d550145180c04d1055100020b5401e9480600580c81010300051001c808050054100740f4a50f4021076048440a40172804040e0303a46034103014000c0c071380c0c1134407001d4010070010710003240300c2c03a03120301c2c1da400642d141c01090080d090a42050070051050640c0590311000c1e040c4281c3c43d54600f81c5109800801030320020441d603203011920680c528129800c03110799210121440500309a141c50302c154001c1d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 95037779 1250 95036529 95036561
    0x7030b010801080d110f0a0303020714010b130506040f022110060f0807050f0c0604020a170703060207030203090a06090e070306031a04051207030909380d1406040501 73
    0x61181100103e846581140c490808119001030300000b1072610541b0300c60b024503402800003980030581d00d0380003001240d010725068006d058003d2000b0717080300e020140706544020044000820101e0580102d94059070041c40040c0c2c102c107503d0354a0a0f40d00455101d01c08040010040c42d81456580300260801034010440303685d6818034001914141c03826011105200071b48001844c0a840b46084920b4084920391554943d40001404c0b0755469017035604074420884e000002c90102c5206102200d00c007851001003014034519101d00000394496942a0704600042051401e607856120001d4010645595070400d510300d09a880c0c0942c1002404c844201400c10320200b0108403040c4130348040f4580300d500700c841d0307403910702c5d08610b4007103200c1058905e502701180f503100381600400240100c03090f5440601010080c9042d06071a41c0161590106c0481850800d001941d14040e035860b107503101600c40c1c500c3d20280d03211609500200c40c45440d85901c00000c000c20441c0078000c0140003551112 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 95039029 1250 95037779 95037781
    0xc012307170a0f06051c03030c020f030d0b0301110310030c05011b021c060617060a020a02030403080a050409060306060801140424020f120105190e0f04050c03010c0807030b0108 78
    0x140200707000d0003a200c000c005403a0400b407403019842d94481c9009003001005c0320410280c044400580c4a1302c1401640840d03e0002c82842007400401d03c661464940000341d40340c8800009850010300520310f41a070150744e07039100f440381c170f0709118021406115a50a41c0b1103852852a0014195080350029030401a9080b54030141c10f04a64890076030990490302e9070076949603c1c02c00110700c080040064522420502d000445e80056a00200d800032684203079003840c1d9400b075510042e48550700d40e0300010f80c402c100c200042040480903211140c1d6602d8180e01c1c10755168000420358095401c181e40d06641d803103003008400400d2040150300c1011083c80089803903d5102c82e00c0c00000d00e421030186103403599401045a0617581101e0f91544110502911508003401a40c020102402036901a00e4811800e0090000102d02c05088072205280d030f08103540c3c0d007030540180b040094012200c1e4881c3c0d07424043c46640a0182d006105d586544074106403070030044c01010b40e01c0384080035050142c148 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 95040279 1250 95039029 95039057
    0x6070201020a08160e09070807031d0303041707060207050c0f0f0a060809030702030f0a02030c03210a110a110a1505030a0213030b0c0703120c0f03110c012307 70
    0x1400f0640d101280416007203403011081d0090f504011002c0c141d80d4001c24440c02c105ca0a908079041030301441003560100401c000364100c035802010a203c50701c21075402480003800142c0128102140300300b002020608240c07150f61000f090f40c001c0303081125180c118100350b0015041a4a1400650404545440301280942c004c2526600785006200c100910100083c030342c040c003041140c045660260803200100c0c2c00d203601300c0c0c9070b003000d100c105d01c85d000da5a07800e004e9190004120200403a00140034038a040062030585a9600140c2240140000060800c04104c001d0010103801405000b224020011950030030505ca4503941003a0f103a02c04001100480b194045d0030b80c0d0b4000100e000042e9a0640c8426a8071141c1046c0d00080030340800100700041c400785000542161740c8291030701d50180b030541016900340e07080c10203500300060a804c00740784805e20036040103c000302d0700f0305070740d1910130a00765603400d6822000141d1307400030090318008041011019010741c440f00901c0c0c0b1100c145024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 95041529 1250 95040279 95040287
    0xb040b10080601090b07140c060703020d0c050703060c02100b040c0516020607170a020105090a120f1205010f05030f0c09070c050709050a0b04050a0b0102030d0c030b090705040806070201020a 84
    0x9200010070403a1803800a1040c0e405200010042e00721103a0690300e80c240c52418a00c5000b074038a02842c1c130300940400400c24142042607644041d4140c0191402c42080e50303040714800d810300c105865074031035600b000021644c103216441c02014958081d0007050030380c44100c0c0940d400d0030942801140b60501d14000f069200c42035501c110310801d00c04101c0407a500016007540183c041c064100c0908030901421071034142e00500030420300da0000e004994070203075003a4403514a4100a8043e030711040241e0340c428400e00056031804600e0070010411040b810b4503400b00d0354240c004284001c141c00e414842c500d4100060004d003024640101111840ca201154203808041d0850040c0300c51105134108101d070074000348000c0d00d001e40382000503140c082040c10180240d0700050780218584000302d5200b000e68040c501081d081030300190310b4801ca0070b2903100101190b00d144401c25a46410264031980d134800440d000c3d44072684c03907644850801c03005c581040700241809055a00c100804007000c2c0d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 95042779 1250 95041529 95041549
    0x70e010c120e03070306140f07080c07060903030212010906050f0402040f1401050f0a02102a0e0d0204051501021e191e0b0103140703020913030c0206030403030507030b040b 76
    0x30340c2c504500d8030074205021a1038903040d0b80000340724509210090072100a155030b0380c1c1c86811210146002d0f9114480c06075102c05040e610440240380070086c3c0808190203400c030070700542c40f0707280051904496806105c245102070700700441c9927444010402003450142c1849044201c00c890861601d442d0405c45c0740707010110300c02c540d07001020308070490260b802030702030311545548910303082e40e1000c107640000d46406058000040d814030741b9401d4000700d02c038101881c80380701c944607511088040d000802d540750390100c1d191035444600043e0a50060300c5a00801380504480d4401000008034640003a080c0320030003042840300c0c80b00342d0306082440d0380010f60316404070050b401c3c503110201c075050945081c0c20b400b0001c014003c031200e200301041004400541224002c01500301013041e881c50880c0c41d840f00e40b20281d409907070070001c50444200c1041686e00c0703600c00d090012280309140d010560a800842d0146c0209540d03904010110b500350150a00111045504201401c200400200c0760b03c6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 95044029 1250 95042779 95042813
    0xc030b03030313030c020a0311031b030d120e0a11030c06091806040917070507060201020405011403190501060c1b0e07030903020c03030408030414060304021c061b08070e010c 77
    0x1e040481c3c3c028180900c0300d040c00c168000c0c0c01c2c6105661a4100311b4203d10822445c02d009100c7c032040384c4203c80442601504d4050000d0240507404003004048418400707245c1c0814040f942e5503c8490300d07000401448800314819511244800c90002c00c0600340003508003014018202000404855502c6540c2c0685413041c2c002c1240c215101c07203020a0040400c20f03001801d07005542c12803100c08040802500c441480755007210101510f80b20f04a00340e002e00e100d0b0a002c5104075280c403805050b86805140d10800400409000701c604503400020f5520a0b07014002084e8159150400e00120445900320403110484645034170b4941b010141921000400c08400c05956500201c1014030900180e0701c48240101140d07200c1d07484009450b00d90748248150407450b00506411201800e00d04180da2040784c0040004893320828a2001545120410121071442e07482c10481c0c91845491402d4000041581d03d84846151011014285c0d040c2130444ca8107020035501e5010000342d10859041c001c407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 95045279 1250 95044029 95044051
    0x109120b01051210020301030c03050f0703080d02070f0503040905180a030909020c1507050a020d02010b09011715040f020411090904060b040612060c171003020103020f0d09050705040c030b030303 86
    0x225100f02541c20b08000040c2c03007200600010000082c030044403d02400d0324007a2060360180c120203c081541c443d202d04c0000c10010381804800410300642e03001e803103118040c40b800b40c4100c495507580c40c150703441a0013105255554600b07000b581d14400b1010160200000c004103461611600e000d041d0140f24454a07044a40020b07200340440b50a000103a09419401d00000390307800c0c4104080e02a40140c0080d0300144940591400300a02c14040c40b50340d104040c1c0031a1942e42030203180319482e4440c480d01407440c40b4000000c1e145441c6009510301c01e900035403000f40e0707a50513807040105955094408104d0001c01b03000070042583c0343c90003d500264021000100c1e40c3c4050b000c280500529032080200c41e08440b04201800b046401040b00c00b40941d50720030340f25141d405d402c0d09414003501c415490b02207601084c40154000c4d402440e0341c07007030000c845007022030485025041d80c40d4000d00722003607041f407082001142041e00500c03c0048640c00c0a0240c5104100801d6890000404403d014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 95046529 1250 95045279 95045299
    0x1d060d031d0a0302100306090b0105042409030b070306031101030b0303090909010f0c0201090b0603060c0d020a05160f050606012c060f07081306080c0a0509040605031603020109120b0105 82
    0x640d035010b007072000a550140421024101c040c1c8060000e04040c460b6843e500d082c0070305940c40b0b40c800c204541c2503d03980178000f11901c440c0c8410200c80c402a807064030a1000300314012020820301da030598032400d0269004200c3c2401c601d01a821502190030749814141880411812654080107135040380605440084059440d580e0840c0500959128000354a15005c210054584d0640203000d81600844040f84142c13034107800d0540d100011142c0e0b410348001840600381201050b0000c000f0000030f03249c22800e00c0700c500c9142c00107281d04101152210403034844002001414019182d2108003401c000b40b00982806040000c010921031200403c2c0302140b011704695a80b000352802c0d61442e030485078880c603051615044503804520100e034449800140020640d00c20234145109040c1d07019068100b03003640100742c540b6002000043da000e625204082007a482c100080e40028880300600a0800e1460002504005154100e0041e00340210405d0010654080d0380504481d000c1c0c0e000481 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 95047779 1250 95046529 95046587
    0x2301260d140a1206180b060a0801030b09010f0c09080f06010501020304050d0609060501031109010f051c0204200a0e0d08221a0304030807080906060f1503011d060d03 73
    0x2c000081c0d0340d0020203c1c40d008000c03c0280700504042c014103201c8000704000320081b420442c0380c0c05000c10780e2000030501c100602c0059001d107011500400c0d640b00114900d55016040300680b4400c05004000419803501000300f0340e0200a0840c0701101e0708041c10b11b03541000300007500c900c02c4e40521406503d00602c0c80c010480309501400c0d03221741201081010396168a012070764800b4550314a4030075401d84001150303000700ba6448008407a0001c00421440103e11488840303032025002c03e990065881100181d40031883d008040e0910603405490b954800203007001e171000480140040c0a1401c1103122070020341418210313444000600d540945c101a402100034010000350803002900c824065548a07200c07620000d035004621a407103142d0140d03554842107441d55011620407a40e68000c80101d210340c24178065040130358102a0122644000d010821f00305c80d482a4020000d1401c07078010b10070060082c11a1580194089403248803101312030b180100040800702c00e001101d20310544140d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 95049029 1250 95047779 95047787
    0x70f0b070216080d02010606020601060903030e121f05100308040b0310080d02010b09130b040f020102030d0c02030705120307050301030b130213020903010c0e0604092301260d140a 79
    0x80b005040301c0c401241c6600c509102e43c55201544101016608044001c1091400410341e40d042c1c951541e0380c98042450340d1002c58188000c0082182c000d04501200384030680180000041508042c0551038058400c04614084070001040c007841c0340b034410403d2000170514802c4030700302d4804400054494407050005460074115a0000f0028891640c0a024294040d0010405494111100b503000d80d20101000c04038003204000400c520b800b0400a800200343c0030b40600d4503030042c4100ca08004008a040b022111078201d440b0241e4000300792001004001c00c5450088a03c0070402401c508042c0406400e900060000401c1e4920000002e05c00004c1841a41c40c19600103000b008110000d96056000b5400514054001c1d42040346441c0e0b824024403c142c1514805000d035480e041c0761810b00c60042c0261008042c41c2843c03462007140011805881a018141c41c0108910105640e145840c5032121f000c04d08036282c02c40041c2d07500b00758110384402e000c041e020301995617070840005d08071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 95050279 1250 95049029 95049043
    0x31e090c030f0a0605090105011410020a020901090f0b03031614010902060d050916140d020301061a040501090905100e1e0a0606030c030902030604120504080d050d11070f0b0702 78
    0x940c1610950b800c40c40000c10000e0007003081d40c05a042040982c0303500708500e003a02c40034051090224000c070a40d96440c1844004c0c103001c00124810780326068100c2d03000403a6a102a846001190703240c0142d20704c0d250052040900c21141100190302e84000c1c42001d14039039048242c00b0345141e9000304083e02c0700310290007003a4450b500801c0141c0c4c400310034036000d0040805480407100740c401c101d039001c01283e08109040585599034112400103981100700002e054000d041281c041d500ca000004415112290b29620301c09580d801e2501c032800c00000410201d000c0d4001113840c6c4c10001481240c0c400007118005507100e481044246985504025075101c041c0c29408500380c09440401a5032101d82e40424150388481e038043c04500c211003011026200c51340c4002e50703d070700504046000070b0500c618456805501e030421070309041d43c5800450414022007140b40100300300103020103100c1d5151050004600300c0015148c01e1070140c1e00c42d0245000d01d560000c04020340000442e0085000700004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 95051529 1250 95050279 95050303
    0x306120604050102130509040506040611040b0301030501060503121315050f0a0806010809120316020a0203030a0f08060604030b061509040e07080c010903051203070c0204020a0807090902031e09 85
    0x100d00c18101450164000c0d406039010581c41e2030851808101841c04c0090503000329009001021a0346035502c40000600b00c4d100d51104c03140003008000f4141d00028042c40c001c40c041c00c000142c891910b4181410b1040620040031a40402c00500314455490081d040079980103045041c0300b241c0043c400e8559100348494900d01d0390011030366894096102c6034180c0300d0b403001e994818998803850700d820fa86011b00d6036542c403000801c0c03000811805849400c0c608950b000c3c41250b81943c03241d0046804e42d8040c101801c0001e20341c0314401d41d00358011080716007004050700d00030b103041e1468581c50910040503103654030a6401450402c502e0030211f01761b841488000380104852a500000340d030740c400d094400c041c420701a100c04141c281d8040c0b1a80340450f0740150241203e1151541d01c1020341d40020111403e0040c0c2c140103101680310340c4003903d0451401e480e40403490403c201c000d0306843d402d50200b0400c600420401254501c4403140480c0100c03102c90340d00b0640c95445109003026034109003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 95052779 1250 95051529 95051533
    0xf070c0321050f04021009060210051509090d030b1009051e0a090605030c0904020904020d03091d0603011b1b030e090903120c090a2c0f0703060519050402030612 71
    0x18082c1502803c0c6074a80124030854145041c0c02e60741d401078a000303480b03104030005070b003142819816006880d0407056001c112039280d81d601501e0040050700c1c030b00080e04c58020540c82000d200b41d900350503110309885540225401264000e540c10b004051217002d000f1940520611404800140c21b482003150f60100000d00d008141034a88041000a00313440c0300c0c59103c0d01c940150b08501c0d06103400c40c2400741d900a400104035503038540900420000f1081c089007000a14140010403050305059400308140c50103c41006050150415094034040110150f0070088224141c400b03980145d803800030001c050001c0400b60f446030500383d84202210701601d4124822070200200580c020000b022051085110210305807502c01f0302f01a180544120b030b94005d02078440510880000d0550807c2240d0b86098141748048510208a40b42c1c0f0141c800000d540340e04414071000301e405006d003e002d46000c0c2c441ca498845001904a00403610348111402254004045140d54507101180103854a03e141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 95054029 1250 95052779 95052781
    0xf0209030616030f0908070b0919051605101e020a140607020d05041401210c0201140703110405090705040e04050a0c17100f0e0714090f070c032105 65
    0x10b500140080720090341d500080c039141c0c410600e040c1c180f00c3e00300f109401019150404c110395032440c8181c00b000d013206030303507115220001014140c08111503000c540701d00042c0c01c0140c004804800d0121585d0402d9108082020342d0aa946a100340c1420404441704a18841004031850a0341083c01c400b401a1028030000320012007030600098082c040c041a6007191a180104502103620b0b0185000f20310050050152061f402e612901701d005075440d101040349010710811081e1401c03508000b419a0260351680707848645d170510a40819808459401d050007501c0030042c100030244100d00a80740b1641c0824007098003175220341d06a0740a0500354015410311f081600f1700f5542d411201d5400c807084007001001041154540d40a14042c0c4c50040061868000781e05014020300389020400f41010b68848803000340420801c0303c170000300524200c50308244a00c41c00c1c06040d40004020603d5804104c0a20100b1a8000303204040c040c1c05180500d0440030000781540d901841285440125040c98 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 95055279 1250 95054029 95054041
    0x306040b060a0b0a051308010605060703080703151508010e0709060323010b04150912020103020306010e0423090c0d0305030a091718030609030306060d0605310605060405040f02090306 81
    0x103012415828206d0f00c8000e980d000100d00780c4442d8014103400c603006001001c0040d002d03506094110041c2c0c20003060074100001c02c980c150302545d1088030320103206104510044c1e0000c001d140034002c0c4200e450094a440d08016000b01c075030b480340100301039030744001c82000300c01c814588500385150000344100e945d480341205030075000b074010895405a0310014204550042e01200d0840e14030003401e66001603680c0054000303400040ca80d506102081c020308086030b0b9a8071440d5440c444c001d00200c40000104186802130300c0050a00e17895621010300c1c007582d9614801d01e14040c0b5071614001e65207588002d8443c2c0506036180e00103011100001d050303a00120580c0282040e014000512180300344c5007420941c1d111001e50300d82c20103410810124195060240007014440b20b510b40c0400c0031641d440225581840318503a022000705c50014940076800344274004034040e02d090606010007418030002981070320482c414a4402c40d59071202c00d0103640301d42c06441c00350380028142c4070145808 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 95056529 1250 95055279 95055287
    0x1b05180315090109030815130c1107030c1505070807061d1501170d1d0301024e01090b0d061404050f0d05180f0d060b090c0301050306040b060a0b0a 65
    0x240b40c200c0200384c46d000012803140040401c800c90110050003c1010300b1008509030040200c00b4a80080100704c081a455402e4100f1002c0004c5106020b13404445241c009044414103112580c101004801c010701c40100c1d4240d004c3e96034071900601c0018011003d44a00080d40c126180c60300c4003070048001e000c044443e4005180d048402c078681542691408210068503000d000f0b00078401b003800034288041c1240740a09000607a900580014a00103d60030f0810740c10b01720000151420b030950080c001099182c4074580100d000034070580c880c852511000c4211040140101403240b80c0c0c0d51000c0c2c07865690b6581c031010494200408001450340d43c040c410070f0301800c8805584511900b402400703a0000051801c0407804c8968801e82040d00300210511184070404299601c20180c2c82d00405958401114005448c4982c0000172044500c8061061044004004010340103007031004011949012900f50340c89075029144038480e95170400064442c10180e080001440408514045c8072900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 95057779 1250 95056529 95056541
    0x2180622091a07050d0905030f040315060503070602030d0b040902040203161404080705010e060c03040602071d06220603120f0206010806041707051510091b051803150901 75
    0x1140c0282c10021036804100100409541800000d8410481c0c19000c1065a0008a90030700c0741042e030349020308203402c0c0c100a0f000340c0c000f511243c141c1000620303290702c103210318001003000b41e0240111528140d8003035128014102d12100c801d441e80300c0d401c11952560300090926a00410454403030400d551803001591809002802150b0203016404a400d100001d440031121300c02c005126036400e00004550b204035034070081d074014406021141b8080001d01c0030b00040c1030720394020b1000340c1ca06401446003038034448042c00b0074207500050000645407481c091388501907025001600d2081900030314000c00580c1e0028000d40c00440b212403401e40d0281d98403035000210340c00c0303e810366280d0992a4031b590060724000d044a00d04040c0204040104001e0000070780114140c0d20140d413030381c0810707501d08030440d420901581d5011083c0036564042c4281c920018900306688549007030443c0180861041d2500148406144000d540b101d98003040b46100b2a11400104a040c2c01c0c03810160f0b01a00d8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 95059029 1250 95057779 95057783
    0x10f02070b070e0303030c1602100809061b03010603020309030d060803031503120901081e04030918050f011806120b0f010608090a02011209050303040b0a0507020106030218062209 79
    0x1e100210701000d2003000c100d40710381801005186541c48200440034030741d01600852401060148489015942c1c0701d00da01003003c4c064440d198985042501107040131401002ca041c54501150131412182c000d0081d00c0c1501d03001e060040c0d4035240d0500c0c10749540074900c0200c1c5903070b0802d880840d0a10002c400385004140b100f0659200c80014010180c545503010441e100e0b940041c04648030541c483c43d001600400220752907a8005c10a03516540001c8084030706401040341d120341001442d007091003201002441a00402141c01e01c49034290741c80806103c2c4c40b000c0d062140c514103001c01c480d07101c00000c01721804064081c52061400072460781046940c03051550070f2500004200d80201100b43c8512014800341a103003000b5401555104c807010a25200c0981e985d000070001042080150302941c020101c42d01c540c41c1500165003520b00041c40c920859060800400c011b890310780001c0964204031406240135600e0001140d82c0540307030503400240030410b04400c2100120b991020101380c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 95060279 1250 95059029 95059043
    0x130b0109090b01050d02130b04030b040512120412021f0b03070602030723010b040911040606180611030c03070c060801050a030308010e04111003020406090512031b0f010f0207 77
    0x656680000012210b64030411400701d0010440d00d0343c07107409503000701008030f02020f204008a03121100da00443c2c015402c100c843e80c11410511080c042c042048000d01140b00248034030f440100881076850002c0030700010701c0e070004c252441d25032034000d001c1c040c0810140b6041041d40034104008001500000034880d000c1d02031100041549440401111000e0380c0150b01240041002070100d0070041c020005481d03070303544e00c005481859942e03001d44107402c1d004800d41c448a018003070800040f221182e002e1010f02c8103008960300740340d014801d6a02224418108a11214209070455046100300201020340d07010001d555001c20040031903c20030303203426a0ba03031880c5030789030018041e200b0784a00000e1f011034082e40040050301d540c40041c0354018400e42310103410a00f4400400c42d580d5401c040680403075000718040c403007a68424208801050300b243c1201c80b8047c20543c0c85d4481c0304244c8240c031542d02c42d1260001c2c01c48200206412031061500800ca495003000b500301c0250808201102d0705 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 95061529 1250 95060279 95060297
    0x10c0e04020301060512040f080a0305040615050108011e03060501080a050607110a0f051009061a061204020f0a0305030f030403030b040e070e070e060c010603060506030f060403031a130b01 83
    0x15003490310a80f41643e0a07a11514500080300e00d03241c18801005208035600107203500c0d80000908400080c1503500800d4501007180e0510341b404005440c0e51224640858481e8241040b0307981e48584420704540b003080e0500c04600800d801d80d100780c0c035160401b60180c0e0503d000014a17407000620306040c2401041903510036100c0000407200780c3d42c400c0d40e03100b513a40302c0001c11010031804503040e0706540c030a50032202d80440c991030681c00d4a22003601a0b407041d0b65008507845038450301e662540d0704001107510034500782080740d180c05c9014000e0305c040c0c0211200b00078090181c48490044d0055500502140e4550f203280d04460300780c0c0d00440c0d0881c00241081d8041a07103007403e000d0200c40402001c09000d140d801c04102d01d1101c1001042003080103002e400c840d02603100c039002408402d03201c1001058050440c02d141054035030141010313000e94090b1104521142d400300d0025000360381490042151005070b0000c00c000f2010703a02d520b9024a460310b03040d02c0c11116034055818503500fa210318001c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 95062779 1250 95061529 95061557
    0x303070e0105070c030b10030501050a0507020f0a170c070e13061d03030f0901150f0509060f01170915071e050913020f040305031c14041110170702010c 67
    0x203280245040101801d000e18405c0c400140036845640d40444031040c2500300380d6503505c0d0b15080d2407007560700e03042240e59070b018402101d0381807002d080380b0045603009106082c20f50707580c1a0503001443ca01c012409001c209521211400e100c8000202003c40d61114241007203206410300b90340c42203007100c00c0341c50454000d5802040c4501031080f644a10042d605543c1d8113130340203921400c002d001c1c1000e55a00e00041d1000080407a00b400503016200050314468102000c0c8680c08002401e081c2c4102c02c1d4000500b483e83c1c2c170850141080707050b603040585648500024034900040d10b00d10580d2204d2060803c00710907030003050400c1011101d900c01c000711807211030683d258413070600d50039044206044e5028094502d50014690341281125251074181c0e80e032185070a60304016244200f400c2e1030070b1078084442841c000c480d14020392000250640c1020345d01c450183c50384004141c05041c0c50551940d0850150051001c440a001c682c46e00d1440c2c2408024028208090300c180864980c441c4101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 95064029 1250 95062779 95062787
    0x51005100b04060c060902091305241305030705070e0a0f050411011b020904030504080d05090102031608090a03061b0509090126070602030d2901030507110703050303070e01 76
    0x20881d20180040c618090508904803203404420780e050305c025464070403e00060301c0c0c4103c56845500d2002d441ca02e99040b51a01c00d04003040301206a000841006101d4039410300900f000c1d41102054205013a12296840c2c00d50031402001c501826038042c0d00b80003e5821113064032a84280281c2c10108400380ca080880409c64a007680c0180031800c680c5507102c1c03154083c40017005a400d80c107103803a06140b11940010503c0c0c2044034110000b401c04541000350580400850715100c481c1d04141d401d109842000070764034040d4a4450400790912800780d07040c001000c0031154041800f078010382ca040d4030b83c00c0c0040540f00c2040000e0081412000c2e030303011144070b03800b651004c0c04014800d035400e07481c2c4031131400a0710518440c0b443c000403a486500e0040400c12907100107100e1074014548521a6211110844088544c070188501324000545003460510030f0010f8007803401d080c005a16154140c08441c1c995100d00c0c882a144294407020040c40390000103144034241542d1142804101c14004403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 95065279 1250 95064029 95064061
    0xb120601200a0209090109060203040f06060f08060f07120e1b030a03120e1203040c08070e090307061d100605091b0318030d020a030e07080d1b060204090504051005 72
    0x44207607004040e034200185840000907400032040300004c0b4510070651150402c0360f005540444104100360890410004c071409010014002c0503950a1910f03d48010380e41c0342c9100811240f40c10040000241110b402041c8960110144480421800d400075143c03654507480144a400600440c80b40c7d0740711490b0000306814840e03856030b5807480c0c0c50b20081c940390141409000c181d035140644403449038140c2c1c4080146104034007400c10320b00d84614120f0381c0c030704004142e08075882d440704400c01c0101054002049070120b07030740712000007100031140c1c05421880c400e100142d40280552040600c100a45412610560b030085400c1250342d11041091080c907001c1c0700300307552903000078000108d0495146110035010010390081e249040310a5008401f00d07440034608002081e61107a5101088070208010b06c040c0001500a00c404c4801c00e90140869040012142280b00c0c40f02c242d20402600340c066400900e2181010701007070034540742054644841c610a590a1450000014000024100c1c05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 95066529 1250 95065279 95065337
    0x1312050702010815061b0712030c0c05031506010806011e0302040801050a0e151005041401080607030b010203031501020a0506070503010816030c030303180506101a0c0c09040c0b120601 81
    0x198502212191b0900c100041515411168018414001000d403400704400130303c58480e90396038403c694140340c03904000e007442d003203a80a0352000b5003912035400d800300784582108003400c00901640c2c444004a4403039044100d080e1240034400060342d0b0003038154001c5d00070b40d541ca40c020300c02c59541034010001c4a01c1c041000b201d41c4d01290140204100981100703400103440c5c0c11901d0001d840b0303c04181913420a0102e020014006c1004000b80703002801007035006142072905212245071240000d680b40409400049031080d6000500400c0e03000b0420042000e6204040e594649040c840250071900309104589036070203264101c21114440e138100da410381c0d500c140b81724106030075500d0450040c52164140d0802c0c1c494141c695011400030000e1034420003410740a40d4001d0f042114901c803041441500c4400030724140401100d501c2d01003440120258155070182480da1103050503c00c8160550196100d10300004541360706000c1010000d100700003e0325031000200c0000b00030740c0c1800d005402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 95067779 1250 95066529 95066539
    0xe0a060812030f0c040911070201121401260a0c030507051017100b07210e03030702120111040608060a050604080d08070207050a08030301050f09060a0605031312050702010815 77
    0x5032240c0036914195400c1004c40c40700307508003a15403100004940004a260300015000310b80305c41150b070f00c08490f00d1604c0b140c0c041071102165103079158003850018000c0545118180c1440c80f10380095190501c05c696003d41181c41000e418144818502d1103400181c40a0143d5407000c10582024440c110000381310b523940840c1164060610000400c000d001c4009111400764001070003010203014101c19070190380e5202c2c000da10a40c80c11000729400448006000520380245c006a5001c010356205503010384040e014640c031410898010230010500f4072000001242c0403d2140c1e100d21034074852141a10401c1e820b688500030401c09008511036010302d0f1f400340360354401c2248035042d80390300181280101e403951a185c1000600307980c0550009070803603001000405c018134102038400f0b0004800e689066090a1240c0421900e074124099101882400008517449011010242c518540c001c00104265405010002e09a0340514826400a41c440c00440c14030300b03840081c2e000d0a800181 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 95069029 1250 95067779 95067781
    0xe040c090204060206190603020a080d090905090a0305030624341b0302041109030c060c032a06010b030708060108090d0e0604090f0203070908010501030803011205010b03070e0a06081203 82
    0x28011001c1c0321408030f0368003607c1d00c40000040c1c03108502c41014085074009080300031500540106045030941c06641801e050600f409803491001ca15102c10390381514140781d41b0343e03540c400303e0640400740e90b81016216039402c86286500500000d45030030305002c070700901d90303a501180900020000c0c103540d00d102142000d0304000580b0b92290101c450304030104841c941c0c1d035203800003002c442c904c80403040d82d280001004183c61405003c0303000c84440403111603040003200d600040d13490080c0321085171325600f15400b10580b64512052480001554000c544081d82c6074000485681c10686541021a40c1000450280c0d801a86000c2c42140300000074454250309035000c403565814030041c2da400401c1080007003403180c281d00811006007060600940d4070304004078000c02041042e07010000c3c0364500001070001403c9502100c0c1112001070406404000d0b9051080c018001ca1400036498800d00d2000110280c10900b9684101c9840038204003c6903608980c6444000c00c0302e0030380305104204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 95070279 1250 95069029 95069041
    0x30c080d0e21010c020c0f09040f030f2d1709280203060405010603030e09090d080402040612060f0b040c080a020c0106080a0302060105031e030d11130e040c090204060206 75
    0x10602d15491116042d000b40065120502d1508462981e82070b1401600400c2c550140f40c01c00c030f100e85100440540b000d181c1c1d80f4041e110410b1405840030002c003000354112054651034402c900103940e0900540b40040900e43d42002c10b034030302403040003904c0410400000c0d0f10b041d0b84404015480780c020034014100d004600721003003007203078101d03200034008602a0754210090707201040000d10036885100009940c600b0341c00c01400d1440030708004e91142d2603150130090f5154002c60303100c0120415050486150300d03240300160250a16400a0001d004984056402e02003260052218118031400070841c1c000c0960603c4140c6140c50381c8000852801c00103d0401e96095000740449000840001303009511031180504141c100d52040c1c0041c5c1c4001d005004501d801d0101e00c81d04c020314908901d0348180b41c44030a8807400b44120045009030344145440128008000301d40c40056400c4624004036105c500518855000ba1425100315507803101c045075032401c078800c85040d900b0300d40050000395107213 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 95071529 1250 95070279 95070289
    0xb01091a13062105150c0a140403021e1002010b06040302010804020f04050403021e030a08160201090516170a080405060705030c030a030c0809070501140a030212010609030c080d0e 79
    0x203005101c1c03610b41e40700340001d5642000001c44015100c48020102600700c035080c020300d440008620301311400c01d10003d200d4100c0c818012192052103904100c03401003410550507807079004660020703421903180c0849401c44e20305180e401090840440f80e0802c1095101000c03400c840e40061031941200c3c0c10442440903602600c0c0b2a0f9005100424452058200750b000c181a500160380841c0564400b00d9005e084415006001400c071400700c000354181812040c0007441450b010700828074550100c449598054400c2d000854465001030854044802c0b107200c480c00c3c08907074468595612100160a180c95902060758110070b9080f412280c1054102401c022840e800341c04104d505d84401c00000180220600c007074020f17803000c0e80740001c044500c40409458140000e0034030b245900006014007903681c004a58130380c00b4000d2043c3c2e9440b035204240035002845070301c207010343c480700007000069804e5011488a064a200390710b904101580d40311641d944410200000c804501500c102034244d05007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 95072779 1250 95071529 95071549
    0x207090b0f04060303030e060f040506070e06070c0609064509050408070b010902070c0e070309020301090813060513060c11040203130611040503100b04090515040b01091a 75
    0x1001400d00c032015000241c100c0d6201c0d44218040b030f4440d028030403000414072030f0702d0340274032140d0725a641850290f98050b2110001031100c4188410b5410001c43c540780d400075101e0495010036154a40c948030180508a0310151051000261030604603034001c080101c8520303e175900301480030310b030328200c2c0030750480c001030405001500c60310942c00041c00c16601c0c0034090040d03004079500c0d46c0e2034a550500407403422051f04017090139070041090030001a4688480300c100e4200b44460031260702c072058100c001e403003100c00283d819070900c442e4106201c004001005000000e61040389800d0347c4010a413000d01404603910140d0003841c80030801c05010784a1000c149100707445013044006800d00290890f04141c41c0c02008000e0520410100841740c41181d0712000261580c5080504c0c000c0040d82d01e1042038110346406481d1000f0750100d449a4001100c2c265200b0152100c1405420740100110750455041d140c680001c000020948850310800d0440030340c045490b4840181002171000d000700c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 95074029 1250 95072779 95072801
    0x40506060f0a091d1b0102010c110a120e0a0833011401050403060c0305100e090c04021309090f031812060509120c0309040b041104030210020102040b0a2007030201020709 75
    0x34a40340d40d90100c00062103a6550b11741070454040c0d04108080c002802c48526200b0b034400e021010240d03074141e50000510803503042e4040141c0044000c4460110b4104410740c135840e07040305030008089070301d6070b010403402d01c030018001080d07404003a01900f001e5035200031204080c0d8010340030300502411039071003034081034400c060504520709541c2c0d5a51400702d074200741c00440001c0d0f0328000c0c0822444161030801c020800c500e0582c40609007583d40d2038540c10030a100a1180e9800185e119028060001c8500200308120b000c014119007401c0070f40118007101d00884c0001c0c5030400b110446015a002170b0243d13031206034000d030508180d03a5003400403c009014692107128000400180e00446401000907c9480e4042c5071100882c4082c0001d40d070254040c607104600b020300042c2154071031010303642140c2c1c0494940c500c3c2c82010109178024401c98000501d1084005042212aa0041030490301c400942d840480d02c01c503068ae2a41e1280058000280141c0110008012000b41c5401c00d000300b02d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 95075279 1250 95074029 95074061
    0x3050705030c07140906090103030807030e150f01031b08060708130f050d032007080a181e170604060c0314010905010806070804030504062312040506060f0a09 70
    0x1080a82c1031858071519621031440c004140107070300101d003848078625410190607900034140d0350461343d0150a0305402000b0404040d990b400e604122a410020010b050440b0b000e02c03003079410000750754981c0c44001d000550f00e40c14142c03103292651800307100c184102c41008000d080380b900d030800111481603010300800410f50001c4185004141c0f104401c82a1900c43c3d001011103440c01c1d88040c0a4402c04a403044203aa040c841030007100e0108012584055800040c0707640d00c80e01c0540964851220511010168464030310216100000c8480d00c140c2c0000003d00070390203596104540054a2110130100413a0415000700d030001d2076035007102030500c0890601041208002314460001c6600341e2040705442c0c0c031103004028403a024072420f0341084251411001900c0d0640300071b0064802c0c0d1180d10201305800c6802c89010a207620503400b000002000e081c0d640d141420120340c000c0050350156118001c52022480360b16003101103500c0c102004d040312104130301e80b010300001001c0d40400e903031006c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 95076529 1250 95075279 95075287
    0x30803060a030803070906020c04060503120705150c04050f040504030c06050c0c0a03020303060418020307120302010b1e010801050103021c02070c080a05060a0e060403050d18060e0f060615070305070503 89
    0x83d40a0307000c0d40c45160365550741c1c08011305e80803009152031480300c0c1030ba01451810806200e0743d14081140d00391034542402044c0c0e54601880c1603403401c140c010055482005450501458100180040040303c0c01101d00340710300f80300001003008881d0165001804543d10100c050001901600301d2907010a00324036003410b1100c3c01c20b81c1c60a042150400b1001a0000820000903151500c517290390004150950615004550b000c241d840b0030b01d0068490500c80701402c0410140f00350020258010007030414410741c0480c290b401902d42c00b89565501050184c030001ca0154481e1003030300c0524422146004042c0c0140d64400020b50055405a800a95043c070110392030000308101d2403914401c900802281c070704018050b0440350802a0036416400c60401e110102c2e600c00d0588010000d034200000340b0100c070a5102440c3c8940900c001e1081d4140400601d150401040d070132148e03442c0742d0545040c0da841004100d817400013044860311691080c05401c010a04c10406031000d14070802c00c507850 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 95077779 1250 95076529 95076533
    0x9030804151706010504030f0816080d230703020d110a0c0b0114090606160c0602060a06080f10321b070c03261201050102061f030803060a03 62
    0x2a540c0540c000c880070145150311040c0041c0c0c0500e81d40700d8000c0e004892010740c02c000700002e25a200c4c2e031002501a50000c075010003400f07019412078601914090369404080c4580c50000b04541140c044803c0c018a002280102c0004025034804000d402d0381d4414415a1118016002500401810b0342050750f83c1c00510203c5103484020140784c0c02588400e411845649000c4400e4101600b1181580e02c43c681c60303440d0b0380c807110100c54105104035aa10b85865085e11900c40d18815014043c0114125090004045801044490148030611401d000381602e84440381d6a40000d030544a049038819810170301d81480300d9200c40030b0007401c1c44907805401b016000c214402d40d601d80d4002c420002203802d002903032980c044030302034840341d80f48440d0401c58107848030a80620940300182001c001713402c40031980308074505c503084018003000c840307500e4801c0c1c1d00400000b85403d000e0f0a01610441000c55015083d45404d81d600e10441d000c801181425036070b0701c548640002d084560400c00858001c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 95079029 1250 95077779 95077793
    0x702060f0c130b040504060609030305070816050a0f02040b0312070204090606081e0d030903050910090b0a020601090b0a0b0403030e03011503050c03010b04021c051806040c06110d0f0305070903 85
    0xb00800003903844036144c60402e82044100d8105600c140c05002c0c46120420010341c002090328080c079081100d00d0b0b25451100304039002070b60380c0342c0b00800601a0b000e05004204100c060071009500903542007162007929020b056480c201e40e40d012400300c0303050100400518107030300500019403151a020a03800d644a0b221450105000d00c100362900300e07103910120303000f41041030141c0d03280303946030501003244e1585000d07101d132240e08401d90240200c0d100c8003d081d4012000103005004120320325541d42007000000b503ca403002c0c003424101c6424400d4050b02d91800003820303010707600001c3c1c3c8685041d166640c00e9604003540d8804e030f40c0654884403407070045080300341e003130004502440c05041c040d00d2800402d42103480310b200541c800c3d44180654103180c0303130080341c074201480750020004183c0c450106070103041c04680000140d0380300300002c0104000616000300b040f107441c1c0d110410b0020700606c14944070000c0c02c00610002d111603c4894407035110b82c02468004896051101c3d2071603d9460f03110b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 95080279 1250 95079029 95079067
    0x3010609090b0108060c0f18010c170c100b0f10020c090c0c0d1103040b0d1508010b0109122f1e0a06020a0816020a08030c01060302120102030702060f0c 67
    0x600e1500302040100181d138800c0c01001d40c000c0103024444d10341080c54076000c0f098003c0303c0301c2c004508044c090b02007450740120f054072034180d0095008002200d61102c00c00550307019072140003090003002d418040403c198080d600f444c403030052450207050010380600c900c0440d0500e85100318030405440e0250b03034907181e03501c48c0148000c514095949601080182c50090a1140340040050380c000c000050407020090f0f03010b40d45140036155075140032031981406003540709204003003110480c90000c0c102c5815070006085503003c0c2ca50300c00c0b091742da00004001c24603103c4041c1c440d91401c495183e481c0d52105071400d030030000203d8802100040c1d80400c443d4401c070307005243c0f4000c0b189420405803804190031002040548002c0c4450300c0c440d540e11183e406154034100c075054464041c40d04641e982402440941108400c030b0791503110300701d600c0f0f010b0049484240c0c013400c10350362908039200060084900c03d10441d0001c3c0b034140c4038003841607403401000b400c040d900082807102854100c0590958 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 95081529 1250 95080279 95080283
    0x18030a0c030b04030e12060109020c010b06030a020c0c011809020304030504210b10030510021b100204140607020d0b0601110118020909012304080702040903050d0e0105060105180301060909 83
    0x1101841c0c2032802810384010a408984100b219000007400b8103000200c7d50f040da545228050b80751007030043e045003d0200b001d0440d0340404d003c010450007900c50384c054031b80b130711042d401c842e0726040500c01520f8030b4003502050603045902641c24440020260011a00948289003551801c0d681d8054451501e40050160b0f031001c2080c080c2c541407010407560150407140c201010700300c281c5950788041d41c54803191348000960381c0105e44002468540c0703000b110b41c84001030039244655004050030000b54418012254118080c0c410241d0605000040d141c58a034040c04130a44500d05032035104031030300010001070410414003401071107a84d083c0103121026850380e003005a0000f43d4810060001801007905800da890301c4900355042460104c44107120104121605940d16641491031080c0700b900b5020b500503042c84007036010180d03c80f0003401c1c0781c220340c0c0c010000c04090704000b074240e4034103035506030000c0c20070b03c100c1c242007a0719800c0307992480d8020000222290ba03a881341060718030745842 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 95082779 1250 95081529 95081543
    0x5060d02070c0e060f19081204060801080c100309051002040f031106070f0201110a0b0f0a050a0603020a06200a0f1a040c060c020402070b012c0c18030a0c03 69
    0x140700308000400804030301078440e05680455034036000f40400d0103124424506441220b1a1140d841840007030400359003d4442d5505a038280203003000c02c040240d115106080014203600000160180045686141c0d8000104080411005c85400310043c1a2903801602c3d28000d0400400c181001d43c40144003d140c82442d200b212451400d22004c0c41d503c04004a006072400c1000c48001005405607550007a42400c007004c0c24006461518503004c0380a00042185c0e50b40c03007d00c041c01d14001c80329407260030035860030b100c40e0b518076049a0965445110094024209400500034103000e80e02056410307510025611005415030342103450004034031825240704451480000511003c0e54040c40c0601231040356005a0402e1381d942c03800704203681f08900801501d12840700465489804494006070450103041071940c4810018032480e40d480c590850044101d84c1d40400c000ca0780a04034030461484207094204450b0501d5240c0303040070902c610b681401f07948140e00c001070b80c1c048031402950049038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 95084029 1250 95082779 95082787
    0x30613080a080c0d0c09082107080f0409090606210221010f060b0a0e0a031e03140a080907090e0309040504051c03140c0c0a03110f150f0a050108030f07030905060d02 73
    0x242d05402d05208804008c030340f06424156401103100041114041e41d0311801c0c0c1a50342402c85400c0c07041c0c3c02203400c0450750724100324040c018803000e60442d40c1900c00350004c901c10300c003442400c0d120140112400075004900160072800c07401c1d11000103c00540140004070b1001401c1051740120b07110f5070000309001c0c5012803d0301c040d642c040c0103840d0070304050360541c0d030140c250b84900c51b4400440102a03a020669910078081610035050b01c120280c0120081e0384a210350400030b00fa2003030841e0222a984106ca1000901d1540c60080f0147c401510f00a589031207459018480500801441a81c0d6803140d0700d04641c1070703a42e0742c0d4803406015180e0340014440308400d114060303d84d00508141800b0205002030080348102245481800340d043c01d20110101c50380400d9820800c4031400d4520341e003d4002040c60042c0c000c110307030f07105000021507805035640c0c0560f030900320b400a0043c0d5816034001e000c20715009100b0401010140e0081c01c05040003039440340041c270030764044003820300b44d03a401103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 95085279 1250 95084029 95084039
    0xf1002070b07080912030903040314100c020313050405040807080703090f050103020415050304060f0f020d0b0a0f1a07060218010314071209080c010f0506030613080a080c0d0c09 78
    0x351079036004807031403a00d00e4060511200841d40c6009210030051409000008101d00d4441041100c008540c0140014403612401181c3c4e503c40c0c01d01c0c07098112242c00c3c03000d91481588048102c4400041c810600c079030701c600b0103007404018900103000312400b1608001c0d41c1d020400c801c0107440418441e076034080e0b0305030030042c1070b2842c0592540814103240c018401400490341212000c3d5a91510f89040758807a91603081c244c026061002c0700d201103602d48600465140c1c101e0b0010640c080c490751050140a40e00400e000c0c000e9514850404124070160061002a03481d07405408101c51001c00b090600300942c903184101d902c000461036401c001252032041c956014000d1150044c1e01c41d0300c2031418500104045c2c07445e5070a248400781250345804040400c01004262004a02490b000708403090348a80908010141138614078401c1c4108400180d00006915245034881d91103403510782418580f010944000e040030b0300d201502c3d5028007140441c0c40d4140304040d00110f0035580c2d070b43d40c0341c0b0740 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 95086529 1250 95085279 95085293
    0x20304020a12020904110105071a100608010b0901050313060212010f171f0e0604060902011103180f0406090c0f0906050406021b0d12050d060506090904020d02030f100207 75
    0x15886211601c002d03401d0070340540e90301880c2d20b5205810909584e050b00704940121070fa0700c19484018008000014a00c40d6956085c1c501d030700c14500110380811007034807954140c64040c400d22610070314080400902007594400c10165030464000c0b00c400c20742001544d1020240c4c0c111036003074010811140d004001c503484804004004102141c4d12000e50104a81069101c03230701082c42c983c0d203c240520450241c050b40c2d000ca003600f00220300f0b0303072800d0805103089809408031034030690000394403588082140101100301c0c0d03a01d04005a80420b07058491f010322008002c3c07060201d5009558400000b03c0046501681c4071360749981c0e80358149507983c9800500040c0c0395401c004200101484244801600042e881800401203080b0030801130082c0c0000394060140070300100943e0030007050f210081d805c00087c041e0480c0003030050144c16220403e0050307074009c9440c91035000d1000004a009800d0001d04c2841e002c6c009410340b40c0b10182900001d14000368144d40b42000c5500240400034420b074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 95087779 1250 95086529 95086549
    0x106380f07020406120803061e03150604050c13030611091201050405060709050d0b0916081b0f0603040303180501020c03070c0e010602030306011101020408060403200c1c030e060d02030402 83
    0x10340e170f07a464107120103480700601404010600e038040d2000448091044410296082915a005080b207031700180310b604c4e48000c14020b881c0180500c3c01c01020601c82640c0505444d221010b003c04107000c946140c0b10040900300000b0420700030380b02000600000d4940d03148805440701d000c8004503950a2514006c0d1802c2c2c001424501000b203510703014403683c3d5400394200c044a8000c4060000d81e103500c42a142410800f00411082100024002520302c2e0003042c001d0b030b640110100703400c40c0c141400c14881da00300001e001940c4800200000f8000030b0282d48140344030715055175050302103074095840c917003240d00c1460392004076030001c5034101c208241c40e1685030290115040800e21035245c840003942e00e00020344414140940c1901340c003030070b01c0258140c070024a217071030031120541402d040280418002c0440c0d80d07a13820b018009610100d40014858555402c0079000b241020301d01d002c41400152914012401c0003961401500640e07120b00162100c05010100141d0b20700f80b603c100814410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 95089029 1250 95087779 95087789
    0x312180f02011701050a0b09010509040204060e010807050a1b0327090e03270d0b0c0d0e1b0103020901030b04020403060209270601030209010c021f110106380f07020406 74
    0x20411005101796103070300d00140c0480d00b0000e400c5032a00001c000680780ca000b504491500030340f000c10005080c581c444400f295003903080c2ca80c507415072038180e4112000d00c1007146c0180032070305151400c0daa0003000510069074502920b42219a1051858042d074911940701c030000002c81046420300c8081d496200b58610300c0300c944c00841c43c002201074680c605d0403107070080350358041d12290101050b0303d0b00d50b0b421540b140e0100000708280761400201c026a00300c0c850714401d481c0703082c1d4001c40907040003135000f420f100b4580082c03025510000044001e5400800c107207040580b100100300080c0c4880c0060b00145100340c40c09600c455500b03003400b50301d024041c9400c2c5540d00440d01d11349818800300b450760f0041400c2c44c1c050780c0e9499200051b00e030450328074030080d0422016146049001070001481200c00b009685c1c032080001c80923402400d8803140d00426200b03201d00400041c4101c88410641c110414842c80c0074540040d00c0c40116540e00803100c40c0d071800c10001800c0741146407030310920740581 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 95090279 1250 95089029 95089067
    0x11011b060c020f0d020601050603061c03020129031b062a010b0103020a091a07020a0e0a05090705060a08040c12050d0e010503010b03061c060216060b120a0312180f0201 74
    0x4c2001003000707545080600c100c5005000001c0400c41c1e94513020011035445e101c1041c0c41410705c1d01464000c3c024600850300c54044003038041d024440c0c455482c2c041d16100d078018000d15000343c51524015400b0f0028a085500c080d0422111140c2807103440c0f400350000009030080c0309003586440f9103007510005038940c0e041602c100841082d060300035142c1401c2d25017035203425030084000e01840009210710710f17000e50f00c62055000007540700003481d59548960540902440192219400c956840c0c0c0b850155a6000b4810301001401a20401c0540d50184c0110494541607982e8680c404510380d6100e001c1c1c40c140c000c8401c65002603000420b00d84030600c203203481d03860356240c84061202804040d14903481031124860807080c141441d400882da15400c040219a181c402071740d10086103000d20002c46845041402d1000149810001d0303550038840f40028080491050b901203c1c07640c00c80702c095a1269540304d0904c02c4c030895603205c181c000c2c85020341c1d0716024072900001d0119426014802848 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 95091529 1250 95090279 95090293
    0x20a0501061706011509150207080a06020403140f070603020f040e01171501050604030201140910120b01020106030209180f0601030506041109161409090903030105040b1c11011b060c020f 82
    0x952240a00c2c08450221030329580d07c004074842203050141c141c0c4402041d118000c4110288a0941d00400c109ca209050f200103c03c42040020740302e48110781c1c007840e41c1d00301000400106000340c000300903144004406914050700c829000d0b1000c8800e812038101200303615299100030301c0c200200740301d641d448003801c0794035854040010140e1145000081c1001000d07280b12207142d0b44d5a0a4070654031005140300400b45021600521030b100c1c00c1341c20843c0c1c0341001049002940107128000943e5005004009a070391094004403190840c4620394080d03102d1100e81c4c503c0804c0c14800c490213584100701424150070706040c00c0b24401c0d243c42038240700760031490a101202c100728024588100382400c01c0c1c1000403254400600b0790140380d800d02e810504c3c000030002080d4010004606982e0115000c019600c01c01050000c80007803649001421f200c825052f40100323a8030f41211340ca0640c145070845c00c9800000003040003045050302110007a8440c1180300c1450b0701841107180c114503440040c512 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 95092779 1250 95091529 95091569
    0x60f0c030f040320010f150f05030303220807050d1d102307060e010f02030c1e0f070305120c0a0207031b09060803030108070f1a0a020a050106170601 66
    0x1400c070001e440101440380c0c40b041070351600c030114502c12502404000800070a44926205c0c006080700c8880d403607503041c4001000c2052016040301005540c406001036085540300d400d8000324142c800c500c01c0003d9065080f880010304208010026584104c001d000507000b0380720041e02c0b402d4803041c80005040708250030780c1e01ea03c0c0e080e480c0000581c02c1c50401d42c002c0d10420140c2d04130580d4101031110100014190007804140e41168404800c504020044030820b03040080072800141c0342d070170900303008200c1407840318249007110508026020a0760310300340c00a209841e140d031190300200c002c0354010a05022410700301d5285680105089021032500250744402500c49610b800018441c003240d294648810001e000075002410101104000c00d03920ba102c3d460ba25002407142420a104442020600c003d0580206040301c3c80181d0080f030501c1c2036840d01c9807036007100c210780085103d54480312001c503400340900c10007002e081002800c11700c00804081e0030000140c00c43c0807166240c0c902512 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 95094029 1250 95092779 95092801
    0x2090c1201090506180604060305010606020706020609060606031303090f0608160c051c1103030705070c060f0e04050a090209040803090c0f030d0305040804030501050423011a131508060f0c03 84
    0x3403a41804807040103170b507541900080c010422900090b02039842c0c00e070042001d503000210001506c05907000c0b10415554a0011641c5d100c2c11600c41d030b0030030800c3c800706003404038140c00300031010b00c030342400800e1544a01071a20b0740c60a070b41c0f10750f0010700440306000950520b2405c0f024409840e2801011030540703078940d10340d0f4038000070450044880340f80b401d64404d44030f00b46200e0080660170a407a941d0070015401030454124900a80d0198800310700000d0050140603074084040a54440c00c4014903c0b6080000030840101712402154507035a41000696910701c00b0b0380720300e2160f450142c0340c1c00c1c1281e0483c50320b81e011041c580649400051404641d0300003030302003072150081c64003103000d964600c2c041c4e0550049034002084c96090005000401111034039242507096114000a10b06000e0480e1030300380c880304259035113040071030300c4003175440c0c14201040203c52807102e4010401e1407101e420800c02140750740c02414960009414031045400405102d82c0141c013811180d81541070120b201c9c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 95095279 1250 95094029 95094049
    0x90602031303080c0c030f150108070e370903032003010e13170903010b0117240a06020a02040b011115070311070b060307080105070e120a02090c1201090506 69
    0x76040d400f0100303542010203410091000d4070000501a101d442004540035036982201240b0001e0901c1d65000114030013600240c2d07401140c8042204612a4440d070540b514a50450061202c1e508000ca11001d402501441c2c030083c20302d503c000005166105040040c110790703454400030344d00c40c0341841e4405c00c860402c056a0540d051070311800f1803034540140502c041041c00324010504040c0d5006600d58800c1c050107840d209605030001d1002803040c0c40119000001c000340c050103064400e000c00c030010300c0c0b410480c2041090390f000d5001080b4200000b960943c4540c1b1840050b80256409400c5040601030400c0b441800e0074580741c3d030f01c1d4460f0a90303184d0910b5500c1c010038200c80000680d80340c0c8070790800000d1070022001d80307507240a90f05004450349803c5407440e0003446001800120741005219076841550a0303a00e10850320413500c108200c50910300c58001d140e2280100c500301603910710b95064081e51700240c81d1a960206080c03840c0e0030f500141e121000440c50705013005513580b43c0d01126 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 95096529 1250 95095279 95095283
    0x391b0e01080d0302090d05060106180e190b0301060513090618020a030b0406090b1006030c08070f11030702060408010605030d020109080d050c1306030203070e0604050d030507080c060c0703090602031303 89
    0xb6850f94440310201b01801a0007402501600c41c84000061070303a00803004682200008980714440d039101c24405026107000c0c2e400b0460301ca4950101d0b1041041d5038443c0840e400c0017000492415620300024a0080d000d603800114207555030700342e5040101d144244102c1112036110424012455000600e40c4801e81c40098680010f81000400b00101684205000c66000c1a14155400c0c10104001036014501030200400d02d082c6441c00610300030074210f889070b9000c4d03982c6108141910421903101c0d911824045040c8018898000182c1d2208040e0010301420400080e40614000402d45031185920707217181964075100b0007801041e50481200c0011018480104040c0c03200e10510440d845040a4400a0350408402185031a41030f001980249941c0d503c0c0e104a40300001040414895407080c540c0c0b1001c01580000041d01607400ba00301c3d2401545010705044090740003908003c01180c0d41c5041d1800040c3e141c0405802c030003000d0142141744000d40c200b146170420300340c00807054000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 95097779 1250 95096529 95096531
    0x160303050a02100903020304090c0e09010b09370f0e010e13060e010506030705010509030c0f010302121f0605310504090317010e0403391b0e01080d03 66
    0x800c02041d0007086146000c0283c2e0381c007001000d02c2400c2c0203440740c001c0e0140d40d10756814803007200d01c0d140c070a800480c800b0100801030f2140ba484e00c03507000c81d65402901456003080c2800c07480c0a03c407017111001c1c1030000d0340c2c1012180c2e00300036584510b054a0b894020b0403242c091410280309200c40340310f000c0c0c151011903004000648481000401e4003205010003440c01c0d080801917010001d064000600805094003114881900c1d5401503615000760503115404d94042d174410700f80340ca800000d20b80c0507041030400600d4100001d080d1880801d080341c6001492280c12800782d03035044a11100c0e0000d00d440d20b8800d081083c035081450fa1070458400c40c1d140c906416004072030150400791361400903c00100100b00c0c049040c81e015000ca5843c40c032489a1401000c00002c07003124040c1031610403503240c1d58107105108480c555907180000003441c400320f003106c020300b500180f0b803078010308100c6801140d034400d130002000414280c074145900640e2800c0303650001080184000078801c4102285818 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 95099029 1250 95097779 95097787
    0x2030403032c060c030a030b0a060c02010804080f0309030703110604200f0a0807051c030509060a05070b150306070c03080622111308121b0115060f1116030305 70
    0x20244200714548002c141e8002c200241100c080000040100f0780101c0e25142403000103040c0041181c104c0980c45120003140d01d02c080e64006611031950a64002d114002590400040302801c5a154004481c920743c1903100040b000b05254101c1c400c42c585070f81e42d4000303282131300d05950340780c03800c071103501000328601c50003606108565504110301c20305d45405803158021550300c200310365a60401d48100d6001c1c0d410b680300c4040c002201e00f14156800c0d01929102d00d40702d964014408150701c44442d400400100b070008400180b640700030107000703028003c0c02094051007901010304142c0c001e44400140100030a402d000281c0002080d540024121202e00700c01c0389018411815244e520f540c400110301e4002c01700c0c14845904094940d80e08440e14900900340c88140f040d54410405902c462040002c1c400c4048041503034604032440f0311840000700312414043c0440c0f40f8031200d5040032001c90715180c0031540c0c05034050b011120f07203c07031040104500c00c580f0f004400300c499580000340802030002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 95100279 1250 95099029 95099087
    0x15011803080f0f09090c09040c1b0305130801060b040f120210030e0f0105041a061206010b0d0b120a021504060c1103010603021008010e180d03090203010e100e0106060203040303 78
    0x40541d540c8650152001d1500d01c1c000403118096801414082d201f2803520109d03110207071041c40c40c0e076500c0c00289a03030305aa400507201521150040c68035100c51348190b810115100e5020b0042c000148850307003d207a201c0d070400034803c080f00d88580141c40c401e100c0c004910701603594108030340b0b014120340c1000100c0c0f204c1c1c0c071280303800c0c0fa0402089500b19802c000c284803c114003a10b03081011200c682c0c21614585680d020001e0464062501e003043c0da1040006200a08803c0d0052491140d038450004910010344040340705246a1500843c10f900401d003030340b040d0f00703080d000c090300001c60681d961300d0309042c000c02503c64100d22801400440c070560003884035032802d42c814400707550000e00400c4c2d0000010402003960009006061064100300040360b01c204043c801a2190301c103170005002600c0484800328002d00070894160780c0b541d22916540c040000910500c8600d00721a240171441c01e402017140c7c1c0c00d4404943c0040119401000b0030404240d004623241040a0a1080c0c1d015140083c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 95101529 1250 95100279 95100307
    0x2100c052803061d04150b0907030b0a03021302120117030f030606040305010510060f0c1a0426130503060108120f0c060f04120207080304060507050f0615011803080f 73
    0x5500f140c03041c00d40346500d00700907402c0c1c500f000c1e00c01d6200d00e011400034000001d000047d580003100454201c022030020441e0349002c4d4000000074180584555111540c0f0780019011080c0d61600400d010b900017000c042101101788030074003400048502c00e1480e07080d041c00f15a60b00c40c0c004115209070002c40820710a5a4440840d0021500f14000348040c3c1449903502c84185454411000072407d1061401c840324042c118001d1000c3d00010348110142d60144030141070036006200312a00300d10381500c0c500300c15040500141c0a040496419142c1c0603c1401c1600d11000741c00c0144240c9c0b1180040141200000340c00540c2c001d0002815140d41c49040d41103060300400c0c056070058000c410402268015152429100e540904d0070480203107649403050342c40c0c400601580c1c96030b03001000140190b034040c40c02400014400c10444200d1520030010038140001690302c40000248402540c0c01580d1224203140700040042181da0f4252559940700910700c254900c1c042240004610070050800b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 95102779 1250 95101529 95101541
    0xe03030307030f090c06030506090f040804030b190507030c090806040506060111030d0e0303071202070f0b0606090a03050a021203042306040909110415050d0212071502100c052803 79
    0x48090400176950320b0b42d101501030032040398540e0292800c0000160314488420070f442c001c0b41c00a01e1a440d140c19915583c200d130070001c0070240810005210210b0a58013881070303078480c2010396400103e2280004000740000c040d0340c0403500d81da000c042880301003100824442c0c2c02c1075007400d20003441d10015840074290b0182400b0031442926001170f4030f094a0780400214400d20407a0744115006014000190403400b07130b52005031004002d000d10000090030301c00c0043e0004001000705041c001c80c1350000b0202e070703916001125150001c2035640704600780a03450b40012401e1030041c508050900e128100506d65401c01c00c9202c035041c08095580c0c0d15101c00b21809080c03403a400780110500c40c20700c143e42030305080c1e50b40d00840c0384c00540142c40e0000030318001541c00080c401d812105564081103942095410300394003a01525400240040031000d9000c211711158000c2c0c01e03030b0841140c80d50102e6104403100800d0100c00c20a00b50300001c8140001d96401003000c0c2d049602075804401c8000f465 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 95104029 1250 95102779 95102783
    0x503030a0906080714030f0402130905010f0506030a05120a050d0e01090c0603020a0c02011103120f0702150609240301020d0212150109150509030d0804030f0e03030307030f09 77
    0x404040311580403200005899071a00e0f10702040d100d1201c00c94010340300e00c4006500441c2480452500c0542d40040d9410034002410701c20400d0700b450480342250ba05840444042c0c0d50ba07180b2020850003801090760007a0114064803010240e03407129a29506054508201440001100048070b40100141d440804013100200700005e2a4640a40240b01c1d840d400d0720b000030504400904203129008172052111665210008950140d0041d03a034901e400d014649039020500c01129802ca80c1c40e0070344d210340600b011400050074607540107801c0102d51301c2ca600c03200e40003c00b040059100c1840c0b103500041d980c03448000c0700d03404204d01e80003a04d0101c170309541940005000c00c0d8803003894016000b01a6414030015154072100000c90070101d1500f001401702d19541410081c080b440b201c1084d051900c0c1c10090714003055440040d08243d95844540003041120b02400141036100e101c8000e9820780b03080039080c607412040080c2d680d0000402803401c142e15802d241c2c94400710340d000703180525 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 95105279 1250 95104029 95104033
    0x510020706050405060a11090103021c05090303040c0f030302030906030a02070f1b06030b03070501030b0307090203041b08030306090c0a0212120a0509030304211704050a110114090d03090503 84
    0x10381500d8040090102a14140c4040c0700708401305a02c80302c0340c850b40038020200740d2100d241050140054010b90814440c0c0800e10030000017003085001c0d103004c4d091080306c582d4041d59883c50316140680080d18160031100700210554003c0c80026000812a4074651040300c02903266a60308810a000e403003400c00003030aa0f100e115100d0100003080c1482c0c00ea104000302d08034903c948904049040310701d082500780d41503101c2caa00b008554001c1d88061a14a07003d0103807500b07151160080010ba9006071030403140d103c0c69160b042c9800020b01444001745c45031001940c55410704000007035114002800b5030170411340004103408075500030407ca03500002d00e0402d01d07458000440c22500c801c542100e80101850810f00004c070304c4040070007101d10460303104454900841c504803200e2800134070083c0c00d0341441a140306070740001050050084c031440c4180d0041c891106d03146002e04450201500e0507062110605101040c8520030003030b1940340d031003600d12207844641030a0460391469580d1006801d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 95106529 1250 95105279 95105287
    0x602130b0a0e131802060708070c0b03160503070c0201080a020405120a0c0503071d1b0301150e10090b13050d0c030507060203070309030303021303120207032307060c051002 76
    0x4581c01c00840850b1441c110b44102c8070380241d403c2c42c0300752075040120b0f903041d80e0200c124400614020010f064010300540c0e000d4244129607030f44055502d6141c01c030041c24400401003149107161810101c81008141c9031850950410b1180502403500090009040c0084a80020b41000041c0d050b28001c2a0040c00f4068605d4052101c640f0303522040c1c4181c07101040000701042c5401d000030004202c0b078a10300040d050350810000d62402800142c241d0304602c5072040300101418400340514040c206c10910078200842c8071b071001d016403428a400c0d6011300c444142e4608a00c0d00441079074201c0d0700c0e6a40007566a0390340e41c00b48054122a400c56544039451280e4003051003c08909002902e01c108125202c40c0e0f08c40005036513901401d0360040010b401001e041c00028403a4000e400529144241608440c1c2c81ea81c48482d25000f000e0004010380c41044100180140a03074204006a14203075002d090500300a202919040d0f20f01594060210b1085070008209042140310b9600d0383d0803e0443d00d03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 95107779 1250 95106529 95106547
    0x130510110712020103061d0f040303060509010b031815150f091302090a020708072307170106060504080703060506130212010504050109020910080705040807150810120602130b 77
    0x10404000400e83c006450070b403020980d48102c04d80c2101c024500d81140c0713a40c5d688c20385000700306580200300324105912210300143c1034440c8036026010305000043c003a02c92400315841c0140c40070961a0601350341c044c001c064052070403071158582010440088000c0c04d0006400b0844420800403d02e80011071581000000c280c1010301500c0d07288200d4172032400f82c0726691000180d028403800645040401c12000c0001076548800f11100e074121300a01d40c900340e035188054240f44080e4402c44946000c4203020640c81c0080c4104000341540d8100700707048ca07051242c0b155803182503000c000c04c50340e500c5001ca28180d9803003c102086500e240e400359078403031116654050f41c103000c1c07090703502841c01e08002080c1c02c4100d00035246200b1340500f03004c000c807035400360407140c0403009080f800c00c1c450204000700c4c2c44081800382c40c01234a001d400b061420b090502c001032100000902c11121003680801c00c0c40b0740c50801d912040748a8011902586a07080124031444104181e0b00c040c022400010350220 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 95109029 1250 95107779 95107799
    0x1091a0a09030f0e12060f01060e010f05040513061211041b02070e1f0605040509070e09040b10120c0305070506090102030a0f0302090406060210050c0f0a052101060c0b010602031305101107 83
    0x2306940d40c9a4030444c61520840054071514170100380d500c0032400601060043c1d0406500003e4004403d6038082002e0780d5600945e88141c56402041d03030011150102c0141605182c081e400d01c0d0400c400e04080342407035040b0300035220302d0b05024680a04168002140031500400ca0100180300441d002010159551b503025103540e0062240c0d50145101100003201540580c1c100500c00002034020081983c407661034200c0040010641c02c1560f0802c100030407000d20784070030480b000740b01e00c13941c001d1203007141480d6250214560110f4840c580412010001c1d076808402d07110701403a0703400c00354030303044175840141c0280c0143c801032070304580b5007100041c070300740d0000c1c80c055120310b0034904000c10b0301c4c1d40d00003991074454400700c8803908004210034442c1c0d40c070640081044002031068003c20110031040190102001ea0203400003032503c00f000d00c20300907115149401044540000d600c1c0c6585100d041402c8050342c03280a03c9003805a40d01c0e0441401000c0c000841d802203001d403070f140c54940000d22 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 95110279 1250 95109029 95109031
    0x3010b210607020d090b0901020a051b130209030c01121107060c08100807050d0203010f02040e01030c0b0a0804020409080705060a060f0b04050904120c0501091a0a09030f0e12060f 79
    0x110041c410000031a500340e0003c240d110b200c03191541c2d003000350340c10201c48030342c0d80c3d11411100303045202d1031109401144062140e1041c0c3c506100c490421038181c0000c100450b0000181044103a20401540100da40c0004038504050000c0c01c0c09075044400d98048001012044031210160000107100f038200112588121b01d1586107494045403070b2601950780e07003aa51540500b40b5542c2c0039800c2031043e49003140c03085c0006440140041402140c0c220a002a42c0003030f40241c2d003175005c1d82c0050080082c08a0b5540143c0181c041590400c99080e9004080b1400a030000c1e02580d6600260003d05c6281c03802c0ba59240e421408a409a007010320884c401040d890ac00c01c061903070031580200e5141c40345006c0341c0440b40300030140307141501c40f0f842e4048880b001503002024814a485c000001403007c1c011455464068002400c0003071182000e98080600100190207041c40c080720140081d801c440427610340c02c0e0764903160003111405004244155842c20280c40310f07100368020001e4130a581d042d51 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 95111529 1250 95110279 95110339
    0x30c03090905040b0628090c110303040c210b040507060806010c02090f0c16060204060e0103050405100c0212040f140406030812070903140303040308100b0909040203010b 75
    0x40d00c51507034824068003141c07800d40780103103901520340100f05107141081d0000d00703c05220705003c003101c07042c0540240001885e4040007203e6241c1040102c0704c3d40154100d408168040007861075846c0680d1400d4a0500c0c502600b461040041601c82e582c50050340d81034206a400300c00c1d5085400e050504039524a41c601c21079001481010019015501c1415035008490b80641102c88649803a011051a4007000b0005503411000340542c6140015030400240c003503000d4100103030760314107000000b03040d8401038280b28145800c200034480083c0000a100104000750000064241120030b0128286851001056842e520216001c14000304280f0540100c804181c41c00e190740340c07400c0078030080d619203110152610070203224071141085030306039080d4401594644484101d03201d42e1000d0045540402c00e03005548080708000405030815000d039000001d640d0020600380c83c00c000e16045108000d0381c80c0c0140040c81c081011500c01350080040f5076030081010301d94022401072050300304c2da0160303c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 95112779 1250 95111529 95111537
    0xd0603030e040c09060e0913050d0c030e0307180207170c03090108090109050601260304030b010e0618070e010c0206161a040f0212030c06280213210501050103030c03 73
    0x100c000d401140c280b81119440c6c3c8504080105100801a00e945c1c000d101d2299008450041c83c0020b40602c0309003070300c01140d265800a80302ca030400521840707030196458000e034801d58090001c41e02810300000704220000e400359031000140b810584c0340480075400349000f000030803034a02e4090080081e00d001c203020390310a589a51100c0ca0300e400e079a1040d0f00a001500080010f000c001701041040c404202d00c4194a01c0b41461401d100307180d98020362041c0e641c001400c0050007420345014100c0c0c1c20480489090000c482d035001c07080c07030100003d4032030030500458440000803a401480490700c5990010714864890401c040000d05c060190790045034086441c105d14581c1d205860011401141c010341201c8842500e40d00341b01e0b00ca60000f0300c00e14144400c2c418013214120402c1418466141c0b48211003150440e203231104002000e084040c44654014004910354050300d8810008a0f914110482c0005184000c0309080107083e00c00940554246000031041c16088103c004519100350780b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 95114029 1250 95112779 95112791
    0x3140405071509031502030c0403050f0d1d0109230a081518060103080306060919060927020702010e130203011d01050f040b01020f010c0806030f01050f0a0c0201020d0603030e04 78
    0x1d003c03281c550040c08010008510011900c0707001c465640515408100503090615064680c0c880c18900030054403003c2042c2d05c100f654654890f404002d90000300768200102a8407020346002802f05104c5000c1c020503002c40084141c041c000c0c103690b07510081c2010702148445e50311020125240c808803014a4014203010f80070501c800c002e82d52040450f0780c6035001d840280d0941d036940006074005800c19501000c24441041c5c0c5a80340d0842c0d481a040c2003100d03107400ca1a000002d884680254001d00842000400d085220301080c070640e80504509000140e540510b840142c0c1c00c2001c8266298020036603492031000d2069581c02503060301c0d0908100201d1000030034642c2c03881e03802401402c0d0000d881c21681c09042c149604029040001401650100001505c120f07003101ca0b01c800d10740008169209026840c10103004040d82d4101c510024002032030907022940304150090280250386959012860301c0610030750548441842c401c1d030611070580d880c1001440710061255a51195180c44 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 95115279 1250 95114029 95114069
    0x1809060f140a0e06040603140f0d020105100e04020d06020a08100f030c1206060b0a020309010806060408120c030c030f07140f0d0c0204021903140f070219030314040507 74
    0x4030007001220004088501890401040700d00024003d0302c0940c00c56207170103010001804100001c002c26500000418649440034800ba01d8182c2c190009020359141c0410301c20020218079840043c1c2d024507050440a032030701d00c081481c014020304050301c00b034400b083c4484010b5000a00a0084601c24040b2040d03c4d218160517808400f248030040c0600411001040850318502c0740420090052800043c429920380300c401c501d6000800c2c0070016000041c1004043d82c00c4544542c103c1b5003941c030142402d0509060f107990390400d01c0ca05000d0440480e2000b01c000c4200304950074030511105883d280c030380641680d0507980010601715103c20b0540c400404a51002034070842e070140240c010000d44540d80d005846810600d641aa000703a000c000004000d0391038410b010811440d5540061000c500d1200b903078504d6000340101360740e08074650a106225900044d100702210b40c40c480354154442601d400d030000d1603155803101c4405544003c007c03d01c000400ca40046440e50b0203070412030705601c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 95116529 1250 95115279 95115299
    0x90a0c020f1f0b030c1e0102120c07030609052b0f02011a04050a090204060e04140f070612020c19020907030e12070206040503101a060304150c1809060f 67
    0x2040003110ba4401038880c5402e156641d0003031501c202c0050240c66880f008800411050381c51010002c0801c4070003503020343c465a04002d010458507450308010304003401080003a460304840e00c4007400050302c4a0f2120b080c03007030502c890f01c4001c403401038071000416011300c549040d1104a1158010031030288040801034018020303c508805c0130062400c11100d482c04000090401401e0b0408a035606d07401e08005844a12903640a003410042840c4585001c3c50245001d80d12085a4600e0b5008016000c843c101c1c0000c0c6001642d0316410b15070700341592210340360000c0c0104640b0128030310808203501d200c80c20460390144841d000b40d41303418107943c42d5070064007516420100829941c1c8912441054a42d030074014041c820300c000c0150f460310b07030ba90002034a000c0d160103003612025a030f061044030b929841d0006840804040e01c4032030a40c5000d4440c41400c0071340006c0d0340c0c00c1a490300c0100ea4664411f085960017400c0e00e40201c1912a181e02030000100f17018003842c030144012a138042a0300d019 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 95117779 1250 95116529 95116543
    0x21209030606010305040c17030c010b010509090109020f0d050403050c0c0303091509030109141605100e0d0f0b0c0702040b030106030521090a0306020a0f0801050a050f01050702090a0c020f 83
    0x2000d40140841c1d00c0b04401103009200080c0180c588082c520400719028035a40461554407039010025501c2d01440303034580e4210360380482007505210040007031401d96100c031422503045800c1e000e001610303150801d020940700d228920303120009a14002c00c00c400c05400202800c4003607104800c40d41045161001d241c2d0300c2c03043d944071079070002d0420702e240003803400300700203205816014001040035182070341d45100701c0904800071101c0d900022a6007000d000f05c5034481004141c11548110649003040e8068010380a901c045030041d080d8001030342c280100c606500040560002d8281040d140c054a8100203030001141244100d04011000c841890140640400c1e04d81040151012035500004048100522140b0700000403041c04100c0382942e034140baa0380214002c9801607900c1582d0300d40103014124200d045828800d02100500c03040d00ca60101c0015140142c80c17201481030b004005803103234010988025403100403442003102c0c0c1915904a40e510010076021214082c040b0b440036612148c07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 95119029 1250 95117779 95117797
    0xe010f05010e060409050a02060d06060f02060c090607050c030a080a39020a0e070801030213140a021309060b070c060503010e13110613030b07030e0a080c0c06040e070212 75
    0x90b102c004550b2618140e80302511462060085400d20030141d03000c24065008850154000351782c40744200030158001c9648012500644080c00ca28940091a1200b600031a00e01c280614400302d111000c110007003005040c1c2c0c030300c02021600745108034a4180c50f25800841c043c40001d00688420b045e2640c2c44004d0100c40c03540340c2c05c2e90301000da4065034000c0c00d1400320040e40c0c4440c070404000760460700105124092201551040030315811401880381c040c0080312070120151504000b000448442803229070080780301c410242c0d44a107410240800c00c100c940001d01490701c5c201c030000b25010708030014203c3c2da1207819514902d56941d0419a442c1c0424403a0854503a400d100080b4410714146184903c82d11542151a80c1040c0f4000b00710740360040c100d01c510050414a050060220705808554002030714603040c0031f0011140c3c409c45e1a00040c0e1002454a43c010550080402081c01103080c54400076001d162155a20314030011120802c0d100d80016000302240c101034403d016045814110b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 95120279 1250 95119029 95119049
    0x30b030304080a021302130f061d220e01140402040f05010b0a0509060d090501020a02010f150506030c1204210c0201140c0f1002090901140102151b0a030e010f0501 72
    0x103c1640038051003000d48200401502c0e400c02c44070788110402c0440c4d40c0503200d42140320790340e036007000c80161041f00780c520440d5018500301c403196595503c040c2c01814031100c5411000605a0040d03081c0b000d0484145280c1840d4202211040069401c04c0c1d8644203d00894040c410703040070407010800c03608280110580500e042100c099018094001040c4602000d0000340c81c11012484490480300030700b8045405035000942611116424010705195000700041001610820001607a0184a5102d00b500580003c07000810812102041e203080c2010700b09044000c1c580b614041c0da5020f0178180700c1d10b910004003000303440f06204000c908085941a15900038400301c40c00000b40e2500a840d450050744203100a01200510a00c007000301b021408401503110300028041001d0480140c101034110090201030780601d0ba40040c01c000198010343d441401c0c3d40320942058040c800c3d2024030301800c000098404407566042d846200444403d5008105210306083c0f183c00341c03034007031240500031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 95121529 1250 95120279 95120293
    0x1009230613050f1006180e0304090c030b04050405030309150c0d0b1c140c0301020f0315010c05030a08310b060102010204030b100503070e04080a0305070e0310050601030b03030408 79
    0x9030070100e50081d160700030000c5a408103992403900d45028400074141d03010603280d0004204403400084800109006070340305000c2480c0340d8102940d2405203105100075903442d04103000440e802584003460806001d0030900141c600344c1030030f60b920741c8169040d8009224035528019183c1d050503001d80512081c00301d00345007060400c40c0101512003900060781c0b01503a010078800c18200441c0d2441c0d410f20441c40d8418103040c0031071040c01c044100c00807034002e0340100039400e000f0000300c04403580080700003040c40402c045000100c82c9655040c80c01080303840000b41c1c403455544c2024000e4030902d0403040120303e00d00c102402c5195000540f101c10080c221501d1100d000851094640350f0040040c400142000da5a85604038140400e4442803841c11180005224a05003801040081e09128245001a06066560340c420780700b140501c004041d6203001082d080e91056901d0304806500602320f50a40084517002e40c020041581c1d1180824545a40600b09003408000d0b0b6040f20010300191960b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 95122779 1250 95121529 95121541
    0x8070804290f04020411070c0b070507050a1d07030606080f04060b060f071a0709030b0402010905150c07060801050a180207020a1805071403040816020310092306 71
    0x918084194080e81030450100d46400e9895090207102e114080b844900e2800c250050008485005a001c84292410001c120100302d60880a1040f250b000030403d995501034181075041c4055074001c0707640907009090000d450503920000d080100102d4020842c103448079030042d000c0714054031456000c02c4039240000e03100d84000200613842805240b0214803003440c6000180d91382c0c04002c40894080003c5100c40602c240b04007506800c82c0e408c1e25050840c10100c0010701080300c1840014070802c41c000006003164815806040180006030144850010209a000580d0080e00c0b00c15541d10555900180c005d02c50110b40d0704844000c3d0107034542a0801150307030040243c00c01c0c00f8440a400b0803030100145c45440c000710040c20300c42c002c2041c01100340440801c0e150041d041d28104803d044d00000c1d1f1880f110304480c0c00940c4015042c0d500c220701000b120408086a102230342c94020f08510a01d42e2880d60450300842e44500c00030035080c400715030500441c0b01c0101035143c00e90302660005203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 95124029 1250 95122779 95122793
    0x40207120c020a08060709030c0f0608160201110324100f0c0609020d0503190311090913020409050607020c040e3003010f0501030c02030a0819090609111008070804 72
    0x1000900140c01140a60b4a500c260b529044041d581640011f00e184420414441d03d03508600190045140020100349400401801100080c040f410100e084000f007684850007517001090ba6100d1140e065120301c1c0c009601c544031401d560800c00c2100060b044c100ba0f41ca48108142d8400415807203042c080c1d00c3c00b2400b192070303214818007240c0351962100d076040075030742d1070982d603c0c80c5203d04010f59035242d0016591029400030780446050600308020780c010000b000e030030f55032106000e650000841d0360310b003d84104c0b66a9080041e4010b0311300f2030154244800422441e02c900e1594007105d503400c0c12a01403000f1030302d0072860302c0416001a280449a195044403c5001036001115030210310503000d02000c0a034002c0e481003141c0076040c903080009503018040c6800d00f4205001460401000280240076100002c201082101c004604010202d6696001124040d080b0728100302c2c8076440d1030044024000241071610690280a0f5104030600c5403903c0d80c03159840795140c454548070395071158 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 95125279 1250 95124029 95124047
    0x9050102010b0d081c020309010b0414010602030403060f062402010e0a0c090b01020c030f03040e07091203030f0e07121b29160f02090c030912090609060708040f0504020712 76
    0x3402c140d502c20800405e044d410f00195009100301c90002540c6000d0310200001c4070045032410101e0041c2000400503560080265000c882e0004808161a440c00700074100524080d003000b0f85142510805070114258100d080ea02d4a010b80c00801c0b42e496521071440c2d456841403c02400a1030f413060600a00c071041e000b036000e01e2418011100851000000281040d20350144074a0303590010130b080040480520403550000450700340b07100740130f0816a201c4001000b0420103000e240d04c8074100f008402c5542d1001c2d22120284041e80d4041c0c0e00c401c0410342111100301d0640d0a400040c65030511070a40c2d4403031700200c3e1140c800c101074070800450410070b0f64120066100c2840814400002031014022606244038800c4940000304440b510401070001000f81034000ca0300707424010003000400000e107003503a40040d08481a190108100082c5062040390415500030700c000c00d500003000b134400e010300180c40a1581c92402c0d0740e20f5000b40800c038011408046c0080818102d4604200d0041c6110b0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 95126529 1250 95125279 95125297
    0xc0e060d02090d0b070c0506070f0f08060109031e0b060a0f060c03050909270a02210c030f0c0907020d05071502120106022409060c03130606060c020109050102010b0d08 74
    0x2041c480403a4903540300400017218642d0108020034030f01010003005100c15070f44450a03040030303001d091341c51000401350307060f54200d0018082a403000c961540e00410a00000350750008894802d5400c8102d50500d4030160034088070f03e02d0740840807540c2480c00d02e1483c0c040d03580e884070b59000741e45000011900c040c0b50303030429001c0c0941041034410a0300d404e130b509442489030450306a070456100701c1030418102017840d907a22a400c2081034000595a140d0114500c038642d400c0e1251401310300c0926800c00718280c4406034940308040714048901c4010600800300c100c22259080c0c82c1d03881030380507600c4050013080c01001803000c100d007000113121018520803d494140c4018140b9900740103c0380107034005e07004900035078030510b00e100221000b6080c000ba5040200c48060940c20a0a80356541e814050310418031640c020001401200d40c100000c290290450414480641d5a080240c0a820361410a900040401c10042a00d50050085003500600580208103201c01902c0300f8140e40c208000b5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 95127779 1250 95126529 95126539
    0x1b080c1003140604200f040e0106020c0f040b12010e100b0102070f0b030711010c090e010b09060f0306060c070f0501020705090708070809030c0d021015050901060c08040e13060c0e060d0209 83
    0x4200e0244017010060700b084441c4222082c1c0d594144209020b80b83c105a000030300715802030308501e180340c680d001006154101502c000c50480241130001c4c80c4900141810307042507203003c00c50360307a501e80004c4221842050b01c1c0100107a01804004985600250086034a2004440b4003002903c404500940c0e011029140c043d4151030b0341c00c01c46080d21407806813500040d1140340d05014034503010310041d00405c41c2142c034a20700402400459120f0143c41d100030410b180100014400341c4681c0c044804018102042d55841501c6820f07804c030441e02401070900512a09a000c40d6505000c070515005540b41e03110000e141c0e403602da0440e0f10b040000e09210080c002070041c507a0390303101005082c2c80511240c02800034000c44010311421100982000545143d00402c2000300d078442100c0e090648549151002020609082048603885a54000414601c1040420401403002c0d9038240160744500c10500950b071140b41c04032000c030300c400e09803035120408020b00b0542c1405c1e5402003241c0700300589 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 95129029 1250 95127779 95127821
    0x10b12090111121506090d02040209040209220c0216050d020a090c0f081302090f22060207060b09011410140a020c0a0e09070e041b080c1003140604 65
    0x4640242e046032003111a003840c0e420911001c50f13910200c3d1014154240c036410b08180e40b140005405c500300c1c01000e03018680c0000c80089540303454040302c401c1207010f42400d94074003001081f54010031100700b40d015083d07d041e02c0350000c0b510104580d003011403a0500c0103440360a050800940305900c3d18101d034000411900000c08060740d000c1c0d0001126262a15022070407841c40140071010004c00c041506100140040010f0307840c200c7c40394000602c3d00324205541c0d61041e141d000004000209880c03240107265541c20404541c00070028a4400c240c14010b0381302c0007003480041c040038002e07114030202c03101141c0b007281050f0940410744011480c1000004040d1412010f569000001401c0180c2081d4039065060419004104c020580c0c5001070342140340090009460b01e40354040c0d0300e80712440c0d601260a106154032413a05800030030741c0a80044da034804420307643d5685000100c4c010481c0032040c80142380644179284448000c00b25031040703607580e0fa0070080142000005501c0c030a940031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 95130279 1250 95129029 95129051
    0x210030b01140f0d0c020102030604180503040311060705070b0310170a111503040f02090c0f19030915050a110702092205060c0703021c021c1101020f03060a0905010b120901 76
    0x1c02603046480c5c1c5600016600d050105c01d01c4160762002d0545460040ca80c03180ca000140000220b40440ea0001c02924600ea01140004c0035485003110260aa00c40d04c0340202c0d13510314000c021400303100064646903200d640c406244189501124220126401040e60381010600c070f102038019152008004140ca04840111075401e50002e503025a0980845282003045003048001160003c1442406e0b50034001d0045450501d44034210a003206004443c01c2d07906000e000760001304903154403902441108113240701500081c2021612900c0b2a030621040c85c0311490340700300b1141c1054014141c041c96540320400d8150008082d20400000d100c003c12002c0030070801d018241c0030750f0b18429010740d10400d80c10f009240c11102649070150380b1850f813401410940000e49002000e40c1c44250300028064054141c50b0000043c0701c002c0c55500005441030074804102c01144510710442d80440e001d0b0708c6c0c0c180001201c40c2401640d189020412807078102a812260043e0f00000303100c00440ca0710310035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 95131529 1250 95130279 95130281
    0x5060f10030b0a05180f0105010509061603090b070305030702100e19020a080d0c06450506090c12070f062d03020a03050703091713050907020a0210030b01140f0d 71
    0x1c01c05e840c4050040b0824020503034042644a070040500f4a0000e0401e03c20400080c05c0b446080d02100e2003154400c4090209401515040c0c003c1550660490300e550366814007401e1584202c0b451030041c05078183d480300100301440340b00381c211100d00003014180e4808441c007a0707a01034440160b034807541191000403240e10401002440003e00e540e5140a1041840c01800f51616556283c91440090814a1801381310ba070014001104102a00d082108243c020010f103211410014055000e201704010035500001004000c148055450004802e60403203000e4a90700240201a102c01c0c0d480f01c1044000d116a10001da90040001da0007804d44107854040c5040c0310224048010a8011515600d855010710400d0340c4040c16060a01c049410356491105418141043c078010800206004c02c600355204003480c094000a8011160340c00d00c4403010f981c4007440703038080b4403550300050b405900302d00c640208070080030103071104000d203001c02c190348040c2e40048074182400841030140c0310520910b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 95132779 1250 95131529 95131549
    0x1090c1101150f0e060306060d060f06170f010905060c0901020304090218040b03031204060c03020d060f08120a0203070204091104020a0e03070911030a090201110f0d0305060f10030b0a05 82
    0x480060740d00802e1510705803003020046580b06444c138070190020403240b528081440f40e800316084884080b010144c0c50090300a2a00e400d019403080d103011004910180d6400100ca01c18011200700d0701c10185042200382030701c041050040c03445d00000003058144550002600440d2014019079042545801c0300300c0c226008010079241004081d40b2082c141e080c244202e50f80900150301940c03603c0b0544000c22000c100141005101036910050a1172581c030a038141c070030900c0c03000c4040c0400c55035202070070143d600078003031260306004008031141b9400010040f200500e002da0061400c0052540801c0b00038104801c007a01d035100748900031135543c0e036248000c100f80c011030f403038000b00703807564100f89413a1603401d42100d10501e251010500400c3d0103401079a03404000b0b250089101d5070103100484885a030012501d050f4400d136180b011b264440412220142c4049560030030060f6941000c1010801000204a80258003004c040c4480f41c8250080020b010015140d81905665203000c200c88400d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 95134029 1250 95132779 95132801
    0x7052802270612030a0e040b060406030504050f16060f180b0c0c0f03070308030a09020409050a11090601050d051005030d050c061006050f0c0f06150306060d0b01090c1101 75
    0x60104100800706103201e52a41e0000010ba401c48120101101401c0d60b03480703145240c10500a650b180707450166190780000c0c45240c0050202900d07143d035a070000e03001c0c00d01a1411074660080c4000c030704c0d002000044c204d089403075108a803c440ca01d0058281c07846103200340e9580070042d503200e0740c0302010004501c0e00c0080030707a26810342e59244402c411904104410001600c2103000c1c5446ca920755600096000c2600d40210340d4540e00d443e141c0d00e140c000c0241d0750f0001d401504003411a0103011020a04103042030140607054400c418000410219003011a181c902054041c40070241c140703004c1d80704660080a0f04500d00c3d110791108000b034034040c00c003403030b54000410010f1391481035001440410b0b0040d0420811860301410070b00301501a00402d215642602000300d8190398141d0100100410101c0000030740380542400d0001d5099511805030f524001e10810011424500b0160741b6004041e4010600c55850390074104c0c410042c211340b500440c00c01c4005000e0014040d400e110b4010110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 95135279 1250 95134029 95134069
    0x4020603190e011b020d030e07090e0109120905091f0909030302070c151d0303090103020f040f090506150306210f03040801090605090d0507020402070f080c0d031107052802 76
    0x1c1380a4000c0c6441e41da22034060415080502107110b00c0c1000034146d054800c102c901045070f20415a1141c0101410301010f020004101e06245405800090040c15282e0991361800b00c1e5444460852410700545030031400e02504030301c00c00c02401079900158103c5d00c2450050f140004a448940000c0243c3e00079100c100f074000350190001d608030101a00c045151020b068480b41003c00080e01c3c1d01600041d54140341d00001c0d0108020301100840b40980741c1c80c0807031a1116190156240100b00440b041741c054511410110103000c01c0e1000d80b03118181c002d1000e00f1400b180101c420074450408014003440c401c0c01d44422410106002a00182501000004018038507040c180300740c0710058000384484d000303901a031015a07400300c204e402181d01604d0150355050240b40040c00c150001401a001813000705d6502ea010b1004203504000074002e40c0c062001800750045c0c60114414004018070301d920000f502c282404641307410728101c0c1000c00c0015406560b5401090725070b56800c61007180d070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 95136529 1250 95135279 95135321
    0x10090203070e190509150105040305030a0c0606230111210310050405060315151c03091509051201020c010e0604030f020307080406081003120c06050105040504020603190e01 76
    0x2030f003000b501880c0c00c5202000280040e51605011036160300000d86041c2c2d0542a03e180d000c01c59014004a40c01103a0284c00c03240c0d6056a940c00801c82031419030110b40050074a13130b0010710a408550f170300e1080950150300025803103104005450b0078002c09003560031802803072060501003019507c80208010030340012540c80c50440c081d82d8010243c0c0d04141d2080340741a00380452514005041030005001c01088034039520369642018280c07010803141035001900544400d01c240030900302d0071070b01d03100352941040b02d40c86030a50f081690340700754458001050030f50208150319006150b1190016924001450968042405425100800c0841607964808024003013010782c00704a1201c1302c8207030300c041e600303140f42d5640e1240544114480c80041101c0c40000c078603071400d107c0040004503071200480700140f80391207020f0800550503200303a54a5150500024150034280100d074400c942c010b084520356919080407803004a080c810040420340d0301e10001c175910000744070701840003100d140e045800d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 95137779 1250 95136529 95136557
    0x10e120123040b010b03130204051806151c0c0306020304060617010c022d060702010e0c010305101e0902070503091c030815030f030d0212070203040e040b1009020307 73
    0x4455070401da00196000c040080001007003d45920f181540c007005285caa41c0c3d15105075010b200005201c02075886443c020a100d10740c10303404500700b040440502035801540d0381c0040301c0140394016030556040011907030314401c004884120140040d10941c45a60025100d40b150740407a0011141203640aa0703d9400303014111122851044d0010404000e11680d00d050740001d48440080000c80c1494811b0403c0700781030f82c4510302071a00140143c085403131501d080c0700000d028002c1a19200450f01526040d000070354400c2c014648030f005201e0900304041d24000302042d40e1443c6944907151942c1800c00410f40a405000502e5010300540045490344010010044913048401080c0ca00070901d04054002035044094603512803a201e42c9210f82c40c41200203c0d0620000450080090000181106d02c007040ca83c050708140c40ca0b9070a034603455440c1001aa6a0b11030340c000e16103a040c40b000020300240600116039804003184981c414031b81c1d0740341d03110410b036042511000b000c1a101c09107200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 95139029 1250 95137779 95137811
    0x3090301060b030c0702012307030e01120b01020303040f080c06040c0303080a0b0d020d240e06090604081c0f0204030b1605040f061419110606060403080405040209010e1201 76
    0x14108101c1c0b038030725608224003c03400c1c070312500c13030000d051101c03103807a1030342401c0190b5415a50141640c0d03200d54408071480c00820852030b88078038038040342c00300c40516510899440350310a2480103070019407440d2581c2d1205101003204400455001038100b0070100601814002d860103240b01e4292b1180103825440d015148a2004116090061600b203c42056582e0072903e41703202034040c1e4403040818480c0c00c007803040c90040140b80300110142418030b00111440d5100325031440f01101901c3c059207940360b00350b4440409a4001d88048001d000e080f504581c039403030360001031103404e4000034001503003202c075416038010350700c1654030b600000308000c0014100070400d04040010700e440351909051207000180450f1602407002000b01c2d40d002ca500d008111400c03900011000400d040b001106042e00a0240008540000644c0522030100d501340c00c05a040e20309a90f400300009080c2810482840000c3d08005102c0d8100700c8500701618413501d50311a0030101c0c42801c0c0c004185080403c400345 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 95140279 1250 95139029 95139041
    0xb01060201060e0609070c05010b03010c110118080f0a0c0210080414120d09080702060f19110d0305090a0b090d110a0b010515070c06030203010608130308011703041703090301 77
    0x3c4107103199000c1090640e80c8011203584541c40e41810104680542001d074010403010122981662070000903e01c060b400c0803403560710401c0800280004600004641034042d02c001c4000d003050703814004034074a01848000703407407402c01d645030040e0811016000200700100c134443c5071012500f0382c0d080c04140401a141d0300445d100413001452880500e402136081480b034124802c620540e100c0030035081020050071a98110340040c07003e51034500d01c03c48214640e02c02002d0142a00c166126040b082c1c1c021240b13260a220403030094000755030303031920030340103400010b000494078014a85030394002400d04454601607040c03800180001c050b80c1f08054103020309642040655800441c10900140d51000c0003815500305131006180318049150100c46806646001040400390803c08140a07501d0360265040300c000d90f544076016100c51a40b030040c4402c080b1301400140f5420011f2003da241d032108c04940c081604212440c060f03031450081c0a40c0b041001042c3c0e550000100b070501440e09001e40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 95141529 1250 95140279 95140289
    0x403030302120631021315090e0f130c03020d12080c120406020f04030c14011d09042d0303050f0106020d08010603050c04030611030a050c0f0403140c0307030b0106020106 75
    0xc02e00c04011403550000a50f41a5905080e034601d00d0f43e4485103402d03016141e5894082403800000b544521f03050111a81e5958070200080020400107020382c41462041c0c050101c03c00e80d44981d0b180e03642c04e850509030905003038450006c1c2c0c407800001616a502d00c100395a0181c00954170241c003071840145aa080600110f18800d001e03c0400300c1b02d0740001c000c9402c541e210b000182c2c0e0b1000c24001320701600580d800600141d2440310005a401c03c002141880d802c426614030109450307405490aa41000c69921a00141038000240020740500313005501d85d80718442482d040300c1c081c41081a05d0400c028200c1c002a212000d2184445910034014003501c071170f001a19030102034410007003000d0070500c61ba200301501e6802145983d01c0d45011103002d141c0040c010700010480d1502c01c2100d9000b500c88078025441c013000103c0ca541800c0036120018001540a40743c5459621800c41c5a51350303881c500858020060386190076a01003007070b01c0042d0b10402c1c0c112a558076200d40603086070129031103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 95142779 1250 95141529 95141539
    0x417120f2208100f14040305040f0608011d06040f020310030308010e0609040f080f040609050f0d0b01050d1704030b09060a0c09030305030a020d15080c0307030f060b031204030303021206 82
    0x1c1880040342c041043c2d582140082c00010f80b0701064680d07032024024200701000c0e01280e2505010605622800030400d443c0496900100c0c15959041200e80d20000d1240d0860b4164402004200704029034100d5006640104040ba80da274100103100101d0b401030754090700d04a40d80d802001007541054010340104000d524a01c107500d4a40042540744800500003482a04000d00c050708001420701503400401d6a000e2007034855844c2c1130090414400783c01100c2c0301e00d41c06c01d440f40d820b02c0c040650741c07aa40d52004c080b41c03580e440c2506102010184002c100c4204241222002c0140000030141005601408448206040c624411820403802406450f03134a420300421000309904541703010200ea50610308aa40c070b076640c000b940c00070b000310030010282c0f604280d10705001d8260030001005880d03020050b281500c075150209030380c804039444014486228442c0300c501041c21544100d003100e0015094440b240355204404d034041e44640c01c202c01107540455943c601080f09121154031a500743c0b1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 95143885 1106 95142779 95142847
    0x10c0b040b0604050c07030903030503090a0f0f062f030703020c010e0618010c1403040602040807060203120a0203060102150a0f061202180601050417120f 68
    0x901c1c911031070424000c41c0c081140c08048500e81c6d5410745441030641d1861b80c0c161802d400042c043c5925004840410b008110002e400da501d144c817031418000c00c00740c6032070060203c2c0c03480c0e2042101c110400c40300c008408580d055104901d41120710142d00d03640d0b40201140a071145103141078040d420715140c29002034002407110b000e21002d1594404044c44046d500e03081325100c49500340013030841c4c0402865440c1a000441e04940101001340c6882c1e00c600120389042c6007a801034006074000184540c07030000481d010354000303001c03c1741035186080010000395540020b41c84451031154400110380c101d89a5445000100b940d603505000496442e2030000d05905061800d034080d1000300300600d814001c030000c00e031103494141c4601d8141403c0071400e04c05202e11800d1030341503100c1c000c0d1020f04440510301501603408010740c61036a0340c03407440226840e1108120940400c0450381 = true := by decide +kernel

theorem cover : BRFrame.Cov 94964029 95143885 := by
  have h0 := BRFrame.cov_init 94964029
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94964029 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 94964029 ≤ n) (h2 : n < 95143885) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
