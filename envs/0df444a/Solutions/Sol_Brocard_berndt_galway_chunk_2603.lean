-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2603
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:11:45.989575+00:00
-- url     : https://prove2.me/submissions/11770f7f-2976-4b4f-9ff6-af93ba277465

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 467985611 ≤ n < 468165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 467986861 1250 467985611 467985631
    0x41208010b0706020310030f0b0703290d020a031407080705011b02040504060e15091501050904171e09010e03011506031503050a030804031b0209060d03021005011d 72
    0x100410140802100300c07078206030091001600c03501e42d0603040c0c00c3d5035442d40c40071345114085031b001400c0c0500420060f01400450300c04201856265a9064cc0700f002d40720100c0c075a407500340174012039007405082e038401c45200074a031948a507201d0342ea1130940d01e9210701c0c0c1542030748001000d224058082141e0400b40009090901a42070010380d401150394078008024016915a0042410054180c011070200c080d9078086e00c01c0000c12280002400c402242d042505218000124001c0600c0c82c914a060f42c6e0050700413182d540d525140d03942408040902005800020002e200d540000364489171046c5d042900c9c043d980d1300c840c074001041d10051500d1103209074500220360790101c44184110382201e0a500f80400c00f0700d0f00410394000d0398003030341c40a0000c1c014a41640100755029031a43d110f50b1098455100d0103c685050040300520780300025000b400306008030f402482c000401c0c0e90441d200c0c0c41214510b403103202c0258107030b40003070380301c49011804410b0005c0d04c95442400540e0010010b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 467988111 1250 467986861 467986877
    0xb030403050c070803130b13080106060e0102070905150618040f1407110309010e040b03100506092a0d0e0706111225020d062405030f0c040e011d03030412 68
    0x620a8401d5200c40d07c40c1c0f00322040c0008642e583c101401c2101402025000008c01c1040d55a00b80a40b039118040324050040c01061008180810280b2855026807032641003c205201d8070020701c66642c0c00400190501c3d160300040c0343c2c075030b699400f82e1645501d4841020541c0104590408058a8060400c0e02480485252040001c0d0000252601418246400c112685402c404200280700381310768103806024100203c0303c0e00d00310340c002d1030041030309a6046441c1c1e501c00b00c2c602403500559101031135a8880c87c10b0740d001103510501410000d00e4502000803285000c800c594901200e9030f00202c0403c1c0c0746949200a400144150402e011107020745502e1302004d0700103156040211204400e5641c1038080e01d80940d19558003031113107280c1c4041c0800054401140410b1107150800c548401e003543c0800208036410045500c207c807503000c1009100010081040102802c040032501209658074030368550501365010103072108a10081c05107541381010306100c07405262202c10790342804100c1d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 467989361 1250 467988111 467988127
    0x9030801090504050604030e0109090203010f05090c070305160c050d0b1602070f0302060d140c220b0a11010e1207290708070e120c1009050112150b030403050c070803 73
    0xc100d01c0c0e1b0165040c45e041c464040c581006a84d410038541288008520100000c0307680342c01c442c0540300340c075411103440da110396030482420018031031660300800041c1c0a110004c80358680074404075005204d0041c0150442e20b82c0081030a08902060507242070b0040304c00c0c03144e420781c054020755080000344050482c41d1f041c03ca4810700c1ca9203a1100a0080c0000039040c012041c0a901603420302494040921050808800b0390070b06030070148900d4407114186581010980d03015480400325000715103401d04001c21000240c41c4a0f181e40c20b240565500d07100704078140001800822240300504440c42d40780d901038106035207010584e000344d0302c000e4005626451801420003c20b0350040b0765103014501980d0721001101d180c2e00c1508001d030081219104c440c003510000c45e6910301110240e48004a100e400c5008454285552240d9030124201c0000c1c0410040d490300581040c400344015034141c283c0d114030441590780110f0f41035000480110b051000084140200380040002d0300055092400d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 467990611 1250 467989361 467989363
    0x62b090f03030516032c1005041407080a030e0d0f06020c1605060901081b0403020405010f030303050a0b011209081606050f1b0a2f030406030e061312050f0d0903080109050405 77
    0x703a1009006c40c03464500d81100c040c002080140100b100c600c8081c030203070415191000d2000034642903255540a8040c000c102d0903070008103400c0b40b130740581d211061000240140403480000e0b07281030396500340170940b04c0045907840c001410015241c030024403a481d607883d030345449101030746c100c03130701c5080104a1000f0a0703902601c26600144841142d4210754034480302203109100b507038002500a03041c000002645041d050380401120700980302846103507103503103401c0e040380c0d00400c8180c00700b20740103404000905264000f81c0c203d0b1013508501e18103182c02003260490603205104490490b10394080101340b031202d0030a59004850a00440b500b01890007000340c0da80101141041000352030f40d50100b0708254900038010788007a0000b40c4036841c9940010700d40703a52040c001c1c0030220b410b0445000390340c5400a040c03407080fa0504010345088070329540b800316000c00080c0070301c10000705000f0768804c0e464540060180c3c80b01c800c8002170382d59403803401034080041680000039192400d0100408100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 467991861 1250 467990611 467990651
    0x5010e032511061303060507030b0f01030c020714010513090b1f020a021905041409010b011805060d021903060e07080402090f040320011a062b090f0303051603 70
    0x11540107840d000c43e6803134101d022001d036202610341390800041c41300980d010391100c40740c0312050b2171176034880401c6d00041d016100710001e001c0061340150410040c5c407410b949009186001403601e14580312a564042d09c0d441d100750000c01e01c1c0ca5441e2005641403525404006a100c0200c4036000c00e03482c41d100203522802d40105c0640103001100402402902004840c0060403004004100c1400b4001c0030500e40352040b200d074606503207414100790380ca600a10510000e04400c4500003285c90402c400e1040c40d0b000a522031820980a1100c240c0048502c400c0200c00c8034580d5001a80c0c0d0b1411400064082c0d010382110140038000f400d120240e00e0b5440035a52050f882200e004461310f41c1d00d000c0b01c203501c40380010040c101540641a801a00c190006c8080090f1300421110140072481048182d101c0c0e042d1620340c10080c0700e00c5028000000d82e00980410510900284601c402d8490503040c0321421005c40010340d90324104603100f082403162000402042c81c08210107042000e00e50442e0b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 467993111 1250 467991861 467991893
    0x4090e0c0415300302103c020408070303270501050a11150a0f110306090f040611120103061401030210030f06050d1202060a0e0a0b06030a05010e0325 66
    0x10030f003808856852594150407850b0401d6500a4680c1e158030740c2402074890203135805070030486042c015105485046082d25980406200c4083e450034070103165280150030b4902c4012030099024480080c8603282400010002c5001c1d031110549040d04071030742c1c14000111000d0381443c0c0c4d1002d100380040e9a002003900d0350310040e030030078105843c50060064a840601e51003030040301109020030614034603980013525404c03168601800b0924150200d600035020880f8500d4000c1d54040000c1c1c001010f403c45290458000c0c04001031984000442c04110340c00f07205807035a5000701100400800c0301e00d210700c1e842540712a923070701015411580058a0f00700400d400d10704068551003203028a105a40c4204000c2c10020701e000c41d006041c0c0b4050001d0800010800b0150103000b0000da0405075902032050780241e40806014042e0143c1d442842c1004003500c2030740c140c0700398241040090000d12030b1140c0a036a10004544458283c51380c00020302000303442c038500e08203504100c0300140307585044940c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 467994361 1250 467993111 467993129
    0xa0c03112a01121d070501020307150510030602030c03100e06090c030c131202011b030c02040c170a0e01050105010f09031e02182a0304030c020f03010204090e0c0415 73
    0x40d02100484220007540f40756008030780f07003541140a600094248159482041c0c05481e8000c0d074a80041e0780b240075202020b040d02c0000c00e850488600e03d6030049600010036684d66042c1a10b03600e0b94000c07a001100c80d00100c0d900042404100400007402c4801011070409900366440d00f1000b10f01e403060b001d421140007580c0800803e5001c14644213480b038610550002030403a554600c7c260f203001e401c2240581c041546542001c0c58054000c0040c008181c054507100303d5180590b00344001410b141208008100c901e000b280d88450030f4a48036801076400d01c0c0080b80382520940340d2421a001a80b006043c8142901611945074105444004482c0c0141c030360100502ca00601d084141c0850038000c0d880b441c0380d00320074030903100150078074080d1024160442c85413003800482c59140750b6450040724036400502c0043d000078803510740c0020782c81c4007a001c04c1e054084003010909981140d00010b400686036021441341c29810003002004407401c036010301c49044038091012800d0124083d220320 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 467995611 1250 467994361 467994433
    0x60c0b0a020333040c0207030b0919030e030106050d1a10140111070803070c0e091906090204060509100305100209010903030c05210a120c050405060904060305030a0c0311 75
    0x5459034a4940ca00004000c0e2041c44910000f010007034940e40c45010890785030212742c000c503040d44000a4460700c03018000d02205d00b080601d4800b55200140c1c08a22589503488031004503940d06c4180a80d05102d110380e09150302c10305034041e00206034900420788028aa1191410070800013080207501c040c0360282080500a00b54040b41828400c203900b100703581d440001400000c201c1c05141080032070704c5038402c680050700c92001ca5916500060700c8401d403405048005c0c008102c46034400c1c05070310700c000c00005109584801142502008903805421014488000c0052140c14001c6100281201c4021482c04c121030002030030a00f4070380405003c0001c0310011a0401008000843d42d1180c0361802099001da041a9440030f5800300038098001000041d15100022403401010302d944080e441e111f00301405c080c01c0c000981c104c41803140c0d02c5525400c00002054050004016409243da28040207180314100a0b02d842c0c6654101e60440d4040c1c1c10145d0440006031002017096210240c03058 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 467996861 1250 467995611 467995681
    0x30b06090d1403160b100f06030e0327040b0303070c0311010c0611030103110d02010f03021e04080604020108010605070c030b040212010509060132040e0102070c060c0b0a0203 77
    0x814a05240b501c200314800010881c0712440c000e08078242e018400c1200e050140d489002000c013040a600c41c0030f1520307904200a200c0540203400c00046109618126410418607450390780c200340800030203002c06480c0c3c0018060b142040d010341c0c061030300107600a528281d41070760740401c445054407003c1c000c2601c100d05028141e100b5100400c4d03441d040101030000c030f141c441c034004160740300f0b00c001c8810004555034200103041a5000020640d016150070708841d07007054050740651f205440e0300104003240071800890340300f000302400240207480b009201c94907192001400c1200181c0080c01400814040d0720300150001100b03800b600d6100141d083d00381c070b0b90301c0440c082a21120b503903c0c00394240001c01400f5800010605c3c121100c1403092a0f606000c080d040c84289506e80d403420b0580c00d0300c02d07228120b0030702d90000410384180600051622502c3e8581c0409070803150490310010b4031081d0603d040c400030011558011009002c11480d60414011550009030301030000400b207100c40481034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 467998111 1250 467996861 467996873
    0xe03071814190513050316020a05030a061a0a0b0f0c1e1b0103020a020a06110f040f0e09011e150e0907030302061609172119030b06090d 60
    0xc1520118201d20110741e0408824016195400b0000088414a8840002d083c280c00f0f110300012940c0080180d071610715500c00c400c01348070000074140c0e00003100b00c0000030300d601e041103d641c1d10350090b44001250a503200c01002107030303002030b16180b156048140c148004000c020807501c43c204a041e4165980c82d03804a00342c1040340d011403c1fa115805c1068010b901080461803186181c0620f1502081150820040d0102c2c00740b0341c28400140e0282138400d000584540c05408004090400c46042030740c01800c806880c2d1080d000040381e003840c841d0030410f11999a41158125040d80002d110000111a00c00080c08002c4120500310b0b07121549882c401c0c20900c2d1160251010f156420740070720301070090035615005032000714010b10405001a51041c1c6103c400140040d20f6500c2c1e1540e0351034542d400000030304410300140c440c040e1054201c440c0b604440b905da840d943d80011140c423000908842d0b001301c0340c50101101030605101c151085540c0d50001c9440c1540c1c211a11240c4020b0f5084c14 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 467999361 1250 467998111 467998121
    0x606050a18051009080d02070b091507020d0602041a03071218060617120c1e1906090201080708090d2109050601031e030203030109020702010509100807030c0e030718 73
    0x5412401004544080b542c0c42100340c0309170b50410b0111600e414041d0822a81d0b1442c80c408c41c00d66000c103005101991030041c0680904400c5902c482c1c1c1000503a80008200807003001089494650006040007202c0ca285a141d4403a8405440c1608610300001c0241c01100324108024200c0d50703c562140504c40d070700e41c00014468102800b082001d4661401d9001421b00d2118200c81e449482d013960078461540e01194030f81c4440d280070b405d80e403800240d446200d200c41078509000b40641c0051402c5d03c2c18084070000314500981c1d02140b09512400050010200900241c0404c41c600741044202c4a0000d49965103401602d0241e90100740034051044d84440c281b00110f80c01d003032106a00034450000b609505070781c000c0050000e00950214019031f0b4205c2d070712004015800c00e0004000701803059020382a0340c0d0040c1000b500c6c1103100030000e05c40801448203003001c69054030500103040e601d0700c509007801a031424040f10034281c01001a84e95a054442e08804954400c0c99015000d81c6404c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 468000611 1250 467999361 467999369
    0x50a03050d230a030c020708030f07120c02090a09110405070503070f020313060806030c01030b0901060c0f06050c0c010c0906020a14160f03110901030b010e1e01091e0606050a18 78
    0x680b0f5252940d6a50040203031501529001c014414400080b5180001104491000b9141e18400389040d500d59a004040e13400c2400034402e0181207494840562602e80700148105c460f2800081d145a0510700070404032103400d0102c0c0100e29190030425400d41000459400210344c0c1022040c20b2001c040032442c502c00c3d401d03070800c1d242081d080002c0240c3c03c03042c1140203a07000c4041da220074400360011021038000c0c501d40ea40c020f01d5440100000c90044800000c154020900c0e0030000e1500c1c1c0790002550000c1e51250f1a0510000740340d80800028071489a024000340740000e89145001002075803241000070140c44030100c0b452030f0b1400e130410440702e00410300103c44a80702c02e580e40380c90804546a0f11041d1100c4c1d2110ae150700c0309103480c03440786040e40c1d886481c000c0180d080842c15411080010503141c0d00b01c04039410f0f02494540c10701c480b0300800c0c0e103000c04201031000706d5000100f0380102c06a010302500305001842400c1c0c01030140c40d6a840b991411200c05030190011002d24503486e84 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 468001861 1250 468000611 468000677
    0xc18031204080105180a080a02010608012d0e030301180b09012402070f170307050106080c0406081f02070302031b060610020d0e04020901030609020f1201050a03050d 73
    0x214640242465401601c00c550800c402004503507140f01c5085154039400c90300005980082813180700240c2428007a0420700c4d80e0b0f10000440c42d4031b500f600c9084800c0001d40c1051041c01075200301d540c0b2035480d015550401d00384014130010401d40c0d15143d8074007042c000c00064030180002e00c0c2d8146840e50000141c1b00008064200320f581d240080e81c01c07940c8100d041020114001e03110603003940005820070440308400400c0c5800d9140003856201c0e00380c044140801c41c0020094a008140c0902a0002404400001d00b540000c003404000c2150495030200c80310341c00c10320400703825190f11001c4800c00e400301e2001680da5019071400700c0c21441a1581013001c5650001d0b00c56040d58001851481910f00f0f5840c2c1482120482040c0c4e03030b482a1001804c002040030042803107608164014180b01e102c1170401081a80c0c4888010081e0380110786c0141c001500401ea850f25241241096401407106581840595085440b03042e29107800b550350f04280300c250350a034420300600001c500e0294030a09 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 468003111 1250 468001861 468001873
    0x160e011d0d0c030c0306060b13050d0f0f030807020d180504052203020d0f080609060d0203010204090e03031617040b1b040303020d08060109080c01030e010b04060b04090f060b030c1803 81
    0x40380204d204034050006840241c42d080b008920040b0700000c4039000c10700000e0220b1103900e00801c10134100742d6034400301d902844030454540012003105103006420301c2500c0b03001c0c4510348094028a06545407040d441040324014041b1303601a60290004161502074802280b00c0e901c10b00a4645001910303171001485018210420506a01003140842d8407180d5550032511513003c40100c42c000f0302540c0281d48040040c0107e5882d14007800c00d0a000f502c003800140c1059036804001c41128006107031b44075280c20001c1001220a0301c103008107070300f9406042c400c2c414444020141607440d40288010588182c03c00883c1d402055195545011064410000d0303440d910391400945808400e82070303201041100002c210958095017104c415034445400410001d8000ea0045000d8450304440b21415580c582d99008151038900454001c0c01c041010645d40c0c1d40380206000440341a07004094445140020501413071400008494100039451420f076100d07040b601b0314480580783c0184a9605110301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 468004361 1250 468003111 468003113
    0x50a1d0312030703050c0f2a03031501080906090c060f0f030a092915011b03020d02071508010506221410020705060d050714040608160e011d0d0c03 65
    0x11070095106074842da50070722040c1c50f44600c0740800e000344036480e01106002d00c07001d034050b8030001084008605803010720f1002e20100d4001c90071540b05450b0858010f140545014032560000c04064011031142d00810007890220322458031211047c0c41640f04600000b48509104411001e0307503503842e180c500f01a5241491451080240039105048a28a2806c60000081480c042d43c1010f0348a40c01d01030100b41d55122100c4c0001d07492040350506010074000603480c8e0081480904580501c00d400400c03c030700c81400040d1418000e42d1012228242041ca9511034660001006045850035100240c0780c418101201e0b04110000300c103003105c800c07208400500c401d040300a52103030000640d0b00e607488000d500c004907201e07010781c001c00b0b4000384100010f42c0051025442142c1c03003070491401c07030011148002c508499910950059000601c482c090100300320012217485040032032801c01400c880401000a452000700e00380c1d02400762010960807240e510b43c00100031070300c0c0d4041d01d03000e06d0b6501e03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 468005611 1250 468004361 468004393
    0x51206060f0f0114040b09150a02100c09030c080102040503010e0d0e13140f04030906031512020a2102040f09120c030516051b0d0206070b09070e04050c12030307050a1d03 75
    0x441f50000e0701c18101c000c26a2030b00312040c0d08855203005282d01a2811251074030b0181d001d0140c00300b07448200840d00f01c000010949112000015020741030000d82e4652800e0304040c00e580480d04a05416040040c1c2040c0c0990018a19106407809480035940310b001110f80030014103a401200d00414440010012041200d0030020301c15446034807024000c580329079003102110a03004854100c0c0d541100709004100020007c0382da600e2004000d01203454454001500741c1c41c200c11840601103034008000c0c11072410703009105424000d840c00708956820f81d261a1451004014443c0600111542c11000e01d4401c00448110140034007107102185039515015584141003210184404021540d08070a4604541c076244110303001440c1a091a02589032880d03a00800f410080c0380e03104130388001031403960b40c038a890722031405200600310311000007051111402e05140c1580c3c00e81c00c20400c05c024a40c0010035250b00040314600495145074250010380540528020140e1501c218401c502d10701711 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 468006861 1250 468005611 468005617
    0x140102101d0d0914040e010b061903050c030f010e04020301090524100e1f030507090203010e09070e22080712090602010c230d06080106051206060f0f0114040b 70
    0xc80201100c0320b458074500100c400c148280581c00c880741ca06036a80440303141036005110668914000054803e0101000602680c000141304e00b08003218803c1415540c2c00d0320a05500c030200c0c002c0f15281d817030540e1240c61000d105020380b044101a2350041400d44d02c09503c55200d096215085510700c0041e1804104610030f01c019000042d841b000c002410004a24078800844100c40c1003060180c0703038a420604592035010b2405e003580c0101d180080401c00422001e001441c030003400683c3c95043c100b02083e6080d0040c403056039030f80140002c004e465500c9200c00e61200e0804040300d40006c101440c2d001d8110040d6014044680118607003090200741e00d814120301d401ca88540c00c0d01a907a0409a00342e805280090001c0360100d0101043c1c0701e523242c038003405002d044c6405450030f0546403101c0204c40c0d0b04e401c8000645e544400030301050a008801410704d500850007000c25281280000c0c03409150103d40d2806070211000c040e1159002d0300000c80301d1043c08402c19210340d00c407421005160 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 468008111 1250 468006861 468006911
    0x3040609081b06450a050d050d0609091122020d0b010305071107060c030504090e010608060604021c020a05040b1b01110306130c0e0d0605100b0c0714010210 69
    0x1108aa40c02c0780c082c03118421048004da901055801c2c2c0341d0a40c060348405242240e61107203000f42202d5000240052042070314244082e00c4807a103a1122035144030450f03000790440108240340c10130704004030340e01c003c03e1180004221030805d070380c50a16015005401076140c000034040e0001caa20484e50182d41c1002d01c101200b030303800700001e6580141c01c0b9158844075400c40001e410042d0140a40c330721600041c1d52081c000d0410174949a6175002d60021581480381d4a01c01e650360722020700155009200054010900b01c900b90b06004503000c10101c01001c20780c0c06080c0681c0010b003080d8060040b01600e0003404030321002c0781c0b241084001112a444420402c0182d5441c00748800c40c0c0a03040307015640100009840708452044207899a401410710040c0c1c0750501c6420034001c0070310307a00c0310321900c6024810300c004511402e03c20084040c01506801a0582e00b4091014000310200001c0035800c40f1402c84002084003030f4400141e01340050400202d060a0414074520724030100a04002c0240e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 468009361 1250 468008111 468008131
    0x1815070302071701200a030902090411090a0b0102330106081812030c3403080108010513020d08041e060f02300f070506070807030603030503040609081b06 68
    0x1964209824201d40d5402d004540d04640c1417008030100c052140904600344071401c00140710420303900091941c2c0411034044441840d04d034001125410300303c10781a00441c41d07135000e1141d1140e40340041d4070303180756209519032003565405c1c032010210b008122030700c20b0945245c01c0146586400c1e00400320b02d021100070881780801759130a1001d100c0001c01c40c984003000b40c101d60558544241007106a0300240e040e241b2040c41c0029644068003045640401d00d80910905941e5055880c0181124a050780b110745564034003410003c00d0160280302c034941c2c580c11030b01c0c031544c0103042c900302071140256040600c0c01c0001d034408001214148440e84240e54880e00c44150b4a040104220f070358031b0f80d6141407c6110020300360b1010100e015243d48420700c0603408420b0078542c8107050060307030380c01c4000c040c1c40d0799020b5014010b403181c020f0150b9030800a246014050181075031400750451001400040149641c0e024540038480c000068030061924a131080001d40d0030203000700c4d610101642c5400c05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 468010611 1250 468009361 468009389
    0x1b1506030507060c02030a02040e100e0f010b121009141c080c03070c021207031a0103020a0b03010b070b071209030207061812060b150703020708061308181507030207 73
    0x4844c041d45403c038040758002d00401e2070f03514903400d200243c800b10000c80c0c03c5100c0c20082c02c101a0080c01480e0041c0044c00041040118a070410b0303095412120314140a584d481e40d501c03003074800211f1494400e4006045c003046400c06c0d860b0015a810b52024000b42c18051040e88030442410010030300181c0d14580c0c3c07044030b9511800d440180d07510085c0c1e0303154045a500f000c0c0c000142070000030350320080d214000b40e0362803554a8841c0c00140c590203003205115035508005000318170b0300c0d040c0200689043c400c40703421036040c8107030404e50b40324948019140b00c41c00d00014442a10801307003007611240d441014886506180b6003c1e6a941542c042d15004c64480520303c01346c2c4848624580488005240200207111640c4582d00146a490499038120546100308030400b68a0300080c54114440e500806480d1300e411000c070705003a005050344460001202c080380c0416034810503500b105980100d20441c4c0c40b01c1100084140c2c010040000494401240340b6044c1a0045110b4040b00e0082c0700c000c503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 468011861 1250 468010611 468010619
    0x601080a022403040204200708030f0108030307050f090d021017060f0a0911090d0f030e010804020f120c0a1502010b0a0e040f080f070f0302011a030d1b1506030507 72
    0x1a07002e8180103041e4a5202400001c1c05482c05803c10084815505c0061004034400c0c080080d65a001200030303900c48000106002e611012010405c0c0140384041c0a5400e50408050003411841003d00494070f07140040b617904503581c1c403d5016032074968020504000f042c2446c0e40503000b1500340448943e096054400034111382049002002c1400000381001401c03420314103408002d2482101107a0b040c1c0e41403011131580d07112081c1c27951040d4002d45903040e60403081d180050540349014142410446103405020050715084150b401c02c0703030102c40c080c180c3e079440c0c0b5019150913010080c1e1a4484024600000c101803620b5104201c00d000e90300a001401003602400940d40c0e45214110845108000040120300d04032804800c10744503e20030741c41d25032454005c1400760403120f4146e0f905d034110354a01d0105a02445864080d6041141c5140c20300040400642c85011142143e02444042e03810380c58004020701421800d960300040c5100040031020040004100324002211240702e4080c01003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 468013111 1250 468011861 468011899
    0x15030606040902130f062105060109151809020405180712170903120d0209040606030524031608060709050105070b0c0a05121311041e090804080601080a02 68
    0x414060300609642c81019041c08090010161913805c000d0150381c9110210303400090350112072142c00c2990a42e000f581c09070130110705280341a4006021149800829004144226810000c44807004501030394140c030386580700d000c0d0080c0c1d030000303600500e08801c0050114801d0307401c03031b04440f400d012600000d44640000c143c10740321000250600520340c075050110350750355005022021018041d0790280a628903810b074103070001c0c034004040640220380d00720705080520400000741524a02480075042514500c402c3c9131040c031521040d0020788002c141942c904001c0e44020311114108200718030340d10b06819450307420607608017000880f0b5641c001034075807041c01034030801500b1481f18141600c1d0498103c2090380001e50700400d2040c14001d9030b03400e0708488a01c034803a031503500321228100c11510b040120341d4801d484c402c2c4a40d1508601700703114440c503000090303024100b00c80001c440c89142414140c6000d02e03449040c840c0300341e00c000704e200078003c5500101c0ca803099600d14001c0d51076117200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 468014361 1250 468013111 468013121
    0x10506040209030c0603090109051212100311040506030330010503030304021c1703010303020303071206210602190c0308060d030c022211091f0e010c0c0b031503060604 74
    0x90341603108a1342d800c1107140000040d9084210100005403a00140ea5813608051a10780c030b41000c642c000c07540070030302c03600281040d80c0415141215007419007160360316070004a0b0400d00500960741e030350006d80d0a4500300125911040701c0a00d00300d0242039007801c041c0754501c01a4007048815960000a980e040c00425280a00d80c020070440f8503204101900e401c0480d54001070b00d002c10070202603e10702501c0030085001e5070299010f55a02e1406500290000d10300c440a0202503150400400c044103410100345805458500c0003400304407070f420082c0203030080c610f019103961300c04030706000c0340f0380c00208904005100342c9032425140c2da00301c1040319400c0c4520010307011400002901c001031818a000800c4494103900705a1400c0c0c50709406421100300030343d0403500560000b4203081c28030b03100d08090390701c800f448001450b10309114002800c440040c0420385c14400395484107800c20070300143d9400a03049042000307450340f038003142242d0084941d10b4518001c0c01342102040240c2468052 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 468015611 1250 468014361 468014377
    0x100504051602120a140a030209150304020f01020609120d0914070513110409240807061704080d050c0415020d0e040209151c051005010f110a1e0f0c080105060402 71
    0x1624038188050805e981050344140102420190700308800b201d01d50f0b60204406501c45034103a001c1c2c40e49814418081d240416581c01815584180e04016070b0000005000862403000c2c0241d60f21030f008112044090410000c1c001c1c4a9040b080040110180020344642115001c0390041c50360390080100000311030108141c00000170003080305000c81c190b00e800424014001452800b106500b01d01e03110120b28a07508060465086040101311450380011548000100c4840072021403c050f80c0309041403191460f107481e082c2c0c9800c009541c2444241c142c4004040c8243c0c80c07101d02030040002500e40d208010f004001c140c2c0900c00c9e195038203081c030170303110000c40146c00d040112445d8559440c030368200c030030441784020100714400303107c540c43c0c05010300074010308180100240c00c00002410004000030441700300429040418240c0c0000141c1c1c480c0c1d19040103880c0d07004805419107030059142c81314023403d0440740503107a000f044a0450000121a4000020400c0d074a443c0300b00801c0c0c1c810080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 468016861 1250 468015611 468015617
    0xa020607081504020f070b180601051e0405090f0706020c1318060506040209040c05040e06100c1b030c0e0604060f050307033f1701120803100504051602120a 69
    0x10249810f0915500070410780c20150a8541400250398840040100c01c07590b801c03016504401002e0400c1003040042c0c00351004440210501008201e030340308040c06503500324426502c074008a050342406108101032140501c0980740c04645600010f541d07903007c10185401402980709042c0c00ba9124401c05400a10b8514030000c182881d8603810040c1c40b0140034268003550030001800c00341e44038468901c603400b203921025111450451329000c1d408009100a002d18000090200503540c840c2c0c4900d090759000c00318091102100082c03401c03540480d04020007424042c840807618402d011754007031041904803414803010b5240d01c0f0510780480c241c801c56805900ca98410700003d524615015040020440314900c2040200141550b51580c6040c4800307802d000c441600324150b10107400b0760306100d0390907282055450094015014001002c2c094100403010001c1544140404010001008000c100348240e081c480003a0000f80704030043e040c0980728480e031914988130148140c42c02818030352 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 468018111 1250 468016861 468016891
    0xa02070602071e0902030601020106050307140a12050304060c030c05010c03060311151602030c04050103030305060a120b010b07140d0806030714060403030513031e02040623011b0b0c0a02060708 85
    0x213407030040e400c06040c0f81e0555403103001c0800d094600300448801803001c0c1c03002d168030080010902540c202282c216140400368485081c0200c0d1000048a084640f18a4840304403490f9083c121209590702038010401c2d4240040c1c42e41c0f40340d05030008029240140c04580200c0c51020800c11074022848892400c0c8000707000105c002d107020f941c140120390024040d034214a0703da03c00901185d109030801c03004640c0e58001d015050400f4400e00001e48000700003828600c0a03034440000e00034051140360bd00c414001003500c108130038282c1092100941800300c850040d00d601c00981040c404545c1c01c1c0c013034400c02c0c0000600744854010a802c1c0000981403030310301419500d0464003603004401032030801a1044001000441984031080e8854046c0348205034142644100815260250702aa40c00b8030003c100c1000c5084101d403c1204440900307050b0100b04071021145540900480d007e404228200e0400c103034007460b01e00070101d05d07030140d007078031425031310b0100c2911042002e03102c94071404580d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 468019361 1250 468018111 468018119
    0x91b03020903100b190906091104030b22140d02300d0915020702010e060306031b040609020a050721023f090a08060112020f04020706020a02070602071e 67
    0x80d4006603041070040e04d601003100101e031440d04221180e50024820982c2d45808210328810b610506070842700d8035121910700792441c0c685450042001d08618503e011124495500540409000700700d01e501c07000245550803411211070f11000c04200d881e015004840085003d00c0f1b0a0160110259072002c03500d49095801000316160741010006100181d81c450004000c908045803250146011071070150b076400840c07000401448240702d485000e40d2091051001d555004035060318004490210040312141c0d403000507005c0d00b00c40d030104491510000750180f045600c02c008089250144103c0d501c045802403048485041c2d0511110040e0460f20340e00841400140c44415403e11680d03141d1914071b0806c201200e44483c2d2101207044801c002185441d82c208210341c0c000030111300c0060034496141c0b0b41c1903144c1701000040280702d030340607000c4603d0590740d9506440c24107170402800c545510903044082d40c0c07a00e40e40101d0b13003d0300c2042c90000c0ca101107048500750391980784c0222141ca51030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 468020611 1250 468019361 468019393
    0xa020408100b12061303020d3f022d0c060f07020106030b0f04031d060307050705030705151f150f0e0d05010203070f03092a030c091b03020903 63
    0xd0703a816a405448041c1c10985500300708255801070b04441042403007045e107840c020b45007450f8021904184826508004001c0080b01041e0303040080d82a82d001c403404040e0030a0b058085881041030f40248041000e07003128503090203c155000b0241541c0710b0044007a0381d00d6903940240d10a0702d040360b0000001a002c611451035694001c00076000106200703461341c1c1c65102c501c038101d4600381c41e201040100404d240c1d010511124580c400d1141006c3c0c0c46d10840807a600d4803008000d10148030f03000a0388000c12104008aa02c1e99420405030740c0458152260b00c0f4600c442a51201c0f035084d08881c404600d000c424460400f201c203114504843c41c00700c01c1c0c09032007032400d524441d020700c1540c0c0760509580e00c9490303011060314401d000050303580ca003401d005040c1100e0741c1c4440d010146010100b2000821248503500035491980030200750451038440c0b07200754030841e0801000d004001c0c0380007840345a2500024031a00b10002d60419035a1982001c400301e00401d4503a65040d401004007001001d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 468021861 1250 468020611 468020621
    0x11121609021c060909111f0f02031b0714010f020d0c0204090503070b1f06020c12011104080a0606061706040c110f150c09010906030e1c02150a02040810 67
    0x141d46400801410b02c01c41104084400d150320a0310400e84079034103541000b803105010b45008104540301ca0307808000340702001804003000010380c107202d007281002c2c1c12540200103490105543c0e41c8000c00c402e01d80c402080c0c07540102d2080081400101d61000c2e9a5800344483d407081d0a181c0d8001c00c0c203103040f00c10883d0314101c01d00041c2d0704603a0b00d14030030000c03c10500c020314801d4000c3c40b130001a41040d601640c580500f007403d00102d0561454103008a990100348500c04207422125030320310384681101e003401009071102c41042d5000001e8000707130300d00d00403440c40302141c02440108515665200d06a8212202110858101c8415000607255107030903440489013003c5c80c5858002e0002d500b601d00e1510282061f0340280e54008500f49407402c1021050302c0d030180004403441d0a1204040020741000964001c980505449884000f01603c04004540c448141110325911280c0d000d0341c0a500c5442617500c00500340e100000040326280c150080350203c0d1050001440c101a1103d602c1c80100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 468023111 1250 468021861 468021877
    0x1c03170601030f0603051e07050a03151407180b09060d0903090e1f090c0c0201080403030e0604080301090b0108011a0f09060d05180105070804060507050d091112160902 74
    0x56075542c00200780f030600b441481c000c0c500c01c0000385200300b400d6040a0311000e42401002c01540202d070188100d40310580588222944240145010034a4140c0040a09030715031802590f1030300141049440b0b40d001807075801001065511050094a46000502e144201110b0781c0c0c1040301048210740f91703011940241341c0780303000b481c04000302929000410910f503800d5480c0310740741180c0c1221181245054000310010b04441d08208050610000017402e409014a0042d060001d410006014580650441e20074140100e0903540a8a05403820784225042805202071017440c000e000b40d5194000c2240c1810380d440502d81503801c000b403400b50443c5500051900e4a03c0702c0503c00012561103000c082d02008914400128051400da00c69451054405180003400ea040405000e03100742c11040140d00250026000700d05a95440700a541d00c1c8500700440e01d0a6251142440510003580c0401d0301380c140889250f40c01402d00b2114a540d0b01381d4810743d044d0200c4904013042003c000390f00801a03a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 468024361 1250 468023111 468023117
    0x12052a07240f02030103170705030c0a05010c120926041707050415121106220f050102150c090307080a0503090a090203040f030f050d06090b1c03170601 67
    0x44a115610440052860440344541a507540721410051949000d501c840006a140071402c661560f06d400c0d640f03104c42842c0c1740f580c010000e8180284001401100c008400c0c0d01c081b076904c1c20700c0e864054000c2104120302c100080500da1504201c141e03034003694050300d03080008049440300b580a00703070401074030345c016604104c820803000500644000b4034080c81140c03030003e4030781145820203100584200c000c0d61040c4540081c2c003401101002100302e4045600f11604248503100034001c00e9640c440e08010090249403070b08042e500c03000c024007140a61b0041000508000ea9070801607a4892038a0300ea40300d0341e2131010000b0742c83e5142401802e00380c0c100808407400c056440740920308015101e4401d076004d40000410301914103000359260b001f01660741d030031491440c05d91a85d4a0302001032100030301700801c40008258152142098441000c1d40b018108080d550310750030b000060a48852103800b4802102c542c40c8a40710381c0810143c420340507140c0d1101450210000b82011a0080070b032414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 468025611 1250 468024361 468024367
    0x60b03030c1501090507080f13020105040b0d020d0c020d02030f070c120510060b0f04050603060a03023006040c0e0c0415080108160311041a090c040612052a 69
    0x1c07204040100c280d00b107603034203100d5125504003858401551002000d40040c80410003d1040900041c403d0a520030103174020700744005514801200c0f0762185074054a0565800700b94281700d8115580101030b4030185410401c10800f56220981e168030f032070484400036030410320030315030b2464242000300219803050340c0c0980440e8841c3c1c0b800d1303d085075118080c1c4090b404054081000b5420344240e201030400d440515040040450050b4021311903405128000c8401102040542d01d37120302000180d036005020365403401910845895640c0c6210000707005801080240424003004a82c080c05990402e200a909a00f8020b01041000010704450444c19040000180d031140342c11220316055030503500c5003400e5140c8806280341c95000784002c500304588140c2080061034500942c9036245040c2c0d404154055450742c0260301c0501220030b0341d00002c40100300401e4841c548000d1007541c0640c0c440000c01b07035076084580f0403650122040742ca03d0511418521440d000903403203042000c60702400ca40717 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 468026861 1250 468025611 468025627
    0x4701180503030a050307090609150c0302100504080a0219110609120d0507060b030f060f070c08120601090b0315010806040e1515040e060a0c14030f0403080a0501050607060b0303 78
    0xc6142d03c40241140060804402d10621039400b1128400604c0903180c6105002d00b0070f000c035001c030300d030500d0007200b0b119001801c501090300078131020f00d00c100454002c0101f40740c10f00305101c842d440152200d005005582c0b001a185c07400c0c8628071040c0b078000180d600102c03500d2040c005039034041c401d810381c40001ca801d240c800d100304100c0480c002e6166581c55441d50003030f00d480c1e000e641c210100f0324425045411343c201c100b50001081540170030694075000980e101d907501a20b000100c0440500503030b00028241c100301001840d0f00d4020042030b80c038a00740d642d607981030000300c1c001581c003410b5040003000080c03441d6114005441e006240141b000038201140f1303494900e41120398aa1407214000042089994502c0c1002c004014900b030703400344940c1c15801440e54413aa0000c2514605903903646442005501c2040d01c90124a280002265a41003018084281031000c840490018066200103281d26540d13020b15812104050084d03400c0c0200755646030054588044025014403062201038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 468028111 1250 468026861 468026863
    0x118060903061d03040b220509060103200a0201020c0c01020109120c051e06070f020127080f0304052107020f01051615060512010b090c03090703064701180503 70
    0x801004031810700c0c1d6543e07090f010384407032290032100c00540c40401c51f02d040141b900c803140080e0303200809183c0014101080e00009900ca40700120b0114981c0b4003103058080940c0560040c01040802000c489444484400480c207880741c0794001041d983c0c460502200503401605807030300b111320406c107886c00d40b86c40c0b0b2102c615040d03101100b0580c0d64050404d2000d21900403080003070090700e51009100849000010400c401054020381d04650180c0032208144080e840994aa841812419650740c4c103040c20015521843c556021420351600c003031080500c1c1c088021580f10907030280221456901c140d0056a00381c0090f100c0c0201c0071404080040013038109d0ba580d4846100c030380c0b00010707140e05160a1084024140019000c5607240c4621041c0715590600a16440081000c040e90b0780c2e80c032200d906040900d2540014429414180d030b244404052515100e03003181440c0c2e4103074101013142c00144002a030003403c403842c000219640780e5103521a6208440e0001881c216030303510340c0d8880c046 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 468029361 1250 468028111 468028117
    0xc0d0807062d0509010627060509040503030108070605091807050c100e010606031422050303010311151218070506041203030506030706021005061c0f020118060903061d03 75
    0x310081107411059001c201c403840c443c00340c100303c0082c020000c02c0d04045101024441620b8841c0c11100402c04801c060700041e04641d020b804082c240f40c00038106454100c3d44c81d0000e0060b10910f00401c200410500d1154095810851008000c807902d19250994400001d0015280f2410040c0c04c002d000307540c2000b003000b542010010200000d80c009602003e608442c07403a0084010507040081c0c4050000100300c00745d420121044a188580250400e08140035191000050403030201000000a01ca049070f143c18907140241e44180c84042000300c01e100381d2084100c0203005038070302804524841c0310450f481c030610b44200126680c03541c81e040000c507030b038000341c2c03152242034110302c280010541c0c1805016000407090f40140f040ca4100312000c2d460368104030420418558440020341603544034030380e0240500c840c00c61190305000da41006c8064028000c000d0b4081114030500580320303000c54540720102c640d02d98030048170500310307543c00010b01034410010310107209908142e003d1007814002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 468030611 1250 468029361 468029411
    0x201032a0809121608220b09031009020102060f06011b0b090c01050a230906030112060e030a17040807080f0a031103010b0904150e090307060605030c0d080706 70
    0x40d1202071a12881451030000301c00c0b580b515515051113280220300307a21039080b000d60360007004c154485202c0d0309030300119883c40420000c00b20501200040c030341c2151005008881e410760075500e03401c6030100510107a0341c11620082c01030340b2a90005012048280805030858030500d000305140c4075030611004181c0300d2600c00c1d80c3c0b29003440c6c09d10801b848100701011032078a00303081c1642403446040d80903201134101508400c3c0148410346c0e0784242080d0364100c1d00d0141006160907101d507151030324450a2401c070b440484a65281000141104800109590a000095a03035110041c5044010103c8007005070084032100d402b8450140042c040324050320320f11402008003070304d44040031401026258161b407145a52030081005020000c1d280381115100c00d0309942c08121802d8140303d0015001c1158010071f61001c0b41001e11032315850110041c00d5550040d0814480715840b00e04250315500c1c11409290701150382807000c40046c038100b02500d0200e000b04800110710b6141d2403611110416954 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 468031861 1250 468030611 468030617
    0xf0f05070306050a080606150a1b1124041a09060406171b04050105030606071a011703090901030f0c1203020a030807050c070302210a08030103020a05010f08040201032a 74
    0x6041c41942040250900241700c000002c0c45241410300110342804400c40003903a00280014116010500500f903502d50f90880c0142c0021400060406440e014044074086100b401da64855100c12841042000100c4a010b6130382482c241c50803103d564a00015000c2845402d400d02907010150b03640381c042c1c030003032016450340010485001c444001102000301204a1880030030603001c60b18a0f9070342520180c51083c2095aa0b0740c913000d0000e111400385a80007841032201542095524100650f2a4101c0d5115000600044400301e000b42d1640581a4180d0b00b00c0d005100410104151419440d01e490103803008505550f05c401400f11070002c07283d002d0340540c0c000c40c0088101507000c2e5490364080e581d80f802c1428480c0c0c1841458a4040e5484060300c241c1c502c43c0407110000003102e4070341c1a2010714040380c1a141032494100956002440164801c005160b4001015401040717403681d00300c116680d00c0125030b030340c2d80190010500140c004440c41110b00c01412840d60360f40d10705680c1c0f41903031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 468033111 1250 468031861 468031871
    0x9150406050a110a05090d080c1c03050702070501120504030908030a02061914040b060325090b100203032202060324100c140c03030a09060908010506060d0f0f050703 73
    0x729902c0544a0f40034004080ea1001c00040020a40c0201680c0954200329030f01c0c2031000340c0b400c0920240c01042d480148600400c0020242c6002c414400d48100c0041d8400b8015951101130690f02c651052103a1408201c1520400d0003007d55980001d0344540300c1d091a1443c0b0f912904400d1540d0008500000903a0089052080008401d211001e075140f180c04140080c0c0000d200c420300c199009040100320480081c0842da45580a00c40d020240c2c1c1c00796404d5005591600b044003660300c4620800b01421724100d00c000c070b58245801010f4071810160010b40c40c646072540c140460f0880c17102c42055880720041c9a0005949400056020740d201d949030340c1c7c00b012070340c1940044007002d0800d0f510403404810454003143d000081d40c803030150000c040c54030022040d019030b41030a0f0294940e41e814000014070a01443c0c02141e62401d42d0040c2e681d81c980c913038486800340e01f01c50065410940c071080074414115004401d4000020b1501c0d184004541d0400b18071148080c0d07802600c01e41d012030b440b6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 468034361 1250 468033111 468033121
    0xb060d0c090e2202040c030e2a040516051b100f242c070c0c080705030c040207110901180c02150c13030b04030503042f090915040605 59
    0x72a038982d0800c00181c0b4036a2109008503401c0500f002c52280203014a4941c0b6420b04118000d51107070940c80192015200c5418a103000c0c03a0700025120000030641c101c0310120700c2641424400c4500c9812400d0154025541201080e9450740118041180c0381800564221100000f4800c250f01000b481c40d0103e019801c0c0040d038801d80f855001d40d0840700d250100d030264410310007041042144c1982140540c4580010109000384c1442c06489407406058000d126049600801c0151464000c00c1c0744a4003540f0341403030b41d4544641d441000d41c990712404039014245025401000c41502c540c802d4a684241000400c0b48028240d0107000c45650102400405440a00550340d000c1042d1000d0076a0921402250100e202c1c0504004200300d00496240c0518280305010400380d0382224030800d2610b818a0f000b090b940c42120211742100c0c0c0c41004d680780e800c0c244e00340c40e002000282c40410180019090180401005004056a00c60300150a10011700d01e24001d0142d03024110200712032403c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 468035611 1250 468034361 468034379
    0x30f07081b010213060e04021204140c010c0f1203090605180111040308070f052103041b03080a0f12062414030103060e07032f120706030b060d0c09 65
    0x201201c0020982d004000521010102a410030181c07038590900c5442015200c0101d002030040b03040d2070000c20486020b020500c800301d0420141500c03194111894042c1c3c2c1c000454002c3c40d000c40051054000d0202d030800200c0ea40d14440762104585000202c40900391907803416074006503a1401a41004025041490b90a0062000c1d03040c60300420f40c5024555581c0400c03611070584040c02030300c02400501d0400605001c0550050401604548244075032250600281c2c015a0115035861550081034950002081103000300e80d0403482660401c180c0440540b103090b222078504040000f58421000e4008881c81003001070240d01303402a030010340c6100d8200810000100c200c041c07000000340101e80f00109002c0342c0c19254002c8000c00c83c0d06c00c140131a031511002d500018040080c0b80c0c9454500c9880714a07140e00d40e142d801520080c1c100d44024849441d89021045226800414081c1b1a4038000e40202c000d011001c0d107020302d0b00303020700403200c02c90f03440002000000d40d0840c070402419503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 468036861 1250 468035611 468035647
    0x904090b0603060a0615050d0b0a150e0a05010801030206090d170d050a0b0a060c1103060a0218180703180c08031e0412030804421814030f0708 63
    0x704070703608008a41c140f1031b44420b1502408010001c100340022984200804c0d80c104031441140a404100350300d44800300b038003c040001901c400000d9803c3d0800304546400e10b0301c1c10032100c2c1a154900140d00315000d018140e4040c650341c03a005552070103004006903080c080300350700c405808480d5854600111504050b83c0c4041c080d8900c1e6802d000f0010800d64400a0130011182c0504000304c1c080450b04d0a2411141c240920030740c503010740700411000041d107170000c000c0c0500c8074034000301040360f90b0304010000425901c42469035400200041c0158040c2d40400000d0080178100800070801e66201c01e1340d0504c54101d0395a0360004118518113205c880600c1c0d1480850031007140c142824110b4484600d507544030044d0401011102103414010b02c800700c42981ea4003181e40311030307103015200d0079968030041003044850302a001e40105150500d52084180031046003071004440981c0d030311240404002e4421168460000300b0000842d01c89140090043e64030841d946901c0b0780c851060200c0e018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 468038111 1250 468036861 468036871
    0x4020d0f0629100f020a0602030a020a260708060607060216050715050306060d0f0e0c011101110403020f0406080307030f02010617100c21061e0f0b030c0904090b060306 74
    0xc8011a14402c07103580d190102ca051a9031894040800b08080307000b01d00d0003c04201c0601010320000910020003481e40040c6170290641c0c481e801b181012000c900400104041c01c0d4079811800d2010502e114401e000054100c2c100411039403d040c0035440d0a801c136404220050901d00e925400f10041007828080400104800c0c1c6525480311511100600725100090a0f148a40400550230306540441d6018031801a1022820850743c51207407030069442c0f0212032901d0101e00806450305156005001c0c102013426051461414a851542440700b44049840304a0b4059100e02d0302041c880d00400192020600a9948904005450704040c0c2120643e40100f46050804141d41c060301d50001040440012000000140c07102c071480c0803100d120040041c1c960720401350000c04140034260300075005070707403403d10310984d03050107500303e211512500d10814030341c116004000c000005000000d513520600c030304601403400c1102400101250f2182000711011105034041c414030781401c010241d400307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 468039361 1250 468038111 468038171
    0xa060b0f010f1b0606060c0b0a0213050607060605220b010c03081504150b130e130308040f1707120c08300906250e0904020d0f06 57
    0x881034480c0020900c450078411007090140c0004401c072401c06464844103100d4201504112482c1c45002c001c00c0300c0403280080e81c00c542c0b4040840c01c007145901c00c50b2000e03d002c41c682e01c241d078a002c0a000c05a0001882940c0321a07079880b000030756031192600d07072038000e164003807070100b0f0884000d0283c212150761034014100000c03030064500207900301c0045a04111000340014142c0b50480004000d0f1148009411389000c28050029140c0c025001604402000041403501c3d40e48075168085240011241902000b248411038400700340551101030b0000d000c0c0404a00c01440c0ea140e052500301c01d10f020800784400068868140103d614020400d507a1038a00300b0892841a00d500c502406148040c503d001890003c0140e00c80c29441f0220f20114111025600303417070141085503e500080f06c0c41048022004107409100b03600030455004900c090b11400410032005040c4248244002c000b20f030082c245180c007201050442c401c2c449403500c582008a103c007060031140d50001e08502e0b80002c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 468040611 1250 468039361 468039379
    0xf050118050a0e0408090307150f032f37020c0f040c020a1704030b13150c110f0115050a05130c0e0d11010f08090d0804060209030f0a060b 61
    0x2642d8481c10301e2000c45400007168002501c0e9400d0441c014840c4074400b5505100f01e41000810121207111003600786002d4490200313000c0d00380c10907070031b540a000c00740c0340e00302e06242d14507040e24141040d00c0101103081d055500342120365044a46901c045605c07298400c141c400b40250340d00c1208224050300d0498406840103103014004500243d05264440344910340b1440b84803032180c400c000304050145c009190140c01c800710407040070076030f1082c0029544441400006107543e914150494481d641c0004082690100442500000c2c01c00c1089013041045070b00c80c0d0802a0010403c04c2c0c03a060703013040009010160b40c1c60032100c20036280e2020340902d88210b030410183d0380c0ea2a04c0f11611b10000d0001c1024184039104a03400304550034000c0d44890f003240c0c030500340b007902c1e002d058a4020a132211445100e000000b40c821a000321000d10290740010300900406201e04034580d0444e204500160030b00d19010002401c1480c07034045407031194018604c007010f220b0f990040814404007a14a464 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 468041861 1250 468040611 468040619
    0x130b04181103150616030c02120c010c11011701060f0e1f1d040203090a0611090904060c020a020604080c1f0806061c05010303110f070e1303050c070f050118 69
    0x41d40d01000307041c030000420b0f600110716640c407050100e406856080c8400d0421140300e203006014407060b030304268041c40450780f5414010800246444104034141c5620b00030101071703a80c41080c2c402940740a410401074541c2e02800d81440841a4068045c03030700c070150161750101c00280703002c02c0d4081d505e1090100345000c0e10740210251000540d07403140d1034080c2140b40c51080107048141d10512042c2c00034400010444c0441c8041703000a5020320400050155560060b0800482d0050346801c2d6408582080401e0018117103911070ba0540308180151102d140c81134000030b100d03411075804000e150b0458503199800385400d2210280c5150030303802201c6212219880101110303001000075001b41750004d1403480000151003001800c15003200148410742c0c580c038004116518621031404584209480b0020350100402c840064035022088550181c0e130b4405184040352889030180c050250400c035205100f1810300484003e0007403803152b95519407611000510401099003d221038140c0c000080c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 468043111 1250 468041861 468041891
    0x60f06010503010b0a02120d092609060a030f0f050703060501230c1c020114070512040312090c1202030c0d03090e04110607050714190308030c130b0418 67
    0x3e041d103074044150b84d2203802c0384400380d150121801142850341400301d183c0241ca44141c11240490340310b03034128010038030340000b800c00e000c017401b0004072442da0600824100f030401e98081c04100e40245404102e10341400c82100444400300501c082c07803501e5108212059400d4040c0600030102880c7c011080d55941d14070b60100880c6035040c2c103079400009540001c0080400102030511158603075a01d0702d840240001e402028100b002c1030300d00881c00b0007d1500d50207042a00d025209030b8004007610303a540c0d03904030345102c0420240c8002c0d03541e42c0e03500c01c0414041e8804c02c001c0c04240014002001450040628103145600010f21503044120010006170381320b024002100c1e0b0381010000191102d00d040e910003090050f0f401d0300040e01007041e04c18810300066040403201c018800710b41c210003036014003100800c03203000208949540301c420400280342c600150b600c0f0b5044510a420111b20b15815000135041342d004101403a40801c0038040700000c80c0310300610130020001040a009103070080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 468044361 1250 468043111 468043117
    0x913060b120a02040c0311161e02061617070b0105120a080a110a0204020f090a0f12030c020a050619141611030f030a09030c0b04050a03150f0203070e03060f060105 72
    0x2409242c6130041d9440c6a4000c1d044908a80c0b501d81040d0303140d211545055408041aa0082e120502c0d100070045492039400c04401c2070030340207403038548cd201c0460304804507507081010450703a107003c00800410717031000c0801401d81c20b031058007000c02035490702007005012106106500742030b0300304115510000e20a002110f003100c449060001041c000001810704200380694040c1d04140005031034041d201428000b01540a001c550b5050300d030b074540d50034070b60f80c401501a015a803080301000a020a00440c00e400d0704074801001d01c205244c40d100400d1903600040c100342071580031707540804803c03604204a402180703111618039003440480c44214048506081010b0024484400303074800301d8505201515044a007401241e59404401500074030403143ca1106440c07802d4680404100720074070001f220201c940080c0703403071a010300316140c4d0348451410303c841a21043e034a000c140803850031030002c2c602c0b0b204180c5540f0481501482814200b201c01449580381141120807c01560703002030907 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 468045611 1250 468044361 468044363
    0x20d030615081f091103220203060a020d02070206071a010b1801030b030a0c030b070f09030507050f011b1506051f030f230916060207230913060b120a 66
    0x440c002c030110914000006140a0300301c0d11645003400017001005c500f500045000d40142840c0c00083c2c004c1804e42e5a15215509000b503058000a000c6100c0d034203550003811490b816400014608001e560008501d6400010216141440c0a8542c519102c1e02c201c0c0c18010900441020700c0c00031424000620584992310301e9060640c0c030f46c0c410384d09840420118213420780c000f8070200201d44a00b80300150010407505800003580d9404620141482090b022040303d60000041c4501400d040421480c8980c142209040081e55020307074101050b130f8080049010b000f03400d81e42d00d1520080401090310340d40d800c860301903c601400c1d01c40f4015a200044d5000c08189030008000542d5007042000c0c0c03c070940d0201a000c03d050900150f428080301c440d00030080300c8100e171840c03c140030400c0000c3e0380500c190700c00b60300142c10070001070703202d8001c07a85580010b41c0c80c2d6010710b0b070500000b0b405140c2540c40c00307944160510203604002051003800b250751001c607820544c03060140d040c15950001e000c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 468046861 1250 468045611 468045631
    0x6090703150903030f051005041a090109090f08030708060f0423070302040816090506030c0307030b040206040b1b0d110c040b0f040501060804060501150c140715020d03061508 77
    0x21921041c0b5100707521420f445c45148009001e41d05081035003500000c0c01c1d0141c0740c825031811031203e1036442e07400d02c44a10408051f010901760380c64105440010003030964103070f82d2104824108800940d004008600c0b4020613115024030741015424004101200c00205024a01c0c2c1020200f484291169000d19410241814240b55848000c114064091540121000c7c82040300c070804040e111b02041003500c103012410007403517482008146d560b03001e02404a400d900160410b101040a500c03420368400d00281080b450113698a24a100c07a900a07400c0000240b841c0070401a150001d024244a20460b80f4040c600080c07013101064403a0124941e4030b110b03e9441001800e1130302c9a0900340c18008006108210969481c0d10140003008103d400710f4240e40303444004030b000c0c05219912a07024200b0b03680c046d401002903495090550301d00c40c400103948211103000802d4011046d11185200b0a5406070858041c0e401d0040d00340d0348980c11500c0000489030b000204d2961007040a540b01a21107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 468048111 1250 468046861 468046871
    0xe0a080f0a02010b030d05120a06030b0f07260402010e041e0e0c04090309170303040305095a10181806150203090f12070e0a0e0609070315 61
    0x71a0990040460107955505401140c05803022207400c0b038041e1122a03c10f0184806d240e441c0c0300304608850303450000426003404000030174481781150200c9540141107041c01c81056030302d9000c0d002400070100f0090000080c0408210465a2200003207081000503036040c405000440c060250812542400c51540b540c2c50000020341d4008110920807914040e0041001008c40d040003002c05146009822030552950001c40140d440001240e00c202d03090750f01e050030017826408000b0b0388582c402080c4c60f00c0506841201c0c40b540007030001c0d0080030502d641c5c210300c84031308050160300580c40070030311100390340038103503c121619a0903017050410000c0c50200301d0034050246111280d61140c0141c0c103445480340b8444014400c40c2d2011041d2840c624400180c2400c0303580c00c9030380e07120300190705800c800003101c0441c9500b03004100e41804040481075904194903130081c41c1c0c009804403030f00752041b61100070f5822440c2042c07003482d4001c00160040c001c0716085454024500c00b000c41c0140440d030b030300e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 468049361 1250 468048111 468048127
    0x6010801091a0a26030a020703020d0c080f1b01020102041a090a0e010605070213020f07031101020f070f021002061e090c04050a020d0c050301051305130803040302100e0a080f 77
    0x840501c41042002480380d456142c440f070030301d05003a40c60400076480a41d00c60181000d42c80005c260381401c03086a005111441c210390910003c20342218046604402044021038204828000c041903a08114002c000303807411003540254000d51400680d040d648100418000b804604100711186844681035958072110040132902c24012684580d0111170814004159281d000e0000c183c4a4003c0752803048161403a03108074228070030b01401042040c0100011400240542d50a0440410042c00103003800840c200407072003a0700540c0d0888021508100920071440d011041d07102840b0b072403004240310f1500f074902c0390500c0550f050b01c0301030707220541c000b58a043c41044000c00b0054060820300c441c0c10f06031140c0010b9049800c10000013410b00c044c0c41c1c010352059090300c0c12600001e0440c0d00445203090b0710342c014400901400441d03e521802d180104030070b18011030081e4406c4d40200038212998803d4002ca54822000c000503410000142010450b000c094130118020082c4080e070303410b40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 468050611 1250 468049361 468049391
    0x60405030a0b19090c08070501090b090d23030406080f01050102031b0f0a1109091612080d060b030103120801060c03080601111f0b0303030103020a120201051b0a0c05090601080109 79
    0x9401e0307003082c01c0c3e07050886540400c41071103280d5040b0758022040301c05690310b030070064550b0b440a02451508541c240160f0101c1e14080e010f244d9254050165280608141510103d003581c0c200310300fa0b00c130b41c400241048410307072180d0400e41c0012865801c1601c1c1d418040000d40703174032810352815441c8002c40c0603182610424040500040d400d141210040501460240700c000a42c510141c450500d40c00055612032021401034240b05140c407070364071041d04180140c2d0321948881c109603281031080c4800070180b0303034501c5a0000341c0400c3c40d4841c0c40358918601140d802e0000800413040000c003000400c031240d0481110314006900d42803001c07141d0342c0d000049500021080d0400e806d4402c082c0071a1400c0d1100410845070200d61601740582c0401c1404d0560300c0c8003e110007900203240b0f15003001600d84225036260304034070525080d46014001e011184082d54408034294094109071290310400401204280c000c11003981c0308a901c3c58070703c00207042484144610119552074000c85861015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 468051861 1250 468050611 468050641
    0x307030803061504091b03090b071b080f070c08070806060f040e1e0c032b110601170d090e0411030106080a05060103060501050d08040b0a02010f060e1005060405030a0b 74
    0xd0f41000d1607181ca0381da00004000c2c00404220782034500b01c6150340046d061080c001c01241a8006580408030f0f280d4040489800c0d601191044c020841d80c111000050300070710090466201c4044600d44641c40c605105a102e04990300004150344000c1007000b017210b001c41e0903580000c0441c0e02c0340704211100f0101e8050801c2c51541119405444035040034048a9101480321180d61400c1f2243ca5410000f0303d07603141300780f81c401c4119400c2d040181e07056851120b6041c00000c0e10b481c02c026916201c01ca918601030081e002100b0704c2070920310780d81040f04c2c00c018054522486241242c41107240c64580c140d0404054800b40c050b1104480007485901c2c2508008014202c0300220707030601c400d81c18170944540c000c0c001106d13064145400003c492400800303c002194000f51461704c0e091805203040c3c3c0d5640310704100001d554032240751100c0c10803240f040400070148800c40301152715040300140c4480d84940c020b144180c1080c40140f0451301c0002d600c03031503144e001c250035209448015200d12051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 468053111 1250 468051861 468051889
    0x6050304031205010306140901061802030405030408010903020d121404020d0230060603070302150706061a040806060103060803090f01020307080d0c1d060d11070c0b091c02030703080306 82
    0xb904100001080203484d6200d54040d44019803400340356250400030501303940c403030300c90824490405503c80400030010760066400600c5003003242c0c540f17a5a84501400d45101110690160b04080c40400d400e5403c0f050903040321030079580030045000f222404000041c0082c0c8060b0094401002203000c5484003101c201581c00c04170502c0c0700041c0c080e000303101507803d05031000200d0301a98003c00e2103400c0010b41d12040d46d6004001030000600c115907880280c029240c1580d0450301c461000508804030b218440906600004960f511410301030b415140404c00340c5001c0c1010300d80f010400c84000080152480101c0403500c12043d0100300300104d2460141080107041a0b10000307910010700540e6018002d160019111088a01d0084a101c00d1410241c401c461700124108002880201168402900311450048079801c1c440c6a446e1694071407016040016907010000d8030880074504410300340c10700000c8030015014111113a0109844aa03584030003001c0720004808180940e50b8400c90b0705000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 468054361 1250 468053111 468053147
    0x50d030c0206072114030609040b06030715080a240e0c0c031804060e07080f0408120a050402040b0d0203030711010203190504030209070e0f0d291815010605030403 72
    0x10242c1512282c04503c404c0404244940120140d903621130301607920941e00188203000c80d0340c413600c5500b40701c90000c0007a13505019880f40458404c0082c0400c08000d01d15644050643c5001007111040742c0b03900c40e103014100d6405104100d4151a20713501e4040e40c040c161051030310b1b1540d44100000303000c0c42030121010700000c00c0710404075040050070425888110340c01d210184c1e03103440036004204281d0301100080c20007000140000340e500304880d0014410410700307280ca80c92405900341d001094503182016512681400f0070342c40d20b800360b1002514205e868a02c920b40543c00a540da10a0940041500ba818425004a6802801620510743c101491030b0445040400001e05a03030280c00201d21412241001c50910b903c10402292045030140c10310344041c0f4000100461413010840c129074550490300c46901409800780700081d000488042a0001e081a200412480c41c8101d4021220f9220803803d202d81a81c50301d0b07581c1140e25900780103603292114281110b1140c02c84212803a2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 468055611 1250 468054361 468054383
    0x180806060f30010c0306061b0f0209041a0c0a0509010810030f210c03050d1e021b010e120a083402010c0f050d020a0e122401050d030c020607 62
    0x303140185202d600e030b4003041d0000c0040014003101903007110b1190003044c0020720684a10882981000740c1d0b0312015010300130040c40c00034292300181c41e0600849040391201c144401c1d25071242140c5110940182440c1c601c1400c20790590002003c40c040c0103011810801d014000c148410302888855000d540c0140703000008450500304a02403002441c0e11020042c807040d400d1003414851a4040309903641543e40d035240800341c030660009498800410484400d81030310100304026503100415011402d0840b40310550045160385007103070001c502c0c0c10707415000114910440d0b01808200c0750b000119091665030354440891000460f000f06c00e28550260b510381149800740e41050819450610641c0240004c00d2201c000320f9004451111810100e00705021920800b012900176240907807a070b15061020041d440d000401a141c100110983c68002c07200c18005030300348181503e54980d2480700b24005501d0100810800900402c0240400c4155140c01c02150744110032104010381141101034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 468056861 1250 468055611 468055669
    0x9010c080c0a080316090e0f0a0b04240b040e040f0804121b151d010c020a0b040303141306052a0d11150c0c0106080304080d180806060f 60
    0x103d60300907265206a00c2c0080c00d5410640c2c440d01108084d0383e010568986282c0b1410040344200c0005001d92207070940300c0c803044500707840e00e104003c080218108200c44c40204204000c80403983c41d0051400b1003030820050104100280313526401c194002e0791740d0705048140c10030701601c0c0030fa500103400e407050344075409084c400c0f04860355240486490141440640e5a140038040143e003103040320100d01442c02c91100b400410506001c1d0302418140041d1590f21540059a5132802da040b046140c100442c0034410705600c815451001d404100b0001e00d011610301c1ca40018685a1080404001700081d500800d502c60400307051824028201d40d9a0744074515100301d07101c100300407210740080ca01c003100c0020040000b031003640c240300340301404206444441d0f8550307207580400490491036480c0d400000301c84070100b0007003000b4081c0700060310032010011001800e100031a540b102c412101d00c0c2c0c1c00e00840101241c12a00150111485604282002c010030308000e5100b0304800c5800102c49026 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 468058111 1250 468056861 468056873
    0x506070605150406061b0203070503070b040f140d0b060a0506030f0a0506031f0e07050d0c090b040c05030a150f06020a02130203070801060f02100515100e0609010c080c0a 75
    0x5800303880d0b50040d038101040c0100038401142e69902c00d0200040c0444d032001b804a04004403c500b1500141c2603032a1291600007107458054140e1140500003000903003000040c0e44281100050b0100804581d1040f40301c170005010078090319005001c2808001c04208155540c01d641c8005105c080c208a440f458403520503982600304454005540d400c000c0014450714000c81c40344001d489622030070b00c2d08601c10604200402541c0300c45451407150500102d201c2e5280c080c003208892181104502050801000b80b0544080202d040e0041c6e00340160398500700d4100064941c800101403001902e810305040b004041500c43e40000340081d1862000705119501203001001e0500a4070f05000005031080c0b450708a01c0300300c8000300010701081c0148241e511807420001883d03858412070f81841d462051140840d1010340d60300c7d001800703551041d522410410f0410160000c94204021850002c5d0081140361082c0e502c001d04001c2110a80002c014103102501c14643c400c2c02100c200c810645000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 468059361 1250 468058111 468058121
    0x12030a0e0115080606310638070309030335011d010b030606070201020a12030b0a091406191d0402190b04060810080a050618030423030705060706 64
    0x2925450188000040340c1c6d08110b40b0800071142e82056805e1480c6644050f01d410407000b01e4030f42102c64950b080051444d040030f255030b028101c0b903060307012103410441e0389041d030b0b803c40c540200402d0418024000442e400210f16400c81e0b805080c407480042c0f4400182e14040b0044016014548003060b4070321390400644e500d00d0680d25031001d24410480360f03001d0304880810910440180b00d50420000d41107003800340207001c4040c418012503142d44100ea0f1040d003c0c0f0018000b010000c0d0f540c2d28085607a20b8150701c40001001100c404214920700b42455440c2010024005805407035103204203441819030001d00c0c4010300440d07290000e100700030050907040602c2545c05912880192142b1034590300c101160104480c0d00c1007140b480c1c14a05041900c086400410150fa0340c1910b40f40080e00c908184150910584600003400b42c0d460113031000203042000c80c92142440e401880103100d0310702e0000d2200c584620010f0050601004180020320700350b21604640e8204002140c9001001021707042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 468060611 1250 468059361 468059369
    0x915042d09030f0e0a09020f0f180102010b0609010f0c05030f072418120c08121902131e08010c08041101020a020114070c0b03010b070203010b0d0512030a0e0115 71
    0x446030102d84202003111000500c00c4d4003a40128000d000300081c002c1c03980200b100a4501d0581400c000600740180025044081e68010079481152a5800e03581c2c280700d1020380200444140e401c00500c0c1000030004691940307050140002014070205010042042d180040c100c022244d9441c500351400814128681d0800c5106160312a40c0d60b64034041401400c01c4032084c1e4203980340c034541c2500d40c43d20042c40c031300c2c07258184090301c825139000c2282c841c0105070005200c00103800505000078042d0304003901c01c400300c4a041c0306120240403040000900c40c11580c0110485000c105101c1604108000c1503104034450740c42c0c09440ca100e0358000b00441c1c071645c081c840790303907402d80d10307000698940d403403800300a000035003541569280c0220f44d4040c051079030141021600d182e8554000d100603a02c01c2e08401c1d013452022520200f10b140034059241094429140250340c40159a5569900e58800103403e130f141a0200004800c2040350380f00c0f851b508050300003031103001c0c2c5900604441d0403c40c09 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 468061861 1250 468060611 468060617
    0xf0a0f0b041109040b0a0806040b070909090b190b1302070302010b0307060206010608011205030a1209050105070203030604061a0702090403020f06010f0e010602030913020a210e07050915042d0903 86
    0x205c142c062518684000880700e44002070182c030303070300c594440c0c2c041307c0000d00c1c0509002d926130010032030060b50300c81d440380380303100b50521030303003400d000d04500b10b040740100ca100107241c10090041d01d40d0f1605030f03001107116450880943c440c5210b103400e9025004800c0c0854051041200c0090155030002d4124120303802a01c529407180d03203c0c1008500d100258001a00540c020484a03850078030400c2480c001030700d20080000c00c1807845e43c50a09503001510700302d005034008024010146041d00c40c03980201414014101120520b203042081c50141c810040e214100030780003e81818000e101c0c011480c1024000d0700c3d01c079a191030850160b02590b00601000541c1c54001295540c00081100e000311b20060150044160151882000c0d602240031601042903c4045c0d1340347c0c400e002d80a40805418400200d290803900c00850700c2d201a030361105100710009800d001c007070b0141000000800006440102c3e2414020042e11a405010580184034002400ea03403c0c000c82168091460180b00b41e07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 468063111 1250 468061861 468061871
    0xf05040c03111005071118041a070c0309030821010e0405010f06081e0f0f010e1002070b01060c020315010e060102071e05060d1d030d060e0f0a0f0b04110904 69
    0x20b01803000e92200300e07014101080d81000410086211942c06c442851402086091444c130312540302003032104242d80440d414a448074103544201c0c1c030b0004040c3d001213145880901e1201c613131402071038580389220280101000149281d601410520400c9945003446620440f550f950701020007014011034058503036528018074070241000a00901d400c9a8a441c000c220040c035000301800002c680e102810035610400350003035070400c030074014156010000e10000861410310311a403420060585807001486204007d550001102c030301c40b29040d1515841d0182c1d000c105031001c286800c06209801c04141c00007000001e03120b10380c8500910542c42a4259207540c0c0c0c0c1e89240c1d5180030800f40c00c0c00c12a03205890140300d6130402030060b02000c511a070f030205645000041c1852041921507c4042c4c07070b0800104c15440311102e005100040c114030b0b050409030b00d0980810f1101000142c0b405a05607216030701190b5481040d033062041060082c42008545007000c058900d540c041d400c083d010ba4200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 468064361 1250 468063111 468063143
    0xd050d140702060912010e060720010606090b03070201061e06031415010509030a1a040516050f010e0d020a09050a0608120711030a050f0a11031605040509010f05040c03 74
    0xc80140c411080c1c0c00f4045509045260040222804440040c40381966940761402e03450881000800c1c040c541d107484182c01300d03010400003000710101c621507120036030500604211076070b4030a905e00111200140c2c5d030340d1030f80c40386ca404a002d08200d900040f000c495004010a0a5911300c1681044039841d44040000c0340000b41400380340135045403002e0401d54407c80e0785407107500500040c502200014242c48049206a80307995041800e5442415104182003c00040160410074070000720103400560b40300d6464580050080d0b4a013480c80c60402c892400301d942c2980741d070307403002c03400c10703030050000a2844d11001c020005040c01c89500405a00349200003900d100003007030065044c480c21840b14508415500c07401241c09a00c0170709a01171003a050000c0c003244082c8810480d0b400c9200140600102504068000d004201c0700148640c000340f8034921102003400b40003080b940141d402080940d100082d481c01001c40e0700c1075500d1141000108000c01c01c0000004040d648145120382d00d8190f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 468065611 1250 468064361 468064397
    0x30f1e100611150115030f091214190507032a020a0b070b041b030803010806070e22050403020c1309020406090510140604090c030b0f12100203060f0d050d 68
    0x30200c14482000303c4030014000024940504901c080c03403418007040c2e024900f50003000300c1c1c0c800f02d01590310380d00c0303403030f01c0800558810861018001c1d20f460a03406e204005c0c109802c0600044012000c0c4040015140f042500070002079200d030f090603045007801101d003465108084000d4130224442ca14011012a55400b41426030f41d90903000703840c0d40d0543d41c66550350296580c145031000e030840038a450000014080100460203010070701c001c1c0010782003086000d0081d2803c030320064403401d00b2041d081004100c0c101c544400e00050346001c2007a80312801c050341070202280090360480c181e002d9464218005030030040007184255400c003c61961580180112442558412814191680c041003004001240e10343c3c026002068146410b0395600f074181201d0010980e100031a44500c05100f40f46882e020850300e004040d42c8203407201c3e000c440080d482c0e0a40000702d000d45507000c400304025450340c0c42c01030507150029160004058241c10f00c60368440b0312052101c00a607400c1540544014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 468066861 1250 468065611 468065623
    0x106020705060d0612051e010b060f0a17070c1a01080a0312020d050411041a090a18020d0c0f0b04031a070c0204051906050301090503030f1e100611 65
    0x65024010850074081001601d074071940340300c01c0d0651541c20103d81c51341c2500d1007441c9644250010034281c00303085c0261411000c518003000b2640d14001503906903480c0c40c000ca40582c1c0d1910451030b41c039113080780180c49480b04030822001a0f151003040000464101841da1071003405220b42c403000c04403814a0f0740da201002d0166285940001419400007800f4442c0c01c251081d00310000360902c0d9261540c0c0c01103900454003030321902d904948280160802d442885038003080c1c000c0514545a000012540c900009000307844101c0d9600414100c3c20456034655240e2907004000e42d825001d20708000c8038843d2103004040850740882c01c0042c08002240071601280e40c840d036540143c0700005403200481d20010201401c1c030001c4681c1000680e25441000c0c420301c0034082c01c0442130328091b803002c11118550404c500070381c5844a11800b183c0f0000989900c8034211004810319502c21204019070404070760342c1e0b006004078805121900703950041d0300e03054409560b10002d01d9840c25803a0343d0380710 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 468068111 1250 468066861 468066869
    0x50a050309040e030c0d080c0f0c07030611030f010302121624210218120703030801290c0a05060901050a050606041206050703060b0d09120c051903120603061a01050301 74
    0x180c4800c1d10000458003404646608c50101564a41005040b00400740180d00421002d511a0842d040a20400016209a055098504407040d0843c604022100303007802040c000030384105580081c40b294100100300c11003582d1510ba0003101020707507800c9000c5003901448800440d9030b250311003d081c440e1040c494020341c2044048070041c8054007100741c2c0002d61114214813000c0c00049080da80540300e11009011101840380140714141c0b940c14000c19070401030304001c5540c080e1031611440e00c0d008104035000e110761900440c0c0d80d04e1104030900d29203028440002d0040c00b901c01000114a01076216503c9540c20380d809000940d143c00400000303200b6030040c8510702042440c070001113a416404603a01c04003138200051030a850300a45000c039006600300240040d00d8007808010013681090380f850020481c1440c64642c402c0c2d950f03442c3c40b0000b101e660701101c4084004442494404c1c00e070000044c01d141d10030001c1584909006000d4851a040840486030a0751030b14500c0d44104c00b00c1c2d04035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 468069361 1250 468068111 468068113
    0x60f0e0a0b04030e0907080603070f0609050105130306090c0e060114180102070305060a2f0910020a0b0a0207120c080301060c170c0f0d031b0c030c050a050309040e030c 74
    0x41032090703079103480981c1c01800a90070020314215a01541d180c0d02d107801d000e1001030301c9461040c9490340070145014103581008072030346805501040541d41041841e001d5603000d0800f561162003d281003d4500d10641c006801d460030f184401c070500c0054541c0c0010b42d041d242c0d40c5110740c4e40d0207006461010528044c554081c004110000303026030700081150346a04144142c0c0e400c5541d903211149024000c0d40c004450030783e644a5180704500e080311905502005002907002c04c0103242c00000d40e03000c0d41510b00d020301c0703c01c403100d48018424082e00c0300b015445040385c4d142d8180001480d0003500a8001101c40f1b462880412645038024203084901030341c0032034014910381c28403004a0b40100300500448120420200f0403004900c0d10002d040e9964141d4000d0051100304802c3c02c0c50035a80601c100185031030080c102000504094020901508508104552080c28136080718403102c41c960280c0359000e014080803c0000100042c102070400312020f000140d04127203000e40340d210320f80f59681a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 468070611 1250 468069361 468069373
    0x90d0305010b0409020304330b0d02060405090907090204150f02150103080a020f0a12080f040b040813080d0c02090a11030f0403020c0a060822120c170c0307060f0e 72
    0x10000d034005503031040c85606424040350f00035090090000180c20b40b22080840440040c41009a278402c038440078104071911040a01c143d000305516102d20300400703019840c00c2c00003410720b80b010040c0300002c1c00843c0e8111341e100d6850880f05000c9261112101c0015a03501c0c0300300e086407000481200c000041400103286928690f540c03000d5608c080341c48010343c0107c2581420840b418020360414030b001d030030005002e030111040107200c4803008007000d600d40203590034440801e01c400c00b07903940300c0d038000e442a80d543c80c240300070400b420443d0b208071032612030b892541741c1d1154802d030a294032620a80704414503850340884030003074504503c2d40e50003402c0103000203504140996202c0b41c0140c0680151070302000b911002c10084001a00002c000c074806c0c10601001d00042c140e20748038034103046170203c102152a60f03005002c07451303071031048108022201407070148114400844000301c0c3c50602e140e40c80628901d125202d80151900b07036400740c031342620003134140b02c42e001c0d90082c1042e10001e0030b1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 468071861 1250 468070611 468070619
    0x309080114091c12061202030d03060e0408070516090c0e0103050c07110604050901030b04150c0f0315080607030f18020108070c0305160c0306360f05100203090d0305010b04 76
    0x6010f080191080402c02c12103c00d110034281031040c4000380038031100311080030704a40107141c9406400c1e102d9504051814100300b000105070000b1940203980b003a0916590790460034124508040d0007008009401c480100003204111076014004007150340c8c030341c0f241e0b400b803000055048460444200e102d511003044071382c2c0002d0014143c0f400300c0c0d0005000030f0510751140007241c1421000d800442e80300700b2510500042c070602c54050418030051401c184840e405098004204424a03454801810b80300d0303c29003180d038982c0e444940070380201005c0300c42a250403c0c2c001c000e000f800c0121004146080c500c411070100c0c0b00c0b802040341340c041e16017002584900c9022154226040001e6042180138032407405040a100761040c1154000c1c0182c0c11910b0440c24100200ca07100c50150745000b20a40139a940e4400c00c0448a440c2d2039611603c40581202d420b15001c1c2d01c1e04d4031001415802600c020341071041459002e1402900c1703a00c1203a01c80b5042c0c4a00f901111000e0241c42010001480100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 468073111 1250 468071861 468071893
    0x60a05210a060e06092803030e0a0305090411040533040f0509060f092406071a0609090c0d0206070501020d0515030328051204030908011409 62
    0x80361a05a0400614550034216036a82401000034046411640b81e0401201c000020044681c101c04288003400011020b10854101c02100e5190034020450078410b02d01414000d900410b90100c030841684c00900d081e01d401480c5174002c1072120b22540c0707004100060054035601392002e03100060082000e0010b4041d1003079030314031140d07941d010048080728403e00c01000b1b880500001c181100d042500c0508150801000da080207204a000d2000c0004aa0b82c999984c400a904010720082d0f99181102d6001d08036690243c0c078040ca40c2081f000110b000400c8003005540721010040f0440044e2900c5900810603c51410b4800103220b60081440ca104c500c5d109000021407480146002c0c60401a9130343c1c9401d90704092107207004a42c3e1807041001d000c190000b60b03400c2d102c044024600c0c02c69041103420082d602c400015207003040070504800400d004038104d80f0380600702c2e0820040c031310381803400500d038075094007403828036508000c0d81e443c1030003182c40018000c800c000058030745001e58041103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 468074361 1250 468073111 468073129
    0x5070902070b0c0c071205030310120302031603180b0306090f0f1f03020a14010809030a050703030b0a09090b012102100c05011d01061a03070f080a020f040e0703050f060a05 76
    0x4c0c003a03600840c04005100f1404080b0010820b129034061901c030f2601507010244102e8a074845100030801c00220780000ba0b01004517001c40c0c80441750440500024201100c8006603620030702c031b03400d41010300450b240c0103510103035114003003c48005040d075644150340300100005840c12030301e5418041c0402d252070344c001c00955902440340d0b42c19005941e20780001780540079070350180d4840c00880760120001d50780110b1695000040340021803401d45015001840c5e0311a049024080580d1451480d1040e40e800c0c058100411034140180000c9800c1e050001d40e24100380708a9196074400d60b9078030741d100c2040c0c546800d100c0c0c009000000030700b413110080d10b045043c0e81c0c003160b1342d5680d1008902440e030642c90909122544a0000446501700100e0054451030703020624410322050040100050340184072a03044c4a562030301142c43d4940c920560064010001800064480072801044952401651f18480d0314160b409105507200c842c00780210040c20744040c0d03080651240c3c184880e040007461 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 468075611 1250 468074361 468074377
    0x410d03030f0203040f063c1121010f15030509030c062712041e0308040b0a03050f0402010e01080c0d05010b04050102070602030c07061b1e05070902070b0c 68
    0x8041140918407060768126442200e00303c904040040b1850300340400e41c49a003003049136050890340c610244280003c1141c940ca402444c20301403c03d103042041c5d00c2c90300001c6031485600001e035210542c03080c0b4401c086e410421151400704c000800000c00d81e007100c18200880c0d2000400c101c500044007030440281100914429184c40100303d000040c2c0403c11181e8481c2d4240e040010f2806054524808401500d1440000c90781c00042100d18010f400b2040340c2c2184c1e80d80503000d42d032404015400c4c1c3c82c444540c1c800741c0295004500018150861030003489a09187d60b02040310381d468503000e5840c4002944d000e070020300354002d02c1c20740354000d241254000c0301c0c0c0021a424a81d840a101083d98401d0b04071013011074001c01c040009580402c202d0014004500145003048440d0342d0b010342d64800780c0f1a641c2007000c0c840f0744603641103202404480b52600041822044400350340c401c001944900c400325034511a444002808000b1407081d23603002c5134402e1110005171220075200c00035411050b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 468076861 1250 468075611 468075617
    0x1e011b1d0418051e030a080f0601090315202d04080307060f0e15130812091605091603051f030f030801050103110a0c0606080304410d03 60
    0x82c00025510b00181103002c2c061148000b4101c1ca1100c0210340d0350200300200c44415a40705020b52224160064001ea0b40441e48602e8008039954040041301d04940315400648035446044070100c104036581c200c01e4180042c0382903000c51548a005c803502501c5001c280c130a0b0100600e40e502201d10090b541c5405010b1001074180c10b0544881c1c0c1c1c00d04541c0000d13411207145650b103401141c0d040a80c02a880900c40b068082c2c090b202680042d8210010000d03c1e039001c000c0c0c605a01e000300856001580d072050300c0b40082005071b24202c03406c02e64074071036061010705c0401340100004003490100043e46c400e40040651100c111403018007030b40546409020440c05650146511041e010115140030081d4061562003200b004036040103040b8500c180c018904140c103122400405c070101d001100c8107001a4070f46092404120b0421000511880e04071542a000c0010009800c3e0a030000ca882c401141d849604086101c64036041900300301800c10f800d21200842c007143c00352030213030b50845a040c0242 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 468078111 1250 468076861 468076871
    0xc0e090109080415080a0204050d0305030a020706090308010315050c0d0908160f03110105060a0302010c110406060e0a0801020903100b060708070308010e07020d12051003051e011b1d04 81
    0x1641d0b04036280c1103034120840144007001d02201c2c450340001681e40100c43c0000440c0307402d00b884003140080c00180c10140031300c00000041803544c41698111403106070081e004011800180ca00100035071428801034135075205411004884212030710906008012248850f0b180030303180c40d030050142c02001390945032002e0501180e4001c980040d000c00c00c192141035a100000302e00e00c0c02806481080400e440103a2511007041101d40700c1100d800705903034090a0407400301881c0d01c0c2506a0520310142c04d5089030400d0000a0800d40100d46c0c032580800c1103407032140598441c2052800c078003c0f1004154182c3c0110b1170245001d640358030845404402402c0386291003c151240c103225401108101c2c0080d03c480d00401194502801082e08402e1900c05421034141c44803004003403485080c00072014540c0d403404900030640485071680103680c01026284500000d1240d2002407500034442c440650a24004030000c450100741440d108040c0c1d11a200316107481940d42c3c00310070308981c5564115a440c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 468079361 1250 468078111 468078113
    0xf020c030609010501210c06030b0409050d031e09020306010506090303040f060203040320090a0b040b03070608150f01020d03020c0c09040602130e1009051b0a0206070e0d0c0e090109 80
    0x3070104034892500c8030000b180551402c07403851014000e0070360002c0701150044c038002c00210100d0500c801c5804510700802c80c2014540001c00421007503d00821610940300e6051001307030550000c2120f0900081d56440c442410303807901c81a03d80080e0000e5160700200b00500091038868040c01541c0350260459040c16103070718140e03802c0f0a464002c000580e001240800c1001030202040046c10b0b005904428485031480200e4011030313018040c2950a03444041070314503515a9030052548200040490b1019507403000d010340303024400d960440390800c440d01c0f12941428116000818000103a000b42648810713564128000c0d04004909002401403403403d107280d9507440800e0380581c0c00b580707005940d2006141c0c0c1c6a1400c00e20390140c090302c5010010031081d10750304603d110450b00300a03008211070b503443c594071000d10070641e460004400302065150340d0590004000d4030803529074584c2c2c0c12000080080110461620303800801040c00c0150078450704948003400f603040000c8000204e9401d044e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 468080611 1250 468079361 468079363
    0xf2105030d0e07030c1505090909010b04051017010c09260106030317090c030c0d080c03072108041104020c0a0209010e1f2607031a01090f050f06010f020c03 69
    0x4200c1281c1560b1243c42d040c024456402003190092104000c800c040c00403018019005024003101940700c1c645d0b103400035520800a4020020064004004216030714001800c614000d600d8000e01d5140d651140d403042c05d184051042e401c44102139120080007a00d8203680820403000c4042d0011a47c40c00240044900070901694001d1882a00c8100070204000022951300b100242100c3d91584841c159a4280d05c003c03030015412003042d01d00030001422400c01403201d10980e9290030513840001009030910400795541303c152030704000711807203400b0012011510728800380c3d40607080340d6440c007100440c1d00c2d1550080016881000c01c0d100c400d80c4540001d8281c6000b44c0c0140080d82c4540c04100404000e880c03403005001542541544241c1094558540200c3c2140425220140075412003880b00301000002e00031503210403410460005180b040980321000c2c41225032250610b100959840f400780900b510801d003c2c101042d840c0c2e07405004560800865017031500354081c2404034109510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 468081861 1250 468080611 468080621
    0x30207050c061c0f0209182a0c060a0905010b0a0e01090207020f0d03020c0102060703091505040309081c02121611040209040e01020c16030b1504020d0e160f2105030d 73
    0x3440580180c61b0007010041c0100700d60316804481c83c903407030716081005015602c01c0700c081c0780f101c80a8101d04030f100e16907085060b101d1040e01000c14800e1204011080109410001540380b00c4d200912910704031034140712100203540240901600030301b00510802e096940500101d0b8001860307006094008000704100500c251410b030016001500c004038596010070070580c0040c081e1a00700181c40c51074888000b048001c0b52070f2204039860b4004602410f2180ca0854060159241910103494800c00e20b00d55240d01220b00e9005809060714441550028505403194845c855080d03075a1711046540380b030126051903e115a01c140d0034000c09000d0740f144d100740d942d0740100b04001641c0b0180a05218034200c46041d00840d0000000400c0c00090b5544145a41207039501e180010b80c00703031318000100a40550f0790520030441c42c4c031402e05196140000d4080101d210042004845900d074a00510800440c1c00342c000d8070000302c030312140d41c1600c403007047c1003c5009509490030aa039800500e02655 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 468083111 1250 468081861 468081881
    0x1002092d0906060a020a060209040207050609060702010501080d0c11030f012f04080a02120f03030424052509030b010e04031202070308282a030207050c061c 69
    0x5405020440c21a0074008840d0703810850460300d080c201060100000c1d643c000e660341c010010346d000b140c000c01984964041d25809039010050350107510741b54200c3c2d0f50760300b000ca0301c504c015170030a0000540414086281c0201300c815070346010024405403a0382409100703e010558041c4642d508650680ca42880b508181085996500d0034164000101420700100415400c00c03804041001b08442c080000340303000800c1d81500c40101c0c2e614000700d8581020602c2d240303200c0c0c5010000c1008100b0280d02c1d461070689800401e0280300c008210504000c8070001c0ba0081502042d03524019079000c00c8945640f800f1b17295140c0b00b80c405072290380c1d82d2039920b400c2c0c0c0080c080300c428800340810160814105480c3c948401811800c04d032103901d0042c141c043c0503081221440c1c10041221050403070740c40000000d0854070082c000e034a40e015181c0d203619009100540701e41c0034003004070710407440790080791080c94000004010b4001d10a041001310fa10507030b4480d1200001d080c00302049840d5008119401c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 468084361 1250 468083111 468083179
    0x41a030612100b10140a08090f010603060906050a0b10050c01110c1c230a0c06180302010b0f012304050a06020f01061703120a1d0714040c02100209 65
    0xf1107546400d126185454030030b20760510100280200f0303c10782d5281980c61b588868585003115403104603199080c81c2111031419105c0d403d1038404003d00842ea04100401441400d08022036500c00c6162002c56a421030351591150300c40c07006100e220300c00c3c4090716498140a000003502d800030242c0b18001d511070070500416030000c0c00507200b40541001e40c0e001201c62820a10b1114600c04c6121041c0c98a4012201e1031400100c2c3c00308450303101d0901040401d41c455020004038803100c411124020310b42c01f0450041d0700b05100b50226080c491080f051451068444041c88001040c4400032450414024015004140000034070b030360313a11051100510490b000f40c944500c9055401d030035a10642c014040303441008003000108400007086540c80c5500490111a61710354000c2c24015154421000c40d0090900c941a4080d11001c500c040450384c0f584500c108800d694030500096030324058200c00540c11115002200507151f40080c07070502001000c0040241c6d61020460522071100380c0c101301d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 468085611 1250 468084361 468084371
    0x40c11010615210f050f150609030a0204090f050d0c050106080a030c0201030509100608032d04230901090c02011505060d180213050714041a03061210 66
    0x6446081c480c9102a04102d40700a08200495101a002400d000541c0381c00360805040f4440402030b0342d01020000390400c0c4240502e040400c06610401c0c2c082e940b0015003580011501561302e00307170049901d01003024028008882c01c640800c00200b904d05011795070b000500c158500010400c1c0012482c100042d04e82803200d0882d41002401c40d02e041d0808450356206824583c0400d41003600111284d45c24600400d00e0381d504800b00341403031101e02e021140b480c20304030049101d0a022002c1c2c0007100810384020541180030001c040b5403001c03a03d00c9801c91008000030f002c2c0305422405a1150484684002d1005d05d071440030039a981c0d402d070700403855680c0c1d80c14401082c660a020714501800001181684035041070005070b00c82c40303800c139441c107540d9541c80341d940400404441041c40d582c000708072004e14000c0d0340b005400f0345411140c00380040c5003080764240c40c2c805e5109843c20f8881001042521982181c00c04c65990310240c4119445542d8a01c02c295040d020000741c50103582c10440442e03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 468086861 1250 468085611 468085637
    0x204030b100807030503090907050c0708010b1215010b0705120c07060801061107060f02120c0606030c06040e0415020c030d06051306180b01030e030301151d0306070804020f040c 78
    0x1e040859a00614540e400000c0108040741c00003043d210180e07421580003a0030344904605944500c212070241d00a401100800108c1000640c01081d48107800d4801d140a1145080300710b840d80080365405014190410041c000d07003084901500ca0680b003881101e941c640402c140c00300d2600040201d00b699030000c2c00034081681d21403803a6004003401d040ca0201c0103003404146403141c030307a40a0340081005500340f54140700c0c401c01061400c50404803110740e0b0341c074645210989400b4102d5181c0d00a100b50404140282483c4040340c0494084002c15007181d15103940c5e54600400340c1310200105c60b001d002c1c1c0440400144001c1040d0300b45000001050f91510090151100500c0d0000c2c0b1042e2030900204075400c4102c1d2520b440102001001035280c0300500103a00500070641d206810344000700000c0341041014082c1c0c0010711050322030658102c1458811412540e100300d403160150001c00c00b0551140c010f110b101d03009840102400316024940300800c08070b880400d000000103040d46d240ca0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 468088111 1250 468086861 468086881
    0x302030d1707090f17190609201f090b040b1b0c03190204020417150106030b010c171219060b0f040506031306020a0221040f0513090510050403031506020c130f0204030b 74
    0x184100200101c2c18060302c0301e0022b18803214002c0c0341d8001180a5241c0b04866104407103002c05464035520f83c41c1c503152502c21601d45500189010000585641808c03003411900260400c111003000303005000400c2c00001a14220a20100490f0080e800b4800880c2c0000141c0741d90144e40340c40380040556440c4101c40160900c01030f03001031b060614095560a042c2d91000d00780803c580c2040800c940c00481c010280d11034841c6101000901103003005206070f0350140811403045071401c800c2031004503101c0c0c942d900c2601c114070301b50a480070104000c000034144075018680c0034044074840e1a030b00078640c442e44180c0e806100f4010041e000014681c118a9509000d1000070511480c5a42094140031f040c40455174140621407050703c81905089041200c0d411121645138820180d4200045540002e401340c002502c080303011a007011403030324005421165007800c40c0d00903030082c40c51400c3d040502c001c5007a270003071200f00c480c2c58000240c0c040c141400140020b40c401c13100c8111350f19140c548a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 468089361 1250 468088111 468088133
    0x1412030411031005071e12020d020301050108010b0301080a06051807090b030d090e060f13060e040b0901020304210507020a120b0f040b060103150302030d1707090f17190609 76
    0x783c0766451a08051003041130340f0000c0f00100760341c83e0150307021030054100141e80d281c80380807620740300c50300004000c05204410b03000745040312400e80710140c083c0d0f22983c1051550000f4001c81082d0b41c0607080c840c3c0071610700d070810340d0840c0e00d4800c070130003d00381c0c240d030300f4140f90458101a20701c41c5c8a040121040c20100071001c000c02180c94141c494038208074001c48010f1016203030703d21500030500040c08a0340c42d15101c0d440089040010032a032542d505080590103400c80d0207035400040390340000c100110600844e031013540e1044c02c4401d00601c5024404420b600e9204e0401000018420a40141c50301e0345480c0180500c000403298003840c9141003405001d0007000429008039800078080000c10502c12550081c0b02420b01160b002a1b41d80d00460300746030ba500295152140310134402600e40c00c610601464000300500000a40d40c0f614117130b0300c100076071050003a03a40300014200021480407509510403241a02a50341050548500c4c402c030300904002a01c000d65107880c120100b107820041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 468090611 1250 468089361 468089383
    0x3101403010c020304050415050d0b010f0e090604020904140a050601090501050a05011d04020f041d0a0218090406060902130602100504020a06110c0303040b07030e030118141203041103 81
    0xa110001c82c00d00e00035164000e6100303440c01292103c91482e0f0f07480d442101100034000207011003c412a8a00300403005107428400d190b248600d03148049903403070b1009200e40c41118140010221034844c0d500740b043c0c14000410a40c2c0c00c0c843c140d1f01c5494400184032030f04500b40520f00a0440e541801d480304126503069026604c10808640c04100f2640c01440114152150fa500601081090004100607110b0000402c000c5c000010b0003003400440380c1c4000c104402c25440007815941e400951000320310900e450b581c1c50901402e01094145030040c0000c0c0d0262107080003040042c1e80300c6c41201030380c000407454a00340240550900c0302650401181c1200c1680e88010b01c9681003a40201d030a0350858000c4004011008418405550741009040102500942100d56031681c504840c2c94941105104800040340c21240f904107160500030201c0c01d506900135861441c2266030744003102040d0112000003400350000030710074200250007441c0b19130300a03c04488040ad484003054200500440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 468091861 1250 468090611 468090613
    0x19030605010311032202130c2604031b020406060306091d0606060c0102070c080c01020d140301050904060e1f060f0b1218011b171b091306031a130b0c1e03101403 71
    0x2703080d400e903e2030513070050b41007501414120b410076000f107040f1031107500284000e5046070501c1c4000402c41e030305600c010b04540d1180020401d0180d02136928640900b42c901c09040f41c4e00c458040f8040e480e2004c000e064024035000010728001040d941d80e1003020169210700400d0300026200f180c20f50701400b500300200c5691402103000ca000351030040d418001805240d0284079030383e00060400140e5803011120040307038030884c0e12001e04210f8040c0c2c02411a800c40301c0490030b1880c0054140040d40b41078003901d045070050f505140d02c1e05c03102250000e005200d0204102500d04171302007000c0c284100c1440500401c0000030600001c034000d0450b40001810010000d000e074208544040b00402d0300076040340515050b0b07941c40e6880c0014804c0311a0354a0308454603c4d02800208001411040000340000001407d41d66503d41c0c00b0348503032817070001014102802c007400140c24501480010140740001180030300c01c02c403840354a6070316a041101c4200e020920002d062103880452808082040c008030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 468093111 1250 468091861 468091907
    0xa1410050a021b0a080615030705040b010e09100e15090c0a0e0907020f15181f020c031b0a03020714010905040f020d0219030605010311032202130c 65
    0x140003d40d02c2c060122107804034000b492880a041d91140800c2000349000c10803940c15040c860505180c0c404c546171854801e2085040016484c1000e0081084100c0141c5445461000260a01940d0314004110302d940100f01c10021440c062660f4105008400c014041d01c101d0010105004400d0750240a00c031030881c050000003031540e40150501002082a100035580b625240c809034034003180c0b031405803c94020342850351000000380c0b624501c140e900c0c80002c440f5160035000b1903101c010b4a910300311001503c05250311540c0c484c1d0000c2c4800c9400c0c2080304c3c50403111074107200c00803084114402940c1c01c0740e2a07010506904100c458003400507182c161010340740000c00070740380000501c82c003030150381c54000d54031000000c1c1d8182c44c003001041c1000d55842103101e030030907a03c120000607040407a24028004c24030303501c207105884004100540f0302d455911000d400700b1402d903046000d0982900e40018040060322550055404000c6141d0041800075071000b000d070031b6072809620b2001d410400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 468094361 1250 468093111 468093127
    0x120601030203010e0121050d020a0c05100504150c0503040b12090607021c05130b130e1009090503071205030a0b09060915011403100f050301090f060203060d020a141005 74
    0x20940351411119410740c038104007a41201c21b10a40c5040b00700141c95402610001c0d140c45d41c02140c581c1440340719148496a8917190701c01c210002012404013000070304140014850700450f40c05040120314607080401c1051980d13500c491559100303402103802c0000c003180c0746261504003180590845040d0300a03000619001c070000b0340e10031904142c0424a48000182d1000d20b001d207089550b035000080c1015031140d00d8149003012030348501c55906131800b44d041b000640d1a210a262401440c00301d42c0301d0315a80c5001940c0e40500000001501c050008001640020712080c44050701c08009458a94403403500750782c5501207030080b408490050804904001d10307582d1703003c041340d4058040c18840071054114401260550080034009601440000c107014031205c1c1d500309801143d1541074443d001c20f866000b4542601c1c0c81120003030a000032096002e0008040760069a440340026103440d0006010b5000164503110903407180c10002c50b5403060102c2070404020069850f001c609040f4079002e14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 468095611 1250 468094361 468094379
    0xb03120a052503080703020328020a0e0109031208040c26070f0501090b13362d020d060b0408010b0109030314090a0b0d05060307140a03031b02100512060103020301 72
    0x20903403006c155000001a946613100e0503c00d00b207032080700030754551618160b1942d0081d404079141e040441c2d0040d80305101c56204040c050252907000fa4088034405608001352103507000035201f124546821400030504920002c1022405001116020020b0b6180070f00681403c9581d00007400d04851060305110340e91704420341d0307402c56152099490350744801105200c01d541c0f56410002d644030422a2203800762244006a8030403005c000c40800d9003541c0304801d0411642d290b100c18621801c01055000c403100907002e1b10301341c90510303d4050b01e04050380b0101c1c4212500c58200f1400700390701150520880b0780034031400000010070308006080a04540b40503001030300302c01ca811103c90300001c000c0c480d034444861160040540180d101c0c2c40c0c103044003101004e480121641c42c081d205024000801e40410401c0105100c40a8401e113002070650300c1c101e40c0f03802c43c0c14421410107072130303a0700d0350040c2c036070b1600444680740d565681c0d030321000701404001d803108001d8000381c1014018801808540d517 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 468096861 1250 468095611 468095627
    0x2032404061508130204052703030f07050a03271712060d2109081005010506090d0501150617090303221e0c0f050306190b03120a052503 60
    0x40c60401c180691344100f680c20801e6900c0030000e4100d03061800340236600741e162500c5c050380b207100d0b0288181c0710340d1003d4065032800120b820300440001e0101207400140560000c0015035034600d00403e02e080600c03240c04181d515140d04003c860040c0d5804000d0044040c0313070300982403140d000c503440c100d0911185981088007034101407040c000445142c04002c01c00200150041c1390b18501c40300c5c07100b6241d000d407509003103101d104001d02514255000d00c1d07041d4842c03d41680c40c010b084900300b001c00d90601034000c584010450b9590f5803029a400e10594055100c00103104c950798540061804420300b041255024203060790030ba100380b050013410b03042d071600031182e01050f40420245081c07604090795902002d0188290722241c2e8a03d000900c03034220004410b45011261444400381d81d0000c0c1599120b04442d440c407101c0a50b0001412484c80e47c00030892808014110f507404103030204c0f4139005038404002e1001151001a400062802603403a03d0010710180030142d40802c0c0c191000380c2040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 468098111 1250 468096861 468096899
    0x3090d0504050d12180e15012303060d0c030b0603010c020f120a0909180501050114151b031306031b0c061104090c030609051b0a030506130203240406 66
    0x101d5900c0c00d00c0e4000e05c00e840440d08044050300c0020002d80e04e101b42d080040050365120041c084848001c480ca500803c000c00400b5005414004241500a040c0c0d0890300058005030340f0044226400b4041043c0c4080b1034040c5000c1c0d89843e4070f90400500305400c660741030700d2071402d6411803407105c0104040421a15100d40035061420f41c1d4026100d02101c11070001e8003c121038500c1c01c10743c0a0407051407030314105500e01c14002082180d0b02c0b0140e24121001b0f000a143d807000a807110701070b5060348140680324000395070106004061400e03100d44c0c15038224088410150001c5901000680c1d40f6000e0301e2800048000c8446100328a110300410b401210300d0003900c1244c0380c1c54003050305084402114001c083c008000c00c80580000001000750030244a13070b00486040c40c0210b610303c0071301c80d10400510040f84100b807805031214020350161200400c520351280350203140044c0903c01c6d0008500c030325401490072003800085e2010b031440b0031414000300e01443c5407041c14000000c00d407140d12844 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 468099361 1250 468098111 468098123
    0xc030414041b12060314100510081b0a0503072405070f1412030702030705060115050a0f02010216060902210607031e0f14130b0a0504020103091703090d0504050d 71
    0x120810850f00c40107012594001410100211a01154000007050b0080c3e01d001c5048144110380301c4d8680720b14100000c3c0180d0445403c40d80040072102c2d8040028040c4840251103280341c1c0c4d42d200c002a05040da99440815410840c29801c00300b6005a40c03081000c50315424a94102000d503111490700700807214000f03080038820b040100c0010010486800b074003010b030b403116503207140286009450750001441180c030b501c124000440e0155500180701c00c11507a40d80c074141403e24075903044030300400380c2c5010f40070765508001580b411a6020340007254039004440101d1000744910510101c000d42503030034100c4a01401c0103a801040114259402100c14034004c2500004c01c1c44003202c0441101e4074800c110301c0d00321440442c14454100c0b151420011030204003a90b18414440038100b00c00710010690920705002a0341e40000e94810340d003142c012301d0700042d4010315650300050080f01c0455000600303004020404c910004204156100c052440d00320704003071610f804aa403040e00f100c0c0050032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 468100611 1250 468099361 468099377
    0x603030e01081314011d0105010b0304020402030c04080708011d010203060a14060f07060501030201090602060c071704210203011d070905181b100c05060f0601140c030414041b 77
    0x716075110340c009081d41c0c4c21040740d103540201c1040242c001d010b0f624044c4040303603203056104008081032060034122501c0300c42c2c05e0724607034407070342048000c0d8001400b4240c039120038080803030745100030045440680041c0e00009400307145588800818901c80d92811941d078010800c00509032039110000049410101f4040203c69445000460b240143c0034404440303e00424042c041c0600b90300a241280e0003a00c8507003980d5102c1d0812030303c8800480d0b1200203550b0800005000640510702c44220003007044c0c070582440d07120b405c2488890f460501c035002d240180c006120540c034080c0f0614042400044448015652088056031130707016504c1015000740c2c8c1d420014008080d40038840603684240029104d007400040500140c1c14249001c1e14012600303615124420741c01451038010490300036000702002d943d0300e001090003c1004080e6070401c81406258501104500d01512401c415030703014686a43c10281032180c892407c0440c0d500c2142450880e448c1c0200690007684138140d94130342802 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 468101861 1250 468100611 468100621
    0x20307020a11010905041406091305030f090f0904080706060e09071406040b03010b030103060c0203070c050d0c26100b0904080a050702090c09130b011d040f05010e04050d030603030e0108 82
    0x181280556003c21b400a081c48004d0000c1d041c2e07200041e2283c40d040b655940c103a240c6618100300035200c0314008180794410001700c0316014582c009031a04040c0144014421808140031806104003520f08513130700c22009c1340d04d104100060240740d000d05610176460030315143c81720040350f070b65882d0f100314500c4c101000c040801903201c0c601280c0251443d003a016550b541d6950034480310394424441580c06038580144005414404003c0312000341d0003d84801e13030345040000308981d1600d00941200c01c1c0c200010700080b00390000007104404540c0555501540c01030180d600c0c14801607001c0003039030626021703a0465681d80e03400b0b00798025404c05189901d603510781c1810340d041c0c49281d002a40c000100010045103440080080118140c15135007551080d02c0500306030107071880f80790748501054070300038101c0490710a0039401d0070200e4002c05c0130500341051851001260301c20307000380745200d0b010000c200c20310900f08010ba0220f403ea28003049542e1554400900c40a2045413840c100000080815 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 468103111 1250 468101861 468101867
    0x18110915010518030307030c14010605011d0d021206390a021e0703020f1801030201210203040506070221030106140f122a0409090503070c06081009020307020a1101 72
    0x41c21103004e400c0300c2e591511410040e2145951007421986c0400b46c248019031018103010304070840d81c060316286031294001000240d00e80c0d4281d00181c0001c00c190481c0c015940d12916402d03d44441806050300c1c0c14240782d09070100540440c0d91803220104c80c51800108040301c0c0081510b4106000c2986039502c0d031108070300309101c008080301c00800508482050540100b002d8049a10840d1110100d0029005105900c0c00043c1078030b440d18800e900400144d40901034601451083c09100d00020b440c188a51049030403e0300d0507141c0f548041c040204407501008809071640020100660340100c81071460601c0c0300500692040280f280c8018030004901000d80320107140c4e422440ba01c03041c21114650114604451000e0300c100102094890746103102202a08a01510f05542c9004d04149681015240d180c03800c036214403007000404040f03060050b14101811036940c86c4006030610071200e40d040001900003004040c0f0420500c078005400044090820303500c05c0e00090119044c400603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 468104361 1250 468103111 468103147
    0x92e0303080619150f030506010c030c060c230904050606070203031b0307080d0e010b060f070b0c0c0d110d08060d030804050115060f020f0a030221040801181109150105 74
    0xc03032151200411035070b0304e1541000220904031a150303070400159946000442d5001c42030b19015020403030b02055000440c0a540200b900800a828014008601800785051004000b08d0b80e20b40054042187d0035985420b00a080d0400300031140345090641580019489218510411260400245900d040300c4414400e9412140d00207603419180c010148850019000148884140f03510f841581240761408005441441c402c80540b24240012981c0f440728082c0702030100c0e00541c1c0180140401c4010401c80c00451150340e90300c120507038440c00ba0f640d180c0340180400b002404036a00400402e034448501c46030700640c05107008951610780303061084c014008099500c00200070b0a04c0441d01540165500c0400d44080c0c0c01c41c2c00f0000c50110b41525141c40c9400180140c00806144000c0c951060540d501c0ba200c280c1d16900e0259201805401c49020a00f14200440041560814810001c4d0381010850003580e040c0002d2810040047d9100100f07601c45050060200d040c21200400e80c400d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 468105611 1250 468104361 468104369
    0x10509010b1305090a02280f0f030209040c0302121e04200a030b0601021203090c04051e04050703030908011505210111090306070518040207060209092e0303080619 72
    0x41c600e0a085c02c1c0d03468800381d40508440584000074802920340711801c0c41c801ea0078142c2580d1454000310f01d00c2e41c1159181401c034114003c1540900a21856545900c038000700c1158035100103030b8030000400003904071350300240405028400740d04070417040740c0060700380c65015074003480340800041010184980c01144180eaa030700103603002c60110803c801c0c3c1060034050304003602102c8008031a000c1e001070030301c0115180e40913504004112101c03801c01c6c0c0c00c810f8015a051101240c101c052010040c1040030403102660150300503c1c08005058105444c280a885820006d11841007400350030300540c80144541806080703200b903e12041c840d071036130081200344041e0081c01301003448000840d264010366600e501c02c1c0220000300344024001c03004c940c2d01040ca1082c4c080c11902d2481000001e4101c034006583c0e0a17003c020003404d41e5508c2c2001c070710800d20558880c0f514039403403180980036040c1c1d18a0544400e1300400a1010942059400d40e020408580a041504500c019000c6103001303940 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 468106861 1250 468105611 468105619
    0x311061c05040b0f090d021c020a05030d1505040204050d02130b030a0f050111040e1f090c113c0703080f0a1b0309030602130f2309010509010b1305 65
    0x400d200c00c00128403c42c41c01103500408000c400c0e2901d004d001e44400e40441e003c0090780c84091400c01d50003003151010b61040f00342c011707240d05091603240d050843d440020a4a2034903500e480501510042c440c010f409040252011409c05003442c010803210600d000e006846020b8030b1116441800060b040b1510100001c0c3c180c03a03218480d0318001c240400030882c215070755400c00ba940c040d803140f000300b5070341118004a174110300c40c2c03940c07101603100702400c0456030440d03086c081001c100c60f4114000c0710060800c507900e00120304500c0d02d405050400c000f0a1180d40300c3c07090129403a4100c0d02018070000c1c4500300c504103086c0000403e00b4a008000c2e40014103110000c21001c0865108001038226607a10b61035002095006d90310b1581142290308004020502c4800e00744081010f81e405041d00c2600c00303801c2000079441d4801020450443d61010451320012641e0130300d040212005000d2103c8251013200c51541044005200350b401406501008000412181080c0840c4000d00300104170240c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 468108111 1250 468106861 468106871
    0x40b191508161703030103020607052803111b01030b0303251a0606030a0b1c1202011103091903021204030606090e031e0c01090b0a050109050603070311061c 69
    0x104450310b554016804282d030441d48140090110341c1d28070b10196109004004d1440d503030a60f070812050f90040e0005586c107120302c000301c1030520101482d018400c40c513403055500700704843c030740200f03c00c2d513030442c0907890340021616031038001c0111f4480c0d010701424240816002060300100e03286005416803110b000aa030f58100b41100030203070b42520f10b41d0055a00e207031103c501440c2000300c00303402d40390540c01c1681040010640542540301d954590b00c02004c100082002458211302008803520071340f010103140f05200c000640901c910039615900004007810742c80d202c2040f607100c01181c881e41c144c680030400c4200406100f442254150700c40c03244407a03290764503410807100811640c0141c01c0c501e4606144022030b194008140c584030103011003200104400000c240300150060340b160b400a41d00c42d0301060015032180c4100d40318900e08030300040c0c01e601d000da1540907a20060f007001d000c1d030091031061010848403d100350105000b80c0d40c40d640c0301c12500d40911080c0801e0a2145007034542 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 468109361 1250 468108111 468108119
    0x9020901060e2706101103030604051e090705031606021c0504031b06031d030901120b15090f100c060908090616020f04050c1b0102040b0f07030207060206040b1915 72
    0x11000e03034010803040e02d01140b400c2c0e00000a88010051b0301c0c908074540d005200040440c03400ba040507501a5050415030040c850410703821031100c5055404107920303003102c58180700c00d04042099541203a0a00c1406441c1c07854084040e45541000500e041390740b00d00c00741080158002d008440c02550701140c641840f003540d0800200d156014043c11000a04083d214000c110b1519490041000f42e0b602a510703205400005440c1d00030801c0c0b2011080e6103491400403a40e5414101d0982002c850400590b41c0302220100500800c41140d040e211b913001003105586c0a0f030091038000300661100e400945800c0e54101100c0500400c4840d9500090002d145400d44c040e502c0c540b14054802e0701d038070000b003110004100030b860080700c0c01d030170a42050100c0caa035614400b421000f15000c41c0001858262a444c0b52449984100b901c0e48240800140010416604110020040c5032030b101405150900c4e583d500d0810101030b00d102000303100c500400c0700c0301741d03241c1c008201c1d183d05a04030b488266407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 468110611 1250 468109361 468109429
    0x40503130e011a0307120c0e060a0e01080610080105270103030c26090409030c051002030108070801021c091416080f0708030406030221010305010f060909020901060e 73
    0x7007401145500c1c180ca080c81002d0960000c20b50340503100548509849180c040c4001006025080040c0e0400c450000c40401c0c81e101ca0000b0050403a4035601c0b00484c1c090000003400004000c1c1c102070250000d85242c1050719030020f000c90640c0d00865078400f60f24241d614610800416a92039141c000301c28000008240d0446107000f0018441c5110181c40d282c41030003144103001c00001045080c02c03c00c0308124a1800340d102545040c0720382080284801c16840706841d120304d195142e610150b00200500c0021400c00291005004602c020b61030542d5440c0801c80300740d074a0089040e600c0d15800791104118050388081c00102d035a104480c0754100d1852000404803281c4110441402900e00d580907007070000c15194162002200198a01490888118020b600c00c074550190308003c941c40030181550140d6280c025402400045400c0c011401e41c2e1080741c1c980c0e1300030401186071208600041e103900b510b1a04454081c00d0100142800d180403c8161803040d04443c1c1c5170018450034148904 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 468111861 1250 468110611 468110639
    0x4080c0103183302090d0209061206010b0417070311150d18260304020904060b0312040801180213050601030b04330605070822121a130b04050313 64
    0x50700c20640465540f410201c4800ca100c0c081c1117a0700072a08040680c050b00741003994130b402c0300026040308900c401c82010b607420620282c000c60045940000c0422076000c0c824041a00c2102140242a00c1459980d0340c00740104a40141130142c003c0e006c14008180c2140152180c500d407542041c0210b10f81d0038104035040c00400b10031118040800414a00c0100543c8820405d503103605a9918580719a001c0162010000b4002c880c907540f11415401135031402d1041c4a2900d01c1c40f403502d52242e05000055083d190356200400520048044110140c4e407210b1204008454008001841c2d44800c401203024110140300181c00500344001958642c0031102e0445104150160243c205a8007948540c0303010420b1040c04000b400c1403207070101283c030b10750052548107201030080c1070b8420700303898200c80740000da80700f0343d41e0080c40c8142070107000c003c100c0403994401c0380c4038608891a0a4841030144145190094001100d205c0001c08100382081150142425803070344da080a0b594000140c0429 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 468113111 1250 468111861 468111923
    0x9020a0b0307030c080a06050102030406120906091b0602010b0a05040c030905070b09090604050402010e0112060e0a022d04120c03170702031b090406230405010605010f0504080c010318 81
    0x140005c030003c0c08080f8640718800075680164095840c19240043c2250360820300780c00ba1921035582e0710400000340d000d00c100d6000d076202e82004d40310024011030f0040080c102d948100c065904000d1021990794800e0703000c90903203501300d0f0b00185132203280408400070000307100000c100e07200b43c80300455950f145801030401c04a040303800c001e07265508810f1200380e450943c1d009011031818000505036600941c000101d5440720203001414596a03030302d145428000341c450190755075002a000502d0800300100b081501d900e020092055110380340040e07100d02c1188100300400c18810461810030240504043c029508940c0d18102c501e524200400b480d03102860491291243e44071240e400300c00d20059284c0501c006018038151f50f62902c1e80c07800f400c6180c0c01c0340010018211010034046203003a006020f0350056000186040c00d0100242c150100394030201c0521009001c104101400000d401d000001f0030710340856020b2038480e05000d94025140d004101124218a01b40b400c000445008404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 468114361 1250 468113111 468113117
    0x60f030e07211407090c0c0b0a020313050a08030a0e010b03071a090301020c030a030b0109030309031502190801080c0d15020a02032a1603261306170703050f0a09020a0b0307030c 78
    0x30400c3e86c01c0d507042464110091042111900145140d101b650255034410223041c0c88c013010b4049951303602c1c1010110700b0100da60200c04401e00600803e948a00d210807404007008200080c031000000e41d50f5003443c400c8101c04103882e2008000b282d510010303a0f44414001e0025511502c9000b6600e46942055916500091814250480540c81002c55404aa800d5280d81119500f552210114840403034180d0000039000c110303188502d030109034074441c8403450741d503843c0c1654100480107003040310700e805041c8039a103058441c0003c0361404403802001d00c440b81d40180d44880303000d03043c0e05500455000d00c81d204000a00c4180c0350f00e4400c0951214072081c8260380301114083c040d240c6102481c0130140c0030081c01020341d015070300185000d10800705070f9040507051460412280d641c5040c503400000004650f58004485144030041480d001505418140420b250180c040f039410700303000704500c802c1c03922160400c055455001c1c001000e014084000c542c3c82c6404600039020b010444000303800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 468115611 1250 468114361 468114371
    0x11116090c021518011415040507050f1c060e1014060310180b040e0106081203040302250b0307030c0e0d051c05040816060f030e0721140709 62
    0xc0d0b84040b0346041c2c1801c81c10a10080c0da210860711240070120f50303980d081190342e03442d03085034000141c0507094410041c450349100a0a202024401a541d0140c403200905c402400804841c806c9032060342c000906400380c0903d02c000c0c48001e0b00203050160320401c101c40e460310510007020403043c42d01c0e05450043c80d0030001d010341001808854032044a0710764003a41005418808230864050080c01a22108008242c000b200307000101140d001d0000c80c0e14682d0344100800940d0010300201e51a80804161241145400d850181d2641c10750b121410410340c0c6000c5a6050302030001048018050f4070203295220b10f04500c010700102900d4843da008144c964107081510703e40101c6c60300303400364000c010b4004194000880041c6000e80c0c400792003407000030b21002c2642201006141c07030140e0742e050085a4a0314011002e8807172160030314100101818075440101c44500003072503000300c0f03071810005d0304607035030000e03202d402c084000d24004c207580408490705052481c00240d003402e40b80c0440c5c080007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 468116861 1250 468115611 468115631
    0x90615110a080301121a01060e01030c020c150307090b0a050304021c050d050c010b0d05010603110a120201081e040b10090624090302270109020405030a0b040201111609 74
    0x181d159500c0900522000c0c0c204010b2200c1169140d800d540e071031040c201d94211060b418000b10074003000340c0091000980a011081c41581d0501803500c55011500141c01e86510020200d400078808030a0903246031400000700702445c1c1328050703500013040303031074605500c070040c0140082559205407001d0384106a40c4e040c00c15004154144174001a5000c001005900c95900040c0d803650002d5400700d030309550340c8090018580300d0101c0002094420000060800d056191526002c0340c0c40480394010449c10000b800040200c5941068250b02400c0c82142541c510829182c0c4401031070740342c030050f2018400e100c02c2040070711101c0d00580744515120380154507400080c04441441c440d1194085012240d034442007861903200d5080c0e1418649204078580340d4012a41540c803608400da14038038641100da6000b80241045405082412020740c40d192420001035551b122a800c0503000442d0f160214046a0081e1400e5054441090980e00018144400344481c1d403003034462920264113150000b8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 468118111 1250 468116861 468116863
    0x12030c120905031b040608030c0610090e0a030305130c0e0a06050102190303050c0c07030312110702010c151b0e0310020703080f070302041d1f2d09061511 68
    0x1d4160b40c00a40180440107280a8201001244400c4250000d541d00780210b00d120781407008000782d2428000401c540c0c00c000030b0140c1d42d100d440e844440300b00d241c001144a4280081402c0400c42d40601d40803c03a034550031803850981d1100007000740014180c2c0d40000c1d441040021152003222044000c0007419030310f01c0166201c00d0710015040c1c2500890203070741c0c0002d0003503200e0b0340c1024044040780c0c18400e48401e40c42c80c00312030381c00a0b40030850031241c104509240f8007452902c9503650146504101d543d500203404003c4001e8024034078404d0502024040d422230707000e0b86182c1b4030b603d090411054056805450b282d960100301e40607008229103542148158001c49501c9035140d0340303080155442c2c0000c0344448201610502c00c0640070840014a002e110b80d0701450902101c041c0017950825904d0104100541d4404032407513021408100604003100080440f1500700c9a09140700c4901314440c0500d07030304980c10000030341c1e1903c1703808580f2105411075843ea4103a162140e421041d81242c2407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 468119361 1250 468118111 468118127
    0x30f060c021219031d0105010302190b041802091815040b060f0a02030f12150d0308061302040509010806041a090c22090b1006050f0301031b12030c12 66
    0x81501c20010040d09412a00321204900c0b43e65191800141044441c0700701d85500040c1035450096a4440f4010310561400d00c1c0905201c46140059108603460901c185c58640128440e4544c0700301d80c4000c5020740000c6070100e9041400042080d1004200381c0c03c070f075084603000c3d00d49080440301040031a07142c0c00c181c8030b415000e0800a042c9410640700380c201b80080d601c43c0c5001021030105100300750340355071100c028203031001c1c8400d0981003901c0c00d0b4480c1035030a075080d080075204400504001c030109410002540c2c004800780d81c41c00c54007002240620182c491580450303000061040001101c103000b00f11b1a000c0c600c10300000c401c0001c3c00c40d801c0d0b59481c041c1c0e2012141d8102241003c92440c000700f282d41144001b1203110081488281c25501f1a00d01d4881510035156810821945e200722821080150105040c41401d0841d07081a100c001d0005020080c000810b900001c0c506c00d0071458030700010502c2aa04101030000c600e070003880b140366500708848034440d40780d20010f40e42c000c240c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 468120611 1250 468119361 468119383
    0x111070c03080f091504140402030c09040e120a090510050702100806011412040b092e060e010b0705010c080402090a051803040b12130201050f07031206030f060c02 72
    0x3818508074155260000107038803607092190507030760810401d0099150308a4194644102e03042d9281c4561a103a1212840b801e1004014400d910400c10401d14020490548250350800d580c00030341d406045821625140c098603401c80030850209000c103030380d07a0001c103c40540704281c90301e070b00503500f018058500d40100342000358028480b50780c10f410b152160b1085036116205152146400e28a90003800d40d40d405009105158801c10702080140104150750541041544d07000b0b02c84201d80e03410070000312480b0000740c40280344005a21140340302c25001031018007110b04554441c0d503500d405072205941301c0d0380304843c80e5017064103082c0b080d070090030260b2081390050b00d51429503442a07202c0d4001d0500400646030300441c171004140d105402c0000e80042d000301a06550380d0900311004280241004041c801d013502c40355031000050346d0007003c3c0c032840380642d50a56200c012614060340d04800060300d840f92140b030b00c140042441100c1d05141501409540100400c0322026422611804030540b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 468121861 1250 468120611 468120623
    0x10c1b020a17030904090f020405060a0e0705070f02030607020708060a14010b0a17041b08010504020a1e0806092b0e01050a020307050a0b1803041503020901031e0e011107 75
    0x904010009042d0048200181070390252441e0180c100c00107812644004802e450281d644404202182401c1c80b0301c1d600440700702da440c500c20b49010078070039a0010040c503080c100040440c440080001d1481e040360044d600505079215403500b290000c4d55000320344540e052501c2108040f070480005131046581a0681c16112200d582c00c1c541640c40641c0f0080c4a40f00f04141002c51001a550014202c1c0c0100d1007003035201e500c40001c80d181c441c8244990030498040c3d240c50240001a40e40101075030403070313001106011800d00c03071039281d004051180d8403440d15409100d0400c000c00ca80400c40d07140300d44103803041c10801500000074414040c15484880d000c81c0300d0141c2c0c90300791b600076005400103044610490340741550359501e032410720380e10340402c96094096405004855102050000141c40344400550070240303480340141c0c0540b640d91024050650004048c211640b0035001400704091002d81c4041d00f400e0340d00301c60001e01d0100040502e9518112102d0f0303c40100a04448445030000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 468123111 1250 468121861 468121879
    0x310e1c090e060f030f011b0e06120604020405060a02061b0301080c0d060f0e0303060a14100c05012304120905030a0312150b0d0b3a14010c1b02 63
    0x2540005503004041c1069030700c42c0d080340d101003007958208401744410404400214003000200c0024100040c0b0140748414001e8003903a408998030703401d040c0c0d9055404030207003205549461300401c4c002d100b5030300706903000880003c0b04064182c0000380d1038000d100810400043c6148101160205e000a00502080ba00006044842490440c0c2d606880170301400c000540035903c880c3c0801183c41100d140340701030b08040108405480d040c480301009003d010201015440128001100e5a0a103280602444404021039041c40710950290500c2e64100c1c3c00503440e0503c041c40c1106504049408403400e0342c0008510810038440d4004a0813a500500102070511030766a05690041d420100403030f6607079440d101507940d2160184c0d000004e042c000075459491541038441e8051b01c038140c14050148412222050084003202c00f0941452946090354501c44905c8000d0441c0801c40d4002401e451a4148044400081035001c1200160261124031003d6071031800d03035a82e00b4202c031010b50700408103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 468124361 1250 468123111 468123119
    0x3040b0105060d0f020d1a0a0e070804050a020306040803040204150f050103090501150b1306050405030634051803060f0408030702070e04200d11310e1c09 68
    0x400054500401003010215130ba8015000c8030003240c004465140300b568032505260422019840e989076400d1081d90344402c81400c0000072040c21202034010020400b02303000040501909000e20b05125a000301030381c1050074207050a8200b5001a07a080c2d2180385400b000b5050000020b42c02c0c400c4444026007505c0d241d14140040d00106005d51341136425549419101e0107813001010444080d192661405459034104401c0404007c44d98002c442407000400080c0481da41c00256264041001a003a04100b0380055100c9048102440210203015020310001c81ca9604000503000c650940400346100314150710400d03079141d105840c1403104c40c2c0c01001040201e07081200840e400340107401240c05039951481d0080c0966000c803420707500002006010b06141801014040c01040112061f481e040343d00d0702c415045542040d080e030701c9800d0320010b2001d0603002e500c0c8a2400b60a114030f8050980003c642200035141c810f14541e901d0194800d07130a405a100b04030407041041c031ba540c1400c11401c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 468125611 1250 468124361 468124369
    0x51c0905100506060f0c010212091519020d1b0e01050f120604090b090d0909140f04031116031424100e090c03010501080d1706060f070b01061403040b0105 68
    0x4050802500003408000402894418600074070f1090740303a400042c1d44840d2710b18000710401c00036000700c0c000e030001420460001c240303c101e50303049100c000801e40b0301121002104001d1045090003000740d030a10a41c04040001200c080c9100080b50b241d0001c20b840003c01180d0a02c24207018000d010014403280113070080d09400d050f448000907100103801c1e07207503842d000200d000c211002c04480c0c0c01040003454550744027010740000c00400304c00384080c2078190f0518090000003010003050080810019050500c52807001c5a006c000600744d410b04c00c42e200310b180c505215070200765a8580030307000c0b0803440c1c400041e0150680b0401c8641240c1c03030000101d00c2495050290402e0f140c128040c0021841044008004d401152010018003130080950117060a42c1c405900105d1590001f903244451b40e03821030410050b10021124202d4640d803072100103540c90040c100060741d007450202d400c0301000301121199050b24080e40303981e40154454001d5681c0340c40111401070000c41c45000400090034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 468126861 1250 468125611 468125621
    0x30a1206050406030b0109151202060d142d15061303050d050d0f0605150c07030c03050a1403040305030f2a010506011706033a051c090510 61
    0x80042400308149070340d88000740a851503500309560400381d07003004024405152140558040385801d001c101d641c03520f04042d4800f4400540a80940000a80e10315000134507480942c4204284000407114107019140304010b1b006010f5504070801020750904141c1100350020740718422000c050481c8072428001e22805401c002046880c60080c40c00100000c0d0050101125254090f03444075140d105103d00c1d40169080070241c041564507010701401b080d20b501c12001d010f025171240040e07840600c1c0c6100da142c0a003680c006000440e040c0c0020040010200c3c0841c1110300035030b80582d035601c01c038108685034800c1d03110040080d403040240683c4541e1081c05000c00100c2c8100d0855140450310f211504150140f400c02e0540c1d6403902003111329a0415240c00586082110407142880d00402095650041806103c400e0030f00082c0c440c001e181e0381d0398400c51b101840c290003c0124007081c0242003a080342d05000010801880c851407100b1040c800d061400750480d000b442464050b00007000108 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 468128111 1250 468126861 468126887
    0x8180108040c0501110a3507030e060f0702120307030f17040f032106031412120c04120b0124050a0f050408070807080c040e070b1c1404050c04020408030a 68
    0x4006c0600d09004290000b50107144101034428541c000c01c400d108540104010b0040c0360180c645c140b080a0100341d11080c040c142c3c070002e4030815074544204560f03105501660400960000d90031880b9030804001201074211684281c4030b0303880c0031502650503030b0300b00b4841c02d411003080643e000090116842c52402d004040c040e00b0b2075482113601500c80400c0c86040740221030000d4841c1c00400c2000404014108400304d803001801081c420307503c564080388140100d00c0b45440d000404280485c0c80070302190020420340021540b1408903190110100100b481800c4201004092002d21301110119040c1b28100c6681c6082c6000c0003008151403050b035000c6504200310092002084880b01003007124003800d500340040c19590310b0f202e412490181c80851142c0542d0404c10b102c4801c4400044580603168801c000c0b585445c0d800001d20743c800402ca13a146c100700d050402210b28414410103041c06a4000d805841d0b03500410701c02e0100303034841c81c802c21000b5031080060020152144003c5c0c0100c0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 468129361 1250 468128111 468128113
    0xf05040e090a050f0105060a0603150905181207110108090c0a0f031b0503030f0304061e05041103120a0309141002040509070c0f02040f0b040908180108040c050111 72
    0xa85548080000490895100740c141d031110000c4014410b040001c40805202d4400074400c1749000d00205140c0200741c8210020b058403809084100116040c204c0041d00040300c1c100000d05d80106460205a07580d42c1128550181c60319441000c02900100c445050f0003007103007400c842c6800c0046038243c8008003141154007500e034030190266a502245402030400100030744140d819800c00e4207034012416a50310f1115414203041000c6d0f1000300c151503c254104810a80382e07603441c00d161000e070204100c299007050b2520300b003203000c0078140e107ca070269000f50603c241800e41402419600c501c141500000600180244200103119401111507144540c86103014010380c20044c40c80c00b40d800420030080794002c2001c0c011ba0a280c041940d01400600d4120401940ca4440c4a00c248800c20080e0007242c548841c1041a40c00e40c22035003200780082e0040280c01a1402c004019820100c05400c8098640540300c2043d840303814068007441e08546620420382c6800010340d11009618681c0b030f07035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 468130611 1250 468129361 468129367
    0x1b0804060804060f05073605040207031209060f0c03150b0a1106130201020606010c081210261b0f060313020303030114011b080a030915090f0606080706050a0f05 71
    0x84850340581406182c00b40ca07448400c0b900d400e42d2031f0094241102e81e01407407184494680b14003040e140780804982c801d950051b9994401d00f41107030301c1001c46000e408035230f00340030a03142003011640c021400e0210a15080040c5090010704600b681c0c24640000007c0d0098030301400501d41060081048046500b400e04a8201c800c4080d810280b00711091842e1a40202580c0c00b5543c041c402c070340d0310500900c0e203080ca6080c165501f85140c056598860190380d10440050205020704a40e1005000d601000c2c0000b00018145585151001d03e03060500c0e00502e2050313840101210340c920359200c0c0c001c4c60404140c0c0410180314050b0401003000c2c003e00e041000c2c0701c015841c107200840c081c00c40180001150a40302001500d0b84081c9039001c0c5082c645908604042101201030311103241c1e1718070780440d40b08071a050120070700d07a0700310240a90918201d83d50003002851945100128440d10007440707038558800b00386880b50110700c11840458070401ca0100014424852000c0301e64184c104582 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 468131861 1250 468130611 468130631
    0x20a14030c1006030c080f100506031e03030a060509061311090d050604050c0102160509060a090509030904051303211e1d16050f0307090c0f1b080406080406 69
    0x450b00c0168903418401d07560ba50300034030600003c00c520380064043d040040c0903582e400541d203561102e0245050907810b5a5078045042d6a4092008007a88864980c0209005030754a48843c0c0307940c0140c440c1d8158901d42100010785d42806860f00f40300c0c0318014185920399900d4270005014280403200003070390080800c045403465886031401c400b003074000c40081c441031038903240c00c91500703c80e0600c160541d40720300e54501c1d81c0c40c5500d0b003600a0302e00c2500e10a888e0b0b158079011a0300d9480030382100403041d0400741000100c0200001802106004940c05d1000d6100c89501c00120421072001a0004902840b0201508400c6000284e000d8001c6130000f211601410030312400710b000500300c1803458580001e0302261401d83c8801059099120141c03803401b503e60001d0b001104c143c070503940114024107204406641c1071042400401c0150340500003400d0102009168000480107180420002c0380d00301c000c001001c0c0010000c651143c0302c0c524140c01d020094440610040c0304460b00790300e0f00b0b1261 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 468133111 1250 468131861 468131863
    0xe0c130207032703171810020309030105191104050a0e06030a140303070f080609071d12071703030115030f0b0d0f060e01020f12060103020c0607080a110a020a14030c 73
    0x1240d02000c0380460806003540b0344580c80024000c45e009805005110b0900140c1810a52403e802400c59611003507080c99070b02a07003180580d1101c180d25529140400034414110298020040070020041003c1081c1c0358130b010450140c2e00404d5048051f81205004020314411b00c0b40e08400001d007101e07003111040da00d075004800c05517100405034001000348038070b144d0410340044005c000350501e011035240510100e50300403802880e2004110300919404448501000012080700d40500100c40564240d10301550b41c0a217803180c881c048400b5024665520000b0050301d06941c1e2a45080c41c4030845000c0403406000d030000c90310502a0744002410261f51a4664804440c0c410715040712400c2c1c281c217004045600d4200009450b074010401c801044411074212103542c8602000d14000d03848100040340203010302154038a00b8820a010b0000d000c0d0015880e5111354140e00003132081d00d502e04060350312030241c004c1007409a40005d580c40009450f03100c80c40701c02c50340502168103040c040d0101e9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 468134361 1250 468133111 468133157
    0x180c0a02010e03070507150804030507060b0420040503150709030f020102030906041403010c0e010f0507060f0606080a0b0a060914130c090305070e01030201020303070c110301020711040e0c13020703 87
    0x201e8259000310000c102074006141f00380700802d00c1d810440c45928098501400910890304010a19980c40e002c1c0444d503581c5600c100b0340c890801c03210944021001010381140d41c0240146031291042c075102180162100410798400c0c12603981d8800280d195030344440340000c0e500412070540c0014868101d81352a104041c1c4002c1000555a124140c203d80a05003161410f0900500b00040c00b4070001060340c00c079581c0021706815181060b525001030030964001c01030500f50244c0e081c04d0007800101140d01820304c41c003c10452904005c80a00c4800b00b040e41c2c1d0540c4140b07008201d407000e04200c05030706000d07851588040a049040c00300400c421007401c440c0c1c2c0e08504000706039001070030310030300c4410044903000d003e46903c90035655046400113550390100400c1c4004000030403240c035040000704000503203a00000b030000c2d901d13a0594039003017210401d10b401245c0110f242000320340a00d0070010f190824000058003050101b803050031050080d600012054040c000010301c07462056241c0400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 468135611 1250 468134361 468134363
    0x100b1207080f070f0f090f032a0e04030e010309050708012319020903030c0d0806153105120d03050f010812070f08180a05180c0a02010e0307 62
    0x45641149418000a00072410241c12403062040b03440400003429007054a4a82604240c00c1c4564420150315080310424180e030080c2e0081043c4010002c1044541403603080c1494100307040c1040313083d00c80c0c181c00900119118240d000e42d6501d010401090003a9440922198103160205409407a502d0301454200c0c5a0b221282580d55906441d14128114090100f070b148242e12800180c10003500c204d0000000c1086251116030004100086550400882d1095540c0c0015514000082040684520801c6600714040da41c511050102461200d023100e440550840e0380210b0311441c81840994024003c144010601410001080583c2c950709139080c00c1b07440100504005243c40700040568101030440703101190100014010920041000c0c00131803144040c0d240c0b100314074248a04c40000d00c00b0058080075000a0038042520b00703000032011464103586c803010403503850041c400030702d5002c1400000b40c4a490301140200d0800f13401000c10030820f2002207224070000d120b55082d903102140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 468136861 1250 468135611 468135637
    0x3041e0602210f070f021e0a150b1f0c0f020604180207120905010903031b140a03020d0e030c0d0501020f03090d03060509010605071203061707090501081212100b 71
    0x8000d10803003e103005a81c0941903150407121a803026a01035a1121090805030150410502840c900a01080030b926290303040180381d030043d940b076001803005141000d00140030300c0c44032691003425901200c4401d076040c0340703079691140b0294039101c00d010443c210728101d0740103404100014400381c6280362801680b54103d40180c0d81c40342881c206007203140c620150700a2002c039007010056030b81c2041d44201140e406060812503949840c0006425010051000340004c5054038030040300d40000030700b18000c920035001c60b0480b1081d41c4041d50001c4a006102c1e6144e44032551046060800c044401000340c441c1001508202644581042c183c20032a895101540205030781c902d05030b894011000281390640b056591541440001071071032040500282c006103003815042020381c031980c404002818a10b451060f403082c0c01c0006a2035220910840040b50f003040000b0a0805010a4403070303da0003031b0016586042d0640b01c04c2c4c14040030003040d004840c0c24041c800517464840000414140001c11 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 468138111 1250 468136861 468136927
    0x20105072a14040518060c1c0903090509070903051209120312040b0f0105031e0307050d020d020f0106080304141302030a05040605070c15180c092003041e0602 70
    0x2c010f0004840c802400030b8590b0f4910280c10321244404120796401001c40860305650b000040201d040f942490075048100d81e00d086942c50600d9484000041980e60460b001015a243c000c4100d4a00318140005056904001181d014081c0010014514101c002d803451360b06405c6803440764116004403804216240ba090308000400c12172044165001054003000e01041d4102030103e0768400c4180c0b1081c2c00c14041d0345884051000400a484001d6401011900c0d07a080c02c41000b502c9000e920600d201620983c0e100d5040d08070103006030002d5586c2e04004504243c0b502d0f0410801450a405040d000301c070204a00030301203414001180700348809000461581080d240c0b6804940d4018510030801186192803000200c41030f1004e1250301c0c1000c2c0109942040c1c4007034050061400782c0c0100550204500060540e47e6034000c00100f070030f800035034000b560940408aa49100c11540104403400d09400c08040c804c02c1c08a200416005450040c00c100010f80074802c010106109071604500318 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 468139361 1250 468138111 468138149
    0x23060114070506010906060f0c080703030b03060a0912020f15060604080f071401050a0813050c13051509040f0b040302011b02010e0d0216050603150301140a0b0d020105072a 76
    0x5406054007c254901e13005c0030080401200070540d642e0280028505400014802c0c14944682c01c07441e1006801425641ca60420310301003401060200f60441e11b40c000081b240e40468004203582c3c0c03006003808041c00318411548054000c0b2200282003a50004060002243c81d42082200080c0c0c45200c0c8001d140541c10a5110041c1a8081d4402410003004006030300034641d214005035005840108010b43c1d4407444c2c606607050000c6000100d80002c80c2c1408200d00205a81180f4000c2c4540f002c403103039075944d2406100c01890f045a000e0200b00c86851460005920700304001d034480d00034800020f480c0307401540e071682002240801c8006039180c1501800728041441507002c0c4040780e0000b8210714450000ca2f440c0c0224510a26108090120019417010400c00d07411040702c5005000308100840803e90421564080d03400d405200d151a00100c030900b06450080306c0690161902400c0500e282d403504895144070b54841506881e4544401c052095040900064100d80c0b9040d8462044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 468140611 1250 468139361 468139379
    0xc0712060f05090d0908120d0507110d0203070c080703030516050a1704030b07030c021f02070203010c1e030b0d020d030c120815190918080f09090a2306011407050601 73
    0x55904003d203940c0004010030021147c0c2c2c0f0840e441c1043e0110041401d0385c0300700040d9244460f840700c85290380920031100a2166010000b05030513445140c0d860386450b10303141c80340e54580c100c1c00018086902084070141100b21002c03a002003500c40d03411107840c6a80b965404032803004011a003058101c000c10103108003e100c0c0d031750650100d810716003040f80700714404000390340d0404103902c490a203000540824850082ea01250700c0c50350064002c3c8010408020001d140c0c01100700e203181c2c011307204501c03030003168402e028400d442507000f411510522525001c1040000d0600d02c2201400080015240008e009500c0c041070100540c6070041241b600b100c5030300c0c07c0c0803503e604601c9042e0310100d0500600419040c00c06072a00d034000007602c82c001d0385814500d80400d07034010380782a001050f5001c1c1c401c5800020a03001409803200802034172a580e4040a0301c02c00014030034168900d00300a5005130503101056400001498200d0581360301810000c1a03910001c02600ca907000400144000c401d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 468141861 1250 468140611 468140627
    0x160c03120e0420030915010b0901030c02030c0303010614040305010e15150603041202120403080d0f050f060d15020c0102040504050106050f0708090f0604080102030a110c0712060f05090d 82
    0x1920203000c007840364078800d010000300f0840703040f040c0c2000c40803844040082290001e012111188441156115400d04c252500034080c01380c0002d0030a901c02d40c803c1e10100c10385030513000400003942141d0034800c0503128500d40050318007000c0014000003000c10802d0080d0365245400d035002e031480d880f581c580c1014803a030003032103141e024809982e01d20b000d07100c0104582e40103400004019800d27400b440c0c00ca0501c44440c4220009240209011080c44824001000340b4141b0741010041940c84945060903550111554121000304a0000c0d0322400c00000b0200400d1290742d03000001080300352800308907042006000160382d070120b01481281032510400303000d004241090760514592640e40516849044070083c030f51320020400d1416a19440c2d28804882d8000707213131944903a00c1c0d4081d5130003500100e444408680c10031400c400820b0b0300008981c0262503040c041c0800d00d04051156184c030070a110100c900550317408a80d030000c41c4038459240200032401c00b420b40d002c0340a8000700810 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 468143111 1250 468141861 468141887
    0xd0509070f03060b030c100207080f0d050a0e0d0b100f05090603190c050306010e04060b120c0609030c0405040b01050112052401022506030e1203060402160c0312 71
    0x15001900030302642241e00e0100c02280c0d8802008030700a5040b1000c24241283c60f0001600b10682504032100203030049030810540b9011800c5404220503850003d42d42c000828500c004540104803000c0c040340308441d02c41038100e01800102100e900c0c0e685a4280f01000c44644070141c190400900440012260f442c0c01000100c0300000305d818000c00117520707070120b141e400680c401c15410b440104003103a05d50000401d00201543c90319a580d4142011854080b50202e40e843c2c945036103072042c0d203440302c103c0c00310b03002d140d00901c6180045014030440d40c1c03003c80c0c220390611818006030010340e6540202071089110f501c1ca40040d500d04400500700788514051880c2481c104400c02c030200603208840c0034808202c184110f02d01c0c5c41400141d0800303443c450030038041c4181103560355000106400170011690141d0342000b0a070655800340b5250103510b08505a81001000401c01034517080e0050003019000020341c00d040000ba80c1c034045115020307441100c1d0034111049000b10a03800200031000f031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 468144361 1250 468143111 468143113
    0x11106010806150a0f0b210a0207020f030105090607031109030115090b060f07021005041e03020a05030f0a121e020d1d031c1b1b061e14130b0d0509 65
    0x145c2c20030400302680c00f03c500565100d4080443c00d0110360104410a114000d12540c0c0c19005041c942c4000000e54080750301a800b40503a43c100d076549040510510b8412241c9101914140d101c10070b0460181c8924080564441c9050041007070790f035030a1040020485052206040346880d1030f0b0304c0c20a44412048484c0300700010701181c440181031001702c1d000194110348007240090410f000b9034480c015600610700d4040c03285210640f908480f410302050707070700845121110740d03901d80405507500d1a4031025900c40c1c100d580040b001950b1400701c4020100d5500f05a0001c40080041c1c004540100340200c0051744502d43c401d10150700401080c1490b1510388044001b101d03c40c0101e03a481c03880500d49190320342c0c2c402c000880303a0300c90110564050300302d000062600415081039184650103134400d40490501030800903142e8041c1d40030010040d9856894601030a00030400c0c1c1d50504201500c1b0114141005008084800c600101c00a004640d1080d601c03114035091003000c60b8001042c00000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 468145611 1250 468144361 468144379
    0x42313060837031112031306021e0f07030e010302070c050906041d1e010c020705010c0305070b0f0f06041e0906180308061206070c0206030601110601080615 69
    0x703062008030307003000080c0351101d42001205484032601098441058008061070030400c0702010158451a1601030404200441d1149162414081058402a940c903401c4c04c1c807a4a0a50020751b184e0054817048035403a0641266000390641031841b540403041c5c111000c02c0006500d0704046e0000f109544021003840c00f1070412800d5550a00e114201780180391040703441c8400a480f555440d000100100034081e022080ca001d4600104c1c0d0721100d01c807503680f40560341160707004400c43c144500344800001e40e0040c10300e5131401e00195540c030884c1d0426801c01208106100200d15011207880c0990a100c03030001140ca0510710210006801900c0e0341d101d2401c180203003d600d5440650041100103111000801114074640800140840641c4051035405601844103258020b828680714600c15140034400952441c041501c0303c0040792840003003000d5034461000744c1090030165901140604000f41510701020000d40341080c00d91041c81c0623880320f0100495400d0b0398010a60003007041d580110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 468146861 1250 468145611 468145619
    0xc02010c080f040b0f0415060306060801061a0f030402120312011403030c06070807020703021324080a062013030309060507030e09060105090a0f060311071a070504231306 75
    0x70910001629001c600d600f045c0125040c031840044c858030084d100700041120554078070b404d802408192059003159460140c0c000b41000c0d001c0300124030840c109130403620f08090307124400c0d8a504042c0003a60009400030540c440c20400f04000c0003800785c00c1021a0b500d600d081c00f48807000d1441f031403040c025001400a95840300c80024401e400a036603080008051390740d428120310340142c0380d00103503100e50000725183e114030b941e90001421140302228411a80781d107800000d20b07060540708410745503000c0d0b2071860100300a580407101100380c0e20484038403940142030500c13003504440d50b441081c00b0031007001c00405401400c2c000007003245040143c1010003070f0700c028107071044034034200b030148012100140a42c2c0c812401c8131200c100c010004000b8a8540342d070161010483d0288401191500f00304080c03441915083c5d407172566104400140a422038031500c241001c01034594000d0003014000070403190801103003684020341e81581c100e12410118104140e507101829802c001ca840d1140c140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 468148111 1250 468146861 468146873
    0xa020408031b281209051c0c0e090d030b0415050409080405060c06150a030b061003111602041803081611030a11010b120717010e010c02010c080f04 65
    0x41800d001241554062080090501e040070022181010f0404415030050407543c03510021280c5180200307a0200c540855000581d1440c009000c3c0c03c2e40004940a41c044c000454108a01418800c090403409a039803904080018403003680c140415400100e81d0340744482e03052203001402c0d04110341c14040c17001003625040051025000755405a41c44100c06028401c000c1c04607030080001800d02503030f41a0000040d900c481c01910b0b840b2900c010112610050b10300400d80c0400d03240c000c40d079500f40f030300c41f00c0411001a00c41d07403510080c0b644400c034242032080f03417002400008200c8803000c00c044180c2d20411048480c00c1c801c0165850503804c500c00031990003d03109a1110b5031000e2007500e910091000c0d144c0d0642000344114601c0005854000315030700c86220618240c202d4000d100901c5070004112003c00360003180b48480e4410b0350300304000a110a2411001d4692500014007000a14038a070300b0b4801c10703036025002d40c3d1910910200c180e40040015130000d810035030256241029590760f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 468149361 1250 468148111 468148117
    0x51302011b0215300103120f020d1d03070644060d06090c030201090b1206040f15140109050306070e0114210405060a020901020709020c0109050d170a02040803 70
    0x50111250081040300c11400d00c0c41103214a86401c020b05407010414000460b036000b02400110f0700c007c07044022040490007600900400319050300a04148945c44100b142d50919a0300c0400b290b20300e16020400350346080c0b0003c0040d24040d07440c010080c41002070304d030041413151407803c5000b022154400241560100355400203000d504044007549500c000901c1d071290070311000d0301d120f01e015000010806290307241e200310b910030303200c0f40c617082da50f8946080180660225040b034000c542c000680d2902e000da22034890b0071840345001442a0310031080c08010100c035002035080a110640d01d4402d580c11503249002030004800078035043c0303001140240841250390b8414107001c1100032411241c80500240d882e100c000015921604010300400d02c400307c1c00761029122400b46c1c2c0c0105040c0d41c540c0c000c541d51134906070002c102c80352030300c4c040303000a5105009411040d540c0b8200c1c030300020024000e0f40c400b1802076503203010b000603541001020820140080244c9441000100011100070084d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 468150611 1250 468149361 468149389
    0x106080706050912010605090a0f0b060c0d0c21181403030a050906070b15100509010c11040e030f030703110301050d0303050405010e010204091a0901121410051302011b02 75
    0x2002d2440307500f0013010350260035190006640000e5110410180d540300d54450310b0740d50304416003800005030100034851244141540041c2c00e070007085840400e28040c1a140040e07134403c10002c010300381000304603a0342c82858110103000071002052014442d019921030b17409018218031424541d204500000d9880c40342c0d8034048184107020500d66815505e640c15941c00300d4001900724003031700d006070044651034440c0f0350740c5100e5482189800c103050300c21030503901844011303102c06480304940d8854043e5000040200c0b80e2182d241c01074200358903014009040060f0002030100d031282081c0401078250b9072003d01c400300d40481400108038a56401030200a01c0e5014100003e841d1183c1c10024050032404840b85a9507000007070002d40803d00340d01281280f031004040302028490b450401441040a1182080302404070410002041e40c141d0090100301849003120301130003410301d040c01510b50440d80c003107424071807804c0720f801e6580000a95034012042142e801c11101c40e035001900140503066 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 468151861 1250 468150611 468150619
    0xe150709050f0907020d1209051005070215060306340206190509060a09030e090c130b1911030c07060207150809281505010915030b0a02070303060308190201060807060509 75
    0x62018000548c80341100c2c0340c02909480b07004000d82c3c0388030068842a0b4122005202c4c9001c0c145059103d00051070043c2e40c02000b0300500d803213002d00400031000302c0859803004201c8261a076038034408000004079100950300a44410700d048006000c10128801e01000d00314140b2041000352200454141e44c4500c5404d03001502c0200e030300323080780d02500c1da9074a02e40006982080c800c448100034050001800c2c00554501c9035900e03003e04115500400c1e00400ca0841d1840e880040076002c0d6400501c00d1010b041182d05150108520300e1500100390310101c00758010850920005140c6e0905820b120b42c28203001b542030400144055407062120360b01d56800982080c0856024507455410034020340040815022103005c40494008220a01c01c0022051410703882c4484046039402c134034100d98000c480001e055440280990196110a50440030983c1c3d0781c001200045100016040021301070744a100001e101c0302001e421038a803a002406150701c03802c1c04005042e40305040321500319040d2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 468153111 1250 468151861 468151877
    0x17060402241b0f010204030309121b12020306070c12111c020609010e010c08010605090f12010c0f0e030c121903170105040605130e150709050f0907020d 67
    0x601d528441d4950400000c10401c40020201c11212481c003000c1600c02140007900c10003845006843e00700e105130f00c401000310b90b5040c020025651411034040d501c03400780e24a01c6141040524590121b440b40c0c01107148202c503801c040096050801203994400003d080481c0c295a072a140c010b00300305030003070920411000d0710341044602030511080c1c42c002400301c070964150641d4140651141ca0480d101c5a41c1d40c40c05000d644410414022006040a6600c3e0340e8241e03424590100c0d40f6074049401d441d0000484d141400103504d414990b184031b001c1c3c1d00c000054625907040018000c4005219610400074261030002c081c0d600800d801e80715940842e00350403510503005145040c100c0a1089a82400c1410404801c1c9904030718101158900480351400c03681c0c0780d00c204002c441443c0619a00059012030703404203080c0c04d500030420005c0da0300071544059109091a10322443c102c401400042030400100480d04040000c4003030400125000806468440d9000f90b840300b0020050080080c06 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 468154361 1250 468153111 468153139
    0x60b0f04090218040213140405072703050a0f0b0f151c02190f0905190b0303122a030c0f03040c0f0e040b0a09050703110a0b040f090617060402 63
    0x106003c1c02920501034030554468440b1082c1d580080001e11a42c040c0c0990703980354076068505417081c40d208074500c2d100d036502c02d03501180004540401d581421441d013400c010100c003180041040d0002184940210500c041a80c035050f004110050a00f110075010b400070301201f00c010801c03000c2e00109c1918140c000703005441041550440d104006900315810080d10001d0901400e03038801580c1c440006481040d650ba880e07201115003c907190410f5614840d108501c19115070080080420000d007101e0030320b03500101e481c21101056070304020172198100c805100c1d5041e8402505e8030200c5401c000c0c02e610b0004801c0610344103620110100c058000005010802d1401d6183c000e04540318140380c91680ba0b030700e03422128605a40956030407100f000040c00c030f07035568000e0f030300381c0c942c814050403406286644d000c04a410701c1d00e0182c0d01074402039001c591001e00c04068401000c0d00311481e038820b85020301d070004685481d000b03500450315004015092400014419800641c1601c0b411050080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 468155611 1250 468154361 468154387
    0x709050601140c03030103050c0a2108040b030f06040615021203041406090102030603010f0c05223803061f0c0b16030506010504080a080d110c060a060b0f040902 71
    0x240b071038805600c0c00d020501c84114880080614182c901c920111052080310343d007000300e03440741c500c541c140700d0020a60006069048450245c82c4901c2949160b04298644070322000039082100c0100e0341c0e100100c1085803a25080c000d2000601450200b0464503408100007515035408944146000f480040070408005c40001810240822401640d09500381071001c04d010303500035901c0a2096003489034102803030030507120302c40043c0519200e0610345200700003c003000f00e51300c5d005031207071840c0d01c42e00068400140e0381070091248580d00c2c908041c0003028019074009016203806407020001d004210700d40e26050ad402c0380d000c400f0400c049190030181412540141540001001215240140b11010a18900f03014804c0c480c2e440c203001699801004450070b00885c0b061450315030064000c1c902040c0320200401a0444ae5074000c145440ac6007420202a03125040c03d0041c2d9114104004504450380b0400e0007a0620560301c03807501066040914a81c0170b54069000c20650008a8598140c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 468156861 1250 468155611 468155627
    0x110705041a090426041409040f02100c05010e0102090d0305220303081602010c0e040e0a02030d5d0905030904200304140a051c0f02010b030709050601 66
    0x2100501000c81032405280c070340f007280c51540c0112860100314a132101c0c00f0881e0130940b401e0743d91581c0c07213651050380e0348100600b401d000340c01519032255034101a0b001d0f0700d44009890700520503803211030080c1c0c8a40b6240f070031103145410708155644184007505040d81c40301000791045400d0303d0500e454210103176040e03448004d04040b084c15a0440c2000000f050b80000d04680b040145419005901d806401c01340c1c2604c01b291034560016541c90764290452905038058003041d84550129108a0440d40c04203240c200705030303031040201d09a00d62040e0f080c26a081103541e881040621000c0c8030a842c030308000c20b641c0111100204c0c0b050040443d80b203000c100c050010300b0060b04018009001d243c18065203d0740550541400385003401050180690400d5212500034494005503185949130f0720b0710100001e09542000079809a81602c0d00455810054901e10145a081c80c01d13131b40c8107010018205040940380c0c00156410711a40b42007a94000c603400c401c68070440404946070f80d038040101c440030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 468158111 1250 468156861 468156911
    0x2160221010614011236020301021b01150608012c04031e0509150903120f13050a350d030b031506090c2808040b0711070504 55
    0x742c41d00d400001c156203c03514403400c030302084c0c88440c141d40c41c25001030140c462019504c0c00070b802450110107801208116007079440d00001c60f04251124a6002900360b07480031800c1c4c0e90f850880766258062800a00c103000e51000c81d10030030b1295a00c2c00c0d0003d40038020511841103411041c4a074421490401c044001e900d5010482d00c0e08107162500d009044003d5944025080000030a007403007180380144204ca503000c8005141d100d0a8848021001e0300e80c6c010142c1c1900340c01b810145001c0c3c0728144018050703000b00703010881c1c6c41d8001c0c04440190301103560b00076071095405560401c0341c00f007a45030091b01c2e103030680420031700d1050075106070f1729040400000306c88504c211440d0b0003c140d0f240c0e01500020760101c0903904e400c80d0010810710f46142c01c2e00c1c510740c000c0350013020a56841d9240014408401c0e4080c000c4a0f00d080100706000c48104508407601180d000b03000c02040040300419998001114100030f178001041c845441d43e030b800d0602859000d41d03542c15952105a02155400844e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 468159361 1250 468158111 468158113
    0x80703120f02033a060602030715090507060801090507030501030201140d060f090c0206090303010503031204050a080d0533150702060406090611010b0906010f030f0903020c010e0402160221 83
    0x58a0956141c00204134099026200104184d080340029024142c00c8403c164000c50a0044c10386071072504054507000300c2100d07940d4194036000180c0c184218402415a51541c3d1407542c5040d170010269100200910308141c074100046c801030b0780243d200302c040300001030703010303102e01d810740141c0f0082200d900040c200010038880020103030b40076001304003810a0781d42a1100f035107507646a5541c9000c01c1c0106a032542003806024020704a08441c0395106010314101c030015205900d4441c80c81c0e011704903841c0601d485104000d40710210542d084503142e903049040c4040208001d141402c1106616458418000300020302ca80304c0b00c0100f902c842507002406580c0d02c95032003001502e0129103201e44000f04a9603a0742d00800704061080d2401d13180060440300f07050356000d004490025502040d182499914109a299984184180341403140310f80c00070013803002c64000251036980341b203c170244102e004004642d0720700403a0010100c1d10743c0c180d44628845016049101c080c980038090b002e12 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 468160611 1250 468159361 468159397
    0x50f070b180c010305010317030408120c0a090b03061302180616020108160804030806040e0a03090509060a081009031106041a060108040b060d0c0504060806060901080703120f0203 79
    0x100072540380c440d0610141882200d85600d01c100041d41030715000d210243c4640b064070302d40c03104004280025031b4458859220f291801000740036903407049a080d00c20b200b0515003c50707010001078200f20604040c0c2042d034520ae00f5840d0040004649903010942c084000d5004580c60700b84901d00076a0354291072000308207a4a440d0315220500010411a8040c1d00242210b80480c8414207064210140134003190341e004410717900c1d0b490a64800c8000380495402c59914258014041420701940920601c40c0d41c0d428106031500080025000016000600c02e242044040152810010b000000c5032001c031000b041801301c80c02d00f500c1d001452140304185004e09130804c02042190309403514480304145a90100e07484150046500181c1186c0042206a45201081e1103282000012403114442c00c00684d0883d00c40002c00c0903101194000303030107070f80844140b03d13562030500402c5001d408150700400e2114a103890303014039074422540300c0007408501d40d801e59415209008880301e0b40044140c0d510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 468161861 1250 468160611 468160621
    0x30e0301020f09030c0103061203080402030a15021b0d09031115041e0e06090a2c0c010e03151b04080604110102012a0f03060f0f0305070909030f050f070b 68
    0x1845501c03c0d080588640550199104158041c0c8550f1742038500360134a0803000c141c165016210100098410b980c5132043c44403200018003610340d440e856030f00340540980c88aa070b250080001d1900381040400ba9000030a44040580c0c2c411044c1d01244d0300069a003c00d01c1d2001c000c181d032020691180c0c01c1c0c0d03100014000c111001c041c5082201001403000184020342c0e200000d152410041c2c81490340300042c0800315030304512070781207401c204400c401000300840e510b552603410f07820b222071400215045105910030f90368102c100c4031182d42c401c0e00940340114800c03060f1049100010f142e5800384500c040703004445002c0d00b094030003a20b48181121a60300389030421011014441c6691401036007011580d2200034000480c842100300d803040e00c84804c10480c0c030280c444850000440c03007091b0791030394002940340700e980145004105000b10310100ca41142016403c0001e03680000480605080034071000941c0410441c03082071840ca0060f46a07003031207460b07812603c92440060040c445203070a005d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 468163111 1250 468161861 468161887
    0xe01020d020604030e06181201140c0403020d0204020d14040b1623030916180605120601030803090c0306010905010501180b090108060d020414070801050a0b030103080d06080d0903060f1116030e030102 88
    0x5081c4011b1196808bc0c3d10001c403a0480d2007180002904254940c40c500014100343c1c0150181200c48000801c0b02d14031154510340d240c00445003603070420310355801d0109100c056440025040d00620f4409044c00900801c5481440c620b440c80399080310010001e00d52001c103209903003425054915410240c1c0e6110304100c04e0b00c07040313203403010554030385480002e69107049001c40c01c686440e04041c0c0150380c40d6403a810b03140d03000144483c40c140106000100329503410f000145c0a0701204130b000909504200004101d96120340016690000074081400310340e684106031003c44009292408469a070f0901080600014110094210741051803880c0b4400c410706c907061082c0340d1130361880410fa80c0c500c1009503160162042480c0d01c40c040005002044c450b030001c02c03201519580101c4d00d0b43d40d0b0444e203403400c800b0182a20000341000da0a104001d01409681e00c460f100c500c05020884030b4403034505640c4110542d41d90b80c060307043e600c0020180100c1115134a0036008000f1501c40030101d070308c6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 468164361 1250 468163111 468163121
    0x31d121204140f0d0f0e100c24060801061e031217010603020d0b030706171e1602060a14011403010e030d090c12050c01051602100e01020d020604030e06181201 70
    0xb44d40813801510003011128070600b440894003200800411102c4502ca07402e40311078940940079205a01070b43d54506648000c0922203070030030030480000601900d840c0c545400c480703e80d000a015070b000740c072908a034480600240307030a89821840d42000b03481900000d0300c0c400c12660301c040395840810000521960035034007404e003000385400c0030704c0000d140a0401d0740310551070140e00c01140c03404c1906054041515000c82d8040c00d101c1070408a850b000c1170054026004940c5582d04140700341028000c070b0b070f040c01031507001902c090051080c900c0c00210b092101c0e0050040d0140c1918841010b4002e0383d003504580c1d0541e45890507265581c6101400c01c2c05012800390580d10401c4990000600c0c00c200f01941e16042c0c2c1000103804c440540000449050b40708000001c0c5540c2c1c480b1054016a82e18480710482c2119030311000003500e13a040000e0304141d42c91011105640140c0104000309401c20111803860508461f607039035075410005255001d104600d603d40c0c1021a800f2400f20043c415844 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 468165467 1106 468164361 468164383
    0x60d020c101401230603060f010e0a0305010c170f06062b091709180a0603051632040b0607060c031d121204140f 50
    0x194002d803407000700800e0b440102c0304010800074001803503050f0000c10305001d101048a89070006003135404000e044501a0400c0b80810f409a8824504801803210007450700c0e040540740d00f801c0313008140c60340b283d00215103403a42d0b2031030100c0b00341180381c4504038402d2a48069910b40c000d100058100d92281d070308810b0b070a165002004425082501030030148080000c036070985040007003c051145080000e9100204001901078682101c150700d00341901100c17081503110036201200500c5e103544041d04500550800071890801801c0c15001ca8220355091003480c4060040c0c14010f04030005090400c44201c02c9001c1181845d800c04130b0030344001052541801101c3c0c0320040ad03101000c941c00c0c0003a80d03426101064089000154450218803402051401140542004984624a40c26074030003a90400201041021010080400c04403401d5441c1442e0f251502540c513880158 = true := by decide +kernel

theorem cover : BRFrame.Cov 467985611 468165467 := by
  have h0 := BRFrame.cov_init 467985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 467985611 ≤ n) (h2 : n < 468165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
