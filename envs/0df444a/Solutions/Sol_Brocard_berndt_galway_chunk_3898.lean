-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3898
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:00:08.432992+00:00
-- url     : https://prove2.me/submissions/4c5c2f6a-24fd-4ff7-8435-4787bb412479

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 700899280 ≤ n < 701079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 700900530 1250 700899280 700899313
    0x6080732010f0201091226010f060c0f0203060f2a030711100e03340f02060f0703180e04050c010513180609051305030a0f0306090e070311030a05 64
    0x200500c5000750b40d2211a19000039042c0c4d01d4000c2c00782d800b42c0c1d0f840c8181048500141403c42c0047c0e10002c040710450051080c86142d003030340f40846e0184d0030201d240060526221507048240400690b1500171141080309864a80c0c0e81d070386c8914080102485070702c1030310b035041404090712801049940d4081c40000c8100380107420038030040c2d40310720850711a160090b031404e00303540440d003159600d9040402c81142c442440c115648000820b41642c29184c04503010a0606030714448025118810004090080d0344450003124840050651010b40e5191507050251107204004850100c4440a036030005040d00717902d0301240140d9001d00508102c0509200445203600102181c0d490310514140008010009544ea80c1c00203e40d5440481c11601c0d041d00c000841d44014807943d00001240c100320000b41d03000c81240c1c020380302800d0075130034100c01c020304400410450f08600c3c1d4240c50001c1250002d43d0008114085a201c2c0004a05130b41c4401e080c0342d15440214001482544408002c0204128 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 700901780 1250 700900530 700900547
    0x8060d050c06090a050306360a0803040303110c0303010501020d03090b06010c150e010b0f030c01270504060909021905150c0102120426040e040b13060608073201 71
    0x4004020712044d03a00ca0000030b080c40d100703a0300510a04448030248154000e07000d110502e00c2008070f01c107800e040c24441d203240c07101032000b0700070200da0000002a0030180250f0000341c044100040300b0ba01e5514103500342d81c1d242d20a00485015100d680c0c00300d400c45100b4014001c030380e40d100c0c0e03807100b031303511440015200050044c008a0314124036000c1a11a010140310b0b130011301030b40500200f0070100500501010f5611800e05601907008500f42036442c1e600800356000030910b0b501d40c00d485100456111040040f40e401955005c0c3c1001030004000041c4d410152103a4000c0394040da4810b2801e50101c560800d0b2b00c00c964102c9440c0d14011600664240030380358071881c9400141c50881c44484466449504070350071074212114000401e6049480300030344d01c0d10059038440d00d01d000d040078083d5490440040c8003d082e5805c01c000640f1003803401c106100300b554842c1043c00748540b5814402c0c0c561b1014090304050401603a20040820003038441d0000590749110281580480c1800445d01900b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 700903030 1250 700901780 700901797
    0x70f1404110d0f060b0702011b06021e0901020f07060801090c05070f060510060302031504090519060606030b03031303030c1a040516093e0403080a08060d050c06 71
    0x654405a212401d40900020840351038a0400081c080c1c000c4049403084a00c0d5401008142d0424445c410040c0d0b088084081081c4c2602c1d1640c400110501e0010042d2142c504031454081100710f994281c9200d070350190403030704c50980a603003803144480301c1c403507030b4404c00d1062000240402c001007082c001554440c148190040c42c100d441c25502c0e894002c403e041040703089480f1941c43c020442c403025030000060207065113190940c91400c01c0181d550009440d025003a120355590700000040010400919400b00c0150b4968080080c150070050001d104620a0201207401c11800c8042031030040701712458208080000044582581c4007114500030b24041201c006800c07800c240d280303500062105204900c154028084035061842e1f168000a1a80c00b0a841c00e0410584005464040d08041c40d0140a68800002418246203007245e4602c0b000b0490641800010080700b03102d140f5000b060320b0482a104c0040ad515190207005103000d01080180492300202c0111040e450440010852032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 700904280 1250 700903030 700903039
    0x5060d02090702031e13080a0b190f0e0f010516080f220809030d1b11040627050c03010501020a08030703061d0f221412040e010314070f14 61
    0x1c00030302c0e45803108100486020701c0c108041100910504100031b0310340980504400360040210a47d196040001d014001484035007404090031100211507201c40098180440c1c140400902800119119508003503941d52550030b00b1300064204880c81651b039068070640d40c035407807566503c07074011500c0b00c00641001152080c5042c002000f50300035001c0b40419000d900500e0380c894514041520b0300b107001c42c0348070034400381001101c01c616152562042c06070304200900415422240081d0037001550800e40000064100601034420101d2035021413028681d4208165240c00c0e1200d101d60000344a101d005034000000c410001f001c21001c0e60b0400c0a40c01d001c01e109407a282400203115005200c1c0909003010420001c1500341a610303a6000052000c140100401010318102040c0c81d005000d000401e1601044402e1981085268a000e01d03200040d0313152030f2078140e08100c03090284000c0d121a10100d841602501300400c440c02242d2107031101440507403408003104444c100b03d90344154803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 700905530 1250 700904280 700904287
    0x30a150305030408070914010605070c03150b0a09050c0715060815090d110309010c0507050d050c09011a04030f0f02040903050915070203060708180a0305091305060d0209070203 78
    0x6698040128406144038070091501d540c04d1000551401c1010762107180084e0402d4410b00440c3d0065060b24151203441c90040c2d9240c0d40c0c0e0512402d442d003190300042219844c0300c0102c00740e401547c03201c1c2c40000c040310400300c40c0da038900e8203400303940080d940081150010811880040d0700c0700c1c04084072241a020210f000d40c4d4070500c2171704110545002c0e58072801d8040c01c00840348414820a42403040a042000100a10340b017003d55900030291080c3c140840c54821038103001e0300300020303001000018024112070003186446500c52810381011802581e44100201e0148a05041c100d0701c850000390007410286507468540150302c811030300b0740e180000c0016070390160f00d40e40075200e44d80b80a510f900b0303a00d07009041402100007040e0241840b040d024840d100040e41c1c0820f030702c0d80007e030900d03042525403280e0102c00280800d443c4000d030710348034442c554406c068001c40076220041044680e00d80c2d480d9902030100c10703104100c4906600005c20b4640d4401494401405074009519104507400c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 700906780 1250 700905530 700905551
    0x18040f050111030612010c020703080d06080f030405010f05070f0605040206120a060f0b040b030f100807090e06100e0403140c07080a0209061909020708090913020a0b13060302030a 79
    0x71909008802d84204400100f00201030600d2501c0b41800c9808030000c000611403244002e49400d29400000c10b06180001c204014094076041040a40030b281e054681140c0140e03d0250f40703a11510555021401d50080c00c0d007200d02500030b841d03c41d608110403039020346880eaa01c0d401440f00502c12644880c06000c42952680071003603261260f0054400020680d003058207a48248010307038030160103018100020701401d5050010359030046500c41c1c4401041c2c0ba4030007a201c1d000c0761038000d628948146003002400c0c0e400f036000a02c02ca0308010a8924946440c8603094002a00b80030b6030903540255004034000130300c51248080700425103e80d180c00e1451010396603040040d40d910045159112100300d005610f8a00801074016104581c0c04000d296000102030f41d1128900c0340c610341d01c0d80800e00c201803140e40e4040304c40d00403004060a209150010303522003004801d0f071007030f80550798401300412004051401c6030480c031030110010940c5803800100300c001c0d50000b4040343c00c06845000200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 700908030 1250 700906780 700906783
    0x100c030504030b071809020a0c021207120b0115020606010509060903100e1e01050f06090408040e2401090e01092309010c020f01020901201c020d1d18040f05 69
    0x601031401c45da00c40c402203501d280b00303a01c1c0c8146074124240d802d00c1045040c094942000a08002540c141c0780130144072a078280c40b87c00c1c4005039000c030a0b6501414580010000b00d0080641a1900b00180587e2044e89040c22640c5040450b10035020684c00c000d143c0d00d034544000035003004200141143c0f401048188850140c84e800b00ba0301e00242e1107155808806402425204086001c240c000c000e00d1900803842d8450310000303444940591401c0b80031506114080c0100e401405840c4004c0100d07042c0f80d120340d9001e84652030084c0b005044440c2244407580324242e0401140c1814051103031030b07400c000e07005000b8200706165501e03003404416962140044404120f20801000000082c85088442c010303003070050300d2881106a91040001d00206e0381c1140007400c0090283c0c004040319001410b0f40c501c0c003070429019480114668000c5108207a0004074105076042503540c1c80001c40701c05000b0000d42c2021a10700e6800b41019010300710000f030f20030340c959101d0b00402c80c1031000c43d515201e0340e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 700909280 1250 700908030 700908053
    0x1c0911013002090f0409020a090507020715091d04050703110402070c12050c15040e04110301241a03161809050f0114030c0d06020409140405070f05100c03050403 71
    0x40c00300c181c02103035103601c80c54a00b0300c11204c00c2c41501c051000e881c003075000400d8800c00c0d0040360001036030303400401c10a40c402c00903003000c3c4c6038a4002c1d03100710403802800340411080d44110303d04140203c1d0403805240440c1c070b260b4040d551003002050b8030303400c5640d0502d8000c0d03c5069250019420f009400100e20440c0e44076004106008000a10003118200581024541090310340101011b07800010340e82c0d1788204684c100e41441422821984640c606034000f880015400d551641c03c001191503402c0a0705001c1c008c2403113210802c1c8420355503202d203c680f400d414003032840501041c030004002043c200745030f40c490000c40c41c6c01c0f5007210000c2540d007924a45500700740030303440c0d98900700300601c00d400d01c1c42c90140c0100c1d021112100005000a5564089a0342e4540a140401d445504000aa4040e07501404212209001c400c0141480081484c4100d905540c0ca2040240000d10303039021281d0882a1100604401036070503002409171019031650a0031802c010040100001052003003148 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 700910530 1250 700909280 700909367
    0xb0307030311100c09061805060f0a0f030b03032a0609060a0506030a0c0b1c02031503100504021522090605040e0d1d0d050106030501021c091101 64
    0x10341040c0b601416180c2d250000c003a040010080c40e0142c440111500000824201c0300c1a14224030342c0820400d1001441c00c43e5030140e030b0400008104209410301d14006421071181a6644c00c107040d02100c0700b01c05032408c1120311074042e00100000e140031100b107000e1040d008084440c2010041e0701411a6151910494810704e29401c07810a006001c4440d000c0c691300140d045000300110340707050b00d0394000003450b4407031006c00c40400541981c00d24140c510f4210000d016910441d140d241440ca00401c040062010b903210340510140744546012034071072107000f1900501104240b05011054080c42da11083c1895000b84030441d031840b0100c030070078102e00030b1b04000002086252507c000d00c4150ba00901c2c122544c0cad00483c8010a5559101d1800060b940070442d03242c0007600324a0104802e00501b80d0003401d00d508043c3c0110a0100540041014255501726880e003141801c0d420000c0307480d50440180f402810b001402001e600c13070130b08406034040c1019100c0848401c510920203c4681114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 700911780 1250 700910530 700910537
    0x510110f071a070305160206010302221d0c041d0a03081b030a140c0304050c040c030e1203180f420402010921020d030212030709051e180702010b03070303 68
    0x7001b0703242d0384400036003600c0801400103006550456002070000380001459640d9007a040302c42032010945a0400703285400c8441d05401c03440e07050401c2036103030200052114052424498101045d021285800030034011120290444450994007119624005880031755003040f9001c491109003440d100542c0940d54001002030703c80c0d0a8040080786c050010090410404103008110200e88049156205800111000a4001c6809006500401d41500c0c00810780c800d000c0700c0958a580742c0b0080d4001d08801145403000380c0c000e070509903201d600070311103000c6030899508003030303001c1245070541c80c1407031255111b150041c4808075400000072a403070060b00c80600f46090100f50358208894070082c080030302e0825003081c07031030341400d81c090710a80c8024010588030585005141c4240300c1da00c14607400c000d01a50701d08291500070a11000340c00303028070854610070440340940d10801d20307007440c01c0c005e480032002c0100811000140d98008040505554032068040600d076424003031000078611030388 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 700913030 1250 700911780 700911791
    0x3031e17091f02030405030912160303020c030c0307030807060b1f1e0906091a0f0f04030611120406090231050f220321090510110f071a0703 62
    0xc030070707030050b03400d0300458545600c104248400304202004854802c0d00c140c40490b19a0484040189081141c0038a418410040d08011041590224100c000810110100c03401b40001008154036980a884018105002003010703500140c505d1304004403400006015510300801900c03c09408219900c00000088800c0b148103444000908207514000d0300d460300550050510b00702070841081405040101c41c1c1140540d60200301440c1100e000b0390f000600a504c900115981c491103401a00003103c400c4d040250a2107060790060a444000036491b0989000c8c0e201c03512402c00820842d0801c6ea00600108200d600b10400706409501c40c1d25020362440381c004246140004955024008514401d40c0d001807154088088100900c5402c0c0380c181038003900e0042c9001d4075800758516101c012108400842e990f40a410746c00780035400d0107038040e40c00c544085102882103808d40101a82c00c41741c2405144008130702c803800707400303070328440d0a100482c90321400070080a00400c455800010340c648 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 700914280 1250 700913030 700913053
    0x310204090c08061e0109021803070602060103031704030e0f01031b120b06090f04020a11070312080f0f0106120f020f0c0f03040605180f1c061503031e1709 68
    0x801c00950703c01019549080c4d4015044190725003001c040c030a4414041d00428111090015055600043c1c10700500b100c0406580e940013940b41c010034070040d008150000a80a159141040c080340301d1a85a55255440c840010400c840303081341140003410943d56114044a00002507110800d0018a0302d0381000c44030030084100944078404841400344e0700501032215540c4a0740b0010400c9503044402507100c40e04520100e400e024850407040c1c5a11130703100000107200d05840c0342441c0c220341e9903a8030740a940b9003074041d0b010881500c1c804800824000100062407103005c3d90140107007880c3c00032454202c0d0b8070b44201a40c201c01d075451070f4002e001480d80d038108000c000c841034a0540401450415141c040050841c1c0185811040220f4003001c1207010399840a5600034050300090040250b14070881012403005c1031280300f01c07502464980c01014210030601f5a108490381582d0707007070041050303c4a03140960703080e80b001000d0040c4c03248641080380b02c28601c0791240000000800924000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 700915530 1250 700914280 700914283
    0x70c050102070506090d0509060403060b060c03030a0e240601080726060a05090c0a030510050d05011505040501050a0920030712061509090c0c080c0f060c03310204090c08 75
    0x70b21500c00607c0801c2007070b0009500d40e0300580341100d402401c0080c5030030803800400c0c80e9219074990304a9900000040113000c2c0c1d641d601568030759043e402141e102e480d81c0450745076580c0c900905c107541c9815000c0000e51640c030981c102548070b80c0528222004400309000c1031802d0002c6a0304411164802c1c0410101d03041170383c070840050034229002c03c1c9504000e404c0718501e1051401c0d0100300340d241c20016400da6a080203286c01010094641d100c103040b0740c103000e4000c00e204600c44120003003c80e00010207141500503d810380301c004002400c61840c01580340014042c104000b90300201c1d01e500004041c0d50940030390b116610b5038075160300c80d08104c10110200d4446410411a02e0304003c100c80045520107125000d8074a00c28001a0342001104184c400080c00d61000b030601c0f00000d0004240c01002c60702841c24400c18003150107540b149800c40707200380022110b411031004e6040074180308400c0004001d110b040401a2454651007e40100e03044c3c5000860503030324400c08020801150300e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 700916780 1250 700915530 700915543
    0x6030606020f1204052b080901030b0a080c0105070c031e03080a0e1b0d0b012408090d050924280c021504120b0105040606050a0e09070c05010207050609 67
    0x1640c009841c4204400c0083c41d014003541c0583c034002c0780c4803801d40c04400c65107002403a18940040750f4a030b0140d01c51a091502d80e0120a40ca40028108645154241040c0401d202075650310341c041d0408100c0c000044490ba080348105981c1c0c03645261000011401b003105940d500801c02c001d00b00300d10884d04016040c28400350014100a19103400b488a945010800458400300d04440700d030304070610b000060305160030700b81c0a48401c581000000f81c0f4100c43c03030b08205000741400340902c000d09042059070000303001c903007004c295000348611214451151005021120f0000e00d41b0310101d0311400c4000741030340300129038209120001031181c0c0c1c05003240105502a001c0701d20383c20344008606802882d869003200024000c1900c031201c920760070444420b440140c502c080b11005022403508280740504028429680520314110b00414014890401c4444090f41510b0b0780c02241403e030184054010024009010072651a03840b000042c000c0c0001c0102d01d010300010501c80c1024800b00f1304200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 700918030 1250 700916780 700916803
    0x151a06030c0703080c07110f12010e16090b010504030602070f08030411040f1b08090c03011e0e030a0504151e020606041b0c061a0a270b0d08030405160603060602 71
    0x110030b000d0040000d00301e03000025801e5080ea05908c641003500c0219008034402c0b040c071840e550820950305144079001035440fa0560b000072407000d6051340c3c1d654500031103400b01c1d0400e0018600300320a00c01b14416400031700440e88141d2694003040c041c0d4591204036001610204c40e103000300f604141ca186032601802d050000e000104004061000c40000403035040c00031142e00303200d00c00001546624091100f00f408140c098000d00c65210308041380b41900c04116094090300d850640070aa0a080c004207594401295886040c075250801d001041690101c072156010002440c0443e8094002104101850792040d001043c40d03040c21070400050703c2520034200310100914481110542e4004901b000e00c0b50008d8000413070795603e40f65100c1c40b101d000d50864010906410025010050b010041142c101800340e5040c0901d8107034006090301d41010300c0030391240d401400240403034104002190003d02c07600441d43c0c036070075010301c0000c461029840304002c25600c5500b0800c1a40510a912040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 700919280 1250 700918030 700918051
    0xf0f0a0b0d060b031003140c03060c0903100c020604260a080103150e030306010c050109050a080a081b0d020a12060902031006022a01140d020d0b0607151a06030c070308 74
    0x1031800517040760341e4110707030300c0007800a0030740d51804980d40e801408504c58004026064030442e01d401141042181d0140320780f01d00a200324802d5900a85042c41103821710821a030180201e0345a6480d98941040340020032856480081e6460f00400c0012000344001d090b1626456400e40c0b450800701e2030600400c5003003100034201a90346061000c0401120b034008c0b400d0034843d00280145c00e01074010104070000500d01c0c443d01300c03500300340501171000d800040050f40c2d40801580c0d502030000d60b1109106840400040144842001c000194000d082011080e140180401c04400c0c1d01109582d0342da40191400356000003400306050901801c180a404140000e0010803150101c0800400d0480c20b1041c200c6003801e09440c40740e2290322803000107030714403080356101d00140460700020340c055120504801d161060318542d0381001e00c01d5441e095044030412445101c1b5041c40c2010307041c41f250f812040b03240449031001c144d5031040510300490f90180420b84440d800e241c050181c000c080c02c00c8080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 700920530 1250 700919280 700919287
    0x11508030a0f030203091e0307050c240304080913060e060d170309010605060a020c0f011e0e04061d0907060806030a150b0d0f0521090f0f0a0b0d060b 66
    0x10710b400c40500b4402910a250050b90b070742d6825945800d280080e1100100c901824203868100e0000101600308103000b2010340d505130309503004201800706400d50082809074040907041c1e82c0c074140310240d64002e00a0003250314201c2a03400144003000c490201001e0300b60395550501c85240c50140d02580030b001038540d8006102140c03210504100002d2000d0240500000007441154007904032000511001d0300c07081e264400403d010f5140d40c2002a01802031440480070710980d0b00c074034102c140c603452040d071640c40d89000b06000c50f0b900c0c212200c010303041034a07454001004440e8810b47e59003178035034100528560601440c0241007088580c461400c101c0614140409030350f020074000c0d29217501200b01c1030554043c40e2000060030900705100c0c1d03c100c40c0703042002445607a50310400440d11400944400c020144c1405900d40070314480c80410400a2202c1000c81c100308a000c02041801001215031424140006003020010b401c807102c41600071481d120749000d20f002d1342016110450b0b94030708 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 700921780 1250 700920530 700920547
    0x501110a0905041d0d080f0906060609040e0f030c0a0302010501080706090b0a2105160f05031b070203030d1506030b0105121e0703060503190b01031101020f0f01150803 74
    0x64071215014030b0b4070460769405070010b0f02201e0030094144030007010070307641001014080a0312400003210910485010040010103e04010614900c9100c0c018200390500400000b0f0200401d180200c0407c0c903c1101f0111580c0e92007000500805422507004001400d1146402400e50380e040e4440b005a41c060802401042c5c2c100c0d08000a0760800d9080903114843c01001325045030768840080c11042142200303400c0a00181c106910921010341458400d2a6420044a5494514803040001642400400c0d94225201000030b0801c40307080f807003404c01d01c094002904550094030b201c134081c0d541c1d00107000034901380081c10006008604040002d070103402c001820a00c00c40700b110105070300c0c041c000760000c0000c80d42c2224a032480d00140513075280c18280030b0020a9603016480c820306c214074100052440b4103c0c08218075a0100e4070710f08607440e5942d040240c800481e580c6055010310010301101791010070901201501110010451034014010700c0810f00d030b2908240781ea42c100308100c04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 700923030 1250 700921780 700921787
    0xb090106060e06090d0312020f0405011b0c030b070c05060c030603070e010602060a020f07050d080702010b191502010b090f0106080105012f101103040c0503280501021905070501110a 80
    0x2138040c041a241154500c08510b01110b07400606112542c0c103520129181440c0d16000e00a00190b500c01e0707c0c0c1007a0140305856040030700d00019001041c40c150600c0900c0010785c05071806401c84690705000b0f401c0b0403036642d02c0f403d101044a08240290b00030041060b640341c204560301c014030f0300381036080c41541130103c001c0d215000205030000d1140c00060042d100a07225044464440d04034080d01d03c190400040245658001d46e505c0b0300543c204841c0745100e180078030751501322035500d910041c10180f8000c04030841c030044401c102e095560305c0c543c80456480f0105854812000c00020307a4441d030400c50b01074459071040c0c0000381000720482c043e100d008001c01c03001d420300b007100e4400300d42d65404840282c41c04040501c60441c0c1828000d509595424100103180618420300c03040300100e841e64180b40c1d0318080c2c00081d8030516503507184400c0a00452561100c1940104009841c01c44150561a014040710b079010340001c40029010741400400c3c0b1420036090074010155260017003004006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 700924280 1250 700923030 700923037
    0xa050d0215210c210712181b0602060901020f040e100302031002180423191a09060102070302100e04061e1d0105090103080309010e0a0b090106060e06 66
    0xe80103401c0003629040701c4003a2202c0310154282d6104a0682d803a04a0f03200d40c1d070350465072070313071800030482008510718808116085105a40e543d540c910030340180b05040307000d080f1040440c050910302400304408240c0c135180541e60140d60b450700d50320700c40c6080c00003842c201d401002002164814042c40707045000c1c1d034040720110f4860020610070303522018040c5800301e2150740029031501c680c003160740010340c1540241c500c0c860308003200c000203083d420501060750442c19446a41104007508803000780000c00e80c40d81c0202c429502c20541c0020403820704203c504660410181c0c03424400e40621900d40803120346d6010780d00303201a0040303a24650120b030300408151400403e01210003d0002c9507250b40d481007004003110014100600681d8060f080c84203039a0140e10a4403d490000403c0160781032034040c101d80e40a03090b400168030303584810050f9000500b40040a540319401403400020400c1400d88450154034000502c1c00c0001c502400c483e19944141e0502840d0450091103652306804d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 700925530 1250 700924280 700924309
    0x8191812050c03061611030708120c190302070c0603140105011112130609080f0318120307230c010c1101053f0c070f0602040f0b090a050d02 62
    0x1981000003890100c1c144409201420f8041c480c200c100110300711131010601141c40c1507154010019404204191a44036029010f01108020419545814042c2c12004c1d40110400e5000d42040103482c80405400000d000942c000398001c0341e130206112094054000520103805c0402020b061040350030104501445941e050104035034982da52004188482200007900304801ca07916000629540c460b20f005000b901c00203404800d01140d42c0c100022040484801040154145401505550007041611403e983c1094030806032145004040002d4000c1620511400a040703d41030844000f134a03030f41141c11516800340700c0309591a600001031060b030a800ca00308042185012005803214410707500c04075072007407a800004186001c14080402c0c14103200440b40b021005c4081c0034880b03004141c81e900305040703007007051800240400e1100e0f5102441000c001d41030a5a45421134004545680500849000002d0300e2156181c8000c0020162070201d404c401280d416401080791060008c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 700926780 1250 700925530 700925549
    0xa051504090302121c06050f0901091e0228050a0e010509041503151835031602010b090f0c071406070f0e040c050d110d0207081918 58
    0x490002d00d4030034008010040300702c0b000c43d0794460f1124041e0020300000c0f107100300c00380d141400108180c80c1180c0340c0d410004001300001032503428080d910340182880c074041100580020110003440d0703828000b4100b0114020400581145009040400c440c0d130b41800008202c81000070364036048e001103040c040044280792964032014590007045c0102070220204014100d1884000100201c07003441c91500c40c4405020b0100901d040401410005101c0004011041c85440304c2c0c010b65204a206103624080030100c81c05440c0b0188000c5198415603d034101d403c00b441c1c0b0102059024090740c0145103054800c0c02540c504055411503041c000340c85110f14100029109040c040d618010503054010361060b44d11500f0b1031013014007150f01c3e1184820200f280000002c9146c40c0c030b407040d90604413007515640d241c056860b0302c44004001c4207403c44000c01003448000c9030f0030f80510181410b203121300406c1d940d8010300903616108540c1010294204404d04d4000341816400580342402c981c200f40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 700928030 1250 700926780 700926791
    0x40303150308180102120d0b0a1d06090a021b07140607080d0507020f010216062909060d0f0503030f0f0c0a050702040204270b06090f060310030b070203040305060a051504 75
    0x40100d00304070341c41403040206c1c40045110800b401442d403101015030801c854a00225aa9090070000c0302a080b005804540100000070800c0c1803200301d6036407017407440400602d0601124030044002500450b4046164481034052084004c86419400f070394808175046406c0600c0d0340d40b000168030841c2c40c0404560b444030085034426008010405102941000a6480d910a4503501200f2020208103803102800c04400c0052203421b48000064560958400101c00c3d0520080c00405a00034000e42d07001010403003080c000c5001d0700c190b80e20091007040510366031700f03020601c2c4900440140441c00212240014800000d120000f202e403c0c0d01d60f420515114045800010024007072944000340c00200400c8480c00806003a100c2030b20034504203010448001e400307040c001940203040e0010742001810842103418035021028540c0301c0c0792484d054021986030f030b50b0b0440c188415280f680150b40041402c0c41040028021103034004401700301004140780a503076484e000c010307001703a4030b00403035807039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 700929280 1250 700928030 700928077
    0x50606040b0a050a1d010609140d03090902270301021603080a06091802030115081518030c0a030f1e0c03090807060c02030f03070b0408130302090708040303150308 72
    0x40070340c44001c00004004e500e1282d43c5104540c10020395118202d000403243c0004181d142c020a03545060b1120310800078080480351003440000f4907960b4080e0148034010b080000c1c0600140014543c0040c0b03440c0310100da0802c010134a554501c4051054820b900500c1496007880d4070225240714140c1600d060521500e404e0800e4000300115040104482d0410207110b4402c0340030018899103034401c1c2c0017008080100340d01c5c2c0f1006001070140405a40140018042108a4204050f0030640c000c6040c51080010000c1920b1035104620204003034109696000600d90007030380b042c19031405401e20003140c0100021209030201480d00907030038884000111810305203e405440007410410707013151030b101e0302c4500107403c0c2004042c0407032181c801e4100b9081ea0641c0030094030384441d40011280810f84407952244040d420016018034070115014002006d032f59400c007403500544132038440c3c203844d081c10b06000702a5049950003111030180300400b04005602c40045035404800c1420359180407068 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 700930530 1250 700929280 700929289
    0xb040213020d1b1e020601140f1c0b15010c0807080c0d090f08070b2b020403061d0609100b010309080309010510060216050108101d010303120207050606040b 69
    0x2140c0310040e04610f8400708210a4400d904400c0d49201c240d241c002c107a494680b03004404000e000e4080300160030190041001980d40a000100b4404c024221034004071400301141240e004424803800b00c0565000920522441d00d1744140c10410200c0002c41d001d40800018002d6075900d8002000280d000a000003032040c01004d403107003040301d00c007a03c054400040004107241038901603144120b038a030100041640c00007500e00103c030b22502840741000080407401c00407804014000010303940e081598581c1102500c000c10256101e0540050840e10446c848031317608002e0241503d203075010000340041101d0001d03a0400b212414540460820703680c00049000d000d8441006000610120503ca410007040d00503902c0f80c100140d4070089241d8540c2d08070395030361034110524008000c3c4071040c000d41d41300704580307540300007000b2181580035640d05a0491651210a881000000c0c10b40184201580200203004d080c00d514819030409100d03464003901c42d02c0150549102e2641c0c0e04811405845 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 700931780 1250 700930530 700930537
    0x80301051e0415050916091a040806011203020d050703020a06050a150e0429070c0813030302030c010c030c0912050a0b090d08070c231c1d0a030b04021302 68
    0x900b00740602c0244002d0f11580c01442d0048910402c00c101c0001c0d4840480711540f24402c41c0d5a41c1d8489803880c0c02020244a4803191024145800400005c28810810000a8020200c0c200a0450207545040084c10040c0c0d400c24002009001c0041c1e4020035400160174489a0b0003d800042d1070702c1d2401140010454070018021b000c4540000142d5800c280070040d1041d4021243c0b4044840909010361324800202d030441e40e48103000001c2203501b44194520350398039100e40e0b8110305c2c0100e01008441e45615a600071401030340000b5003c23440800c01e0180f04820716032410b0038024004024005401c40c030050003003003400310840c240d600500108000c0c108205802080d2203d00f130400382c1540362211b41a0104d180481c45480100e641c0500c5080e5002c0c006401c42c800070801c0303488a00c0c854052524440104c142d1154402021001e103446414540a0905480314141e5040c1959507070030b8039109103903d610800030f0030010408141140040b5a001d54116410700d807a1510450a200901 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 700933030 1250 700931780 700931839
    0x405042301061a0403020a080c010f21151503050106080a1a090c0301030c12020f3d030e0712020103050c0d060f030c090b0117070219050706031808030105 68
    0x2038400c10f1000880c0d0b41e0200030000ea9009070340043d00c40d62500e4a1700e50320807018840e0340c0000e001d60f80054450b0b10a008000c10080010006900c0120303003804d003000d842c10580400c42550915104200b03408000700d07621a154101c0c2000c0c050340d803505001800e059130041c0040324858441c441070715000070a4542c0e0030040b00042401015080403004200903810902048805211580001c00e490b030b400000440c1d102e90042440d811032440405000c0b00151b41812404852203802c80380c164801c80e160301e41d040c0d2082c00c0d10141c41c802c000e9001819100c912851620a401940c818081c80034040000001c8640a0030003080c0751b11003105559591160b450f84841d85842e01002140070f00c0300d0302941c2c048a028148900e0559103482c7d4250885441188080c0420b81110a80c02c1080c211075000364006002d0040d07450041c0307042c55101c066a4003800440d880d41100d0418880c1c41d8141c4510a1a0341c4901c01141c0f0800c0c296071000c65611041c0261403084044102c6d83c03040010340101c044084 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 700934280 1250 700933030 700933049
    0x90c1709010b030618102c0f070308160506090f06060a0509040f170307050d05061017280b040c02060402061209010b1c0308010504020c0316060f0912020705040504230106 75
    0x107005800b506c15420140ca00c0c1c005c8580c1e10450041f5000900044059001c5007010207003001e10300d196940a000e5016107045007070742100d105410042081408810303c14907420014215844820001c182491f4000300601d01c00d4561345000d121548405680651090f4450962442c000c56810180c04080e03400903001c5d080b2400100f08a98036501c100030300350f8000b070080240600c3d110141000221508070030984001074580610140c100c115010494012003ca01c0c0c001d022408030b840300e0148181c0c112000c140c65140ca14984e660308181c031070200d0318600313071001c2c00150410b42c1c0080d90341d01c45c440c0681c11151213240030408005c3c003980010300c5581c000704182005402003411440803c4021002d078085082d00c0000149400c1c00d0003220074001d6030501035460801c4402c00405060458031050703901c0e990703520030503040440c1c501ca0403404030300071406448159000d64000345003170303880d0700864029030400041c0000541c2206c000c0c000d4881c0c44403030340b00c10305804060310300600190b842100d00703 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 700935530 1250 700934280 700934291
    0x203160e120607020a2607020d02010e030105070309051903021c14030a050117072610111e0f0909060619050a03060f030c050402070804090c1709010b03061810 70
    0xf1160001028404584507400702c0d8008256209594030741403400ea59500d18000c01c2012000500d080001400400d2050410412044060012908548c0d0403203141c0f020a03910940c100a0200c01c010700d0f0304c9450740b00703083c00300f1940c02d5400945807070221400d003c14080825882e9243c0380a061200c1c64114000880c075264a00480a0400341000f84113440e030451407038055a0140c50003180c501d00f034034511203480200700c201c800c451909110800c07400656000f0b1407800702c0050194007034100d0140e9841549500c0d040c0020b6005c1c01c0030070351041c0c506040010042800d0b640d2108040e115108800c440c3c01d0300681d1118003181e030302e20698000012040c08072014010b0b00340c10402501123428203503401c022090b156401e01c40d0f1810300e4080a003010004007010481460300b0b130000c20400c2d1185001d2418156110340c0320054800741c4910b2008945101100180e080801c4034440d40140114024001001030b00086600e600001c0d1120415040c000410101c1150400128600e045480810081d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 700936780 1250 700935530 700935541
    0x21606020313020a0602010e0606120c060c1b010c030e061b0307051b0607080334020303070e1c0204091106130302091b0414030a080304240203160e1206 67
    0x100600c2c81401c80c03081c80d20000200d05c81e0710520950300f000103048001c040d103032500d2040003504c2502d0307400111b080c821000364803000d8032294054606a200d040c000c108030411112040358482c0b07804040340c10090f02c603908402296208010100302e0380c080e0350147e510340c00c01a050860f403044590b02030242c40000f44007801c0200008002c81401d83c001c4a03028603108000401c1180d03c201c4401806401382030000c105182030a04c01840410a00c28a01c0343c0c3d988078255a050f00c1d02c2c4002d109001d80c00200030061074a401c00580003008904070342c0181501d01c042c0e614000b0364031340003029000b159100200002c00117166025030120b2002044103880b841c140654601109031400104d00801010b408100b078010100354913254081c04044035400d00741400e1001c0000300307114210740d6252017180608008190000020360140340940340c1505400c0b080842a40807090541008102c140304008008c001e501500041184286034070b418901d0301142c00c00500c01c01e8000502181c24000c4009104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 700938030 1250 700936780 700936801
    0x4060b010903240b040507211404080304050c040207080a0513091803110a0317040302030904020d050115110c040b040b03010608010203071805010801032901080606031207150216060203 81
    0x40990300710100c14004c2441803010f02050700c80c02d66600c0c000c109981ca4009140343c40301e20020346102945000100c40c100e4000c10381d41d074082031f036082e50105000001d00040c004244214020001c0640c0c041d407402c1d80c10340d950241841045a1b620801402040090090502c1e0300d588000f00b5100406200700d40312650b000400c800c003000224041542c0341c20f069040d0f240031491503900f51705a00e03951487e0f69212140991036000400480850000304a000300650381c501c003812502c2d4241e0000030305581000d61451b04240e081118100f80041d00e04c80d1041d518000034441407802c000e03074000c10440783c3e400206000d044803503074040e0705500f004804076184a05601852107003420340c0d50300680340d80885408211203d503010700c0d400202440014404984901d50502001c005040d016603c3c10300b80c00044003070380007a000503805412810902c48189030030030600d804081409803151034640507941324100032041c208001c00c11900412400e035140340c0500244851604150255507910b010003041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 700939280 1250 700938030 700938083
    0x1d030a02161a07020a08060403080103021002030306030d050c120f09181b1e03070e03070b04140d0807020a080607030513030804110a050d0c030204050a110304060b010903 75
    0x500041c49002101d803240150403032584202c61000d04190840012003030b040c41142d00210041c1c2e003101341c0110000d40048104a558400d0780243c1d2105e10380d505510400040d001444c40c1c03401150b2083c020300003603640c0440c982c80c01c6006410201c8e0f4030500901d58504086081c02d00540f04031b0040b1307500041800d20380080c10140c10803500a4076045486a040491600c191148200100c00001c070101c90b007140e8004024250016508a000100c00341d40210998000c586030400204001c0c07107042c0d1070034200300c079001411407950300604050034440c100c0681c6100c0d80203a0300c01c02d0002c188606100b85031080758141341c2c0282800502a40392503a0380e03524641034407443c001038584070000d03da24001165081815601d5a90980f55840da5140e441541240300c40007a44810b4030301000920340e5502e050401c8082c030802c0303021103d900c1d500400007200c0700206661060760070321001482032104207040f01d500540c04000024007803450001200c950010390002003e4540c0020b8500003a02c1d5168034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 700940530 1250 700939280 700939297
    0xb09132a03150b18040903090b0f07020904120f020c0310051003060c0203180a180906060b040906090f06080706110a0503030106080108010e010905100e0a080d05041a0c0d0207061d03 80
    0x1061301c5111002e00c0100d411908015001440d07280d800c1c427040100f000100a640c006030380d9181130061540005090b00d0080d5021105419486039a03050580c03c01c0c1c00000c911040c1c005080061781c042e001c039483e244d18804c1400c420744e980001072112290004024090f58205c0020040740d8120b140c00713903490344130300b61140d080101050500d1083c90301a507040c0560f060030403d410180d441c1032010000e00480e8000f11000d030b441d05004158508100060001010201c0c2d0102e42680f403c46007504072640e1902c42c0c8007040c06c008050000d07440000346602194000d00d040e0740d500d451041490308103100807800501138007000000003510b40d8031940f0107060766100d00080015003c000c0909089452907100100707281c104a000009481c034503441541e0888604003a6981490b4a550f8120603502440540c0312441e070b00c100b44806e0103848102c1c440003100054861015061810a00e90240181240649210b4000030b1490030060640c01a000b04a20b1248140c00d5507240010151a40c000605 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 700941780 1250 700940530 700940557
    0x1b0408160f0b0a0f030b121c20030405060c15040c05101e0e01020a0b310803060d030e0438060327070b09132a03150b 52
    0x8000c12030780307071140869031140f406460720148907091100950140c8112090f00760302403d01001ca4481d071200740012100c0110031000580c040c0c0c02000040c010128489070018070084468141c040e0907000030407101070310422208103441d1720643e48113500e0b103d8078001440c6080300c07140501082203400c410300350a642046500e40c440c8040400121050001d903540040200340c058040c2c4885802440003000503001841598130b0f51a06071524085218141c410144290705040c2c50031551312541c1440c82604025a14800407040a8880e4a5140405000d507446035800040090801d030045214180e03101007d40300748988140004409189920303e034071682015488049208140000030402e150301d04018603450640d1945101180001c506003000d4500080c2141081c040406c1004114018880014425952901c10003401180300f04d0616030b070f4045041c03002c40700c10060b260254040112090458620318070016038220060404032030340c4d407030440d0402004500d2070b00e02801403800600340b89 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 700943030 1250 700941780 700941809
    0x1710052d09070506090f0409030905040207050f0120030a050a061d0f150a1802071b06030c03180b0a140109020c06060a0303020a1719090905060a0303081b040816 71
    0x9050103007074410011744961210070030800e0385261815a105541c498024900140165224008241281d04c15002502c9581c001c41442c0c0c1c065009002d2400e081c0e0f42c00352800754843c0c03141d02c1501240030142c03c0b41078442c2c41d400010104001540328000030043c000c5448400c2d40c041d0b509908154040e104012041d041100040d80c501ea100910000307610040d002241c200d2400c0990071418881500701c04080d07408200b00c5001c07030f1510f4901d8103201001178805800518002010341112103040c1014185030504d0094001503400c8103468030b2035904070780d50b0101a03170780c031413041c0040070341106001866a0100011500d014554084d0001c08041002c480b010340307460040000c15040d606c03005005a22144415001900611100c0e0003540c040c04030900b0b1144454582c420307142c800d211b1a00041c5140c01c2080003040c9409002c2d04014103507600700b03860b13045842c028000c0c103005159a50340000300540b101d80c2e003040310484000344081c0c000e441d250483c0030752072001c90000b8400d01020039490b4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 700944280 1250 700943030 700943039
    0x70e1807062604021509041b0e0a0f08150c120412180f062a0b0604060e0601021c050f07110916021914030a030603030305011710052d0907 61
    0xc2d0b840300c1c02582c00411403000c002d055502d030b0103170381e00520645410549642003c0c031114035801354111901125129000703d0b40000342400101022a44910038001e001d00302046110000314072148104548004040c05644d8909401e80310320821030844440c104582c20041400212a030540c882c1d2210303503d0003180d40c107c0c180c861741002540503500c04103140d100f082100501a00000d0095601e40080400503041d240103008100c4410206880fa001250100400d5180901c141c40240280d43c15002d92410220b00003542c4048000200d108042c1040030380d00614028815030711407440d0002d05a0b034550080c903101000000402425015008103808641c1a10040060b6007220105600809002441c04212901407950303003026126503800c0501c54000c0301d0188010000c050348c0b0348004c1452451441d00401300e0300142d004406500301440030b0040d00303101146a03007402e02d07a00e0000c107617500c03008480c51004408034000caa00d03041d0807402c1003e4081003088240700b490346500341c0e12201d544 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 700945530 1250 700944280 700944347
    0xf010b09010807060516021504030b04020306060414070c051c0e1003050708150d02040c051308010b0d03110304090203040c0f050d0b0105091305120706150503070e180706 75
    0x25000d000c4c0801c8080c000480b04406182100381c00900040c80c114138602c030b00c3c51200d00c950068006451514095040205500701004035540090098508020380e000030100008081e5014005204210320101c2711b10074000300b0884854080d0980c000e0050701e8030098400742194800b00c10260142c1c40381d01071140302034020f10a4138860400c03500c81d00195650a41c00341d41352032350702103151f07802070625034240056211889500c804021603161140c1e101014028081e00c042c480d4403400c05031381400c08460842c1c44065034200480d616062244c0c01050600c3c1c0349056001d15001034002e075101100b0407040c03000c040384801c2190124038035500c40d99183c0050007082140d00002030311509030751004025505140352440c2e4422b005100c3e942c48441c0d5640ca081c14949289d080e40c00c000c2c0085002c8060010a214052400c110361244154042c40c14010980728600c900c83e01c0e0001c400326001403228040c43d01c00c00b1180c1d401c94161002203880c0c41c000341000714800803402120341549408100e070f190 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 700946780 1250 700945530 700945543
    0x1002030916091407080c070b10360209120d050910050c0a1e0b0a050a0e011803110703080d0203151c110114030f0403080906071b140f010b090108 64
    0x20f02c580140307120f40c1c40780340554107220054005144268108912000308061642c014002c7c10b10103000c4046c9440c02420050551900341040725090202400540080c83c0c56007540540e02000000340e1502d880340001444001c080c0500f01e0240551180d4000d40c960100050102c003074125000400c2c100c403000102c50b40e02036030310920a650b001ea48540007241468074846080391107900402e1550019030b4643c42c1c0303004140c2d003521420380c0720300612080e5103207030081e00303d90407540b402000011500c0000403c10104003001400348010080c4403040c90405008041c05140c000004036583c01c1040c141d0300080d401181d07a075100201010f8614650704e8074541040d035040b0400c589c1608000542c031030340d161924200c442410b000f50140c2620341c182c00c200245200f11018440c584180c039150501610009004085440c0e83c0c000001300028a90003000c0da403040c0a9049403030186005501d00380400d4144068a03980a01c64441c80600b81601500110160001543d1506860340c0e80d41c10640d4482c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 700948030 1250 700946780 700946801
    0xb03090123011d04080403080a2f03040b030907031e150903121a10030b040c030203060105040e0703090209180d05191404030206070506071409060901030c02100203091609 75
    0x20a03007042800d04580ca60210f5030000d00554600f4a010f60740d40d2007081a074070607206c1d500032035020001e01501e50641c5400c103000c900c0c105002e42d000e0803600381041e2240f1940c092903004a10100200c0d52405007041141d0140d41e0107142d034800c050301070b15001c800071640d680c111294082a1407481c010051405071b10b8110f035064968048584a100e0500003400132074000c003104c08940f0f00f0030750b202d075501981006007102584001a80003459414402603441980c5018180350040080c012181d80c401c0032101100c0c941072a1440c5510b075180105c01804100394080d61111503c07051104042c401d4120038010100f8600321041921042c405445034026030314200b0f514101ca60181814900844a0f107c0c00880f06054038031340364403076001450035001107070103680e6903000d00d08101c130164101904000a5403001015424009a03d0010f2181d104981c440d82c105901d48259a00513402003000c034008845c500320a41d2245499011144d42d955414a02c41008002500001d0381003520b00c03c015214 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 700949280 1250 700948030 700948049
    0x1504060b0604031109070c21030e070e221709090a200702031e030a020f0703050705040906090c080c0f010c051c18090501050f0f090109150b0309012301 67
    0x65070380740100004005e00400513424000c0f4100e03d40c0006480e00e508040d03400003005100c0466040500090403201b60454581e250b6215090622007802451030145d8805201d10fa00e402c0758201404882816144940085c40e041e49207030702c5150984c10101904500b0019602c20100d6641d02c046542901c0680381124007030700303606141850444400000744416400641100c2c03d2072414400382d52440c0040709a25120b0b00041500c0281d142d05010408501442000074041542907459403032f103031003151007a5031155a0740d40004040144276004108603640100704008203e03030b500305180c3c0310200003400c5841001e246803801001d6001d95100f2440c3e580004c000e2034903144024524040c152150542c01c24405400b140032183d601d41c3c10f055018242c18032011409514260078440315000301d40d10644640019210018030351a80e016842c11540c00c01c07000b081c020181401117405a030207400815600c0000820854080015080804c1010861045003910b07180210300f8034414900780280c0c00f04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 700950530 1250 700949280 700949303
    0xe161101050906150402090f150903030d0c0306080d020d0c14060406060302010e0612040b060102030f0a030b01140405010804150e0a06090c06050c030a0c0201030f0f090b07020601080c1509031504060b060403 91
    0x480c14000c109c440c02019500c5c01c685440e844030700280c615003218404120a03901c3d10b829128050349800740000401c40c280080200c1804820080d4071104800d040008001200c000181407140c5602c50b003616101c904252100360402c1d0801001803d024001039000c84c406511244640c1485002c4400c0503002c01480e4450b80c840f542c3d003000b80400038151504600c814480c810128440c2001460404056200001c00b6a0000009850400e024482403540c0500380002c0102c0d0360449166540070381e004c1343c0e103840c0c0d101d0050044000c02c6000c00c0d000b2248035038100c44082004a0303109115a40c0180e19080300141d540c203049070684200c400c002010f400901040305082e001c0c50039685140d10505000c510f00080d5405001254611001020035076260316520003441044410240c1007841e51024019542c1040140c0d07035112520781007203014a800110702c1165149480c03d46007124802010b4030420a044042e260007040d01340c03025502c280c03402d140b0300894a4010111000c4aa00c00010702c00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 700951780 1250 700950530 700950559
    0xf11071202040e0d05180a03030e060d0603120908120a14070303060308401a130807053604330f05010e16110105090615040209 56
    0x2a500400c0400300d07085910f81c90301c070448520610460f0a540d8080e900c070303625140030000c029042c10112103514015045c810701800482d511072000240c9101c1554481d0b690111001081e00401055101921140c5c43c05c014508580d80024030504950709038040b039100b403986180580c0ba41c8134055001010452031800b0b1440000503a000e4542c40d03010382400074010303699031203100c0315078091140c0d07914030180303c103c002c451440000790480008410318400d5180614a102c40c1700c1c60064042c210210031449029020303071090308102c07441d0706007901d0011825aa80c456152740c0d02064004d0a10454040c0340307103100c6e0050701c040b0300f002021102108010b030b8100d6110094840015006440000241e229603440a004002c0340f0100c00740f21580c440b41c80341524079101102c800005008180c1c2c200001008540c0e1842c4041c4d070405412800800ca100402c841a2000c0b030030038405604035402c00c401c220a4070004110f1034480c10040c89023600c49020b0b40c08010032480307040b001561081151b102c460 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 700953030 1250 700951780 700951799
    0xc02011b08100f090b01090618030b06060d02190201060b070b01030611090627060c032a0a06090201020c011e0e041e020417070305100506031e06070f1107 68
    0x1034002603a5880c0b0000240c0f01e104665a440c195040000f425407039064590940d680702034081700406040c40c4c403130503418142c116a149001c403444007400032a03812000c29440e0b5580001c4503091240030070704558910703682d00741240c0040701101c81c1c409546400030001e100c80502d01210401640061100c0b5203a09645d16a0024103441c2d140784c01c00d000c1841243c03100e407280801804031100c6200b045188001da07802031280749140003407082c0140018000403201da070002007a01d50195881503040f0b076004004195a007160500c01d20054207100e252903107414400e29900400d6400e000303900782c03002c851040380150fa401007907030300482c02c41c030005045000c0c1610a0a00f8000707007e008002241c4003061025102d2020b1031003100d000200d17800202008150842c2c1c1340724140c81c03548006007000038a1920707101c2c0c540314842e407492040d80c0c039000001c074541d4090103802880600c045511882d20040700c1a0369603030300c0494402001c5100304094040e041d0254071205400c1c282c4c640108522030400ca03003c6c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 700954280 1250 700953030 700953047
    0x1806050412081615020d0608010606140715060b1305090c03370b040605030c0319030e03010501030f0302010e06060a060c030c0b13021e03120304140604060209040c02011b 75
    0x400000710109510000103121100032484d1515820700540c85120b00714240d402c940144e403107019141e1400d041000721b560020701c4c0b07603d030b0150507020a84030342042c1420301e0800f0300710f00c201800c1d9250401c08250300007001d0280c0080300403186600011750b102e5042c07040e0610b0a40b508588500c1c2800010401004400004203200e001281a10384a240c020701c411400c01122315500bd4030713194410303c542810184200c0b80101021802002c40750501000b00e80c4907204a030642400e41100d00b44c2600740360103802e11135840d4601900070071880d81c0d28184210070010118044005500300080b114030901c00064060040c10000c4c0344040980c41c228003903800080341001142441200010240444e10000f916032280781c02812051210803103204100ca105d40268241131403241c2911034070b02c6514000303501a441d450f11565155662140e00b4910484c140b4000d01c40100e10030310007040200302481d009440744c141c080d14240154801030f8810783c2030352064031401c10450071000c0a2650540324400742d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 700955530 1250 700954280 700954297
    0xc1e0201021605010506010e0a0b030a0b03120a2307050c120a0606170f1203010605091203160c120206090f18041217090606040c0e030d180605041208 66
    0x51515191038031900d100c90006100f541d40e40d54a004002c00c03560003180401c00c84a04442c00c400c068145000300b0514000a4550002a03035503664100b800d484c20013141c5044110004000c1d152a4510780c014115035850300c02c040440c00d8000c1c800412a82c003800da5042c150b002c0c004c0e00c40d881400050284021002d096913109128411171480030480e21b01c80e14001d82040440c4000c080400d00442d480c128600222045541c00114491a8404088141c0e41580c45915003d0b581d07040e1f450006a6001419441c144140400200c2e030081030940c060f4803800c944180c0c80284065030f264084048030000140280d007005007081700000030b1900405a0810490092000c0d042c0f1a20030903000305164100c1f41260351030105103403002071540101c40044c42028803c2410300d2840c0441c029030b2900d038003610190040d500d03482c0840a180c041e0801003483c000c082c0407181c01c17400c144c100403c4000e041fa00c0204d520a140703000b00300148a0300c12030b41901c1c036204861182680315503a403c0a584900304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 700956780 1250 700955530 700955533
    0xb091516210908070605070519030b0613290c0c0402030a021b071a04050a051c050d09180c05090118030215030402181611070504020301030c0e0a0c1e02 67
    0x58924072145070b88102c01c4414040d000c0301e6141c00c031a2400b2070458401500d41c00500c00c00b80000c034080d080d941c040300764601d064980403443c80000404030790f15002c1c00b00c0054000c1a0541d01141c990f40d800580400a6a10241200544900e4400e903000f0b1084464803015900803070001c22980c10320350000c0d0707002941c1d9071b001031519440c4510501501206540c107103042c0c10031041004028000d104146004004540c194901440c001c0040c1c0140c1c61403040c2400382108402160900c42c140c680c0caa59540c200003503910036007610034010010f03001405810280f43d01403207a40302c1255184030318908290117480e00d81ca0701000c031006407500702d200b200043d020a1403500c0880140c549200c940e0100310060021601c0c7d082c103204012800b40c80132450070340b80300340e4810040780400700000640d41245e207003007800b0076035412140c20781402d40c0c9812058115000100020421109030070000c1141c3c403007943d40703945854910f4040280d40c0ca001031744001414141c0b0f045851142c1c02800940301c0e01c90700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 700958030 1250 700956780 700956827
    0x403051b0a02040603030c020a090e0606131409011506031b0302220e010614031005040c11010504050303040212030c06010b090a05041e06050117040605060a030b040b091516 76
    0x2030000f000e880315078004030002105070800300c0441c14120600d42c060301c8a01000d00450b6111846a5603402006000303a1095840301c3c0c03c4400701c2d00c69880550680440802d2142c1490500b401a019051040700010782c09a000340c00198a0720030310962100903100c4504240c040712880301280650000c1d05100f88594110b15140031810b014070300440245600c4ca4121180d6241460117010403807600e0705030070314401c10402c101c211104485454242c0304100c50000310240912801ca40c12203030070003800c20700c1d0701c1c08007032205020001000e14440d61080b9034884601404000d82c035200c2c082e2211114480e40400018804200100c026100111000d03255403c4030b680c4400080030380d02d2041c440c460b6502d2200440d154500705004410140030300b1b0a0a140d00400c1c1901091000310050000d45a0759448002c9051591500903000043d504103c03c3e40c01802c00b8142480d10100a0722444850302c078100c40010215151103900d889901d10b02d20260090031402400c2d10070380e107072030500310030041c855 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 700959280 1250 700958030 700958033
    0x4050c1c0e011d0a0b1f09090524040803040f1e05010b04060803070609020d060c0f08070201050631060902181e060711060706091101080403051b0a 65
    0x22440822080a02404603824990311285402c40340809065081440c960414000121001130b0948900ba030001c4041c40c01d54600f000b166480c04408840c40d401040003200240490a0390884c0103500e0041084e82c8d0300341680c6a83d80d5040700301c02280c01c0349035850300005010a402c0005140d0190051546600d00c40855803160300e914411003200e10402c102c100e41105202d0b00b44503c180d40041920708101443c14100001d82d039000b06070000340813984400c000811511820444080b4590080050043c16030500e006000f0403031881c00b0000040445c00082d041e684140a0702f40203940c0034040300041050b96070845002c4d410406c0030702d0f09020003801138180b0926407050200a1500c180d006071540341101d080c03800d2108a02050b8801c4204000114682c0703440ca01c0d41c40c001108840c900d9454040f0b01d088001c0590480800342c5c8820081181020300101b0740010710483d00c9000190b50744003079070006540d0210144d0b400b070000f4170306000800c141c009204886d0000e070302d40021a210351525 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 700960530 1250 700959280 700959307
    0x15100813052e1104051903020a06080403390219080313060e0f010318060c030b120a1205030a06080304030606080d050c0307111c050604030807020111030604050c 71
    0x322075024040b114060141d0301c0d065200c4108000300e40101d0360510280c04480a40b9009014900880307100d12a48040d020302d261110003800002e41c4d024000420b9543d031020081c2030b031302c0202c07020f40100d141640d02c0c5010210260f083d01c0c00144619012001c45100f40316240c2503890803000300e80201040e03045504030210341203682c0007081c00000859480c0d814200440b4031440d943e0102c000d120645071490b00682d2013000000000c4003c0c03070001044281900300140401c100d40000d08888c0c0750101d0a022180d05400c60401c1200980f40180f07560003103140903035500f070b21000c0507004241443c600c40900b031143c0000c6800414460380401d010f611540e03064215030080e40b08554696488404100b4400d080c481c14681d0310003420301c0703030600a0720110142ca03032007184d100400304002070000c5a129900c2c510907020516550710001c100000c81d00d0310607a20602542d042c1c02003035100000402315481400307a91105d5840b01c0f1102d09607212081400702501c005822845070748000d20007820101d88 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 700961780 1250 700960530 700960543
    0x1030f0309120c05010e0f090c130b0c030a03150b090d050705030f030304020f0a050a0603091b06020313050402040b0706090203011b0804140c06030408030604090c0603020408061510081305 83
    0x3c80d0104038003450400090101125001d095010300901540310650b0741d1107035500c1e540042d46c07594540e5246026841e08150300301c00e0308180c050300d001141c00780010347c00102070005852181c6040203813440e00d41440c211520180701d000807010301009220340504050700381c0c0c1a031600c00e6080f61400b039100c000081c2811081d0121044942c404401c2006520344107240d040003c2c07040d140c03403507401c0c202004a80540d1042c040c030700c01e02d5210607100301049030552003102200418103204000c20303200c3d10000d480764007100380520481c50005001c140c0749814803c46c4e046808a85000d45009010383c1c489000e80041c06099034035540c1d030300c404c900c0e9480e40c245600c514030040e0341d159100d20303089c0340c544249588071a011056034000030f09130300c081c0c8514003201d0300903401280040e181e58a0b180040c0281c01400c2000f8040032103d440051003941507005001a10781e0042510083d40d505c1200c40595240022000d5111100340d099400d11809001d22607040007032818286042c90060300c400b4a03100c2c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 700963030 1250 700961780 700961783
    0x7030b070c031808071707091401030b0a0b09070e0102030d060e0103050706021203240d061a0108060f010c050304030b01030c060f0e210f070312180303020601030f030912 75
    0x607100038250301015440007a100c640060b00c426101c02c1420440030503070ba41c50501810760340741081003020341c08100030090000140b0194a0038803550785105001c200900b002e12003100d03003c1d100301c045400e505260003a4026928040e01c4203800c0d580c0c0010440d0840c1c540c6241c2c1e030540c002004070000510300d43c0180c0c030240c50503061560003035155107840761400506a04c04000c40d0444402d03006100c030080222a0041400d0241040e0141d500a641412110500c1c400e64807c00f02c85c03e101c100038003a007103d4203509082d10995003a0712480015103407003a0441e52940d21600a8010101540c0100350205103180918112400c054070b07507139410680142078206444002a40504011440e8003110100f0706001e1807500311008064900401d51004041c0c550510021031404184041c040800c0103401210741182281c0d40c2c0365503400e0031130f024100d00d001c901c00910070803601201d0400401d02c1c2e0045a501d940107204682c61034440002d201c101c00c00c00c4003044030b011400180601c0034400080d885 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 700964280 1250 700963030 700963037
    0x5040b0d0614030f070e0a0605060a080a0501050f06030a0e0115060512060d081c020903010c17010509060a140607021206071716050912150417030412030e07030b07 72
    0x342c14400c0c21403008001049943c425806010155030311840400c0c00c404443d00c0e803041c24050703112061520043d1540d508140d8003d10080780c101c0200c2d03400300c030690081c01c031043c080080ea43c0b40da061044800c0030800594100702d013000031a040081c0e640c001780d841d9441b0000082d51540c0003190020500c41e55102c540003800100300c03080300b8000c04803402c0c2c2041d01100c403a858098165245010780c0611075100c00701c080341542404c0340c4540d0b5011540035100040c000c014043c021500a03041d07002c9101241810b403030800020500d41441d91005000e403800418420a041c541480184d88019003460203801c100140030110041e2a000d80d60181e880c0520b000d801c0c0d524003030300d00074921503480901602c6c46195206001500e076501900a4401c040707454542d6803044030001060514920641c0c08445105412080743d0202d220031501e40164400d82c0481141c60381d843c0f03d010340340400d44002e0145030a040940044034000d41c000b0940310781940940718000d580e515030801c0f051044a203030020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 700965530 1250 700964280 700964291
    0x3021e041803020d020c0a120606082d010c081819031d030c0f040f0212090313090e0303072016150c0c1203050d091101030b010215070f05040b0d 64
    0x201a0148502e40032454280300521400c004100000c0c407800c07c0740310b50001c03840225101c4080c00380b00d400c100f01400114084850801102180800c00d6051040139003440c0604150f40310038a0301802a00da07941038582e1003194079156a00c1642400d15601d2424400340f2404d150080c81e40509041c0140080c000e854070319000b401600803088100801c00b0740c2e4882d422845244403c5e0382c6080c81c0104095080c0c60021f12900e01c00c031904001e209556a48484501100c2000180070000000b400140c141540300307805140c0e80c2d40180c055914015500c40b440c0c1040c000504540d114400c205159011185440c0c142c0780e644000504140c0101400d041c10038010344184a003482000c20240d80007024a03203110f03640d5450311403250801040c088c031308050340b5000b144414548218113444c001284018200181203040c58400c070030744107010182c1e001c02c0c209088034109600110302c004c540340c0100000304c010342c0c07501c5080714801d0240d05900107000040c00041000c1d141140070b00009110540002070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 700966780 1250 700965530 700965533
    0x6120118060f0e10050c12010f05010f05031509192316020a080f04031a010807050f18091002070327080d0f051605160b1303021e0418 59
    0x1940c11441160000c01c3c1840e03d102648140098864641000c80600207615102c1c240c001d070061140441c900c02c083c2084001017074440c0c104800008030340342621403004214100300305407401d005c111069500450304400380d0000e410300072000c40c0d101484049050a944903400107004542c000301c2c104000d07809001c41c480580c104c4182054011403192010b400040c0e14a00007588e0308110303a4010714082000c0380800b65403d4400039100030f07551280911510000040c04198058030074070900c1d00600c01c11900280d18245451035007201c4002600d040310780c2040300c0c0d40d01c60884010b0038503200ca100d102d100c820702d840280301034a0340601c203a940c1400c0c2415045c3d410680c201e02e00a09480c0e851a803020000800000b80d00b0544103842d01b07100311032240154055541e800382440f51144019840d104600700003010444560403a181c64032148035070b450b4400121a80200e441d4010170000009060016180c003c002044100c00b9180d070114105142c4081800d884059a445031003a200322181c80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 700968030 1250 700966780 700966793
    0x30c03160207050f010c0204060f06020d1404061b0c05130e070902031006270906090e0705010e01201e0607080405070e0a0f050f060103061e050906120118 68
    0x318000c49440141056414080000d0002035109038032030611940c04c45d99000c544894210728004c080c0f61002440080d542d00000e5100c26156a048001980d4129005800c015103000d44083c0d03100da91340c02000080700c101240444000719001eaa810419000010316603944212031160340002c1800498030040c0041000d14100c0250060442c46006108001610b41d4170ba9003c030032200c05150807088100707281402201e8442948454a02240a0101162782441c0340c0021040364400c02040185400c1201c4198540a05006450000700145500d07034494ac462440707011042104032103100070300080031080e86041c1a0036030000c0c0c04c10b0380c40c420070b40c664428040180c0c410014105000c0600c1c3c183c1c0c9680c0ca644a60045015851050740410555900c5600c800b540141c110403c01403424015004511088112100c41c0004e05192011a044204a803055441c074491004500d003203041c42c0811100322402041c0c0341d00609001d40403d01c00c4824050040b49500c030070051285004281000c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 700969280 1250 700968030 700968061
    0x5040c03060518040f12021b01080f010902030a1d211c020d0906090c051003020f1b01020c03030a29030a0609080910110f190f020301090602030c03 65
    0x560925241c420104070585030060444582c1c01e1030303604041e0f43d981d645800450506000c101500400540760801041c80e00016030342e81181d0b560800c40071140c50070300110f814407011035201d0283c00c50f00c00104207010164001d176811040307440c030228180c0c08020842000000c85041e50780d4030361000d102e40f09007620400038182162029681280391165449600c50100e44250004d1032595002034882030360a0a54400e100d43d5034040018450741003941001c007a0161503014052080b08625060054580a031007103404900440c00301030300b0201002604940405400040d01c5103540810042c1300e01c040034030003584140112800084e10b805841c0c0ca15240c14101e860180e0004210b1030b03440042c0d540001c0460400b80e0101012894a01a1034100301e5805070083c4141c0180074148400d1001e500520848064010030048a031196060061156684814a141d101d040090f855000110321410684102140041c0c004120000c0c1551140100d030b0040794103003100b030800300c01e200c0c0790160203c20 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 700970530 1250 700969280 700969301
    0x9073005090607202d0c190306091401111206040c050d180c0b09010e0303070f150212070509130b0303030105220c020a1e0b2403160504 60
    0xb00752503c0c0651019001c1c072000c0020801e008002050011403080c204614076441ca41503200700c049105650803141c07070b07519101c0d05203454007441c0c040b0500341c2001510440344066546000a501345180c6400005016070344060301c0d0090094004a4445800d00423200200e924400c0c85503142280c0a1000740c24030054007840c81682071030f0a150107254440256612211482c000240510107140044280707400c00343c00502552a041c2d0016040e000c0c040030701030807074080c3c880d0001610410101600c03441030340c800030000c200b200c41050200396a0b400080520484200051402e250070450482d00327901140ca5500052000848070303424200404501c48011209000b800302d20718000000c0c0e240d000502880c0c1c02610040c05544003401d1054403d6040c0c281c40d0384c100015a4400300c000d46450320081c0581d0040d02d000405072612404d00b1080b05200e80148034441a905c50551034411a100c1c5501d15501410400f0440c085a07030500880f2105140008010302a41c5000141703c01d48070280078 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 700971780 1250 700970530 700970533
    0xa03240e07080907060e040f09050303220c0605031801050411010e040203090d0509030307080301090c0806060c0309060304060f150f081612020307081212010e13020907300509 77
    0x2e0140404000030103030291001c504040a91b201d03501c0c040b0f40200b0715201040380841c1051414010b0103000300085001c3c4104250208441360a1003c1d50307002c1c8aa440300a0a130302143c42e040000d540310344059a04000c05502640b500d9113000c80b0300d03094038001d56054410382c0c190544160a580c209162004104d8150780c00d508600c0c2110303a9030b4031440d1044048003400000a0700e407207030303507801e2086488803540480016100c2d40c50300d0001d8010020042c15001040707102000c1507691400e1415651400c0845008515210907501070041542028004603041516501c040035942c0c00c50203829051200e0008454416103000020200e011160f8490782e43c03500f00c0040303a0b40f0110344031401030503281d0f15030100802c020140301007803a000c11035000c08240e0103404907810074007866200800007030300303107003420f50b1640d0700c0b83c080300d54a03281502c040070000d264000c410018180b00c0c042d55800030351401d0400103d07940040710b00d26040c10440300130300c2c05404a000000b03801c0500c1101d03000b0501a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 700973030 1250 700971780 700971797
    0x15130518070c0813080106051c051b04060f0611100501060c02330703090803040506031906080319120b03032b18030f020615060a03240e07 61
    0xa000240500c001d00761108020024103000144a085011180c403101c401c070700d00c040c41c3d0341c882c0618000c090328001d1901c00c0004803410707184407840705003015030680c100d4040c10850581c0615011610910024550882d40399040014900001c7c03043c00d00500441c0c940d440841d26103007450b402c1c0100c008002d00172130b1820700180b240d80e5001c2c01d0f0001059040d07498200c80700c0103071860882400030510901503024103100c0300700204070110151180500c01d403a2070f6200f1303489c0c0c07002c6a124083d60062640000701400068000031000d81c004c0440c02c6041c2001521903110804603085610002e1584942c0c2c1e0410b00d00b4000503440100c0c040010180c520400c8840c88103000280c903032140425410b9010300182440c2030b507110325510a8404120440308200c542d50b00403014402020b1311a0aa010408040301c1051403800492078034440e0b0183d03119172200886080801c42e080e04528080800c1540e10361305070b190f4411000d003105092004010004000d480c12404422203000242070808016056 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 700974280 1250 700973030 700973059
    0x110910030b01120203030d021b10020304080a0309030e1503011a030c041a0c01060e0106031b08071d040609021e0403030509270f0f0709060504090218151305 69
    0xe00c0c01c5415180440d180c00315007906400005d11314080da0b59210300c80c43c8000b540e0f00c0b0012610b01120781034180e18054448404000314a102280421240030b04a400c00304180040309220354400c520035846400d00c105955141c002040004100d040c1c08990484000014800c0708039070303d141030700082d9041d2a5461071800b100d561034a802240b02e51a51121200680c1c0740040c0240c094500005041c0c1c020803ca130f43d07465095076001428418100880d02d4000310300020800d00c3c0080c040b10300141c960859680700e441c011281500c40480c5d600d07016441900440782607031580100e034001d00c0740420140e00c0e008035040720780d615a504072200c3d200440400040001940000a55107118011101001c181c80f201c40031005170b10307180a5801c01030700540100440701d800f030465980600800000401c95990311101564642c0c040d000b1980800d5090104101c3c000140d0028040c0701001c11071a40c0710161f45c80400c0301c0b0350070413402d020400d601062001e0150131141100c0300810080322040881c1051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 700975530 1250 700974280 700974293
    0x901090807110d1202060f0a061202010e0a090e07090617060106110313120c1a0706020310080a1406060f011407060603200307050607051c09090911091003 68
    0x1080300c002c00071030b195558000381c0c0c0d90701042c070905140c12500050031505034040094861004a808092030f914840c08121085002e00c03d0340b05858241081c948241541d400550350704881951481e4004584600490403241038011035035000605001040368a080901c1d182c240c038030541000c0c803514003420440c2d0345020b001503d503044603014200004018003050009085110b90f9400c6400340e03102130000619650341d0f2503d02a424000c9500e071450b01c0d1200420b080f24404104a5600c00105014110110b841d990080d074114110b01100144c107582c03840701604115403494143c80301183c0c8510b5828101042c8030607030303000700201e175900313210946000082d01800c0301d8038124400306004140413040040542c0000c0107541c10000781a070080359401482046c188840c3c60601038090900001103d05060068604072580880540520081d1940c05181c0e2440a0301c10301c200503440100040c4070b9010311aa5000302c1c040c186601800000401b4005003280150446011011502d01000440c03403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 700976780 1250 700975530 700975537
    0x6180b0a1a061e0a2d02100c0203090406031a0903040501021c11250501020609060a180c080313060c02130f0908040e0709050603220c0909050c040509010908 69
    0x2140c1da41c0d100d100040c03078a0540c0c00442e64010984000007007041c40c13180c000040d0300ea4104a10246501e03207071504a40c2140540e0030010344007503440b200f200c10558405401c0500610340c0303841243d00b051404000502a01c0255006035510601c15540034000c2c0380c1e0201240d80031040b40c00841c2341070302d8000006e648901041d019074541d071010b20318804003071040f031301c42c2427545c955030407240d00e52100c84d0803034200029401000c0c08800071003c0005c1d03070350000c00c415100707640c504040c0486035102d07401c3c207001d026003100e03102c0135403404050712002902c00c3c03e458000c0c0200300021601ca000c0328410b8051005a07802c9a81031009002c400e20040c1d03510060200707000340000c40840e03d040e5482d900c03005401d1441d0010014600401d011a0460011001a120b1406542c039007500f143d580c003d00c01548810744036103420350848444a0003000c11009a81d55491050300084c1003140d48065401c03c4882d0900e04848540284144000034509401050341000e51040200210651076a0380783c100e20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 700978030 1250 700976780 700976831
    0x1603180512070309090510170a0519020f0604030501050402031b0603060d030504080102040612050703140109020901051b0a060c0e01050a210905030d060f05151606180b0a 75
    0x1c800240315820541301d640100004d004000782442581820458501d088140c2d009140c3e40d41031070b0583d42100c82d400150144c100c0e804c00d0242c051158a226404030791400382d10160f80020b403004a00d503c9840301c1c8000c00080d0300407000010b5600b443e204250401c00400139038141c1e4a60655a00030641d40ea0041703c0d04640220782003624510640b50070745950040d41d001d801e065101190002d49079030800355405241d04080340802880d52000300650480d168440c5800011100400500032003a07207a0050014800506026040c0420303080c11b503007100e41c220030003001d540081da0420300304001ca0250782511001d500303240a4084800b0002132071401120110301c10003402100d00101604c125007601480482c4800c2031280b0a01428029030b2a0700528110f12013030314011b400121600f07038070111f40645200800c00030000d0050141c981541c2c01802d42e030318000d01c00c2401440040e00074030a00200340e41070412410107070400d0038560b900c02001010780c0016401c081c200d00d4090300e0b5500c44441d14 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 700979280 1250 700978030 700978063
    0x10e0a060b0f0d0e0f0a0c0803030106080412020c060f0403150501080c0d0606080d0207081203010302060f070201121514030f0604230d021b040c02060a2316031805 72
    0xc0740341103000b20241c2004c40450016000313103c00d1210058001c00c00c4640180102c0e207812225503101d0a040c1c2d2032109100e84400038000801140015000c150441c0820a5620466101000013400942c007948040e1400107804800501041000042c1c0039200300c0c0800d60307000300070035858644447d446240210055128004d0039180c070040220640c80100030300120812102c0c4100050b10181d680e0341903020302c1d149403099240e034660b481c2e42101201e060341d502401c41c60512180c4030802000c0c0c2c010360002c80c140555170200303d496211511600d5103452007614001032880c03400803c00d4444ca24658a41d0290f00281c0348030203120000103140e500298040007048405c0c07000d501c03400d4010b05612801c02c1c0c1340100410416006d0340040c40b184420621341c4998846180e441c200021620040c6044000d6002203000540300a0294081c000711651201900d031009030f000d45042e07036440111420418207660028000619a1600c10041382c41c1300611103490003149031300d42c95075680c0b000040704c0700c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 700980530 1250 700979280 700979287
    0x106090b011b0b0a0213090212101a0703030230011e0b0a0e13050a1a0d12030f0608031306113004081b06040f260d08010e0a060b0f 58
    0x41039411501c6d1040c07203101907840c01c0c0d19003070700002070b5000844880d404000c1c00041100400c07449240012070740d4040000c01c040404d10a4441d06800014043e824940d082c4030400041039030b20300030800c8881001d41d1011034207146040414408040e00b1180c58403003a044100ea2000b0954200401d4400210b4900d0712944200310071100b280b18005000e820081011155010344c240350481c81c0691160041841403130408601e05041034002055543d00880141c0c07450040f541c24210f140440b403980c83d011500101c1e0300c0c0341000f511060350102c42036500002d2008110030032494480090041890907c60a00c1c907613404660f50383ca1a914611484080007030480d00c41841d050560f206020400840d4403280c0da03914040d2100900c4003104a0680d0303591a400a40c54140d040310300750784c05650b4090005c0d040800b0700c1079410105600c11602c418142c60000202402c000380c0c42081c4450307032001c40c503604118070003022035400f910901200d81009400e2003d074030b650080d240d13200d080c0d803003581c3c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 700981780 1250 700980530 700980541
    0x210140c0a03020d0e07031505070c081909081609050c030402180a200306010201050a0b210a050f0d020706020706080a1a0409060506010f080411091f06020106090b011b0b 75
    0x1480c41c6044a591403182e20360020801410300312007040c06231503031020441079650b680305641d00030300a000104200c004100140b01006070310110b01c000c0d902f40c40d0920007903444241d45850050300d43c0f41460b9800070960104010550703801072907880f0144210060440c00d095001c90760502c2c1c40302c3e10807100284440060ba14540a50102250441c40e00d04210031441d0201c1d810f04660054641d80c0c011350030400050510405030259070401000034001000c800443305c81b000b4116030400c5003034a18000e601440c0085031040200b00c0528004001602014505800191420055911520564100707180421405411060142d403100f185d0101040c4554100769030008058034070306640d1300c9807400342150140300c02903001c58031800080e2203410004c0340881e8103950b000000c4038000c10458075076200c1000c0f4200b100301c158214009000450b544c4041130300c500100c0c049a004000103070340d1411300700311501481c02055001c0328282060004101d25100510181840c100c000d00b402014074007040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 700983030 1250 700981780 700981807
    0x315070f021603030e040c02032a0a0b0408040f0e0702030a030f230a1104030503090f03120a031e0e1509030412030c0c08060c03010603050907050a060210140c0a0302 73
    0x1d00d074000b00b094582e103540d100e00e409004110311032845405203180402c0131420500000844280100c142554030030101d00240e20302c11584880007030b06160150220b441c000a02541466014610507000d10341c4403810100d0180c890ba8255200c1c1c095030ac484014810215004412121407902510300030412074109940000a07021003044010415066181e4000c403e500501c007a02480b964401846612200c18000c40c2074000d03800007411940080040c01594600407428403005c02000c1d0980e03041014101c840082500012003500c0860b840702c60310180500e1b29080612110001d00c070070410a00e80007400c039540d080820f000b400c018804408620703036040c00c00c2990700401401407000728000e82840c00400c0e6650103c0e00710758034503408402180e9010003040d85d03481240301a01c107030f042da0300e8a6003c901400c0007810180b0716018141c40072821f511480e00c0b10780908020b8005160900d50101c1500c200c981c1310701306c980d031800c40c0d10520002c00044000c48402d5010303450050303103400d40c141448 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 700984280 1250 700983030 700983043
    0x3020405191a1303080c0f011a0618130203010e011d240d060614030118080a051806040b0c0607020105090705060a030f181e020109121a01060810050315070f02 70
    0x1400071750300442c4420b410400050604000e500b0b21009100c1d1400840014101c4240f00c685507038070400604c00119082c00001000f0307920384000b4040d1007070380202040d400c1264020382041c2c0d86400200e0060182c103240f4a406003161044619002d110b140900b104100012110049003010b911003c06250940e18110305500c1c8070b401c48000c10280b962002281594030b46690154025403d01d030000d4103040c01c0007401984190040030031032411060041c222030aa10001c001c0c0100280c220050541e0345800024101500d070070301c000c5640d4401c440b4018030b000d4004103108216810101040300c541804a0b01da070855800ba40c0300c8d900d030f041152041d40640b15031302900c55218a402c140c404511082c6002d170120038000c198500d003030f2015072501c0c144500d010b007010b8041354a856003008001200584c0303c411070300407602c000882403a00c84002500c8801e038400000105800c09000510903410031403001080c0440040040c12004031700f10b898500010086414000e11002080381d0340c0c003e1002c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 700985530 1250 700984280 700984283
    0x303090210020105100b0c280602040b0307120e070603050c0d0e0a0b01050118060e130c030507090503010b090a0b0a050d08071a131410090303020405191a1303 70
    0x10700007414040802802000c080b1441c80341d800340a0400201016140100e4030b00d00d9180000e0316002e069000207010005503c00720700d481ca00303064803140200d40144090800b604c91144003540c0c80c00c01d1840284090624442d52000b54a41008240c0c14100006c0c803004550940c100030602d0b40c0c5111301825180148a02000260300f00001071203000c030041451940641700b0449a405a600c3e0300044404c140d901c42c44450480c040c2d40c05000f600d005400803c00d408004103000c02e9411f07402c0741c81c003d80b0180603900c00032070741f203100303103d4215003042c1942c1c0a8201a002005142240720008000c5080500b159191564991a50780c3c141c0b1208080d0014240c003a1444811039542e10b8a03200301c0c1d02031002600c000e0a095000f805a07c03039aa8141d010b8004403500c00c600006540381c004090b60841441b400503c01d80c08000110b0929010b50001240252401601c580c07804040c4001d19070100d20305040000c0c420014010200d000412000c00a000c21349140c80d56402c1e050141c0340401c3d46c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 700986780 1250 700985530 700985539
    0x5070b04062717030402010207061103040308120708010504020f09040f020f12160504030b010b0903160909030306050301020f16240209040b03010501051011120d02073c03030902 78
    0x5211034000282c0401d4001c2a204148aa0b00c50102c055401d0719400f003901c00900603005540c04200051140e900726401c80f0b41c2c641a80d00c3d0944d81e43e80c003001d0350300580d91002c484a40314108044a5000406140100b006803429490007074840e03000c10b59841a505014841d558680c01d0b00c0310f0b0400d07507056489910110f0b441c513030745141c0d0722030641030610b04a4040301d800c0314050101c45518481d400ba1001c03240e015104184990815462100c6a01300e011504c0d014491002040d0f41c04095801120042030081380008026140741070041c00e03516980c1145009030300402a06020301107000443d0702e81c20803204091100c00052520b050440c000040642d091610314490341c2406810303500600e0000c00c100c4081101c0b014000c2418240d443c03d206040e4003103414100d12001a000b00c5815940c080c03401c0c15a40c184544521080e000d420401c442c00004e03a0229440c004c10040315041d0744481039021100d031181002c20501000003d100c2d6501100443c0e01040301c040502031f400507070200d81d0080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 700988030 1250 700986780 700986821
    0x1621020307080a0510060e0a0209030a0b04030306140d0b07050c0a05030705070f08010b03070306050705040e041a420d06050a05010f030f02060a0207031703160e0105070b0406 77
    0x3400660360b18110f00065501d400b44030380006641206100707000444038116440c0fa11540c0e629140b000030741026000941500a9448490000756070040312445544a03860006c1c1450030070360304402413540d910b9494025080380c100d907000305015100a6601c441d82e454040e03903030003201584a003040c09090009100c1c0c40045104420000042040b000f6900c0720955020f0701036803605e865080c0e802011100e600b40d000b07000184081986904400c0c0d00400505040e03141c20358411105004050844090b240200c03610b07549500c10101d1054280c00c46503001d100041c040303998070200d0f00304c00912148588401500810340000c2c2070880542d218010081284c1040c04d0a4205000603060880d545118a03240c0707400860b91040f1601d04cd0143c0e07812009504c1080c100d03900780540c0354854080c00040d48129240000010007034031640c10702c0c1d0080309035540c030384c100300200d9202c07460030050350405d010072551501c032181d9011041c0c0d041c0d0b940201e0300c4889034450303040c460020402e85441d10441071040c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 700989280 1250 700988030 700988039
    0xf0d0f05060108030d2a1d0d110907050901090b030a09082a1b0409020a050904150b0a030f02040903200304050f0d0f020d11190608091621020307 64
    0x1001400b00c0c0350442c60305100c80d8440c50840e0300340000b4181320100800b0301ba450700c0003051181040200140340070b01075000300420000040d485001c11070302110025410a09481d1608050800360340251190400505002140300060010b0401d4001d0300c07000100800040d00a0036180c201896482e0010001d940c0c40d443c11400f82c480030000030080c100c140c0c44060340001e403800007401c0e030300b10727060151005990003110003084040c041c08130003aa0310001c440e102146641e107000019010f5846000711002a0030311030008010740d0344001c1158441c1d003080b130080020550a24910741c006034102c4000845001518051700e4044070011000ca14901503202c005007001c00100902c1669401c9800c61204070283d07003040018049000014051502c643c2c40d50014101183c42e1168503204030b4001001020380004154003221080a5a90070292400100303c001e80006405030810788400141401c546400060200340050784078012090f0b44c2d484030000c000580d40c00c203090656004094585076640c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 700990530 1250 700989280 700989283
    0xd0f0f120f02061f090903110d02010b01140306150c030705060f0601030f020f16030909020d1d0105060919060503150a050106050a0c0f023706020109020f0d0f05060108 74
    0x400d091440944100f60100e203e8044100254101406954444081c1814900c0b21400b034800300900728188820f081081221041c02d000300c2c0050003080d800003d098880b00001003c0704150f40342c3c48000d1404101707000c0c4a0300d990801507000b221000000b580c9051884145107140f16400e0003070414000c450031f1106075810021401d014003401d0307a00f882003800e4110340c00102d10801d21042c4042000f0040f54070700648a241b05004240a0b0410307010081c1d596842500383d03401010a03440840d0750300c151014400f4000ba001c0002c414041c020032603454030380040b454845010700320b11145c111002001c000c2d0075582d00004080c1030060309948401c01b1416072502c0314102991940a01801c1c00d0010554500c00c90946038540ca9a030f85148180c0c003a5210f020044810f540107036040015100c60440004110a5001e4900307920103449084200e00581c9080c01c084503002801103905100700c0740c0150b038032450103500c0210120391107030710f1081a1901161554041d18001c0c494001c041c00020b20840 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 700991780 1250 700990530 700990547
    0x80627010501021c081b19080103150603030c0615050604080f1c05030705250305070c0e060f06180301090503030103060b0901060f03050a0603170a020118020d0f0f12 73
    0x5080e000c0320304c440840590f0a00c2440401d103a0b8002589820006280300380c8607440c0203008465503682450000011800c0f02103071b120903a68004111071000400402010301e40f84010300112207030030024a82140d034000d241001e10200900320686603100000b414107060303020801428000d1a45e0b41c2d5545d01e07124962101c0c13082c0c04400e01400351b020350f00b0301c6003e1002400d50503201d0b40e84180ca90307544c0f0741081c0e0f0642c000d9045110990803401114008002045072190b506009869141c2c449000349400f400000081d0002001203d550041c400a51110221855125421a110b41e11602442000762a014a110308164550f00b801420300c00d1200100017076041c1d07070180905011000700c08086c004000400c1c4070b0741000402400003844800c1c801e1b40010380100fa040070108107103940303840380d150140c0c5608a00300601c0c40041d228401d190244152002d14010b0190b02c0890703440c60300094100c50401d41e01a15240c0310000c0c4038200002e00001140c0d11741d021030025484035030703168000d02c4d226 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 700993030 1250 700991780 700991789
    0x110a0c3f021e0607080a020c0411040e10081b0609060d0b090a090f02041805100f0e01050c070201030c050f0304060b040606021f0b030c0604080105151f08062701 71
    0x30190342c1c1e81d01e0a00d40d41c01034000800180881e032415400741d0b43c0b00200d52000740000c0440c06401503840c01c65a95028810490503d402410348550034103100c10107016010304070f09401e16004808104410001c6501541800c889098600201c40c4002189517882014141c40d48801c0000b004811300300c659000b0701d0710400c107950101e203035035820081504481c0116005030464500880b034000614003a0000c100032030004805500358841692502c1c038022510003a407050645414010b00c1c200303a40e10a03400c803004404006d100e6400e00d140c1c2545540304003240a07040645825519a01d140504103c50f04000280905c035540e1900382030941c0107200c5d0705c3c1220b01c21801c1c0000001c0d403d2000607044901c030000d003441c3c0d01c180804110300009100a000e03154141c015044505070070f6480c23001800040c20030400110381032078040c0c0e1428410410346e010600c940750a040302e81c412511101111010b034818140b48800b07031204000540c2c0300e126040ac42c8501c480503883c84000d0b10011000d00c0c100c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 700994280 1250 700993030 700993039
    0x100606110a051915020d051609050109120305190207090b040c05160507080f0f070e04050624041e1d030f09040b091006110a0c3f02 58
    0x40034000d012619035140301c40140c1541d01485000750388106000d0840e0400d48980030107800210441400030a03a002070340a210340c40e54840400c044010404001c0b000b0060302d00e410b07091a403c220010300140c104d0700540010008940380041014014800c0780e5200241e0340c3e041c2541e90070305100a5403096030f805041c400310704241200c6241c0c1000d0044c002d0000003074480d641412039900405105115202c802d858178401d000300000e8104050100d08032803001e6101511550100d000300702e14100c4294050800351100360f081101040020445070b40005460781c0b0074480d00013250150644920b46c000f55a805860804c005507080c11701c11403400b02245c2400180503683d0102421034800412a58070145a0010003484500008020003032010ba00020700008000c100c40011440a0008481051070940102001e01c40c654018030480f84258034000141140c02099840848844017481640b400c6034081c03a0586420b20302406c0345400241c458510100c880d011606240d14641294090340a07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 700995530 1250 700994280 700994297
    0x9080706061e0b0c0709020412021c082a06070804030201050f01051e0409080705010228020705040c1e020105071b08070201051312050a0209070804020109170f100606 73
    0x8200d600d004220798100040c042001032900e50300f00c40943c4803e209a00718029007801043c1400c940c03001e4001740c0058031301031030a55414070502c150034040d45c12500d1802d510100d00310004040c0021607051148030000c00514001d5240c42001e0f40700102031400950080908210f183d50740800464860f034000d40c000d2040340c171400782901a86d0402e008554010749040d01404030950303030181c0340074124809000001c0c1c400c6580c407894460380040000311003d940002c0c4d00070000100b04a510031020014605101d6a91a4180695911460320071107001315100c01001090310b001d406c019040c00c0b00185505a00150110028000c160484841d00410600c100c0c0030f11201202d0f2149100b2548442e980303180051980064510750841c1682c04034003481c1c44070104803601e02001601150348114000c00e00320041d0b01c10051074800c024058410400500300f0407000d40c1e0722042c0c4608841100451500390390500d2285814500914503140320ba100f614240c01c001c0031294040400c075481c83d92000032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 700996780 1250 700995530 700995539
    0x60e0d20060f0c1b010b010e15120c070605040309030c0b040f03061d0a050a0201030c0804050d08151810080f1203070e152a1e010b040908070606 64
    0x340c411032040321204551005001074007802d54440c50641250024507040e0508490340f2900001142d0f848119100d65120301c4840e4581d40c10070013803500c02d402101d80c4010301c40709a901901c140601c01d00c9a4503030f281c2d0070100d001d0750b074100c1c02c80d131340c080e0005018091880c09041c0076054140350301c800c40d1040f04400001271060162000d4170300f5102c03c990b001003407130325645404000d40448030700b0411040200a98412400c0108901d14000d40301d0409400000b249000240c11110310b010390005100101c8104000941b010455051000c124100106c454590ba100c4405203120a0540b42e00603c072800b03425082040d100304540300d0520940c0038000c148c1c981c0ca1039078560024990341070081c0e0009140c1300f14807074a2405594042400d02d000c420301e8140c480010400d00d50200c680c554ac070400100b04410041d06010b00072a601192600003d0321400100c4c940d645c0c011020090f896803441d400c19040000a41299400080041003404040d86c3c1d800c00d81041d0340030240881e051482c00e0750005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 700998030 1250 700996780 700996817
    0x906020c070b0f121518101a041701060b0309010f0b0d05061614031602190302060601050d020c06040c081911010e0d1a0a0c0c0b0105010c020607060e0d 67
    0x6288981ca20071450800320043c4c201c0003002000742801c40074180451a1800030b885010003603003600403880000b81d0030309040740e4412620825802403e10f0301070049602c02404901000c5030102e4050744c031802c0c810984050520f0043c11903400240e009580041800040081500303e601c6010022804102202101c8100106416580c60082881e00000c0000e1800602c095050083c142c09040443d442084685407001c03d40c42140c1c500d080c2410001004503860b810401e17000720544100c0207e00606903910041c1d03803510000c04290401c540005c0c00c50031030b41d854066900f00750645080724510f00f0240790200405c812400750310414410a03250340b0400c0072000c21084d200707402c10303416581d0650004c0111800070284d01c1098006004110320400a44242148911410840c5089043d400c0080c0f81d03405581858a000082000052803800401c4103c11a40d04450090824a50314945032000c2a824003501c807000d0720413031400110341d03594100400c4030710308007031690345040240e207068422a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 700999280 1250 700998030 700998037
    0x1b05030402182d10142821020102010c18120f0f030201060302030d03060e0a050402030717030904050a0c0c0b060103022a060108010b010206040f0309090906020c070b 73
    0x20b0350080601004070303180892801216003003204125103034808900c4409007110f007007040e40307802465000740b4104000e802003100401c0c050548200d4006881072280005101d09441c0054040c0c240d03850f481150000640b541698005c1c100030000d010b40d0741c4454448003204c00c11000076030155080002c0c0300c0f40030740b145103003600901da5001071000c80740c10700e411010081d00740c0104680749a580804140403504802e01c1c45149032080d0300108200b419441407504005103c60400281820101c00340316443c40f00031541d0380010303000c500080643d1580006858242241e02203140d100441c00c80014010b8044000c0401c404103980912650700d0700f00b40d08045442c0c10200d4000117030043c1e003c80000343c105003400d81140c0149809030801951009200866043c8040d07511996160442d00704901030511650f801000c8d02c4008008102d86000042c1d102d0030001d10041c44600d00501c80010540548a04005051000c0040100f000342c0d00c1c20000035481704c080780d0340b60b215580002404c0007014046 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 701000530 1250 700999280 700999283
    0x12080415020a050a17070c0b1c0510170a0b090304090e0703080a0509040e030a030903020606032b021f090201020114040c12020f06070803100f26010e010f1b050304 72
    0x44c00c0d80c106a8807000c81e00110800c18410090080040d500800c85505155000e002d1400c00e003580c4964a12030410754070301403007400c1d01580c20300c000c00c803680015500e0041100c4228401d00303088811001105e0a000b0b0300d010003020311006500303000c0ea00c6030000141042c1d074000b076820001003103541c1506a440c1c0d030034440188031603001c000340442c00b803150002d019107400141020984034810700c640d50464000d103450100080e80c414907002450787c10401203401136010740180040301c441070000d0706280b006280c02100b80c5564038170781040c68420810031303042034001e1046c90046480c114148000e011507802c280d0044d0300342100d00450341b400761401405564031459000c56a07241c1304d890004180b8954041c2d901c94030340b05080610340c40300c400800c0c40078401c00800c2d40c4c0c1c0c5000d86241400c0400f54100c4261299101800d214814212559240c0e00000c9480f000b0901e102200241c05410041025116075080c580414100e19468102011400c40d060700c03800c054219220840e1140001c450 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 701001780 1250 701000530 701000533
    0x120703020a170102190809070603020903030a03020304031101020a030605090a021809060a030602030109050601031107050309090c04091d07060f08011707081902090c19030f0612080415020a05 84
    0x404001d1084002c2c40c0b80c9503519240009800e01c450150056100724a4210b001c0100d03607032404000b1030450034400c25028101a0a085080c00307a0b24020070340d6400b0f0b04c00030000f031560000c0400e05050080100e5860546444000e65039200340200c008c01419180c070500b401060800046201d02109009840e008044050208541384190080042201000c1c08403038106c4944000030000c110f9500017180a0411003101040038100b450006040700c1e0b11000d1841150000c1c404400054030101c00c5507000f01c400c403860b80480d00c2d04124142148110762201850710b1804081071401404000b000c0f120300340000550300301980c1c0d4001507402d042c80d852502e0000f9144001440490440c2c20030b00c5110100004495109072243d01041c58203201c80c3c9003d68001c0310300c00d45030851800360021684440d4050b80d0705d08107070b018240b03000c1120407101c0080606440e000c0581c491241d80c1e004000410450450381c0d4455902c0c140a0b0a590041c000d0072014255251040d8046000103115850180e1000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 701003030 1250 701001780 701001799
    0x40615060c03050d09080d020c010605120c010801180b0904140606090105010c0b040f120206090d1404030605062e17010305070506030907050a060f0210061a0c1203040503070212070302 81
    0x4075a2006094407141106c0110040c02610444801480a41f40c441c4880000141e4035040804006c100d440ca900501d007164001c596441190341d0111550381155401c00800700c0c11130031b01d08824017504244081940082480d000c00c018485901030003282e4401001c15900c0644450b0240824407109001385800314014500d40000030700e81c04040c592050003031151203810595a5101482c1019959400005038001014028070280500c21004e2200c0241026143c0c0001c00030b0000300c5001e5480050704581d6503c0c0080c0c19a00d9141e400d1000e0103000983c6d820700b0801034260300c00c0c045540c101c1e80000c0d01d400d07001c0301540803041400d0b068940001c011f0480926040400071540c4c001812144280602540011a13031038006a8001074641e54440903115213103040020f103058074410348444070350304052080100e107103501d088204086c4480c01595072440c020415514101034542c54644403040041000280238011018000b894030844000b03201000c0c5000c0310381d44410500000c1d5000134400d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 701004280 1250 701003030 701003047
    0x8150a053003161403070b07050724050a0e07030b040b19050c1903050f01060e04140c09040c0504180c0c0210020109060b030d050d0209030a0b040615060c0305 70
    0x1856024406402034a081c2084115165141035400c40b0703081560503040030340c1060030003614661038121889440c00039814020355403600200c0341c8004d4060814840c0000da40002c1c405031042c0250000244031014010b501201040750040800303c40030303d070041c506000e100c0354010100b168421260031140105464640b0f0301c6205500c040542b1003082c00404020801000d0002e005151040ca0107003082500c80d0100e598582040406009800c01c2500d02400c000f92000c200078894152803091400b602c0041020b004180184017014003400c500542e4020407441d800f190700148001750050790706218544810710151200d0141d800b80038520740b680c22030600c00760305035400981c40d41050301d4110300c6c0c40b245030040751030300340149034540c0143d44500124060040340d014120003542c041d00240100c0940100c02001c9009511741d01d64401c1e00001c106059582c00c0007803220b85030708130500a0040c107103850704078010400201142034507220002c0c005003203402250405110394060301d9140c68503e44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 701005530 1250 701004280 701004319
    0x90203070e091e0a05060a0f03051c0806031510090e03030a0606030209061b01020910050306011d061605122101090603330e01060501021c0207170f01090308150a05 72
    0xb1b007021340002c0c104200041401d48210310600860013480030700510080380c10f80c41c5c4009907a2241000b0700a525003401559140000d80b00d40e40302c10b03d848140c2e0303515003d0000645800d15400fa110490801c000c00c104104007100039402252182d004000c0345031340760003e4091b40254800503500c102c3c148202c0b0201c803c180e500055401403000010301d008081070004051040c3c440d04100000c00c080100411540c0000c41e0743d07000e0700102d2104462140711400980e05121304054150140741800000040200812000001100190300561110b11302603001d40c0c143c7d105195004140c2e00d100000802608610031042540c4d00040c15208003000c80020a90b0020756174942c03070f050181d00e80140c1d00c0d0080781c030a00406000e9680040303400340c500f000091501119003540101d914003500510f40c56500060712a0440e00d08880303099100c4625003085007018070403628241e2950034444c40008144c2d0114115100302c50068040c1541d0003003070144592000e02e406030542021542e0300514000d0034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 701006780 1250 701005530 701005541
    0x6020c151c0e010c26010305030f09060408070b070c060503010f05060c030d110414090115030b1f082203020703031b06060b040305012304030e0a090203070e091e0a 72
    0xc40751004209503625840560031603c101282c4400101400e41c110420b05280444010100010703031104040e504545609440e4810b10404c1075000600190f659125152103080e500240304010548542543e60309081103143e000e058200d034030705108140492060300a900f680d05032440202100f04982c10401840070315031103850040700e80d11050204460080050203022a20864907003c00c0d00c0d14503091644c0d8002d02c03205d101c24811400ca0b030061022801403003d0303051481803481c005c03408000304c8005c51342003420000004904808400031180d02c0343c11550352030058045c04c1e0030340c03800c1c0e1141703198206c2c1041b02c482c0280180c000e44000c0011a1051a02c0c0c5400c01d080030403c034600c560740d40ca0300704440e9254130503e6903402c045000c01c2840b60a02c12050140c1025101c1ca1500d076100b0707104a42220000e10040a00c100c850108078203440749540040984244078085650b030401c00340c080c0c40780804080091041c0090740008115074861008a40c0c1c41d8011700b021802606c412100001902 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 701008030 1250 701006780 701006827
    0xe010c091a161b05030c0d201503090d08070c03020d0c1103030d0e0705030307033c0c02040b19090f09080406110d1404061116080706020c15 62
    0x20b4800c0c040c040854205441d000c02c3d001e00e10764800040e8a44001d050410101804c000d1092407185080b0020904900285203103004210302d00001d4080d810009004510070f1440c01707441035000c0104050140c00040300e41a52035280c580000c0e0340c0d035001003100c040984201c000c00503004076100914040c00346454a8030700780b045006408562240c40401d142d07800c00e068848040391240c40c0655804004e106500260030103034061440c00e852510040c01004180ca2101c020710416500e540c4100c0c1607030490800d000c83c00a50100c40d4821050007001880001005e0b88102e145c01c0b0307400000d2416411003a0201c00c00000002c1e02860540c0610040c10031032100c0030419102e002020000b4004001400503001030340f182444040c1e03201c04103146c080c5401c141e4080c00a0000d141c201481e05070161000c40d4102d2030300d81070341d036140051a41000c4c49000031f0b54081c01441408104460089031107819102c090f070807100007000500c10040c041c40040c40340c251400d0204441c411000c41c0c501c6800651 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 701009280 1250 701008030 701008057
    0x6040509041a1906090e07060f0c0605041a0603010917250506091c0903020f0303071401020c0d05030f150d0503041e1401080f150a03060e010c091a 65
    0x5803000c9411580b01e200c01c55141ca1030325501c00d4090400802441464094213041900300040340070301071307032654130b000342e0203868244082d029500c0c101d544940c0c444041150b10820600603814103280c100d407004d21040840155000c0180090001c0c14148611400c49802c0804460b00c04504000034049501803015428078030b02c01d00b800c8441042440702c03103140c0da12a07802001c403864024102030900100d01c030800b01090007a01c640c8215680004003009490f0100c0300f000c40c0000c1c000c0081c0c651311820200621540312600a5080c0c45410341c0030b483d00054000a58600351055075040340c481c0300880d5000d12540504001c286501c3c00c3c80e101202d4410b000c1e184155030202920344618540080c0c0c0031601005c0744402034142c0038a41c1540500502c04050f004110082680c00a0440c030f1000f00701912242400c03001070341c01060082c0a10408001520400030b090301c80c280304000d401c508901c1c00c1c49600384100191610301c02d6040c80101c450b402c9003203000740c140c001132052562140101c503160 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 701010530 1250 701009280 701009303
    0xf130b0a080705090414090f0105060d0323270108060d031409030111070602040305010c08010503060411010e06070f0b061c060902042a0e0102160b21010617090c0604050904 76
    0x1b81108040781801140090700420344110100382840c00e41d10001d0541303001c1c1200c005000b000942000c034540b4449680d01c80c0350070740c510840b24941907000c3d0b0744519055140c0c0031072000400000620a2408490aa0703600342c09944010900031104e10b60000180001c945120030703900343d0840d401402001600500110b084000d113003003c0d2417600424030035038603160300140420401c2001d11840d00c6009590410442541c9098002905c070500208040d005e0b05038440d541c84540e224481046070b84d0f10040c00903841315980d080c20103510501d01030480700c6100d00c2c0c000c1103079483c0c1640039074500d50031200684400c1c0c0c0c10f030b40c0e410085c000405c81207800c20703216903250142e40c80462507420700018106241c202005400c06c0205410054100b0301e065402241c20044002070800700705003940d4a44401c640d4500d001c0100c4000c0c44501c481d101d0b02034908a0002c1140d0354040c41008070320030440d02020003a1102c1650680720340000783d03000c1e40800100010412400e000000c0d40d8818007603007c0105 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 701011780 1250 701010530 701010551
    0x61e030c0e06090a0b04032004090b0f09070b0a052214060f0f0412030806040903020c040e150705040f14031c11010f0516031b0c170f130b0a0807050904 67
    0x40b070301b007a0022203020740100f80340340c00c042510302c04070944c02d01101c0507c00441143c44051130000d01070014803400f80c04000007181d401c0c08004000050203003044c4141d1711410032000512a401c0803210707442440078003030040310b9140985420015a40404184e00c580f0400070208101c0d03a010f22440c640046051040c240f99490407070103007005144800d007a900c090900d1900030070314540242301d944964600014000425400201d1072015039007580c0c00540064000003075444c100340181f0540c0c00c40f08210412400a5200010340110340030140000c0e10203482c1c43c1c0d9102c51900c003039140c0ea055800340c80003080c0c0724844c0b04810154207640c240264640b24104c602400c2d99001440514810f45075002d05c10f1501d18060600d4001c0884c8c48d0070070205001200d034040c8286040542020000b103008880244141c020100686842109046568040b01d41c0b00e0011a0801402000f0f810781414000440421510807941401800d0b50303401900d41e075001056446401052166821070307601c0b410400c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 701013030 1250 701011780 701011799
    0x51002070e01060c17160b0c090409050a0209090706020d0509062709101d0903090303030106081506070819020c1801092414030c0a061e030c0e06090a 66
    0x9003c0c0c8040e81d202c202c80c8480d8101a2004900f46002d031038040000c000445030014000890030710386034443d02d26910740c1c940d60042001c0e40200914541c0c0240f0700f20000d42000000a0703514586442520f040d5200d41c3c50804036500d402d00380c410400580c11200710040c12074420401401e17141d40050401d82010428120301d000c1420311215480b00000c0022240d105180010350241d12119101341e5120141c02c0072014007020800008041e440c80c00100450342d09002801a01e0710b00a002e012a5101e41e90303000020040036060fa00740e0000d00c200b641320001410504121540b107078200039400e107040f800f0110b89102140800341a000c41c01008015501da43e928002c007038000304050881342c09541404070704011035805000101121190390345455100e00f0034501c0070122103142200058409140c00400e04144440f164942e11a81110006c1512a00011198040564800301da6010021900207404540c030030302d04140480e0300184680c41c1403818000130044064045c004881181d030303916140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 701014280 1250 701013030 701013059
    0x1801060b0a1205010e091e15040f11030102030c03011e180b030712120507030e0904120f17010b0a050c01050a060501170601050f0309430f05100207 65
    0x1c5000498849081d050750002e40a000d01500d4a041d12000a041502101369220440995048822a00f22030b002220f4810b00c2420703c0c010038548607203164582403400c0002449026011513a01c400c01c8014020f500b01407082d203210b00b485030801480c61b402c3c15540b04030340d40d1800004a004080c080302080440b810786031071780462440d1002203000501d200400d403c000c02c40c0c0000d043c2c40d15003200480414100115807101c960b40c0d04041c0d94034003482c02c04903140003550120940001005080c0420810401e40c0c2c050b004050740d440302c013034a03005603045840c0358250440c145803094050043c401c15100321700810303c00d240d90810724074126036007200d203007034130700c01c541556400313581e00c0c410019940c102681d2030300701c5c0c036540f4118945d20300f06001805a000f03001141b50403000200000b04100410807031403400d2258005200301900001045007900038078440b10700b46800784210780507513090a41c0000c001382c0d4642c12200491506103801c0c0312080e400104010114402d8100010300c400080082 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 701015530 1250 701014280 701014297
    0x5070c020904060e122a070b160c0305101802131a120a03020f0a031b020a0b030a1a19050402090109030b1f0b03010501081b0415120b0a0305061801060b 67
    0xc50f00c98030100c40d4110b000c038211035203a2600444086d030a00032100030451005495920711500d07260b6580c09404104801c1c1100002c04598540da07010052150000d40d281403000c10840c284090f0614031580d400d00a40040029001404042c0c00c0c4a408420f8010011500f103900c550001201c020740010307103c070b1900741c1c80802074114482000615505100c1000c680407903000903c0007522566009000c00b01000003c8501d13820750300e211085555540c100401801d0040e600e13070b102d04140c80707548028000780c5420a0000807030815100541170200e0306090410700512800c009625042c01e000282d030001c0601c0d41007181c5948003100040c000d03581030380240200b840000c88039204070800d034991021904189400c2c0e80a02c0100309582e4400b988651001c4080e0f0301c003280d0081ea40d19416035002d43d401034240c1c1181d100481c610180d016036040718243c0c1c0544240038100f079500030300c81c13601c11704d00014265411180c00a100181c181350903248050f40c0000000b2281d68528818419800c075a11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 701016780 1250 701015530 701015563
    0x1f0c0501020d06091e050412110705040f020a0f0207050109031502130b0417010216080a020a050d02010c1d0f06130f12050c09190c05220509070305070c020904060e 72
    0x189080952200d04090b01c2d0f004030f00c00c04106c01c1c101501c0d00015818030014800070041166900562003400b400084004c0c0310180c41481084501104500603400c44094440010401301104ea1a0351002500d00216281030312000c146904680380c40c40329503083c81d4003035411602000400c84860324114103c1c000c01c0d00000d005e446500b403100c0c1901ea0900048005816030041c01070080d02580365403900412540701710b4207035490b00300e04400c1c1d040500030740c00500740d802804100e00d43e20b40c041d000790114808540d2005166880940035030100038480e01825042002509164644d0800c040100302403912040f0011a0790f60380c0c5d0403912200c1d40c40c0c00030a00341d030b0000480001c00504200180780260215401d040a140003111450381c5101c4505000c0055140e0701030040190040b0100c610002080224400112020807180100781c400c0c4102d901a91a680010f900240f0900c0303070300d006071025501d00c550501c4580030080c10300809841038507000d6a400e10421b41c806c0801295400403a51134 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 701018030 1250 701016780 701016791
    0x1512080712030519240303111005010e0a09020604170d110102030405060f1003020301050c09010f051608071406040f02030705100206161106010b12061f0c0501020d0609 74
    0x19110780c901e01181c0c600000d0600f00f1003400f80201e10a50010140c1c00c5046000070200e900c80c11030000b2012407404a0301000640300c01006255105000c10b20002c40d040c1100d80f84040150f0b114121102489000001b0700300c2000700d60383e80b0b095042003400500082c0090309041e101c00080401080000f03000f01140e101d11002d5444036004100c400c6501460b034000c504500d0551501d5031516401445030107a401580002003411001c001d280303016613009802000a450302e5041d212540c1d0200b5104c90219603050006205644280101d6580c6401c00c2801502c0b000f40341c0d10b05074103800602c4201e030362110059590625a40c10000d07940700702c3c011400c9003459400b60040c542040b030030f82c2089015400880d0380855041e0006490341d00004441e04081c1d0023014103804861411520903144c08501030400000f5072040300c000609030361012034081c01415101c140800c61080103010314207480d112104602c0d0103681c05620b40e5003400303018100143c42c2604070782111003205d90a4200c03000b400c2e580c0c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 701019280 1250 701018030 701018033
    0x506180106020c10030b0105070f020a0b04081b06030103020d1b03080a0e190602120c07050909060708310c0b13060e090f06100c02180a0b0904120315120807 69
    0x524032041d1301c0c54241010011103000500007041440785503005045a5561400c0c10b0441d20780055080007804400001511261101221500c50b022070b82c0401c1c2e55203a624154002d407a01200300c2e4102da0b401000305000a04683d14000a0702203c00b007000b100d07d4803180040440e0820009080e810342566407054855040000c0001e28044140c0d4161720404d102d10a0200c1c036000a078480c0340306003040e000d64440101e243c00c0e501d03003e9550841c0d504140c900050000d0020f0004404e0302540058445c41c0d103655618407428a00390a0081c0481ca409800e21019400c10094525060140c081c0c0000420191a0041200c05034803150304400e10003001081003118542c441e03110303c411103080300c0303a0205007003141803c5003024002d010b1510805445c482c0001541c0a010030b01603240c0d000c0c014584203201c0021004645a04440c6100300c9418003441c00c0d00361030a0b4450501c900d40c0310107400201c84407624202c006100b0310340258020404c010002c1607090644120020103031280307030000c0d6100710740e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 701020530 1250 701019280 701019289
    0xc1804171215120106060e0d050c0a06090f091a09070c02030610091505030a02190f140f100f12090c090501031211030f0a0e190806130c03060506180106020c 69
    0x2003070400161364540b6205104141d40301e40e1038403410004503140054020103040c0b003420010070181040d07004482c010001101c5030445030040442d26a803c0d02036146665844840581d000c800d51421241c0ba10044224203140040015410403c02e00d000c1501900980c0444c2c58283d040d07500316800100c0c0b59007041801c0060082480313600d506259011002c1c03404010959030360904000900c2099100098032800072104004001010050140b060076665031a520516904000030030703004e0700300f101089086003002440750b40702804139500e0244207402c10b003044480c0c0d82c440141c1ea01003521131440c100402c0700d00e036440019003c1514000b41d5035240d072810500150308400d00c9000e10a160852080302480801038551601000445560320100300c0d4003150406aa0f80800782d0001242c543c201200359220149070580e04000300b2140d142d11038a8412800140c2c41c03000a04c0c540c01081d0520001c2c00c140c006d607802c020090f000c6c00840500c101c4074091075000341c110f20010f9000804200b00d0b0f140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 701021780 1250 701020530 701020549
    0x11d060c0403020a031202030c120408120c03122203021c02070503060a0c0302040e011e080102090a140a080a1401050c030105060708090111030f04080c1804171215 72
    0x10050003151900d4034580c042a10300aa40c07101800354850780e01c081920b90300900450300c1c50900d440c1a1461100d4503a00e51500c1e411034010a01d480c441c0302c5007030250342100801c80d1031141c91070700114280b003010114103039030103401400200750000003458990306515001006110a00c650041c05242000c08221607a803d0700c42c02d44001c42d881508100081d8601161203500402280e0f800308a9122108055010344901d6006180060030100009000c0c580c034455a91098165142000f2080d5141885402e0780101c0c00301c564084c2424004001304401d03800107801414002d000c100c40c081d580e01e811800c00b80b20900686d850708811030130300403451081c803d940c0d200d070a406e8001d09650620340410020700400500400310031001030b4418241e0b000f444110190074032001160342e58403200c94081001d80041c45101014031a15520034064901840398802c0110155580d0443da5103646440c20f98611a040010081c242005601c0ea120301824040e44140781644c080c03c0d0202500c0240000e010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 701023030 1250 701021780 701021791
    0x30b06030907141c08070606080a24140105010c03140d05040209010b163504140607050309040203040f0c14010801050117070f020f010f1505030a0807030c080c011d06 73
    0xc1100e40c0b0ba1503c1c40c00d03c082d10702c103d421800c0c40341c5414061030f00c4030003230085800801c441e100b5401408100185100c404000c3c201001c01d8000d0303214040050001c0d0783c100c0308400740303000c0d41c04014460381d4440c01c00c84d500c003402440c1040c240d0007000352601065025527440f80c80d40351180c0800065007407a141c1203004000412500303203000c400161201152100034001040c42011a0382d068810f0030821944c900d5503140941154010201100d644441e40544a2103142c0948012001020300c1c02c401a01d020715007110186150085c6241044000e5200078030032151042c2103203445c1301042004204902a0130500c4a0100030a11800090f21010059010700c1c104400701c00016500c03400100580e4004810742040e04211903090b9080c0e04050041007051459071030101d405004540d60b8001c840e1084042058900346615602810b403a104601c902501a4004011940010303228468000920740504425403e1103071455a80742510b20740026104800c107100c080c841c44000600003143c100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 701024280 1250 701023030 701023039
    0x120f07030e0613030f08090907020c03060a090c0e040c0b0a0504031a0112022b050106030b1e010e1b1605010c1e08130501140f0703092001030b0603090714 68
    0x45000341601c3c002c1c4440c3c00000e1805900c103d0101c10000b60409607540d2020041440000d80303001c010084da900c1c66504018071a1264030041680c10305144180341101e074200f04107000c2c0c3e50903e403401341909400740c0115007460407d500069101e01c20005851070821a039103480c1d85500e5404c0404400d07040d03203001c264484c0d10f503004115030459180030001c01a4161092071110f60401900740072608a904081a0001c00c00b00312001c2100c10350020080d6817041110001030740716000620000304144c485001c10666510040c45110380b000c03012a8040f0303450340042c030b24540003043c4c10850b8110b4040049140c51481088040000038011900082a280344c04503d0049003003484030040ca20000c0c034014042c0782c8e008280300b031409810640e48a81c1110090025030401c10000068940440320208100650703c08070301c15602c280141c000710b50b00040709900b2406000d214100001107072104c2c506241e5540c615041503120030014611403003685001e01040b82c80c0010084400e5059044240302703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 701025530 1250 701024280 701024287
    0x905010b190f0912060603080a03060e0901050606070b0a1e0507080702010b060a110c1e1003150608060105070203060f16030b130b0d05061003110102031812120f07030e06 75
    0x1d4580c000501c008480006021074007500300d41c10170000030710443e000548044c1d8000790101034103405030440000c641040c900c00d031055a03554480c0d4200c4200b51241a807094003001110301081c05911003d0b04452030480c0050204202031041d449903d60742c42041c405501c030020850303141c1c0c00c524115030141007800280300407006500014005c2c032402d66404180306008418a6100b6030402103040d80c03000c054601082a00c00c8404241e20004039403000703204002e052051070001c1d100e4040c680d07410a41000f48000d40d030600c03000344c1c1c0080006203428100302062000c0000340e901080000c0c007503030860303180d00900e0900c0c014060028400140341c00c14507091201c80307662512040400001c00602c10000111840b420001401d024507050000c4c100d07100384001c2c0320340b4141e80084501224822140d44542c845c0405c01683c81e4010340d60b1284201d28010000c5109007410f4850010700f40801041d03031944120810745665075008401850303184980030509908044d00422851840300c8101c610a09 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 701026780 1250 701025530 701025557
    0x1c0e03060703020310050303030a0b040605010504060c081c021812030c030f030901180b0f010f1409060f03010603140d020a050d03020c150f070e10020d180905010b19 73
    0x2900d680107040d07141055400800101e0340c40c0c03040b241c040604001015a66a806c1c5842a01c0240509010007445603140c5100010150f0250085408640d050380360200c510840da2603101c07554108403141810140c40044c004098411440105004480c1c0c0c02090900713004a400c0c001c0c600100140c0c010103510401c06140da61000000340d500700e03a070202c1015a207503190410356014294904424200a000404407c201300000000b1881a2003180108482d6a0307105605981c0c00c50a21420182804002c94800107041180c4d405602103c09801c5440d040030a40c040703070031250300794020b54001c2085101e0440b00707041400f0354078481c102d61005000d0704c90305031222a29140081070f41c0051540c0024100f03030700342090040b1103d50020f901c0c80351051034149032610b0b01e138000f159131500080c0708504485c0e01e03103400c46201c44100c0d0786034020018450360201c15190744502c50b804170007440c402500090394000a000f10380c06040b403541a40d4441c2c50500340c40300743e000315000c690b0620120200078403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 701028030 1250 701026780 701026783
    0xa33030f0f050c0906030411032b08041707052805060108030a0801060c05161706090106061e18090e1506010c0308041b0b0a18080307021219051c0e03 66
    0x940d921005c0b64a2552500d07a80381072484040740007580c54041c05801c03041020a02c1c1c00b8042c540310742c10b00703955080c8881d864504490108045400038a40040640084200e40e1260050881c0900c154116400d036140f69400400c5010752940c2d1000d0b80d4049840c40042050030b10486006003082d20046007415070000740a009141d05019200c10807140342c0041043c0a4204018100425203d507001d084984905940004e81281c0d00040780c984500340c041100040d05106500840b0302e11b40d107071000c50050b1246030708031500c4a50542e00b0003642032104070040d5040700c0c0090040455110026980f1108802d4500304030509403d00c0c81c0300c1065042201d1039030800707921344046a1604e0010010380d0b440c6804c201106401d8400504903c01020126200b0103031002801c1040070341e10341120207420540742510b4408580114a44c0f6001032000800505000c0c8400705c0301c00d02d403020364138140c028191b0003020041d0400192440da00040070384680e960192081440c030201445c1522030043c401002c139 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 701029280 1250 701028030 701028037
    0x60306040905071d010609080312070f05130e04050118320105040c2d0e0a06031b03110604060512042a0509090c0a33030f0f050c 57
    0x40380600e031240740756420031600b8880040540042590b0f050341c0442054409a210424001d60000c01c1615174085241c0d039000080e01c204c0c070500641c1c125a0355a401086030b90035400d008000500c502441200d078a0740c3d151041da4050681600714091030300c0e09040c001e0a4960380b422803840c6085407005c40010038400c0e032603425403020703405200000700909003d01c10180302c5009080c480d5481c000602c410841000000404c88107007942c4490071305442d24560301d140c44050040c500303170984075904009070113002d0380d000e078040c0b1003070303400180940c1c2c0b5140c4119a911b008070b84c0d004403000c4d40d03051041060391949401c24107000d40d0f50030b0410f0f0900c080074045200720005540047d52440c0010104915640131040c190032030310044008400c1d4101050594269019851003451140c00040c034244e07000441c0020b43c88000e050304030781c510b00103000000918140203c1024805829902415007280300c20501a41c000c0d031300090900ca50454400032035410b01e4000c2c0d660b07400c040501c40d111004a00340d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 701030530 1250 701029280 701029291
    0x30c06010f03230709021210080c130e030c0a0804230d06240b09010813120503040c0305011103240f270103031e0c020121151814060603 60
    0x39040f0b82191030a01c40d02d007a095500140560b4000030726408a281c005121358003400b0007000c29607099840b458455294080d183c03007070f500000b2800b0014500a45500b02d030710000100700680340342034211503800c0c2c20000c07050800e40d03480400040402625181c200300c60803015244814100b0b0507a01070010380c5c40c05c403240015001d243c44407487d10080b00d11041810703528110030600e44c8003d60b1003020303008070b41101d00c0b01d50101d0003c03030000306590801181001c55507030001308440034085180f001c1e100c035000038105850360321100340d021001903400d01c240c0750f04010144044d91286044010048a00c0c00310024140f00400c030383c0c83e2001501d0304d0800d0b080300c2c8001c590001c1050242e541031b080c0a10580403d210406009000005141d088454198200140d04150100340d58000c4151400040942c000f0700045440d480300c0e1142d462030000e007a80500205010480030854038001d00e141281c0e0b00201d8002e0301c0070b805004201018410040601c1e200d012959161600314001031032400010074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 701031780 1250 701030530 701030573
    0xd03030b010521071215030210020f0106030b040c0519050918031611031b0105090402070609050d020f070612090507080601030807150203010e0a2c030c06010f03 71
    0x3900059a03000e5015604210410340d004181512032000c0d40800440580d941400304200290240e04c080b0715000b503510120f200384e1a128018a180e080c0309039001e00f9810081107002c1c070078444c503680000b0b0140c48001c6004d0510060b1074241410015045900c940c4054403030141e5100754003e0000c2000703007900319402220050300b6a41d4480d1001c1d4071405601416180340000038841010407090a59250554010313129481001e1103a0141691800e9100007944160f21200460712558483c80042130010750251000d420b0a91907505c240986004150840d40c64004c0748250041a40c10060140340c501c1c010000c040d004d06c0d0000140110b4849412146d0040d1a88002c41c14003904000c804020144003040f03419540c1d50303003000040c40d0001c80f0103d900041140c01c400c800394103402624142d0303030300d4981a02c0c41e49401c2180340051030080e6a84c5002c1c00900ad00c0c03503e034072200d0301a802c00140080070b10b40e01c1c05101d6225040c02c10507088240b80415101050000c262004982d140e40001d044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 701033030 1250 701031780 701031791
    0x10020c06070c0309091103100603020a12020a03060f081c020303150d080f04060906030b0d080a0c11032a030111120c0c0a06091b05130207020d0210030b011d0d0303 72
    0x80881e000000303904000d242c0b0703090150321b0300340340d0751040114030800401c401d00002c00e84404044003644039104402d8009996444020b1101205500130700007450305003000034006544000c0d46a40380e032180d0200b01240c10440c0410040c1c141b140c03540b000110a4400365145290034038420035550143c02c101409486500c1d90380042000d4001180c94048039041000e403600d03542c100042900c5910f014400c0040d081003081e030711604105d05aa51001c1d1f00ca44880d06100315010111127084a1680c1601c07034242030300a0220584040c0505c1075082d0b00c507146081c200c290035492010750146120041d000c3d82c5015501466840c4000564094100030f410052698032490303060410384c081c0b520301504902030503602ea000c010050740b0102c20b6034420501021008a00d1104452406540c4035043e082040c0020302c0c0072403c2d0580c02000c000d44028880c0380d02a02c03d4010803200103422400c4c80c0813a0b665441031981d5a080900301c2ca00f425000300c08410300c2505004100794159164001f401e058461 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 701034280 1250 701033030 701033033
    0x1204050f190902071722060201020c1002030c192007080304030b090a0501051005090c12010b0c1f0209091303020a0201050d1409060a1104031a10030f11010210020c06070c 75
    0x80c075014403c548080c00741d5111806c0515080b00000443e40d203400148141c0b20025041c0d0040c001e07198020781800c045e142c0c1c41c10810566020390f100a2400040301d608001003002d4001d84000103106001c0d55880d044a05c08a184c80e03a1451504200c81036241d008900c00c0080c00c2001088606580d40054001c0507a01d903054401d1801c0d107844001001c0c0c1d42003504000703106a491011008491048400e485640c4a00078400c0d030a11644440c6c135181c5050600500c035072000c00c4000c115507c000000c4411034034510403480401c0080e03800d50b0b006d0580001c1d03c40d0451403c0e00c01c0c60f0b0080d94040c1c1403500540181d4001e582c8002c1000b00906111022400d45030410741c0341e0251690354071400030003050345000d044094881c2d01c21542ca810103468044030342c11890244051350166a4002168a851018412412a1890010304500c1142c001000c0400003488901455241c5032254481d040407509210000e4107050304186002d0081d4418052041b0040c0005a215004080e508022070300d4510b6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 701035530 1250 701034280 701034293
    0x807020103060315050609060607030c03082509051203130e0603031c020a030510140d060b040c020d020c09071706040b060c0a1b060215090f1204050f19090207 70
    0x441d0b002a100403034002924482c00c4c1d4079089a40300703040c01c42c1c041c2d0041d42d41104212240c011581b01400040c1004080f07000603008008107a0450145080607001d0030b1001c1d01c4141e003d044210400008030030100c2003200b4141452600e41d009090005103040130417560b0542200c04152280f90f10f200001404030320070340c900740215000009040c5d203111107048080000d1020754820022040064a400c000a90305002482000182e601828861224040400030008809001c1c882035500590760425420166102e00c01d00c0e5604000e600034281d198074000c0301a00300162002100c1c000c0402100304010607034420140502100f0007888489140c80d50404a002810041c00c175940003100050701c100c0704c40300060a190740034400e441001981081c4619042504003d12038000964000c14400e0201c0c001e2500d007a901c04000740031508000a252100c0f803626140d081d2800400c800040d0078001e60609440e902500d00c0d05880701c801c8019241c042c0d803203081c52442100c40030350340820b85c1001c01c901c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 701036780 1250 701035530 701035541
    0x31b04050301020d06052707120209040e0a0c091802010309050114040b0a0b0612040305071a0f01060806013902040f020a020d1106070e0a0e04110310180807020103 72
    0x80c1c0219259140826242c1c01001d00d406520b110b644103190b940b4004540508503420001c0ca11500d102c2ea86580a00361052101c1d201c148600940a00c84124542c40e94030941401e2240600100702443c41070810b0b8003400341c60b070040803d41381001031141042034a100101803075942860b00280410b11804e0213401400f40140c4041220444018001408144450b0324011005040d04000014038803003040140d20403829218104e03100d9100090100303000e00b002d055007074015080307005201744440e0032144d843d004580d200d1034107426000505c14181d00c805203940c40740e07080c02d0041c90030f00d00c03a84a034071262400c4100600089503090300c0c600c1110070700c881421203601500510285c95009803c40180d00814105001845616644803c10b40300e11003d40c0c001304548090001500d0701e8408941c4525141c42c1c80d5040241c96400090b481f14001100f4803403800340008440e0b844105040608003002200d028803902d04125100e124460f0320003c2c03014155100c00b42607542d05540c40141d02412 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 701038030 1250 701036780 701036789
    0xc05010c0e01020c0f01020709051005090a0c020c0a050105030610110102070f05150705040e1021020301050f0c04061b06060e0f0718050d061b021b03030a05031b04 72
    0x50a0580144985401c03556400c040c080c00d0f000e0302c042c80510300904c4052801030404a0060f44624402c004c0c0c150545e000131f4000705c0c1c0041e045849900c2e00041044140b0a84081c0000c80d50744081c03007001340d414031880c4100c00086a114070410301c0c000009056010203000d4a1155501c0c80c40407041d113000714020080d94901d4802503499058a041001c00d030b00c001c820079101409900301c13484001030303041e48140c800d40c02a00c070a4209410295540b00140000744100ca040c140550003003268a2801c440c0b5181c034881d007408421404040c4180340c00c0d900040c081c1508640c0c4041884441c2903040103441c01e072200ca1a056220000401c45403054000405000d008075192000108031150922140b0740700e648040c0c0c0130041c60f2903c4000b00c4942911607980741d100a100c1c06c00380280d10b04001c11030091801401c01040b10b13010300e00010503800c05002c0c40742c05684014001d0002d0160300403403c2c50460110f001c1c40c100b0200c50400380c41b61200622504480b803901071880d08140014042e140600b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 701039280 1250 701038030 701038033
    0x10f15020705030618100b0604060c1e0b0a0e0d050a030207032a0302070b0906040512150c0901140306031e03070c0f060806030102070c090c030b030102211311010806010c05 76
    0x2428411091000308044980c45c6606020340710396000321600901500c841100c02800085c030703151820b24115140140a04111540c4108800e014030300b500314100208030034000d00a004050070803040c02021640310703c1828440f80c0007401007580c01c907008003d0f1190804581405640c903905890211103001c00b01c6100c04c0c1c041c02144100042c014652540c0e8849840380d001c0b80e18440d00d031030b10340c0740600402c101550b000e0010081404a81000006c581c0380b6000e40381114041030280030f200001035401c540c1c4440944002c07507500031560740603c5445040e48240e940502d075080050209848452030204200542500e01001d80003038000c1084070348081c0c121078010205a141e1400c034400500c81e01c12500000e407404003045171840d043c4211401071380d119000c090494904000b8901800c00280350806160342d40303841071410744084c0001c14070301d500b000d100684104540ea0f01481503401511500c08032551056040000b00d401c038900d00c0c000c0090800981964034000102d4414055440003010b0303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 701040530 1250 701039280 701039293
    0x1302030106140423060409030e101e050a050405040c020a14070e01060806092712130909020d08090409210206090313061206050405041b0509010f1502070503 69
    0x2c035801c10b00009044608032418084414640440321509130900001d0040722186004104585030551101c1c8a0b6072080c180184480d400c0b00014401c0110320300c1d85030100d80da000c03201000c0300248003544c200000f1414424140428804028060f000310b004580c000c0760f40d2440040840c0c001c11000d10748030350103400180d04900c0240010b4998000384140000c2162090007c680c4500440d44140b00f4280641100d049503100d01c1500205104181c400b00f80c902d14903084100343c1c400784401d0340c8420038080c40f19a52001d044558080c0e0b4401c1d0b000303054031481c02614000580c0c4001c445019070350030507845611102d515000400034403d540009002c444400349164440014011801c0034100300e809840c140e82e0b500c000d40c0d469202e0f282020000c0764106509114041c06a02d00b44c0e8400d0300c03403000040d0141c5030301c0800d0859400303032002e82c4c83c1c0c0c01a50048841001c0c4940920150000307031105502c0d5403505403c5007030000c1a01590741e5402d030bc000d070200d003a0302c00c10504005010083c115440c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 701041780 1250 701040530 701040539
    0x60f12031b1b030620090103150e07050408060f0903091318140d0e09060420030a060e090f030d1a13021c05010f0512030d06082407020a08031302030106 67
    0xb451030103448110b0700c150800740d0307081010100000d04083e03910300090b0103250454440046000b0320713040c0d248100c403000d40c11012404000301c4503014800c104a88603256075905120001d8503040000f07200b12042450a002c01000003804000c0d80c02034a800e0f620300003000c50380c1c1034140c06015a4a00160102400020107042c006544880c800b1000301005466090304400411681a040007995a40081d0403502183d03c034105507000d4030200c1241e5219018804c940f03a001c07041e82d441a0340d02c1c1c080d941c454070b082c00b1050658410b2500105044001d040280c8107040cc2d6407030f400360315250342c211a070343d80101005070300d44512a00c4424005128207082c04244d046040250440d400003d01c0140300c20220011020511805040c0c171410740203070700702d2840c00c400c0104180440280d103055006c04d020301c85804210340a41c001500c1c40c070014040707403c1d010b0280c003141d00c0d14904102e82040060700380b15420b0b801003240c4142ca500805210760301d54410002c1503510042d114005c0d05586003010015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 701043030 1250 701041780 701041823
    0x30f260703031505011704110d1e0210092718050d021209090408070203160f030b06010c1505040215070305120f04031223010e0a060f12031b 62
    0x45020a209a080380c040d91204011034540c03400300d40c0390b00621151b03c08038000c54896141c481d404000104085010003c1d0744e100421482100d4004061800584005d0110310700241c41c5880001545028001c0c81e140c041c03801980c0802e8001b852507200603484296580d03030282c0004680d40d1054800da45031110924240c0d50b42c2e92030510210040c0501d0307128140600000007180c0081300020142465600c640d102c0b03000036800f544080b80c2c580b003401c0d44040c01c3c0c1c1c4180460320017010328501540030189542041101307450018101c0d4100b1840300c0e4600c0000d0780d0700920311000480c003140001c01c1d40d943d1011070155100000d010307100480c0030401c081016408002403030640c0700d0032840074103034039503400600007001c5c00c0d50000d01080c00d02e4986840c140003580a00321506100f5460390001c04c43c00c0050591890a0f04500307104075464042101010560085400500d0700103141c0074041e00c0c00e2240491084076a00080030450b615070004040b1000c4950201c601d1340000400f05915101a41032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 701044280 1250 701043030 701043041
    0xf04061b0f110106050d0b090a0f0803070201050c091e0d0b0109020a030f0b0102030910030f06060806090601170601050c010603170306100305010303020304170f0d020f010b0307030f26070303 84
    0xa100050a0703449200c4503202c18051202260f0018000038a600056500c468419000074004480d07445158410004510002c0710b1131f41c03581c01601200c0e628100750300020f00350b92005041d80801d400c1040540c4540c0c03503000030828594024140e81c204510b0003400120151003410740a00303130200c408004604400c1035401040d0094840d1000c1240c4070f962508901620860024180560410308c031584c0d00e41171401c0c2c0218400b101d031500061400443d42c040c0129481900201c00040d0040c1c20444c69080081e034480e0802c4e003d08061488003c40218900f40a800401207030402c10013003081c2019040941120b0003859000e030710640303100c0759400e12494603001150030a10070080c14204502d0300e800313442035905032501940603610741420082d0b90186615402001180e900c00e40c1d85541107038000303000b0b081f03880545a014fc8111258800c6090a450200030054400d0704074040c1040017441c23052030081c00075840035103100580c01042d48040b074074101d0103403070b0622900020800304056169000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 701045530 1250 701044280 701044307
    0x901031407050a0201060e19020f070c090501050a0e040b0703020c030d0516021606050a080621010b0901140a0312020312040807031805061b0709020f07050c0907080f04061b 76
    0x2080607e542d9500d928442009580c0e40c245031080c0400707031821b00c0094000b0410700c02c0000d0010b140040f280d8586140b1030640e0f008018050303550006110303c0ca0a03464010061a940055410703c2c141520341d5201014003a00c084103040d4001108810280c090003a10320b03ca50301034003000f0310320b1302d2202540801d0030b03120454010b00072040401c842c40c002c62a00d405450715941e400c0d041c40190041514107590261425a00150b4400c1c0f424035070788010404c40000071800f00104800c040c441c280304802c1010f801280725030181d00d003403442c0d5072180324284007207a4025828030503a10100c001030303003548200301e6240103070700e961401c0009000841d4020f04102d4880d551380c0c000310380c076241c1c0c030101141035014265000c00708101101c1042024458115240c45540607151072030780d40c2c940030f8200e9000804c101d198210200b451018000180f0811a5000c400d503440441e51034610401404800c0050103c070174400500042410300c681980001d00e40e45244801e03800d190003004021b4000c0198445 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 701046780 1250 701045530 701045533
    0x30b09190b2701140102150f130206071412180103020f0c030f04080c01170408030a110c010e0705030a0203150414060a090501150303050a030c2708060915010b0901031407050a02 78
    0xb9010744c80c0d4400140403014494410b410b440a45412000210400000c1c00341c50b80700d04515060005640c5140061117440c7c230030280380382c90020f00041141488003141c0b82240a540601c100d040e0412071203130508900d02c00b440c00503500da884080d069254068180a000c0394803011580f40d600d0301c2410000c04c1501c440c03000b1140002d11060045a6511080c896407545d84641030115001030706400195402a128030008100e000c29a1000d000710380140705804020381d1540102e0240200c1071010201504c07068025190889203500400c0c0d40e420285802104d00602c0e00c0003a00f4407403103c03004140007141c10140c07074084c2070000000c40a81910a0155001d501c1c0940d68000200b42c841c6490440c0c4d4503840c6d071070510714071050540c002d1010084240034440517207c00311410301180d0040404070250080b00d117506080041003407800100070720102d22980800f88030300380201d00c844080d0440700c071074007403a640d4041e803070040f000b81c52180000e01807500b8075002d0005441e08400a82072040c410350 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 701048030 1250 701046780 701046809
    0xd020102030118020c030406120e010e0d11010e0c0108061507030503190905150601051b071a0f19050903160503010c0207030314030604060f0905010303030b09190b2701 74
    0x52850300328400c5d5140b440080c1d1040000f00b0955000d04283c0d041d02d0003041e0001a01d05e181c2d0712031400d44404032421394442d00703c220030f1000150455000e01079142c0d802e000f0041c10381c40124aa2343c4003140e18040c0d0600000c03200241c40f903510010007840d0441c1d5a40c1c16038440c01d15140140c505e409c2611662030588d01e0b120f0041e1000001e1140c0c0ba14580c00c031006085030403030800316019004010702440e0404c5010005000a03104441e002c2031103410810051003500e1409007c2500000450340301ea802c1c8034204142101451017030181d40d17052148030000700c080c850200e01a90705105220003036815000e000400041c83c000100b01d1400c4601c203500074480c00c405660300701c1e1a80ea903400010041011051688190000b10001d10b40c01030010300b0000b0260b803641d4114002c04010b60000300c0144d121f2006108041e898024440501015a424030890a01d400c2004845054000c0c2220700c60f5940780c01c000d55070f2070740c8003800c00d007040f408000d91365010b150350061108001d00403c8945400d06 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 701049280 1250 701048030 701048069
    0x1917060f011401080402090a0b1804021509090118200a1e2703060608030a170606040302010c17030106024c020d0507090e07090e070f110d0201020301 66
    0x40780ba540d40104140c0d5a1401c540c1d90382e0800110b50340103010781d65000c0e40c44c0001141070700c0302d20b00c41c8980303441103455503001c0c5004c0c41003042c204c5001034141043e81d001d00410f41151201d41c0000d040d6003a031104804d070444500801401000d2031000800219550121100d1201a5900600400031176554441903a245103004103842c43c08441840005059012220b00205116401d030504500110581c1d581c5562a111030003542e0780da8100030000e41000400820301c3c0d40100c041c4046994005158000d483e0880000350207008920000c0d0600c40200c01c10802c01001c1c5002c09991941c8144144c0c0301e5850f90b80080d51002402d00e01090040750180150303825100341640c500301c903006d82c0a200041c8600701c00d41c449602410180c03810503000d1050b40f031506214010130348074550980d00ca40289240c180f0616843c840900201e09211403104d09000c0c03002200f900e02d500240070300f0034100c50312080e001220b1078190341400030064015840340c0440c1c607506400541c100d4507100040b19100091 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 701050530 1250 701049280 701049299
    0x601180f090b060f04060f1d0307210f050f0706050301080c010507020d290f06030a11031e060a050906070519050906030f1b070c051917060f01 63
    0x18052500051400403040041104540000310b2000d0702400301c0d400c0404042c10760700d560700a0f8101c0300108985840000800380e01050013048900d550541304803039288440440d071181d0140c00380080ca05403038000319134003243d001d0318102000c3c0e01c100d005074140e4903402c0860719102003d442d141e45020342100050000c3c031900c181c1c2c0c10b8840f8031010303000c000a400c00540b034a501c021403c9810401809003a804200002845400d550b08001002c4c0d0400c6803810210502c207000348819980e440c0141440b28546001840e11f010310f501018110340316260000091500013400c0a00703d9034814142200e451600c0841d0850048072040d405218640300d40085c261580701c1111894000746046c041c08003082a40da60a10b492103039402d00d94a002d1080340820402d5204071005200032525005000b00c40000f01501c140c24602840d1850411a00b40d4904c100c0d0101440760714894101603020b000e510300d000000038024101d90403c1f80840c2c0b102024980c8a010444564060311035801c00081c13400c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 701051780 1250 701050530 701050577
    0xc0e030109050c060306010903080d05220b070c050f0d03020c0f010c30020a0f0e010503010501090504090c0e040b010311010f051210050613320123120601 68
    0x6220000d803456180540130b011aa4100030582c0381040034403100000410300c002c0080586a445801c007041d58a0200741c02c0301507140c1020150303804440c582c000d0300441c00d81d10044c1d401c940e0500d004030030507010b810300910302042d0000c40d6106024561098004940541c018048240c540d015248007000e1501e8450032180110030000c041a05840c030118510000c00721180c1d0700602012100c403012206c94000103e80002907481301186056038a022403a401c980803501e0203a0034601380b40380d581480002445140544a0309014544070600303030b420020401e0246000d03060214004040f4900780c102a14510400e00c4141c6130100c80030500d030819446010000b03480307800340d15900d141001c28209040d05000003090403040e860780d10004540c03039403a4001010070283d0901c484c84c0150410780c0c0c528004142075031186200d462003a010403e4100c0c000441c112000909044211074800ca00180a0040c1c1450000810700f0008018144a01c03190f101070103480283e84001c00c6c03c810035070b010303207000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 701053030 1250 701051780 701051783
    0xc05041109060f21070825050c0a020d0305250b0402010509030a0212010204080d09080c120a1b090c110604061a0a0b181c02010f170a0c0e030109 64
    0x541000320341d646003051801040141005641070349040341000c1c3c2c0509400035002c13034038400649501401220b5a1240c3d040b60012011b02c1d00500401200060503020003402c030440003484008641101300400510410409940180c5540b149103880d10300205030340c0c001141d000b107034a4030b81c0441c172b101c0d4890b13094000101c0c1d002d401c1455545403500152035039044011102c1d454458540740200588400480807010411200096121f038103021100d82080700c161055000c104c0c88000810014200243c01110b4a030300341d0301000210920a00303542855407000000d80200c0c641811032048004401540e0300715042070300c0400062400b40c40807135200c60705082d003910b5a0700400214008c07560315844502400d1421803031080c0c4140c0f90021500000c0a548240e440c0c001c0450f98252941c580003c1c400344c103034121a203000b1f402242c00540001075207200007a0400842c20031851b00f885c050700300c0c00c2d00506040110000b9180039a888000f8042c101030392000210302030040c00007414140148a0501d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 701054280 1250 701053030 701053061
    0x6140c0309041e020c01140109090510020a0905061c06090626030421020f061303031101020906040b090f0402031003060216020607051606170f0711070902070c0504 72
    0x10380c0c00c004001c00fa000344489002c0082c1c0c03404000200f40c03000d100810f0200d907480004100342403100040c0c011013105038004a4120304140c000c500040c00403031403001e107800b040710044e12100c940d50109c07031002705904090b412000000d6054a5148030600420300419030f02c1061150755161f0807068151280e61081510143c600c00d05000034046003007489102d0704498040742e007042e075100e01d4000d0003116a107505641e00c1c80f001d000700541c105102800302100c8296009480c0c00e09590700d00707260324160310018007001040d030644180503100390100e9200000090240c0d443c0c2d070701c98014081560241c50214841c140c103028940c010f090500960b03100c0d03e00d070b45100340000e2942e00c880003e54884c69a0748802c0c031403030046800581e01ca601500c50980034500920000080fa9041900034600e500b04034140414070000840c0400d00300320280d0307c070240c00384103040c0c2d0710b9100040e00e1613200036541c403250f4025140081103031180b541c003a0144a0140c41c0035810f140c0d0b608203200450309204450100f6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 701055530 1250 701054280 701054287
    0x20303040b070f14090114161a04030e0909190b190b0f01120603060204090204171209011d03010507020c0a0b0906160201120c020c18060a15021002030c0406140c03 72
    0x48021035400740c0301d9880181801211f802c109a46100e142c0c0c000f1007070103806031350b41050500344902e101200700042d03581c0344010b0305410300da200a03020000c0a80840d109604140018288100500502c0c904503801c0a040384a06114034210070455021200e038102640400c1c40303c07060344094011420b46140180c840c840b10b01890b801102c03d0035040c41040041078031484000006019407004000400407070308010b880303d00302300407181008200c9140c62140da00c40c03480c800e8031319101001c540c030313019003400c0908200710181507900c000c559444a855041d464070b81000402500841e20421034001202c94041180e00c078010025a0301510500390340080d0140420b00c0800b550210103c580e500506103207228040907002c2c403040d19080d000040050304011800c079200d06260807440c1c4050780292400155181c50030200d0710380f03e1076118040040f18100003000041c1c0c003d0100b00d22000482c542950740740703002d1169031403660107803107140000340c9070181d03019246070301d68195144640c200002d90724 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 701056780 1250 701055530 701055557
    0xc090403050d0605150702010e0d15020304060b100e010305010f180f020714030d200702210703030305060a08031314130e0a020405060a050f06030a020d05010303020303040b070f 78
    0xd07680c1041c2503003260399564035008184c9540e9803006007a42807440070344958035041440010b01c15100c00070baa50050518150f00e07400103405000300c0c0c40d190708503400180c9964882c1412006400320300c00198202c4c90440901d07988a80c0a50802c070034110a03202444142d1740c40c4224041485148102c009aa002441c440903510030740c3c20543c6401c124107000346c00c040d03503904d031848800c020002c106055440061030407180341d004c1c0502004921403d00c07000c03c0480c4800d1181c0035104179440240f0a10b402d031140310072003204058200708040c200045032859501c80c0f130080d000f4001035640500c1200701c0c20300041c0d0100f000084071800c80c200560404a945003c09103001c6942c0342c01e8071039019050b4126502012114030411007031004080003480c4480050043c802200c02c00341040e4091001c4940c180203d840311003003040071040907180d00c0e40d0380ea00c09040d0030090081099423502c4904220000090603400005035005038012070f0b06100c5a10345010558481c03103a11181310100e00c8a034680725 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 701058030 1250 701056780 701056787
    0xd0e0a1a0921011109011b050106031a0a0b06030402060d0203102705013305040504050a02030a05071106061903060f1b170c0a112e020f030c0c07210209090c090403 72
    0x200002e220348e0021039103d440c1d07640d00a84880c15004a50150300203000c100c0051128090000e00441c2640c10318034500f420380100d00391f44035224400031401d40010208519410f40701c1030340e0042c011000344407240300840e8505455000320b030b00d842041c10b041c00b00124000c3c0900752a100c0070105c444801415644450150f1080c0c0603a00154040c001c0901c8002013640782c5001d1144109003134480181e4a25040143c402110800340c003e02c200401016143c5040200090711504101e04443c007550020201c0792000000613035410091400e4244040c4005040c40784c0c119210a01005102d0041031248040407600c2601c507406455505002c030021800c840700c007100400042400b4a014502803076408109858440308516105441c01d030406401c03241c0c14041c01503e107520445205510340408145644400d02010305001c0e00c2c0c400010b21224104c0080091070020144420700d6a400300c48004500340f2001020400c0c0d0007a440f5000148400ca000f081c2c00c800c0142c01002410562165242203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 701059280 1250 701058030 701058077
    0x91d0106051806130e010c0f0f08010e0612071203081e0a09020d020301051807051504090e070509100915031a07180806090d0e0a1a092101110901 64
    0x200d800a84c03182c4040008a0f40d03000d401341600c1c01742c0c0042450005004010440c8040c2c0000400b004076128990050640c8215528111411424802516180c100c0020707528020190a07100794829440c000640401d9500340c0c14246009807030f840c01c0c50360740c903540e0b92003256601a00f1556440304000520390300220350002000c240040d00d228034281e00ca83c0440e0843d08203450240d81b108141542001c0038208010b241d000d41002c6c0d804401c254115200d1646138081c13801202c1030036480d0101c807281e564040000100900c0014010000ca04103100105a1500c080c02100c00e40c50516140061010300d001711030040b030743c0c0506007046142c44003506605a403000340880040020150601c0840464208c18078094070070344000d030040d800c000f40951710b000112a0b000081c081c800c13065606a40d14401010b049404041e40d40c8840c0d42c0350403030000b4500c980c40e80c403a40840116124020101c01881c0c00007010500c1c0000c200320119800400c2d4240541500c0500090100d8104008200d107003020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 701060530 1250 701059280 701059291
    0x1180f0501020702120c04050106050910031d032805090d02060a140f0406030513020306071b05011508010b030c060901030e010617030a02071505040308180901091d01060518 76
    0x1414021540d00042c40314200c040801d45c69401118014920b01d0944507840c01054035080030f601e040d4200c000b007107150300d1403082b0909066031082c903d10103821008880180d62481e4043c1c9036076680d101182640d840040d01c07a031441d100c00c607265041c9180200101c6001410051100c00c000c8026420070900380c0c08101d072132003001310014214186100c3d0201406010380c8130050280c945090280043c100ca5004249000725074104503400c015172400703d0700a820114902c2e02408040740092204091045003800816035840d11010420381e04542e5841000c1c3d40c8000028130003140714404260351580e8280a0b01da120310304010807111580241e2040301c450001e5800440c040b42c2e01d041e61000c03440007443c110616000011808425039052000c3d0010f04450000b001402c841e144006106000b0780c00001c0880b9070004120101401c0392421078400c0f10000c09040c07881da110180f0306c0c00b4004031403d280d0300e07800a007000c6403c40c0043c020042501c402802120246092445003940f12601421 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 701061780 1250 701060530 701060533
    0xf09140d0204060b04050102010b0405040c05010f1e0206190e0d0818061005040501170307021306030618051b0102100902010509030a0f1502070f06200403030c050f01180f05 76
    0x20400c016141c41c000c40000f0310801c080c490f2554030700000a401d642241c2c1c403892049181a04000010ba103048410083e10070030301c0d000100c0c40e08884207940510b2001d65510300707403070940503c2000660014041e03108410000e100c02c620040545c1c0b4005841e450003090139607030400d01c0c9807182144540b81e038035808403482c1c0d85001081f0baa00000740c10980240c1e00c0c0031080147d48403c0c40541070a015060040690b1a03034044111881c5040a483c1d01036046c0007032080d143c0001c1d4100807509078100401441d0054803c010107154540c4001804103401401c407000c0c003a90211841080448031801c080b107906801403c100b81000b8064001850200b200305c0c14000c081c00803004a8030100203c0c0026840745040350a529014105a40100d840c1444000054010440440085c44507420441825805a0041020800c03044500c513a000c0e90481c0400701c42d00420000140355009401d010414050820f841c83c000c6100701e83d9003a0780d151500c4101c40b071074079000c2c0e00018504080c0349820034080c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 701063030 1250 701061780 701061799
    0x20d0606031208150d1e05010615090308040303051c020d0c031a030d080603100212070207050a0f0e09070905090307061a06030c03090c03030f09040c030b0f1c050a03031b0f0914 78
    0xc0141306d60600038801500c0380e0395540e00511074001d030003841000704003444c100f450b01c0314034640d280c1c0d0481c40f035800700804000c07001c15035081c0c0d64400300300510400c240071429034403600203015242c010060b5848000c00a4202081d096858100d581d419411711006005002000c6500d00c040c2c0d40000080c05a6400d4418418400d200c00d01030710107003026000c00c040b03418103802c003410300900d8000140c001e58860118801c1c10091084e01c4003904045a07102009a10180d480c29222400d11b0344035440041d00c10701308000c002c6807040c08001440d40a100304010000781e0500036a0542010710b81480580202e030400200e401b8101d640095940482c4040403076121007034180105e070035500f14098032002d521010400300300c0d600d0a4003560340c10304070510b02000300004840000d0f07403110080504500809400c2c1c0340d80d1480d88407885460203d90020701f10b8003a9091403500070000c01820240d05080c101c03c051940c84284140c085052a0415982d800d8005003810341501500740345141d00c0f940080100b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 701064280 1250 701063030 701063063
    0x1804260c0106080c0117010b0421050715090e0906060607080c0d080109141902090112050f0f0c0406020604020f010c0b0712150b0d020307020703020d0606031208150d 73
    0xd020b460007501000b40030304164442e840000d40185c03911440b00c1110018400144010400c40b02a103045030021129225091766071000185a2103d181002d40b041c0503008011804880c1c681c41c0c05595195a51925142665121392020401c0705461350006d03a00f0010100356646481d501800303c1c103009420003403070306603420740389458800003889c20741c0440c4e6010300402c07030a8120300c107102201c3c108244840a82c90401c0e019048000d840305548035090380840c07450f07100d034462010340c070a85209420821441c1006204140e000b02c0c1120b081c9002c035407620008040000382d40c1a101220290b400500081c0c8a607820060700000d20110a07040010100e83e50002c40c2041060718020205600c40315101000034102d981507440c1080c00e03020b994000703041000b10043c2401206c0307025204203c01130b1079072070b41c403000c03810f041c070070b900196102c3c41320003901e020b1140ca0b5008c2000c491050b20010000c0da92003405030f48111040b21501990f403448104c0800e00c1c10000394110700300303200d24815803010805 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 701065530 1250 701064280 701064283
    0x30c2104060c120c0806190801020c030d0e010204030b0a0519110a080702120906030405010605040501080d0f0e0a180603060e150606030408030714040506181804260c 73
    0x2180d09940250b02d4884692082d0340007510000710b10100701c41030050018040c3c001c1d080c0384003d04120700801e00d0380b6a10b08009000c00612002d020710000a641c0d0b40107100000355030343c10040c940c101c00c2e4500f4802000d074110510031502205c0d8404840059036881c15100d40040000508503100030002c584c0100484074203210705c0d1005d10110701c44d1502c51a05e10801464018000c0582d802d66020326100184062050309803036900104448244c0c0d80e990f80c1c40e04c240501201c2d4400c0360018104000420100000310b00550929480d644142c107030201094211060340c80580155040b0940c10002e016403400c000c0c80000f02c0707011100c00b0501d640d480d41c4003800c60b1341005120300d594000e0b40125900604003003a140e04802c0c00c071401d9055040c5034481c20403a10020b00080d040c00000c5196000f032916010a50700204001020240c44020710042c010484105c8a0858416130482003842c0da0b80c06c02030006402144c002c9010640c1514000c0d98500a4860b014001040101031000140d298030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 701066780 1250 701065530 701065597
    0x3070905060c0705040f0f230a0902030a02031e1b060901030b0315010b0d0f02120c0c25140d11040213050d0c030203011409060f100305030c0705090a0603020105030c 73
    0xa1301c41c001030460a030b580d9603021074024101c920101c114900250510103070071423000f0342040c10700d9000100001c880c030002c2e2900c1241d00d0001c1d054000c4842050019420524107c0842d0400003a5440c0684030a02c800d041c40c0c0354200f0580c0207030140302414442d4482d90003a8103e403c098101d801d80942c03540703480040c2009a02141800c0000540303c0308071b00c003032b010341e44500003040300039800c0090481c1c5000c1050001450b681078528007103401c1c07980c5c0000300a660f210088140c0ea4a40c180c580b0401701040140394014102c07007450480301c0524030304000c0707103101e10190031504101c4c1d0ba0b005402000065481011300e04280b255241c0f022825945200400b0401803040b080080d5031440e5106050035900d2444000c501e101d40001001007074100030456690009103031902c190155200400010110f0080c0c001500e24800810146100700000078504103444084070080340b580d48031004041580c00b03a000084c00140c0900c04103400720f2402d406000c81c41c140601c102929405169130004200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 701068030 1250 701066780 701066801
    0xc030b010224040f320f07050d080f030c0909160c0f05010204051c0203010e161505160b04140c1003150504020c0a1a040c050906030c03030c1e0303070905060c070504 73
    0xc006805009803442e0440f0340c040e4003944000640361203013000100d1038903040325108590080c411100e01c00304003c03c40084be110340e0a14541c260312401c0c86620380314250402008980140c03894004600030600d40f100441c0c4540440c1ea50034000d10050340c1d4040c0c0403000350400c4901e03640a00011813641c0d00c1c00f0215107182c2011000c6e0044400c0d0740105420f50b03008c10394100483e084444001000c1c0713001e0740200152400f800301103160300c80c1d90000721118030402d220300c036800d54140a01401c210010001c0740c0a01e0280c15900507015041200588070000760012a40c000840c681070104580a078000c00c00b01031400c018042c07201d03aa540424266801040706601d9034004041c00d0081041c5522824951062940124414038150740c50098400c41c9000355407040c2800d000040040e9002c0140f0703907110001805494070780b10f5600c5c5e2140c2d618200c061b113100600160303503841c114400000a81e482810719640b40d554441c5000e0a210195020780c5107080c00d4003031400701069a0726a07005050448 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 701069280 1250 701068030 701068073
    0x50105160311030c040605071a0f060907020106082505090a41040609140318060918040f060603050c090105190303031805100c030b010224040f 63
    0x1000200010100c4500b000e005150850500910040c01001c00c01c0e1029100c1d14144a0341d11600ea08180d85c100c1c2802c12003c6800394905c04202c02c915500700300a019038001c2d03d500c0004e03164030006a00360740c250f02a101d0f01c0c0e4807004915802e07a41540d2110700181c40034218030040703a210310100d030b5040021140c01400f641c4406903001780f00b98081074401001d04101d000c10724103041f42802084c0329001d02d00380051742c16220100303091003241e9110510b042d03030140f042d180c1c030030500c0551900c0750017002003007880c03100c1013031292441d04040084401c003a9000380a10320940d040402000a0030f03020700305499003141d01d07550034000350440c400c680c0030b14081d2005100b00035900013044540c0c201600001e004150341624000c03844401e056a0040c0d940c94103020807101c0d41c1d038010b101070f4000720201401500c038201e14011604620b0f40070322110f607201e5505210014200006981c2c89984480d1102c05030040c85045070340880501a06401c688196000b0300e18400f20340320640303a2108100b0321100ba = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 701070530 1250 701069280 701069311
    0xc020f15030f2505040306110f1306030c050a1e050405031203150f01210f0f021305040b06040e07021204062105010b040b0c2103150d0f02010e040603050105 69
    0x40000c080f00d40c00400b103540c54602844191031002003c0303004500c0010020390300e480460550001c3c400648101140d00c1c9145502d03010700c2503241031101c00d035114520100785000c04001d501841079040351090112a260081000b0b1011207041d114491a80c00008102040c440854140c7e000d201e00300e0041d046460341130b1a4103040030104075110b004103005108091020307103c00a81d800044202c0c4141c0c0740904c142840c5071043c1c91401078414113440c00d410602d000d0314152002c0c00c55014002d1060030484501050361513809002c129104000c1465024034103203c100481000a04d58a83c8900c3c00d1050701c44a141a0210000c01d421030303040540441c21908228401b502c5018010924401810040c801949005110805481513000d0a0f404102c000b4090380b108808001881403810000d03003c039941c4141c1200d40681c1c0d08290303000745041f9020000301d149403920100040440d50000c01054203580280d00545440d1420154141c0280e1601400000714200303200b000d1095042d954151003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 701071780 1250 701070530 701070541
    0xd180e010608040b010806010e040b040f1b080f071202151606061409070f030c0219061b11030306060315030106061d060c070e06150d060906080d0c020f15030f 70
    0x80d03c01050300a0201e40d401f40740100035102c0d000c559180c2141d00420f02208035102c0d8241104c00702c0310f10001510401c0310002180318030340010040c00840d00620305036243c001030a0102500c82c0c81c64400c1d8101c5050605095026281c41c034001c00345050041a4685013a85604a601043c180d15100ba21115130311001000400819100c1c041c0c0c4003c2114101c01d140b07403801000d044044003191305405c069503103111200141c0200701c6049500706105509d0640c3d641450003130050900e144c2d55400448151071004200c5d405a2452800e405205020394119659141401010741004104690301c80c103c0d005050151008e1055030050202d90342c3da140d0311000380c0a0300113400740040c0303264000c0408222800301144003141e494261540e007048803803241c13203d80008a00009414405050100014041c0c0d00d9445e15884842203452110090124a546800b9035071691803288406001c07076840100703580186003140c0e0b00511403c0051031031840d140ea941c0c03c45c54540044402640b00c160600902c43c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 701073030 1250 701071780 701071793
    0x50a0207090f090611120a0c091a0901110313060f09051e010806060c03031909020901090c0909020406080703240f03061b020d0503040602072a14030d180e01060804 72
    0x110455100c0400e1840c01c40a5103541b49801c8008110f207000642d55803480c02c2e5180320b04c00d214000d0203508100842402e1040e034105155001502c0305002c505045c80310481600c010054030446509051840080d81c13402000340c4c0c0d04200301140c40e040240802010410380e4131010028154600d110a890111034041e0000d002000054001c92042070140080240b07604000201c07a03224001c102d610360b0041c01c0c00300c0c00018001001000f0750004400c030000c1030605455000390890019640e800310041c1d91020782404a1059020390000200180001051580070b03130031085403001149410b505410400400c100c13400031507040680001e407c602c040091150b14000c8401015126000f000052007840c0081c0d500c1c01d40724040010700601200107021303c0155130603a2105500070340d403600c1d004400000ba01419400705c000d59090700c1110320108200f050103000da1240b00010b8010300c46500340382025204007403055003051006160880100b0226a81c45945000f000c40381c40c0e0540f941007900d00207 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 701074280 1250 701073030 701073041
    0x40f12180e07142704110403050d030b061603080603100c0302040504050c19210f0504051501080601051521190b0303040501050906070f03022a060901050a0207090f0906 74
    0xba003409100788454156a00340c4c1e04010524501a400b402c842c1a2103404200a4000ba515180444030003080010900001040c0041c2d00f0126039400c101348081d040030800c5601400c10f51030b000044070f9445000007401554040e4124800808461030040d00c2480c00f401d0764032040d5241d000940220f020041410035000c0c041d0400c60360aa03841c00c1110b1840d028108520241c2490200455850f103440c17500c88401078031400e0000100d043c0080c003c9074180b20041c01c0d040d24100c8440c400c403541244054054110141a2200c03400030380000c0c5d29010803c0b40031064138291940c22001084200c0b180f07606041d00d815030b5102000c524080c1d04e01880c41c41030384080c0c120904401814001e400f4440d683c00f0040710b0907a04242441e988450420001c10004c0c0030f1020000e1039000541d40540c2410b80004074a41113002025950341c0c07102000c2d664400c50580a0300041d0002820b222811241d80202c001e420412101d204a4000595a0350344500761482590319800060341c503414001440640d0140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 701075530 1250 701074280 701074307
    0x4110d0e030c030307140706060906030b150307050111010f18030e060301030b060603040f1401090b151509030f060f040312020c0307030c020a1d010905010905040f12180e07 76
    0x1d141040c0c00c1090702a120b01c00248440e04000c1c0c14401d9000b003480e5903060300c0d40c07540c11080400819882d441c80000800c0d4502003514075038a0030000401c07a81c1805e003102503c04016003d030a00510f00b01c0151009100850514045c0d500c030200081503000c5c0f44580451f10900d132951000c07071080c900b03018001c0380070300b0821070217507078204010300200754030a0030355821400a0b10455900c2c0c0e02c50420001c00c07140080014018201050f440c0c0107110305410081456028041c4149185c9910b6148070400d001802c60b5a085084140c2c5844862810400f030980310030040c0640c4c030085580c4a820782007003001c481082203d403280d41840103055219010002405420a08500d0995a002c55a940c0e01074081e00500300006450a5011500c40182c3c0030003e12041030f0300da00210b09080407510421003400b13004180c0f1300d07090001404030401d00030b103030185070055244084c1000548401035154110701d601c81c1880100d542001e0890000d01c511802404140d0200140b030030820001400640d25901 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 701076780 1250 701075530 701075533
    0x17060324100509071b030903080a02010e160614030411060a0203041a040e041212050a1d01020412020d060612060504050f1507051804050907050111070b070b0c0904110d0e 75
    0x4102213150000510500e000f025050b40801e1001850103c8182d002c40c1c100600e180342c0840c0542c5c2081d015086081940e41d254240d23020a8085100c006140f0101d11a1000145407440c0135400c0b44581c0d801150824081c40e001e03885009540c01180040e842903a80000603800050304020f0001000c03a807e0001d4a9180c2d4545000d140122140001030041d001a00c201c0c00c012714102d10500500390303032140380130441062180e858010440c400400311841992507081c1085151281c004061084030169141c0c8407120701361a003141c0070721000280800c4100c400d02da58442c0401c0d004020351110b0f100c684150800b04041c03801307142c0349042ca142016015071030b03440700c0320004410041c00c81a80e0b0140003850003503100c046107265800703800ba80d1505260854502014130000041c080b505100b0346100f03884400b00d0481c03c42006035030305610303c1040c40c40c6030107101210004414100907500701d403207010070500303104e8018002411100344119000d21210006500c0030702455500555181110000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 701078030 1250 701076780 701076799
    0x403080309121614030d0c110c0d17030705070f0b0618060d030509190b0717031308070201110d0e03011107080306121f0e06060f01170603241005 64
    0x4084001448500100410004200100250500c020000c1c0c0e003c0e040c000009007c103284101c000750103000b00100301c4815002e10101080b0070b0600c0d13100315540e940c2c4965045508040140d20395041d80001d80300100300181081084086042d0b8a41005102d02401041006040483c108109034091000500b90450700c03600300100c0f9590b0030b0038011002e81508125036600c0d124800904040c00c076070018402044500781c007007694410303c005418190320a0040c580303045084155072650380070449041014043c42c03007101000583c0d000140c0705161040c1820440042c10301010ba06102807480c900001070844c06c1c82000030315090190f1501d9035500c004d01c030f2411149403034180e2148401091540100f800110021030003104012081c0c110010301c0080c101810384000340c0300680900c030b841c00280d02c0b03580086080d500c1d10699040110301c0c161203c009401b09041d02d0700784904020149903050082c2c18a44005070a441c0680307544d22100041461146007403c2044041081600028010310011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 701079136 1106 701078030 701078047
    0xc06060f01020f1b0103140f1f121704090c050c0705041a211006030c0f260a0813031a0609180f03040308030912 50
    0x3224000c14080c510001207907140000000091540c00000c0a1410a00c002e507104100d40c0b41810b0201e0728204014428010140407a422030010030394600708a04100c0340e002601c46562801c0d00104c1c40c6041400e100250100b081c0f0051506821046911400440409075402464038900500940303e03041c41c01405034003c1008070341d8a2040701800300c0c16107058022180a403040410007018003400b001001a21100c0c4800c1d0390307400d80003280b8112400d8040c00a02c0001d09001c6001c20b40307619610781125020714582c80700e003014807520300500071040314034400c1d420b02e01c64580105280b01e103055102d040c400d00c070200801800c1c1c001509164003c1e1050410304590084106131103400486103d100c017038004403030716a440000240051003176108014485500a80c200485441d030402c0700c0d003180b440e030194100780c50b80c00c0044100042c2d0740003084014030511012070081d0500061 = true := by decide +kernel

theorem cover : BRFrame.Cov 700899280 701079136 := by
  have h0 := BRFrame.cov_init 700899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 700899280 ≤ n) (h2 : n < 701079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
