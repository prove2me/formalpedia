-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1705
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:22:32.285791+00:00
-- url     : https://prove2.me/submissions/476fe2b1-9ce3-44b5-975a-83af389792e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 306474820 ≤ n < 306654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 306476070 1250 306474820 306474823
    0x1009110a080402040504050718060e1302031005060301020c0102040602030c100204050d0f061103090a0c06050c0c09040602070f03120b0a120b0603010605191a09010903080c010e0601090b12 83
    0x2904209203645501c081d64480d401d20010b04406001144d0302c0c8030300040070856641e41c4c1c0d58503220a2400070002942460901b180c60712000241c44603041d03c0c0c11030040e00c090f0700c02007084090241d01020201d015180c0901003402449282e690460355440400c0c04508030364007100170143c02d41c4040c1281c00f02c41310741c0c0000007203201e070f48030307c65000120700084000582c0c08441596003500441d000941240300c00b1151685900c2200c0c4018250000c0328140d040014018014002e44154542141800d00c00d0b00d0003513491001800e0544100c2800000808004294048658041c2d10a5030324945052610b00502075203c84160580013504122551b01d442c1803051515044035140b961a10f40180280c842c0d009100c0c01030602038143d500c0c1d500100d81f5444a56a4002c2030502031000740b03d081c81c100003a0b9038080300c4819514170034000c100399100c903130780000b030750080d40e402c00b44a682e81d04811403641c2c01803002000780c40040c0202400041c00803025032040413040340549407a4022050013060742e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 306477320 1250 306476070 306476077
    0x7020f062217071703070f1409010c051c0302031b070507030605060d0c06120e0105010e0c0c03130f0303030f0207031d030a0602030c09101d1512100911 67
    0x80382a505101420011031000342121040141082d041841c240c465164a440810303140488521a18004180700b011944800f43c07040c0303d00d29107480f151501c080c1c80700c24100c2c40b0b4090043e040080c260100814000240880d4004400c00e80e400ca1914855500181c0079400440c0d5140b03d100c0c0620041011405110441c0c1429500c10043c0c400c03641165641002054040c0a56411036045003880c00003c08425104025045907115402c4100b104500791060f225501c86181d416418100104021701d0302000c1c5070340003141041c10686400803003009034914040c0034425541c955803000c0004004644140701c0d0190f9000343d130180245144ca00d0b05030143d20a02e54020f001a40400d40c80c0d8514011041e4400090f030010141c80c4c00c3c0344640c450074282d030410b0b2038001980348001680d01ba00d26013006103420784051401c15081000f50004011030401520415500400130031001402c807040360782c03c40b41d4041c166180a20141000040340800c290a40504240342d440e06d4192416400303404150f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 306478570 1250 306477320 306477361
    0x120601090803032512090606031e080403060908071a040b1015080601021f0b091302030303150d12020a0606091514061306170105090402010503060d0c030b07020f06 72
    0x80700e500512902500d02280411040020040740d8041180001c5e0940100300b0494000c140202d42242181800b201b491141b4529040790040c2184410000360710105441c00c0b00d0f00b00c0000620720b00a810110910b101c2c05030000c204044084070030301d140d0300d08218203006600406540326035685c0c03c1d00000141c0600c0c0524603020000920402c0400c2c0b18840313059200038103106844480d9415641d00652141c0703016002ca0395500c5501020060034000082680507100e0081ea0f104d160094002c41d88030702c000f8065204808801c503101506446a680381208586e2290540d42004581c140003921409800703400c460090034004001501c50143c054500c1d030410300740b034410a0614000c0a1030b0043e242402e819000340d01802811110741c883c940c03280080a03143c80c1c1c0080342d511070750301c540980016082244184500d106100160b64410141e981c00142581d10010303480407070405042d003040c0c0380d20050031520103108019a056000c81c810049555242c00c85541d6180d05883c9000403918125 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 306479820 1250 306478570 306478591
    0x324150316120507050901090f0e03040e04200904110910080c0d140d05090102070803040803070818131b08040f0b07090e010b0702010f0f12110f12060109080303 71
    0xa00303022141c1407042120b40d103480b9008682d9801d0b612000700f48109403da11140649035186805003000b5594003d00c204418103001840c5405e0400404104100340544042c0501848000c651040900032102050b040c600030285c17401480c261a250007903142c0940100d0040101340b012606c640d1060b0503c40940c1c4d605005010080c20075028010501a40c41c002d503071041e841d940d0f501c2041424400000780306110f5440b00d5a400c4248000380c90300c08207038000380044e07004100400c000180841580c807455848040990380c0c00040480d500c5103002040d4065000e01e02d03c0c0d40e94850b0800b13611041101d1440c20004650380c1003860300741c0c7d404504a4014003d1000403e8840001e68414444c42d40104103003031125165894034003800a1160903001100103900024441c015581c10690055003039550346030915200354440c00043c550390b450300c0f44142050b1034441c0022085148000d413007007101c0082440e6101c0004604012021070f003a20303400d001c2004241c1c003042084001c0120b91180351100c9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 306481070 1250 306479820 306479863
    0x40312180303030231051005030405102a0e09090d02061504090c03050c01140325090b0a21020a17070912030c05101803030b03241503 59
    0x110b054002e0b6000710f5065203c00c6003410b010400166403030b124000360302c440b01070000b218244010301c03034900c900784086c03424000300348100000110b0020b04104000700e4060041100c80800e4580001011007200d0140306048560790030080d290300c502030000d00c0e60f08403130300d408a4540062240e250072b0714519140068002800003030b0000503040b201100d2410280c40000ca0701e04544800003891039a81044034580c010300c0710219550b9025010318000364911500768a18180a01401a01d8000080d03030303084c82c00c066591703d13202070185c14188000c0c281030800540d01d04041d440148003440340321f000c0d040700c0344401c01c61102045901c02d0f01c0c40a01c01e0b44954480f0900d4801030401c0c00c100501c903904100840002258181d50003201903a128401d840e84030b400b440344c0c079005041951178000c10000d0ba2034007080b00402d181400548000030b815080024188084c0804203050003944180c1600802420714070f03480d440780ba190440e100c2c100c1403203000d09801404d400c160f15941d00a500561210f40003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 306482320 1250 306481070 306481073
    0x804090218012a0308040804090e030a02010e06060f09070201140c0a030f0207021c06090c0308030703051e070c11040504051509032d07020d0615061809110c0f030403121803 76
    0x252580e5030047d00802105080580c0c825259058802e100e0440d40d0641010841410031034090003800d003198504d0024000d54078085011a902d1035605040d10311400064001c10085030003948107000107503030344141e88050300e4031500c10001680b080d0f54440c0024a04560980e030581103109865040fa4010041c0c0c003000c1c24074400c0da41c1c0c542c0e00d1109603038050340d07044100c001544d0040c030800214403d00c401902e03440c15010250850f02c00400b000200e05040e01c0d20050b540d851001194004600e007841078800718030341000f0100a660314032254200d40b074003092100b40a40000d601c50b050580c28211201c0b41d40703d0058540301d0150300041017689082045202030300352009a4030f49404a100da8041c1401500d03000990303c40031280b03040d10744640d00c1103050070021070704c1501d1b409007031a0300300102084410506104e5215642c8203201c103a96449110403010a18001181d110400680c00c0b100702e85500702c01c45440c1d41c0b192004440e0700000803040300005020704001c9603019503805403c4000d0740b95 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 306483570 1250 306482320 306482327
    0x11706010f110307050607030506060a0e01030e251a040f210203010f0f05090712020f0f0d030315170d0f02070b040306050a060b090604120804090218012a03 69
    0x1041082010312082d1032031020b4024040024043c41e9014400600b40c5050184000d41290b02c0604101d000d840308002c010a0140c00c032041c0010b5075402e00c0c0004074204005419402c180c0104104010300000030308040b0741d0758035544034600303854040d008000e4010744080c1c192090f1041c0e202d8500d2007001007500708825011251445110b040310f517100c195a00341d1f64000790031030b85001c644101d901e0350342d400c0c010b04e04a54810141d0051805c0014580141800064212000e50050080c41900c4040041c1e80d962240c0007200000e0038040c0061607560341c586405405041000790341103c40301300c000001801400040c1c000c020024000c098421403540c0f480884500380c040d0950000e511a5800c0011240702c084024401140241c0000920381480048402036503000d0b8000000ea2005200c50b00161341e441c0119130172184c460000070a800113628200ca0140039a5200038505840811650300110760f04420b031904078426a18942c10107403620201d19030f00d40b4108120160f42c50300c1c5650001902 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 306484820 1250 306483570 306483587
    0x30e0d0314010e1f08010515100516080d050903280c02060315150d29101e08040201081305120d02071205270603060907030f090309060e01170601 64
    0x10810091000c51003c1d00b942d1411400507844100d00340c1d910010451230700d080429050718818120350348a080d035080708008220f801203610b10f070041042c0c602c8000070041060100c81503038801e161b060100c3d1600f907100540360b0f0015009105020707040c0b1b0510051000e640d1000ca1549050307142c820382006136400f0301c07000390801845904181d420b205440ca2580c1c403c20010070aa4826650554524030300c0c00c40019200c140d60320880050300041c8044a00540040c85607282d10261103411001003c2c131000c0f00c04180003190b00025000c4440c1c007148140e413160445108034000e813101055a1140f2038401040300310400042d0294001030b01412520044070000c0807040b443c00c801500b404c4194440c820303801c6155407180e001c64800501d502c0d10a41c220440c00203840c1e505210258604054003240d00c41c4002400984250810b600080d100b600a52000203c2c0d0306a000400458943e80350140c01450b1a028013004181d002c15030407040d61080100446041500300f0489141d207402e801541c0054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 306486070 1250 306484820 306484831
    0x1d011e090312050f0601031a03031b07090c0314061c060c0c17070309050a030816060603080c0d080105030f03180303160507050f06090105070201141603030e0d0314010e 74
    0xa640026030002095402142d000b00030040b407111285c1841000941140c05200b1300a0384113090306031240b00c1c0d13503010055a1061141d01400501c02c042520f03c18180031341382c2c008804440c03030000880070030340d81a48001c821494201301ca003e6602c1c0c4004020b40040c00111580c1902c012442100010300d494122060000d04d0313080001000401c1e540304119000c8450507000e180700045600c80074594000400d100506003603484410351420350322940a41e1003004d01404240c0241e0741c507003041240700e80c400740042d83c201c1102505c0740d41446a06032204030491000700014001000031440c0c2c940800c0481650902c1030045140000c00c200344040311581100c051b41c54007003409070f121083c1030440014030707280c8904068070000d41040f08000c40e503200c580c40d00d07010351414054524166000011961000c0d02420a0030510a00140a068a00c1a0024030340d500800780305403820584c03d500850000c0c40e000090341d0414146c001c0450403070f120300d060043c400f1040d20040051100c04e219954029 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 306487320 1250 306486070 306486077
    0x1a0901120e0d080f06010c15200c1014010501200109060c090e011d0109052509060206010504051023040911010e010f02030307050901050702030a05011d011e0903 71
    0x2002903416070801c242c0301c0140c0c0c0424042d504000448800c0200e03590702c54000d082504013440301c1d403284041d0140040714130002541e6112200220748042424424014402010584d10780c00d0381d09058860a00b107007490780040c00c01c100881ca01350004042810388006130b65400444013001c503001c07100480b00caa0143c0c0c0f035695241c9400454058055541c8a40072134507404440c0e4a06110000c007000168402982415a9044149440c03100c04860b03044890002000c02e59440e10034101c098904502103141046101e20000300000c2d030010041ca0888602c0d80030b84540f40c0e42e80c82408191081164002c0c6902e0366400280100c0200401b0707641809508a00000d02441c1c0c1404074040f91480c007419100541c200c0d820007600d69120703011107913041c03017071030b048002044044002c1e40e640000b1b850401441001300d56a05a42d10813030940e0303800c5070014101c84140141e0704043e402480180c451b1100c0755451401840013090500404081c0b00011981043c40e80c82411040f005042829084080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 306488570 1250 306487320 306487331
    0xd081603150302040f02030103020310060b0702090726011d010503120f040906030501050105091807050405190212010602070b040308030c0a090803270a0e010b070606030515040204061a090112 84
    0x540c803248241e03801c18205c840300581d6941140105032074181030a0305001c0132800e00d6024411a24058241d0b491903038180c61110381da444070b8400303a440d80348055000000040e040e900b8082c00e982c090388a070488411650703032007100903a03002d248030120f02402001d0f050f47c00082160024100c200040c01c944001c41d402074240754440701c1c111b064400c99030098800d03a4403600148960302e40b502030944c2020301204400440b05500c2e900350303103c030014420f80307108503a10340c001902c24400074040841d050768914115038644200d00f04070002803003801200018841c80001003010b041a104941c103503604950b1440c1140c3d40c40740c840c001903000c11708800400c01d00000002d561081040a40030748102c0403510321900da0004400e8500d80c0003076228922551611b50200026039a0b1401d19054404100f04140d0b60f12103414440d01a2001e03520060091207007094140349003950310300050040b8401c4505000a0f60b84410a461604600b124045440003c00640c520766001e040d0510220031090404070303c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 306489820 1250 306488570 306488573
    0x30601080f010501050108190b03010e031204050708030307020709020306130c02031801300b090906010608090d081609050a060302071a040b06010c031116080d0816031503 75
    0x104402a44840e04550125215071206030082c020503015103005e01e00a200341c60080a841c0f11403404419500302c003592041405e405480c2900455000944102101d0340e071510701000f80c500a03000c85040d00c05003e00381011841c00c101004490040340e02d5070091640504210044000f540b016018542c01050314803c800564014003c0c1440103a00d900a5a00d40c21502144115086510141c504000c000780c00105182c0c1c0c41008260300240810314250400b4071540454010700d8010401c540c0059490100300544800003402c905039942c9036103042040d1100245180d03103068240e8010003140d40740c400204c1030381d90708100c00c0e21074a840c40c200031429520004070b40b02d010550409000203400141907402c0c00320001070101e00c1881c440065203a4545a2120000c1100c050009810402c0110403038003494400c0130745220120110003034528020800c11011848252031007442c1c0c41d130003000380342100703240240c604070301c01c20300440310204010003108110018880b5907280c410210980c2c20110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 306491070 1250 306489820 306489823
    0x1003050709020d0b0a06120e070911091f0c0308130b01090f0b06090a0b0a1701090501091a091b0f0c03030a150305070603050a021c0b040c030606090b07060b03 70
    0x200203220748100143e0321010700c080e0000741e5420300001c0e03002d0050340a041101a9005550200f01e440c080f03000074207682c03000c08190410106030300001c2d86500340141c0c04190310f4101d000b4029043c0031a4183d40e0b401120b25001c20f1124100d2415011850841c00716002c40e0081c694583d200c01c02c204150f01303135183d0365640ea10901082c0c115107903941da5090244100300d41c6108001c0e0315102240c00909050f0b8540c0001c41100f00e42c080d56032100c801003050000c0ca070141d0804c108070100c41d002c4800c69a164243c0d140104400d11642c04c0d03450824488450712a0701d0180c4003000903020b05a24529501c0301058403022103001051801080c040040410940c03071000503005454461019654070b0600118800a80d1181080780e078006c1e08a80d01040000c2c1d00141c03450843d6890300300461166110300e80c00c0000d0040304060000c00e2000c40c03428000608545c1301c12204201124100184064040120304035011400b03058085003512105000301080030010305181440340e000030a07603030400404617 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 306492320 1250 306491070 306491083
    0x605090a060e030403020a1a21041707050307030e031608010e0c012f070302040f020715050c0d02030901061a0a08070302160f060f020f0c1002040501020c09100305 72
    0x12949600010a50020489240292004501000c00940c14141103400280e824400d52140e14150308159507149548da0986c8251001d0740c5440c0700b00c426180c0c54100d24116800101c904403040c410344d1189012131f2544030240c490031a0030034001c500304013860b0350546010018001445e03044c480c0800381001010070620380000f8012036400418402d45210036075140088a9059506011680c144c07000204010b5080d5075142c5070840c800403640c0f082d912003e050598075013029400c68244900c603521101d1a400034110b9910480142c044081d10841c0001219000e88544003a4001040034000f0090f80350003640d0800400000001c805a03500b10f5420740102d40000c188426501259414107a904200310310b61081c0c480c201940390035182c141c6100070f6545604010011700502c80c05100b403100b564410115144101011984d402d02c218200c1000d4100e03406031a140d00c1802c1c500c01d0105410b00a40b4116101030b0010035500e100c0c2e40400943c1c0c0c030000c01ca5104a001600000041071040160 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 306493570 1250 306492320 306492331
    0xb0f0f1c050c09031c05121b031e090a030f120b03071d0c07111002030c0d0e10170a051f060c0311060403120e030405060f0c152505070605 61
    0x555848034440181820880c01c00340c009000013161170312101c015003000c22642000c003584441503a035501c400c1e2075910790144140025503a207000c0f08008410b80c00c0f040d0070008441048502c10039a0302d038000b0070b540d8548000e0080c005041b007000c3c00302450107400081851101c5103c08105191208040303854020701c4d0744000e04101901320104203941d1103000ca9504641c82c440c0c02d03803600306c16850b8945008180ea61681c060394010042003000382c424000d40d40350030303d12025241d028105120040000da2020840c030b201d08002001040c40502a0f80000300040740c8103000407043d944c00344820005d00000b01181c0c0c80c1d41c0182c10207800c1c080d481c603214000c1d15007a00c41158002d81400c0c000c0c00940c8110417640b0382d62000d018400425040100c40c0740383c41040394041200c0240d000c00e24110b000d5981b21a400c038901194410b08126020041e207404101c0308203c400066000103c0402c911040e1900056800199180070300180f1400b003c0403460a075003015464964a0b03580d00d0304480d000c651 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 306494820 1250 306493570 306493591
    0x304021f030905030708093d0c0f0f03110d080a0c09050604082802030c0f04060f0b040905090102160f030c150e010608031c09140f0a06060b0f0f1c05 66
    0xc03003a100d4a0300110b001d1108503a2048e850508984400c03411352188401400103004a00c001e14903081442101c9880110b60b1100046074990318524060440c414880c400301c0c040341c030b0008448000c007000a24003528020945e41c158007a00c030015948002c0803103100c03100c10841c03a1803020070705850303c0e0004c00c01401c07800c00030451007c201c02c001c4c1c02d030b09a02440145266003090040b000d42d5002800c050344400c1242c4044421220000003070027828150f10010294a455000107201c03102d14018004071002488140901c1d070360b8004240c01c078461180e0341d215150003101002c1c041460b810000300d206107c4c2c00c09000c0e801c01c1d070f100d100603122039441c404480d903180c80c40b50200920a0090000800c4504004d6041c90381c000d0460f602145030200300d4640c1541c4203540014408080802c0804c3d15140d025104401c03050003200da290810b11300203aa485041081c00105941d0f02070484580c800c8040080741010440c00907540320303502c00443c04e03450408031040d40400541070702c00d5a000341c1d040c54 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 306496070 1250 306494820 306494827
    0x81b040f09050a020f19120f140c030402150708040308030a0e0f1f0e0a06020703020f0d0e090f0703150810060501030506091f080a0501050711030304021f030905030708 74
    0x30720050644000030460b0f005103006000e003542090112090b900a42e0a80301038071400040504100e900c0c205640400d003040d428151928412000d03940714121a06210351085001d50303568040440724442914000d403c40640c064032840f0b441e00c400508606882021507501c2c10365607481d030116907001030356400d422039626000c0c9000c2031030420400c80801c5074040030300307110380d01c60350090202035201268000254035002040100c201c20320604040740d503c01011910b07001c650a00030b64903021002c1030f1525100382e90100d81e001d8082e900b803200900004000711101c0e80c0303103441c001c003420000d4000424507880d144080c10741c01d821500d240190a0903001020a11000b00c024410385c0d195500079418145006c06204064480d80005d540c0300c016184001d03641d001c100241c07909141194030580c1580104403034401005019000b4501443d81d581d1a0300e04411200026a00d80c0f1058030000e41c03280d800e06060700008128500c00200b4442c9040000703018040351034160841e400780c0e80881d000c41002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 306497320 1250 306496070 306496079
    0x4060809030f130e010e2a070503030a060914130f0c03051b0a06171b04030c0f0302040c09080307110301180b0a06080f0d080c160609140303060a06081b040f 69
    0x103841130f004085106e450541c0342010001c0d6400040800d0418100d40081c101040d02400c001c2d0072030b4003260303010707003101d1f52450700c20301d804001c0040b4005d2012041c2414a0f00b081a0b40c10300c1418040c040640500f000c084095a9078101100d118404591117001c4504c004003291050118580303000c2030200d01c201e02081c0604120720014281c0240d424804000300d4040302d41d24244c45503a108400d9940e0b109031040010300141103000d594001070180d180329201042245001c064101101e02c02c1e9010b0080100d503440603120b03150746015002043d8414070424011901c0e403400c405406070003400024803410038408501e10701210700c1040d614415160f050010001007841902d00400202d0058504440e01000094680c01c0450f50601003102540c0401d41c40303007214040740c0c05082c000c080201a909540780007406010f003041c040c1d485014451f01840c044101000310707441840000c00414690f0300f02541a0744900d07000c0e2000c40340c00b4903291221150b86a040080000d44200c404100300107141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 306498570 1250 306497320 306497339
    0x4050c09090613080c01060b19020d0e0105070807020a05030f0a0203160e0c0c01020d1805100621060605030a08090a141e01020115060822020604060809030f13 70
    0x380540c41c456118000b0001002c09445200d0100d035030004030642d44940c0c288945014000f580c1015881c85000107481000c007956405601c400101c903001d4410900d030843c0c050740d80b040307100140741c08140104540700018042c0c100804110340300400c0d01c2e09c815251004240380c0907800703a6946050380300d146003105501e010070003e00080328101c056402c940c10080d0500e00c40201600c007440e2030b4408034404c17800305001e40646555060310f10701040128a488513054a0f488d244d60144d415001d00c400206065409005d80e00c04e9901056840d60005503856666000c0c01c0c4540301542c0c2290349030800318080d5824402c50123100d00132092039490b42a808100942c1e8100c9512580014020461404140c0c41343c0e894540340d82c040103e03202c0704200c0c0400507805400003041d40c11007051b41500210f401d0307422011090040d80f101c01856140c000300d1031030031060400c441010398000414042080602e1040c14030982c00307010b013826a41068610f010700003007900301041e26420321030390769000d0110307104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 306499820 1250 306498570 306498589
    0x170109050d0815030a08040b0702060d1410081903050a0905150d0c170703052707090b030f100203060402161a06091608150604030c0503010617060a05040c0302040504050c 75
    0x20f0072006400580140d84c1d80c40e415201d580319640f444a00850468103654030f0304203032080d818501d2001d00c100a10b05c1d001a0745a00f08a41d44000c00f50096400320b0031517400141443c410b014400740705d0700e5034a0f545007034919402005d040410403486090101d4140c80784002207540e80c507240c0300981c40b0b413443c600d00001e5400814202007001402a4500050007402c503105410030040e00b000141d81d103a00e04a440ca0181d051501c540c19440008001c206070000200ba00031246400c0c0100640c0e8015400c26480b8811a54a05590b501c071612450704500554019500502c1c014401072802d541c054584100f42d42c140019038080c550705501e06040003c803440709a00c0201215046102d10705220340f13440001e0b168401504000800c000128016401552411240001400591038658914001048078494090700303019500740880014261102040a00c200c0090740c041d01e66a607680b4100002000014001e480d0152034020020150301c1c1c034407d01d8000c5018a000c0c1c2075444101c2c0600200d5407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 306501070 1250 306499820 306499861
    0x1501020a151e0f06051507030c05011b0e09070206010803040614190f081005060f07031419030608030c03040303050f0d0f050402030c010c05030a140d1a01080705030709170109050d08 80
    0x3002c3c1c6c5084203404c600b812039868582c103082441611a141c20040d0040211414140d011440b0303100e080701140e001444909000303811103a075112503450400407030321040d00384941c501e5540240000d1000314080c4011040c400c00d994015400c10303620110388108801100d5560b40400c150f0301c035601441e98403034051136200304c100104070000303803a05002c154a0700c5010180820050086101702c1058031403100098041c4129030401c3d03c0d40c5c1030181d001d150700310f000c0004000c28034010700060719410100c1074820a088a0010314146450b5072016141d940c0103110250380c41c8001c001400074a4100d01c1038603a44948041c001441d407403d80705041c0f13051070361880c5505104000c039407030001680000868003003c1441c5042201c1650030a11442a40500d141400203a42440354050040d5056003c0440d40c5e01c091b0380d0b4403070580300e0b0801610035110944451000500ca01014810000b080301041702c0c030380c600c200020b01e4102a0311128100307803010740410300040e4182e003803020038a20f0a8007541e180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 306502320 1250 306501070 306501079
    0x40b030322030b0c0901210e0601030b01050a091a0609010c080d0212060f0a0b1615020d06060c03080106031a040524011d090c0403050a06020a081501020a151e0f0605 73
    0x555050000c7c12001c00d41c00f81d04580780b100c569109024545410440038010321303000301c42c0e01d0f5071603203803a60740e1440902405010395054400020401c8141c0100c103a440f403d403841c02c036107203840020b00030b040e485112000c0c14401441118030000f8a00d400410b01c646110a00580b10040c0203095a5003071000b0302103510900080c22800700a9a44801d10021174031040c3c80c89a0b0b44080b8031644021100420300646814150b1b05e4401841506030004c1141c00c40384e4000b088410385800080d00c82010140c4046c0000704504014081180260302608030030003c2c1848c40e0384134000c44c0001c0c041d10000c88104041c00c0f40d0b100d01000000407411860300406017420b00800143d6083c2001b120000300124042c42403034034a0204659040b52000c4038041c4d5003102c10766211071580e0030241c01035032040103850001402140002c0c00381c85544411150200164041c20b009034203600e40c05188036608144244090341c1e1000c545465042031840944807000c2c3c0f41c00b050b1241c1a103007a03000c580da154040b9004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 306503570 1250 306502320 306502327
    0x80907050f030c010c03120e070306050a05040b04060b130216020102060f0112060b0a09062304150909050c19061e02121c020a03020301031e03050405040b030322030b0c 74
    0x103541c0103d55810324650030f10713000c0c5e980300e01d50504444e101400c60006a006141800e50003151402240d81030540e4000d10040c00312380c84454208040314000c90b005060703403010401207000155540c00001d02c02e00010840210862403880030012070303000c103103407010001281000c0b0b02107503014007060b40c0c06050a8103120440d8036202000045c5604004000e282e15580d16007000503075256010f000117040080b41c1001015210a0030400d0f41c404101c031090141b00d8070710704110340c0c0303098064100f07030750305550f00340d065070f46411204005880ca002e8115558001c0070314890864a40381114840a0760f4070038155101231400380301a0030602040c011740740c0e0154940607060b0103500000c8020b0900c0c0d01202850707985940c284000c0d141101c42c80c040d00076900014925100c40c0e4190051030580740142440345034607080d420319001d03086030745500a010030010700040050f841c09070b008242d2980042c003038914001004860185202d41501c0c0007401c2118120103009114590007003550102008801914 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 306504820 1250 306503570 306503599
    0x603060f1302030f0312011d0103050a06090302010f0509010f0b031506091f03030306050f01030c020a080a050403080c0a0b0c0c06011a040b0a0906030b03030f1204021f08090705 78
    0x4003030010800d0241c900700c201c0c4034046440420440b03910b100480c0541c2d40350801807810002d020360030b109421000d24400c00c2d0321421900d1012050490344e2100061070300c40120341d42c1001a24564809400395540d40c95408411101030191621a4113004d000050000484844408450912013106c1c0290f100e180d2000205192019450700004100e4000c16155601e00c078040801380480c1c1c5d038106203106044000105074151b0401c90030781c0c80885030480d80e02c08103c011030031074449070480d100503804030b071f407010206040d00c0c002c107907015551070071610301030b00c1e0303183c203866540890107c064590240105000340400714100c1500058090603891034030b90a81541c683d68001030152050150035070700309181c040d0740d0b401280e00030400b20329010340316224000d001e042ca055611449001c41e040c51103141c91032a004c0119215450700c2c1d801e842c1003038410a40c460350b42400500c2240c008458404803446220b03c00ba21800002490b80c50340d809c1d10740300b0303e8503080461a502141c000ca4041e100100c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 306506070 1250 306504820 306504841
    0x309050d0f0c06020309120706020405091e0a05060310060b0904140127090c120b0109020c0709200f07060f022803091b050a0e130f1424060306 63
    0x202e2680154026880340c882e000e100d4142034076036004c8820362400003050300401010303402030b108840040350f04803003640e034910b8042540300580d5640304141d0850000100c03408515840769400c40c502030103c6941401c07101d40d0b0001c480458011041241012410f81c16a113458010070002c42c007510111041549081180748502a4180c1c070314041024200e000c40281d0300c00d40c0a0b40c0d0140e0001c0c644006165921110708108401150a40d6111080c0c03001080c204094000c8031450302100c8014200c26160689090007031030358800b01d40448030690400d11855550401a040c1844c0541110790f4481c41031400c002251003035404100e01c140144241d0f00303000c5101e40b0096807124290000081c81c0c01c500c41c100d0003072140032001803c2100003a200c881e048051001c0c0d9041e200c0503100461450744405043e115410121000850380e201e5080050010707401c1c514103920305104000136000c41c03000e03410490070440c1a85c2a507013841840c145480010a50340304154100c0001d4014082c80c0c18000d1181 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 306507320 1250 306506070 306506087
    0x61b0115060906050a0212040e04060507080405100b060c0d0f08240f012d020c010810060c03120f0902011205060109170304050a0806090106150519030e030a0309050d0f 74
    0xc424403e01017400d50455000303000d10f00c0c04041806840e40e03120b8850620412641050f40c0941d5142e00e00000108994083c00c4d003140501d4000c0000c18040a1a07219880540f9200079010382000d01841808060881000350b90019005c4c2c0e00e801204200082000303144210042502c10903c00035155110a07400c0e030240f003041c0f49400d807040845c0280010060f00d8031404010344900c0c401015980c003203d411110019581c0d03942e2139082d150440b1041004503080003080d43d0100c500c18401d102081014010381304d841085100e800e104a440400c82a0601110005410000c02039110400d0704115a030110100390707000603050301088142810000209000a14044c021201114480c01141c10300208251002880c009140360300d0b0030307122160103440f40d000f170383c15104660031b000010402603914008611454903a44d01e4a0503c5900600100c400151200380c40c28580e844d18040400d80052006202d10425034402250314a0302e071420fa4a0625100d156008000c81d00042038903165001090 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 306508570 1250 306507320 306507329
    0x3051c1202090409021c0b070c05281a09060a0501060f081504090f0204050901021c0b0402070b1312020d02070317090a170c0114030c0d0902061b01150609 68
    0x162030b1a24100410000e0061460180d03002e002d444100315207580000081ca00c013403080c002c0600300c5e06c44000c10348840200520042881d0410141981d040c00d41e4652400f005003c501c0200d03505000341c80e181181000d1007030440401c3c800004001116100708006074101e41032035410001585801801000404036007200c0c400c12009002054130110f0070314061915400c01030040000d00241c0c0f5012281210300d0408038012070414000942c1500c0610a44580b101c08000600400c10f0078061040104041d00800381e21650038030107200410840c40c40c091290301c4071003d5100b5408281056500380d00410400c000310b5015000c6549125804102c4804590748400440f00000d1044030041d0240554003045800ca100390a00003080e05042034041003c0a44900351980c0d07900c18001100c6036007200c0b44005d20300b0410804111030701c210300000d101107040c042c4005900c555a600080c2c0d40c1c1d0200c91152424845c0e64148080f100c42071258012080c1500009020285000f901405c0003080e4800d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 306509820 1250 306508570 306508607
    0xe010b0f150d141005100e0405190c110f0a081905040b0a0302090910030c1a1c06050a060504060e0f03010e061f0602010b0d0609031701150f020303060a090e0a0204051003051c 77
    0x11412140051001c02074520328148248612f206004004105501c407050781d40c07187c410b11440c1c501c040070115800510300d40107030049160041403460300c4075041c071b0a03091404201d010003001803420b202501030156001070759409030350744240c1ca040003d0300002510301464411140010400298007802e040b00315a030719a079000300d0300070824640c1540e02860b00008040c00822420604400c44da5000c4015180700301c0d400441551186000c0b18079028038012000410f1404481c480c0a107001d17400e1840e07900c80180040b5069030401c4e20942406005d0b20840c0342c54010340c42c088107001100f15590080c01040c4020003450252a001402241e6000e5014040340e68074a1f411080c944240030725407105410000c42800c82d655180c1601144000b90f016034005004001c01c0e500061000c805c60703014500090142c0e9189003406942c10041000c1e40d100941c910582000c1e20040e1101e004203031191030341d04c000c0b4840c1450340c00c01c0c6003840c81800000510000c041c00300b4403500d4004446c078800008012 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 306511070 1250 306509820 306509831
    0x7030506030a020f01030e100c080c040602121c09032f070b030702031e0901031104051f030b100e030106050411031302011809020d0e010b0f150d141005100e04 70
    0x713006078014104003003551554065810007103596501500011038900740b668a4124642c1c9020b40322429000b40d008020058102502d00d034203052125016103c0303135100300c0c14072902031038554100c41101c608810450106600c25030582d402e043c024401a0840c40442036a0024840b0070070380341c7c072249140503030214200c021002c40e00c86031003082076410a502281d03800c41d01c403001a825407d40d4110903421800030f0300303000c9150b840100203801e0310210360010b00750004081c01504200802c189800004c420140d4450034502e103551102403040c02007145440d14030148070420305041c20b44030305400160141d82820b210b91401c0300100300f00c039440249007110100103251880100c0b101d4620703c4402d0600d0941c0d02c008911614954020845203040040412841100c509502d0a94040990150b4060038002000b07010342000c921a8a04e10b841d220b0b45460051000c020b10200d8056554005554032801e041010080324030b0040d6010307020881e88018000080c00000707100c040e248820714007864907803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 306512320 1250 306511070 306511099
    0xb03070f06180801020a0207030510180305030601020f03032403060108060403050f0f0307030509150c0301060c1505070e030d090f0b0d090f05100b0f090a020a09120b010e07030506030a02 82
    0x2d441c02010f885504000c4d591480e1215000359910030b030340400d458034080c40c02c550340140c0381c030700c103124048a56642c21001a030f01a1015501c40c1c0004008506500501100e00c221620910007984103401c2c1c18825607101d1410401d407406140803001050280e803001c0f0042c01000b0000500c664407660518040341c1d600f44000c0c00c0041ca0081040025034024080b0030711217016015001240324510310070032190780e80b2004036119001e80c0c05450402d1048400c200522003103106070890703420f41c0e02620086180c03100416420044420803500140028440c0f04003c51030710f010311200010f90024981405210300b840f60502c0c0c800514440c0c00c002c0800012145400c0c0da151300f150300a1504508006000e41d41c1d401c002e500c42d1079040c00c0056103850481050b2040c600f103940018420070103400741c94103980d0781003040c002b980300c1c41200d02480480c0130f00003041e01ca0310b15151040e504c1034841004035490080c01610a400141c2040103160409082140c10f44000901c003400b280c0465004c110910305 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 306513570 1250 306512320 306512357
    0x60c0304030f06060608091f0203090a0c0f0303021e0613020103141e060105070b061c020a0b0c0d0905060711040b13020304020907022a011b0b0a0b03070f06 69
    0x31070748010090078107141101d0034403c05501c80070459015403642406660ba00798102d45484441d2642420802c0411100107141c03025406903034054240070844001903c151140301040d4843c1e400032034855000c0d00240100765041c0601a11003907070100e40d000d9400e0b80b80703a240e01c07044010701d801c8040e05c3c075403440b2041da0f10a0704180d090240b2054807031242d003021711140b0040c0d4903110f801144015280d01080b069407003001115146500b26018500c59111981040003a001c0c811703442e01802c003460201c00143e912448044004d04500c85000d42e540400400d440c1045400c0e0b5421050142c03009040185131281e4040381c15903980890714044c54442500011300400c1241c0030550403030140000c20031504844d07801580902c0c002c84554920341ea456100700d03502c843c02c8603480c544e04500f00c0300c0c0e41481c030b40e030200d00e0300544141808000c10340301d200d0104040029490941301c42081c0d42c14400c41c03046a1068001c0c04c0415000790a49a00b800d80d80c4529518a1103000e04003c1e140c0201c40c1034014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 306514820 1250 306513570 306513577
    0x5061e0a030c060e10020f070605031324050f0408070204091b0902040501020f0a11090411100507020108151012020702060c01090507090e10020a200d12060311060c03 73
    0x18490164105640c035004018a0f504a82041500580007040f07554025400011f2200d50380a551000f0310700d86091010458607500050604103080b140c1100140014043c1803014207a0964181540080e107501c803050025200040c00d02560b0010303075402e01012401c04c1046075070315901541c01080c080254940300f21101142448031105030f84483e400320780380e80e00d9001081100d1099003281e00060381c107001262a0410b41d00001c0820f044900c80d10740c0380c102141017070703409400344000c0d03400b0201101c00f2941c41c03802d0340d403060006040010054110341e08944c2540d0803506000e100b000340a903031000f04500c07560440a40051048242e40060f4a4030160122032030f45034080e106c540ca0717030105030806000c0d040c8944221440d0050004c0400d0190a030303c5500303501160b0000403d01c81a84040c800d00079400b00d20400c081064012902c4c400541074903951051480000082c4800c04a205005100104203081c2d241828144501000032442a10100075900d5084441d01c0d960403071004540d19511 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 306516070 1250 306514820 306514823
    0x4110c0703030e040c0216090e0307050703031713020114030603070315051b0f07020f3106060302070203060a0507050403050a050f01050106090506070f080412150f05061e0a03 77
    0x2140e00404400c01d07500895044281d8000d4805121280c42c000c002e80c0c50304e8001254404a1401d43c00407c050760b0f894015255250b03401c002d4915014507a150b19080c07038455007055000c513900c100700c801d608048801c031940c008900035056041c0e000c180d0009110030190f1000480e18000070022844594060000c54000d6500c10044503165042c0341300030000e4a400c0343c104c0390502d00141c2075501c5100e081c080302c00c0d15092111440c540328407582009800710140d0714094021044030b1148000743e01002d850241c03004450b000ca0a00000740b03c1c80b0050b64030b00d40004040500501038040161030024442d074001c83c00f4240400c10f690381c8901122a8041c950000e0928419940030205000000c01d0074651036405000070b10450f030301c0d80d0041c1c0b00b80030704d0320074680c00c44001c200e1301020447c0030f040407040a02c02c0c0f0302070b49019995469000106000780050386c0c0c800444190012025041c400c0a1000c0c607841000c7c4028602080010900811144d0318040701110042c120034036546c44900c00042d6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 306517320 1250 306516070 306516073
    0x1d0414031306030911040b06040315020904020301060e090a1107062f210c0f09040f110d0b0f030309120a080310080d0201060b041806030f0305070b0f04050c04110c 72
    0x15036400004010b413410020a4400f01c001038100d10aa013010302a1415005c0040d010900d440e02d19a50515070804c0554000f121f40c1e400d201c1c03d58150b449000841c004c000c0c903940c11010b02090f400b0020580706c00303401045241e141c40c2d1000307ca40d00c04015111400d81010b00010420140d0140c0c900703881708211005000d02410356a003082d4448a0040d000b1105045102c0e000d9240d80d00702180d9018082e2051407004400b80a501d41a034402c07002000a901c001d400420f2801000c0211802e0711403031420048412030100e018407030043c00f441860b000c0242128030225010002d030119460384280000703180600c100071003503050b020040249248880d4815401366132403a11910710341504416000303620482c050003403070000b1148140202419110b00204045c982480c0c2840310510300c001990800d50701d41c8404000020a0b40095004800760017a2a1a5032320f80e443e240248400c1c0004081d2182d0280840a00c008210b000941c144072400503500007901c0c10b851120b100700d03400f4407502c1e94160f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 306518570 1250 306517320 306517357
    0xa0e07050402041205121c090302010e0d120e06060d06020306011b2f010215090c040204032d031d01030b030d020f10060e040b0a0e19020a1d041403 65
    0x604200384101c1413440d00400c2943c0c0840c4084140020398424011030b0307050842d03000c07203c00d00f2122a5100344110343c428000001c94a484100c158100441c000c90500410b241034240c02880f40c5500440d030a600152010303010620f1300800044c0354204403403019000c0c0d9400320000715036074000d907502e0540010705403400412100310700e40f280409030401360280b5040841c05000140c0c0740c6184203941403600503000f400d5480100f8280c2c10f1005001450ba0b103542c8140d9500b140c00ba290707403004101850140303a03001310a400000005030f140c00300c6501c1d03c2c0003002c50701c110000f00764003070070504075440c201c1400350364040d40c400120090210f00546940c18004e900042652a80008642880383c2c00001502d03501004150400d045541500c0307034040f00e5060300c001030f0001f5000e60b801e0b070b407201200710002510003204080ca80b81c0a070f0f0414908641c01020300c02801d40c50540da21070020410792031246074809048100c940d4041010308010807101160b4008a0f1004081c807c5d582e410300104281c022 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 306519820 1250 306518570 306518579
    0x80304031b05030c0c010509010804060b0112090b10050108010b0f0c0129010e040501150c021207032a0b092e09140f090105090403030b0d0b19050105090a0e0705040204 74
    0x200c95104004c5414030b8802c5128a80295016a040c0d50200005031940401ea41d00c5840791700103044000c515604010752607280750b440d09000d200711000320703001d1403401005280c0044001c00072101904018140301015004100e1108800c04650000070001c0a031521554038401e02d81c0901929031900b004e42d54918124600d0420400107800c8445090f40c0d01e102440181c410700c0b0841d1802e00800f109036500044140c186070140600031826440540031142d109841c0c80510304080c440c0e01708a4801074030300000c045c0c49040b0740e40d42600d000b6044840300ca1524081d140000f607c2039050080c01550080c1c60078080c40103881c00111915000c2c1465442040c2140c40100b003403605000700c00c081c0f40034040340a0b00341000300b5056200302d005030081601d6428072082202d0720800500850425480d50f40800d126290f040204001c03d00c60000021181031662145450b2103034044081c0516241c400108410350b44d10b00e2064010203d0203000070260381148449090418681125801c00d000260000c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 306521070 1250 306519820 306519823
    0x9190e040f05010b1522150c05070e040b06010f1806030506180a021b0c0609060310030f050d0f080f0105060d060e011e06320c0d030f051e0103080304031b05 69
    0x140100c00400c3c0c0d0120386c201050325240030481c2c2c0102040744001c07000d00c4841a014030641c89000f8011401c440c40280d4407841403001082c00c45044400c0c64000c1d003409280e5821070103452740b80f11181020001d088001180f128542c1e0b451094108254540000c1707201030701e030f2403100480c43c4010120f8046520340303425007402035486107240100b600d0217040d6009a00801103110859654000d246510700214401007040c1500041d280070520500d450000000510304078104441d144544082e00e04102c0b41c86018164040341700090003030104003000c0118840c41031109130305661040300c5040e103624403010854000d06040e000f44520181c400004601a42031180c10300100d4130b5607483e40e181948966044501e42084207411820441703007451824191141c040f842401000c02c2d10700d0703080c124082c050510b0079504c442c11b0b0011a0744d40c2d007281521942401045d030302403405407045a07862040110760340300801c14032010306080408000325041512600c01400d10075000a42540c1c80a09814242d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 306522320 1250 306521070 306521077
    0x70602060c070b0a150b0a1715091b0f0414090a020a14090103090606090504020a0b03070c2003010903092d0b0c010e010507030209190e040f05010b15 66
    0x1401600c1220000740c2a2140740044a4000340c0c080040e0701c01e511040b040740d002c2d09014440c6200800300c000003007150b11004018040da007040365202c001480301c1c0c50407521049809049242c0240e2010f801c61060b4540844c2181c00640d2881c02d64a04040541c0b076100c00d00a101805045143c00a000103070704680d05002c00d40400c00b250400c809445400b40740040b4400c00c081d0001080d841e420f42941c00101c44068100c01da010304020a480e1044d540300d4003100d00c1908048032680c2d4403024001942010350707440000e8011110b0151030750038a44005041140c480d0002004084043ca40074100d41080b20140209003025000303105501240c9009000d030201070040008491a6810701810a10111072040c480c541d8802200d00e010304104070030790194803100d90f442c03041d900c59075500200c80c001d100d400d1003600160b03001615003100780e08200862105010845100501e2130080c000b04590360b02143d0800e9000c000000030035001d20b041405005100003456010000781403086480440038000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 306523570 1250 306522320 306522329
    0x121d04021b1203090706080405070e04062702090a090204090501060308041d07170405031b100b03070302030c0415030b0f070905011817070503010e010606080c1815091207 75
    0x6555610241d54a4080b403800f00b2551450300f5071001004110890182d90303e990418028026030b60160f84400003070b03403c903070140c90440d1016510f0031401d5100e5010246000c00206000c030940d0641040c1e000140002009400401d450703650300c041c0c500310340d00c5500030710207960310a00038030866940c0c4c10b0005250700184110008544142c01d40d6901d0002c00c001d0717512035219500c40d00c1441c44184441d100598005000700c0d0941700400003095201c3c00030140c0500007801c0c0c002011000b01c0d00950405480244403007a0003540702510500060343c000ca08040114800e450000345c0900724980d102e80c3c0c0c07099a10181040103500d0900a0110081c1c050f14031410f110307199100b21569400c01141d0200116200304024800e0300c80520410400c5c55000303503101a00b108a5100d252103074000303800c403000300358038441c00d0b959030400b045105e400c412065404150360f95013508022070070f90010b0b206a0b0000009110740c200015540399043c10000350f51140300c0140c100001002104145541d440c041e000c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 306524820 1250 306523570 306523573
    0x102040503013207200f0f070602060f06011b03020a0b060a0303052b0c0203040305011b0507030e1801030308041b0815040c03080c030d0b010903121d04021b 69
    0x100c26104040c0b0351060700d041c404480c40b43d404100000015029034602030055010000c580c51071010300b244901e0341034403114030113020b00402d00300da0350440c2c540416003072032409a41246208005203600811405d5211802981c80301940d550380c801241ea566420a4208001086e0044441410b03030000d44000ca503449400c0002c0d060b1513442c00c124940c0c250f0302c4014001070f410040c002075a8011004002c40011a002c1481141d407036842840a80c0c1d00340c0718590041c0d10105d010814071209002d2508200030001c68a5044010070100030410f114440014041c044c0701a4521000d85030503205c0c1600700007030145c0140c0c550f100d140042c9482401d803015070f600c841d5103040301d04242c14880c4043c1244c0b5444010b01441c0c00b52501d25500007001401a5079615989a000011a042100030f12150004c00007441c1e80300c250b180b020040f504031031790381da04101101d8010b0000a500c4000b4800783c1145003081e00c48640d0011349240c0284a15080c41d8100d400800d1028580c400c503184555204031900 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 306526070 1250 306524820 306524831
    0x705031c05070306180b0d0203062a09090c070f170a0f17011a040308030708160c1211030d060902090a0501020318040b12010516080610080a0c031d010204050301 71
    0x40049040c0d03650390203900348000081c04001e940040c00d03404481d2044018061b00e03005c47c00c9400081c10075904840140944007500b03840015041482d044103e400c0404051342c1c104000c5001182400500412000040d000000c150051100c5410148030f0190b202c000c14454106d8039100140c43c1e08000018008903042e50310b52486d00340141e200c45003a90b145a09402d0030f80c0780800d50406100240d08080b40700804210100100b08210001d6110300c0c4280c960808504004202c10710100300f800072001040f8070101210000345c0f02c102c003075460ba51289040042004d44d901662b0840c03280a01054042d031401d030000611511a4029000c2a48120747e12440313603595400580e12031086540e0303c1600c189801c1c5025461034203511506c00d07420094000c400801640c04901d007140d1096414a12a425820300c0710700c1103605c003c400707500102c00c0d0b500e01d2801542d808013400d51007002d8114000c1c10340b61040120120712a911000304902e5410b440e48a008100190783e000b98090b002d864001e50801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 306527320 1250 306526070 306526081
    0x1906140606030f07030c0302071703060111030a020705061b010c210c0e10030207080d0501090b0105040509180c060a080108061602030a0f0207090f020d0609151a0705031c05 76
    0x590540f44603107210300c80300310f099951800803401031110b0400d4a06042d401e010480c0400c2c216149070034095026140c80345d9a08060001500c3d100002942e13503600d500c2040702c1000d040d070100346407003150029100c0301e403590342000d050078000c400146000461340c40c001c2a00c001660092214040c140391110f0041140c140614084c10358040600400104443d5802442541008501c030400c01030189001030401e912503985012960120b4a0b0500e006d84a034010300c02081b0a2141044d20b1409086c0140b5051524011520741840103000d040889440c26840a1250040c071000c0300da0b81e4014816a62006240700103484200c082c0128041c51140c0c6000540340100303103417080704024007a001142070030034862040326003400c100c14503400c5004240c0300290921003400744041040301c008000d81c0780ca00c0d0b041394030100c0d011640b28a41f82c03400d0a1040e124511403c0365002a2012540c40414054044c18850101d120380b0790003c004c0d03c40014100a810a50014111040720b10300301401a6100d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 306528570 1250 306527320 306527329
    0x30f03020d0e2a180a090c0f1a0301030c0501050d09050102270405090703120210061502060601020703080301090207110d0305030123030303010b0c0a061a03210301120519061406 78
    0x320f49003501300320641d40f4141c00d4940c1402e03082e8045041364012079824540c1d55145410f1585600100701c1442c454014061001080c0c8070103501d41d4012425811980340d0344480c0315a46052043d18117001000801c11020f45503900500c1200f07400c58000d554400650004689401208141e00c00791004000341c140c0310724050184502505400c0700520750142180c949034940703801400c403a025845500c541c3c0d155002140035110003401080010000c402e180000a07081400c0200100c2c1190030024084c400030380d20300284c034159080e1100050701c4a20f203260401d209800407110740e44c4800e0b081500804c240e40603008505840440b200d2107480210844102d8240d8940300342958990810720041c0008807004001e008030071320b09011200d1841250f2500011150711054803107200510b090301c0541401c0c10002c190003401c8004100303100c520950810026800180140101986244861030521a00b0010f0004070301460204a24688036450480e0007040064011001c410303104c000101c40d0b150 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 306529820 1250 306528570 306528643
    0x9030d061d07110a2111010513031107090f02090f090c0708070c030f0c0e01150909050603010b12240c090103050705190e030106050406080a030f03020d0e 68
    0x2821000741251140c10003600ca44044126000041c03080c11544000304009240286000590000b800358082141c000188041c03040480304145a0410f4207004480701004903240c45190180781503146040014041400c15032154403140b01e050500b0768034500304829600400c01d9500880d505c24800c1d0100e018049003a208852620f03100740e00384621004280c0f1440201540d030f20802404501c25126614410030401c100c205443c4413aa001d000d201115010301118058200c503049400000c00c1c1c4c0e100141a88417a0180d46603481d1544049503080e2030941002d004103034003d0104820843e1044002d54030980340d2031030540e0136054013414003114003861400e8003407008031540ca07190003034800040d00030f44006415403041140c00c0181d0b0040c0003007920003980c0ba80a44e6603a0f001002c0c07440c1054250303400e5800c00740c4202d2405c41c0030402e003100000c0001800e41c2c103042001c0402c60742034080c0c00034007a5101e550141c82c02c20700e403184204004600104a04d540008960a405403100044142074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 306531070 1250 306529820 306529859
    0x50108010f0b0c01150b03090d03051003140f01091202061b041403120f2a0a230714040c080405060112140102040303020a0b0c0c03090609030c040509030d06 69
    0x40c14030054004500804292200320008941803c2902d01d0081700049a885a40180d6001c000e10030b101c0010b00c040c140f480d40c6894244a07500700a55010100e10b0180b200404511612490308956601841102422800316000308050b4141d0300344058030b0800008080014000c04001510714030060b2243d110034030380e40d0452418a41402c600d01042c81c1949071566051061049180608404d400100080c0510344034164454286034882350007a40139601426003107101c0700264100d04400107010000c2034008414580014800b00c0e40504401003010f50070a600a00401089144a0410100d40400199010801c840b18488100d6202e0800d0390024100d4000c0401046075105d00203800d4901c41c06642000520803426010a00f20fa005900807005a0001e690302c00034003240d1540345030f1140303d2045003031810b5159500e00c0d40340c4c422541c500e8815034012541c15415141000350203a503c102030400c1015003000a00d40e03a498001c0d0300745035101401c08402084281c4848030300840d04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 306532320 1250 306531070 306531089
    0x40c05030106020d0305090307080702060c010c120b0603040f02010e0d05061e15010f050c0309061c061211010f091502060a0b06120402040b04091a090105150907121508061005010801 80
    0x1000b0ad5031902d16a501c5020241ea00100502031285401070a11a88242c1c4441c2c1e2505043c4071f0303840b240c0100366001c03215924450941030040102040442003a150241c0e424a0440c200b200c401e800641540e6035210060b1440c40386004204405030401c08041404543c281d01310603d07034401d40c01c00d000780e0381001ea40340003954486182c03174454050006404031b021100140c0b0f003030401140100300d2540200203119903225400b0711701c16200e00c0911840d4041c04030b00d0403c00c80b20340a51209900701d8030100429042180054030035903542e00c07801b840030140600003146220a02c9032100296142c0c03080d60b409412600c1c0188000852030300034100e500c013560040003040b2075642c6408001c014000f0b924910f800a481d0145080003411204900e081d8004214051506050500d000c50031144000c00860011005524501107503031883c803003940c0010b1529200c804d4540103480b06014060654508015610410000c508444041803291046281c200d60a412075550320044605144c01c0c400c20600707 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 306533570 1250 306532320 306532327
    0x20c0d0201050d0c0306091a0a080114130609080307020f010510080a0605060f0d0b01090515090a05091c020c1314190905071203030e1c0c050a02040c05030106020d03050903 76
    0x40d8401138004a1640c1e510381030004140d5039400c0d8405c142d61109101c520400c59140c080c8545207001c800320005070405000804c01002000403143e4240c0b0040d0a17090380e6046d2083c541c08015103500b100d1000350340201100d03102d0900d07000c081d40d0b40c110744401001c2542404d00051844004000000480d80c03c003000700700c000b9458580b8002407502600080d002450520154566100c401400240d40e1088035011038a45c90014440d007110360151410f066000d580780f0841c0c0c26962000a207030080b0384042d002800b521642d02c06450f141a4001050402d480c00389144081e54003c5005051614280c07a02d144104a0000810440f05c84005200300308080002064043c00c00360050001c00340f9202e0b000811075a03589690b032411201344d005500c45d850105d803180806902d07000f88001100280c3c0280f00c240c01c48546007000c84810b010280821005c000305206001080208000d2a60007510422100d0007240008005a00034017400000d03214a440a00d4154071038440c403481030900002a606 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 306534820 1250 306533570 306533587
    0x415020c010e01050c0f0a120908060603031801021032040b040f141005060112020c0705011809060803090301050c1602060901030603140105010609090c020c040e03120115020c0d020105 81
    0x791358110f603091010f140302e00c0c2d00400a03800f0400c210981c0d40e0007180b6000c0e0381c3c008c22000a181811542020721a90031800911500c0c0c0c03000000e494140c0703100406001c0301102040100e251070910003000003c3c0b070822804005881d4901003441035450503000080700744d40c0e5140c2400c540101901e000f04401c40085c00100807405550001d45203074800d0304441101001035160501e0000d44101030440903640e502032206960300213000c00740c54809281d086d4104000303c9031181c2c0306c1035640728036418407058100a5200400354242e40c0301030714a102d020420f903500e94440e01d640c0e400c0011818003d610341800310f01c0b1101d1100c01c0d10760345480c0d000100022201513003403099030b4114011250602d03450354004000101c546c4a1010703401c400c0700c00002d0940c0f408c140205a0301c01a0f02c0400d04078a446000440c00741e000c00c143d8203514090354049266208846818610700c2503d82c0c518502c1400e07070000c911400c050161382c1d40c0340b04176400c840e20304e548082000011031100348000d000ca54100320030203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 306536070 1250 306534820 306534827
    0x503120f030601170708160f0c0303112a190210030c031401030b0709090c050d0209150703051c05070c11010c1b060810080307080d200415020c010e01 66
    0x164030440624013094030094003550124488000d031884404100c2c41c0c0c0c1007001d24150409121603c4145140c41000003690500191003400340c08405000c05887d90400c80c0002107a40c01c171084500f4138180d00074004c60040e10384107a0505141041e040d0300406c1c0c3d0101c01c1416103c031601c08150000d058801070030f90440e082c0c2c002c0481401c0f10061540f90090320107604854030040d8025801800d0b030340b440c0d1606550040100c1c2c2c10760812902c0f00e01d00f5140600360390b03204041d40d40c41c1c040343c8401661000200c0c0003c9100e004586070328500d88001540c0c074109a4001d015026182002400c107009600c2c2c010504107860007180c01c000000d135001191004030340032504000d0078003018140742544400300d8a4131034250f0201071984010031901c81741004042e0340083d2044d4803030110381800c0750352030130288100d44910607071201400b14130b00881c02c148a103035580d0100c0b50020b0070100d0382c44649459030711068190003a119121341945040003450040d80040303016001c26005a40d0100309103203060055 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 306537320 1250 306536070 306536077
    0x204060f2a110306060414150f0a0f0512030406020d0c1b2301090311211005160c0b07051c06080114070f05030106050337060503120f 59
    0x45014810402000c8016845008041040d80502d102205030048034090610306100600018002d80c0f404800c01801d0140240194100702d44041c4074800e020503c001840600380c0c0b0490a521205c1013500044191702c1c480c0700011600c1c1541d45102281d64581002c2d124040c0348945805a00070500b028441440b510082c0b0000707220311803c40311100c0249150b0310043c8a504081c442d1007444455900e0803400c005e4485001c2c07001d20f840d00e80c90741035607100d40048803001d0a4600890f000c920700799907900c24110400030100480100c804220000c403480300508019510140d829521024010900307205070078408001d07422800c10340940d110203034100c520783e12a08000800d145084910050034016000300c0009102c22000030843c98014026202044001780c05841400417102c1e084010350341001c1600e0450f10142070040d00c941d920180c2c0244500c0d010440c50801e040c0c289182601004c0503640c090020380020300b0014980c50b402895600d0000c03c04a034081c0c401800ba1002081c402d5005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 306538570 1250 306537320 306537347
    0x703170f0706020d06050306011202030309060a020118030c1a04051507140a0504051305160302030603010b0a1e08010e0c191505120901090206030c03071106090f070503010204060f 79
    0x549809110348070602280c01c1340341040d0445864400400162134100452030241c02041d10708414041c4590000b82d1301e1041c10002d502591012a0500305103000390301c50100c0169035034508009000710303d0b00524a000c52034084507106e0411200e54062000d5200e41441142c0c406c00402c0ca03055a040684a03410300242443c0400201100000c0450341c440040d0a100c032540d240c403511141000100242c1c03c4000065110540c40c2800f045281d40c809401090102d8045c01c0041e641c3d1100c1d401b2a0140c407200c1c0156404c000e01120000e4026215018503400080100081c01c01d40e889000207400d84d8000c1803c0102a404081c2c400102d260020018207000c1001502901c25907817003c1d910465801c116290313005c03500105000090394071300070465500080602c001c10905131aa4001354040c00060000c1c80c0095001c400103140c0d07030080c180d0046401c01081141c01d5450281d680c6680d414072031000110a0080013400101030405000341c0701551125154481c4541602e5000c03604068190748 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 306539820 1250 306538570 306538597
    0x30a0504020d05070906080f030f1207050708120a0b0307050a0b1308010e0129030a23071715060d1202031902010212130b0a050603032a0f070317 64
    0x42d00740012010400782c0700038190000302041e80c505e003031803881c06c2480e034000f40c20b1250410084145889401401c8a8640c840b20740b0000a98031103210442c4e0324042c540c00100012400100e0303010002c4030a03500d510560400c3c4051290b000664141074503602d0a200d426000341e507880e400d0092071000805406040000c94a4911081d03503000c070142510400c000030180360b5559070f00360407068140100321210042500504180c425090302190703039000d80700006852204c3c0c04074540e82c00300c09030074415240361480045030700b4035840d417242505460994010720807078411300303d10109002181c05940c1c0f10721001440d900c0500a2600c070124072407613491f00c481c2180400c0050300f22040d03600c200883d000c00c4941c00103888100c43c4828004000d8003601c00700800c0405096500080c1803e130381554840b407050800304143d210800400d10750300454604d45030b40d601408200c0d0082e80d103150381900c0d1b54071010460b040f000c00050140d496903c035010183c06060030380344150803c800d540003020b90044000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 306541070 1250 306539820 306539839
    0x601090513050115060e01020a150f110c06190902060702060f0417030406030606080c030a200d05150109031a040c0b0313060c020c0a14151603020f030906030a050402 73
    0x190b9031421954080395241e07040c10f0070b81c001d00c491548040c2c0440e04010a00051040d101030f62102d00d10840c11406000d80645c85811401c0003081070740002e0501c1100e0487d4130707101c51111031034940340e0300e0440d54120100c0c00041140c40518107406000c25058002c0c00240ca0141350703400340820baa001024050008004120008a00c2540f0200d112a0721911020f5a101c506000c00201503c1b802e44c0100c0c1042030403414800b0651b0010704503070700000d9107040040d0034840750b9020242c0c82d403000c100003000c40012500c4552140640c000900c643d41c416a02041500550019249600540006000b8540c000503046a5410280e1a00c0c5c00500a0356020f0141e40d540d590302c903090740308039001005522280c6601c4d007007000e6401344580840c40750000c2d08803801444045038081c9940c0c40b41020300543e114200c84651514109003020100c4102400d90300c0340c0c0030000800d8400e80280490052103050702c80810514003109942040c48010000c0d072564907203800c03260280030040c00581e40321801e40b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 306542320 1250 306541070 306541073
    0x330f0525180e040c030b0601080f0105010c0c03080301060201092109030312090507260a081909090c2102040302150702012c0111030702060301170708010c120f0e0601090513 76
    0x2d19400d0f00c100d12428001c2000c0e8110f161507405000c0181485043c00301d10014404250076041c05141034401c00e1030120f0080c9007038100b17200e185005601c007800101d800400481c0b559811341001050701e014104400c1c550442c1c165042d0b04442202e0003500241c401c8034213000080c0b01e9078000d032070701940c0540403401031059110030341492055800b010102421050180502c40d910020f0340f00c0e030610364080c1c01c00700901d8481c48414400c408600b40d9034056030542d0701e5528064420040035120340d500810a000c100c4401038a03407030103039203030010380321482d64409000c0d07401c3c0c001c407419694082c1075108082c848400d01d000541016008030305000b00d1100c40030191214988001008503040c10708000d441ca014001b501441c200359040800313420400082d00562207041c1100c0c11074040321031a40e4221844644c207030602000e9040700310349500341448508a20f6128000f4a042c2101200401c00c4107801d13100d95044901c031081e0900c1c0d0340c101800400429090382d2001c1c0d88400115111455040036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 306543570 1250 306542320 306542339
    0xf060711030d0218040605061912061d070215070f0f2c0a06051e07060605060417070b030601020a0611090d06020d0b030105040f330f052518 62
    0x80a580307000d0207040328281e103485c0740c140a600000e190a4408a00d014010540201e8a01c48030004400344002c3ca400c200303582005500c24001000190881080c40b6001910000201ca0070740d000d0005100d0100c5644040072540a010b01840766130310303000c4840144a9091ba046103c52030b245080c070401000034400c108080c2901c210300a900c01864099480300ba040040a00068115404110051101180ca00b00d181160007250004201c0c0d50740710324040c83c0c200f000d091070760406034004002040000d0144031302020344455101c4202550841a02c4901c981c07a240011902180143e00262080c00810070b0366216a50101e804244d4a140001341800b040b00100c01c02000c03600564000382c5103e680b68a482030710f41e01413003200203001905140d12001b0700141d450300e001d801103400041c1401420030b82c1c1c508402e6540c1ca019070400908881000e07500030614401117004a80c106170000d51281d408001c211410f01e040d082038810160186022a0744144002c20b86010000c7c01c1000301c0d01820 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 306544820 1250 306543570 306543577
    0x1816090507030606020c031002070c0b0406020f240c0c25030209060603040f02060309030d330b0f0a200f150603030315040906050a0e07080f060711030d02 68
    0x128040440d060030000c00080440f815580500304640082005620b503a901040381244c14150304e41c051384521a908000c100c45407160b1094840706400600050500d401282c1c00e8171402e43c0ca400e460404581c0c01c0d113800100800e10301500310044100002d1144940da0000d0302c44146214103c541c4820045180005850b510000c2142c805041d4801c00840c600352a80c81e51204007030f40d1060440c10135950b041a0913008240003489000080009200e240081003615440640c1c541e0a01c02140c5000c143c90040d011401d4094600b04158a50000110780d504994212011041903501d044c5108000214076013002d81620f0811541501902060901d210781401840c42c00c409001e607c920604540e16000d843d290b40b0070890540020042103980100c1920f60000866002c101420001c40000c0c0040080c00c03401480c5034034000a116105c0520b5001074040e04520084640468440040e12707961044850702c403043d0f5002d9030018145510409030355220600c01c0c4212401c003414101001e090740c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 306546070 1250 306544820 306544829
    0x9300d0c120903050c1e030403020409021207120605092a0301181505060a0f06030209041e0902010225120f080f0c190308130819030f0c11061816 64
    0x400106a49038080b45c00e004a55000b041160404014a26018915140d018600c0040d104903907540900e429520ba8a040c1007050b010b103015110010380f5205d0340d49078058070354010f0f03e00d6032800d80010100d81c07000800a8611150210048010036464040d01c42000c494003496099502c038a101c0443c0702c03491414000b4948543c55000380d0503c1008072000b2150000c6c4414401c030701a2008000442d4150f42c1e45040d9111440d015030755211b4074001c90f02130a242102602c0c0300c00c00d43e40040b401e01081e401002341500c05d03400c1c0c0b042c0380402001e00b18100445804000402c0c50030000304407221030810550580e030711a140c00000c840a5440d00348042d0060040000c2c071100c00580c05410490600a030000c450039440c0103106d4404948000f45211401054801106e500500307000c140030b0315100380d694203100c0000c102044904000028080d000700451703901e030942081e40740b058a5002c0c03001e071a1244241e0004240c40da0b24080d5001000c202c21000c0c80c1c6501425115081c0d40440d910118040d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 306547320 1250 306546070 306546077
    0x30d02031804060f0312031413020a05090105060f03100b070b0a0c020604030903030f020a0c06030c02010b1f05071103071418070206011203020102090909300d0c120903 74
    0x7480c00d40101c1000211030504944101e00d008400d208540440600304142c03904020381d0710440c100f83d44190014003052603500c4a41c0c41c03442c200003016509031100d0003d03510998900050695800c24811160828010720354890700901040c101c0d680e10101542c0c0c00503074100c2c888803c69031103440c44000d500c06441583d0344840391040186007502400307000b04240306ea100802e41c0746465200100180400d0000a08001e4a0704001095910070050701e01890382014101ea012079403040302500a00c0103a074210099400c01e041d203001440d04182c0074203000207141529a5018000310102c40c50b501803002115034002c48898540b450714100150380161152450101c2da20f0b000e841003022052000c41443c000140d610104003c4a0780030980310304507200303c0b818105000c81d515003a8064050b5800582d0400e040004100403120000f9050b074900412489085002086100c401589543c40c020b269141004000d42d0420100d9540005d08031542440e02e80301036806d0aa0740c0c02543d0801c001603000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 306548570 1250 306547320 306547327
    0x40c032c2508060708070e01050a0215070305160503310804080705040e0102070510110f07120305060604060813020a08100903030b060c07140105041d07140c1f0605030d0203 76
    0x750801003003115000f8a1340d0524a415240040005002d181404d07121410810041180c02c640c60003001031503124a40204443e01a1802c680700600411003207503044404510700101c941c074140039400301d900802c0020518980b85044007032609110b0039807850180d1009540b1140c5000c10380341006003019065000103008401e00c1d000c100010b603107449140360381c2a48104072400015500081d005440c048201c00410170b21103000800d01d0034002c104100c075012400182c0c40040000e01110401489102d40f0100003d8880d8000d0080500483c000e203408210342d100480c410030610a440a80c2d240f0003004484115240c1d04400e0401c2540c03540b54507981c0d15410881c0800d501809001d000704070956101d4200080d00366500d648500612403040a00f000111402c06030340708108940190400e0421400030440c0007030f406c0c045000c01c481013000034070381c41041100c924101084500300e6000400504141440d80c00c0001c5801c0c1d444d402031402940e440c40081e25880c1070008840200c21034014644 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 306549820 1250 306548570 306548579
    0x3030301080a050c1806100504170c0907050f1806070210030902240703050904151212020a080306040c11100b0a090902090f13021e040c032c25 63
    0x7508481c0010a403040c60040510700002c085c00c00025401131040361f400209003012101502d10744110f820a5410014030351001a082200050300000b00340700351a80080d80e86c90f0001114140242c24031482104000c104600113041a024070a0f008080242082d203802010760003c0c09012450f0700d035a001c207440300d448000303501d0150780d0324912000000e0740c0d05110444200c20b00d03040c480c001c1f0040c1800000b140c2010247c0300c0f94444541c0c558000065030304c69454110303400c0307440c00000f01100d48e0991901340c202c1052005c80c10b05120350344041481d04540f260001c1102030241d8a0250041041001001c900c103201048044111040d1000025906100006010317075594942c1002400600744041e032001a140c2100580c0d01c4108030801c10704984411140c0d0440070180f20010b03600c03900040182c18185411098210b06060440b020002c50f40040d9064060b12001481050b07802501c5408000010003140711644c5110705000307650307107985110700e0307107040412a41d501740401004000910 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 306551070 1250 306549820 306549823
    0xc08060f07030509010b01020723040f140a0902100e0303070f0c0f0918121803150f1503021002030c01021206010905090c0a210e010e0601060f08040803090c03030301080a05 76
    0x61308991114003d200c04140440041d5842c0903921641c0c030030784481c114042d203417002c2c40c03041d81c4400382c01001800031040d8104a0b0303003c0c082e505c0815107034034a641d003c103c02c07030101e108407070300254094114220500480b406591406031000e107240c140c00100b2609000400781083d012943e0700c0b13a8120380d1401d01b80481555031b4625a0400d0f008030307243c0300059006a123020002d44ada56400610410185400f000071030340040e42410b09406c4101e001408008c00050a00c82c01c181c5030000c4041006154500d00c0350309544448803840c41e44040c2503000e0016050041c144040ca150500440c0e19114159023200c1c02c981c0100420345030910f100060100e40e6901c1182c0e02e004240483e021201d5040048848169215205182e02845510200700302d030070b420300c00503010a0750700007420400c2044000714a03010300300c0006c0e9140280a000004680140240c50030940404203039105c08071540c40d603480d99119480601001518070030251400340a60b000c00056003e0710040000d80302d0b11144d4a0807a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 306552320 1250 306551070 306551081
    0xa031b0c210606062c0406081509100515101404120b0604050415020307170a02071a1605072604090c0801060c0f030e0424150806010c0c08060f0703 65
    0x440401146003814200c01c0e03c61700b01420005032215107020000c0250002400038801540024101d00419180107808124003414502c110128416100034005100b00c0c50202c48046032441d114080b40101c5424a0400202c104e60415281c1404240c0c000c440c04004a0703904a45c1c4030740c0711440c164100c42304004480f4881500322005a90500090800da640c0c0307207d070007910f030311a8401940400010403491103024524110380e40075401e0625400c10000d200c02a500c4803030305554180c1e0340100405c001840c01c20b55803240d42e42401c85840c07044140390480d0305510840c0191202c4400b06110000240911a603111030780e080328505507646d180800d84010344021085070420300070f0120041040903007200c1d5040300300354403603400d80390f03c41685401e86005581d195503503009407401d80e240030804d100d0822135a20101c9100d900070450740c0c80440da9040c002001e00e041c00100e400e400f0400325401518071000e40c0d8442c103030b02c001541d1070345002032408070201c460302d400b03001b4501440081c94051040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 306553570 1250 306552320 306552329
    0xc031e0c02120702090f0c09100f021603030e0d0807120905030f0102070302070501080c070501050f01050f0d02030c0d0f0f0609030806010e030a0201140d020310030b06030a031b0c210606 82
    0x41d418041c0e990001181c404005121060706c801c03070320005000b21107c2c4c0884810f48030003032045650920780d000042c0383c400e14045200c05071290300c45040300859001e0401e402c403641642d07103805080790113050119132003c1d404219010f1030248119400104025a1159428206d40e01c401c000b0746446c0c101454106c070b0307070144040c59204000c424042540860b032002130310400e080054942d140d180c580103044c07080003030140c940d528140511042c048081403c504960b81291541444c0d6046801c0010a000c0340400a6140e4400c2036217401a0910300421040c42c0c0c0140c4003540210035079240d1078000c00b0030100448400340d9030b008000405401c0700040c0c1e0010020311b402014a010403021907528168100c000e81441406101c1a020207100d0007160326118002c3c401395140d0900c10740c885c400c01114041115028801c2c00003990b11b040000319409095056540c10030074100071311854143c1c290006081e100ca1110900c04150f504011407510380960303050b10034030b040c202282002e0702101c060307812 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 306554820 1250 306553570 306553603
    0x20a0507080f0d051e06040b0d05010507090f060203040803041e0317030402090a0204030f0f0203012403060e011103010b070201031b0c0512030c1215091801050115050d0c031e0c02 79
    0x944d40c17585004070550945c4100251000a035548140000071003009410100802c00d40c00c0008000c1115030004410085444a03005512019202c480690301c900583c0079482e03039940288170421881d82c4401d00801560342c030381032450889840b03498807101d4143d600302610030721000100740302c11400c2018010b5886036200310118206411136603544040008810090441400a18200b00399a02980404a02008105c0003a6043d14003c2c0749050000540300030b803886490000100c032032003018052078248000d0140e075680b03160300300082e80e13481f500100760907410196a5011103c1300c1c00d44080240c01650301c1d8860817024130141c6400c41c03a03c1c40d107409070300c01d205040c42403004003d82802a90010321001c02d2501c10340d69040758404606030b4900c1444c0d40801e204c4107109a91003049010840245204000e003d1680c0300c4a11030700c4095014803a0002402c10069480300c01ca065220500c903d00c0e601c0d01142c146110342140012103d41078450310200e80d1414107000c81a0100040c40d0300144005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 306556070 1250 306554820 306554851
    0x7031a160e10030e030409060320030c0607031e050c0d14031801110a051b0105101203120515030106060e21150c091002031c020a0507080f0d05 63
    0xd001803401e44205030450042d0700c2c40d000315038894002d4000c50300c00740040c82200d031120340d200210b4010b80700e280b00540f50072001e1001910b40c86185203001f03040302d0b0003900401c1c0a0030302105104e1258404c603010b60801181010305100150080d86c80d4070181c0c4555143c0351100d5401130218109480711807100c0030321120115848184c1058016254040303040307100c00b4003400070048284d024108040c110f81e00d0781c50005100ca4880d8000c0c0c0038028481990304841804804078034503e00303d03241500c030b4568030301e9032030410080304640e14840741da018402e10b8a100d0046a40e101802a04e8054884a1744e17880304801d840001d0030244110b0000700001e1400c1d514141400012909840c0c10a80005001d04001708000d01c60104215064220720100d0320a00c05142c0b1b9040802c990300000f017690301ca19502000070700a14400015101444544246450f4800c03400b40404025403200c0240024440280032850102d07160344058448074221000c141e42d0303a00d10240c3e050450f4002008008211080c5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 306557320 1250 306556070 306556111
    0x1011030a0e01120c0f14040509040609031701060e040506120d020c01031104060e06070618080d181218081603060c030501081203100b030103050a1716020114070507031a 74
    0x100f02121042c5d5a0502c40210801c8450340d411314421900440c0c0c2140070f6134103010401800c5e41c0221403080c065a9020b18010380f01d081904504020310841002420b00020b102c15441c0030391010ba08020010030580c2c40b0190800d00c60f0914036180781000250b000700b03465600958040c0909880300070140f46881c134013030800d040a480f02d051110107500404000c9880701c1000300980c80f0000c8031003103000042e02d0801c1c510b4034075115403000310200c20050a180c1c0c101c4440901c128610b10b01c80e404602c0302407110030580c0880d141072010307807051444010040000340c220740900c495a400003603a214003140508600b049000c0d1405200e0ac1000c1500d403e0040040001c04914114103004001605075aa15803036080310300303104660003079114494000000800c100b00001c0c000c0e2120311410b90030455002e81d84802c0a24011071109902e02e0780d4510038000103611800040d014101c5d51500281800610f440d60f0703207001d52a030421505079400055005003000c520100756481a1031490380d14011440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 306558570 1250 306557320 306557327
    0x60306031203130c0b0a09050d0b0106031a040f14130b061905060a0908010e070f0504020912030c0102040519080d03050a0209030d0e0103140c04051011030a0e01120c 73
    0x2000180c0a501d04040045840d01d240500003101103504039440000060b00d0718600c01041e03100c0c958140101d40c1060f000102400c11464602200350055031320000c50380307050b40580161140d102030240c60b41300d16400a00c5a03035644125501c4000b02e4100044407141a0031a10712414042c20381505c48080d803440034001100440d545520075001d541c1c5144181c03100c0a0030900b005581c01c1180c1c0604041010004c40d50b11129090880c2d1426000344545a0080780d1a034841600340612003041c540204284407078146500244100040a0010440001800318507402c42e04000b04203100c50750005400c103c40d18141c02c600720480842426207039818500b5980a82e1221038103090b00903d5180c80c000786891180c1c1c0e040e94541d0704c1c0941520b2000340326034802442c0d4122010b240340800c0c03414840300054210300407103a20504028005a11745130924080005e020880100802004041140202c2ca4141132000d001d05400707030f44682a101074140b001400c0240e11919070000d051901286c103402c01d0b030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 306559820 1250 306558570 306558583
    0x106021b0a080a0222050403020d09240518060d0b03010b0a080303070309230d0f090803040b0d0908120601021203040f0b040c050a03110a050d05060106030510150f02010b06030603 79
    0x90407136069050222504c1c0200c44070070404002c014081c1b03030030100018184c000ca00303480c0b0304a59555880c40c858644041158003410145110116a4400c110031740640c00f580c02446200102094442c00403216800213003a80e000d403010034600750b201c131000c40b003608090003400510901111071035041810a500c0a0341c0e0702000306441c0803d511030744040306010101400c014802e071160701030f650512481840540e24042400e55400080114044080b00361003145608140d0700381e000958a0079250851103185c0c0c3d004604c440c50925565481c50000440820081040c810455005000b41c5400000641000c0701d01c3d85410f0007075410410000041c044110032103400e03910880060f869200c50800040c246219005180c221551480200c2844041301c100200180c045910784840781d01e03901805855001010014400c0e0710120040c001607001c1e410096110010450102d6560f079034040c2000c491104a18000c045180000c5c481030b1180d081c086c5c1d40320188191403040c0395040c540003003039413a070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 306561070 1250 306559820 306559823
    0xb040603061805071b08070204140f090601050604181401080a060e0307113102070b060a031208130204021207020d030e0d0c0f0b180f010507121a090106021b0a080a 72
    0x1a8545c0c05c07410402414207841a05030042c01c108a040540d98160550520035184a000d5084900024407402030011b9854142c0c0c401404075810545040c03046081c1c032521000141c1443e858100079001160f10b01c5c1030078000c1c01c2c600010034011085042000c2120812251481c0c140c2003009400c000c504196401000180300755180039010640f0041d0441e0942c50035510800b404500e8041c400309025a006410202c5c01420810340c01c0d180d40341000b000c1c0307645100003881d10f05a41d0184101d940140001a4003c5014401036441080c6600090880e44040c0c0c15414007660001480341e146e504100c00030643d01c10303007820001000e1140491395124a1204000c1c104100c4d190100100510154002c45065004058018034100300c4c801e0941c82012003c08842c5105808d00060810814000c1324042e69061302c0350a101511a10340e18041c0640c04022241d22f548810708014507211264014002c0030144d02030565940318082c030b03005031183d02060b14440c00d50210140101e9102051607818103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 306562320 1250 306561070 306561107
    0xa0905060c010e0a081305030102090d03030b0a18060e0702011a0f0d0b010f08120712030c05070f0b0f0106181811030903040501122903070b04060306180507 69
    0xc0c11840507180c09000e9080101ca500e010b4080004100301824001d0030300003410340d80c03c902494460302072600702d02518800c00d500c810700d100404086030080c0d100100c0a040600080101c0f51078883c0e07000a01121034003030b00c9003990762204201c0c2c2004800d0094114a50b4802031240c1001407034507100a40120081520418150314140200c0d518032540c00d50580d800454041d6075a9034040718001d00c0500d10070104103005a4400084000002048070844c1c0d60240c1c21124001280f2412002040d24226410600904011802c04116081d0076805064807400c0540c01d03514050499012000d410390010052100803000b9540d10107040d03001038261908c0d030100d10030b20380078814044c028280da8040f214040a0000c14460351160100040060361710a880d0304565502004081049400c007100ca60384200614002a103c4224a007801680d1031005084685140e110050903900d40d0050703001c0c01c0420340d959410402070b0030144010209912440b0200031526203280043c00041d41481c0c0d00811 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 306563570 1250 306562320 306562327
    0x42d06050a0b0d03020a0203010c020c0109150903142a062d0c0a05010b06040e0105060306030a0204060f050a0e0709060c0314030103030302090405090d2a02040c0509150a090506 78
    0x9601141d401991210402080998600800d0134040d48030015541c0aa0003542040c5030141074900004504c0c0160406a50342c00b402890b0a54071a2400d40782d0442c001000781448000001c00d04031030349002103d406c80e0161807400308090029607400311800c880d4003c114820029069552490f00b543d845109528080140711008595040380044040241c0f90390b140100790f1107a0401c0015101240d50f109200801456a46008028030b0b4000ca01c5012030070000c0e100103102ca03080c454003039600054081d04861020105500140030342b0f010740c06c100307000380c0c012204009134a070040074240281400e881548090400000062064a642c0229000d12000746100010180301c1c05521120403522800c030740d1603586031b01c3c0050195200041c1030b482541044049002c0500218810550b070f015a202e00c5140185045122040b031304000c3da501c10f0100d08804a00980c54a0180700340b45a030f541d8895966041000420402e08107500340305800e070105101104150ba0850425005d9902c01c0707581c59107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 306564820 1250 306563570 306563581
    0x60a020d06030b0f100602011811010513090507031a060d2a0201051005120604020906060702214308010e060723030f04020303160803042d0605 63
    0x1e019035a01c001c040011503410840482250460305003d0840d41071500e11940c2c0d1010704a00f6204280301c424030070114a10f91a0000f1041480d103040700c0b4060410340c2c18000c40c2040c00c031003c0d10356071203101c3d0283c56404000c2460307458880d920170710406080715040306070f090340031030302d0b0b0b00490030709440440d515004150445116403140e581c401d00702c0440006c00c4103224000380600710a645010025054000c003240500d441e2061a1000100200034101f17070740c1720740800c0b0342440c014002c140c1051003080b407000035032207104c0f0b5481001001c14548013110b550003203062414100305a8040e13600082600c0101070301c403104506c0c16004400c0d10031014251407045802d070014441d40404503d6281400d500010a004030700c0b0352141072140c03620300c01c0011840b60429081580e00900302c2d41e010030000515805d111014158010340085d0440741080303411001c0e082006030782c9006640c10f40f004020002003000f4102180f08400b600074a00312178403034856006030620a201001840700341c40308005075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 306566070 1250 306564820 306564847
    0xb040f0305070b090a260307120f02070515060604150f0203160614061909020711030105090604140106050a170f0d0c0501140c0405150d050a0f1a03060a02 68
    0x20400c0fa00b0095030f110a0610f070305040d50fa01a0b20000704c401e4441803103c0d841506800583c1280800143d603018556502c9500c200d071804240100ca0f818903581e940b004024020f02c0c4003600c3c0392881180200800d0316503000c070946104000b054144201800c0001740102c045810404c034001c0c800341010301400c14408000d07800d41c05036021560104441e500d01c2e106102c020f0b0008440c2035a40d1145181a441d0f0030180b00045030020040807840384284800c100d1000164014000b13140030310441d000e0a80c5440010b1f0039114251248002c6600c07100034041402410300c845d810805c080c0d0000c100311f07890180421501000c62251440320100c001c0141d48042c801d00c00001c5504441c01620710401e59020301a164547d201400d41d00e5610384540741144546e50210705000300c1c100f000c40d07402c3c180b0302801c1021801e552000d9280707120050004101c0c204282c001d647c092011031030f0108001200c0c840800c101c5031607100c440070a141d0599200040d40300411480d4202c103082001580d10340420f201c04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 306567320 1250 306566070 306566077
    0x15080a06110a050703110705090a0501051e0901140a0306020c0705120309030c1c0c0b04080d08040b0609100807121203050f0c0c070f090e070e010e07050715090317070c0b040f0305 79
    0x11a04112740401704000704804c0e80c41281170351000c88896550488050324504504040304030143c1000d1001d005000c1c1d4041f00d8803100d0042401030600031040c1e00c035617592041c0e0300401034900050b84951320a001d03500d411454074013410114402107040c40c07000700c0040da0380c025440d0124050545c21401c000f0b40e6000e407c8104846070018000d040a0740c1e1071810001c0c40d803061203140341c14028107481c0510340c0d00c1064514015031b0046400306490700e660003007060248000c1d203520346c0c4034101c04001446010074800324005104030071480112010f142460300f40090310320241010140740008120800c0341c190b00958018000801c2c0980341c0086038840391508100b900081c0802600100014201c100d0390000c1188044040a84003604e58030b050303680c08040c00380517a4034181c5508000070341c10307881400600030300342c043d041c0e04100d005d034080500e08464141d00b045d40010000d5518002101209500d0b90b04020585880b0101d500751340c98140030340d00041c3c0020140d18960300034000b8103110744283c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 306568570 1250 306567320 306567329
    0x60302090d05011a03010501050f03030f09011b0b01030c05090c0a080a0b030106092901020d0509031504051509070609170a020406062d0c140115080a06110a0507031107 74
    0x2088140783d410b139a00e403404051803515100750f09000c00800c003401c0802e440c00404602400850030103080140d044201c3d04110302c168100300e8a000c0404509403901d000154040c02803000b030ba0654150b04140c821a1125040715001d00711410600040c85d89d4007003200c80f9a120783c640700a00c0d445151004003e49401051142d25609000c03020481c454203a01c1b40e00c030303a4000510380885c45091908900009814502d441c0540c10070b4602da00b4160045e00100326410004080d684041c502c141c60700700020f0141e405803042d900c50082a10100200200d4a400894803002000500d1070314100800c0003115004a00301024921030200403500d04220101c0b9403030b0300910911026403140c000030072903640c00c41d20b071818201d41c40712852400711501e40c1c2030f01d14407140d8807171100f0506074440c01050010300601006a40d610f042d900c6000d50400d1400000e800b40350302030040810741d410030100359490a03403480e6010a08000012000d41c11508842c912607260a044441920800d0001c1c10042c46500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 306569820 1250 306568570 306568573
    0xc0204050c09041a011407060f06060804020f09041205070507150806100e150708090a091506090b1b1002040b04232b140609060106020a050601060302090d05 69
    0x40c031164020301c0c40a024104030543d800c100c4640144141d4442e04002c100341303400700e20f9002c9513140300c01c8050020203480e4020369010820118681600086840d280d20503000a203140040c00114a403114101074040c10807104038820341400e0300d54102034a2502c1030703103040c04800a658010440c1c00c0c0402c40c01071410825007181d01c0050003000e40504401c43d90a84070780a00c07413003005003500600c0b01e800380100c09841a41daa44e0041c0c04901150710094056602c484140044c460b15515407003410054019103002151251f03140d07190104a100c1c40c0c00000a10102c05003d0000c00707681c3c000e40d680111020b02d04c508510407030300f00c1400c0901910344000c1c11030000501052030321081005000301c0351100780c40000d9042011041600ca41481e40c0756030710810f0301c201d0b140300d0f41c1400036000d0b6110442160149004803580c440c10090303901a1082e01a42240d4108030300090140300c0c0c40d0040400d40050905000103a403a541c95081c140190400c0c5036020032842400e4440041e4020800c0d8042c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 306571070 1250 306569820 306569831
    0x90b010e1f230118330f0e120c091509130c0b0903030307140c0118020a08010507120c02070b03040f0b06010e0d0204021608031e090303060105190c0204 67
    0x1194000610b003000711118494840e0002c2d030741d1075120340d00782985124865258100c8900f02005c440c01c121744000d11110b0302c80064002100031100c510f00040d010036076101c48155506020015004410040f90244a204602e072095664000421103246002c0c01b22603840c4251381d82502c010280f4060116240c00070951820420840b510b072000061044c018450758016680d5080e291402d4410102c480b038140c0c0080c404180058025006490082c00300c00b4150306015101141034211248482c10091300301c400902001541000e05c5800c001d070051800900c0b4030324103298007420301140c0800a844441d0341da041c03885a1391092141001030640004410795900f1303c1c0c205a055916283c00940d50041a403020913103941c02424a07918142e0081e0001031416610780030440290003215030460724454001c80000000c20000041d48078440c100a40141103036186e0142e0940d860040c048140d59008005005c020780e0000192611051924070340150801c0c1860102c0d000368404030025003240c10035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 306572320 1250 306571070 306571079
    0x2101e02030c120921070201030e010f0603110f06040b130302090703050601020606040506130903090803040902130e06010e090c091305090f06010f0b0307021e0a1104090b010e1f 78
    0x208020500d18440360780c0010180c0381d9000954039000c1c024455517403502e0141c1c0404280c01e44602078035440d40141000101340d401c0521290030345008041d80b1940c00d070749203014000c2099048da01c4400040c00c0d181d020340302618602042051203140100e034040742d800f1403115444860342000101565024000340c1207420140f034041d015100650302da41c00b500034903000842c503040c04e10590748030300d4001b40702c0c4c644848c0011700c0400816a42c0310039010400803507004a0301d82005c05c000c00c000e014440006a4402074111014110721240d0000403603c0f000b4002e00c1341580e809400300c4100c0c0801c8600c1c03070441d11b401d0701c200200d2080c80070554101c40c01580c050309541860b44070318031511101081d5070f000a1340d8100d071501c840c024001e08240c90344880c000c2c81410703180d40280d5488400781c012206e0703207815142200d8002c8140c16000d03507160b125204035810860582028094554165400d1000070032654826100c2d00c014040e41c01e51500707500015038900030f00c0c1568001c00305030003020941180c41c3c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 306573570 1250 306572320 306572341
    0x21207090b011b110906010908060103080306010206090706090b1c0f060503071a0316260106140403050c0d0c12050102090a050102030c1c0905060a05030a060f0602101e0203 76
    0x39180010b010071031003035419a015019001110300c05034401458040c542c40d01c401c019404030064007890400042c4c5801080a040400070240038601401c10f1548a2a080000a2800000503c16100c0c7d8106250412000f41c206030084d043d200000300181d202c2040305035490203240baa8004404a605103038030200c1365240f82c0d2110081d030300306030243e5019030f8031507642058080c08046a038880042c1000015503200d50101c405081d40614074054030864082c1d2482c8215010461a070f0040c040c0404c0100100c45e004521001d9a00f03600f550541810302d0b603221507440c0c07a0a100c880e4000c2154018820801074841003107000740121000c600c510304c01c0b0b401c1180c001c0d0000b0921a010b05841000441c9960000003642c0c0c00707948000042055144614441200d030320b04d44220010f00c80140004141c80e82c980b009401ca0080c03e9a0b059140e1402c0c20b10941541d40d542c2c0f02170181c100701003080c0610359000c1101034180d01101e40114040440aa45241d1070724001030514141d407000c024090180903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 306574820 1250 306573570 306573581
    0xa0809270a0e0d0903020409080f1b01050601092402100612050f0313051e040c03050a0c0e011e0c06060305010501150e030d0311090409060501080d030911040902120709 74
    0x119100400602d5140c02e4060360340d500072030f240da0201d0000c100c1040140f8242e0440c8005512401403141491000985003040707070030812484014210041c0c903c00c0200003445102e90004091030100c49040c90040114011041c100c2c0c1403048054104400580e98000c00400c400383d403000e48108180e643d1501142071030800c29404442500034401d408a500c0310002c03d031240c0d0021001c088007107a1031700082010b49800c07102400c010f0141c20201122640c0e0ba48200c40d060949a00c0105051401203072441c03c42c1c41400ea24410308c400601013401030790340080a1610303c50a601c600b41c000c05002d40c00d4450350b0010304010519170074060003104204041d04113904961090301c0764111030004410a6400f811411030b03190705640a0203640f0491071298014407212030308900c0d11032074100303000041070560b4002c9800355609a12000104a600f600b0420340c1c41052041c07504004000190755410b02840440711498492501da8400ea4155515104c40212140c1c600046504103541c40305814054407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 306576070 1250 306574820 306574831
    0xf0610060908030414030f010f0609050604022a070e090f060117100504020a0b220602011401050405060307120606080c0105040b120403110d0e030d0e030a080927 71
    0x50880000120240110408001d68030501c010f0342c20030382040b1304110000d65450585a0503c11070304038591580003881a0340306124000b00105c0c0403820180c4081c140d42c00500000d028900c100402d0000b520f203020680980f035410400140050060740e121850070640d40c1210024000110901031462400510040d02c61300c40c42c02d40e0003580ea81c2d980c8611a110884096a6a070000d40b10080c580307103250300c4a5802480144008041500c48050014541084510800c0f0b10f2110611960000c1002c82400003440780f032000703100d09480c5004010348003d06100c3c06024544072804140156810b0006501034040c618400c10205e58600b02000506114840c003022030040a1a540165200d40110390695a241d84400e1810742c00e00e01328020703d03000400940401c001c4695100007060280b28465004030640d03504680040004101420300ca80007a421040c04905440350025803000308460700f0040d00640300c0b50b2506c0c4a9030110f0300c0d9940c9049100300d4800c4881c0f82200d003220030351440d805071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 306577320 1250 306576070 306576091
    0x1513060e04020315090a03080408120117070e1e0901090f03020d0e06040e22020a090c09050f0f1e100f020606010c03140702152b02070c03020d03110f06 67
    0x5201c135003290310f01a0040c1c514002035041946140d005c240103264441c1c01600c204003561600a083c400c2000c0c0e01000c0c0c01504440e804031180b5000c6407010000080600308135036030b00c0c8680c1400500341d590610000c88211390031410798009a030b81c034000e510483d210303908415501d0042c015450300948036228410742c0c0d40812400c0c40e0b00d0809d410800d042c1c500f0780d421f001c00019161501c00350407003004054004004812a914544030050301c406507264014000c54101245100c4407481c040d007094000d0f040719005011200105c1d10301e50704c00c1c80c480f442010540709100e5013207003004101040300001c41d050350406840d05a070459640c4c002211008400c543c1d00b035547d1600e0f003034011141c8030000707000070300060917200748061044129402040c10910003051701e041c401d014601040103030001125140c0134044003420004000b195541d881c810060241c04514282c01030340c0e8030210250f54040640100389100c201d01c1014000d05c41452002c46800440e941900c1381180260340700030071100606003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 306578570 1250 306577320 306577333
    0xc03020f0d050405090108030406080a0b030c0a030302031803011a06070305040914040c050d03230d0518011d03040306050606040b070b16030903090b2b02180114031513060e040203 79
    0xc21f00048250303429101282e60f60302198403610b402d18040d01401131060703490300881942d01c0d566a0ba001d000c0f801103129401564460021150360500321074001c11840c000d13414004900c0f24030341c3d508041d40c00c21408440031a11000581070480f03050045d6084400150701d040d08440a003480074444038801e502c2442c01007446900da00030722540c1546001c0c020b010501d03106000d19440c0301103c1000300250140c1d000d5050000c04004034069482c1500c1400b02203000007400d00840001b8042c00082c10b5011030540c4409100180c13181c3da83c441e91001400155840b40401e030aa916001250010b0000f00c0c2c030507031500c4190400700d0024805540b12100300c140f08850203005c038040d01480b2095601030300c0b0899020b140c04002d00044d0300c051484940c0c4403048451902c0c0c48180070350344c160703007400d50740c01a1a82106403020101088081145041c4030b8620080e0031103004207005c0f02e6001d00c09101c0c60740d0034020740010079030410459003040015420018003040b201200794580740301303500031403c6845 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 306579820 1250 306578570 306578579
    0x1c020f030c010b101704060e030c030f040305061501020a1101020c10020c0109050108010f0e091e07080d051c240618050d03080f07050702191e0f05010c03020f0d0504050901 76
    0xb81d010108000c0b2220645d00c0300041c0200d006640600d80c40c0c0303841d400703032841c180e81e0b650410701750f511080c803d0800c0d1501160070300601030204601c96109401c681121100c03003040d40040c0d81e41e0140c0c10010b08040030307400000102c0c0d10030f202c061880301010b00310186006001002070f440e40101381c1c1490010304a1200092607600c2000250f040b1480c640446120381d003480900017034000700502e00842403107050103980043c00021800708000300820050520142000c80c52400e081c1101054002c0100500018020301e41d4900c08109040c0202da0010f0541c01041c0b01c0d00302c2d01000300c0d02600804440c100091015042400052410914510703002110345032002c0044d040400000038002420050014002c80f005e2000241c0201250501c03e081c0340440d800503800da4a42c40400d0241200440b08114410072b9040c0d2003238650500c402411240e08001000d100942244a000d0420400d40307038080501d80280300c0c1050307500e50387c01038500044c100c82002d40b4a5105102c6e560161501e0800043e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 306581070 1250 306579820 306579827
    0xa18030c051510050111031201031b0902030f013003080109180f1b0905010603020a030c0824041410170721060b12060405011d1c020f030c010b10 64
    0x10303c60152215407100c964141801120701030300b003100c00da11b42d2008002c0b4000843c26a01c031240210700c900c1107001802615503090920f581b0030344c0301440590050060184803000c3c0f1130054191004030070640e00c8103400c2c011000000ca4840502050742254421600c145640700442c2816502406028000074606050790b141a140300803005e4071520110704440001032030000c2422104482040002419403204041170841d24203a1000011950004000108927003600a59000c0c08081c00c10f08460b00d0b0414449032020340b04422140003261190000c0c500399103a5004010742404080c1169403480c009078808181c0e4070b1b50090b8241d2204200c4000f81007000003036000e050321074400b214045041d0880c0d03103262618540e402150740541b01e90811100303032610588804c03000880c2c0c00400c494202810550b0860304058140d10301e0450b5240c01e0b41d12150005000082c070b100c0380c44004007114810320200e05160540c07646440f50f01001400d800340d06d0054000d03c201c01d400302c861920924043c00182d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 306582320 1250 306581070 306581113
    0x3020601150c120513060504050a0e090a020d1704091d0307120c03090902070b3301270b1b03040e04061503061508060a09020105120a18030c05 63
    0x10001d0790042c089070000e412404441c9452081c1d0030300508102045042c000c0d4003103150446070020340c01140400c42c0345000c0172031200915210040c1185070034031340102601c405600720080d0290b104061880100900750781001500401c1c2c0e11115100c54940b412840500501101c0300000005800204103a24000c0f00b214091980800301403041c2e0348410064648250303482c41a424414020780025107a00c40d40002d24880740303d1154580c0303514265440250220305034800c0480030710b01d600d0310700d0001407008011038003d000f400d0030041d50817140c1d0294036241c03400241c0000d642d0410400030380f01e18040007426405011101030300890400703100141c0ea0b07000d6031041d128030b1400a400b141c04620300c0e0f031180c904180a603188810507502c9031180b1081d590140661040358104200821410390705008250b0400c2828105100c0e984031a00020420301404240b0220445004041000a05240d11110710920292141c21a41009090141050402c424203a4103801208410307801700e103001404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 306583570 1250 306582320 306582359
    0x1b0c1707062006040b04050a050709050106110d09120c090e03040815090c010f02012a020f031303061104171005162102040503060a0603020f010503040b2406030f0403020601 76
    0x4000580d00c541700e4500400001e48191958040d859100b80030401c2800034a01800648002040700d500d010340041c00000c034441c1e98082a04120b04030070b00e1030350280f00201141c4500100180d0760345a4144a11480c3c41540450551450310466280411000c0061b2046840d000d054460a903030440070745260a000701d0b82c4002641201c9400c1050350b0003101c6035011403403644000036134a842240c1c1d5801c14080891240c007030161700c40e03500401e5941000000c0c02110550055401e0003841d00703442114034900c1c040182242c2c0c49404a2001c410585d050320004c149408500070006042036030981c55460040c5689980c2c0d0400b0002030000001002c0c3d16441002e030754a0082c0040030040100442c92401540340382c05400f0440050300780d4042100d903005000c0303905d001400d00c0c03031841040022882c048445051080c14020030002c00c40030110a50300140d0404200410103080c08554402c10380d1040c290360000011080c0441d001e4840c8402c1d20640c880c0e0212407059813241c4c404c01050072403005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 306584820 1250 306583570 306583573
    0x30b01060c0b0a110f16020307060c0c0b09011103030a091e0308040f0c0f1404050108062e03120305060405151513030c170c0105030402011b0c17070620 67
    0x400c911040c82c0d0700c40f02105500c01e400380c0c10144c60140c0745d070590740030284a5070386c0403c2d1042d0805500c1c0500504008001c2c6041040d0005000e51343d07044040820b01c00c0c05000765000c41c500b0b105074042c445801580070325006a982e203260081074900203010b200406d60340c07015801450003000d089800c4c00242503815494100403540c550b641d03106803910a0344c040300d42c0180d0700c01c0050b503940501c079200080c144051840c20743c130001c8000e100865005030f0014031a540f0010510036490010716803500b501c540c16651114080300c58266800d003d00d50391009144c0c040340d50407025190b030b050b80b045020b210112403d0003162250b01124030142829031000d9804075640b6000050381207800000c00c601c1216880c0743d040c030341ea00e484410384045290702003600039104a554035031120060044840d00c070803d0070103606504142d00024074140e0500d016455040302c00d040003040c8051100013070000c0200c20112981d8103069800103031542610f104000c049412a4a4000504850740b01c0b00c9100180380c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 306586070 1250 306584820 306584843
    0x628120c0e0105010309200d05030d0c02060906101206060b040f080f0a050d050715090302010507021c0e06030a0b030a051c020601031e1e0602040e0603060603060439030b01060c 78
    0x1e05ca0340c2c05209448030240c8c01b00d02806100006141800034040900c2034120001d10318450810203414801b005151041d550800b1080200e80000112038070203880890310484104240c82c90701800421482d0040c909162001c6030001d251146140140142c0c0c550070240d80d20300d0140081195101c00d20038001b803c5801c41c84904c0442c0b8443c5d000f6210050140300003e200040641021084811500c81500140d460f4010000600c1c1c040040340254551003408803800042d003000205000a0700032454818040080440c80280142e04203010f180401800da503000e8246140c915550b040b272200008019818400d24102c042c0007040c81d41c100c0c0d8000e0304047c81a1802c10f032082c0e20843e1004101e81d801c110800d8000010030804505a9240c0704540041e95141007044500340090000d0a030762103648031000300f01503501d01103002074000398800000c1003400211404c4441c109108001c0c0000058004440c1c1c10880740c5910140450b07001d03030307a028003070307600c03010116600321103000058095805070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 306587320 1250 306586070 306586103
    0x120106150905180f07020a20090c070305030c07032006070801090b011b0c0305030406092313050405070b2802060402060712050f0c010b0310050628120c0e0105010309 73
    0x100130a50003429032065500c4441039a403a601340340e0801c040000b180c000801c036140c46080c01c50b00341382c02007801a1114100b03111660000e210b03100007000b4403500c2c603010407880201b43c0a000c488040e049a41c001210011642c04210783e5404122031200005660200010302d0b080b503442070079040c4806a50702076200005884081c0c0140b40d5603000c50318503264500000101d02c0074800343c07004d4400ea5070346009151400031a401e9900800400400054403110468403550740c030710030300b09070040312030002c142655076041543c00c0c0349803503100c500d00c00c4000520350016004902c80011034070080443c0b0f1003070900c8410484c1d48000844000303402500400040700441d5503010010500c2c0180d1418034509582d94408141d5070704000f9400105030345800c020b100e01d107828001c41403400401d081c00c110500d0100c000070407400c000105e0254110005a601c202103004c0940400540351442c0080c01580052420b1980518940300705002c2100b0303e0700201b45d0358428028507400c1c03038104020340d4449814 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 306588570 1250 306587320 306587341
    0xe070302010c051029030111070605100b03011e08010606020c0d080c1621020a050609010e1002060f130b040b13050d02241e0612010615090518 63
    0x60400343c070584100c42d0044d0404103540035141c01c00e4082c00c5505880c1c01d4441c403081e4001c5564034914881e07410000307042210354100c415207100a03045032010441e9290300d0003241c040314241c0c0080600740000800403468903655140d000144041011212820b60740700002030890b4101d0092000503009002c0c03a101e1440e020041031180d5001c2d0081d686800c40c514186803900385086102c0c04101d03c20842040700c2d10804d02e015060810141c0390450482880d400919904c00d00d01480b88503030030100b1894180d901c1624043c80b01300018081c03821259001c04080c0d40c03081c0440340180724100a0b000101070f8441e02c0301c1d420a0035400b00303100302d1036100c50392004400200105100122001100d1080110b00108500100c10300d140e000341c4008031042241109004003101c030180304803641c05c207002030918080c000c40c003940300840e140031281e00cad4000010380e00c40041c0208401507081c00c1020805184407030b0000d1580455446132456180c4ea0010312030b45040017071480d001e95110703100248030200b8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 306589820 1250 306588570 306588587
    0x9120f07060501031b0e0c0a0f170f071e080c0a0c0c0e060a05032e230411010e0312030a02130b041d1302011d060d02130512030a14041805040203010b01030e07030201 73
    0x141c0b8282001c03a070182b000e60b072074a200120b170081d00001198062004040d0000e80b1103c414a0499908002403030b5050003409030b80c409031005484190000d60001c0d0944a4448002102d600c000020245c5640b1603030f80d030003140c0039568130740700f07034175202e000901407400040c1048000d0044d103500001c02002860703009864400320b20031000c00c1e2510300c540100e03014150030402c2d0240140c1c560401c1d090034103111000c2d081c1d1280c05070510420a580814654002070b014003401da407107529a030b803541e511101401a020380b607a9460f480030300070000301e00b000482020707000b82c859607002c1c044010419045107030807034401d072552180140d11101030000b65120300305004000080301d01704a048079424001c00c40d6035010011494030568040303004c42000c0c001d51040303c0106021a0b010f05009801c12a4135100c6c8100c040707070401c0c017107003120003421015614183c0b0300900e940710f1086010209a94150046e00e03044a08034481d500c2c241d0300106075801780c0301303c1428411540080c040c0c207056a006450010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 306591070 1250 306589820 306589847
    0x206040b04150203010e1f0812180312180409111c08030a1d0d0f18050411031f0e070e060f070f0201020f0609120f07060501031b0e0c0a 60
    0xc2d104085464100c00c900046000f000c49a05000c01841d00705451a41c1164922148508401d4a4820071901e0000180105103501c8525940c0d038403488200740034010803c0004a58250046415a142c2d8010250140c5407084440c050042c0c1e01b03080360200700803226242c800420084c0d400300c0c403002c2414400d4080c0d040c21503590078500140c1c243c2c1c8420030650021685041c1690321842c0307022800b80b80c2000354120300c14020040403034064a00b8054150080384110004002c0311b902c6003502072a121300e00c40d00419000c1c000700141c0302d81c00000155a4000c035400e0910440042c1c203040e442030440710400450315416080001c50301c40318400c5a0781820340240c1540b28005000f030b020100317005401484103601c1403440c02c02005071031002906080303058800e020242c01420400c01e0380b000100301603072082581c10300ca5036180d60048425002c2e0140500203048949040000320400803903004511b0801e80d220600d140d1603035034040040c40a2402c454490720030704140140305400d4040c600c000c9105 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 306592320 1250 306591070 306591083
    0x1150302090f1908010c02030c0c0d0c1706010f05030c0a0e0603010f0501080106060225031b1d09060c160b1312030b040c1b11040e120711060301060206040b04 70
    0x60042d00180c000404500c0d0040ca18000000c00c1081c2030007403040072070f0807110340081c509000c2220f480316207442824074500c2c00340c48403c110b2001c100310764910340e0192034443d0308003143d05c02111445903901c00034010714401840112021889103400101d400c6030782c0006040d0131903a420402c18244804026107102d80540d01c492078031040e400c0d071740102030280c07a414000041c01d80c54403e00914050290105a00a502440c2c072080c0b000d80c81c0141e4020340c9c3d008900f415000c0000d201080d9094080e500061082ea0080344101d12000a03204140c040d0301111b08443c9152107808800b4003034400e04183c00461404080d007080000d810048580d440f01c1c0c8040902d510240d5512005800e030314168004c4002540c132641e40301035241500c942e8019005a103411000003500b2031641120445240002c2c11645010700c0301c9100d680c03250400c020b01803540c02943d14108404101e640e60383c003d1b0b602207a0134034000034030890078140001070324100c41c0c0700d600400c05903d07643c071115a803400180064480 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 306593570 1250 306592320 306592339
    0xd06020c0a030c02090106080717060604120609020102060c030c07170403061104030501050c090d03030e011b0e1503090705060706020c1204061211040b09031606020a030f02060115030209 82
    0x1060240855076415000303480322006021144104280610160051030600900c407003800b24480d8840d40a81080100d030301c9090782a100c1800041d080d0044e41c2c0006c61850728204a281017018603007011052038400e0302214000d4960107084080e80c0421244991030010501a100219581440380500c3c02940d00700c10340303800d440c0e440b0350f403c3d5428646124040140080c041040145c24454135034001e00c80c244542c1030981000000b036015840080107810540c581030080700d42c171400c0d0b02c070580702c4a0f03969001c0c038a2510f200c00a03000e800d030117890394840c0880120411003030b09000c00b22485525020b005d01304141c1404200a0540c00101c000d80c0d803150300744001511a10104002015007a1a07201035855030700d0150002c01803078106480014081c03c2c42003210700c50807a8025541520901c00100b615440c1c0303840802d02d000320480a082000c840c10303e0000c2d899401190150300e16019030340340c00240c003104074180e80d1504284541d8284070f0700c05640c015114800e5026102051008220760007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 306594820 1250 306593570 306593587
    0x73c0b190b0a06031e0603030c080703121d0c040509030d091b0b09040509010209131e060b0a140c070b0a050c010203190e010c020a0b0a0b06070f020a061403060d0602 73
    0x101ea40d0160081d8001c030781c1e20607640c44000003120368120741928464060108901f141c1d8001c01020b226030004240c0b0001107851001c050103000f000780d0780101b0034420401c9144c020020206805d410560380c2c024040c0c0080c1519034105401100d1280f4a040019458000b154842c1001043d0f864010fa40c940c18a000084c1141d5524403410014681d280304a502c4411020420007207a82c040c0c148280c0780c2c410441c00c282e64803114107100791100c803180001030740240f88e4030009240300702c0781241075801d00e88100890007000c95005014500c0440c3d42d25000141c150030782c04040d104140e080c040907808408100640310744000108640750980c6455400c000c8021142c80c03c1e6042030701e030902e0f6580002d204007209030103407107002a4024034500920a004c43c4450194590040500c050b000300c54180000302c0c0b0f010150460702140d000a0201652484e20b42858020142811412440b4052841001074000e11483c40603803940344914002d440c0d5100ca01c1003042d5040b0400045900c0e54090081b0368 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 306596070 1250 306594820 306594829
    0x3010615050301050415030327080d020106030516080709091b15181508060301060e010806100e010b040e090f0d02030403022e050f073c0b190b 63
    0x20140c40d01515460740329410030f8100b0060f201e071401d01310211358a1010400c0441c1c2d01180458008100c5541a9612002278207242099401c0307801143d80c41c403600310303c40d801541c154420001c4074064425a01c102da841300c1a404040c1e528401c907101c691010f00c05201d800d5447e03002490a41c82070240c00e628a80c0908400000b41543e40242c94a42440696a040d90f401010072001c846150a084c107125041407040e91114007030064070f0080100d00340c00994070b51000d60114001d8a840364429001f980e650080030342d9140201c60741460051030040c00124074400002c402d050310307a0100c000c1d00301030411000100e1034100404242461041280e1001c0c0c4900a0214050123040e03a1b02035503440c0d05500500400140030035100b1000082d00c01842c0700701c00c440c0c030b00004446051800e1030f6205c51450091101d801446000390041b624400c0c0708049229010b11a800440c00160104100282040c601200c5841400242401030300303200045040c111905007103d40e0b4010341c00010380495010104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 306597320 1250 306596070 306596099
    0x91701140c03092b0e060409020d0615020706020d080a0209100818031216021c030c090504050610030b120f0a02040615020d050a0e0405071d0409030507080702030106 73
    0x109494040002800040001408400e00313070340b041c0614a540112020882c800c2d0300c000b250150030060a402c826055588581c100d07001071059800239500e4000000c0d0f000002c00441c403540b00ca1500034845090881c3c004203018003219400d4000d8003061060960950b1801c2e8000e00403031a8940c00c203c9500a541c841c9080302018541d9594607070540ba00c01c0c0c1e5031303100000781441800a40e1041c46120a20104502c2c110f51140c004507000408080ca20000c0c4c0c909094044031140c1580f01801c4000305075416404085c5201d410795030940310541c0d90081c041220000c0c4c0340309401c42d61040d40341aa25010750890050301030094440c00208048070b2003141009030041c000c0c00260400ca03051425403030075014001c0a0001c0e100e03901e0070b4400d2100081d559402068000041c0100840c00882190040c050703c00c56084c00761060206240803000108078508070300f12071114041000e00140c1c80d0030244254400180e2589a89291038468ac82c1e07080700785c00c850003c90740342d9203230031000c6044d95441605 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 306598570 1250 306597320 306597331
    0xf0e060406051809010c0e1c031701060f090902030415090c0803121b03160c0305040504091506060e13021803010207150b040c0522081e0105060301020a09170114 71
    0x30102c2e070b040084c0340c607003901c90003010401044440c51400d9180c0e5211550303201440441d007102441c0d08413520701940ca00b0045c000341d640b0070321402c00004615801400c02e092440190352040a40e5849440c2ca504034002039501414021100e002d410990300740f50705c40701d4854002e01d04000341a0303444007801d2855001680b00c8000404490030322402101c0f00110030b0f4180c0e01e01145908503e0070010047d12000841c8107141040f0100003070005141c0141c08a4000c2c000c05041480102002e04000e020103121810706a229881c0c1100000c80c2c07032040b0403280043c0002020391411086020703229000e0342200e13110f00c1c280042c228840036540e50034401001154803503052180300300540f101704411039892840503401141000e0780e42d20400e41c010119041200d03826814517140d6082c401805008681f90407001d118030403026030200501c00007040e010740d140c400e0001d02c0203035614002c2c1400c0c5d0007801b61910116849020500426120590170041c4e04c00d2136000048040c81c003c14200b2620050340d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 306599820 1250 306598570 306598609
    0x120607091404020a050306060f0d060b040e09060f01050607050312010801050115050f0322020409051b01110705120316030c0213140115030906090c0e100f0e06040605 73
    0x10001e041c51070128540c1140210b0702141451080784c030180003480010459071040304001081c00c0345920b01e0302990a20780780d9183c20403071240c0700c03188001d8950040c0241d20550880301c001034658400010702034440c0261f840c1c0040e241c0d10b4a024070104d900304075000c58286c00280040340d00001d50300c5449001b03205020001c1130ba54500088401d0803c0c0f01c403507001c10003a042100c01d581403505400c032a009880000c2184055a00e0182101c1c1c41c07104c0d00d0300940c4a810075510741c046c40b10000b0450240d42c01a184c11042052400042d1500c8000303510400b00703900400001c0143d442c15003410f1440c68032071070a42c0c2c945000c0000040c1001660741040b8045840c1071065030950504550042000c2e1001908001e048508030403100341c0d03101441915400c1c58000000c0a40314400c2d0002c00c440d51303101505100000035440d14002580203401408440314145002a00464404100e181111514041c820019040c48000a0541c1d4001c01023508261900000251074075400c1b10003804070000c0f907 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 306601070 1250 306599820 306599837
    0x13060b21160503072403021902060103030305010f180c0c050607050a030c1b141c0c2105031503070f030f03030507090f0b030a18050604061b1706120607 67
    0x11201c6030707100190402c40c000d40c00054280000c4030b4448880308050135042c1c0890340c0311072200f0114080d02c2080c0c00b2000241140d85400d202540004145050324403e4130305202980c1ca0f44020126855284509a0010b20380c070b40c491169006907019a03008080c44c504001d182044d61039803460203505132480030024000180b0110b80071350510170760b500c0304001e141a034108000141c004d41000048103018000c002c0724103003106006810012400788641c07040c4600100307800350070050204a40501d05a46a800242c0b210303ca09481600360901c80c1e1507a2115070440d111298541031002c421100030303406101c0c066000c01c0d240c0345256408011841070309400701d064030700e04d40142550b0000d800c8000740041c2c0b035020701110000407100e906491442207a15200d40c2d8183d1040c0c09444c2c030310f085040e0403401d91141810310001180d55840765004d200c0c103118401c0d190b09a04c500700c01010201c800145480c415501c00d607074481c2c10075000070300200072403ca5204e54a040f810729106540d14400300d203444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 306602320 1250 306601070 306601093
    0x5040806060901060c0311070e0907080111030f01180b040f0c030c1103040b0a05040b0304050a02011e0905060d09020907050c0d0e06030708100807090204030209010e13060b21 77
    0x801516900c0070094846161a501d000000392004444000c000c05126513602d481000b08400c010000003460002d400d00320608061019580340c0c1014040c3c040c0710350808241000701080681103a00070740c0340310b00c00701d8660b203845042c4110300031503031032642c0d1152280440c0c0500d948900411a580a01c3d110014042d84020406812501e60848000501501560944420501100791802c407506164816680c1c241c40d101114039109a411401c2204408400d20090200000b209030310f144c401e07264200c480e81300030501c00c0e0907082c0103038010000302404070910440c14000082c2c040d49500880104001040c1e50008504c40ca044071403600007800030403201d011031000c001d10106c2c82007070f04040c00c0c42c0700d43d80045491403100034403080900800c0404281082120740e83d1400610711a002c1d1008035483c0d0080c2c0300030390b21520080c1c3c451181030340003284102c040c00466014160f9407407040a00c6207181d84940261100303c1c080c41d0f1120b007401046d10001c03400112003010103120b074040c02c010ba00c0ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 306603570 1250 306602320 306602323
    0x1b0f0109050706031a03100b0d1a060a080303013005030d050a051006020604080a1e0c03030b090603030d090213061d0a09020109031113060611060a0e0a0609080702030a03050408 78
    0x4d40c040185c0712840e0741c4400070301d44002c20645825078140c1c0d0041103030800d220104102662800000f030480060b80d826914041d080d201e540c5c080e0400700c41c0c84101079a144e07282580c9000038000d030030300981103426490a46052801001190000c00e94503051092141c4549045411502c0c50b01c0c240b176224020003000700590320640780e0040c030411440401c9820498001d42d07030480100010403d240c002062200b85001d2101c611607046144111a0380048a030030007051400003400442c0400d08044181c41c483c034010103c584600030180065080072000070004002e0400c1c0b00060380c04c542c88400600301032056010f058041e019000d49401000d50407407122844e88001020126103d1402c146580140c1e48201160112900000ca000e06802501c000400107414120681ca03094a05840020029080701c4074808109410301503841d550b075154038410555500c138900f5200c0e50400c45040000440950014101500441040d420b010b0503502003480d140c500201580802c0c004101048000c20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 306604820 1250 306603570 306603581
    0x70e1512160206010b0901030e01060b1606140f04120e15070201020601050a36181407061e030603020a080106030209010b0f07080309010f090c1502030f1b0f010905070603 75
    0x740c0e44024401585041c0c1d1064480c004c1201780303070405841c0d241c14160000b00f5003284000d00154040140d41b04400e6404203803024600b98215486030911400b407a01c81d410358025407080c528000c2d444403e540da980c42c241c080300003020311030a1040c00400036881c0d0307e640b01f0441c0804018040c0d1a9030304818000a413801005912191188520b0300007030181e4546821b980954140c4000024803c01c0200300c00ba1428040702d10103441d841c0b070651320158074a100c41c0e030011224094011012030002003003101e52a110280541c00114a0400c1c1002030326120f2240b04036030404034500050074580781c0d4000703000c2c00c000c4d80c801c2030300e40e4542070b040c0154581010f8184c01405140345d41d52a007001c141c00210540144c4001405450000c800505110002c1d00100c0754000e0038002004550124680b00c00c1181142c0220810105d44007201c80c00c03d8000012200951a44007000f41081241c003020300c24941202c0b1801c0e040d0203098020500c03c5400d000b0034a08902c6000a08869414014010120381 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 306606070 1250 306604820 306604861
    0x10110a050609100e0a060902010504030f060519090530030109050709061e0507060902210105060d030e0409140303010306020306130c12050a060f140f1008070e1512 72
    0x1813418005138002d00340011009100b551290000c50a04c06a000685490041c2c2c0c0c0b0203050002020100d5003040102d60203d440303a44600c41b811690124103444404882c00c40c41c0040155003c003403101420621001c1d0442d8a20f040c00019038101c1030140000ac2ca07400c2070780030140041e2114288482e06401c440d082c806000b461501035100051a06039101005580c90044103000c800520f0b50184061600308016458020740541e09070ba04a400420346500c1001c01d0240552805000c11030354940302005d22002c0340c241d138030700c1c421a1074042048000d045404046440c610340d8a15202045410f00265000718000e460060b01c80c980142401444005aa99954524603000c0342e0300f6440e400810106000c0003402c0005081c2d519041030700000c05160700326180d40f040307084000420b20b068403103881c1c482c00c058401512001a810500940107807098140d0041080d00d00050403051098030004c044e298020a000742c0300780000340c40c0d40f103940410050b1007022700c010100320301ca940800321181c90070f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 306607320 1250 306606070 306606103
    0x140405210405031b0301201204110d030203070204050c090109030b09011d0d090510050d05100503032b090c1a070b0a090b1e0129030115110c01050910110a050609 71
    0x240081c045040481c440c0c150240d02000751240441e0501500501c80113022b107014152200c4a12241006940da40103000101d110b242407a0009803061000020303620140c0041e119605007600395560800000801840e1621966030303903451010b403800c1c0b0890700700400e07850005005144010b12001f4240c0c2c8d01a001140510707a00031680001c9684a01124000b0700341040015143e118071100c000300c03130080e81c0119407610000c1021b0505903c802d00c3d90380c05c0407160421400103003071000c01c401910160319014bc00394035030a000700411160400d01d10805e05021000341c1c40d00d9a035a803803440300032098410002141d43d901c080810400c0c54a401e41d0082110303841132039107600c0881600030b0900140501000410000c98070782c41002c5400a6a030b511000b0a002c640b40c4d0f869854280e0420100c03410440099082ca00c444052403000c1401d070046003042c0c2d01e5601c2c00c2030701c600344001544100503e0040204030f140404100c8070501c402d0881c00d10800c090006030a01044151402035140c511102a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 306608570 1250 306607320 306607361
    0x9120715050c010b0a0b040815150603130209100603060e04120c020d080d050a110310031b0e15030d11070302060f0c010c020d020607022b02151801140405210405031b0301 75
    0x5105c1c19040e500351032b01044400a542e0381c0c4081c42c0e2810301140380301c02034104c8505414022138444550302c3c0415600d03103907010040195148e4204d2040e0000340c4000d40902160f180e03811003103200d120b40009040c00504503903070082e407a50b100134080d4003540e06009405d43e2081841411f01c2c040c000e900d0300d51100d220203811400c00c0c00d074500c540402803000070558850890301c00506071003903804034001e0000300c0410b0118078042a010b000c061003009420b1003800390841c40700110f030084820382610190380009045981c110703400c1c0445607001803071140c03040380c0901840c0d80058003402088494003003680503280041c103003240640f030202c0290401d4155082520440b0a41184a0503a000c81da444100421090102d502c00d1381004202d143c20030b1f04000304000c00c0f8954210340e203403907075000d949002006400c401c803000650162007075800900540002c507045480f0b60321203000d042145e02d0310010354038060395680042d10f00043c84684005108140004203018542840754000840010003403000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 306609820 1250 306608570 306608581
    0x30c010c0c241e0e0715080f0a1d100510050d20100216060207030308010b0c0f010204180b030705010219030507060504030509120715050c010b0a0b040815 68
    0x34404a10000780003912004882c0b0300c0151900c0d04050882c801d181d41c0540040024000f940240c80c2c4402604600d200b0044001040140403111003c440380c0780e03030b0f001d00e01e48070501c615808030342c0584407845480d1a07540c0125400c00c80029a00c0c8060a18014460f0210100f0050f040e200d00406090090083c00c80c100314544500f040e41c4081d5901c19400500c1440c035081d400610460401207035009000031203040c102d00e40003e05103000400304820720180c25601c1500300ea46003c0e5000081c00913190200400803c0c101ca005400e42485190640b161400c80703050060032600258421840c920241200b40361101992007203400450050307001c0c00400d818000041e5a8449400c46030307802000d805200c40501d4032840a07600156481013041c425411305090043c200e0708500c4290344510555100010b80307120010b41d403000c540e04003c408441050301182501e01d038110303d100c2586952a11145049555041445000b4190548019440e40e00748480c4a10703080210250115015071a0107101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 306611070 1250 306609820 306609833
    0x6130b070c020f0f06070c0b12010905062d040903080a0b06040312051c020d020915190e031e0a05070e0c040308071103011a011e21180302030c010c0c 66
    0x418807000350f4584d80003035842c20104895104e0f0003000390650340000c10218070642410014448400e000240b07800311390f01c0c0c0c1150411074105462803544070908110400449158140c50746107106401103980c5040c0000004c00c05440105508500043d40b50080003200e050f14443c240020f401920854102030039941ea000030103410400c0c05d4107000010911780e51403a4a200311403410004290b055444252102103032001e9008500460301c03449809410324400540340381a00e0201441c208552000144140146c03401c1940400c001c3d01809820030054592072a00b0340f1416807880d0400a02c40700125041090610200743c1001d0030780c001043c107100e40b44442d00149c50503640c000030003c2c0c1d13407403051518400c00c0406064994042d42421441b00011f0345030240c041a2403000e0b00e501c040c02c1984804205a032075100340d00b50119904008168044202040030401328680700c00015501d02111541e9690b000c0c00c3d079041300180c0c40000c940160340d03401c1c00b445080306840e040482d100440780c0e4400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 306612320 1250 306611070 306611089
    0x60d0501053f01020412082a150402030115030b01170303011511030d05070c030e040e030a080406140c3007050a020705040606031505030f0604080a1106130b070c02 72
    0x200191003015054580c902c0003941143c008002140243c034a0901c507180002058110040340700721081d03841419034070408200b01001150500ca8064080c0800c614101c16110101070020f9170150360319980b02c0144115901084051805900e4020444d0b02d88460004603000d042c0c15204190001d100402c41701c005400c4402c000485400d14481c1410540d45040c658010a68019069424035080c001015040380b54020814000d0340d5203a1550855410301042c1c1d07d01c0f0104c4c81d0254000c00003c0c416078400d0300303043d0b0010303c1104003140141c40452404030a40c000e55244c020307503100007405260f21085a940341c0c1000c059001d0480ca204a01548550b4144000c140e5001d102000480c410707414424417240000d401c000f0f10401a80f912801d004006040d1a400700140218015010880c1d20b40080e5100c41080401c1c0201959615a81e0303140c841c0d04015085001d1040e100420284000103102c0b0354400c1f2001d071405e8402c0e070340e01d003043c0c201e500d0007030070400034410b43ca007800000d6160001007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 306613570 1250 306612320 306612409
    0x18080901110c13050f0915010b0a05040e0405010b190608060d0609050f031c05060a05041107060207030305070906080403020c310e0105091b04050402010905060d050105 74
    0x101c0100181d00303800707042098120003168010900c010903c80c0000641c031840c0500321100d6192515900c40848590380c400c0c4070f00380300d14a09200010071000144c071000b0041f0f03140c00e1030f001e4103290740c4242e0001c100c0030070350341112180d440b6941b90340c060031302c4080b008040d0541d1030756003012864501c02400840b8003501c00c074000e1180900200510116406c0304803229440f00444802c000c3e000760090b140c1d0011003404040301c02000500700c11225501885002d0003005200001051a28042000804261664001041042c03001c0c42c0440c000f840a080094001e46000c2090b251080d4028801e507211f401480c207001c00315040c04007095000518003030030340007038440c000c5a00444d544403103003004580c0a00c000c00711010141e565000950030100d0114003038002440300352610f44046846442001c840d0342007080014007074010749850707080250441e0042c10304c807001030388600c0400d010354400326009042c15110030041010742080c058503159184544852402c0c0e911808540c00b58040d5800b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 306614820 1250 306613570 306613577
    0x80d02151b0901051603020d1407030206060603040614070309020103060509040503190203130308041d06030607050702130c030911030102090d060b040b060403050604050709060b09100c021309020418080901 90
    0x68002e0140d0080040f9843c0d070801e00c106100c140c140c2d10b802540c82e00070210180018107e100c00b172584201800c1515556175168010b4100c0d42e650b0410300142d500018400c2d601c040d02d0f080c1c481c0032a211001d40d01e0065441d541c1c04201d100440c0000340507614194011806403e4100420010070000b206464601e900c1d0500106a8103504034102e20794021065581c0844051000000401410100800481c0d0807001c6d06a010f00c60084225440302040312a2505908100e00081c3c040b8456402024514401040a42c0d84107040c00300c00219107129003a040420354450040f0b00784a0604252810807000720025440c10150034045100c11620b024000e08445d120b82491032250354541129401c5d003c05403070143c840f640e07811b00d10790301c20701a5426240340c000c003000440c0b9003229001e01000d8491601481d4031700380c51101130068056240090308100104902c00700c006039114000704400c090300410105031501503004100488087c0100e07820004402e072201000100c40b0070584521140909 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 306616070 1250 306614820 306614827
    0xc03141606052b0608060c2109070612020d061203021b03030a050c10091208010f03050601051e091014061305121507080114010c051b19080d02151b 65
    0x70f00d04003030b1185401020a600074001004044c20508001d009030444007a251300340c60340c1e000d150150f040c1c8196030b200d03402c0e0040d003014000c160055800300e41c2d60355800c1006182c540e10741160750440c0c019070400079080e5018040c0c9010300d5810456a044684a45110021451081c00003643e03131288240f0f02c0b040c480085521250b2450522040c0080305004405115070542c2d85007902c405003030001d00d0401300e42c07040c1c000700d104480c0d05600400d603580030f030007091a6424801006103a134444440201000300200e82d403c40c54079020109400341003d04a50030310142022181c81680100240c2c05018400a104150350051511110000c88505848050840c00010300180c11719072100c2401107070031818403c0c403808030390025000741200c0c500100b22901c030382e008004581031503940901400d00e5100510f000702c2d908000d504901122401441003184000c041a50f00f48410340f03603c0003450360000e6210034020307a0188030034100b098458800030082c1c500120010004003039800405440c00010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 306617320 1250 306616070 306616147
    0x5070e0405090a20090c18090a0f0c0c03110c01020601031112030a1e08010302010e010f090f030303020d1508030a0309020d2010020d0c0209040c0314160605 69
    0x20300148500c10b812104c0c052242004220400c00043e02106107400380c1000000501d601d140101615108062040341d00300080f1082c00f006a08076014180b582d009640b240103c010075014441c500525140e078840c410b9104540c00e01600d1000400e4802c0a203400150310044543c3e408140641560361111402000c00c81d82d03400305c0d042003022004100244000903126032004c1c0c10220700310a00300d181d03900f040b4005807a40c085402c01400c1c0300080c0895010480c902c250760088031286034110702c0c1d18010300c003d40e4500c0f0820010803140d00a5010a40c000b82806489015014028110b21122840a040c92400013415920b100c1c0400320070130155980106000c640d510000c8609440c0c102e00101b108414170f800240f480e4450901480c0314210001841ea40b4900108000003041c0590700c5108440210340c007800301d1120005c0c4200c0300d00300070300c002000180201800c069441c90090043c1980210384403500c0c0f070100c4035000941401800c2c03114400310600d80c032800100c48030520007451840b100b07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 306618570 1250 306617320 306617323
    0x20f0c090a0207081605010f150306021602210f12031306020903120a03050702011104260607031b05040312030c030f0f1a1503060f1215150405070e040509 68
    0xd00f00000d140300000254442100300c881e549105150160008000d40c0000c1c0301444210307a40c0c010404030000c01d400040004c18130a50141018006d03140d10300072101401d60001e1810941c0c201c1d2101d81000e42208a0a030a400b04030350054031502900a00702d10640c9800c094441c00f0060040e0103008503d8050b508210a40c1c0541e802c01304007a04441039428034510f0081d140e0007450b00030380042d00d01400200030328414040c9040180d15981c055152509100e01d60a83c40150000700180500440c100010844200302c002d10511850740d00203098400c207c03083da1203031850040d000800c1020702c03092020454600580c0c1e40c040d105d0400240145502509801a04405801e240030760b2904040340c900b00045d4004041100348051643d8031014844100150b0601c0a4005c0031054400d1001983d9802c0074515107041c000d008009103254641203481c1e80c603208070498103c0d05a0320460034456000c0001841140709001120180524500041c00030140c01101c003144d4403503030f00c440204139030b80e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 306619820 1250 306618570 306618577
    0x306061909031e020103050906060f13150f2603030c0706230403030605060f1602010221090f010507020607020f01050d0c18080c091306230601080601020f0c090a02 72
    0x34403c2c1464850b1202e280f815888181c5020143c0c0400c2c103100000744007120100d091881258002e0089100c001820148542c103101501f003500070582e01c3c2a000184110156a5070007000b2450f2181d85e081d040c4081240c6060380807a11140281440d010070b40c1d0701c5004010f0300d030f102c25142901501c6045909029000d40703140c54540c0015a8114038180c0d150100c01e00344d031b10a900a0b10300f402074035038800600c071461040305d0017003035250018807400c0c4111110501c084000707401403040b208030341b1148401c60142c20f0795414501c500700740026940f465041422420b90b200ca030900303009042801640110705103114200c07000744580800701c042640e0340e00440039101c00c0c84103410100800c0700c80d03030300190a15500505103c1c4c4107049020005980200041c00520100d0140580e030498840360000001c01c2607500040b03e000340c48202e509a0025041e8036642868035200d2606003900b804400504a8071000d040c660443d08900c142e03c09600f400500600e6540301512442d2540d0780e0b0300301d030b00f00a01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 306621070 1250 306619820 306619823
    0x10f03060f0f020f0a1707090509191b030f150e13080a020307020f0307031a0c041a1801031b0c080706090b09070b0a0e06030406020d0c02061803030606190903 70
    0x28404240300008500100c00744c107020b4550b864506d14502c00320543d5212680c2241c260303000860800c0140700c0d030304207101d0140e00314207a0401c10801685041441c82642e40c81424000c500304041c811b0003516030b05026a03e82a02c0c440d808224130b4041b1650f403480004140110240400c2c810b02042e400d001003001c2140e00d980160005403200d065003c0251264007003242a845000583c020035514030300403815404480c3d100101e5203100a595841a43c400c80041004003820014000042c8410004c100d003402c00406c200400d0340e6440c8a40600711604c400b4010504041c98041804104040341c1c9040c030317444001d0304020712021100d24280d1818031800100030601818000c604d07040140e080680d9000f080b1600a40c0d00c51602c4081c0b005e11800744905540024040c0c2240e2040c81c2403072001160001d00510740076140541880c503400640300d4080e162001603110f03c0170444105101c40150f844c2e07440e010042c502d14284000020803e0103103a15000c99400cac074100c6440c525000d0542c050095 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 306622320 1250 306621070 306621101
    0xa1703120a0204080f010216020f0102070b0307050403060c020606130f23010608090a050604020108040c0b0721090b04090b040b1e18040b1303020f07080c120303010f03060f 76
    0xe00d4030107003001c081c3d0068400c010b5a84a0760141003030054060003520041040b00d03200d103400001c1c640800c841d01303482084076815402a41008902e0004040085120340f003580c40d075554661541c90000b04850845101c40110f4000c20207010f4145d54500d8061407900210201081d21003150b134125008080612641100310145171210783c1115084100034125420781d1910910f40c0e0341c0c110441d45030009103c008003160041c7d4001401903004d00945030304140124000c2d8110340e01c1c0c01031444141c1c130018050b141000e1090500e22580798003807040003d9031007031030078030303000340c50002003243d0340c0118001d2102a5031120004012511f07645e010381900d240003069400318400f440d908000d601d9000c61014020045000700d0840f42480000d214081d41c1d008000c900c080c0e40c2d00407100f110742e211a004070118001c402c9021106001005024068050310020f000c80491120800c42040341011340804944c005200400c400806541c2e420226030b0000e82c0403585400202550f8000e14a1170a50b0424 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 306623570 1250 306622320 306622357
    0x409081b01060806010e011a1809040b090c0a050a03112b0507060305040c0b0a1103040f060219171c060902090405250e040f1b080c090a1703 62
    0x1003105421003012115010b0503640140d8803486201200c070002d014800c0c80c035420340910310440c84020000c0070110840c58078000368000010028021740c0007690140c0e01010080e091012646040c802009000d80850700118810b24001c040742d41701c80c10740703c040c1054000d00300402c456201c0e01810000005006412a40a040302e501380c040c54104810030707662840b40001c0490002d029100d8a8011904224410030f0907160011200c115400042c0c50300c10882c1c001003d0742050b100b00080c00c042d01d01c8001c954086820520000c0c940412107040d9010702040704c0b16680800c4000707101843d00c1c00e11416a40d0b030381400d505a4009920131002401c0b106142203000151810240d020342460041110300340080e4a8441c100c0c0d1011080c2c1a500100300781d082c020f290b01d41e000d50940c444c1072601500100d0700c41100c03100da9048480d080c01200796580031480b60800e40b90f00481103a8856031080780c9506111101022810720080d40c01010004404201c4015000704104281c1c0e900722140c6480c031b0003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 306624820 1250 306623570 306623617
    0x106020a0c0f060504030f2f03010e01020711190806010603020307030c0201092004150f0509070f020d080604020d0c09030c05030a02011706060405030a0f12030b03030306040908 78
    0x1954440300c4029a507401c00568003052442d44658076504aa4540c0c0c0d5032800c00342591600b800c850403000045410b400000034603503816280901805030240e44290201d0165440740506083d81c0c03c00c803200050364810888600001c481d80c8800c01880130964960350030248040e03010b0744002c0950845403003841030b40c00000e0f9150b0f060f0000d40c8200d2490f5070901180300e41c074009a00341d41680200600c403c224014180103540d04001504031780760f0050011981c03902c00220f82e0030442081c0c0040803c1500c03003106101c642461815241c009401c0d14240c000300c0800c050007521007001c24000c1d01006030300d6002c600355075a0380c0c041d110801c1c2c54600410403580500c1c000f91005619200031140d5007124400000c46245c04100c505080340c0603142e00300e9010404822090f0007400401d0150300c0304051001003032a85081040880302e61156100340c0600d9802c0c100740790703c1400b4005140c00c043c03d04955074902d4401000741ca8100c1d80950f00441c562440f1718002c00280205000918410b00d500354244 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 306626070 1250 306624820 306624823
    0x120901050114010509010f0807050d230c07020d06050c0706020c010b010f030c020d0e06072a05100903021c0501110909010b04050604060c0c0f240206040203100f0e06010602 76
    0x20304a450184002d448074450300700549040c01103240041c04a2a554910b046040c028045142d00c0717142c6141c0315280c4011468002c2c1101e5001c80e80081c0112100704850b4804170f1441110740003102800c0702401d0000b02c2e800100505010b050003003071161a00003080285003480c041d510070790382c8080155100c00803111802c0c0200b2844400d5400035614000d102840b074068400d0091b04002da501504000c29070001c1500c8140c001854103402040410601000c940400d450b010801403030100741d10600310320212016030041540199118003d86111003820682080c030490450794181d444611103012131082c1c4000544650015144bd401c0525040141c86c0020090100703200132610040304ea6290851000345005a00666801c241c0c100000c4c411140104c40c2240102c0c441c58a4a501d039807143c2032341d020000325600c040708110b01c0b0070914000082d08108000030702690b02c01400a46001c1e00048e50380e4551315024103455558040101c800300480d000500b41c0803141c011140c00796594280203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 306627320 1250 306626070 306626081
    0x3210a0c060f020306180601050307110a0f0602120705040501051204020415030302030c1015290d020915090307062001060b030a0615140f1b0a03120204030c031106120901 75
    0xf43c8165015143c80001400d546c80c2d07140158030607512030b4150340d1401020b07100c1200b4140321401d03e10600d01c0705000034440310500c4151070301c1003402581b10480d1a181d5007103000c0c0a8621400c0c00380500082c003490342d00c4410740301c071089070a8000200f81c07901d0010030000d02040d001e0001207445807201005040e0004010a4203840c000115540c203846800e680c412100c800c01c100c3d014078000b913400c11200d80c200120310843d04108504240380400d460013007010348e1103410070000e0190040750001041c6064142006621350b26481c66203012030a10010f41c4400003402010b0030312039000b10f0150303804c401d0103400401c54807141c02080020340390b004a40d0b031a08119000700e0b12508001010035400284003502c00103040030b840e44c19003c582c0c100c00782c030203030840340d00c00c09150014132000349242c240818021480304a00058080d8802034103000b04515050907420100c640104010400188015818000c494100c06241100711300d40000541ca441480c4622007051a008284010000e042d03101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 306628570 1250 306627320 306627331
    0x110a0c06020607051614010209060309010c080f01060806010809030d020a0509120106030507060e130903050d200a0e030106030f14010e0703150213030c12050c03210a0c060f0203 78
    0x2c0780c800395510f400444541c0304e20a01440c000d0310b070010382c03000910a200c0d007a0409101500150a2010260208480380c108940403091691208500e007011508202032503000302221400301c41a6050503c05010030707202400060410041c0c1e400108101420f1099400c1001c01400541d510420454000c100b80c0010401c10b1040b0300001d44640c495005204040440780e000d006820741034503100c42a6401c110780c5200c01e82100a45002400366142c034400e60005074880d403109501d618124844070100da40401400d107004800e4900708030418060010780709441a01e24265982c1445200420f01410055000a09204041003d0380030426402c0070040250f40c5c000082140100001c04141d950750315100180110200514058000c21550010204d082c0d4540c940040c8a64aa031042c1c50600c2c1c1c3d900c0300b02d854070703110103100810409001e40707580c04d1000ca00408000584a080c0c800c407420080700100424000142800c0c800d00a0a10308042d6402c1607007003050b0380c0a0b500000c045c0d407040700c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 306629820 1250 306628570 306628573
    0x203160801080309010806101403010e16320403171e040e19020c060a150905060303030106031d031801032304020405070c0b13020f010c120807110a0c0602 68
    0xc90303002c40c0042a110400b8059441c1855502c07014140524074180d248200200308544c0801c000f5004402c00a41c001c01c0d8108069815241c00c012140c1c1408030b08030700804000070401444c0800c10004044074040424401d02d501022000111021078404e80d4401041e208401040e1844814000041c2c11960714010000b000100200f0a0354814030031400751100400092000c22042ca0340b9a2600c5c910074184403006103060710180019213400d40c02c64000c03c16a84076440d000703c03428456049401441d64800901044c141000025203c0c00140502d4040541e5980c44000040c1c00c0140441d000c6511030640c1d0707445e41129119090000c822150707601080c00e00300003d89406a4a02c1a440d1400b6410034070760546650382000003a100250100b410403844107041c00c003040108989038000d1104121880c002805c41c814807049150714404d0a041c004248450000724160004030030288019203004212540c030400207135000048502c00e60785510541031031008200c0c0605c104d10544401d0340 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 306631070 1250 306629820 306629837
    0x2120a0b0a05091915090303090b19061403030d051519091109011e02010b0a0e0a0c09050d2d0b0a1a100311300601020d05181201020316 60
    0x180c0050303207441381480007094500303d00407211030b85006030f0004040a229181c0442c500300c40c1e8442d0200301c0d05c00d54540c14040e01c0520900ca84034428490400140010030889003402d040d0303000243c0380e000340c0f2400c5803441c2d1600c0000d640c1e03260040d41610030040041c90b90050401921701800082068002d8545070303480d041443e080e24424005031440e9603416903d04c940030040c5056031030300c40c00c05058042950348950108416540d07584158000c0c090f01da00910710341c90300d99581815150f01000c1c030700c02d00684410a0065803141511550030681220611106940c10540e2200140001800c0300c3c4142145007804c00700200548240d009105012040c480c5078454416030301d000320065840d99102255488200c00d25000381c02042000412440307050510482041c2e144101504032048161130105116581002252501da550403441c20302c0100b01c0a0a15a0003074104d01c911041c07021190400c80d031070032803070703135405680002c1c0e80e5080700235500ca0071b0045003081c10050b44901303400403c0c041c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 306632320 1250 306631070 306631093
    0x101404050616120c170901020106180b03250611100618051b19180f0e0f01120f050f0d030507030c0203120106110741090402120a0b0a0509 61
    0x81500341c004603084045c0403c540d82d07802c810742c45a485100c2c0e1605654030364900042c02520707035200000404102401050105c82e0f074040500701041407610300d03051030b1915032002d030100c114034001c41611501d00340034000900440005242c0b02c0000c0169101c903007002800b0a00881c610a5031341031425400c000c1c0600d40b14036114206003c00b80709130020100301070001d0035038050840b8007401020f18509002c100c91302c51920641c3c140d0195048403050071070707010042101c11600c8440c01d074044032105000741194108400320304006500e481c040d00c9c000550090000303120042c1300b4604070700200300440701c117802800c40290107000d01b1249540403a107009501c845080c00801158001c41501540060507030a100301580d0b080c400f020002c071075104650001c1044005030104401012500c0809855480781003c0443e00504444007503156450700d60445000c0e40b01d0800d0b181d00603604490303003125000d40003000d85c034120f900800500429110030a01000380b140758011400384050300213551100d50301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 306633570 1250 306632320 306632327
    0x8180406090c020d05031005120a020a08120a0c11280b0906070f2103090c210b0a0b0d1505090609030717070c06080601031a10140405061612 62
    0x20301c0801c0025070003211007040942c1c4183c5c000c582c0b0040342113000800e00d449002086071014502151103460b40049903240c19460502082c030000d000080042403000d041e06051030450141c81119000e0106200c5201c0c02c114800d82c040302000405010802209c000381c1a007440681004ca42095000382410040f40203007902046881650780900322034502107050352080c0c4204260f0005a03a048089411a11043c8950300045191003403036601056100990501c91105c801c1c5a102c50300407565507141c1e801c80348003010b005000ca07400a8040c50340d42d5404500310040c1009035289a442007002e0000020071852070000c02504034000010000b03175542d040c0c0b01d07944440a0f82d00b24480d50041c4074403000600303051440e90802c55001d03541c07810a02d2540e070305a02501d65400040115a42c0000c00c07a0550349072150550710066503403c0483c0c62000380100b4003070707161005c2d1901000352100840310304040940441f8024240504120754402e4080c11b1003032000c1c4042000c648080c40725155000084c407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 306634820 1250 306633570 306633581
    0x3041205040605070b0c0c03070b150405070c0807050f10141303090b0f0d020f0d05100b030c0a02070f0b1c0905030f07110d030e0102070b070b06120a0818040609 71
    0x1603030300c1d8a031501d030744c41e19030740f080c680c0040c11840030b82d4003000715207001c2c9024005095101c0c4140e6982019080628040030001d0070400b1443c0643c3c6407400300058258400542c04419400c144400d664000505215080246291418455114895625000034641c0c4d0000002d491000e045411940740c8002440044090b03400180006265440c14881500c481000b0030866100680d000d1504241c40511404c0c0e03005098011409100891180b003000c03254002c7da68080080d000d486151030410060801c43c1c0005014141c2d00000407a031a10f00e14000c00c07026018181d03080c00140d0165980001d00700680c072100e114031869032403458000d60540c842c0904103040b58000d0145007080c0809602c82002d41100d081542c050b400d10041e0b40d269252030842d10b030002d0090f61220483e814500000e407501e075040c3d100c4040c4200c100022008103000309802ca811a00c02ca42c0c06501d508101961460400e00c0f103005421140001294489003010700d040c0c02d20380340c0c207a400f406910303a5040603c08480 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 306636070 1250 306634820 306634829
    0x6070f110c1210050106080402100c02130f0608030c0609010e0607020a02040504020d06090c06020105060d0b0f070e060c01061e080606011809090f02150301061d060409020f0304120504 81
    0x7408844020864501100030303059030b0000100711403003280030756400010740340283c2c88940410310710818841176041101e140210441d00341084a00300c0380301d502003a04210008003a00c1c2050342e400f03000003449000d8020f04010a80c2004490b1030380654482c0944944003a10301d40c030b80d0f62030010b0301d40d4403c81c0410ba140c45408560007402040d80039400344400307410018003c030782c003401140103907000071128032501c68514080c00500310014140800a421120007400442c401ca418641480020306040b4002d58049007105402d8016200e080c030541d6130483d48190f0710f138480d8011481c5001c1e810150321040c11240014031001c0d4525035600c500c0c40c0115203000e101c081c0d40004001030038550149483d20b152203c0405030440081c1c1d52124041201c100300d40c201d4038005800d40010641c60300d0b00e83c0114540c40e02e200b45265515140d0f000d0504c02c0894092403072400c052210210aa5030744e419100100f1342200c065581e403000c2180300700c1c0341e40202d800f21001c8014040600d1645d2041d0103440646 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 306637320 1250 306636070 306636073
    0x2031503211809131103030f071e050105041a06060f030103031b0206190806060322051c0c02030607030e060106050904062309010806060907050711090906070f11 71
    0x4000c640d00100d0b9203046601080c0341d0045503115150394911440010002148020310f51508031003020107104042d2007640305010000080000d58110f0b4001c65102291400401d6001c80c0c000c00402e003080054615442d000410050056444820381c11001d00e0300c4015882e52000100a140e006c6c100c694180b80344180014070010340914102510035011022180c00002c040e80060b940394009030824000d230503080e9110000c1d680000342c2580140086800a04514200d86405413002804100040c15102c0021003802d120045c044a10364281880cad103a0580c1c01c4550015180000202c412402417080000041c50740b40700c0d2240340c001c20407140c06080d259107420340c11240d5810a009a66005940b40c000007100b0390300c1440c0c070742800c00c220000801d080b0316404129218005900034081a04410200a07090f40d4903181181c1c08406410202c1c2c07a10303802d08040170a0300301c640786140c1286410043c0021003e000450502c030389401c1e0f0b0342004001200404031036490038149205070300d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 306638570 1250 306637320 306637363
    0x5030f09060f0f0411100f1d060f0a12090b0105010e040507020a02012f100605120d180503060f0906070203040f031412030f04020f010908060a05181002031503 70
    0x1c00c5032509030640c004c2d00401501c03048200c2070707002804420a010120000c038024482c0305031500d40040090004403004140080c20005190106110380702d080c1d0b055000300400280d00d840d00e4020010262188034130b02c17040101c25442e15045035240300a000e4a800b045142040c01c0301c518050081d94031403c0194013421b8142c41c950300544d010810465042d1070802980d86c0441c0328180795141030050344244006100c8048030b441990100d8465800a5004988c480d1006004040002c0c0c5061814140d04c0c0c00722018003410310940c00070800f03030042907150042c0c00501144108084800303000300b0030101681c001d6104c80e803040e030340c03446244a0302d40c131402449800c202161100f00051004800c0500342c2d40302412000076911070f40d10841d20415898082e00a00095051a0088031403204d42030a109184504000455942d80f8009240c0b40d2a161101c00041c10303546110000b41215984204450302d1113806c00700305020750012218000b10081403d1812142d150000e41d00404080c0b00941084 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 306639820 1250 306638570 306638581
    0x6010e010b0720030a0605010311030604050d0e010201020d060b03100b130302090603010212040318061d0927070614191b1b08011b020601091e0c05030f09060f 70
    0xb500c3c10031820140030180e42000b050250710144a00440103104841c006201d40c15881d02c00e11141d4003c0c42603020340c0c812820880081e0700018458800380c060305214103000d203c500100d0183c0704100c3d810302c00c41c0c140132001030340070685000386004100031603850f40d0064035a010285203000e40d8891801c2075400d10f50410150130701041c0143c00c48000303000503240803800c40c5000e1100d58107450481c0040c1100030b20083c01048003500d840035042e64601035400d040c601d80310010110040c11214455600c650100c1c8000000c00c036000b4007406000c02140407078000100b01364a0b24254030407200801e03000014510500900b01c01c6826071940d03003040060010204101300c0d40003007070b14455440c1c4a00c62485034086643d500c2034070040c4a051489a82440c1414103240c00d4441c001c1d1b01408003040002c02c10788098020400c41c1c15180ca503000010f8840120421074001c86810080c0c448080c034080322240c0380755001c0d00030740c130905441300071700d61586079800d05a07550b50040703c0c480d0725420044080390 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 306641070 1250 306639820 306639833
    0x90233040e070806010c26040302060c0a03020d03151a0903060f15010309080a050307050417071a0306030a12121b0e10020a0204150b1c05130c030f1b06090806010e010b07 75
    0x45e044800d1485041c20b041e202e50102f20a81e10419400000c0d6000706d142008050b0304100e4050041010b10f018020030780c00611580c20b480b554080c4080e1680d098103002c001d0300820741502c910b03a100400329441402d041781c269141c0d503030070b41d100c1c01e13041d00844038021154042c0c041c0008803a4422202403070011018011129a040074084408201301000001055500d110f95034190b1094000600a8103141030140c0b1f04138200c12174403003117104c1c041c420030400d95808100e1800c401d8104615807903282911000b1605500c0c824246400d0710301d40784501c1107045424040e50181c1000d0b84034441890b1000c8100104940c0c010950300c01031340404441001030415402425180c6600c07084c003d0800e4868480d4002c1c2d070002d5503510401d13a041d180c4041d11079010700030f080c0c1142400040d9000d0b00904e44030383e444501c8501014010346440c148000400a1b54113064114240742e00e407211449072280c000502e100d4032449842018030582d0000304440c42e04034212412503604120b260f1900700242d0740d81 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 306642320 1250 306641070 306641123
    0x603062007061104050d0503090306150f01030f022a0606030a050d03020906070c03030f090f12020103150305010501032a0b041401020a12120609090233040e070806010c 74
    0x800d9900061000150386d4035040881a101c03803051014544956120040c140b80c0340340141543c50141e024908000280c0300c1c50b02c24070002200f0300e804140c407280c450910011b8441c42035402459003032203a135100054840b00011000c078101300103540740da0702d500c010103507101a01c0c0c00250594001810b03400038540641d000b0151550003401842c00d0021580314900134403c1580154041103190820309212a400015075000d0b240000c5500c1c03165007001c6a20b610002c600390000d0600d5600d07110307018031001c041c0100b002940c0c0100280000d603100e1a02560581e013803140903800d410401c0c0f45c40541d100030f060f41d00c2900c0c2d110882c941480d141204140041000704e200506500403c0b1300c4101140007049d85010450650301c4120802c1c21711040d2808a4003107501500300540f4182200005a595400244048000c800c0303051046403039014402c50540052404451202d000030000b488040014104d4429003050f01d5103042603403014015240001e80401c02402c05141e50150300c030006d03d0004c00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 306643570 1250 306642320 306642341
    0xc03051b0405011d0a0b0c0c1009060f050c06071115061c021216050f010302130902030405070b030f040b0f060f0907050d0204180b0a030b0f151003060306200706 71
    0xf030750814400680403e043d01441c6d00000000000025001200c1c401048403480f141401d4489920085030081c008102401c1c0b80241000c105450f203140c40041e21400a80300c141c07a03c54141c624504180b10060b05080501c0b554020760300500022003501c0d4004030000d845010b02429259811549205d110b411211040f003c81e070254801c4c525240485c000c0105c603240010481129000900300400c21003582c40103001d2504150041000d621742500400d644000c60f1410900035850b40c48600c3d0040c10644990410421000d0203c1080002c0c00141c584074003e0f800303621004201e03140c4083d602c01c01102200c003641c0041c0145d1040c2d40a05059070b4065004003a4680242880c07881035190701030f6449607025000f0001c003413807102c01c4003c00e442480b41c45d800c1191104ac40d02d103940d5544065010040c010448600c8040004203507030040c00409080680040c0040c1c02040103040280061070309010560381d02e85060647c1c600d20b029021510700d00b800d242c150600700143e07541d41c240a0002201c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 306644820 1250 306643570 306643607
    0xc070e040f0803161b0510020711030f0303010603060e041a0a0b10020715030b09070c0203161e0503120f07050f0321070c080405040b030a02060d0c03051b040501 71
    0x1201c8002c0742616010b9409032103420002c02d035a106103030004000e400d03051a0005051240748062000a4000542070700300c1b0001c8202503110300003030800b12181710200100d19003501510815100f40c0300040000c1d4103071000c94808018182c1c45001400c1d002400702c42c000c00403200c00400168000c0c003044043d62018400d8030215100c080c15000c5892400100503410142e0b0140c0f5060180817481c0700604880381083c50104000084040098025607010b0501c2040c024424001819528244101f1441c04102d00ba044405035441d0804d01400c4400c505d0740b81100c0c99080080703090b1402043c590240480c4241e924240540c0260300071041d800294100c0f2070f4440c0344482d299500c0107101a060220010b0004080950601c408050511004007200e0070000c8030800c541c006441c480580b000d845003036400081c00030098020a01e002c02c0c40f00701940c00180803c1d1120504510780009405026075901400151160420000e40d4580540c0d000341d40704082c041800194802e440c00c1801702007002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 306646070 1250 306644820 306644843
    0x405060d0f0e010b01081e04021005131412150a021303061a1003060e01060f02030c100c090609030b010506070519030c0b07050a08010911040321140c070e04 69
    0x201c404491107211000d06607510350038440c04640c0c210301042d41c0459450b070904105a6100588000200014002889580c10303204a035100c0b03114100f6540310342501500030445a48031050710030b09101c09907980b4810306000300710303849209000c11006111651140c00841580b030302440400030750804503600b000c40072902c01c004003050041c0580b1b07509990007082c40d5081c0d00e00e0000d000d41000d11100d80801c2c1428030104100d007070745104195045410a01d08460b58200c80d1608900314801d0343d00d850708510035240000d524201c65448601024a0340e00e51455059039580103031048580c0b84409444003000c00010021070421100070907460344900140e6501d00b03060b80505a0740c649110301a07000920303207000701c0100f01601c0140f940250031400e0481c204016130b0401042c00105018030003096440e51606000300c0521400d0750091a84446e40034802c59160038240c08d615008190340c00050300c0c0402c80b00700c1501200c12102e10b02265400b03004030750704014007241c003244042c0c01203d01c001c030034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 306647320 1250 306646070 306646091
    0x90204090605010303030b09161d0d031101050a0c0203030112030311070c05030714091302010306080a14060a0b011d0112020f03040209010b090102100b03120417010e070501050405060d 81
    0x40c41800c00c40d5215803400034080d411400c00400b240d40c4815044e004241c0c0b401403180d41458070800f4a11007060340b400c8010609990f40d14000e00018107c0160003d40701c03444142010b410010941000341000005c10103585d40500d00000d0b1843ca1001e0320141c2c208000500c0746881105811041501904022603040071490701090300d0b0380441025034201c191403c080c0418a01800340b0401010300d103907154000c0c242e000004001610242955101c108403084032821039000742c03c048010201d40050341e43c4082c041c00c08947e9400e004000500e1030007210005800100f1600c2003119405040c1e59160b03107400d0000300c00e18041e00c03c0c6032080c148844c401c003ca5030036005000400c001054087c00540307030f00305031040c02240601a008050242410301190f250359030700040903000310503040700c04200d521114020a003000010200341c0c182003000980800c1d0910782c1484000c1134400072001b00022050b105081c1c0d00d5250768045d00f40000c80401040080d85002d80c007400010001040c0001d610418 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 306648570 1250 306647320 306647329
    0xb011b06150608071407020940050c15030f0a0b1309060e01091e0f020303030408030103051501060f0806030322060e09040c060c05100f15061806080603010902 70
    0x22035020b0310008240d581007203c6180d10048204600850b04031035400d0554940c005140b00d0b000601d01100e10246490440300d40340e949400007180c291400c54604140f01400b424029541620400e17282c520030200d640c00c080c10700450040c44803500303501040c1540c4070704d00c5680310544054500c880480e100c0c88003880e01d548114006e20514042c000000e140002482c2c8034094508003840c1c0c50441e4500610071020070f2220f05070400c040b680044d000c5403a9880c3c500391910403070400303010350140310200070001000680380003107058034080c408441689003011503801c00601c00340116000540c0c2c82e40155a428040c2c1d01c041d4120f00002c0a0724100300303440507109a2040801620a80b000c040b600410646401525150240c002074540c1134603442c20b0784915000d035155214000400c60283e4030103080c4001402049142c50051006220540d60108020081e0680780050608000300082c0041c03403c0c0980201d0209071a400c6102c046603282110a44a03180001d14042c1c15549a1645030010795a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 306649820 1250 306648570 306648611
    0x1090b0d0b01120213140a0e070b0d090605100305030a1812030f0807030b0a030b040f0b09030a02100c020c0909030d060b0c0c04060518042603040b0a0b011b06 70
    0x80381e40300500d5602e0040180c50030350030030101001d0346041b001e6002c0c0008144050750101c0d0a000119140008000c01d518060b080c0d03000314020b07c404503842000c1c106030781114104034003490003880140c640344911032403040248401080740d481046900c4150b4000d00016490502d400d90014456645401018605002c44412070008615000b10340105402c402e5860b00f01d865840c04004042c14031010451f00d8280f804050260103500b4000b4003041041c0004107034840d4030260001d41404e04007551562a04010506405801140e40c02d02d4a02400d100f400f8084020394000e100707a8440f0404d002c81411b01a055010750700081081b104185018000e10340140b000c2051999501c4c1c0e1303041d2803410006444c8002c1c0c82030b82001000c0200e40da50340200c4028101d1408000f11645072860980d1804210302184000b08050250180c2c042000c240914440c034001c14194155988044071981150b07100740045002c104000c18025156008000448a4502c079500004800790f82901c00c025950 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 306651070 1250 306649820 306649829
    0x901060e041e0e0105010906050d2d14010506030c090414010905031309060e010f150516030c03170f130503091c0c0f080c0d050c040e06060a0b070b01090b0d0b01 71
    0x1034841d00f5191100301c091042e50f00501f1200c50810640d4100000141007841801015060841403664035004900c0c2400d0020b00d11880c0d400f6440351200c0d8900071154a0468551240715440c0c00002021814081480700c9101e1004007400300aa6841d50f40200c03100a0000c6c0800b0341d90386811000c00500104024401e0307502c2e02e0b505401c00f91400107841d003900d42a800158002c4504c80041061445841100058404c00c40b01d0366007004413100d0445084c0203003d003d49422038910001420b0540026085050724041d9032402c59507081e04070380c011081c206684080c820f9451074002009000d4800d02401030a10070026680350000540010381c0401c6486034014220703e40810480402c2804140280101448200075a0702803620000d01d480b0115400218001c0c0c01003a510820031409000b00c00c0d0304100107004102e505041c0c00c00c140e5443d002c644403409110710b41c6010801d01030702015111300c44e0b4001581203403030b130030a616000031704060151396422645054020300003038403030090f40d0302a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 306652320 1250 306651070 306651131
    0x503210903071e062a030c08030403030609140403020a030f090302180f06092512020a030507021e0303010b0a0e090103050f0c010c020306040f15060e041103010203060901060e04 78
    0x840d950456440c154484c4e110b0814030031029051215545084400307041c051985002c404500040d0a0642e65400f42413002001e50a000040204140d00756110f1000d03290f084804000c1c0f8074400d80c6102c0c420000351005809a84041114000a8032408000c0340382c030a0740c900204415666400300702c0807582045800c400c80380980c10402040e0b41c40f14000c0c1c2c0701f94116400821400d0001e4480e130b014841c11082650901c2040311140c02c18014040d403080031200b54030466a4810f03803680240208030070740f22000140a020303c803100d4440b03000c3d46001c0c8002d03070001440c0307140d182210010f900c0d03002581220034000c460240b030101303039070b000c80c918025409200500a000ca04c141d406080c000c044d0183c0d41448104200c10000d600c0018815600580c8000c1c00100c2d25007a080a8145568240c0c42d8202076040c0035010070007115455603940034510514101c800e0105030300401d800d034042200c215400c0b4510f030004000c00382c468005106200405040003ca04800b046050110095540b4444e040c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 306653570 1250 306652320 306652349
    0xd020408010e0a150209040b0d050c0111030f12090f01091a07050301140f0f10020d120203161202090613170d02100c0228020102070e01050321090307 66
    0x60603028050022074202080240c8507020265843c8803240c0300050140e4000c0c2c0d03011462a003551507c0e4040b21690314014900310000d612460b0035540c0b40304501d206800101402e01c142c01d0081b000050355061400c5410700c60500c1191050042c03040b1009040c0600f82c07040b0840380c1c15200c0d080c032940c16110300401c01c0c80f201d03c81103002d1a40c1e44034040c2120003000400c00c010410f01d100c107280c03440a080700303da4000544150400280807100c4040300180e201e62083c4031000340e01d0300040c881c1c00c500e05075118648600414180c0300200c8c0011545a01128201c015600d0428414443d140c0101542c41c001418040540040741d0b890308072018003044421034402c140300d80000880c407507040d1600400104145159008000e440f40c0b408000003000c00c1d01d80e0300d400c0e4128000d100800c1d0000201c070b45000c4551404003201641d1103204001e030b015001740c080105900c130301c011004d81a10005001010b048140c28541c84600580400d09117038420140f0684031f02c0d80c2c0a0100c5401080d0252500e041e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 306654676 1106 306653570 306653579
    0x10614040530010f0608030306280810020a03052a03061c0f06110c070b0f12070207031e03080112020d1208041b03030219050f030d0204 60
    0x22100b002c4501928001d01540b10f140d111622074418003d45603078805554513484181c1d00c25421150014610b5002000748215206000003000388080d003039a01da4070715042c0060000c500d1a550380010741e4000c8150f0501600d0b41082c86603440510103042c0e010b407124404800c82442c4403070b040c04000103049995580c408401c4800c031805090304481c4514014014520000c03040710f00500e0f10341c03101000b00c0810160341c0c5403103100004000ca00c0c28900481000e41100030078044804003007012824582042e41028003c0c8580c0c0c001340405130840c580b0f01188000100780f16100071000103c0341c082948003142c103044440c00031705c02098011038008180c0c66414604c019000020000c070709448141e01000c1144980d0146802d020780000c03000289000c10124070010300164403a00407810f5041e000180d80d07003003d00ca00d0482c2c00034028040d890341150040000502080d81c040b40401c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 306474820 306654676 := by
  have h0 := BRFrame.cov_init 306474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 306474820 ≤ n) (h2 : n < 306654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
