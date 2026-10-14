-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2368
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:30:28.741966+00:00
-- url     : https://prove2.me/submissions/e98a20cd-4733-4e27-a741-c221276dc2fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 425719424 ≤ n < 425899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 425720674 1250 425719424 425719433
    0xb0a03080a0f0305150d29040804080d0905011706060f0a0203210601120207020d020411030402180c22050a1805090604031e09150302040504270b13 65
    0xe0400303585107864031184040300340b00050480d10014402016500920b0004259031206110300320050781c0b2402d800c6070080d2407214002581c04e46100c0d094244400401c00c4204244c0038090700803274044208640d03624486802c2610300e103406004103400103c01110045a1241e04182c2c90380084019042518014811a280500364440007074040036a000003900c0c0241c0e08500000a80b90304507560901141c01d068000070114070340248408070381500401c4020944d941c0042190020368024000c0018030108818119140c0044070160300c43c52400d102030360148422508107110f0a2420b506515020003c5070040300658008460055992028000f0030f02d900d42c1d0001d14090300c00c4486501c00303000304841c01016514000c0845100303400c008180300019400c0310006d10b41c2410700509111140d540345080340c0c5060300b98815003030b0440120480050540684c02042510000e070b5060183c4128000d080c1a0081c01d0000b00d4034000c0414802d0010503c018a225005220070b0007021800b501030301c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 425721924 1250 425720674 425720677
    0x80702060d240f0e011505030415050403090e0a0507020d11030403020d08091516030e030309220b0d110d020a08030a03021201060e13020904112a030c0601090b0a0308 73
    0x7000c20101c1c86594240001212095203100500503450b6113842903040080d01780964000c8a07054041c840080080f030200041e800c48440005506c6408116514003070070001c01c0d214540c496118882c05050100c0d201c095280140f030300c2144590000d10205171300c4181107a5401d84a221211103020600c00803005954201da2007000034010751007030740c549180d6020029030402070500404101c6040201d119400b0f40d10070400e00e0140c25040102002c507622000c01d083d4403400b074405600422640740d4864802583c0280800d13061900350421100030b600e4140302c8032400b840b8024000c08004010450f1602d0107090501c0158400b402111400c0d41d110718440c0f5681103410300201190b000320304070b51031401c0307121501c7c0100014544403800604410218000f017030000070300d425080e000201e070700140c1c503079400c41d41c0e107400c90380c1e0510750301c0010f620a8000c400c088201d0101081801080741000107000090b41d52100c0d00380054030859180492040080c22002000b0340c00071200400000800c3e580030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 425723174 1250 425721924 425721971
    0x6061c09140c01091a0f0706050a0504060b040b0a0e0a02040e01080d080a110703200f011b09051e01030b0405040605060111120703081005030d020a060605010309080702060d 76
    0x61100d211148200d81400b0700741c03216a0400c4a40301d0100082d840c100c1c1841c4007281c894250a58600f00a40c4807607240c400c1540c054480b905100c2402176146640d4071961055026103001c00086034600d040205a440078120540d02111040f000c1c081d4104545035a0f400c40c030380341001403a0070342d0b0321220000504268000303002a00503101c1101d0300f03a00914980e0384122040420000100006c0e4001518001c0d014054100007044400e03401c1d12040600160305a1508821643c080d024140a20b0203401070384505404101c075151301401aa00600e002d4059900041c40044c000c1c1c0c010126000e04000c0c0c9800c42d041584844084420b51694401e8900481c02041c01040750b24240300003600a640823480010709a0100b09803c100c80d04520139240803562514001c0115290f403620700c00c00c00b84a420250789801040098510681c0004a0241451003000c0521215543c1d10040d411540522805040c02c801001444014074180c001408140e45041d0b00040c07610f0350381c0341c8005120101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 425724424 1250 425723174 425723183
    0x11209051903080108120d0c02010b0a2601020306010801060f030209131b020a080d0c14031806090307030f03021c0e031308011104050f0109081c09150806061c09 71
    0x10201c10051507400182640580326010090a10080100021600780300e81100011084d9685001001c03040c402c0d0084502c40c2c00c0104854410340d210030100c107420408031906410314802803140d540f108018003c0e2446004140c4400344d050786020030036101c9031034400348282003541c20001c51341d295544030202940501a40e000265041c000001a401c4103034018851056510000004002554400449500b40f401102c089100c2c1c000e03d40a0b074a40c499200300c80b00c0e04901204101405001450740c0300d000c0c0101c0101e07812601c9452416450348250000500001d8030f41c8401003100e800f07500100215403580a400440040007943d000481e03510050810aa400004a51508403141000fa00192981000070040310b050703071044589500c11803081da40074aa80c42c44040701c1c0e81c0121102c01c001d00e51002074400010030310502c002c00d5007883c0c1d40000401c40c602d2012a0000f42c0c0ca405450301c002544401c0440d0311000100191030b0050402c0b14041c01ca6007003c03001c601030500030600c44034401d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 425725674 1250 425724424 425724463
    0x50901021902060405121605031803010b090108070e100e2806121506031a070f140a12060911030108010f0b0603040b060310022d030c0901120905 64
    0x6960840341c0000410703808210f5000c2d00900001c5880401e415000315040101c05960700c10744002c1d11000c01c0c19900141c0f4030b0002003102640000c000300c540c1e0b034154044000300440c101e40020411110402c0c0207181c407580c802c07441440840c82d1046100c1c0c0101c40c4240c1c4540c03080d641c0514004a640403900503903c84518401d62000e07080561101e03882e03001552041c800d280c140783d514003901c150020090201000c4407140401d104065001c2070107103401140502050307883c1312142100060035103a042c00200d408245049441c4a50f103a900b01817140c1580301d10308020048200d810004115206c3c0340a03946810005540000e0310031042010182c0d11074586a62401200b01d0071203000001d122415400c02d8021074196a8220271240d11951040040807030351900e4020038039000601040c045194070000e082c48071000d54020000c070210384044484959024041840614001550044082607061010f22820b42c010002c1e228410b808680004108ac400d880382c51900d0382030301030b0401c1d0140303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 425726924 1250 425725674 425725687
    0x303020307021003110702222c031c0b03010b0604080a03080108070302031c02030f0d0603110d111509101e0905060d0f0b030d03060602010c0c050604020d0c0905090102 74
    0x24400350f05030869180d42000c010002104030b040c801c034828400002e00c10303244013840e991035600c202c020400c50622030004000f125440d0070800c0c803848003030441001072114603103610520341d00003040340c06a07844d44c1e03d142800d10000101002610b40d80c9901945552613800c90300150b120000600020140d4400412b00101681806015840113070480203554100050510240e1400504100c54070f020100e5407004a02400080313095004180701105551000100c5000c000c40c59000352003500d015550103901c4c25418820841181410300f001002d0055140d2018000d1400b452500040c42c1029005890b100842e00028403068051a00d403010807854000e0840c041044074183d40032002d80d041280c502800d140020b00d0f90b02400441c2c298075078840001c48020780440d04009080078002e13007211440b1201c888060003500341070061ba00158a80415080130501c40c2003007150b1550000c011340402d40b910b030248040b407440c86000b5902c0e64460300c00014059030f684140ca00c1925040c00050f182d55 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 425728174 1250 425726924 425726929
    0x40f141006030614010c031407030504060323010e0c090603090105010602120f191214090d0309020d0f140f06010e180d030b0f030327030115090c03090606030302030702 74
    0x42040d0070610805141c60014420b940d46103904401d10102404c00e141e04043c0c81c903007102c0c51050140303a050300c4440800c001c2c00b0580c000025000b0380d011500c00703018941c42c0110300f403d030a50300081011000e80b00b070300401010703440028490300003a191240601e000c0f0b10300301258040d4001d4030f0b5a0340582d952001040816414815100e240744080d07501ca251641405801885d401391301142500c00018540c0c40350b01d540144e856005460400e00c041c0400c0c4602c2c0101e0814240c102c8203400703940520014140d040e486441040096640103060b542c00f0001c5031075026946e0501c60040310809101c503c004003c0c8020001000e00d0602080100a01c1d81841e080110307c0d6030280060712103002c3c00c440c3d04940031010132041040b800ba07240020303808071450002002c0d120341c4413050740c1500000806010304002c851a40c030303c00c0044d0824000f030036000010705007221441550140b06102ca02011300c01c00e803003500074151207a072502c4c001c00e0341c80680e124003040b84d440354000c501582c8005140000c50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 425729424 1250 425728174 425728201
    0xa0e01050a080304030206180d12021b100203040b03040c0509090303041101050a050301060f09170c01031b02030f071712061c0308010b070c03082b0623040f14 70
    0x2403002c1c0000e141440d255602003090390003111582c01c044040f000346107007240c8640b496100c0443e0851500d0004043c0500e0181d1505010114841406045030101e49103041c0a0200e40f1804440c0d0f00941c600381c5081d40b6070084e034002600031101d50840c41e400195950f03034012520300403c2250040c554908003031502a800201d603401d40e6041c454140101c0c10344a0300503056a044401c1401d100e140c42407002e0045551900e41c0e040001c41039909000c2070b500210025065500d5072003a20100201042e12600c4480f001e403685441c0e0040e8000c0045441e440740c40b0020300070700c5103c2d4a5016803c05540508070aa0b0170080700308010744a00410840d5600e8005000800c81140000c0c18140e00c542341c40040580700c0501408680e80400121071041189000281c80111b4016010540310103000c4c4501d6003800c00004d0000d444005507812480350100d9105281c2150280c1e60011540410206803803080300809000710380c802d0b41d0b80c03243c4030100810701800b8100354a101c3c0c2d0365241d20b8032603800c0030030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 425730674 1250 425729424 425729429
    0x601141210050106020d0215130605060301020705120a030c0908030318100e03180105030f0403033b06180705040b04060801022a07030b060f0a150210060e22020102010b0a0e01050a 79
    0x5186400c040c00808031701000f149c2201070300801c0115440c2d07200c07808240a486407234001000c62049543c0c1a104035180380c0075007640c0405036020b024401000408070340d16500d500400070141c10400c00314650040ba520302040240e4028113a07400445102241d0341182c0020503c910550400101c00c00468940816904652800d007821415403c002c1b01c2500c44a80c001c0004061650b02c003070403071254032500504190740c0c5900314940c0682003140c41b07146a00000542044040c81842c001c10611070800f41c00f10b042600740c2e0001d2000ca85030404000143c003e00c913465410580c0d500e0f0200e0122420700041c20742007001843c4080c442d031408002a005200f085010350560000d09040c800145d4442c4141d82201303007166800c0007500200700050301c03007031250311001600395501c506002c0e00d500401d015162a5180d0b104200c1e0607510104001c2002c81201d880d0030304540c06400380c80004d440395555401d00c0c01072000181d0800540041030781052160420480403608034010400d41c601050078002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 425731924 1250 425730674 425730703
    0x10905091b13150f082b0e030705040e0c1e0d0303090230101104140406050307030c03031403280905011802120307020f090c091509030f0601141210050106020d02 71
    0x41c0a240704491007400d1140796040c1c02000503c078080b65048e5000c0003105d02411001b0000c02c461180d00300c0b4613682e20410b0074002c3c041d000c2c4074034003081d2900380b040680c5200c602070600780c0018110703503049000703007c040e00072603120346c0d10b0128000d0050080000c6040301040c000c810f980700a50302d150b5141844042031b03d0401420096801e41c4505d000701560200e070700d500c2641c28058041c200180140007190405034252044d0f4000200f0300c0114210801180c0c02504c410320020f0190302c031760440344400c41d20f10f000062403000085c00d812140d074600c0c40c49003040d6800251200c0070342d90242075401090054a02800c039849030380c154540b000840340340440c103900552415442d0f078085000c1940340d804181c811340c45000042c0821554000311071800380300400007210185148003140c0990050a9524024460f085600e4051500022803e0503103901c045184005403c04041249000e0001d526141c1c03401088006c460500039401120f000c0d1039143c01415160500e20402480e04184044500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 425733174 1250 425731924 425731963
    0x30a0806041a010504090b010908010f06230a06110c130515030105190b1210020d242606010f05040c0207060e060d090206070b010905091b13150f08 65
    0x103440341e1300314084400702c912240300801c0307510780240141c89040d10340c1d002e9000d039402d007221400541c07182d90180040d07130600c0c4809400301002096000380d40a84d4100581c000c005030f8420f12480d80112040b04505451100301d40d1003a0f01003011449623149a40c071001002d0302c0b5000c0c083c01c2e01d9250821584020241d0017000030780f4050b04901d9074084003130a0390040c0c5588000d2000541c40d202214074001c0c61007800c6844001a44602d50029071001e9503034003600e46000c01030748440f401c05e600080009003c00c00f0b886a40c0c180b00e240807110051180c5503601a20040c030038074140406200703090080440100d01140546850f00f40401c4c1c465420300501150400113060018680010880d486010f09030303503164840c00c0c4458144000c00988130060341c040404508007080050036140641038581c0c00ba014003080d01c5285040d50350b401d030719034054030810005450200505085103800060703210f81901103200310b0101034100e001480b0390030880a000e0001000e1040b15000c0051a507015003180e41d24 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 425734424 1250 425733174 425733221
    0xc0f0207090504050c0613050f0604050d0b071b03050403050606060316050a052107030b1e040b0402040f080a0c050a0f180e0106060c140a030e090702030c030a080604 73
    0xa444010900401d084956102c000c00c0138000d041080c2c8103002d401800a03540c03008604209010240c071445180c0c440d903c0025551b4940c1014010785080341c10244c400480740031550750303144039040e00800c4c0f0405c00041a1030080e18140d4440d0220743c1d14000e4941c503039600d0840c1002400c0140082001d405503400700180100040088008400302c415881c02a45492100404031a00e1240703911940b11000101c0510500f903140d8102d49008501c542c0f001c0048072006001d0000d01c40c2d007070030350a140382800c081110403820709805c42203210000500040c035141d2a55103070084e0400300d41040e1016030212142c1020420306200910103040f084803000070003454040e1421102146016580d22100d00d00d504502c90a0340790040030056180e030000b486207684842e0005c0c2000340d4071900f6240314800035410b100030000855280030385a00355443c2192814840144484014082c00e41c0d811884108000c1da107010092001d001030f0307803040c0e8801300d403410110200004d41d00d0040c8008040007441400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 425735674 1250 425734424 425734427
    0x2330f0114010c11030607080f0a0c050924070c170105010f0501210615030c1e051b100b04050105060a08041506080312010608010803031b07170c0106090c0f 69
    0x5200c10030707000d01c0d264a080c500e602e040726030242c0d4078440c0358061251505012845400850440c8509000500075542e65580680d1005484d006508000407030010403245e551410700c1b1020410a24107000940424409081c202645a004002c2a030326411205002d1003040c820600444011401100911582d4104402041018060321a185c144134490601001d003810f288a000c80310707540004108640b039604d0780103400c03010301c0ea03240a00083c03030400c0d131044060040700c41941d2403840704850f42888010070415581a4045800e11507000382440ca006541d03001000020301d00e0659000108180810205000540310180c11051251034144100500b4507442108076034800c0d040190880210780300d03a03800c0700516043d0810f20a40c0000201c0b0307900189250051412110240d0303403200c160381c0c0d0343d403466100c4c0000d50f03449400c4407401c0c80e8240c0c00703945500a085030340e00509451300354a04920b1031100b69800030741d480045945441707007041230740c1c014402c0410b80407460030180c5020180c00c80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 425736924 1250 425735674 425735699
    0xe010b0c060915150a0e0a05010810061a0a200d0201060603060311130f0e0604021207030b0a1e0603050d0905060406090506070c08060f0f250f02330f01 67
    0x51340c0c0460b10b80d0b180304080d84c1d81142003001420029a002e01070b040a01641001d40803d0291404503c61000000b1041c1d110703202c0c2e00215207003428808501086060b154065601208091040210724909134081805c3d0340446030711180e00f0b40090100d01c17820702000e82547d0684d8046414180351110400c01308070094121242110103c80c413902001d0441c0704200140900d00d042e249840c90702143d0101024006089030043d07000302d40300040000c060001c5a940d103114000280400b07240c401241d48914581c0110b14a85a038030b5484902814144645040702c41603403040d11180d2001c201001c40580059081000e017100340c2d02c1e0341c5002d0400502510107240c62090500a43c00011001e0910415415984c003a00d50389003511980d007070001c4808000c180c26200c284405200c0004141c10074100c00078031481403102d4070000903801a090301641c10648050f04001580588500601c03101c0350790f100c5a025980c5401e94000d09801500d5010400f14005c009009080081006000000d228031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 425738174 1250 425736924 425736931
    0x90411101d01031b0c0512040b0406030608030c0706110f150103060e06061507050118031106070504030f030509010c02090c0301180501050618030a080301080606090601020a030807030509070e010b0c060915 90
    0x1085100e204007884d0952811a10b047e0132410120049008207040c05406c0050048a6840d9000d2141545840c0265140e129000b0b849045900006040100c00d0080700084030000f00e98094442c0c10b8140c41c000d0b4103243d2000442d40d225041440144100010362180701283c4100f44014031b4075117002401b144480050300c0b24001043c8004c1210300070020709420040461114240768081303101545005085040c3c1d40b001041035000c0c0c0350015580c3c40c461007d4070200c0e1b81000711300c07154244940b000da6181e440140f40034100181c4100900240e00d8040300f0500504041c06655134961401c200c680e444501e8041c010360080c103002c01042aa0b807180299010701311b0341c0038a4586032082d10b00003803501c1122000201103140102c000128a0310101d501ca105890a8548507401d541d403400480c1ca0310120341e00140030840240c08215001d200391701169200c0344203421030740d090340c03240ba4220842609038000103400340300107060b81031440280b00ca10380101040d40107010640017030b07210781440c05005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 425739424 1250 425738174 425738177
    0x4051302090d170d180221060411131b0807020705010207090f0219020c090606031306111b030403020325090e030f1602010f05031302090411101d01031b 67
    0x1d83c46054016142400c461400303400100030011220100f802000a4488240c103a03c00c0c4200c2c000e0303141c106d2403d035402c0300d03162080001e444903980700d65a41780d03840d4401c207546e60042b01c030046014800040e449000c140301c80a00c0007c40820394514001c01404006140300f0464101034010000c99030002aa4020303903402d000b0214041030101500d9009000c0e039034901241401e5010f9101c0740980205910119860580344054141d884005019641c4019101041169075100102012a0070365000c0e4205452101180b0f103040b400503901c049000304c008240072203420019080086140030007002c402c00c1c8072101200b40d44404030780078440390055031107124032039520307803184955015042c02190103000148180c1525003007200c802c807005414400302240440d00030011860703820300407400d89210300c0350052100c40c120340950031710901690280003141e80402003082403c80755038184c590701c0840000c2d84c82c248034401444614028a054108450506150100b0100072810300d464078800030003607 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 425740674 1250 425739424 425739443
    0x51002160b0c0d0509121501031b0e0c133b010506090d030905180109050f0610050d1e1b0302030408190c050703050303060102011d071203050d090804051302090d 71
    0x341710118107814119940710138035003c0c00e40c05064007041c10031402d060300d000b002d810b071181003005030007034901c0024001c5032079081c4e0a00004075000c1060380188850043c16002c0081603907a0316600582c80c2c1e08520700c040035002c255803001d04645c00700d845844800049c3c0030f0f411a5250802240f100d1103820701c43c0740078481c3c1d149403a040c0350040314070000400005c2c00e180c03c03400501c004a007a084003070255070a42400c3c517010070703017944030800078030701940f4020b02100710721250007419031701c03075011001e80042107850f18590101010f250321851a10200b180b80403859001804484965101c1202c0c80401e042c81801844041035596042d5a041c0d2904c50b94820b015a509070240e8105502c1a4014214400c2c40c40c08410414088091400394000382c000340503800c040e546000c250009484442c030a036000d40c0c030800c192403410301c00c0e0a14070b0103414501e1516850717130f15000075249403240a0f5102e00e40041c0800180c107154085030450790f44c61000310f0a026514001418000f102240a031007141e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 425741924 1250 425740674 425740687
    0x4030809060f0307170603010915020c0111030114030f070609030f06020904020a0903050606060a230c0a0b011517070c14191a07120213051002160b0c0d05 68
    0x101e8204840003852030605880c2c8034541004018444421030050200441d189004614542414060b1301c0b46c5960202c4040100d0703080803040382c000d41109404428640d00c468400c5c180c1c1d100b000065001e05000c1c50b070a01c5c90500311f0141450803500e14005012030748001000c1001c0b65012071003005072540007450b4200c030161418403001138010100110340c000d1000035080c000d42e0704000b240045074454020340f010780e550001004070501440c90000f000c03507000780c80300710074200c1d008074506184181c850f200d0070100e0859109107403440300d0303600301c425801400050022000c121564104045945494101c015101d0000048080c8c00b503c1d500c24006000c50410812000e20701022000e000d000480b10340078616501c400e99a5000841994180180680d4058261001880070b10402c02038071a985140403220200000307500c400f441e0b0710b41c0303000a10007040783ea507403c040028000070755004080030000540841104812076100b249155030030001d00b054204041641c800ea1a0740f03040c0a0384441d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 425743174 1250 425741924 425741929
    0x607080a11040306290f0102030d09060e0a0b07140304080f09030703080c030a08010b03130f0c080a06060501080a060f060e010c0c03081b01060609030b07030905300f04030809 77
    0x42e81d08001c0800d030400c5601e03404154156500015150902c092141c41141038082c040c0300005415020f0044e0010050001000b026070070042d0410311900300000da08222400c1076060000580d07080b9102d894070b6080c00310f0694040304040120350450f038620314506095548480f51300c50440241c50700c210106807200e26542c103024800c01940c1145c0003c0d61024000882c40d1684e10070404400421080c00000c5154102070007600c0c450303058428404060103030307a141c4603400c0b4884001141c038940d01e8140800c51980074821291002d20840020640508090024010410082c001c001962800c9401c200303507510501800100d80c05418043e4080300d040d0012100103005680140070100704c1f5600100b00801c81e40180345119841d8060a142d01e400010903090782c1c3c0703d00c17422000402c200310910110364901c0c600e03500540107060014440005544035401e00700c0b00c1808054a08040c191214101c21a0200054202001000c645090b064404c5001280144d001c080c09080020402d2581034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 425744424 1250 425743174 425743177
    0x903090d0633090212060603060d0f08040501110d020714040204032306010506120406020f0d05040b060306010b070302031c060b0f13090903050d0507030f110306120607080a11 77
    0x80e16201c0160840b01c0c203201e0b034048900b4103058104203200d14031800299110891080d60b00a05ca0701d500311000d5222241003261940024100039031150f01d500100b00001d1800e809409040d1045010070b440c0c619000000d130440c03201c0c50707500b50740d50000921000d00942c041071290a48104803040418a9601d1001c03c0003402280c1008044940f41402c03513280e0000744402d400760710032090843d17409030707240c5090101e98001c0c00c030402c120306074420111700000c019401400800707800205840c286a104600c8005840040d102a2902c4c1c840c070b402d0100b141014428180500005844242340c4004c0303a5000399680b0a400c215200550401c0d03640e140e01e04140c0120b40244000043e09407109510402c0d11101c0d8400103103c10800782c552000500320b0202c1c082e480c409a091344840b41005074045800e4003404006200d03404040d81e4514103420035001f84613002d1459100c013640c2d41c40f841c0c042c00348403608440b010111001d0f4400020004095841180075030301511500000c9040114880a03410b01e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 425745674 1250 425744424 425744441
    0x2071b1d061c03111f0e010506010201020c19020105090d060b0f010302030c120c0c01090b01060f020d120c03110409020a08060d021507080706020a0507050c0111062d070519080903090d06 82
    0x2030960004003840319005582040c030f4a1b0341484d00030005500c130388005a08074400d414010403260090007541d84030112104d000021907006041031131074640b0200c00100341c0900000704a44095440d9a510718074101002e800030201004c0c201107196090464403a1901e0184ae1400b59058440000242109071054155183c8002c080c0007030022140f18034140c0444013090113584000b5011901304103200d80700241000350200541c440104003800c1e030100310007904001000c2d000b4140c84000344407000391070000500003000601d030010380316808207000802ca80c1d0050100c0d4400e41e00410681c0250740d9100c41d0b440341d280f261413030a659140341d1034089441d0164002c06040e40c1e1000c61000c525581100040540c43c0c0318405031030700c0e0350310580190307141c03040460500c0386540a080020b144100c0c2ca800034040e00054844170356100101d9007450041c0100701d507448006a0003140c02040160000c080c4180d103031082c1024007007484e0421000f9501e005405600713201d0304420458005000709a40003885 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 425746924 1250 425745674 425745703
    0x4091e0f02090702300a030f09050a050f070501030e0c060912071d09030c061503031c1d070e06090406060e09060615040e0a02071b1d061c0311 63
    0x711842c3c84000030351a0080103a951600c0701800f01204903103550000b0000284011510f61420000028011002001c0202c00c1600c099514603412000c9041000000b0301227200c2d40041c0a510b07246200c0a003440c5003030780040d06150815810450f81c0001248000307908000395001620791a00c0310000760300300c0020030740004e5801a442c0115142c1c440208550900061144000d01c68807001e18203903403841010542003da8001401081017403008001003014120001c0840307043c0700e84104010300f980499001c00040c0c55640c035103201c00069002403903140300230030307000307803249a24004c012106144001d1440c0d105425920000741003000a50001c0d010b07001030704a5809601c1c042883c0d942d610b90940d0914031804c0100d01e42c9070711a17103810071a001d0710300078426580e00380ca940c503202029403c0000c04032010442c4100c1e8021520700a1a003c3c010004030070a50610783c62601405c1d00000301400850040403016940c410f1124040002e4040647c54909400f49100103d501c1e81090b802e1320441d034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 425748174 1250 425746924 425746939
    0x30403080a0905190e06011704060908091314011e06080c070804120b15030a14011b021c0e060a0507060b090c120a0c0806010c030908070909050c04091e0f02 69
    0x21300e810341103c0316806a80c820503034039142c0d4035210f00659081c40c10002c00300c0d14802a20010300000c5941e00300c3d80005208464250800210400180441c0d0321700b015108450364032920056665441c1840c5801085051107020402e030905541e040300c100540618010701c0000c002041e81003080404503203410760450000c2c2d888503241c12a8102c050704048027503414021107004104100c501e0241e5035680c0e080100240304028940d6110305205100e00c0602e0b580d55a500d1003101d81002c3d040c0b4000203505541c0c090050800c010310845107020b2640d2544003040703100c0c80391282c00e854040c210b980290141c10019190000c80c903285001d0000c049240d81c02103000c3c2d0501070a548090040c0c900380ca014013914130380d07545d401032100c120384684c00741c0d100003008000401c03d554020f248441f015402803604200941d16010a01c1c94421a0340c00707444030540c0e603040c41050080502c015059458116010b001082541d10b400c502c10b003081c1101c240c0703140041c03480301c2080114407042100704c0e4050301d0311 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 425749424 1250 425748174 425748199
    0x61d060a0309061401080d0e0303070f0b090f01110405011d04090305180607020d0624030b040201200604020f01020114040b01030516150c17340302030403080a0905 72
    0x5000d0b242102045603550b0814203120828088001d0391410384981d400100b2281039400c400321245031000950302d8141c0001c000c1003000c036801041c903a40f000d00034084032440e818000740d403614290307142d103800c0c0c4143d00d005842c03142e6001601c2124201c0701c0901e0813858006801082041240750202c00c0e81d406440e140f00401090380000c050b10000c4e0340240c03248042d20280c01032000c0340c1b0524000039808080032400d80c1c0081e02542c0107007405074924810803c1000703001400b007503142c2c3e83d820580342075820000b04400c56074428240c1049901d05a48064060080d1088640c1c401010300024494021504000300c0b5134801d6214111000800c0c0000c2e541c0d040904025920f000c080c0000e681034080d440144120304042074204c0b044035001c401501440742550390442c2c51491507041110185640c8074038038544291680a4404011030104014000402102851207035036422001c3e2050060102c00002207900401510100c070380010002e981c0301000a400c40710b01200d5004281c0c8911580c001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 425750674 1250 425749424 425749427
    0xa090617161725020d0203040e2806090c0906020613050120090f0d03050a03230109051503070819140f0a03030b0906060304060e070306110d1d07061d060a 68
    0x402a10f403001c8188600702e280c10700807038951000c91464030159108110400450a540250136405913482c3c1c907a50400580f682c02204540d4100c1084c80c1098403010240001e4141d407185d016803501c0c9081c907810b83c62610070084e4841c00000c002c0c0e862030060700100070a100c02900420503048d00e6001d00019460402c3c00070001d5040b4080380c03400740c4180280305545051401a8411a68041d15201d0400c40c90325800c0303000d0424040f02d40004252503000624103580081a5400b80050000104031840d000081c0301d801c2d0020390803d8826031044604004000c00811140700259448000382e00924990914140c5407110340080341031840b400c5d901c100c0100000c45c001001d94481d9900b400301103400410017030180c1003500c3d01e81e03100f035080002ca80015040e41c04504101c00350410f5404103540c23030301c44108032645462040ca11010010306014920703800e218007c0f210040c00c1d207140707000c0103454446a8a0005001d00c2061080740e9aa0b51064501d0007180418441d004001f1991800f04000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 425751924 1250 425750674 425750701
    0x40e0402040b0f0a151407051e03040801090c0608090601031205070224030105011e140918070e030f010e0322080604060609050705090102100b0409060509030a0906171617 75
    0x400d40d001841e204002c1c0d500101d46d5085441840d0000001c0122512006180840120038022000c0a100801000680110038083e22080600404126905a2410710081c051200041020040c1e030091030062000440c0141500d0903940e0518102c0d4440b509807020440703012840000c1016000010900d0003110f07a07500045040c0c601c01c0e80e074540c43c42d058854880c0f41c403028184103800f00b1000c00d010011000c0903000b410080c00d000309409008a080300700d05410f542c083d01c0c0a0b000480300105205681420000c01039403000007c000c0107203020b041c01c1039031640203d080f400305054031545200c81d18a411b410001c003500000056840508140c038100d0001c002030720a40b518a070030300300003801107401501695010b04060f00500f06001154000320f004100761050740d03604c01c0d55402204e01080d158454140714000540056682d5100030030040e0035541039512002c20001e000d542e00358102c0c03503000c00b80d401c01d106800d240d0010f0200b0009840d00c114034486090041d03070380c0b010021030519401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 425753174 1250 425751924 425751959
    0x305030d06050117090a0f020d060e0d030b010926120a0e1008091c27050901050402041a070303140f0f06091018020702040204030b0a0b0402040e0402040b0f0a 70
    0xc81300c000d214100e54000e1440c60049171030b22443c0d0800400100851121094100e40d1880141844a0001d09589810440f1012483d08400394030a0416180c21501413041a6846030f013420301c1340941e880c1212141c418140c0f502075010480c1c0300281c05801503400c200c00610290324150564846203240f0b0300400e480c1c2c13054000c0b8400e00c01110844100c42c081c018171405401c1c444081d20a100041c1c8050142001d82c610320000c01046c500107409a280d40c1c1c1c540e0505c0d8050000c090b03006464141040003440040c4c01c4544503500c100f2040100c4103100d44e502c540c1c1103043c00c086c2c5d182c03006414207400926111100c00b24400400b0200302203860141e501510400b2080080b100f15120f820503c1030240c03041300c11000041c0000c00c24046280c0a0b00003000c0d4106860001d4500b9525034041f0b01070f6007043e841150712000c50414070a604030240609615014242e40031400c15180800c2096a43d00c043c0000c0c0c0907907035808280c51117495154030a00cd444002c0c0049550507542c49600030700d2178102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 425754424 1250 425753174 425753177
    0x30305120a06050609100c0506072007050603010510140f07121e030e0a02031c09080d020a110112060807050a050d080702190f1d010b0703120b0103060305030d060501 73
    0x28030018031450800d100d2041580d2020f00500e0070101c000d0f0a011004000c417525034140420b00e61450b00051041103050310800302655003060b440b5803820000b42c0e000c03004040800340d03000704405010329101c24058030b044a070210750002c0c403001c40e0304040d11604c180c0c2100051302000042e0620012039840001e1280d18401c46416410141c94802195902407407940c40203007442104041074414443d40020310f51100410a44030000c3c500d90000b49002c1d1141080c528100f01100e040e00f0301c03a000500c180040c11200b004d04102030108200a440d19014000248070010300c1c0c401d510580d10581030807842c40c90b241030400c01d4075240d046c8956107800510840340700f48074031a0f01050703d003001420214410781c05098182020141c3e400c102d1a10007200f01c045584040902c0003443c42c2840404000510040c8464107003000035400030b0009442c142c01003102020104210400a507000200400501013503c00040680107800120702400c555030000c0c01e14400403894850f481e400303030700c07800840300c09 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 425755674 1250 425754424 425754457
    0x8040803130e1303120b0a140301270201260907080f0102040501051209120706020405030712150f1e1407140a0507031b03261b0d0e07030305 62
    0x120b50034000c1c0740d2001c49000a1180b0048a01c00009005002d01c4810f0b01c084400843c45514900200c5c03000402580a18040813405800080900b0284035003114003440010900382d81c4d9118500346a28026004024108140030082000021405021458070005402c542c261800c04810b45079423038886008010043c00f442054242c0100148200d904a84045e140d00c0d041030110b00410310318240040401c4414050180407185040f0300c0e01c018144948158401030702e86061406041ca846604d03003112084540d07848a54000c0342d800030000c201d00094050101e0280d40e9401e55001a000802000074640008441107280b445150052b10503402d0000c9104030698901a0490301410200710005031182e041083d0030030349208a005203000e034081e007000300300081000888650080b5151041e000551074116280c03000c900d00b10821800550520084220f043c003c000e44000c0201c5100002d40b54400074a02100c04207503004202401c504200351403610b0396a04000e0016801048132100c43c410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 425756924 1250 425755674 425755679
    0xf12050705061005100c06091e060f060e0a05180f01060810200336060a1e0b011206060305060901060903030909020a030209030607050c0c09090a0807020d0804080313 73
    0x3140403c0904445009108519100c05002d0503641c0c01c0381c54809035004c84c0c9504040000c18054103c01c14810390384001004d05e401c80c3c1c24018112001800700301000c42c03c2c800c080060103d003814030750300b1030040f01c000501c50b00e032100712401c4415034080300101401070a180d00c070004010750140c03044070141d8090703613607488035000400119070b050f4041c01d03c10341d0080d201041d000818000b450380148144034104402ca6855004002500e0010b00060704c2031021603504100c19061040c10b8000062001c140850b08440000200708030350540a8400c15680d01c0100309268400d0118071070a1a20366001c001c0540c4440c0010050441100c02e00d010b181c1c0d00000040c410720500c40a400c4a4042d9559410142010b004201940c0141703208420180c0030b110790360040d5001d03c0400c0c065038054850a0340c525228080f82c6c20910111245841401030b013040002c40740010641807180e5900040f519a5440c0f248001402148410006001030382e01003400700d558a0004000c010310f05c15120840e02803903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 425758174 1250 425756924 425756941
    0xf0a08311e060804080f130b0d0209100512040b0a0605060d0f0b030a05100b060426160f051318050f07171e12070b01050909060907030f0f1205070506 66
    0x3c055030000d102080130402d440c040440d010142c410394901c9090303035034410303903c480c0302c6140d4003c1e500d450200c50380044c1621951910042c12034500d116410308d541009906051018242340040020302446002c4d030000e55403001d00d5000102a0000030310403138403501140a100b00400a821498040f40d203484002080e600e0300056900d0440c1e4480003c0c021003000f15410805425003219a80c1c00000600c0049580100040d04854030701c1101d0f001310700000c070f28401901d840c00c2200030255003030780c2000510421079607580320b10a443c0c06403010319810400c8611040100410b08544801d090f9601e80c01080040100702c000700d1900140455000d1520f98500e2043e0329904081003c4070303030120880c40c9040c40c81182c0031401900441c1582c4200d1250404c10300d003540124000c640d210103c1c0014041403a0842540350841d846400600c501d14044071940d6480ca0b183c040540f02410900c90722040003403070104040000d51080303003086140e80b40100581140c100c20000c484030700444001038601e5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 425759424 1250 425758174 425758187
    0x1908011508060312090f0a03060f0f02090d0803091e0d030b04110406110a060c030c0315050109061202250210170627090705030f0a08311e06 62
    0x1203030024058584c4910700a09488a0350014502c0c3c1d402400703143c0c402d0840c1c0c1d2440c80d0340c07000358043c0c1004144003039550700080858111412440c0700174814803407101c480c0c0314100c1e901d81a50303205185551740c4d00c1d500c1407285060100540d00421200d9404201c0d09000c0c0800c2880002d0f150341c0b014003c14280c7e404000c16030345200c040c060407210900c02002000c0c49011069a400944401e40c0c600304001c1d12600c05640002003a0303401300f40c442c0c1c2d9610300164540f04032801071030070414240d802804e0000080c4114218410981002800c44e15414465415030403034210718640c4018949030780c81e800c0b01c0c0d400c0880421040c0d1241410600203424103001d1003144041a0340706c44021203036640d010070001800c00041050181c41c05051000c000b02d00400c00c0c15000f042d0300002401824602001c1516190b1806c100030740c142c20918500b00010083c0342034801000d600c0e103407600d21a10380c010045075580540040c440d010585900011110300c04000b0400390700c1c070284407011464840c08180d528 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 425760674 1250 425759424 425759431
    0x70501021e04150206073e0d0e060702030d0e0a09020a080601030c0e030c090a0f0608010e070f0602150c0c061e0109020c1009051603080d05010f2403021908011508 72
    0x4512004400c850b042031180311207c440c0d0741090a0a810149200c08103100c42501074800d4035640030702090411150030482011007184200c1d1801c0c40c3c84910741c0443e0311451407021040030300044c1c1d4090030503a03030f8080c0e146c40680302d1000d0440d00d5000c00c5400500618081c0c8101340460310300801c151003240309000d0107803400720180c01800303200344440601c40000401440c2022690b0740b0018503842c0c504600807600100800d01c000b003800710389600b00c98100072a9a000c200000310190701040543c1d00415003860841400d003c12056a403012210001480f60740c103a040c031800f0360810482c07c0700000c50216040003507195442c07000ea1301c4034002000c07071066141066456111104021a1850390740190b40390500c0f0700256138030350a4440800038160056002107c0360580414560f00d201e090703200d401c1c01030110341004141c1d9458a0f40c0030340c0b030329484020040381049403100c004101b030103038040300c41034101000321100c00422103500600021007801a60002126400110f08040c0326940c032501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 425761924 1250 425760674 425760677
    0x30f10050f090907170f15040b0a0506030703060e030318030414130902090903121006091415030a0902120102030c090d1a040f2f0105070501021e0415020607 69
    0x607150310303100c20018001c03002090050f0922410801007000d107420741d00d81d0300040454004103254468044d140d4142420340c0298100d400c820300400012400d26032034a07401c26680003002600e5100c24001c2824050709d500042c10013420684441101070002005510030f94440040e1b03a45d401754580781588902ca68851002011075241c0d50120b00e01d060004d003000c1c80030b2801c0010b4014030503404540003007011581d07604190030220b8103840d403040203040e0540c00303c225501481e5060500d40090209841070240349804880d000d807090050301c2c1d400e82d4151107101c032428140c40c0d00c1c140391194064402c03004101e002c0e5a184103405650303441402924040e80300101d0107810282480d0070b10402555000c0c00b9981c2c808095030780826005802101802103002c1c40a200120155080200030309480100343c04240000100d5206c0358003010204410218003403078504c0d17440f50f0500345540640152043c16880d0b158052041d0748401e40100248100c3c5c0b0702c00c02c0303001c0110f403195040e80c40300d800710343c40310 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 425763174 1250 425761924 425761939
    0x7080307120c0c0201050f0a23030609100e0f04060e150615070b0105090405100606020d0e0306090c010e0607060e070305010c05181c08070f110307050d0210020a0b0c030f1005 77
    0x110000d80c000906003442d100e151212600c42c41d5041001142102414052740701030020901c440c0e4140740105607840500b82c840411407610301450510144801080e00e6503e15a080114003048a02c0e040030038a90f08100c1150072000e141c096280010400340d80c01d6205000d0428007510501d80c500c250307076079640c0180348408a603180c4001d2111189005204451600500c442022a0540e61150030b0103800285d000f0424504102006003400d58a40f08652180e445403041101074480040c03e1112400e082ca0410002820f120100f070940c094180c0050010b8200829000c403050005401e00899005000a00644100da0820744491041481c500b010300341400312000d0a060207052415403150401800040300d01a499190343c41c1c20030b4034101c548018082c665000d21040d040c030b0310410300c0c0440240c400c141c6844000740d075246400500a0080d40e80c0c00c0c514010a00910420207204d82082c0000200c0c600020403404560045858009543c408004510551190b02084082d201e0140c0040b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 425764424 1250 425763174 425763187
    0x1b12030f091505090a0f050304090c0309020904110402040503070801050f130302150702150a020307110c100311070501060618080c01082e1e0504050601050304150207080307120c0c020105 82
    0x42c80548001048a20503104241e60300001410890b0900e404e01e0044019644807420540102d0a807114420008101801c1841c40c13805030344da5403425900150f100d0103082d19030140c00c01080c00ba0080754000d942c1400307000300003d0351240c10f400c26480b6441c2068000100e41d00c03200240303240307465540c0280041c3c1c0802d19800388080303016100d50f0040e69034011185c0c40d0f0b40024000c452440100d03070822142ea000b100b802100344d08266100000103440c4098a040b40c4d5613008520804205150f40081603100d4628840000c403650840c1c00442d0004000e00c41143c03500e0b0060590021a0090b01891000c03080020b903c400209030741d003100c0d105a45022164990300300d060045640c071400680000b052422842142411140761390040911980284001c41c51042008880c101079008d280603908203c10014640c0e4440c00b01e940c015440800030f0030740d05207810307140024050100700600d0010b0000900c415250051182e50307044120540900104040d507904950000c69108001e002c68001d1084 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 425765674 1250 425764424 425764463
    0xb030c030705070b010306090b09120a0c0303110a0305190c051206030c180105010f020114460c1d041d0604060e0111130e071b12030f09 60
    0x45030400c60794a0302505000e03864540d12480701e000e07031045442d590390b540d00c0020800700c03451003603000280601070a00b422140c11000c4261051103492010080011098410140a0340c801802c1300085000b064075428009009002040305881d040445840749088030203042c0c00d40a9030000c26159074a40d41030001307006c90b8041515000e00070b6641801110119141c81e00c0d200c007468001961035503a84c8255140030005040c95510840700d00031a41010007450003056090185038101c000340f0125283c0c19122080c0625011138820b0314440702c4c405044204040e0600320408552403010301040040764a03500d003c1c0c0301100104002d61001810b00c07503840640c0b41903032000c0c0c0c80c400c0103800d0805004024483c80e0501c1c6003214100c078180d58458030a082f0b010240710702d900c0704041c0444649890313900d0141c0c070308028041c821a107074200e00100080b90300f0702c210700740d02d10360030340794403003940458185008002103504043e9440001e02c0c0c0518410160198059140c1894001c2e852100341e00b4000d15 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 425766924 1250 425765674 425765677
    0x90f080c09011707061d03060a0b010e040b010c1209170f070b09010e010e0f030f1b10051209030f0a031a1e120c210c030601030213021e130501080109060b030c 70
    0x1d412244000403018a400c3c7c0d101072160364421031942d8000100500315400140c9103a4503259910b0140d032400380c444a6507600020140d5950703800c642c0c42c081050350b00a003240e03422580c0d007011080c000985440d1050500c0058841d4100e100c0c102900e1007541c03501c490300628090150360790f0000e088401e20054030f5000388103000d842030014028802a00480010070b2034420034545650295000d00d424500025900ca0040070340c8804549000c280d901740c0768010110301800c2c02680c420354617403001c100c80300f001b08222031410f42c0d02c082003500c0d1448100054020700c004c482c958101c04a2075140811890709850482c2212080103612640042e43e00a0282c0310402e0740c41d100b0503118212800c84a980c815081a01c0f592600a040e02c01201c0a41510b08144040c00f0090182d800900180f00603984c4190030350a524440c24010307103c00c59103005d00f01d0342e4944484034420309000030701e0910205102c48500141c1e2002e88a0301d200781d036141111012183c052044890000e014000714001a01200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 425768174 1250 425766924 425766947
    0x11240307020a061e050f15060d0204030501090c03120810150509040f0203011701060303050306040b030c21010c05270a0b0d093807090f080c0901170706 67
    0x104071120030007196115411155051042e00011a01c0c10303416406683c40d003d172651000c040c06c0004105c0c10402d04083e5401e01f0703070746614032078500443c01c0540c8454030340c10390b002181c015000380001203144c1030400d4140c0081c0400c0c2ea0700b83d0847e50940d84640194142d50103242132030b840010701842d0030050504a880c003240002005020000c108842da500c1c0070301d6401d40144400180c0c1d0354500584c00150000c0001640500c0c0d040000810100750804252540b1440980300400d500c1d00701d000282c103003c590302040741d200f101350903012003070303594a02414134110765000200701c80030368903605440b68020300c00000700603202005800c02103055002c409240c0f040140c14001c2440c4c907181188811b0b0000c41c94404010b0381c0d40148018040303081c4c00403018215841c0041c070480b11010300810460b012040c070303441c04040e850114207110700c1015030ba0010654241051695a110203d2507140e000104015114100c98800400d4482c29840710280c000c110780c0003002d807189000d07001c1e07850a0509 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 425769424 1250 425768174 425768177
    0x6070503090102070b09100b010c1104020306131b110c0604050d03020c0d080d0b09040201080a0504020a0503031c0606050f2502040e010203070801170a020409080714070311240307 79
    0x4d01450340041c8401c0e00c001d02400f801070203042101e240040000071620b0410f010350402411044940208111580e108800082a4ad001da5030f5a207200114594250748442c0e05541c6160104a420f46001c1032109941d10f4503555540150286003078145130b540340601900742c0c0c488802c01042085180c90000200b0f90b40c801d006592204c09900d0000345101d0250400382c910700750018110341240518030514080403000c0310700c03240c03d007001d80000342680340080030502100d0340c51011030203540d03d81d842400201001801c41390b8644811041460f010b401000e64003030070341413800c0460818000c00603110b8940c0c40341e0b5200d0825003945c14038440306c44c510405000c0121000e6003030380942c13a03d0140320303003080807100090b0381c0e814100c0005000b1001644042035210740c101c002c135107400c80440d00c0c010180c4c0441c2c010401516500b00340c1201c3c8a205030083c55845035108000f2109404510201164004c2c080d49107110203103018444440000528074013005000e5810045034580740018540101c101d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 425770674 1250 425769424 425769427
    0x170f040b0304020a03021917280606090c0903110a0302030d0c060b0a03082a0d0c03031409010e2506200706050912070b0702040519050a0f0507050c06070503090102 72
    0x141d40208146607240500034040d00c1c680102402303481c0e01340c51030604400c0800d000302407130034500802c0d070300b00b072080c09201e04540304900d0703508203011568000102818500d001048903400c50400a01200c401c2d10084900c42011800c803880780c0780010101040700e130080d024240b40b40080004072031080d80f20b88112030180c1d50788942c0f1902d44400c030000c00034601c01c4a11990b50304d20002d104464458000d0041d240e403010402ca164000703400700342c0c50705c0c1820908140b650791100d441c06802804d0951141840b02c401c100c10006000d905420818503c1e8000e015503000381c0038003000031071561801c2d4001282d03c1d9000e40c108100c3e403080944808107030324ac0380c110383c0b18901c0075406424841c0991111002074004120340055242400c01e0270021004403004040040c5041084d84050084480192040e652a000a202c110074000c0484406032043d81c10004e0b40b40c041c01c07420041c074031007420b00401460800003030030041c0036400321002c9400a0740107168541d150082151907078402880e14a49540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 425771924 1250 425770674 425770679
    0x1403010f09021605100f06080a02010f0305090723090609040b04082b20090102060420030f0d080109020909040f0303111b0c2d03011d0a170f040b0304020a 68
    0x103009000c086101c11101145401c803031000131b02500e0b550381090405820441c0c1500050388c00a400304003181e0b8601307020030580d903034107412420300202d988284452000711348403000030300701501540000380040f94804059124101800010b00044400400f180803800205020030500300140c0380720560300140054242040740b0051031000310440134804141c40b000c64070868004d0b1940704c680c0511602015040000280c0005d55a10000e00090207400d070202001c208101c44250591101c3c03000740440e0010512110701c0c2e581c9443e410840f000003070b002000402e4400090080f02d00340d04006225083c82d840700c1c0c680700301242d0124400c9007030540e103145507000069000041c007550301300d0700096680242c0030498981802e140d042214400c00c0c498204140e40c00d040490301d00c01151126082d0144031051000c2401092109011800ca21007584450420b41c000a800014148240c1821050480190082d403050023050000c6040c0c00040c401841014411000755901a0000340401040365 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 425773174 1250 425771924 425771933
    0xa051510031103070906030f020306280515060406050a030b0a0f0504050910061e0e060105041214011103061906021f06031406060907170c2b0c1403010f090216 70
    0x641e47d030b1084911201e5101b504003546000c0c005140e00584030124641d20b030104503049108185003600007000107643c1d5000c07a0b028003000000305456400505016580c2d902c0c2d00000c1d00d0768101c00406800070f810b0041c0f0807550704000c140101240c50f100089000503080000300006440c00500568040c07042e440d0441c5000010b000d040003d2030b1351101816136010076600651780d030300039402c41f00021040c0340c1484600c0e42d110044804942e20340003940f0090301c0d1890600002c080c1c03d0306000d031a600341100e5803d000c0c46800114011801121100030b800d100484400d0281d03118072850b0003581050110380c03041f80c0c051042181c0c035a00f50350000784080d03c1c0d0780c9207404007100b1314010080368031410421181e42012222150407104130b0a207018500c0c80c520080428840c001c0111040030300104001c02407015461007034408801d40c0509440b02007004800c3d1005140d14031022002480e410070b808660940b44046034140c0c2c0c200b0618150041c100340c158000303540011030300103502424200860128 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 425774424 1250 425773174 425773181
    0x316050f062701050105091b121f150918060816060806060c1f1b0305220302100c05070b01060c02010905090c07020f06090d050a0515100311030709 65
    0x2d580610900300c4080d5111952000400202202d1806030324280c014055596030744060b0750302906286c150b201c0c0c0c0800c400320030b50704c0c0200e00ea8424410700c881c05000031000654910410000305001150344035a131603200c41c20380750f10441c4810201e020030780306000700001200c10f645000110710703010507120303502d4503810700d0240385810740043d07015a071806100e00350303000b8015030b0049030440d0aa03082844941b003840d16035442c1e161800f0248000030190030280d800d9003000004402e28103942d40c0d00303519050081d025040840c0d5026506410301d44460700c06086460b038828042d011350041684d0000b5070203000041c030910140f4000c1c000284541400100c4007080140a06026580c101030020688009822103071240c00003032050217030f601008400148103090f941c190760101d03010f58800280c2004a05184110030740036801900c050112018420006042000c042c41041110340030302080780c461030302010984000101660203801080810010150040c0b00c040013001c2c0c8000f0340e5110f5200085 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 425775674 1250 425774424 425774431
    0x908070b0c06062b03031512020102103e031006030c02120a0e0103060b13050f19050d08041d041103011a041a0d050a1e050316050f06 59
    0xd98000104001c942205011150f049002030b81c0070108407405200380302000c0400726a4030081c0703200f0741050060500c250040400034421030040c0300741da40c844200c840d2400038003906a001d449621949c40640240d48180041c0441104014840c3c05203100141c005081241e0303030705211000c80a010203100d5004000714002c281c0c0351201007905143c0070300038040e1080d01e540c10b0155048541c03284090b01700319040f280d80140e1483c4c0105090003000c01a001000960001c0c031708000c000c11040c40e210b160460000584400329942007401c000002000142841101e00c07440740c1c000043c041286007001002030100740c0c800c82a103400d1903207600c849603c00440c0100c0c0ca0481c1000740601c02403101078140070400e070109600138000e040749048101c013140a0800b085008a9403010720401c1c4003d10b603250074040c1802480c218283d045414610390b145100c90003540e04c0d1600d2140b1111441401c45816421a40000614140f409003041c6000c184180340703041d20305005a0104a80740342040c40303c0e80c031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 425776924 1250 425775674 425775689
    0x120c1c0302010f230c0f0304030e011b0c1a031501050c15100f05040219110f0304030f0c0f0e01030605040f021801090f020a080c0c0304030c060302090907050906031303090807 77
    0x180351500304c0343c0b40c603030352005841c41c0c405413410031248010781500d1040f03940c01030b05400c001510b01c0816004840a0980c0c03114a0051400c0c42d45020401680303015001c100d603014001d180e030381901c448002c9884e01c0107a030351481c19a500c3d032041e0345550251004d4090041000b0603030305c00c0b00c62001d207030010420032200305401500346042400318422002e814000740900303560460034034008507008041c0003180301c001c1c4180148001e484820145c20081046591040c8042c1c135220f6590340f4210f040c2110860342201c0b41103c41d0b10100b45120443c0c1c0c500211600304009408a03441c41c3c4502c1d00800014105680603240d00f0301490150325151110515520006400d180780c1d0f141c81d070610112003011120358680341c0100322040c0e20540c4a9422034003d9124001e49a484503000451461403186610040000082c03101c0096880d402d54041c1c018038406440c425100e40e520310f401c450f84c0c03003100c403841c1c4d2128007400862240d001c010b07000f40c01144603062045a403500e5080701450030320035500220 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 425778174 1250 425776924 425776961
    0x1021b03030106200604170c07180f020c03030a090305040e0f040605090d1d06120f0435070501060f0b0c07050f030d0807021c03060302120c1c0302010f 67
    0x45034032800c90b07044c000251429500c401001c1e1000c5032100c81c054006080418080035501c80c48003114111807500341c0307600c219004141c0d6640b07a041c28110b10074000760390614000d184440001640201c4d021650300802031461540d4442d5814001c0c11490700940804c0070501002c0340300107007039500740e001d4100800801030501d0585080d50503a03400800c070100d15000a50b00b000d0850300a400080200881014130385109411000714045002e001c507900c00002c0d100050000401166807005d0147e0300a00c12800310001a4400c1c00038002043d02080d903039006524400004c00e00c003009421114480c1d4000b2900ba40d50307a00c500709106494105042d0400c0002d6840318481c800c00c01c61004000650700390b18030f034070302500007502d61078840a10000c0c0f040050020380d0b0035100307002c072540c408010350901004d0103003068020020000380c00700728001c400e5101108140280094146d101c45401030083c0c94002807580121a8004240400c89c103540d225182d881c01c02005018026a6075036045484 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 425779424 1250 425778174 425778179
    0x6270301020a21090803062103041e06030e03091012090803010f090618021612051b031602040c02010603020904060b1009031205071103191101030216060b0301021b030301 75
    0x1140f40b01101841501d46441d205405000920900540703502ca881102c00d02e0050b0394041c1c178207990308100c561010b48e500000902060310b1500c4071071220541510341c020b0301002e071074250580440e0280410031080707500174031110340d0a00e0041d420f00460301042c40e198204420840200f820395a40305401c42e010540440180310184e030300001071008003c0100d06000280c41d0100840d00360244800403004030b50000389002800c0d10610080c0e180681c400c00344640c00d90f06010003000340d001110b05481000c18013501c810000c0f0004182c170f082a180301190b405205140e42000014208011003005654035220b000001d60344001141d8460340c09610b010459601440405c0910034200b0043c0c03043c007041c10001c0c008510007088008091896042c0995030b0902810500d590610180415606109012124910010007203200721100e12800403045903d48480c0194240d0142c00d9201669044c60340070200441c1c6190000e46035844060001442e0240da92110900050322106900c0030b0340c00007004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 425780674 1250 425779424 425779457
    0x1051006020f031201140409080c100f0221040201180611100c050d09020301061203030c120c020c011808030301030c031a060105030a09020a090c02010b0306010b0906270301020a 78
    0x1805440c55490090340c51311480300c19403080d1403c1802000c100200341c02100b0500d8940b43e000550141e00022180e4894640f40f00c5569101f46000719440c0080c1000c6c040702d101410f9000341d030400c030460f084004001072000c810300300041c0020800e13410014400a030344128004401214090300ca190340703000e45101041e00103454443d03c007044c454094a4640750311041e42c0d1003405c0d104985a088004580c0fa406e80c00001e007d083c081d004038084590040c40d0004268040e8810f491022140d00c48805024184424101b203666914601c4007580100110942c6503203c5c140d0340040440124001c2c481d151940021792650b00240c10444108455030070030310034450071400684100002070303006001840d007140028100c0c000030b4206030b8490341f00c1c819001159101c00d0500c014100d074072000c20800c1c80240f0000c1c06850019031450080c010030001046d807510a2341100c04c000806000a442c00300090a1407900c1039401c0b42c5807001001c000071660307903540d003800240f950b8002640e0304a07090b40020907 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 425781924 1250 425780674 425780683
    0x142202071a16090b041d090109080a0906081806060f03100c02030903060901021603050a0512100f06020f300301030f110d15110f0f0c070e04050c040504140105100602 73
    0x450100301e103017408108001407611038080034851842624589580ba01081140503005948004007800c80104080c00c1c03d80d0700140ca641143c0066882001a445002000f1043c0ca090340448000d50400c500150483c02d00d02d20342c2611420140031030307800046402c000f030102da60f151514801a0400103411640b0715080002c103030001c0443c00210710303140309140e107542c50f0603100c2801400d0082c0481e007100d00342d020750140c50003030840c16690401d03450040030359411004240142c0d080d404590b88003149840c0f000440b4000080d529005280c5c4503080703081c01440da003a150b400c902e65825400d0300f84580644001a500840c456645801401014a06401c0020060540b076004a82c00920240840c200200b0281030100107400003803c1e03c2e80984580c0c461080c81d001e00540310001a00d01482c001c41b90061a64040f0390060b590306607100c00001081301d05c00d49000d4020b5120032140952450207074002c58115206014002405024504144c2915802c40301c007424022540010007101c0e40501 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 425783174 1250 425781924 425781929
    0x102070f0501230f06060c0f0106170304030503031f05150309010609050415050a0e010c0e030f0a0206121015020c040605030c0105070308130f0804142202071a1609 72
    0xd003020303103d028030340c2241c541d10b0040115880980c001c01142850721048201c854642c091815200b01d056045601c0e1701030003962081040c4458144105010b0843c04003e440550b89c0c88009185140c80d154144a0491a482c15101c001480d55400040340c0e91604440444104d0075500f09460b440d09181c90740c02c4440c10f84c003402c00d241c106030400c0001140ca24400c4400c0c0008280040c250b110580c5120050000003c100c0f0990319011058416540150706e0310307100030040701212501084a951b580c0c0750f501d0003038000e4100d242407000d1505181340840c000d038041ca4054840a000ea41e40c0e13421840c4d51030320986a009a04140035591190819019200c050078054005051070364001c00000d0541c842c800001d41008547c45c0424440b03101c5004000700d507504030b0285040f00e14142131440040d8014458a103507080c4000580310607080080700700465401c0c1d45403450841c00b0030b520010195004080c12541c05c00e04c01070241140030907803e014010030520b0b040e8400f0003c14a00500401c900d47c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 425784424 1250 425783174 425783201
    0x603041505010b13050402030901150f0e0108030f090d1e031205090703030e010c2a06020f010b01050a1d040f050106261501050f0708270a0302010503070c050102070f0501 75
    0x20050b2440810584d2011000c44e0029100140e49130388640b02540180040c1074001400b90100c0c000240c1004809050300c143d58200340f000d0b025980e12500c80f6903a1003502001d0100f07010a00c4400e040d480c1180503504014040ca00714000c04220416501d11f10541001c22030206038040504110300005210309940442100d000300300c518110b0300d0107410f449407a0652410070520b1140007080040001d02c107240d0706000400d8150900040b00701541c64031640c015000184581e003c130002d041d205004200c440e0106031102450298004800c0301c44140e440c194100e03070082a11211034a8076284140c03034031080f46840016155050400041c032030124550341c050075080e026054030840342140482c40e00590b4099242d5810f90b00580141c8031030041030300c2107004042c00724016081c015640028000514185014900b0b0100441107010304548100b2031900051009810700065000c2d40086030401554100403000c90030b03560798039003a40d01c400ca01b11114070210786098208042405442e4460408 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 425785674 1250 425784424 425784427
    0xf020102030d240e090c040b06090a09020c0d020d091811071505010603060b04140103060b030703060e0f0c030f0a150306090b01060804050a0803040609021c02030f030a0207180b0603041505010b 85
    0x2400c295a409400c2080c1f13100f9aa00c1c8001403031565410216251700030b024000078034155030b4080000094000c58420f01c0f8902840445a03940ca1010a0303000301c00140d61140c0b14558180020590311000b00108000e0150f03459000e0101000060007402d20030341310b400d04280b070221244200303098940c183d003c40149802e000041c803508503101c090310182c0340d1a01c1c031142c00d00711801c0100d000e08070b25400381150003000000c0c4605070b945a0000d10030740d140c920509449480314081000320407070489a1798040207090000c42c10300100300e058140c02c42028400814413003400840b014520b600c5500885515554520080401040e444141e005100341d00b441d101ca4074050700d030a03448103141500109000303000400201009503d610441440e42c016200c1c5070030025040307000b40070f0840703c58140d1180c0300b40d000180c0d460700c000084649180032680601682450218030042e00880c4600f0303103e20545070f50a44c02a51154801707035104038001e5500e294606000158101101d5060300300a182000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 425786924 1250 425785674 425785681
    0xc09060803090609060409060314060105010c020d02010c060e030c0706120c0c02010503100905010b07060f050613090f0f080415030b03071a0c0d020606120106080a0f020102030d240e 80
    0x40200c02d03252021000e5410699803216400024081d10454000050072450044080103126102200502140503081120b1050340c07aa001518841404100207601c0750544540b080194400d07443ca00c0c00d1031043d0710100c2e51400ea0790010b82181c112500c213101c1540f0407202001107a5014084035a40c442c10002040f80340d45001d40100502207120020303062003030000218802d90004121080101410842000156118072841c601944843e40030355030756043c0601e2034848030340c0d4450740d401450b000f48103000c0d14104841d8a806040100c9041c0c0d46520581058400b299481041a071492b12410015980f282080e100500c1190054815810545081c20400813510005584800d581409810700441003840400e19070704d00c5550a020b000d40188207113a0340950300090a540140303030441f01030756010032281045080320594072a8040a510404070b034804a041c81c02003004150040c4140c9181811691b1340c1010303540302d03c400141280e000040107140c404c118201002800d405030081c0d41302d08 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 425788174 1250 425786924 425786939
    0xf08030403020405040507081b0406050f010c11060f0d1401150f050319020a0801032303040306020c0c09160210140a0b22060e1b0f090a120f0c0906 65
    0x356000090040b541d0390081801e100d0104010802045c10f1422a500310402080d0b030020740305200c007014059418848085a14904240041e0001ca010b07034072099011a01c0d181c01d82d144070307000d0310550008400c00512501d01074200c02002d8040101d030012a501c4905400a00d154005900c9507014005c107000580c51039030300c4250402d119800d0301d401074903902c800e104c3c10300c280c0080b28114807151001138080310540d0001d80f414102c1303024040d29a280d0305451500b1110700e071182014099600300304020310010345a5070182281100c85021110a180c4e040045010480284e80c660350f1150004a07506116a04009403c40034001d04010b01510035032801050a02c00d01505682019868000c034103000c2d00d801c001016100d0000b415074a1104441c0000401403038140120307400d1028107070000380d0350510420000e800386100d0214900d1310020300f0380e208803904800d541f6607019100110000e04800114980308120780034412642e100c1070305d860420002c1034181d01410907941443d41c00c21600 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 425789424 1250 425788174 425788177
    0xf030c1409091b030717010f060605130506130509012702090a030f0f02040f0c0201050c070c03120c060f0605040b09071e03090b0f060307140d030e030114011e0f0803 73
    0x150f2091007103281402803040080c0c105000c4d0b40103001203110400140030414415041b403131085110310400c021003510341c00115070900c120041468400c1d03501004025600300b2100405140000324a80b11060b41c9450004e400e0407006c0c4c1c000342c00518180071000000b01d010780030509804920100310724003509800031038040c580b10701c0060950505800c001c420b0008801c425000c656004204001006800e2401030003403556a84040c01503181a00084160700c034a012610303950703084544214564039542d1a4640d52490f50742d48000c00c4a00c5054400140312030048481c149469440420300c9424007040c4012284c4401c8132520030202c0784284429107401100f120103102d800c8820f45618400c0e10002d030040d10040d40700801c0342d40c5020422031020340c0c07551041e000c4e0750120305031103e9907510440082d01c905801d0049910001030132101c000203019621409603500081c1c00410f1211032041d00703a400070400d0703120504054004489004001c04039507484017610001c050003000f13505054080e03940c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 425790674 1250 425789424 425789443
    0x90b1206040c0507050f031b06130b060a08030a05040306050604021201050405092b1106010f0b03130b040f06230604090f0b0c04091b050d090c0f030c140909 69
    0x110764840e80c0e4492903200300b0858000c0c41d017141c229004480b0b020010750307407580301b01c01008a00001030301d80d2690030000f040c0c03140182080c0c0204038030f2080070b4451005c01c69025082591000030100700180c40001400500310600e040e031106504e0702e2540c240783e13080c0c4000074040762080b4070400c00484c4c1c4583e014007041c103492007a9000503140e51420446481c2c2108070400b0007020216900e01e46d503e08508000541d1030364540c0d501e00306004841d080682e00d0a0038000d0050710781000c04240a00c09803480503544c8004c18440b0f98581034415202c2d503054400c1a901540c2441c5030007481e10501050b030003140d12031040c4042c030700c06001c50201320080c03100024021510964989190000748900c2c1d2001c01002d54200c0400300301824000f1225080e50303c02d00c129910349061500a20303059001c46182d0707110908644503580341c9200b0480010007460725040848111090b0340b400b02d00d100701003484c1005944100b500100c1d141c203003504403080d40f403e224620703c250b8064040260706000429040b00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 425791924 1250 425790674 425790679
    0x503061011030f13080714060403061104050604151d1507150612150507080106080a1d030c01150303020c1e1503180d080c0c100f0b01090b1206 63
    0x18200c001e20482070541c860010188110100402c107640c40100c0c1000a80403990220100c4240990b40e42d805503a080c001005190700440600c801c2000c00c04039080a800741410004091030180c9030b0002038a69001343d0046c00c0700e210542000c58141e50800c4804c14020720a4400b41044c001c1034001a8003501808404820b144e00400d00c0003c000705048815a0400d000c1d600380119130700d0f4001e900c54503080b9241074806a001751244200f880c1c040c8909801180280d862144582c00c0c0682954140409000308400b01d43c0d4609041c1d00c10410100c10302055859400381d5a0350400039095400d40d61844230b070074a9020804030400009400146e00e00390110300352070440c45840748411501d0211021440140c1080303031882071110303201c07080009602c4ac209070b6540000c00d8403011003841e0b640200070700610204003544003051522000e40090074003061700e1012100c070302e00004240b8098800c84102d0040040d15004020019a00b00f1814406000a01c0e0000d081202c406800122084050311050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 425793174 1250 425791924 425791937
    0xf030c060d020d020702030304030f120804020f060a0513030c1a0f0405041d010c020307060e06070e220e07030302010507080c16023001110901020a0b0601020f16090c05030610 77
    0x4420304030f0307501079900480d0002c003a030307884640d01d06102c21801d407034060031104078070461540e581c0c0e980244142402183c02030046466803440106004081c1c0c894007130b850511209109600402480b610310101940c8600942d0301014074001841c0780d010050300c040c5400020500580d0000b1000c102603a00300d070000c85001c1402d04000303642c4114008903c2031110a9401c0100c1d910a142e0000018215244079482c104000607002131010345500b000c1d0f555400003501103003000514035203142ca034032104810748803081c2c0340e900a0650204840098000c801d0300c2c1c0101400300b05040d028130580398005e460341043c030461701d01180440803920071220301c4551007a4240e684401c3d9141c03001c030300d06618281c2c140c504041d00002c400030881005c0c690b00403459800d01c0b20020b0404142c0301619800c9006800070044004541da43d040e11b520010038046c11403251540642c400d000c1041a90748140040911201c0356007802c000405458604100605201d01041484429181e0b8204640301e42400d24042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 425794424 1250 425793174 425793187
    0x114091c08160501020a1808030a200304030309420903120206270703030c0203010b0406150201050702071a0c120a020c030106120b01031205190507020f030c060d02 72
    0x300c105001e00b05810540c0e082030344045040110560041445a070a0b880c3e003a544540e6162004aa0503a400352040c41c2d08144012507000e4003138101c0764500d584941d038045603210320085c1140b03581c10690041e03000071117a000c10042580702d20130941136030f003400d40e020700300010700b44010004141c00401078201d10304804c0044106485808060040e552140b9003070340b030307410703120000355152001c0d541850064405230040c0c1c40000ca2641d09810a100f101c09409c90500c1c3d505d081c0c0703801c00e440c40241c0c3c055489d418010030035a5a441001c0203001c101e411000d21259005000742100d900420827002c0d9400041c0074400c80600c407195440d9507403142400c0380d0b11044031401d6410101c0d14421b02c0d4642d080031640c84402500824002c500d1442a0020003446640f0790301181125810080901110080307001030001c140203504800141055050252401d41400712072044c200c1040845000618041030140440c034084000107209001100208801c00c40c1c540011000d00c548807000655a600240700b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 425795674 1250 425794424 425794433
    0xe1915021c030b0906090906130512070605180a0c0e250e03010e060f1815040b191b0807031e09030f0810030605130f110114091c 57
    0x3010810750480100701180801801502070b00403c8042886102034500140650a200242074030a89084c0c00910507600d592540c445035a040c10411745460098817091006900003000400800e132159000095a140ca0860040d170304940d84002e24103a0072030980c110200c1c45503d0398078103a4981900312405901d0b099220744410f0211580458001003118003080d0f042e030442d008403c0301c0f6082c0e00a1100c20382a002c0d1720380302c250441707041c4080e481032004240300c2c0d024400821007900036078048540001940c3c034118140b2404903070480702c441d800c1c81042a45154062110480030030100f05202415555000e20140c0380d40c02c1003101040a4500054038135407003034000512041c2840303d0103000c00b0b100d031800030241c210b079241603010501da000d245180c0d62080072007500c1400c003241040001c0742183c1ea400040c20026103504c02c0c0509020450000c601119142c208403071051100d0f803505031503e000075101e0700001524004480c000c0c00708040342c2e21410055040e4040d408044004880a480e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 425796924 1250 425795674 425795683
    0xc080307030605091312050a090e040f08040b0c1203390d14010f08060414010212010b0703030b0907050702041d0a0308100519060503070309120509010e191502 70
    0x410f651041d004800d000035a5040c250052034180603000e807007000454524240c809114000c00e581c0003a581907001c00c507080c0c0b05006140c001d0b104080b580c00d8610f164aa1468036000342d0000507402c40d00045081180008104d4100b00c041050344441c21407170002c40c1910700c0c0307051001d06003e11039a006c110040020707010b10700d054581407940c0240c980416a048100400c0c00c1c43d20f504440f5900000420907404c0e89080d5030032161540010a80d40d034680d82e031100c40185065220307240d07640038003e02d8442c20450354620b020b07040341c2003004c1c1c0716a0301d030500030305588076035455502030034a55080c0100c1550181c04c03983c4007501610080fa4103548402c200c1d1001c01e10b1000240c00d40103001d4032508255200d40b000380903403c40140c00c07a5594441c0d080001c0400480460300342904905001c00c1414002d4000c2c5911440a00f400111555140c070303842e410188144044001660010300d92000e0b40c2c00c03543c0800c070a001034460011038004025041c205e013186010700c01d1307840c6403e0f0707070060054800c20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 425798174 1250 425796924 425796929
    0x120f020d0903032c1914040b1005070503090d030f021e0c04361203060e061e090406230408070f0512040305010209150a020a1e020a03110f030d0c0803070306 69
    0x40841a285000f4004501c648180703001d00c000d00103062589005510f0240a08c1c10865002011044c0d420341042c1d0a403165800500e0854940c0024411090755584540c0d0f2005064040d0b203400901d5010404001d00f480d162017820000400d180d070600300c80e42d100092000183c2420741e40000c00303020521401c101003c075861001100f1039207141030300e044070382d00c041141d01602c1b0340c00c000d0050703459803425000d84003a40103008040c03a100c03000a00c14070b080f510440300c242c00b41c1203c842e0103501d5030104104220841c2c0540b03040da1204000c10f0484590b8150300c8081d040200540700600701a07442c00790380e2296140140440d28094050018000103024000403100c0e400c41c441c0c0d440341d0300c1c40c105010390001c0310a10f1255021403480220740c0001d6049891850040d03016143c41da0741d903500d4400d45110703041841101007203418130100503281c40c0c0301600514064001100860320307010410144980748034015000360047c3c0d240d925580d4215118214850303200240d55200d981c1e01c60120024400d65 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 425799424 1250 425798174 425798179
    0x3050903030408030f04030c0501170a02070212030c0606130c0504052413050405071416050309040e060603010b1f0e0301020d020a0e010225030305090d120f020d0903032c 75
    0x1603c80c180b030001e0f0005204492080a400d04034565270345c015100c100b18038801c24074400507140090040b08595005100d5144024480301040f1a8900e0191854001119a0499034010002d200079803401203982018170b00d501d807040c401c40b1041c2c10000d0140c0114411a40603420480036403d00074107024a004448420013580c0f52205642d01e500b00c00c9680310320400e80903a141c8400304007018401e14103220078a5030b0072506c5113001017481040d07100d180e8204054801d4001805104042e075124003c00906060100082c955414007030201401c40385c03c00c42840c410740324200181916442020400d98070102401c2c140b044c1e500003c042806849075031802d81055100098204203203820402000200388284e00310303861180d4006d0b0000c00c208c00e008600c51486501a400c200081c4280010a0018400381603aa1084281c0d034484001c03940b0444038001190909100c00c20181d0304200d02441115549003600d0368514540700501040e0620b50b01041c84022155501c000400400e845a00204c01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 425800674 1250 425799424 425799427
    0x70203070909080304060c05160807020111010f060906050a2d0f0b07030809070612020f0418061d1510170c0c010c03270c32030105040b040305090303040803 69
    0x5883c0441450784201e80c11140949099941895544158141c65404441203110200303c0100d4451101a4100841c101d0410000c0d8400c0b2403401000e000f010300038404910302255040c00d0130340c0d00c4140c85c403d400c0180074115804041217041500200703025100e1411380740329005a60421394904444007504a03c1e14804000320014950403408000e01560307000c1d076079560054807581601a03c0b0b4000b442200001241d01e038408000d202543d00a06540820798003003490300c0e5440d03176034010b50b031400309504c02c0442d0f644901300040201066510282000800c10360200e01d48040d0a08988040c013007064002d820004540303030203500030f5012854150240034a9007951400d42502030455010705503848640d42442846904a030280c0504e46001141c0030303006130041001d910002c40b9055440040e101d5040400380050340030b41c6283c1c8154804030605240040c01c852964004141600100c00c0c1d003c0e80c0740008010208040c101d8030758016a061422a07a00d403d080002441c0d40550b80269089000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 425801924 1250 425800674 425800691
    0x60703080c1b06040b0a140403050318101b0819230a050603070f030b1605070c030f0209010501110d0806130c0305150405041203020d090c290a02070302060702030709 73
    0x2000240c0f64421446600c003030449955603501035060b103091081d4040c0c041c800c1804200024011000f4551002d49441719280144101d580c041c5884500005108050350b40c071441c14102a4055a0400364a074a061101207800c20304000c145460f00c4031108071900b40c1d02c0100a5040301d68484404507286010035590107070500d2816180244015a103581c401e01c100440010403031000c2c44103800322070300156441031940d1031007100020b610180079083c0400038104050000104105a2500039602840955024040c0e07441480f603c50b40603000f181c10b0004080c41e0903000ad2001800211403036562420246540345d07000490090020120841115414440480d02e2260f05030b200074412185040039090b4540c110090008451050306e000d00b01201800c1207201700360003038004005003885040c0015102086480c3e000b0720301c1c001c0e0814031888650100102540200102403400e807144110307460302d07001800d200030b50303150300c2440024014100412807006541d01031224030000c1c035645006014910 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 425803174 1250 425801924 425801977
    0x30a05160507030309150f050a0e012313050604050f070b19050a030b2d1f0f09030c09020405090709150c02121c020f0a020109060c02041b0201020d060e06060703080c 73
    0x8d01126460700a07450040900c544c01170500a074115540c0d044000d50340703a0310092008000d41d00c02440880c0c41b5038a403884800085041002d20720481c0204060300041141e150814100507103a030142d5090303101801000248000c00c0d1114000e088c540c10300d265201e04504007075001d0b02800e00b419a003d0049003c1c10302447c0c00100c0400b00754001000340313a519503a0b400f0400c000c0c40d00c140c4210301c81c500040e00003115001d4660f01d031070760029007000d6031440c1d503d50320402e94003895004003100e10340201e01000641001c3c41c07134541003c0039080480c0c06d54100004038107039144010b1802c007040389070b024840a5456650000300d034604c0302c0d0f0503140f160030945a032000c44280c030b8000800501c1580c07421600d031580816070480080c3e05a4172092003a217000c50803500040401c03000e9078016a1a41c120300c41d10842c8000940e1842d0940000d030b151090080d4010444100d503000c2c1d00310001034020803140340c1d40c0d04115030034681d05040204441e1502c4003134031518014628a4079042ca103c3c00d5125241d13 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 425804424 1250 425803174 425803181
    0x2030901240812120c1b030a0e01080606070215090d0218060307060c050601051302120f060102070b0a05030f07050f030f04061b020c010e061e030a05160507030309150f 74
    0x30380140341110069400080b9001103031040204c01c04c2c1001c95000800c40350300048000700300c00d4030b0b101001e111401d001004030382550700580d02c00b004100712241030800b558021040d1036000c1001c4071814142209900451005014030000f00018540090882101d54850380a800050f0300a0035071801c00640140819503540c00741d554a100c0d2245030000148071b48100b05070301c2c034568018094407141e482e05051004411043c04030360066078007401084c0500e0001044584582d80d40003060700c250400c5000642000415003108440d03200800c2031030f1402d6004800c40340c01c1a85440064001d640e07021003140c441c0942e40203240b80b01800428440b000f4826902c0320b01590264004205039404003040f0703103a14141d0003442000d80c014400c0d031400c56018001d4000070320400340a480c07802141301c8070700c1a220700380c170700a10390400d000c42070004a6881c1e1098941c8000c0a60415110312802d480c090310741d010b050001010135480351418810000540c81d866101991641d0500c40b0480b030801d1076015 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 425805674 1250 425804424 425804429
    0x10030f150b040e06030d0c0314090607080306010806040c0518120f060a0e030403020f04230123030c03060612010e070608070f0c0b1503070e0903070c0905190203090124 74
    0x102e04403c004a00545004036140040002c03540300e51003070b04410340e816501a17600030800c000700031050290001544400e4010404148a407040c00e590345880700c009031080401034503c5008900e8015075204640e00001195064080b860704140440d0510000907403110013543c1c0700c203c5001e04110070035130080001e103840c016507849100344101504110803950364040d40c40060340c002c1074139084080c542465070150404104400d0b004120741400e8031000003940003a8042c0c048040012201203010300146485030a001c01100603196500f01000002d980c0d0f9005030920340309900c0429240c0091909600050903460502c0c10f4138000c960b202c0000c0d1801360103e50410201e0302c100c0e11211000d220f462480800c0b60300024000694445880541160380c0c500c0000b601031190b003034041000c140e1081c82c2e600c1800c034080110303a43c41da03520700942001115440700016a00b031006105000140c05464a06030f0841080103840e03954000565024001d140c82035900d100e00f0f018140c0000201c098003809 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 425806924 1250 425805674 425805689
    0x301020f04031202031201060e030f010c12150f050405061c03030902090c21100506180a08030c060f04080d05102301140a0e0a060302040905070e10030f150b04 70
    0x40402503110103a8982c4540c00301001542c0c6c0b10340c0184a05402180d416030300500207401c840d0381e0004a40118212441d640140b80424242c3c1b1030b0b00c00b1001140a484184010000c0d4071140e2403402e00b60b03400208280c020716102c0d81e12a400500c49131100c00751320510001d5039502d1440a0b2040c10090b00030701003003500768000c0f20010001380c1c04040da841292004061030440c40d00c0344400087c0340180c1c45010340401211552041c00103203d036515006090303c1c4840c008445040030b50039040280102d020b902902d503540040c410f9030600030011030560b92080182424502c0d682ea9490844613038803411890b41c0c00340340f62600303000c02501c201140400f80e4548080310301702d082c400c5c00c112400d03044800c0c40a00054803a14800d19081c0d411020780041c2149052120441c2d80010010391940c001d508400d0000c1c1c0e0105041080030301d14045d4507040212410701583c40011741c40410301c9040c03400e210b5400c1c151074001341842880c0d5941f0441481c07448941421126440c0d091040c07584d0b0091080c2e21 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 425808174 1250 425806924 425806943
    0xc0513030c0f091e0518030403141b010206150420030f0708060d11062b2306010c0c09053301020a021e06070f03121a1306050301020f0403 61
    0x14880c41601c07644d031410310422103006100e0010900000900402000b4117200004421514038004c000c00140c005984a1000b00401c000c4403022103107090240c0c00701c20448180c1c620600c40b0742c1d801113101600840341030840300800d02d142004c02c010b031069403030510368400102c0d00c0311030440300c11004c0c2d80543c00c0c00280d103031551103d203401c8410319010317140c80da880704446640e10001810a010b40d044400064060b5090007080785000c481401c0408100d0201020f0510301e82444415100e035010344d40000c0040141c0310303a001a0504070300c100403c01414000b1041d040800d0016041001d07000b084120030a018a2030000b90604d84000f940b0120304c046800402100303410440700c2c00117902920103034010701c00c41d4441e07020400e9031000080c050031141400c1c002164903440c0c200003068260b0041c0c0c98203074400420300d0300500354082c030707a01d810b862461324440b04020f02400c580901501021190426520115070344100140582d6000369030542c800144d01044a045401030010bd07030064a010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 425809424 1250 425808174 425808179
    0x18030b0a0b0a0e160e03030d09051219030506010c0c080d110a0f030c03050c0105041a091903110304090f0b030c010203190f031e1b0c150c0513030c0f 66
    0x489040240d00500607060302d11400600c482d400080e82c2044d0039000e24010000141d0034001c6401c69000b4011048000c0d260340d40801171210810412030384840c40c2c0049403078090f132202c000d11403210000422081580f07070404292681e104030040e0314920b4020650319032160340c2d088903a0355a8110b10032a00402c4c0400c3e0451a00c000100d000060780c0c3d0441300b4402003854542c1d00715005207040d5002c44c1801000d009000380060240b0595120f107101d45901c070521018101c0000c0080340081c400f86190744210b48409a88035200ca140040940c9420500800718002d140c1605500540e0051a0a285000d0312440429071980055803801019070543e4030800020303004a03100e200341286040c140c5034000b400d1031214400d1460300d41e4001b0301d107000603000300a2440c9040c003800106403609402d4541117092480040c1c0303100c1e601e04540904100001d0581d542e00c04950101011211030202c0c0c0c2c0d4009004000d0060b0210740c1134084820a0152160f143e00d440080507815008401e0102c1900001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 425810674 1250 425809424 425809429
    0x20609030f0d1e0804020f01090803030709060806100e0111100e1b0f030a0b060d020909031801091508090115260a0804030803060d02090a0207060e0601051005030718030b0a0b 77
    0x10010080f00e6507207100503030380e9a40900c0000d041200740141002185840040d40d0313a4180013071405905a55962040703985001402412044003a004c80d00c6802442e000384142908000403c0400f4800e0030100f4820740f144000a081806081100070aa820a440030107046000301e0b00381040d042000803500f400b00f200c003d000381c200350350208540640c440480c45c00071400c08448140c0c0100000e2154046507042d50100e88a40c5060f0346c141d92503800481d1250f4000d00401e82800c00c03840070701e48131040324a1302c1801c4020440c81c0000b6070502480d0404034200080c2034100c0d103041e03900c10500d81780030340e5101120780a44800c00105041c0d402c2c0303810342d0840034801040c240005034229100c03900341411038480811a60019001c2544030400b4800d440061b2a220710540c03184042580041c0c03a40000c2c20864291350055a101309150004d5006114aa03120100424656181d1419a8881e038903900142d41c4128141080106007042c91000020042d40040040c82103203060028800004030409 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 425811924 1250 425810674 425810717
    0x10507020d080406091709091302010516020d02031c09091a060d140a0f06060302090303030a02160503070f060e0309010f030c0c06090b15101209020609030f0d 70
    0x92140040e0000c49044070154824040c5070b81040c0625400990b1000329624041030380c0460036001640d60b404140c820580c5003c0d804550b00c02c04601124940313000e140e000800b03510904180b020a55402410a8159100c4404001c10154007408440060680d5a480c407114130302c440341040050605800070a6a001c180108041c02e40c41c5080115203100850800c52a0f800000310b01000c3c50382c2e4540010701e000783c400c215025088281001a0142c00e0031061000c1c5d80d240c0d0400b00505004000300c810b5910000b007100d034007880940f801078845503244440c1c0d0401850900c043c0192101041000c14880400005800d2a206110400002c400194100c0e2a40500e091460106041c025086441802604804014905480c0c0070002d0202c684e11706007101c04444042d00c104208a04208014452810486c580802214101f080c0e04100300018030706030454003203215154566a813101192a039800f6a00c05103001801c0d00e81000500d2a40c030303a0380c0b1040685100181012481c05c80c00440d295 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 425813174 1250 425811924 425811931
    0x60408070612020c1603021c0302190f05030a171b0307030e010e032a010213031e02130c0e0105031b0f04030611191d0f01120c020d020f0105 62
    0x24240340d9140c4041591640e0001034005002034080080c03200b4400c0522400c020001100300c605080d509500510251300014542ca01080320b020403170030301107900058446c860388405200007a6180c1f4900c3d0040741100c43e00d5009103a407001190301e8240603040383c940400d08004402c202542d554007401e50010a020400e14805207500704007181007148250401d004a159808c004108060800d4001d40341da80007840c103c85280414502c03420000d8070b104000e90080020000390700f0004080780034143e8401900c001080c196418220b002040c2410000034102c0d074005003105100303480120b1140180c40d083c0312100000b0701d0300180d0801d560103001560301512a10350120302130078554001000a0380f100b500a510f500c401e020000c0015332502895604036004c0c00c0c0d03035484403d0180300306030740800e2010304014000181110001140d15001c40802d00108841c0703809596030080042c1e90340c1013204075403881c0d1400d107a405910075400044800904120303900b00e440101c1c2c0ca0310b0302f508030f0700d059 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 425814424 1250 425813174 425813189
    0x60b0a060225180506240403031d010207051309020301020d0906050604090506180a02150a0f02011a0d150e0d0e120d110718060501030501050103020a1e030618050a05060604 76
    0x900403d140303c81c2a0b101e1036001c1409048044860f685440096070101c8009036410310002c002000d004250340074403c4200c01c10100c0540e880c90b070340840082d4440a20b4003034940950030400406945000582000d00190f8000d0001c540e10402405a0005030810560640718030382480c01007200c504292041c6184507411101400e05520782040e5480030203542c2d84d04070004c0c0300700342c2d000c800341e034913900420280c4c5005c0d04481d651740460b0304080c2031114900400b400b5a40341600e10242501108d50701a50700308116030941440300c1515254036000c15041c5403a07030041c6402070805145e400000c212aa0407400c1e103640c096400d20004200180c00d0501c2e410205400c0f00305214103040c011232801401c1700d40142a103d0311901c6100201070703514900c1a41d41d001da15040d04201650b018412107015003001c0c40d05600d0b0150b0b03250301408030805101d0175030010580ac102a00c91034840e81c040d1303018210a408201010400c209a4000b61205461200d0f40c141f410000c1111032a10000b12021102c1c41d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 425815674 1250 425814424 425814449
    0x709050c04050a120c090518071d16090521010216112b02040608030a08010603060b040302030318040b030709090605010603060e0115210c0e010f05040e04060b0a060225 74
    0x107116000c40601390140848c1003922441c10240b44040d030600031407029214180440707811070001a40300700441340c040c046685210b80301800d807000e150b000700d126082e181c06407128546500e03403141001c421f482e5024089455440800c0110741d0096402c0a0002a8060783c000c044082861003082440d44064202610725802018030001204d02d00c21400e142d640000c0000500a50b2410300c0760569103c005103000141980340107000d511b0f01071040602820018800500303140c2541e021039620320613025180103a14030b00c9500d16030b45d5160340040c0070b5640003906540e901540c840040000c0c0442002c112401400c040000c2113161091081c030040380d40058602d80340b6440c1030458116102a01390320400c00400c68030414240c4034100110503090401c0707500082042c0c054500501031000c0780300040c100000c450301d984900b81d100d07054405a80740030240446685991030240000c01303000d20041c0c0c224002d41030008000e6008641000480031011a4603041625009500b54181842c0030300000101d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 425816924 1250 425815674 425815679
    0x1080c01030c1d041d0a140105070915080612030406030207050106080607020a0312090215090306060409030e040b01021603030203041a0708180d0c0806190209090103030503090709050c04050a120c 86
    0x20075810150385c80900e414922100c08800c10382900b0b00c2c000b0740d0305031410a101141200911003d101d4650b10540b01d24185040c00c0c24101500c80c10340000000d40304105541002c80c003156582c200b1007405041c107104aa607900e5603050b001c0c02070f42240c2c1007a21103502e0f041d00000c111001182c01841603401e58082e218075403c560303040e5101c10300c0303251a0303064945d110101d00c01a03c1c1c844612034101d030780b5224244c89030700d04001c061a10800030000c030300032400c000b0b80c1000240c02c103100101005003194081015558030004030702e06421010701d1549010205000421b042e00403005000f070340c00c0c8901c02c0704403003800c1c09081f4551081c444010303c500001c10000c443e8002050b8001a20b043c000e050f50120042612124040a0a9003050f0503903045081448404a48481d408104c0d4071008c0f800c0d81030083c0e920016550b02c805120280601000000264400d40c0038040312020f441151010810350034080ca908078a60002d004c0d190003800c1190300450715404c3e291640040943c081d039030f500c0721070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 425818174 1250 425816924 425816929
    0x14030705042c070e15180c0f030412170f040809012006011503090503161a0a06030b0a0509032209020a0509130b010c030f0c020901080c01030c1d 64
    0x12404181140007403412600c03003114008000d5528a02c08070b4005108450504543d4800000c0c0034200c09004c20781d18000c03501315180c0c482514001c03141e26241044c1a41d8071010246603100b505000444030b20000104010009944215500c800341c66541c2d0100615206400d007031100e050b502000b1501c88400001c00166a010042c4004c0c04189424064085401d00713410313590707502c06025112034000c1c10061082c8003c684030a02d4440c55440c0501198901d915140c0e240c0c4945402c603400c01c07403988800c0c0144810b03d082008944c401024210b8180780000303200005100d14082100e4424031180400d0302c00c0030038024140518001000740d80740141010b150666003e01041e1018940c0040000084040503880600400d0400e40c40e0707513644000358030070000150091044241100c6c509030f4008581d99000381201c0840d036060038003400d440442c4105072071141c102c5000a52100b5290008565410049070500100c1020f03202071000c12115001501c4400e0a409884044c58078032520f0070a62 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 425819424 1250 425818174 425818181
    0xb09011a0d0f051c02010e0d0509061e070c0b0403030906020d08070e010c06020c0c04110a020303160c060504060e0d0905151e04120317010e0f040813090b03071403070504 75
    0x154400d00481c1c002c68114080515401142104e40026035952842249003c0c8240004e072050191840c04500d001d22190002c1d03802e005040d9415841c60200f90404100314010080312125501720303030f85113152075441c82c2c12030640d4080d002c114001b4401c1000010304500004a0248240c6545c03030ba002182e890480403510403a0740c0313180d01d04224005080c0000325072684000c10b0111041c8000d800c068035500284002c0c0d4451201d10800e0000c204030b419003069010003601d030005080d0160004203440308a040751419540d000181ca0b940c0b0300030a110812a440e801200404845d00030307140a04190002911030306454414640c003c541d1070181c050482010009001c03000401410f0285c0702c07400201340d071a541003504401c4c81e02c0202641e070b006040c0c200103007a1498048080418180d810a0910040c00302c014001d03034807114820780450304201d0008240c45c905c1e0481c0400c83c40107680d5940b510003500c12a2501070282c050800080340000c0316480c8074048110280040500314034000900008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 425820674 1250 425819424 425819453
    0x60705042309091e15010306020901090915061202031504020901110102030108061008060103051009022701061107050f06070602190806041b020a0f080d090b09011a0d 73
    0x303419191524480d9030788904a56003e4040c401c0248494001004541c503004200020350400c1d52140414200709100e08800c107040da81c1c4003601503207820100005880302c0c2d066400684501c0e04260201d05102c40c2a048042194580d50ba01055060703500114012807006443c801100c01d5500400103140c00d05030014074000806142a082c804411304155089810a8001600e50f8208c6002d0011040d56200c2c10009010880041c2c107095243d5550a50785005042c1c3c42508252a00d10a10566640b1003021411074040441d02900040b2500211a00b0784d00f4055a004103004000c003c2c1100c4000881d44180c4402400c010072450402d02080b485800140c81144c80302e408000c0b82d540300241010891000381c56440d5180d043c03c00c00c0411007500c0900c076000f0303030743c180140c07444c3c680035800030f5402607840d007041200c400c6010038285104203100c0e42400300803142c00e10441a00b000140307102241300d0391400000704900b0300c1c481007005442054000c81d6501c0f941e81409500410148081307180d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 425821924 1250 425820674 425820719
    0x40b0c0405010e0904170c01090606060201022107091d060102010e07050d1115070507060822110d080c032a0c01110a06050a0905010c031e020a020f060109150806070504 74
    0x86101c43c00840e20099404081004071f503035100ea06900400c019030207100d001d064140000e6040200300d0420007075000c200f103100b2100250318400304480a0107410040d0240000e02c109a0b01680385800d0421516400d4036810f00661078229501c40c104d101280000a070f031002040c58545000644542464401150503154003010303200b0552446200c0e1001410420310401c00b41540354900980680341d05001440c2400300c0c000500c80a101e9100c0c95800740c506584415001143c20403070f030102d2202c8004440062070500c00045003000c442c000005032140c3d00200c5c489c2082101d0044142c2550120604168000e03481b0580600d030070341c05080c24108440d0710340115240550382d034a0301016070b0030a48020381c40a5580c0981d0302404428040c450714071000307007030034002c0c80304400020034030301650030007849410790208083c21958401d2009640807840281101c4d0307256101d81d0004018540034441e4011584c07510790010305c1038008a0071503c10700c6c5e9612500d050900d461043d640c2490150031044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 425823174 1250 425821924 425821943
    0x30e0108160f110f01140c03060906010323040516090e032b0f02070b0f040b010509060609092d0903250602030709260316060902030a0b040b0c0405010e0904 69
    0x300203803410081c0c1d1000d880d1030130012802000f5441c0380508188050984455a9002c10800440d03407621003036660030481c20310b000141e0601440d40001000c81c885421400401c01c03105104c24041d0000e24860308000381010389011036901c10550085a20300c034805000d6400074000010311040c100ca40d02e011903a03d035038051100103c0c102240c00c681d00342c2e600b04941503020600340300b403000034081554000d0489407544001d040c91349401c0302e0110144100c5102c0c480400000e0380d9500c54400340c0e070038010043c0806010341011340401c031111401c1441d003800c80c000c0450b91115a4000f84820b4000ca0381034004e185003403850718506100c0e20841900b5049803804550480000d2840c1c030044d48580030350380e68412010304182005458050721101000c2d16205200100d01c0c01c0070200403a0300f8240c01d25015480d2070f0591402030302030042408040e5040c003541044009200c02201200e00ca2480398500b050280c0d1103200200790340c051402400c0c006440b68a8001c1130b070820441c03068001e8050039424 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 425824424 1250 425823174 425823197
    0x1020903060a15030b09030a120c020a060b0109080a0f02040b0102030901140a0504030c060e0f04061a0304020307050d0308040615030b0a05270f12090108130606050d0b04030e0108160f 81
    0x403548002606e43c440141c1c400604100358136400580d440e0503184003081031115007445e15000756a0701c60040090300c00d658030304501c00d80b80e000b03010400c0240242c0080c1c4134108800e0510386003051140d403080e8019428851002e85561010003103d8241d02c5c140c40d0300208003144040300f0345c5a086620700d542031090400020010a41d0124440b0040086039107a100402900c424001140015818a40603d05140041c84080240030801c0c44000080c0d0805880e03598600009141407075961110f500002180100002e01da4400074051045009402c14001e08041004001c0800394900c405080c840401c0049006000990003068001814182e98408030942c8401c440c0d102c449403450281c0c56000c0d00c0101e003404001d1080c01501c461180e03001d4104589800041c2c22040d004200f00e5013960b4180ba4402001a5907001c00003602024260350265a81403600d8941e04000382c1d000c7d00402e24848041e8003c1d84140101c83c82101c81005132951030150150546802030240d00c1c42c0103002d6414201c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 425825674 1250 425824424 425824433
    0xa09060e04080714011b0e090c160305070c030507170313060f050c0f030903123f13150e0a060b01020a020622080a080702102f0d0201020903060a1503 66
    0x9030030750141e006200061b4a03101d104040c04182c814604103005070030360810000105110011354018201d480840c600c07075929440d046446120b0000b0061043c1305020b0301005110300011400240c2d070754050210781e5600300303079610341d501d016124549514894130b000c240505845040c1d40e0012801fa414018140210404404d00345180d51708214081ea1010071010494a010010f9282c3e074509100a545480c6001c0420842c0c08021117000f0103c904d9101145e10540200da00810325440c9908403040a05014a0350280601025004e40700c1b451030030440c0d44030b4001445200b4400402c04020001011b4598952025081490010f0305502401740004090f0311810014030b40f10300094900c8114940011070544514076640000c00e5951040760050b00003452402101c10441e012620740d4a25110868206c4da412450000342c10302e08440b10070310002a0828952810340302c003050944190901584003203080340100c0d6445503060784400b0100321000d80031351000076903145900018001d0b5031a40c07076 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 425826924 1250 425825674 425825681
    0x1909060e010c14120f130510091a01051c02130f0510090603020603041502040b07110109080d0c1e0501020c031201050d0305220515090a09060e0408071401 68
    0x480360311907510741a0104059034012091034010814404075800e09000e008012000280101400c0080711a0804280f1140102e0b480078261039000e011605096081c401c900d000d1700c4a87d07000c464142c1c00050580c041841d5030b1341c480c1a604081c0c4a900f1125807000d80d5180250704a1050342c10901100501c20050858081c0c1c400e800351180001c6034070f0600d40e00c01c0035507040341d80c030a4a03007515080040c00180e44810480e03410136008050b40668581d00c40300323140280300b6070307004006441d80000c1c03100c00c000485c1506074580340300740c891041f2984e48410841d250a40e81c0341d0307100010b803c2d080c41070000b140c400c900700724180039072982884a000b40d41c0705d9089034001c6620111990000c110290035000001c2c80b076001d09810f692030117450401c2d5401030803600440c2d03402c0242c01c98652003012261842504c01000305801424050714210303088070404a6488985158060841c0d00e002064540fa80d01417102143c41988564000c2e941c0d54840b00c0d09a00417030803c683d00c0e20094042d081100c401d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 425828174 1250 425826924 425826941
    0x9290d05010507090512010203040b010b07110a0f0501110d0f0c0c0b1303050f0f030a030504020d1704080106090207080a0c1e0636021c08030f090105010f0b03190906 73
    0x40310344c2d14103401d1400f0000e841c503450014101980c0100100302c002848111054111520078003a00e880703281510b08891000480c41c505500090301520015000103400204400c40f142a21007803004201d01010030348030040c081004011034449540e110a2078400c1c501d0344542401946891403040d121100401580c0c020020b414086015a50a0081c0101408004900745e02d07000200701700b000e00c4000f40c1e220701030083c90000f403503034480000e802d640703400e864040c0441c3d0141d034911000304000c00c1541c840e0018050308400d90718119020800711046e200303c1d580250032044840c140f400060b001c03100107000346011030b20098280c2440c01085824003503140924461480811091444150f030440c40c40011609881c0c500b542d010140c204007207a8001642580551b881500d40b0369007071030404172109a0314002c0034144d0010400007d48500c2d007401c2d0048510400034005a61313160245400142c4501900e64140c2c010004101804501e4400010204a03800045010106502d6000c121080c41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 425829424 1250 425828174 425828177
    0x30b06091e191a1f08010b1312050a050105010801150b030c09120d0e04060b09100509030d1d060408100c0207030204090b040201090501030e030f071505160909290d05010507 76
    0x4540c0c1c8580b841c00e801c181d681080803c00f4120550341c0300800424620043c0306484140d0000116480008d0714101070102a01c06070301c0d0401345c41224902035698104242e000e40e459440c1600119544a0600400f40d0182918959508a500705031254069030300c06001d1280380741c81000929626250710441150400d81000a410718108803c3c001e48900605401144124500107003440400c16020130789003d0710090b0380101d0421180e6400380c83d2445260000ba0741842200361300c01c04207030701c044102e07030640100c82e80401e590100c4040c81000d02507405402c03595002000c00100014460780410781c039034400c0c8129000541e0380d030040b030102c030180d02d810f0f00c1c200009400c10080d5608040064010b100a103400c0100c60008440b0640f01c1c025800c002c100d4a00000b500014444031941140c078000c1d01260401c801d040c41c2e00c8000641100e20308100110301c4244001036030110a105041958621038144600d078840411940d807180386101086034045440c4e41d60a0214009200e003500c00c03c040d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 425830674 1250 425829424 425829461
    0x203060c0a080a0510031103070929060307020c0108041b06030212090c011d040b06120f13020603071b05060103081305041b081e07050301030b06091e19 67
    0x1c000804100004006601040c10a401d020707420010110003001c03203800c40000b484440006d40081d00701400395200011301420049140a0142141c0036101800b0603440100c8141c2408818801103010031120f540150700400e0060100754000d02c10141c0c000e1083c04110b21415940c552500e50010780e030401000291701141110300314076580c00180d00550284000c4c880410b101b400284400d0088403600e2112100c01505442510b0343e422010220100410983c2c81d2400450040d12500301201c5103d030340c03a40c400108803001501c0540901c09038000c1c104615541c1c0d4a0015a4920303500500048144a403008001c0851000d0000d280a5480b5500146c0d465a4203c1514614032890300500d100e01c0c941802c48403150705444040202041a003040b81c01c035a1854003039143c800c90201c0d89d1440750808020030001701d60000041d03050740d200e05c0d443d101c40e4a0350401d114001c402103925802d103900c10f00d21681007800e01208079034050100f140c0d0001c44c60101400e4429a81c201c00d90629a00c913 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 425831924 1250 425830674 425830687
    0xc16080403080f1305010c32060a0f05060604030c03120923010201050c0906041502030c100506030120120a020f0a0809060a1b050a020c091f0f18180203060c 69
    0x954094000801003440d1541d40b4501c15182c01400000e45006c181501c900c04582000c080451a00c0d01c00e0708d450601034540794540300347c0c418003800390900d2000c6203070b2404d00012035274070b0400c0507107050340e03000802400498110f54814072030803424a00032090043c58000004c808403410024040c03074050801402104281b00d001a09541c8042d14401c4600014420b07281130361504d1050750210787c4100c0452144070750141c0c0030380c00c6104140103900c0c075004982055003c400160059402254140c000308030713000f03403101e5050034148083d1041081401c2009210210381281d46201d40001881c08018540a140c90841e50b030b81d4454441500410044d908016003900140302e2039502c013511002c14800034001420044070040b04c1301004061000101d50f0202c01407007000114180200a810400719052110901e0544000b202e18a8100705400c040480c2c0d08110a000d44201d8000e805408240d80901c803071003000d0300096184a0001003444603420150b5410000c26000d5960041610340c0d840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 425833174 1250 425831924 425831947
    0x10090609020406170a0305161a2a0708090112021b01060806042a030614090c010e0a061d0904080903060c0c060f0c122d0c16080403080f 60
    0x900f181e014542013207103501d40300b44034003010038045a22585403500d140d8500b10b8078100160f00341403c20240c80d0300040c2009134441e14944400c68010010512000c00c8507174202000c0301001050154803541c034000f4440b007030025030014003900e0603003014100142e01c201c408480500300d8116248484030030281818100480a080c490000640b02e041c000e4046807030151501c4e480001080700300300c000325080460194100e0301c262460003640e8009010300001d0340011a0400782e04060f1012003150096020300140381d801066480000180902402c86d8503142040655584501c2e800b0b241c1c00c050300141704a81d5589195190348520710600f509a200c00e000402c0c140380c40b0700181140c0c14240204084c424002e00001c25070381c8110010a06051590340d90805485405050046c040c20700302c8109110700c83c50302c40240c02d401c0365000018041c50405848443d500070341a1491242c403001003006040da00030303081c040785001d4042c8440b2441d103640d0341d49042c40307079210004070100514042150390445 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 425834424 1250 425833174 425833181
    0x270905010f11090f03030405090609130501020f040f050d03120b030c0d12090f0803072010030b10031a04020306030a08040801020919060e010f0912050f070608010b03041202100906090204 82
    0x44011781c0218240342c06e00021800045014082e188646079960000d000b1240243c40c042d41107500400075500c459182c041d80299800074058094890f030041d5001c582070030015a00440030b0b415644040f414121140c182d0f008140d0407007801c0e0140074004420342c0507141c008001c081c80f80301d0054283d2500da040002400a0490b403c40361108000c0b00003085404030010940f40340542050051481c0800701a90241201000301c00390340243c0103001c0702d05140d40652040b8008101a11000c1d040704211100320220780d00303200c080e10b0a031070f80144c401d03041c14550701a5034040344c0a41103c4081c1519150005540c0050340304600e00c0c0e40000c1c41050a051202501300c0fa107000d580800c0540307041c404064131001008a01d241001403840560100c00d04c10000301d80240060000e85940803103a04001c1d45031900f20086131003d100740400010001d104500c07103812640b06003000c904544541eaa14803410301c40300c80709402c41c81030003000e4000215610407215850b01c114800192540300f8414807098 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 425835674 1250 425834424 425834449
    0xa08030f0601180b09030703060612150209061e090415170a020d02010507030e0405010b0d15061e092103030f0b060a120905190c270905010f1109 64
    0x40050801d024079415410840c01410340341340000c080e44854882d80030030b103030895640c000380000341450710003d0390440d0800e515100d03d004803451304a47c2c2031440010144c1c0700304843c180d0001010008414a0340f489c644154202e0541c0904034a800411800181550070000f05591254074482041086103c61503040c803460070407070044d02644c51b880d00007031a0901812800380c140035000402c001003503c039441848904600600070055541c507a10b008185410244482001b14a41606200007202400c00401100c0c004c0e5540428100400442801004c3e440000414490350034800b00d0344014540c00e184490f8501f07000c5400c1d024107402c00900b50703607901d0b043d06445440c043c126001c640307454044401d00d64550501400c100d0f020300d9048003d044184000d007141c05054183c2020769403a04110701c1d031500546180703003c9512803401841501100041280ca69240038401c83d404a0b00e4011201c01e0707000b40000241c29481598030410b9038485411400c018030f0005a0084901d0641e106409 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 425836924 1250 425835674 425835677
    0xa09122a080318010203130b04080d0c020604090902030f0f16090203090706050c0c06030a02070b0c0406020c1912050a120e0306011e1508010e160f031d0a08030f0601 73
    0x82546000c1049899100d007075500000c07014591a03c480c0340e40208205d54900b2400212207442640d502e1041d40716821034080c1100d14014031240300c0b1840d10644108078010f40003080d5500c1e003841d08520314024184c2c100c0c2240c041c061948010681402844840090134640300a000b0701280c4001140b00d042041d0805100d091041c01400300c0c96030000f82100603540325040c203e40c0c84010305405844e105060403c545e012200108200040c0c60390340141c40d20700d00c02c1c50a503400e074640c01600f0700e49010f603010740d2005034403040c8142c21030310b884a0819502504d040da2074070301940701c07030030403d0700708a5610560307882e407160f445040ac100d140c0d00c1c04d449070181480e091014180d4000025200c107410b101d5054060200c40fa004030301d03c81c400c034020041545503900c01d0070131400417010780312400c00d00c44c0760354241b1540000b460039480142a03600c05549030784d520068a200f40c1e02540140355207086404155044400e81d07211441c1044040d45542c0550300680d201d240c168429030503900001c108a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 425838174 1250 425836924 425837003
    0x80d060b030411010c0213020a020c120f06130f12020f06060f310212100504200c10050106031d160b0309100c031a0a0f05060a0912 58
    0x404074240b0080003c0000091800d0451102a0300014140700c2c5148120301c0300d0f5100041607031140341c002070f034015480c000b40c902c0800401110380003034950310210600c68403500040c002420300b00030103400c02c01d540e218005083c0c0200075500d4440c0246907045040d40968400305028a9030b03041000001d5222000b03c0c0d440307400d20000350201d007101100905800503054081e100d00c0003201001c080b5a0303c0601200d0031512148040b808110301d40c0305441c3c00c00080803403940401c25003810b001d074010080200080e5200745d20b03a52001142030b804045031005502550a1005504401d4015a4000e0802d6600032500641c0000c203160f40410039038049880d6402002c05800a490741d00c0030404841a09000580702e50329001d03042e0900a41c142d83c01181864036011100a0383c06901c0410101d007041040307107144040c942441656800e0340681c800302000c01100700120718088005214544441c5071002c0e2182d41e51006024281c1c2c0103000b00c0c0c07001c901c003403001d842c04010310150b4002d60340c494455 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 425839424 1250 425838174 425838181
    0x3030b0d0510020a030b030a06060e0c18010c080c01050a0c140909040b07050c1204090501140915030309040f140609160509010318063e07050703080403080d060b03 72
    0x603555242c2c0021031615a0300403c00c00009800f075880f0816210025082c1e52940340c0038909030b401001140070b4003001c0c2808c440403401d54510340d03042c0c44d031800d1410030100803031000d000154bc00c040140f0302200c805c0c0b410042020482c03000c0c080d117802160011130114881c01c2c005c03000703042c0d04c4079200010035000042c00034011b65030724244220b030481e402c08280c04068071504021a01c901c611000d081d12482459440c190b100c0c0c04c940103008542c403011081210341d895004e0201070300c6020509581c4082d40c4400f0429884683d1405441100b00604030b91901c0411030119065900c00c090703e0300c0b02940d0300c8070a091138055805440d400081120700040c60301c0c000483c1641042055030806c01c1206c080f84510550b40203031301031902d008405800801e00000e9127030010182010001040701001d521618216021412480c101e0614800d01203045a640000c202032494011f00f405544512038654004003103007100004101a60154007143d03900c0407421840c0c1f0941d0419400f0a04250040040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 425840674 1250 425839424 425839433
    0x20106091a0d0803060105070b010b04081626071e0312050901090e090a0807050d1706030a0f150204080d020d05070b01050618040c030f0b030f031b070801020a0503010303030b0d 78
    0x44490950300090041e1251600e000407107e0b80a8250010704000c0804004659207030707150054000c40d86540c08841e00541d503c180d5510420191084400000c000102058041050003218810710045403c0703445203030340e600d00c0060140300132080c0244244400c03801d000380082007114004500160400500d00080c03400001e110302d20a108180c0311340f6020021a02011040c01329074100c40d007041000b0780b280510b04209480f5621200301c000800c0341c03c10b00c480d85182001c40244181e40040c0500007181d0a074071059900352800c50220350040068074098005201c600c080e00c09040e644000f0b003a0380740b0154020f03140000c141e80703a10a01c8000d111b03200014032103864541c1511800d0300d403e511084001c1d0459201010f0180c010391003403d0020041800b41d26502801d000c0b0402e0900380005502d03c4189600c80c26103210319455900104002d90000100040080000c6c01c44012940400e40d01e420003402c907008051120001900080100240750f414050400c200e0b030119250400341030203641d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 425841924 1250 425840674 425840689
    0x91e032309061602060301060801050108150604120507050301060602030306091e0406020a020a060c03050a060b0711090402030a0503120f0c03190b0315040c150507030509042a020106091a 82
    0x4480780310b80000507040c10642c1201e50b441c00450307030180a441d225612a0f6000c0e060744400d00903640080d6054002800c00282e0009900000c2005401c0618103418100d45100ea403001c00f5080d1600c0c40380303540004140c1c40900c1100002c28070f90340039549904241d130400a00c840c000d0a2000300000c401000140011700f10317007040d00107a002c0001607442116140680c181500703880050704491409207042c800503010340200e440303103011032400c01c0540d03103400c000c03002c9000d10074002d40f40f00c50320701c4020464100101e5081e0407500013011100d0a0455941382d920356401288400c500603140b500344601e904089032195003002c00e06c00703083c2c01e44ca000310f407801c1102c410341c0f03500d40d0f141d80f26510103010361014400c520405c408040708081515003070602c3e0024000a124210715001c40b044084442d62044094500943d4540d82d2546440028800c10000e440d04c5078500b10405400381c4030140480100340740c1a894102c40e00045101c81c82d0180d413000f243d0191024880356005a084a11240e4500c072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 425843174 1250 425841924 425841937
    0x30e0d0b22120206060a08150a02030c0403021c03030501060c02130f062105060108010203071e032702090c0405060f0d09022d01260703091e0323 64
    0x30322422402660707000ca840000c5a4140151040b10104146101c2c1c55021a2441c81a9419241742d000a50341e1101e003a40d8000700080c04074025130381e4001c02d1291845400071504031584d406003509003078498001840da0340401401038942049a4001d43c10150140115801000c081c1410003041401340c0104401807154410100749644c1c0d5a000c00c081641540254040c28101814a1540311810807814402c940e5a009444911032a800025840b105008a0384207031002c0ea14a4842c8000541d002e41258050440c1070515890750606500c4c0401d11060400d20680214031662403603040c018044861400b40058100b1541040207012035101c0b01c0444410811103074002e03a4450401c42e01c00000c00800c0320007503000510360302e01000c2840e88002181d00c408200056554107040c580192041000c0d14000b183c540a8079100703594802000c80b0441d4050180e0402103228036041d0303100b400d1501d60f02c0300041a40801e002250525900c283c2d10206d444c00014420160045100400220700905 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 425844424 1250 425843174 425843191
    0x30e0601050a1707090e0c03060a0c02030a0f0302122701060303050316030608160f0e07091205010f05161112030f0709030c1d060303090a0513020f0412030e0d0b 71
    0x250140c82c4128804c10a2800400910400300695031040000985641704400814402d209070783c017107800021180700784a2280c45607002145050000002510188083d048040074560709000380000c841051103c9072080038554142d14288400741030090000d100c01602c0f40c01a0300d495402d0001130380050031641c2042c04886403807090440c0080032005458680c04c260010301480400f111400b00c0c40c0200e1b0141c40c005143e0078100d544807150310390560300032201d4000203031403402d081114095120f460802d180c000d0002084440480f032055003074503010380316800c0c05103a82a04d25a51503004020a450a06100c0680a40340000206e20362900000c1d105104410a03000840d6115005030027020096034080c0d111107003580d036117845100101800c1d241031a0780c12002d00040d04c9241c080111440c28078001c0c00c402120f07061030188001517081c0e4140e07200140d403c202d0041c0314640c210141000704440c0c4099955102503190052503400800c4c9141e0092041c01d50322000180744c042c804d075100783c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 425845674 1250 425844424 425844449
    0x3090a0b0a0603050f100c14090d08040e040f0c0b0412020915090c0405044a011508190c0603020a0318050604050706140d020f070b07020d030e0601050a 67
    0x80030307208001041240d10042c113a00c101106003400c15008209804d003500c00740010005031080c004103654209044981c00010300c000c11050750b481c60441c0485001d10701490910f81490b8480c0138000760300310142c400303550b5032191504020401001450040103480b211041c0c41c20b046c5403540340300b0000c200d03e000a108034000f000091981c020210340c46135058005000500c42d0030f000703468501551080c00b07282d02450800907044034500545000c1300c02042c0920303540010b07412080c07180303904620130b4203c01c4010035910b00326900f44800b4014016950443e110f9900389601d0600d60714038002c1980300202d1580156038035400403a45402e0705504840c4141805a541c6d900f000e4228010103411a4400348001c07211450014000c000811030700c218800c030126031741c1c46d80b02e00d020b41c3c403908a00311040281c02c00700100703000341141d9000303005c0c200c090362030781801c0c000d456907401c00501c021500d44d0b0059100d6900c10110759031602850000ca00c581014104550412011648071400da0240c4016102c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 425846924 1250 425845674 425845681
    0x8120904090b04080705011b140304030915050a091a07030804030203091c11010e060315031501080d09061e0c03050903010906060512030903060f04051218100503090a0b 74
    0x2101e801001c000769024902c40e400340b50500d401d00d002c0c1c00002c000e844640c68491049201c00302540500360301e0304c040c1c80741c00074851042d500080d01d80c0028402c81c10000720240c000740444000303030701012100860b207a6907154091000018041d120581c00008035403500030b1032081c80808241205c1801d40c040c0740000340d076611800c1c2a841d511912980540102c22250140440d0200074018039107107200740c1000c400462038200441d41e00d0301410703803d031303010008202003005001c440d00308054241c0058103070b41a800201c94881400c0304244d000d02c0c007607080b0000401e402a40710745000050300b45d03401c200d803000b0303114110842d2030401c000010050180c5c0703e91281c20300d0b0280b0296064a2001002130120b000a458a180649001e10a0034010040c0c18070402d251180401515489580034004149035030340c1c0c45e2400149003002c1c005482a000710b41c50513030b01e180014010504080d000c1c004e0394461480e08140708031000301c10300b0b82080207401c2c01444072407480030401036120381e08108003040e20385 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 425848174 1250 425846924 425846929
    0xc09190c051e18030606091909210219030f1202040305010c030c02060106031404060209060903030a09050901050a18110c0a0c05040609090209040b0406150627081209 73
    0x410034100304a07200b28080369480d00415640203080b4080d1941031a1108400481403590394003090b10320f0366115a892000501c080480746420101184004012802e2076075070f2076110010750540e4400303040030020788110104580401c10107103d00d40340381600762409460746009000590b804404002c0003070052596603291440d40640d0701039600b2400811484020390701c0600102403440c034140150203030100000b50740f40139104050a040701c4d2030080b5600c1d501d0b9651080290301c95444070380e1102044c46821001e072410170240500444603103c201555040c102000021074059000c00d2290418103014000a500424865005403c0020100301400e4042614a503070084040c0403510b072007803110442c00e000d460769030301003100d0301502d041111039198010941540c502d03c0c400b07034001d2801400320300000c1c048141d03180d201d030007280300256256083d050b0700014811603010313200003041808580350a0070300d20041c4624803013203100351101c686064045500c4080c0c43c0302ca180c407140c000c1122402c43c2c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 425849424 1250 425848174 425848177
    0xb0703020a020c0909030706050a0c1d030304030b01030507030b0f130209061816080a090f0224070309030308100602120717030109021b0313030b1315020306030c09190c05 75
    0xb0034009041c1590f13407600a107017960380d4126803000d4811500304400f02c1c00320803480c880d014080341c007a034480b0782c126104145000207190404285816100c20000000450640c0301c800e406944100e02600303985c3d1840c28031215802001e48103001d241c0102e800d2120301e85d2814401103005a0554100d040b1350307202c0f070018070001410040080500118000c0280408000040381001d01240c1c480003040e450340c01000007261803840d001085003440428240151901e12050310800003800c0528a003150a20700102c041c0c2c01c00c031411404141d86030418800c140d046041641d10010400140f2201407030041d0095668443d101c0140302d200c2c001603003e00b40408000c40034001184a506d8640c0d81d6581d0416000075032120444085e14040c045041c44200004001c0b83d001103192900718cc0079900f50b072501140800d01070a81c038030000b100700071200010b540d0f042d00e10a90104040060712032400b0030904d4100b00481d40c02d64824595142041205d6140100f5030b1207880d0841000a41610140d00590701c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 425850674 1250 425849424 425849443
    0x40e0402040b150306010315030f0816050a0b071d130518010e0703030e0306040b070f1101050a06030201120903050f0708040f0b03071d280522180b0703020a02 70
    0x181c448008a0006143d0b1005500034102039800300702c0f8010324240403104004030700008041584584020700842ca01d50f0140c01c03460a0900c54000d08403c40d92524034140036800c084840044640c00c100010703400100c601a034a12401d00040b03003594003400a504446145e101d2410555501c003c1011400c003403070900e010b440720784001c00c0b0320103000010303990311413032440101c0014020480741c050b542408606a4000c55102c0c022880c3c541310f5030070588400c400c1000c0301c010130113a9080da0901d07034001d024039400780080c40e60002c0d01e5402d500004111170120001484400c1c10200382000081c0c4c0a01240c18000250781c4e6230b03858206600d482c0405116942c0301a2480c41b442038003090504d10480250b002e4407075604c82c00c5d0041c3c0700c40740703c00d2540d003040c1c2041d5203d400886034508004031140c0948052682010001c002030310340001034040802c0501c003a840450a6030010300c520201d2296011500400c00b16029858456070f50704c10814009040000305500440d13032507e01030013009910305 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 425851924 1250 425850674 425850679
    0x6140d0501020f0f0414030d0822020405010303110c010509010c0303021602060304030207142d040f0507020106031a1308180a0b19180501200106090e0f03040605040e0402040b 77
    0xa03581c1d0032141801441c1c0080c051a070300e2146046c0e4611103483d0014034082d49110540390001c10759984464a81000b500b00c8981c000704031110b46550050b40c0c0c521800e8040c3d4883d13240c0f05a001140e081c001e1504001c0b0038817905010042040c1043c60380c200c2200a02a5410301e005039540d082882080ca01e83d003030442c02500050f012051104041c1c001c075034001502c80419080c884500100100501944e840303004448000e5501460580700001450740521508040c00206403150885000c4c0708039081154540d0060b5507801c0c040c01080b00e44011603030704001900102085050042e080c114406051400a100040001e0300101c0346111b10341070141124000c0c00c410071656107111800040d81310050020280002d41420400140610400f070210b42100c00b8a04000c1c1c240301c010754114020708070002ea541103034903420303041082c2402660081d254a07800400c4210180010b2481d00340314580d80307200c40d00184802e0140f194030500b5035003203d000810100d06a2118004180140709543e80c554 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 425853174 1250 425851924 425851927
    0x1c1718121e0f030f12150d0b09011b0f110102040b031305150901050109060506120114010e0424080706050a0c03090b13030c06050a021b181003110406140d0501020f 72
    0x1850004008041c000006040c1c0800034255900e1b4019100003d8090581c0d900c07a240e21215004503104450080c1e009a424000040c0b0b07902061194103580507102942000522011601c41d4003070784031800c4415800800000d40c20182030260784199400300910080582e9072800201050160800141e9910460034014102d1801d08554407800f130007090040344a828100b88001030fa604049044409070b02d20500007041590801002800180c0501d107114100061305152410355a5548165291203140385254451111030754404440440076070300c44211070b00040010000160014212408041c0d0392070300198401207490b00340d4074034440f600518140480455a204003480d000c41410640e40511491f41460343c0d10401112a031040b815140c00603000b04070035906200d50180c040b080d21030001c01c83c1f6002c0880d140c00076120320080355140850101042c0c1002403001c58210400060020b0341c003449500c1c1002c002c9408803512410050050046030503107800d0020a43c10b4500080800000a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 425854424 1250 425853174 425853187
    0x33040506010c0f0b092413140f0307021005070c030b04170d020307120b06090d0f020607030507030305060d0b13051002040b1b0c0108061c1718121e0f03 67
    0x629154011200e046281c821b604042c00c03642a13500410010035000c88403140c4d00e94901010a8400070700200c22107240e040340703d0705006c059044c4800c42c0c0004904000b0360b01c0d00314900411100320680036000d811710004000200100b00d4150051007900d802040b80e006903107481c607215940780d89880170502c00c070002091021224140d500214041d80310380d901c2031000d14000c010801100c0c0c4a01405500c071004208640d82c0d0700700b8480305000d690042c424140c00c602079402141550b404040200e0000798001000700402d50184151900601e05440d07041986503150ba8800756104060700c41c0d141010080d04000400c4401c2003000060000004195200d65652140e141143c005075902180728600352150803915000052920401c1c005030754100340c90700d81000384510a20710a0001c0081c01b920650385020511400303807040113601602d41d142d592200c01481c16415605603441a01c90760981040b4500841c1c0000d4044048419100032140502d0400c82d07145007460302105c80d00c0601010401c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 425855674 1250 425854424 425854433
    0x90a020315010e06030105071b03090512010b011e140c10061410030203060603070e0d06050709030605011211130e0a0803010e25120609050f33040506010c0f 69
    0x181221042003c407110340e1150300c1010f00b40d507801c9500368002040c4190b0142e01d030050541c070155032402410504412174440300843c3c0c1a107003404c0040c4880c0c1d1a18008011542c0c88000202012806103040c00705c100b01a400618440000ca82c00321208004140c15507008014001303143d1072000c031030041001d0ba40e07803c4030301828500c541303a81d80300341510b50400b11414064000c0328441c40e001002e50346183d88203001a9003071410346807590b4100c03070b40700703e00b100089282c40380a000c0c200790b403580742c030f681e02d11315048060742c42c160041c0304a00444103103500001e41c868040d010021040308c996084940601210300107001e0068003002510400c8044c60a00111a00440c1a11980e240103942d81c0e640d000802c0780204c1410034500700138211144600050b01c5046080c05a203011200820072690b16404101920701c00e40f00140710419601c107010b0007051412042e080003058240c2c54411818410a071641016030907003140c0160703103030b20014429038429902410003590110f910b034000d4405081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 425856924 1250 425855674 425855713
    0xa1b021b040c032c0d020a05060105092502010911060f0d050402060c030403110406060801060c030507060605060711030c04150306050a1103160206010e280b040e010c020c0f030d08090a0203 83
    0x4c1345040c500821030003540e01840807580500c0340b1313004002040c0076481d04050082e800383c01031040c802c0040c80014009480c400004910040540364000700d07102c40c42d030030007141c0603411580700381c03040d00304000c1d4002107a45181580c003401429000092940c0c0e441c00400d07210301c40c0445802460200180c040108041c410b40720b0722000b400d4808005464950748180e848400078001e0750081102c8003841d00000b8400c600a100c2144512000b058140e5074002141407034001c0700c0700301c030201490031251100d403c1c20045c0c9528454112010701c4002103155084944040c40d002c0541005e48860000c0c41c0340c50709801c030703124000e00220b01603641e140807080803805401d20300300100180074800001640c10101344542c0c0c001e171200c50b984001c0303d40407180484189070981c080718449489880410b0155198803032814250800d800208440044410003400c0c429103a150901c03c45001101600769140090b08640c000d4450500b20710381d884210382540b80254000c80213515100d450001e0201841e903d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 425858174 1250 425856924 425857001
    0x91a010f090605060306030601050d031b080301090509010c090b0a03090807111503060609040b120607020304090b090103081e0d02030c1b0d0f08070e03060a1b021b040c03 75
    0x1d0304100d80ca4880003006a648001c0c1c815a41c5a80b003c801401b5600c0c00c0c003042c0b81002d1090601c80380d420801d490041c1c1d03e42810b4000d441050011004002d07901c910b0141c507034000e04030302c000c0040340452107000d80405028010001e900c503010401602d45400395000d43c0d40c10360000109900c0d20340c1454082464a040622940a036050f000c2d442e6008400740d06490040e50000c1c50507017050888000d0000502070b220540d84e100d602a1500c081c091018800503004000d1540999555400e00e682c5100750366190b450340d0700440300400100049204401511841c1d0011850705a05041c00e80c202d46c03190150407450741010f1301c00000c2c0034040c4a241c004000e000590b100f00105d0109080360300340c41d50400e4603600302090106403080b01c0107126125040e030007c0700e0300740000b6541000c40424984002140ea83c0107440d9900d04444812008061041d00171003103100400c610081800701d480c0d03851a07030b0342e4a8011a21404590b685a0094224a0022030308030b903c400c1c1040046040c5043c41c1d20389 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 425859424 1250 425858174 425858189
    0x100f1e0512070b0702040f0c080a0615120c030204241202120609090712050714030d050a030b0d02040f020a080109061d0a0f021603082404091a010f 65
    0x4a5001a490400521804400301e854000d411040d1500c0400603040d4401e1004980c0996035104540b003000451043d4a02c03d0840d98825a044c5008402c4100300e0305103400454842600f50052400564480304880d1741c40034086020a80190840064000c0e019135080701080802204c40c99890b040740b01200c00c41c51199548041c6400d000d0940e00081748140e40c0c1040e21790181200241c41c90415404107600210b0080480b00316599038030b850300603003159143c1100c0a030064101080a08030f000c211001c1c0382002c4020b1f2050208a000c064203510070140100305058070350480b03040e95600d4914050003650090b0041c8000d045c0c2c00203950084d449400c40b01c0c08500c00d8000801c80ca9464890001518280c1103120243c3d40090060100050003c1110001030349442003643e42c81d03c1c90020700740761507650078882d111124529002c3c01c14170006000303101d010011040a1b9000702d01951070401a00c0a8800040d10140c0d820241c0154ac1001c1613007a14020190002440743c0f65280798004a6101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 425860674 1250 425859424 425859479
    0x30a02090c120c3402030d051c0b0108070f09120312150317070204020708190f080f0f070c02030f0705270601051c090609140a030f0503100f 62
    0xe5800d503508902940c08510407480f04605041e100031082c0001311404020180c8a4442c06a250300182c070308a280121103000400c04283c031001c01c04c4170f5000400c030540d145001c0c400c0f6421040020070041c80140300e14104025a0412100340f4010b145d40c0b000b603c400c00c09550f0a0f05182000303080014502d1140842c6490016401801c0d044c2c641d030b440503613174403040c0fa46900015510b001026001803038240e9019600704400d06c0011041381c01080c15400701c6d4440c4000390030318600948500e071091085428020043c080114240301c500000d5400f811142c00c0d1461512070300ca04030f80c65018207000035054880c020f0181a42003000070f11000f120f0f0200c4080301e844086007880c0c8031039441040170580d0b03020440702044456000301e006c0e1030081244100c02c40c5c1c856400b112030040e507640e078800342c070415903826460080c402c0b806d0a1078801e400b04001003000800c140c0e0300401c0d1200c40602e0b036042040200220303d0040d044015140100300001c4140e40407502c4402502000c42c0903802804210302 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 425861924 1250 425860674 425860681
    0x62a07110a1409040201080901110c0106150c080f0a0504032415271503030509010e0a0803070f021c111309030504090203090102040905090a140c06090609030a02090c12 74
    0x140d02e00d80c0b44260070054015495915142e00644c1d079600042e040c80304030354031182e0741c00004aa06020f4038035404a40000318402d07240100801202441009040c10043d80c4070681020031104011924103041107440d081c2ea808410300e08654900454000500d1981001c481c40342d1100881d414a008101141d8200310306100f00249034403281031442960101d0400c401201500c90340301070000342d0108038180100b08480000200011413040d90003c8001c50004200840256409a00604542415966049440d00301a441c6a8a0080390401040302c2c00c11022038045440f40c49000c80c0c50824080900307445006458550888580300a40d1402a088801c041e8040c0d0001d01400390310b99010389500341303014142850040658401044040b00359020440000c0d41001445010711440b0003401600e10b50f6014a40794400c600e40e0303010032101c1e90001d02c0070303d042d540d1001201e50409080f91015070b03510804010034189294440d020350700c61032803020003005419100003400411100d44441085a5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 425863174 1250 425861924 425861939
    0x103060207170c0c011d03060415050f250309150c0e0d02060a0c2103140603010c082205060903030603120a020d050304020d0b150f03010b03062a07110a 67
    0x70b954071511107034821390321a515540103100e2040c07031078608060301c0062410000400d00d041d000340c0307086455880c01400c405020006118840d0041a000011659030800004600c030241e0351004414541c0781040c550442e49000e9800086515400062041014a18085640200a01c800c1d80c00825040c0103000e0701881c0c85855140302d00c1d8014081e500b441c540e018101c4100c0c0e131513a4101c5612001c58002c1c24a0300e24809030303401c45000340e035000c90086108291140c860102404084c0640e040074044544140c00511943c3d01410f03050084440042d0700348601441031880401a0840c090b920500180c2000400110302c540c0054048407000b50820324212030f28402c002004006801c5824115102ca21500086400038002491808407001a480da10500b401c10b4a000d880c401c40001182c0003820560340c3c42c0d2011500b03c0080046402c0140442e4591400420400d03d01010501450400503105c1d41d01c010450300024190701e8191038600030b0b602400710f4040078030030764080d0310010300203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 425864424 1250 425863174 425863177
    0x603050705031227031e01060f1502070b0d02070c080318010c081602010e10030b0924130207050d0302070c0906230102031b0c120d0207031712010306020717 69
    0x100c41c00886132140111040d101409001200040c40c1d141c014801011108080148950601c214082c00003820320f00e4034607104120161681f100c1410b007100102c0c03850703994000c00c200080351660303e602ca80d256401c150000c02031043c0310004014100707946d8013180d0f24030700001414032101d81c2e4041c1c5401c880d0200c01516030203501c680c010000340c81009042901d840d01201d102c5082e10605000b001c4070f80240000d14a009008880d20009958504201d000c1c0f61078284c5e039400c00c442030546211080e0a481020b40c601c011003c603402031000500381c0407039284c0d643c1107922050304131003942c03c88540f01a0040c0a5805280150741309101c200d00841c0c1380e405c038440c16048400700344d005007504d5030b0001310a0303a03849071150300341c11343c0414070800381c500d00343d40c403065400803182300030700b00e000e40450810100220301e030003801d510350010106880158002594200f6250488034100c40194252840d00c1e8600c905e107151400e02141c2c0d0000400c10500f074014040c01031249404c040c04040c0c4400c0e00100303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 425865674 1250 425864424 425864437
    0x615020a0c090b060d02120403080105040b0f040b060d0204030302070f0609121b030605090f120702150310091b0f0f021011040302030102070503070c0608040c0605180406030507050312 81
    0x70761801d50800c00510455500030b0b5401d00700500381d41d04251100020500300e82182e1100300c80140000104420941c0c88203d05014042c11201085112001008901411940c2132620702036607490840c00c0c520390311082901c0d110148080199a1561130f40ba0081d00c589031846041380e84c00060401203440c0e40519140e1040d100345d40c1366100300c2010398680004142a800400c8c0300c80100b00d00c040f010a1a90052500c00c010320381c001e016078507482c15a90714200305441c0700c0c48011014860000143e55041142c1003100d03049103030700d442c4e484800030f0800d41c5126031f0040d4001450300c07a0341ca003070090405001d05407566549451a01100100e016070b528000700d213011005810511455030303e407210b41c0c8000c4414032a840000d00b802d4507a40800c0c00c9901c2071a042d140781e4004601402004620000b81001c0e1030346240c80c00c3d0b1810300380c0e2003451b081c80900804e814030001280c0201c4400c85d1000d61440042c00400c01e020841d52401c2c40c42d285c800300c0c05180d00a00960554035000380c482c9003211907 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 425866924 1250 425865674 425865683
    0x9031b0f1a0304110d05100e0c1207140102151518070e010302030c0c1207020a08070b03040f0807060c0c0b18030405100e09071e03050c0304140c0607060615020a 71
    0x255540f25541c000c400c2582404180e48841c45c040c661003c06d00070014505601306039507001802421480e1520318184040d4a003901c120500401c07201008004507440c0111a079900003030141180300001030703061000c9502e04d070303100035004820841814614240f014160760280c540003400c0024401114581e5002c5640030702103454591455101c0d4481e60045910890100b411800e001c2c144071100c2c02c5c0a00303104401c0081101056203002d40c6410501c5100400b07214000340318807450b254004aa5000c000c00241014503801d04040911056808551003503030310032003c000c11805a000508010301c0c80720305441c40c10500000900c52007586400342a0306204800443c2060714090070050303030038041640e29003000155054500079031101e03241580910b00d5500c40d401c2c007104408500004d100d0031140102014105028001d1886c07038041100d80060f040300c180c0080e407031158181881c1c4204001100c4e0440700006035001884601e90014094a410143c0f54030000b4a40c401240c2d5214240070141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 425868174 1250 425866924 425866927
    0x13170d0f260c0d06080f1b0306040b040c0b0f0a030506030613080903030c1504140307031d031f0c030b090609011203020c0402040f080c010f080112020109031b0f1a 72
    0x1030419620710000358000c05140707100d8a4905034400100680c0c100340c2c418002a030004118241c40c0e102031161032a8140d940304020307010000e1400080d52020302400c05410390308204045400d2010b4220f0110240400c0030040e943e81e038030414019015402174802000103403900d0089549440e0105410380207032441c42e0132810424564940c0c4a1951059181607803502c000c00c40c1d52440c4100740944070075003c058201542602c2c05007001c41401c42400c148170705c00d4000300192400079800420042c4135440d2249640b400510150200c0d1038070202d040d24244040d40c15203128490040340c9c00000c2581034590302230105e41400814040240700981e081d40e40a150320005200c0c0507112070100030114042e10494462410000100742280d010783c2001c0d246c1e041104003400407042c204100f4006180030b00e80744a840e10f05a070000c0000d001030080c00d8107801034850f5902075a10415200000c0c68000303030498501c005d034045d11001c0c0b030220b02c5401e6049101309000122600c4031070111805000f50020710713 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 425869424 1250 425868174 425868227
    0xa0e041409010b090c0a03180c03061b02010c050301061202070b0c0414030105040c0e07050714060103021e0a03030315031505180f0d350702120a0c0813170d0f 70
    0x81d00a04030307000d803a41e4017242003c9070001050320a40300b04021804bd41c800600341d1410000740d86030054110801c0d040d0383c10700084030b42295222007202d0441d040d030302d0912203074815071011001070304c100e46010b015211014117021070440c4c20801002100d03a428500ec642c0d0005006160903244104e40142c07000d040c080041000240745841e85512200300e05d0114a412001e598080b88000306c0710302482607500110045c002c5051150405200c500701c2a240c03450004400006969002c10303000045c101921044a1200c07903241e03000240256074801000841034000359144401020200d5007140c429200f01b14148101c14041200072444030070001910002460a40954100b884540c4000240703440309042401c8001000300c031115960140740703104450070107480080ca003110004036904200410480d810205400a9001c10031750385c0030410980310403441558298603081c551203040b4103680e112400790798503804140f0801d81e400300e0311075284c82c44007814211410107000d20981000001344045 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 425870674 1250 425869424 425869427
    0x90907050a15050705191e0b060d050f010609050402030c0111030403140c060c15091906200a05120c070b060409060e0f0a110616080a0e041409010b090c0a 68
    0x1402240401420500d24091342540d4140c50b14460011244a40d00358000e01010400030200301045039210b0080f696120b01d1580b0b50b510044ca014000d644540b40001e010010032200380000c40e101e094200080040603a910032580160008850486c407a0045d28031040071980039200300b500704010040114281800c40c2d0340c003900e1943c05020100c452007401c4032100503680b5440101200030750007001d000481c4030520300469404020344031085c1a0030003c40016506030301818004904d800001c085218032004e40200091f442040050203031107800a81c1300223039504080207011410709003a0410441e070b100c11864081c2d000d402030042802c55a10b0108995243c25007224881600032040040c9001c4455640792500b00b410806827015040300e10300201380200c140d908010b8032000d581c2c1d10301d04826400d03010b40c0d90b00e41150003403100310301150120315140301d0445500b45400190041000d81c40b0102e14000e10f41049a4468080d8206140b000450510361400780c040c600002c00c050400703240040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 425871924 1250 425870674 425870699
    0x1c110604052a030109120e04052a1213021504120f050f1f060b030c030a0e16060c0c0501030902010f030c0c020402070803070206010e04050c04050402012c090907050a 73
    0x202c440a103041d81c540d0042d81c0d0b800e00c2605001032040c4090401100340c03d030040c2490304079400c00ca01c650314160030000103094003002103407481c0883c1410f41622012260941c828060074101c11012014081007058255030512545d00036402103c10042c000c040136146c04041c0b00e02d0007a0204442c1c0f80b00d400e000106607654015090740b25030309503000e0450a006051078010160003540ba50149548801000a128401d14015088041030340f451444c10000e44800f520001e0104000c40c6c1d0380e00f05030080c09074203000c01c40d1030141260411440556400c0300400c0107103410400c7e2a940c411a400081c5513020b44140c00c102641038613074a00c4e0b00440501680140030130084031040c01410310040c0300580d100c1c4010107055100340d54850310707420300180c02440d050050700108180d088000a0002207a400200300700c07005401c45002c01d86544a2004a84044000c0560440004041d41040d10000c41755080344510a0075500c4003507666546103003a6071490a80301d0b881e00540c810313005200000e034102c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 425873174 1250 425871924 425871973
    0x5011e0e1903140c120c03031c0b1c03120e0c1909020408010e0606030607050d020d090b07081b0316030e070b1309060e0103020604050105070609051c11060405 70
    0x100002a02540c07a141c4105158400703100b500039030401320a4030418076200d580001040203041c020a0300d02c1a090100f0780c0c900c0f50248031544e4a0102a014094010541084810070030241c4003c0d0081101408130550f082440c41c07c5001c24901c0a0040c0c1100e414400e00c0c0c90030480e1350003403000340800021302c11461070400c15404840348414010400c5000303400100000c0215a00006070750131040b134060f003010806041e2501c2034000030148103075681e00c030f001ea8400c0c10143d0ba00587e1900040040d400815440c1c60041c400390806040102c541e070040201440b07018406003004007580061403604161104880b072890003900d090260401320f11031703405901851010422103081c5615900c0102a0380c2100c0b0b065500340f481c000d014001d8030324600924000381103008408070254119400500306026078041e00703040140c00300759030052207401e0701304454003a0040203403081c0b00c5d000c4840e844085540c5000c0c81c00b081c004040306040c6900020364601c21504003024004281700031001001504802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 425874424 1250 425873174 425873209
    0x901020a12090303020f0c0d1515030c0311040509031b1603060914030a020a030f0302270103240e06030f03030a0203060f1804060506150d02030105011e0e 68
    0x301261000a0a00d401050085a2a86940818501e9480c0080c680000e0190100160700480b4030030149803110004121069030001e111244039201800350b40060041c000c0d440c0303494407070071000014400780380840ca0a0b00e01413602c07113507121004020310086d10f00c00d441c0304056901c20042c24000c07034101030003445101140d0b000e0340c4d12291080208028040703950800d0302c4442c0d440350301a00b00484500302900440505000d9410316403c6100a5112000300002805100c440400300d407140d03109a048544003000404c00f03400c00e0318890456016048480307846404a4502840300c03954a01042c81c48036006010f0160038802800c04901d0180380da405071600d9098401c0b8104420b13410002d00107580b0501c0440c10058a03480c025007001845a1540c0c11180100a80700312040d0305e03244e030182194015000130740401c064030703070f9004190402181d03c2d2a040500d0040342c460f0044610ba00218100c030400d98a103a410f08461f08c001d0351a403140b4030000040b491107141107034a401e000401000c0034100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 425875674 1250 425874424 425874433
    0xa0f0503060d1505070e0a0305210c06040c0504060f0509060d080408060906071403040201120c18030b0109050a020f0304030f0c020a090507121505010e040615020a0c0b0906090105090102 82
    0xda0351800c3c0d00041c00ea05000d010b403204200600260303c24a188010842119182001480d40e00c0d02500c1d05092a21003040740d511001d2503481c20182c00031100b40226201c101c81c001e180905014603182c2c07503030003460b10840c00c201000074800052940d0100340d40e4010816403c07900e900f000c02c8890740030900212991402880b0001c1d51030307010b02c0903520842c80e40c00a04164030f050701009202e032181200b90321109009105000250341d01c131541c0e4008004484001514001d05031054420201901000d4a0188500d60210400c040500c01c68100d9103403c0c0240003948484078142c003640105054007201010900c000760110b0b00c10038501803408424202100f445001e41c020413030101503604000b030301949510920406650000100501c6d407401d4a0810030801c400310307d07541d0315540344146410081c0c3c3c0c000404075582c07154800702c000d03c146421101e480300c504501035160500440165081c0303507404070004510340d6070812104581c5000700983e180c04d0130700c0d005480e284c1085440f641103114 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 425876924 1250 425875674 425875699
    0x803040605090f1f09031401050411010f20010e01050f06060f030c0d05010e010510030c02030426010c090509130312020a11010911031207170915181201020a0f050306 73
    0x2400b440604c20078103a40c0c0c0b80065003581441c0e440360301c1c0801034410582c500300400000c9201c0440c24400c0301c40c246089a8410102c442c1150a40c1202c203060840f0030300c0c481d5003040104154032442c0c1c10b6469100a0000c0ea44906418485c0d06e411980190002c200f0400c850046103010300440e0700c0503a58a44070305001c054404041103a200360852000e000c01080148040e280c14000b4511020043c03500307004c08906840001c0d100d009038030450250720f540d80340705c003d1030064403c042088042540200315075260400c0003000100d2a201d114080c50a0301c001c5544200c3c03510f014030441c0c0c2c00d52900d0a0f4021111007180003540080450001c00c082e07020080710207402030049040070b9016006641d40d078011402018141044070317040d03c0001e1802c11660f03000546a886c44000040740030f49464589000201081003038144400c10040c1030b9000a0010754100100d0020060f8101641c40c501d10f0191141e15508038414404d080300490303807801e10444070b14820801907900182c00350200403580c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 425878174 1250 425876924 425876959
    0x608090f010c050706140423010902090411010906021c0f050403020616030905120a0b0a02121f0f0b12060105130306062c0f13020a03030203070203070803040605090f 73
    0x102c1d281c581000143c40020250184100c0e030040b15400c06020000b0358503428995510502040d006648020040341450454580d440070b6101c603203481d8000e08008014507081c134220384511b800191660102d6049c01011902a1001614103580c6900251204001943e504251000c4a4a516200400c4000c000200058840401501490b10b10707000c040800c0c015442c0c090500f540070740007a4040c5a68101d901c21180000503051442a00561901001d442e04002c56029100305240900d25500c46803c2c4103503a624820042c04d6040c800402c2c084403511048030441035640c900c200c403040070090104000224410380c0d000d0b00010141005c52a140c42500c22140001c000e60056900a540c0c03102048500030080d2188003000c9041080e03144050141003d03114000054410a0380e184800001071040d009603132007500140d0014164a210365030b03494000e60f6076000c00c03000ca00034041e030000099094030005c1a41d042d20110303201e06003001e41c0c2c0f005010704511007812103903000008181c00e60350107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 425879424 1250 425878174 425878181
    0x30a0b0d0206040b031b0c032d04080307060b04020f09101e2705010f0c060b0433080c0d0c0e090309181302010c02061209010515090405070608090f01 66
    0x2844c0e1020b03d184c403072801002098442015043c6614040802c2242e003549040100403241c0c200107032071050300141010a90041c003480b242c3c0045c1503403100041c02080d000d100002030f1107042c1c0300d0001800307100200021710099000f0035804540c004800d008451507032610821070b00c20b1880780d140c8518415a14039200d400c1504645441c03003c61085182d000c2009008054041ea58990310601c2c90010728100009081c2500d0311012000c009048084004015540d04658200100100140807040c2502406282005540c448a005075022800903007401d0824200e00201c0380000d02408900d4441e4040c08005980c0450440b0083e6100b10085400d210f050300f10750151407000c00958451407804203010390b403e01490491071304c0c032003031003008059503070311100f01c0c4d409a080c40c0500c4500e8940c4081121400303403800c07260402e20b0440c100207801f001580706c540b1030000c0c091201c504480030814000e82502c00d407409815904410760503c5114003900b19113400000580c1143e980c2c481655019084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 425880674 1250 425879424 425879429
    0x120c0901050405070e15131a0421060207050105190e0604030e0f1207030b0705071203150b070b0a050c040e060f240c0706030c1e030b04060906031e0503030a0b0d020604 74
    0x403160082590307602540c00c08540301c0a401023500304189501065907000c480d020340d1141d02d8460079000d0a00d141210606185100b207070380810250f469150614166002c1e001c1106c0001450703500039140301060301c09000f070b2a201840711020307004640303541e10112141c00d40307160615041030005401d880591595071301c6564046c4030320060040541140b0344001d03200c6002e401c07581007017000d0100b580407911080d41641c001240303080c0001c3e10f1880481c016034004655004200c080408603655050180c00b00c6030900c9420800d2041056a8035075000e4070381ca010358007603400c034400d1440008400b801e01c410001380a103802803000c4c850300c0380000c3c0700d0036402c100301c02501440710120f07c40c0356001c000c02404000d010340742010700090f95261001010840503d0303060003500601c515042d52180039034850029100c02900038486a9122918007019054500c03080b1980c40c00f580201910300b69600002070006d91010146207540c90b0b00c8070010203031512160310b0303912075400410603006030b5602c40240b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 425881924 1250 425880674 425880709
    0x40b0d14193c05090a1e0309030b0c09030d0201180f140303070c03080603190308060118080106060e03060f06210105042f03030a0f05090d060b120c0901050405070e 72
    0x5050b40120000c01da40000e010440b0340c0e449034407a000003036080601000c5000d03074014151700780d2200d81000c0b0f504c08200e90014044001d070000b0f0005c0d0004040013049258800d0702105d000c101064012400c032002d80c001c1c02d9000038001071820002e400703081e1014000340070340c8924000c54000a4100d00f580d00035640100402c1c44201400200754214243c141d01810882c058403d0740c0d0310104400d541045800f009080010b10f1000801603809905104c4c00610301b071803143e1006888402c803d008009a000d420082044022000424507000500c40e1160043c0d101709005030b1901c5050101080e000f114102083c03504802e45a40d0316002d00c1014801d50180c94803c0c562600c0e440c150030748500d6030a02004500d00e8241d201a15100001243c1e00d036034092070100400a501081100c450085214580d484440c804541d0280300c015000020140c074203c501c00784103020b140043d60342e054140e0344d00d070300085c6081c01048145065804268040d82a082540c41900110000741083d84060000c48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 425883174 1250 425881924 425882021
    0xa050d0e060f0c031c020f0304020f04090501090605010602071217130b0705030d051303090b03060a050a08061e0124050c03160b0c04050904080c010908040b0d1419 72
    0x5517065074401182ca520380000301149401200a5500410b21008101034000c6507100104030254032268040000650054002c0110038001c3ca4884040c0ca070070b1003140018442c41001248100300504980c5507640d000140f203266842030810003450f90484a0401c0e0395041e642d40000c1d1203031045001b0403100b807154018561750082c0303115210448201600e040a000500300c0b0039030010b13400c82510001c0d01d081010071030701e958801e030000720034117416000242c121203800c1c000100000c00251080c040c0c0140a10030311121031003113240e91100c109208543c02d082c11118010b46009400203001c088000078503056185c0000c030f0341031707a240d0b9000c1c2c507141c0b00d0301d580140c18000344118010619040640d40e03d0271840c00d450180001d40002018001401100c07000613448011202544881141d950180000d612940e841d00e1050941e00f000c00e880e43c0580c1400300d81c01130a0303c20038800d03100d0840c0100e588909982106101e0040400c00c01c0e041e09898088801d264015001c6c0e0b04452115070b804040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 425884424 1250 425883174 425883187
    0x1d0a051e030111091003052a0915091e0d14100605123a080916030b0103060207061116050115050904140307080d060501020c030a050d0e060f0c03 64
    0x1400c452445aa12500d11004d111880141d41c802e408510802000e15000c1000d0702d402050b0001248180c1031500f101c80d05c1071450b00c40f00b103108090080e030601190800720f0300c141490501c0d4103200e8030011a62100d8541e901100d401b0603005105030780880546040145a0190f440c0d80c858100e001070080d0340c1e48400c0b40c2d90003505143c007850000d020152001c44494a49490b510f643c1c9030804076a10403801c68038a9000e429500440600041d0394022403010b415418200141003000e0650782c09502e80607030720750303048100800c0b0b0303441d41101d92050b03003400281c4c6036403242c0e002908006811100c1d82c0e218400f60452003020b41c00b902c100481440c2e881100c00840c9001402c6602001700d00c2841010035908102c5550741003003040d449504640d80051021401440303034194031911100406001000c15502d14031541390703121905451003078084641e115110360800d80d803400860b400074440e900241d414507080f489081ca00b0b40003070303001c1d00721801c191003003e96810540040d1890703a1b0b150f0012460307 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 425885674 1250 425884424 425884429
    0x607050c0114270a08180607060c031e0b01020a1202010f05041209081207020f060c0d0c12031b05090a0f030b090105070f090504200d050f0105101d0a051e 68
    0x9454510f40c486000344460031003940c902c440f6001d84070404003180010092002e0b203403216030071a503071075034030030010090034450840140007000031310034025911a003115030041c44100c0748250b8101d00c00580080c002c44030a556464502000d8205600c115500c0f0101d626031400b585c000d4501540c23046015148001c035100b00104945841d50080205a220312100f200000d6540221080e2680554192103198808800b04040d442450310002003441103581000c015540a80810400d0b84945d1500324108090b290803000e498420400c80c41c44200da56000701824054401010f4800e4080c0c03810b11030a0b942c020300803002207030b5441581ca02460078100b0060240038442c09501034000c2c280703861041442c6800504101da03900940d80102e68a10030702000c01d010071540d0f030b908a011305880d070b6150000b40307601024140a0b03d542c095500500008606498031950892103420660348603204c58070810740d003407190000c1c80c03105038115415903000302e40c0f0f803251002d0000c1000580400010710601a09 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 425886924 1250 425885674 425885731
    0x1008041514090d110d09050607020315090c1e031902040b0301060806160206011a0304110d05030c160522060312051308030405010f031e0e0d03050c09030607050c0114 73
    0x118135220b801c403682890360f1680207103603c0103071481500c03c1e80d00c0b1400e1344046881c2000b1800c3d459000c3c2da4240401001210008400c0c0501d503080d2015180c030202207840c01511107580313010320b5140d0400443e882c004c40726410809455070000300003056030403804011a0854026810000315070f041801005040b6516444000a100c01072008014940c504810004407159019545142c03601c0000880c040c4403402c542c1c0682d1000040070241304c1c80300f0b441c0003556940114078402803401a00c051b1801440b03940c015404031f4001404151542048217010401006003409031095075540d130a01101107062514402481441a11001e070f480040c015642c200700b06540c88420103900410060003686da00c03c10080c080001c1d800c01240041d03800d2007070f2460710311212480307000924054409603611000a201410f5081c2d940b01040706844481c00307400c441c8100b5403410b8141e0f00c07000108071401c0c400c0e001851100b250400000750301c00100d000340d0b1000001d85404080c08030752242413022150785003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 425888174 1250 425886924 425886947
    0x307050403030816020706050c010e0d171f1221200303160c051906020d1103010b0a050c031303060507110a050a110a05041d06061008041514090d 64
    0x44401814510b0100c0c001c6d9114210b000e040c081020200b83c0364420030094011141150303200007658056141641c00070700c9900410220741c0f10030b60300710101c5e40b101c03404050b5554980702c860801a42c4d40c144003e40e042140415000c0310b00d0386210301020154692806c0ca4403004005940300010380d20900c5912003a1a1000c200c0c1060b500100b05000440c21a480389540ba41d0150804014464983c01d005040c8141c0707508608071001042c0e0404100951680140002c600440c010083c40340c914400502d20f010034001e003c1d00e403000300300c0000014003a01c040c200341c03628901202c1c51f01159000300c00e80d0100a81c01202c4050300d1b50f0510500c142c0214a2502111604008007007a00f05a01c4541c0cad10507107920050003c1603c540c501555880c1c40700c90a006c2d01000d8801d03c1452221a81150144540750410455000d6400450602e10300585250301c66541591018081c0d250f40d181d00c0d000c1260002c4c2e1400b03075682c820001100c1022132203501c1c800c81000001e42400810792a01401041140e07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 425889424 1250 425888174 425888191
    0xb0906041a090a0b040602070803270706020a140111161e02130c020709020705060103061d030712030612030201020a030b0a0b0f16051501030521030609090c0603070504030308 77
    0x30300402400740000100a00f0664118160b40c40d0350700e55080220091080c3d86014007a03000000070000c4000d84450300900c00154030101c4000303408070016454454031640200001604a22644404900c4040351401c3c00000b00000250300d070b034003072082d402e6680548030071042110210101428480c2c0c0301c0c1b0411110045890300c078900c003c80d03400500396804020460300541e6035581c032207180c1403003045044050148400115501e0900d0f00f0883e903148000d200456819003010005100c8403030100c40341590f0381c098001103081080701c4d903800128080303802c080c0d0209039840e2400075054030480940c41c4214041d0f00010380da0060006c1c0103080d00c01d0100614024038650703100b0000044100221080c1a0689400648804d0304007440348100e0300500c40602144609a45010000c403440f8495040782e1280c800c85e60460002002c04003040c0c007003440c04202060a000283c517605185068a5102d01e240050b1041c583c0f030a40010070b203400039242c03840003c02c04581481095040386905401210341d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 425890674 1250 425889424 425889473
    0x904120809150703020d0f050c0714010b0f060724060e06010c051015050402130501171e0601023d091502070807080720041a1c0b090604 60
    0xd070380b00210781c031501802120070140d0024481c1046265948141d0b04d40c14580d1062000d0304010400c548603070000c08041e180414035007a041840c4070148181d20300810702415040d501400070042062681014005513400240c03202d01c400240c0071120301041021044100003400c900700780a1071540b04d8028480750610001c3c0f140000450400281503016111011001c101101d10110b8801e00316400c1c2d204941250020400240f105900070781c040a0303030400c0e695007510118003144c00d806100f099a144d240104400c0042d0b00e44d2542c01c9000340c2c404018011120802005002901181c208404514002c00c64810943c42c510a0490b000800422036800707210105854840902c5180c6035010040d13843e6002420100700240301e8291b030000f0740c016161640314034003428240d440004045460340c0c0d4004c11681c80c4d006251500c10090341030012035500d00405401c400b031026140c00c02400c5038403003111080000c0010b110505d080c0c410305005015200d941007030305c0c0c1a94402060762500c203c980c1c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 425891924 1250 425890674 425890693
    0x306021332220f0b0406180507020d1b02060412150501050102070315020309120a0302040503070e011401030b031207050708060601230319050703021c1505010c0602090904120809 78
    0x20340308611800c00041803400115143c5032003182005100f40d035807041d00941040c1c0001000c041c4038500c130038400c90b52030b000e0210380c0d507201040388c81d00854425000807507001020302076140d0311002c0c3c0600c8684050078007850f26444841d0780100054602c400c035079058038030100591608441c005e40380100428001481e0b61800c0d0354a04010710905040d60b42050b502000040c81200d0401000c1100101e010003d5610208060010043d520900500d8068402d440c0c000402c624214a05412181e0740050420b541d056800110302070150b800b44c456051080320f600d0901040c00c0f5004103007071442003004041c200c0c60001d14605114009082c2c07410301c041080c0000300031b041405038030004c0b10250001035590780c9100528035179981040390840c800f45400208401c4070f42590060a0080301d100b407103c04242100f9550081e20703000b0340d40181103e0302c1201044554000c036918401148900340140c1460340710720216174a034104403419207071080c3c082042c4030108d030090075090300b0044001c0078002c60f00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 425893174 1250 425891924 425891959
    0xf1c0302070215093f0c0d03180b07081b070915031a100611071509081603110f0406120f02010f080105150a031b020f0c040212010306021332 62
    0x111007041c8283c00c01000745c030324403180030700081800c4140180407555170302c04c03401c00400c00403040e003403c4001303003441c1004520b901c246405c1d0b65101da400701045103840c41e20307c24010b480085004541940c41110004544c0c2c03101802003a64a0a1510080405601d14205501000600401d0078901d40c003040510248000310390701c4034250713601030400307180403441220903600d44101c0e41e0000e070002040302c1000c4ea030300d94428019000c641301c98040f0303a0215021200e403090800740788001404d6204026030a0305900f000b0318a034142d94401080010015270790200014118410b2004540c01080128507100f1580c00c6500002d2000d410300d8440700640c10000404c401054142201c04507210100c3c145800c0c51184c0c20151100c102244003280f0700c0e01950000c3c0d5903208250841c8010300a83d4040e0a8a003807901c00c2d10804500e1080450b003507440c5448032402076100074040f00c404980c030b800120f84000e00040e0052245910381c0c038a00e420642c1e000c00a030511103010401d100c2d079002c50011aaa0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 425894424 1250 425893174 425893249
    0xa0b0a0e0d08030606130909030f0905030c0a0603150b040f030c0e0405030d0f020c1605211005040320210403050c09190c0804050106080f1c030207021509 68
    0x1139001c1d180f09035144544801448064055404080c0250406007a00d08060b400511801d009415032a5101c0c0140c0b91020186c484402d028040d030400034400080028074840d40084c1c628405191000817030035200c001125440d48103800803002030a410740204100844045088000c000040c2d88294500709980c030241c5a21a650240450548a03035654580c103074140e044600c0350001c8011151004c0580c00c40711080901841424414000c0e220101004020074903010b02040c5400c02401c0a44800c064442c0204000340094040003c21460f1003000c1108410303500c407542420f002080207610828010f00407401008405154000910042000487c00100540000001c80700c221096541120a29807100c0010320402c2203030400e100880c00503005100240604c3c004c1e0004d10141d501c5086055551401201060701076024403910200600103000a80b80c19000e80390241c0360650036000900b0320513800407403078814100018080d4040c80d09040320f000c0d100030350b02881c0600d640c2c0401084503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 425895674 1250 425894424 425894431
    0x1305010203030702100507050405130e0714011b080903030a081f030201050d1e0203010f0512190807080f03010f05310b04020405030f0a0b100e011a090a0b0a0e0d0803 73
    0x146071b190004038090a0240040e030b406401e003d010345070498042100d6101511800401b90800e000306100810a1417041c041d201e0795401c1070319062038040801c544d01d54404101002039600c048140706000d8141e400340001c00d002075490f03907035400c60f0a061090540f00c1c2c0c5007640482c230040003c40c007040142d8010041d50803c0000e000001100140c1c0460309134401140d1940d044440e2000001054008081d50810b040d00d50035180100020b2429a00d20780c2c2c5d0036240c0009010100e40c007010700c00900b00d00d0040140350b11400e19142449660103030030004ea0001c1c0c010685010710228184040c6c14a056540b16600442030999420056058184002158440800b04098417240c4180f071030f407a150100c9004100c090112011b148401e500191604008502100d501c2c0306940031541082079041074205540300a60f00500507480d020f1640d110740030000b2980e41b9a503090080301000d41d201c1070702c40c3c018842f01400b03e81c2c41c00c010780024108034001146074401e43c3d44103d0328020807207040940c0da2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 425896924 1250 425895674 425895703
    0xf08070308091c020715110f010515040b06030c07081306090e0601020d0806040e010b0d0507030204060b13090c030e01050f101e05040c02070806040305090406060905030303040b0601231305010203030702 89
    0x54206c450b404c0711000400b8059031968440ea50041c04000380550100b480341c000103030540410018001040165981d244c20103511401c24004a88841c4100d030041100754840d0301030514000d180707407035414010926030000c008560318510400c10032208c40440b992100c0240f0280800809442001c1c1204201500160080f559404220702074002503019800301070000b0b0100e14568024509580d45807440e01080303001d9401c100000072240b0f60002900c04180d4440d40c00245181400402401017079200768580405484440e11014941d00384030b502e000c0c0800c2e507156816850003d661a0280c031450340188d03141200c4407051440060884407a0381581c0c000c50b00402d9041403d28101e02c6e190458004400341c1c02040188001c15070040e0041c45252002d440a20450360764520544410240d441a150160005c00010340040d4004a1555000e0014101000307000280c01c5125455107038a50200b0007000005030409904520403400030041c00244021860341c03412400003500d070101c034640c550 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 425898174 1250 425896924 425896949
    0x80c070b0411131a0301180503040306051b0a080610051303020105390c040b0f09040507030c0603020d0f050601050714070e0712181e0f08070308091c0207 68
    0x181656039101004150f900c040b0f080c0710803090b445595000d4010707000054400e40c40c1805403c84544001214008290004080c6080c68516100c0d10040c0c00000c1c44c0741e0521100900c1d640b51840c84002908500640390741d00d5015180050034000f030341c4078400b041c03000c2c4102441021003203400c1001010540e5428a4a0358541c0d90030124802410030050090040c001815020040420590070803d03103101d2180071204c030303c0c1c800300a0200301d800316000250482090441c0540500f003d440007900588a5400c41303400c0c603a26110004009240d802070b42c0060380000308415000b54a00804185100c450401c0199051810010b441846030701703002000700d0b0100d600c9106404003480a030000f1310681040801500e40750400401008481c2c848101c0c03a40742652a41c809200601140f551941c082030108030030018043c020205d40044004445250385031000304000f65018019265503031290311004c1050428154090500d030700c4280400b500e8500240390310420351b00140010860f21030740e5600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 425899280 1106 425898174 425898203
    0x807140d0207170d030903020312010303020105072003091c0f0c0906090e0d0e0301060801140a060803270103091e0309090b1f0201180503070201080c070b04 69
    0xa5811350701c49600d07100341c07034000d03403000c9603450082c011a4205400740000e40d10809c000d030011070050b51a4010301c1041e641000180b4100402c1501c641107030304400440c07030340c1c030300030100300314802d4032410713054202c890030405207102c141e81000c08603071030106030309244141000d0340c420321400c0751600100142400c032510412600c0100240030b07060040e0496412124031502160b0b15074155660040000d040308244589004205e46071081c260918001891004903000c07035000e41c0c41900100324048042d4080d45440014a041070b90780044482c41307600403402000c0d4548010301201800c54902824100c10580d12000340c4203035681c000060315541c01c942a40c03107080f02141c000c03481550162042070f145d112610000c15a1000107040041c0700040c10280d0007410044d0b0b06d541000441c8800c1d540d00c03d0005502603984c012040c0703482c48a82e14480c084000030300c050107116118810 = true := by decide +kernel

theorem cover : BRFrame.Cov 425719424 425899280 := by
  have h0 := BRFrame.cov_init 425719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 425719424 ≤ n) (h2 : n < 425899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
