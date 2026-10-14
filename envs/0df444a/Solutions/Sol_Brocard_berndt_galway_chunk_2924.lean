-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2924
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:09:01.080985+00:00
-- url     : https://prove2.me/submissions/afa7c435-b520-423c-87c1-dde144082be1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 525719424 ≤ n < 525899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 525720674 1250 525719424 525719431
    0x220501020301030b1b0703030c12050f010e0c2d0c0a03080601020d0c020f0f04060b2206020f070303110118050a060b0108070f120225140a020a12050705060310090b09 73
    0x406d00c00d80c808644030342c105911f8545203003000d0044081155401c0103555086030340e40d03240c102e1500100034039801e40310101d038000c01040940d420928541e6807171794000d41c008428000100800150350103800e14004980300058407e0449050134864036000e88150000c0310b002c0d016004441100b00b101d4002c0302c40b0001c1980c020800080b004028080001d001188600103411a5444202003400c0400900511354005280220030840c1140003042c094424640c0080c0f003103400c05038103030120180002c0d4460a80750706040c080c12440b65000d00500415400800c840d0741500d4041420a001e00499100d0308540507210603c1a01c00441c015590340340c0c20f03942c03200003a24404181c900c080c86030500030b82d441d413201c0d00903140280ea00f0204607c0340d113250380b0801e2649030003030100c20040c25120381d6981880100c044c09407602c064001802200c140d10540c0141c0d482d00420707004000081c0a507a01421b0020119500c905020324141003803607850180e8000c40e0301e003140021481ca40044170911 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 525721924 1250 525720674 525720721
    0xe09040809060a031b0924080c0c0a06020706060611060402010801150e090c030f090d05071101051207081b030103211107081b040c0c020405220501020301030b 70
    0x5400e030190709102060b4451591041010f0344d4000044d840c1494a41ea20040e0289036110501182030076108112034448009042c0410130540921210304c3c0c0090710168090004102d480d20340c28000c0c10a030501100d07070340007011144009019020050580d20490a68070655141c0750581420360b0002e40d16074007075a020303021400701401000000240d415850040d456454001021610500810401c050640c4c280816034804401c028080c92130011441e441040040200081d9201450141562050035406003807440125400c600c45e03401201103510040684102d00c069192807400141441000c0d5800b240c5c1c0c072100010048402d014405403410f032030f0440e4040ba541c9039201d903032080400441d80c1e031100384040c88503032822207001400700350010311505000d41310b200e401a04040d0401003101c00e9621840c60902100d9000380d120046080311641a600010b482d1140381c110304198103101c1e5480b0b0322003030b40c00b402c008010301034020f10304803071103400071800603240c3c088401c0c0c0310032800e1741d802c6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 525723174 1250 525721924 525721927
    0x8190f09090b1e0103020409050c1809010f06080a1e0504051603080f03150d0f060c090b0306040e0705150c19031b0206040e04060c0917490e090408 65
    0x32440343e0011030000d020603050400507c1c0079035844415007a03900c1190f01d0070b054000807586090303100080c0c501c00447ca008540d030141940c14001c00c504003903071600a100411801c800002c11080c6c41e94401400780303202e2284400c8a4100009460203010101c908840d580a020401c460513500040c1e61000d4a9202440c0341c10803480000d1003866800040c2031a4140848100004554407400703041035203117020f0551500102d50500300701c0141c60300060514104900444108002d02580c0247c0c0e41020046a0120702c1038444d908442ca411403903005954004615070143c029564004000c0080a44036819034142c070310014549914003c411102a0100c0c2200f04034461000030710010300e1200b40b00604590070640c6034002403201036021207048412030354600010040a030403442c010000d1900c0103108079152104011582c83c0c281e1105c0d00000c1c0512a01e9000d00541364100c9494001c6041e0207001440ca41c51107410300440210110300003140300c0c40141032150a0900926203d1600008582d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 525724424 1250 525723174 525723199
    0x411011409060c03070b0126061506070f02120a03180602061b0c010504060b0f04050103080d0b1203031e0a0c02072114212508190f09090b 61
    0x8405070b0b01801d511034030f42c041000300900152417044464003900040e207816114141c00c3c00600800044080260703c40c1e0701c074408001e0700798420201e80c102d1407402e68042d6140d100e140341119002e5a9900d000350302c4034100c2d80d61034000800017684044140a50395510030140042d03251030321171025000c0c0c0707801a002000003c040240141401003001001c001d214503065000c45100c0c01c540050350105c0300c0070b8942c800d500781803070658645001d8000440b400c200b13a51641d9074a841c1441200340e0b00d00e500d44c4801030790505c0d90f14440d100010b100c0d0724013601d13583d20b0413440000b4038550301c406681e02c9201400c0450100e240320700c142035007901d654004001407424180140c070800c8132424241c220790390144281000404200034410034504801c01040c40403007004050980180310351309039110341c3c1c040c00102c0310f83d190300000c01c00504402c000740c07500303103881d0600c0c10451168110405a0031020703045580090350100c07088420300b50b5540d0700c1c07007642c0d103401c400015100c044c100c66a0010604929 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 525725674 1250 525724424 525724429
    0x19151b020d112d07080d09050301051e06040207021c0221060c0715020a110f030702360c0a0e0d02030a060b040204120f0c0b0316030203090a06060e0411011409 70
    0x80f80407095046205071034010080840519020381900000000c0d0055048409400e8120781440c01400044000340143c1c075100c490242245134644421008176006000b085076519941d0445a07182d401628003449151721100035041100c460078220b00899610000d41d186040d40c042161112006070041d00d0945c60b4880c03600c4154000c52819103c05608178a0000c2c40c3d9424801400034880e65180c3d17000c1178030314400c104d060a01e50541303110300382c008110410060f42c0f182c3c03000c2c10f09903815034000410310a1a0040c0700400c60f5800506e426108001071200c601e607010080e080c0c4010740c1e6a40d0309088000000c0c0b09402e002584000d42503807042818000045c0c590b0002042c420016000600f010354501c50319030a90340c4101c01f5110000d5580703844090182e03401038440170b040c2030791145241d401c20000b2a05014410303d001010180d012010803040c94060003010174032500f0043c14862261508048a40c81c10300f55011990502106200b41555001d15200d4501c80d6886040f00e082180d40001d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 525726924 1250 525725674 525725713
    0x5040b04150605040c0804020901080633090717250e1f17060607031709101407020c09070f0c02031504060509100e19151b020d11 57
    0x500301c245030345601c004074a40d2600c0c4100010505241e07074034241402e0500610030320304c406800c503c2c015000081085141d161004151090301c15800f010015903111810010081615040a680c0004034809121940e60702000c02c2c0c40c4d0b801c00c00d021801e41d880703203900d603075203e401185000302c8105110b03da103a01d580141210303e400100a40000c0c040c204c0c83c1c890382c030013a18407104100820104241e80b803690341c00134141c80c1d0000051b140c85140040588025020a0b18035110042c01e03212180000c41c203c0043c4281d00c0419000b9034107204880c0a040301706032101085601000503c244282c0400d18070700440800c1c000c031715546404140300010101102c1600400c1401d0703825110b0001e22a006650b0a80c146214a0280710001443e003030859a40381813240f440742d070001d81401e0541804248501080c0e00758038190199152000d403000f40780200b002e5030101030800c0603926150b0020361100941e104141c41c03c600b58240c80030012140805c1c0d4140d000806480019801405058410b64002d40c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 525728174 1250 525726924 525726953
    0x2150a0e041109090405030a120915050c16050102070b0c12221407150c080316091d1005010306080319050c100b0102060a05010b1801210b090105030105040b04 70
    0x1255203401c0c003c10216428000a440488065100056200655030311a026610000a42c0360038810000b80d525038010b1404421070b540403040c1d0700d40101e03420b00410400c9806000c3c03860090b80541a060074454001d40102006542d00c1541000003060068841d0444040e1070500300504500c1c0c89100c41da26900c140310404421000040040601040c80030504200490300040144120790400058554170388005142234284000c0503401400100c811050700d500017541000017001c100c1c02a001c5a420305641d200504c952000350a80b5000707100020701b181b03c2d4544241500796190380b4401142160796512440c4000d030401d02c81001000300011603c000100c0600c3c0660510020310329a82c10114030060940f03115560310101c41095805220b0140d0003182c64004004075850102107001c60b2140f00c45800040781303c1c0d40d540400780c0c0142c0d050121401480b80d8403003224400c9403880700034202800b145201e94120800055149014083e0320310a0780c2c0800301614903119a41ca44524100c910b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 525729424 1250 525728174 525728201
    0x81810050d0f020c1b03120f1e040612020313080a0809070e13031112030c0705060601030c0c020d0215030109020a1206030507030f06060302030a06090219061b0201092102150a0e04 79
    0x440304011f01ca500075002d0038080d181c40003c1b59650030380116814480f421000c510803052003d0004209042d000212521040071440016940c1e9580c641c0288002e00406030003009840041008a00b465104124600c52210f03c021905d03855101c0300d0155070071b02c048650b00c0194400021240009102e403112032103a40307250707045991203c8a08400341c1c1c0740d0000c5860340c0c80e082c0b011030321005000d03041080b250407820030708040000c0b628802c0c0c0105552000200a40a0780d02480010110b45590305810140c07800c0140464170307941c481080704082d511049003c800501305114800181001d846208100da91010017003075620701d076a855441c0c884110805070748680d501d003000000350b282802015180c0c0c3c410040025600064410040c040b403030640509071083c0b081506201c01c6030000d28000d00c1c1c040c00e0407004c10317400d040e00c0100d904180c4c580100882105c1034000c03a42c544000504080854421a282040a4906032002e407050088034441400500c00c001c00420500305a44000b064141c107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 525730674 1250 525729424 525729433
    0x61f0603151502010c02120307050d05041e0c151419020f03070b01091a03060601030203090f15061f0e130f0c020c0109170a081810050d0f020c1b03 65
    0x4408010502004100004003d81d459490080220368140401940c00000041d254207506100c0360081203401020415070f80b0341d41d1080403809205041400054403481440c820360407060b5840d0250702002d1714411a02204c20046940c15a0703805100c1034500f460b000200181450b42c2c880100d500c40382d00100641c151301900e00c407044000740034001800158002c000f4034500b940343c400c1c10390840e0a03a19000c0120915003a0440240d500811429001071013460302503180e848090f280c1d4204800021011058072401d100c0c1c0d05800f5860b100d140c881c520850300010407005e20541c3d5100712160b0714940e030005d10112101c900518004d641414000c049440c00112401d0b03114400c41100c078450b8540025900000c0da080003503901c11003000241682c0c0d0152104c07000c001061a47d52204402d0003015000d000c2020360900c004266000b440f440d00a100000080d450500544654014030026280d641442920042ca0025000b101e542005440040a40f4100d502000003c50f050401c1c25074180035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 525731924 1250 525730674 525730679
    0x2107090e0a1115040611070506071a1f031110020f03030f04080f270109080307060209060d0507090915031101080601210f180507050607080c0307080903061f060315 72
    0x2424805040982100d4882c0c132000d40c01b0044071403500345181d02282c440d000c108010f030002170f200c08070105000c4056a19070354a032105204000c50b140200826071040c01c0500001041c0a29200e02c004007250035a06200d4890314400100d07140c281401d1030716107641c81003020480020384100440e0b170240c0910403190404540c0150f426030383e400807109130004d420604d004aa000031082c0c80150a41003400d0600e0658504950035403039004242c0043d180319408185580d8a0301da110494070004c1024008004600c3c0035400680030394180d00580600f285000e1607009498514114002540c0c0c00c41c00740b00400d042c0000440e104403004186504204004075014804003400b42824170340034005a022503001000a240c20480e0554081070088680c4000b9203400311300040313901c01c103890054030b20356503c000070304004440d031268810400303503444006080014040e14a02500b0303503400460541d25603480364840d4807401d08180c0300c50198041586d00030023543e4040d41c410800c0d541140500d004030b95 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 525733174 1250 525731924 525731959
    0x6140a020307060510031e02031002090301060f0608040c060302070206191110051806010b0f090a1a0405090c07150e0a0b04050d090b362107090e0a11 66
    0x210b0903501010100c5c0600801d008000040d5007242e02007000f920b2403550b200c50303900002d40d07680e1030711442c1200d6540080d0b8104640c50039000a00a0f0020030400b28542e65a080014a0014102d4054403080210038001c40c1807440381c02180c80d0b0035002000b9600f01000d800c00b800c1a041203c1c0c2040900c1003800789244914424004440e40d000340b0200000c0d0b61525900c10a0326244140400c40340303801660040c000d040c3c4110a5401a021040100e500d0f080040c010901d1600b13a608400b103408a8842d060014801c900000d000740d85060301c40605036150808145010301500364000e01401080d00c14560001a0f58810460544c0000898502c1c03a00ca4981a14480c416141a9250340100d044040510b03080038103c0c0080040e42e0340c144c64200c03550349144422610b001803144580283d50314911040d20f1228146108400420100d8114090b800300c8444c01242114034441d80902507000545001900c00c1c0b0307010121007805002101403d03500c0d01000304000044951040f00b044280b40880c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 525734424 1250 525733174 525733181
    0x281a040e0106090c0e061602031204140a050f030d0c1e0f060507110a0f061b0c05010b010813060b030f0d050c010509070f090e07180204050111010606140a02030706 72
    0x40c81034000039986091084250035203040d1519901031005c0704841d00c2440d1030f00390464440304441014259501c999100180c140342c0241c0c244403402e10b0101e404200c44100910407802c800c021a04400c0740e941e100148000c100c080c104042d4107404c07246c14010000d0050a0aa11151041c01034480301100700c4075048111305115029070b051025040500c04000e4548140c58000103e410038070388900075641c84940c0c0d02c1906100a204008036000441009080c2d0010095a07005103071250855881c08030041005110500c1554550708001030800e01d540a811140e0050703520513501078000a290315004007810014581f140c05114141008c01c005030244100000001288e8555990300c2150f50590b0a4860141500310036400c5003004100c0e85006862500c2100e56520700810204030451481c1e041205076403040090b00c8060141d8007145109500500c142c0d14262680c8141001540e6500e0807550540036600202c1c01180c1b44401e510801c00107011202d8107031044a00c1c001180c2e5800040c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 525735674 1250 525734424 525734441
    0x3050a0f1103041202010801170703080a0509061204020102160e0601050703090b130303090e0702060f090a1b0f091802060c100618060e0601020a0b062e08281a04 71
    0x519803150702c913002c543e400f10719140140044c407544a040800d150318076884034400d1000800d041800610600c0e4035004109440d8042c40c020712180d210090401d07901001c6104a40032801400740b0200d8030680806030b9500301c26622a05990115651010019030f01540320708010b03400d000c802040007885126600040405503450384942249510707616000c1c4c009104c54200b458969040401c101186a002481c23035441003c0c9003044035107886100405040852002010b8544460401d081d800c9401030f0500c201160100160350404987d1602e050381292000700344054213003006903040d0003604c1c0140250a08121620036034480720441e40650048808507805002c065440000d2202200140d1041c100200b01c0404103008501d00200005d40304d250440d0020250903161010034800d45850100d49610000d0191078951040140f02c28000800f500c0750f00000a114080013a0000520b800c8041c02c0701450400c50b42c8494004400401030b10803175161200300325010180f44403d03903a5000e95101d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 525736924 1250 525735674 525735689
    0x114060d020403080d061a0324040e0a021903050c0909031c060303020c01320408100218041512110603010b0c0610140402070c1203052503050a0f110304 67
    0x3512220480e4403019030300164040c0c0c0207050807207015155124400b0450b0307271240a45082010301d820741012403640302e0408168507001450310201d8540c9020004407039086034000ca900c0c1d2000030402601142d90322940c0002842904902148543c0d4240954000d070040481c406581c10080803540d176114130800d043d800d42d81e490700c410040044c1034060107500001c410030310300b01e0340540e00b0603074148503101c0c0159480b580505c1e0602942c403414001c401c0e10044d0140b901a03600c1410700102c110040e41043d54500322801d0400c3e5243c070907150500c540782100c00c010704410001072a020b604054030310781500a03181440d22030204151942d070140114040d01c0400c5440fa160546800c5052802a008050840140000d64140401e0880105107600c9083c101e40250351401c03a4034024066495030352054503140c14408509003015041805440300d4030425401505502c110701c5081c00e01e1620400203000f0480802c601c010b814442c0d02401200d103022308000241d40840700011340780d80d015510041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 525738174 1250 525736924 525736927
    0x21908010f05190b03040c0905071d2e09031a04050f06060901050d03050702041a0310061d0402012d020c0102030316050a0c1a010317030f0114060d02040308 69
    0x4900302450700720001400069400308000305000f032040d124640c0a0144c904c02e0f08000c8002400c01c0118aa00710103413004107c24409814040d10141089001c5a01d4603102c3c0d0389000341c21024280482030303000c1c60b490000a640000d04601c40c44900d04c151401407010043d2400001c40498010a940414131a410352003044503d028144503040600e80600c0d6078903600304074240300c0d069890744c1140d4190b68040b42c540394017217081d01c0e080c1c55038403600c1700087d0850b0a02c0c1c842d503040959942d84201d0f4130825401d5418010306c200d1090101c819602606140814100d908241c4080305c911484d4013610605204c500c210079111700201082c10b860100065a00c3d00303030551a9140c0c18441104c00b840c0c02e000660460611803d0301300008088400d0108204c004501c1c80c40b464843c0380c460b4092a0045d9000d012002148a03800c0115424042035650807801842c1c05502144001180d03c10800f184510000f80d0902c00d001c07107070055104172070b030b4005400d1122312f8503102c2c14801000154031406540c0d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 525739424 1250 525738174 525738179
    0xc0c0103050c0c0703030f02011d030711030703051b040603020909100e0a0309120615030f020405280e010b131a061306030c02011d0d0201060b09060706050a02190801 73
    0x141503072001040c050003110b00344050400380342d00007407a60a903589070070b20304040c54000008a00604540707030001d4100d42034a914554041000c0010420341c1d00800141c440a150701051550713440c400e120082950b84030300941510810318400384146544005c201241040e680d8001880c0c101c070a03106104682c010f404005840c050303a01c1103089a08a04019009544250b00c01420035002c0303210740c001d820318a407910f408100300d031742c000030440e0015645018015142d00700290540300021080f406a441c1c036000c154039101c2c00c0f011112b800e444041e50441d4191001c0020054010b007810180c1564a80a0412031a5141c4034083d5509a45c0c038800140441e66404403aa41585044018000c08080181500c446059200d407030503900e40e401c004c07807080c1481004a00412861520184241000309501041c00300410a04814283ea0b8024840c481d01c80c00314460900c203c161741a4000c408014450010b40340d6003060303a00c201e8030080142002d520302002d0003c1c1c0f40034850400003c9204006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 525740674 1250 525739424 525739427
    0x70f0305031e07051606180f12090b0901030b0f15180604060e1c080d020406180b0901030f0f06080705100c020a03020d0f0203010c08060f0409080415140c0c01 70
    0x4455042c1d100302101602414800c0000d809481401035400c442c4546104131814003500341c015600a03580303140d10b40c0da100894142410414000c0e0422200000d50700360381a14584500700190544204c0401c003842c280182d001580203009502c022034115a8551a04005503505c0e41d42e59a04400c0001241e40c030380c03261402042c511070f8030f003680b403051b0410700043c8440c5901c5400013618a0094810300250484c44500100d2082003507401010312000160441003400c0c2c03500600104c69507a1607407a4204800c11103204022024021085070340420b0018044541c4a60040307405400d0158001480d0145040c60b2070a94056820407480c43d07100e0f80c0308014605000010015041d20381ca005240c01850740d0000e03856404600c0302904c21a100c0f10030005100801d000c00d81035a82c010003c0040603a0b944028200d0f080c11a40c080c40761851101e0ba81c49404d141c0145118194820400d503d4241041e01e01c03402d184040c500c0384200311962800c0c0c60342c0c000300300003000d002c0c054800400c545500d4100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 525741924 1250 525740674 525740701
    0x1b0306090e0604030c08040801022206020609152e0806010605040e010e04021203160501050c0a020303041202030408190c12020f010c0203010b03030409150506120f040602070f030503 80
    0x114100c031034540680d1100c2824045580c41d001039140c40e02c05c8090000342041c030354600858000c4061540b0000303004113107007104000280200d600c1d0740c421030240e50b0b44200360384806084035040b4058001c910300320a140c00d06000984e01080c000c0d02284203d500d003da07458000c1c60f50001d00c4809c03640c0f003414080c0391010081c0c1401071140b46800c0345401c2c00d0a901d0019003506228100380c11480f000420110b41e41c81c6d100350680720039030003101c2c4c4504c206444154260326540094625519104c04a030362881742d0800c035141e01c2400d40042d4919122556996106440700b04404d007140010300002c90aa04144100d5800b03034a10f8118070510b0405090a410a0354643e001d018020000095200182c80381e980f000c1a15009091141d429882400880c0c0901241c2c01e0150b414000002c0214414005a0040d91600c0401c1401c1d41d1783c54a0380d087c80050301c1041d65100341000104006508200704844495100340f1900c1c02509145059030b980328600d80c1103108602050002c0100000641c0258 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 525743174 1250 525741924 525741929
    0x40905280c0e071d0d06020f1309111605011b1d0102030301050d1b0e0a0f140c1b0c0924010e3f0a030f05030121151b0306 54
    0xd000382c0503081c440ca0141c1078480401400821440c400e04400c09035403500d44050300d180e0090341c00c1d50b030303480020803046855001840e0343c00814400d0001040341c00062041c1c40000c400700003a6031074801049241018440d1a4508440b590340f20b080e0030b02c4030885455a00b509003200d899101003620204900240f07010510300700e80c1158400d01c010000e680c3ca49010103c1942c0000c402c10b9040b5450701088000384a5070065000d9201c04420b0102c0b80555501c051610000503000708004d22007401d1029115900782c4450600700d10074440e210310144000380035260000c00e90100c0c2c2e050f40351040030982e400750803505800e041c01d45107040070503490780d909603c121840c2460710818030361150002a4000070303009049045018140710480c2040c000d1140d02c402000046030116410246c21485556012040350880c00184011100030381d00d401181946d042c1d80f010102e020145888420799084030303600f8a01926800043d01ca0700f1070014192242d50600c010300c0c0c80c1c205081c120104003405803113070769 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 525744424 1250 525743174 525743189
    0x4120b04120c02031203090c04590a0f0302010207020f06030f0103140307051b0f010810030f15021602010801050102031c0e070f0e0106081b09040905280c 68
    0x84940001a039000c00c6499564007171603481c9072a92140f190951070b0a44880c0d10f81e070080d00c0c010341028011086243d80e202201c0403001c107542800304840b2651244944841c811140303c0611036076004107500800d514000752101d044030000e81301c686500c520403a0110080d409030354005060003e50500c200d024458900c2911100d1560920b29074480c40301c0e00521000d0314680845000c03986410b001e10440f100c41d50001d04a59090040c400300028403c01c2d0a070325413241480c000110301039400b803000584100341101800710901e1864441c0c0c0c80103401030800f00c424011549400c0782001c803c0c03002e808901e0110824110703080140c0700143c45404113030405030556005200c10041901c040c6d40d40030b401080345071301140300c01160340424a80070040c1c0100181800c20070011031110b43d00c0c14418100c41c1a5965115540c55030311042c10007244011410903401010800d10b5590b0400d504030b805581c3c886c03006c13225215500c00c0d0b00a00724251104403101d03190b01c0b180d1a414440010a00c1010b170052 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 525745674 1250 525744424 525744437
    0x120312012108070f05010608120c010c08090a0b130602030c0c070e10030f081b1f0204050d030f0e03100b01081f1a070506010902040602101b1404120b0412 68
    0x1642c480049078000c0c604000e041800282024007001802c1d0440c100600180003143d026411441030943d181d000b07035545481c25031800740402a014854120a4002c4903580041c0c07046003100d469020105200a190402d061445450f140005107144000c52103004d5114840340c44480d9405164140740e141d9010801c110869818000c6d1100303060070700b004603a03100300022024007192034144c1c890301030038500c030b2131402c040c2581c0d82d400880454004400e1f0160942e1268440419035604102d003c0c0f400f486800004604210f40064004c103a4003010b401d050401e0580325440c0000240b0300100030f020722050326147c2191003030310758105481e55004128803d154200340e6680030803c0c1c545141e0301c1250075805c4d4200445071081d203c0350407150481e800105985a81d0303100e155900c013a601c0782c41810014498a01d03000100f080c07038410303501480801118007680145c0b0007400c59264015448950945904100000c0c0c0300042501c4648000e00c2400406154075003070030690800c3e40c8102c00300061000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 525746924 1250 525745674 525745739
    0xa110f070b131e020102071a090a0f030305120c070f1416080604080a120504061d0d0905060a1101021206040e0d02060c0d06050d030e030111040501051812031201 71
    0x4509038001e2120f226003000a558529400100e01d010b2180c2c0c01030080441c0310441d9202204160001c20801074150380c00c241030b40e80c4039a841123192075403000ae00000d20a004204441004a600a0300400520328844c01d00c81c42d0f072a910f0001244001c1110000103000140b040c004060100392100c40e07c041e0a0340209140400c1a0b1301d500700100001c150000000e03d000c420b0f4010310942c41859107a4908218600c0c051400c28010051412100315455000312070030b080000000d800d21004400c0e648020035203103403500340419600000150300901c018810742022700082480600500c00b200014030304541040c500340001c4402c07290403840550030000c00c0303185884d00011015082000800c0710f07980d9604200240c0c0080c0741640000c1e80c0028000128018942d101c042c1480707c080482c0200030300061428070805034400c1d8450240411402c2c404008250104280700c030740040c01502c07000d2110701d51008a811540043c032400c8092210100503c20f42080b003c100d0038000d100740360100f1058 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 525748174 1250 525746924 525746933
    0x100e0c0a0f0506031b04031103060f04030e0f062209050108070501080114010c170904050a0e070e040804030b090a060b0103060b030415060906170f0c06070b0a110f070b13 75
    0x1c1c40c90107054014000080403845038000001c6020442210300300c0551140d03124500346150001181c1024030074442d6102141006c00c030580e203e405150300d2f4450403a070b40986e030148040030030511100e5034052001d116450389640f1450b84d01d12240c24001882800c1d6007402c1603582220b00680100030650300070079040c860b0f66040103c0c507042d210900140c3c40e0381c820120040b02c84c0003807110001c0140601000d981118000031028200110040340c3c248020741d104031081045840c0301482032015030050004210f2241e0360511103800601a1011071b2800d500ea840b44c0700800c03c160740b034200c16400710480c02c5c01e101c103520031041c21200903c0d06002c0f40b0320303002d22046140409000501807100600440250315020b500030001040310160a21215503212440b071700d84000d008580d2918000da01000e00121004a41a915080020a004d0500c10342e9100d1203001940100aa0203060f510300421030752144400203044010581d0501c190350380f0441c940010031500180c0703c031603500d41800e400300004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 525749424 1250 525748174 525748199
    0x130b03070f050c0a051501030b0f270f060907170105010b180105090d0308060114090d030507030917030a0306061b080a0302070206031e0c12070309060e100e0c0a 71
    0x500d80d4034020f515004a103515604003106404028554800c004101e8201c00110665030f048074041c940032040c80e0788000b602041032800301c40c042c010360200e1001c082d13442c5124900c14801c09011040b1500e074000440c01900e880800d87c2d41020340e52140310100080c166085054801610000090000f5454aa03074156107018004c00d62481c00030886913444541d03c282c00303880846d1b10080024295115a003000b500030141a03d0190008460402d070450303002c9050120341c0006d80191580e0031410b041d84045075181c2240108030b04100b202c81d00000c8404410440b150180b66030b2010315034408000798042d040b1211a44110248000902d210a54150640c0b0014065030020000ca9507010703c24400c900a00c51144029070042020040c0800e401c91841409800d00350020100119125440152154010140440078040c00b03840081e00d258407a4000741c2c03d2522440000c01c55a201d60202d03410800c958000f009115501c8443c0c00303804004002d038440344403081e2509402c6174100203190082 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 525750674 1250 525749424 525749447
    0x60506030606060a120c111005060f0f060304060902180109050f1e19060f0e0108070b120403110705040e010e1005070c0807141c0e04060501120f0917130b0307 70
    0x60b1590350341d0700d51a90b40102140c1c0b40e8184040b0072381c3c1c014680d0300f240000901d42070300c000340a4031000b0100ba400b81410440003010070f130020810303401c40da15517503014054040c440c0c0c126003110380d07100c40c121151600001c00b80030b455000030100329841c0c01c05004010100c010f000e40d0b191303800e08682d18414075505249a411040b4007050101242c5030902c810f01405041e40052150000c503407002864600e07113610386041c2e032548001e95060640c2c5003483d000380d025181c4e10000a420700700111303002034001c0d10a0350650209009450580d5900d0001400301c40e036203902d1064994540031042c000450600c1070204002003c8001c000f64100b500c1c0042101b15101002840070341c1c0065442d0900c1542c401c10701c440418081164840740780c00107800c00314168140f42801203008070f0780d0518185024002d00059038410f80d281c500f4080742d551000c0c0a010607005030f43d410703546e820843e0042800b00791480740c10b034140780701c072552581da89180c8214140c081d400019403000a1007407003001540400711804 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 525751924 1250 525750674 525750707
    0x60e0d020a1701111308100203010807172a0f0a060801061202250323070809041b08010f0e010812070c1502070342060b07060506030606060a 62
    0x50654084075071030041020140c900300441000c502d000350703004002490000c3c0c0340c0308810368000c03450350851f40c01640028010503000f5001400b0a001c1c3c802c59144e45c1c1c0c0410101c8049a42d8440328030f541311000e0306812550401c2003000180d00e102e82c102803002070a000802e0b170712540b00900e0244000c09007130040c040c850800c281c1c1c2a0612501060340c050b11403008030181000f20a030200d159600b9001c07074009044010550108c0c10081c9500c508040c01e803d030742c2d580085880c00e0300c02d0307a80400550221404560107503031082c1e03181c1800500c4540082408143d00d401840e075042c42c2224200850585c0515030100100c40180041040490410b9028000c0500c458903106d9900e004018004a03810040c4246505000460459400140241240e014000a40c83c001e011345c41307412501c1c2c1d03108282c02d107584800034a104940c00005440c000d800c201c000060410303203e5243e0004c1d40d0164000f41da07516100c1040c40001d1070280030340e0ba0400800c55a42d49000020302001d0b000840d110440780c0e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 525753174 1250 525751924 525751949
    0x6030507030b010509030d1b0b010807050906090405210c25140607080d09171309050403021c0201290f0301020424030219020a03021203060d0809031204030309060e0d020a 75
    0x1107030230019030003260001d40e109149403095070312410703115910f621600c00c0c0e6105100c03240c00700701c8074113160441c54052904032014203100b15200740d0001c19012649052206c11000304021480864180040b0038041003191884c0501d2450346640b03810202c880e0004205102c1481012200d50713580000ca0b0842640012601e4640d1031403c40100105100d5502804005400b0642d40b4171400078801050380e641001e003030980c510b46825408044880803580280035a00c02d41980c51010000b003040c41080990b48004656542400d503888000d508076041801c0380e541100061100d8a07000350304081154098000f103081a10f04041a6501c440344605a11050254041c501e01c0c2d0b48250111151243c4241400c11045100c0500130340c2e441e021354041c1d005006421440f910070b002001241d00640c0010417215444125495400d0554055210f02c1e60500c0b03482d1410303160412a0000d000114000c1d144c8015680c58114050840c801800140d03102e98840c40b83c50006036107512410702035404500061 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 525754424 1250 525753174 525753197
    0x1c121416020d020a150305010f031a090f0d020f150906040f0507030f0f05060a0e280b010f0f090605030304140f0409150b120a0b070c080406030507030b010509030d 72
    0x81c2d001100c41201035000254110007096100d8030641001210541d550104210380e600e00070303030060f41c0321030000420b88089011000d22440c3c4010300140c02652010586511080320034426203054000000c14000d604503000c0860310344414801c0c0c407170962200340341c244d1524086900e0f41d15410001c00080c0601003034014081800380800011780550380c1300000047c600301074100030394010a40c89040700c20740b1507940040c0301b40b0302030b0003500c085d030700a6801031220120304100074007101c6c0381d031060070348032500c20414a02003000105814001d0803110303400c81c0b0980c20b0510b1b40092040540220250b41e04003441000103880000454085074130400c101c542c201040c2c0e000825007203524002560082c00e11000c14140700c07030320b004e10355907015040c420070a10303104074140032401c144154800e171540c000b0350145010480c1320944562141c1145810021b80707134255551807650300247c00c500006607032401006901034062081c40c203210030900b082410706070707000002603440500c42a00c0e030400c40003e542 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 525755674 1250 525754424 525754429
    0xc090f04051203090105010302041107030c02091f090c0206010f03050c100908030d0b0a05030c0924060a321b160810060504090f03030b0d021c12141602 67
    0x240100c402c03201c0700381d5507a420011000c60103003200b804181c0c0324901d0700c1c6a0b0340030014080100c8084076450707129170220703d03d80d4003042080c2c00c000b8400b031152060011142e24104000c41200042c2200742400590154988802032034442c05804c2980502c0d008402400400d10001e4008580070b0111000285002981012180d03110154880c07041c0d4400803c1399116060300c1c0d0807a4007010819143e45075065620406c240d55103d00b035000c503800020a00100d410328081018140d140c0350070040c2900790003026408164943c0c44410341ca80021079141905000f190f803181c47c10b5840c2c000400e45503c280000000751158403558540d0007220050f0214040c8150041c0312020350240c00b9600c610005a5075a890307074959407030904800d600352501c8030124152400384603611466030480c0c03a0b80107490a55030f003500204854800304e5840000204290f005036180c1201c2c0031106240600203210b0151480c0035668104102070510078080340d0040d00c48456854000c0d04d00401d140c4041d000001581d001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 525756924 1250 525755674 525755683
    0x603120f0a0509100206060301240b0f12070909060e0402150313080c0a060e0106031e08040e2811031f0b030a020406020d231b06010303120b030c090f0405 68
    0x190103400070b44c903568092401c2e0300824190301c5040250024000c24500c00e0340e40e05940c410180d03200c0003030042841400b0481c140c02c0a8008206902426440d0424030001d4240041c811610440020703038455041c8403800041c01000000c02e00d41020341194142a400504600c50100c20000d84035404400503500c40c80304a80024002d0f004500b55607158491100c058460710f02d2082a21803506018a80e06401014400c500499030000320320241410780d40205900c0c0c1e00e01c044150340f01a400e00c030200301000601d40e200e001d900101902802104103d403080b07442c1c12140c0c010240145840c2c5442c1d920aa00b80031030380e012260107100b500ca40c49014039100958416044000040808810031040d61015401807042c2c8806400b01c0c0c1c008000000100ca10240301d4124156082030800c000c464640b40102074542c3c21032004101c0c8020900b202507900d003c81c260300a0380010050300104440300d01a02c1400041c6034113502038042030a41c58081003405c00082c00070b900701001d800004050120900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 525758174 1250 525756924 525756937
    0x10305130f030f030c0806130203040c150302120a02121503010917041e0807090b010302090303130905010504062111030d08010e0c0712080601090503010c02060a050603120f0a05 78
    0x50010300308402d0600520001d800c403007000204c0c2c0382c1300070018424041d8000d203224800040c40364400450f02c100120180d0006072048402044144000c104d0103086030900314024401c1e64016140ca04011044559980c05803860401c1072040002442e2010090000d0b9804911b0b618105900311010021a00500d40884041d01110710492044420f0301e450009004441c0f80f1300306065044040861100c4e2803810b8887c424240d40300500c100150b030100d401001c05200305040050921440e000400d0456100e168110084049400180600aa94429276014002c107030340410030903040c4001c0d01f42d50712007102c0400c100da08400d003207410800c9a030030300c520002018050722055400401c0240c0f17444e4080c001d520310141500c0c00038914110200581e40019040700984644507548170042d100c4800146c42c1ea4100210300101207450348090054403140d00496000b00f01d20b150038510001201c0020344542e2090b0003900c290aa81e00904090740c01400800781e22594481c1c10f40002d540521408 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 525759424 1250 525758174 525758183
    0xf030402280f03060c0e0916140408010504031e020a110a0f0f08060702161203300e0d0c081803070e0a0e010501061e0c0c0806070212030c070201030513 67
    0x280740204588000012890849200305000c0c403400d903003828192074410031410219040072184002886d03003400c0a180403003011107401c02070442e000d0708614200c690305c0340e040149207a44650500080544c04550ba0841a038a000748142903000c034040252140c20307401d4050585001d00c200403680b641c03014889070042003485d00b0304000a680302c4680e07050200d00c2c41181428069400050841030010074048803842002030852030036420456074100301c5415903c146c04103ca0be080f00c43c0e441c07001080c51a003150042c2411103078034108064000075141800e182c4101d030340050070100c00c0305410408034088181d0010410782c48425902d00000020300d021010340d8144a00c40b0005541d010180c60503009084288085c0440b20b0108072072800d0b20300c28400d807400101c0394020030407121310013500701c01040520318001050076035030703120f1040c0c1c000c2a40140d1116040306c000d014030650100404801d88050404440c1140340110b44040f4601644201034140740d25a00081c811b044001081e01149500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 525760674 1250 525759424 525759499
    0x3301b0304080a0c060201020909010e04060902030a061b0e09010b0f0d06030807020a0b030f15190e07080105010804110f0604030203340513090515130b0a020f030402 73
    0x190040141d43e000742c103d060342c28408107100072a0b1144180200d981800c0d018141e00590b03440c0088284400100900a51f1880c0e5204448001039609102104495000384008504181e1100b035a901a8015130720b1801841409140c005484d1144807074a81150513003540140c40b0904080d40c110540700743d000c3c2c440083d141040c08001c10034503c000d030281301d00903610140481e40f500c518007194841034482400c101c4134140021749503ca182d1074003c8102018003104142502d1010034400480540c1040094070018820451a00d5101c14807500520003440c1c036265500742a2541c0c1d40c41548005014080d0109100402e5252076034421503004550150031160032000085828210010881b944101c0340c000d12249804445052013140580700001c24000412b8285404000184800311003254103000f00811284400c44c86030044c0d00c503198541003e41c40340e8040c0360800b100000108440c050610501c9099020000002581c1d80541d05071007403601e0f50f03d0380340041942c411540d4111031a220 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 525761924 1250 525760674 525760679
    0x6080a02030a180b270a02120712050303090105060103020306010518030c151c0608071e0801090309080c010f1704171305030c1516060b0d030e03301b0304 68
    0x800081207200700004074100e141c103250440301708081084c20b82c078000b00b903000e05000400b51510303443c07219920b11a4021501000d40d40c3c5030344051000c00c8a001e60740b9401c0071040142c3d40000380601c4e54001802d2a00714503510380070300041c0450182c031081380c5c2503044010407000b880c0c90030070144406220051404100480304000c907403460744103818000006450081c4151554681e0103070505a80d50507000e42038690401c241490004110401e03094228a0000c0008100d01d0a00c42c441c0b105000341d50f0140198180100700e481d06081220060402c50482008190142c2c0b0120640042d0303600c0e88554140d4030b89007040981c0913a1101c0000a0090008580482c1c0d000c200402044030030681c256541119140700700500d11800452403a6000c070200890b2400c04104500402c41e60702c100000245070181c24041011281169411408101c290040030068a420801c04200d032203010310505016034441080740c00b11500d560072510403000480d0642c0b114055440741194116284216a2a5035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 525763174 1250 525761924 525761933
    0x3090b0c04030201021519020d061e0e100e0c070212060f01081905030901030506060d0f0506010e0d121214040804060f020303010807060c030e0915120706080a02030a18 74
    0x144070b44012409841050742d5180c0b03108000e95240d1044286070100107030070081c07100c1c40e0069401202c20302562a42d400703020401c80d6070880b01710303400c000403414142940d0a000c1c843c07030980c001410016403a0101c20b01001100d042e0314600d94040a032444960f101c8015101042100c2114511020140250003c000d200800a00b4013812140c1e56411141a414a035081014050507044082c095030404c0003035202da5402a04003a8100401522040c60168620602402c0f62441540030380c02c180c0b27030414000c05684c0b08410b42030403101182d02d2400a049580d9922070040c1c07401c554414130045002c2d0380355000280c0e2000115001001c0c0302c40c110b140a18148060354014040d00d030202c1d00084010914920020550303068590480040c80f0150603c0b0050700c5001015a04504000b198680d800303451f00d450840f240564038018030703010b544010304108407090702c4080008a25a10510080144c140e001e4811a0400c100440059507074a819900f000034002c00c05032504401c1d0480e1f180d80400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 525764424 1250 525763174 525763177
    0x5010f2301050d2a120e061617010305031e1c05040c0504020d0608190b010b03090703061d07080613020f031005041a10030206040302280b0a17040c031203090b0c 71
    0x110310b40d40c805c03010901c40c0394044201d0354029144213050380f1502c0054651604a14960301114a900b003c0058812a41240c0d240e90000d0b0003c95650300301040f00d80301200030000914117642c1030001c050034001c0d1a49420200740e410200300080c962541e022600380300c0c01620000142002a00955846001d60001000f4207900d00c00e102592140d0880f45000215000307403088881d51250700c1c08410303440d050b1503803400d80002d0540351460003040703400400903400384907550001d5801842100d040440c171103e2030401205501c4403401e900403408210b20036114400044039554101d41081d0000d000a02081c41c0940990311a81080d207007009000c00c0c03003049202c0120710b1001d041195000e80c2c58400c0200070070700d24440213401030010300060006141c805c400008500404400c01702000002c03400d6200c490580d4030004746202c00164810000744d0084040409100c06005511039081c113980f00703010f801c0c0c1e5200280800110701c902002c5503203c0e420a840403504140034030600d007403903010414203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 525765674 1250 525764424 525764501
    0x1101020c07060921021e04021206030c0405010303080601030c0c0c030c0e0a02040f121a01030b010503071e06030e150a05160201050601020c09060406080a0605010f2301050d 76
    0x41602900e00041c100c003507030090702c030304c1130705000c00c1601d1103c035400e200d0202e2401e480e00d0b1038007207006008034054030b035480074002210300c603010700d009400d00b5010305041074011034030180030380c2c2071100510200e03400c090b40320b402820a10b000104402008800c40e00c04240d8200241f0410b0a502c000040c8501a21500706803403800400740010784038207555000724801c0d41301d81d04100241060400000b52410030078a803d60041e1800d41d405000ca00585a104400340c00c1100c503032408c14010b201c1c9050800410300071300403040340020300010b114607084c581c689234070030a4101a21050b0302c40d2021000e01503880310300c08114040705141010203805020b010211204038005102044580d5403510500955000e8001a0098011044014207010454130006c02042d001501d918000501d01030801203914214050340740041d0390350400095044000301d0b5400400c02650100b10200300801c1403050070301e0003509092941e03a440400101d0005842e840d0310305280810012951541485560901c007103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 525766924 1250 525765674 525765677
    0x308161d18160305071b0b0601050c030304030309060f0605030c06160b16170105011b060204050a12050c120d030e10050a0903030606020d0c02190503010e1018030804121101020c0706 80
    0x1550f14490211840c41d9242142d42400c1b0201e0383c408003040460307042d03503048801850242d1500d101c0c111018510b5200b41d40403000030f41d0b41c60282d002c0c00154480c18064809210f020f0040519110000756500014803000f40302c2d4500041a2840182002c08408425804580700c2503078901a8665108144402c500c0c4000c1a82002c5185c80040300d401d4050684905846107010007448008015041e2000f20b0202d0308ac40e402c000202e0199107000f0030b58001c080d400c0c680803030502c55152007402c014500907100d00034a123210042e07881d00700104090350721724410b24001408015050700c1501d40454206c40707480300c03481c200900080341080d03000010503034020f0300e042c01f0050303586500301d0f940c280413400f120008114400e101d0041c6841c5d81801c440140c6410303046030580e203503000a401c46000005200c07282e8008062400c0840c401d015a0380014a03500c01c03ca0070140b10748004d418920014001451045d2044111071000d000f1120010300b040c96400031501c030102640c4039035a4a100703009000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 525768174 1250 525766924 525766931
    0xf05060a051b0a14120703050d02070c0503010f021b01180b041b03112403060d020607020603010909020a0b07030512130c030327080d081b160308161d181603 69
    0x417a0801807404031070b540c5a1540d552454075808a01e880003c2d00700c16002c9a01e85040c840006499500f40a0314601d500c400e00010b944081104941c5c51300c280e082e0750022640d05080241d95401c400400b40f03801076400128003427140d0385501d0000480c10084d02c498909150616010090020900d03869030310420540e101c07251808030303100b6122108000c84541ea102c000400003c0ca207400d00d0301c4d0003d0020f00c080c1c12281001001c0e030000d81950002d8001c01c51069840d400c40c015450b040060200400166242a142803442e807801405442518901582214683e002c41c01c1c8800404405c0b21030340d00725108009440d2240780090124800424034844601303c240200c4a88040a03c5041214907910080926040110081d00c40c00c41c024502d00804204100369a4130301c102100410000f803400d607050038080700b0b42c60003910211000c0c0c9a151401104c01c081d03454984c01200032111000d80040b207080250a1500003000180340010500300e0880d0754050001c41c960804a51743c2503202a203050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 525769424 1250 525768174 525768193
    0x608011b0c020a1a0c150a140c03070318020d030e041b0203030a0c020309100c0224120613091a091606050306060f04080a0b010f05060a051b0a14 64
    0x4484034506800041e501c001c07021410402120184544682c3e13103011000103050240c620140b0f41007400400c3d5074a502c003140b804008204031148a0401452080e03840300010303051182c9405186c0c000103000801389552088035010384030300f5040308003d09900522005401c1613510b00140070038001034a10b1300642c01c0104074800851903000c1c403c128aa590300950541d0380c1c1c000f0602c0035040029212055000030008800162102130040c00d1041181c1c854454a103c02c1c41400560703501a8881a4a102c20241c1c50801c20300641c208c0f03e029050300f0068145031101030001d41ca0803071011001d04c01914000101c010020030342e99081ca03840b11035401d664140e03151b00049880b81e0301003402c40c0b50703048811010300c800c50140003c0c58000c02c01802031400c007240355041c40c2c1940d00c02d410500859102d401c03404100800000898050960541d4480e0042c3c50b007004190fa602030643d9038030910001044035004060081c2014609900c204121000420103003801d012034460000740304001d00454002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 525770674 1250 525769424 525769427
    0x711041109061804060302040e0604120203090913030306180e01050105030601080c01050d0e0607110f010c210b06160201020607030504080403021005070501110d060611032208010608011b 82
    0x251001c94501502551828a8054140b6021920500d1160340035948200200140c0c855101d5074840c2c80108000b404a400d1504211080000c0720b8401d100315403041180220326190a000d05800158041c0709400d07002c800c0c541500134100e25007000c041c0b4044011701c4000790750a174002d43d6191819900800550f40c880091586441c800d001d400c1c01d030360100300c0382c2c2d49035481603004201d811900c0900040140701c282c512410a40c0c10f88402c80020b00440401c02c1a00c41400308603103104d40e030030082080255400000d072000c07000d50020348000c032400b8090300c0c441c543c2c0d40020400b050004d20320750751407100006402c0d0551400d601640180710700ca0026141c3c43c042d11500d40150741001c0c10a041c81e1035a420803c840c03034050600000c021080c000c560000e0024058015510303491b0142039100c958403011402242c0e100d9100721304021361000402c0e1550b8020048960003007441d1070200001021742540c406081080d880207045600c1c0240004880a0641c07160003140301c0600940710b0034230700c1c120 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 525771924 1250 525770674 525770677
    0xf120501030b0103020f130207032c0f01030e0c0a030c061106040807200616020103150f0e0705040825090501030b06130f061706070c1a0a06050607110411 68
    0x42603089640c0050026240c15514002686e20003440720396501400d601c40c50076038001c07c904601280d1414030b031000e00800500b008404000404900d1030605612002408800d42c11900c00c0c1032582c3c1701c103154415003040c0110201200003612200f00659680b4155410381c081d88a908001040880c201c0640340700030510600951304030400310309004c00b94407020001010300385a02210140418882d11176100c0c807010f000100fa082c00140c1c0d08803003600014080e501d022004480348843c055060048100010940381564205040e0030070740e90b80d4003c140d405100b280c200b103959220320002054a4442c0d2481704803051503059503000d600303a03641c0441090b00c1080c0030040035110b4400c001105400c102407da2030503020031001007003050540c0820811074810b50888501c0c03400c1000000300c9507404100441c3c00a06c1881d0a0f041907200c0d44070f44281c1c00107415111082400f02c000700d01c80340403641202028005c028846551402546003112130b500f1521203190086d41403c4c4c4407035059403402c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 525773174 1250 525771924 525771929
    0xf050702030703032a05070c0e01180e1603050601060306080a030c06050415060f0e241504030506190f0e030f070c09141b042907120f120501 62
    0x400035410b000b082d9506030301410841c0e070080404404844058800304c007902d02129200495168517640e5034880c07d00c0b004000c4035802c55441510640010002e81c00f50907204c00706907605c1080001c01e1510002207506001e0322104144440006d06000b00600c0b1000c58498103e0311a9102080380075510300d909a01c40c002c070301000d0f0100f2070810219022a10300d4000513070041c0700320300094030f0411070341220048940135000040c541c000b11800f8026560300101417904100e441855640000c10019500d030004100d40a2900a95442c18002d194250287c2030350080d680c8202520308074544003000b141d80e203903000c280c184031506011810045808503c54211844001c0b00030790710b000c500301c81c03040351a40300e400d04403a141041f00c4001003e900610482081001000130305625040055000ca1200c2028400903601c08042004100d001600040c1020040208400318907800841c1c44684250180c154050010020810b43c0c04c0c42c5035005802c4604c902080e202e01009840d015134840440d00c090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 525774424 1250 525773174 525773177
    0x5040b0402010f03020d240b07080904020903070902030f341d04110408010c05030c04050f15070c080f0d120e0f07030c0513050f070e060d06030b0603010f0507 70
    0x90082009544030f40e81c100903070a440d040c094038100001400000b03e5000c092485241110303001c40b142c52003425195000240051040d00c0d083c010315440b0102c141c8202c0100600c241d41c00190040c00b502c06004910091100c00404c5480b458600c900a00c001e134211b40107001140e1446646030012454500030701c030104e200080d50f50b0b80310304031400e4840101602070303810150b2020011900070740e203d00900000b044014500ea4555103041149801c0d59000c440d01c1003805024001c00002e03448038030688040360002c948210000e200c03503012603111070050311400001354001811109106c1d818035040c1c100e0782441c1c1107a526a1401008a80326060400c5800c0080d4907082600121000d5801903944d006501d41550034101641007100d207001490341c000c403095030010b1004c1015180501d4400c80038842800f06108030f28114404d1040094001e0900b004e00644000c4c40b1031a44a80e41600c1c915004400c04011440c0c9170308150f40c1c0302d60111241403081d1300300703c074803902e0700c0013400742c9800740426 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 525775674 1250 525774424 525774443
    0x316170106050d030203090909160b190c02101b02060c010e0c1c060e030c03030108060a050a0606050316140309031b0102040f0e1e0106090305010e010e0c060d09020904110111010504 80
    0x41d0b020482302a0000d4606111703441602001a44e40f0070b401803003401061402c071501d6031440701d00c8185080000c02d28410060040408804c1d0240e00c409600e50050304003481c050f030503041d490f0120804214007140c0a03421a201203102c0c40c001d40154071101003151000103c88014404504000c0402c0401c20201c5034400c070a003215000a02641240600003507071000d581c00c117a500d02540d441c3d41c009a000420303550002040c020344083e24810300c0e40040c21400107101c003a08001000d445840042c128100ca40603045140000301d204044158400f095489419070382e0800c80c0c00305959402403440a074441710f04030301070f0700d107040144200c50803070301340c1c0021002142c45d10030a1007000c84001c044603541c036036403980c105205000b441e01901070100c03500d41c90700305411410200d084a1801e03000050680c9081605040c6a90006400200c508211034207075544661f0b406450141266030030080d040310030b54051000300030784000b4850a440c020f030b942840f54590003982900340d5000f500d01420280c00d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 525776924 1250 525775674 525775687
    0x90e0a140a05041707030201020d02030a0b010809030306060a2d0f031103040c051215040f0c050303130504051503071206050c070803010b180306090a0213290316170106050d030203 79
    0x2000809170101e103010f07000050800504c4943c0380281d80c82120b0448610350781d51a4406e50b580c1202919401c0000080298150f2801a01207441031050560400902049515000728080c60048501c4020032200b6609445000440302400d84800050749601117801c00030b00c52580c0c40744000b524403880e00501c200702414a030105001080c80f0884000649002c4d100d9000010500a00e10364001e07807061545040b14285070030107450f5501d0f0380e008280f103500200482e0a2a200000030f4000b0380300b08980006864440d071400201c49004007020a4141c02165400240d90380140c00404959020b000144141d684840c000314061182c0762000b404401d09100500c4410b03a058040c140f104018868180003201c0240000d03d8540c00316100149603102015200860620311140b001007000400c007886080078180980c0407000100c0d0384440414a52401c1010540c0c00b0828000740038035010301400419124540d05181400e83c0001c1140ca60a2044c001003c0c1003940624041c03030b4140e03024600300030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 525778174 1250 525776924 525776963
    0x10b0d0c0e09030403020a330f1d04090c150c051b0a0b03010b0c0d0801081f060b2206020304150c05070305100b0111010605061207090e0a140a0504 65
    0x401c0904038020500c02403002000585030800c640019103103403903490700c064624403840034442c00001d101c0b6441d001003030441001c0d180c008c10402c0d81c0030a00c0c18070320481100105103480640b1101c0400c5d90045c1030090120a00807202000401d5494569405001003001d210a85400b400b501c0000c10560006800b2401032146c02d200109090004180700c0d0032946d904504c4883e40c200380c110008080c0000f4803020011020050380c5003004290a004a2a6160902e2715444032a00010021038071503c04058490281a1b230003100506030241d00780c0d444890740045448032005100713800040d064030314400301c0c000f40000305550489400281c600a0040d12003801c403000d00e4079000445d01489203d41c04000140244101e00418042c0840001d44071310060004002c2d0981d0400000543d01d400021b011a48400b400c80b500602e0000700d00d000c1b6100c80104a4025603580e000030302c05112070050104172012504011009034140c548422182c80f29070b164411180e040d1001084095540300c1e545040c2c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 525779424 1250 525778174 525778199
    0x70c02011e051209120406050406030f060305070b09040905030a030603020901060c0b060f01020c090702160905010b070816060608100606020303070e010f03090b1806070c051b0409050d090602010b0d0c 88
    0x32507240540d030100248408511071758001303801440c0818004a000e103c15507051003444d41e000020780080c88280c0c5503485060302d40740e440c003542e000d44800140109035900c0302d070007aa042a510034126550394003440c00c000d000f4103030740c00201d00c034503d41000000e80620030313100744203074580002d0082e0f09906e030103040050002c004500c41d4154000c6a01da004107a0b1040d01c12403040ca03168000e003400c040384250100955407250003104190f880d281c018403010303c241003515242a84440704960300d1800c01c044150121041070000c0c461424850042032080c0007040d0080c1d81803400000b4400c1c02d40b60007044e6241d000807250b140000f080d1440c40c5c14190301c2401c000c43d18030700ca07040000d400c1c20143c54036542c03403c040b250750b410b80b0883d078204a00c410080003d5a4002054a00126203400a07607d0356241d680358840c8420980504801c4050381c1c0d210707402200745640c054208c50102017800005450441c841c490b407809540f80401084090405229001d0344941c0300d460708844a05100446561 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 525780674 1250 525779424 525779431
    0x60f041e030812010e0a020c0304032a090c080a0b011b060615031d0a12050d0f0c180f051320040b040f080102040b0405040b0d0b070c02011e0512 64
    0x801450000110782e01c10014803074105480d000c01407940c14210075001c520405040080c00724810030203001204008015102034a51161a8411241d0b005060b0052442e0a698004c8a1124540006035820b010b0b440380c00b03c40710325151030b803040c1d0b5020b054104641039040c015010550000c0d041d005130005c1d0305010300082c8a06000a44d540d140c04158142620841c000030100740e580600d0315442d031407031400b4100350242d040180060720381e940d00d0580c280841c40100d0288440422038a00c001040d420541508803214030800c440048548001d003c40302042030f0141c1055040000301e22003c010022105036440604031100311171040406400914104683c4101701d500b02c80c264940c500d00c01c00600040411690f2036031500c0c1080141d503400c017180d5001000e02d0b8030400042241c2d42e02141940c3c100c850031200000c60b0003075140412054044403e004114080140030005c40a41000c64610311a000f039031400081e1803c0032264000ea0800a02c0d200803400a11420001c2c1da00205900d03072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 525781924 1250 525780674 525780719
    0x303090705091b070f150c0e100512090a0501090804060e0306090c06090d0212160f0501080a0207051c03051504060e16271d040f122703020f060f04 65
    0x42040540d154030866001d01401403050700e847d0720401c014a82e2241110300607034000c035054142c143c0ba941014116100da9120b00b10701d413080d2400910008403d1102d45001600070000348039644141ca00f81a20703034450301510340400c00d2015002144e040024a41c1c0c400d184030300c000c120503004d0b42e0410071a60400100254001c2c40242050300580f2500142c080c0101048010070b207840108070915041074968010501c407071000e540401042c0e03400b150464000707849260040e1359a4207800e0450400309540b1090042240000c1d0b0091000d51541c0800d115040007041c00c651288854204004d5407000c0c4500c0440121100200d520421035038002c440c01d1703044d41010032009a19040b0200050000c031101200b525510704200b056071040540c6c8603c22031114a0742e8460300d060342d9400c40c01185200b02800c03c902e81c100e1014414042c0b100381034020520a03c00d032070007050303101011b4400300501003203010f070405524000c42d80c1880420b03900c2c154440420341e801e142c1001030704021404007090352038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 525783174 1250 525781924 525781943
    0x31a0636060f031f05070c120c151410050102070e040b0a1d0a11090106020d08091204140f01050403080f090307050d0302010f0e0609070e10170303090705091b07 71
    0x2100d0340e43c10041a852a0702d036040c016049101c000544040710401485001805900c20925000412aa50b07031103409107107080c03142e4102c0c043c2c00c1c42d5410480e503280d080d100c145054000b00990100d041254800c0c9218032400001c01c0c0c4980049868111610409803484244c202082c000780c03c003407040380c0c031103e00d945c0010341040f4007001888805902d83c554540ba004140223905200c22082e90a11401040d00e00014035454030100a540f40b580d002c05100b0009088042406807400340100d0050503031010505407903644a03c05d902c900000b411025214170b50140c0e6941465028800f03440850360811000c5080040641000039598081c0f0780650b494082c003d400f182c0f555404c3c01405045009900001c7e03e01405680c58044030300700c02649205034041c004200c5e1366000014a070040c6ca20702d5111508544594515520071015904100e20000d001100f00c0c184410000c0691310840104084606840e41d1b1000d000343c0200c10707940300a143e01800b800c4100595201c0081c080e0341d2042d100070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 525784424 1250 525783174 525783199
    0x91203090607080d0f0c080106050c010e06091f0513030f03020c060106080f1302030c060d0b0306010b07051c120902010c0c030c140303030c090118031a063606 70
    0x69440d034402c910498000c4004140300d660307076001c1d1140c03145011041740c0402842c101014090900c810501c2904100000040c2c0003a0f120340a410101c0401791040489100d07003003040050303441e00600d1070150b00c031844500e4446420315040c010140a0309520a840341c0714181c5440845003410490245014541c00700000c49080004000050082c4000d50b00d00c0490700b0b00a05c00c6004900c003504007003004c00c1000082026a41c00700390030910b200c04441c210360b14004800c1101c081c109042d03103240d142c0070340000041d8650500b070080186504c071390306582103056107803580245405000030087c00140d20310301030410100d00b503000c00568ad00506224901c20000c1d9500d115043d0550000c544580b1802420030480d02d64962400c15a48124007860451078402840100c5003e400c80b031504101c0103980300289031110007102005503400c020403c20601c1c980d0300f140d11014055900304d00940840901403a0061000c5c43c00c8030140c0c20708054489241a01c4545078006000380a499204078220f104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 525785674 1250 525784424 525784429
    0x20603060111070b091201050f010519050d05030d1b12090c1e0e09070501081b071e0b0c04060203030403030b030102040503010f05011a03060a120305070602030a051b0c0309120309 79
    0x10031006060f131400259581003c5000d00500708424000641c0c00d0703041c8020311004409083c6018107460081e02e04aa0301c10801003040d0061520349d000b076400414807140076050120100c010869000458428001c030311100780410001e0703924036410800100040c1ca000c4000c0015000384100c2400742483c20721090f20790010b9a118941d440c101c0c0000000324004000d80002044407aa00c666604040c0030054544000a04101c00051080710310400d140c02c3d58500c1c2d00054155242140c00102d481010b2183c54405010940d54040568542c1080800602602940400c1300c003901c00b958059401c544503130390b00303074050b11064807a1503065400380404580d07070f1402d1140105038889403a010450b94585904400501241c24035010143c40400802105031160000203044420180d100d02d10220603003011103040c042d0810040c0401e00010600a82d1f0560ba00251b010385034909901e2151030103504503000c903101d00e40080c0314940050082e03000d503140c100880220341107440140c07460001035900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 525786924 1250 525785674 525785683
    0x807031107090e0c18010b0405010509033c03070809091510170603120f03090a3c02030d0309110d050319050909060d020d050d05040602010f0216020603060111 70
    0x80c3d0541c03101350b4480143ca08403649480c008001c40000d0819414400d03042d801e0300c905d0141a050040010786007840c4c0e2000c028a0b400c2c1070320010211103c00c03a10f8000c0710343e00030b0790684003004207403011500c01c019804403c80754403a0340300076814074012004051100c2c40310020800e18000380080401c00c00d036116020b0407915840559203504800411410200d03020342c01518960003a40507014010390542c628088070200c003000c0036029240d81c0c80e1000b40d841c11100000050a9601e90303600d0b002c1600506020b054072114082c1280300007407040300f80d046440c070f004c08081d6242d8069070074220320030b000307500c070240845c007030010b4003943e11440000c0387c1900343c981021140c1d030303100142d44c0344100c5071800c512030512518603149251801d52400509020f90107411244100c2d200c155400c115592100440c0c0156400402e90b070120f1031401000d030190b08a845000099428103c41c554944a0b500c215a40790800c40380c0d41203400a5502400015000200114140300c1600341c03150303e4210402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 525788174 1250 525786924 525786941
    0x3040504050a0e0d030c12050c0703080c130305070302010e01030b0a1e0e090a030801050102030a02030d0c0c050a030903060b0f030709110903070906150519080a0f1e0b0904080703110709 82
    0x44001c1491b500c0b400c03004042c0c5064080c4000902c0c80c0c0014007602501d40d404882c0c1d490340500d04100940c46903050300c9801d2040ca00c0803032000c580403c0c0001004404200d03002200e000341c0751101c8005800d0019000e551503101010b1307010703c00e01000d0007510564000440507055442103580c2042c3c40d00c0051084605c240c2c0d40c9034059001c52902d4080503442000309000d04400c0c80514280055080701954038060340b4098980b0f0350b00c0b03040004450b0322810000580341d0f0040c0c11a403404000d42809820464540000d84081c0e09182600b8610300f48448031121280002e002000c21a103030481020003482045074a4031091820407000d89280c0c1c00700010070151000c07000000d1214988041500300c00555401d1300c0610109001c445180d601c0c04007549aa11100c2c1803115059407591883c400400b1584d0b2081d040310302d4050030201c01c2c0c2c500c0391038001d040102d0078100490f003003141c00c012060400303c074000c080c82130410800c03000910803c0d2501e404000d08048821058460304d991080d6294803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 525789424 1250 525788174 525788177
    0x9030304170607050a080f07030b06030c19020d1b11040504120912120c1104020c0f101a06070c050303040902070615030519051204121b060203040504050a0e0d 70
    0x41e0032030194944184003481d040f0b5102d09169240083e142c00c081e010341703001070031001c407541050002003006000c0d4002891000e4002c14080e900c0c60400d01040084d040000c0607507818108414214603030340000b601070b10050681d15809c0d040c80707101001001c15440e10008440000c07000700c01301c0352601e850080d980101d00c100082950004034490050042101b81d100129000c2c00302503144c0407900424503461180c1d40c510304100b2038049424582110405003560903001440052945003a550115800b8803440090303042d00c6400403100c100030306558001d1041c400300480440071910a20b8180001c0803d203220302c98116240d640d9400080c1150000d074000f000f42500000c8c080100f21300380c41031710b0310900700f00501c200c01415500c4180d510480d00e40320030788040c003d00301441400780402c10702c4400c0e200d5031815580d4684071b5007004405055001c080350900300368590031072500e0700c81007018242c40c4c0c80d5000718185841c210402025000103072040c2d40aa56500c031901d00003106200c2040c030144039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 525790674 1250 525789424 525789449
    0xf0c06090c1309110f0d0510050603011121090f0106060c0b07210b0409020607051b012c01030e0105070804020a120503071112070305071e062309030304 67
    0x9201400081e00103402c482564524100c00c10000488400d08501c4029040e10f044131107401c1e41c40030451040301c6240c054101c2c0324000003641d008201e600014410f04095000313100703640d8003030b0381d104546c003401c0018040d48a0303110740c0840003414180200d40c0600c8180c21100c02c9046e841e515801c641c11132300200c000608030001c034030501054041d1241c0042e03107407501c402d0684d0303500e90b110701900386074203603d40b81602e4a15079403d664540c4c1008041d40c2d00100320366655405032420b69500d0043c10794642d181221444020b90648c003500d0340c0d100b90ba0007101940c0280700500011044030f0b000c0c848103410301d651000d21500c42c042c01d1180d03e108502d45d84404070281803500400030301c0b40a5a06c110f48041030100710900150022040d00d44550340005550348150940001525503112100703007805e1482020b41c00000c0c0140084e480e0100ea0544441440011107624418850b2485000380d5002c11241015481103500c1011900c692055410321181132401480c0040e080d544958420f954400a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 525791924 1250 525790674 525790693
    0x206030703270503070b0a110c0102130905100e041a0411041a06160807050d0801380903011401140f0d050c06030903090a030b070806030a030e060f0c0609 68
    0x501c1c1a68411503400701c04401801c8000350b41e03c603664443c0310740c01040d1605141c0407035030314039203a000901c828105520302c94a4040340c0002900130b4115024056460518110020f00ea20f0903100e918091850705800110742d604042012800c14000b034811118402c1c0350541d45801246005070500032403145400502c8a410001000300f5101c900407a00c0b1100c2d5201d4206034030355101e80c12078952690b01d4135607051408090811404e036006694019003c1c1c00f96106007140a07031b2180b8007e060b541b0311500340e0a070501c0441c1c1c0105c40d000807040d10303464100b91540c101a80700300b4400703440070400080001c610703a5490501d203000500c0c00ea102c4d24100780007203d410340030b01e0700020320400d0034410780f035000d5a0912130304d8a03603840c0c4103008410302030701c030000208003600c20034402c45020810190402411030340d40e1038034107980d0b202240e07003030001344201011400516000c260042c8840d010350b54100459001810000c0a5005904040a0040800c0704000f0840240f05640c0b042d03070312a000d040040b1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 525793174 1250 525791924 525791951
    0x120f11060a0e180c0a031109060a020609160b0403030e03010f0c110717071e03050703030507030306090c0e2205010e0a0e0d0f030b040b030109060504060c140706020c07030206030703 80
    0x140030981d15080d081c50801040014550041174a962801a280100c1d004d007400d2900d4100e84115222590003400004102c0350854001a1050040d008403088421900360100d1070200b00101d0301449040302010081000800d1044403800c400740b0b00100001000660500d484003100e080000000200b45044180c0c00040801e000d41030013004207490f1490f80c014450751440e03d0b50310b00d004010441c109100080d43c1c00c803203e601c8401841d800710459220a44030308000e090303500110005c4000904054020940f16914000d03401d103003100743c4441e08a0508002006185040d0900c658a004484c1e480d03071000c80c0e06c0340502c600070b02d03960416090608049181c00240c0d00f807000c11240b658088800820001d40c4041c1201509841c0c3c5000501c03402040c00041c09040c030426030035419800c20008205011180d880203018030310412040041e503525080035101820050310911117018248103d0010800f80d40003026018148015034011507120390004441d038201744d48610000c0e568031418010f60 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 525794424 1250 525793174 525793189
    0x1c030b1c0b040b060d0c0e130b0a020c160b0901030b0f0613090c030c1d1305180d0f0905011b0605011502010b042c0709061d060a120f11060a0e 63
    0x81005e07110460707050100d0f01c0d00c200088aa01c900303026400540c0c00280d050322848403034100141d005080412034185142d504010350440e48840449001e018000744024407052200b0045545654074079007400503000c019070050560940380c5402c428003c040d01c81d00d50b0b88100400081d0020f030024030b015410610303564102c550000ca000180340c641b0a0300310b070458100c0c0401c60f0700002402d603190b002c4094400f04840220740418040c80764102024044001d0502c800710070046080c1d0300300c85a60100c180c04441c00c09001d9441c9000c03c00d4400140030359445040c00c41040c41088400300481c1206607500000c0f50f509900c00c043ca0030521a4500b000c91307081c05041e60351042143d060185401c552800135070060140c410841c078529078141008001000d0000e4402441e40c0802044260364400d1001c204a0407000040d001c6c0d41e0000025000707103045505081501c110a100000c00f20099440805540944105542e1104480c16084980d92950014040c00706d441e5200140740e80220700f40085c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 525795674 1250 525794424 525794431
    0x31503050102040801022d03011203050f0a08041103011e15081002070309140f040209210706020f06240312210624090406030203070306020310081c030b1c0b040b 71
    0x25010300e10070407c0354800e00310950b419207500c00d14103000c0c0f42091405a501344251020f1980c01d03c004211902090b07041409244640d000c0d000440304414150205422030301d00c038a034550300700340e00f41d80711100103125403002003800111a86140481c0c1c1b1050701e10f1404520314450103100c6d8001590004140c4d1014465000300301c514074031040e66204200003440c03500308a07410f50045901047c0302c00555515038038070039620404601c0b550700d580c80007409a11212240602c1c405440b03002c058600400000801600c00c102100c6aa4221030740507042140c40b000440c00140e0500c038000480501038844001000d001c90610340141d01c2c0703244030f801e40301400b41c020581449111803081540e091000031404100140c42d2071031583e92003041400040003440c6039000079401d480307550000700402440d0342c015401410803140e1a26000e90f2000c6056503400c2c10960800540b04803012486c401d0b020303804c180745d814801007102030426000300f204400600e1310002604c840d0780080c00c1c4024800880c504681 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 525796924 1250 525795674 525795727
    0x204080601210804090f0f05130b07050a080c07060219090812030906070c2d020306010f05060f030421021b0a0b2205031e060c03010e0703150305010204080102 70
    0x2c1c0405902c400100740500d220b5024056211091554a0b8019030320803198403481c80c000b0001400e24100c4018001401300088138600300c400c010401d403600075810356284a01c03a42e1541d00c5035680d414585110b800002d02201c91a409101d602c0d01680101142c0b1064138461ba901c4491920f8541c00340e00c4c0485483c06203000d91010814000c0c454004070b40a41d11011a0506501d96402841c142d00360b14120000500e15070030700f4070080085c0801950300040140203c1c111659a600e54015044004540c4502584810104203e41900405001070b6a115001d81001c01d41502c541913025aa41107005a40006030003641250214101c0400c141900f41c4c4140c44c0507804a08000392200c40303100e06030032114011102c40b41b102c14510f200106030003820001e030685490110015450b00030041b04900700d2201c0c000e000025402e01d070310380c0c10350f8103c0340d200e240740c40b02d1340380c0003070a40050908940118030080312140100c041182400184010145c1c00d000580d40c55a200c000c1e04083ea03030020100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 525798174 1250 525796924 525796979
    0x403180b070c0506031e07030f1a0d1e1709130b090703020f161a07020604170c0c030a150c030603050c0103020f120a0203040309060f020601270204080601 68
    0x30040b03040180c12005450090341c880380e40c3d80b01c0c4019540d40d400d042208103401c0e4024420001c0280d030681180c003038510405401d000308048800302503040d0111408080d00322140c4820000858900c4000d42440c860500402080302c82c0307911009081240056500c118403c001740d1f108081c104400301420380459070760200900720781900010102c0d03101501c1e4004241c0c004c2400104502e100040700d5407034100218103510012686404654842002003191803241d407100012303102070003c2074003031150b40e006501c070b00604500215411242c01c00c045407909807150700c03000e401580302084400d0002c1d00894540c01c642034500c080314180e0b006125928101404c082040001441c0021802002e40003404c0150b140c07100301d60194400c2c003440d024040b07206080400e00202c04074644c01140140d000c3e5a41c5001907855013419100040c03041c00d400300503031203140104007600c0300e0b518024440d014440c00c00c140d4021100080c069030020b80001485411220041041c00d16050b0000303c1c4000343c02e64403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 525799424 1250 525798174 525798187
    0x70608090c010f080703290f0d110103150b0c06150a0602060402090403020c090c1c02030c0702120f0102071a16050d0b0d20010807110c060706090203060403180b 71
    0x30021919075401c48107104864011170405c81c002e41000441555181d00405100130345116100d241402e040302d64000e000d64075041c185800c084031809861030300980100c2c2c85100d103030011002080a28055189191514004100108804020035100503000c0081400f41040301d0307a01c00f540d803c01318041c8100c82c0c041c0c0c03c20200c1e401041e5282e2150301100e40280565a504080e41024440601d26505c06007050404c041a00004090044400006060381da00d90030481c022080303100540e00880041014031040c0b006241c20302241106041d0349003600c075004200d0850509a03001160100c1d034024050f01310710315440017a40e165510801c00c2c800030060071441200500144200d003483e0f0781c602e4030b40951618503164520702201640d8881d440c88a1852500c400d0046c1285280407030303000407190804900070310f1050303003482e45100b58840034001e868860700404c0903983c01520b08448607600e940380303a00943d45c02d00c1001d100703500070740b00c440c9071040c0d0300120400c5250b580c010100401050040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 525800674 1250 525799424 525799427
    0x100603030309060e2a040f0c090e0a050c04030210030609050a0605190e13110901320105040b070201022b020d030509101d060705040512010e0d0c170408070608090c01 73
    0x10b01d11060174840c010f05050003041c0454013409803080425281800e2515a18615600c1480103007150440c0c2c401d0002c40c0c5907000000c0948909442280513100300384010705c00761504031425859a48103040000b11559101d6441041d141e0450b451507e65a50f0321080169003810021412084c8600351041060b80c10310400b10700000000e40140440e900c0e082d00da408011001010b41488000101035030b04030742e541c1407440000105105420060091032800101c9400b064000c2c9400d400c05841b60303410141000f00c89080d03134000030403e038118401c04c094102035a80d19002000c00e4621300500055185148501030b240c80e00e40c04121040503d480304001e01c004010035a120079a11402c0c0c04202142e4422803075240c01c04102c10103545005d400c06205655412a0040040740d2040e11f400203c0700310040500c0c200c5a02c6091808140c000f000d0f402e030554400c0721002c01803031041046040c01e89001c40b9405c041d42080d041408158080f040c144880c6400200640d4441342c02c00060034201c003030780c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 525801924 1250 525800674 525800713
    0xc010207270203060a090f0c1b12081012080c160303080a09080f13050307140d06050a021905180603130b0705091002011406060f0301120203100603030309060e 70
    0x749500c0c564048081140c1303960f400c1109001b4a203000050011805680c0450f0040810600100114014000030b64044000c841101c942c6034000103941c01c40c1611260a44580c40010011100c11f261280082450103d903005d030b240c0300d4092903c1a8450600055031450581c10f034401d10769010317020b4401c000080d44808043d9000c40805400301c2c422040385854061350140d40c050310b004420106500003806e003003010150071250100c00701e0714510740c5d401c0078100d94143e484d506500044000003038004a15181c00083d001900f240c0300600c3c00c240718290031070311460720a4490015500040c1223241d4480c941030050300e80d900303c0c0c6032451420700040c081d5150502c008000c1c10b04c204840041c801600442c00d403008004c000d000b0080280f8841d6009000700400e00029034000d00c0c0350040f6145041c40b100b40c1f05c51079a00c1c01c00070f156034244a03003d000c0594207801281d0504c00c00d0741180410708070b4040e8100940c0300e0388001c5030034581703403400400f91842300c450010303194400020300504403200b55 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 525803174 1250 525801924 525801989
    0xf090608070b0a12020405040c0c12031a090405070b04030b07030c022a031608010204080601143a03170a09050d0f09080d020717070e16050c07080c010207 68
    0x1000c00c013400c010b14000c0043d000c0d0340d11556000b8545000b03c080284c0105501e0481840f03a0030004164460180941c1110380d055950300482c4002d01d84042e548c00c0040c40346800c140a102100c2e68195030721001112580681c0048960242d070005010440317406002e103901c8604980060140c1c2c06a46c510441111082d103084000294150b029103110b49041c07215804030062034100541072a140c0d07140c070740030394030138403c1c11350610442d000082c818082001310855584020001c0c104103190040309070201c0d031003280200c090100c0414000d90704000d0350810a88510a440782c1607602110b40c1c1c510000403004010080080c20a454200014008141d200c1c00944a0900d62003500e20504200c481c0f40031500b0103da18490380c250204841d400043c00003c64084944180c81000304ca5a41511002d051081c4000c1e84d403c00045076441084c2c0007a0415605549022402c1c4500140103501c0c044c4194886510390300000600720071075a060241101400407074082010b103604c03401c45001c2c01140d50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 525804424 1250 525803174 525803177
    0x906010305151e010e0103060e01090209060412030807113705070e040b0717010303050f190e13020a09050d0501090b0f0609152d0a0f090608070b0a 65
    0x910000310b42451469040000403406030125588401503114560000c8154a01c240400c07440c1360030020741e40c400d0164000741d0300c100401c02220703407034188050040e4005183c159441902880f001c0b41e0003403100d902d54201ca001e95141d895506007040c019041e070140c0e105500c0590446036082c0305616415080302040b154292803604c00d016a185104183c0b100902d00030114094290009400710070b40001c03034003880c0208604e01142c3c031554030641c0e0f040000c0d07801c00c20240360740c0c00420103c1d0061001d00140d0f140742c0b5031580b4102c03200324109024000110340313201040300700c0d0701d030100303418041d0020401c2030a854045240103107925001d0960ba05c0361084500c54030b07141ca030038401c001007034001021050303122460703c07181c0c14925581140814215416030094801000040e40c048115580603180d91002d0702d049401c1d8022025070080101d18190740303640081c01d4801031165100c10031071000401e44400007001d1241441c0041003a1080c1390b0003003005030300c009414000b441c2030004660808c442c0323 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 525805674 1250 525804424 525804431
    0x10050f18160917101409151003021807020d03020c19050c04020403140c01020c090430030204030201020111040e0c0703022104050112110d1d01050103051c03060509060103 75
    0xe00000c42d58242d403500404003812141c0400010f00d180002c005a81e008804414841449402c04140845008032500c0205a01c0303051110000100398a020741c0156545040400c1d150301c0340c0100d94090840031115218400c0e90303042026041d0b05011042c4114040d1809502c1d1a0354984003544d1041940c1100d010041034218190421030100700e440c1d80303117001500640d140c95490516054071041010005e030340303004000c4600031a42c40800c0040b0601300c0280030000c9a03c407911151000c548403801201804802218035036401b6509941120300c05140c0d1700980d03103171b00314800242075640c66a4850741e800d00c213020a10139052001000d50307210018407251900c1e0b410a003130892805401c0c021019103100600081a1100b070390000031300680d5020303201e2951a003074003ca218200d40054150119105c0c042c0f15010104c07249400081e01006c8580d900e80030130044986003403c541c404c0e44111459880031081420013004441d1031230600340581410030803145010045214040000c0c52241003554 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 525806924 1250 525805674 525805711
    0x1b040b0a0302220f15170607020d08150a081b0901081e03070602030a05070813050d111213090b090f0103030c020105041d0a0e030405152110050f18 65
    0x180d90300c1192040e540c13860034030413884d4210260030f0b00c10300d074020700101010b40c551800c140c80300002d0540c000d15213503001f89500303180400b0499540c100503050f80b5500300240040703a0070756200d0101720050320845000c2c0580c2c6040c60603581c403503001840018026806070004001c8154081002c03001a0454418101a42e120200d003d007140300c0d24100401c19071010041c4180c0300344990010344107450a44804c0b0160701e42150b01d10708428000300003803090b03101b05030b111002489411030500c004400800c403600856540380c58a843e41040385411000011107104015241041c0542041610705517089a03160030400490300a0041c14000901480b01103400c003003c69128400b00e030018948210322803030a198102a038481101c0c2170324115800e80c00d00c000c040e1160750100450b03040b00c0008048003c1070307038441d00f806041e412039050740c040e142c103102000b88107946085031248202103620303000d48a03d00f4a800c101e80454003008107405003101400d44540a0044081c940d08200c4024507451402e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 525808174 1250 525806924 525806989
    0x51209010c0b0103140114060d02040b0a0f030b060a14090a1503080307030b010e190e04080d2406030915050a0b150a021902060406050c0705031b040b0a0302 69
    0x14407010007401c2c840e482c0000414420401103120103004030324003d010420b21111a51800c400640d42103030301c03c0c048001c05005240c1a4000412100041c010407409940d50200c100c10001c80c0d8000c4d21034500100802c101c0c0d20304500c8003009400d0b690824503546641a0210b64a144018402d09072075503510031000d001840d60b500d080046a01c90760166030b03481c2c0008000c0150200c503c1c07080c040f0b801c1c80502d080928101d5082c1810004030071518003a03030301c7c2c4680e0b21207443c0e02600a0702c04050800007a0030414480c0503107030601d058007007240080b82031407a81c529234801c0c6512035001c051a1032403d00000d91685842d41840c0c4100d10302041c40d403030340c81d04000289200b200055111007d210340b040e03803800c240081c15641d4059001c1d41d000d8040e440c80d00341e000b405128025489007040000344051030180001d0150700b20900c040f942c6142d01d13070004c03078600310f180c41000c00c02e00701525a078002c03480c0c80d006450003201c00b0f4403030b41c046500d0365010501c1d2898940308000f400c0036084840c681003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 525809424 1250 525808174 525808187
    0x804030828030219090509190b190611210309030c2d0604050d031e06060e0406210305160501090f02031c050703030b0d150c030507030905120901 64
    0x11094500889040d411141d0160080d408a40b090540c041c01144812819004014941c00c6900c064019601551001c0842e018665074541502c9a60b94418111180313403503401000c541d400540d00d08100150810402405128100e9840d11107a48400d1901e0300c101628002e120641400b007000540300d0b00e42e12800f60550040101d030100a116410100301c10890ba2540307061035549070710310b600302c4200940075540c8409044501034625801000080c201900c21707413100b85a007032031b1402c1c1c1c8510803105d0321400130780c0d2095010400180c80020b41c02000d15040c41290300411030b4051004000e4010794a0b0340d03651003900e0015091000110301c2101c10340000400c2c284042e13200000f040740d0700c09842d0412030001c40607401e0f40240300c0c8207800051a144110989c0c00d185e5075440301d81c00c100c00b6540c110058508240c3e159000102000d036180000c03003401c117901e01c000034020042a00d0310301240c010f08541009003541c0826051079100c00c04950b010407050200f542080406a60303184440c01030f00d0030f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 525810674 1250 525809424 525809467
    0x60b09031507020c0f0d0210031401060306030201141605030403061a0906010f110f0706051b0303040b0c070507120b040210030c0509120c03030a02101b0e040c030e010513030201051308040308 84
    0x44143c100e81303200316456481390843c0c2c00ac10301240e0b03c60362110700440c1102e0060100a0100780d207101215034481e414030103088190200442020159425600e031401c6030080d0340212885502d804800c01020603803060142d40110980300460b0714504000000c04402181381081d051103159030030700c140b1071018010340c060640352000f229400c9a40782c50081499000c203030418207402801b4640741c9510004001c0ba0300494000440d249591140e00b0f000c001d540c04440100d03014490500001a2584050007411000d0b0290603a004076140038018808420304081408040601e4001120081d50300a07041c2d80041c54203403440b660280041c215507180c10100304941d54544004100d0201043d40003417405d0064802c10401c2c410071196801d841640c020710044100071680c0080025400e05003070b4020031540d403a0f8070700400c51040340c408403800c440c01980c9200043e10980948014582c090103600d82241d42c41d84d19001c0065540c440040501450000030402c540000e8440041d2a4610240f0075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 525811924 1250 525810674 525810679
    0x906090501020a0c0507050d050d1110090c1409060306070e04140f0711010c020604290103061a01081302010503130b0708011805190507020709060b09031507020c0f0d02 74
    0x56428140d0f0001e00107031302c00d1200300c4580c41030000102e505e081c01048403017141c1d03202c0c00030903c416604500780c602260030000f5546500ca86000c0300400c02c468001c01d4011401040c44140490610840b10601c10078910140d00400f8803c0a01c0131035200003030390503130094440c5001c1c10450b02d840c0000e400340c14480360700c0303403400d4100c0301703000c12760090568050041000c0d0b1544450705000d0410036007a81c0740f505014002d40c02100000d0007241d0760444d80e400044541207203030890010441c040158803002e820503510541c2d203d44075020b60302c0200c2d00c510554030900340400349182c490f0019244107600200241040008004148001a0200c140c4003141e803120103001645004000100920000d03c14030f500703000518620101401280318503406000b95401d04414054040d55a41c0503060144c2100c0c114070411200007505107192040f84060440b003c4229034581002c0100b41c50104420030b021650b0200034107001c01d20ba0005911100400240c0e10085207036103a00003d42c0d103410b2004080d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 525813174 1250 525811924 525811927
    0x6030203011a010305060a0f061803050303151513090908120415060608160804030e0301060b0405040608060c070f080f07050a05060c09310c21140604090609050102 72
    0x3000a0501d800c2d441c0e804003a0781c01c000c56960f180030828030340c2c80d41c403400c1403262032004180007040c829000e0200880079500a03010a690f252b48852035a0710444407003034400e0441000c00323050b00d4003150110003240031009580c00c0102c0032049031100740d1284612038070700d551039840104100710581541c0c6641c0d48041c8010503840c0a0808801c83c00c440750418001380d150a4010440c2070242d202d00e401076580311010b545500840506690300d22014100743c09104401002071041d42d000d00502c005084004101c549461034003007400142c904c02d401010154012808001120b4148002c3c4c074001c540151807828014040c1c24030003124880d0f101c03003c540080000d403d8003030140004d0780802c1d042c41303a0112000c03950b4201d000c1c03a01e070042d0a403550344042c1c03440751103c0c40b05030410001407600b80b40c1d2525801d03910804001e011140d01241c40c1c0042a0801305500401c12050308a0244042d11001072048030002103a04800140c010542c622642d035514102050069981c00121306580c0540210b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 525814424 1250 525813174 525813191
    0xc0d0509120109052b170a0609060b130f0b09060d060b131d160f02010b0306100608070302030610050a0521180c0915011e050a0e010203070506010e0a0603020301 71
    0x9174848801840001d02c62052000c141d080601e50001c4000d5000e069890307801c1061500c0c2110308900e0b0242886200d0358881c0000724900c1c000e84281d000500e01000d00c03d40e9402c0d400480045080903500c4560500c0346010200f180d4810f6908858108108495055503091004c0e2080010b1070540c100010161010490b241d0301c400300380b0b030b0038252000d03101c515103d41082c4824501a41e01246c44e0801c00943c400c1c1400064012070b03034000034a00c280004501c40036207070046032406c00c089030300e115003c07080041004038540041126801c000f007840c2c15480c40ca00500410041000483d8400070400c002594118492080d0b00391001205003a09158400040c100514044042600d13515400640c285e400100b00400180341c40e0010005030458005a8480340325185034940031603c681440080c2a4800200d6504500301001c1d00c3d2580302c2c16140c03c40c521340100801c10352000380c0e042d544200060400f259000406074111082207004d02100e60718040c0c030102400c05584003d4040d803d12001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 525815674 1250 525814424 525814433
    0x21507060e0a0201030605221a151305010206090c010804111c02270a090f02060c0303010608011401050304060b220209030c09010f0b07080f04060e0a0b0c0d0509120109 74
    0x10344142d42e000f640d0a001e02c036107031000c10881c000c040c072100d0491004003805015070313005c80d002a50021300510303c1c3d01c0110808000718032060003090420380303c010001026604102c0101c1d0b4403001d02000e10042c5402d14100410039996030303030402c0751410f215080000508003e180f04034a03680242c054500003c01c17640c034032001040c808954041740b0840814060070603084042d01e0b406001654103852189030384412105038014002080c1c02d0312078000c0382407070b0005a15107200800d18411084011360380d03985007500060103003406812540e4120014540582160780c00800c1d25001038114800181e040c11000004003100c80d588081d00c2002c1c0540d2120090f0840e5a02510304078506a0580d1403299a210800042080901803400c00110084062041c1813408002d84011841640f0035841d140c06504107901d90307006503001c0000201a060b8040702424000002c1004084c02000942408aa80c1c80c45d6192000b42d1034010412402044042c100d03038507042c0c615040440b4900811040c00541071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 525816924 1250 525815674 525815683
    0x71d070206010b0f07060b03190f0b0c0909040602031005090c0703090902130b03070c0f0b0a0c030b01090909030c121e020304051c11040c0503011409040f021507060e 73
    0x8a82000d8007070107000290010041044403080340d1860b445500d40005a59440000e10f803440c401600740c480d400543c9505841e00e0182918140140041c0e5a400150329008100840c002e0503142c44040c14000d50303020780c455542c06500554011400b42c1c0b41d542c1c0326080c030401c150603400f10b58030110f000e043c050300c1060600185009402681c519080589490f080000da00c2810b50515134184914001c01c800e13008032010355006074251a04240300300807502c449039995403481c4e060b25030500040034011030840701c2c821841c80a09509052007000c00c080700203041c402c4180300da814070b152038080c4081094030401080e0442507010311070507007114031444000c0c0001900b00215442d09140b14024000600000c00d40c1c08481c002440c81c0c41850b0a01a00d8502c0100300d5001c413000c840c401c2450000e0f6a681c0186c2804c26001c2d52080d031250315104c0342d60580b01e0f0703120000b4004e03080281440049036a9180121040303406850001d4840b10303080c1031202502c01c424000d007000d45050245100d540001c00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 525818174 1250 525816924 525816931
    0x11030307020a09051e090607031104080604050c0a090b0d08090109080a05160e1b0a2c030c01030908160f082805040e1513021c060914040311071d 64
    0x8016804050041704070313141d21058800002c540c1c40328000401440c401c0e00400e05280d0401941800d040c0e0f2072444600e0000281e50495030703500400624a001c0c100907194400801d40b069007401100702e007801040c1000804c0c81c004d400d0100014010b29a0f9000b600352038024600d02c4103e80b2072101034200703551244040c6011040340b605003240081c400d000114213602503e0581e808030a020642e0461001c2a0b0050316010107201150380c803013002b10300c2d0582c0d94402d59a8003002440704241c010805003812100d0352080d052502e00405100841c0012003a19040d02c0404095a0305200034280051070045205d4001d08e0900d0000e21126130241c0c44c3c00c6100020888904041300c00b003800400c0e40c150043e40071f00c6907080c00e003400245102c0e40689001180d000701418580102c181c0711b101905991014440d05103006410700c064440c001d01c0d204000c014a031044080154a200d501100b00d9480003070009801c101d20401c0241b200340062100100408554108151000300b540d241c00c01c800044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 525819424 1250 525818174 525818191
    0x204050405010621020705121603080a020f0702040506030709021c05091207111906031a0301020408030304031202040b0301060e0f1e10031413021003060303090311030307020a0905 79
    0x2000002c000d401403002c4e40b100c61104041001110144541e50020340140c0d00503509449900522400f51041d440103020141030502152035828507428060b1507d080940100042841041f41903402140c120994240035030484001c5116210703103001a141614581040d0855440000e2845001850a45148488503060001d02140d075034003104503280c0220100410001c40308110850000d10341d4010076403108401800e01d204181c42e07103801140d90105820040c0460b03079404141c00140000c0d04403147d00b10741100258907150a0040d41c47d164040a04024148803100f100119240003940681d005010a134504584a40e99284010007500250178150701030250402d04131601d007800b00c088410f41071843c5640030b0600b5600e00b4810101e0542c1c07805802c05580d4004445807072301e41000a80140129916004404400e00401c6003800001c041081850300c1d100003000043d42103180c02007201d0b0002c180e9404410011b000ca41140300c0d4440096115007401d0010420368041c1d4021030040521 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 525820674 1250 525819424 525819431
    0x181608030702150708033706170303040206041415070b222102030720150301061707030209100206011811040b0903070503070b0a02011109011e05090d0602040504 71
    0x350884585911803500080e102c0780040001503101001d102e200d041003a614080182c005820300110f00030b0408045a00c00081e0b11b901c410028042c50100c0780c9d11208681c0c0c080d42c032354142940065035030b20480c41703a03c444200340c00b41d103805903440c0c040d400300b15846034882603038a482c03d107041c00d1528000c503030101000700100d50b03004003002c8000d50015016400303c07a801001a483c107003100703000046043e110440c030041012000090080f21240b0340da200c012030100c03d070800c0c0401c100000318070307440c8243d0050f01400104506644201422201400400c5c0c01203d615018021400b921490705019000182e046442d0f5000d54009116412039001850b41d00292020f50850800e80721511003114078a0000d010521071903125900510013181c00a003110300302ca6603080403d0419046c0d9120114903400407a212074250380a014080c0803100001d113403440c0000d082d00180c002440d681c21a0001802620248803072800360048030500c03040242104401170092038120f02940c084d00900340520b04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 525821924 1250 525820674 525820699
    0xc0b0a0203160e06090f0f1203131203050d180b01030305090a060203090f0f0f040603050318010306030c0b070f15020c190203030f0f0d0504030509040b0f09181608030702 75
    0x4105941458454001c0426251418490400401b100c0850805901c01c40e40285100c2903902c10400c2085100c0e501d01664440380c1384a030415503038045074000401250844000e80c000303907111003254084113403810005a00307001702465855804a082006210007020400407041c1500000034100c15241118000345180d2501d40480c1c49000316496940c000907004ca08800618202512003422070000d0500007881a03000001001c0d50310315801551590000242404200c0c01440ba015101b082801c05008091031551a100c500c80c0511a404400341c002c246030081040041d510070b07010350082c43c1c0c4e803841c0d02307094120380003503200243d03400e81c1d445921b10241c401c0d80364888408805400401460504021800c50740495006645455501c00d04006a0305d1403807480c03140c2402a8004c2e0780d580d8440c0512000d00c001c0714180c8200313920908041080c4540c0c1d554110960f544416007443d10b040c00039002c0c030064030705013003c041c2852040102c40c0202e4401000000f500b142402102c94002c0042c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 525823174 1250 525821924 525821927
    0xb03010b01181502120a0306150c050a030e030a020a03060507090f03080301062102040803040e010e090d031104030c2d0e01120f121205071704120c0b0a020316 70
    0x1407616480018101e007040070016210f424030195000541401900e600c0c00c640c112000d800d5010030703c2840401d5a0b00d0042c4a0200440085d407045411810042203090030303910344607500c10300640000d040001405000007152400d02c003507013500d82c0c00780c600d0b40000d8691915002403d8100e42d2400000d00b4260002409a01e0007954011650011811031660b4244507045400c030400b04e6480c1043c81c4149040311595140303100400080c0000070240da10341d401c0881d0b00c1c03252001a0b00c481c0710540c0703000604c091442d0201c1c08030190303040c604000030b080503aa4420b5900d030040b0340c0040c020812280001030b541903202051039060f00c110a4401c40030f40e21450f05e1070044d0030350251708440c000500050103071080001c810684a0b006200124414516588640100001c41380a80005890800034840380441d401116000502c60414035001014189020740041d0000c0002d001c0403011f0981040d8503001e403000e2107201e034006a500144d4942a40b004000e94000d803221050b080550ba49a801a0f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 525824424 1250 525823174 525823187
    0x3110c0d020f0c010503150d0c0b090a05040c121a0414040b0603060708010e07020304090e1c0816180302120d090801050105010504030609052b090b092d060307030b03010b01 76
    0x3104145c580e141541c076418650314013000e600c03d03000d8201c04075622500110b08030140c50390081c507010108139a03a111700814412500103660020f030007030341048000e0003915000030341c404044e0a22003000814000d9031145010b002c1d10740200580152501e900d85005900446103544074900a529040040d03c900007130660b1240102c80b01d5001032601c500600408404410f1107402c00114412681042c3e01c508010003181c604038400d41980c0c4c400400f203003c01d6039071542400e00500909105110749081d00d5090440b5519a019004002000b0b00070802004031070743c200701039034000c0c04e201e0b618890012501d540307040115040c000b0884204000542d06414010241a90740603521203082038590384c2c0e44005400c103110100c07154040c4048650144014006e08101c0c00340c80402c146038000180c102130080441604010f14490040000c3c190039228840405c002c5a104080022175410f040042d04051003107000d540d0380880008180b280103541a041141001401c0780200f00000f40a0300642c2e86 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 525825674 1250 525824424 525824443
    0x3090306222315060910031e0602190e15040609030609060906050f0106110303160c020102070801020a0e0a21020420030c1b0303070e090703110c0d020f 67
    0xc00e9160491000900500c00d9480140c5103020341214011159958906003c02d5801d64030740c0e482000c0c20060507140c40194107410080c9001c80c1700c07809095031540048500380311881881c240e04050034070308004032981110b468646044c002c01042900c40d6009100c103e048075403a100da07010450b60031150b0070310700c100c2e01294460b03207980b5a00c0c0e1550341c8010241c5401c21054800c150750300c8918001c0340c8a401158455800f060140d884ad40c18414040c000b4880b0804070710303090307000340100040f80d1074895002136030b0700d450300b0180c2039606a480100c0c64042e160704048469400410b034130550396004001560668011138030b007400c10381c5956412025201c40962620404c1d400100d84015051580c00000302002d1580c0c5600c440e00300040540e5654001e03191201103501c001160610780c6807c40c65a0200c00c1c810700614174500300288000e2182540805241c420450000803400f200d011b46e1000e411000c06022560702c5202c051180e5460710602014803015005081e15002c4011010545100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 525826924 1250 525825674 525825721
    0xa02211c020a02090a06050405070c02100309050c0d08211e190f0e030a020f010e2113050a060201091a1012260304031106060907080603010605040e03090306 69
    0x80040702d980800800c6900545011025555088046519106c0b402407500c10001512486004519841404404c6860360503280426241034070800000d03001240c1038140300000ca80306c180444440c01c00300943e218091000c51680b001202407031302d0700d820801e8148108800c0c078500071351210f4060103591300c15041b2203110f8172101710f138501442d540c0c86038440c124012900c4400150400449421171465000c1a4030750301680c410454007841e84824040c0210341c0f1065009011180c0d141c26186020700032540c1400403030301c00404c032000c0000200ca42c000052100400303498400b5078840c4080d0081c2040342d0f00b6203000c032030a070303940501c520b844030072030f004541d0750f40030615407841d08001d20005842100106c07400ca9421801407002c0000d024008c9030040f0754101d142e075a042a283c0606600c50503444c022468000c1800c201540d135500c00b0665010304641420b181d6560741030002801421560002d5074001d00d0011044c11510000002e02806078080d41100c1c1103884a1800e0040707103076407400c01503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 525828174 1250 525826924 525826933
    0x103021207120f0618051515070f061103070f02070b090f0f10032c0307061d0a03020706180506040b0a0504030b040f0627140a02211c02 60
    0x10740c500d200300464001074407003001c006049200c52424005450065000c00307901c0302da4000400c400310641c071a4940000d0a0304c024884240d026000c03401e022000841405181c1d004140202800040386585100729844441001625004490708429400680e5040c0010701c480c0a01c1c550540002400c40907625520b07086414a1004400c00148400018056801c007000e03070000304840e192502100c0b0603e81c0f948020031404035504d4004024803501000c2ca50304103210102481d40000802141d244941190340440e604400c4218881070782c80040b02c2011910524000406056000c0b440c501524099501d203c0361441020b0080000fa51a004031507020000b0002002094120340090500341d6090034a50301f800c3c0c0c0c030341313440e60829030459040e1100345050303240004000740e0340301b0402002c4044600341340040c2d90501c41c00d842c1092a900402094441d0b003445640c840400884400c140c2c0200b440b80c00010305003100b4049418050103d8031441104071045080440c0451140d400c00d20303074000d2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 525829424 1250 525828174 525828181
    0x1802070f020910270c09030b010b131206090302060a140f090f191115070609080417010204080d0c02030d05090d080414030601140a1a1b0d020c01030212 67
    0x46207a42c00a0700c06000030403400740c0040d0200b070380300d01c1c6218541c1c018800895441000ca004050313800c1c02412208128540905000064000d0039003810340c0c28201030a501d0701c122102c8178400e8401a00404580c508a0103030b50100702003900403840262280e400d4500d0b94444001c2032003130741c9408406041030300440c00011040c10a184038076a126400030121218039000702c00c1e0b01e0408600c08550300d100f10b00b15450500388040b03100d02070b1030a00b045c1c41a803c034030381034040b11581d4011040001c2509072101130f03500501c510482035074050120941404010055814842e000398050700c203020f00d85c0900d00d2402c603194011400c09d1600740e0050041c00540317096200854156004010056101d41000d030840046030b00c110140002d00341c4284045081c624003c10580303800c00503409220042c0042c2040c10031612184c40360000c60b05076202c50342c080300010b04141341a002e02c0706100f4030407820030b6900140a50004044220525507001e58102942d604011000c0c0d1203000c100b920000c4500000c0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 525830674 1250 525829424 525829429
    0x8010c030b0301020c030f09030a020d0515090c010c030f020f1f0b030604020609061b03120718030309060c03050d0509030319020313031d031002040906060306030f02062802071802070f02 82
    0x8c01c0442d5004095488a9001d030f4000340c2e035823580c00c40030388040c1c0c0280e211000041e5042c0c840c41e0000d0a69000309a882d4040000078414a00308200600700f007102c000c0c0481550003082000c0702e16030390310103403048045881c10070304000303000e0300d010300509080440503026403d0200300070340a50307009000d07030b0325041040c07050100d50360203030a46000c1c455030350403560150a03092018054a0710b6190590a0764203004400409400d03856001303c0c0590a2104100006a0400c0d0302c01d00b2124507081101c000c483c4ca04059a840c040c20b80802401d0741003c0c01c01c400c160000c801540324044030744032582030000b075102010403030008840e03002c01c4010a140140200c0d0044074909241e04000c0c0b4402c440040400200e814500300d480700b40e03170302034000c2401c1c0300441160091401814881ca4104044c03032a6864204058034403610103409003600140711030b010190382c02416410900161500000400c1510003075a60b83c043c820b0103908880001d40c02d00026060080b214410b400c1038080514149036001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 525831924 1250 525830674 525830677
    0x20301140904140a050616030c0e010819021b1c1b0f06090b010311061303080a021c02030a0e06120412051c0504020a1a0f03060d08030108010c030b0301020c030f 71
    0x8107903000c00c0f0405035012011001c2143c1600d85219001a2216003000455012a64480e128400a140c00c041404003a1540f00c04a104103640900c0c0801003515180001d0701c0d003c01500c1d001c1e0103076000181c0311010800061441401600031001c0f01d01e04016801c0c8000e401c500e08001744000382c0d4520500f580b000c00000380503120f5000c1c0b4070880200b030039035583c582200c920304800c0380d08e40c044400400601c10882111a80756200380d0380f10749400b91a241c0c10744004680e0100a21881021682d2180da602c00c000c51000d031054508140c14884030b240001c0c0d0b880d0018440180000d81000050b68917051542c25100c010505402d800030b00d44440d07844018403a031035442030042113030034001650803050142d0706800b038507030301a000141402c0030b0040c41089a425000030040b08003000c04044c00d0342888040703c03030219242c00d5142c1c4a072202e100003001060a0031000e41451000b100101d05954103520038031415450780c03070401950020501381803d0740a4408200000d4200380602d10342001d60741c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 525833174 1250 525831924 525831931
    0x30b01020c040c080a0b010503070c0305130e07020f0712080403030e032113090b01080105010f12020d051f08031e0706050903040e0a0209031b011205090606010207090203011409 78
    0x151075510712603601080460300c0364008080051008001d02c49a122148140211240d0078a403c914500e800707040500200403030303031004080100c0002c228803a442041e44440281c20240d16581080c244008000e5985600010f007680601404000042c42400c4407600003d0302d9001503580c0c1003e10715102900c2c0711441e454110340500411240d04520f00001403141c0a0110740c218039503c44040e154139560741d200e25085024003510b01100000103a800ca00f07490304550007482c005800c034040c944200e0b0824040c090249425002040d0688a0009a00001d101c0d072101d59900700c10079040301d01110804041d20550310391b0b37042000782d40d214561281c5440303000c0030f1b8480004d144c241c0f26541d85089800803500340d0780c3c80d00301240511007052900035132a00009001c03070075414540e1800001c0e8850000e448980c642822084d0310402e280d020313480741035008101c02801c10203880d1030840c41d9200c5c0d10840307025005024406000c60754640501c01c0e84e0681c0c2c020000070304001951801d200c2c1152015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 525834424 1250 525833174 525833177
    0xa1b020105060a15210c0f030b090c03040c0e090717240705041d0103020a17030a03020a110a051b0a080717030f0c0d17074d10020316030b01 62
    0x4100518003810407005112148620400000c5006c130f110740061603c900122014109400e02042c2c40c2c3e20f6855034a031542014509071815521303241e40c030b0240035941c4030354031454440a0050410038030704800700701c1c1400c4402508185000001a010b1315460703104480e203a648150a2811155a00c2d500c41c400760351140710342c18200d00c0c1c01d49603140c420803a0740708913058040c400684010300c11420026100c00c02064511a0422113101003448151613005072401c0f8410154086002c031115842000d240d40107448103025600011654205a0b440c1c4200c000307884a1524608409241800c117411010125040c10340903118560501389012880403100340c40f2030281c4801d0042810450341c0c840180740304411100103100140500c1d42c00340240d200d8401c50b6120045883c00c11030b0451b008007203030250070215110340181140e102d201c0c500f54a9080f652244030094082c1c1030421600360208040140610400c036420005200076910580c03108603010444001c00c46210134150340241c00080b00c10905 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 525835674 1250 525834424 525834437
    0x30c05032a0403230f0a1203020706020f1e0c03041208041715010801110304030e0409080313060e0118030c05120d050406150602031611030102030a1b020105060a15 72
    0x481e240120940294100340d0310415000390944001048030000c3d002c075040701028044905000d68001c0d102e03c0d41200c041c0c003000302403520384425842a4104d85446503c00340464903001c07040f00d940c400f034100f805a2042c213a42c80200b001640450010fa9400600381c00c0114505424180720741d0026428100c21101c01c3c0c0280400700728500403216024160b051103008003003010030b210090f203141d401a40203c1034bd901d0102507400f90059007007140d91003901802d2a4201143d0a000305000b4400e6541c0075014039404001d015500708850102015140207100a12501c02550b40715400c071460180c0301140d40c8806607180c00060b000e5a038003a82540250f080d5296501d40c0d82490400303a00c054500c840f00c07640d0303500300030802c000c5200b4a48080174164a0050050400c4c00195032407040411105a6010040d0800104200b1010301055203602034025500e9003806444c0340d0180030704090179078a101d003054070b040240d80305108841c801d200c01044900d00c13130b24100450050081c850604c0e810441c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 525836924 1250 525835674 525835741
    0x1a090303091302030402150307080403030b1908010b041109310504050105060901060c0b01050411040f08030301030309080a0c0b0a050c0105040b1b04050607080c0705030a03050316030c0503 83
    0x84402d904a1948841c50001d60b885c40c083c81002140c2c1801c1c00d0348001100240300340201d0b507901482580c1c0c0690315007000102d00035880d00187c005074407905290410180e412020512200c10b400154030060241c5003806004c0404e5240c070840c0c011607249580203a40c0100b202400d20070344000c0e1207032001c1c01e001d03400d18401c0201c240b03054602c11281a83c95a445006208290501d0a4414018089c900d0840505a61a9600c0e13003134100610a4521503a200c0840300203042461007124000c01081010500444c1c0c3c0300d0105450750024401034020401040740042c1c07855004c070340300000a620820030314105040c0030048105401410364001004000d02c8400c0110009102e0f5038022401078543c1c2c1100c1c500000140b40551005a2600300c0850505c4100a80d40701e403000d507213405511120050326108a460b0b414900b1203154001503140c422514014107058004000b540107000c00c19104d95446040c2c0402e8064402071046000004c1c42040052600792840c11081881d0b100c2c0360346c0144045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 525838174 1250 525836924 525836929
    0x302090f100c1e1a0f181006080c100201201810032c0a03080a0e0d050c010c020120070c0f0801020d05180d0f030f09140c03071a09030309 61
    0x706410880c01c1403058800c81030148696940d031388030300141000d005500c0d460003140e400740744140604140e1142e50b170720b80078042c1785200740403080e5046600e80c400c01c00f056440140301c0da0390030ba1506090003507401c1c8001c891810310602a400e250a142c6207005281d518294507519281e100c450706409140c85515043c09942e10b412880030000c2255901055684d0040110302002c000c2c0000a201c6400d02e0000e000349800c0071036a4030100b0380500f000041c81c0e0f6130703850240c040c1c2640a0b504046001300c800a008080e0440040d040301c20040e00204810140d000c01a8201c0c0c9195004480f07d04140800b10351894188005003100c501c00d42000301020b5a9070a000d881d902c0941100b201650080b9911101f60454465154005040c00116550318039203d209503c0e211940f00341401c01c0340001441c500940030750068604007940160030072000180d0b0810307492060f03101030300198a00075080403c01c280b4000407442d09444450368541c89000010b60100e1096100c9000d0b1750b003600041c010381c001503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 525839424 1250 525838174 525838193
    0x7030e0102040e071b0b06120c100305070206010b070b160302070b010b2104020603070311131508090d020c0609030106050a0f0905060307180213031b150302090f100c 73
    0x5040e038004200d49401d0040300681700c8102d0305006500c0781c40c405000008140c03002840c80c0c1140003910035020300c0e0011519141000c5201007603035000102c440c1c003014007a034198400c6201d0896903080d03640ba41d1302c811703e00441d1301c513800016081448502c0401e882c440e08045807480400c250070300500d40403081c0e4520130510002d0f40540519200800c01d07100c0e10010483c007125040c3c640b4100070030340c9495030014030f803404041d18880c20141d0701c440003019845138004036054003d280d03c0c40740f09030ba07640704000c180307141c009580c0c000502c0c2c100101d0304443e400201c100791440c00390060048401c0300010b001541d040328510179490341d01c3d420001541d45426209030050b0042030304ac9983c4070705002908040c0ea2000e03203160300982c00444100910240d03198521303214190040d000d039039007407100800d00b92003000d5000501020000114011a04490603607081200c02074030b0340380080018584160124050000f0598104452020703031b2001e46020341a6580c03044036410104141d1b1002d86844420 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 525840674 1250 525839424 525839429
    0x11d0d060b0f10140703050f0706090204110a020c0108071206080c030c03390901140102060a06060f03050a15031a0603061b07061b030609140402010207060807030e010204 75
    0x1190741d1880807280604029040441041043c1c1c1d00d85040301c00c800008000b8104051a1112041c2c042184400c16114000301c40c0c00340040030342d007600c480090900ac0c0041a800710200e200d2413404010070114208901aa55a59101d4016007050030440340103551007600106640c0030800b0141c00e6440394009440383c080680502d2000b80182075905040c5450210400103080c86540703c42c48518003c0744c440c103100011301ca09001082950f22610f958800516140151980401c401c00082040d90394007003401c80b0004260b0843e05d241e03c1d898507c00480c0c81c80d000f02d400003400c41c10103052140c029000590400007400d40003401c2000c080105030f03c0c6080d500300715001c02d402e45003003108620001324150070a104401801260600345c00096007048810700c0e50000040200703261040c0244c0e50702080200e44451141002e0f10822413005008049502032210014906904583d1109016041501c00c0c0d80c10380003002c0d0141410410b82d071170000101600100343c0c0301c4029110701c500c280080c000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 525841924 1250 525840674 525840683
    0x8060d11180a0911060f04121a1618050a06050703120606050a0f090521030c1b12010209030a0807020a18050a05060d020114180d05031b0a03020705011d0d 68
    0x240b58103245130091480d40d0380181036220316414403001c2e000015110803181100d402d00c1d9a4030130030703003d071900d8002c50028103c01800d41d41d001041050784100c0010102c0c40303000035550301c004034840c446100c1402e603442c0034450f0028103104083c044c01d0300440c0286005806400c00c107c0280b001c020781c500b40c500030b03080b400c0020b10104a2444494100c85010456440ea040c4105120b0170080880d4403101c000f1074041da40030301000c0080801e8000d0040740d0003240f12800b07a4214400f10603580094a0203a42010701680000ca40540c0494061082c0c501d8814014042d00707521185448409030390308506d00a0b6440400c03e40001507004d8000d440c080f20a514503030208007072822014810803503d000b000c0e20b0080341001c1c0400c00507a404408071103542d0003100040c2d02d0720f84800100f0a41c0c2881c42415411505000d8113005000b030000181001c91000d240d0342c0141d0b01700148250700c51500a1000300560710140d02440b20b50b024205400c0e00e5400000a80485200c440c000b51344841101030a44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 525843174 1250 525841924 525841931
    0x323040503180d050c130204030501020c0105060102100b150d110301080c0901060804030e090a06230a0f06090e19090b07170c180d0c0e010f0608060d11180a 69
    0x2122038003018000b07a8070048400c8450f030300b40d5482d59500d480a964109214910784075401a0031a52507043d81e000d982c101c1c000b19140d64040350410300030b210a03903505025120f6941c0500c4160701c20f00a81180d0302e4094800203000e8805038544103e030b0000000c1d100c00301e03200e1203128840403283c80654000c0000b60b00408410001005001484106800800400c03460804110100b90001a60002401c096034000819a11080e15600030452a04800c10510300c00c4104003205a1903101c0341c034244401c4400100f010760751607486c500d012181c840c1030041078131003104100012107030005540c01700b4520202c4070314990740950303c0115880b02c901200c48850010500c5a02a40060000304100d980104400642041a0100c0241c02100d484000000c201400d02d40640c60302e110500b641640144003114079031b00c1c2c03568a82811004d00030360201c0c10384c0040c00640140700745001c40c007c90010380040003925043e101c120302400c1c03211509400000e5500d140070031010750226140310f100c0381034000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 525844424 1250 525843174 525843187
    0x150403030314061804060f050c090a09020a0918180b0a0c08011a130e040804170c0604030618141606050c0601060e120a03080121050c010323040503 65
    0xa400c0328280c1906184650301c0d24100400b03526007003913043d8507088441c2c0d48095030751145420b2015003800700064214900b0141403110110205001c1d110540046a1800c40d072500c460000d4104d0040040c440002041c2010400000750341c10780601d048071203100c0c0400c0c4141c004100454000301010229901804241000081c10329441400031440092070460110352400c201c00900c0662905415040ca60000344245011003004000c1c0040c0120309030048a0310f46414044c81d00d802c6072181d00c40b01501c01e0404083c4820104006039058401481c01c7d00309803e40e21440000d01c50714088117020031448a460005c03610301e28101c2c0a4810b00e00c020246000c0000511070a00083c1e8041f2043c00400e2007101d0844001054036410b58000d443d06036080c6d920400081d00a440400c00c01001780903004c003140900d9445000d4a041e1920300401c89031602680f4080100060004c0c4080c2880e0003c088010080d0302c80e4000711001c0001e24417034109a100891038a04024099504880c3c507440002d42 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 525845674 1250 525844424 525844427
    0xe2e020f0a09090c3501080a050105060d03050409150b07050f070503010b0901030f0204060302060f040311060a080a051008100501083a170115020f1c12060515040303 73
    0x1901c0203080030500c1032080c003000c4c501c0904807040c8005140120000121000503a0040707400c2d1491400c8094007104503541d4411980b9200c20302c151042d2030650030200000c41608003422211803040e4190303207051a052418141078010450702c8650300c224801d121000450a2507040a484014080d40103402100d8490340c1c840c0c074000701d0740e01841c040c0e41884072001072035681403e01070459030010300741c0064880c148005401868a40c0009500640108803e0071040c410f4024106a074410b03400312248014442c104101c901500c084c0d800084c03540c00c002003074404550002034110101e40c40c10f0513680d494020705030824240320101e01410f81d9440042045000c00c0107007801c007610240c0c2508085907880c040c400700741d4160907804064070780300300c10601e0f0ad48666003045449017003c0c4110305550311541802d40c1203200003900c1e801445481c001c1010305201081c0800110f8810700c450b601e501a25106564002c6407544005800f070f942d59001402d40c90f042606240e11b0702216003555180c0c107500e030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 525846924 1250 525845674 525845687
    0x1109010f030b03031602270901060506070f02060d060b03071110020c030a0f09050a090c0f11071a0417010507020d021606050f091818010e2e020f0a 65
    0x840c5040506112000c81030751004404c661000d0100c0004107030000c95400441c03404204048207070700b03030f440301a103001502030807010340c078052403161b0300910505139114200011801042c40180c0141441d124860040c0741840040c2060400c025010030340669490b41940941c00445075480410480c3c4100400c3c00014400b6041c11400c2c0d040440c1007801612506669024111003a01409071000550006c0350203030043d80010003004004441c065118861039000d0405100100d01040c4420f2400c40d040d80030b00742c0010184024001450080d240c52150381c41e00c5022204100c10407010440420300100c113017090f4803190f40040010407142044400240b60520140340e1008640003003003100d201c80440188582110800d240007501d8001030240e8024030320400c480d0301d91010081c05640c549924495000c0d00c0742c40e030071034911004082c078019542030b12032030300461000d41c015000d9560544120f41d08035070001d030070f107810007410201d0300c1d084401c83c1d02101135001c0300c800c0850000c00c003603488103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 525848174 1250 525846924 525846947
    0x51006030e030d150806090a2906040b04090203010e0706080606040b0315040f0207060c030b1905040c051201030b060f040c02030a030504170711041d10020904060306110901 76
    0x40e00300000300d504241181c80740601c0c040004691385501180741420208000c05018040304800d558060800e01c0a5a0340d40c158000704968400d01d8402008184024140c03407020425601c0051205598240c10040180074441d101c1d80d01a603144045e10258900340b2807400512101c42c002d10b00c0d5410254040d100c068010143c622908040100b404114800c50603250001c1d45082c0318146003d545002401038000c6140308040ca0744080740350342c20710103076400c00f41014005407820040c00d2450002c0c80780701900c0111058070796510203020015420242c2c441040d0744075501d044e9041c031094006000541200f171f441a1110382902c400d200180c036000d03000e00d160750f40c2142e08000a520b15040603460780070307161101f018155204006002d100041e901908001034400b0055514032452070400b001d48074503a60345014a1800750303511020345a0803000c034807803030100d40141f041040c221107120295201c0c014280d009510341c28000000348080c012035405110038279100c0c0d1a900b0410004207144d12a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 525849424 1250 525848174 525848177
    0x190e070b03011e0302030a0b06030a080c01050a14010609031103010b0414040303060602011407030b030c040c030e1006030209061e150403030f081b0702040603050601060903030908030c03030109020c150a051006 92
    0x81c3e5042005940001e14000c55a504c80e0b120422075a5138400207091800c0c00e8005031030403500260801d1202e1066208034460102c0c05400c1240075640d20366a0060042400b4400c0483c011b41414008544220b11075506a04000c0002c0350103040e14010074103450300c00481090300d2083d03800f400200f40d00b40c00340c10060140380c0700030040000313280c80340561800082c1004007850303500c0c07208000d503450620481020b5140a8418003e0251850700200285040303281040030f07006946080ca0100c0d82c1d4003480b0203c07a00103003010880d80302d49040080c200c8280261003400e52802070b040f1255150301c200012020541401e50f5102c9103181009045030a40406100811800038100003445444440411500c0a0325400e641c0b203403043e01c042801045250006460381c4192800060100d5004524038152031281c0e440308922942d5075029079603406480c01c3e07107e81d0781091006002a6030964040d0481c0600241114540003020b81c00501001091300c04000081c2c0302e02c02c000060044000714001011203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 525850674 1250 525849424 525849479
    0xe2109010207150c140a050d0801051009080a170d060603061d10030803090c040f050702070b0406020601050139110307080a08131d0109061409190e070b0301 69
    0x702c03000105071302d600c103000928080e130748104440e1681c4100039005100307074417100b219002008a50041c080c441d00740700303151051890070640310307000f13100d06401c03c101d5805100515801c0380c079564501d91408686079900410350b06124800300703c1483d010f550006c1015481c00110b02e810324004402d600d03001441e1082c000001400c0c0101035882d03e07108002c90350030041140d01e0f92112840b00d0b043c81048039400798094113080a03020300504551003e40034600e207408440300159500d041444d54001c900c92400940c000400403c52035001d0040c018205284c56000f00c03c02651303c1c07580030030314003280c507107041d410403030481604220f401e200c4a0b910300c4044000b4442d41c0d28086000f682c9003130403500140104400b00740401c94841e0038072820050151554020040c8800440e11400c1c0c8a09120ba16030907070602500103403450701803060702c80070380003c0e1507460360341d640c003080101c555036886409210640c0c4802e61042407105205100107003200300070f240d69075490b00c1c00444529a440500800d82140c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 525851924 1250 525850674 525850709
    0x50105040b01120b06130902091f050d270302010209010905120c042c060f220b040c0b0a050c0c040e071208070b01090c111f0e2109010207 61
    0x80061103d203200e031000101242001c1003c012a09034015480141c0b01010111004103a40d80aa00500a086c9003a500f00444c803041d0424070300080317001c0d0750b04004a48200000c0b0405401e81d00540307003100c0d41c0501d0740e1014405c044002e081c054912400d5005035808101c00c8040c0d0b900240e8200102001c490340b401c0216090030f51074450030510501d512403030352420540500d050901c1d0403405242c50900c44503030b06040c4210213845141c110b8680600700c2c0c0781e8001481500e40011100040111404020340c1c0110b180c1e6030b05002c41d0050400d80340d2030201040041c00c80c03d02d000070281201207544064680411168441c43e00804000301c91050742481c43c00402004006120b804403405000c003050000d0041c00c101c10b852107500d00140164840030004111090a40c200c1c012003102a56072a0b1540452442180c42e00e000700c01e102d100e0140015154205c01003a082042500400f0095034001c00c2d0a4600407101c141081015100714004501c95803a5030b0144410780081031400c80701000d403072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 525853174 1250 525851924 525851927
    0x1612050c0c0f03252606180d0503060d0203011a01090b120606090a09050901020711060310030215250204110c0709020f16060e16082a0d030c0303050105040b01 70
    0x402040500d13401d098600c07600c100c280d0a84850000600c0b00161003681d81d0341d0001c0c000050103040d00014044e10a00d400300c1e401282c0c581d09409100c0e031483c00f40001c00501c0030120340c5540080c004503481005040f024025a03800c1c80380764100c0124130300a40b10000d4500001d072001e80381d54099401390b2000c1c400c202c01070740c01c46201035120760201c5216954503e5480090b80c00003c542120541c2e514007030811040350300560013403150740c1c014000f1558040302030042040d0303844200d40c400184521007074104014144001c05401580b8072244460a0400010296440314110f208a0481d120042c8a810075402c1900c02e00030325002c980c905514042241c0c101d0703a60b507481846480c0403198001000c00604410105a039000c540045101c02004003906090001d008a101c1903001801810307255901e441252103008101c41e1450302900d103d0050303035111001c012154040324a84102031641070482d54954088024207880f079103031003400409a0400070100c2c0c4051700601c2c0510721380580c0f4502c83c3e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 525854424 1250 525853174 525853183
    0x918050609090d090e1b040609060e04230a020d1107110f0d1b0b16150c0c290405060a060608040206120403021018060b0a0f03081612050c0c0f03 64
    0x203a840c0c01105505d03469000b822030403911924881c440d03c0a0120f00418500d034844092021101340d40e07030b41d804a4048100300800c03180010b0488020f480900c00001c1e540c44089000340e44080b4408006042060010750f0100b13a82c4001421a0880c00025080d42008038245145403108000d64003100c2c080749401c04602803810030329000c0d1104c500d50701d1a04009480c0da5604000e00803110340d071911140524400c8401b003107030f6130b811100c2101c010900c506002080c41f503103000368200c3e51815001ca40586440c0500c80f88a502545006440000711410904125031640514480d00061209103003841ca8082104c4107900036604002003032080c480940c2e03c20041d00c1d0300049103c02c800080d125032901740d00d0000b071500018070640c2804501c44e5400000c0041e02d11407400782c10203025580d100701c02c005400145005200f041035501c14140041241c450241101311410700c0ca400f080303811034681d2400707805a070012900140c40020f42d140da001d428030070385050725410303134004030356100040000342c96 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 525855674 1250 525854424 525854429
    0x170c121306090f0c0e131101030b014821110f07170304050a0b0a0203070c09020405040b0d1101081f080109050712030f0e010918050609090d09 63
    0x4412a044480080c071000390300601c038059010b01c0c401d01c1c440e0a403a0a03003418240d442184403100714500011106444060714000300756210207603610000300407005500070072942c01800d042020310b03440d100c5069a030aa50780c0603803800c03a0b1013403c07503884940d28184022050382102012100320759880c0c0000e03183c00b4000d1020344601120612650006821180300032446180b200c144248400b2503440301010a05205071200d01502403881c0d004812210784d28481d502c6403e400001c8a0b100700000d0300480003810101680d803040c1c9103840304640b074010360300040740c000c0c1c0ba003541c3c001000c2250b441d00b8440c8140005003500c0388582e21956440313811a81c41606101c5040c010340c000010307910380d081040441c0f00c0018031401ea10031621030940c14020040e03034400319110301ca000d50101c0e941144921a940d12039040d9560b07003456900311011258541011401070520a4124000c5000d200c40c99540d1070303029161030009007c0c82d000341000317020303000902031a0254012040746903840358000c51000a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 525856924 1250 525855674 525855691
    0x2060a020a0c020d0606051509033318100506011704061d0a14070510110c0a082b17090726070608060604030b06030f0706170c12 57
    0x312031007440c2042e252850520b400a501001c2e10540b08100f1042d588202d056031000d480440307126821250100c02403003400c4810360708da84040ca0201241014010441d040c0c0e00c22084807000308544012500190000d8920604c0360900340780075006800c0420600740c0700c0364030030410b00032806d1440c00030f0420350700302044a0041d240b00c0d0006080c04030700d0b007040004035030108100c0c1c4800c0c03003802000d884860403841110806490124036a004000050000a50300b000f0080e20390300141140c144d0303140c0c0030720307a1800c1680500511030f4050742d621000d44000307080d0a000340286020102d807a03c50249000e07a04082410151741c40003160350704c02200d42c0180028024460203450300144580307021303d280d204503a41c008040103541002031b400645031240d000ba07011104c12548441c029180d608040320f03410781005007400200003040100d5045130b001000a403d46400010340c43d802428051590400808295003000c06108442803c1000b913012020112050901c034a402c0300f0100504007524104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 525858174 1250 525856924 525856927
    0x8061608060d11030d0c1a06150721050712090e0619080604030e1c05030306270106080108150105130506010212040e01090513030206040b0907091d0607020a0302060a02 74
    0x70708100d00508049200d81000381101c0c1e10040340c2030000c01c0f00d000c128046481520003003654050809500c02140123000080600740d07541d0b01d00080720305541140c40103480c002c01e4251a90903a00c003050045003480055581d6655840c0c0a041015a614408521108000741c401041244140341d4000786c1d00040c00311a008440302100c515030504000ea07070000d000743e004200070700c420103420643c0751002030741c15250380c10070000508500e0b90000101303038040e105400410000342180b03400794040b056828802000c901c40c050707100c6404043c1909810031404111050010b1040142c10802c00000c041502c40030710b20703503044c0b00c04180000e41d0f541460b60310580380c101040d2541c0c0240000b29541e428401300c1602c0d10365824180040180a101d0101000d00e03020104a48000a1104608044d0150001c0c032650301c0316915244941d6000780103003514084c030540810805410701410303118070030041a81ca625a4801889030504501400c500d05540c084a074940020340c000c28480c1d44045c0300440103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 525859424 1250 525858174 525858199
    0x813050f0108101809060203150109050a0e220503120702060a0b0a030f140303100312030501030f0b04060615020703020916020717160e3111120102040f0806160806 72
    0x104085c1006000050405001000304400340408500d075552039a02607a910f05119962414080c80b0a50b0f40580c2c461400031b200012102034100b00074028003101d202e5803c2d25030b45180c03546402e5804c00308119007264016000e02510079410440203402a003040000c01c85907810f0f000144105103035100051030024407440030070610040071814280040c030ba000b40c176601e251584292941c81840c0c002203500c0c5010080f5058114424481c45043ea0360204507080d510180340c441c0c3c3e42c00c640c0200708813242522024040740e080c003083d01a00c020409900101243c03401e600c1044400c01c00284840c40a203154a0480446940007520004030323180b2018a10074108603054503400c0509582c408462004e4100e00000d00d40e40d03602c07499104840c0d01e000c0700c0380340c1c00310f0030001007441c03541000f4001043c4040c80b600c0411041c100c400c1900c0001001040340d95250804682a0781045c0d024220310924008204090b003414801564400110b10b01502582810b83d0064003445001d00070600480c5048000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 525860674 1250 525859424 525859469
    0x80a1506050a030f0314030f0c070f06020a05431403030f09010c0e030309040f09210906020606100c020d150c020c030109120c0804030813050f010810 66
    0xc4024090103001580000e4880c1480b0703200300b05035801140060007a01e40d503034084c0300800590703004960543c1e00803c641c44109500c0c07801e401040301564400c0e01540c41c58002a810320080082c0c80154031000e8442d842c0b4030301c0c00400e00e4140e1104022010318401c182c0e94006c0681590784080c144214440c0c2609107041003004e80407200700c1c9030150300c8000240034001c0f004042c0203205074080402070148030075860044bd9801c4800f2142d44d0140e0041c09501440e2505130808016608400c0c00050003040306d482d4883c1002e40840071165801d00381201120342640030301b044000d402d0ba40014010307410301901180c4d070031000710f40392800c10454002010440d0380f058010031441d900945028603803007a07808203800a003d00c5100d1000b5102d48041c1c111142010302401100c00d0300400100c07481c0f405c0d004290303082c0c840001e0844001d1010070012002541d03070400b0308000440c813103843c503070349041c60140180c075920180307090b051101c03040800411801c09420300065420303010260351030040c2202c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 525861924 1250 525860674 525860681
    0xc05010c05030d0e0a0c05120d0f0210050c0a0e0d0c03060902060f21090f060f09030417060601021b09041202030c0714030c010504080303010905041b0b030a0509010204080a15 77
    0x80d6900c4142c180340f607420340c2c55000a140c001e030303d02a802c9215051f584600f0040c0841d0390011102c140d42101900741c1c0f1140c0155601c0c0120310f01401608d00d069481e4004500320303081140e0f52100c002c03000c5486660b880e070009071889900000c3d00c000b065607400380c9590005891a02c0014009500c07070721420215107070303682038a206084005e1a44c3d1107040401d08484020410450088022a0b042c0000c0c43c500000812001218018000d80881c0d103c0010790082c4a0004050201030320041200080c2c1e0740000c03481e4012502c81001521641c10818002424202e0b40300141a14651024000380c450380c44516882c2c21071351141003101c510009400c16030a41c02032000045850180361000140d04ca02d030100d4001c02e550841c29500c1c0208454015160f600403406649400d500c14001448a0f8000e58041a04030f80076a102c40d01c80540200c5036400e041c1c1540040b41145000b10501c84072401c40d00505070009040f400a508150420884942c2c1b89503e100282400c00840121450041c2039031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 525863174 1250 525861924 525861937
    0x1406130c09120303050a0f0501120201081302060c030c01050a0c0f0f0207180c08130b0106080c04030209010b04051915050d020c0f0604120f08010e091c030c0311070c05010c0503 78
    0x40c00e00740c0440c1c10f810054000c1200302c407056881402d00e084210301c4030709032003103a06917071001c1c40c400d407804202c0d0011203680700d00030007081c00e9820003411000580d0340c0d0000f404100f441d4000a5640710b20440e020703803d5a030080c0c28841081d08089201c1c0c2803c0d08044070354094440d5261482041018071400c070310b06112035103d011984200010b0304201903113a0440c03a0405101d80740c04050303480e402541c96804c210502e0140030314501e44018410316100f12030701504064041040b5080175203e400007090164280d1080d01c007450001001c0040d41002001c0c08024091051003540c075920b41060b07145042c0840a0030010000d002a0000041100c0d41c10b88200503c00000c4640c3c100000384000e6641c0f80076070b07081d5242000d40c0340b403007030301449103010b444680340c01d41c0e0f0014640d291445c41442c48901a083c2c0010b4010100140040d069000000d240460b0a81d00415400c51144000d81242e01c000c2002e80c9040c03003049100e000c104a21440e6040395420301c1e01404100040c00c08904601400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 525864424 1250 525863174 525863189
    0x30804150903050c0f06040c35060a05010501020a032307060e0609070e04120f030e030c060f0702032703010605060c010b090c0301080a060902130c0507061406130c09 73
    0x21078101c06050740316003c2c14207a90342008903405000ca038001d8a40da04402c031001040030074107407400d1121448107030703d4110203c00090075208030a120100019210300915401801d135000310308005a083d000c3c01624018002030010f442e01d240680c0b0000c20301480b1101d40c0515400c0301100b4480241e0b0b05c3d00302c0f0000e039000381c01080f01480019096440d4101a60040c8442c0700302680419502036803250350340120343c801102414841d14180c01d6801140100030401071555a2052001d003100c2880117000344030001c00035108900c0e01e03007418070503c50054504021580305120b60f5504d441c50510809103410703800c03241c41800d450040020301400c401c0d0012034101402203010541404150030900b1000412189000340d541c440120300c1d000d000900c1810010351149a441c0c010503005c0c2c4c0100065030002d007000d0341c10000d03002c001e015244101c240a00042000402c5030911595110390710001440101d003004604152000130980302980c2c40b01074001e6560340c000601c0d00e005410910050016 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 525865674 1250 525864424 525864431
    0x100b03150d11181504020301050d0615090207110901061b1e141f09032a02041104030302060a091713080105180f010c020706030f02130e160c08040303080415 69
    0x5001e041c43c00c014103494140344002c0f08074049079945040e00a882c1a01c0c0b02a2000e5010381d00d54848002810301c03412a015485607019004c14480300f07600041ca00c26000d8121a212951003806111842405034090f00810502018110b803504e020a04000003030340200c60880c6d422204030b00840340c400d500e02c005024001d40d4404074095007011030954031410a612803508255100004038080e203041e100000c00055407800340c0c0c1c000e856054030b454413000c1107241c00e0032100031550204080319148400c042c07000401180400400d54100400c662281481c4c10034031410007107035103201484001598401401c100410100c1501030320100840003009004000e11071030a190520181c20304040041d500240121200038250007014046e00001100c0c5600600541d40381c5401100181000c019503900c940d000c201010704480d0448070f01780a03042c0d007030b68468039060459481d0745002c0700d200510280200016510003051003201524201c07134150400200f41d60703551270580f181e4078401e003940c01418034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 525866924 1250 525865674 525865699
    0x1514090409150e06180c0303030415180302031e0c031603140703031a0301020c25080a0b0106030b101b06060504090b0115050c0309060d0b06070b100b03150d11 70
    0x240d081d0040c45c0071418160a9981d0f00001912040034003841901603108102081c00100300040c451441080310380c00140d0012420b001c00018503028405500503031010a119007024a401003003003c40c002494403038135003514612526101c0c000c4681380e1101007107115128050500070344296422440303032058a99100000d10340078006040c6901c3c0c107a4000d091000d44035450070705100b01c030010103164005185610091440c0011401513415516070451017035000a54501e040040f18007484c46075070303104c14540c10200010300711038005010502c44e038062480d138034005030441c1c0010f1101da17000c500d44409002a0400d44058245a1f020b5a007141c074280d401014031603c144c0d203034140ca07842c4c15282501d0344082d404462901408000b810309420070080e0000d0782c0342400050905c051780c0940400c51140803000120f480c1c00c54402920503486100400071700004800c4280e0152040d0070381390b42142015114414155101081e06015040c0004924103000078020505030b001402444c000f04c00c01e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 525868174 1250 525866924 525866951
    0x3140a050f0c091e011806030b100504030c0308071a1e0c131202040e061914010b0417010b030708031803010c080408031b030a06151409040915 63
    0x14086a480c000c152805001c0b4004060720303002c85082d003000611221401d01141c0320f4000c0e84007050300c410b060003914440c0c40700004c62440720000070105500c001802003c0368092120000d8091411003c0080c2000180001a0318440d840d00f80c035089031180b902c030b0b0300e14600030025807e5a18025603d0148000b0086800b19040e01c1d03101440360010984d1040d1a02c801011460040c2600780311002c540d105c0600000384c1c0c040300100000d00040000c03690300040748619007001000c0d17030640e4201c1b1107a10481155091401015070030900c107019944a0b42c504250106a400b407409084002c090703100f130304480030300300350803200a206d00101510109aa80c01d45150340e83e00000152548050f125031392a038600e4188501210103d150311983d919035107655030301040344e01c01800256204840788003e40d0802c43d090142d44142004400080c07050b041001d40607034100900d80c407004001072112600d501c150042c2c196200d4580580d40480d0060851520b80380d40b200c0e44091444c464170384100d07100c048 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 525869424 1250 525868174 525868181
    0x19080a080a1407082523030f0a08071106040c05040507050c01060b0d0b04020c030f0a05160c050117090705010e0f0904060506090105011b1e0803040506070207120515040303140a 78
    0x4150701119402c041000401c0a814a0200d00300581002904800001b03111000400c5811031103081e02541d2600d0740d1495000301d140c00000210000603603480400560540048415070042e205500812103442c0a5030341c000021a180211802180c4440106004034002d00c00d583e1055585070090280e00d489a812610a4006034800d410403400c000b88407800b0700301031085511401ca00d90245280c5041c40c00c4015250f03001541123010010200607943e414602c80e0703103d6035158412000c3c9030b1010700d040d00050450310000c080e614490032003014402c40c2200068210101e80f402e0810290642261001074580b80c2a01020350304005880200020885c10303078042e92150100720f4080505036220780c01100c25085000e12942c80c001181421404200c01c10010900409620712609a002d80fa540b0380071389401c1075030121855407014040c001e405805101c0b42c005030420403030f1801c03029803549032250b03507007140d04185801c000d642022505042c030070b0300406410603030710040000d581002608e01b0001e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 525870674 1250 525869424 525869437
    0x3140906151c110a0308031e0601110a0f030c0b01171605030c01200f0c0423010e0a060b0d090c06021f0f0204150c061a011d030f010f0b19080a080a140708 68
    0x4003010000044c0e0640c050f0008411200f0802f004000c02e06555850b07868002e1442d00a83c107001c8040b505100149440354154040c02d13020b0103000b0b031114070a0781d06142c8050303e04002c0c5c3c2d441007500203016546002900702c200240910300003e1a03040ca00010b49504002d541445860184444010203e000011070b40d449400030789080010440340174860f0303000c440c6d520303c0400700e076610340040001901c5494010b4109001c0800020600c1d85e482d054030700b544c400749021040c1e0b41c0341c100c21f07401d0210b200d804a00402e03080c0040d11480c25040b8006540104201a141d88140e0310000d0101c02503240d41514081d00055800d01c40207021440302a0070704a6403041164101d05058090b00c6c0c220b542e12580d07081c18010303114030031441c400840900392120040d41032601846600c019024541090090703000003400450f000448006440038007411048201410054000c00c100401821400058540246401038030340354a45098143c02c403103070364542d0508200d03008007045160a104e00300c0c004004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 525871924 1250 525870674 525870721
    0x9040f0c031a0306150910080d2c2809051509010f0e040f1a07030b0f090903090405040309120b160206100504050703140906151c110a030803 62
    0xb00e14588010140d0b40c0700d0849034591a144954642001420880c804035040488450030f848200d171102110b0b890b01c440780b0a140300240c030980c0e00540c03510208604039480c00281240d50b0140c05100301040324402070108a0746c0781161412511401e81d80005120003429409005002e2402c0112030f5211407185502250311a4500c0000010701511a04070b2108480c19041420b015544503119003840c50b04c008026503040c1000c0c020884198220902280314800d191000503101c6900424805c1001c005440c0314051203802041c032400388400001c0d02e0030140e080380c01007010794440c81c1c21940105a94480c0c000c15210148070400c20140c07010240c4104046814000d0760748003620104d940b15801e4402104840360031b01c041c44181006c0d001075600c0358041c1408954800a0b203014540b1410445810b440c1d500010207000c485030700644030f0828000e0480e09030285002500c40c0c0c20f108400d80c000200500c800c07207001d0700c450f180c0c00c20780001940c021943d40d40700e1034050030710303080e00d4000c000000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 525873174 1250 525871924 525871961
    0x513020d021c1506211418010c0215010e04021f0203090102100612060903020106170309030c01031103010b0307090302040c20120a030e030928060903120509040f0c03 73
    0x310741c501d42800401c01c80d1030341c1d50348840c0c50f416075008100c0d5581104454425a450f1841c25410455006d42d05008151040440700c40a90401689084445982901086401ca500c902d4a8540c900d0a040d05403005640841181d81700c510000d10703908014000516840e03e0801c0d43c21005401102520b8820350a8007a501c040d20317001c14080071900c080c0a84511000e039240840040f500e1980541c080c00d105c0d000000d4131640387e1140390416002618814034540c40010720907a2070034148084c99a902c4203007424011080581da11b041680014054100030910220019401304d07c2001a54000c5401601c10040b00000200c02000030a8916404524200806904076040c0001401850341d0840d00b40c030500b405500e0104a024114115507504584000d010074040c0b540e920b150403c8404014019040c140600c030030a0b919510a40e00c00818801107803000c1000c04c000c1c0121060320b000b01c1c07070500d035076080050005009100142060460a10780f012000e2090341560100040035046d60310784 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 525874424 1250 525873174 525873191
    0x1107031e0c0b0403030507110307090612140c150a020111040905041e2a0803030f040311060105060d020306010318050f0c0603190509120a0e0901050d0302070513020d021c 75
    0x80b0498452844000c000a004000e0400407907c4900c03196040200142a10005c6a68000c04419a001504040064514000c0782010004540d0b504460400c081018140f843c030340d940041c000c402c00a400429110000821002440c801c0d403001000200e1151910303182e94035000039100816040b903088462948000030300192001c1d070394034480081e80c8074240401200001c60340c690b1240b00c801071044210400d820208800303405001540c410500807080c140035140c1414011b101c0032029103070100c02e4110400511180d182c0100700e9168100c00d45015940e501c41000480c014003411000080c1244031040c078004000c80800c0c80c048000c000805c0703601803403566040100c180b2003a03d410180011300da020350766408642c0c001c29070050300c1c401503d503011100500c0c404603a0100c0d1510300008c000e049080102d1030402c0038113003d8141501e005584026503038029540d40860701505101c0c06500e0408841c81e11590119100410036081c01d6403514070051042c03c02e29258646003e0450410300366 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 525875674 1250 525874424 525874439
    0xb28031a0619050d110301120b01060f02191707050a0605060a270924061202090f1005130504020405060d0b0f1e07020f100510061107031e0c 62
    0x181c42c030602910500074204038880106594a030300100c030a40c952a1a544003165180d601400340d4000c0604501013028561700d0b14094000103016004041400f18141b491281070340e002402c581c803e1280c4601d10321210036400d01030b28428a150501c1400c0314009000b00412401041e4072420901c10b84c014461a01ca9808200903040240680080e60301240c1464450050307a803800325a9424641c1b00050540d41030701d07080c0b04080408c0c480e5201c900801050380101c80c031403090358002c141d400c811500c207040c50b60011f80000d201500c0401c0043d080008145640c0c1c070210020300500c8000c0040b0100303641617602c2009080c1c2210143d128524042c0044c440b4103050001085095000001c10040d42d10700c000341001480c00b42c1092100d132a42d440411f41c03400c10300c1c0501d010349201c4c0c0040905540164555280090300d40300d60316503e051405010040c0740c00141d100079103015050501400b40303100e07021860305100c0c1c0e0010748000d200052a080400001f0403070700d5414081e11001804540f80d244 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 525876924 1250 525875674 525875677
    0xe0a0c030318091b0c08070c0b030103050f19080903011407020f07150c080708120109060315090c0501031a04020d0c1107031502090f0312030603010b03010b09010b28031a06 76
    0x2000344000b0b90613100700341070380c426001c45030742d1351281d2000e5040802c6510340221008054200d00115a030010041c402d2240811104413050b4404000b45440000070b01c10000d060401e4400a12660340811041c1055500307401942e25020441005c580d1898a60301c001d507603056082440850b4001c6c014046044034040c0f940d4184030540d600d0300d9558140c281c1d1100d42c0b0350b000c9603041d036000109100c0060b0402440d90200c0c02010020b602060003415030415401010201656050700da00d428624030005210401c0c2400311002400d000581803202602c1140c4102c02040c0d0343e170f1052000501040401c0c2684c0f0082600020b03030b0b102046005103584a41d60f800c00382c003000d00500103428141c0303221420b0382c008141c40b26015102c65094030045e03001c039180100c1400384252181d4040204409401d0034841c80103241c2c8110000d0101160340701c003003600d4a1042c010180d1400c8001a000b400c140c1e442984902502c000d900384000c145805002030041030f02d90282e44203520581c04e0070409242000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 525878174 1250 525876924 525876941
    0x306030503030f07050d240503060402090c031302040504050715050c030706020915210a02070803010504090609050303090c180f0f0709092c0601180e0a0c03031809 72
    0x4004601c2c41d00c4180d540d19850000402000411200300400c0030000883d00440128400310850f0030310304c180314020024000083c3e0080d60195128104210242e960002200c0c0c106094419403640c98860009081000300c0b5450082d4016040c08140400c00c08001040800c440e646843c4084600c0c1c034200c103d030241b20321420024694018402c800114a0560082c2000c01006000b46040400500c4107109138009240104c81100c48140030f084050310200704c568401101242146800300940d200c0741c4a01043c040c0c28012a601c0c4030440400030254818100103801c00e0869840e49070803406135564041080ca0b050041e00160084a05020034819490003524040000f0381c0566070030856a81d0904024416070402c1000f450014400c00c552048c1442d08882681d82c0c40c4982041640046014440001c038800394412001089401802c0715546044540c00c2c2d4081205d800f4800120b1404001005c054a6111030a800104058000c00c044610003d00301490352001d50360005981200c00c4034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 525879424 1250 525878174 525878183
    0xd0c02040506040b0934020312091204031b0314160509150405191e05100302030a080f09040507030c030c0c11060a210203100906230402070b091c030603 67
    0x40c02240c039801c40260b400150446c0158080749070044060280100002c540015015030400100c075032071112440040d9900901c104000c03d0384094801c5046414452440f01800b07120b1007140e20304400070070810120041d6008102510407140150f9803540b100703c0a000200308154000c0001980d0400b81c000c5031051440c400c510000003100c0c0d003440094440104140030000051004000c4c803021442649503c3c030011720700d40141201500004d04030b03a4054114aa810707108101000142d50005031200071540c0301ca541038540038021600806400f035601040c1d402410003040000441d41688002c032030840d595410301a090301c3c0d03103045d10850798001c8058101c41d940c41500440b03061080043c100e40301503180040410000b2a4401c599030401c80c04098406e0700001030001d4000b0030720501001e0705200c442000ba40c0c0c41c040140084003040d8441403200342120f026507101c1d680303942c181c0b0300054016170704007410701e40710300c155494500c08256000106506048404842d00c81e100e5a0103680e8070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 525880674 1250 525879424 525879439
    0x6020903070938090a1d193503040606060e03070b0c12120105010807091d06120a03020a030305130305040e15030a03020a0c150e1e030d0c02040506040b 67
    0x1007202c08a40a410f07101690003600040100c0b0340c0310388803150540e219244c911000034039040c480c1080398460400840c1500300b54400d0007039107840084210303121030b4181d001d651044002c010782260710421905156412004095a94010240d03118030000c52046102c0d40003007210603221102980c00700612a23500e50140e000c20170a01030150044000c00554410b03000f1249480700c0c10064401307035072140440c140f0380100d040041185503089244c15400c21030f03505001307142ca8140f000f25446039284015103144403820101040c40d03a01c0f0359025102081c03541d41a0345151616080c040d549a84900040740020724040008104d84444500c240d10b5950603a505403409140402090550070040d0207517906550031008040203941c00c00600c00090310a070050007980320740f8180302c2000c2074281e0100442d40300031525801155404428990051300c00c9503a24580203000440100400704016856014172411002115450f00030b10000c01070341c0300b25020301407940d81c1d4090200351859545490b420606 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 525881924 1250 525880674 525880721
    0xc03050702040f020412050a0606090c12090c090c05090f22050604110408060f06041a12100e030d0605040b0d02131112062103031b090d060209030709 66
    0x14160030000016100c00070141c1006e07250f0706c4542038420b454004980b2035000c90780c11801c005003405040028640389800300705080132072001800d012040300f20500455038416400d4100118900941c3c00b6060400f0b0401880158400142581d071000000da40b04401c40006c1c0803c91800030186000b4071544444000f41101c000f0329031003e807001400082d80140c0340e1103143c96640744500580300600c048001041281055296140c044001400d100d0240e801c203a021b0100c002c0301000c2c0700520005680d40012010f085521600f022622189102002d041081d41e03105075900201030071030b0038200101000260307920400c010807039000c2e8403501d800c600400600c4e005841d1a481091291072440070200300b603010010300c1040d40d4000e00603022001d40f00310900006040402c3c045040c1c0c0c03403c90a1240d041e00246950f40d517800005c000e06101e4600c9000d000103103402c00c06403000441c0c05040c0600c81800c40c540f0201039041120414041d00c28481c002401700e110340540126054a89990410443c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 525883174 1250 525881924 525881929
    0x10140a032403081e0c120301031203020c1e0a0606081c031b03020a05070c0806041401140103020603060406030f15051b0f09040902030d030b09070201020a0503060910030b0a090b06010c03050702 85
    0x4c9a8410b1101010814000c400006505110b1a000d61148a03500c0390780e507045140072040703e548200040c0406205119010400300005280c41d031203d640800d50841d440340303000c11881c01200d014020100340c18507000094504002503090f2800711411145542c200280c2c2c001c404403013003141078010202484900c4115540030350300800810202e46400b038580700e0180c440d4600210f955002c2155036024208110612604a01c881050f48944000740281d401d03149403540f064078103020182c0315140000c0481e805603a10b9114000844d80704a040d80d000103142000303d0b00220b003520440426050100040007031400c2c2c1e5005100411048255060070415107202205401c04102c0329006640ca064402c090380d01041500c0103041243c0d00815007011400a110314908060038610030340e0b0051000c5d4040507006420b50b540907405440c400c1841e66124800440c1400c6036002501d0214080203224a5000030b80100c0407207800b845001d40103407201801142c1540344420040c0005030240102001413 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 525884424 1250 525883174 525883207
    0x6040902131517150d020307080709200304030f0318050105040b130218040606030c0b090f03070b090d0204060e01030308041e020108070c05120c1e0c0f10140a03240308 74
    0x140d60241c0301c1605c00c0316a0307001c03e140000a40003618070380c1c406441000f100429029002030040c071126881c10041010960701124040500001c5c01c0c00205945403505900c02ea01c426102d58140001c1e048403e124200038bc000d0400340e60a50703540b010351001800c01070b2610000b101d12580a4a0b0a542c00701a21103407581c2840030f442116010380362400000825a0045060301410702540b40350307695114a000c000215260003081400703500100030070440c02c00d030001941d01d01003081e2251481c031307801c0740300003001044941c01180741d01e180035001000b415808500c03103200b103105502210301200d07885a021401e102d1054003d0008110200040855104072110b20140e0b1181f021540c540b2744a101050b81ca4106001c4045642c0c03180940f125038605181000d000100c100010f00906199034003c1100311050003400703800341d20313160002c02c0320300c0c4640c1d0410b407603405a0ba0402d45030907101c1c4005001d04016142d42d03411070708000da070a20300e610a6410008490340411b41502c0c00481c0e22200c100d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 525885674 1250 525884424 525884461
    0x8040512030711160807140d1218090209130c030e0a03020c0a0902040e06040917120a050108030c0a1118010e071404080c0f06040902131517 62
    0x11800384200400010088201640c0248001d40f242071020110b140c500e86001400c00795020000708540c010014520003160740c10960b00c40c000d02e4904000c2d003c0101d400c10501140040030100c807070008008542c0d0101c1420120801201410b40e80c0380c2e0b51810b8400d078091103880d20b901800d6010104d80e10f01c41c91707011300391003000c504011036002c6e00d1010650424108142c10380260f00b2681013078075140f810781000c101900d18400c1c05c50a03c6d040a000100320b09000380920b01a0380e840d6202d0080c0b0a0358032015441d105044095647d0709035000d003440c814041070342c194900320b0030b10b030001ca4031003004000e682601e10070000810180b64030761128040c4050302d42b0700c00c0d04401e003200104480754100b20b9050290281e41c80c21581c078140443c2c001c0260900c410304410042c000d004c00d102c0554085180362111508450400ea0040c00100250032841141d101d44942480042d80d07118a800200404045402881011100740030405047d1400c1440008500e68020101e000aa00c1d07135003507102070718 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 525886924 1250 525885674 525885683
    0x140f030a090c08030a0c14070e0c2d04080d0305041119210c08010b0d080c070909030c1101080727030b0705030108060105010e060307080603250503070b0301080a02010804 75
    0x7000c43c0c0e02c9030410304561201420f40300003626010103a060144480207010804407c0c802000c0c1203140c1004c08550790300140010340b4565001628994207001c4042410f521168468405a03104030716008030030507449886501c2181c0110292000f2290007403044501c50703030700400d07070706880c5c0c20180401502030f1074804180f0031400f24440110715946061342041c4021986001c0b0440b0240608000c000b80f2110b1340000c001d6030400031081c020f901d80c00300600031190302100f01500c41107950b0075982002500d40290041c80e140201920034590f114445544003801600550504480c1d00c00454100e01c044075a6000f0a8113180c00641d01c4410640b40320024031100603410156859980760b400c520030a03106200014000300c01800f0b901400d00c80036006100908000101c2e0a2540129855010041c07801091051312700002c1c02e540c8090006420180d004420710300941315010040c400546e1130302855019105840011408040074000c89040c0e5148800030711403248294011240c40d80f006100300c0c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 525888174 1250 525886924 525886943
    0x1150504090f06111213050309060d020408010c17070906232a0d05090f010804050a0506041203060611070314030d050c0a08090a1518080309010b01140f030a09 70
    0x129030a4400c1800d50424040300b1980c8604141c1ca170240400064020305030714544801e02c030001900001100d100c0c0600b81c580c0c81d00e42211282c0c3c24028010b0b580291640d50070103a06615069004103145401461981c0c84545520303000012a607441c0715010b00004202d02c004089980c1200401c550311140c240c08050345072090780c3c2c6080280036074080504240d002180b03507045203400300b0b100b0a080c580c1503245c91802c0418240002e141e00640a86c01414880540080380a208042c051102c44d99000011118181001d1804c1d10700b06803100120030000c0d20f0702d10042100d5103c3e20081002d0400f0600802605085840705101c0c01c54000d1007030300c24441080441101c003181e00509200c0c800600f002504c49004490203080d03042c0040440038503070001401900001c9240144003122801d1100000e0302280700b110109050040080190123040080704200300301c030054200010340002070703031a42950b12081c1ca240c0234074014040740380c4880c40240300240074904580d1100d82c10501500408 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 525889424 1250 525888174 525888203
    0x80f0603032107090b0703050919031208160e0f0907030b03120a030c030203040305160c05030102130518070807030c0504051807140c0709110702030d02070e090115050409 75
    0x4a0b0110316070b41040300d282c0d0b030800c02c201d81e90350003100b19001480444c4585103441060b0b07800500500c5514038072489918020409000c2c14405807100c400340d40d01c282c480c1d010103540d0101030b004280884001c1d005944101c2a40011b074820490b1920019015024a1550190b0010045511002402c003020141c0d1500c141e04166030800c03205102070021003002c0d0740c1d91982403005040d034000e411311a00740b40c010801d11000981c03001c00c071860443c41000f410300e03c0d6030a2070003880d0f41c074a990009a2560010403c41c4141c03940b0340000d01112412034400518a00420010800d65400c07281c01003c01e080c00001950117010b40c0041e090300c138292506501c1c2031b4640c1e00086001044c4840340c00201060010812000e030010312542c0014265000c507420480d501750020ba85100d40d00440c412035444c1d03a044205e203c0c1d000181c0700c100d039005046da5074440422030000c1d034174030761031145807c0c841905020440410b418458040300086100048104604000c00e1101600c92000c0031148040340c0e0703000d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 525890674 1250 525889424 525889447
    0x60b0f0d140708011808070309180e0606030105010602031909032f0108010803090409080d0603081314030d080702031612020c0411030103110d06150504110a080f060303 74
    0x1103650907031003050900004141d8001d8285860351682220b8003030707854014411408007521030504070441c1d00009003603031035006180031204001e8540c0030a0347c52414a000410f180c031680c02c5100e0702c01100046440540d41c48003090301b031366000e00c50360b40540c01c1004682002505041c5903c503c81c480e080426809540f991080d049440c6161400c0c2d4005080c032007004000e82a588018080c5024603154406504000c2516202c0c46501512031095598003220810440e00d00141c03032080f00d10110400c24182c1d6810080541c5e40701e01041e98100d4040d54001c10461120103090848a0000d0010580c2c40110001a1618000131303080100b50f20051101c0c04001e110403501044a5210b01d040c41c1900c3c40400c4061300d032091005000d403045013020051221f0001d64015241141d400011802d040013619003c20f04001036140040c082600385201d5110a44036580401c0449a058034100042c44200c0321007003c1d4003034120194009a0b110340807a1f8005401d030702091700140010b00ba00e16102c1d50000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 525891924 1250 525890674 525890689
    0xf060708090103231f152c04020d0b0306010b04120807060e16030201020d0f0c0b0a18030207031502070203060708180304030b0910020f19030b2814030a060b0f 70
    0x40c03a110140810359401032107510000700b038004088400310251446e0480340c0c0507203048881007040203051740944481019070541040b0056080e4050002c55a452140403903402074200140c04031f0192290700c00001e0940005400c41d4200c49180361046c404000030342d00c050182d072010509035a40c42d03d0b40c409480c10307c4244482d1824041c6622928240c6107140300290070101400801c03000e0154922158400b550403c60b105040766121b210200242d4031442c000c0002d024450031505035180007402c0700105500015040141d902905403016050400b100d694143c1c0720344030000b505608090081804507020718105500300d00082c12030100529040c0b401461034000340c0c0140d9070f4882c42001d10907100c0d8117210b130210444104005500c0d10104c2050060701d03200d025149aa14809a507078900c1d42d5120758000e4034031500c010b00d40c1e04042c00300401c0600c15150f08614102e42c4038200e00c0000d9604003800c403640c2070a0041c024100141054540100515802c0c0c213043d08800c00841030029580c2d8050b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 525893174 1250 525891924 525891931
    0x1b020402040302061209011118010806030a051e06010e010b19140f2104030c020d0c24110c030d0309030c0204060f0e090c010c0b0a1d010b0f06070809010323 69
    0x3000021b468004861429070301e001a501c84084000c020452401005030000e8091500a0903e120341c0e03210440428940f074011080a1b10314050b0070407030080d106207422500c20a0b47c541044030303404d90b00c2f40c00510b54100300b84105c100307040040005e42000d210072014181c501e034160070304000c5403103966880142907106010b9080c0032800021a1007a000c000e1600030302c46d03500c26407040c040d4940342c0c1d8064006c0b00c42c86e0b00603103c1d00d0804100400c01a080c05010f02800300060721400802100100905c120a004101d002140c030008049815140000d210070990000a004040d1010180801d9000b8850240283c00b085100c080800160321075020380380060040d13140c1c00310300e64030300340c00a014075001410b43c4505403c90640a1300070382c1d210318a010041c1c0c00540307034545603c030003038560014400856804d004101011512140481c103501c6944c070080140c4224484070b0640c01080003500c41d40d41c008151032001e006e400b16039482907100001c00c44100151f81d08120501811a40b5408e048 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 525894424 1250 525893174 525893197
    0x2309031207121a13020318010c030507080f1306020d0b03011121090604021c050a05070519270902090406150b0705031207051e040503060709061b02040204030206 71
    0x751880410195920944400b01001002e8560203c1c0d410001100b000e0700584d50049242c011000c22140c0a200803c00000b0780100020402030582c80b1000c0c003e060101c3d2498085201180007480601c1000c0106108240441c11224012060381d10700d8029000348100ea00541c0d940d840a015980b001d00ca0340410810071035115440e1489004140700c08120074480862009984013401402c00340010855007181c2d0454550703443c81081c03d60030707000309081d83c4060581d01c10114940207001d800f02d106020f6a00c10b440004420015031080c030607141c21480303500c1c8020145c941411840790b1308106802d80000424000c2102805600000d0384140c4c250b4082c3c412554400002d1446014580407200a0818071380c00c505001c2240c545540b239000703262007000172211840000e801144640121546250254140000c03460200066855500103020300c5009208030000f08400c14015103c0387c0c00c8540c1d0355100d9090401240c1001407240c072600c02241c01c07640901c030210040e9500800f800941d10503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 525895674 1250 525894424 525894437
    0x60501080a0f1116110d02030a080c10020d091101030b0d021c14070e0a060f030b04060e03180f03010b03070623040e071205060102061f030210080412032309031207 72
    0x22410500c0d0701205c0805100c0c89640c03c80140001070f1400314141207180d03040400079460f80080c11800f4180101d48454900652000400003600d41155100d409585e000d0440c030200f10321180d0045d01100c00c0d112040d6402800c2005a40061903d80f004810f820b04908025801030480d1b5981c5000710b81718002c8c1d103600d4101250a10035803030850f010f123078401040081440786501d003900401d8050001e0001074243c500e100005024054181c1210b01c03121814000c403680c1d0082c0c0d5021004c1c060342942924410810f0548421880c030b414015488801c1c0001e026043d40d51801500740d9807000310311440f850f5040b8407034001c41c41c02d0819018000074040c4030b5029055140017000241200041003001c12203500c0c020a101c91640d0005425501c0200c3c3c40d00500c10882081503042d042001c0d50000398000e8000010320202d5901c0464140114441c1000c0344502100710425419988a4040d051860007518501404004a401165081000b40d4242c91a0003038029103410284400ca4450313010400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 525896924 1250 525895674 525895717
    0x302130b0a091425050f03070509030a08030604140c0d0e1f0501060f031a0108070e06030118151215060e15031204210303020c0601030f110103060501080a0f11 70
    0x4d40e240704403040800f41440d4846a49034107000c0e00303a00400034101c400e10000b00000300e10038041e000b2200840001402c5500300c1c202071800d50441c0d802280c006010394146001c1c0001d5072401c401c800e0184031003076801400d080141c0c9070f1000401c5a5051a41d007442940030003044401880300d4491030681e0200003048660400c03e000c1c01d200c0b0401d4001040501d841031182982d8a00f1445680030002440c1c1240c46486100046800c0e680000304150720290000c000200e040c0290394281c0c0001080c03205200c21722001e0300d403011b1100280301e400000b41d521001c10b000100f00403606c102c1e969000074000742050b140c0300c1c01080b207803041f1940018542030b8040008a46003c101464011078501013030b614141c202801004400306100400e41c0c120713a0341032860100b6010781c0640c0d90b07100c0e4210403078031a50380d241464500700c1d10500098030130507124007010405520a0150b40c2c02c1c1d440c181c68004084d195000750000400b43c040c00f04290700e68070920f41d854000100014031200340d92900e9481100f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 525898174 1250 525896924 525896941
    0x160f0f0201020c1f21020a0503150a0608041e0b15031203100b0325020304090f051003020607050703140c01030e010911190522150302130b0a0914 64
    0x480d03a031040b442108070600403144c07001c1c1181d0181c4041403a00c0c02c00f100040d0b44403202c0b110000c00e0b801d041c0b168001f184c4c154640381d011001d10300c10042ea0310030402209965043c80420b0340c00d030040d80c3c0043c6048001401290351400012200400311004004410140e00c410008081c25200c400340c481c424100c41c03407103140410540610400d4028658510300741a800020000c01500c1807000340440031001500d100700d94030f04941404070140801d103101d500034200940300ea000780a080c0302c203031804a40818404480c86120701c03d440c42180240c0e86811134003042400e4001c800c0407144e03445102004400101c03208480c1004014074002400e0490425002405a5500d44c4d01c14180703a1500c0d8004000c10cc00381c1040440c00016540c0042e282c1c0c0340300b038007296142250000c54101d010342d048080a40800810707440250740c400f200704145d0b08806582e240032241807001a40c071075060000140440d20a5200708e07142500240f55880c51b41e86c0d001c9030030964000d1840c00151120f05000c218180 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 525899280 1106 525898174 525898183
    0x40e030d0609060f060809101d0d180801050610080603211b0f0d052b0605120d0c030c030905031603050d110a0602160f0f020102 57
    0x1c2d116070320a0701524031845628002d0701003140c0040c455200700748040c01002c0d4200541184030f0141004000b80c400b11808040a010300d03d00c0c200100410000c0c001001d840f600c801c2c04070000c14001da40320014940c80007480f039060008001169079070300801c000d04125810056800e840e03000c0442d191100481281807410609440c1d054440c00c110040e011032128501044454048081e117192505607020207190140d01038a8100401b85c000e50107044004069100c0345030070030003090b1501200111842e04400160380352018855802c041c884184603008880080072060801c1800070714038050100050204070641691100b0140310700740c000001c24008040b200780449155644298110703d1008481d43d100c1d00c8090609540295840c1801c115507001410f101d030360a1315920080d600c062115416514030700404000144651180e04900340124955410101d1500c00640707032 = true := by decide +kernel

theorem cover : BRFrame.Cov 525719424 525899280 := by
  have h0 := BRFrame.cov_init 525719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 525719424 ≤ n) (h2 : n < 525899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
