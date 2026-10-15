-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4614
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:11:15.507563+00:00
-- url     : https://prove2.me/submissions/e5cd2a9a-a785-4990-84ad-63bf39b7bd4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 829676258 ≤ n < 829856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 829677508 1250 829676258 829676297
    0x10170604030f05040305191b1203120f0e0f060703090804120c0308040305010b0a0e0603102a08090f01050c07060209030102070f03120e0609031803070503070312020129040903 77
    0x1000074824200e10001603031034641100b00f10103100d800311400c8d988003400900507081f81800c0854051501031810811940940003c04980240e503100034101850001501310000d6200744556244040b20350399a03c03080c0440899915500040143c80c04000822846000b0500d140805020b801540d10051b542d54850090342c0c002c0d0b20445041e51900d00004107442c0040080006181c1e45004003d14034050002a4880303d4084906000540d10000c0e00c9022440d2031591a001039401c001b541c200700c2c81e070b50140690200f19641c05041c415151101da500c58180074440c01340d0302e821515400e01c84190340f014080d4003d07081c580d0309594240203910120390400d144007412800b0b9164a101c2c041124010421b80e031610180301c41c5076200400780320200a001084544ca00121441340c03000a6880001078100100740d440b4a5040c41601404014092003035814a6200001c0c1c00070406400f00032514500d980301324000342c0010b4112151521103040681085240c14440d01d0103090000c034140800b034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 829678758 1250 829677508 829677523
    0xc0507031d09010f08010f020901090b07060b040c050d110901080f072d0f0c03090b071106071103100e0d0f031401180b0301050112020607171210170604030f05040305 73
    0x4c1d05080114041200000a00c994401350031b080300294500b040da840041d05002c0c061290841e2407200103069001d1021b20f83c055810258003d005010090038200002d2040e0030400c41c50601e6454054800f20700300c010030880720110b4040c1c484216594849010101901000340301130203110945140004500d1003c6101e00250703a040625a5866222a0020b10740061042d00d141400b00c008409404a038210b050813084a00d401c4450382d0710fa5142c50403842000b442d000c41c40e00a000851076408100d003108218081800540c1213038250078654100c1310a6079203420f030400c5982c00040d00c900c04203100d154034040b018524100424000342c0344c02c11100d101d000740d0101ca00510043d9100031000c99601030015540c9088000340000c2d410a1f1030301007070a08600b402449a140001c4500400c1414962954209004c06070729071110b102e60380134441104201c681010440c190440455486100d005400700e1b148400010f12903135449550179156410401c208406121341400004000b4a04100a2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 829680008 1250 829678758 829678769
    0x30209060c0601030f11010503090616020c04140106080c1207050d06150c0203160612020a2a050105060a0305030a0c11060f04030506151003020a0c150b0307090c0507031d0901 77
    0x220342800482c06c2041100c03401e0000e40d410403104009103c100d1070002505038014080280200c0fa000010b9000e914107a070700138011750424101106100d019043c140014100c40164450f1001ca40e0307030301c1d0b80817454801c1840701c000c216079060200350760034440c3c0f0140404852403d000902940c481c4c0c504d0949001e81581c42d800108503038880b10440c1004d01c04c03076041d00d480c903e21012a070706101025000020701d0880413207c1c1c2c1e000c18100f81e41440354070390381440c0340394409200121fa100c090440303c000344900300f60b0b065801e200101390710782464032504044035000000386040220098040b13400200c80f900a41d198404000080700964401004025407104c00542030f68452851034010304209008068441c500100d241c1c80c00e2a850302c400d00c42c42003a00d03260069903094040c40580d4400181200035100c121080d0031800c0d0008103500c410368140d41103003280c2d60340365150142c801f504e816103213400009034240318000000e4000d186a0880128052402020303800000c0851000c1070309034000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 829681258 1250 829680008 829680023
    0x60906030c031e090a030e030133080607120b04090b0a0c02010506030601050f061c020301060c03030e0706050412060216030309020a21030f020f1204090c1e030209060c060103 77
    0x14030410f94203000100c26400b003c036500202c2c1d4a803485600d5180c010700c0c440a0180118000054429a000c1d8400740010101c00c0c0311480e030455402205101c126014803100080d04030100102d08240000b032a103204440e0340c1d482000c02500c83c0e081d500605000440290081c0d121070380c1d40c00150148000703d1094161900c001002c40d88404020f080d031350041c2929000f600401c0043c071494031100c0d15201d140300c003502c00c0e40e40e450030f1030b4442402e06070311501c2200d1035202000105207aa4044100341c2410b00070303134040c04060741d002010368031022680725400108804000c10014080c0507d501580e0305d004143c01400c140001c03a2105108500e0300c0704400080e48c40c41020110718044144002506c01c40c280154088a11000100d0600304aa00603040c081003c0448071980e10070060148041d01c450141c0e459600521240100c98109000c1c0034606402d0411074459580b1078804220030703446030180188a40c42c5241d00350002e6004002c00340d0400c01c01c110045042d001080540c5c0250300c90390340c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 829682508 1250 829681258 829681261
    0x3010e0d0302250c1205071e0e010905150f0d0f0602090a06080c07021e060703080a06050d2d0b010806070e01170601111c0504180902180402060906030c03 68
    0x1038001c00640300e0002c3e12000005401c2d40002c101141c25102c10342d007010126010704409410032502c0d245240d8080c0ea9801c0540a2803c420750214a4100841c2c90700c510200d9180d1301d035003d00701070755000c580b100030148515039049503a18041c011a0100c410203403410800480640310510410098203054480607000a0b041c286420025004001000146804041030401c4014800d040c49881d0300a8070440107410103040c80e5030221301000300c0c3c510080261303a40b90210701c1c0280814104552030a0042e180c8000000c1074240746400303a00d1940d2000300e0f0351072181640304c1c90182ca40c80f429201c0c031031103590803504002101c070130b402806040c1c03e000505140c644a00c00503c40f81d481403138241040780381805d00180c1841d085103150000d00900300b00e109850646585d030300d41106141c4150030818420f031b8030003c05400c00003e1041d103001180c4074600c007010f40035a4080c0c61611000039004001c481d0701d00711100c070806105800502c000c0c005850b15041c2c00009486404c00d0701d000854400000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 829683758 1250 829682508 829682527
    0x170402041b08011e050a230a060e092521090f0b010803090607080c0c040f0c030b0306090601031e020a1d0a05101215020c0c150f1803010e0d0302 64
    0x30b51003052840280381c0400c10300c0c03c0002180038914035201f0f440d2820382c0003100d01b024900c0c440781892540805012610034503030b142c00c000d040c5072500382c85d107002c0d080d00d0021900c224402040000700c02150700300303044d1545809034101c42c0c01543c144468485411046038a1845000f03010b800b07a068002d180a60080c2002c0c01c0c500c1c40d021060380205100d81c020803074107041d622401c0c140d64409412040c0c568443c910161014241982001d1a81d401440c201070110400665400400d818041d69010070440038040d040c503656020999078200c01e684031000410020f83c01e919440f82d810341c16601520010129404100700e600c6907005005034110703451602003024141a629540300e2241c0d00240030b01d0600400040204010f0301030a05a29200c8080304280041410414500d8002c0f1004540e1441c0540ca400e88541000c108184203061040d0588064070441060741c4d810f80c039280d5101d140c8080b010315010019030082600d5099503c400d54030b01040c005110310451001603440c0943e80f0100031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 829685008 1250 829683758 829683779
    0x70503070b0106051207020c0d0809030f060103060501090c094a0a0509030a1d0a18150501110c2106091c0908060408090105040b03090705010e040903170402041b0801 73
    0x141b5440c02c66101d0f1a0396840c0f0b50315290068002c070780200c0400d0707440c4036203000f09041c03a14010800000e4485d04000004000c2c850b80711a0407950015020805594481002c60340c0440d140305804860180f80f00c40c100c0341200c5040c2d14003055000c002c00d0002003240b500d10603403000303111218004102000400c503100c14039005030341e03001c402403003e03514290702c0c0540646994103400004540c251328900b030003070740d03151101c1c03c0c1d01804c00403426000e0011640c2c0d41502400181d000082400c1c000c210000302540240c0d03001c00c0c05035280c13000d0244002d100c014000c6082811703080441241c0e0024645100000902c00103008408520240600c845888054071030414003240540c10000080c40070044480c02040340b64200c2c2c0d020480c2903482214030012078481c048d680180340c03005000811300001483c0011100112007003030302d405041440c2541080101e601e01c2d20003402041941045090100260300c0c0c05030f105100410016103140e204405c58000c01e68040d00b00c021070240c000502140211 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 829686258 1250 829685008 829685011
    0x70209070e0603070809031309020408070e07080a0f020904020a17010e061008180d1101110f07020607060e1e10062d030b0c040302040e1b06070503070b01060512 71
    0x1d040240044500c100402e034140b0005007440c0c100418100410415803081c4210384800002043c02c6800b50786030950213009500030310504050340300d0044c000400c0950724444510910281d110084142c0d00c0700405405400921140e0550315400c200719007d50b926031018010f20343c01c9559403005141c0c0c5400d102401f0328103130848801c81c600303d420011256100d0480c40c0892840b441c0c82c0c1001d85070809002c204800f04818008140104068605125404100c1030340c08110180203004036003440e5842c1c031252080c3c0b48480c0380074504001f10005030400360700401c0d40c2440f031440014070404d01800f20b800d104d503001c1c54160006a40e80502c0c0b213210200100e10441001720000c00c101071070030b09a5010401c81c0c603a0010031514046500c222104280300b080c004540002401000d4a080458010b8a50003408128030540c9041c082d42656400090000c001c16103850302031788412040c03001c0100381d8000d03480c02c441d144000c1040301c0003c0c03c075210441c0248801d032141903d03030700c101c2d0580009040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 829687508 1250 829686258 829686271
    0x901180e06060312071e0f0c12050703020f01021509030a0f080f0106031107060501301a0604020d020d0606020c030d170415052404020f031906030c030503070209 71
    0x500240a0240c3e80031580b04400d00260510666482e140d1404503600e110060b05c0f0708201c101810600c061015104400b10b01030b1203141c0a0501c50f0704c034608002c0116000402411a03484140244018145841190f4100405004031044150f41035048081e041e0101d0b070041c51608007080da541c2003904000c083d0a8005d042c03c018a0b24504a60650001d40d014420441056101e961405014850074110341025030044414802581c442500130110312049954654203101014400380024290b40d4542c0440c1c2c0c0211100d10140318032149880119000c1d162642c440d40c00c110001c405202c5100404444018985c0890b0b05898190003a05064000700564000c1d00301069048115910000c0800031400403843c1e41c07550344940c02d1480400040740400412245054240480840c03c0c0034810102075580d105640b001d0402400d02c4260300821320070700044401800032440404007c04821a034100c2c0e030340c00240d9503581e40c85940185005e070f40156a290000101d44007507040082c42a41e000d507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 829688758 1250 829687508 829687513
    0x2040e01020430080309030a1b020d0308060109080f1c0306052b1e0c09022506020d050c0301030c30050703021018090b03060103140106050901180e 65
    0x51802201d00702d5010b4445109002d0250350340846550481d00d480e48000540000c01ca035264641b007079002c3e0b0340ba03005011103030200d120014103801c5110301d880c00c140703003a41c040c126140c80e209583e000d44032118040c0c001c5051040d814800300320000700f001189880e06075000202994440c14510f10320b000d44112150f4101400c0c036000344003075110002491241c08011200b400703508003896196000c9274201100905103504031425083c41440c290070700030701ca40500301014529a90b10700b000128400c0d0420046d10444d1b880d0f2560a4002582c5584500d42c000d0b13034098500742c00b528203402292400c4912090145c03020005209000190740d01202a1000620040c40704115400009101804284001ca00120349600c1c60400c107040c0040e0000710303406070000c0846a00c1110240c01010110610b10440c0340404000400d00381c5405000203099014015001d603900390b4072030451428511200c1c00c2c45648800d0009802d80b80d01410034000d0140b100707248410f0000242403000d03035205942583c444d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 829690008 1250 829688758 829688767
    0xf0c031407031109150d051213030b13020307150507050601060503010819110402070201110105090c03010b0a03021c02011403091c03020310361a030a0807060c1b0f02040e0102 77
    0x412108404140b0000c0845094021b80c00601d001840c048110803150840d900225413180107000240e6002c0549104203c031014558074101500000d02d8610000ba5056101000400802100c110180c2d0001c400340303040d07440c000007034450302d103803c8080e4007800c000740c4004010440640c1c00d2100d603058a8161042d039520b040715842c0d400d224035910445601ca02e50002d82401103a0180340f800f040034514000034000d40c07600c2c0d840b10361203c20710306869001b03500700321445285141c00103d110603a1703401050b120400b00600c1841490011160089061107024052402d4031030324000694460031120b0002d0a4110118410140d1943d08050100a050040c01402012035080030b2440907210030a03150300a840d541103800004c80e0945894500003c08811703c8002c0c1c0d0344070b4000350501c8160007150704600142c50b00b80341e030b10707811007001610741c0f401801030500081158101c040c2c0ca0042c1e181c1802c410907000a580750711003c01800f110f114851542d24011802c09004d40440481c01800031800d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 829691258 1250 829690008 829690021
    0x30813060e060301081c030b100e0301110c07090209060702180105150f0a1202090406080105040c0b2106031e1516140903010204030f0b0415090f0f0c031407031109 72
    0x2207044102030160940d8006d6842003d092003030388640000b80009008541c00c100108010748100ba83c00c52560082d400c0c01c04201401300101d0442c5c411001c82401410000d14102203c0c00a400110341d0b030351b2202007006100090380e5800140140040d051988001a5140208110064200710315003a0165000d104400301a00d0030003d50340500741c0d90400b940341c03004400e41a4028070554040b154454941980072550f88030540c00180320340d101e00040790101d9280c4083e5801d90151000343c0e480207200581010300c52041c440c4184e00164082c045950309003040e29040354502007035651002a9100304511500010b442d581160480c20351194030500c80510311005085039040e0950007204440010740b000c00361000d504540046420803107500c4011440d00d002c040501c0301340c50a466802007c545801068254840c420b80c41d607000e10044500d008030703503600c4010300e2703825400d50742c5150140300080401c0519141e250a806c540300545552811031901e52049160440d600380289aa1801c0050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 829692508 1250 829691258 829691263
    0x3090705030610140112022a03391e06180d05070f0602120103210e220f020a02011503110d08160c0f050105071a060a030813060e06030108 61
    0x9640910ba0384c180d000c04080c005035051008100d052030316902c0001c4484501c142c24218100c800340034481c104500440c4514541d40b801036a44500380700894003521003905215540c544d2854800100220b40090007140d21801d200705030000c0607032511500c0c5524201482888019888010210705c042c1100c8414401c60341c40400c40d8a000030f05c2400111042800800d01144008941c459070941d6141c039120321903900c100d004e03c42200d0703030700c00441c1004155410700c880260b070191395541c200503011001c08019003a085280b201000e07074100414000f400c1041d000304006045036040c0540da0700e102500003800c50704035601ea25a9805020b5043c0005803c030309025544170030458014001d000c0a003006801d500c41c2000100c15088910740b81c50820050704041c40441d5014952920403c0d0784100644140c810701800030140d041a420440085818526107038020102420b00e4070784940709c0c4d4400c2840e9101a0a01072003101a006c00c1001c2507129070840e20544040d51b05a065502d411380881c3d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 829693758 1250 829692508 829692541
    0x3005010618091a090421051206010c0f0212061f0302060910180608100e0108060402240406050408010b040c020307031d09070807030c020111091c06020f030907050306 73
    0x40a0743e480e4800090034582e192018680300c00c0007042c0002500742441c0a04110304008460001c510003600020506400340007568210b0000d80000e1940745d44030801100c80703685561040320092441145030b00540c48851a410544103424018030030390500d00007100f080c1d41181a02e442800e071215007070005880d48003c7d586080c205445030001003140e00e601351003004081a4003041c0d1550701d0000240d441d8400c26482c02004580e5100849030b0b210f80b81e8034010882409a4001603006102060060500c4484440400030140442d4880d000c00c1c3c0d00c0200d19441b9a020400003140401d05009018080c4901595030300d0894040145d0f101c0d04030041e40b01c0c081c07410080c040c4500c400142d01440034000d8141c541c401c00030110203161504080182c80e24030140c0b52000006d2504ca10424007d005100d01c00d003100d400d064183c18140c0300c40c100a00f0f0380101004103040c580c1c1310600c03000a20f0314005860264a007190661b10303440c08081440c5040903503440789201e43d00c00014405510b06202e03004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 829695008 1250 829693758 829693769
    0x9010b220906020a0c120503070c0f050f061501030b0303090a0b0f160609050f011509090602090a060f11070e1311090c0c010b2e3005010618 62
    0x5608034003166004002420a050003820040c00068035894a0b680080380d149600d1081c891443c544503607034412100c0340030450b803d02c04207201c181c1803c0444c125402011003507204004076950000554255800d1040c151004842c8208410000010b50b8140c05852a020303010740085040c0709007200026590551485445409040004c90003040b0207041d085503a01e284004500307814222070702e000c2c0000e119426043d01c232070190000c0c01c510f5410600624440304004014501c030316080110880040640c10800c48141b41d00f00b02044a03600c40c0942036009264513101c01102d0700f403403103001c0c1c00d03541d40e90740081d0150008141807100810f0a01072a4000081541c012a424003030b00d4034405403030407190003984c4411004c040151003c040001040703000c0d00074001303010b4221400c0a1003d00e10003c09560030810341d4400c00e101a01c0d50340c86010f0a4102d81c50712039001c6104611080340c15011000f0011100b850a81402c220300050140f2401042130b46462040500400083e5031801d41e1800381 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 829696258 1250 829695008 829695049
    0x602070803031006211404020901051008160309061409160b0d112106041a03060f060d0812100f0b160302030919030b010905060a0338060909010b 64
    0x1101600c001c0110741d0600705e6030034104000c202c007030030a138107000003140c04a216030500000843d59080a0110940c001c64540321203090762950000d500205104109000806d076a40f103851020a01d58000c4082040080d12819840d0814024803400c10301d241110041482d680d420800c010040baa0440341076920036200000c4400356a1424609881a0b15840c0e494078940c0e01c0030040311a14000da503000740070440c1e0402030b8051141c0e89840d9103424060040e8107070020000a60500050500a81e00840050200401655070340d560310070354209500340070541e107500040040c61000340c1142c00140486001c10400640303030403484003640c030a021a040940000c1c61ba03c0c408c250007042560103881c4020034980440c2065002580d80d404070b4401903640405410000030350740390314410b00b4050000503100305615411521181e5039404865107101c3c244000740784640060301500100210386d243d4038002c43c0941000300400c403001a001d08002180e0349819603110a03a2350390300c944000360071507001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 829697508 1250 829696258 829696277
    0x60f0302040b040923011401031e0905031207090e010506130f09023408280306080c0f0604090e0703020307030303050f15061b010e0f070602070803031006 68
    0x41100a80119489020041c0340407a012986000a0300a414441c8001d21810076010b40c085503914000c000f80b08000ca14038149002c8400303035100c0d41120a401c413182c00742c03d400c0c0c510743e5074010460b83d082c83e003507a068102080d81000424040d15094210f490751900145081c14260800300494061080c0c42c440e41c40050107600c3d54400501150007480d01d070704080c40850b80c62506101a500622040d2400300c4003046032000026144108180b400146c2059460b8040558466a603a44103481401c2e403020281000d02c030100d110048554240110760f000304580780b40c18102c1e49007004051809120b000d191008a0381c0c1d482d05420745044810b220750200d0301c0061142e4090411050390406901801403610200515405411203802002901200d240d2617544401c00e0000d8030303e802c1c1485e44101c040000c41e4101150300428513445460400020720506034015103842c00c41008880451500b20281c2006481d4052080070001d00940c0041c6165240480c2190318008450060b08284500040e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 829698758 1250 829697508 829697537
    0x7140d0f0804060f0e0303010501090603060b0f210408090901080105060108040b0601090b03090d021905030708030406020919060e0d020315040321051f060219140a110301111306 78
    0x4120711032102c843e40d0b041080d0080d0740243c1b51a984240205404030381a160f00061551003481071404440090501d2401d201800606903590340c00014010b143e034444070b5101c4d1080841040c024050b80c4226105540c130812102030100741c4205038800c5059924040030000c0c5660440c1000c0ea0065000e0201d002d26a03c890040e20142919040350403104404410003124540001d55031043d0100340e002c40f14408070031803200f045c40795468001030403078005021400004090300c0c0595001741c4102005070920100f100440d40c500040c40b4550b0921b00341c1d02c410011540c01400c4202c00a03825190354800603a1900880d42d41c20000c5400c0f00c10340b010800040502d40300300c400002546060000305c4540d041e04601e403001d02825510300c460506080344c41c00300500c0c0c850502d0125819a006800810406890320a040602e20010b8030001d41640d18100e0220301441040d000c20710854800315001c3c0c2c66400e2500711620003a14038018001000160741618801340d008003241c9041c580441c07400187c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 829700008 1250 829698758 829698761
    0x11030a030e1002070809030114090319090b0d0c0e0109050a0509060622060306061701170708010204150e0405060303031914041a0609040b06010e1f0507140d0f080406 73
    0x20a0007110652000c60701c4c0c0d00300a205002080301c480101d000b0700c040c1074007280000c0307074100c165509002c0b40e108000b10141e00d42a0244200126682e04045001c550354901085881c0d1011840600203030303490101d4404070b600603044105106d03083c41c0001c1e5035814100801c07007940807030140034800c01440002074100d0b80c0780000c807610403614480d48817404514518640200103103006103c04241445000300e0220301c41c0300051444140305155540716460800744401c202501240341d0319a0164110102d03019500b400248000c24040002a2206010310001048246004812445641400d081c03255954001090383e41003860b442603114a00f1001030000300820740e00504200008081c020001070241c0705241e4200b030300341c02c01201d8690340e0365400c101140301c003101d008000c3e00382240441c400e5403082c5000ca5044402900c001400d40e460003282080405900240300050400204882007041601c03000e08245400002040c10036603400001d842d4580c486410760070840401e00103030034030055 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 829701258 1250 829700008 829700023
    0x90f04060303030207152904090c0b0309151003020405130f05070303080c090117090c1f0906090803040311041d1c0e0108060607020a08100f060611030a030e 69
    0x6004010841d580d140c0980650081c120645a02032400c4000c2401c0440707014500c1500c400609001c0040c0118042101e21310704c0301420f5400540e00d10718240050344101207080030f0004045845d803203192500d00141382c5888642007102040034032040c069a41000329800d4156a0304803808141035496031605120003004d0040030f400c25620a08150a001c0013007148826640203944e1060310ba40c600e00c4000d20b034441d00400d50300103250356071075403002800342000c030350022500b10954000c034108400041c8050401600d0281c42d4034418102801660440740f0900140028145030600d0f91416140301d48034003440c032000d400c0049102d610b040c942d540f944a040340c00d8480c919002e40105c4c01d20007a9072031507440480411405401621180107025002100f48500b050b516403050b0b5460a042c040e9541100d00126040300d0300c20070108040383c0900c07118244040e10f150028415010540a03015920030f80e10240500031075204001c40a580881103840d500090700b408070b610030010413118908540c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 829702508 1250 829701258 829701289
    0x307080c042d200a0e041e0f0510050102060408180a030611090301150b0409090501020c0a21031125021e0f040b0a030f050102040e0f010510170c09 65
    0x1407800c0000c81404030b0391000e18858030380504043c42d04000542d00c5001d10401d074a00c404109241e0300a821171900360041107039142445800c1098880b850f0014041c0c0d480302181d40e00f081d45800c10012100f039000f5041d4010b040920062242d4100ba403138482d0706110701c15075201550081a1414070030b44459414100079079104500300316070032440c1c400051982000754030501c40e50034003044100400c41ca04580095a20a84186181c1403402074a04004c004801c011100f65400340041c0d483e061040c081152441e014140641c1c80712146143c0e80d0240414000c10418103141c0840c004500c0384c0c15054a51103030800300d480f1010003c0800e24a901c0c003902c00002d50007000b00310728202c080050070703c200e001841600d04e1244d1a41c0e14003088150341c95080a1500899101010070102e42006080900c16000c0e0b80018035142d00d07500724014142089a411140074481b50041100e42003407400764205070803130319003241014550302d18a400b13001c014080014101021a40d030300d26540d80c080c4402c8010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 829703758 1250 829702508 829702571
    0x25030b180f07030504051218091e0703090b04141e01020a090503030903100221010801020a12091101052a0f070e0108150a0e061f050307080c04 63
    0x61040032052030400111900a540c1c010540401d01560003401401d019a42c0280503000301039508040d00002c2d009405042c1103c0c10b031855460326500e070184880d02030320001d4900300340d20300c62100c20355030300c2c46c0a0440c13030415241c44020008201a204500e800c6680052246482c100c408245441d18900c00080d100c110580d42452014590541c001c00c00d5480039201c140c6141d0340d41c030170903407240a00d1450a0300358002d00310b00d51020900798028041d0741e02c1545449081d030036114226611480076040350100303a5000400c40200e540124070641c6030320140c00c05010b6159290340d5004c0c40174030104181c0c140080402e03007a0080d600424080040401003601d204c10301d010200d00780c5c2d07502586040c107000d8020014003080e00e000d011060780c140c4403504010071140c04424403003a041c040080010038059681c0c0d024080202c0184101c501a40c6012480f5034030980010b41e04180440c07543c0000e00c2640601005c202040c808250003e00354001c1313030001420f12440846004507a1698603203030307009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 829705008 1250 829703758 829703779
    0x1020a020f010b06040f032d0b0915060609040504020609040212010e090303070512040206211f0501020705010c020321030901110a0903060f090501022a0625030b 71
    0xd50024600210540040090003180325181c14000d881c0305502800400c1040b010052011038140102002c0e04014800344003442182403441c1d596000606c802154a06801d4041c40342c220070820444266408624440310319041000028819110f001c4101d4001c0e512200010150354a080c20780d486004003402c10b541e60707101c5001011078500240101d40b01d0075004000300d80c4010300003098038800c0806407905441c00c8420064141102d0001f0403c070780c000010050000351a00c00d0b0004692904911300761045400d20154481000300840056164a045070004001c2607a0000307440049070000c0c00c1490510b107071400481c2c03e00c5000c404440758400003201c0c4528100a03000250312131481e40008001600140380c1081851280c4d402c03240006045001c1400454080d0740580c0b168814804001080319240d1b81e1130703007683c200b000c0301d010322070b06503203410f800781801607003003440b1031a200c0601038503c0c0000e1060000c071f130b98214642804103040402d404071070103507100c499854002400001807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 829706258 1250 829705008 829705027
    0x130b042604050117060102061b090a0b19170118110304080a1205060906060d021e1909051e15030f040606061b030f0e06040306020405100c171b0102 65
    0x3140c1c014401c00c2d0010780390b4508036002c3c2c030041035202c0c0101e4059000d02101d881c4d007040020708441030000b00c0121401008201110350b261003244004007041c0854035101c44001c4188250020700d4031184d014032500c3c455030740050740740c151000d05503410159840110300030040c1450007009001d42c0031001e0300c8000103000a10144d41c0c050700c12808940e0f150210f440f580308440d01034400585030160040b200c0004503040b89851300240c04c40d08600c160041c02c10702ca026610200c000d0990312414500030005914100b50503180300121510800d040624045d49803d0101d0203013050010704043d02004281c81e00026074070702e00c152500c840c1400708075480e800c0121f030420142100b540c1c221401d624007000090f000f4001c41600750181840840882c11149540313081c0c450400e0303540c90b4000c0007000c555004290782e600000d80301035405004e005840e58105014841c0e07a9940d020001d007800741107503075180040c81c0010950030710301103021280d1300c80600c0b407560030038400c901c1150035047d40041641c0c440f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 829707508 1250 829706258 829706333
    0x609091801020c10051017030406081306050406090b160e0409061803030605090f0702030a0c2102060609070503091c1206030b04020316060210150e091f05130b04 71
    0x5022951003a91b411a03542240f00566200100c802c865038100784810001c207070054400c0c40d441048550b81c00ea07604081c0c0d585004a03003040f102100c0190b1349000c42010b1250369400d40d0341c807098040c0320131261008450003500d07844c40a424144551703100d105050400280da005521840c40c1e40c0d0303007150400141d14005e0301600c03050042d1800b400c0c1032400140411940d0b030f01c4d00c0c002c1c41c050300550316120f0401e2040740e01c1004001d09840070f20100700d4000448000c80000b200d180780c40e601522803410300030308000581c640503040004020007441840302400d004a880d04114003055101103901c00c0900e81940d561010002c07001c250ba14010000046c4451441003910581c400c809980c1281c074a40f60035036407401e09000710300050f4006864003a05507055030095080c0c40520344100019580c0300845100140304a44035880d640040d41c56203815072941d07030f01c00c1c004142c0c10000e01061030181030030350200070900000b030003050441000ca028010403680d170a004101080141c0001c5600000614 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 829708758 1250 829707508 829707511
    0x150618061528030903050702010302130b0d240305060f191a030f0706090b340b0f040b06151207110d080c0d0e1e0c0406050609091801020c1005 63
    0x340c141c0200b11000066501c40d00c55007800070342c9911280e0a102da203400442c002d401c02c55030805444416000484c000715040d025016030248500081040341d60403a814610603030000c2e44210072000c600342840014404101a94030900240403a91a80c0c2e5600d544009140741202403220103142448101c001140f01c0b5004a1440040d8103d03642e41c540c1c115910354a511a2048200042c05031109000340e054000040c21000219520511074109101900070860000c1d01d02024007110f000140c010000c00c8882c0c0ea80c40100c0d4000801c003403504c2e4440e40060b0900420440c42001c5c01100c01000c400550240d6509240c60709140d921850200c4010701703041843c000d401c01c2c900c51228000200e40c842d0450a2003441c8000440d418000e0b4581d005000e8000021214900e000c1c2c1040749000805130505081131115807802000001d00c82d200784400c03100c00d900000e00816041140c084d458682034440780c0c0012582110480d403000310350105009004d580551440da002c5c81251280040c201d80203035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 829710008 1250 829708758 829708807
    0x105221202010801060c051b030a0203030d0204030209011d040303020a0c0b092d032a10021207080903030402010e0f0a0b211e060118030f051506180615 67
    0x20012641c945c030080c1c9425243c403d0050255001c507810424407400a190b0301c1c03086102030308a0311030f110240e00213415904268441d070a03469000ca000c10039480c002180c07a005141040c1d480c11603103003e035080300b000000248040e0a02d600041d90701c0c03c0511420784c0d2070038a41c04c60480805420a4400d96460301016841000801c1038290340c40d810140343c00951448010410003140750008218401c101d903a1075010440c00c0c1e4400c260000308002c818043c8000c070030784c41e400042c0d8419401b4154020403401800d51420040c282040004103107000044070f030003a4090900141c0400b00000140044210301e202a41022000c1c400181a015101c06000441034003220b403034404101d070540f491500001c64050004001080e170a8400340a0f10b003149400c11010b1500001d100d6005441d2500d00080343d0003240c0d1006000c803100103101d010300007012100d001c1d0070f039042182031505c00243d14071948010a040d4000c1d1070040340441e0f07030b480100320130700c000c010b0703119185c80310014135060848190f04034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 829711258 1250 829710008 829710017
    0x3101502031c0c0e150409020310031208040c030f2102160e040c050108070905041e050a1415040f110c0d02030f1e070c03061e0515010522120201 64
    0x1480300d420b024000d64a4800306075950516a0941504102c6400d11904601c20f50507410040451010114002144100302918240c40300c1841d40c645030440881c400d4203101080300e510f052100044544c00d1f00da0481340c0110000709800302c40d081140a00c3c490014801c08000c5582d000c00c1240e8000c12080300c0c2e100c405403034205a41daa5a03041150160444c0c0040103100e403100144065800392200c980c22040902c2c0104006841d41701050445030000540d049105505a0017a401001030058030b9100601c0c403828400868002d000c0c415804c800742080c0c0385540c420071101c0003a202e5501c102030701100c9210034054105001d1500030f0070362140220040a0207001c681c0001c032400001250648410610800d10344644101e13610003503800d80d060f08044080c100702000104684080e400c0c080c0d03020b86c40024040900090003030000d4050345114010a017040100002e5846c0d0302d0030301a4040e007c1c01e110359038104941c00c032144120990070003a5402491a000706800c010b041c07007140710f40d02c00c2c1c84 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 829712508 1250 829711258 829711297
    0x4050f0601060f090e100317040e040f021e0a090c1214010311180a09032f010609150905070903140705013c020f01060303120b01110a06020310150203 66
    0x501517500c200e90519000440c8281000062901c03e07211140f01025401746041a4452803030881441c010740f03081d1b03100d000c1c00160106618050011020311001e000d40304034410700102c08240050071501c14034000d25035620030000540c4c09801105d1000590b840b00304036281205600b000020f000b030000382c407040002050301e15075040140d01d00b10340d4070700d041901010365200c0b581d01c4003504040c1001c404021020b084214984d80c005000001ca0707543d10751104500c2240780807030342165000d03800b0702c240500749071034140040303084080c10041e504c5030900410203942d02402a55104010b40c401000688442403103010340d04003103444400d0715400d03a50310791414000701e0a075540f030f0301500b4036500200a030300ca4800c0440c810043c68000c0592401601c04c9004411002406c42d9030f107a00681c003280340d0f03e680030341d0100b083c0300d0300c100d40c003090908ae1800c42050070a19613400b9460710041445c0e900101158110400315145002440d00b0480030f10940706a5000a4413608803025103010001d0900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 829713758 1250 829712508 829712519
    0x220c030510151709070f08060601020d030501050f150f03101403060103031b03021216030201060807060504180b03030d06091505100e0d020301020c0f160f09020304050f0601060f09 79
    0x16810b40b40340900d80d03640c3d400350010001001d40b0090103042ca00e200d21404600107641120301480304000c001070405080d407480e1803000a800d08209100100030180341c90014016039071802a41c01880c2c0b0300342c81841c4807503100c40455019120390000c0c00c54005020003081201039620b0801c10075a6000e8034136807054810300c42819510482800010041880301d00c41c2440c05a6250031581c82c54005d10440b083c034459003c3c0721105901c002030b0703c182c070326a805544040c550240904002800e0440c000c020300c4d480c200005001d40164040c4481100214541240d00285074120000071a0014140d0f0782d0b071680f440300c0d0310040c000d603c81c02c1501c1d81410a0401800103a01024084400c09047c1e0380804040e0441100d1f41c00c4491002540004c40d01c81040140c1c409202a10a82e5510b40040401400b110001032804074a0321041c80000b440e01e400303021007440401001c04071850a4809605c0380c58138034025003002100d034401c0714140314810000407480d40c0046440e01c0307006c084e10b900c040c10791240c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 829715008 1250 829713758 829713779
    0x2303061e09010612140103143a14030a02270312030a02070c181127060906130612180f0c080d020f1c020a02220c030510 53
    0xc0d040d141d031112149004210340740c0205400c5013041090140001c104e0324018a0340010702007a001600ca01040000318120000b080101c400305004a140c07000c2c0c0105030039000301404018400301d0180c141e420a00800f100e0041101c90120806010295164581058100f0094200817144104601405400020703541d88005c84102e40034003401502001104100d500002d074800381440c40c0e00e6600300000d00220b103045804a0140101c107404000e141e50141d02041500c0c00070050302c061250401c040140700001236500000c100c172070540c0301841241c0c1c1c1c000584a000708507110b80c10200000d000c40d07852041c1508a07040d50f80d1343d15841d0b111000041c0e40012140b0101e54400000714546000c00484c00d86044c90300114072401144540030344a4240c0750404d07070100c4490002d40d00403500c015003558184100d143c4000000c01d84048410100d100950340c0c10079000113406444c0c042440d484610807010400c0150780c040d10140121a25450014010441103840002c10703032004c0c10100386442c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 829716258 1250 829715008 829715059
    0x5030a0e1503070c052509050c09061210030b131208010b0708030903041d090106120b0601050901030b031605090a2c03040504140411030607050415230306 68
    0x188200d40303086603110b180035a143e13200503030107031200e1080c8040145481400c421103590020384a0984492601d002a460309581c07001d841a803a50700280180403541e1203410946425450b40e240c4100f894440344401d030210140c642020b8040d20704007041000e852101c0c0301c19130031a4401d4244044204070f14200302d50380003013800b50007020301c0d00b00004004510306001540d00807518205403480c01d41d5868017181ca800c0303840240003c1e08544020802080020300c1514010b107450106840032540d90380e10420142001448a03050040200e0358000c2640b0a5008040b002070103021500450800310311146005a903202d00b502c80c00300900000c0f17a05885020722600940c50030302e400a09086881c802c2030001410250398510311050000040603901e9008140c56440440007689181c209070800c2e1550710781c4151518000c2e400388042c400c44650000864048507200344c070541c00d000f4000011a80d01c0000f8450046000103224a6402c0c1d040d50401180621000c41c2d58644d0f600f10620f0009100300b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 829717508 1250 829716258 829716289
    0x20a030303092312090a0b0c01051008010903050a08090a140f0c06121302060c2508010207020f01050f0c011b0216030b070e0105040b0d1a182a0705030a0e 68
    0x440c040d0100d01300b020b5806001d01050080000345115140c1c1c4d01000340390046040e0180e1691134809201c0685005d8a0840c0607005000080c01008030030b482c0038050b4480d45844004000711803000445402c001e101548905502030541207100804011341e0f5901c0c110300f4142071250068180e40b020318901082100d100b00245807010740a0780e40c8c900881d40d5014680c0c03081c0e03080b03101044030640d0101d0a00c19040c0300008107a130008145140e00c0b242288000350340140020b60310401000c40541d6900c4000001d51304246405540c80c3c40340240c03158030740500800004550300341021035407145c4800703004000e80381c402d9084402550040819424a003001d00c070290042c401400840d1483e40304980c0e10030300b80d0060500d145407981e6040541d05c0ca502151401c0da0180da100d180700b880c500320621103a00c250088034000c0d01582c3c02c091401001802401014080f102c042c0840c849054030b030300448070381039111900c0c1d856142d64103220340c032640007104100010700b007498000c0c218500729074015864031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 829718758 1250 829717508 829717513
    0xc0306030f020d02180c070605072c0406050d03050c0c152d070b090609010507200f030301030c0f050a14040b0f030105010807050901141507030c020a0303030923 71
    0x50154003400300305030907250182d0308031190a130100302c1115400c105e40e00610050350000da4a00d0141494011220041c00c01001c000d1028011448806030020a1072100104007142c1c007500300aa00203402055954042070300700b0b1030324601506040d0000080e040302c010050503510919890410400700001d400d09280813102c0510031601d0707465611020a2104401c407405c00042107403001c1d0030a06e03401480044407552002d00410007080800d1200030b0700403c80701d00a000c1424220343c0640707d00c06030f000c900d00d210111007401e421010200075460880300f0800c1500c0d642d58682c14410b61601030b90145026460300601d00240c14101b400c0200200e84c11469601243d06150741000080d100c0200c2c12640003880560041c2070b65000e104050080c2101001000c18070718180600025103030583c42000c00081c13401c1c10a4194481c080905540f198088045541d004186800e6540030307840407019410002200b00841016010790120304643d01032101200601c20401402401c0e021401042c111038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 829720008 1250 829718758 829718783
    0xa06050a062402030d09110f220b03070b04030c0806070203120103061d0601060905040b01050c190212010e070302041b0e010e040209041a04140c07031202160501060501030c030603 79
    0x140c0d4a00c1d0491144846441500d24003101c0c1c05c5414180d441c041000e1b151400c0c032886c40c90305454180b80344804000140d5075200c0d07451302d881c00c21014015242440a106031a94807a03011580e0522981c40038000f009040e40c0c440b600c0e424a0502c2c00198062002a8030402020a04c2c82d4000029140481c40360895160242e085a4600019007092407044424032a41c00114030461024042180030702103580da958170131380c585010041980c04400c05503041c010100300c62051600d02051040303415000110755001c0c10000d2010810908200050796180d5213013600a001500d40452110100ca000b01e40c24011190500301003040c0010442e90000440c0c062003000f656940208010030403080002c5c00142400c81850104041c0c582048006040c46031803101d84104e4a042e20400140f28051b003a1001c2e00d11f40a0045401841880380180030301845a800104440903501100e15100e40c007410b11003d4042460054041c0415001c1c03240401e040522141c8218420300c01e90341100c1c2c000300e103207050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 829721258 1250 829720008 829720049
    0x606081b16120c02030601090e1b1c060e1005070e10090914190c08040f0507050a080618030a020d0509241809010b27120a06050a06 58
    0x10380c1d01030450a9540c098480c9140046051154015103440154890001203225481094200308058105001451030a40e2501e02401d0018840d806800140789100d410b1000000180040368140c1c54203a440f508141d503c01006215000706890340c2c0884202ca00c0d0500b40342c940401e0b86c9003118041e0010344001d142c1e080c140340131008401c0401c1d4034140f840c2c145850b040038030180c65440c459034003650254402c0c040200361303d0141c42c00803500c0f82ca0800007000041d100400d6140d014102400c2c0c509006c81d190b051010500000004000082070000015030b03c0d4440c0c0d890301000c031885c1500c40c41d01405000509004011a100090b00394054525205814010349054000100e100d8004a900406003000c0345104400d02c0c46043c400c407042e40714000240c4100c2c030384010003030050040300788500410030090356506440700c4031107900360b542e2070102c400404540500c0f038a50030340c0e0100c02e41c2c91183c40c20401041e20488140115014051640c6280188041e20308038845c404140c202c2d903151030039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 829722508 1250 829721258 829721311
    0x2010806210d0f0207120b060d0326011e06090b0706090b070c0210020102130e0915010e07090609080a0602210c0405040b0108100b0a020703140d03060608 68
    0x2141d00442800302007240030105401e140c480480b8103140070500391110543d40c01d80402a50740101071002e4191044c4105070794003109143e000d840c142c02109441504130800d4010540841050508840e80d60882c4100d1001481c2500a10403d9000580e204154044045200301203090710010744402851030714103201003407c1c0d0300170203080da0a07560b075601250000701d10660090190f08940d4419080c0e001d0350040001644407003040e5821744e803042028030314000701e550444040710038000c241d0b81d07680e0f8ac10100500784500494003100c5604440008510014050380c1d41d0300555099407502c148a4a40900340d480140c20f00440c51b050340000e03481400140c0b180c005004015001010301b00c2c480030070107140c3d0707032000c103a90400030120040380a1005082500c22007185c94001d20b4850520305021000984100070390166004c10300001940f4401759008021950003180d0091500c2480e460203030103592030358050a00000028200040010080e22901e6403601543e001060200f090500d50203460 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 829723758 1250 829722508 829722529
    0x90f130207150e0607090e010b0d0908030a0f0b03030c06040b04110d121205060d0f03020c03070306020705060f040312020d1e020d050c0a09060e0f0a0b040806090a02010806 76
    0x220540c0800803032000a061655079400800315110104800584001c06801c0200c010321480401c822081c08101c43c491a406c514115001d00b1403060b9540082d0440307030050003c462014191070000003c2c03050841850703000500d1061001c108200c07c014007001c141d204c0c41940c600400a45c80203000c900410102e81c07010303400a20540450350345004c0800450b0400138001c030252a03100c107207030702703442e00079004554032004c0b45035034004000350324207100083e80181c401d840c042e02080c991521b600405000300404220f140b0010308130341c1d606599240200195004100c1202d071400707501e010a00442e003003004580102d034541c96540004180500203030007504030041c07070016285c444c08504008202541c1c1201000380c0d4a0303003d80d0b1001100040c8003a0f603005040400a0041042405045940312400d04281c0320f03e4a0456680c2c6400301c001146207810110540c2e0001a2520000c1c04003030401c010011a070080003600d0050f9506003105484544008002c2d0200e41d1401c0016070b40d142c52100d29 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 829725008 1250 829723758 829723789
    0x60c0c0a03080a0e0f07080d0207030c0e060409050f0c1801080718090b0403050712020f0705060a050c1221060d060b040e0105090303010906120f0303021c1b0e06090f 73
    0x50040e094601301d034030300341c8812608000e50300021340602218505100751a003d49082c0000c1407c14510307901c1d01d442c00e1003403041c2c4207003803000c0c8007244403540c0350b4005840003034014048810085a42000c140c90b12409404240714a0f24a1820150310106000107412070b403540e0050220203103403059506c2801c3c521001c8426255407111000d0011f40d02c201c041e4010741c040ea54842d1282c141c1d10b44003c2040f0715030380e01c4080d540201c0c10100c0040d0005080d90943c0c0042d1296a02c80d05031800c01d4406001c3c150050005002e05400102c41204175800750180a5200d10b0324010020941e844d100d00c0441643c031990468842d0b00700c4408101c443d0003243c85002e000c2c00c0080d6802c11031210900310b03075083d14072460a40000004014510740360007880050b0000c0d410304282c001d03882d6aa10702000500800509241d0080340c2d000d40c000b1a0105450401344504051080c0d168105469000410344210f007404500e8800440301c803030030704c142a81d510700302c0030b4176041e01da400d00002c02a04150a41a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 829726258 1250 829725008 829725011
    0x10050d05030d090506150d0b1807080109080a090b04061b0201050d0c0804060506040b090f1506160302192a0b0f04150e211903050903060c0c0a03080a 66
    0x4600502c1900d00c0f411039038900035405490035040194640550703c100c105868403801ca40132a10b4045140c03180c0880d0060f4040c08409078501030318a80a0a1003090b91090180e03501e001000b030180403500b00107105950859403100d90b00798032800c00301c0c00750140f4091000064501d035a101c1d028a5511404000c00740141011814203580788201415601e205403100d00140d03005042c44100b1519000e0144c21070ba0865060140b11400e5000c40c0458500604ca00da038100948082204045248440c0c0a0007001410a07981d503454240040f004804001f403c030010701c03545011114249030481c21041190f072050b50f03c41c030408040f24401140c2280d07596000010296840007402d0f441c050020031a140410340101d88031441c110300040c00340c20100790303030040c015180010700c0945d9580d41c810710b0880c40815181401211400c02c40d14150345200540d040c00c40c0013143d10b0030300d5040406030050000840440e00c0a58500e025019140102c100348009a8131600c620000203008412041d4400b20280e030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 829727508 1250 829726258 829726267
    0xf090103051e10060b0a1701060210050606070812100e010b0a03150b030702161409040b0c220312020c1e0415030f0512040503070b0901050d0e0606100810050d0503 72
    0xa07407804c40d001da5000d142c5d40c41002500c0d10000b80c1020154041c9606d8240c80785403507150100c00307900d500c0c41810942e40d00c1da40d0f2002914a43e907110135a4012600181c9068890504407802100c11000307030b450750309010060100090890b48c000181d8141c80ca8090890705004007042c080e4060b00542c0c0c96180c1d602160140490b10504180c00303035200d02d0040d03008100031181012041041c091a420105a000c001001c40c14240c5640c0c00c800d4000e81c0c440c00c80601640c9101c1501d405000d0031081a04640700b11102c0081074082d1602242a01c0c050142203015008580c001e91b42d9a204149454006c1c0c4102c10701c2c80c15031030190600031904406800490100180300610301034080c030350021035004905501800a020303080004140017000e01c03a1042c07600342480c00181d6070b50605d11803414031040000e541c1c0c0599206006a4540050402c070a0043e006030034405d40d00c0306011200302d03018080302d11403010240d103e0f01d0914006e88c0d40e00403040300c0606000c14441e0640301c2f000d00341c1d0706100400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 829728758 1250 829727508 829727533
    0x1b030f060f16090b040506160c030b0f0106051215030106030f050d030b060a0504050904020112020c011a011412091501180f060e0f07111b0f090103051e 67
    0x507849200441034208841c5008903480c4800740c00d510040080148007481031184201a00c100c4081e600202e07481e58a6418840707070b100d410010100002c0c0010082c01c0700008200c0c68a013818020f03040e0702000c91103a03884e001e04546070b00611441c5040e189400010075903104e807017841d0150005001d00041403494990300c40c08640c010450046032103074020101000e085a01d031250809000c0129003e901e40803203500003e00034000d07800741d1841041c07044045011680076a96110702e11200750130642d12019040c55003030007001007844940d00320282507007810556100e0800c42e0303480081e0b030b0055804c0480cc42c814155610f0024400d82451080079804011003609416080c02022100d0303500c0362145000f2400e0f0113440349041802c40075814600103110010b000b04406030b108540c01c1e186121a580c50b0360031034070540e801404a000c0d001e488110580010080d800c01003c080c281d48504281d100e810501c00807000901c0003030507a40000500100310100d151480d9260801c0e00c0480d0b10480484 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 829730008 1250 829728758 829728763
    0x2010804080c030721170f0a0b090408120a060b0417010908130609050a0e0f2809021c111c0210080411010201091709060708030a140a0e1b030f 63
    0x88003900c4841d00c50121821003111010940360fa45681c0c45d00794400c08001b8000301c102c18000d001c041d001610403000030407603c1e080e0b0001c000044000c0000925003850309160280c1c0d802121121044800280011500a0349010f590221000054400c0c909850079030307082440c40514120300015500c520380c8601003441c00000c0c0140300b00b00541410701d0744c0b41c0400900150400c0c0c3c80b95000381c84445c400c02c48003d818551030391004440c00c01d181540d44d615082140042404540004a00c1903417041800c1c400c50b50160450a1081c1d50a0000012030750790440c1f80d041c1c8a100404400c2c40380e40c00e2900c0e040c101400c11441240605000d40c406241e4001080743c480285200300058402e01000305002c40722009260300300d4280000c1000000c1a00c1d03e0f60840810021040d0205001866000703903200c0800300c13126203420008858030b900f00500000080c0c02c181801c1440b0711050b10102d00c06040501c17904e41c2c0071110304001c10034107a02094403800c641039054480e505025484084071718000a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 829731258 1250 829730008 829730017
    0x180f0d0605011d040201050d0209031e03041409060d17160503120705070203060f09070e0118050601051306030507030617150a020a080612010608030a031e0b010c02010804080c03 78
    0x40d4408600c0c2d6040240345560682c040c41d154040302c1c3c001d001c0c840540d0b009011241c00d07140b086d03c00b594a0301c11201007494003524601b240c080245904901d0707080000480900203480f0341e0703106094070804003002c2021401e030507907803582d1020110034000d00103602d81c906005880c54450110342411b00020301d60074007082d40081a601c5410000f5460b4504405a607140d41c440300509100b400e10196801295807000002d0103091581b840710b0100f00c03071130002c0100300c004080100740c4a000d5038440f0440b1120303403c045124640d290402c800708180b98092000d85643c4485840c16286091504004402a28010700440c040c1a0f41d0980414001541e1a1804d406000304006000030407055010401401d801810390203a5803060003031aa000d984461115040704d03040351030b0f642101c034503841980140080d50121140e80b10000301c2c40b080c2ca80580203000d150041025110f000401c140d100f10a03a07003402c0170b0a000821811014005600a92480e5049405210801d00703003110300c0c1a03140765600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 829732508 1250 829731258 829731263
    0x1b011107050d090f24051b03090316061e0c060c020f0601060e030a03080604141f0503030f0405101806031505030109031e03090506130302010e070b180f0d 68
    0x903248411142d9003080b036140c000c28102c5200ca50b05854008103000e2810040c0405903581401d000c072510a40c0b040c02030320b4298180004c2030440e42c1000215036600d520a04006010b402145040c003042409601075200311040c0d41c4401403900c07051000c52203050304000014041c00821105030b408a04c0300c0c4220f490020b001d8006014200d5050001868014144e00600802c2112075006510340ca001c2603400c112036060070010a252940c0380014050300c0e03a1b41c0705000c1c13444102d0811821589842c1c08000401c200490341c40d900f07440b9000c1c1512442010005000c0300c4042104001c60b040580040640030707224075107400d90119000300102e071188541e01600c0003a443e54010085841c030060244000c0c94110003c010120031036802070f110306016581c10305022006c06810603900d000380c03c005612940001543c4040ca800d980140c0c295400010603001986030000300c3e207101c14000740e0042600c4940c43d2460a0041e402400c002c06003805140c0b075084894025100c9164a0f1541c02c00511403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 829733758 1250 829732508 829732513
    0x110601090617010605061902070e0f040308150d020d0317010807140d1a060a120515060d03090b092202181906030f110a0e01120e031b01110705 63
    0x38030b0312801c03002002c240d100d402001d0749040010819640d07000c08030384025045138511400c81550038410303800d01d007940d400176107940322130000c02c0b4120782506155841603209466101c199141d084489800c25000341c5a0b54011b81c0400c2e400c8013500d03000304030b904c16600c24508a1289802d0994140e9041020f07400120640d025403014041940c0640e00c0241154003590350203410300840d00c034048009500f140700040104840c0c08600c082d01c03004110310141000600401420b82d09143c09a83c0c0c903481d03004480da02301c4c4e6001103046464941d43c3c2001558266460341ca203036060014152041e405030880076484000100f188130340c1200d4155004c0300d90a002001038440d40c400110b2018150043c00040c403814100072915054600c407070650098942d00c0c0390014810114680071002403901c450788010700c04d00803c01204079948124020310103c0203a84240c03210075060325074000d880c083c440401558009114201c8500d420f80032501440c107040d000802c6002c00f03500b4a2140b40e20518083d60580c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 829735008 1250 829733758 829733771
    0x9050601080d020f1213050303040e190b090711031c09110612070c05070e040b07031103150d0f0b251715040b03070906050f030c01020a1211060109 65
    0x40c0e10502c44000146281c1c0041e01120307082d00d10603900d4202903062441803000c0407a100a01c3c00c1072400300c00140c00e000c1d00300c9076180d84920180321410012203080c95490054128540f02c0c42c000d0040325890a401b400f1011540c9070105c0c00c1c3c41c00034580000000c00c0c801881502528888000c1180d41c280507800b0008841c001c906110040c48240040a401204200400c1406962072501d4a80c401c0940c5088400d40b0030380c1c980381d0306106559100c0340e04a840303070040c4800d01403c03070603050040380c41d9201040700c040c2d00d11160f1114001112500110303040e0381b0803038855003003200384200341c0380c40750594920700803803030380c401040c58000d860310000d414002e5440d05008941350a118030b03a140900341981003c4140e804481918802029025144003102c0400e109407519008460300e450018203840748140c452014100510300e0b03118561040514205400300c0b414085240d60003030106030f01a03d1150200d4544610354040e080140042144c02c2e404402200418400640070705485480401c08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 829736258 1250 829735008 829735019
    0x20c100f0e0c060a271208192d0504030f031116030f080a030f1a0102011104050f01050304050a080a0f08151311040504050a060303021203100504020d0f09050601 71
    0x1040c95450079103010b0202005413541c100c1e001051558500c81c1042560940d801c02240d002d200422544041c1d166143d00c00340808000c0580090328500381e103265000e401f01c0146000300c41585448039809000010405c041401032143c8202c01485c80c0d00c1c0c00c0070340c0307400c2d640d40d2500344980c078032a010b40000d24041103001c46120140b050032521080700c1c0c00c47c08083d085454040400140381b00051088c9030000d601e00b4200d00a070031040404030044403c104500000c0c883c03404d013011580344c40b80154a030001018010b90998161002d41d10301400f80114590f04d070005660517031010707006451078400d6244e0f0500203880039004004100455941c803000022031480544043c030050440003030900780308420490b50301c450084c4d03000c7c3c181c240f0001c038141540200ca0041803146800064010b400c020420940841a81050007101d10a5080b00c40d02c088142d0300181600007a01c0311840b440d0030710310800c150319298018001c5210140000621003420707590b0784049030205902261240c0005004014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 829737508 1250 829736258 829736263
    0x181101080f0c09040c0311030a09031107031a070216031b0e011202150c07060c020a0801051017010204120614090f0c04150e0c0301170a020112020c100f0e 68
    0x80080749250304420a05010039071514a0003144805800341d5900d0340d003450528445d0700950580604406e0040d41c90900340300c50ba0282101d40e005070040784100e01e0351250b0420014040c421690001c980da100400f0700118031a01107800751900341144508164036001b182046800ca00640c8260706507050301018070140026607006900010038401844010084846030f4240c8914055044540c1102070a07010b00040302401418100074062040c61004540c07590000701d0001d10f10f008035442c85016640d110124283c07501140c3c5440300c7c0030009402c210502c2540034103541401440b00241c00c1a45441400701d0071411140c06840d000e490700080391100710010022900009018060141209610304ac150b441c058005041c1c0981d0b91000203d04648885144201421224540040e40c0c00c0c580e50032080364100703009510240260030f003126044100040e145400b1035060311803440045090303d150000790040c68600740603000d920928800151984100f170f00060200800054880350129000d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 829738758 1250 829737508 829737511
    0x90f010f0b09060907120204080307050c0402071109090a06141f03021c051507021e0f0c01080a0b030d09060e010504180509030c0625020c0a031518110108 68
    0x5240e4030303261540480761901210700b40c1c0044240c2c3c1c2105691112441190034003e1804c078031095510100700441e48100100042003003134041c1b402c44201c030048104110491150040003442c40002e42c1030400182002001164008898001d03039100d00000d032241800d80b05012880e032140300344003040000c0140791840b0390320001000940780056034215030104920000387c21a02c1c03645c606e182c104108001c003c01c641c040c22603121004008506003100701941d11302c44141c40410060142001800366500002e0f50300720000300d00b000b07005400741c40e40191003000001c1c0032040030340e03154490703074101c2d0300c0802c120544004a5600c8240c0e05241020080c102d07000103100c541000000c1100300b20441010151001c40d48600c080040c0d280c4030b07404041d286200e0840680c1d03941c02580d04200202c82d40812440300c101e0040100c54000d02401e604a84880b54964000c0d800404030303000340082445d02480c0e0804010702603000800300c82030301c06604041c0d120382e03017154000c0540c0b040070b5107942e0020109 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 829740008 1250 829738758 829738781
    0x150d0501050f07080a2904020f0c07050f030307080301030602130305160e10051311070b040305031906052107260f0304060c0807020312070b04030311090f150c0303090f01 75
    0x70040c5000701844144201e0700c540c1e03591b6078040c4a0440b90900da841d41d0407100511180040681c0d64031a03109010f0300c840807881450311811840c50380d050340341404000c0356803140d8400c0710320b45140c2c00c40e55148001e401c150f441e529508201640407000500030042003424021100000c02040e00c0c02858001c40e61005080120300c0c111604100100e0f151044200c1c21628281d0780840d51000040d0090030314002c002003c0d1014078440240400d160b0040002d500400b010442100030642002d00201510124031400d500300303c64996140703100e5804450800b00008910039284259555019651600c0c00d2080c9d4116500414031004041c520400c1000030441000001d503007480e14000000d00803085064016042c06000140c40b82150f0f414040012404080c5d2403e58542c44a42080040410300f00c4e0124046407814015660700034035401034920b18680140880c0780300004005115208159100c0308140d00340074041649480c10503c081d602c5188002c00030903c1a6200d9046401e43e82e00e40fa11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 829741258 1250 829740008 829740011
    0x9030d02010c32040f030309080303240a050406180f0b010c140304080d0306030303050f01140d06090501020a050705070e010312030c0203130803210906150d0501050f07080a 76
    0xc0b400340340c202c2070b0101c0c800c00c19141d03550b691154402d44010b0b101a084860940000060042502c12000b10b82c4400d0740d0295a0b038070724080e140c98047d5502d101c1030b0f41180c1070190424090181e90490901140720b4070010381000c04290303581c1c0204082c0d450130341060303282001104d0903902d000c03000d218810170040001c00910050400100107491040e000707a000e0070400d19849101c5160004004440c0109615400c540d0390602c1c0300030040017807121780800c4001038144800300d45548c42c4950000d06aa04100000c0001500c0382c0820031a454408402c079403c98941003082c003c58000c2c40a06280c0d2046c1e11855542c90f86031401906190041e000102d031405040e0050001c5100035144100010050500240800c0e05010903842c5000300c0c422020003165051000c40c3c160f034044060f00c141d9900c0441003c1000e40900b50405c20101246c0460703103a4854400038609032a6409100c0603d0b2001c2d08890023000300e91100c80c00d440c1c0c00c9420f0b2002401c00c40621209941c000001a07000c1c840b500d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 829742508 1250 829741258 829741271
    0x60f07031a0a05041d0703030509120c15130b0f0301030c0f0b0306131d070306050106020f100f0b06030a020a0915080402010f050c4201061d0901090209030d0201 71
    0x781908110700442c4d000e255101030070107669505002020350031a02c001103810040c3d891a000b029a4170511000d8010300001800c0c03a80194001160324001400409107614a50f00450130103c0303410004080000a6580707500046190422008141c00c00144580d00c2d906d40c15030a21704038441003544540c0407205501801c0200c2c103010410340f50044002c4494444c0c00341090101e501514908035a050014101985803070a51000070b002000c0f00e100e6102400160303030703460090340c03180d40840310300308a034101d00c0380880d5052603503021070880344500c000040c601c04103101007080313500101c0340783d02003903800560f01c00070302d80001c0d011000f1b0103401d09620080e2000b04000b00361344809400241445100b48841000c3c5000381c098500c110403480c1160782c00303000c0f42c07885811140308118404a0400ca00514148603d2060900d00c02c2400c0c00d01c4003a81d6442d0880c00c45800c40b41001804044ca03c00a0ba40540e83e1b981d00b06e94002d0151540150311080d84400705804c011040004009680c58a03c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 829743758 1250 829742508 829742561
    0x809070b0c030403060504050a060606081e0910020c0316150f060303051209070810090b150907050a0e0d06050a0c03090209010b0f07060204030b0f010806011a031305060f0703 77
    0x81110f05881d8041e00200d0903880c4d901d0010b250444000340140b2003420280c02080b11741d8841c2c07803248140c40d0011030310541c2001c202d405804100984074040c40d5003100414844004841c1c0003048454a907070308991800000c003191356070f0114094801ca46100c510300d003910102200c6c1c0907001d81e841c2c01d000104001da02d1541d0292661080c0f46905540041110001d4410034007482000010b000400a503000c0e83e940a018400030420b160085030041420804107407034801d518802d100302d0704c019001102513101c652042c1c80c550005507a403020000c1d00c028940d01074542d04c030b4500f402e40c450304012a19092201002013940c0c62450550101483d01d680c401c050703a5142041b60440d00b24003001599120030b030f17441c168a841190b2003d000a800082d00204121100010501ca00c0348406c9081450343c0b00c58443d516070034280702d0070f869849004080c86036006110300858100c3d2201cad207165440d0040d0390f00d0b5400c04030704403060412001c0390000c002036650075001d02c109500b0380188402404000c03c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 829745008 1250 829743758 829743763
    0x30c0803131401050903070f050301060e160503101206090b060108100303050d02070f0f0302060c07050c0f0a12060e0d2109141204081b010e01081906060809070b0c 72
    0x184074500c0210b8504000ea42241d014000b1101d4004014065440d8180c440c0c440c0c2c405240540f241030300035072815a0000d0550440341005004a4500444621310240c0200c05c41c1c698002a1010b4280e960000d0300040703101010807400000c5115900118403d00075003072080340100f008254078140803101c0101300b0a020b1601d48141503c3e03050078466203070340d86104c82030005c1c021080c000740340280512005050003401560b204c0c40b58865800c0351600d036181c40d48800b842c0075643c0006e0450340541540030052400992405145501404168190755a440d1150f4180d4a203103043e18910380d20003180d00c0c03036441070102002e501490304184400c5108690b0b0340c0107600b106000b881c0d13a07a56482194007040015102c1c0940c0c10321220403203c0b0390b980c0810b0404254400e100d040f1451041c0310500c024002e000c208100061016110030145078254801500c1400008092041c1d204004192008030740d494890603016203440e03035902905191103200c6d80d180c45215000b10440840c20310801d40003c400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 829746258 1250 829745008 829745047
    0x14071203200f01020a03290a2304020d090204060602060105032d0f150109060b2a100c091a1606021c0507030b090f070e2107030c0803 59
    0x40400010156040c0e86a8180810201100c40b15400000e0040b040d41c0e15803c041d442c00e00b000100141c1180303008511001101b2a04d03510b8000710902010080c1e480e2000c9503c0e501c061052406100c1084540003030300700da110082c060b000581c2d07400319a0550416105403006420107000400751075061100095603503514000c80c0c144c82142c114907010010040d124241c03400164003c0712032a201c607035611034841c07035240e800d090320503406400061148030a004003802c540c540548c2c180f900100b4180f40201a400355a050107002000c0901d4181940810241c0d882c03929003500011040100c14004255030b00319400451801d60350b01c1a4103e90031840d0480701810b00203501d8081010042c07a0400290150100d420a9003501c4c0301403070303000101d64101c0d510841d06913504109002c1c5800c00c00030522030641c2c10343c0e443d0010400090a15005000b28009040000c1c40400740030f84248a0035031485d0580b89505582d013001008004108100b602003015000110180d410082d40b6042034065441c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 829747508 1250 829746258 829746287
    0xa06150e0f19090501060f030b070f0c0f1e0b0f0106230313052505100f0c0321020f0910230702010c08160507050a03051e07050d14071203 61
    0x2039850300c0004008095206d10014514607183d800c01d95501e082c1a86001c808840400100345880c2400030307040d01c01c4d0309004c41e040c1e0003481203805044585842000d103403407098080c51444044420b0004c540e43c3c18078280314000b2500114103a6040200051044078061740003104560803085020b400c50051050b80e5000240000080043c50107041a91800640c1d42e41e92030f9110420303032101d20000d03401014200b5240191500c401a80d00c000085034a4a45000c0c003100150054403181c000a124000c8491300141c050b4a80010256080c40035040745d0101e603c640110384001128402802e080e0810314404006042240354114040c4840441c0840e10901c3c1c2040701001511504581c080d082e18030415400c0f11501c0d840302c070b0004201800c50717400300c0103858500c035901d0005014541452840107699010014140c03486c5800300030310a0602d80f13688010f0307034090100c01107025141e05040510450040f0000102a1160007205082c0551360b000f104078154005004004681c11042d44c03902c144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 829748758 1250 829747508 829747511
    0xc06090a1503020702130e01050c070b15010509040c05040f06091214160608040215030702070603050907080a0318050609060702063a06080f0604140a06150e0f19 71
    0x3407075031021002803049403030080d0320004800d003128481d0010f40c070a480a02c0d401c8003c00094445401c0300d43e20b0301940d400100907004d01000140310344207041542107070000604140c4d080261070380c0001d00307851441c40080000f8501082c1003104590462082000b4859030404500c02428903c5030340041842c1c1034003a26480c40c00c000d480142e0010002c0d804940c40d034455421080d07466000091844c8015207040e840340c149501890754842043c021280a001d2a400038002945460801da02426008288130541c1c0104a0001440102400000d90301d51081e03540c680320031030030991201070401c0c030740000f4040c4070f0600000c58591203110454603a41c2d011a080c980310001c2d130380740c0600031006000b6450368120540305041101c2801440b54511090600b0a001494642840340c0c0d455082c100f41610f90390105d008100800c200c5402c801c0480100810345d003500045803107039415070b024040240c0601c02c2c518810002035072000714040c0c00440d402200d0140741040900080aa200f0b88074000199 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 829750008 1250 829748758 829748789
    0xa0c152007050901090c030e010e07050f1302040305010b1906050f07260901120902030c10090e0f0109060503010b0d0308090304030b0a09141c050f0c0105180c06090a 73
    0x1100100074060080600030034100896071102196000350511509040200c0e044c0400d8041d090010b0083c2c4201038084801001c1ca00e00d0007040000003c0250b0310141c000c00c0c0324204c1e030741c12406400104091409075001080c05c0c50040c050250074118060309a800508045c0240130960703002045170b40d2501c044900507210702c07050414088403011203003203042d55519048803480442c0030343d01074246003600340c0303c03491940d00342c07821507055402c019002903140d0401005c18034a842c2c040d400325585c1e4110300d8110040c135100c00d041500000c007500c0113050410600c004204002d0b00c1d000d941c0281c00203078024020924580cac0410070104800c5030060070300178cc0c0340005121900810a440003141c00ca058038510341482c0d170029000307014800c0c05540b0150801c03a11a810340f00058542030110700902c0c5c540105150620807102d541000046003990f9404010b1400038550900034140183d6005c45204c4280d0401c0403890310b00812101890f01507801801140d4980d0341d8419504200d03040100146201e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 829751258 1250 829750008 829750067
    0xe0d03120c050d0f0f110f1e090d050f0606060c030a08151801031502030402061b0a060504050609061b090609040204080106060c0b070c0b0a0905011d0a0c15 69
    0xd0240204881d900381c613201d45032422040c0758102e11141e112000d002c000030700d190358000801e446514040b8083c42c44c200071350001c40c000d880c05140c45540f04004141000540000900002140303c010344040d0f0008100303064044042c44002e800c40000ca56841c50b040c07003e05400e4a0340210082c5400348090400054a0b5103e4482c1c40d00c00214002c00c500710306040b5850380480d003082804180d444110500d0006044d001c0e510803a0301458008000505003070403200c0140b01c2a043d1003840e14240200d4000000003004e5000d641d00071480380c4080d021354038107403040301d00e0001300600555103d165030700c00c0003c041814044480f41c80090310201d564000e5400032401074455136014401c59840c1500008641d07500c40e880200403031040c00e82210b61384810100301d90399020701d4005011b5000320004100b6441083d8440c0045600c80c40010520740c002c096050199150000d100040307803c0800c9a50400403c002c1c100054000d0340796004802c0000080200b0703005483c0c943c4c0d070820b1201c08100e0385 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 829752508 1250 829751258 829751267
    0x122508071b02060f0c0105061203030f0a020c010c090302010e0a141309150c02120a0203300412030c080415240f050f240906040e0c09010e0d03120c 65
    0x99900039002c00d50b04d0400b0000210b07160b004058040d102d5103001c000c140e061521040140c500f542c250001c40c215120781c401143c0608018186800340c1c1e5007008540310030310b000e010301c0400c0906500c80d4401c5502c4d600015090b0828010f01e1481000d0240c2c060200b20000c500700382d007881040d6070030f50180142002c6a030050011002c040c100c0300b0386800028840d00290091030f0340e07050660036034498a0320b1118956550041110248c0581c10911145404202810214400d00141650b502c4040c3c01000345801c1c02906850135910241d0b0a0401c1e403c19801d402205180c00403031034520304625103500c40c03011030042c00c810710390800c1c1c032240140c103c0400700b140180c40e04e883c00d800c6580c140d90303803850302014403062103500d00441120b611000103140007003400551107034190050344d8041242c01000941c0c0d0102107003a030311140601c00801d994082c06c1007248a50400c9407244c0d5622403900002d40b6035041d449001307228205046400b00000d5110301e032102075401d90040400c4c012402c07901503c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 829753758 1250 829752508 829752557
    0x314060117071b020910052d0d0602091008061e2107030212060f15010503040f0822080f06160807030b0607201c020105090406050612250807 62
    0xa50052045c400d019030010641904401c44000711030101902c0e0840c03200c23247e041402c5165980188102c0044422030400e10780101c81c15114210051a08849100240401c0340d841c0070350b40010ba20004010b41414031500784550b04500d01c4201035003160031800985d1b11100c181407035100d0328580740000280402000303044080e40d03009040c02007620b00341d0075031039a4110454484602201e2400418000c42c1c05c4440400603072410f81d58540740d40c0c1c4680700c0100c02c9800103c04c641e401b9040003481c801d03103000c3c1c0480300f86071600041200a81e00d071045071441c000c01480d4611403504880d05105071083c0412880340b401025080a4800d551489000d8000b8141f4000c02504170360001040002c00212840c41000c0d100c00b800780e182c1c0080d00b01c092180e0a82c0d0400c07e00c800900c40d082010240d8000c001504003494010301c0419441c1d2243c01049180d042417010500640740c89040c41002d901c208802d80c0260103800e042c14004031a24401081b1600190555041c0800c0d107001100d207a8a049059 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 829755008 1250 829753758 829753763
    0x2250c050a06080f060904200123040f150507020d240e06130525050a060f080714070204020309010b19060207050a0503030d02090a12030314060117071b 67
    0x2401c225a5800d800380c0251001c49040c885600d00200240541c42c0c6128924011a0080e08820201c20001600d0603c5111001600d06125410000042480110030030840380440c40b040c0e00c0e01d480c607001c0102c0000d031094004c1c00e9090520b000120020741d02c1010303901c10b2a012100855078003c5400c211105044108000c00c40213010b460303a10310903a494103c010000d507210103d80c50365079800c1c9615082c41c0041001090341e0081900107842103c8020049a8545000014124035599400181c4c400c1000da00600c007203a211503800c00100d4000890741e50282c11400c00c0520224044a081c44500c110b0350002d2240da40440403868601c0e0940c481c2c071000388050319040503550f100a410f40c19481d184201e00c010300c10040007091a0a211550318115240600214288030601226001941211082a4204100c8200007540e000b0a25054403424026117000901c44161403850051090051506040c040356201040b8100b604c1c0650039480f45061a068121702900350302c0c18050400c12102 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 829756258 1250 829755008 829755019
    0xa09030513080c120c030a020111251e0e011e0b03100f0f050f040b150a050a0e0604080a060504050102161407090903050712090f090c03060902250c05 66
    0x10945501c0083d40701c6200e10111804465004807800c1c041d61050505103440d0541c04c660130760001940600c4c01207004448020941c3e08245000302a282c129600c4d00125400c0030941c1d804004861840380c09070044d240341107001d9402800c0407200c2c6d89920701840f901d40d00204414050b0711120818040b01c1c00f0780780d01d007051552400c2c1043c40100090044c001c5038181c070607111000510225501c040b0b421504042c041403028080715003004001c0c00c0f004a080d4000140400035102801a00300070724088249469241d203582c030414000380540d454199503802070400700410300001100040c0721940e1b903480400420306d647c0d01d1a08034064020f0b01e000c0c400d4420401c0500003004881c040d610f0060021404441a1955426018055070008400500071132000c100c41000700d00040c4107410b00003864140030700860b135a1061030810400c2680014001ca40ea020202d400c80e0b8140070701c000a00300b031202903082c2140024282403c40c140e0341d4214118001c00c903545d0030000c1d0300050794001c2800404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 829757508 1250 829756258 829756297
    0x210203061911040e100e060f01030506030f060906090115030f0b07031d070e0a02070b0609071704060e19022b0606030308070f051309020a201b0d0503030a090305 71
    0x1405900d01320650701c0040303401540700045400d0f081c5000f9540b04400041c42d400d5080707400c00040d0020308003e0082c5400d030240120700c01c2840707000c1199078040c1c14040300038030703051501a1010307084940322100010090394096040020070b00000c00d0740505600800c84440d10b450b640e02c02d03001418540076401090383c20705400711548030003254600071120518401e00b000d940d1408c3c00c00481c410100010807154508000c41d0960500343c01c1a0752240707403400c1000801c034000101c40e45400b01182c1c1150b030301c4e440b03041e00300001c0428003064a0341010030121035003201c410b500095012407441410b4412020394195108a1403440c0100118540c00060401c4025200d0900070071849040300e00300c0124110042c02d032410b51007407045400080c02c0c0c0400d0342c401e508144111010794000b4005204228035100041e0000c0390b0104100c06400c5904014449a01200741d54000040a81080d0b84910f500c0042e11000c140c0100403a64842c054540c0050000120f190607206800752250390341034004880d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 829758758 1250 829757508 829757519
    0x8070320011401091d0a03050c030409020403111c05121602090f07020106050621070329010809011a09040807050a200406030519081e0421020306191104 67
    0x1c81c2c070341a14000030b4107101c11001c0009107426440700c011a0380e0154410325002c0d020034416005880e448205c901582d00d456a00c891403401da8000750070030f07550384003186d005107680c1c545180c08081c1007541d840704480200c0103480b820f40b5004002035010f04110005110f0f02410301c0c907040049280d9000306a01901d007400020000c0700d40c000c5071300d40055884c0250104d140e10b44082a0340300c10219000c50a915a100b030888195039070080d0442e028151106000b40034071000700c051003040403034808182003010100d40010942e48012b00300186691412403c40450300415000c14a06c10741a501030b201c5403168541403600d40301c0c1400107080e9000ba0840c8104101180c0415000001c00e0600400e2181100e01000103d906c2840010096803216159183c00c0094481c8411500d001d01032160402c5540582800064040034104d20b14190009042c004001040500c000c41c00e010b4050ba8075101c1c0c0345c0d001c2582c40a01501001410303001c0d100c48002e00d1040c0d0024541c410000d070345151603030340d40c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 829760008 1250 829758758 829758791
    0x3050a0e0a110a1215150911090405010f0b220302060f0307090e0f0f100515040513020702060a050711060a030903020606030609030d020d11072d0807032001 69
    0x440a43c810342101100003200101c6554192800d500303c581600c2d0403030504030f0400213001c0d80501c0750f283da44c0d0040000e0029094854424508442c5110a43c0e1382490004c000032120b05070000b00040414550a2040368981d00c10746001e54100c10406248002c410078540c050100d680c002540440001000d141114441c800381d4011540e03078035000710254030786040f483c042c101100da00942c640c5840000c0c59684103000b1140d0083c4900c3e0300016100d40781c00c0400e07180c04d108484c02074100e100003406c01032424800303080744100460303802c114281012540014884e02c513030303c290810028007054103410700c04403413401040c1200007081e02c0d9440f0740c00b540240c05404481c1094001d40a004001099130802142107071090083c2d8001e9840e0104a49141e0000d40200311039000f010758419500b5042040b032401041418000d00542d031040e211b10006d010000076090b41e01071500b89001d5100300151055091310030700d580c10305103101050021a211800703240022808005c0358286520103041e07040c035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 829761258 1250 829760008 829760033
    0x906160209070e030c04240f06090503011505091f03060902090106030e07051009030206031e07020f2a060a08040303230103020d030504030516090606030506030c0103050a0e0a 77
    0x7529a007060b640d60000a0300c40f0803c1d030080e9a0540c0141c00780c11081d01c0c00f680106004010000c891101daa400c1078413056000464108000c0c1c01100101408003542244101d0000e04003100240264900b49140250040483c03254900500c988408145041241c210a1700d114021118403c1195a00e08165014149842c1c050b80076114070000031607190301c64094290900c910074000c043d81803078001809466006a020b074410403c002101000595646000754052a81c42620f987e45203512040955070f84005071801c015036000d6000b101e1100d501003200030300d4032a411079442c40301c1000c1607000654803104e83da255012600042030072140d90006022800742e8060380c0c040044008150000402c410000311584000c100c280040005180511348101118400d14046041a079280d031000d10f022501c00911080403082c82062107035000ca4421701004081c01e140501071400c246010903103902605074850b04060701e0b44001504c05080d41c00c8000c1404160b000c407003041450341020a1320108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 829762508 1250 829761258 829761263
    0x609110d050c0a1a0306221802042d0c020c1f080105010908100902060d0c020d080c0a05030a0c11070f03020913031e0905030a21090e060f0303090616 66
    0x8a003440819504e00300030b20102402c00d0140c42c2c610f16180c031303010000410303004250741a580e05544c101d40501106400b444044030781c1c2c2882400703501d42610400055070060702e110011001c4441070146000e5203411010070481c0d01710800110612021000c9081200114005800064013040c142c004520502c60988229035982c80720703050390300e80004680281c4980b040d801954000c0d048040d00100030350106600302d10080584d480c02039a4254441914949016100560802002103001d40d0b006802568010180c105041ca000721828004d031040c000030b048001c1595031403a1005a140c0160000810252480e086496255403081d400d901c201d502d0004038022000ca1000c181c2200c025482e2143c01a40b540360f84001da80405108060280001012020003410703e100286980741030182d040c0040c0101c115011304840700586118164101200f0410089071074401c00c02c11a80c4140306070000400c88000c4141600c1d400003a2940c055061007031351103500001c4506019000981d501d00003031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 829763758 1250 829762508 829762519
    0x10080d08091005011a0d0f151a0c0a0303050c0c0a0809130b0d0f08070b01260606010e0f030111030907030c0e040f02130e0d030f150b070609110d050c 66
    0x40142d10303505441c42071058042105400c5030700c1181e0403081d8017412114441d19000200f00e40529407200035282d140c1d080300405000b1600c10701842080001084200140c08100c5181001d1030503201e546500c52103024082581d19000b0800300790319441111b500c002000c0071200c82850701d00f0488050740c04484d00c20304c41e50042c2100081400c190280d1201500010012803020501d91140f0743d071441014402c8481150800c5280005809144090f0103800704400700326165046103c8124803820085641d0040d40c06401086026070303110fa50741304010815184c05503070000ca440841d001d00b41d42c4158840345030010081040e410ac00140c804110b81c0030b0110041d065035184800c60801c801520003900503a00c283c840300142c11b1901881c0d0a00180a00000d0080d00031003c040c2004a030109100010340c03542442144682d090103030400c20001001c004c0800c0340380a5440c0c1c00740c0700d00140101510384403030180302880746c170b41c00701000340700064000411558189030440d12202c0d40030000e840389 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 829765008 1250 829763758 829763773
    0x615050f121e0a080705062a18060c0307061a04140f06060f0f0d050f0705040302010e0301021624020f0315040603120c0b060603041a10080d0809 64
    0x285429049030100c06000c20140009404050034200561800402208940f06903041540060548002808020301501c050072150500e102250030901c2e13080e458180d040140440c0802403502c1da01115100032035609000d12400d0340034042142ca00807103d00082600003c5034003414010950040380843c405880c05400c2d80d000d1600b08421154050003076140024200006030281c00d502d1035041d01301d0b074010542d9003080c0302c002889007168000990549072150200d5a003030681c5e4180a12600316200444024407860404070041c1076000e0b40c0310281c1004140c14441d00141c90070f50440cbd0181030b00c5840d21124412a040414040c00c200101000c030300d403003c03c2e020f1490f0007442514039141c105041c15207591641d000c844006c0a40c0740c0c0880c1c0c4107558500c0040003030403582d124903407003016490304940c03030f0814100041702036002000e540c05890100100000074070b07000c0170002071984c00d240a2205071140c2c81b01b0200b4211a801c80d006500c5241c0442050a070001c03000d52052181500b00c0c0d103032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 829766258 1250 829765008 829765039
    0xc0606030d090e180706030605130c05160c0b0a050c100b0a1503151e0506070b0601110f06090303042916050904060902041e0b030a1107061505 63
    0x1188504000c140002d2070011061018040b02d401d8290045403000c81c800b1004801681d05013012510340c08140483d42c2c0311420002400c02c1b41e4000004200301404000d5417108440241c19841100400c107070754a1401a240c04000814546002400c621441c0340d451b9841c3c802c000e442584050f104030b40c280700d800c1ca211511103050244444900028140c0100c080c9801c04480a030651100b207041455200d401055151000468900c001c2855861410380d80c2000c000101c0002410b4110306d01841040081e1000310b0380c10b40d000760f0481c800b0303e0941c042900002016041450076030303071044240600028400340b0f14000018501645c05080c518100084813150110500321461120a55a080384000784140f403a482c110490f2074000c3c00d00307030302d0b080024000404444940d00508420356011600340001140d103146803107002d2003154801e001c0c03070810803590483d000003452451142e44516590b40c50065140030382d008640c4c4142d0034030050046080185146a080c001c0c0390254000203000d004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 829767508 1250 829766258 829766263
    0xf060b030a270609030c050a120e010207030503030f090f0f0303060901050a03211b0c031a060a0915050603070305040605220303090215070f03022a01080a09020a0b0c060603 76
    0x44040704031407950104036195203030f40103000b0044041d000e004c111076a80000c6541407285c208034a21881c1d00100108049401521052400d401241154860f003410301c0010710010440b0b400a441500c0380d00d0f0741d900c0b016000d1900c0c80b03500c441c007402d0080088604d080c0c1d200201450048404464880440e071300c2c0c20911094000390300c00541000c412120500d0303070203c140da9140002c2c042e460b2810b4440c035000c1001851040301e407400c440d2068064030400502c00c0001920b1506800e010107203c103424454006207880c80c590250115aa40c0c50481c01100111190100300a09001e00b11984a240005014004080454054039440d0801002440b044146070300100000309542071103825803520b0718100c0c01000c1d0741e03000704c0c0c00c0005599000041d80d10b04c001740081e98072692807890301b400d4a180080c01c1510020101030740b210f4440e4480d11f020455076059400c66001e103802c02d0107940d1201d0900c040e00c450070010f50407008010005c1803060610000307280e8200820704440c05501c4003014980e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 829768758 1250 829767508 829767551
    0x9060b0a0507020f1206011706060301060f06080a060906060c0318080706032304060209031e07120302150403021006050603010f1205030f0a050306040e0d140a030f060b030a 76
    0x8908220305001442c00d41e40d60004c0b80030141c40065a11802d4001900c0d00c00c0070307001010f0701042c2c00288a4404020488168413140030340c002e0195525000303d2003032014a0740590400d01140b01d0010700580300c41d520200082c1502101400103d0307403504094001245ca08054001409032184900e00c14a010010401c44410a00400d100b13843c180381240102080c07040c1c0c0301001160780032070b03c0049984500c180254040c900c0180d84000c40803c0503d4200c0d001440d814417040c41d810480240070108450b411200440007106292142d0b181c124140003055101034460601001404181a0300041486020540d4036082101da40c4076070401660b40402d01ca026070720081054140b0640015020b6500d10324070401c00c8038241010000f4040c41c0750440803030030001a03008020021140307010b01420700070610ba040600720002500e43c000740301c0441c410074520310100001350442071601c42d6003d4400480d582c2c404101043c0c0f40c042104950b8401d8620b041050309009000503020403015400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 829770008 1250 829768758 829768777
    0x11119020a0b070b0703021303020402030a0204171f0c0c0f05070f09110409020c1203072601081b0a0f080604050105090c1c0f0602070501051b0f04050d0503070501090c09060b 77
    0x740713507554800104902030f60211004d0390040940e18000001600d0380d00246000712140322025031654100b150540c00354061407a980c503c1d40c4a05140300c4100340343c01000300d07280c020000c041080191510705440007554800c000340602c11000707103802440030100e010030035940d40c0e203a04544140c1e112140020b5503400000480450010030081020441076402841300d040c2d080c1c156525400000100040b94208071200000703d0070300c0d00181e2080041030341c6004e0140183c002d00000c0c0d41020426540d80c8060082035805021082d0b5070313015540e41e02031541c0281007003062030345042d0302d50360b186407100000e0310110380f25030800004c50314034030011606020703881000e058200780c42c40e40300c9401081e03030034071b0f105079801482c98a16001042d10342c00240b031900e001d000007081a0900900075503510594603203c916600062109005056a0f03404a40445208880c2c1884500072401d01e40d09600c44c0100080032586005400c1c4c08000030000103004450a0280c00c00003143d841d1038281032440707001c181 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 829771258 1250 829770008 829770023
    0xe04030807021e251502100b030d0e0f04140c07050c0f0609010507060f18121d0d11190e01060c020a211731090b011119020a0b07 57
    0x700030385000c180a0003064000f0007031311280d10729554800b60307815030100010100107800c0505030302004003070b078091400c40c417100350001c0464452103103009003415203010085d80305140d41550007580740d44039001505c40c04010034032a07403030b400c0052458a999101c110704440502411401386494a4825141d003100031000c0c00340c134a051005e800440c3c540d80b2000e401c03582190741d912441c0c61008244951079800040c60545500e003131250400042c1c0303c50b031000035000c2011001d48188085240444244441c1007607a1081c0741d4855441c0907101e4145614846400105040c41005400128003c0c50225445904c402d2280e98844804031021444a040a5002f50040b00308010341c48401c0060404c200c40d00c1c491243c400c03074550b90740100ea9424038017510003c10100e403003002c40b003400d400f0880030803203004d91101051408000303810340c41c141e01c0380b0701404d9528102108664000d2501d0020740005d00107481d4000400c121b0740860059444c0181e0143c00c920502048642c545401c54801c02e401a09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 829772508 1250 829771258 829771273
    0xe0d140414090709170a03080f070f0e122a0a08030a2a06060602010506010c030c0b0a110c0f060105040908090904051014220f08030703060e04030807021e 68
    0x1c0c00101c1c080030f450207040007020700e00020b41c0f08480300c0344500d801918000e040288170310f0800400018001e4150348035080340200b4401001d0b00300c0c2e0030140900c09410450b140888020002d500c2800d40c2c0000c0005000354880107019100f61240110340d0604003400c559400e503550180466607000c1e020f082050f0307100308142944980143c43d940343d08036462241c080700800c450038258500d03000d05421110203840e01c8091001503020301902c1c0d8403010a1030054250000c80c4ca00609041032401d0142c0500c43c072001064210f14150002206c01c407400001c180d407002841201940e42101c2c20421a441c06135100210f018a0b09008200815400c040d186090200d040d0030803100c0d90000d001124036100721042e002003140107000f0340f120001410400108ad1410a006100c0481108040d0360242e000e11210000164000900300819030400c015985a50b5082c034198000d100d281c2042d403e881c1700804100c01c142d031040c40c0c07910500041d8261000e500e000a94070501c0062a160710445810042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 829773758 1250 829772508 829772549
    0x1b170424030b061605101a01030c0806030a080717070f1106040e0a0b0a08100608070e0405031e0d09060504050118171e030a0506030609061017100e0d1404 68
    0xd8001c62180076909885590541c3e442c0607088461002c00181c1f124101440b2501070741c0c0521030a05031b00d4050800c100c56192910020f500c81c81e81c0e40004080580125481c014401260070188410f0381280480f076407000d8034145403100215400c8102d4140c108492140d10030b0415070b090b2011181d01d50b0f4090300303036101c1011603406000d031581801e400c0b40c1d81020000c1c050301c04202d084c1e00c2c0220350320009076260801c02c0b024140380058000b0654031010100b8040054000421251481003140c0c1c5c0d280082c480080f540790070310414017a004070908002500040c844160300207030046200e000204058254282c00c100d010150f10009001214402e000300701e0174400400401c2a240c11b010842ca0109034001600c41c3c940094400003602c42e034601c100205400c0c01c008444d004051a0f00905840c03074080003800000b1080d0096440700b40003420418074071501002001048214610188420381d0650855075807440c2141803000000d250300c11285845148000301c50648448101c1e00c4070030346101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 829775008 1250 829773758 829773787
    0x522050901031401150603020306031e19140708060711010b01020705040f06030206040807060e0105072d050a140c0a0605090f06070b040c1d071b170424030b06 70
    0x801e2003c3c0d555280d40128224641440c4890301800040c0c80050700d90514005040ca048651002c50300d00030480f55110081000000b914805000382d1000840d0300b40b1140340114501c0300c0e245845509105840e00401d0315000030404c3e5101d0a1541d80c0c030200c2c842c1040215003a50500c0040c940960842c440a12445c200350304040701003264800040b0f2078a5995010500c40d40c000c1c1e00000c0306800c4070400340492a804002e140308a40240390060a00c10952141880c40d88180152240000a081c03505070000540d80301d0b803460740c0c008041e00c1c0c02d03281c1802c0031a4130501051111810303004194a00815103000e45e184000c1d07591559070036040038132400920800065201d1303041d81c480710500924002600c55901280b2541c0309012411695140168103200d001000c020301401c0403d2a042052056010200b003040c05005025010341d15003904200040b21050040c1c6141c0301000603000c40d1401c00c2c1c50140c041117950040d40e034a00340782000704a0895070f032891031a0307201200b04107100040d0090f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 829776258 1250 829775008 829775033
    0x3032001021306021e1513060b0d0605060103060f08070608060d171206010903110d150f06061206032312160212060103020a0b0c0a12052205090103 65
    0x1a600051420035880007000d800d00c016400780c0f0050b407002c01100044000781400743c45408102e0001c01c5283e044c04290040303c01e0040514240d1b039a45c2c5040030a00c0540e80051071041c801500c10507514556042150151208440841c04607042c030b8000611540a846000110b40a18001e452998140081240d0300c0402400040d4845070703e00b00c0388045041c001d6409040001c0072009681d81e07035409895074514100400050501c5000c0400304040307181040144034501d81101e10051a8545150495078005a01c01c50295941381c1510842d01903000d80c00602604c06030780340c1c0032210b1001e56001c0c05035804d43c00000c000300b10320349a15800040030a43d147e4051a0311044d2210400306821082007608031f21841d0880020044244040d424076681d01119a28040060a160b60541c0c0114514001610498410741c0c0002040445010248490074510382e01406100303101d421030754000c007544c0110340e04e01c0c035541000c1038040403901906a004110381c2c020b004843c0c1d41e0301c1c54580320600c604 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 829777508 1250 829776258 829776317
    0xa11060a031b0201020406140c0d0c0302011e0203190b101b061505010323160c140105040203060c1603050a0c060c0908100b01140c030c071814010303 66
    0x1c5900c2c441006020710660300e1400c1100703500041c0c449141010003444080106020411401c00700b055140380a00070840185441081c00c194402c61802d1038124018070300444980c80204c1e00002d852a00b00307403034000358001c00700d981d0000000a9070700703e0301c4100c849020300a503121621581003460207000e2115607000c0440400d80d00030907082911800150b031140c050240300b410018800340b05560301071040c40704080090161011080031521405416007025015103003050100100b548014410305ca8071030703956070050b03000c9428003070300b032a240c040e01064a0072031107406040e0010380881808002d480b415030136845400c0b04144241c40c1565280d00a000c12810850b804072400017040344c0c0c0c040c910060445130b075403007002440e002d112414941c881000c0b400b41030510480c6c3c00340380e0740003810a80040001d06860341d00c0c264040c000f4914480c4900348031003401070304400624503840000001c0e204003910002e1000480d0718040e02ca044000f400000c012072007200c3c0b80d00303815800d1141c0542c00c2c0d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 829778758 1250 829777508 829777511
    0x90b0a03121e080405120a230c0a0606090c1707120b0405090c100201230618040506040c1e1e0e2a030606090d05030d0510170a11060a03 60
    0x40001078003145040c01c0c604100491030241c1440308000e0201b0184212681c4403201c1030903d0300f171210042c0010548080004ca2450b00f82c0da02c58052105d20844424203100300465940d0b9815103012000703401248900d9110629001c0000070a9008416841810b4017400705041107544d44031080d1600d6011342c840490184d500c0740c4898280d1500d100f030b2402080380b071004000845003034041080c7e50002018840441e4140400803c0340005c0e4951b00e5010030104105d4602c03951114082000a89010390030050ba07003480e01484103000c8040b40301c901940c060240f00c0007146e140c00900c02200c810402c10222041011410018001d00507240e4580c41391a00c0c510340844d944801d04208403000342d0310720202e101111407034880c030031140d8940c140313a43c4030348816030641c41c100700081c002e40101152540520f084080b1801080340030b0084402c8080815020080c070b007007426001422158a003d86449a4101c3c03c050141c0040040c81015040e4015000c200803240b00040c8596500501c04c00020305 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 829780008 1250 829778758 829778777
    0x60b040b072f09060d12030917031f090903050d0203070342030b0f091609050a0c21020903031b0a260f130b0d0c020601090b0a0312 58
    0x9803240c0d1854250129544450307941d0000c01c404103e00c11001400203846028a00248000030b00300c0000d07016840d415040002c3c0d00c0d0494104219880000f020351421400c0000c20020042c0c88010700741c0c00a8a8010407414083d16041c0550403262440e20240110700e051103c0c2c40582025002554492010314000c2220301d2507a000e041c1c1c1e40402e032450086490a070034804207540001800c155801d46200f07885040c0d034519161184c3c0d0001c050100f000c5802d100d00002d29507230301000014803580b00c1c3d04111204a0755500e00e04000d000c1a15680c030700e130782000a0507205c0d6129014000c01402200001d4122010400e540e00c001c0d0320a07020160035010a20485140d4a6940408804500808003810900c0c901d45801c0a0400d40035192409202a4500c0c10443d0070040d0103507040c00c180310040070740d640c030111031b01a07241c9010340c072403012410001008100d4902070741003601c1c41b40709034088601c241d0300c6060032030070b903010b04000c5604446180004c001040c101e69003070b4032002003403c128860 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 829781258 1250 829780008 829780043
    0xb060a03080c060105100903110d0807020a0618090504081204240906060b0403080d050c13080c03011a0d060b0607050703140c030604020603040605250c05070504060b040b07 76
    0x1034002c08400001e42e080301c0c0c0108914146020390000d110490716000380b040341140c0d613121030080e030301101c04d02988601200301c2c2049845400c0320566078000305180580c80d941d80f00200f40d006140c00d82d1164640005002403011800d0103441d004d00c1d030044441d404d000d4034010468081c0c41c0280103840000301300d055003442580181035640404006000421000141d040600c1650100d0b440404402c000308000c2011030405030980d2aa00501c0001250b1620340b0340240340c981c011568a180c440513001c1c4005503c0e000080c00050211095009001e4000b100d100c40b00301e0507000100903049044c485c0f01c00d001a007a90b0000ca0940301c0280910b0900c83d05456003464075043e50800c4a20b4007084045003400d001c10000742c030036050704500071304c21840c20340c0c040351281c00003800042449032550046242500306511030301d80c99000305440300b070246650400408494a100080e162805216408101402c050150b41d05851035140e485203400e00e1305034244202e52000d8401c0c2d80b49011505a0703200d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 829782508 1250 829781258 829781273
    0x6070311120c0115080a03020309010807120606050c01050f0601090b070602070c080606190305121c050a020d0b0102070302030c091e0a06050f031605040203090102160b0103050d0212070b060a03 85
    0x1d80c0b1898500003d80400c503592400a0010140c2000b1441d80c01b610038000001c0e4000308844582c4004c0ca0940c4454a64503020b4030444040079004040d181171400100305542d014014001c60201d0384002c0c0002d4441647c50305001c44107580d600d0000d1100a010712684c0785980c02000202c1c07241800504d40b400b01d84840d41c29083c507410018190704030006000e50f603e850103200c040b400d00301c07000d2100a840d5a032206da5030316400038071011001c0042540d0007001c100e1185c804d5604034081c02444a0701e44024000000c2d0702c0f824540c07040c145000385002c069440000e0100035207501400038404200c4c04820000b5a080c0207010b401070b130280e021612161244543c0300c5001c1c41c0d1880000c1012424141001481518016064000c1c0d02c003060340e5485800707200f003410855905903801680c0b83c40f40318040c0e02900c0f400314804040e00549820004008028460604890140c0c0584618520784503081780c54806180e184400100e0601481c030110b4000da80140c1c10800013442171403003980d40d07507640c80c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 829783758 1250 829782508 829782517
    0xc112107120b011707050409142d0304030308060904020f0d1103070b0901050a0f23030901050108070b300403170906130b06040906050906070306140607031112 70
    0x5039048001e55800007045180c0c00c650780503156040019039a071500c5105290b89a07503910425124a0702c56001000f408401601d901006a0210940d010900910305054840c510306680c14041602440ea80c0600030002c01928141d0707925550300d182c82e03182c800800011384009001642e2040500540844aa481c40826622a481000d40e0115060076600b0141042816032200490380010005500c1c40d0303a0080481e510b03a18242043c120151aa103011141a516000b54444ca44900c200b40801503038090040e62040403076100a000981e00d03000c4c040c1d00c07849248501d18582c04103228408584c41c0401d800800500f10f04003082d034048018684032b071009810b0703d095020076014030a0070300a456894200b903000e805480200b00038140840c007046030b4031124101038070785285caa010030801c0e61550011904950045414481400c03c1c1c90070540320b8400b500c400011a00d81600010000c0d00d01c1000000ba45000744500c0c180000c83d00d0544a82400c010302c4236182c05050009402e90515a0180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 829785008 1250 829783758 829783769
    0xc060f181f030506010c0b06010507030320130f0b04030201051c050a051501090e190b09090f0d020c1c050309150901022107060c020a140c0906010c112107 68
    0xd818884820102a048450113000c460401c1840e5407001c0124204a0503550004400c2c039150340c0c0d406050804030010300da0906240003d144901240f100503581d0005045c00d50a9a2040e00c0d141d5030311f901030b0412023501e00c40c6201c00c200611007080558061405414503220340148035a03000003401d00c440456404407000d003c11681ea038117012880300a0150040c4641d0f00307081040c0b0103400c11000300f450745002004103001c0100b220503025680940e030082e04803010050a00681410f21100c190b880d01c68041400350301e0b203d81101904020f10010b140112035201410780e10314210014401d103028603115109680501c41000010728540312409048481000c080c0b9403a120712820000a00704000035061140446480c400b12100c62034000459002a900c0303440001d001000d42d109070f0400048000180081b2480007138080b2104004c6030040c50680e04560740001644e81c07000641b0384807000c250250a10a04a02444890400050314075400800b480d0345050141681040380c035160303040d04030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 829786258 1250 829785008 829785049
    0x40f0602030a030f0c1e0c06060b0702311109030a11091503061602010e030a093002190b0714060a020c100506150d0218030c060f18 58
    0x14544555414400c203181e040c0010800d02c1a09134500c1e0040040d0b2001194094081800086c0907005014044015041c0c0d40184c2c1840802d0396000660020f42102d40d0581c000d40000c0581d5035510a030010380306501020000440140c210801008000c0441d6404255492810005007055a07020802013003101c0c0303d80c400d50711201c1140280810864058140c45043e0303641e04030960a42e4020521a50041e0782650401d10b09030408070880c09402c03052104220b0f404001140600194041e03040002e4500760b4668400c10304c080c80c1000c406d43c14000081c1030f41800c0c4125840186044d444806450b28680d5000d20600d40320200e9260f503078000c94084607605209552080101028081c0300c1d1301021655045082000d00c029980d100d03214880031a1440d030f583c100181040d5075541100a41d40380d01ea075100c1e140c1400c4400d8400a50082e00d17480c010310308040c140e4582d0301d80029140181c80c0c000e04454240042c000d031403801a01708003e2010701c4c24103610700b08030340c1d250001c0c04030f00140c100c0740 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 829787508 1250 829786258 829786267
    0x1f02031b1c02240a06050402040314070f12060507020705040c0201020909060f0d0f0302030d11072a06050a05210708010b03041718040f05180304180b0303040f060203 73
    0x600030303030702410241490203542020190610b40c0a469124803100d5500c035030300c05442d9440d4807404000700550703000300c3e502601c00b203804000d02c14941581070840d0000c0301283d105a80b40c3c0c0a60101c1c80c014400c070020340c03041048090000342e03650009600f0410500480700100e856500040c1907506803000758005030760100b0b80020f14901703c1e50054009000303035850b603840c44c6001c02142c600d00d0120704c042c05000d0568550420140300b08211150b10001d000100a400401c40c184200c070b0340152429203041900c04032080b44d14044855200751814801c0e618000302d45090b000382c0c0c03603801c011089801d00500348241e45052080b415180140100c4006440d403614041c0b0000d08011b2040c0c200c044a00d0050007007100098240000e004051104450f042d12011748080c1c901c4180402d0710304035082824001c1d0540090321f550009030041414141c1038080b5040b084030980e036801144643c5041801011004207004110707402045000b0010301507a1030f0039114500030001020681c0010016400042d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 829788758 1250 829787508 829787533
    0x200402070501060602063702491404020103150e01030501052203020d0315210501240e070c02030a0311010f02090609330405031006051f02031b 63
    0x1400a1035040d1f1101040c2d0120302110500402e03206109842d52030b0560000315100b8031407018104406c0e80118600034212010b03003800d420b040e0030741c2880e41095040380b000d144240c0180740c000c040e103403034001c203e0704040c1d0344070f4004502908030001c4082d90780a040c0d1001c2002030b2030001081c080c1d400f40c0700200d000d0402103c07006075607400e484c80251001480d00f85900207a03010624401c00c40c81440e001c91011002e020a10811516500c07012403940d0710110855681d140007111180039015100802c600d0180f9000c5200311002c9100301c0c0000c0740e0840d0203000d440c2e5010b00180c0c00c4043c52800368449445030380880d152000c1c031441078000c07a00b000040000310409018040c482c4000b5241503013040040d20200e0003501410900502c2814100300810ba10020b00080300031303141d0b603040c443c01044249445502d19a005008090007409100202810048540613031011950044e1240f5a0046500c2c03500328500240000a402c50104200c010b1801c04080f51646000520801802e502d1500a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 829790008 1250 829788758 829788781
    0x19080f060601090e040605090309040207050d02120a090e0a18030512070f0804121e121401050303040b0d0b06040603061e061d0a12050a0b0903040320040207050106060206 75
    0x4154904001d400340341440704e07942c0d4241c0190869805000440e0300d8031001030a5042d030040074043da820510100b81c14081c00000220840d03c10100c3d02503c072505881540c01c001c43c0b16840c006404600090410800d0389101c480c0140d12048042c0000782c11901c10030042000c070040007050700080c0c00130030804581c0c40c46400d401c0c0c101105041480103070030002c80182025100410241a250300c0354400195240100c0081044a002d80700c0c0d05400c0550b0703c0082e20418212103070041c100e00e800f600d1000a13456000281c180c401c01030003141064580003c502160b03002c50007005032592075210300c1c00c0340d81340d1901a20144c0100d440200d0400d00b040d43c0c0280c0040003220b500c4100c8070b10002000740c241c00082c00c065803450300c16480c0b210303001400415204186684804508800d15a003401444804504888131a10a4210310038688454040d95581e0003140009406c02c01c001d80c1d000f03070700003402000c1c00c01000050b0000d428010252166404c44a5581c130510150300604200034850b00d19 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 829791258 1250 829790008 829790011
    0x41806050a0b0a1b0f02130507120b0a17030d0203040804090b090403090620030c0115080d0f0e01200c1201022a0102040f08012a081519080f06 63
    0x600581e1401c0200343c96005180c130030000250068503c05400a0052155614100942c03940180c0320101c0c032402070f6009802400101d841c940004c150007080400341d041070261503000c603401040907202508003060303404c0082076042c9a01d440d10040203601100e84050016511490084410640b0780d850101601d0a5600c503540c214440d920801c10030000075001030750705081e00c1c0a80f90480000203090055008100d60035000286031001003180100e00c001500080c51115148a000c4500c030390f180d003d555110210494080071444001d440001d10b886407021400c109014501422104964030300d0441d05201c9107002c0580d600101100e08003402c044802e0b034075482c0960000c5160819441c403030b124051407a2101020b001180c00000d881c0790b0b0940641b4040c180c8001c03160070315035880d9441d500a1505102c107030348100c0311300c120318408541004150003031443d076110001d15685003c10040400c0d40310007560b90100307440c1e08402144a4507038600300030f44605001040d8162114013064a403000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 829792508 1250 829791258 829791269
    0x3030c080402010503041212090605010f0501080108060c030705090414062b0312090204180b010609140105090d0c0f031502070f3e10080907060e06041806050a 70
    0x900d00107010040c2d91240490303501542000c400c0f541c031100d800c41140e0b00502103443c3c104060070041c2c0c2c0e03820b002c2d150b40158102c80c400025804840c0d6030b0001501c00d030400340f088880940041001900c490109001598005c1d5649481443d001c0340000007400c13101e1107000d190417403060504000c26814001c4400d65000c1240c2000d240444060a01074613905101100408208580c90242c903060ba803030300400d07040c41c1d0040c0188081d5001e00030414002c40044026240c031520b4400010300b05000b9001481500c0080721800020310081f001034507290722098449400115500d01c180101c0e50683da000d01a200c038501c101e900700d24501340400703100c3c491480070114500c1000032400041e02c503403a880200390301100e40302d041600804001079100c40c2075240d00030320704000d803100301400d074544102d558001c0c01c803151080e800f804002101c51000843d9020160760280c081440303194081d154100241e44024050b038601030300e8441d01d0303030300d210215064503825454040034402031402d004084003408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 829793758 1250 829792508 829792517
    0x19080c01080c1b101803140903190519030302090f01030b0907031104030803090a2306040308130c08100b0105070c05091005030f0c03162402072103030c 67
    0x6040318502c2541c4102c40d841140310b10180880d0310300312010b0000003c144084441005407108000300c100000c105280700b03c001600c0c82c0240f80441010308290b8498440240082000c0261000c0c0704c10f59101250040d02c0b1071189596030140d00750280340100703086100b581e0141e141c00368141840810080304800b1810f060400500c0142500c840300d8a60b80a45640790101d0180003070001180a842107410141244c0e00000c04c21803101000621603000520030340c4c210903401e46084207903112100000b600c0361150408000301e80801d01c1600c226030070011118410032840420364820003100295800210340d500444083e0043c01c0f5188200300e0112000c0c02c20520b4030702e40741c0e41c401c4184168000e0601c24986440411801d00f11080c500d0302925015007107a0b00500031070021691800c603000014842d1042c0800013180403003a003c1c1900302c0d0b2555045921840700b0010903c0b0030510100304004511400c01e00207828491203581001c03c01410301001100ca81900700102a15164001c040521 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 829795008 1250 829793758 829793761
    0x6120c0e19050306421309050607080c030a05040204111b06070f0207060507030504180b090a061a0304060b0a0b030a0510060f031d0d110c031518010b19080c0108 71
    0x2484410810407450359010607400400c0030884885d20100108840c0c1000491044600c441169480240f00b40e0159040301c00a41c2c84050442d0ad00300d04440080603c1c0c0c05101044060105401442d04188005c001280261203a0440c505c550002401410741402800c5080803e03a800d100882c0c0154462400d42c10701c8100400113580caa070507200f664100140007902509140c40395060f903014007900305480c4444a0007002e405e0150070001505845084428007180c803502a904c034200803960310301e01503040b48004003152a456000104240d515a48a2500c07001c55034805007500b0180403030314060f503101d040a0480200311400200303042c4120583c07040074403c00b900701c10b03c000351189034580442d443d0081e041d56281002c5052542140348540a0200700e2940c200031020103900c44c2100701c03103030030b2042010560755440300c8c800050030000c820302080808400155400c0061140c4002090b0441c01d0030218007044800998440b83c81c4a00340244038428061080d40750b4dc00c001d04e04941d45 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 829796258 1250 829795008 829795051
    0x10f0e0c06070b1e01030605430306090e0622030e090408120723040e0a050c0c0307120e010e03071e050a0b040611060106120c0e19050306 61
    0x1482604405440381c03203d8400107140c8072080c82401440103003c2c04401d41960349140c040084c0030207640242c1e034070600c0140d07100e01c4201100704001a100c141c1000744686c40065007107405042c1500c00e42c0401d600c884006c1400541801124010704a035001400c99103001000c50404200c01011488010180e1610f200441c2c0e02c1581d4030901d18007280e00e8501c1d03480d64904110544542190a9071091942c0200440c442e002010440c1201518026900c03402c1c800141c032003980f00f5400341941604080002c142c4500c6103a2246070301004043ca200d181c904242845443c41c4c112032011945511501c0e03000807065400304030801c0b20307482800c04100301c10141c030019031290f81900586422381c0904030b80c148440240c0d20300500504003c1c1514007165100c01c0349840d41e0b07002d4011000411001040b445920100040c0541200d200e40d42e1000321131606118800a025140c00e501c0411041d07403020482540c4e0500c1038011030440d03c0795010010301c2c1c54180f40c00d0500040a9403007504990441082 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 829797508 1250 829796258 829796269
    0x90405011d06100e03150405100207051902030304030c08010b1806130e0c0a030311062505090d060c03140105040b010e091b040806041b12060506040b04020c010f0e0c 73
    0x810410858011840180b040f000712092020500f215915109000b0003940c00f00d0444c030030b10700490003407060315000c10082e10803000340c1c420a803004040da4820940b10300244e02500781da645091008040d20b01e02547c81d110400310085a4104101c0d40e5500d41c5070390b0030740c40c0280845003900c0607a8001c1c0150714103480010310b2200d500c8940400036413180803503405803005105c08003174114000c0c1007078070880d11b9040041c40741180d1501b080d4148208008200310720f5142c13140010740410040800c80006a0302c03000c59172a040010703116006665408010001915405080c0d44010340b42d4000507448142904e0180e45101a80524000c070301e00101c030031030b50340e111000294501041e41d284100c1d8440c1c0e1104413903049402a804038080b004580400c2001e004100c083c0518041e0365104080004c0c82039240c11528184640c00d00c0f405600d499800103962070300420340c0700b00c0080000a4400f40c141c00700d4141d0340590b0091589035541c40c01011107040a120390103000b4420340042c007200c4500d001149 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 829798758 1250 829797508 829797511
    0xf03040e1f05310b0306093004030c2d08030a0327062316030f20090a0603090c030803101203050405010e0621060301021e090405011d 59
    0x28002e003120085030480101040c00300d0783d071210f58455004a4070520881200078a001e82c2054800e000304004582c8200d8001000000c250344070300d03407841c0f003040828a0012541030119417480341805000001c08030f20915001001014003003010888988030030707104c80017034004114400e070074440d8580612040fa800010f0700c02038407040c20009101c10303440d10303541000c00203120803a1034403c5244d00401048402d401400d11032036089010400542c001c140e40c0c90440040740c0070440c3d5045004040c0c8990f11a80001015035510400018400da44010f2000c0000c440084e2800340b8500050880c00345c10403007031000040015250420040056564801c165040c1307110113002e51744040302103562400f0440d110360041250444021703141215140143c8107030800d00c2000c0c0456141c2c007000d4480d050101c1214030100651180b0101c0b24040c3d84040220302001d0715003601590301303108500702542c0426010403030301074048070b4544400c0200100400c1e9101600a032110007d040c0c040c50150141a042c01d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 829800008 1250 829798758 829798769
    0x1d0402031902090109081015230607060e060906040203160608011a041214010b0f1305040302120a12150b0a05070516140a1a090118080f03040e1f 64
    0x540d0321803c80d0012141040a41c120404501034082c0b06d600507a4103501c0314020001d5030910603515640c408080760088e142c480a0707201130070750402c041080d1815100501a084c41030740c000030448160358285141c00c40c04c81d000e90f6154069000d11044d841d04010000f031440c07a04400348540303070a02d0700c000c0c224a010310564622400f00d403450f000201820381640c0113400151280a0a40442d0820900c43d801280f1030003029442d2004110b0f40f418030140c1044000009080404e42568644030600200360050043c0e0440c01101082c5000c8003030710380180041000c598494048000740099601160314111000c00d07906025081000589420401c2d2000c0f050f0900302a41c0703504a5050441c00c0402c41c04417000644913995020a6101c5a601540c01d4414242d44110b0300b59218103501d03045110302080c02c000800d0a000508056210702e60483d4036800b401003070a501a03880440500d0404c200d120a501a040440e06000c6170710700c021615440409069032208900080c2d5050a00d41e100307006c0c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 829801258 1250 829800008 829800011
    0xd050309011116060b181330180f0506070302190f050d0207050109050f06120907030b1b1804020c120301062006180f0105071d04020319 60
    0x50a69500b07500c10510541003060003a52801c0480900601d041d9640c8221041407400c240c001450401c0c05420b40481ea00440100d880d07141c06920b24851024080105c40343c81d41d0540200c47e2400e1600d0424181007410385030700220901200c0a0000c00024102190b001c60710701d8104071a44001c40303941c0441d2425120701380c1e00c410b5414201d04102c00b0004440c20800f401009004101c42c80c0204103909001c1e400351078140140c0c0f4012a1951003a10500d030001b8240c0320b00b07100501d0315000b100d041001c000c020a00d0117500d03440e0085203040c111a03054140d00014410000d1090540c00c0d01d501243e00c240010740d140c20030102003031358004c1c13102c2020f0b02d14901083c1d003000e849960454502031403900c05c41e5005160340d903480b02150300034014a000222002014450705854502400c03c040445024049591b1507003406041a2050a4160500c0c861040c0d42540030a00784920360240c1740e541e4481056090303030035010502e105048801805644100304114413620100106030942199110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 829802508 1250 829801258 829801261
    0xa081e01110306060f0705160303030f0e0c10110a0605040209090303040b0a0c030b281707121e060902010320090103241d100305151e010b07030806120d0503 69
    0x4170700c00741780102d02d0010150310800780d0300340104407081152002c480c860f640501c1030a09a00c540000d6800702500901706510021100710140b8211040300c41c2c1c1c00451410b10b50710702080e501c00380f0b45507a44609a800030703650303000d110641c01c01d601303519030200d040c500031480c4d41455558400f80d03001c000e0590010f0781e42c0d2404d071084140700c0d42201c00300703c100510000881d0440111402882c00007440c0900b1000c2105000441c00b807500e034000c01004a48016000281c5407143d01100e003a00e03801c0848000c1000c010380c1210f200c40051804080c0d000740c2001030601941e10000d0112110354a001d41040121024a8291000740c2c00722140701d202882c0c08180c0f180040e08850a2004c115400703604211100004141410402c0906212515954580c0c019448140d940440d00005000160070780c0c004072840a19141c81c400030039084110b020746e92610000c40c41c040802d10a082e0404040c402000810005240e070100245421220031911103101c483c5400380240d880e00409a140c0c18002d003c170 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 829803758 1250 829802508 829802527
    0x1103030403080c030c1e030904050c0c0319020f060f0112020310110702030111030702071e0308040b070516053d0c1a2a090a081e0111030606 62
    0x4240c600841c1d100c000e05031650381c1d0030107440c0c0b01d40010482c40c440d803050906e280c1504564080c2c01869601c000069441c05660405000103400010f00d0f005814404000e110340821007040140100e5003d8020200e407222000030090404042d8052040e0941c0107006101c40b6407a6641200d044442c0f8101e64a00081d47d80f0100c0d04043c034200300168418600884840c9690710380005110a910071002048000c0c021100400076010540e0f000c0700607404203105110341c04440c1020003015080c8804244030598a549841403580300c2d411500404201041500c1006800c004d003507410b6902c050301e010b605003883c021501c0d203401d13200b00f000400d85030703030201000ca035181d0b00dc10343c08212141c4041eaa00d041100c05802c21607120790440380070a504e211450701c0103030300044e103004000c9410380310382d1540310701c040b24400c00301b030700748034607404c1d42004a115940d0300d01c0400b034014100040030348001440e5500303100e28011011041d4040364101940380081a40c00c508885c1e22070011101140c40f100000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 829805008 1250 829803758 829803763
    0x92301030b1c0c1a043017040905010b0304030c11010504090f0501031406070c020d140f010606020c060f09090a0204030206030408032706041103010e15010510080c071103 75
    0x35168901030540034100d000038880a0310140e8280c4e050404201d0408000701001da40510441c4900c4040750340c41516624000100783d00401e480e0b0111a000510200c66202d41410001c0807840c82c1409000007010448151702d801342d240140000d0200d903046180c507840140c46010340c1c2600410490301119042d065a0141060b00c000d008440001c020f0703034407100c254100801d020f0005440c800d00030900f003171043d0300000c1e041d032080b0b040340d90700b8040381066420302c641c0d4101400115a40d000f00e528001007030404000385450944220004034010b45882d401034140402c045903030b030007014200402500001d40070102c405242c4103440741d5410740e0751090b00d07100a000383d401c003d40c00f46000080c8018010b280000d1800342402e903040120340c0600a800044a017080200c0e0411600f113280000d000c16a498100880c00c100a40045980512030495034100320301c1c17030041e001c0d49581138010b114900b0880e1000078000f215041c403091609000c0d003202c10601a1080084c0308544108001030340340c506 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 829806258 1250 829805008 829805029
    0x1202040b04060503030a080a0e07080c0f03060c07060207063e040b18060702030109030f08070c0c03020108041a0a06031a0903030c0310030816290a0905010b1807092301030b 76
    0x58260ad203480d03103440e146502c410340030f1820351003000f484038000024640403030414040c80c0700001d010300d00852a5a482c010350001907003581c03039030f65a0307502c9026403c140c11603040482d045400458030040321180320003107107041c0081013808036003400f0500405482204440318030003c034208840030510b001c00030340d070383c41403442c02501075007803403010001c040c0c00414a03a18035005490f810b80d15500e443d0121000d03000800080e0416114440400141d402018070a8000313000c3c01070740f4140040c5000f0860485815101c910002e66204810014400501451254101d9040ca10015400c248404980e41d01004e0452145024000301054443c98400e6801c6c00079070340b10790365a456940350304221110b90b91989007035a03007803035001c80013403d0352502c9a40e100126090755540c100ba1529207404c1c3c010801070000f1100c40d0b680c0e40d81d402e440e5850079060721300040883c101c0c0100713182003d0300411106407a031240d11100c905203007070805d41c0644650500c52a0702882c002030101055400114401070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 829807508 1250 829806258 829806281
    0x10905340801050708090f1e03070c1e0b0c06010603050907090c0206010905090a020a03080a140316021c08130309030b0a060302040c0903030203040902160203071202040b04060503030a080a 83
    0x3160400000d100380306402c480c2c828641501c03212020f5031100c240c00e484003001d08100040c0c1d08800220088071010306022030046280c030301181e00303142040d070b9941d007890320a401c9050404205d1415187d1251100d100b00042c12424841904010b030302510f207a92010103008900034580c540c4006002e2410801401d8000e080e00041841034600b00000651962030a01030440c9c22806d100004046410008800c4030266014018000c0249903486e04c13443c5411412030441008a000300c1c2507a040d8844025500030942501061106602c00d84003034980103240c080f1500c5200329221403042c06030000c06160f840140d42080380083d1400e031400700c422440d107030001409540c4110074006821960b511042c1501d1080d14100031400c1100019902520f0520000740141d0003008144003030546c44d001303007419018490203001c040c1c0f000e50009007082c1660708194181071820440c181540761901859a01030403d5408000890500011076100d21603280c0c1001841074a00c04186185080d5101088642 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 829808758 1250 829807508 829807603
    0x8031308070303150e01050d1101030618050901050f060904030309050307082d04151119080a0323040807050f0f0c031c0219080423040c02010905 64
    0x81e000d280c00b900501d104d200c115040300f00782c6008258065484001810f84030300500c1720720074031401c0c2e80c2c2420b81c2c000c10205604064450200098504000e0222000740f1610034001c1113500c1e002c203d250840d28010030b03030111030202d0740500103683c803060480d5401030303050f140120f480c45290070860b145108442e001400c1c0080000d002100070358144010b42c0702e500002c55400c240d4501c26241d201c502803030150020b1801034440b8030402ea409095102c0396107032068155103154403005150340030003200e80c0c4c0c191988080000d42240782a450b2007200d50001140c01d907542100051400041011030007080140007110005c0c0130012b01004000001000c1035010444144100d500682034440320801d2089010f88981b10340158075503560700300003000050650080103100144064049010564002901c0c401010400403920004c2100c40001440f43c030781c508504060250244005c4424602d1440300316407404011000044020074090200c03141000f0800708510b02e801850718185030800181040b5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 829810008 1250 829808758 829808767
    0x12020f03010e06120f1e0a171e041401030b0112060602030a0e06121f1505031009020304050d20030412050717061f0506030a06030c060f0c08031308 65
    0x10100c18281407080505507a003030300d00c0c03c11070f40c2d4031354402c201001712409420440010030303884810381c407140c1e0345140603085075909010758a4013060907803800742d168079801000800e44241050200e624101d000640c200745d1500c0d00d046036075491010b1002c50303181010340f900c0403626141c0c0b151000740c1c0015181c0c2c00401c00a07a840602030b68991003607102c1d6000c0b52511104168074680170080c0c480070514400f00f100c003640c90041c01c0004c1c05180c2881c400120030f050020800800d02c15800d01e0490003526110342d2400e05031025881c000e00c90340600851401041008006100411a062444100d045c05d240d00e4070000412050380c0004100d5182e07501c404100003070301400091030413411600420589201c5a1114003503103060340031042c012119440600410380c500000c6030a40d203030702c88081007078601c603031680d00041142d441594a05045500c0d15010b200703014003041600700505142c144894165555000941180c19004018003240e9000c000209006606851154036a40c4079070980c0c1c0e01d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 829811258 1250 829810008 829810019
    0x602070915150e0103060f030b04060c1403070905090f01080d0c03021f0203010905010b070308010308090d0c0e07030c03020a020c120a06020f03160207050112090303140106052d0a12020f0301 84
    0x5075140c1d03c149074000383c200703140025854004a034040507281c02018074a102d90b00d9403290301c0a010304644801c00c10221b40c0840c20540c034008041d41c0900c040e9079820b85610f03c0d0170104900a04060460f12101034244010000c500c0d0001c2c170aa030000032428510b08000c01070505a05181d222455448400b21050514800310203d40c01981615040d24041203281d0700c914540700c0070b014880005010458400c018400700b44148041c0c030000200800303648018105950701030b50300480b54440b0080e10342e4401880388041d05130051044000141c03404500f480382c40031000350f564070002c0c9001d028180d8030b920411640802d11000e40102d0300101e0540d41c1e43d1042240c1d00107540211514821401d40d03085200c481e503c04079440003142d00c16502c40110038041070701603000b0203018a0031400c1c503070f03255044c92881c2c6404070243c0c02000d01e501c1d010b80351804001c00700b9003109a400441c2511800d40e58109016050030140d6a18403003501e030449001e034640e18000024400d0340361407908190040000900c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 829812508 1250 829811258 829811267
    0x5070c080a020f100c0c08070c180f0b01020d0e0d140303070206041b060804021c060c0f180f12080d02040b070606290a050409110901020c0a060207091515 68
    0x150403c200c00300d842e14900d4100382d604513012101d4210028100440001c0803035050009091010301071140b4480c0103a40d80d55404a0115000c200c0c21290f8803a51807082c080c0030f82c03242490000d000c0c005030248042840c40241110300d18030490740702e0400440c40c141480010009892000041300c1140d540e030610300d44c00f030350b00e4004903412944007450546042c000ca00f6101c01a080307903c140c94210081e1156803c10102e0300003490003071101a400c5040c603000c101c10340540c0200b0080f0b91101821a281a40020540042d04010441004c4514010801c04206000071400c84001d0188a12181841d281919080c0b140900c80e003007090010801184a02040e07008000c1c00384105030400049944a01c0b005111400d4180702c45440385040c10144105c0f542001401d001d1200e103400c070300e0300e41c5070352200048a40150725441180004035110200c0d5804011600107640121084d20b103203803a100c0e000b5540c00c0140254030200e6168424400701854003030352381000d01100c01050042d094150030040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 829813758 1250 829812508 829812523
    0x21813050a210f08070804211d060f0313030504050901142403040f020303041809060609060e04030309021c0f061d03070b040f0209090f0f010506010504030605070c080a02 75
    0xa250110b515110003030705002d41d007104500449600c0e048103d41e24400181c0d00d1000081007514071302c582d4200c541030610000d16094598981e5100c01d0000c85400d91403160003400d05e4046401620200040c142000c00107040d6039000c030285151014202071803170100d0b0341c0d0085d0340c0a590040103290001c0b42e00303910011120b091090660342104248062042800d10b0030b07003182130288015007000801c0200e12800c4061160f140050304072440c1c5030341c42c85803100c00341c002e056108541380d6901102e010880240503400c010810160103104680c00c1600b00c1812580140008040c5580c40205e502151a030000018004420804c1c0e582040c9450400204000911a00700c0c0d001d460061202c003080940d140280401c91044011414882c042d503544194500241003520224803007201c000040c0c4d681580b061141040c0009000c1503040351100500e0680c121203aa003140c1d04003001c01000b0b99102d070542c0c003207d42288004c250394030360400a072002100d180002d1300510f00014001c0c00f0310740002d00603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 829815008 1250 829813758 829813793
    0x909022706041203092301081f1502070303030f0b01020c1c12361e09050c070b0109022511030f030915030609010e090f0703050606011b021813050a 65
    0x302c200c6c60800411581c480c228040c4030701048101011410040c004080d42d1090424111103031030301a2a94a11040040110054030050344140010b0041591602511020051241080c08100440c00c0081e4881c070b001081c90b4090400001c0002040c4100050a00400e400c4400e204580000c200c004009440c42c010460300c1182003104504583c1c0707250041c0c0711200c2c2e07240c01050074905001e118403001c2280101020b00d039140c0c090203c0c046000307116940c0540301182c0e00e95603c103024034203400344000c16403021850a01c1030242c171900c1541c1240c003040624000b0b401040301c0c0700f40d2414855080064036035980610070584040c014541c000000d000d0f42d04109c40c3c102d545404203a2035500751104495140d000784103400108000701c0c450502c030f50400380071015036120142c1480054a0303c4110760003901d987c0c2c8500c0601c200c80d40c11112a1103c012081e84040c2001403580226031001c0f2a80c207481d40c42c0c010704000411700c0c0d4101c0d214450059114003035803c22802030403d6070841d503285a48 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 829816258 1250 829815008 829815029
    0x1e04090f060e0f0106120617060412171317030a09050c06071a0702210304120c24150801140903070b0f0c04150807090902270604120309 60
    0x41000b510351102c032485007510740b802c460568205a82241d4601c4510700b2200c0b02526080040f55010000070043e8038020154001c2c115840d15050902803464a05c01d050107006804070030040307403110115207039400041280503000b801c565103003014101e40d0003181d280440e4404824401e1024036508008801401001101c02c9030310b0744000c1000c41d102e25a4010070030114819030785980201e17610304503031201c0c089c01a1142c16540070b03e4446d019842042065521b040001000b0810890a00d4211300c40d4940c07030040e01015040c4d44030035545884011220059400104080010701241c0180380142001c0350590ba03401e0740c80484501a221b01507007510400c10440004500c00e8000064503241030704010552030342d88552079800507021014003139400340c0340c04100201c1c031220f00e1102c80c0021780850745c2d180003e24100000410700325030750b00143e803020b00410680c604890b0581420190403e091003039a040d50640c800508648a2a40b100c04501a546050b0091541010300d103011500000744 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 829817508 1250 829816258 829816271
    0xb070201050a0e031c091b03080c07061d06280203040617060603040f080f190f0f050f0d02133206041403010b0924031b04021e04090f 59
    0x10b0a44a02542c2d9142614145c2c1020340013503058150802440d8600481c078022410350400640c44000345035401c1540c64400004403801c48034020403890000300014581030b4105200041c28003000d00b09440042c1c440c1d040440d051100200a40300b061035400e01340f8056126820340c0700040d4903074000388900ea011841c3c42155240c23100000050310b1141400402851940d507865584a1582900400540380c1302c0781808500e0025900000412400d0401c06090004410f01480101070500b810801000c01412091822070160801c05444076651041c0c0c80396100d148030742c0d031400280200c0e150300080300d441c1c010008a0210b1040d21101106041d070b0700e5030001845001d000ba2a0002502094000e4010002000880f4030402516840000180081058008c1030001102d00d01e0a079620b20300f141d104408a420079045c608442440d65007640500590701440f41d20000144095480720302403600041c8095910015420824880c041e15581589031030721441184001c24540e211094034916162 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 829818758 1250 829817508 829817531
    0x8010b061e22050127050d0f0b0103030903061a010c080d11040b0a090b0406050a03050c0403140c1c0305030a0b01090b031005090604020c0316110a03051510030b04120c0b070201050a 80
    0x900b121885c40c2c41d10300180c0036500c0d000c14001c84088140c400d9450700c90800321800080c147c2c10320f140c021802640c81151050842c00c000f404c40d09149164540b01030410b00d1440aa40c02600400c1045c0e000310403030391541102c0340c0da81b003d09030300d00300081c07409000200482c290b1406406030680b00040ea40d0898499154606005a44180e0080d40c01150050120803c024400d410099102e00e808155604281e582da64454084008544840282d084051480c400e4148810002c911042181410002e0002030310007512520001e08410700181c0c880b80702e4003650340507121000041100b20340c507a40d2841c02c0d11400404450500900d407042d410900410458a028001d440084e103036403000c0c40c0f4210842c5511010300d11401001c480d055022111040c07195a8683c0c608021401040a8840c3c0150315581d032030a00002020400e00303402c4803000b4404030300c180c3c070100d5215520240f11903040040703c4080e24402c0c4506802816079080008018084d40e043d0420340c0600180c510134441103101c0c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 829820008 1250 829818758 829818797
    0x11040801241a0d15090c05091806060f0d1b0906090b280306050a0605090405060418081c0f090b0f04120e010509030a050c090108010b061e220501 64
    0x250b40d15074040c4244100c0c1c1071a41d066221207001c90302d00f0b1204078082e40d5189004280c60100181c500480c8011581c1644ca041c8407650103442c100346290000c8501e4000d0008038280070780202640d088001148040c680038141d40075082c45803e400d17841d51800c5441000400c1d55a5034010400010310100000403420b28040030b03908100c1d031014070102c441d820110205281d00030303401c109081640b80d010008094442c01c0c1c96401400c80c542d901e640d40d0800009200607101c01610031401549050106c681049a007091100035a9112109650392800d10100540c0900a1440b0070005440c24140706826081c9038445003a00703120f404460044c0c2d87c0d498000130024004c450140c01d440f040c61038000701c42e200316880e240b0344605051450601e44080c01081c9407114404003101c4c9036100c206901c0d03117481c00c141481d0040040500900c015416007000c102217004201904c0307001110f660b103101e00040c81c00180c9100181c042074481d100406024000720198041c4078150102c1d40c10600981400400e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 829821258 1250 829820008 829820039
    0x408120301050f06030a0b150c0c01110a080a3e060f16020a08030405030c070f061d010302040905040b010608100e010513020408030f0307030c090302131104080124 72
    0x401c6440f110f584001407100550000340b98001c025500e141c0c01c0110f17a549075150041580c44c00f500c0e5119800503034482d03d8102e10350501c5041c01802403010038002000640c1540b006d83c08495180c8a15240000361206038540005038003082102581504000b6401c0301030000b10800071540c4030341401c1c80409a2101800e8550342c144911280000f0000f030f1400600d5000011280b040741d102c8515034960600c990010354044549820014a50b090308400700a904040d241000c1c0180c00b01e450044050910300c2c0074541d900d0035200e426144900383c2c0c06581076034010702d0aa1010b1001c1c0c80e041c41c0052515009000e07510200314503d010a5002640405410542d800e01d1540c40c02c99003040100300e400b90821185040440c0c080001061000c800c0c0090040c5900d01400c55443e4108400058140c0c2d004200880030052200700c1000541d42d500c0c64000e25522010002848950100c01030b041c40c45181c01a0070703d0360901c100f191404000b00110ba000441d801c20b4111300c540c0740c01400c0c00741c421 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 829822508 1250 829821258 829821269
    0x1022b0e09090f101a0411040503151005010207081525020c04110415030209040902060c160603020a0503180109140c0a05031902011d09010e1e160f0201021e0408120301 74
    0x282d5100700c00960405030b1051038a1f03203140e0003450405a440d00082c1c82c040e9034001d050302d54402c54080c800800302d0a102c10019110900240c0f00980c240704000f99a800c0c9c00c00c140c8811000d08000c903000280c0c451a6100d03000c06c007005a010818110030180d0340b682c100501a01032407605940b801c0407c001000e8500350743c00b10310140c00d40c4940c501d04401a41080300f8050b0b0080e039801c4100f0041c4e42c1d0000400c000e48044010744110201360f000d41c072800742e440d48107000b814010400701d00d8070340e44201105c1d40550852141ca164a003004159401096102c00c01012915408400030218100041c0c6003e550f034100c50b40441d403625481810303100c0e41d8a1543d2039101c3c01641e05240150f02940c440107060740070702c00f0f000040e201c19002641c007035420380c010440c004111042c400821842c00c100350003d60341804000c96402d0800040030700405020944040050826080520301e00c05e4048942e5038035164441307d4044140101c026203907200d81f04103d1607104071524220b20480e0141568101d50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 829823758 1250 829822508 829822541
    0xb1305190935130320030303010e070507020d03030b10030b10051e03011d06010f080c0306030a0c0902031012050a11040608060a050a0b01022b0e09090f10 68
    0x4001c40320b00e0082c420700c6880342c45200707440685032504041010240c00c05500814410400ca07203075090807546040c0344c4416400d400c10300d07004002251030010490703046401100e0400c40035074405504445500a988000703520100b00c00200c02850303031507004100c10000880740d08580d0144108142c04840c22109103503008100a4901d6030300b58001d002801e02803e141006071018029400442c4155000340c025050600010303030102d0320080b660104540c050402c0c00c29444040201101800d001c1700107214414010001001032004c1d203061104d510b070142c0c08210120b401ea10b908a5101a410447e85003404207091200001e050400c2903401140d40e800a014000125841d114501c12084150003160490b48450001030300c9141008090f2188154440004550501c80640001e60304100c802604540c811040322b14040301b07020700740a44d018401d50f240000000580300f82d5174085503d417596404183c1008000030a50302294412055200c54140c810070710a8240041c120350012a1000489 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 829825008 1250 829823758 829823783
    0x20a050a060816030219080106120501080a0f03030e0f0606030f0a1505060d020604270b0a0902180418030921061a03030d0609140601020319030b13051909 68
    0x20440c1d80e12022000c982d8680946403041d880d5882594103080c034034003c0080c1d1f550004101c00c40d4444440c03001e0503590705003404194034000d002c0c0e65a1150410240c51000e01c48441002c040c001c0e400000141000c0d41603461854610008680390f04003140c650703000e0301400200c0f08520383c0c00303d5004030803a403040c81020541804d10514009000080c061500420740b4507c0c140035a50b210042c000910700901c489100c24040c02c42d084800110b24250300c10725091401105041d40c0d41d4641c0c2d0f007a0354801400503190041004805501880f0071883e0340c00516103201c0034010035003506005045402600c4a0b10260780e2010345400071b40d0710520118040350924070b15400200306400c00c0114a070b400320640854000e2500103403c5a00c84c91041203441d555a00c10494040c05000d003000f40555146481074501d803a50010317403203115181c14008802c080c1040500d40d140241d02c180c40440001d40900c100e0140f441c05000204030664500f030000d40d16407244440102d05004158005a0084920041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 829826258 1250 829825008 829825021
    0x1e040f060302011e020d11160b09031605060a0f051c020c0d0801081203190615030b0f03060a050c0d0c021006272c07030c06180506090d050607020a020a050a0608 71
    0x7d0303002a4032031403107400340a100c24446103aa21101000e030020180c0c06541d136034200109482c1122070302190740c00c01410b40042005641c0c0740b0a03540b422074142002210003001140c00c817154459012152138a05030b00c0a062000502d990180a4000c030000c101c1d4400b030010310701940c88410034030801d643c1c0d13404528115040c480003405903400410040f120600c8003400c6526030103480b100d810600b840300b404000c90300d425a050141c2a130032602a5001050082004040398540740010b20404141d9140d4000c1109140800b080b2034403210032510410608254420003902c0d010620721128080b8100300c03020a0b030100d0f0840c444280b0144250140c0c0e0b00c0038019518014141c2c0c4880d0400451403035918640f101f10054444800451910141010905618054204e038a042d0003900c00c1004844650301803c82c10000942960421540140c0701e90369500040c0c194019150010500c1c0180414001032a800288241c60703180300701c905421a944807800e01c0807180141c8130761000900004086041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 829827508 1250 829826258 829826267
    0x10e04060c050c0f0d082d04020d0206030408040f050a08060403080919050717010b01020a060207021504090509070911160204150b0717181e040f060302011e020d 71
    0x608101e0801a0916030242512400c4c100d1301d40d00b000b2a50003a4500d80f2484d5817110400781c1c000c0a0300403508600c0b103440034000c0a40d800316502109164144041415591403501d04d0081c1c5900030f03c141d50b80d00c1d242c6009240c0b0b4105201d96942c20003070035408516880c10016050a5915401c000c0050382e995480440d186007010b0301e529810700070303076030241010214808240c04103409100148445032030aa108070010400b000c00002503451300b140140281e0340880c1031550700d50442d0002da00d5003c03600005e8071002803202081c000400c005000a460030554004a108d51420001e8a8000d070340d9110800a68080d11446006004c0400416154406c10040003c0d014005403002551101100ca001f1800e086a017141d03181c0407001c61804200b00380c0005000105030310640c47c5e810300592001443c00b080031100010b02c903211700c02000303000d2072203890601000c500060007442140c07260060302c4c0080002d0302090307000540d00d5010000b102003020300c0806e8511a0f500038400c10320502c038110b4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 829828758 1250 829827508 829827521
    0x150306061d251d060c0703150506030a12020304080319021005010b0f0d0b060301030f120908071a16030e010f0302040b030c1b0a0507090b011716050705010207050d030b0108010e0406 80
    0x391202105400c900e00344c5802c3d000e458102040030007848454110f044c841a9280000c40b2100c419003840200034030b43c1c80100704040c0039075020300303d00c140700b42030902030f400c601070ba400004e00c9100106450200000404031062500c10302e809a4600964043d04102999402d014400c485c1004200000542d04403400404030320151000000d40411030100290341380d442a8800d65103d50b1000b14581401069024201c0040d010300340341d034030289400ba84a84490040c0f080b100c3d41c590103100341c135a031713101c0e482140c0f0100c042c030800a6400980d882d010b000540d44054040c005440640c4002210380240b0031241940e1100c1140d50a503031720404100403030390080b41c00395033b100940d8020503503051003046850801440f89010742940d81c20321015200b1111081e03161410091540d038088280744150340380311f40141e041f54405058001503039007910507203c1d0301802080342d03100181e65814080042100c0c1a401d00380e40d410f00040440e24011a1250070030700603442c07052030034008a40040e05075404507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 829830008 1250 829828758 829828787
    0x7051810090b0706020a0e0a14060708091f0207080d0c02120f070905150d030807080702161d0903072d0209010e150103110d150306061d25 61
    0x2100d07501c0c1c5500706528150044002140c030386030046043c40c280394102281c410300410a4405202c09440c001c9102c20264419034240d014000000303000c001d001e80f0900b101c0c0d1041c0050410603182d075448018030051480100581d00500a40d071010035480c00218040d441d212555480c1410518650208107204417032080400a912a0000a01da2910240310900080c040d10000251030318207040b01a00c845d441d036030250701c14800d031032030b01e000030390440103007504104249055401e0355202d020691501e000714100d482000c4852000003a85c0f03d4094190350392071072020040301c19842d20100c1c203649026503200106810040218014810341d034180140311940c8401d0181c04e041c007180c02283c86c0b04e00c03e800c1101c44110b000308011601ea001d0348141c1c285c000a180400485030215840c8425004460f08610950348032140040c040000140d032078003450700300c00208900d03550741c0a2420042e900103103d4504660240c001a170b58071034844003804040b2802100100e0b01514001114440ca00c000c50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 829831258 1250 829830008 829830017
    0x11091518060d0f051603060b070309060c020d020a09090c080a032106150504050103230c07030908030309011508060709030b09031c050907120c05010c0f050a0b04030807051810 77
    0xc03503c40401c1c500895006040344403800113034034070582004003a01e903250800c03400004100040c200290b400181e01e030031900c3c4c91605d118007440e14070000302c81440d004400396002c075001102003040c945a80c8130341006440742d440401c1c030781e07613911046444901024001d40030403c441010386421060560340c24110007a880300041094541d0078640301c58568400c0341b000038001060501c82035030503210f0344440c000d807480003650084101c8130030207605000600c0c00107242301c0480e5010425016242050142c03911000707680e200e00d041d245260082ca41c0302004420703044032140c000340c40304010880030300a543e55900d071880c9508646800d500c04101800020091104000001c1c502031100d15082604403c2040410030f4101a205c861806030b0681110a0030500d1004441c006898455402d0458200b030070240d140c0394803410100700b8440d11041c041c0580c09940032000030004080f080601c0356109456081c4140c95020044603a4001c900c0381110140c0d0441c807040d0685041b14a191401a240c6003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 829832508 1250 829831258 829831271
    0x3100f03020d171204231c050a12022101150f050306010e10020d030c090b09101412040605070c050c0910080a260708031906050411091518060d 63
    0x410b009120360445e0140c49841800b0080b0145140c24071060032441d40603c010620468961866002c0d01e2030140c1075000d002000a1680e055400b9601d071601c2e94200030000c6446060011061440e0756030400d89000c4010807800109058982ca10a611812010b90300d140b54401d810300207690746d500190049041c0b214010310040c841d610113081c440001c00369405050380c0407040b200035050300e0f4040002020b03c900c1c1101441002161002e6540340441240c00420060190500f03968000560b0b040c45403011002480345d54503221854414003803403103043e0400680e40e0703c040840712a1020800182150000010052140303443d07a0340c66009600c41609a921595440c0c00314a0845000c10844180200c541c0d03440304a40400b080185418001000910702256a6038111180c8402428001d8245040d03d880a04c2091648403101800000d401040300340d500000340301d2182c02030307582c176880b5270990003410294078090826030f8011025402807503814080c030301c20008079400001403110380655034070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 829833758 1250 829832508 829832527
    0x5041208090a0909110306060f090a020f1611100806060a03140a20042d08030f0c0607030e211c0504050f06040317060f040f0203100f03020d17 63
    0x224400b009141030800000d58030744610f03005034241c0805a20b644244c204508020860710b507604503218a080c12141c54049a4038010384000038080d000b010301414001141d622441c800c5a6508850540034001d4410074141040400c845080481490310001c3d00c070901141c11402c20f40c003c2d00c1850f41c03a003400b05280221707442000c400c4d04112100310609440b0608080c0c40089060f81a420404004c4500e1a140c10101103c2e042103600c18404011a500b0720002403010034014148090304998054035500c2581ca075110750190012000031030b840c041c0d1004100390314020720814400c4103c0030017504804401c0080034a450b4410181110403010821411856034907400c10303960031074405000050300d402c0600300503140c01a0300e28111029031050040c080030a07000a40c00101000110300c1e09030540e00c00c000300f03203003060342904a5003207414a0800c4404850300d80256104840d03003400400e807260b0b203001c1001c0c01c0aa03480043e4018410480000c040391000545c4861100312a040381e2420100c81c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 829835008 1250 829833758 829833769
    0xc110604030503010f080105060d020f0a0b040e0a0b0609030a081c050a05160c0803060d02060708341a0406060e07020f01050c400e04050d020d0504120809 68
    0x200e4046000410001c01813000f0351a001142c8040c20404d030080126140040204001e4074072100041d104000d205914030300c5558041001c40940020100c2f10344890380c1d0403d01350380c2c0b801951264981030070240411068284030b816107413903110080082208400c1922500c11039840010344039800e00c5040c102246541d298080c0c03e000e43d603084800165443c02407124912090055071481c00c00c2202d0b03c001003c20002415240c100d241120130740f410703070704030310005080344101c84000b01030b01d0010503e4490b40403417800f002c0e80b00c201c8418040d945442c8440c4000c103441d081b80000d06454881003440e203080542c00f6510f6100d4403521000440300d40380d103503015040c0d00845141c0c0041c1e03c9032000d103c2400003802199004100c90324214100307200072425400070254401c83e0402800c1e9282d0030070382501c0c5c04426200d05c0140c14080050607031175008a07540d40c5401c0300d05840510441d140302c0816880011038010240f040c0e0307181070405080440c491840711082405070789490060250254990b141e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 829836258 1250 829835008 829835011
    0x4060e030d1d010b0d031d044205060a031512050a0c05090c04030206071a070f08091b0904030201111801030e06090c060702130c0e310c1106 62
    0x30b40c1c0e204402100c41544460039a500035844a00800e683d05241d00000d42218840c0103520103843c91138140100307c0041030003002a080e10b5000001441c020040580b40d021689510030724408100203030f40d050848800b16124140301d82608190100038038080d0b1442a445004d1001c0f50b03541e400d0038240d039403042030403500c4000815901034100b5040002005034106900c1c2c02071000b501c81d01451f282c400410270303190103180310180c06504002211350400801c150b038040e20402a41941c805410144001031001540c40100408210b0b017801180d0a8003000a0341004600905204400405810180002d801e80500218255901c41c201441804051130103004110b04c1090340c015070140c035000040503a62018550f40c0990003a605000c6203050100e0140e0451310b0a80e1020350b2003a551011032211f0304607441c00440a4500040001000e0340171208901004d0304488121074094003540d00800721102001209581e69400c1d0300c1c5c3d9284401e40c00c6902038044504000030380741030300780d052800e1580 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 829837508 1250 829836258 829836281
    0x123030a0209280507120203041109040c08071a0a0c151a0103270b060613080c121603030810031506090f0c0c0b0907171f0b030604060e030d 62
    0x803005030282d899240504002030f0000c1d00b0800c1c041030403e40c2c0060820310b0740101700a001a00000002c0601c0142c012410700c0d00300c050200710382c80c501400c050303c80390705034000e0403d20300a5207030014a0790030f034400e900c0814011030a20351600880000c04d55103050001030455403030090200a000c1002d007031085012a0381601e8041003594010b00004040300c01c3e220100c4681030041d0212643d0303003070103110b8800c0244d100c01000c550b501c807000016076500402618811041d566100031641700d0010901c4840b118040c0e0300008160300c0403074000e40b151800c400d012501020914104040781c411084a50000300c2040c0011150780c13039498110b010300031503048415081e03c03032604001034299407161716402952107200300912011310100902c46140c414010f0600182d40c4003041c2c1c60041809003000030118000189001444001031a23100d50a803029045200f0980303c442e00710b10143c0c014030310a09002000b400300c07582e0b155503071030052070711945101a80c8820f02c003248844085118603009490b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 829838758 1250 829837508 829837531
    0x1f0c0203120a080a0519060f0f0f0e04060b0105120f0f010807060905401104120209070207080f03070c080309030d1b0f11090f0123030a0209 62
    0x4240145460190076030500d0300941c07070410490120303a500907195500014031907000318554481c0030170b0940b4070500412a60801c2c5c605100010f9032300004003040201c800e115000121030340d94400b075410641203445032240039182c0a000400060080e8402c00c44080c050421034180070240000584181c0c1c02c950540404c00f10304140320004040d003403c0c2d40180b210304014180223090990090030340a551050500841080000000408080341c50a442514101c0e95003130f0500d488902140400001d88640400c1b40313040c44030440741301001c00300c1d070641c0c400784e062003545c403895828002e030010020104030840c020a070021070000001e1003c0034208a02200440c0c0355050350410360320a58484c1d200d400180e00803c02c100b10354401085901c1d400310f0b68100b8021210354003902e02c008401c08a40102414460342404d003c00110402c0c809940c1b9069030009407960341c4280c0460607020a000300403c13a01c114407036440100d14241296810f26015054890380c40980e800b15050680a0703403080c1a14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 829840008 1250 829838758 829838777
    0x7140607120503090304090f093e0f060310051003060503070b1c0908041d060d170705010f2901170a09050a1103010510150f11030a0c03030501090b06181f 68
    0x2000003e6103101052401c201c5540da092194060310300034107001c001214211607100045240d40318544c3d030bc1c02c0340b40500107560f6850038212080c2000d4040c0192840703110381d211403100f0300f803092081009030381c80600241182030401280f0449500f0001090360002d0003030f00d900c003e154440c0900c44010344603c03004e6480d03605121138408017400c02901e0344021548503040000c07a0366000150040603410500340a1044c00d90000c04615201c0c04401500540c2003140c035064144066101c035500024035554640741c80703242d1403465061001c04c038004d0300043c0f00303c0c4000c002000c160fa10f542c101800c24800030382001c00355101801c0002d00f000550740c0e4140040031a0440c1003c5c010a548025201e24103517910341001440b49040e070345042050700704000360b02224003903030080640c00c0710803e41ea000c4a480c0c2c6c0400707900074000034400700114002420305000082c0811140140305208500415290134500503a540c0704450007480c0d056a13003c41c0c1c4c08011040304555603100781030090240c0d14400d80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 829841258 1250 829840008 829840013
    0x1d0f180313030c05040b06030c0a2a0308013203010b040c05120c07051506040612080919050f04020d14010323150402040902030106031407140607120503090304090f09 73
    0x9207450780c0b11320b0250b4101030b90401d040c0d503044110382e4050b4088140301c0d00c40c035010341d0458014040920401c4004044056445402100fa6441c00340510a81e0ba07150640e880c1d03011500d042070310340d030810540c61004c040000e1081c0c112044841c1c2e45030140000919100320400a429540e00304650750101c1c60010301071500e403009c540e000e40e21017000111a0f1611034140d8980e40d0701c50340c22444291b41d0750002c0c003243c410340e110382062008003080c3c2241040c0c94880c4c14080000e6000d01e18a6100e5240f0460140402c0702c80d50050701210401840d80412882c1041800003940c045680401095580c061151095111002890103036000710456800d09602c45401c0c140120031400c899402e0380100d0034a5620203036088501da01aa068501081c1c3c10040e01c0401d01428464000a20380403480c1c4101c00380c0140001c4540c200e0300505841c0107140c9000d0103200a130b100c0c07444043e00c12204c0c3d2011508032070242000310341020f202c0084074501a69200e001d01201e00c110070b20f103c2207481d0b40c0d41070103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 829842508 1250 829841258 829841273
    0x1b080a050903010f0c05070f03140d0e0d090e0610030f0e0313080c0f1e1806011d0a03060e120a021e030a090905070309060e0a0c1d0f18031303 63
    0x5805901d06810000c209505c2c6025015000c2d07400002c048070031380081103041500c034a490107001c40842d04502d44074031942207210090000240701c8245032042c20b14501d081c0d0310032240d41c811100c1d205d000580c180c581c40d041c0410900a017020310300345501ca680740035400e003e82c800c0440310700f200800303152260fa9940300352402d803e25500940382030303100c0381c2501d00607a035891205009450844001c8071003030410442c1050700c080700305915809016005280090000d45195030302ca4102665400c101d01c0c04402c1440d0802d061a80729a005114043c2c140001201948001c5031001c01604440c03659000d1112a040d641c080481000103070003148042801c800381480e985071021000c0082c500304001c0c0840142151524400d00001c0e546400110301041d009234409040c0c250021802d010a80080800c181c0d10780000204036445c80e0f82c100000360303070b040300142c00000350540c003038003c42520340e070052082038140a080011105000d4901102c80c0b13008100403e030075000660800f0b074003403642c01d2180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 829843758 1250 829842508 829842521
    0x6182809022106060909030d0c350c0703020309121c210e0c1302040f03030503041209030b040807110d0b0f010b030108030403140c04060f09050901090b071b080a05090301 75
    0x6009154945c2030000f452004030507140003079440030002030a141501c43c01c461800150a481c58420955008510315015107505403881104202d040300440d1903043e94400f140c40b4001c1c000c0e0058100b44550380316490840004890001c554084504ca00040c00c4082169140307010714501003626440461038000319100c0d48610300884200c208201740c40d5a01c210b403103a03e0032010324481d00c1d100e510110f03051400e80c10f0310064544c40724040c00b4103840f0319024065074429a416910507401804000a4600c10000c0c4010b0382d52000d00544140c446a5a034211381d00700c414111740704510388034549004c1d140c1e0200c620340b40d8011820400c9504088840044180041c0c20000070f0b100200014402000008125000c13070381c0c003044461135103045100c0f45080029105c0c5955000d800d01c0310000d14595020700040640300960343c200850780303130300100a080302d400395030003010084c94600181c203040c059041e2801420000c3c00c2c143c0a200d0307a507502000c40e44001480390100c0d0303010400384c0a0f41000d20454 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 829845008 1250 829843758 829843771
    0x90301021201060f031a010f02150702010605030c0901060f11480f10021504060605280302040504031b05030d1107020904081606090b06182809022106 66
    0x2048090105480ca02c6c40d52003807020340d0305100101c901c00c880f40e842045002d419600041202d0368034104550002e010b440a44a501d12034440c1e000d8254185c036101c0c1e6024100c40940d180c0c200d240340c030400c05a441354600007503480d150040300e00360742c810a52203621440300d018503280e4500d40c0d440e14410007111411040214900d907824044030700d0f9915040000111000202d5580d090440c11000032440c2c5205070410300d01d02c16460050104200310380e04608141c03441103030744580210f08a1220300c00300c040074280d0304901030110030410160615a10450700b15000340b91181d002c41103204406030000159008846940c0000303944092041c051007510745009020103814a0224190002064118054006001400009505000d9160000100f680700e90f100d001802500114100101c0280040741c2e46802030803186100210031f2010a1900e100307645008495030311072002d081c2c6c1c0c5034006000c0d140a240b9a035034401e0102680d80c5490f01400d0001020604038000d2a20760072030f00340000036010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 829846258 1250 829845008 829845011
    0x30405072103020c010e04090f0813082b050f03040c051c02011202130317040e01050d08160302100e060412080c04030314040f0b030a15050d0f0602090301021201060f03 74
    0x101c40000e5000c1040001c48109281082d01d0202a10001d07000b8815014028000400580c14408005108000d4140555004030709022203a40f040e4464440ba464002d200c500707040302145184080c00e000d005010286503180c500d050121150722440c1542c01038800f0b880040030003070108294070f881451164280000c0901c0c500c10045c0d903001078058445410303080021600858008a28901503440c0300085402c01000f0070450000c1611440c1540540110b1182d10325007000415079083c501894a00185e0003031565241c9400b01c2807034001510541021400c5018000c000c0a80d07010034060705219011000103031141c0e01f02413070310540e590300019181083c0100001000089099181941e040ba505802d105400120303011740b0072128416034000e0180d40c450b00c0e101003942c009100c0038621980c1c1c41c050410000d81c490f034446040f400c20b071041c41e61100c0003041c1ca400281c60401c5103c07101d4401c10015042581810000b400c5e40c100c40f049240c880e82002c010888268440ca00303040201c03907401c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 829847508 1250 829846258 829846319
    0x2041505130908070f03080910140103061e06060e01020c0910120f020607060504021c21050c0307080a0f0309050c040c05070c0e1b0c0d0309050a050303040507 70
    0x2041c1e400356034000491410766a141ca04040c414020308a503c0705510240c025160718651038041c0808005a030342618510645410800c0030405216003088045000400300a681c070313503614600902300030700c1d04000705124400c0d45603610300716000303280c081d0026441c0c14400181920009203400071108055100d1455401407000710f510481d03d11060707030421004618075484504148242d444854402901b01fa0006070034000d01469500c940e0255200b03c40301c44040070351081e41c02c41c8a4844c10040d085041c43c86146501e000c5e801c41c41c1100d40d0480c02c0076402d100e0f120090030700319086220207440c0754800082d000c850030303800070030007000943c107003010000e401c1c40c7c1d00c234181c2c0d8041c200941c034010307075850f001d030460780d801407083d51002c80d0b010b0020000e50f522005800080c10f015a55201503a02c402d8490303500312101e0050b668480f20b0580203000700c1d1002c000071400307803d4070b0205441a0081c07040750400b082080c40107511550241c0010035006181c20603210722010504a000101c1c3c01910 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 829848758 1250 829847508 829847519
    0x10c021203011e08060403050d06050301020c100b030109080c0a03140c030a0807031805010c030b030a1505100b040f060212160f02150a030506150a0903080a0c0606080a020415 77
    0xe5074151510107141d0034a030f0b10030b44030800e41100c0540001030780d4420f1104020801d903000000f4103580c00c40c04020b10003565a070b810b041c00d0303005e1030781d00411540000313892015460040e170150000040042c00412461240d44450100d80d0109540d4099600001103540a0541203030344021208000310750760703151044e5456210345900490315101c00b00440200825540c41c82a00a505401c0880c0d40c0307088000c6043c5082c5000309458480e180200307051103048140c81ca0003140341e2210b82d4005d600172450028000c81301780217000081400800da03560540105004000a018101601d8090805120f55082410191a0695810642c11046001c003d01c2c2c4024612002c1003422a40c0301305051103003089840000d132050184401d034489100042910807007142e25402c004d0007200143c1e0b40e007440d600926080006d920032482d40c0004101e03640406c100040d1000020100880185131088141c0c03020b686203000d407041035200d80260740c400c1740d04209500d0f2070711880021151040030880c080f807400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 829850008 1250 829848758 829848793
    0x3010303120b13020909010605030705070f05100e0f010506090606461827090b1611060f06040c05040308031f0f080604122609010c02 59
    0x1400010104082a501150151125003010310b82e50001841c031103021000d00e403860700941005100758421500c13a000004c04e9801801101c1c020113280c1d445918101c0e2135103c0700b0303540004140484484c440c134401002550f00134400c071030105040a004e01075800c1d08149050175107002802c124480c4426100340704581d600c3c101201d582e0100d5151106c404100882a21051a20041960044544142501070289124a8206410181341c81d0812100300100d049a4100901c0c001c26084040a2180b8041a80c458104125103140800041142002681c030124045401d40d403900060070151422200700360850711001121254100034134051924148070301c3d072104c018002c180125941c5604003c00f40c800c40c100c401654015100e20380c1c81c00c21807030800710b0b001248141d070303040c141c1c0c0e9101003040c0915003c184201d030060300082a071038550303440f4038141d40030310080c1100b442445074610365900d44174061440441200d1305107031828600406050f01b52400d06a500d011504000e50403a110b4255 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 829851258 1250 829850008 829850011
    0x90115020d030c1b06050a0e01230903070f0c181e11040e181908070204110417071e0501170603010e0f06060a05040e0327100201020c01051b03 63
    0x1030b18020070032004282003550b10250f00d51161180d04801c00390b010a124242c0c000500401005804011803c0408c40040c221102d880d20804d003c59280744c81c900403580c0750700300c03504104980c00790fa00c1e0404a5589000140c07081d8000c56801c0628081048411569a400320701c052042c0400e018450508801540c00d07019010b51102d41a903c004180812804200f07030340281244001151365030a005038001880c004c1d40100d240746109414414414030031610410000c03c0e40a12049e01740300d030035401c110107400c007081c061010700000d100004031380c640303018401000045c40b030140c01014144510003121409034020000c200c0c0410504000303e07680b00c9041070703400c401a10b855640d6256000081d014082000820b40d02d442900c0e1462441480070414030700070b010440740780040a039950240000e48501c030421402c0c5400901200a800407403450319052501c0140189000d0900c040000d1822000400404010303076004c140840050b00900c81c954000500341154529010444100fa0f9144030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 829852508 1250 829851258 829851283
    0xe0c091201020919140f0105030106030b01020102070609060903020105180c06180a081b0423060a0509151305060a03030f0302071a0a1b0e060f0c070e010509011502 72
    0x405418181030300c40039416255000341c0100090706103500440c4072034a408442c024958001600110303000d1130300e0103801c0324030b01a4060711001c0c1103030700e440c000780c0c0100108a021b6055540030000100002c074140b284c420502e105000c000b842043c01e0900a08417200141001c0780820030742a86a050030002408000a4108403105540c400a9030300424849104001503500004541700100d03036000b01041c0c00e07000000b408031028032010b4020401c000d0340c201c880a5603900b4007910095011a61940e02c284e484030000d42104200c994035070125105000442d03045040c16074054084143e881c00b0521821690081002405170381020700000720741c2041e074480103051002201d4580081406901900c40294201032000c01c0040c1501860b00c042104464030b10501d440d0a6a402e58141180c1129150300010307616600e00c030000c0028403038550b0201140b90351104003403000090584040010700084d083d00741c90558154500b40a10542c1803041e002122161002c5919828040d8006480101550b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 829853758 1250 829852508 829852519
    0x120a060302150c0c0d0812070302090a0e1305150106030c02010902150307090305100b010824100c0b1602010e0703170d020702040219020d031a06031f1d010e0c09 71
    0x140040a100e2500205604d8035070401c5a9000f240300344160740c0041d0002242e9101c04000341d80c0e81001c101e04900c25225038075800b800d01c1c00144080594605226804031000400b00c00710000c0d0b4444a26283c10700024102002c041801405025814010b0084000d00fa00090128110541c00628003000d0511802082c00c000301c0080c40f00c41c85072000c1c100454110007030f143c0001c681c42800014080c4502d09a021a070b05001062088003034081c03a4101002c1440038103402000c41d03042040c0a032003410b5040400640c1c01c900700c0410103260109003d40f51003052410580e140e00000b900b5180303902240451604410401c0011404580e124250900051002c0341d480301090383d620024095888081e402c203102190b11500481e0916150300300e0286078080f07904505100e0310803401d451a200c101c3c1072800310120b0b8807980d818201c0c040d54006061245c000c8100e014540414102c154a601c104a0201c4662540300700e2111340322210b0243c510280714624500d0208a0501e9611840c00d469001c0c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 829855008 1250 829853758 829853767
    0x2070314031308010609051003120c05010b03030a02160e042004020f070302010f360804120507150315051207050919060909030c030f14070305120a06030215 69
    0x1180c007481101e8045000c0e0b0304011070702da02c2c0d40000d4002d020a00030005c81c1e9140001281e48408240c1d445c104695102c0e031100c030b00456280d01203840455000c0112455921070703070722030b06541d0188040c2010030b0641c0d00170442110740d03000da0302011902ea03000000b103810010a005c040b4514454032008610b11000034500302c5d0b051804140240304e20701078000714000c080b54200130580c1c10340010380360291441d028410f051500f43d0560258181d103e540403d40c100c0c105860340c0c4201600514902030255011900300f0350303155002200c0204461080701c0341d03000003200340607030040148003041c11010b81c030f402c05c00f011500104c0e6180c0d8403540070342032083d402c5e0b03654a0754419042025001a00d80644100ca0350704003800c00185520280713841c00510340c240320300460b000010703214034000160190b4a408545031280c0b800c5d642100041c012a007085082c101d640c120421460060102911039514140d1381d050621040d40d0078680034040c1480345060050820141c0e507003480107943d0040101546954 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 829856115 1107 829855008 829855043
    0x919121d0906010e060d060605030117190b090a05010e03180f090417070f030c020906040b0a09051f030c0509010b3603011401030309080a0201020703 66
    0x3021407000090071540c420440400050400360015107400d540241410a4403102d070003a0000c1100003004104080d110000c8841440040004e408a164240c01c0c032003680002a801401d003d2240c008645003000600152080562110013000a008540010358903504203140c800480c00914103a5845424504090461903400402201140e6030f01e5071015880440d81954026005040c00f6200020783c0e81e4114a0b00075010303031aa1751882546204010007464010180d501076400c1003c0c0076542e80300c1e01d803031383c007542e0b84410042900d6540811101c0b503420258254030103685140400018007500d07074104402c1d0385003564082d5040e81c880c0d91000691085080302c840480801040c1d05650840241c000341c8002c3d1240313955080b0b03412100181c29540c40c00400031503220801c004104040d0003607030301002085220050040c100241d00040e407a08041d02c8041c00890a95801040 = true := by decide +kernel

theorem cover : BRFrame.Cov 829676258 829856115 := by
  have h0 := BRFrame.cov_init 829676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 829676258 ≤ n) (h2 : n < 829856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
