-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3869
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:55:13.925592+00:00
-- url     : https://prove2.me/submissions/b83461fc-429f-4ff2-8145-e25defc4d248

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 695683453 ≤ n < 695863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 695684703 1250 695683453 695683477
    0x40c09090501231206060909010f0c0f0f0e060f07170403031e020712080a030b0d0c0906050d020d0f140a0f060b0904023a0c050103320a02 61
    0x4000500d0f5240e020111494080101c1e440c454074078100c0820030300203c0740800e01d006401a50000f10546028101d85900900c030400204002ca00d404030303d4221400d0000a40c0030410385c822050b227080c1c0c003a6032800c02806c43e00b000d50000c1c1c0c1d507000141e6140580400f54404a5000903072004000004483d030040382a100d00ca00e40703c58992401815005000360301c051074420100c4c1e19130079644001444000c03a0501201150800466101e2a126501040d1060285030300c8000311441d03510740b00b84050328503016480e00c2d084c0701c0c10040740d8815a520f0b58025882118a22241800740c5d9401303071858501a400045050f80100500c1c0120410600c8445051a4001c904441052280700110700c00e030544a91010404d81c109902041051101520b000e9001400c070300e859441403034903442d481c00d80030540042c90311000142040711f42e4090515421269441c1c100420047c558241c050b0080c3e2280d000d8403200713040c1c041c866030721200c11046844d0025000ca00d020a5029440307070b046a00200e415 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 695685953 1250 695684703 695684711
    0x1e090b03060f0d050109111c02040b0d05060f0a0e2107050a1208040b0c0403210e0a0b07060c03051e0c040e0103050607080c0c150603030c011521030509040c0909 71
    0x142403e17402080108000d90b0a45024101c168442c54000805040c00f8098080d6408444080c0c080c00001c1440e0b43c0b410b50088032200c4400046a81004921302c02d038451202a41145440341c0303040e040c0c07145055400c1d280d60150342030400004d06070603031640c0040c04000036a2516203d051052501078080d6020740f903e04105128842c681d4400c5249100e030380100c0c000c3e5216100d01f5100c003100c0c0719520011b09012070340c2a82303000c950f0032680480340601c0d00740781104125414000180e8840f9032640004038070040050040d04101d210b020340540241e0078101003000d441c0548142921081d881c180000e0745000800041e0b00d03e07176400c03d980207485524000d010b04d607182d141035a40d800e819101500818000c10003d0655aa00002c484440345100050100b001d80f1b14503010b4803180140c40c00781e00d0700043c08602883d01d824492013801414080c4c541551a29002d00c2c107202d044030103510b20703009032480d08020119800008072070100c20305944c00585c1c100159802c4071554415003283c4150303410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 695687203 1250 695685953 695685979
    0x206190206041e030c030e04110301090b010206090c0108060d080f0703091e030c1211030f010902190515030c1b01020c0c0609090a0c020a05010203090d1e090b03060f 73
    0x10001d149440307180b10311a080f401280000c0d00050f5800380c4400200040c404010007000244540040034050201402c08038507244144800e16068000342c020001c0340c0ea445c00c3e04601583d040200d2a00001c801d4040e240c0a41204002800b01d240240043e00079aa1900100100180c84080702c60103086140481d0302c0e4002e5150060250b4100e1043e0000040e641840f051000a4402c028040320f5000d521089901d00d400e40300b245109004d001900c00b500c402c07281e800143c400703001c010115220f81000180a907030500c10800360400c024040b24800526402c1400310f030f15034450201845442034101354032503503829602451440f07420003000e600d14010074107404002c03054002d007003491150407e4400d500400300c01c3c045c944c0511180141d000b980c200c04641c81c2c44140d8070100c21240c152068510000c00c54030f4840c266441502c804619034003000034010700545c0444120604100700e1040f980303198002000a284048030b01030071001d10310010100d102d550b1644c1e41041c013251301420103081c00b0b40b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 695688453 1250 695687203 695687207
    0xc110105041505180a02041d01110301081501140f0a05061c180f06020a090b040f05010212031e060118060305150d030206011e030c1214030406090b07020619 69
    0x40607195450b0348909100101c4d0504007205144107185016900610020180341c0030403000d0000410201100103d00c1e01c01e00c0005001e0146071440058a0b59844d80c0e54984080c0c0303440c1c955501504050350140100500c42012805001d140150003240c80d241004061800106940d606034401c40d400480012002e482c1c0710710202c41d04c2042040380e820091640401541c910b07241e410000182101a202d03052400241d040d03020b000c40741c90034681305c1903058817a5408082c036840b580052041c0800040200210360741005007041e051009005a411030904403400e0a80320600f4203440c80030070307400c0c00042640c0d101d500d40b0440340700f042d0b0a20041f05c0e40d0f8000500200801e5458581c10207002c00c189580742001d1800c10300312541503004250982c0f0f003c5803005a10101c1c00c1c042044003c2030b40000204080640c10806021f000c0700c01c02540c0c40c2850070040741c030410818034108d600248000c008098110804500312101e54241c80d0fa00d08140c800565240704254060002254801001441075 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 695689703 1250 695688453 695688473
    0x203041419150908010c0203040b0c1e072c16230901080f0105030a030503090712030f02010c0801080606061b1501080706030203090c04023006130b0d060c11010504 72
    0x4202c5458004000340c807004840d0070790748109044000350340200701c20800b026000c0003c060154030a01954030381404500143d9001d00d00c40c1c0e00709880c0e441100c0030310080c10340d909401d4100000148520104402130360074285244000d00c0c0c549410410f40341070044900404140400102c07041420031420b030300c002a0344580c0c110b001043e00103810440014294221140d00d54180c4000030002c00c408031442e982203940394402031410900340a16100003951800a407c402d85203480791711405d6201d510240000d00312445001c41a01300007414004014450300810301a800c240c1c1034400c5a81c905818200c41402c40000180156034410740040311450290140350905031240d80301a50060340c0d40718011416404199182c501d2074020800c1d9110a19140d4000c040b10700710744c10100c03806903e124101c580c100c1e082140406189400d0b08000503032404118810138100e90070320400402c401600441c01d042182c0d0030007401d0559510303da040040c05281221440d8002f440244a285800d02d0214002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 695690953 1250 695689703 695689739
    0x2030d050a0519020702030c060a090b0304150e0c0f090703140103050d0e1005090405040c120b0f070f0509040207110d06140a0e250b180a0b040302010203041419 71
    0x600b0f00c16441c04245225008a80300990001c0080c12424401030030841c40e54042828402400029580003c050102d400618402c0e40240303c001c00491310700000500b81d41605c0d50000c2e8503040f07404061030941c0c400101c40c3c2e840b01700780d44150081e81c4022042d001001c90106101c000492880000304108d4000703990805031206644150200722014180302a003050185100007041c81484410384900700f81d402541d0060188011380065a910a5041012504250180e4207440751700c0400c00144400c035559508460585003030301e180d090b281d50041a034051000d80c503110303c0d00000d030002072200b0030807800404c000040c00200d080060b8940035005181c0060f01c001620004c42c00503001e0f401c1445a0200d111600020340383c101580602e42801c001481841070242d0380d00c1d04042610312400c0058065540105003444407001f840341009070351449603101d9215401c04100c18001030340c2c08016581101d0b040b1048480d080c2c074180000d42520240e000e00140760a141c2800070791203848240344032034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 695692203 1250 695690953 695690971
    0x1121040504060e0c2d0c030d060b030601051815040602061f030b01030b04061e06060905120c13060305010f060302010e121c020f0604050c03060c0a0e010f02030d050a05 74
    0x80c140c3e6420840440726001c68800c40313600c4e014064018007402c4100700340d0501c40802c0c211440781c2c2078080d075075605400c50200c1c185103034808102c580c1f25008a204d044003601000408604501d00b07070f0700084c11132150160501c11402c852142a1042d110a141d1003800400e2103031071030329252030b402c4c02540c642c41141c04c85500031403170350360043c2401d426622100742c0703030002040c0146030b08503150394011001c0507004540d02c6551390b280083c036190b10000d000d00c00401d182e000c0350072494110b00810160554210503c33640840204040d070038070010b500c41c000742e13003503500b6007900300c2d070160701d000a25035035002070103030350038403140c02c410500d658802000e580c0b003620b40e404107032044014400400c00312a059200343e4491a58408030f0b4000594003042e2060358070489032800c01400c0740d03d003410700030f0300c08540071390014502c1c442924040c0011513004a8265206040480541c07008080500c40009581030001031105e255505200380200c8200004106040c41181002d650380d038002c5c4803c03100201 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 695693453 1250 695692203 695692211
    0x90702010e06150a03060b21060114041a0906010512010b0306150a0c0308130807060b360a0603140a060e01060e06151b010c170106050a1121040504 65
    0x141d10011500e120f443c0c1c4805407a14001034190356440c1d00420410070410303440020a403d44060800c000d124492450b1100060481e95160081d00080f07016001c154900c21402e01c0341c28640c41c003081c1d40003103280c40111608051511a500181c0f02407080c0216180100c00081c00404e20342e1000d0000c50007000305440071103122084a036a00b906006002c02c420014140e40b0404002c6072060480076003082440181c008c107401c09640c0c60301c0c0c42c0d00512048521a8a42004070441c1c54490f01c10242c100184100e144d495603600381c90050301080380b5000c681c4050000108204110a60101028691100e80040c06141d00c520081d981d54502c802200d66a0400d11125070850060088804076100041c004800d91034500030071590b1340108107110b801000038010884000011031100c4034100348070b400020307040c46505c0c0007801f8541034443c065028454400404c01d860340039007124920511403801400304c0d5907142c0e141d070501c208080c051020a402c1c201e0948000c10b070b00010001c07954202c400708 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 695694703 1250 695693453 695693461
    0x30f0103051e03191b060501030501050109020906040e0903120114090601020d0e0105030c07050601260307020604030f05010615023301032307091b031b120902090702010e06 76
    0x1c01c240c1c60b1400200550000d215550040310400c1a0115459040c20042c1c1900a802140d50103e4a806070a444480d1150010030034404280f242c02c0c05400ca42100b9860000c5580c00315401c3e103e0740c4150f8900d040e0260014285420500a40301c1d1614000c1895000b542e48040381e080034041100807522030020710000c62040e40c00081c0e00c4010940d59218030118115036001501d0b00c1c0c20080040041351000c001c2d203400180c0510440380030700fa18002500003410b4590452400c0c401d6654000c1c21648100300c00c4000d030380d801c3c0980703048030390056000720b0350121490600d01600b402e80c45002850106041900000d4020410007a20a01e507402004100c0e0580460704100da0382d481e6a407034004281e401803000c0703940d402036007019200c4001c40c02da9650000c1641841d040842d4060380420799260366080c0d40304038001003080c1d0010280340a0003200082c6070920581c1c07a0220130003051100b0886800740380e43c0250046005160010006034440c80d02a401901a01002c840c054080c01900006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 695695953 1250 695694703 695694733
    0x3030f090209180703080c15070e0609040b060706060305030421020a061b0b102309070e150f1206190302150f0a020703110102010b060d05060a0803030f010305 70
    0x155168940003000d8000c241c0b540d000b0040001a049240c14031030140c013101001084951004241d40c0b65040020300789800d80c0c400440340000064810010485058880e81030b80e540e01068541d440d5040f100040d40c41ca0310000203a070b81c030484400600080c00c195000003404008000390084036400021072185031203d0780c8055204122303c4009602c6250803030180300b150f2213003c0c0400c3c019903030403d011580d0020785560304240c0c01245d01d041d03c2e807450901400f05d045070044bc04035080400340080320505042c40055a6007400500903810000c100340358a41075a0b0700c82d030200725031b0000c2414075034840144262044980c0210700804400c030b52413020035250708100304100b2042d8003162903c41c0107401c59082085445080985c40c100d41000d012211101c001d0780018071007051980c009165503403840c903210b1441140007110314156490884005045d4590004460004415001c0010070b641d5410005210b1241a00000450322011041102140d50710303c0d0907041e640144101e03901c01482ca139403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 695697203 1250 695695953 695695961
    0x50d030b040b04140f0c090a03050a02010e01030204140f0319060504020909060705070605071e080603060709120201030f060909030503093a0c051207061a03072108130303030f 77
    0x48000142440c0c0012501c0391a00c501d941c20a44e10610300745040d21000010f8403408c0150020340d00ca030480761300c89045680000040c4041703c000e0030294109807510b0f04544040860114007801504c818411441c00c1c3d07028800080354060101c000840d081550401800900c000c4800724011503c40000c1802c2840001e003651007030010350b5034186010129503900000d401c003c2c11080500003036500040c0030803903036100c0d40940541b5544801700b515010080614000024110b1401d1002088084c444036401c01c4643e0b407901d4084c00e001c1601c000204030500186510707404440c009203805400b404061f442070007940507140c68002c6131000d1404042d0521a61031102c3c10400d4280c0ad51030300c07610303100c181c0000084030041d42000a9588940d4071010700346265005d900584030030015844013001014800e160180c100b40d040103d80040160110740d0311078850050380100086d403901082d0342e50f07603071802c070080342c1e80011540d07210740303a214002540004600084002c2800d01c0358481600600e440303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 695698453 1250 695697203 695697221
    0x302120706020c03011b0f05090a090c020c180c0f0f18010914030c0f060c0109050d021e07030f2d0209010e1018090f05030a0905010504030b0c0313050d030b040b04 72
    0x1b00000f461404e102550034410010148003400070a000030300b001d54030703400c414000348203d40012510340701012000f800e080c040310040344144d0085a03803c10083c90402c0302039006400401d01e5503140d01c4c060319007889004190305070403071510004480101007040d00083c2400b20003038880d94a03940d1105103440740800700d508081c0c2c166001e09603081d0305240c11204040303c244c0141040e441c190703000f4101d40c00c0d07030803800b0b054506600c0796420301c11003607041044d165654038184000d0b04006c540201e003500e80008d44005044819280c403424144019400300440d6040c904240e5030554510400c040310b03544034401d0a1384174800300030001510965842c10584031300741e22043c10f15443c1c01c00100e40007000d1045c0c00400b0311640c0e9205a0f0005031401248084140540b0045841d1000404001c0c000d1404e40c00142c1000742c1440308000003148204820b800a5035650304548079940c101e890000c2107014603000d48a842040480000c0329015400405040e00a844c10304c24100b044090105803400d400d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 695699703 1250 695698453 695698481
    0x6010305100f0b100305060a0503280c0e010e0108120c1903020705031f050921071a18060906060102070e060406091515030b060304020f01090302120706020c0301 71
    0x740301d894080003603070140d007103256884800070b0070449030004124221101c54042021a40d03c038203210b150714010713020744000c5c03c0460003080070b5009103041642d80e0741d003205c4004103105841409810440c0744c0110401901040280c940150b9480865034002d40c82840340d0741d006d0150307c20243c200190142156600c4440310001d04005905110808546498050075000c60040444c08510380d54180300320030811504044001021400391000c1088410140c0160500c1d40018080411040070b01204803180c06c5200340182c071142141400c0c0041c0511500b00075615900d1070412060f0999071303210910111603001143c80e5a0350b0040001d40d05c0809803044c030b02607401040100110003040d0402c070f900190141c0042039050340c80303403201c09454011291a0a8220400060112404403547c01c001000e051405109803004071012804510014001074084d4210381c03c0030242c3d90150307100100442d4060500e03042260101500d684403400c5010780d2005000e1806001003a127414002c580e0103036895 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 695700953 1250 695699703 695699713
    0x1e280305040b010e1e400212010b22050a0c020619060f0b0a0206092d01020705120c010c11120318010207030e091f0605160822060206010305 62
    0x4010b41a02d00b040082070300c082500711000000d4517040886405000d8502d910714801030122618011400855030700c80e81c6055035140145009502000482a415035010380301030001c1c244c2c2046a0b8090281042030503003184251400121180440350200c4442d8114030003000306441c0c1d00c900f402603e5001c100e000041c0e2186012900b4003000e03103c401e01445610b800002c0082d90386000000c1e44502d0b0313201c5a0100404110b41640e0782c0c06111700c0b6400032245c4084e11465a00c0281c1c003006007a9144414080c1c000f59610021b040801d50403285059040b000311902900c5941848800d80c0c48542035500c40e5003054009c800b1280507022442008004102a00d80b272402990031100d075800c0201a41c03981c58907280803001d101000c0c0700524106009a80319084c4038180c101b48000e5400142019161090000342800078401d2a200f20040c1c46892038069554070102e007215405162080e0f018042e030740001000300786140303005009900b0034404800304041319901c12090362245001d100c0a0413503085 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 695702203 1250 695700953 695700959
    0x60703050f13080912070803210c0d02071703130203010f0e060a090f1e0c0e04120c05030f0c0a060624030e030f180f040b0112021e280305040b01 64
    0x3d00d8014010042c4040d200607002144c03900280e103001071a62102006810000d0340b0303940d4a408445003400001e040480d400b04e801e1030190f440848c450104100c080030f5000c1800010481d807001c080b9a40108a440c4c952a801e01c806198405030356000224481d40c0382c48441744c0009c0407400340900d45801000a000c040c0d81d42000070000e40a800b0088030314030940000700000030f180118003840d19007031440b80310519019240a005e8a111600302c400454214000c000014414000320120203800f1700d40300200341c0442c40c0040c910b0051720503006407043e01140e039003117500001611040c02d40c02407500740211a5282e00040c9504008140b0034003461581c076040071400d0194005002240c14901240e29124003000d05100c5504152140e40f0400e03a583e4411000c1d20380700924000c1e5180031a02000900e418100203810700741d40202040006030082071803a868400300001514400703946c42126614240c2642148880c11000301c001140740d10740d02c1d07080300503109114443c4100d03800085850a40d007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 695703453 1250 695702203 695702213
    0x20f0306040c260a0b0406030b0f0702010b0a030818040507020321010e010b0f0c0114180607021b0d05030415080109110a0e0d1505092104060f0903050f060703050f13 73
    0x300030144c064640c0c0342c030300400c1a80c079540b00f0741005500415a0410900b098800c140060744090311080440e810700d100101c050b40c83e000a0030031250b008001c2c940d209001130620110700c22404a407544035142c04100004190040001c10010070144800140a02c40c8012012000c0c4203004030011218007030f0051000c00c0c0c1c048000c208500c8030f0104a400c1c514001422070a4504200b280c002940f090b04c00d000c1d2110296249004801603000500002c1c074000d44001e40c1e641c0d0340e405011a580002c0e417060410b0b281c8640202c001604403055954560300c1d0b09540e2100d202200001001441c140000604180380380b00b40c1c00505502e0449918004045100704c0e240c461444540e907108a00c1201c1c00000360045408012503252010b01051230710300050824284900802160482d10f85940c90480401c0044100c0e01070350b21600305003e901c0700307010085541c0320b000c0d08000d0051185c0b46908c1c0c09602c0003c0c041780702d40b1079607805000954426000c0948103105440c075108020714411404000f40f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 695704703 1250 695703453 695703527
    0x1a03130206091207140f04020307021213180203151e040b04060b0c010c0e03031216020f0a050708071a030402010c06020d11030105180417130306020f0306040c 70
    0x28100a11444011540c40140f906004090f44070110510034440100a68185074503010f80e0014100d80840c10340c0b400381c101a449840309000a10f0850700090704041400d44c520b1444090140001402508c0c8074914000000303510954071040c15070340040e16020a440c0205959455034a00303c011000460070005000291588041c074640c40f80e1240d0010170082002805070085000300d000201d144145000d0291004503028101400794004006504025002240c030070b403c0b0f07010920302c1111142800089050105a420840560240c005c42105002c00010382c2000c0d1849401586c4a4a03599800e9030080000070001550100041c40001c0c0590301504031858228054180503151061440c4201c0c22030b10b821101000c03d0b032000c0010301a0f81042c26032070f0301c0742c2000c0610b0000d43c24103407100075201d4581900780b101d2100004403c9544010041d1510085034012420742d2261100081000c041d0421203d1034052031510a0000d5030300e1103080004164510a0814070314121003000703001190b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 695705953 1250 695704703 695704717
    0x60602031605010b0409111e0a170a05010c121a090403080901060b130305070b0f03010512010f05010e060f010f0e1e090a06050a0e040c06200a0c1a03130206 69
    0x9542c1c52440342410303240ca01400800503c60b003a821f00201d1150104081c101c0741c0355447c40c0038a10200070112507101c1100c00c4090f100d01800810028102c0c10034946808074141006041d5420003c502c150746802002245041d00000814410603000c149544800460032180c0383e4042c00140109020a01900c1c400b500034242100204045413120f0f030181542d8002122003141903146081041400b00a01c68500617040240420b4681404100f9141840c081800b540d841140c9410740860ba01c0000d5000c00300c40010011b06200c0f039a9147d0f80c001d441a070460700907000f89560f24407450300c2d40c82540ca40040c0c4205844058018040a040c442d1003800d203038044a41d14902c4849090729500c039030086110300f00360300c408110301c0e040c2024000451441e13480307008001d1b11001480001100a00fa40c004e60341d45107030044480c5051980d1458100e072800305a06107004912105043c001005001e034203403051541c0d603201d440c280200b06561840104e581c5100d0b00c004000704801450004010145 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 695707203 1250 695705953 695705963
    0x7180b0414040c240c0f0c080f070e0405030403021219060518030a08161103030c0915040308030a110706090b060108090c01080f0402210d181203120204090c05130503010606020316 79
    0x110004c1c1e1f42c0e107554201d181e005030425601403c22000009410808800501201c1400342c482d400c180d0b5503141c1da8000c3c0c3c00020701c02c0d04030440d00c2502d074804004000c080c580303544000101002c00c2c00e01c01c0040c403007038444415201e011020703103056070130010444280f1005030343c9001440d6108005244004a0480b0034401c02003030000c04840b0400401c0510f025200000c0d00e41e40d01e41ca88000c0064041e00d1410301403407850140020804111084140ca50064030203d010640c881c1c00700f5403001c3c0d40700f1400001c1c401031510601c4018400d0cc0e4208610030107003a00d8000c17041c0c50344a0b146599058944102d80043c40310000030320301c0580c0c41c111030341151018082412440768888400c5501d441d0344464841a8820040001d034143d0201e20f070b1032040250034005201a0818548070100038105e10003406114140d5140302458103164105d41c003e00b9a10020060071001190003003160f400146250b02401e11600045001e1a040c4034000890b203658004501c1d15140740314a4042c4140c2d0b540a0351 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 695708453 1250 695707203 695707223
    0x1203010501230c0a0605090c0904080a0e150c0105151c060b1f02251809050703080307050a080c121603060305070b0c060901060807180b0414040c240c 66
    0x10340a10f04200c8003600ca4403401c0b0105144c07034152100341c42c09480302005031091408100b4080816811422507040d03954038a010030701c001083c400703d960000c6002d45003035080c80029507e80050010340c400c60007064004800c40e00f80d00d62408000d00c41c0300074804034045140580d410400250640d001e54038105010300540c0c12030783e130404a2100d40810880c18030250f044050003008454034084409200c80090f801c08a0031420400481030080e00b18007a000c05981d41c0f200103040c084100b000074004c50b41b15003071035070b030345418900200749400111581d80070442c54030128148400340300c00d440114200811926603680e0311803088441c061802400d40c10b041c0e07901c1010022510600040b00030f0050200c4a070398403503844414610300900140303100880d9240c0f14080c03005070781c08140441114004400524070010002100340103007680380c00300364810b1900400e81a420802d0140900c10350007821000583d565800804034550080c5600d20580b121646001420b18003e14200582c1800790a0a40c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 695709703 1250 695708453 695708467
    0x210f0423010914010c17040b0402090c0903060c0d060609230a0801050106020d082203181d0105040c0203070528061406030d09060903023d02120301050123 68
    0x1282004045443d80c000d9459028028078281c1009038020300b04041e01c1c034640107243c243c881c64100c0700c01510080c070600c0054046200c50088105450001c000103083e00c8043c00e1500304229240d002480c04520907061400024246000f40d040c42c0866860072020051481c0d1140c10443c0c07154940ca0a40d801820800041050882445103502a00c01c50300140000d404110000e085810f00511403181c11008500c0c40020107003100c010400990b050030302684581184000c03407020385043c0c1100d900c0e101c19001c003160b1503500f102024100e8609440400c014440c9403401c0b81c4910610300c0251850b80300f47c0c0d00321096000429200411504c2860304801d040c000d569081c196818051140c400074003c3c410310005107000d0000c05403c002034201124814a044c1010300360038090322020f071042440c061070844a00b991182002070384008154220b120031003541001420340103c210388010f04c034070703020491025580000c80703040e648140c41d18030180400010f10a003001031b804011641d000148100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 695710953 1250 695709703 695709713
    0x103020415020f01110306030a030804031407061d010903020601120203070b030a0c11010204082104210c060806010509060711102c0105070b1308210f04230109 70
    0x1020381c00d9405012803044030440c950070b5803070181c412081e040e4200140400c0d5940024034015165060a00c0d03501c56485050503100302c490050009a91400011034404001e00c55022040d04110031007018202900b03407981c94200c50000c4001405070f805900144040f03c0701c0100990694401001c94016a8580c600c502d615081a2250906503840d01c0b03042002039000095031840010300802182072601e81100180e40b002c00c03451902c81c144603034016090001152007194050140c244c2030640218072141c1c0744000e80144c82003601d10b1005600082440e500c1640300798050324050703450a041100e610204400c990090f0821100019100b0b10300e04507440c0d02465020445454031510180f0f0203030b50184000c501194085083d40d81d02d0b084201c03490b80c01000b9038180302e8000f01007046a81e1084c0320410310300715010015003108004100048903544e0a480e0b19601001180045429200d2640d01c00c542441600e005203044180d940c50b842002c00d025001102c800b480c4004218000c1035215 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 695712203 1250 695710953 695710979
    0x1e100b0a0509030f150115230304030212030f06060a020f07080715020304030c0b071e230115050103151a1207020304062f030c0a02030606120a1101030204 68
    0x1200340440c1010582501c545000d210005101550130042c01d081c0031114000e03203841300705020780080c0c0250b11501d0076210f0700c58413554031800603035075a0201c60b08075400d64000c29081180c04600500c02d40e2444070b003590165050368014511580d42120700d840380300811125800c01c1003c8011881145001d0a40a000b006800010082d0001402c60182002c2605004100d071805640642d44108070410008240040304000c84241940d072503222902031a0035010408503102440c0000201317548103090144031380c0c8a8030090001c01d1099070140000400078240c1d01207030615801e148803100c6c10041540680c000c046441e010b0030300540c6494a94400303610b40706034406409090310010a116032848955480540c200d03c0034001181400e242c8140100410120b07188040d910b0403221003103541c4071203182d1040c10110020187c949030110034004039078401e00c4d4901a8428400c0c480030500908003079500c0c4d11a101c064002d0200b1045944642006c00d0484d001241010b81c20030000507403d0060072 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 695713453 1250 695712203 695712217
    0x403050d12180b060a33030e10051504050103030f211104170304211109011202030c090c0a030e0c03070303020a050f030a1e09090f0f050f1e100b 64
    0x483e0219400e0000503c01043c0c6540c0004c034901c04811b05400105221034080d1b01500360f2290324904404650704202e000d407035a000d18011502c2102d118000c110010f030051442020b6090a00380241c08820800054800c20b20000d1b0114501c03810000322a0b1092000031613a40180d8088076514000b5150902103e2500c490583c64a0005c1003d1007600542d07071038602c4403403800c8011800c2504044041d121001c0405003201c0030a8181545c00800c02960009004100000c0c585051076964141c281045500383c0c004905c21300485583d00c0c40e52404e8281d40f0f01607552820054213144c0902c2040c0c00074800c4c1c01180c00780d031040310900703002a0303010802c9002a40c030030f5019101244040c6455807a080c0502c40441c1c0700e4009020740d540310780d400a900300361038000c054440c503603440310282a158503600e508000b00040c100703250644140c080741c0001e400e5101011080106560f241c128808058069801c100c0004001084401c04208250410f8009203403e030000400d66580c2a07020896000300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 695714703 1250 695713453 695713463
    0x603060409050d051b062503090c0e06030115080c06131505090907030c0e2101060801150501020624120610090b06070b01180b04090b1b0403050d1218 66
    0x280031700244402c2d01c101a400421030008103240d00b03040550000da00901070350a03500100f01960380b85064402d8018445258004040c41005600d640c02131882c400f044441c24029803c10b80e28490b003c8030441341204441c01c0340b0140a4400c0c0c103604200b2680d0090340d403403441c40034444e400300714a600c0d202020020b510980340c21b65030318030744020301c000c0105c010011400e05103003001e071304011500540400300468048a184038010040345d6420b021062010302c8418561800a011030b144005603c10038481000d10b40b0250415594001280d40f00d0081750f5114030307040038450142813140c21611a19220400420000010640103c007034a0302004441c040003007103a0f0481000240101d00c00c1e03885014090301c07103a1601c400d44e20340009148061042c0200a00320b1800f1106000e000d90040d000b80074014400e102d214224141000b09a0090703815041c080740782b0135100202d500c1034007240c0460768841d0180c081103c2c842d000351140034140d9601c0d8500307900e4101125441e02900c5020f54590f211f0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 695715953 1250 695714703 695714707
    0x30d0801140d17040608181009230a1704050a09020a020102090d0321090b0411040e0304170f03070507030308100e01030602120a020903071205030d02040b030109110a0e0603060409050d05 82
    0xc144010003031b000c00380111140400b6400c00070050500401d0603284408003001c081088800361030401c0c4203480c1d040d0800d286c3c6c40c0d400c0e544c050440e408a20380605502500000107284a80a810841441141f149a1307202d6041c2c1400c01c070301030050300909a145114000181803502c60f0000c107180024010b0300714001040400d0072004a80c0321804841034400d020360400c12260380c8d6881c807510200c0984050580003150850181660703607a04484068020032040d662603e41d10820140400d048043c903140d1402280869148a1800419500d00a8114000748951441c5440560303110708080c01c0c0780003000c0303002d00103d2038200900d00c3e02e000318400d610040e9210170a001d5103080c548041c110030609801000145d15603580047c03154181c031074000c0004402c00462600e9031a52142c41c1c0e032203198500219000030031441110145049820840c4240f2403000200f10040c40d41c070a901036080071940010780010a4103194001d1580613401600000b41020544c58140c98050200c400030005880 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 695717203 1250 695715953 695715959
    0xf06081e25150c0305030c16150c0305090f070312030e06070908010e010c09090b0d020306090c091b18010302090409080c1209060403061113030606060e030d0801140d1704 75
    0x5814206072880090b03e08102804100d0398020142d10002d8050ba900b07403004600c04000300001035000300c600340e00042400c3d08a502521080c0601948440200420325241c0014502200400d0078070401003040d01400000e42180e44008014815800b61410555102c0c484170448104002e41030080d161a1906172000b460b020610b400e4034803152108440d44d04054041c0c228541014600058540340140880d050328680e001c02e6255480e510060350520500f0b060104480c07010540c4405c201c400d8a044079203503100c480142d0a56121020000030000c200004600012500380540041c9014503015185c070400c1c0002400360f803051001554121000224215020000c001c030000d0004002400b0341010556030001c1c0c1b003809184006480d00d0703200c01b05001c0201400044514540300462184001030701c80c100040107220b0381c0280070204030307883d80d03410a6250000b40450b40f06071542c0d0300b44680c0e003098030400800c4804200260021038064030100091450450965448501010b250326103103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 695718453 1250 695717203 695717219
    0x8031f0f030c090e07060f02190803041a0103080a1206080a200f030742020105010b0304120e150403060b04050c041208071b0b030403030f06081e25 65
    0x2c01e5000421480c500700c201034100c900070400310221022420b0805078036a11450076410540c096090002c51501408040200043c070800b441c020360044011200003503403482c00340c90040080c080602410020321562021910505085030542940d50300030800d581e4886042c0d140c01d40c01300e01214804d450f0018580a0f0f000c0a400440c80c0317408030b491085030030030300d00800d88540150155a2041e6500c0031185030744c040d400d40105c524081000342d140483c03a015492507407220014103c00040d4201400082c6064100f8103403405907402c04082c102c03c4985010694003030181d07a0783c2c80c1e009000e41105c0400c024030200580003c602980010a200e401c0b0002c010031a9001803465800000900c001d101580c4813628083c4410f50003c0010b9958405d4181808416040d01d003920300e160034400042101500b60025601580c4a40c4060ac03203201c4945502040d83d1144c0600c1005038441400d48030110400600500d415841000361340301c482c1012001100c40309180308503800045d01080c1001058 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 695719703 1250 695718453 695718473
    0x23271207051c020318031e0a051c091a0c12120c0702130c090509160905090412050a0c02030307200a030809040902040f06030b100914011512050a0b1203070f08031f0f03 74
    0x401e000c1b5130100d14420040ac098400b00c51406040003440d40724601030b04010b840e20880341840941c44c111000c00390301002748041c6910001143d241c40c9940008904040c1040e42501c0e441c40c0d0040c4809400080008818000c101c880034810030015007201c00070b0f60351243c002ca1800303601860aa255440000130018003424070342d03030107280100b80038020800424020aa050860b0b0410700d0032a695420303403e0f04442c01d501c8000081d40c1030000140000800c066011400c0c03d180e111108142d00d40314220030400036401510000c0d16608080103a40080d1410780d0001e11654801803000446100342d84699080b01c00b07503003084880d07440392418450b48480311031040300106006581031103501c3c01d007104407010300c0044c454844a4001c1402c49013009000b01c0c2d54402402202900304060714055070201d0152071034240070340c02504c81c0c4a0800d1040c00100880740c5c0c05410000c81d0610154a0341e5411180d48000d0803684402c3c0300030540000c603105020440c0003415601008034140e03085007041d030314030303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 695720953 1250 695719703 695719723
    0x10c0b070e15040b1909030b0708010e0606190809010204030c080106030320070303030b010c080d060608010503030901090e0402120604120323271207051c020318031e0a05 75
    0x2c03403080c44100200307031551013250350081c14011240000c004481041c2c81380e89841d08003d00313043d00300080080841d804030140c1c0c12108404800a8642c0340c42c000d00c26144900340030001001c48030803104028038011280250001c607000001443c043c0d903078403094400100c2c0d8100382e00d41e9440302420001d16500030302ca0619903401200400301e02d07500d0207844d9518012480020241600c82c0c001d10300583c016221050044d0300810b5072659034619802c0309005007020301448001c17690300300010038030781030010940e800280d045c0c540260040c101900d044c10080e00520803a400501d41c03500b0100c03800b003800701601441c41403c20440f0b01c5682c03c00541661034008007070a030140e40b0611071f840b045200c203180d87c00c00d8610492950032007084007501450100402c85800314490409007581c0360709020000c0c09020b0241003034802c440c418000c00d070094010740010b440140d0007402481c2e00c4090f54640d04801c14001011600c1e00e04020b0b519418000081c000d116940e0450f07400340040c00000c0c03042002d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 695722203 1250 695720953 695720989
    0xa0620030c04121110110607050c030a08090106080313140103090b060d020102011104081f11030c0d091b17010e03030112050a02090c03190e061302010c0b070e 70
    0xc5142840070070506009620444245007005183c01003031003811a0143c441050140074170f144000b4400c00640003068a200c44031091085200003011944a842507513016807006003e146400040c000840b290840640802c0f055565034200085451042000b0b2051140181c403801c1c040d4a01103c081e00e04e1503280025043c07508090150340000d554144a80d440041220301c44070207846400100d0050105403543c0d1190480010041845070000519030058040300c203003206c1e008054840320054441e44540c100441d9414400324050380c8140700900aa2002c07010f00046000a83d20741585801428080400b4051544001d00041c010380c1e0402c204140c08134002e0101200146400b583da100521400080700c0303031207005401304a01401884810750700244108010f0070944400305440d030090311001c8000245100d04680803844e8050800d042012102416040c1d07104c0501c010b9401c98808100d0401050a0001c0001540f060010703020b50601d60710f80c60000c1030b140900c284400344c1140044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 695723453 1250 695722203 695722207
    0x11e210203090a0602210411030106060201020c030a080601111b1e01021c030f0203012c09070e040812070e03120702060301030809030c15070204150311100e030a0620 73
    0x5002c20002442034005070301240050342c500d000003000420308141543c082c1e0810034002404140f20700200d0310385c10711104034020070425948800c142d08070b100700710750702c0b0090b04140801c60000780582201948105c040c1010120810031007030140c240a2808031403001c20314081031140d801d04203800040003a4290b507480c0552110461300107956554091100c58481c8604000041c1c03803486034102c41034004c08000f080d9125615040740036a0b2214600b10000b118142c2074042a0320346c03810070140d020384540c402506545040c1450074411031710080c0305445441c010411204217140c5c1041403841181c0580d9286110315080307081500f403299110480b2480c0071300b44441c00160351f8120849045980c0b101c5c00350b6a41644c40301107424801c52101440d406070784949a0281c02182000614030a4400c0310b08120780108800400b103042c0a900010740031040d0309a030840c80d410041040c0f50103003c14208940504210000640b4144410350100c0d00c1c2510303180c10b0b4030f43d40c5680c0c10040d441400307560b06038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 695724703 1250 695723453 695723461
    0x80606191214060301141b0f0f160b070504060f08040213021201240c0809030a050f0d090b0309060412030212070903020f09040b1302011e210203 64
    0x1954902400c6486903a0400c008800a0418018020307000403644516040c03000b000d0402100c0c0007484102c40f828002e5007030001044103d02c0000c21359101d03440340d41c1c00c0341d401005444140541d4100b0514410340a100f00241100035200b00e0207405501890302ca103440d150103a2402c5512000c01800150a00405010500907941c000a000c80c1104640c900190580d68600003d00b07910142840c203080544005079824541028980a40c1603074504000c1441d00d82e03111620380c1080f41184044000600bc507410640001e22860040126205c010121129041c0c03540712242080509000c030711855001ea9202c0e885142c01000714401031030030510381c5041d450030306440f42d10381400910080c9403040c4240310703112142c0240d0640d40034001b0030b0400340007460905809498242c1a00007039100b045010880413451400200251050390300241800f400c0e254030f0340e2415104401c0c48203d0600c01141404c0f14040102d4103030100009081e5100303020781d843c010f040340301000c0c103082d00300c90f10340104108 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 695725953 1250 695724703 695724709
    0x60606020f010c05030a0b0609040c110d0e0a030605040819080106030c0306241110020414031f0506030312090105100509040f0807060b0d110a0f060e0913020d05030304050c010806 79
    0x11780c1e800038020700d01154201c0641c00080041c8203d420440d4882c0c50800c174582c141e6480780d070302810030940c4400c4402070007820500f51085041c8803000c1d544041e6103901400000e500f90056074100d80300e440388504002c000003c809246c2684175035000083d0f4210f0041001c1030b810b000c1c00c181005a41010004981812a443d401000b010071030520f107010381006007816403152900940c4100504141e5103000000c00303950003e54014418201d0a5000031101c400c5407030301180f0001405452072040b08034410469089000d030500410360f0b98180400d120414000034504001352180030b0403400003a261411490030410050a9040240210740000802c00080c01408642001680000060b61940d803145000e001a0126200b029000a0380400c00b104000c0d8141c0300d2040d801007210032203662a100c0840304d050724094460b11001661400b020701d41c0f41040e01c034264011032110103448841040d60082040032080c2d040072115540000104800e000c01070110342c505540920384220f5034207001d800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 695727203 1250 695725953 695725957
    0x150121050709090204080613051203040515010b040b0307030b03010b0310051e0606040306020f130b1b011e0b0402120103080d0e0a030e0906030109020312070b06190b130909060606020f010c05 84
    0x745403800b0740d48c0d40d0001c00f40001000000c40203c00800b1302d603900e240c9480d0468444003102c0c81c0900e110360300000820b139514200152002d803100c0c60241821039680b0b83c022809044000c2c401ca0b019581ea900031042a1030511242c0d0302e00c40c4c50710011642e03080c010002d0750455800d01352054815030603410b014040d580c510440341260b400600140c6c6808415140702c8040c030461444004815a031030000903108200006420aa034070020207000082c8070741032030740c281d425034502d110342e010317000c4603d12150032198044000804098070050405001144c81c001400085c0c000741c50310900030038800e400307000c2c82c001c18001c043c1c4140a0920440316682c050004445072201c28400d01e1100001031203038800754070039000070b80c005048400801c1030350652040c540c0305000640d561040b18000440500b0040c100402181c40d001445003120310b048150a0700d07400080c00361080009404c000908014a805060052805600d0000306c845ca44600a450074a4040601c0080d0741026034009200e500041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 695728453 1250 695727203 695727211
    0x100209010c150e010903080a05072d170702010e07080f06060105031e040803060301140105030604030f050c0307110f010309170c010207062f121501210507090902040806 74
    0x8000207042c1c0459954078041e0000041846103036292101550516034404161801060b40810800c1035803183c43d42140c1c00d0740036100c1e1200c1d85045115008006000c0760604048c0c02d054a06801d0030001501c6c20384042c00c0a0f40c101c00141e44034810204800c80c00c1c0860b000403e4220000c090711003c11030000c0c0c480e0710080a0342e0512001000155652010301f40910a00310713181c00d01122850140741c1f102071900141c0d1501d0107980b82c1524205003404a0000c681079950040041c500c41d6620b0b80d0440342c04c0d01405089d0304025003448006050381040025046480c4111840541c0d01c000b1414090b50301c0c1050407050401d070030658007601042041c111124507041d1881040d41d00c0e81d802610f640a481941700041c003081c130388004010b08844034806543d00103a01c01214100500f0002501030b02e00030419204024032040f03001c03450484001c003000c0c4c8010418140412404102511610082a0241604010354441c070400103100e0340000c2102c040c0c02104c1d011400c0c541880c000c0b035a01c2c40010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 695729703 1250 695728453 695728463
    0x6150904080c010c0210110f070605090a050613151107110402130b0306030607020706021f0912110610060918020f031e150d03080714030a060602100209010c 69
    0x18020405000c4014111103041c4040c0000b0301c004074459400030365980c1d0440d450f41c0c51618040030304461003a80c80c01c5884010501031950305101042e1a180020030015042000e03074030812800c4800a00280181882242c021440d002d20a020b802c1a44180d211024070074070840c98107000c038620490341c0d010b95042d19007014008003040c0307610001c00e00a1040c0c80c940c02101c0c001840004440009000440c4030700801c0d0160344040d02c3c2c50805076a10500c40c0a50000340e04182c10f80c0c030001e00e680030b88070700102c1d228101251240e450303120701c0c0000c3d692034194400200c0305140f40e044c500c4104041c41d0001e08030a082102c091600130010302000540c01405000f0201e401b03c4d155200f13840d019a4800c4200003001503880c01c004043c036039041021400c02d05e201702d0480004980d810808030000242c00081e200c1d643c10045503800b1580c00800034030540501c180700b140c807000e00c140d020240d1700c2410300007400103640d4104030000e032600081a003406441801000b21034041d0340e100b0000389000e80d00c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 695730953 1250 695729703 695729719
    0x8091c1d1305090d020c041a0105070c0f09020904140714130b031e0702010c05040b0f070501090809011403100e061f0203030105010e0904020306010501050d0e06270615 74
    0xa030300003180c51103a0500544035030304000510005507070100300b200d88506607400b140c44825610090100f0b407a0900c1c01e0342001d880c00b118070b0585d9401034004040b001d100360b04210a0988075240e00105d030b0030319040000700c142d0100704007140f41058401c00c084000a00c251402d41c0c41c0c0f03184010078100f8207040c0c1841d261300110783d00002e030040e02e042310040e092403c4042e4036032070110103089120045505070f02030a516523000c135221034011f100d21000d4a039255150f900e46800c000c80b80c42c0562003034055243c0500200a0140030910a104444501d40f0844a03a0340d00e1201c0000103100280d002808a9000010418004840303000915035088606901c00744070a41c3c0c80c4000241c220440100d5061503003c9240c0038840d0f1079000c001141030790301c241c0728010750070001c0c4140041d0080c104c4009426a03c56401404650702420241c95081c03803058020400d495221146803d0403000d91368081c01d004071092000c1c0000b4508001e40b4176400080c0108010b01d03200380300100040038502c4480c0a0802 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 695732203 1250 695730953 695731007
    0xf070501020304201003020f070203010618110a0f0c0f021315091823070e07180621180503040e0a020a08070807090902030c13060302040b071704030501050708091c 72
    0x248d0075070f40e200360010000c108450382c03141c012400840d151040d200301482c0103485c00c81016014127540031807010b941d40e6440d20080f504180c0d4010048071041e55400e44030b407003900060303803a01210304c0d0002080c5000304810b403643c4044802d074481d0f40c1240588a00706450498460a81804181c4194002104204a030662066004030b200000c400c803640340242480894840c45e02c070405c1d40200143e540c1c000c0e2682c200b10303850002d60050301460300002c0f1215000c0c010301c40320b0078506441011514001425180750340c0b00a030201b4800c40708070341c8c981001c03070100884d4401c982002e9010441c24130035490b00840c0b490041a03410028040380900c0781030408030700b2145c0729941c2e2001800d008001195a800c0a03154005160081c12003076080e10180c000200325584070703000307860071509080201401c11003290760f00040003d01d100450388000c018840007001c02c10901510340210f40d141c44e40c01d0b042c10320481c800c0c182503c0240700364040080c6580180e456500c8051a01c07184d00e8003010440c0f001c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 695733453 1250 695732203 695732227
    0x2010c09081b1e0a0608040c120b0a0c20010f060f140d1e110f0109030c0b09040213060504031e02030a110105070c0806011401031103060f060f07050102030420100302 73
    0x3c10b0300616000b000d89000030515640104101d40a5801500d100c28650f90390340b1604048000031a00074803914031940421103c2c601c9402c03240c07020f01d03142400c500300e00a84943e58490b1001150003e240da449580c01d0091565522416000d0302206440c440c50301d00b0032061500c4041d00c1c80060780912144007030107040c800311908075000040060f4001e5905402818001c12a02c10a00d19a205820032900001190b020340104011070b54040c0c2e4003900c040c41c0c0641c1c0890781d0051001d0036040f0381c0800211414921440c1c00c88003500c42c0f80c8138544c41e40e09608141c90901185040a0b410010010601001d42da0005d20075072055444100c108920842c0701c012551800780c1a40180b030350042450100e141c03140445e1540c10f81d03190010100b1802c0d008070044080d51401003421703040100810101c0c2d010301382600c0004450700040c006070b145c000c1c0200c48004d01d43c0300040503100c036540481404100f104220400701c1c60740c1c0301e80000004440100003c3d100030b040494160070b0503800181035003506 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 695734703 1250 695733453 695733499
    0xf09030602130f0b0a020a060c02011410030b0603210f1614010b0105090a0905040c03021215060607030807180f03081b0f0d080c0f0a02010c09081b 65
    0x140e4400025500c03950550348030710303101c80755006054451002d440c0104605400405694400040c0da00a00030328040c0e85840006000140b0f464046540380c3d981411410450321a040c002c801c46030315038654601d1800c2079608500090b000910a400060301c5000c21008045c140d450150741e00045079654840001000d1544204442010078481c0802c026080c08114940780c0341441c1600024000840e2a9004480382e02c11212501c1c0c1c001071005007408120a00c0d44840c1d80036100c0c540f800204c0e92290001030302a8440b0594600b164483c2e9072864030320607041c80003a00014252402400c000d00b5607005005100010050020840c0e00c003e00982c2c017200181a0340100000d1984000300c946a0418a202c0da1180c0100f8002600c920100c2c4107445c000200046040c4401c0301401040c613040a0890300b204001e000c101c1803910520001e808040c03c1c40040c06c8550094000081d02c802c00f06001d4210308103540500e1032500304035400c8154001c411180d208041c400c0f1482c80d440c001c000c102c40400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 695735953 1250 695734703 695734709
    0x10090e042904060e06060a1211061b0d03110a050f09030a02120d021b0f060a030b0301050708010501410d02030f010f080309010203070f062009010f02010213060f09 72
    0x800040024481880f01d90752140c0760b000c241c1000c1c0c500c55900c0c0c905000e4543d84901c110403400500b0b850450106410440074120719000502c12440e1400d9a000c0041085154401840581045a0320040030760580b14803059420117041d105d04185201c035010382940204210300d5003240002410802580d0300340025980c007a4020031302610764200e4540d46540d00c00807000748015100340103030f00f0b000681241c40b602031603000600c004402c044420600c03000d90061040c0c02e00703050302d880840310159400e0240c4e5120f0030700b40c1c0c4e801c5800d614000004080c0c41c00c5c441951201c008106444900e1854041d01281c51500342d0955031101c4071429800d0214440c104041803c0b51020043c04400e15908000504803090b0382024000030740c0b1040400d0300c84c1301e03100b1414050b074410401c01000074805ca02a010f4180100400210b03c9a01801c4140d6454108101d501d5240001205a40c0d0360b0808100b602c651b80d9440218181801c07400b02101d0fa1600340160000d1002c02401c08105504c00c009403406 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 695737203 1250 695735953 695736023
    0x607031b081f0806010906050d050a1e06050a09021503040c052407060f05071b120e030a0f03020111070507030215130f0f0501051c15090207080910090e04 68
    0x2481c1e90710095031341c580c042030051031041070034001c00041030b00c0d02e20000741481c1e0304170380501540001690349405022160b110180120307031804148011404600c200342c402c00da40c51000c200000c143c4100200c1c041181c007083c01c640b0060080c00301103500c141004080c0c07241918480c14201003840c440c1c0401c4602c158001c290300002404108010f00c030342010f03095203110f0000f403104d5180c0318800c0d18142010f1105081c1060024000c401080d045010882d0310045810064219401800402e00b810000310f01515114110010802055424400e000544941c099060b09051031551842d46910789844064415500038145200501c1144100c4021030030359045840065501c0c200c0140000343d6202e00c180c040000c01d00000c60394000d4082b20b02c00510805541112490025a0b0f0001e0402d080140a0048004c402143e0b0300e11510040241b140616102916030300f40c902005071008074200004100302d444501040900d09000081741c00c158050307140c90082c1c01404500700d803101001c041c005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 695738453 1250 695737203 695737261
    0x3050319110f091011060c09042705060c03060f0d0602090904030c050f1506010c21021b06040b0403120c0506160305071d040f0e03030103080c0607031b08 68
    0x296182030b00d4001c21803110305840140d1201c4602c10207444407103080310310414607000030002610310044c40c001045050f10041c0001001c40304659040004124808850003100c06110071009000d07082050300e602c80107042c08a840c51802d84040b404042c403046009000d903104a029800b0030003079406682c518400a00500f000349482e080c000c00014240e1001d680b540039144d080823840710301181c0e20001d800980708922160302d515004542c07044100308151022524058983c0190340e94110803806000c00764000c11108068001104817910120101c40c481c180804c810440e4000c000103407801c483d000349000021a840080944204a410314018600e0281804201030121100e855805180716580c04101c50350b43d010068601400441000150b000c441350102402e283c0381d00300342c1701700c3c909a0000c101ea5034001c0d920b607d560020b8004030b86910303001c103403020143c00400072035501406c2498140052003c1d0000784151003d090300100c00c0201d0400080d4251500b59000c150a1610303480100d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 695739703 1250 695738453 695738467
    0x30a15052101270b010602010c1704050c040614040b040e0a060c17010e160e0d11030f01050109051b03102907050a0c05010c0206030a050411100e1005070305031911 72
    0xd03268104101013281da9445031000030031450b1052142c1ca900310742c47e8030703680c06491140c800113030f01d4038005008035464440c5145461007a00c4c5d9000d50002062a0720103030b401452184100820b90b4050307628503000d82c0c546480624440700001d031260f40280c0140c80050515002c144c11a0108221100507100c04004d800001e00581c031b52010354490b03c12602c08200d80c029000302143d400480b40441588130b2124500003010070580703e81c0d009440701c000c003140c0304001488000c3c0e0070340e1002da10890499580d002003082d10002d4040f040304001c0c804409034910310301001600a1484c0c2401401c14103486808069200050a14450341440700945d0040e1107106620f13041d03030746242c200c108503425a03c00e040084d042d401018400c4009500410050855456900c0031000f8003000307109840740c4101c80250807080d140c003104541041c001d9501c071169040080140604070380d442003100b0400c01c00700904004070307a00c4015280c102c0c5019072102203091070400b18001401088100b000c51050020b504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 695740953 1250 695739703 695739761
    0xd030c1412040308040f050114070b06030f1005040218040309230d05010c031a0612060a0f0608042f040c020c0901090608120405060306012a08030a15052101 69
    0x2e0300c100c0341d9280300201b0040d00c0e1401100c0e100c19104007011100020302c0a00c00244001038070a9000c40042d0868446540c85c500310f82c50700b4443c00b00b803402250744000348030946c140420702c000d40545101c40c040050038070b55001446404e0394030a400c1064034000c0a85d07000c1310300f6503403500300c0e4800a04400e01000103082003802410407410000c0428a8107030f41040d10107566095209004000b03100b94100f030121242ca00d00381400406040d80040100c002040c004247c80e2028041c08050340c0d030036041d01d0686030042c0300140700080c0101481c418102c6902c0f0008201540c000c0200c141c601040c2004200005c2e460110600c52030350344103035508004500300000d40d11040c1214041c104560f0791788100f806034442c51285010791508081c00300009510340d40101066401a803ca40b01c20017030000c0300c078000b0048118000c007110081e40000030321030150440d028411545080310ba248440e60714007c00200380200e201c0301045424010590104880400e5205010401c2c041c2420803008540d0018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 695742203 1250 695740953 695740957
    0xa06090b070f320403080403080405120a050606060c1606050a120603020a032d030c060c030b0f010f051c0b030f160b0304020a050303180f0d030c1412040308 69
    0x20000040c00c0a4a000890352284003110122a01c42111201c10002800940883c500086010003a42010400040090104002000254020b901a60f103c60420040140d400050441c603c0303543d110202e84e0700400d9001c5545600700e001200c60503500c00b0b0140e1280d00745007414032241603801c0740040004016070000002c140668013503031420302c84400150b125045940c240000394000810300340a00004843d6105160302d4000170803c00c121890178a12100c4100c494030080300040e05107292042000b0300c80c0160f010040107420240f042d00d804101044592810303014a604100395801c0810300240500c040360360b1000700e020414070075203007803101e0000703400d501c0c25040c0244030740100c6002c7d040c400709a040d01d2811003085894900e00e000c1d054100d50308007400580e4460b141d000001010340d0700700010000c45c045d5441d5400c150500380c041103070b603a030200211801000101d41d4040000c1d44009440764440d80941038190b0310f6001c180042c6414148801c0100b02c4600243c04414413150b480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 695743453 1250 695742203 695742211
    0xb0901110c06010b250b07090b120f060604030c060e0f0d03020d320c07150804080705120409051603020a020a0b1b1b01060b0702011b020d150f060b13060804050a06090b 74
    0x23a40741c0c0007903582e8000203c030320480c040184200140c801207141184203c1146801000c0200018200341e101d4446248503900c0c0d910400202e101c0c1c1c0c40c1210a402c1105064600001c2240c42c00014111510040d466001748443e40d02000180d02d02045401d00b0b46100414003940c1d0110701a820a03041c0808085a1080c003442d21280309840c400100014101d00300360340e00000341c0c0d4000164689a507518031a81000304201d400c3d0084001101d044200d20000d00000e00d00322001103082d0138411402115041200c4268040500412180c40299000914445c0c2e955118820441a680e040384032607024541d0744402c154210001303483c20040039002c80c07803070302c8600f84402000b016591310820b0701988110b40c4003e01040d0220a0072101580343c01130203107118005860407040780b50a58442d004d41014581c0311020664420004224146c24881c1c0c2d0041c240b4541011b14242241c160040c0842c3c55120348401c00401c0c500003030410609000090301964001001e100c40c0c41c091504000b041c001316 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 695744703 1250 695743453 695743457
    0x40e060a0f06020a020f0d050d05031b030f010501121a0d060b10081611060424050a320408130b28050a090603050c04030507030b0901110c06010b250b07 67
    0x94030310341186420001c103d20140e000002700b111800d0604280c800ea0002014110115115507514041d452107200661140c00703405010021581030100141c81202030b07800d002c001c546001c0040100408030006c80c55440e60468601d02c02d2441c914040f03003e000818002d0750072035545e0450b120040e410810007402205000c0310503c1c480000c0404460200c51035282400950000c40414045244405044040100e0401403081d0600071b414120a42d0b80c05d0324420062640c038441c0000300104c001012440312280d00c0054508011161802100e10b000f600c09800311708001b4100c0701100285c50300383c0003822070040b029110540780810401c1403203920141c0d2400c0c1ca08511003070080d44104110340303a840d81615001c81060030004210300a100c02070101144620802c0040301080f000c0102e0b000031031040c41c03801074515000031070b42d0a582d0000c2c1d03d584d15020911000400c1000807811034117560b01c00070107548540e613045428a4258440c14001715038007082250b1000d100110030740c1d5104030116 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 695745953 1250 695744703 695744719
    0x11040b060f18150a0503280c020d020706020309010804120e0d06060f050901051f02070f0b13060206090a06050c0409110c010c020c06090d0c09020a0203120615040e060a0f06020a02 79
    0x1c00700083d8148200c40c261400610308000203911900038001c000da541c8036020307603001c940110013a0001200d42000100001d80d210825544060390304000301d501a000b1407010f1420041d9110020340f0040300984002d099450714a20411554418890360700071040082543c1440d0b102810040c00405181c0503040300c50b240400003003918100000c4550417514081c11144a038040e20061000361180800c0c0c0908500826100088156600c0399030300c050b1101c0c20610740d4654620015114900d034540c050401e541005041080480300070900442d12a005840820300703551b880780c4c0756050300c0703642c012400981c54800300f1658400340c5000340c11041d1980b0000c100e0b40e20035401c01d0b81e8031008042c190740d0004082094840d2802c18280c1012402e106412402100340c541488005a81040301e0680050340080360341d420148034004116044071041e03901050551042c00d001c00c2d42d00c558080c1c8070004071030344042055500e5401c00e85000b4940d901d02d10030801c3d29580002e444400e81001603101c0c1c181 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 695747203 1250 695745953 695745979
    0x50708070c0b0a030b03010b090a0207170c0f1006060507031101020408100902180c04150e0603041a0f2505070c17010606110304300b040209010e0411040b060f18 71
    0x500c01c60b002d580300103149c10030964030200000c0183d40f20740000c550324002c00f540c000041401401418030708101d4400f0300981d1143c3d02c03100b883c11140300a0500c641c0d040c004c0c100701300f580160031640caa40d0545040040081440d039518060b22496001180c2481510030b08606c0a0380d0342e00c40985e9910840c0c401416090b045064401d51000f075903040444c0900300803c02800014424000703445802e070600003c3c10701c0b070394009035054000300c4041d03805144601103d400c030182030000c154043d0540310b00c1c80345401c00c40c0c01005259200441086031440d0054030320111360080702502c504541c45000d1110240e245c00103400310512a16070f501c2107608022000c00c0c40303070040010b40907401d210030007541480d1400880b061600010005103401408111141c1c00b9115000703802c03d64035025440c0030f04103041610501c098518140c2c010050b0251900611000640c0600109211002194082020042000003401078881c10304140107508000030302c2c03940c841c00c0c1001d03032650107800c03140b140b4840303c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 695748453 1250 695747203 695747209
    0x160f090e010e0601091a1c06061a07030518101d010f0c150b0613081b0102060a0c110a030207090e0c060409020703051b1e07080d050708070c0b0a030b 66
    0x1400d07501e41055030700104010b0002c2d01c0168000c400f1071084086c0220599100808640d207080707510084c0c12131103100c400394403d110307890040b00c00a017910910042004480090802d103400f49010040810400060070070180704a090030781c00c41c100051034100b10950304103010344404529801c41340810030030b448010080d805144c44c08541d0f040307074595144510031a41ca40244100710700b103584605585020b000c0719a10381d50081c00c90080f081120b5141a41014030b02d46c942130704075100d000484c512104c0d86801e80d90100c1c1c1990884545e040c0031449004810003601c1d070108c24031f6520050b1141e4544141450303400280203040301c403400c5040221100c1c04c03c003952920440d080c0c040e00400c0400040000c414241e00070305a01d03000c1d1a101f0300702110101c1c1c200b2190005420b0b81c0a59000b8044040740443d002ca500440f01c000341c0007040c003d4501500a901d9036041023420382440004501181400045412100702d250b1020001c010300340c689400d00015088040040002442e00c40c0c62113447c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 695749703 1250 695748453 695748461
    0x40501081c0e03151b16140109020616050f030f12060d02030319030b030712031d09060409020102010902190303021c051c0b030604061a0d2102160f090e01 68
    0xd5009006402e424880b95002061440017411844820300c0300f00c5040301e05401400a481040c0000008000326125824011701c241424100032a40e070b4540001c02d40160740707041c100c620400003070380344030700e050542d007049410600075003000f41890000040707489500c11810010040c28000d601c643d0117a460b190309210000510341c6000703401d40e0041001d8410340b05a802d403020341414903c3e002c42c00790000d80219040100c694400b1502c4002c0c04804020150403126070f8041c004040c0e000d2041244030380c009419a1800f500c03060085a0741c04500d0196403003900000807181e00602040484040d851011b0703c6d030b1015100650040c059840d00c46184242c50a0400007144999903550611142940580c042c44c105000308241e1559004c40c18510b03202407006504c40d0340a20800100d5400c108952118003030b400004500c25544506a0301c000f03411031340120380408484110444003a58000141d1a2011461003c09003444031180000c05104c40c0500c1c0c0c3c16540743c07a0307050010000b0401440c1c00d031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 695750953 1250 695749703 695749727
    0x3090f0e0411211c0806030f0c01031509050f010302030105160206060108190504050724140918091b040c081b0f1209070614031503010902040501081c 66
    0x580440006078491409403030b07000003000c68078003030100304604041891034110a04c00c1d05050803080544208402d030030039515035003c18180c0103409011043e0944688828020b074015040c550f444000c00038403e40c007205007000d86200e000801c601d0900d2500404100001d1000f00e01c02d6003000e0000760918140f00c13541c44039183c04c0d0010040e07a161000113503860b41008060617400340c0540038448005d0130034040d00740101d000c0d10280c078400381010b4030b01110b100003005005402c103c06000c4c054841c0c0c40030003c401420a020042c3e19400c181000415503045020102d01194146050003410140407482000b1100c200007000056020513042c4404d60300210700c500c0c082654400010710090070b00074001080840343e20a41c0c0750a01d901704a000e6a00550303020b03c40a801039080100d6807a040201c4000780c05603081400e0030b45070f0040441a035100040c200c1e000b4843d1440e41c420603403025003002c2660f030350041081c481c6685a0b1919a0f40700004950880034281000703c1c82c0c951405100b04240c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 695752203 1250 695750953 695750963
    0x5010f051507020d0807120f090f03080912030c0708060114090402010c150203180c121c1202040b09040b090601081305250e0a110d180c0303090f0e04 66
    0x8400a400c007144103030700200401d030707001030441c8044000207441d80c00410b90f1034442c03c80e01c1c6d2880c02e2442e0040118010303008071720a020a1300c90621000301180c41e25001c41c1d03404100c8582e5900c2020100780c070031000f1111440a072001017480b8061010125240f0103070b800180456041f070380d0742c008802050100004154005220314007290240d4824540c03200f215000758400d004243c2c05030200710482c1e004a46400f40b080400d190703080f4440060110900303006d811140d03000782c0c0746442c83e003a0325200e44401440c0721a01c1c5000c00e00405020f00c2210f0501c528005086484560360401c0c1070103030b44040c00c0e2602c660324200c1c20740c8842c549005200c0c0200c1041e5104072171075503880f224100c407401410b01510140701d9180849270f2010061200999010304001226a8510700705000307510038000740c40e5000460800c00041c80d04800d88042d50b6810750841c03804a2030402078030159201214108000d0496682c001000c000e040c4c100000f40f04039801010484a00e99071080714030007178030060300e000b0703c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 695753453 1250 695752203 695752219
    0x9050a080a11030f070f1b031101020708060c0414190603020d0608010e120a0504030b10031403030f1314011416091217090a1502060a05010803090405042301090605010f05 75
    0x401b00e05090699140144207240c1048924580f0034118941a280c0d07004441a0440000081c26541e0512000004142c100010400c0e03084c240d003451140d02503805006510180e00c512403da0b5610950b00186500004190340c4601b80c403400010046d43c408007070005054184440018951814403c00c901c440050740070700919145c14a403124107900040c04442042418000400821408030516005030180201e8801c0702e4079600d8286100c6001288c1e142240d0020310412064000b001e200c5503114540340c03100c1030410a240740c80440c1c00010b400e251f41561038603034820003070521154171901600c50404000e40076054500b0031103030b03032500f4000c0c0d0840b1003004000034002514443d00c155898125001c01d4200131501001c1016203500b03911040b40502c808440342c50f803c3e0140002900a07688407000d00c0b603581020021580c0348504c1118a02459aa0000a0a1189035420455064080c1702d001c2c9035110810410b40c040d2101080c2078030704a2a0100008402c07080032042403c035800075000300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 695754703 1250 695753453 695753467
    0x105041803120f02130602010b040c08010305030301030803060d060603050a210f050d0212090610150c02060c0127020a08070e04080f071203060e0f0f0a0902030109050a080a11030f 79
    0x1102411512028000c9190280116172042643c1c08100c0302602c0c460b03000090004013001080246c841c00705001003030104802c01407000c18070120440341503070307000744550b030b525100d40c80815105d80508a02501252400e0401310030404089140100b4501855849032102c03440070b449508180e41d01d6002c0c000c6819112090002030065000d4084d1114004005003458203514120087c001e084400c90415000342c010050362040724030300d4a002c0c04903540c010f40c040c040650702612110020030040e110746400724a0500d4030000b500f0038603901000001240030420002400703110140f2202c01240b20b62069000441c0310f0340000784200032500b249074074040e1500c66444a1003140c1c02601108400da00401c00000400ca0503204403c0c11091a540082c002d854508204400340d00540aa0105034001090040c5008001da03071903001a480c550001d528520743c40024010121150b0003855405124450001d011404002e030081481d540c807175001c100b400c44289030b240d21030300e204807010001c00e1240c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 695755953 1250 695754703 695754737
    0x601080a200c0616090b04140d0c2903060315060105040b13060e0105130302040e1005010b0705162d0512070f0803130311150705060105041803 63
    0xc24510031200503a60a1035001c10040d4202d50007440d1404840e840300742803041c41029900b00450002151500d20111810804050a03070701c65403107122007600c0d80b0944010103998682d82e541d800395010b02c00c001e080c0c1d60b40760b00d908484071f00451080160f1807191442c900f8180c900441b8454400100a007001c2084a90311810b43c0070040e01860401c0010300c008180391141c00700426840003000b420304001858080000d003140b02c00745105042090030b0042c501021221022002620741c1101c0119810f047c815440340741c402c452002084081c201800029000001d03402005c0e0745008200383d4450099403803178425600c941d4400e0307000d158004070704608544117600201c0103103c80c101024005660396000691040d04030302105245400c40c89040040a906180d02802800050b014508000044440c02e64400980c0f00140141812801d0b8403295510085600c0b1988001610a500e034145403c14540c0c1c0c0000b401aa4080c61826540101030300043ea07099525580c5543c0300316003101d1101d51 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 695757203 1250 695755953 695755961
    0x30503040b070f2009070903030806090a151d061203031506040504060303111b010f11010e0a03120c0203030f04020f04060f0b2505210d061212080601080a 68
    0x40e11180f02101418001440180c441e403681c5610710545081480140100315041c00040e0540052220103181040025040041c00780e01000441d24001e40d544c940c2400c00107014051007800d0301801c0a200030614a006400c0720300160305181035043c066880c2d030180105900041600c40555200340005100d11414401e240380001c00070307099034105540c0d84045000d039030407030308220f01003002403a0200e8019010480c2240054030900c0750020381001200282030b1500d00b011660800c14401c0030702c04025002d4000707411090012080360307804d0b1304e503080c003e254038140340c1d242401d5030524060701081031000065070300404400d800300340182c0304e907400c002d40c150f1000540c0d50000d848030000a110043c422800300106a5020341658801c40d0700035085081c81a82880c130400413103e074811010800001c0e02191805c59006030008201c65800020070074003036913003500354460400c8030205442c0c540d01810f2004134420f802201990030041c8050f5100c8408071000d5000a500e0000224054400c2d04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 695758453 1250 695757203 695757217
    0x11130b07030c060204030602030121021f0903120c02030d17070813051516080c040905040c0e0406090201120b0d02040b0607150603020127030b070912050c030610030503040b 76
    0x38500d408024558940040c0e0f0170541c0b0907502a90702100402501c1c5032188491001c10121a10841001c40c43c0c4c0000d0301820058041e48044c0c81c01125401054000c142c403401864102c1d0303915180d1024100014125000104124080c1c018600c502400030301403440e03417201c10b0702070703003441d0030355171522400c40c1c0c134034401440d83c5811000b1074100c0e404610203201030035103100b001c00340144501d028201c180380b140c01500315000300000c0004100c00008400140d80550300e28800c0401c86449a0814001d0300c03840703411801a600e200300502c020090b65900ca0151f441c800c0c2c0faa00d448503183d541000c12200000c040d00c0e00320f454207024500602d055841002d00910040419080c800191502120044582e40861200365220010b009540c1c1081c0b00d02c1c581c0340d00302080c8680c2d65004004002601440c80b0080500414401007902203020b860f91340050204c02440300c60320b90789400c0c0688d072010240011782c0280035203c041442844ca081c0c0d060181e07900400110f26043ca400d0455800d984140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 695759703 1250 695758453 695758457
    0x7050601050d08071209030605060a030c0302040f021e0307021516031104080a03120f0b1e010e1f031a0307051509060310081902011e090b0d02040911130b0703 70
    0x21352000541c2c05044020345096568070207200c14158940b983c100d0300003800080c820303e0300e0403080000a0721500001d05480d410794011485407400c0003000007a0083c0c50801c0f4105900601c034030140d007940c07009584603410f1a400c03911244841c58240056480556910785d01014403642100c5060290708048100820303d81c483e8075203035981482c2406c00c19644800c40015a00a000b880441203a0041c0d5981c0c111189003044090803c50000d0000c052400c00105650300d080034003c0b141c4e00a14209441000240440070280d00c0114059800d280d10005031010034030302040c0007440e10042c91440d0a894001d402408006d0070b003800c001078103040d01c80400d8921000c009800868403160701450085005101d0003d0b0355050081c003904100f100040510801101c01c00500580c2c0d01111108826108040301400f1000d80c11b4112403440e2160446101204001354483d00c454990f401803044507101c0200b0404d101084006485c02d21030641400c07052480d4081c00c2c05041200c1c5d0062980c02c1c400c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 695760953 1250 695759703 695759707
    0xc03030108061f14280b0418050702060106120f060303030b03060702011a01120e0a0627020d080702040b03060c041a0c070e0c0c1504020a05120d0e0f04050907150507050601050d08 79
    0x9a50111948801508281a1b02e42d0100b420400c02802240040440c1070312541848589004540251348460520555003004040e4054000c5181c00354410807008c50604070901a00c0d03180e05000d0701414012606038041d10a02d80014141031040c41110342e0351300707203403103c1044044450045818505104000303980c0b550761032031802c100504001040303105100d01c0d00800e0103203040d0454148004040002040c507407101d12100e0050769600325800f01c982e4404c603416180c18403800407800506020b011160075116a4050044024054024004a40035607051500d000f2400c8280001801401a06055a888011305025403004040d80981c40164524607509104084005910b050792440c1c640f0300e441c1109051205504107503d4000141106445000c0d49a00c4902015a148105900e000410001154003211070340d0744d1499420b0041c00510a0019041c41031100c1e0301da5a40e44159407025070200d0b20b454609000f0010381e810f2581000c050402c44e841d00d000e0000005014400b02c40100d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 695762203 1250 695760953 695761009
    0xc011d030703050c0a06170415020f030a05040b100302150c0c0607080d050a11090111031303060506121609050405030415030c080106090f0504110c03030108061f14 72
    0x304200710001180500c004042d0520250709000ca404240d4100108115080d19036130004100010072540040d070102c4100101d41e00c940a18000340a51060750301d84260000038410b0113001034011500550040c0b0a01483c0d40360014a4580d085183c80000d40050421941e880086001005403051600ba0000d50f0106d007215000590706602100c2c00b1600008049251000e800c483d11540341d03c8400c03a802004440b425141c66032845c040c00184504100201200c002002014001d82d400301122a1100d02826264640080900350494015001d51180004003205690008903074800c035922840c00c0c00c41d54244074242d005001c1c01001a00e00e440100310020b114046092040e80840c001c0c0e0303000489107211900200081011790213034041000480080c0905101c20005408580040f200000c0601c400386140b40c460203910328100f458003000c0000507022001080c0140720b03d0300702a0540a481006a0701d108200d050f0203450b800301c00711202c41d0ec8a0400d544c2e00d040b85512171031070600000c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 695763453 1250 695762203 695762209
    0xa02060c0724080603191410060f060e0411190e090f1e010b3103032102030c0a0305060f090103060b030d05190f1202161110020c011d 59
    0x102c002c88110300380d090011400d110307840f05500380c21a0084000c1c00c0c42036110802e00c003074501c08050103095031060300d0341c13043c2405c0200007641c0e060451b10014401e155803040100308422982c800c032408140d8041814141d482c2912509000c469141001030624400020b40d68000400c0c003420303020300c0149890716000782c0d100a092481800748805656141c9454400000c102178090b00b0000090320041c018007105805409170342004206558071142055182617150546188500c440240c4800c02000b000f41640300c200342540b0110501d03207900740306e926419001244021550036502c0081404080309561181c2c10141c1c00010080250500710181000144111400ea0080b1802c55581080032440e0405202e400c45041c0142041803c100b900a101c022025140640108100c00503000b00341c1c55000343e40742d10203001c080008548a00d1020380c5004852000c0da8150350008415000d00054a0590915207400110740e014022a4103043d0054980c0350b42510380095207004030050a03040c1c2c17 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 695764703 1250 695763453 695763479
    0x171b03030f071110020c0d02010503100506070f0b070513030f020d1a1b0f071101180603051f210212010c0c0215030720030409020a020a0203070504050106020a02060c07 74
    0x640150001d440b1400c1c120100700c41c003114078130707642c1c00c0d500b000c4488a0b02c0d6480409081d072451b020700702140c0e0b035031b51038401c01c01c01241d5400c42d0b42c0c40007000c02c00d001404200403441002502c102d9980c0034070340f9440410b544070b010313615005440300014201400010781610401d20500d02c094a00740c01c0140c0c59403044507507a5090302d404200da884004000485030040003003101a95281040740c42d00c0100c2c4400c114501c1419400340004080d200c46182ea0703403184400002683c0302c207110010540d01c45400402418041d640c15041e510b4840c11203c0c2c3d0103140d10700504542005150210881140800403030000807920160307030003c01c40e440445401000e000b13440790105580e49140c03082c4010f1040042d0a8600745508200d60b800b4010069031680025020048140c40c0018009011040700e00c240b0311b1081b5040b500b0000c0c00407800e00510790300001d6403104584200c050380c40050321082070000b120350034882d041c01030b07001c1e41d00700d40541083c600501c2d92014500903101c0d1262140d208203000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 695765953 1250 695764703 695764717
    0x25030e10022101060518210610080c01020c10032004080d2303010b030a0902130c170c030a020c07050301140117060601171312020c0a171b03030f 64
    0x900c80044015500d900b0010b0058090030b02c6007091400d00350140f10041d00400d0500b100b07070007040400101c0c00003211500d040c11081000e0f008503191361400414410056070584500122803103104654a40f540c008030301d07078140c49006081045009a0504201d005d0000da03800c0015074102000350182ca00b048400400180002100404003280a4840108801250103039900d4185402ca518100ca2095100301d03030442e00660041ca0701c945445802c1c030000e01900c1e400a52004991100f031040103401d42195410342c80c25218004200202d05580d4414007044401b24203d00c401c00001703081c41d04030340c0a0001514890202c40c03140e5101c201003070840f920070600040c40b461140c0100329031700e00340114880b0516031760702804607428008006040803040410103501a00c02900148004c2c01a0310306100701c50700b141c109450b5042508020792903000300c081040c02194504408156442c2451100711003a546800500803003055038074032100c4124807500386504d40000c000041110305010090150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 695767203 1250 695765953 695765977
    0x503062b032309090621120a1101021903230114010e030c1011030903070902030114030a030903030e0f0316060201050c070b010e070c05342601020417010504060525030e1002 76
    0x14070184d8203030127880e078040c07104001290f0707004000b290411107400c14030b003880f480e903803c000c910030040c6101c5906143c1c44d00600308030910031400000d048640c40030107045641d001c0e00c4560038401084141901c0300903c04865401207140f0500d2100e841c840c00801d1140c4000a0a503030500605000080c10000d0359408000e0030ba802000602c8808000d460320039184d481203004090042650794040c0c0008064031000d000d000600420f8400c50320380c00b100042260009013600c0e2182e84000f500d40c20200039004070f0005601e00030008414a00c2d80080310f1100e82c0121040078160b18040d8030f5000281c0023080002000f04040c00c240020390100303da000c9505000c00303c80b0007002c1110418020140c01004ca03010120400800c004c2c40d00440300b00140340d4201c0020585c404080e44165029100755070001010950407084502c003154190311a030301a078800d10f018802a01c84c40c1e011306c070110208207040004000c90340f02c090302600070341c4005650200141911105c12104440d04126084500c0d0254 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 695768453 1250 695767203 695767207
    0x4210204050601051606020d151d060a08070e0a020d0216211403130b07020706090b030906070c060f14041a070503062b03230909062112 60
    0x1140303400d0140325401207080c60241d060184d40490780156107442d84018180c941c1c0007558140810f850b400810800b020740c00300714401a030b80e80e245141160a100581c1c2100d10042c089a0310b0b14181c2070f41000c6406e90b03401010b241e42400101490500e0280c02c0c40d00702e0b542040210701e500302600103003070ba02c03000352241300c1c18268a08120000e034094180ca80083e040b82c051408000340c112400103c50300c1000e0116840750760300319071281c3c1810200b1011b4012040041085040c07540019824107071000c5940f043c070429603555840076180003d036000001500843d0004402134410740b00384004ca03020364800300d1542030340580d0404945814421a4042141743d0400c020f00c00d60020b1440c03c0e405000039440d43d407070181c0f0001c240f404003804061048650011614200201d4003612424030318540329500c6110306450085c00c01040d40701c044040611220600314a903440c40c090b55014000684101c1069895904015200300452400c4200510b4260301500031203003080500c480c20710441e01c0b15 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 695769703 1250 695768453 695768519
    0x90b0108011e0b011707020c0301060b09040b0301150501050a20010f05090c0904080a050c060a06170703080703081306021204050601080721030e030a20010507111504 73
    0x71410b05245091141050403c071030304a01c0e03640100f00301c0c0040c0e406103401e0781c01d441d010000c0f418601c4c0303080040d03855820400d0114260000e03000500b54020200c40810500c40210213042c00da0f926040e0380c0381c2c00d2440b840c003000f440d40294014808201075291040c2d6451001c4000c5108601e450118141a95542491441c1d00b10910415401c110204010f200003051b0800050300c5c040010320092040340c0100b02040340b0780c019800c5d9943c00c10180117a40d114500312481400030059441400c000c0c0b4580324580604070320110f034071000c1c1c80e00601a0b5242802c107460560343d00c207001d0101940038001c00c3c04e110201d0001e1001e001039010500c072032011410b05003040b9240c00c00c1a0041c0c82c0da80c1202d841000810400c80180e80c060003120b0301160703070000c1820180c6000c0c00d00a851b5400d40502480c041c01c00118004031402c040f48000314000000f02d0714011502d0b8018058000c0458520410350f81641c5045030b00c00f03020302101030785e0511b0640c459800c0c0b81c8400440e17400c40345c4180c90820507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 695770953 1250 695769703 695769731
    0x601030302072411030f04120c091b08070c020a0905190203061c020d060e0607020d0905131d0d030209040f091713051507050c030d051c090b010801 65
    0x3907402446196890440340da81c502c0c0700c10700040450442404c0c4a2030314181c00da501014420f896110b0244400d050300d0b5903030303040120000810010100c840c003880d01c4000c2100c00342403040c80c481070261041841300c1c038490032080c0c0799048042c01810903ca05602402d005a9814600d0409052602c602180724140311401c801d1118481e4440b0501d41d00510420900c0d44503002c419201241c1c0c2050000d6040480c008620302225102001c0c10f02030030800240ca4a040c0014034500030384d4103500b01c81c515940c40e0b40403203050340a40149680090b0860301c024900d1300c41e8200741742c55010700580714075aa00e2002c5a40c0717800d4400b51603401198010510003854030b880d2043c0117802030075400902c01252540d8441e005400a8001101e43c010081504c80709d400c044015140a4580a0000903400083c1c907045141d5400903601104c861040481551440c240465420b20303040f81c5071103645c14550300000c8001c5012882c1c0e81508400c1d520700725140031502c8036804600822016000284c820740c40c00030707 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 695772203 1250 695770953 695770963
    0x1030f0c09060b0c1b13090f020a03081b030a0816170a0b0102191a040c0e01122904060c12021315080709140d02030a03080702071715070519020601030302 68
    0x10844040307010f000180602d0300d075201451010045454002800d0300c7c80c0c80d1400b00c100041c41d001c1d40003005604040300b040300c154014561003070510b0410100c09420981990b49128a1105c40f0004e032490010610f8000c0c0c0d12101003061141c0c2c2000420f0b4401d150407241c01543c21501200c541c1d8036243c032640c103540c040c040d039102c1c8076074914550f008a80c95111034400d072460f440c0c001c4c402e1913890006820710203172100c201c010b00010207642009580d02c80b0500302d0722103e608141d902105640184100d101002c0c829154540c860761001c0c1541d440744c617460020f1400d4031260003806a102568505404148002d01c9401c501d41c09d0340000705c2c00d0891410b10b12001480c42d0b81404141800c1c82480e07504229040119080764282107000303041c042c01f142c45810785950094251080c610603c0c00c160b000914907100302025401c4840f0a0340c1c0d401d03540261520800000140e800541e4000c403e01e1a0518555200350789050141ca842c0080d408031001d0b40301e00d0001c2c0d006030840401071007050b0341484 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 695773453 1250 695772203 695772223
    0x1507120f1b0f1b0303060803040e04032c01032f04090e0708031603050f0d050406050f150105030912070503040906050a03022209080d0b03010b030607020601030f0c09060b0c 76
    0x180c040b4880000590181c10a2000100c840012004000d01d01c201446034020f540a01410300c06d0381d880d1507542d8002042c030b8505440031808038010100d00344100000d0140b803c20b4108140880c00d00f001071030019401010141c1154440d040f208451808070300c0c849502405010401c4c0c2c040350390ba450071041e03908072141400e079145a900b1000c010402214000300399010002e4201c80442c0c1014549001d58013441480224030250307001040345007070b05595902452045006070b030300344959034400c4904040b80301c045501c41030104cc26205018a0b502ca0000b46038070010010840381c0c0320100c06148444d40e040502c04a80651001400340020701d81401070200904003616404d403440d04540c0020683d00103c8400100b102011602500e24075503504141b0209070031410150b9901c00704204100500500c80701c0301e0080d070034003468100608000984910030030841c1d016142d076900f15078425521180b850010344046c4820b40c00803600000521801000781094098542c1d511035a20303000c0d041010b141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 695774703 1250 695773453 695773457
    0xa020c030a020f130f18051e1e0a0803040f02130c0516050c09161107230102120c06040b06032d0a050a0c0501080f04051507120f1b 58
    0x1441c0300c0700680f40d002c80624580800c94071042c08802d08280000104201080303174190908021012810001507001c0b46461800382c01520340c1d101d40b080c442c400c0c00082040c0c4600700d43c4003198030000c1412145a0b40385500302d00080e00c007074281503125411613800594064603031544800030b4900f185408510003084044501c0d0500003c011440d015090f4040e401a904450101c450a08100030052015622a2200416091550030311405409801c0c240d4210311021441c48d00d46070b90f02290005605040300e5071100700300c22002181d21040302e45801d001e08541035103c1c124001c041402c4a4003d4801001c1000003800d251405003080c010120010b81064001d410107900c11780c03205040c4258001c0740302a000006810303914a8105031030080040d902038500d002e4900ea034400c00030051501c2088031026a20a4025142c400c0c051190503401d860041055002d81010000c07030400b87c034003d500030094140749284000c020b051a041e40c2c1907400300d002e0310b42c0e107164204d0080b0503000c40c40050749641c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 695775953 1250 695774703 695774713
    0x3040f0617011d071106180d14030c13030b040b0610030603020303091216061d0108060d031248020d0804080409020c100e010207030f050901120c050a020c03 69
    0x5100700c40c1e4030303c070540c103a007207a8504002488043c0242c00110700c480c445401c6030704034641302240840c140d09106102010340038401600012501ca602c000f1003102d02d80407441d18685039001049e040ea4081c2c4042e4041c0c02000d00000041241500442d108901801c6a1401c620303091041040201d00511102e0601d0315140c0284050b8400000399082c240041d1060301c100740710318044520300303142c00001c848a0851204041b07030040d4041d000700a44480c40f29030a02c42003041d0015180c0701c80443d000364002c8001c524100c04030f807007503100c1048440130301030005900808284180c50710544108011590a025050b0f00481c00c50500c0c24403807030b81d04180003c450000f120300a455000e0200c0700010804030101041c2404600c03001c443c000e02081c40c007159503101540f48143c80e80150626081c2e21441c0c11940f540c000c4d07043c02144d2950b03034142d071040c4646000200513509074129445440c10440700e90041c07000401e061080c150750305180d0321016103840e40c11000a00d03002502c800c0c00e00076040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 695777203 1250 695775953 695775959
    0x30102030c03060d062913061a1809070c1101031416030b0303131d16050a11011d0d0c05060c25061505090f06120c0303040f061701 58
    0x3500c02d9076082402104d5103501c1d10780d5800c0c6400a4280f801600c03c1d440c0c2005020f20820081c4140c41481da2410b8441c5288405070928110840d031461081600d6090180740c40041060704100a1078954406032031110011000c501145a045e401c50304000030500a20300801440301c140411006a0424a014403108140c02d086005029000c0c1c03402c01022040210480c1440c0a83c0050010b0400030b030440e600c6500324514692a030031b5a20400030307074900e81c5061085d8248007040c0248508040700883c100444c44000445080e0f10003035110303080001c1d140d0a16007945003070140b0942443d06a03850300c0301c0780c8042e403100c0c100313407642d0051000d12900c41e04440c006400032070300c1503100b4001a0348070345500b04404416484007150040c04500080000c4007020001c1c10b500500c4070484102c03040100b1512002030040c10031068880d0f890161485c0e0006d4203619146400040300f409044c2a00c100d51258404a840d6800c603410149411520400c18404160b0000628042d9200b54006a0181d45 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 695778453 1250 695777203 695777221
    0x51c05100302010e04060503030d0203060f061e03131e06060504091109070c020901080a1101030b06030f0c0c070305071e12060f1407050d0c030209032d1e070503010203 74
    0x5807000074184241200c003c8002e0361654041c0000740009415640e840b8841c0802c080254411506288114481c0103d2035560419405580c0740c1c100031000c1c8a40d040c100c044442d8641c00c004c1109404505614000000a0316529003140c030346507074401c9410441d298500b40f81992215045030317015a240800e11400f041141500e180311202c00d4030140d9107034075440f01c2181c01e491903840c0070390070010030400091035000001d44050303000d00421203910942940320044054034981c1692a6110000b400031501c0c00d0070410000d0742294810070440d181c42c500c40303c041d05004103580141c403581c20298042240d082d003070250030303024540f140034800c0d001d0420003d03000c04018004081c10003607985041240e2440c0d983d00885d0307060b0f605103408801d032400903001071003544171140c6021564101055404558042e00913200460703001005444100c00001c2c0000c0701428400c03071a90803100444c55100c0c4040e0a0100083d04240e400569180c2e0480c0c852140c60302489a010b14003a80c410800c00540d60 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 695779703 1250 695778453 695778481
    0x917030609160f030e120f0c0c240a090305160914062124011e0302031209030a080d0603051606050d020a020f0601060e15030c0403020402030421051c05 67
    0xd0306070700300001c03101780500e0818906101025206185040041c6040000e2800d1010f85601c8407680d003114641c00403c400d21210740301607403c80c000d418410201e034294180c10b2020344420180e51808200c1c80d41e40f500c03100c1c90590111041c600c0d083d50752905009aa4090140e1855038050301c00d00901824502e01040204501c8400d80c81c3e903a5100305006151402800b0604454070042000c01c0c00541286130720105010030720401c0e008000c24220224440c0504043e0001c07030b6001005400010460000d450041d404035040c3e40c2e02d4025841c0ca00300180f00e801c00380150602680000130b0040c107514205191416002120740240083c6008125096011040f1800281d51032405038681c0c80d5008160301c0e1160701c20408915000300c40002c503549070310218007500c00f041266441c00a08000300340d0000342c4001d41380d0950102c010801807025040c140c0045402501c51000c00082d42c1100d082c020b1142140400400010000036012241003480e68120118010300b190401c91400e0109440303000c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 695780953 1250 695779703 695779727
    0x305011e0b191710061713110301111809010b03091b0105040b0705150703090201080609060a0803030406050a14060d0308090709020c0a0218070819091703060916 71
    0x107442d070703403070401e4035684142c459000540c03001c81c43e90b00a00308418202052a001d00411002440f03400910b030351914581d801d50700452188045003450744840d2a00c02090480910690b01036480e8081c0a4080940d0002040d0203403104c0a407c182c4107280081211405043c1c2c003454624009009100c803070440407032a484c21902d40c007506258800230000503145400f0399402103a1401c408107691050140214000400503034607102c0000d255a20002901241d04602001c1c2c0040e03421000221103060004007690000001413003640107980e1a0030807491035004035001c03600140c03108180310503083c860003401400041d03a8105145440c103c1c01099401c800746401400700400200072446020f000c1c00304a0140ca540f50040d55201101d90f0b139940c0e41ca80f91030040f802403800d40c51078140440010000c2c1d000b0240c0350b48500c02e41c2c5907400388140310b80000204085041c1c0d40e00001d40040c400c9161080952000c0784002c0d180c2c68030004118803110020f0526504a43c46000c441c0c0c1160b0007403c4000c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 695782203 1250 695780953 695780977
    0xb060f03150a030b0c090307080303010b0f03060418050f0d03020f030c072a0314070f05011214040b040b0a050c0d021b07030c18060b0403031409040c0305011e0b 71
    0x50141440000d80b4081143e880030388041440030500a424003128000c0885440c164200c0e0725581d92420501d0752032009209940c03a60406005c646070b400c824000071030308144010030100d15a1040c100400900300701303d000320f80c00d6000352404000718005005201c40340341035082c114142040350303a40041d14400103225201950b40084d240c020841d894034608071080300c0207000701c440c541001c0103481122242c0000d40d0750702c035100400c105240300094041c3c2541c0307210803c0788100746410f00644890b490308510004031600d915190078180302d0322400d07900c52030041c2002c82c19810315040074142c000f0040c08a40c8141e04000070024007410281c02c4541c1a211190010b0b518030b031554122070700120301034429007075000c0c2400c00000c2c41010708403041a1030040003400744003418481c00d41d08490451080c1a0843c03028802000407034012100500c81051142c40d4a180030585c03000203040718050406030012954850044c8003807800d95800034801075003841494000c506112100c507030390090020301c20b5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 695783453 1250 695782203 695782231
    0x10b09031002090d060f0506010306080307020f1903300f0206040318051309020f0d120c0804170a05011d3307050c1b0d02040c0509030f07090b060f03 66
    0x943d540792003511090703c0c0e42200e02002040315488840c2c0140c0029103c5c40e00003402c1100202e0b4001c0080222102e41e03034014039034184807040400b13200c011500301d00480c820003120034000012800c3c918440764002c01001005000c2d2428558480c030310507001c08800108403d00000021440c0c0001d0344a400a80506010071076400c4600d0000842c030301500900d800c03044500a0003060700003500071200c0c4038400c44403100e00141c4001400051000058098a01e18030050a141d10038010b1514980f21030254440718a496111519903208820345902e001c0140c1c030000040d0180102841a804201c030f211f001480041d103182405a616250905044d04005100d0031a001d0104a07180382c405101c02041e0000302460680300142884d08250042d0910b030089202d0031000f0480304034035448403e4002d02807003508030320b602880300800c00d01c40300b442440b0301000715904e20ba0341007021651310034519004117280c50500780d400381030380c403020341c420b005400070301075030180c80c4020f01038951051200ca00ca034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 695784703 1250 695783453 695783467
    0x503040b041416080601090c0513140f100804111203040e0a090b190e03282703051b0604061b1203060e0610050a180e0c04060206010b09031002 63
    0x5080070310715041c80f10700701c4114a000402c01c10101d612030407516480010800e42203031100aa42c148a00c00e05600002140c140070b120f41c00d00700768401e001d443d0142800000c486808045599001100495008502d900e030400007080b030880c8140701c107100240e511049914211058a5807802103000c3e00d80d0b4041720400080c1e4508140e44140c05482c0c2003406c400701428103481c09480380b10070040245e00740741071060301d038003070040003040fa00300007100c1400c50300310720307860040c1020803064040080030041a0f03800068001850400c44002010002c54805120325500c0e0031441c0800c4c0e1000e409100180c03400b014450303500c4505403001c072902400c1c4002c40a68150444481d03d001c0710004040600140f10043c400f03074550b1003101912800304a02031540c860fa02040b8180d42204408400250104000c9641c144150800322281c14140c03443c480700c40d229104014180d0b401c440881d400207003c282041219810081c4a0050107000c00e041c1c42d00c41a180801d4540c900464000072180e0006003003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 695785953 1250 695784703 695784743
    0x21110d02011209050c0a06051306030204030206030f1e09011b0306030b01050108070c060612170c060a0f0b130207020117100614042106150b12070306030b0f060406060503040b04 78
    0x103135804205c001d0480c50709549a10004c1d1131a0041348003c0d000368860740d004541d0301d02134402c940c142d0750018103040c20b503510000c1c03240c400e8400402d501c00205500101340c0741c4d042c82c005040d0003460038100200e0101c0b01050500c0c0700024040c082c030100350912104202040180c0c00d0903040d100c0a1914007440d0703681d010180c50509030840c008021924041c0300154103500d201c1000f451038841c00018040f0180d150700641e00340200908880c01e41c0000d000b2564508440c1c3c8060141ca541002c0030138000c4000c400290f000881044051225400140d94411507038002001c00031105602d64107003681c140707102c0c0500c000180b40a20700c107200d40010f405d050042c1c0c50040c3c4005200000055000b41074156034024115034030941102d0003400c10101d041c889510b00034220a41e113104c01d032181824001d541d001c4040c0e40c080c007184181a51030f4404808590302c600740c14414008800b011001d030030a1000d12003101e2455100d081005004d105000002d8040f09105402c01d030001c00c03c0d20030005256407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 695787203 1250 695785953 695785963
    0x10504030f0b1503030304111903050d0c111201022104080703030e0c1002030d06080105070c240501120510050c0306040b0415230a0303090501051321110d0201120905 73
    0xd4141c4c5071002004120400c030b02c1100058130300300c081d1010301801401841414100481d404001c05907040a07003600401e0348070700c44620103680180001c8403a0310152010800380c60280040d68040d0b5000641c010100400001541c030900c0c2000704c0101c44e113803988900c0d60070300400310020109600c6070100038400034204502d20310b482c401050082d0140b03c050019550389d200786102501d440c11315000040d030501c1886958800c01c26905e402841695681d80c08c07440115422484500b80405124107802202c68450f0038042d109040c1c01809410450070402d16008200c001c140e481e0741000100440b00f07412a056a801507419138010815003a2400014064000302080b01a01c1d5046d80001036900ba18240c0603105941c406909034140c0341a50520914029034000076010030807825041109502c42c2d00140740001503440c1c0d6180441d112140241894988885070101c5280580844240b151041e00302c00c0400007101c2501e00c2c0c85c12540007800b001d01035407048900c10b0707070f0b01c1c214800d000b0b003070013 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 695788453 1250 695787203 695787241
    0x30319030906020409091e030f05070201120203010b03092503111c150b030105060319050f060705180603070c14010914060f0121080a1e030c030b010504030f0b 70
    0x1000350f4540345c0b500d88840040c201003000751050b402c6078000410f28200310324000d4101d601075036001284099030070240c50302d034404602241000076418866110103084c0c4003840c047c2200310301c6e01d0303603074103207400160b140c42444048407101144040e408500001d07000381c43d40c11a50700426990b42c0d0109180022482054000d00c40168031645694104002d078010910b2410030840c4020080c04c41400e09141c03c0b42e00450708603400da48048402c800c000700300d082c40c4c275440f0301c40c80480701500030000200d41088030540b0f0035408914040b82c1e08200c41850f114550140c2810b542c220f06610302104001c0c06050044000303010010204070340309902400790018200107800190b80400d6004281c69140d50b407008840c021002401c08001054032a00454920704a6080003030340000c0b81420340703440c0c0880e404a0900401d1054215002c00c0e01080d017441042070750940e0b03d0010310102c4482000d01960302e100340003410007400300f00c2400000d06206008400d41c0e00080d03207040710703a17468031504040085a6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 695789703 1250 695788453 695788463
    0x1e140409060c2703020303090d020402090d0f02041d0c010c08040503030a0e0301110301050d201513090605030a0803040c03020402030c180612130c030204050106050d1104050303190309 81
    0xa54200240c0c0140c0c0f960a40c0c503090408110800142c24200455020390200a600d90020010360010380b400d00d1a0041050006100524110704040018500038401c00b040b0341c0984800792110a51801d44250310907100b0000c086046680c0d202220f0340c46000b42101c16052210129501003806075050948000d004041d0880c0e65940301c2c0c402c054a212040d4034403600ca9820055054107500ba00429a4126040545070743e0302c8081b030342d0f2108402c802c09031310107900f8050400708989a5942d03014400d46080086e00803903843d0001c0064400d8101190401200e642c01c04204200365100021014941ca4206402c9500c0791128504840500c81039440607600ca800030080c8440384a00300000c0c03041500b90500e00442c1680b00d0b0038025180501400030044c40502e02c002444027111800e2154558483d41c5801040c0d900c0381d000604480313083e045400051400f1035044051161813258030040c1d078801d500c0304d0401d460000080e5603442881030100c1d0b82d82d050116504111300075001030280c0c55001e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 695790953 1250 695789703 695789711
    0x10e0d0b04141006140d0809060c010b030607050d1d06060d060e030f04061112030a0e0c3703050607050906040f0603270c060305131a0403091e14040906 67
    0x2c558414094010f81c003403a17400b6040c8882801030b0380340c180c2c0540301d019031210700035003440741c40c10400c4010b0f00045d000c0c01044d52100c1542e50345640920446100c0d8210792915038407171884030a104100c0c0e29544202c2071002d0080200d44048800003800340d80300b4030481e14160066817526002c00a82605036254900e032001182c0240d00c0c450490181c02a40d0166503420258500303c21003690b01e41011a49081540040020981c80790983e0009400307415a08100c55108191402013480d25007200200b000210b050342c0c48213016079258414040f9500c108200300c08090a68503425120f21303020700200305005001171055150345481c0143c4008190070b020725900c655540c00c018000d441c921040b04071200c1c110b000600b0041c40c6800455500e504544140452418071400f640141030240800030301072100d07415200040e03044032080140c0c224a4003182014109031030007900c092940d4004d280d080800307404800c854058045243d0440d241101c510207610700b580c0119000b450002006400c45040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 695792203 1250 695790953 695790973
    0xb03070c02220c050f07030c02010c0203101a0105090906040b01110d0207300201080723070b0c0c030d0903120218030c04020a090b0708160b0114010e0d0b0414 70
    0x31000e501e510701d6641c040520145400c80400c51311840345d2202e980190105200460102e40304003410200284103061085521840c0e4001910f800b25920030651090348810f804e0100400010b40c4040d4a1403c1c00c0c1542004134110005030400c20051590703006540d11420940181c0c0302e0036031462011504410f036416020195002502d40c40240520030350082e8001003c407400d940701520108042d03241081c010052950f900444034004083c0003d0108080030003003902d001440d440c409000c0311500d06c2c041d80d4007110300d40000c0d00c0e40300901002c00f42c64140320402030b400012040310003101c406100000c60700920301d41507580900320f5007408292480811240d00d004d441c04d5000400c040701b141103c1c201040e21040000782d204010900001524081c020402c00488001500c103080c8503100315410070070b5001007160054041001511145501c600400c842c0340000c0104c24081400e00e800951880d0f0f40000c954150401940182825070f100c000800740030714000d00b048116541e1082e103c00c40c0c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 695793453 1250 695792203 695792239
    0xb0603011d06070806010e01090501033b07050901030b19021c0203090c22020a020109150203060910031109040203010f090521040f0b0f13090f0b0301020a090b03070c02 74
    0x1046980f000401e010343c001c00c3c400d60068050708a00e842c140c2d00e46032014102070044001e80000fa41d80707106c00b929098028040d10507140e03034117904080407000702406d80d080d5803414a00641944034038002d00c50240148042558400b5043c1d100c7d2007404680340d14007440542030700034414000c924610038181d00395400c4103c05a0000c5002da030203a0100d81d0340704114070800810703840e4810710140c2229541d9910240c0c001c02d4010b001110690f00000a0040190b118140d07603034039008801103034a80c0001008040d14200b480b0640003880c41c00610346441c10740e80d0748001443d107440618880e1880d203002504640d000d4014100048503400d0070320602030f2502d00b2658501c20704600c1c1c56078400c0d4440d5009501055810350f000c49a0725418403070300b5490802840000d03070103c0314004040104000d2241d200302d84200d41d078000d00600800082c4070020b03192680455000c0700d01c4c207109900400001c0d155580c41801141542d4002103003981e030340c42d03007502564060480c4a0082d001948a102410000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 695794703 1250 695793453 695793463
    0xa050c0a0f060507030c080f1803070605010f06020a030212070213180b1608061c0b07051c060501171807030302010501030219030c03030c0c0e0a0b01030e010501080a0b0603011d 78
    0x1502c078610074003050325901c1d825421788002d0b0303131040d00003600c0d0000166611030051180d40c00c400310650b200341000c10032008030b0866200d0941507485c02d40b194010001c003840c411011004100381d1000e4841c41c00e0750b5500135207504060340c890100c010045010001c0d50340b1200e010001d002518010040e202d414251015601640d2170107039048071011000845006a0407c0303000d41c4032207540d0700d410b10348e10001080715002d2080006112180500c0103480010b801401460080c41c035922000d0b1600707440d0300585682694002c1080156003410340070815a45c101c28041d100717086d80c02603030401d5554404c01c61010a40750501c1442c0707201c3c800d4000145601940300300c0c140c900981d03801460307a82110904884403590f1200400320203a00c0002c1020921504800c054a48a0048011140d50703d8410301c4114900752108050140d40e1200484c880d0303050301c2016000c1041c1c0f4003e200641c94001c078180c68046694010380140c40300030000341c183e0f40070340c0081c13503840925075000104010204040d5482c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 695795953 1250 695794703 695794733
    0xa0b060c0c0f090c1209010b03011d010b0f0915310b0d020a15020307050304091e0903020c0f3709090b01170f010c11070b0408060406020a050c0a 64
    0x20b00b1440071819034500745141803d110340c80b59008207192482103290305030407800080c62510f6a558400f0752070ba01d07075401e0040c50070344044070382c4900404002d181d00c1400c50700e80300d2606100b080d161040c080c55484000c2030552001c0140d42d04900700307a082c0003007032800504000c0144c41900700342d5420451000f490b11103030110344922082008000203400c0c810310444040c1e0182d4440040c4500700159071840c0e6920000f40200c0c030550303050100613507445195070030a41022201e26180c101040000c100c042d42421000540042441580c1c41a10040c1d110030f402d64010b40120f003000001d8459032100d0201c2041c0f585c0514042500c23003d0510020080c003201c42490143d440c4010000076800902d001c0d0482a41d00039407010190303442c1450540c01d2030003403160300220b800f0354411f40c4007441c028442c2c6500080d064840d8009035144032a954200015a00019142c82084c48203105216000410755840340d4440801a510300200209a07081d0281c000078013944c0c80758070700380340810468920000070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 695797203 1250 695795953 695795959
    0xf07031802012f071e03110904050a080f03060922060510181413080307050a0917010603022803140109082d0403110f040e0a030201091406040503040b030a0b060c0c 72
    0x7591100174100c00b04100a8480541001081810001700386858110940c100c0d100310101e482030205680c0c0c1d10116000100c4990700d206004c000c0011909043c419580d100790041c80241005085420425040e00202400392025039a00300091034010304010100140c8801e804504416448804907400b40c010864004010350000c008210317032409203440034502c242d120310701c5803d40e562a442200d441d00b00d40c1d0050200021603000085101da0b18035034070302c580840000480d4180c11801400401c18501000d127000c00c036000d8842e0707403103035040c240f00c1c0c243ca40c0440c44450740c0700320100d8103000d0304800380040c10300c1034002482c00c1c59030101030a41051941d01080c200518110b0120900503008603c0045d0070141007442031a468a1700c6088010121801040095110321030410645003001100085000d42e5543c00d0040901c012090300b520309510036001000c1518050f0344041d103a0007184100d0500c8000440442d4449070180c010b00341c2c0e0ba17009480d00b81c40c3c241c0e2205c001d070f55039008461140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 695798453 1250 695797203 695797229
    0xe0301110c0120030109020309161d071e1103090901060f0207060203040f05040f140114090108191e050a0f150605100e0f030a0b0f07031802012f07 65
    0x2034030350a2000c41403510440641e4444c2168a01910880654001001311003240034003d40040540702c2004002c024000c1a81000c20381c4500c4110312550090140c1420140442d83c04813a003100041024500440281d207800706010380360084107441d40c044c0d1403000340d00040b00000450070306c0e07101528001c032200d1542110010741c0c0d02d1200342d03120b01c200e005040001040c1e81080c80603003013603046100071001d14240003d90107842103010824080030703000600da114029183c2504c605d002002207000d40990b20107000f0203c0e4110b5001d1000d404800008c0058960611026194925001401c1c917070381c000041c0e6035298501d2809201c541c1c004441202da2042100b10312800c4069480f0340d800381c031000380015560f8000c40800b82c4840c0c0304409150703841506031540c071280f0b41307040c03000d000214032612039180d45007442c142c001002c40004202d103007090314051481704103180d144070041c1603d80a003001c03400c1450144d4000c04107185410161452251070100c9064400d000520000b150b003034541c414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 695799703 1250 695798453 695798471
    0x41101120506010c0b0705070b091b0111030d091e0510051302010f050903070f0905010504061508070318020603070804060e0c0f10020c09090a0b07050702090a0504030e0301110c01 79
    0x20084070001c1d52414000b611843c440700003e0300b5403c0468000c170140c10840d08001456580c9280c4880403180d0b09107940140e01c280700f800c181440503001e41482420032030103207295000001d0b564010046600c8078641ca881406050001010400c0d07101c80c05030000246c0c00607e410016968800c0940310f0400a02d004002010078a224004050b4154141c0d141c01907210246070440381c40d040701041e00d60600581c078000a106101c0745801009002c403000100c0c4541c540303020403003103074001e070b00c402e01740d02c0c400501c070741d03225800761505034881a142000214004c0304c0400c4007106a024100a40004000003802429a08044a80d12071442090309000750301099904580350b40d40303d05082e40200c211010521035140002d181021300000348100c0d42400d6a890015543c00001c3d80d00f6907103074001c214101c080c00031601c40c141d8400c0c0700381882454208d4542c04505100c20041c042105540c1d03c201050403d4803851402c007001500030300a212070813201030154401d40c04460090f8840d0301e407070821 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 695800953 1250 695799703 695799737
    0x2070504060b1204020f040f09120201060305060c0309010609050108030310081906020c0a06051003030809010c05071b0e100f0510020a030507030225090e16051002070e041101 77
    0x50955a109620a00340f10304500688401c120140040380d01c043c0a810701c000a0716a8411042c1210300201c002c01e40c1a0b0a090102843c08000300150440e41060018400311b14009040340d0415020860030b5900d5481003155401801d1039080340f40741504080000030010000805580964010b1070012600c560b5112541c0e80c40300402c42c00f08802c180001d1140203d031003a0301400c0d920f01c0c034601390b408440c02d90fa100e004440301121440300d65910850140306250340944260342c0101810000c10085880000181c95801040c00051031249500302d0030005011448802000f0401135165413142d003403501d01d002c4900d14070b004100200c9114000000d107071401001416155102d03801624180c90070f61404c590b690b020b5080ada0551056004128140c420108800385000d440002307220580d080100010964220300d80c4010242e0101c1c1115076440000d0000d101156002c503900d6081e40301802c400d9040c010340c2d51180c41c0703018441d810070050003000d000103a4002d000740c1c0c0d410303240c1c0e183c1040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 695802203 1250 695800953 695800961
    0x80c0702090f0919120518090c0a11030322050109050601060f1202070f0314120a1b08060117220c0905070216030f0614130203160e16050408030a0206060102070504 72
    0x5005d604044a00c92800b83c0034034024200d601011404003c1c40050300d01040d0308407826602e9480c070740400112030b001d4580c059007011414100e5006180303142042c10001090f94401f0300d0009102c48460a0982008025401021f0841d0701809860341581e641c0e0024004007110350450700801c01c403690341c0c8201c02e40f0384200c40901341e000c0013403507000b01c0c207880803162441003111041280e6020402c1e41c0c0f00340304104e426071007a1982800800e640f1700030b0801c806030700b14201c9a84240f02161342031140f660380040454500140441124020703640d010343c0010790032076001610103400f9941d040b40d4144015885003500b42c50710341c1020301c000c3c3c03182c50003242d64842d45c10450002c01c4c4206000d200003600e00d2400b0400c0c600070310300840c0820700303050074001011080d0b464030701c01da980480b050210308003480b1705000100e20340c481c454202d28282d004418407800500c2480b0200d0701e60440300e03013a03004000340ca0152500008070f030b840300300d9210040e65509050b40ea940c0588a001c0d0000340503d01801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 695803453 1250 695802203 695802253
    0xe090108030a02070e0402012d0e09060906040c0e1c120819020717040b0c07081908070512160c090b0a090f14160314070f080c0702090f09 61
    0x20007030150a00c1d041405c1e21018029004a04210014903100d440c5550f1807075002c480c0f10340c103100301254074004a001d007013415201505400341150404010b0030f83d031100c0c0b2190b07101d04250b60124020260b0310040b00d909407485400ca5020109425404000c100345407440300c11445610584da1720a61b18606482c801c01c201c0311050380c7c601410502801e100d2503006030840030311400994031202d1001180d8a1103800ca074100c1401c2000201e801c1c40c10350010000c5030000d2401c2c0c0301074640c4103032100e0007503054505054050880c6070002036403020400100407803542450140207542e2588038a030002c4046941d4500305070f40701c98406001182c41340d25403241050622000700000714861419540b0301c094407800709031440349940c5418590048504d2014188a1071142c00070000d83c10700000064100d414044541849424090800681c070743c0125144030f003502036081c280300d80d507a46251061284035426009402980c21030a200a240d45404038074024004003041c1d9200c4100c0504182c1c840301302507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 695804703 1250 695803453 695803457
    0xc12050a0204120807030c060c2703050d030218040e1c020f060711030909070207230a05150408010905060709050306060a031101020721021903080d0c1e0e090108030a 73
    0x41484000520100d0042a05c0c61090510b80302000140e03d0714000c9032001e0000402043c1d0301503480260071142c7c000b881c2c0c8180c90702c510403012419519101c1c1d96181144910301031640c00034007049900c400052110303c440004006000d0007856042e102c1e142c42c0c0030040404030f20420000405040e00108840c0c981e101c03081c005100381d90300c44c0022100405915a2502103010821070900c054039288080752240002d9001130540a241c04207005640a040784a450050116018282d0541d2042d13107100c2250070444000c1d0601f0041c984c2008076103c0d581c081021580303030228a008010000c1042886000d0a444280d211503581040c180c0b9030000319101940003950039024030006d49004070b010700400c410320486072455220503070081841020240b404a50361700c141c110f02140303030900d07240f41492203030344a00c00d00600d541c0d960070f654001e0b110740144903500c807030149150034410040284202d029003008113148403018000780881e0b8014440a0244e00600004140343c4000030171591540613039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 695805953 1250 695804703 695804729
    0x9150906010b0d0f06080a05060610031a06090402090a140406090e1905010b0d0b0109060902130b0a031e020304050601080f03160215030f0a1532040c12050a0204 71
    0x8940081c0041c07040c150304400e40b50399170401003010702c400c2042c0b007401407144004103540d06080041042114100480004060800d03a0200200805000c00d200d81c1700c0c156042500c03404603d00003006401214500c9811240308080058a5401b07580c620f0304c580c0b82076400700f22154035080004155020052203015a5104e240d20056000301d90891030041c9010b0f90001880d1074032000021003201010209843e01e01c50000184059000c0d172003004000c0541d44411403801030402114102448031780b042a10007030002c107503040c1c02e5000c1d40003610b40000c481d0001c24500040382401c0c000350425201501d00e4441c0e10000301c0e04800002d51a602d450b80400103604220380c0b40146a2116403c410032600300d030201420055006104002c1c501440d02c4201d845030302d02e00b1000d14000c5500c00364180c0315520100741d0401c0101c101c02e050a04032400608d669082000c0c4c0c8804645030700820003030039002460000c10001190b400051140e000351015020712517920380c3c00c6030100307a01a9009918807a140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 695807203 1250 695805953 695805967
    0x906120b040b10091b02010f05010f12050c0604091a0f0105030604090222050403020d08100b0a18030809040f060305060c0309121801081e0604020f070b09150906010b 73
    0x21011415503c10a01e09254080c0390300d60212800b540c100145441c1c8440400d58203200c020b0b028040ca101106070440100b00310b43c0741141200341c14104c2e03c2840d42c60070f014030080301031101c10301c0088610100a090030395250b40d43d801c2c810007404606801c0503001c80e414261069850301c01c1d00302010410595601e0300b991148001c010081c038241c2001c983c00f45840603841c0e0200113240300039007841d810042c00a61032516007000717804c040c8202c20b62401c01c22a03008000c0d0400000d010031007030360702d2101c10588502e0300113000c2d94404214080300d2181400d8074000003c200c2c1e59001421124400d81d402d000401c4000c04c40c0003680e0072408001d01c190480c00c0010b2035800c500d40515403100044040314090002c071901d04019901440c9000440b690b8000b8150b101c0d42c21200130354004050f80a800e010260344c40f0040d210b41d0f00500340c41d100e2030300024004040c1003103106894405806c283d03154082e0900441181c1d4403513038010134501110002001070080c4030085001412910064600d51070051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 695808453 1250 695807203 695807213
    0xd23090613151509230705030a0c3006080a2102070f0807080c2704020a0518060a0501050405060a0813060501031202060a232502070906120b04 63
    0x204080002e091560b504480444038030300034030381d4000b4003200302c0004800540c400350040e103220f161410b520050310b41d01802480c95102c000c607940722228901c0028007185101084550070b00345003580300c075030100d0039240440c0e24080ca8501c42848001c8410040256220801515246118800b500c210703001b164051990f1812300400398915118415910030507204da8a007061321000d0780101550f544903810601040f0810061071907694400c80d00380c21402500310610342e240c0105001c0007140428080458115150300d101980908801040c3c0482100007080812040d4803c442c102d102e0100030b140000c103940160116800d0f40c00c003a08032450120544000e4880720006032801201010307229450002c60070900c00c06019500c0783708902c2c08400001c41c000c2c5008006020101d18501d0b00417440400c4948007100c0c0054041c40080d400075a441050843c00380f0924506004c6620f442c1001402e0540e010519006844500500300501a21004005420108400000c2c40075503d10040b9012032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 695809703 1250 695808453 695808473
    0x10b0403060f0212010605040f06030501051e0111010e101a0904030f1b06020706050f060603190b0604120b011a0d02030a02091801050112150302060901050d23090613 73
    0x410b5101000d49062040c2c503d41c2c01c148426401440000c0380460180000d62282c05060b00400061405111070350402c03001810a209414018007181c14650200b291b69010702e641c00d800c0d61803000200f0200c900b1110303c03610761301c200309240080d41c64960324050f4614105c10f60401581e01501001c06036550303682c250382c080e40f0706030140c080c000c80b4940f074140d01e06070b07031502d40f0058801c110140e11031226183c40400e540d0041d08501c0020051001c200c002e880300804d82c3c0c0d104003040800c21103401040d000d40002d081c0b203245142c00030800030780400c001404c010303031051040c401c01c1e840b01c0ca6039a41402c909a5641c0b10304007803050310700b04000a00c01c0c5168018540000d0401c0b0014a801c1d0342d1000038001d507040841d4948019101d0004010640c0c02c04460803551040c12030503c9190191443c0030b0307110b6501c0c00028400c1202103030102c0701c1c0e4416415034444200401080280e0b502e034441d001e030042c07a9807048580c03544444002843d81400854068042c0c4103a0be10840810810381e80d1a540ba = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 695810953 1250 695809703 695809721
    0x321c080405070e01060512010506070213021804091b0614070b1018050610020a020f04090606080a210f02150910180212010c0c060905030702060c0303100e010b040306 73
    0x15114040c0045100c3c1e0110100781c4c002c04030303a19150b81e03910800c4614082403e0503403000b441043d05200ea503001d612003c1c00c2d038000d4800d546005036140640003180c021642d005010766041031803c404d0f4010020801132075901c621038180741c20f060950701d00044070010b411150802d4a04014000b842c0002c0b042007103603402c01d841d4202c1e100a1915429280100d58500c021516540d40b14801e01240341010010808058818406054101c01c15008541c80b80e01050025018a6583c20030f030742405170307581c003840141c81e1600036144610103608012100c0c0110303403440c1d46c00010481d000313104180181918600c1c210789801401000c140843c003c0d003945802801c40341ca80c0120140807a84000c1d034801e41101c0c1480c1c0802d401e9045e402d0040c051407003100701520030346a00d081d50150100350004546040d042d0300000c0491481e0389071900754258064403000942100300800c4200800c0008000303580f00700c081c0c0d8102910540e580d82804450002841007920380c000c00c120910101c1e5091b0000c00e90 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 695812203 1250 695810953 695810963
    0x609030207090e010c110f07030b0c22061214180c031c170915090307061107060e07060e0d050109020a06020601151806030b030a321c0804 61
    0x140030b50b1001c2d541e0554480f800c003a4600e95480110000464102101c101c14134a43c100400c51000c0451440380e17115150301000e89812500d000160b0442030310005c0b0348035000d0360b07001d060742954100c501c4602c00031140190300202c2c40103018440c000c44503125582164110010050194544040d5458050411340150710755002e404070840e40c80d101042200d25200780c0541840000035099401000541040c40d0f0300e281200701814840139034400078190058290b0b68405ca4480c0d160008a10f2075440b80c4103005026030308200c81c1c1710b44569044050b01025004650500c0500c00c0800703070740d80740e800a015107004100102050413941c101602801c5050f4401d200001d80304200d90001180046140d11003030042c0d000ba030040c4400710345441200c2032802c090610806803000400c0c00400d07001341d40500307002c25949035540d114a036000c00c00c034030540e90811a000c4d00d0f01d10200d1800a8401904203e050b0a601d01e02c011051010001708054400c4500b180c880c18518120707402c42c2d05600190050b64 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 695813453 1250 695812203 695812213
    0x8151c060b091f0803090609150705060a0f0507110d03050c0405061b1e06040305090402040320030705060a0917070503070914060405040f0b100b0d0b0f040204050a0306090302 77
    0x8901d440d041109400f6038221048a01c3c0c103c5424942034500000fa04149035507002031000340c405450f003005481030940700302d0700120031164000b00c451540c011b00c10041c3c007501c580028840c01180983c400364100c100d4000a10059a41d10419140c02180806c408200c2c0d00442c00303080f103244031342c0c8882d402c03000842c039042c54640e881c4006000b83d0001112444950502a48500000001c00007655014603100c2d144000201c0004082c2e142d040c000d002a090040010340c0e410070f0741d01e55048074003441e40314145000500d0507601b03092124400707564050182c03103240004103040c40c01e101075429019a41c0d803400e0101e410315a15a55020395141c0c2031001c0e03c40d159000c99645c0d020301014000d811f520b0b030002004c160b6182e0900e4000c1001d00500e02503031800741800b010603051143c0d048003a40180300c00c08161503c108841d11152107500200030103001281454004203079070402c034044081183c0c0940c4135880481084101d1140b8840d0950200c4011000c0000441a0700280441402401035030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 695814703 1250 695813453 695813471
    0x712032a050703111e280803010603020904090c060c17040f180e01140703051e0f150301050903090307140109031e05010203045106170a0308151c06 65
    0x170380e40040b0b20f06444007942000300c80c5001c810760101600d49401e8000b4022041b41c01d1900c644403a80b2042c00b03070b40d04040d00082c01904980780e81c0c001d01c0d0a40e40c03188040300c01c1561200d0007442040140400c9a41c0c50306801a012002c986600344e030261100541c60720100e03854080256800601030302d6007200341da1590003011101c0828421400d1041207140c48486500d08018010222803005042035025180ca904404991904080d0aa88417034400020b0300a030f10303a130300c0441c507400c19440815415030034070082004415010019040140c0140c048400142d12050756209901c2c5c040003460010751900000c20204500c0e8941d01080d50030241e1644003503030152105420390380111020382d02e045001002404e2a04c01c03812240030343e9000721200803d5020901085071890070103044000daa400b000c0740303500302d9503554014001400d2061002c5900325001c0d80b001d4407040e0035181980403551072400108600411103600081d9080240b000158002e400f6507541600b605940503600d00d9aa01084 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 695815953 1250 695814703 695814733
    0xb07060209010207080d0f0f1101050c09010e0105030f040f21050315030a03080109271b0608100614041806030203010f090803010902030405030712032a05070311 71
    0x10144240610409a80c6442039000a03141c0303401640903003030075401200710050040d4801d00c209000003ca1a0030550390200d00e000321a10350003100c8413134195103041d0030300100b41c10000040c014200207803039541000e00c1110046d03481e8002100d041d801c0e8403c600009001400c0c913041003040b00e1141c60b000c581c43c401d103000f99808452203200340000c2034000040c0708040541c0f100000d019101100180501d0381c045d41c0c004c240380c0040c0700d01b0110300e45402d03040d1100c450222044101c1118404a50703030a07011820109102c0c444003020100d00003038038070040f500511074041c81c2e03c2000d46500762005580f900e98200d8410b00e00d200611194042844041003844480e800105e4039180c0c0c030700c045262421070042500b12441c58002808035880c180b082c40000d10420b09803070444062140060700c0e03980c7c07410102d04501c036005004003542c80d030460101310741d43c140c0d001095441908030500700264420300d201d00d640240907141c001051007400300e500002c1c807511102c2072443c91007040d192640000150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 695817203 1250 695815953 695815957
    0x718020c0304060c1109011d0403090b211e070c020a150807031b0e190e10080f011127060a120e0105070504060c06060302180103111503060f0a0b 64
    0x400001012003285509001c000d0201e2121305d1812640c0c01815450a80c2d841d00155064155810b40e04050000a00741401885000000d000e40c03094255a03114091106480485111002640307000c20070215042030500e03940b942c6120780e109205085130b199101d0644081024040c2283d20004000c00841e090100305503072482602e42c0d482d2603500c1d00300482d021b41541c65080c0d48110100c0c1074604c118146900100c20840c8bc40140d0300200d04150281040e601c0c914030340c1054045450302401d00903d001481d550300212408042664030148081b4901402d840b00407005481c0d8071000e101c0d88048046403440d03054455421849851101400700c0401c100d0f401c1203000d4004160b5260034032007040050f006400012a5200003044a4038003200e01a10078000c40c01404100000c20103072800b040502d134009006180c008003000c0a0541540c2641400c0703000740011196908002004469402e007103003402d01341c1c040c0c000e2070390840d9500c0c800d025044403c908000c1e0300c08a0000005899404540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 695818453 1250 695817203 695817209
    0x3190c0308040f03021e01020601150306080102040b2a101a03060a050a0c081308030907121128051903080309010209040b091009050a1b03150501030902030718020c0304 74
    0x14043c140c0b038034500410a2400ea80d18040344a801c03074002a000c1c913a800714016041d16132140c058800d640355650214010125a0014a43c40d80b0004000c12010a04d0020b820032100714000e002c451060442c3c2e00c40380c421226175082003680204041d040305619a00094402c00b25840f070a08001c03031141c0000c0ca805000d03101400c510341d4610602203084903600946569580d1428500854141065182c142c0d03410200040d01c4c207840407012409140c03040c816503009210003449000300300c607103090131a00002c640d140f50388912403d50000e40d0590180c42440c00320681c40c03a448030b03254503180502078000c40b8100200c2c00d20110042c04030008003074202850040040c4400181c6815a90f010301080780c0d808082c1c24407904c40c03c800c0020380c070344000112040da249a5000700f0f035a1140b5041f00050005c0d1740e1000c1c04a85c0402d24002041d5142c2d110030b0503484000b25000c8c41550b540015030071520420b60103034068000b090240480c0213a80f0321010b030f000f00040d006207000c0c0180c1d001c80c1190001c0e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 695819703 1250 695818453 695818469
    0x110a0801050103050c07020609060d060f031113050c07060c35100503100c030b060d090b06060f160512040308040906091a1002160b0901081503190c030804 68
    0x80107010550f810301ca03682e44203c5e08241189084215000a034003401084c24241c03140c00000343c0340101030718541241c03004100047d080ca00780c80d01d03858020341c20886601c4031030040e4000c0c2065152001940070752400380c85880006407901c400d40c0c48441c0900071025807003051002e10411810001011041041e4060403469030070a0525022145d001502001d44128403400c400502030089a03808a1083c0c400c428070034000889121340841600686188542e80380d100101056000d049d0a0f5508100b00480c812840806c0d0350b0380d064100803060007001c402110440c414094402c1d291070144800203010b02071812512980b03008040680251300c15081155140300100301040000e58501a01c4003a00c40c00e5014048080740460349030540c246c44100d180301c0c01050310107a012600a00c28002c01c002241d14010401c0d481d070724a101603a21014030a070014140800007604e116581d12050b41e202c0d0010060310a03200000b40d00020b5161031102030f40c140b0056200040010a000003c4c07004000036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 695820953 1250 695819703 695819717
    0x1060306080f060106050306060304060f0504030e03011407050a120b04060b1905033606070906020f060405060703050712020a0206240f040e030f070c1410050d050703110a 75
    0x540c0703800e000314200400410781c04030005000311600314090b40d034409400c1d11195100d940320b040c088054018406050203551a08040c8024942c1c0418144c2482c0c005030001c1c40b40807140101c0e600010021507900000600c203000510760244908010000c1c548201004103407001d01d00d00003001c684141d800003041c000f000030604104103c00d201c2e25100d06490401d02d00f10f24080d00c00995103010355030300c11105d411501d443c105810345024582e6400c001c00c001c440da076180400307000c0c00b028454001c55016100d0400500004200060a20b108961200c09400c0307944410302e080d00641805010340041c41607803950520305807810300c003074048450b0660040c06076090620550410340a07507a051703030703448010550300c080c50389032007001d000900f0013035030006200c04102c41004d05601443c091100760000001d070240504c02c0801c04c40c0c042d14290341c1d0303007514191071004010030000400b0a080204a06002c808000c140551202d58000740a09020902c1508048803d2455201005110200f035203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 695822203 1250 695820953 695820959
    0x140d141b0f041a0d1404060f022a010e0f06012402031606110705011413031209020d0b09010c0929031b030106021e162105030301060306 60
    0x3400031120001402698598500005659603007803501c11030080070f10402c40c582c00303034050b40c03004401c4034804d01c01c0312800c0002c128090504155000d00740d4095810701e0034822030006000301482103c030749840c0104102242c20124031512400c650f00b168482a6560310b403240c0140d0724041c0410048003031168080c014960600d40c0d2880e50b104c114440307a07002a650850b504502c0c0e00042118145191000190300c0c244140c40c0c80006130031484d0b00e00030b8111000c03850b0000c00005401c1460b03a00509030540d03440b5600c030a0100032681541c44007400184026000700c0404a595001c88040ea0024015003030081280e100d0045048041e5019130071a0355070107186070001c0d80710b120300b00600751900058142d00c214015200e2090062405501000700010200f10381040c405003640181101c5e101541c1c49682d140300103034642600301144001640f800b80e4010718450080b94080340e41000744080041c80d42884820700b00c01c0704103011403108011729041640401c81c10406940288400e03039000c01c0ea0341c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 695823453 1250 695822203 695822221
    0x30c0605190f05070f23010606170f13050f030703050403030305160207061d03010c051210150e130e0d11121602130e0304030303060b130501140d14 65
    0x10800d0552042182d2082d907036402680c8281120102900310303004040c28070840c140200d429070385207880603030070313618407141121828190040303000c6074515100d00707100004000215000d0316007158150301c50322074040010361160040189515150258044600d0300c0c2c035a140903461640030601c20f0307000c144045420001c06500d03000c0c0300d9211000c00c0280202d62201c1501940e10b142d40e01030030041c420800d02d08402040004a00e0590880040007440b0001d0b000304080c10360380c003d18940b00380c6810240002c04c503480c0400c8100440c2ca40d804400040c1c60308100440300d606100801c0769005042802d48030620b0070302e000748440300d41010b01910b030180304204041d0000030480d41014658000d8000800020f80c0b01050303c605031002d030a5404045154800200c100c03000c940c6505601c0c1c07400a1038460400000050815a403281c0c50402c00075403140c04204890050020030081914034a006120552041812042500300ca031410790070101c9190444040d912101c10700f0055404103020417130a01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 695824703 1250 695823453 695823487
    0x6100c05070e010321110c0f042004082a0105030a0209090f01090f180b0717091005180307031409060a080a0c09080d111c0c020109060305060f04090c030c0605 70
    0x1a05041089445078414151b40d101d4807000c0314035105600300e1030f40aa150301c1351f400c40400c0000e540348040e005d40340b8079480341c0260010b014001c0d8500c10800821044041d0840071407010000c1405c60030400d080701c0045805600c018000c42c0b1141c4c0a00c211144c54841c940000d003d504143e0411140358100b140c207400302c0d80c0b003084031030a607420652500103014141c501010000c0c2c0004900510b966101f00540e41000314500c41d504011811080000381d40010540040410480741c05100c03c0d210700051140705444444040030a80042000c01e000070b019040a455003600190660300b000001400500c0c690000300307014001c16441810840c500141c0c0c4200e030030101c06410407026144c181003000b5620103c0108820620102c0440c024030f41d0f8041003010603204500030310400c4a06500c10041c25040030a00c02ca001c00c40205010030502c1c024000c04e8810007010b0b00c00c49101404800b04009842104d030705449458200001001007103004480c000900050307146c007555544640041d01e011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 695825953 1250 695824703 695824763
    0x702030f010c090302040b060403020d050715020703121101090204060803120a060b09011b1b0312020a03080a021602181b07080909061f020610090506100c05070e0103 73
    0x564504482403802c40d41141400082e250182d030000360030386401005c00c01602ca9900003a522107040391400c42003140004a0006441103038070480d205580644003681c7d100e0441c00014140390302c613001e0348130b003910552200003056440400407400801e6a00464112031558010030925000021000d0743e0356198030a0542000354131f00b0400070340349410240140e030b004041305541086201040301c1c00107035200103000c0020390051002100d00c128602c255002000c0d6210840b0070211454030800c00c2400410b14600c4240c240d203c0416654400301048000d501a010706440318601d03420000150712900c456229103081e101000d0b8003420542e0300850306044255a49188600420120000900302e00685130041c500751109140c0740c484100040460480111415112000303178070040741a80c2c0040c041d070241407010310342045d05855040b07010035500e084a11030b8004000703413100c183c19480342004580c400d01034000d6490203030b00c85010841d403031003e92050341e44600c030f110003410924040900c4010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 695827203 1250 695825953 695825983
    0x201503013002010f0513140a060203390a0606080705060c0705131e05010302090c1809040201051309020304030314060d0611090301020c100b040903050f1810020102070203 75
    0x48100c11440002020a01e010001d0410181010400000d4020026519006001a8056100341c0c90716104450302e1b902050b690302c41c4904031000100c80340040704131204510300000b0040040204181244441a4441421a9041c5844648520341c001384100703511640b00b4040803038014900450b071441c200090700000d00c101c1d000c001c044402d17071000500c241101d00c16541444684400304514000304400c00b0303140101410000544c0f003002c0c1c141d00890589100322907059480d21410000c0050340204613032850fa61104441c201130301e281c070264070fa5016105140051926040707070911801d1102550200780300507008000e00003055013602504080316240802e00050340362480005900d07560447c0b015082c26500c51400c240701c42c111080b203145030320240007990342d024402011a42c0c0d4072030182d0312103000e140182d40c8600f81740502a1541c2a1f4140c2e4416003030188000c2c80480b19804000d4001d40c01f54615040c2007180c1b1000701400800c941d40e0001605d82005006141c1032590708400000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 695828453 1250 695827203 695827259
    0x3070807060522030c030f17030c09092706220c05040507031b12061401050a081503150105100f050a0f090902040f0812040302030a20150301 62
    0x5007651020641c0c4040600241c00300000b4004910f0840c09260350b000503000000ca04000302c288520001c4582c2036070b1003007101c1d0780f86507190104051a0f000075100700480c8001006504424038040401c11b420401454031941c0502e086140d00c0c0b07214001c4090075005401a20400620500e100580300c041050501b00360301c40b40095036414150030300360044c51700c290342e1200414410b621070b60042075010303602e1094550941482c2400780c25400d0310301030750021604204003c5101c10103005103a11401060b101c050400440c08001d450f05ca8000f00040002003c10301c2d191441d0303404200d01d00c0c00421018402c0f07265414141440382c8030306004156810300a9402030714080a0340032003100d006412901d4450300101d1081c808448445c082c1e84040100c90000c10b001c203c00441d02a20001c61300c00c0d000f02c46024030034a9416620b80a80e04c4040e505400c51741002020401d0762140007440c2c1c8540200c896041d045030f00041c08518010b142140c50b100110040c07000d82c005a9580b07241201d01c2c240d00d2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 695829703 1250 695828453 695828459
    0x5060106140307050d090813081f0e0c0103111201030305040614030405063c010f05010c0b0105270901090308060a05031e120a02010b0a091802150c030c030903070807 73
    0x41c20030300c00c2d1510307103c00c6907a5101401c113004004050792000c406800e428103070103949100c06940c544038429525000c0d0550790503030120b10040d120703cbc414004144003600c02d505078000150000c003400080c00321202c50800c95101c0340240c808103070340614840d4444545960600ca001480c02d840300c0b00d0400c814408100344004100c0c006501e95010010a190402003002444d070000050701000f54070b07008075106d02414512050540c6503905a580d0a032813414000d548000440c4c050522482c00b40c000155030006110302d04003641c00c054100070106100c100c1692a207040e0744282070803510794803143d5540000d04105940320002a400000c101c0742c940301e89080c0310009803210500100c1740341000c0c1104103401d45110030704c1403508181011100302d84601d50b40c00003902078094400032030310a44030b607140808c0c0d10701180b141c2415400c1894029082030300701d07800e100048045480c0d9486a135030600443d0800482000100116002603014507211200141854030b0f054480e00110030300d0300804818 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 695830953 1250 695829703 695829707
    0x6050906130e0c0301090b04021512150117010305031b2107020d0c0e0403120c090909060b0913060e0703030e09150901030305030f07020a120c021c05060106140307 72
    0x5901881075158005201200c1100711868600c0841d0415055400c1400a00034844148115440369000303564a00e10f01c100c000052040d48075002c06100d8414203403010800d04844ca20042d034034032ba01170400a100000713041100d101d80b0800d078011a080d51000a04446104440240317072400400c0d60300420844600821821800d018512a680040c0c00800c5a20030b41d0b4580009103e000c0e009810800625110480c42c480d000003100c1c21740100e01c0000000314565014820030051032102d0343c41c010254140700c11840508401c950a60b0420340b951041c454555811001074000c044d00c00ca0032032507030000e16060b01559901c0d226003201d50885d000800100340c01000721032441400319248681551103028407140079181217003450304104160008420145c103c801107000c3c81e0303c400d1076051903651103012a0b640f0500e08004184403c180364800e5074500595016101610041c40320462110601500081c031a010343c1c03e4440317510550040001075003000ba000041c0072041d40a40c030314074040c000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 695832203 1250 695830953 695830969
    0x52511060606070602091203040812030402090112020d050d020d0201060602010b0f0603060a0e09030306040f0b10051b010504150612031e050912010c0305180a1511040b070606050906 80
    0x4142c05a980001c41d541080200c0c1e0407030382034080c014885511881c0d0001c40503501d40141c020b40d022032140348a802d5048000005481c850780d0b00a003501e025a0070852404030b04030310ba8804070780296030b02032440002001032094a80444a076801810342c3d081111009080d11350030351101c0709592404040c405191242c0402400f20541a20350700d07941c0c0c5810010642546217907014501c00c00101d800d0151050001c4011402861b045a0501c4154000d042900840b0110b06100ea88410a201c070f55030028001c502400200d0350260011412030760305040e05094034000c403812102d0154441c1207100c6a000b602c01c4e1001b400c1340c10302c0c5585100481e41d010f4007070044800e20006198070881094040c034810422250a41006481004044c02c0542c03554040c0c10301186100100342840d00164002d1104440c40090400302c0c030046c0351055a903110951245207040b0180340d500c0d210582040200404001800185114180705a94801c1402e15104441c13039a04a42d22885401052095640d50300d24 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 695833453 1250 695832203 695832211
    0xf030f15070c150b0f0a030b0109060905070e0909070522060b030f010314030717121b07020402090f2d0604122a0b09130507021c020f0105251106 64
    0xb2000903540c1040000880c1c10a0100c5d00b01c0d03001807880340210403c03118685440c100c3d40100028071003e51600302020540d54125000c8002030b14040004200b881d2900b4011380001444058880c0d07282c480001c141b05030845c459500101e2446d200c1c100100c0501d21501006104200100d411030401c03c05400c056041880042c0210b0f000c00c140094801c0280210340c40c041d40403030250f5900b4240e01c1d4158082c1c0124000c002c0b0940180002000c1394404001410380d006510400c5160500c00d50800c00250080c818542e00f0040340351645849486080e00800440d4110070100441c0010040201111044203040343c0900018001004075110302d02424001551040324020300200388504800e55400301441c40c0200c001180001404583d018010003142c50151040c004d00401c4080d0041500c205607115001a0301c030324901c0a9042940d540b004203600c440c41552100e28100c1c11260960300f00380c881000c100041240c09050035000e6103043d021035402d0900392840301580c01c07290303190345001f0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 695834703 1250 695833453 695833493
    0x5131b033c0303060f0f03051c0210150803030903071202010908070b0703020c1c030614090a05091e0c04060501020a150b1917070b0c07140f030f15070c 67
    0x30203041c0400d806500a0006407040300110030000b9a104115641c2c105107100c140c0c2c080c001d51000130880c000391a040d400019454000f41140343c820740524000340000a06003140c50307490600454200018002180513042c120020340d00c2d1045800c101040311302005d001400e40e8074000d2510300140544c0155000c03190000ca0301c022039956400c003503010703104481c0c04030f1a50081580364480a2103c0707078400c00080c03e0355801c0041a4447d0b407844980500e0880050b44042d1900014580d0300e40e84c0c103c25840781e0000305039008981c0956680454403840c90307007a4419040024880c0482c1403620440f00100320074070040001125548030160382000116003a8020b03a01d032000d40803a81ca400344081c1d40088034510004001e03a03900c1d4590850256885001507078001d00c04000340a061050a40c5c418072000707000307001140c0c0b0b0403480200319031518405581009544180c0c0748156000c4c040c18804220910141580c0001e00c0c185001003c00188440c040c085082c4000c40424000c0180000c00349840e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 695835953 1250 695834703 695834813
    0x90e07080105041805160305120a05040506070c0b0a030b090c0708160c12080c0d0c0203120d090204091113020c0c0910050409150b150d05131b03 64
    0x401d5019044c199100e00030300180b14424001040440b803c5101c000c4030302507007c0d41c2c0201c24401490041e0302c542c88070940090420300c41800503103006001001c009200b04400300d2810307030b10b100b13402c62508806001030101e0f03619003203090310782840640c01c3d50003170340300d030b0442c0c03410300c50741d0307074032030b60340031f00302c42c4000125190030200300304644010000040c0842841e02c141642180c1b0341440c2607403001002031958002d4400c000307000380c003803000e401007242d00030083e000010184042c3c0743c030364102c00d00e00d48040d610742c99101c0250300e0341c1c41052003440c0a00442245014404107000c0414460811a90761901c104023a00b15000049082c1d80041c0b001c480b80c1728a0348510b180b10126802e20b0b001700d40d0062910480b001001501074100090f0030200c9014007022030b00d4070801c0b0305a030071090120580a41008130040c03e945503841142e0240d001c5200701c3e0030140903216080b68403032210b04080c45424001040c0140550400c1c5d40c8090b020141e2111400300554080c1203402c0c1044644110401c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 695837203 1250 695835953 695835971
    0x30a240f060f060309061116050708070e040209091002030a09031707080a020a02100c09060207060206070c080c1e0f010b04060f050108130803071d030a0b06060901021207060c090e0708010504 84
    0x18a401004047c1c1001c1c07e2161100030000c0701040107611000101d0309480351400c0000c0c102e4000c00d022080703403172071a5008030603a00c40d0244001590020650b141c0c6003d52640a0164110307440510302480742000e0000c2c07010810301d0003900c01200b584002d8040034100c8100201107620204a0380c1c00041400050707150004074800360315220410390700054090a108507a2005c42d4810090021591107600325455507945a500780d031905410380c0c2140c006041141110003107903030000105980001002103d50b0a407002c407a0f81601c1c148941c0491070385d080040b20000712030090290f40042c0350103c81c20844130345848010500d40805200e9681400b1903400000c818020720341071049440c0e04040400d41da450030750342c01040401080c000030074884201100c0912800c000030318001c010350000e1001c009840e0790f810040e0070f4002000d0141148600019441c0400b002005010110b1140b003011441c8041144041e29a00280d003102805e034880030100000039601c001500d0456001f5100055107500c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 695838453 1250 695837203 695837213
    0x20901170408130e01081002090f06030f04030f0f0e0907020a0b0a0f050a0902091807090c09082103010b0d0225022814030a240f060f060309 62
    0x1002204903034015164000300410b02003100700800c1961061200a0080380e12403202c60039000c0f0a0244003801d41c0b020707580800500407640180b1042c2c600400d0718070398211000c0010030540c022542d991003280c0c941c050004054001d010760b11400c0c002d003000809980b02220007000340d1608050300d48241c40c2000132991140c000c0c0004500207401107407406083c0307415a0300e00c0144c60146c00780c04140d4644000a801c0024500c510180d040e802051804262141c819200c5001403108000c0c84030b000b00e881c0040c800c0d003240b08843c4e2041c0c4903116440c0c036519148030241043d0900b41d4000c1090483d034030703041c015110001141e054840f40400c10361070306070150b40307100280600c1d821009101c150b02d006c03810001504c104e010403188200c9081c000f2000000720349604080186203540e40518040092010f0000360000034100c0c0005000c50742009102d80302c100c4504406880740c0d484080f00c1c61403459409c107c0c0509071100d144580c0c20700c2002d1030010241c0103c0950310030001010b54034201502006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 695839703 1250 695838453 695838467
    0x2010917030a031d25060903080f0a09090e07240203070b07030905030409050603010c09031101121b0e010f0f12090f12020d1d09070c03050d0603110406210303020901 73
    0xa01d00300c1116640c2c603510200d045c041094000200c499442a100094558840c12130141038070386c01081d403403c1948402925684d504444001c3c001d004c111030300801d90020303e1007000e007016481c0004050091400c090b24a001038041000356055400c80049200e03560000202c034000c40d403010413450f40c0e681d2070030114000c0c01b20560040182c000002c0009107003074540c001d980110380880081140c1c41521030141e450038100e10005012070015940c405c240e60242500034801030303c240001c81c0020342d40c102e001080030502200d802180300380c0181c5005503030050400d030304640141090010b420852402810710240c401100e02c03001d4481e454001008903494030641c10592059500d00704c1210000041d40301d6612a110200250294003480e08001c084618402d2240700605550650340341e4020490b5030f00340341135040d818000c040181c0700401c0490303caa400114058120710181b200c24400b040107580c40f03030303210f0301342460203562040d42c8420440d0412026030741400c00603501c07510f040050740c1c44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 695840953 1250 695839703 695839751
    0x2010b102006150f032104031a071202030a1e02030103170c071203050d020307030608120a0507060507052203020301110301030b06120709060e04120503010612050405030d021602010917030a03 84
    0x1b005145880280e0158000a801642e1080c4006018041c80105845414400300c99480c0004d48503a54400511103e500441c1c00501307081c004200540c44080c10b8050502111106190903800070041003880300303d50103610640307078211fa814500310b00800b5655070b8010f43d008085098001f0540c0504140c003c804540340240c0c40e46041d5141d141002c8080e000b801c0c035204242c01d0380204007440815824420840d02d10a54a440b064240711080e103805006150003003031417040c4481040181841e645036401c00c0214801454000d43c92419803046c9801d45820340000c41e001c13907044c0014030024000f0300d21264070043c00d07900350004422175450649004907503400f40080d1494044045001c0015002c4281706038003a44a6984a901c21700c0200c3d603e1100740715030307000035a042141c1490160035400c1190014011400c407420008000a040e04903404002e0324a038040c0021444811560000780e514010301003c03448482070141c0c000d94545a00c6454492002c055582e107100c88020382e003003503104007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 695842203 1250 695840953 695840983
    0xe010e09010b1206041106040b0d0213050a081f05010311010509010c080d0c020f030f041710230a05010f17031e09130501050303041502010b102006150f03 68
    0x8540c3c1c60841481c0c0303401e01a0f800355140780e4030041e1100c50342402c030119001c0f200540f0010b45004951a80c2c14001c1d08100341003210182c1070300f800181941c0d034001400290040740060002800c286107894890f15001ea42643da140c10000100302150308010300d040c200c0c000b8205070743ea400c29000120b4882ca0b03c90401405100003180c0300e5010b0165602c1031a03034400e1902110441d00c1a920b885a480c00340040f10101c140c0c04000602c40380143d806e0414804805c28101e41c41000050646015103200010b030301d074000c2141c1070142c10440d603941c00d2038000301d66660401881d41403881e5040190818001c2c08501140e000412010520400480e010540e6101d018501185070f103500034410351100034014812301100d0a500404d949030b204540c101c2e00000c004600e01464600d03071040300c0e460717220341400355540c40040302a01d4442c0e100412a00e031300340d540c010704400460309680c0740c0704668018200e19070007142004040a2510001028001b048407403080390b001540c0020b20f00b014905500c0c1c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 695843453 1250 695842203 695842219
    0x19032d200a140c0f010e0904061d03040905190c0903020103110f030c19080907150c0515090120030c090a05060403030309060507030c020c040903030609020714160e010e09010b 77
    0x5401500030503100f0f01d0807070849920030141c090074011120081810312441d03000040710f0128000450b0380d401004036213038510b150302210100214503815500550700171203d0319101c0d030800c2400d45168040d01c450518400d000c0080c0d00010100428268840c00700a061595404240c54540e444e43e0540c0c070b0161261001c80d90324900220a00c0940d08801011500d0290b01e01c1100b400900a000581c8588540390091508625050607402c4500c03680d80e0707100174030030001d951501041d420301080703010744c0100510500d01d0804400b00381c21943e6101c6245290f40c809218410480300039070859400031440300d00d01c0d444510500c001441403205501450740408001000800c158040e005140721501404003080305558402054055660304214600181c01040c19000b052419600640700c1078040d04d00014050345a00044049038403503070040d120320411406d180c8410394104208080700380756540c428900d80c0303000300c0502c5000d0107004c0c42c1d1180b20903c000900041e000d40c800002e03150300400c581 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 695844703 1250 695843453 695843483
    0xf0f050405100c020301110712050306060d0920220e1c080711031201060507060b221505011b080d090605060301200906070519032d200a 60
    0x2400070903803030f40228001c1d400d040003601c0000521007510403194200c2c149071515004d40e4421201a4030042a10b9070008003400b506c4022611842018040f0f40f1600000b04e0707514480c02c00d6010782a031028204c1c46003901c0445c4480700c003100483d0b80e5a45490090100d07103900030940075400d0040400c1036002d0b0600c40c00c0800505ca0384045814041c0149480d03400118182c0c0a19644174030442003002070502a04004004141c89a0014460a03002c0e500000303070600658002903011040000c1080e20311002032079402d60f54054440c40e001844034907210404149003a0000c5c081e0306502201642d004103401c0a8810302c182c02d0205c40d450341100300c2c10005400d0510b8010010801a5441c0b4020742c6050f0050700030441e01c100c10424144117041303050510410604010319a44105400c40b000d000304084030200d0000f031410400318911030b40301e03401c00d0780d80c214100030304d242c03420f1368904603141c09031001c91660f81004940b91030025020165906184580c0154648800514003c2566003013140d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 695845953 1250 695844703 695844707
    0x20a05040c350c03070c02030609060105030d0503011a0c0304090609061505030f010302130e2b0c0c03030807050912010902030d020a02060409090501060314010605010f0801060f0f05040510 83
    0x5101011100b01c42c02040c103440c440c80d506116240c4000c40300d500004144503d0001c0e0141d036000c1250b00e40040915034a50202e81002c40640b511449a44010014001b0345070500488500ca081342c80c002d4255854480054404000d41042c1030701c0c28400207c458044a052084030b024048805003441081c1c1d664445000504941c4240f40e00c102031880322b0000b091203a411a8014079040c44080081d909540821119000350440c0c03d02c01607030b588854270941130a200410040c1003800442d06910304044a80b0050342d04a074010b400c0052000c41a07000414109084c0f05598143c64150459581c00205442c244501c21000d94005c0460751890524501500500115171003a400d0700c004540440c426651018031140095000b03106200a200244059000344245070203007002040d100d58039202c5003220580c900c8132042c40c0e5113548040c0603550300141c81040b41c0c143d80c505140150724104009115000500c044000c000000d001032800c035115030180d030050300c030052184803800011800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 695847203 1250 695845953 695845967
    0xb07031b05070e0a3c0f020409060906081209060d0932030702010309060f02071b060c080904050403030908040b1209030a05040506031e04112812020a05040c 69
    0x1443d11a9030081c1d00003070210344240203010854509101981011543c2000c50345914901ea2503841402e070180b1800d401c22020b40030701e5059000d0804016941d509141c0201c0a4400c0e940007000c1180c00c06200700519000000c1d400091a80151065240d080e8034001920511681c5031022006044c80271000c00d11440e0740c0649048040561007231004680c681240c0140c0750003650a05060b0800d101c44400b55000380c0165003007501c81c00002038081c4c40c002d0b9803c12038206a07401d03a1080042140380170b10054140000e0003602e15824084040d481c1942c1e0b4210740c0c400d0008650203552280040323420540241c0001400550140d11503172500d07291162601c064001012803641c1042542c040341c4e00700c0b00807088688014040d0b5445203071034100810f00c4015400508407010032240b540c111004e0070104080f0500640c0300d400d200d401410b440c2c080003220000250700c030b0b6455291540d00e0300f1aa000c26490411903d0304190005011f00c6400003c50b044069881150043d080c106101045984540c0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 695848453 1250 695847203 695847209
    0x30b030105060a230a03050f010618050606030403030209030f060a0219140405150d05190605061318140c0304020a0b12040611160f0302010506190b07031b0507 70
    0x801c0265900c904000d254003081c851580c20302c400b44003100c1450b58503102d402c4140c50150641c4c0005603a9900c5d24a031240180607a505070b50342d140f090111241032010340c000c01e468604103110b41c0c24100009103d520001e400102030641c00a100704140e1800d01c600b050000e425400e50307182c2c1c03500e25444c101a500040300d00101c0c2906007a4502c40d5405440c9003c5225410380c000c1c0d0915062400f84007240b407880303030710400b42001400070b0044200d140c06a24402d078207001e415001c3c095a1032280058650580000788030b244140581400c002e0011003034400c8038171020200040c1075014010b11300809202c1c0c00c02d0100b405500070850140740040085005031b100740c2e502141c2c40d680b650f103c03516004811415000041c1d070004503010a5960308802401602c01c0b4115242c0507200328160650315414108a4a0402d000005414150203104443e1b1021044d00c1e5040c4010100c00500f2146d40940500c001d08800401c000c02814032404074801080e030001410309048006061050365000944 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 695849703 1250 695848453 695848459
    0x100e1b0a030504020f060a050706091a010303020f010606110606041d030724020901120207241a0a1206022d0706050a270f0b0c0c060903190804060b030d030b 69
    0x141451445c2d04201003100d087d031303c80760340d11810b10020f17958400240c021410140c84030a01741106000301d0740c252000b107000b54840e400504441c2480d502c02d50946440b0303800402400040709160300c40b904007085055000c02c00301c90000c0d411503450040d1440041107d42c4640ea88004640d80003045600e98441031110400b10035803610100d0102d00f40140d1090032141030001d0b0742c07100e02c20380c00425600540080d0748141c07050382c1d07081d2032540000500303a01c041c2201c21003506c41c408050311142000d03115003c4c00058484568240c100080b04820000724527005204640c00229005c0d0b0381b10707008446c1d003000b0005054080c8a0600c80f80c651a039005108143c54040c0b1b410003054031907030349106100e032251078448404040c91804c2240d40a48500c0201038400d0b901c4450705400152020490710303c51080c068040780c0b10780c491b00002d45011001004c041250740104030110012006105101050080d4a04010603607a00d2600790090460401c1842d0944584070400c09816019040001c1e0304d041a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 695850953 1250 695849703 695849719
    0x6070f060c180e01320d06090308060414190209040f2018090c16081306020a0203100b010c05150402040b040b1011160e06010206070503100e1b0a03050402 68
    0x1d0960b035000c2d100f003881565a0780c2e582c0b0794801d81d00c51018880b1040240300e410030650008920002c50781c420030790041214400d83d107000d200101600000362682010042c0ca0800428540b5250403250110140505014041400003029501e0990301218007812001c0d00501c084862078a47d200a400500a02d00c0d20b0500d144818140c68151803d44007100c45800081031034031950000c0c401c4d0082c0182c40a030303101d04104100750900d4207040c019114148958085540e91404d01c5556854440b00d0300090210b4000e10400300240e0b500040c80c1d0960007044200083e1070154a00503110721005401c000e14a0003641c00e800c0982e20b00500c510b129500988062182e950850100000c0b16001210703250300452203800d19100c10710421a03450030040313001c101c4212100100e02d40d02c440130076520691460201c0e000700249942d05001040d004801d90400302c0c2503043c059155000080f8901480580704604400603040302ca0500c18040780b007110841d210754a210510004002c3d02d0120ac0030b034011069 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 695852203 1250 695850953 695850959
    0x120606040c021b10030e0a0320071d060a0521150c070f031b11040605090709061116060e0907230304020d0206130602010b1e06070f060c18 61
    0xb0440c40d44404000d010041c3d080300303410400c216030140002080425a9940c2040c1c98910100b011101d054029240d030703070343d608030141c61103440c0c240100001c5d8540c110020411007200e9400d400107205810281103e130700d0b564140030402c1901194042a4042c000c0303040d9003401c500580444010300781c031300292803c1c08001f00c445c207100b420030340d2050a94001001840c000c40c20fa940700800d220311138a07200448200008102c0c13203d81c40c80c1c406544000e040c4102001d80e00d0103210b000020081541c1480365860241d601404100c0c051141070300740122411034036a160401d02038503080d500c103050800d03507083d201d900080c16008415040f50080c1a2003005c543e07554004c0801c00c400c074a0384040190403040440704291140c2000c0d10490f000101d1202d5800140d450801511a08110300d00e032070344080c503041c1e0080c2968100c819540c0280c50750324142c1c06200d24452880c040400982d0003607624096407034009800f00b0f00b0300016001500d495800504142d1080306c0540b00d89a2044501003951 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 695853453 1250 695852203 695852207
    0x901181b1a0a2007060f03060503060114090a090f0b060f0d080a03020d0b030d050a09090b0904060b06131509061812020d081c1109100815120606040c 66
    0x95518150302071203080c01030301100c0f403150000e8003c01d21084210700e03440400786241443c060464111401080307031a0109115a5403611981c0c1c0117040c201c0080446524241d02c405002c9545c0a420340211080400211052074035004048841e5010103107042074a03541c180b0fa40c2c070000030344146205070350b080030048182c58090011143c540d00412040c0c80c0824040003076000354802c0180703c901548900c200c41890307605000002000c0590340f61280d5495248800404c841c8803600500c05141ca00400300c0500d0700c0d2415059030150380403000040b400414800121303240a40c3c02000c0c0004070321031010a1100c4030704003503060321545032074807403d060711500d0590b028041e5000c0507010703c10460307003006520000900980031b6030000c1c0800b05003242646440d00c40e0390003180140f45421100f03203580c115150621070101135141001c801c40c00c04c0341500c00111128105c2401c101004500f1022814912644003120703848200104602000f0076900b800301d403510000c41c1d0403482245420b5074100301034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 695854703 1250 695853453 695853479
    0xa151a0301091220070909030e010c0809091302090a0912050702090f0606090a030605090601150806012a1118040c030f03050d02030106020102070c06180303080901181b 74
    0x90b0b442100500c3c41c80c98070030103c84400380095500c444056081100349032001c14410040940b41c40d45001c80c80048a00f805080d00c80a005428100503412907081c000c1500f03241500c080740e0048034024282c5d10384c11402109881103290183d805200da400b401440400741d801200058440c040c1c0442c4c44c03500c80c106850300d004e020300c003a41060f100000580710b240701307500150b40404000d206608280e428000f040c81e64400342c10441d81c3c1070741c0d00c05109003840c00300441401046a0740010700159a0740100800e040d4000e400a814402031001000350442c8441030303910040804501090690028108007400e9114400d02c1070003020039403892111196001e9809201c4c0d5003110351012030a1a690302c4004002c00e20b18150208102403024050071401400154000c1240c0d03400540c446400303080001d07030502c40368016000c1c0400510186c0e0405150f140d04002c49416007081c000d65074842074094091f000116080340c000d0785004219040000182d44404060004049000c0300e0307450342c00b005001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 695855953 1250 695854703 695854721
    0x9101a0d0b100305010203040537060e072309061503180102070c0e04020909060403121535010204050d020d0201120903080105100513170a151a0301 65
    0x42042048a080401d06640038507400441c40030720070110075038036240d00c1c1c00c90700b05480464240e0009624104a401030311000c141490804c0ca122413040241d1403a00c00c5814020380c024a02e544845021042040502c0007400034501c56030030b0030020401c40b6102c4c0403000010350b030034420b44221003c658242010782c040407882d24261076061640d12010020b4a44003100c6010f140da42d034003000018001000ca01c3c02c10024900d005151800c2d041900c10008481c100802c50f01030b0768446001c00001c00d5001d0f0b41041e80c070106201c00100b40c031401511000158083e00f00728001d2503101d014a000c0214a6251040da4145400b0025151070701c1010718280d1290b80f042c0e0b45e0104403a9042005482d10310072105010388141448900621080c00712816510045025804100b00314010800350500300072100c4032a51519246240c445d04031400c10b09804240203072064500d207441094010030003001004540b640102c00401c86014800c01030020b003190038004042c1cbd40c20b01c803440c1001d06050160400c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 695857203 1250 695855953 695855959
    0x909020f0d0f1a060109060503131b170c01030e0a0506160c0609140f0102250c1e08070b030103031d150403061d0a03050a0f120509101a 60
    0x4031104200c10801000c06508007500c5020100c80c994000034070942c039004030544400180c040600c4d040c40003401507000c950107402401020000c00184004508198601c51b80c403a1704080e00340f0481d00b1054807812960010b40a8292030b02514000d0031000909d50240403090340c05101d45804141070584a400c82c00008106a2280002c64200082c2001c6c00603000142e280c1030544c05019110003003640c0743c80105440d051040004400000c100f03000c6518490315030802503240c07816080c1c140b1030f0401d4540840341b1000780125050104011610050b0091948460440e1000c2072000d01450310566031060a140b84140c040005000b01c444007a04c0c1242e800d620340140c00402c03081d02c9030030b002500210310f6000d903000c0d441e6095100e4040140001c0e40c001c2d44000780c24403401102400d00015003480030010342c00b42192800090303100c0200c44d410070103880c26040801080744261040800800c548040a0030034040010000340080c05210003070f140d14040c445c0ba03c6100182540c0e000504040b60 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 695858453 1250 695857203 695857219
    0xd0e01110a17070e0a0303030b032803030e01020714060708060423070e030d030b010305061c02120c0a030f1b0e01090e030c030f13060f020606010f020f0d1206090902 73
    0x84105240000720391041d09030400104c21089580010381500c140d8104030082a07941110081130b06003009603000c404001c10721442501e024041c041a840e240101c02410591590044d11861101390151a1981e0340000e24520042d000101d0350b842d1001107500c400083d50340360001c0c1d00c0e441c0070300604007042402540640c440307030003900d411200320008040c1018064000c00216031a05e0401c040b40d00c0d0b000d00c0e0f4000a80c802e5070000141a5030019100d1482580c42400015445501301405402d043c1e04540d0142d2040241c1c0f002801d002003040712691102c500b80e4000140400d0317000959440707118441d000c0c2c44070014820700344100450300800b103400c0000c1c401805242404e41c07008121010010440b401d251210140501e140e21541904903016400304203444401e0000c40c000001d02a503060050034801c01950007551034000401440c100b0100c01c0f44a90380f1070081c8616044200444240c0c2d10f904400680a000205c903400c0c9154890b2800c1000911040039101c0c0003088c80d07008001d88 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 695859703 1250 695858453 695858477
    0x1517010501110a120203190513140d240b040528020c030d0b010f02060f0406050a060302060a0f0816021009080f16020f090601121e020d0e01110a 64
    0x1604502140391001c024443c520340c41020882ca0401101c0c81240e80d4015640c0d00c9540c400c40202009011450080c402c05100c07500303000b654004050251020150300e0f00000391600000f8034088a10308018159482c810007602d41a06030100b20501410300724002d102c0a45e0490a1000f2168125807607030078403e001c2c21581c101051400c0106070303107140040140c1000a2041c42d1821a0300103d80702c07000c190384100340c0350a9608112044802466400500300918042d446080d40c09001880140403d60381c00c00103511801592113071010319006030140ea102e1480d104003500e0b40b05805482c40100d01e6000002d0504a10304400c1111601190301030010101ca80c1080c03006012103040c116840c0c80148036214403400100d000d000c25052000105c1d0342c4800034014000d01e00300c1c1c0e140d010b004409000402c00b480e60000d8040b0341c040448400007a4a41d10b00500c0d11101046040c1c0480b0319000251540199080341c200b080c420b11300c0780007082800b00342030740c13007459214081d01c00d40400c0f5400560 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 695860953 1250 695859703 695859707
    0x6020607260402040f1514010801081506030118052b050a05130e070507140613080d0603230f01050106021f0e07030803160206090309060d060f030b011517010501 71
    0x30716085440540302107000d50214101c40c0a07200180301201040c62a10703010400401124410408078100303007440d21641d41808221394980345582c098100d0b10a0039004102291000d6110f00c20136815001c3c1250040722618003581c40d6046040110549007500c6800380c1c0c0d40e82e03a00c01c0e00c0450891501e44c00d15041403203000382c0d620341029605100c3c1e254083c50024160b04003640380307031013008282e039074030b90798000b614100360002c8000307071200130300e91110b800c0100c0884141076426000b5000380050b900c80c0c00c0721403110080c24164200400258074040f410846001c1c1d62004e15100391400141d5400014101d00e9500300c420900c03440c801640300707041c85494210011210300e44900e03203100102e0103c0e4614281481c20318254005c580100b0f00100708210709211800490b480500d52026101318244110055600e014040501d8450540007803044400822130b80b24400030180c2154046403d0f0b0740b4280404004400d105d21403850b02000d403d5115030388075440030088512008a400070302c0c2d0800c001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 695862203 1250 695860953 695861027
    0x111f02013602060409020705010e06090f070b030c0d1a03010b0f0609191a0a090501020a0b01030b2806080d090b0d18021e0a08030a090905071e0302030106020607 71
    0x7060360003000820001c540307500180001c003212401800081424280d03d820180f51000c01400c0f00402e81008150700350015000c924902143c0030b020041d0380301e480d081045d04081c030440130284002403400050f044030400b06416418000c800f05d00030000f800940e42131042c0b0b60a41082207a00650810050803e07103000034101c00705485403660040c0190712400b9407140c180144a003140714007070101d0006e10300341e80000b402014003420b101610240465940340050017030180001854000500d000a18001426024440c00c0504d0351151503d80308040000000b0401c9000702030f2a8020030f0030110840e4090f100800031100c04002091401880386070000c01040b803848083d0100e40c1c1000880c015a41c0c001065207004081d460400340c51507003208021800d20070380d1003203040350028000f1280ea550419045d00480b172203c000801c065880c00c80842d16205c5c40480c03450344c141000b04004405500d43c0c003550590346907400300c5150340c80d044405da0307180121284411781d6498130a01040c030302c0301750a1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 695863309 1106 695862203 695862311
    0x18060c0d0506060a08040609050c0a06080a0c0f08071b02060d02090405180d0509030f0d09080708060c0a03020c2d011404080412111f0201 61
    0x10005d030007400d00074000380803030f9075561215040c02001d01008607114002451035807002e49685014110341740581d100500c3c00e25014134021110702030301120840100075215003030036640c2d01c84100c40d0316040c0c1c81005d08102e406d00440b40141c4400010341102c1c20456005603c0f0305103101404119072000301065861502500da08078604804101156860440d1405554414080e030101e45400800e800c81080d1344034100c4005003956101d911002540c801c0e10030340d41e2243c0d94241140d920403058400360094501048141e009a00030350081c6400340000b026541c001210306540c0c0034078044800312450801c403000820010000c00e2095807100400220002c409003480e41340d00c01c4034002c50188010180312052042e0074484e11904081d6101e0000b008080161400010308219220a0f20300030099820410710400c00d07000740300e040e40700b84015640c41c2d0003904141184244640c11075 = true := by decide +kernel

theorem cover : BRFrame.Cov 695683453 695863309 := by
  have h0 := BRFrame.cov_init 695683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 695683453 ≤ n) (h2 : n < 695863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
