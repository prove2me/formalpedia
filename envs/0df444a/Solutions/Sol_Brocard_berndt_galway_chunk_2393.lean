-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2393
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:35:13.154109+00:00
-- url     : https://prove2.me/submissions/6f20d0de-053d-42d5-bd59-71b8c9807a6d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 430215827 ≤ n < 430395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 430217077 1250 430215827 430215833
    0xc0f030304030b07020705061206090718141f03020a0f0507020312030c07210224010b0f31060804021f030209060c0c01091203050301050609040605121509030403 71
    0x390703022a40c0003215080d55842e00301050b0304101d15500410b030002d00000e82c0301c0d80c50700701800c1280a613000740c4060000e5900e1006c01c490710321040c8001d51458051100c100040400c4c2803446950003002040f0310b04191038010354640241d400c00796000171a8000c21504000303034000d01d45601c294045d09000f803400340194002910381101001490b207031100800800d01d10043d03130701a581e0a9902400780000c441e846000f01e51320f290806143d00061151498410b806146000e2482120a210a85e40126404c2c80c8107040d064006140c10f44ca10b030001d00c402c11510341120030400341028810600b20340038035520002c03501e40703245800c0603061003208811f1000680f18080c10703040c10010200300307a0740c000b44130208070082c1c402d82c11529071001010407015a51007003c00c100700170710001d03200c1c141680d0359010051310b4040300b04400741c045181800100324900304040107180348a001800054165140d40000780d0a03904030781100003944c1700094021101c80c0a05035160014a80d40c001d50510745165 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 430218327 1250 430217077 430217083
    0x1b0c0901121a0a0f02030a0b03120406140307020c270a020309030910020309040e060a050f0f070518210708010209210a1e1a0105010f05070201090b1305030c0f03 71
    0x2244500075000c5000980e160807641c130440c104004914290f6030b9003482c401c0301e070140c940e0848641c0711f409082d04943e08031441c3c404940440e40241c5400f21100b82c40c0034034541a8100a143d03000703501451416203041d81d14600380c101c5260030703102a00011807841820f11502c80d0001c0001d0b540301d104106108103240000300f07441800300300710340b10424910780840c120b040d40924006150482c1c10140480b52a50011825a10500030705001300420341d03c8400383c0000503001e0b01d04030404444400401d003414800c4008060540724204207c0401e04440d000c81c07840060130401c42d101d94072206005e48105018043c1400814a940007581061038540c001403445002184415000d40070101e00a24846c0034004541030035000410030074006281c000c0c0d84030b0720f074171a44115494500c59207003007030380910b08101d54107070741041c0d44548401c21000429141c0d81e02000303043e410712100210010740701c10054000c1c5011041c1c0f41c1c144016928010606160008004542c0e128000d07040c44644181c07000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 430219577 1250 430218327 430218353
    0x60503070308030a1805010c03061a030f040201080a29030c04050603070501030905120406020a0b0a06120303020703051c0f0e1b0402090112020d090b011401120e01021b0c090112 78
    0x41344001100d208102d00f91a00c0303e8140401131039542491000d4040c147c05070700510485240c102062107052a4010000f0a0300c02114910781800203080400c0265200307198681e40003980a00008006c004c80c984264108800e03501c0b03604001c4021004402c505080c84281e0711140269028803a80c20304c080081d071551410b01501c1d04240d03480000005004d010010101280040580150740b10b8507084000e441718001c020030b60b510650000480c0c0c480c0418030a1808490000c808484410000c0d0b40403006540310704e9040c1d003002414490011415001d00241c60740701090b840c0011907001c0e640c281d00580b4240781c840d8115402c1040e21031080341040114490201c01102d00581d100518070041c0c1c0e0001c094010280018030104164116100c0c030350044525500a60b107050840c0c3ea5000382031280014a03185c0b500241d10700700341c8001d410454000b03030103492800c0b00141c20503080080c0441e40700c40303d51003049554401d1000c0c56142c1050031072103014282600c40240c00610301e4803400104888 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 430220827 1250 430219577 430219591
    0x120313141e1c1211030f011a0c0d0e0604050909071701060e06271302030c100203071b0b0d05010f0b091005070804030c030818120c090606092206050307030803 70
    0x45007400002198680c0880803913103c000f1115242e0610441072000b60720b003402010035010a80456038964291041942d2004548900900c601907070407600f141c0340714498481942001d01400089042d0b0350b00f1000c5c0f4490000340004200707007842e20f00080c0200301c1c2000d40b00072592404c60240501d580c07030710400b64000d005807000c44210b400f0419105408644002c203e0040320f100050201d480660480010366900031411a89403000c1e0300104003092040c0080d49015a004014140c00929400d00040b941115400030106007039a4054800861340110402d0b800f003503540005000d00c50b641848800074082030740f01c4504154602d00403514503550002d81009102002c40e51700104404601110042e5501c001d540e03100c00da482c0b07800e40094100c40100e00380005a114009407a0520100546558003000c0081100a10700c0d014001220400b170f01c902e8211004010f004682c0d12071071103050350014641e50114804e0080d030303042c0007140c44c15001988070b41c20660040010800c280309894000c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 430222077 1250 430220827 430220837
    0x91501050f060f0d0203070c0615060813060f050108010903031a0d03080c040f060c120333080a0c060206151005090303070609030806030c040905120313141e1c 70
    0x1e683e400301466402008070300480b4900010400503c0703a0300c1401448158801c1606000c000100008403040380003134003030036001500203400180700c48010309503008003a005040002e80c041c102008442920000d801c2006240c0d118030741c8200301507251003807142c035030300b1006440301c40c41c1c1d207500291100f040000060b04000d200c1020998803045241220700a00a044100311200e03078451010f0708994000074290340c1707041310650b03010403d40203019407a01d0070313240041002803d410f182c103a0800b90142141e084404905040485c0d192010041c4400c1c0034051191952030500c0c0c00d0000303281240c01011a0025400f140e00c0a1079074031051045a401d52941c1401c0352100015804645140240c483c090300140c01c001d00f00c014190002441d50051000354241c8508a6400d0240070550b02140001415030307101801140f51001c041d8003560b005010f5072041d08000415460301c04400e01480c8000c0c00c4c503001030602d10741281401316060407074100000581f0602040f40001c2420102030804281444 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 430223327 1250 430222077 430222087
    0x11030405060307032c1608030313060f090602030a06090e120a2a0b04060b0d0206220f14090114100c020127050405011e03150605040504030305091501050f06 69
    0x605c02e148058095500c1358500782d2070744009507035a8941405c1c003c05003100070390001050045011007120b00c07915203035a80d03080c4202107648200c011b001c0300000d920344a1b41d604ca0300000480f207000460040d100400c01080e450300b00804541113916488400c01c1951101216841ca0f00540c81562a1140c0e42d0a0881187c01c114415605007000c0c403080a42c0c000714014003000b00300c41300c244070b40a070b401032038104030a01108083c080c000c0c20511002e58001011b0040c036404401c001d02403c04228443c649002e91503440202000801440d00200050300121407400c4c0c90b414640401070040c00c0f4100d43d40712a041400106103603004054491041240d000840070640e401743c00c00484a1200040031003107642d040ea00840843c04034002c41d881542001c00018400c600c3d003500c041c4942e1043c4250001500c0e650b2861559803280440f071040c15154400001d40d580c07948100c601c194080d8601003420b20740b4060b15410b1608500341826031a5407040140456101c4c00100004a0000d4890588d11 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 430224577 1250 430223327 430223351
    0x4090c090e0a080a0f11011107080706110a02031917040816080c0709140403020303160c05030f03040201020d0306030b06040c0c05010609090507090204030b06040504080904090c05011103040506030703 88
    0x40404000050310500c0000341d1655455400240c82d01c00403401d40e10f00c0d001800050b2110700303032390b10410780200d41c000c140000e4000c10701580041040e2071007000c0c009100b00c0c68420444c11b07600301348003000140c5c05c0410a4a02100c1d41da0340b00c842000145001d4003841d0f0303645030904600c0c20141c806029a5008100404149140d00d070300154160071070301007500c0e074040d584030076070700d11203400f489000c40c1c2443d14525500514a41d114001c6606801560071a81c030010703802401c24540c8288401c0100c20685280401c0342400107040c0540707440c5101d6078070314050001a00d403145540c10b140405280c46e0040000c82c0040e0f04a40d0094800c0300c02245490380c403031049614580d640340c0644103504c2c0c0b0600007840056940200b03841d912800c141c0c1c407866521254007007280281d200180901c1c51110008100c2e01d003a034044e0f80d00503c81c00c00581000b0403800407408507500801c0840e4a600e1a900c10311696070448281d041c0110310400440c40c09040c6030210b41e41d0b01014144000741500c40300f2207101c1d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 430225827 1250 430224577 430224583
    0x20f09031203090f0715030c18060824180a090818030712200105070609050d080903040b09060a0c021207050103050f062215060305010f0504090c090e 66
    0x24000009007295020395860300e4201590344140c070200d105128444a01c0f2902201081103800c50f00400c0150000c401c5105054016020341d00c2c444007041084003031341e815a0420fa801c80041d00d66580e0fa0760a1386040c51010404004603c0b8468003640240300942c00356446084040100801d00075400e13850302c030200d011028140400c00140144030100382c41008a10f042013514003242c0c110116805140d03940c580c06102c14812074090041c0d68011180b000100c0c81e06101c28044006142071860442c1e240c48070000c582011204a83d9a0414207141e030f28a5400100e440e0000c1001025510b0305d0b192198129091044200d920f00038003021450f031000c3e83c0103203105c041c00394026200188110030060120f44800035402050b010a1a25001c21125000390030a903201d00000380c00c190b84008400c190503035070381400e070380b0b042229182c4186464200b5218010002000580c401080c554146495040e0194580e0040c60055207046600404a40310301c03841001c46110074400a00018a580d915007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 430227077 1250 430225827 430225837
    0x30e0c0d050c060c1621140a080d14010f0803071104110a0507060f06050906010c02040f0e010608060903071e0c050306010303091d010501020706180f080c1003020a0203030a020f 78
    0x162100001c00c41035000a0080740e60f542283c0d1a00c5c940384c1c00ca895101002c00032040c1152000c0c41d5641840400024a00c1c00c00b0141c1c3c1307820201180c200f401c160303443c1d1007030307500c010720004d03605403540c4590032000003082d070003409004006000d9448504040f595541d80c020410003409514010780360b4101901c0359400348500c11b0606c000b15544a49909025011703a001a50440381d280c80d08481c91006c040742d100754404da0b0782c020414402c3d615044c0045450340c0c07640c030b41aa0700c02e81c0d42d403115075a400c0034800e03100c081c00c41d0400456124500700700070b03080541c000c2010750190000c010590000c0c0706200c43c4044040d88485265198000d420100700c01d90381500582c1d014422a4008401d146c0c1044013801210400c0c0b070110090791004807054621442032240070302582c003800301401418060a0700e40c4120001d041542140343d0b0300c9038080500030f911340c000c1401c0c1d00040148415804e15080042d00b802e1a41002d510f802c0c42c81030001d42c1d82c8002007400c400c0c5075020034801002c10542e8101c0e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 430228327 1250 430227077 430227079
    0x6170a020f1e090a1b02030a051206061c0b010207080c032503150b0a0902070302070b03060105070f080903190f02060702040e03030f06011101060b030408090d02090c0903010b01030e0c0d050c 84
    0xf03651490080986001000c0075031100d0303901c07000703c519072201030f100000300d40100215645044c1400d8500d9a50310300b03242c0251040c1c0d84244140301300c824450f00540003804001d84010003044010103a8000381c01c001c1e054001d03501d1600800360461407601c0000b000300b02c0b02402c900b0340000d0902c00d4a10845590560401001040d210038138043e143c8054020000c001d10403181d451b6a02d0b65101684202d00c01c001008000d6000070310100401c02012016641c42070f010b0512625042c00e0766030f1009107051502c4120307400e15000c00ea1402ca8141086a0029481c0c01260509031030510345644c0b40c000391104000303208940001c0e08600315100d5421441000209004498482c101740341003c40e40d41007120194001440c04400a07680d201c140640c40c12522259941c91030f48c1c5070f9440304406a4007200c4c126400100c0302d00180011303207030140001d12070040d58001030784584a640070542074600d0301451604040c20700325800380c030034404100d5490b00728080300d140004030a280b4100341000814490b01d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 430229577 1250 430228327 430228339
    0x405090f07090e0a0c09060f0c200d0b04060b0904020d0b0a181118390f1b06070f0309050a0c061107090510150513060306170a020f1e 59
    0x4031003001c00f25040001003403015186c1d101a40c0d00c2e9501107421104110715200024440c0107030328003140d4550105140c07107000d2416030030440c0e8400045035440080d001d044554031003800c1048184482481191041036089500101c5401c05400140e00300e4034440002e0926460031012880d1407540740e125040c1d840d00c00c1e60b00088540e440c24016041d800b1502024000ca03411400382c0b0800c0900c100003440380400c406900b92a90858002102c50032100d0740712040100c1d4002d802c080030fa100e201420445120060380d56441404440034000aa80c1d001e820f01554014020300c41c1494202000e0401407480d440d000400840f141459850046040405800c40c40c40a20200d4026848010241c03003e045104a038110f5079038041d80c408640b011921500a81440102449070950501b802e100c0da141d14500641000d8600e162103502083d26072105000c030781e840c1420406512882e640c0c40c0040e03041c0340070b4510b450568001c1141030b442104d480d80715582c40540c111070400278075000c0001590140803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 430230827 1250 430229577 430229581
    0x30f03070516290c0d0e07090e0303070f0309021e040b090a0f0b0109030f020607150606020a330b040207051b011704080412061107031d060405090f07090e 68
    0x180183c0358184203030085000322011202c07440b5285011240a6116016041e250900f0710303040000605034031404010318011101c0008111070140502040c000540380607583d0380c100300d00060b00d9801541e02030000d050800080744090781d200220020300382036041c108904131080500007030050400302042030340000c2d0b00382842100c0c0142d9220f10904000520304100e10415440190740d5400c0c144001080d04554000c00001800c07c036000d065514030420b0ba0f40200b1140880c050706407040d81c1c02203070059011010840600c040c1407090307440030814881d85551054040070043c40301901c3d011100300c01d034a5400201c41c1d52502e40c1103403c40307908601503642e4032030310078804440da84244030f8181c002500c40411450383c88004e00c0641c015640b01131018038091404494921420305404140c0e91203544040b18180000e84000606d0482d1107130751440381410040c00c00303a241001003036034680a4442804148a01d4880c1d020403038000d503100c001e040080c2e0300d10500f00c0f04100d094002c3d00c140456501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 430232077 1250 430230827 430230833
    0x90604050d0813120c050d0504030203100b0f0901030b1f080303070e120a030c140105070c060b010504050d031e080c040314190c080f060606030412111c140408030f03070516 76
    0xc0c480d031718501c100152502482c041d40100c4050045010180d4141c11408450115041a034403200791540064810303034a1071003010005900c4002603000780c901261844c104400c0210800d141c00c1e8503002c2d40030500005040070aa580d4a0100500e03403810710250540e0364030a603951203a01d418002100080f0395030340301240380003400c1d0507500008694078140703040e602e00c81000600840d481000141c1d58003121000d40c1d16854040c040c5401441c0c14413004001c0403445490b0104401d100074000d89904100c80300d291322048034254900303900c0040168920501100800410480b41240d42019080907c00100d01c81282401c1c00c60310741c0c6604803a202c88070010444001440d80440e40100e0a40d401d00072204030741c54554504682d01c0754000390130400180018446254132804103090f280070340a14050b2621603142043d150310042510316000c8400030700650041a0140c00c055100c1d1060616242c01d4038541da0340110081500e03004000320000300c0141c0315400b6035081132200c2511314100c0e00c0c83e00f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 430233327 1250 430232077 430232087
    0x212100e030405130c0f0c080708070f02010e1002120703031e1508010203040c030206030a0b0d060e010605031501090c11071e050306040b0c0a050d1109010305090604050d081312 78
    0xc8219401501c03131005000303030300c0d020303106845450300c0a0710342c1505049080021102460181022501c0d80d4040c42600040b0b100b640280c20340512800710041004454000501070001d0704030460700c00d4401000700c6a00ca40e010442c0000d440081300e010345c44500c01d15080c0c0c0a4452003007494058200000c1218105c4195085003400c4d1340d01c1c0b1402c5d00b8040d2195805800d0b8407040301c026101c100180c0081006040c81001140d02602c0c0344c800040d0001010000354100840d0310007071307903213a41f195042d0380c52000a2048800901044008103010f1820600354100341c101481008034580d681ca045a01d00384c010302c400303400741c140d280c25103130100d8491804ea5181140e54101d1070190402c88404038807400d000500e07500a80c0c02403801815a601d084078141c141d4410300c541401c001041c4001140500903024003507422030380320340c000d0300d48541c0310005040b00e50051907062603a2100041c400400d001244806040d5801c0c0786c000d096544405440401d054001c2d00140344448142030410320310344c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 430234577 1250 430233327 430233329
    0x309060403200309060a1202160c0b0c06011e030c1205060109020406051c0e0304090f050f040b0c071115031b030105031e120c1c0314040212100e0304 66
    0x98641044100512100c00700d1018610b590050a6008100781c0d000e03481c14402601c0501c0c12403826201381d20150f90b40c13000ba6089a602c04440182210050082211403d100d0307001d8110854401e080240d1601c000e981c0c2c600c18841d0419030018240c0c8242040c02100c40000907542251121242e50356131000e8440e0840303030042c10f0711140a41c1001103901c0946008030348c1200c0e141e039113403400c1c030b982110602039400307152068022496403007101000c80710b0180068402083c3c51000001c0d400c00c1410440c1c2038546c010241074198032145e08000c002141c0703001441e04561204006a03c0c1c070410716003c4100300804510b070742d1010074a079152410390071040065116101c1881200040115078000407420700080c010154550040e66040304000900d00d0050600500d90085803008415100b0201d09a806650300500c1a0003103141c00442e034502040c58042c8170302d545010010b040c0c07018140c000d410310160009225200400413201c818a04005010f9900c10200f000c10501110a0030380b546d96001e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 430235827 1250 430234577 430234583
    0xf09060c0f0703110303070b060105130f06020d030b0901030c0e0c04030206041202010e030d0f261e090601030305030a0504032006060f1807030c11030406020c1509030c060d090803090604 82
    0x2c840c0395040c00f07003000701c207841c0c40c03550043c141c80e09030325020019103054001b07412415041c02000030001d0f00c500c5074de1603040102040e402404490010344d00c002c040d9404000b0f8540280e180c07200410026400b5944501100c80c41d480c4402d9175102d02a40380f0030b900c1a603001030b501520104001c1348140b00d6142e543c0c4858800d80751840c0c015500300515032945601c10780140801c4103594451013841c00303480c100407100748200f06031024003041c805a12007560286c40002c2e14940c4d110105142040300d144503038102e9540c0c40100800c2d0315681d002461361100404060740d80d070300c4001141c101409400c020a00001c2c03840134078409103c0042c030740d81d5150b04a645920941070b0402821080c00d01c070580fa15130020120003c03c0940e03a040041c3e0190a40118902c104809035400911183e0b0500240010b00415805003000700d01160803c041404900c0c106200701c80200041880c503900040e4859030303040c095031503586a4880310300402c004d00041d0800b0f04159000401c1041d0040d0105520f841548 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 430237077 1250 430235827 430235843
    0x5010e0c18040b01151808070807080f070b07030903050a06050609010518220b100305010506060306031b0102190b0a06080303040f0b1504021c200f09060c0f0703 71
    0x5908a000c040184141c2d40030700403407030400060003d501c0070039260788185000d05116507080081da00405010a155001c16100d0f0420203080c0500f15091061400600c40400100616106103090b01c0c0c45000912070035010b041d0000f12241054001c4e02050020358001c4d040c1c1b030b805000303030030b082d8040c04040359111300c1014008000300f01e5241060003141c25240c040c0c030384011665030030b409040c1e0580401d269035846410400400000e00441601d9216002400c0303603c907980d03d181791150175510090012403085030280704105840d100003542e003410b0705c0006034409207003000c800141d042268202c1c91064114000304901c0034001032030400c85c000c009041e420000a40c0c0c400080d912400f042c1c5d00101196000d4603210301045819401a81041140502a0358006d01000040881e448401d40b40d2030b02012541c21582607002d481203849140380c0b174000b19543e1610004146141c840c17030b51035030b035100780201c1e1020043d11200706441c00040c94030201c9121b80d46114000380c8d80c04451000f212111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 430238327 1250 430237077 430237099
    0xa0201110301120b090a060e15070906050909100b030702071703030105011e0909090b15090415020c01020c0a083105010318051c1403150411040305010e0c 68
    0x40c15050840e03048550a000c07038180c2d40d1883d5114000100d01420704a554416504d44501042091103a40700c104840d10091841d00d000180e0713503600800081000c000d00480400030000d541d0001c04880b149042140c08200503640c4281d1401d000855030011044100d02104100a454001907000c00b912044022454191610f80c2596668402405514001603003108102c61800134910781070701c1c3c1021405c1c140300898441d040380e000c403005042e040c1c07640100e41081c811b554010000700d41c00b4038002d80d40042e0038078064465641d414160002000d9095002070310324a451800c0d812395901c000c1840a4448000e082d0030310100a800442d8064940e281c000d102d00c641d000718500e21602c00d00300c00c034172f1410145003800641c01028030709111400c0040c0301d0a43c8001840030b00030324841c0c900510ba802d5240c0c4040b0720080241d40c500480144554042090100403405021005866001124080365145842c04420414052640010255030a00c40c12854020001c50784001007a401c2d01d074030040c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 430239577 1250 430238327 430238351
    0x10b0d02120f090f06011a091210090b0604231302030a0602070501050601020a050a020f061209010f11070b010302150708070506150d02100807050408032b090210050901031d01020a0201 81
    0x3d000d0038440c402c69080511f80c8524141c0220b406004c015030024040f82120003000c42c1981852100b074894590169074184041c108003801d801c00360005c44c10343c6e08101188419080540708100c500803101052408400950b01ea0102e4100401703295024003075540d000001c0c40c03ca0040c1d04001c600721065424800098446e500c00a42100707925000401800b0b980303455020b104800701d04500300c5030030503010400c5032410403640300c103107000305041000000d1421900c2202421a804030b00d0320121401c007009800b000c2425031341024152030b011144800c1e51941080c89141a104064005140c100c000c03990340c1c14030201003901489110b44010300b200c140809002c100c06513541d6030000394442c01c8441410b50302841880e1903644001c090401da40380584609e250761858010b222141c0140e009501702c45609980e100360580400c9901500b07008094141c4c1c0081d10b00b051008240c402c118000c00ca890740c0c0c0e03119401444c030031b2400008a1081e4082c0c1c00959010754005400c9001541c01d26000d8208 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 430240827 1250 430239577 430239583
    0x3071d0a0506100c050705040216020102070905060d0605130b0709030303140c0d0c2c0102071d010324020316111b010e0a180204050a0b12010b0d02120f090f 69
    0x400c0b500204940d01074100e00006440e43d8100000c02e48844c41900000706040c2c8951000300311481050040c1e0524130f1440c40024600000d40e002500401d04210034040c1d151100214900310365804000031032a50b4542e030100780c18140500c0081d103c074240c02c0c03c4c456120342090340502581c0c00b80d50309211b40850591230075040354003907031110751065080207601031408050380310704403e10080c074180c0600500121548005203250011025035806070718210304640c0c04005000042180694041d8030404030340072180605014400600300320441c12040d04644141030002c0781e04040842c0031922801c0c140250940f41c2d000c14600d8011035401030170704030190400200c000408960301c207014114019940115001084500c0998104d1070b003640120340b40c02290707802c0c4511802c0c44070050f100d038502410800c100140b9030040510a40400c174684d13072408903400c1c2c181510355507803c465444621800803002803042d450b544031000500381c140101c40300c1c82c03907034980603010400071034070f08510414510761 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 430242077 1250 430240827 430240831
    0x6010e0f1507022d10020a1506150903020a171e100b0303121f050306011403070f0f060315031407050112180b2a070210050f2703071d0a05 61
    0x2000182404d1002e00b1032810351881d1108004d503105546484801e940c0300ca1a40e140c0d4001c40300c1041c2c4440c01406100782815101502d02403902e01401c01d80d1640d00810025450350003906c0ea9420a00745403121035008200401d0400490000520310031600a4416165030740a014080b241c0d041010200d07141c60000103070313015003c0c00c1508140340d4417051514520000c0841c81c3c034101c00701194002070555001e009660003030041c0d0268409102507001010b0603c10560480507101c2e210080500c400001e40c030020b401da8815040c005002d00d00102008441c0e00c0c281d1005081c1e42126001c40340141c00451082c0c204c40f82a01c4102200024102043c1903032501140c05000c0042d45403a940403c0411000942000400d10b0026a042ca12840303020480b00850605404440002d03080085040c400070070541c05100785440340c00d120a50110300c130340e44219694100e0110f8028400c80c04810580399101510900402303e408290352400b0b40080340203203000b542d402c5590940002c00c80c034094040d0398 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 430243327 1250 430242077 430242139
    0x50408070b030402090a200f0c01051f0611010b0a06050717250807020316031104062d0506130603060510080f101a09100207080606010e0f150702 64
    0x190171707655501070680040102e1210312011140010205d40e080c100d06004017180c07280104056a50300185e010b45080d60405040703420354850f0745c50800740482c0350f007103941c003502d01515041c41c407214110015030260a007007078407030b43c81002d42c1000180b843d0000300400b42103114030f50424a0040f602d000c800e040c040c3d001d00e8200c00555510050b1800641d80352840014403031101c0c07506010541d0082480e050b00b03800300c800c142c09148024414080480a0011441c070101e6007070100a0030036080800c40039006e1155072150790103d50281c4000c0c56000c141c0007408018102035121260307001c05c0783c2045031500c105c101003403903c1400700c2d5504080d15881d0034035616448a00c01522050548000d0710300060080e11050042d20002c1494100d201d08152022506800f0b6a1540da00d0020041942100107101c0d0a650091f2010840200045a80c50b8088001d081001d240300054001c01c0310305942110381399200b0300c00620341142d010440094031090b07009850781e0320103070620f03408918003a0948140c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 430244577 1250 430243327 430243339
    0x1305062a1f0c180b040e010e06010c0201030903020f01050403120b0d0c030305130305030a051209030a020a080c150108100606050a05160c03060f05070f02010c0c0f0503090a06050408070b030402 85
    0x110326034480c0303a002514889100e16103003101011200300e20050f841d503500400200c0d03400060820085075009006405402080c0d00a030032400c2110003e0120328000e0002810325483e410f4440a140c000c0c041c031035644035040300030b0050303144c02e03e030081402031181c0170480018542007009583d410b02203594001d081d400b0f5080f0071160300f16201503e40390085100d2854001e9480b04c0031000039000d002528400000341c4503d500c035425483da4040200e401000c0610f42d500500805a0303903940003c18454260300840d02681c1c4107843c0136210f04000f070906010501d44810400050710f05000103400e030600c10300030740410a0645510007214a4825825800c0002c0e0b030030302c081078003003040340d0300c1288981c030a01501c00c4540d6607941d00c80649140561002c2242d43c0d6008000c01c1580007229141411042c0c4020032004801340c41c09403804081c1e40000e0900c1c4070940e168010050704104403842d1040040c000660b0340d684250040c00d07540a8007804046020301c5000086202182d4180ea008650082039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 430245827 1250 430244577 430244623
    0xa2d0207140402040b160501050c0c0606010305061201021b1c0f0f030609090b040c05040606020a0f29010303030c0302040b16111005090909070510051305062a 70
    0x20380c0c040141c05420302035102d5801c00c40041d445005c030009001030001ca1391402c070b83c8082030810350b08540e0020481c240c050020003008690348400b08106500c03400c00d0800040b140c5035100800d54a100665080e0040c4d0700c0042c51100060341d15008581110700c4030102d4100041501c101c3d49100c10384182a00030650301d494007840e46010f0100c1040700031f2540340000d0107540e9406488192220484256022a5035409220500201041c5400036080c1075138144002803070080002d548201c5190090283c0d000800c100d020440b44541514503050f004e10074480a10036809581c20400083c88200c0110340b8103002540c00d00e029000f60b404445260703403401c1c2003481840750807180400b9450205c8810040c0d00d00711110b681d885040b910048070036590503444d0180c035001d112220310060b14074201c41d44204820086a540c505000c61702441d6407800d50b81f03600f003075084401c2c05445500b07c154407002c045800f2000c11000740704900c580d0486400b030f480c0d0001000c0d0880c0c036203410100003107000e000075403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 430247077 1250 430245827 430245839
    0x5071104241202210c030703030305010603150509130f0803040b07020615180a021902010f0c0305011a0f0d0903030b0f1c0314040b130509010503070605041e0b0a2d0207 74
    0x5100c240041d82e440954030040d015200287c1052042d40080340403c1d070341d10040c8042c41d8544101492040301e02c540c5541c0d80d0400c0d0010701a0b0000400704072103070f0394041c4410204514182c1075041c0c00c1c1d0028ac0c142c0c50381000d16000c800900210344e50300041c400c1d0000107840000900305240da40394003520a90b00300081c680840036140008260720078031034003080041c0e0903500054508900f0000c2d50b000049140909418405488580564008050400c3c0041c80150400c801168426a508240554424146460101d90300580d000d0042c3d007884d120b031000034541c140d0001e07416800e088030b01c1c02d1205888820041c0c030300f07941c50000e1130303081c82c0d0007442000038090040d404010164002040c02c01d5a5201c054801da0700c40710302c0d02420107010f0010130280c244202d2a5002d401c0c114007074410141052801800c600030b0780b06150f0258403084800032920742c51000600038142003442e01e590307401c44143c0600b145602d021600604030030100c5034407450302950301c00440048240e024003009481d103a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 430248327 1250 430247077 430247119
    0x30c0709150b161109130b0a0c05030604020702180c070c0e010602030307030b01050405040e03071203021e090112060306020c0c06091302030615030108160b03060a030305071104241202 81
    0x807012101c1007a082c400450907038403ca0700512407156100f8030605041c0902d030112121f40c0142860304c0b558105881d4110254200c000e584c2c0c0079605880040e1111030a0002840b1140c800e495500400340320400d00c62103250160041c1001c074041e140281a2981e52480c03641124424868100160030610101e46468032035001041e0b43e210500d00f55003130945450000b070803503016442e000b0442d80009903240401100594030b080003006800c08605010b80c14903801c507031884020f01d400030a0b800058081c0c151303010704005400300c0200c00040201c1340e101e1500328025409503404c115188258105002c0c1ca180c070b002251007083c0050481d0140b036103c002624069000130300b0040e405106089117440310b210342409076008224020051038a403d10304889180c2008580100042d05010000c01c50240c69a1003880c04a0381e040c600607030740f814181000c01d4603500e041c400320750050030070840300400442d84c114004c0a04c0c81d07078060008603540f1f03840495041030352500250400c50000c03a000b01c0c04000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 430249577 1250 430248327 430248367
    0xe060604052206030501020d060305101a1908010518100b0303090d140a080a090608010602030403020d1b080318030105010321090b070807110d02092403030c0709150b 73
    0x22a0101d01252280d803686d0a90300300205030a445651080c08009100c0200131030400304040304410415182201d400c000303850510040d0034018522020350049207055040c412009001c004000c0010f410282908545000610b810200c0ea10600c3d0f200d4400c441d02e84584280c0384402001146071820341c1060100070740300f00005440b006141180c00000001c00d11a241c441440344080c260b565104440c0548010321a81000040150200041c40580d400100722821b40c0d0301111655a070b204185002d5078041407027000b01038400104100020306080003c003a0000304030012b4604019030840c41810700b00c510920010f0900590010303644014800780009103211200c0e0310380001503649515080c58140c1c00b01d103080b030f007031300000802d0741c00d000d240565800142000c4860680c0750b407064001030440f80015048281d030159207105030212040020f503503115010054243c0382ca40700f441542984841e01e501c00c43c01c4050610f4004110421032095035070940d90604803050400c009095110419111 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 430250827 1250 430249577 430249639
    0x12030e1210180f060902010908062e081e300708160309080c150306090727031403030108030415020304050d060b03010c1b0201110c04060803040e06060405 68
    0x400e6000c0c0021514540040503d940a48400f0032050450310006091003a19404910140c1100e8180301c045242c142158041c4144150a91500c1e91a40052400301c242036100b41c0300fa20402c5000d0130160424a68446030007052000d49611151032580d406500c80c915100b030003926038894152001e0b01d40c5002820100d030141103894100400300700c1a802c07a400c0c0200903000720f050325400b00a802c2d0704200083e00ea00096910580c1052440c082180b40c0c0406011103105d11100000104114400c801503034074046104d400000c2e24080c00c1d26840750902038082a10340d0f01296071005001e0200008a034100c45030f110045251525258031866a1120100803404501040000081541d281e008203000140a1000020041070032010507003110100381c2130900b80203100b25001d01483c0c40d14100450950282090080c041215101c18240000180c1f102d45c49442c081c80882e585400001800c180c4451100d521041d8a03000d007000701c9401356102d5564000c035023a036043e00c01018a21a10301000c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 430252077 1250 430250827 430250861
    0x191e0f05030c0d0203070908070803090d0620040b0a0e30010e060a0c0e22090201030e0a0b010f060801120809040e0a0302100606092102061312030e1210 67
    0x401440d143d000d0340e0060b01c2d1900004d2405405211000c4180003003801800844d00461902040d6000300d010804950000790025940d56030164990003d060390100e0100c100f014256569254103610005800681403000000c00c1c2d80655409400e00a200d07a5004070200700b07031200e4059110240b40044040c1840700d1055480303502503901e00d80100f2107540a004494400f085e01c00d604400103014801c0b9040c19442143c640744543c2c50f00403d850b816038001d03c0500c010030b0700120350005070090920225540c009100e165090300c14096065500b6040c1d441070040199040e90b142c0040b0ba05030400e00820328242e00c0d03c48a6030026003c1070003407440540181c8007185803e01c071090a4180050103600b034016030040c0b600141502518411800075210ba800d010881030304180c7c1d801c28103c907a400c0b5504209141d10048107541d10b41c02560b00c620400c3c180070090503142e0440c40009242d99504802150310640f6140480c03600030b0000648030350640041c001c40b4021000407001d05103d1400043c002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 430253327 1250 430252077 430252087
    0x10c0f140c0a08070c331b030f0504212603130606031202010609050c07050703120e0a0314011416180902040b1b030705060a0b04020906191e0f05030c 66
    0x5215050042010b1041046c1d2096142c1c0ca10070b114004800c84281508000304034041c402000040761041032201c0c2c042c644862980c2c44030409489512a42d08018020000103146009030713541c0c00c15600046201c0c1d0303164540e04e2440c010314080340f10140944443d0003002e000050004016441c0d0940e064000d40c000704903c2d50300c1e200d81071b202d001c0d8861003005035140c80d004c1c844410b040c019603410030001c0c0c81c0c040c0b41c29201c2c0c480a44416407030100400c0750401000b4590755a10a0010309a14800180070b804000d0340c9291004141c074400c0c403800c0480d4200f100203510898845005440b40c0d030004001c88241070148011241040e0180ea4816000001100803503d0710051001d04003801d40400159034504020f414125600d0542e40780d10007944c802c1103184c0000d4400300b103e0f600705459400c08651502c0100006019004482040c2c0e0040f8020941124070300c04a030042c41890400c0e141c2d060704a104054100070b44400204030320100321118480560648070304c0003103600142e1845011300300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 430254577 1250 430253327 430253339
    0x150a110417011a100c0209040614010f03030909020403110f0111010509030705060124050c01270204050a060e061507080406030905070b0310060302070f05010c0f140c0a08070c 77
    0xc00c003180d0304806103030341d03d580049004955410940381400308031070001007900b022400801c02c8410348002030080c81000c012904014207038001681e484595000c08102c1d44c0c545d24842c440c4001d9210507000220482400907400916200712410f0300d0700900c41c0084040000288003d82c100b40a00034100000386040000000c1c00303205a5014180710b101a5a440c812401d22030300c1c1c4001070304000c013500000c0c440b503100300c038007010f401c807940041d803c04507150b1501120141c0104068062010706540110f5080e40d2024491001841207100301d4080210744c40c0c2c0980e480c21912a401501c48194929001c1941403410380d0100740d1640f144108649042d00c6680c03034220740d0b00f05900440209403a010740404011003032042d038018092000301c8509528088280e02074100707061040d02d080c90350002d08481030055400d0940503158212009005952248000902904801030044000f03140141c00744c200010117001c44010381c0d030080040c8215201610703800c400e0b500184049440340d180590000352 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 430255827 1250 430254577 430254599
    0x503061e010e0a0f091a0f0d14060112140c0f04020f0d0f050105010f050c0a1b0e090f0f0c06040312112b0309050a1506180e0c03150a1104 61
    0x904504040191300c81e00c2c10144105840b44940c4140c00164031aa115109071550301080d90302020486e20b1500c1180c40703080034108005006004200d030300640001140101d402021842c00520884240c00c42116501c040d0307803070f9071410590940c0001c560303ca0380d90354039042e0050a4040c04840c1030a14000003803241201702c84480300100e565548810040000f980c100d07034601080142410708030318041000001e21748070040074000510b1040441c0c0e9107110111510204006030483d94548450f03410652400780e41c0345100010804d15204042c42c0643d403400100e402001d200300a8207a5042c1130540c1c1d0383d2030200321a1045a81044004082c00300702e06020802c110108040500d4500f400e4240c10918851000c040080c02c145400e010748036000480001e160b40c6000d400a50b00b40390f02c11100100b1000c4c082581c041d100c0c80606003a680e82000d4940d100300315800c0a0b50403200080c42c60400d05446d032031500c3e160000005003900244411105400c9800358200e940d0110349011f480704c0031691 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 430257077 1250 430255827 430255829
    0x2060f0907121511030708280207030201140c1c241526041e050d020f0705120c01050a140403061413020a0605090a090e0606100503061e010e0a 63
    0x6040300107180c80f08241e40142c030958035501c400c041083d03e035281c50703030b40504456000f81084171400c0300c540c2d0341613080d44844000d03200205141d505664a00c040c2c10000d010704402c40009168407482030124444004407001c0b01c09094402440b0080c0c890034081103001017804841250380b5581c0124540d91691960351120050040540d012a4408280d0700080810060140c00c808a07610a422141c8a480c04540030340e0059204d46070310408290f4240f02c80040400040041c2203116800554901603004511100318040100481d4102943e400400511440c0c90540b0700706504802855811544134000078a041000c90402c80d0001e040d01c14210040e502950094070440c0e91040200329045540c2c2005401010350b460550303030101160000b1b0020351146c891442403001c0099481c116840e07225400c0010a844602081048403c50000d87c40f81821503403684074609240c0d10441144c02401620701580002c1c0500034249401c0301d031146e0104608101e40d060240d151000c118607074817002000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 430258327 1250 430257077 430257083
    0xc030210050403050f06240f19090e0102090d230604061e020c0706180b03040b04060c02030403112101020c01060f080106060813060b060c01090b060a0602060f090712 73
    0x15030b19451420300c2428100002020070058020a0030300140e0f01c0c06c3d0420f0b183c4e02014440d241d5040c1400c42c001080c214280346541d40109a101d0026480102d4050000850fa241e800503c1817100103a0414201d01c203580b1500d602c4011080214082801001106d41f480103007403401c0d815200080d4140c0c640b000449080f2201e64582525840003011203800e10010ba104a03419818800040300302c5403205030380d010345820003500c02d003020507410400c807282005008042c181d039602d0030030742480f003040c0c50111030a40d5107500b00001484400c0c4000221000c0fa500901c11219407005401040302c034183c0800100031994054842c1c02c0640030038802001d03480c90ac60000507001e881c0c18a1303001051807542c020f12030303039150900400c03005410082c1c850780b041441b24006449801841d0120080210840450300410040303450390020f20305500c410942c82c0176400c5600103a60300810054921510300501e030042c1c0040c40442c258911800c2031070b800000010948203a161074419112103070803485425 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 430259577 1250 430258327 430258337
    0x61202061c1409030a020d08040b1504110703270f1205013e031e0c070c030503070b010b030411011101060e0c0706060801060f1a0706050705030a0e010905190c030210 73
    0x2180c21a40402904155601f9402c0204048c90643c0301c031107070300e10000c0c14800b41d4040d0f01c0e0111840d039101e078080f003400c000240c040c503120002818002c21300b019a001243d0445000441140340964081020003240e804914180e4614200519081c03204444070049030159240c5005154481005540d061400e15040c103a50541d1070583d803481040e550ba00011404140800c00d00848040c2034083c42c0b00312105a881400588428410005d248100b003409402d0030380180c1d020040090201c010005180168414146641c94141107000b6100c19a0300070028040690204ca01e54011321200c650080102c0000030859940d000345c030b00c40b01084070040c2d4040310004805082150707510400b0064500c0f240208a818104800c14071a00014000d0454079400407100c240c42d80903080071544080c0d13003c0d0040c0154188010050070580007550b511101a0810b00d0302c0540700414451205080d030040010050058000e060032600c0140c4a410b40d20440c031300c4c0000c005600c6089160812111580d80c07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 430260827 1250 430259577 430259587
    0x2120115241718030c0a030e210304060309110a0905070210020408070302010e0310020c0715020604020915180c03040605160203030c1c05090f01061202061c140903 72
    0x8000c03003144100c008041402010101c0451001082d040240e0001a41c0e0340c4410380320142d9245451070041510091071841140848801c15038080304242856205803030345041403602d06a0004850180416040650b0080c0b0041244500c240c0081c8071080c09644182c3c0070240c4040480e11170446038104a00c8036482e4014030842c10350405c00e840580520b83d00440c2000d0600070180c2d100e034a07074800641001204443d0300102d9070288a40741c81382d00c424600b151381c1d0f2501078005444518921980545c02202c0501010190000c00d02622981d80206441e0b50350303980c000c0341506031543e00a40d54002c001d42c03a210024180d0102c0d000c0c0510341c0085681c0d100d14245c40d050081e62402040c2006982600129007280c58002095070b4001c220748880c0c0380c0300e802e02c07000c0300400e20360407107400311503800d040c28490805404503208640b43e650320024007a90751250221000c50000140094205000700600c0240c181c043d001101280c1e8015404601125114042007010b54191080b01e429000054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 430262077 1250 430260827 430260869
    0x618240c1b051905180a14100620061902130306202a031315030c090f0b1c020a180509070e06070f12020d0216050d02120115 55
    0x401c9051102d6865140010138105008580c107080030700350440180c0c070460082040c0c03000a40000782003040070000101c841c5810614180504d05070310400e80400c100301812005103244a04007200300c1a040e0040c00d00707459038008402140320620207021125800d1010f81d075412503100000700103500601000c11040355a480c0300f81070b86410107503051031840400102d001030344000c078010b00c0303140b04901c02803c0700e417209200c80c114422900803580d0380541c4900890404654510381100251a0354104900c4420039026583c80840740030710f165a0700c45010822518000c44020001c5d0039107010084456203207550300d0000e98104c10701c1d460203da0000704002c1200706184081c1c005140c21500541d40b41002e4030080c3c1107001095565010b0fa400003402c0041c00154407104808540c04110b108240141d800300075107860703412410350f0050040a40c00803865841c40c05880503620010f0070468505801d60802182c80200982c880555485440b2241c0305c0e03407491026002885a182d83c000340c2c0205403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 430263327 1250 430262077 430262089
    0x9070e0109090b0705370e01022a01030e03040b0304031403151309020d08030a060f14061b01110d06320105040306150618240c1b05 58
    0x60001441c0500e0a02030501081c00b000301c1030340082d45410300550700d03a15001c0b4039610400c2d03e2410b084014400c014039003603d80540340718109414039075820254100700f5004a07103442c0421101b6000c80c006001d00d0b09000c000111980240c60141070000d0040340f294080360640e001980b10000d0f200c0c0210800090540008000c4840140c251101d861840e00741c038241915400c2c0e080c10350154001905d074200542040d03100a421640003403c04545d50706504d09058130341c1c000c03184c038240e090400b00005250903042e410311042d155078449840384081c00c0024442c080d0003024900300649684039041d00f517010280b003021070035a56064603071340c0c80d11842003400660f003195209100e10810f40403d07900701444140074400160840c00c0d0a81d42d4a000c2d001201c1600554201038221458010b542c02c1000e07241d04000d04a880310346a4041c0079200d0070300500b2040e16481000e9060b0021062981600034020a002c0c00300c1c1142010440940d10340c94058070000044002000418100c1d01407005103044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 430264577 1250 430263327 430263329
    0x60108010b1e030c16060b01120612120924410d020409060515211e011d0a0e030406050904020702041e05070c021c030e030609070e01 59
    0x1618409203489180801c0564031030310045000850744002c004503088003080021170719105084180c0f000e2a4a10342003590082c000c1007a03030740c003285c2107810990840301140110b074100c031140c5085030f10403140b50b01ca065690001140c80700402c20000e4010600c64031418940400380c21000f0400d131a00d040c1c4030042c200e215103c1d00e40d0395078121b00e0400641c95500e031808100c03614460a0709492030005d2011019140a16903100748c8490010401040700e6215610440455200b150710b440204d14004c8003104600c22a01c0c4c800caa1001c144160804490410443e03400a200034012100f440d81c0c1e00c5940342400c420f030070444001030324500e030140c3d202e44d015a494000c400c02c4010405a843e50f040e641d134a22440c8556000e0120101d1401201d07500e070fa040c0d03010f26030058020701080c1d0f0799060400c00303005000008a0658500800326a88520586900041c0b036405412080c40b2101c201c1c84201030202038108504108041c011309460380c90901040d0f00408a401c020441c040c20804050000441 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 430265827 1250 430264577 430264589
    0xc0717010f020909160918020a09050f03070506070828030e010b01020316030201060e0a0903090902030c03062e120c0e030a230114010509011d0406051305060f06010801 74
    0x18003c0fa6075070343c0d42800c01500400b4404207488100b603100703019122182507621085103a011801c10005110345600101141d06050b581e2542280d142c0341040b5010050a0450343c050740441014861401d12600038016180035030002410130b003503a8044140f001032072901c1a6401c180d000f200c280d15801d4022051050461402848107943c00d9000035505d008001c0203901a140c01d00c04001414002e61014010b40800007114869203000000f5030040d102d038500032000650340d40c0340010307104418801d0301d0250001b00c0100b85503440304020499090b500c004100480a51422004410607400c016080d000e5110f0f1a0241521841901c54044a4441030140c0c280540c0100201d150341d804201382e04501e82c4003000c02070324070700507480ca110980c280341c000ea20f80d842c0c0100b6624041c84000001c0c129442110002c2482c0c1c1c0328902d010010124041140c10b880c07015000c0340001e46030307800495012600d4008039420f00e4003078551600d084400c1d90000915038244080c0011964405c14030303809404c0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 430267077 1250 430265827 430265831
    0x11107030f0c091406010e090a0b0a0e01061e08070f03062d050a1d1503030c0303100f03080d092f120604030f08060a0e0405030d0b03190213020c0717010f 68
    0x182c0103001074440c0c4407240d03240e4810f4058100003084272441d0b501c0640b0001d800f52803408055111210491604802e009040c0400d0b07506070000452039090702244130a0700295111452500c4604064074144c0000040c4402c0c913847c0c1002040000703005042000d0401494000c143c3e00b601515044048545c540042e8050302004006001078070110480040505101002e8041641c0e00100601441d0b6092280c65050000040a8041140c000003550055182c01c2110a0066640c1409040210720f4413004114502c244444004240580e0003c0d41c0203009074010b03041c00c40080d2207245400c3c9040200a0407030646c0420b01031604250401c69a080380309401041d06007481e440140c51001400c10803820048481e000400315158058004020f141e0242c00302c060b803c02c1e19105840c0d403c000c102890461400490b51410701e80040c01d680d441400062041c1c42c0030068003406542d9000034407802e0711503020411649109000c015807001030496503000352414241032099070960f07205d00301c28040d0034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 430268327 1250 430267077 430267081
    0x3030b0a1202061b0a1a010801050402010806010807030605100c051213030b0c04080a11030f0c01080114030304050d0f0b1003080a030507030f05011710110306011107030f0c0914 78
    0x1101e00503a030382c0485401d502c900400a4040344055059900c003401c0c05044021010803242d41d80c1c41404c40701452114440b82c0c2ca454140b401c0b988202d601a00103190704012070500e50150110303940042c402e14012070040c0c0c85401140071026074012003000150900203103402c3c460300307006030a05076040442c15440c1500420074100c0544c0e0034000a05070091010200300800041d034125402054120260303104102d250a1403140f198507809101c0c080d01580c52514403010000c80c40b000d0301141611a5201d0f6420404290f92070805d603040319030180300400c8007290310341d1416a80f1900c203114060315100e6a2451420720000003024010340d080c0e9002c9001400000e1840b019075443c000306140c0045d040d0342d08802200035108140c2a00b480381c1c9010000b00d40070886c01500e8892260030011545204905048201220340038160011010780900c00b01e5125031181300903040b00d0301840b08561400d030b1243c940b00019410342004450142110780200454051401042010541c258103410b080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 430269577 1250 430268327 430268339
    0x15080906010303050a0c05070e01090f140708100506030a020d060501091d0406060e040507030b09030a021009030c020a06020f06060d020904030c0305040b0720090402010c0f24050403030b0a 83
    0x40c84180001014440d01003101c0c58603d00c610b088803030320b5030464202c402141d03540b00e0b2032154032800e004000165041803a000c05483e828011404d034005c452501c5042c40d55840001c5608007400342c69521590310314100007a02d5902c04004d5030140388141d1006a42e01c102000d980308036500380d4407181c1407200b01581005200b00014031044c000c200c00080308011313a034924101c17004101e10b0700100403950b00c10061205000001460f0010741c0d119002104940e11400c44546d41c9005d20640c83c001a03100d00d021803040095034104e00141486418018988401d9600094444c00c4d142c00c0712005070f1001000f1004482c0400405030400e02c2552a28040c1856030080340300c4982c010005010b20940480c04030400d4403d81c00ca5009110807411141c0300c0042d03140907050100c400041c955010b10030080c5101510f008188240215816124988442c210b03030759410407807a8408040e545080c07251100302d880401008424134411800b08001828940782c40d019049500000500e80140c0e52850f05000d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 430270827 1250 430269577 430269583
    0x90f0102070b1902010213080f010c030605060f0c070305030a44100302060a030b0a090621031404060801080f0616030e0a02060a0206061519080702010b090907150809 73
    0x42825006000f0608840303000c060303000e4410443e2108003100c00010004860b800403d1001c5144100c0009011012901d00304600796042c5000321544070004000e220101e45051009042d14440d00080e10004da540307440e0b0300d045421044590021800c40c80c1c0c0415a00344104410b01742c0c804004401c080c4d402d20543c1c42c00780018900b40c16040e0401c13a008104a104000ca0080081d0342c021728403551103d40b0100200601440490302e4000c0c0440d00d070114a13010140182403d031006c00881e801140c07020301140c0d05182131841e0076001c1c8400c02071200300321501180240080e0560782c90b224410f515220000e85400d04148800119820000500c144021901f200b0300004003246004941d040041c0045801d040c14400d000f9408540007401014050300803880700e02c40d02d401c9030b809400c0341680c80b586c40140310f103561074282c1c507107044c11700101c0a010302e0305103422050f940700000d403003400000441d40046007500c10715010340c41075104005043d250358140d9504000307480c15000c40c0c1030001c04240c2d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 430272077 1250 430270827 430270837
    0xf0a05090c040c20070819021c020d060504060204050a090207020a1401050408151f0b0a140403060507020a14070509041712010b0d06050d0510110c03040b090f0102070b 74
    0x312031512a0035044403a8030900b030b188a061844c441280d2181d0701505200d94840841c4500c4039680108500102500c0380319030030208941d0050600c20344400c001044500000d4215800c0703038415030b244034000104100c0d119003031289200d000010b0b03455051004001d400741c0d05600100b400390040011200603100c203000b4500315a00b0940f011074402e04000140e07014001d54009201d280303c0c014011001c94035400c021401b42c2000700401d4202111020f6110002441e0700902c10440b208002000301a03110701c100f40c4491042455543c10143c41e0b50303440003030750402c1d40c02c100168058081007060105a500e89000c1c0c01e2842c00a00400d8507241c0400c41c200340040001d013001e0607450794400c40c05900307805c8844c1c0c0c00c0c424004072802d6844144006680d000a488098083d25010b07010600e401c0500000c000307550040003e1840701c400950f400050007000507a60b400c507100b404518030910042003e0809070500d0144140c031650400c0a006540640c440000c2c110740c0060400c20a00d001070b01251 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 430273327 1250 430272077 430272079
    0x60212041202040b0310020f120c0a2a061404050607080603070302041a06121b071a09100f020a320f12040c031a0c0306010509030c09010303080f0a05090c 68
    0x1c1138a1603070400090810004000c880012800024602e000700323040c500902642600f02c0340480591260030311344100d80507014021020620410344640500207040706204d022403541c100c0b218030031540e07480b40c0c00c5c0d9006d5034145000d6000b1105100c10003200b401031541c494150329001e0345da8600000007d5882001d48400303801960391b0081114001407002a0000720a0701a00080e620320041446c6126014200c45800049001400c445117007401c0c10708480c09a078200c1ca01c0901c01040000c0440403510182080390248281200a0846491030092110b414140301d030058888400f4040034206804008001500c1c0c0c0c020711141c80c14240401c0d210f8404d40c4441000c68440d480c0281c060304034850072024050030049081000304100c40300f00d41006507441000745c201e9a108550f005e140d18503040d64030840d000c00900c0040c8007948201c0252241d6040101103c0c000c81010001c02c1c2542820f0304103400103a201400c0064109035109086d420003c0c01404003c82c2c5801c0c0340d1a80c0f5400c0300780b110303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 430274577 1250 430273327 430273331
    0x10c11060a020a0b100602060a05040b070e03101a0415150507080d060b0d0e011802190e13033002030c0c0114070201060f0803040b0c01020f0403030906021204120204 73
    0xe004010b100704102c54016902074018a651704154200510000c01407103140018070540002624141d01c5004003070203143c0c421500b9480391110a015154905601d0003950584640910840044514021514560b4405118441d1581e008040c0400c3d110a004001854611400108908100c0107041074404601d0b2620b02d45a0342c4901d00b05140d8030402c40c61804c00c504110b000315400c6c0d00d04004020038400301e00304000606020b05890b00f03842000801c0d1442220484114001d42401201c229a080e12901c0200c40151103000060b00c1700d80179070320354080b030342035007036680030160480008030401c4044e00c10503034610a217916010410714403290454004c3d4012020075100c0342c984058841142c4802c00900642007454078442258030112a40401503081c070b500096403025594000003510800c001035480e0034200481c0d0f0403540e01990588090f5035081242c408507564a03809000a14401d41d180d210a03071400900030f2902401d4541048002030801c0100000380c405402012516816280 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 430275827 1250 430274577 430274587
    0xc02030a170c0906070c0e0112020f1e0d0f0c0605120a0f0b040f1e1a011805040c05070302070e0c0901030c0c320609150907030c060c03030b010c1106 66
    0x14a00300d0f00070600c0860300007101051080c10007012a01d0401905c440e14289035840c1e17641d6142008244d860003001e500120402d001c2400390030140c9003003181844004411400300450808071318081d01e181070540305408800001ca08004201103041c005040a141403400e0010285002404030000f07059480b140c0d58401240091038901d030008074207000000d10401c0700e03034007451031840036000e00302e250840d48000c813500c9a4001c402d441050100c030134500c900d94003450b40c00010f40361030045403014040440c0d1a0b0340084c5541e19401005c0071500e0f03943c4c074262501d00914010f4a802c0c0e494204a400948101c01c00c00403410700819601320400920300407800c0111180c1c00da0b0040c14006024203e06411140550040800456141c1c00b00c82c0d941c1c0ca0103888150210319850f408140c3d180d51880c0c2100c800c100342c00f000c0b0a86190054003c0d030584a071260350390303a003441c4ca0480b540203401180070410140107154052048610340d420a00b80303901d070700b03005640304900d41c401e56061612035500466 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 430277077 1250 430275827 430275841
    0x103320403120c050301051c0803060d11040912120902030a031407050d2f030d050613020703030b0a09140604020c030c060c120115050d02030402040912080106030c02030a17 76
    0x4803240c00980582e00410004410400040c002d610902885010300300c91543c2e6114407901d02084044903411607151400e41e21481c0c100480440703500420b8071207030f055484c4080640c3c1e0b43c6c81526a818071410341950724084444000c0c00e1402c0c039606c09501c2e24904803408002d070714045101c620300c0da49440c0c0425a404034a420f04014028500b000e0140d110709203101e80d515800126032144c468a80103036501d401d041e09144089401c0080d00b0035841d800074006107155480c0b0303800460704220300400207504000000000c0e0204d070001c0001343d0010b615440013810030305043ca0810060400e000003801907418805031001a040d010340064050b0364000755141300001d062003a5942c540215086d01c20034100700000001079082401c0d41076540781038a0001030b803001082643c0542c400c450700c450b41003c003c885003100a400042042e40c0080e00c48043c3d03c0010120000419000c046803980c00c429410304400800300e40c4a07824100555100b00182059030b504034142c03a86c40c07040c000d00c050903035031210 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 430278327 1250 430277077 430277087
    0x30a020d090b220309050f0604080307030206060a05090405031207050d0e0f0d171303033e09010c26040608150f010c1104140903090103320403 63
    0x41480808503180c505940100215101c01d907000320110400015401c4445240ca02d030040d0f5070000078003280707040200f04800c0c03c008109001c038801c002c000900303013555201e60908507489200c0440060300a44204242480c00c01c2d070880140600741c039144158507040c1d580c95902d10800c5041512a0000703000a241c252048003143c445110b800000d0102e102d44d225227680c2d8000800c0c402c5600d0041100d03e650786846130700180b038081c84092842c2807a440e48134158944000049050701096203e042118401007010a000060b0342c03610b000e1038002d04400000c4441034200500c84200c04c4040142c000a030ba4010f03043c074501038004c5892501d40e00750160f0003512004103c001c410307103000414000348443e0807668130f5100d001031114024102c400c1c0d40070089007103242c810245c0410006401c44010034000c0b8002111101e02410018001140820385d541c691400c65507420300307500001d00d41c0d58650b4140036180403080d07440302c201800725010f10b04591420098009074592004800001d052502c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 430279577 1250 430278327 430278337
    0x605090a05030d0f17060d080a030e01020a110d02070501020304090b03100606050a0206100602150405010b090405030d0f11073203090a050319200a08030903011d12030a02 75
    0x408988003c100d140e8068020558003100c40c011403c00071034003040c0e2468602d182c3c03040c04000d101440000c0740342d44010fa1b9400a6104200f0542d8034001454a50b1007440140110b01081e02d40d882d580c0710b1443e00310b2502802220030700c1103401c55842000756980000075039080c1c0e4840800458480d0354040400d103030010740a0030b2126030b403c05000040c100c0c1c01c503000307101729900f03542610b0315a9610405a522020148152030040e0f00403c2070002c2841c8a622094000d0300c01c50012801170a02400140ca000c001d41d410b4400e0b810010b60424011140d100d226041b41302c002c2c050150112540380d50b000b0f1b00400d080a03002e180800103541c401c42800a070807215980f40c13440c1d84017001d800c0b84400c1d5a81c00c42a04a405801e10042c04541c0d440e0024400c59110000704041c400050a603590101c0781c95044000c2c62001c012800c440e0a5550708240d1001900e503100c000d54844280008050a4480030300140404d60300051f020064403a02050260a40d4403c43d00281c0e81c0c0c61300b03c0e44200070310074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 430280827 1250 430279577 430279579
    0x90b0402090d0b06010314010e0a11040e1e15060708090a03020307030b01050a0504060513090c05030304080102180625020607060f090212160303080405120403081b01060509010605090a05 82
    0x1103031142c0400c00542e41000d60041ca0b007a81c0403c070200460a900c03080300028010004250201c00000300360401c940c0207891500c0d94114060300b42513848401c0c2411210075503043c031410310401c2c00490f090503031140080d40306003001082403900e0002e102048842c49041009840044001070414081c0c5401001c0c500070341e40542142daa55070f980c1422080c407402070050f0b074401c40300c0d080001802c1c5454015401030b1007004005210141c3c05101010040a41d0030040f00d21850007980090503990a1001c4e000900c0e400e0005661040040e0f4500c6c1c43c5a0807442c031600c1824248507000d0002420b03600002541c1d52006030710800b000900004026015071080105080d00345640d0048a00403a041044298401d540d04d03440b4800c1c68803195281c0144080c048000c0e800301404001182c40307601c80f190814094826103602c0d4035045071803c00c1d41c0c0b103038009882c9071038000b07610103101d10040c0900340540b668070001c100850402002840800301072040d5410018085100e0113182d44200e0307164000c1070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 430282077 1250 430280827 430280839
    0x62706061306050c010c031505130f0606020d021912080c040b0403031707020a03081b0912012c0303070e0f030d03050717040206040314121206091609090b040209 71
    0x1940b048028820b034840c00e90f5850342d50a02c0c13004203425010740120b04c401c510380c0c40d0400d0031a003040e0501180c0f04008040c0380310303a81c44204000036140c1078401d0034080d02d09170b03000d00b220603403c0102901e89503465000b03503001d40ba2041050045400340304140e242c54001e1401da1701c1d07602c4201500c080f60049400c04502d519000800104150b040300006010300c000100e103c00542d03d50101340e840310f4071560041c01044969002484089200c819854000700d00c9c52003d0030205c0369408203001e04002c903010602a9900c4484140ca0b90004440c002210440c1d2000002c2c00c078081c4003ea01d80c04094589014010701d10038448031036807145000c07805008040c0c119691070050f0a4020007810081d5599000324802c5013080f6002d1600b019550b20807500505841e160034595900d200c80c401c81c0c0c002c8031081d03001c0c102100c28455080c20080100040190461119060200810900c03120142019886600351410801c1380e6401000113401c903940d00d8070000300002004041000b0f4880c0f90380c0b2a034810 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 430283327 1250 430282077 430282079
    0x11210f04030c140127180e101d0a080a080402010c211d0105120702030f03041103060c21280e01270b0408040906030303050405060627060613 62
    0x180329203000c0c0d00f07100d00036617542507000c400b990841c0c2551021700082028030116802440b201002c00044081d03072645200001e400d581c0c50001c241002101c0140c000d0b025100c6c901d010140e03681c0b5218101558144010b0040401940d541f030f0914400c9003260030602500000003020342e1301820100040c6030300418034141c2c0c903e41c030140c1446000c0952140001c165500a15461625051718100d6084c00607107070b407890440c00e03505803c142100245518114403080020094400180d0055401036100e5400322031113401c04d0003010b040c05002000c108034000b040c40f5484442c041c040c40118800303050402702096444062482112444d0503ca800800c50a0b60007006d0300700640e4800585030928000801086000114080c21801c48240101580c48180000c1c000b04050001e025017081c4141d44080c80e10313070707200340400030345205520540220761350310200000d000042c03085907407100c012541c01c105040c4600e0707500d0000514500c44443e41d400e0f580058141c3d00d85a0488100301103845486c1551 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 430284577 1250 430283327 430283339
    0x40b06030109080315100e01121109030d1d04020708220849050d0f090b0a050a110d0e010f1b090b040b0d0504030302070b0a0c11210f04030c 62
    0x3003201c5c0140030b8019100c00d10a1007105125040c24011102c4c141e6904840c40b200c02c440501400700c07008505c80207101044182c03402e076010005203400d0005601e40c9844a101e50b410031004180b004551030103540100300b050001401c050440e1401801441c3d480c5055425400d041070084407030b0003d800620850700500114100c040c420303035011038a600c0b0007042d400c444411841000200003240180d05110001d841c2c0d01d402080548010001880002400c030809260b0005a42c003600c0151181d802900034442071000c18028a0ba01092501080c0090178040c072200b070861080428800c410340d60742c00d041e134500d02d0a40200d440c40d800c030b00d01401018600f0395101c1410100c200d40740082004400c001075050056816502103c040d090150308128000303076244081c100c01402241007513400c0040b000002c450034221805101a102c001034009485040900346840000014940ea070141741c0381048074612070a20344080d01c070240100e46035040710b40888581d0203a500001c20b40e00907601d0100d28 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 430285827 1250 430284577 430284601
    0x9030303181b08010c020703050606040c110d120e030a14180a090c02250302091003050a05010c0e0a08070306020906040b0c0309030c040504030c02090405160e10090c08040b060301090803 82
    0x1591034603c001c01204000100030399440b001840020403a40050b00081d02da0301c1c05034051010020b0714101480307140c401c0d86815041c510b503084080c1c0030030107102004c0c1900c0d0651007140c4c81d2282000c020740c5081c03c124000b07058240c00b55079182c0e0030703400060031400204030325aa8940c02000a4141a1455207996481010381002c40c01d45005105a10502001215544010040142290400303c2203421a020301104581c000d10300d8600c80d440da49e00000069081043e03c0002d03010b83c00000e5024500038008200b0941844d145114200c40310782840124004101c06080700da0200380142c3e42c4041c01e003c101ca0b03005903030005000c0c0801161613528002c0c0030008007a02034084095814400c042c4c010402100d0050300c0240019490300907020050501102040e0028041d60441d00e425150f4445501070528581050b14040d020000780052103800e80c806038081e003080c010920010069840040207004024000340010b104007001ca101502c0a601c908800360300105542e80e245899015132030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 430287077 1250 430285827 430285829
    0xa09111c1415040b040501020712052a0d030e07050a06020706030506010503130204020c010e06070c031205220303020909040c0501180608060d030215010f230109030303181b 76
    0x180c0c1210003046a900c84000304411071409a41240070b086a256903c0760807200f000200111407540d800c1010001090795003088080018099076407540c1c0e5070050a00700d070310329500610307411000070444800c1d9074024081030101e07e420440c580056260843e00c0e00e0351400310181e01580d0000c0b41100b02192584c1d001c1031a00a54509440c24081601d40000440380e82c80201d401188410f42d2180000040c5840d800400c901da20748000842c403264444035007800d000c0180c4562010600500d40c501c10950016605100002114070410032807408150742c596102c407495480034202c00c034440741070070140641d06440c250400900510981d12740352400c102030f1146030040c240803800b6040304951400540c0784c0001a10040c0c0e480d185180c03103020902aa1114664080341540611010031030130b003552400440c001c140c4000c1461403207140078580c105a840b080400c0c107000e40d5207900581c40c2e98006081c40c044981c180390015031100d10803c450040759107043d0084c150f42c10155138440c00ea404e008128 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 430288327 1250 430287077 430287083
    0x3030d0c020a150608060c1602060c150c0306030c0603060d020409032006010501122d140f0a1104150e0621150f0108130809030d0201020310060c0305030a09111c 71
    0x3e20f5981f218203404031580225104000214410b1448100500301500a4024940782408480e00404210841c450315402114003040a10010081017003a29007082603000060b001e485840c80c41c02d011011070b0725030313940702d0b4040e0085449400340390816124040d540381d0f140f11704600b01c10506800351020749400303003031140c680000c00b00c01c480340c1350003c00e203d9081c0c100c0c62091000551030031013410b0314a01e0140b00031101119a00d40340030107040c06d0070030041c1c4901004580984a454119107600440385090003214909100340010704c000c40401c43c0300c1c000a4001c0c00e049400380b028000051440c4945400f9020102e07000040c0d000f0318032a50442e901a40e03210104e0100c010003a41440b10902e0030000c40f0f40047c4544000c034420003182c80802801c0c0e80101001071034a1030600c08030340b03000040060400180c4d400020007002d62070752929600541503600d88811003203071503200200b03a80030190440c041e19a84404507420081d03041d101000c50440a000d099040030080041d14865040ca4030503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 430289577 1250 430288327 430288333
    0x50915060d09060b0a1d0a02041703220e070c050c040f05060918030406080c0f191b0c030b09010e2508010b30030328050603030d0c020a150608 63
    0x2041d11403405401e140261800314410046c0e01281c1d09112080f1132016264081255080101140700354004e10740e4980440407a0080d942c500c03100342c0e14041d2280c0600c1840348004a0320082c03006a0806a1f4150044010b1500b07110244050421905024542c0140c0b41c3c41494000003080401300380c1c10540c0300d02c04c01ca4020102c0c0c0c1c0e80f00300c03024980c03400500001070f941041000f800034030300900c2416080f540c5e00d0000390410b41c201107810305c40d505c5450740400700d03841d00d41e140041c6948800041e041c0c402c0300a100202c1c100c41e9070f501540d0a0180001428080d42900203500060254410901c0c4081d5030105c0d4030807001c07014003050390602a1501e001c40380003400049040ba4050103080d14580e0050410000c82c0c0c0c0c1d0204040c00e030350845a001c041c00d0391261500c009d180302040658003074041e00c050a01e04040d020724a540e082807046110b0b1406050000f00325090354040103035000c00c910100c001c140b500004000f20f04001c0300c0ca00040c943c192841c0341e814031480903030101e02960041c0c011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 430290827 1250 430289577 430289591
    0x1006030b041109100203070b0a02040e0109020906040308030402010309060606050c0d0908211908010906080105070206011e03020a09050f010e16030218130c1b0c050915060d0906 78
    0x103000035200b4407000c000144408002c0c401050900510603411a072491043e203060180b15500e40d0342058086e258074016030380102d02403201c03505042050b401060408002c5241c00c1c102804943c09010b00d100181000202000080942e40243c000451280d070003101009a262911009021070700700305c00e00c112130321507181444010381c0900e4664099039050401403660740c250075035840780754060301024a0700c1b40003481001001d01407645910705c00c41480d286c0d0201c542c10503d07910212a0035600810a503170614061000d0b0a801059241c10340321288103080507281c00031001e640340b16440d44000d41142d103168000851102c550301c098020785a800608440da41c0e11585844408411345401607200c02c98921422000e029034001d081c083d40c2d2002c40c641003c101e00014a00b240140450b01e02d540e00c801c0402c6415500c039841e5840d08000360300c1580c08101c143c981600780d1040303000365400b408038480402c0b0109000c44c0c1c04403901da8010180341c1c0d00e441c08000480a00b1b880013048801d5824600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 430292077 1250 430290827 430290829
    0x15020903100905061f05210a0b1603050114010f020f0708031b0706021f09060e0a0203120307090605130902161101020d140904140c04031e050a02100e04051006030b 72
    0x20724070005900d181c0503040d02e410207041010f103401c0b41400b10301f070310b80c1d04410301e00100d02804860100d40c000c4251480b14500034405044040c25401c0402c01c16240c1401484203910041400000c0d05003840c0a0310f010510340300691612800584041d481e100b8501c4c002041e0100000404594450341240d654440203010590342d603502500458026800544c1004002070381c40c1a007201090f0110380c040796104c129258030048561002c0c1415980d001004050154103081040000302c510800400c3c0c654038012400a00c2c040e04c2d400350000308000010406c075101d0b50002444090000703150115079890196481010742554101e0441e40c5489004002c1e84660020807080ba0300d00c6691200e1042d00c0c070312455118554403031564582e0003560b40301e1050300b8110340740c1030300d02c5441450000c13580d0b5411030400c0842c081d10f40386030340030090001c0c80b8500043c00c0031544c1031825038180e88900c007038180000d007a510340d40d030104110f400926003020000310901e03c115803405c4402a44042191082040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 430293327 1250 430292077 430292101
    0xa18060803180d150915050f2203030f02130602070b0307050d051f0305030a11010e0c09102103110c1e0303070f0b04050601050907020a1502090310090506 68
    0x24140003010315024861402d0340c1402500003004500c18503038801d0034075000d0090811580c041506451005403102444802d03601c42c030526400100440309001103240140c003022441c0f401c0300c0003425615030783c21800100342c000e4000c2241844881810341d11141080c0078213108500c6403042600500c501c4a002918500940c100c03405004241da560740b0745140d0039088005844050820b6000031604907040b48031350300004103800554403c070050b43e55116507250052000c1251030003074180ea498181c00304030b075200001d603c6525203c00e0703034422515598401101210011507100000340c4000900381c02c3e1217070454801d414031070700c6074540c1c406d01c10300d80c5065507640010300821508046c9003c1c07520004c640d05490201e0354100182120710306050360b901c409411240c500121081c05001d018070040002c2480580d016150a5030323464203610340400025650b103901c0401504501d061036040f800183d447c0c049a16481740942107a42c0d00b09900038a200500d81464141c809000e5032000c82c4000f400d070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 430294577 1250 430293327 430293337
    0x4120f05120c0715180b0907080307061104050907020309180903070f0516090207051c0f12140412120513030e130908070c0501020d09140f0a18060803 66
    0x300e10440b82d4864100600c1e55100ca00f0603140e6407000c060140c10b8100320300400031202511882c07103000c0f10b980d142c010701e080006494905503030454030080c0300b90f05001040e60b191513000007003c981ea00d4402e000503481d00c40ca0308150381010000c0104942150008000c040700002907a218800805102d400803071500d06a800c8800b0750410000440440e10540e07100d03500c2402082a1080422410300403080d503d000c0d4030408a190300810107500b8001d09005011034403846048903240030060782d17802130500b4a0204503009105d0100540a000303078041d84968001e4000c403448045e141414206088031b0000c4884403400295410a00358014085014a038040e641402403004411031135070f070580d1001400c20020f904241c0c0380c95480902c3d481c9000d14140d1034000e405440d03940c107031400d00450b01c000c250020b6055610a800300c070543ca43c0a040d4070120303a1007050f0405c04014600010b519207000801c10341c1c1c48950390704c011070642400c030540609521804010005140d030784004503128091 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 430295827 1250 430294577 430294597
    0xc031602071212110601170c040603020603060112061208091002010b0a1710020703030e0f0c06090618040c1d0a050303030a051807080a20090402060a02030f0304120f05 74
    0x20b60503200d000540600c940301e031800704078141191361444508610389001302c00d0703102000d41d00c403510000501c04e005001c02c450b6800d0641c0c0c00d001c50f50a503000303e0410701c0081c0c030b064100441e20881d1403040a1a03448400035021310301d00d030180115281800c000a030008035009201ea101259007800e41401407003040b20b8084085c0a8100300c526005500017500381c49240f4000a0140090019400300244000c00d08140b103620000b6800b4803942d506854003a403003541400301c1d40071080303180c03240d690b40081c0c4500e01d00c21030702250703a508184503015070254100440e42e00075003052440c60368940c0000300c8405000840982c0d010581800b0100201e800c0c0c4c911030036426400030070210329100c1e00d5070400c55010019224081d551115400301525142455010b5a00ca0708010355a0080025403010384200181c80a4060b248070040800186d800c1806071000b0320030740c03000860283e02030090003545d0060f60304500558480c505800d008102e80420a01000058050318112400340c1c002c0c1c0a82e840c0e141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 430297077 1250 430295827 430295849
    0x4110c0a06020f250c06051204021c02100306081c0e120a15020406080a0905030d2c010614030f2e06080309030f031c050612060c03160207 61
    0x6a4507814029400603404203500c103410041164204030b003c22910000b406074609002c411524100359003c5540c41d0003500411604011a07a80c3c806e01c1c8400b00d410940440d054040242d81450001e11981e41e020020340180044c4030f51026590907a02500848035150706a50895801c903000d4003590803886200310210710141d1101c03505040844081030302800320700c00c0342d05910f5103494001000e80d581c0d0307000d101c064000405101803036120044a420402d450300c28041c282943c0c2c0d419460b801040c525440d40d55880308030b18407802400d410403000240c103200c1a0b50001074000d059000e4070190060034000010719005188500340021091a06481c88001d025140600403e482292101890300350082c100b007141c43d51a001140f0801c4002c03e80039004503611200c4009060030402507111445d6160001c1c030503010b209001c086401000410901c0000c1d041e51940000f50342e081b01141540054403824082000f0303d9141301c0250300500d0110340d20b0800c03440c400030899403840c940c010710200e18 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 430298327 1250 430297077 430297093
    0x901080a1403070803090a1b0308030106050c010b190e13210201060506120702010c090302130c0201180606290414041416090b0c0316030c050d080604110c 68
    0x41c81e4401c80c440703031032a9900b03881c5441d03c0364807000c0d00b9400694540a06400c0703800341c0c10420489101d2000f010300c0c00c143c84244c1c2e61540d240ea0001340014814482840340014041e11001030a41c00030740d403100c00503c0448000000d403144d000351801400303164103040c141804540d081c2c0c0c000c049000c00980c04480540d1889048408000010304850800b06564880c1c5002c92281d4801000d0090f081001d0b02c03004951a00d02002802e582d0150440350601c070002c5420b00140e260b201c0c0320903403030b01d240101003200805480120700412043c49000c07483c0c800040640c007007050b20f810580455491a1442036030944008e0b1840c1d0103d403c0c511035105150070070081200b001ca00f00c07034034641b0800410005007803c03600c500c280ca447c0c04036880340035501c148100d40156500586280050b001c0b8014041c1890700d10758480d59a4801c03035142d4900c81c212002840205881440284da01c190f02c00d0039501000c1c401c10014085100945115100301e062580750507240252005403410501004010280e172 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 430299577 1250 430298327 430298333
    0x50405150901021006061713030804060b031504050105150619030b041d0c030615090112110d15050a0c050712090f06120b01030e060c030a020717030709050901080a 72
    0x295000071821070541c050f000d50b6443c503469522540740240510b0315503512400070350300a0007403448010a84c0c40802d44008804011952000c50260700a40c00340c1d0005001e283c080000745048814112804641c4201e8104800c1010641081e801000c034100c040310f01c4005601080028001c9480403031803c0e50198200c90414441d0f00028030b41d410151002496401000c4030340100c510f420320703084180d8007107501e414550030100011903118100d40000601d01400304001000c1031010701c1007240c100484d100c800c0c02c3c01300c81c51040b10301510003800081c40801d14039115910440d1219042030343c1c0d140078001403555215000d089004552a40e402c0d1800741283c0d104007250024024450802858941c045004441c450a5002520203500e8032001208103040300d07400c0c2c40c0c2c4c0400b1030741018184a000f101c1d48100084d0741c5d800001c036080a549940e5008640d50081c020520003402503204401d6045200c0c080c0c10045014050700c0e0b0340c2860182e259414002c102a0a203d9915550301500350394001c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 430300827 1250 430299577 430299619
    0x105060102100203040813150801090221060a080319020c030d0c0b07110f03070204050606040302100f050c0d08010e07030c080601030209010e032e0507140f0d05040b16050405 77
    0x1000348919142402c1202e00d0000c2c101f40d9000750880641c038241110f00000690b081107246005087ca80000d510700415070303090084ca090f9036a1180e110505403c08101e6070783d1556207040140040000322501d5040000c104250800d503044400e0250085c211203a440d0308000c00ca80748100071035141c030760a920559030340800083d4020404820071111a46841d2000b4042c0b00c44110401c1c075100443e103a03030b103d0042204844014100d41d110382c5080004100584602681c003100741d01a09048503154103403001a90944561080394101d070140041c160303081c07074000c030b2141d0580f001e084c88181c00360b41e070000036800c880b000c4040c2e5001c00c04140001d603e03503100b5001810310b00010b141c000c4000d002c4202080c03078444010307003c0110011209900030300030340302d0302c59140c14a50450140194285400003402240203801e0107031445000181d551100c4401408440d0040d101c40e404009600c1c00741401c4840b80002c1e189000300d10302503070480d140c09c0c1c419400e40d0156a030052a0310010001510340b44c076 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 430302077 1250 430300827 430300831
    0x30c0304140a08130602060411060a020a080c01050a0e0307230c04060b04060e0d0b070810270e280201021c27120308060613080a02120105060102100203 67
    0x300c03545003101c01c1d908032509100700a240782c41000d99135126803100000c0d8141e02c2180e000170f41198092010030000c2200c46c0300000e92711030151042562000b08020403801c010170301e40080c117448800155068000700561049124083c412001c00950780c2ca80d01c11a181e101c3da09018282000170004419031105070404030070999142000c40c2d81c1c0c0100007011405580465101c5840080701050802210707800088018561000303d902600310002781c1d0b1040000c40e0040e098104220403100098001d08103180b1000c05840140461000b07501d841c6c82c103082041d810b00220308024200100800400750004460012a1044d6042d0040d5904104130107408110725a0503411445030105d01d0025051500902c240c1d48090f644d41203055844c2d00e032040e00070b141c80c103880000c609142070130082c5503442101c0401403a814503104020b501c0c4d000c0010b82c2400341603e00b0801d07168001001034072180c002040401103100b510341c0000282c56a0740d813803c903101110740b18090380140046074003a1096500542d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 430303327 1250 430302077 430302083
    0x1050702041a040c03051b0a02060a0203060301090c080307031715041e090f0b06060301030b06190312120e1204061215170f0d050d020a0905091f0f0b030c0304 70
    0x384080800d4002000c0d1134441c03030844040395882051003290060912140180c00599114a25040e10348800941c6d600000b450b21800c13582c0400800c0300caa40c03c1d00f20100050b0054031a5030002c0d200e040c255103a61040c0307812008030f4203801081c00900305040700f0b68030950284181c10758000d810400e02025005d514803408629a10811920309160070707118071902c1c2c50040d4400008c503900c41ca02000301e80005081280300d04400d2004100040d0040b92040d400f40064441d000480d44c008285803c40700950002403003003d49072040c01d50a81e111030844044000703581d042c40000882d203103182c0c41d002440b10324020b031081000f060115900524a845842c4410500094840c030742c01010469038003182c2054448404071002050070700010040400c1001e40900681512408208040c4c0755205455581549a40105000614501a0354150001d15000d07107410103500d04910580c0d1042001c62600d58880d10190380440c00b100140100d005036170140320b6603442d5440303440c034011054000400403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 430304577 1250 430303327 430303361
    0x106080d050a02070e18060c0310061115041115040b040302190905040c09140610080a0221040212060f040f0c0b0c0c01020d0212042d03110312090105070204 69
    0x601c003c0e5605d0342c039101e049402d00c00306080e161640c216081c00750141c41054100d40a000340f00d13010a0ba030885004980443c01d101c003000005d81103840c1000003440344007c811072842c04010074801c171100300c800c0d900000c99511030303201040407c2035090300490168140307070380d400d110900c0113040038030030b035140101452081c43c0030603078444625098590440d02224132040c00807041003003042500a582c0742d000c1c04041c0c179859140450101e0004a0242c4601040018200c0421241d4aa607811100340201c524046211070107131502071009148152405c034014400300b18211207080c80070170502e000d250003285154403a221070315814071100c0c0c04072083e1041c12040d070f0300003084103180000305040e4034540c010309040c03c01e400c00a400c00200141182c02d54001c2004000c2c641d0012044800b560f2880b48030510840c0220121003042040b981d490326040b400c0207000c82840420303920b500c40542e0440882d201d012001300800b42e94003510540c107001c95002c2c071580c001450244c100c440b54845000c1c1c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 430305827 1250 430304577 430304579
    0x20405060408010b01020d1d09180f0a0b13170a0905040504061505030d140d140c0c010c050f070f020310020307050c0705040603020d0209180d0504090b030106080d050a0207 76
    0x61090790059000030301c41c0e9583c0741e1402c0c05503010b200d0040d038082d00b0b040c440058401d018248210000030b0301e07143c0c4a01d107000c0c001000031f40c24230b00010250310b500044806518000745d1303c0b07a60b0040030340c1c1682e150303202d0030014424024000200306a40e0348208428011500404158101c0c0c2260301c82005203c176207071002c41c160700c56108140c400da000e03000202d4600301040549810001d140c1010b0b0190b004004d40c0f8400035003081d0005001110403041d0b40c0d40740e202ea203038a0b008040e800d52810100280d01c2c02e000c03a0255200281c854091410005c01900c03039007020a0b940d40c071411001410000c002d00c2113802007130200a011b41c1d501d0001d001c1d101c5d050a511b0414080303a0003200c04401240010842c540d6408080040701c003d010169802c100c3d807420758001942204000d4002413103000e6000000e00c00100da51a42000f510300041101c03100002c00c04007806a0300b050081c1082903161045140b06490140620340072101c080c8050711011036803107001c885603800080c10200f50711849074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 430307077 1250 430305827 430305829
    0x20f0402070f0b1e070e041503080a0c021c0b0115091d0c1c1505011d06030c070b071d09060d02040e010209060408031b1612020d02100c02120a0302030418020405 71
    0x8040c17164a46a60f0148500b2001c1c040108690030050451064141c604050001403c100110b40070f500b045d05144000801e075100044e88081a040d68407a03410154105004001014661506940010441c49450104000c0c11100c900051082c6901c0401e41c40201900000e014000d98000e00c1c08210540b4009255019088101010100c00e100035030341c1031a9200701800c3c0303101d0000341900b480e000040511050f0a4071b010890070031070750301c02c0304000089880100074204a80c825507110380c40303511500d400500540b0f104000600c0d048003480717011805030a440c2108440d8407494000b440201400308036000e03c0020200f00500d1583c40d0341c2040035042030340c0d07100007800041c0240d20045558944904041058000546129456600c8046c401c220f64410280c2107090354404c40d0700d4825a021400010a010805000690800c240b030865440d15644411940c0e07040e4005d50781c044414501e0020280d80e240c40c408003030300607082884107010040401420700b03660b01880c4c01c00350800382c03968 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 430308327 1250 430307077 430307131
    0x6090f04080f0c01020a0e01110d1e0e0913060f0203071b02060919091508030f0d02130b07050106050a1809050c0a0e0f0a060303050d150b16020f0402070f0b 69
    0x3c2040c2c007c40d26100c0030b00c00300c0d84c0c81007181612042000150009440558014106000108007210601c18442070000b242e03104101e800c0d1002001001d8185038100854842c00340c202015041c4d47c15810550307001b40d1320405000301d81c010856941c0e200c0c160310385480c2d07640c03158455500803079010700c0800c2044910760380e00b040360010103021101713182800d14020986088a400750340103417070400001400c108801c400700035509090411541d1690701d00b412101500244104640a8004024043c0100e11a0301c12405400c02511840c004c005143d05c1e60100000441148654003143d541c5103c0004034151076041003442c64411b80407200010718030070014402040316002180900c40c44030802000011036074030b2540024002e1010411142103031002082442011060602c481c0c41d41c40380d40c541021040818014010710840c076403a85288a40498091309600b401d0b44038150300d5107010284c0c03400c1c3c42198441917100c2070384d0350f00c0204c5a6030110305076801407003030310483c2c0b80154514502d03400c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 430309577 1250 430308327 430308337
    0x408031003022710080a02100302041509031209080601050613092a08041502070822090c050f032815060f0203090d11060408120301050906090f04080f0c0102 69
    0x3c5018640030840150040f0310b80c80245414029041032004000f04000440c00b040300a4064817002180c104282c8254042c0c400d96028580c900700d20088444140d92000d1181d040c0c1e4822282d168003075481c0c007070481d031440f15409101c0c016048080104000c0c60803800034030380644681271869446942d842100211104640d0a0340b52190038842080000684074025010745071509013000241040d848101802401d90301402010364001100760601445009551000401e0080349050000340b00468540c04500c0c8114075110b828601b0080d0450700a40a0394030111102521600750317640c4152203100c828148217046043e4046c080c0c0c1c80034400040c058460030340441140400702d68607010005007285421705034007086400c14064212160380d070540702101140c1018110904101140018042e8803842d400213150740700e01d00080d8070025030340d0080c604031502141e402405a54080c10b100411100310707410341078420403070002800a191003000d0040d2005414100707042031010030a007404c903400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 430310827 1250 430309577 430309609
    0xb130e0a0605010803041203030203250c0203390a0b120f070f0e0f01090b0d090510091a150d0b040c0611030a030513061b020d020c09040803100302 65
    0x10403005000c40382c01064014954040114a81071900144003411160f407200142015000008113001e50303a00c04440343d01ca00e54280c1d95a4880c802d5070040d0100c480c01d41c00b01d020780610b00e1199a034401c03400b18580e2030601511040001134080007014030202000c00103a510125542c0f0210349184640090400d600884504200d141801410756100e210020100307000c00101d511014000c030b0340b2041900d0168815034081455004050041c2c41e00b0445030440300e401c160204401001401580100d10300c40c0c090b100752002280540c44d841e00380c0d12000d90141803080e0108046d0046c012107003c0320382c0211409520700c100c10340000000c0000240001c1513410803814010b001c01e01001030f00c034100a1503141400c1d40b040c02d001c541d5580324004e480c070050a051742d41c80021800c0b0003140140e00b0a943c400800c00c82c4a040d06210342e01c47e03590456603401440b8100499410a00000300d100000d00000c03d1510555140d40c0d5504055100814202417004600800070058546c0b00181404402d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 430312077 1250 430310827 430310833
    0xe0a1706070905030c0607020d1104110a1205060a06110f030744071a163e0f07080303061e0a03020603090a0c03030c1104020310090b130e 61
    0x411a80082c0103042d01e4000d81d1082c1c1024414155603902c20045951040e4190380d0028941c442c0d0a0141da1084815901c0b0b402c43d0602035086824820400100301c418100d0320303550f440c580c8000e03107081125400c40f121a0800761510003440f4841c00717805c480040100741c1e0304551031520f244240c10308540140d4000c5070314008110a8000035151464004240c2c1407010706030401601554090030741000035001c44484c403030000381401c00c0c8000f10b100140746203d03103941b8440e0703801c0004e080c0f6281c2180c0060307100000c495900a1181d88518403560b440500c4500c0c1e40b015000320103c8111030340e0340034402c286603071184051401854606000c04170060040e0009941c881ca800f000744070564481000e01c000003240300c0400005940c0e103c040d8010399405940c0952a03590720203600c0d14003103141c000500843ca040b100007007015840a80c1c0724055100300d03405500c121400080c80700b0b901094a50584000300c80030700740a0000c00d6072005c190140d005110880c01c1d417031003803060221404000000380d1030b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 430313327 1250 430312077 430312081
    0xf120408070c03051f1514030a200a060c110621070f09050d0515071407080307030b09060f0f0109050406031a1003080a050f120a0c1106060a060e0a1706 67
    0x180c5048242e2580c15001c441480101600c00346c403103002c1d115000d92220b0400c841a00c5c030303082d201003000000482c1d03c0051307288003000c400440000f4001c40e00c010381c8a40319034100800c400344140b0103911a241c0c4101c0007809001c4400400a00e9004811144425240e14034801c50b0b1054504038140510f441b501c8100034090400401492000c45401050080c4d620000d035900003000000c02c801001d4255403040400d8035010400c40d0b1001e5001c060360300960000c1a0354040c01743e110019801440300361400c00c80800c0840c180444003008031260381d400040000711f031400e410544114000c3c0601403618141c410380310f00c001403c4030490380080d9a92100708009944603c2c8240a807508414000700450030207181d0741e21844640700c1c2c3c0ba200c5040040114113803040700054420b6491907144082181010702c1e1018052006080703441880380003c046000c50480b981d00460130034014900a03080d09030305c82c2448000c0e00c100a483c403103c0e400a400b030000144520081ca44050305d500c800c0040d00f254 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 430314577 1250 430313327 430313353
    0x40f0c030303020c010b090115120f1e0506010c080f0702032508011508030f0c01180303050f070e030d0e060d140414060121030c1205030109110f120408070c0305 71
    0x11400307119403d009040c810014802c45102050990001380383d4604002c01c8911910800c016141074015802030904020480cc0884585004d140e211000c0070000c014075a103141c01154690303d4403102912a40c002c0154014012a44008188890010b0211400142145070720001c0d40b43c400740c0049501e01200341400b03400700c2802400e00b0b40860126004a00c0d091126190726803090142e0340c1c03000100018500a0141c080d0411080e40c4598100340c4404c01c09070a028010744001c6500d04080301240001808040c091040f0040444015004041c8841e07814415200400c0b072070501d50740000d081c032200c200f03103466000d0400522000740300302440341042c0c501045007041c800c0b180007050300568014082001c04070340707a0b02c2d0010741c03404401802038982021780d0070748400c0001901d80707943c0214011070f1a801400440c1200d00b80442044080707082150100c0b580140e80d0110035610782008031403441070b038113540290828000c00c8200c2c07034000d080d900c1d4034140b1400d5004548680140ca681201 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 430315827 1250 430314577 430314581
    0x70e010906090207120e24070b131a0604020405090c190219031d1305010e131505040204020c030304060605040b0d051f0e0d0305010510050a09060305040f0c030303020c01 75
    0x9100c4604154103010130765850700305901c0018109002c011140414038020355a44030079902058100e80311000b01c0b2103244400c01560300c030388400e8801d80d6280340869090240707002c0481800d40c1045024104034055403e0490400010b80003a40c0542c090002250550710005010702903500c082007295506c0d854600300d0000c00b205910b010075034010a190040007204265560310041d07052500d100915045214903802d11505d4070581c1d00103504400d40b07079401020b5400103062340e0821400d2001c0b41d4800210094408640d44002c0038201d2240c89008880d24503000b003074110f44004c001509000154505a2071900101d0f4141e03116512140b04100c9410680700358094424140d61401e920314498841d580d503a04040700e644440c01c0328040d100701031183d5600194003440f04200b520b000d1494520014050042805294400c0845e07440f2040c9050181017222182c0099846501b0864a030120941c000e01c0024015580c401c500e02001000501c10311400005c1c40c42500e006031140c1c000307031109003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 430317077 1250 430315827 430315829
    0x501110c01020705060106091d0a0f050403020f0114060120071505030717130b04020f10090503160303090b0307020a1707140114150111120405010f05121302040b03070e010906 77
    0x7c02d01007061418081401d00c50301120101c40f090009040386d0712560501d40042c0b1100301070005491429050104269010401c50642c1c0d600f0f00003881403510907040b005030440c041d1003c5010981000c0c000c1d0720400c030740d1030301d14014456500b030754402581e4074105a805050342002d100020000420850011f40010300c5600741a01002c0d0106145400c034401003208041050103042201141d00050840d51420b0600500c1c0c0c5014140300c010440d504e5000e03000a249000705807003402004255484512404d03509000c981c1c00d555404600e41c50103046035856413000e4001d100314012809480701044088510394005800c940d5416a280c860b4104000360100d0340391f15081990502e01a4000c40e10906240c42e0042125a14482d441c034120006854080501007030365658090110084484406e4a000d0300417a0b00030781303c8108010b44000300319140d200d200140310001ca6000042207405014845c50b000c0c0a101401c00111008010002807a1003100da0201c0c6011507000010302850400b40540c030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 430318327 1250 430317077 430317089
    0x7080f01061509050312091c0b0a0b04110301030308060d0f08190c030e06031e0103150b100f05161506090c050703020a171201060e030d0801061b0501110c010207050601 74
    0xf280e00c1d0706200c002600c412003c1d5041d0300401011035414010368841c84034440030007074907201c40f540d100c0301d20300b03020030313610854088c031240b0f25283c410521400d0601801c0405901c0c80c80c128590b030700b190380030766038070002a02c101d41005038103001c0b100091283d00103d03111800703030707929503241c0c0e904100c00c1d000c54001484000800840c00d2204001a4020803c80e04010b01102c90701e88954506100d9040110b410900440a541c1c800001043c00b503442003a145081003001d0911260340c40c0010300402e100010070f80c80005403502104507030284620041c080d40f041844054903410381980b655820300d102c1060394820315a580000308034134400f40c4203840d4041d6113420401d08082003078502079144e031a0000061b02001190381c0380e202c54116003007120f101c49960011015156140d11004100d82910400c00d8040d01c601c1008100103030003a070100e4101d0f0035690350240342c2c030729040d400c505014030180112465901c85603580900e552800c084c0c000081060300050b12500682003240c40c000060b413043c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 430319577 1250 430318327 430318337
    0x60f13050d060f06150f200106091e1e0f0b09090c010e0102061029130f080c06180415060f080f0708071d0307090203060906030106050f0f0307080f010615 68
    0x5c204425007005000e54506c0c407509044a614131400ca00645030b41700b00741010b41c5546049004104ca403800d5104513103850000d150302600341340441d4441c1c200c900e03100e210908911201042c4080b242160030000c0c4040e10140045a0503144201013800312109841c4d050303481e0051500d080c05541e02c445036500c2014244020002401c0072441400400114001d105012070801158107a00c105040c8039030034540c046810594503e0720300740c0c0744102542402000d210800b1854006400d8038005031084a041c001086c15180100e0780751004980200e18002a820586482c0300560350000740c1038040080030b145d203410207620003e20005001c00802021903d480c2c03103130424445019803140d08a9400f841c1421302e42c0706000e90301d0b001d0120406000c0c1a5905100302c940100d01d5070030503006540201310a03903071003030242c4422040500740c9030305002e0682c1005072050140c40d1440c2018000211320f2000d02900c08103510745450714181a124441d0301d80301e0f9100c080c10407119071407610014611200d484c003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 430320827 1250 430319577 430319609
    0xe0103080705241f030515060a1205100b0103090203010c051b030c0d0809100c020102090a0509060312090427050f0f060c0a0e0918061302060f13050d060f06 69
    0x20343d0402e8080c1868400402c20140e48072a403c80d0b82068028603084812507a801084420b0344100003000c45d0101d000700903051001482c120001d04217610107a100e805400408208206040100080d20b502c2e41050b848800300d40260300c0a00c00d00b03240102d0344e51103558902044600000350b450603407800c10b07140d104001c1800d4031040800c2c1305025500310710b00039519403155960340b440e01414480c0d8924a9141503c0c45840c1c6030154000d090f030b4042581c0901c02d6560320000c00c0008141201d140341c05420013903014410000d4440144044100140300140c00c40056940d040201801c1000b10042242462440c040c40350411805200c03460f004010301c1c22000105819491b40780260403608002008901031107142e0089401070920701e00030381841c5583c900311100a910110f8038020085a006003804200c10315001034074a600342d42c0190000d1b24007844030180c3c5500303034030100602e00c00460442c0003280958910b21114020360242e0008038843e502c07903108100b214401d80c005c299070b00da5949 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 430322077 1250 430320827 430320883
    0x20d1407030c050f1209010213090b0a230907031116140309060706020a0207120f0c06021b060c07030b0705031906050904030813080d0603150c0e190e0103080705 71
    0x1040300c0e1614400da40502e05506d44403150341c068000c40d03c80c0e440002c6240000b1850200031b5103c2c0701e82e00c20440d2103a410301c0d559042001c1407601c0c003800d000003034010500000681020845983c001d545485c0008021805095400ca260052088003aa1024045006081c801e14408280881740d45d20b001d54a400c40480001d240d9202c1c45070010001c0390042600080540241b00c1c00004084a145003a84041b03c3c0c07505003500c1d00d0072441211101c0051030003107402c81c8000344078128400748c241608441281042007001c55040a00d4061591140c5000440010b16039a001405000c82d5140c00d600d82c140318100b07800c40100324180040e26440c2500c108003903039540f0030044d0000d80505090185407030350115507079115004540a81031401c0007541e5040303610568000c104403070051000c04c03040ca10104000051365030f118900300000303008141e270020500c0c10021500a0041d01c2e400303015542c0c1d03030304c1e285e89004009034425200c010000c80c0003010b01100b170141d06405003000820f104640c22107070b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 430323327 1250 430322077 430322107
    0xc0103110a2a050105010b0703110703020f01110a06020f040f06080c120a1d0c0109120209010509091f09020f01020606150a050f1602030106060f0c15020d1407030c05 73
    0x151070407921204000020700141c0c2e0364900442420b4200009205941c0c60380360340c540540c00311a0840000310b03654820b0300780100120340300050313940c02807609109000702d800458840111600c610814001d5140240024900c1e200521460720b84141680c1c440d85001c00d1036803209200d502c6641072001140401c00b50071980340c22610b840e240d248008196854406208001f401c4e045000051005118a00292840001281d441c140380c00d1341c1380b034011511800003409012440718003c0d000803100c00180940d14100404a5000b510001200d05000701c0c5460058180d544101114900340d131103c03030f0301c03e50501144602c0019000e000510844c249080071900b07142c5060503034085940d000c0341800084d8829000c90b4900c8440c0b202203a2219070303e42e1022404024808201e200303601e4041e0004445018a030502942038003034440452481c8c1d02d440742501030703821200d443c445560821078244034040f18410b6141c0101d050616100c0d91410210140844403100e040e80306002081c06041c02130610300c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 430324577 1250 430323327 430323347
    0xd020415270504020f040e07080103110a031e0503090a0605040e0a0614010e040204081b040c0806030607080406091502030a0c030257101b0c11120c0103110a 69
    0x3e80300140d5030300c05404440c242d40038540100d1280300700b407c284400240c0c420342103410303a40035580d103200f400c2c0d11104000300c0c0203c0388002031035450f440c04140c4036440200c04000140d40640140c0b4501042d9000254800381d80da0010008260301140034424503005101d0190301c40303180e88040040c0c6003842440a04012119801810064803000c03141271a02d698040c1e40060071303144110b413204c251281104540c120950309290040e82740502c3e200c81184522540c0d401803801030b02a10081d101c080e401c40c2c8000c4020420340351035440e80103040004682c00111071844948a81c0180c0720300305554058140c80c5256420400c05005210a545104010000d8040c0301d410100158561103142c120084000105500d0802194021161180c4d060381c8203039101201e8203201926048201414a4400c59030840c110412441c2c407004980070050081c00c1045c0c0711805900c4810303503214a0300002c0d5003220701c00501e201581200490711034550301402803000917041200f10504122144400420201170303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 430325827 1250 430324577 430324579
    0xc030c150a020a0501180302151512191a090703050d0302071b0306060314030a0801030803041401360b0a1e0c0519080f0415020d0204152705 62
    0x24122941c82e000b00b20300c03510113a0000003406080e18611012000d890440300503009401000740071003038400d056a40030710820100d8156841001030400340504404d100f83e18500c9417046441142c0c0584091800138002e512521f030f03030640380c0000501d14071380030b9019080c4a400c2e80880b00500001d14046071001a504080c0360060720781000c1d0419404028a00300d0b00070329852401804018860b8641042055a006e83d40340018165200859640d0344100e00042d0005917000303006000080031940107503005070050024110014181c4001421110161000d800c4551192a0035155458852145943d000b00480e805510b403076986645407e9000182416103540ea9821600d00c800440c0c0401d10005181c02c204003c00d00f40240c001d480c90703000f81110045e182011142d216401d1046804c184120342076103901e022521150b41c0c41e10210b43c210161482a5002d001840d49801d4520161001307051150828043d20720f00e56003d0458168400b80c0445501080e521081d4161447d00c0c8208443d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 430327077 1250 430325827 430325869
    0x91406270c010f081909050d080c030903031506091309110406051c0302011508060a0f0203090a120509150301141507032102030405100b03191e080304030903050c030c 73
    0x10b5000d404505c03c40000d0f0160541601d00304880090180006000c00711000036210302d1180e0b140e600c0d40c2802c40c0400c40c7d241546901c20400101d442d0341c41c1e00808080403002e0085420460311100142c1d040da2209416104240e44d001d0200c10300202c20b11041481c4820b440030030410342008042004060002d500c160200041e41400c41014400d5200010071417000c02801038054545603400d803510300680d031400c407079401c08580b01c00d0400940b0880e802039005400a1001001556401032200c00000340d044c00e2100c244080c1c50fa40d12a445a240007850341001d0035504d6041c540b510a620900f00695405400000305d003000306807041040340c1c1e007150141010884902c604036440452409002d107100894008414401088000140b07516070038510042801001c40d02420300d03a07654424040c044801d03134043c1c02c00000c40d950003084840d100340706003894003d140d06c0d1a03030b02e820381c01550224009840703028200140300d01400b084c0e1200e0000c501601c1880c0607000000d40c28004103c0c2e9400b150303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 430328327 1250 430327077 430327081
    0x210f031517030d063f1202120c07050102100b15130302030a0803091c081f0506070507050a060507050706110a05010f1d120d091406270c010f08 63
    0x21400300150f030240c50814409006050301d6401507402c08848540c0040840d1280c40c15000584104d0802c07060305400c1c0d03045441920041c0c8801b04e0300130040d05c0b80c900f5805075900b0003030301ca00c45500500c0c25900a800a14143d413511000a02d40144c41500c1c0751041c0c0340940d003250f40e44c0c400c0c44035240350300b09915181c1c5031000200e4038110310603160f1000303605100d00f084500c03c12451030082c6116070502810344074441c0903500b913003c0190180c80000300103654080080d10844c0d90103408a4415555070f01c1043e050344400204801390702164084e6500c0e407001c4020016880c00032001806014503240490511221303540c1d0a07500d01d00c0c0d0140c042032211030100e030103c1c0c1c402009004401c40d0800c000b84502d04419410300300500f603194001044200405420a80ca4400030b080a510400340c220341d8941a1040c00d680020303c1040000c9030f0360f01c8039001c0703101d82540800410b4050b010b004520075140685070350f1243c101200400b240341e02d4029042c50250340e0b03000a0f009207100e03082d0900166603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 430329577 1250 430328327 430328369
    0x5042303041212020f03070f170304020d03050a030b030a0f0c17100519140709060e0102060f0c1603080924060405150d05010501080d23070c03210f0315 67
    0x3040850310a03948506c004103540007404040740c02ca81016004074002d54140c0ca50803c0d0406900c0101c801940040d11000d1601c0004d01c140018840c400f020f1500060501e03a1170700003424541d082c84190750305045003200406100c5000c480701c00070031201c0006e5114400d00c0c05034582300c0144001c8400c00c1070b9203100103644c00b50141315540203040300c81d03000c000c1c0c2c03000300d644820200401e440c0303540060070711800840c03e03600517400b07080c4082058008007410741e0b40e01c0b4400b1001c10700818840a00d00148000aa201601c0e4802d2406a1098556072018940340014a1401d00019030000c58900c2c405a00d1402a00e40e4880c01d0b04101b040e580410303269107150700981000e00200d84c0a80128170001e010b01400810350150741600e6465041d5950300d94101c008444440d920b61048101c0041c0180211411920030000c201192049241744140e50b81c03520789164070f0140d101c1205d51400103c0c0c042d10041e134058045001154a8181040b60b045c20002003201f03100e103401441114441045c0078000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 430330827 1250 430329577 430329583
    0x20f01061401210b1c060f060605040512010603050f07170a0803040305090a0302031b01091403120d09060203070c12140405010f03112a01050c07060b0f03010504230304121202 77
    0x1211070003a011044160558641714942c1c0890074003600c07504d103845074040718150b950007004110313004c0e5a58a810941400208000000b00c08a5940690340e5050000006241804610a41034900001d03007207040c50301d0f0510500b002d242c844820302d5041002807000149840b000da03500590180746c0540c0711403c81c004245100382c030380c2000c0d525115400b51007401603030060049a22420a0b600d0000f515a16400020480710025030039605802904c0c1c4802040054000b80c94146001c4002044110700bd4880400301d9000780d4003007000540a40000080c04000020800c4a504615000c480f5183e40c0d2501c0c11503000341c0c041d141c10801740e020002c06a40c829080707100f90803d01a2700d1655030000d0346001c2e041005a1440300a41d001150141c2c00d09081841f40a00c50088084818508142da503a4a0024034a0a0a103a030101d40300c0c1017211991400d2088511451149030069003190405901d14148d00904540b0500c43c0d01c100400d0140130a0948600c0400d80e102810b0071040e02c0c1d5003400c0e41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 430332077 1250 430330827 430330841
    0x50f041419081809060a050d0807211103120708090f01020c03030f090a03050901030c030e2a0604050d0b0c0f0a05130605070f020f040e0d020f0106140121 68
    0x500d41c81040346414800b01900a10450031015080034054502000b4058007100403141282e02c07181d20399040025040c41000d01c0304440c400d02c0c10602d44a51036031b8481807080340c0c00030801c0c0034600c2d140b121324141c0c2140000040100c20401941000881d6800e1014854000d0000d81001040800b140c0120350410a48440c68100002592502000c0040035603d07003041318100304070f050000c0403454841c1d010844415003500350b6034251400200c0001034000e05900c064035420107586051480c1d02034004e00c4004940c030b030320b60386a00c907101c1c11005a8626031450a813841c81864100300401c00750783e07032807180c20348241e002000c0100c2d940d84c9004034007240903400c0c02c0d0258030300004500040d150300c04000c000110180306002d0181e80c803440c0803030f030394024101d0041002409a1001001d840c0ca4480d1440000380184040794980c0014a080d040014050388103025031700c43c4080c81113020b02030055001402442d00c6038444040d003400000d01d25852540c411140800c180300c003041400311034000c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 430333327 1250 430332077 430332103
    0xe01180b060d021c0b0603090a0602091f020c03010b150d091505070908060c040308040b03060a0801020a05090918070501080703180305030402040e01060b1911150402090109050f0414 80
    0x42d03c0e00d820201e0031010344d0881143c00007081c42e1410351003d40c070346442580e004042c248003c120703200240d5200703c0290700c00400300368004550050050207400765000d0340b1810046502038045a404001890b0a4503054102c1620030102180043e410581440c29030300394920141001c00c1c010900e04044080c0c0040403400781d6494203200401010f5500460003108403503510049400c155114440c41031140503e0000900204080004108a162143c0516003200000701080ba0550340c1301a41822a40061480808207401180b200034074903000750a25072040c14138607d01d03440445083c4080c0c80e02c1250003101d051001c0326000c030b00014442d41c841d40800c003003d8040600c0444a050145c041d800c01c8600b240b24900303215a0390020041805200203e03908010b0301410845906c802c8111010b00d009540b0400113000c00c07901c03242104004040f0701410320280140d040c2418018040907400c140c12001c0300c28104805d0141d0f44441091041c0d005410981c0b104000c46001422030030140061022 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 430334577 1250 430333327 430333331
    0xe0d050109050609160302090c0d0c03050106020c0a08030f032505070204180b060906030f06010e010906050108010f2601021b0610140d080913020c0105010e01180b060d 74
    0x5081240560245949034002c0c801c4030307203036920340030080e070b40d4a0901d20524020076080c50410042c20708003a03541e0050980e000541c2090f8624460404458287c0c510b04002902d620041000369010302c031b81505890f09071480710085042c4950940c0d42e1203058010100c0c1c0b0350003c0090600c1001e0760390200200103d183e07103e2501d076220401041c641051000340e04c0769152860051000d0304608c404912250b001c1c650300015500c08040150070703c0020200342d05801024174640440310280301690207400701c500c2d101015410a5044c104840b41398124505100c100d01c01484040606200c51007111505a5201c410800122000030044020306d4104000d40c00071402d100e42410b00003054007103c08100491307005039110b403001030340c0c07019901c2900c1c0503509140c070366641400d0450a00001600640c581c42c03420706810041001500c683c2ea07c8800c0d15404140c02c10101028016240140940300c0711124650400100007400c19403036030208030301941d0b0b408102c1070b9203c410941d0000640000d013 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 430335827 1250 430334577 430334599
    0x6120307031e030b030f0124080615060c070e011802040b0f03091905011e0b01090603020f13080312150108060402130f060302040e0105060a1b1b030819080103020f100e 74
    0x5501c1c003230140d140707802032a104821918003020040061440c21031b5240c034010300e020b840c0c1d05034000e1001e42c0301101e5500410104403040401e10104046c100074200d42c00c1e0a01b1f650b151180415140020544400d02c06e030040000700003500303454040d611510155070320269640c44e42d54a00e80360800c00d0104904940c00c2c50421820b0080c10342c450345040010104882c444000c9071a04002c0341e240c1c01078030340230a6401205100f41c80c46a8090000041d03020091481c0001146440d14070b2502a8031400240e0f00001e0b03070765030204030010075941094641c085030340131503141c0c40060003218009010900171070b404640e910800c1010346000000b80081c14505081e142c80e040000c02075402402101e90708131060b00000742e9410044110b40108038180d403035160403942c0ea000c0f20104007044001399101c01555a04807001400038000000441c81401010f554111901c0c007540c1231b041802540e0184450300004001607216403001542d105030445800718102d0102009a80c081070300c1d0841e40d082180240 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 430337077 1250 430335827 430335853
    0x1211011a0907030b150d060b03131202060108071401021c08010918050c1908060c070b09010c02070603200310080105010f0f1404020904050f06120307031e030b03 71
    0x320030400303410159051080750740ca080b020b50650798480060394001507814517003420012140003501206080e20004140f0383e80e02c000ca110643c00980d45690600003d0f05c812041080b082079400000506001821843d03140044031900c400d818410702c5150f56550403910171a80c824410f84c449031008000300b102c400005100202070450034042c3e0000300d481c04000040c3c41d82d00c41d8480c80c5055000c80144040c02d142d60a01500710105010001981d4003003602103131940060100f1449040c883c21866140c024900348441c0020703014000400c5640f61044400c2c60540c08126082500d02c035080101340344128405240f68484000c02c0000040c0d000700900150200800500b01124040f8000340050390301d84e41c0841c140409440f43e01d02d8100d04e03c200f0040940107010940c40705030f00030300050400700700784040f034103079101141d00780507513602c1c0800c020640ca0502034214886890700001c605109450754082c1003090494a1009522501d4000d0043c0b40c1c4660030030003c1c071030302900f640c0d92042d5000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 430338327 1250 430337077 430337111
    0x605090601050a080a080316020115030818090f16050d1d1b2d04180506070f02030f070c0b0705030a1409060702010518220b030d0c121101 61
    0x700030300c3e01c42c901c0600d0014400c50300090803078100d03820404503031560721400384040300c0d186004402c0b002e55490b01e06001d62070b80c1c01031164006600808120b65a01d185990000030700b17941d880350510a805600511883d185003012082d40f02410311070400c0640280740c826100c50141c8107980310100d0400351226109414104200110aa05000c541c042d15003600702c01c1c004d503282881550012510b50a1404080c0c1a1188400303030f003080720f06800c14400c154041815108119094690211240c0261003004010000d1a0740305c402880c0012500e42e03402c800a40360311824403c8481248003041c210103100040c18020300030602c01c01001d980c0d031342038501f10340c6075003100e41c66001103004403040340043e11800046a82c2240000e0442c0c0c038048180e03005440607002001c040300c008141c14100901500c50040c05108002c0400b800912070200311035280580e00b402020074000d4010001e880035a03500881d54500d6a580000300080da0800c2c01411a4000095921200c0f158205000003da45240e0307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 430339577 1250 430338327 430338329
    0x100204060e030102040302150703180b0a020c330c0d031e0e0c0114090409080c07050f06190c060c0305072703081303020d11031501030804030305030c070605090601 72
    0x158a40348070310100041094200d000318031020307403c10f40c1800c00c00d00c11240c68004002c598800c0c240407100344004010780c01c11911b10741150741c0030b410026005007040d030100480382448408841000b4007040900d611449546285841c000440d8944000e10401800c3c0068829a150207000c0b2560810980402005000c1c0030036401d08446103844101c1c1c14047c14021443c501c01e80400501c03105800b074004540c241c06440002071395a400f4000001d4076a0b0340d020f00b48400d409040d44030740f0b40d00c5400126050402a602551007500c40000300351158031440301351410308a11880454084400040545407100f0008004044514101c500d04603141c0552241c0e014440e2591607000030440400840c0780d4031070100000083d40ea004400300000f955080040a604e07100d00004104141d0b2640030134600074500700b045500c0c0d09038074502c0380b0a0800300b001a519035100d0b28004481d502d0f50312342909910407404003030b00b002400800588c0030711606007200e0545a009104005600e45003040c01e0300c446007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 430340827 1250 430339577 430339589
    0x50d030f110a05010e16120f0b0c0d150807080106081e010b030303040309030b220605100f060804050c100c061518090302060f07050a210914060916060804030c0203100204 75
    0x2005101003002e0b01b60100303421f801d541c0128501c0000f00c10781c51340480d43e0310040c80701c1d0b9070b030004004882c007014860041d00c801d4821b441d003900082e81801d4001d820122030390031426a03680341060412014100054030705140750071046000c40b000c1c01140041c00740001e40c032025003600c00041400201644203040c0400c07280100244000350b00c07807038074101d2201c0c40c0800300082c164002140d00049402580240d80065400129046141e070b680b80300e049030b50496000c40302152040d070421043c13005c28448990450b40440c3c801e21200b203c5840640250000e141c05413040303039a0820032603281c02d400201805040740c0f5516904025025842c107000c1d02c2d4008048005000342000300d41d010016081c10bd02500c003a441d101d090080000e0215003034041511500c150641c05000300e07030071402911440252a019a5900020503001c20340c0d0f5240800c041c085110720740c03140784c4103940f2200300200d1700e05a0b0440c3c030b040b030311940351800c3c121b8105803801406036140c00b842551550150050f4004c10031184 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 430342077 1250 430340827 430340863
    0x303071e110405040b0402130603061a0a080706091e050a30020603130206040902030901150b0a08160203070c08031801050408030d0c14070b10050d030f110a05010e 72
    0x441c0c0080c441515016500144440c08600101d4010b20380f00705c4d0124800d108900004104e41d99849400580d5418804000c0620100f40d001b200d509140034610701070860715005101452030b154000f481c50015200d004202e203044802c04400315000103800700144800cc0010120948450f2212440d25851808000c03401928811400720080d020444550b1500140281d0460352009484038040030055000c03a40103100b0170011840b00024405103000e002c0c0c500000896000810b02d100d501841c980000d441d1880c20703c4600442c82e80402200d504c41c41462016109006584050f840c50150207401055441d00c840080f60303020001001d0802c03842102c006003081c050300001510280700d2400b404240343c0007013200d41d40c035511541014010041514003010b00801c00940c00c00d50b90407241c030031160300c40b1600078404c0075082007030042c02911080391304000c3c030107a07950082e00c5070034100701d5107041c89000b6040c1034042405224030080745030084020b02404110581c01c0f5111171004400354170800d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 430343327 1250 430342077 430342103
    0x2151e09150103060c11031602032a0112181202010f0207030504030605070215010b1207030513020904110d05070f06020f0a03051c020c030316030e15060303071e 71
    0x1440095440100c8180004009031a421621418040e142540200050080952544801c42802c00048c214101045901c0c910411584101410000b80e00110b07041c81c4030008500b809018480e03001307010721109090840401ccc411480c044060104a504a110307000d49800560a0010071040c26208200c6580200086a60002e15100724000d501000d000100b050000f8400981c26520464001c002401207030500c080c24140402d43e894260031441a412010901e00e030f4581c101e450154001c0a80d0505201c0d61401528000c05420b240750064400c080f460b004c941840308500d0004a000c0c000381c103d072003100e010b007450390381c2d4580352040d90000310a179440011180e20105401902c881141e000d486000581c1d1811200c64200d0307880d400020440b43c2000a62a4440c80104540c0603100301558891406c0c0e0b001c58a48031654034090b0902d400c0c440d04034100742c0081555074420405c03155603402c944030100803d1840c003604400074515074035141c072052040100039186e41c0c52403054238501d441d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 430344577 1250 430343327 430343341
    0x1505040e0c01050706060b0325050405010834110601080312010303050d1104060306090f0e03030106050a140a0809060901090302100f330504090c0605070302151e 71
    0x200c4003481540600d4000c12441c140540c0b080c0c1c02015040e0003844041201ca8540d00386000d541d009031000007110b0151000b0284280c082c407442c048103506402c18905240c03614002911482005022802c01000000c4581c050052074022100341d10040c0080444944201c1014000c007020b0303940000148034020000408080020498100e8003c0c4200650f030b82c0d01e03540d01925281c10490450540c281c50300c2160020503803180c080c20081ca59594041510b03480c04886104070369401c2c000490304ca0400c1e10400440900008890440d410340c60419540c2074480c0c802c50f1207840b44003c5484505000450202c03407a84a02e005006801c0c0343c1c20746c0c041d038840600460072200385060050160300644150551300416074041901d241d907000c00401d0420400708007503040041007540342100b0402c3c9211003009004140c000f009006c090b60100950902600ca90086000302e100711070410200190480c1094800d109103194150038000340a51801d040100b11403100245003c3c80c12002844002555 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 430345827 1250 430344577 430344581
    0x60c06040c18290d0b0901060e160906050c010209060301180c1b0f02010e09180106050109081504031106070206150d120807020115080309150f12100b0d150504 70
    0x70000154441c41c0c600c1c140840024100801d4183c070a0340b01c42815183ca01041c03c0c4002a44100103c000000304281082542130401303501510068444900200350b0103619008040242580e405003001500c03144080c490b140648202c2c4a81c603040000071000280c5846220400501c1c80a802c50900924008080455608102640c400305a42c43c00080c0d0b0045920745004d4100d13640107143c030701d18104500002c11450031040e20014071207c6e111101e214108000e2160b1004ac0c28240f90911025103480b001540e64510384c405407024400020118040500800a44000040342c4051f01e40364940040b01940f03402c000c440b1412190f8010010f08107900e481e6000414440d4000c3d8071641a80c4090012141e08400034004c3c4190b40d40c4400074007014000720b64080051103050001d5a94905040610882c0c0380c040b0700c0070360614000d10107030b03000e001c3e40425144d0100101c2c4070080e180d0b0311104d03e50a00d10361984400980040010f40b00c501303200301e0300210b45d464803084540c1d20103503440044c482 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 430347077 1250 430345827 430345841
    0x1306030e0705010c0c090902030c040e1c02240a020d14101e03030c2f120102040803031b1306030203060f220209041401060c02010810060503070e060c06040c18 70
    0x2001708403031581448080c0c655402040000d0000e0100c8586019600201d402c403040502105280e42c00380c401812504140701100b54003000f1413025024100c41d03d034501090036200319100d81c0ca49030040c0091a1059541c0c180d03a1940c0801009202c0b80a0b2142c11600c0c0346070540c0c3c510b0160350002030100e40d8150b1210800d06415104541e03482d130b185983c5080b58000d005020849545543d81030307801c10000303078442c00d008182c00c1c01d0b004824070040b00200200e1425002d0071124690062008200550010064907841590501c4041c0e012668600040c180d11500001d01c4d0345100b04940843c580e03a066001e035118030340940e12032505010b00000c00c50b003400c00d40480c1d05203040d2042000084291a0064400bd100c003030300c0401c070a10000346100300309009030072400000c2c404410603000d542c0d00000080c0c00982d21048a4111410004002d1203440b004048074103201e4607000b03000d240e80710103003140d0039004c004055a96504240ca0143d030018442c0c072444a90080741e0303940c08080744061041e65 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 430348327 1250 430347077 430347083
    0xb16030e030a052b0c0e040b21070810050f011e030201030c1103070b0a11030412050304171b07060513090510030209010303020a05010c0e0d0b0c1306030e0705010c 72
    0x25007400c40c00c2c14111082d62103252401c0302c943e16141c2c644000c510794500280f81c442010004100d060030709000a020341c11000999205038208000840141c60710480421a64080d403504003155403190850b03490600181c2c04440944039111341c51042652680c8018080c0031528814113490340c1c1d56000b01c0104c00d509105540007510100c003000198025800070110550b68100320a105001c00c0e0300a00b190026602500d07509200c0082000400980c454985800c415808a60030341c101903c0d040303914143c6d40d03412018000000301160501c100001514429588030305041d41c1c40c2e2040105099100340440c41440c18800c0034001700301c49008809a6408807540004000744038542440030014080c0680b040d40260480d9602001589901010318041e40c003e800400ca180f01503d492402c5440c0400f2401c200098690025060b590b079004194040d034025102a4403a2a843c00c050401d202c0e442c0c10303000c00c480e0307038a000409a80681064828961307813010780303c00c9540c40006482c130752410780000b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 430349577 1250 430348327 430348333
    0xa0201060519063011041511030d050402030109080315030c010504140f0d0f0b0f0a060b0f0a03290a0906081903031e2a0806060c010908070b16030e 65
    0x21072042215442400820f07401d140701450013262a0351090308460100109503440034000805000800010000088119051514404c030741034082a180e00d034020700d8a004511500c031000704056540c01d41140611582007001c0590b81d040800001c040703100380511843c042d00480c8000c903160760044090718110384140724100d440c510030314100100201c3c5000d285a10400c0c0090660114885e6451405050f1151810b42081e0070483c83e003140d9441c00070044035442e07007001006d21400b400801a140722440c80351545031501c01407101500034201080804140000640b00c409990303410800c0d02d404098256132645e00280c03100c03180000d5034024082d4154550283c40c410781417025445500402034080e25000541c129450a0b070450a514401404041034a030103012001183c1c010917003510110001c1515140311560340007920381070004102038800d40c00400c501c041c42500307400c00c0300042d81c840d201c00c0e40c0f500303245460610300300d00356640e6103a41c00e24981c020940b40240304000c401c0c0c003c1001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 430350827 1250 430349577 430349597
    0xb031608070c020f120f0109060c1b12030207080c06070e010f0504080c061e04140f0d0b0601030f0209040f020a020609300d1805010b030d051206060403080a020106051906 75
    0x900050356003101405c40280328a5036444002c032801e104c1d801d40c5503c142400320b10006407182c0103140d94401e82444091400324554070001400d40303520510340070003500780961221504d0810b12024014180003000d180181d00800c03450300e5000e105c0c0015042d003605e5400c003a24850608850303038040c4e806260304a601c084070b90509454200003030120b042013258030884c00304805000540c1e58201d980410184509194044814540706283c07202826080e40c1e04181c0000e03c0c1c40d11a4101c0c8040c0c03955040c9030f51422409054460790f011502000400380c0240000c21121100344020751008207150b006001d000045091403030081032308230b01c90300016408030101c90a4076030003d05484011070724050748000c00c148050821640103001e4413403e4080070500a0800381000303400d51b40302d0404e80c0c0c401e410140c2241c0030b081d00801510303090b405084100001d07a4031400495043e1049400143c500031021400000040d815048942954030030742b06105264000c40b29080c14044600806001c00c1c01d91103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 430352077 1250 430350827 430350829
    0x60405160e01050d05030903030c061501030218040504080d0213050405010e010b03150613120512090307090b0307050405040b10060305011202060a20071a032a040b031608070c020f 79
    0x10f0700d0060b1401801a47d00d0220fa40001038995440078504881e550000000c200520241ca00d5a200c900e00c282403d6203041030030700c0052908940b501d11140301302d569401107018040880142e442c012000c2600b1544c807610003008031100d0035644100f52045003888004980c00410821040c101c0f480b02010ba415a2070703049250040d50400b441e0b10350411800d210908800300741074100d500a00380b0032003021091000b400d00e5410080e040100f1503502074100400079a9407000500c140442d486034100044400500c00041d05002203a0300080c1c0c000d08041c140410f200a01d1038803802590388035410301c0e00590341c10058003610001d100d4144080711440844015080c06402800d210b0210700d030040c5080e8101c0b480b03200c000032040c170201c0d00f54001031040c0980d00b410034400340d40e5204c0488180c25460005000000d87c8250720340120310381e0341350900542c2c0c82a040705840150500301d40c0d103a124608541d000c0203180007a506c071750002d8000000f040c0c500c0d010382402c207000c0750050701c41041c4480400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 430353327 1250 430352077 430352089
    0x50c040803030c0d0207080708030601110d082d07021f060510050904090501241202090604090507080d02340b0309070518040204060602060c030103260c060405160e0105 74
    0x30300203c10145d001c0250800285101c001809428030541c4c6a5480c1e050200006100816112070040950701c5002210203050308800703d140e0042c1c1140500900c0440d408034804800c0e42c01007600d01020f000010b02500301d401041c8800c4020b50100924220f5480070001d005403281071054942203041240314800302c2d40309078020960f140002c2c101140640c010756a42c0d0840d000d03c400c1c4494411290389030b04488000d082d8000040c240090069a809065000589909406450180b04a5442c0c03103036420444140210700040c081d403019240d0140351a04042e45072a40c031401c1c1074104885000001c40c0c1500003030401206512080071003446418610610065030010f0991401841040000160f03584c0d0808080112991121080450304051043c00280c911a40003030040d900710380200b040030b201e41c0e819681100e0f003105375400b00550300c4000510307200c0200b0820b5036507030001801d80500680000c0040c080d40c0b08404950140031091012021801d4900500b00040302403c0100031601e805 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 430354577 1250 430353327 430353337
    0xf180204030b04030e090603030906030609040323070203010606110c01030f2403050c01020d020d050a231309151802090d0c0905090a0804060315090f020409050c040803030c 76
    0x10000103140540340d4507542154182120218002480c0e80400c0c41c841c240f010206804c084290015802e05642200041d42400014492030180703606800180a06210341c922407000d400c5c007220407846807400c2000d07040c41e5102640a0703007e9030800e000040d16512814004c0600158a0058104801102e00440c046d010302d4241280c800d03100d5041c014108001140030350000410b2001002141ca180750060505580341c4406041d504151000303840142c021480340714100d4185002c0d40d5688648200f5207101d980c0c001e80c45c20400d25100d040c2d003010000001030100c4012000442100d540d5045000290340d04000d0308000c00303000d440c040100325400e449200c07100ea83c406000d07081020792b20110b46540303041001a52440b41c41c41c0b041007000361034410705400c6030205000d4144440c89444900991080384603550415545a84135660701403d43c00030b03405803e004100303110884440505601a4015000f1800c41c240b800020418079400c0504842c1207aa00901950071981c0c1c94030880c2094100e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 430355827 1250 430354577 430354619
    0x20c010c0c2702030118140c250501092003010902010e040e0f100209010f030c0e060c03091201051519030b091207050d0f0c020d0b1b04090605010e01020303010f 71
    0x540306903441e140040c006180641559a001b440709290700100d402507506441d8210031080001041c041421200c000701c46201c0030115011480440017401d0b05170000310010040c0c019445c00c030000c0b040154144c0500110001070000d080029415001c140c00c030707800c1c0039000340442c40c080e50041160502c0d41021400c00e8890f030544080030144132582c2c2c00c2c803011a0005003c9a400642569590f8000d041180d5260040c03400f080380c4410018003030000074502106074468a8040303140c601e4a035080045480440d0003808540b19440354210071806454240d890302c2200c0d00105140f141414688407038410050004410a149891615080d4102c040a0110300d010b0146e0013502c1e130700c500030700c000f07141d001e108900900c00f0094014000b40441520a217a07010848078180c03140c0542e440d041c1484c04907412030032120668950380400c91400d182151501245140400c0016003e502c07680b0450840e282a00d600b0015142d24004a84903c000d0140d803203c180782d00001e000d0300310480040f05000390 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 430357077 1250 430355827 430355879
    0x110a030203150105010f090b0304080d0f02120603010615020604080c070f061d100f08060f0411070203150f040b0403120207050610080c0102190614090d020c010c0c 72
    0x9200c0d004a4141a000c1559405142c1020b00400095901200300040e541d01ca03d070010410342496410f441d54400904080e00d1200007007880441c80110760b00c1120051640c41d000c550f034011114a45284000c00c0720154403039440c0440c00241589402041d50759100e03aa400b0702000c1ea1180e954450710780244010100c175215500e00031070b0420510081e18094000b03500c41c09003d01800b99404070f4000c549480c0b600079920034a00b4840316810408582a6510f907003030006650303440070b02154206240445082d40581815150a200c1000740c00a00200b8000d0302a01d08111540e0180c800c059003e551002e40e0002020026000c00d10903021640c000c1d10030320b081105035020004000c01d030b0300f03c4132041c0e81c640c001d20f0501c901031199106580c014400e04014041385c10500300043d4580040344882c450348120414010100700441d4480089904c45640c0c607441c0d828048010303a0385143c60140c5402512901c0030811156001d03003551030b5925403049aa144082c01c00311a40840d0314500419030341a2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 430358327 1250 430357077 430357079
    0x120105060d080304110a08100b180c030405251d1b070c0312200c010210021806070c030302120403020d030c050a020d06151d060f01120204060f031413110a 68
    0x186da401d60900050581e880104000c4075600c41d400300700c809407c10030740309640e8112160095960210b401e94400c011001c0b0b01d0712a522424041e08000e02002110010030448001d20700c2c81000602d0780003a1000b29044a02c00012080a04c1141c60152003140465012400c070030750405444c80200041c80c4240070038898190f030ba55400070120f01000103031006c14102040c10098141c0b005401c1d041c0d079152070080440341d42400000c0d481e030611041001440781c0004050f03178400c03021f240304c4030701c240042c01c11982c0b0f10307142c00d0a140300340c4980022001402129a007003032031462031003074409481e00140360101d1380c50656001d45107099020b0f000c407564011549854007680d50002042d002034054400800c00300004456409162459040550540348050040034108428041c2941c0a541030b0340000c2d49591860041c6c0d0500441e0300f440b0551030000601103081607001800180000b82c07510107001700c421344d2801207404c9604507900f050a004005195001c40d0300c03548104605100a40222009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 430359577 1250 430358327 430358329
    0x60427050a020306041803120b010903020d06090c05010801030c120312140402010e0102011e11090303040b0a080c091309030521160305040201021e010617010b120105060d08030411 79
    0x1441049a034201c0159000c010071016042a001c3c440d10200300c08030010701c0040c40e5801405032007100d10072443c8195110314100d40d070f07401481d0744000f80d03800810f0000c4288062800708050b0035001012500030425000c0005c1e03a50007140240d043e25407046140d1301c502e08081c1c4480865015013425805c0005001b151405c1d40628845c0c0740c860502c0003600040c0b803815000141200100d01c00c454116850010b43c1142200c8c9004a1294280c41100201e1030b9155200b501d860b03030103005140d80d4035000015002404181c041e004040e103240c0c0780c490030416900c00004100c540030f01031405811840322156401c48060341e5005658091003401c0c04d6082010711040c0fa0740001e001219106d460210105002d0214148400a03102150600c1c060019281c19030000f500e45414815491301d00b2000b05a40007040000e4101c1c50142140c041c1400b070a0405c03200c540e02a100c41e040345402445014009003034603a040c018680f2070314000e08012082012031792030f250694001441510320003100981c034405 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 430360827 1250 430359577 430359581
    0x9070f03060f0311040b0102031e03060a0815011a0306010801090b0d0606061725050c030712080f060a0303140a091a120f090706031d07030b0123060427 67
    0x81c40c010300091040d501360340240411560504006130541d4014016442c0784040014482c40403c03461040b43e03180d4071044c0116220710003075080074025024500c0d0381d20036424400c45090494080b000100441e07401e26019035000d10095030580e00080d8000d0040c800c0d2030f926089484032200c00307401c09a58901303d403129012100b4a8218038009110184c3c0c44421900c55426035401442c2c0c0d81402410a52540b10b1410f6a419400140184100803c1031422054140283c400c40d540001120b01e038284503107802402420102d41c010440300c1c0d0000406c1150a02c041110152270349900c8923022107205041481c0303940c003c4903244042205902001c2641052610099040100c800d140342e03d450182e0001c40741c00200410a500c030121540410940f0040002e440040f18024100001d41507440c0b070000300090b400e20101800b074410000008100402000c860b4101ca1408402211074100700d10018030409400d0746456000e58288028000051510f00450400201c0c95400382840e0600c810401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 430362077 1250 430360827 430360829
    0x7050d0b0d0b0f0712020414151303050304090f330b0d050f060d0b0f0403050c16060f05130311120d1e111f111c060e0609070f03060f 59
    0xc02c0c03483c0501400401504040003090b40881d0b26411740c14141481606010000c031040321500c100d10701a41d20700c1d94140c000850303110291702864400e0031600e80c10300582d241c0c094030540c1c48a40c689081518090054032819484214500d00683c400e481920070105840145115101c2803129940001e01d664803c002415101d007034007400b1800d03107030021140d0000c500081083c0d000380806a5400b00241c920410301c0d90107880c0d251446501d40b2a070408131458010203680401a20548c1e06080c840040d608004045039045c0d030310000f00140a14048925004404c0c1010110842d120305000086041c4603698042c880940a1040c089410824520f0001c00c50b03421408203500051607125100042e81180303410700142404680180103400040e0fa9010710714074417524203141c01030503a041c03010342c118185029400c04001e403600d003000101d40f101c800a00411602e2468800d00041d1451000c403040e01c1103100400080080d911b6100070764500540c0314080081503560003002c605000d10b184070300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 430363327 1250 430362077 430362091
    0x4080a1406010e010e01440c04021806090d0204090c150215070f0309080a12050609040503030402013902011808250506030106080906070807050d0b0d0b 67
    0x4100030300006211030404906801c000035a8410740d00620000c40809500360450384910340d00d9440b10020314103c0008880041284400150420111031036003101c03d41c0111003e52009449106140c2c02c01c02c003c03880380c607000724080010011888102d16010300034000300440a0078907250402c80f540000c044440000c400c403484082440305024a450681c072458a01045000030608640c1c00e108102182c0c20040c904030030800301c1544028130f03920a030025185d26500c480001d440d00b1001801500168402c0e00b24100d0134a8070000139001c2c0f0f0b00c196200e0089411401031880e64a95400455113040305000740d40801d6011000d05001042801a5455001c0340d0312541d00c160242d4030004040e101100808800d00854000622000d140403ca64144000341d0031482c20508040000032500e1000c1c3c1e10280d404100480001183d640204243d44116000c1c416111a83d480b090251031128064507840002402030040002c0f000c003952200000003c010105c81d04005c0c0350b540d44ca643c0104640803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 430364577 1250 430363327 430363343
    0x2070b0106090b070b01091806090303020405010f0918020901090807090b040b04020703091e17070302040606020313030204050a0f051e090109050a0b0c0c100e0d0e18040804080a 78
    0x108000d9610642e4040508800d0506501e01036550300c40e9000080b0600504017090747d50901015050b05c0c0344a03203140c5a038000c409000011013070802400035041807140e28080b510700c6404180d110b100d03840c050306031000100014110301440051304d000750000f1088078103102d10014003050b203820800507140104002c10020030713030705155414007042d140384807036581c00303180144140700004e80c10035109410f58141102c0c1241d20b41407005034a07001c00d80c41e17000301c0c1488103440803050114400f107130140030341c3d000351400d002d0301d542d480040365284075040141030003030a4080207200502e002e40000b500700501f0407001c2003000202c1d0600d801c031402643c20300e81c510a000107105402e0300d8462502d42c07040d0544001c02040540c0c2e1582a01d88103d90300049c405814900014402d244010554243e0440c01c0c04540c21400305000280007400c000e02c0044a80c030034a040c0c005007134070401c0ca88455040182031600b2a1040000880c0c09110240080700c411030188008215000e0030045e50b14036600585d01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 430365827 1250 430364577 430364579
    0x30804080a36050402040302060912011118180c180607020909030d1a060a0e030a0507261f090c0509130606090c020309010503040501060803041511070503120a0c020402070b01 77
    0x600400c0498503849603001d18010300c1b0400141e40c0b242e0503501120030a44da41541c105116007014010000320040d001d46040104102c40d8007448010341a002c0312042d1070303207040081c501c4003d20741020100d541540c00002000400c0c00c24080260301001402e001d06500e00740201c0d940001c001d00700c1258001c1841c3e00200303441c560f0380a10f015140c2091948802d414070580c01c80041050703407007014a04818420991303440100c076101007014603001c5401030241c490141c6c83d6107404000c90000c0e002c5824400d0062200168150f020034818282c0000c1a00741d00000404020280940484541a5000c064404002485845240d002407040703030700700302448440000f464050112403e80c0c0151200b80d21b003881d01900ca5400101301c80c040c0c0000d0800a84940e80c600c2c1c001c2c0501038542140085010202d0009000741080c440c5000d1005a901c031203082c0d082010000f50b03541c3e014810985e00d644401001c0a61003030075001008002c006141c0090745130701c143c005c0307010303079016080403210105e642c1c0c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 430367077 1250 430365827 430365917
    0x3030708061018260f0c0111010b03062706090c011211042105030a0305182b02031e0c010b0a03170d06030b040507090501060c030804080a 61
    0x80c028402c82103500f001d00c0d45002c0191100002e0800d402103001080c030101880ea03441c046466015056040d603400c60310420070000d001900c0ba1020000c05001c26561b80c6503104110060081c050b00340c0e805401003500f80d07600c40240d44094408410b1a4440f05583e0300740e404a8414042540b0840c03105000340328001c2030070b0004060200034829030420761f10340005180406e6480d401c03a012101e03a82e903100a40380c218800305009105d03240000b0154030000455000392078040d04903501c038040ca04682c607459260599000e84442600b079010605400c0c003c01c005104023203544604803035029104607400d04400002d000310100e5030088c5202c50090118501c81c03080ba09001d52804010300ba50311200051455503540c3e80d1515020481007c0240400c103010511055800f2100660300311214a1003410300742442e9449244500486199a08103400031a8150144401e680c0c06079265490804a948545602c81d0f150041c000e520100a00c0e500801c1c904e0522078100048240c003d035660000c186420 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 430368327 1250 430367077 430367089
    0x304030f141c05070e030601080d090b121f08010c02150a18030f210b03160506090402070f080f0423150d0f1d150c04051e030303070806 60
    0x34028503240340104411a49022140e2003490b1994158a010078140c59214040e2004c4181001c56900b44c4039100c000580a500020200176418103502d071501c4c3c050319901500060302c111401c1c45002190800824410302181c4828044900380700c0c0034081164a404140782540d0040305e400c0016070007a51480d10483c4082890364200550013030800024200c0107540108003007040024040c0688100381510f168001d0b801c1c000314001d0384441209000d45070072010f0060031b90410140c000d216012020f56204070b08415401514001400c02d07013003003050b070b00304000f83d0311034034085410603c02c110000010302c9c480b000d071841803c004800d0f070701c6034102505001505046c0c164000342d0642000c504c1001c1c1c0b510201a41650855010f542e941c0f0440300312403014008000084880ea40b416901c190310740b2440e01c80c01d101400905c1030320010b8640c0000c8102403841900c8110700c140c0b0130041000b452500303410703038035411050220707000002d4100030000b400c581044808101080048080100c0c0d49046 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 430369577 1250 430368327 430368347
    0x71d1e010906090e01050f220b01151e091202061c0e100b0f01200a030513061404121712040b060d1a0c0706060906091404050a020603070e060304030f 66
    0x410001c0000d4030300401e01e000d01c9440601207030541c0c0c4444c2041c0300c103020b62030312a000858012112401c6035035039070781e40200d0046000c2d012000640d030514440c0c4200507a1107001d4115115030340c003c20380c2d0900104801d04202898202d90290040021a0b103200c0105c10706603141000800000307a03d000704b0341282c00c000c1c0c0407a800030410721340032038a0740c9070f0340d84a40c044100d207003031900c3e460030400c100c90401c1c40031000c0c800e1021803140f030442004042c1e01800612116100c40d68142c0025501d081c1612091060100303140848030521043c0a1a00000c00720724002d801030854441e03081c81c3e20a02069035101c850028140b80c081d10800c0140b04c2c06000c2c444d00b001080d2442c4820ba000c0381c607044d0800d0640b00101051050400c04107a201007c001075401c1160005c07810840c01d561841003000401d00340c49003105503424112607840d081154060680300d16000710260580c68463303403c1019941c0000c010500780b05c0400080070241d01d810018520462194a03020301d44881c2d5000544040d8072 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 430370827 1250 430369577 430369601
    0x121404080a08250c0303091a1006090f03060e0705090c0301050901062f0c060d05040c06030924111602010e1e15070b2403071d1e01090609 61
    0xc02c0800c1e400c2072800750b030f04080c1440078035103a1280c80c8545000c40240850b10303000b51909010148001c40010940b4001d801003c8855181c4034042d940e0b901511909400c2c490750901004199003000421350310342200110700914030554000715280d40001d048208159440d411826001c030052106d030400007040f9015200381c4c2000d030210010449414680c28041401c2c00f01b2850415030144030002c10800245c40d440018001500ca40445c0d61200050104440030380b0f541c240e500000540900034070401d12504d40116104040001c001c110070f0403090144107100386903030b43c0c0a0b00e0000d00c6440002d0702007100b180d05200641902c60000500040341e480e01d4510503100e880c00c40c8600b8003040d1000b400d028059508071141110b806492086000f5a032000c2c1c0070203103440401450308040f00d1402c0348035032006580b42500411106141d40c0380200c0c09141c481c80000385100080011802c020782e40300c0f20703003911800c00c0c1420b46650000000280d0001007002e271500e4051000d800c4074003d548070104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 430372077 1250 430370827 430370851
    0x1416082a071a1320030106120c12030903021e060706021b07230102071205010608070f060f11030706111806090a030201080408130e010e0a0c0f121404080a08 69
    0x400b0140c01c0c03841e400c1c03803400800e0843d06041d0846004043c41240b5200c0a00070005c1180ea5682c072400035001e40102001c981c1c40d0366a400114100aea160250300c9056019070b20411018119806d001c01d5402155120a15400014106081d03940b81001054070760f2080c4800350b2100000b03e807440c00b00008101c0340c5a5a0040d800a004402d0421803444205104112a40424200c040140d0034071000d5004020103110010072403041c0403054010742d084480c004222841e0596a00c179070002c201c91400388400003007000c0381080b00d284c4901403204203007a5080690b0b1901d115036440b00e08032000044542d030403a1012a03d80c006002c0b12490000f4943d00351510b41c5003820610010750304ca0340601009040c421404007180038001d45d4015521415440c94101d1449500c541940b22205400d00c0380300a40008440020160125401182101e0050780c81707201000e00d943c442524016800000d000c04181d9450000164007144120b0324040c1c0e0040104964505019500401c0c01308014130200c40b0384 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 430373327 1250 430372077 430372081
    0xf0e090d020c0112020409090b1609150e01140a020105040c120203031e0f1303110609030319050c07061e2307020109030804090506041416082a071a 65
    0x5401040d0802c116400f440c00303000c43d6003c106800c00034001c682040809610345000441000b00b04006503004850385070b5074140342510800304441c4c1459a003e55081500f101400766401401109121300045050610310605008040c0c61182e6400600004d00140e441d041480240f0203150341c200301a200c41d07200e0300413810054012a0f940d1044002000441c5d0285840c00048068082a185c031010512407295481c1030504440c03c03581c2560006030380320a40b10300032a202e4036228007110b11861003e000745003003000c43e030504444026051031480170300c0820072001c50f0421041c45440003a0186031142c43c40d400c00c060415804600c140f401c3c90074860740c1315600c10324268880300002d941001c0215103075540704034801218150082e0340014640c02d0b0204001c2500022034111601c02e80c0169010015007800070f0070310054100c10f0711182041c0c598601021540d500c22030312154050682c010500c001401155141d000c000e00151101e00c0c000045030200810003242842c0210f0000c1e054204494 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 430374577 1250 430373327 430373353
    0xc040515030703020114191d2205130203190b060a240c020409060e0105310f0206030a0e0d02030408070e0a1404050601090b030105090d0516050105010f0e09 69
    0x81d440383c0c00007030b0600c154940b102c050398000c001190244124014042c01003a5541d0000c0e0078081102039002c4220760000100d401410311103843c04001007501c20206201c1c01c0b5000d41c000601c80903251100006156024a0141e14108154220405c0c800002c0400d213685080c0700e400e4142c0600420304c510b000c0c400070007445544404c5020403038501d002d110031010005000b070782c0407155200700079040390401c240e050134440c4c154414181d21500364000d01082e03568001030b900e13100b10b0210240901c811200c1c0314841d40702d812000c000f41841a1180f031524800e90f000110903400c2101c048071490303180e107400c80c50303900c0611240c010910607000035070509081030030441d2100802c0c05025601c10181c000a0180c50b4240c2100c5140300c05006660345900385414980e131226424002d200c440c41c00c01009440300d040501c40c00e84181c00ca18090b1039103c0004404807050391051002c000d4162242c400000070480030b00c00d030b40c002c002c0c0b5400400b40a1615412814111004080749281e8200e00407081e46 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 430375827 1250 430374577 430374583
    0x90b030606031b0d120c0b0c03043c050a0c0b0a08010603090807210306230405040206071406071701060e0114040810090510060302031902061b0c04051503 68
    0x1190340a00701d0486506400c0c0813484900d920340d0064002c0318921800602c1036080084044041d000310100d82c1c650f0340d010201086480191401000107425424070b001040d041020303140341c414145101052104102e0705000c80d0315880380107a40d03d421425000c0204800b80c840000200f007144e03461820542d00e0000030303190540520031013040c95120f020080c20490800d00301c03074407603500c0f00044007001803d024107000a22040001c001103840c00d0400b00c0c500369413015410400404500c1c011811003c481800040c003c040c0003207801080078411080010503290754483c19030301040040c607652074083c100622443c1c4500c110150554074400611450360f0042244942c0182803e140c1186003401c1081c007500e110f640d020b10098054030600070000c0086800c00f0300e02900410448040d40c041401100c1102c10a101c025419404000c1510011003c85810000c09000034159814040c2c400d48410141c5400500800c1540100b42c40104600c1e0910a0942080c419122411942031600100755 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 430377077 1250 430375827 430375843
    0x30d03140115021504050a050d050412230f03030f010506070c0b09030f0102041d010e090d20010f060521071a0c010c0f110105090a12030b1009090b03060603 69
    0x107096884010000150f0007048401d040301d0b540a460221440c00d420041d0310783c1d0681804035400e00891602d030f92443c0c1f03c1c0060310242c5040d205000904840340e602c480d1101c03401c0081100700000c050054445003001d0061440024019010790f41d2807a01c030b0320600c07110340141c102030b211360801e00402020425041c4502d0079904203504807562112040002490800e00b170b42d0401a80d8000039000c204074101d0710303019a894011101211040c0d07214200c0d035082010880d00019594481180c0d1008148110450f0a031170b40824106d0100c41c2c03002c02c0c80e40c2500d240c1716206948030740750081004641030050910b1510590fa6140c040483c0c44511404e40300c0d41a8842c640c080003040c0e0140c1c0035503403104120340c1011041c600030041c2d281c0344800580420540400b52001c5171000030b0f1104c1145044c014280309512102c0580400c03540743e82e81d94a11011000d160b0100f62313440e100303450b50352200380342c0c1000c4405c2901c51010103858240003009031036038101e0f80e50094000a0074080d083d100054200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 430378327 1250 430377077 430377089
    0x108121908041b0f0503190209060103110409111824030703022104050c010801080a12050712021e0c0102030304110f06030106110616171b04080705030d031401 70
    0x41c60754a482c100125510028482c05410603100031001800504a5600d83d080702c800307400352002c074800c09122040040c0e119501030b40001c0c0201c0010000e62080e4060300e150002c20000d181003549822400c000c441d19200d1161840ca00003c182114003001c0c61440f003002e00c11101070440e03c12030b10000c1e070101250f007580c2c0034485000c030100328118069019181e0030100c1110b403401c0c0d04040d440a14280d8800c0c1e5050302c050090014180d400d502c900d4040c0d05a500702c038005c280707040c0da03503a0710003101d08660700950810006001c000c0010b6143c030300308849007403254020009094400070703104800100740740180140d0700c901c1c4c50f00c01e241d03004015039034016080a000c160030941c000100307010064408056a02080000001c9500c1d0f03000f122000c0c030102d80c0012034009070764182c00d400d8070001c05c0402a010650b51201d000b45107a1030b0459a44c072000d180074103040b1003500990315143c0e07001900000003d42002d1b0043c82141020400806440b80928091003406014244401c40440601941e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 430379577 1250 430378327 430378337
    0x60602211206030f0a0b19020c030a110a150b100816200a0305070b06031b0405040f1707023a110a090506041d1024090501081219 57
    0xd19699800d01c0228030182105060b0b500d504c4040c94408a0b11808035824080e00300b0f01f0380b180441003410701c01d6408121a4034015484c020070a030b82562410f103203c81c41c08452003139440715000035141d41d850b00a081100800031078544680b008210400130403001500c100071240d03003004440319100540300500c0b8603034141011400d058002e5900d120010324000b041510070358802c0e80400d80c1c02401403000320b00495044846e5262039041640340c0451a030980300080da0050190315500e030540c0001c0c0c0151261a2a500b0f02d00f85903582c8492004502c400c0d4580d510210ba80380a43c207044511006582500ca0104444071419110b0314280000f4002e1490000410486000b000070b4994040030403031005101c21a040d40c1c810440000e48411100a0b0043307007810f1101d40541c1c1e45a00c001c1ca01600180035040303124548020b9001454004c0051300014402044a010913003040c0c51500a40705e0300d10081515818014150316100c0c1c0c1030941e0007010401c004005555607010740800010010781b0300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 430380827 1250 430379577 430379581
    0xd0614060f010206061504170304181e020315030f0607320a11010623060a020604060b0a0e09060406051e07031a0415050a060c0213020f07080307030606022112 70
    0x1b00358071740501d8228810290409003281140100040a4400c841c8030f0503500710280c4d84001d490055441d4880c181c682c80180070785022001c0102e4019583c0302d182c00c03074040c10742c0c009800000e2910300c41c0c0485420030707007243d414810044e0f4000c2500c1220318102d40c0c08195600b5440329101d100d41005400c1800441c0818a2041e0364440d007000d400140c540b000034030070140c8400c1a10348801603803415410f850b0411552100e5410000c055800c3c031089070b0050800307591252035100140c290880755982c4442c400e0340c04a0040044c01c070b05401115420014282c51910f440c1040807928040e06d8000c04081842044000040591311140d212846190110b901c064651940c61400070b403401c9141c3c49400c0c00b000003002401d0261010848004444140303d25a48160641d0040701c840300103900036000034040003901905400412500c0030500610346400460303210084690030035540310b8002501c0e55001c202080d4100206910900f1004070380584000344075401c18984644d1303c00001050103180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 430382077 1250 430380827 430380859
    0x3040206072a082a1207050d06020904050105060403020607121b0302061f060525020301090c08060c0306010e10090503030c0d090e0c09090a0b0d0614060f01020606 72
    0x41510b0755044a50030b1008550449200110210010301810005101c0c5010780f414102658812030b540c0e01040b00c60403a1440c0c0340040c818035561a0401c1c200c00d108a041c006840d0715945c61444180c1c0c0a00c0d40140c0780c2c0302d8401004250f85044c0c1c40b03e403245100b80000d0001d03035100c0080b2103806a01c084040c07500c0c0c44d038a40954062842072104000c07040c8801802d01403580206031540b10300c0d1150f82c0c2030303140c8440144417202c80700c1d10300a600010b14280220b05040c0e084600100d41c003804409031900c9103015500290958880b281c3c11501c0c001700382010840d9410421501d500107403c0440c590a516103100024003c0c200c08504600c660048001d404c080b234090401640a401e0240076281e60311000c1541c0e81e5511b04007402c0c02c00142d256600000e002c001488218018410001803500c0c2040540400132007a03030240c0000300c0740e5522841c1200e913a4805403039542d541d1103808046030402c1c0018442c4d1f41248000c100c0b40c014072a2112041080e80d020850307950207642200d83c1c4181c42c00440e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 430383327 1250 430382077 430382093
    0x30906030c18040501090c12060608010b09400b03030a05180301110a0210051303080403110102180414100306020a201e0715030c1413090c030603080304020607 70
    0x10b00000c2e0801c0c60030b40007240078800c0340c101e246051126111a016030116010000440300c19205000010303080c0f030010301c01712140c14000d0032a020020710312004910600c0c0c20440324100d0303c400b50681d107030140f015545000e01d1100010044861402040700300c40031404030362288160141101084400a8410110540c244040410b59070150007080030325110610900140c0c00070121704094469a5624883e151a50140b2131262010201403450070425513030070340703203e18060421424800340030b002c40c0300c2c1c91091002c4c0142d42c10032041000b90800300d106201c100d40f03520004c450100441010403c841c65910286022030342e01810040c1c2d6002088000c4440c1801100f401060302e00340030312041d0080d4009201d0107080d03040e401c0100c010300d917010003551310007091180c0d40c1941c0c082c4e900d10140d14000d03030180d64100705074101017200c8480404094460390100c0030202d800500c02c40d050000002501c50041540c401c1e08041040c00e0858032040e0303040c00010302c001c0c1725140000e2510704200445e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 430384577 1250 430383327 430383367
    0x906160c080313030318030e010e0f03150a06030b1302130506091605040902041206060801020301050d080a020c18070801090b1507060b06030c0a11031801030e070e16020f030906030c 80
    0x606c800c030004044c601c0c004001d41d001c814614002a5144d00082d080c0c03400214603116100000c0081140455015198644d10001401081102e54507034000010a1074104e00901c24a00308140c0c1011600324810800d039035568108007001c46d4a4041042015140d102c0b02d036403c18048000b11404990010302100c0610450b08804001c07400400c002456900101c00680894803880003031047c607844000d11400c0b07000900c162540b020307218020401103a0484010b1942070717841c2c8160303012080c502005c00c40301c0e6440713440c61840096610400c1001c03540030300d155000d45000102400000a02c0c1b00080f0b81d00702c845044582100005190010840281d00c1301030b801f6401303044241c491805000034402600000c0c04038000c00c100d203020342c0c40108088216400c150080f82e081c0c001d142c0590046008100b021020403440c40746840114600001080840c425622100a030000e4902004024100280c8440d10843c0e98402c0c071404d0b4075a540c041c1502d920044d007001468460028501e041035521032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 430385827 1250 430384577 430384601
    0xf0307090f06090b300312070f02100506060a050f2809060c0c090e0102070512220e0a0b0a0b0a05130605071106090102150906160c0803130303 63
    0x1605011284040741034200c901140c152001c00c0080041d04002d02040d1a00101c18003a050309145400c1d89080071040422843e0790540c04403824200000e09403640428140c84450110301c42e4411980010b60400c512100c00b003140b4014092400e0030804500a030082c0c140306001d03c0301c04149031011039085000e6808551075503220040c0604a80800c41c03200e1a10013001c000102d203444003041140c0500b01c2d02c4461644024000161071405e00304800a0000d04201c0c426950200300030408181c0030002d480c41181d11a220720f6807040e4410661401c80400342d54024040440d00e81003066007e0004e01c49e0340b0591841380030896000040010b0107006244c0c01050754004c01058035030006903c40041c1181e1850390340d1401505440b0407090307541c1e00460314014504050320600c13050b5070400c14041c010100040c0101e42c52021a42580d04403010700f180c580101d0340c000000c0044410401c04010581031050600403075031500b81c0c0f181103070b0b440020710b22211b0400441040080503c03a030701c00700c0541c0c6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 430387077 1250 430385827 430385831
    0xc070203011d06180703080d02040330020f100911100201061a0304021311090a0306090203010f09020303070b0c0d0507020318101d13020a0503010602010510140f030709 74
    0x4500c401103500001190a80e211038422540014012001c810841c641ca40c2e90300c00511403a1b02d1540c526019034080488600340540038070002002030318040d46540561460900c809204550b07149041401d8491440401154041d101c0c590f11441d01040d0000c518480d14008105004541410b480c4044620482c0b504a0307000c20001c80005e5040d030140060710251040c02d5890011284a1900c5000548002c5d6115020018460400c0b40039803003810304603074100034103050408150010b50340140302e43c0107840c0591a900b04004502e001e1241a1800c0400c2030204162402500405d68034090420024042164107002c558460596810307a1001c10320742c24103104603d800700009440c0d4005010b00142d0a0940207001d1003450303c07a080d503480c0012661941d04070060810071a07801580040310f203402000980394511403e14900040103580c6080c3c0f00d41d0344d00d516140000303085910040000d999030280703050034010301070042c40d220394586085400243c0b0303085020029060062a03070105c01114 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 430388327 1250 430387077 430387091
    0x41b08060f21010606030506010912230f0c03010501060801031502192a0206030a020f0c0102040f0e0c030606030403030203040623060a050105070506060d0503071403031801140f0c07020301 83
    0x2c0011500d02d4a07000701800280070003607441c2e5041d001c0d940182d802d0ba02140c5c03602d9081c400b203508a171301c4d03484880c0503040b40d00d118559101e0344022586402442c01e900e40280d01c400490000400c0501c03251001034001b00955850100028480c107010302008005068512510203103040f140c05845d4200302c020034544560500c1c10015281001c1a07000c0100644211600321211039140b1407a280150040d104a03d19901d504008009620007208041d04840030b010100740030f10240b000e80b0150200012803c071050810800901c0ca410040040ba008401002000300544038042500e4000383e050801584a0300c60b0300d00b00028004000480b040c1d070441001800320303001e5080d9100d0140c40150b9a4400700790b1580c004555910030110090010350200e404a0045d08241c94010302c018006e0043c3c3e42040348642d00e440e2210155940300005a1000c0300303100c01c1421101d41d0440e0142010002c1200404880410103101c00042003110302000c10070000b06641d031280c00313b0f4486a4002e000700550 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 430389577 1250 430388327 430388359
    0xa1103091b060c2a09060f01050d090807050106031b120303230a0f1d0303040b060a031a010608010f050931030203030f0f01030b011401140f18041b08060f 68
    0x211380390340c800100f20f100e2151002490b01384400c5250142602418260074507184400546080c1d01c02c041001d04280c1c0d820301c80001c95840c002410855101324000300d18a0b00d1828003054042e900c0030341c1d41841d09100001c101c1400c0d4142c1c0c000200d80e241c2808540e1a030100050703480710f0007190403141c41804400400a00100c5644100c507091910481000400351822001d01e00c0588060b0100140e8410400f0030702080e0144a1594040e0004080fa041d860f2660354002030000c201d050141042c0c41c5000511510303800c0019940904011400900c441e450900003c10200c000341121803580c2801107072000ca502c41402c4e1404001d418210308100201900e8025600c0d80200c072042c814240b0300003c5003c0440d515111812079400c4a24400c043e400d01c100c3c0c00020f00d034048118144804c68411a0b01d10000c9006454014444034000d91030740542c1103444601101140e0321407086140606100203024440c60314140202c8514092660380d8500003c01d8074625510403a542c8031055400100c1e007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 430390827 1250 430389577 430389613
    0x80a150905011206050106050a050702042f03040b010b12010e150a2904082a090a1a0d051e0705180402151e0304050102090d05060a1103091b060c 64
    0x1d15442070b64104080c0c0e0ba500307000c94230341c020300d00076500107801000084054600b035004120032070070b414007007500c0002070301481403100304031000803030001d0011080000748024004940d00500e4083c554610b0203246603250b402034801405a40c4203240d141d4040303601c885c0040000d0b034034401c0c050301500750a9200c010b4402c90729414004100804190b088bd0300460806000740d07003c03100114010725012002010041480290049500d4444e281214540071917540104c541d000d0010f084000544098600c0c40c520000d030510300c568012161003100800181c000100e130f40c20f040c89600d40038000140030200030700305045540305a5000d003001d035007800c4510520901c0d030f006078401c40344400107070b55100346524240503110300c2408548c05000b80e002e1882e07800c1c008551251242c0001854030011000142c8e03081e05002c820348240d8032803030070003d140546100d0030030f4840d40c05006c903045103000401c59660f00d5130b07085201101f6890003013080464844a0590328070400460a5640140602242d484 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 430392077 1250 430390827 430390859
    0x20a0e0a0b19030f0305120103060f0c020c0306060906180115021c051e07050102070c0302040b040b0a121a0f060f0103050c03040212030d02040806060a0f06080a15090501 75
    0x101441d000030415a898200c01c0b07410392140805500b030701c0c00d103180c40f40d07554203404a03000da0a1141c10000d101c041007011846a010b9072061400080700042074080f40c08030ba210a48620965000d5040380707841c0d41d070010310140c2c00130085034240300d01d550380c0c0007241031100c024070b6603500044080c001140c00082e80030203502c80c259a5003140c66134000780301e000749030021f0720540b000425010046c2c842c05c01c182c103186581f100e0004001c1c40c0780940c180c0e106800c982c03010340256031041c070740b0030103000b1454540207189400d2011501070204400c00000201070881911840754401d0a540d1013804005480340040b041c074480102d42c40881c0742200e00420110030446105c0d119511800c005002d0350300034802c69001d106404825819a03503030764203100311030b4903005403001e05120910032154403991500080c009040003901410440c2881001d001154609030001300780c88038140b80a0003455448484144e000082482c0031a0040ca0a03254440980040e0022180c8505110011400107510304403c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 430393327 1250 430392077 430392091
    0x3020f0307140f070509161407050d0207050604050f010c02040b040e07210c051017010b090906030105010302030606090408090d140f0c0a06050a090e01061e2d0c020a0e 74
    0x70030a0820f220080d03142d46143c01059484803401c07000c0345428004a180040c20710241c246090244a84084480183c0200354101c3e011350001109041c0e4507414000c00005200070f803460b034281070034400014003840c400f0084d10f04104040f1000d106540d2160800312550300b001d0400c012031103040d01c401d501c8009901802450714400981e06458691200018812641105040030031a051400b0031403404140d985500400003d22148907958452111403402003419038186681c4203405018408066001001c8521a900d40300040000da1004500d4980c4808100e420702003594880c50070b45101d010b00b00c9003070703013210711040003400704803111304084031603500c40044407041c1c40000d143c241c0d550b24503590751380c100c0105002000f8850044003d00001c1c1042d08110905684407004030480e450243e120000284a00c0301d00400c0c480c4040e203003100a581c80c07419818001c1c2c1d402841c0c404c0f02d0702a00340003d01c030240500700c0d8660b1042000b40b2020b540104042032883d940c482100902c101a6084 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 430394577 1250 430393327 430393333
    0x207080c030714060c04170f0f0319050708070b1902030703020403030305090a200604032f09070807120914010b09090109150f020f0307030c030b010905061603020f030714 75
    0x40e00c40d0140000e036041c03040b01c5176070f0094034141c10410441c0354080c00100810541c81041122011800144403400f550361400c0011502c0c1d641404140b0111400e40c10b244083c86800c005107808103a01e0030855070403680042c041c029a482c1d40300c80303039803030105900016052440441804002e0340c1c1500200204e80c06a40c09000f41d4581082c0c15895070000341006141034080440744003c0c052032040e074401c03034030028040c50801d9541e4440742200201c4031100c0011280d8046001451070503801000903d200950311001e051a0121005d40034981c060080c4042c88088980384880c02e800d6080203444075400640c44118110058400e40605946c0b04d01500c40e071012400148448414841c3c0d0f81d060b90000782a90404021030303002e400a084a20b41044007940070803c109040e0020b10003540194420fa4001444510080009040f182c40c203010a0400212a500b040b050f5101c405955031125550302140b4088420301d4160720b04150202c1800b11804003081c0282031101c2c1d084142000b04420381a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 430395683 1106 430394577 430394603
    0x21306020114010b030c1602031f0b0a230d2909010c0203030c030a0c0c0618021207211406010f17060105031f0207080c0307 55
    0x12000d40c1d1a100940101802c07148854010b018490300c49082d400c01081c00c00d114418000c118440076401401803040d985c0030b01c40e0814200d04034032250003101000700c0c19000741005c414264464202c806000130011070100c0781007806d03808030241c03480348180801001500c40595074240c403801d60484503c61101700c0f00c40300e05144174444403440c00313034039011110509460340e1610000441d0401d0051080407640341090b6508a01e4075200410380c88038401003200c503030586c404058801e81c146441d1310300c220181d00c0c150080e1402510200f4a500c2e104140560780c807424800c4200820700082e4041c81c407590b90f00c0702a05c0511035407081c03520165a040c01c502c0c5c0a800e0b0062f40c00c0f0001d6200c1008145410311703d040c2e19101d040040d025542c90000082d4079038260b004001d001032850114900d00d0a82c80d411100300f01d40c0004101d48440550114940c1da8009413030468015008802c = true := by decide +kernel

theorem cover : BRFrame.Cov 430215827 430395683 := by
  have h0 := BRFrame.cov_init 430215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 430215827 ≤ n) (h2 : n < 430395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
