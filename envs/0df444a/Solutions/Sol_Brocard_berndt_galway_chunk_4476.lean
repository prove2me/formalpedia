-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4476
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:44:09.307109+00:00
-- url     : https://prove2.me/submissions/e5a4ea39-d32a-458b-ace0-e1b11e69fbaf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 804856115 ≤ n < 805035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 804857365 1250 804856115 804856121
    0x30c03050a11030d0c2c010c0309090c0804051c021f090609060b040605030c030303010605130e0124020c0a180b0607051c090b04180b040c030b0102070f0518090c06030a 74
    0xe03903e0126945110046030000541d5140c00017820a1b00c0710100000340c1d40c0110b94804885d2000d40c200010300102190406c00760007000e6140e440c03a40c070307040b089c00d00c2c0c28500d040c4080c40740040c03409050003008030b8032550042490020340003510f03500010612140041800b9040c014030040401c0c0ca0003a48004000d2a984500e0075408145d60030080a41c5a800389139813080c00111856050340203000402440780300c1d5000f03020701c29540310020b50042e0340f040301036102042a04400911509000501c2c010405400c02030806000c0388000d10240300e010f004608600880e002d50007030311100c00c2007c0a112015001703600848405050544c2d03480144c03e140307407142e0404804514903a90a01ea6604251103140000203407045082d0151429103401d00e11000025030703503420310010392513140000b215030f00d074402c4649201c02c54030042140c44008000a081080d281c00c41c064481c1043c10910443d100d041003d1903031010700d000d403140354aa541c06170b40b0b0075040030410341d8895000002c1008088440e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 804858615 1250 804857365 804857381
    0xb070305071d0d11010e031204300f050304080d080f15090a24060314010608150609030102040e180d0e011b2a140d030c03050a11030d 59
    0x142c0d40c00c10704010240840c030803003010701840382e20000c0b01d42d442010404c2048007820140c8141400e44070740d10300c070000c030781040b22214481000c0f0102140c00c0040883d14000810f21000341c0002640034940c841d00a000003000c5980034003140070200a00f800c1000c104102d5024040302c5045648940c01e543d40244040000c036890fa6503446014040740d480c61481e015640d0744000201810749a03598455039100030200c104212180e40c2e038904101da007201402da4030300050141039070003041c0985220302085842d0701c180d0000040000d082d0400080c0036010a029001e800119106036841d000940020301a020315000700104040100070701200701e01d031000500307009031082c095a100b007038012030130b0300c4180c0f0041e100e070701081003c4c03840a080301120740c8903101144034245074000c13040d10f03140c11803d8854024031061ba0307200c2c03030702c05002c00d0103446071038a8280c07022100703644031030b0036a0b40c010f100403e4188010140240800c40350030650080c1020800000c0c01411240c03191030800018000c0c104038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 804859865 1250 804858615 804858617
    0xb040c4d01060e012d050a060e01030b030718091a010f150804170f0c0d050d11040b1e04030f0c030b0c12220606080a14030a020601210b07030507 64
    0x344002510f008401811030490715001d45801000b850340510b41142c002c8445840f1500060140200f03d9581344040c107801340c02a951620011902c110014003101d1816803c0f43c4681e020550030008031107000041e4118520f8410082546807480c90038100e0500c400b0600100c20180d84008034508000019610498500034030358070b10101140d8060384d500c61f00340c8003c0d0015a40e0300908040395203540092658a400c0302049182000b80c100160a00750070310342c13072800075400060341403850150740100e03442601c1701d0000d289401c5c68020112031303034841e0840008400b8460801e0324069203501050710010350f0070200401c80650140750008401d441c03400110384035885c5001003074400c020341060703c0d0840040b00d240c4000351500c00c212250007640e41302590004885c100e40c0030000710240268030081c50351a00410801059103004101d0844480c03280406500c184140c0da151039000807181d046030907149000940c8003d403458010a07143c0d107080900303148504000c0c066190b0303140d130000b841b500c81 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 804861115 1250 804859865 804859871
    0xa0e0409142401050f0a090f09050d03020f160507030b2d010b090409110607110307140a030308130c08030c0607020106050105040e0c0d0513060b040c4d01 68
    0x594640350300c02c035916407000e0000101c80005020500b4030f1105946070300b2000308602c000c0369655507001e09840c07042003580c1c40d00d034403010381c0300c1041810407803a20344040d41c6c10150b00b819644101c108450103800c1201504440800036001845001d01a200103540c0111483e0602c1c178042c3d486001184091412a51203c03010107a9001103990554040c1691105002ca0341303440c2009041001502246070b0030354005950050000c16556410700400c803a52003040305c1120070480104250410020382e00000441140928042c4165140c400794001d83e5414203104046440703000082e250b42503000c038000e21031a0340701000314480c100000586054105501100c90f40d03a507a070ba00702e01b6191180324080c0482c1040c0014030074038119410050303000030014a2941410324113008603050340c50a440381900300560140040500069000d81030603a00159424010340c0341240c3c00602c13040704840740141034007001c140003140d0303841145c0c60700060032110ed40494800700c0b0315950700c0d0007018400040c03683d86 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 804862365 1250 804861115 804861133
    0x8062e03140d0f0305040308040303090302011b12050a06030b010b0d1e0e0d170a270b0105010909090c0312020c090f190603051e12030906060111030319020a0e040914 73
    0x12081c040c1e00d20947c1d056582c00c1d1180c0369039406401a081081c0100c080d55201c800d60186405400d0300820030104640d1040d01d1000700090040031100044c0c12034140c141051002d00c0450f42c0b0031001811520600403695442481042002c01016065480c0c1e041321002030f408442e00300c3c0380d0015a03800b0048804d03a940302030a031005589401c0c1c07940780d400c00401c1d107100003114110389900c03e100d442102d10642103000c48120000048400140040707030446000d2005109035603120000c0300141450b29002c020061064544408460051100406e07204013041c1c44c3c00c56901c2408030002948004c2c0c1440020300b803074031168440d110122100841c501904c07500e41010700160040b1000c030794004001d03103c1880c6910100c0003402c00c0050703906180c1f05180201c0c1500e0740100055200c0c2c0c401001501150802c100010511842d0303508220f500e600074130038000c0c502001c0c064056001c80c3e01c1c5005980301d00403c400c1e10300d000d202032010780c418640390001c0103010f190700c2c041c840000e460081e140707164 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 804863615 1250 804862365 804862367
    0x21311040e220204020d090b09030d1b0923040207050c030c0616020f0d08070302010e010f020406020d030c031b17090601031a07020a06020c01090c08062e03140d0f 72
    0x150103242c14001c1059030002000760800340d0081281c40c030b040c00017285140071034642c000911003e6480010662000030710308210041c030702c5209203844555002c0c900c0d02d0084070b801001c00d00d683c0920301d642c070300d580c0d03040300d08240e100b0010000d50f401038020354484146040140d16450003041450090045a4007008a840c03c03004850740c10040386c0791041401856000d2104408000300d15a0300700d03000d80030ba9008140500040e0560512950000ca02c41c0584008142510160401125584d0040c801403000700e401241b680c80441440c07030005600a80804e0440c040e0032813240c026448090b4401103022385030300c10021444000340e400f440b81c240d198124816580c03142480003401c405c0490111058011070488025000701e240d00c1111604070749902c580b41213910100c030102990703549485600070480350400c1f10000308005405000340707180c40f000341e549590203081250262400103804541c8880701c420ba003400303540c0141d58080c80b41020300a071380d0340c0e40314447e0301c401140c2c010803060552 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 804864865 1250 804863615 804863641
    0x70b01270209040212040f05010b03060f0103200a08031e0f030106080910061d0703050705091302120a0501050901081207080309031b030a0f08090712021311040e 71
    0x9006004440e82003100500500c500030341040520a41c030075001c010840100c018080b489000758040c991080000046142442c01c54032955521070081d0070581c108030404480d002c06c00d0440e9000342080c0801c928511040c1d05000d1000c0c1801d034401d100300c8010808000c004041e081c84241180d02065100041c249413215004011584403100b00810041c020700e8480e204007500b01d110700c0c00f250003001c281005e21041d40d070319400c0b8120054006a4209800400c080c0c00c0d60407107218101044a0b08054500806a204981c106801400c42c1d2500c4000c05c111503046680c0010401000c3d417590034002c1050001e010203114051180240c140081442c0b81c003c290394440f0070002d110311b441c01c9019a100505604000e21045181c04240b24904a80700e445506501c0004400017943c1e44422003200a4000c0c0c00c014140400c205083e81048020a80090580295500900d00c1d81c0310740c4507480040c1101d1b03c0b80d94840500360400400e413030101d000c4c00240080d05d0300c3d0740e00344407d5600c80103ca412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 804866115 1250 804864865 804864899
    0x80718030b071803080706020a021608011401090c0c0b09030424020c0a081506120303040309091512140304180b04060e0610120219080402120a02060d0f0b0d0602070b01 74
    0x5e00e204014810014655600500549013180103568070820307036200a84003000075a002d8200e030f0b5100c11321140da4401e05d610741809490f100c2401c00540c03811410003040c002c9900801461042c2070008500c40c3c8000300192002040164035050380001c2c9003510901c518110b040c00d4015210341c4d510b044540c9410194401034828910082c1214a0340c4545130000380005003009400c6140b0307003c1221a004c1c18001544110300a03184e84d403449103082c41260844001c009030701d44101000c0c41c1030000304149445041d901d81c00c012582c95100e07004080500318810303a1b02988015403408601c0341c8030340068200640b40f000881d02003040517a1141d0880c816581280c64540c410941407100346014000c11010001c3d00c4102001401d00d0310b06a10311383d804280b08c6040010a25140400c003c6103040c0c61156500b555075000b40030001a00c0d804078078280550085a803041e61242c0ac0c420310b03c40580d20a002e0003d0042180000c100c9504144000354403008081c1c603030580b0700001048201401145004c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 804867365 1250 804866115 804866123
    0x11d0a11030d020d0e130207031806180303050d1515112b02100c02030706110703020c061602030105070f0f021b010302070c080607080910060b0a080718030b071803 72
    0x18444444d2808440c00c1c018140d045034005036203803951100c4000761001d0040341f80b0a0b141c1d070643e0036803100501b5024805603c40700c1001807c421800c086420503034640112079050070140c0c1c450007070000c8500640440c45c94250340801d00c80000170188012070010f000e445107916a101031000c0014400c0c1c88800e611000840c02c94413401115488180703642640182c809403040d50000800e024160b403e4031054008900103078404980c41080c451944a400346403035006c261a480d040c0240d80c0a51035075416003103141f0640d400f00342603542460400c0b8000c40b09600400810451400a50261045030800d450000107800400082010b0303000013401c0d81448000750000228449040c0114003075480500b045680c0310310100f0029100710300704015070180009440708007880c03805d6444140303002022214109480d0a002c0704120000c0618101c400001191801c80c103130303a44900c001d550410085008144501015070b0000602c00716025941c090f008036038801c5996405c200c0c141209903c00e001c0a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 804868615 1250 804867365 804867373
    0xa06230c07030e010c02010e03072301090e04061d01020309010212150f10020a0611031806130f140a050a021323040c051302090301060510051803011d0a11030d02 71
    0x608070750700955001805c0b074414540424103a60180109081405a82c003130b0b54100402ea40c440801c20222403103000368002880c241a00c217150242242d03a00130060701c0549110784d01c4040d850f1544500c0c1e09222203d0382075000350350324101910058001c3d880028000d1400c0700420115041014021000c0820900100505400ca0200040102200c403200ba20b009500c105c003800343c0002c2c2c143c050200844134410440e0345a01e005d0f800720743c40c003460610110b650f40204042103a00145c0c4500c10862903009217076a84182014544100c854040642e90003103072240ca96448100708000500300c032082c0c8240c90041840910000386400d071441c149540c2262075110950141655241c410585d001c0e0050005101c0b003aa0b80002c68900d103030000d0b00c2e40d8031940024003d016400c00340124001080241c0b0f84503140598484001d205000f680f42c4c0c0c0c2031350398590800084583e02500b01d0b0911552350340c80c0c0816082d208221680e13541d900079003103032451558400340781d480c40c0104400000304000e4003d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 804869865 1250 804868615 804868637
    0x71e08010f05061807050c0114151503012304110307031505061b1c0503090d180510110d0507021206010503060412090e040b07032a0c050a06230c0703 66
    0x24204e14000100070340104542404110768900c0c0074040c0022511800095101d54141140c140301d08601c003500a80c040c101858040c0c210303448036000c0300e04455091000c000b01651783c1c1100a10411070540b8160700500700103014068503840d034001e6004035120741303080102c40b0214000d148506018030956602030424840e00e040100303d03c1d80c1118000020042d00d04107110310b294642000001001c0e800024004000c20000d92410087c8032954180c1d030802c4001080569400c2c43c0740e603518056103004441c00004100d426006400400082c0c0d0324000b0746030101303150711005001e50000718041c2c0c03142d000540d44a0611201140403416114064007428866646807620382c186030304180d1103070070814041400a10001002c50490240340f01c1d94440403a07040c04100281565240300040c5129042929105540764007400d0b403004140307907410310213044040d80c2001403c22501d20005032140327060448003112010f8824100100ba0440d006103441901e984540c00e40c01d02803508002d020400712030703031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 804871115 1250 804869865 804869899
    0x7060b040b1002030f13150f11011401270c080907060512011707030f0803071706010806120c1c0512030f010302040f090f03080106090b070302030d020a02071e08010f0506 75
    0x40c8a070041049032540120703a0360140a00060520900000003801c130f40424030380c95032200120711100d80800c02403042204580040c0000903061294004508280c0c40e1300036112074482c0f100dd51080013050400007400d8200c006017002d081203650802c01d000e502c40104600b4002c800303482404d07080d40c54110703a03a800c00351690946224070034030664a00c40c1e801c0000010b0200400d508406129000c519181d0401d0740d40034141903402550392054001e15010000542d034002440d503881403040360007510a181c209100e6090054082c1c041d41c100a100402c2e25816082081c00c0c00058410b80c100c800a041c4055131900900050380e09031500f0300c0b5600108050710b041c2d04008012080b050000a480034a540c032001400c071340b1002100414150f400401680d07800100300e5000301440c0881c20300c1d00300d503507030000d40b0fa10849500b800803d50204040c0e8942d882040754101625502d0700c800b4452140040c1d2484481d82c0307115100b03403507007044880e0700300a45500581d03028501c050511548811000a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 804872365 1250 804871115 804871117
    0x2010c0e041a06180a150c0b06040e01060608011e15050a0201021204032118060203040f1a0103050c0123090d1b03031e05030105010c0804030807060b040b1002030f 72
    0x81e10300202c02c08a412803419590b640042c0703c2d10040c0d88000500d21043c10501000844d168041039002144015030f5040c50f4021640001e0030344d001c00d84095980d2540c0002c0e00070130b012902007105601e42140401c3d059001015141079901003410360250001080d03002c1d41c1e079102406800c410702005c00b84140c0c000c5c000d4000d801d405400d80005401c00f0903500003003078100d904803416000074040c3c002c88103002d544031544c0c0c5420034141ca01800306d40101081031a00c0080c0100081c40d09600000040500030750310103101038240c1c01500e030071403000500254000403000703000640d600c0c001c4404070291b56005000700c0104110180700914103400c400c10b00749803500000707525900001e4140c0070340b000070305241c8082c2d4803101101d0600300050560034010101d07002d00e601c1006a00318890b102c5051034000b000e81707044410918101c5250025890b00e00c1013800b459100404041c2d0100d10141000b1017038011001c5c0d60010769041105e1342c0c49030108991107082e6604180036030410040c055180342c02d48 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 804873615 1250 804872365 804872381
    0x6020f07031208100b03190b0d0b180102091c02130903090302010c030e0a06020313090501030209060d0302030c1002180d26041205300a050702010e0613060f02010c0e04 74
    0x30019050b0764081700c001580c02119a50151030040002c001e144501d8428941c5800701524845032083c0150b0320f11a60400c00303054144a80136804140810314025012281548405001d800f0b0100c1003103031b07260f070a0002030f40480c410b06004508181c3c1c0c64281c42a0a07000d41c150344c91070302051079600199010740640e6810b800700141d111701130010fa100d00d00740b00024120341c0d0046035641e40d014040303102c603002034011540f07450428004001595440c0a6540c00c50300441d9002d41c04101490180d10b18425210700096030b002e032140d0b4088940700e0f6805003481041507800c240d0702284070380070010220003c0c00010805110101d002e95421038600c80500d009401406140c40c040e01c9014242c81c11420b01000c840682c840d025202c4c2000d1007001001052801000400d100c0d00300500500141c014a1044d03400c01101290b510305680c80b6200d40c1c02440806810306503a0980c4040d03410b21000d00f4050a0b01003180f00003681e00d4580f0501c10b2a6035600303145d0b04c02c140d0240140070170016007000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 804874865 1250 804873615 804873631
    0x30f0a020d151a12010510030e060c0711010306081504140f011a0103020a230409090b1014010c110a09060602060f1006350a020406020f07031208 64
    0x1d0000020000c894400d254810100d01251075001d46007400c032600e40850724580203a00d00c000e204140f0703030180b403081160540d6401c503004414071503810411801030010419801c1c0301d2050400748900c4804010082180a00515810448203011401035054501c14403035030b211680a06003002c101610302c0b4055810600c201180709600c6446848036180151b005aa15030b240d41d50300b203e0964011140800c00c1c034040a090550900c0f9142001400c2480000e05e0214280e034000740c803104410b400f074101c8004d420f26100402c404040360030441d000e000300711540c3c104da081040020a415074607440500074030178140d403040d1030801d0942d41c0204001d100c55900d5000741da080b81c00300e000c904034007070034002c0e050560003040e041c542001030200c1038201820720118080003a9042c40082e44c8501c803485003001c1e102d030781c91a41d080c0200c0d160b840282c504840d51401480402c2c4200c082c2c203600180111032140c1e003154040c00300110111348840440c81700030f017144030f440007070700260b4014440c80c0d80c0000e01c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 804876115 1250 804874865 804874867
    0x60605010f1209141c0305220f050316030e1002061b0c012027011205190603060614060f030f04140102160c08031e090a09060e0114100203030f0a02 65
    0x810780a0b145410003504120f8040810900c141040552501c11141d11213520030340082d0039101070585800c02054808c014103d54590400541480010411070700d1075000300c00011541d18040c2030081c10a0390319a401480781200703810355175030940b0010340e284c001c1b00401c0c15503100321030805101c202584a08240740483d500d0321907604051000088811848204444181e40d03840b10840c01421780f2403c0b0340794200012484003162403a40c0c800c00ca00170314201e4090014098032896500c000400a1b000302d000250b050010200401200e41c00400460300701c1c6a44088505003141085030030b004030b078a6034151800610000f02840304004009030040e010303c1c050001584014901e40c2a030740403180c0726841e1000c100604040051502100d4010541076010f9803c22000c0607003003010340c1050141c0c101326071010460000070355881c50040018600c84400300a22030b510509038014403824851280c040c0c0041c01403000d07030304103103074402d10903961b680c069899580d5a4040340d4824a01518800d50294 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 804877365 1250 804876115 804876143
    0x60f0507270503100204031205030c0a0518061b07091a041a120307020a06050a020d110f01060806150613060810180e0c01020106050f0603061219060605010f1209 71
    0x43c14410101306002c1c81d50090baa4a04500300442ca050440200604103c0100108540b42410805442584c41585011541c0c0d01515400900e040d0145055660102d00050059940c00702c10380c2920810901c0425205110b81e5803007528101d90400c001502030b00300750b05030b8404c00d107010351011280746090491122040400b002040b05d0450070404080e9581c4001850025443e0280320311004155900d055858200c68100003925880c102c10500180615949800e14141083c400310b070a540841303000b00049541c490240790754490603240e801a002d07030014843c1d4103060080c00c550103101080e100c0c0412500e0314100301c8003544c000781059055030318580301045201140c00c00300da15032060200072a104450b05141428112003020441c156803500c0310030841034445020405643c4001c84140e038807a501c000c0440e209a40c8a090f0702d000e8002c0c0d030352964000101840001c070b05070040e03074108025a129401543e80384089034001000c0399945699030600b002c01d40140391281d00c00c0c21890a101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 804878615 1250 804877365 804877369
    0x702061c09050706180b07020904050c042f0f07120207091104080c090613090303090f05150c030103210e041b031406090c2101060c060f05072705 64
    0x7100080708840c95000b0040801809078848400c200d0084440d807420101c03444e086001c2443d100720f500090051804c4c1c8009402d0001c00d2140301400880039100380160254000c00704001d10b01ba02c45140200e880d10b49020250448005551007100315210481c0746c071034541c56198403941d09282e114118844c0c0d080c0400c401a250258208101c105c0c52280d846038100002c160034200f02d11007850003207405604010441c0e03a100040d44420030100c00c00507800320b042c1001c03006042188006404555490010b0040080c002910201c442c0182d021200603150140005403600c401c1c44081c0548042d80c080105c40044048680d5142d420fa04240c11003d45140c041015100e880c5103139010b6610b2504202041505170113004528111a10b0340782c128540640095012807015040100d006800300748640b000c0481d8902c0d180000d01004020000e6968044c000e1440d01d540d01b04580c00d5080801092101040c0c0c058680104103d464042031032910800305100e110344a41c0301c1052001e61800040c00b9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 804879865 1250 804878615 804878621
    0xf090a05070b0a0905010e0a0308090114031302031903020a032d091a0a3e010b0415030f170f0a0e030c030607050703081b042d0b0702061c 61
    0x1048420100c1d0388400c0f40c000068040c00c0f982d40068180180d4050701e10179503981240e10016a54854611034031781e015040100c03200034130001c61440c0c0f13000c00070501c8921148800300040841c401c038103c83c010701c40e000070343d5480e422021004003d40e000800010000780a400c50131900d010202c450301007294403c110880d401c00c200600350203d0302004003031101b1003e90074250f0200101c000500d10b0460701c5d00000f800442c40c0103510444201810041d105141181c8420a4a4840800c103005490010f15040e008020320070b40103205a1501c0e0106080310341034081c80045940100031103c00c402103031148001d100c481d4108401410080104e0b1131003d00b4500541a040d9440d50380c0301c103504e401810f2515004102c0204c9120f90b01000c2004402c0c1c0c1d0180c12030f800c4c2a45454241490307252182c107801c004c292420080c904010115000c11216020301030700d034506035482401165540040c8100410319240d01800c4240c2000300248405818048018a500b4000f0301c840b0f00703d82e001024400031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 804881115 1250 804879865 804879869
    0x19120513021023180a030503040807060306031e03170702250e0721050c091e010e12070e09030408071e06030c03090b0403181d0f090a0507 61
    0x1a0003025403040c000d40c1040803101d81091010705080b81c1901c2d0040601c0341c8403e80030701c15505040000303580d0400e841400700780003020201a1000715401d0716880e1054403074119000e00d60040c81000c1d40007034a00d200b070184074103c075003080c8809202c1e204d0403641e81e10b80000030004c1d0103000c180032490009100c210042c0748a40e40c3d0340d0140907406520001d01d20003a8001e24240308406c0707200e1003444403280c44407000750821201d00f41154000700a05900c0754090106540c8400d5500d450100542002d0315002011300c01e00440e9802c0c00100300d003100018a22041d04114000381400384411041d0030a500020310751001d400c1141c2000781d40300142071003090100c0d401c145580021400704601d000411070301c40500b80e40208980c0d070031071551490b00b800c0c4542c855101015121840864018043d900c20700c60242c1204000003145041c0c1401f4041c40000040340c049060480f07400509000d20f4180304114038220034464000703840d10f50324005214005446800c250140b0382d044ca00164041084c080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 804882365 1250 804881115 804881131
    0xe12191209020d0602030106020c040504050c10021501030c060f02160e060a0f030c140105040e060f0a0902030a050103020a06090b0d0e070f090f180302060a240b091212191205 77
    0x40d4a41c1081c01c0207080000b10318045000cbc40c10501444005a004500310103200fa050304c9810714946010b408920740f500d400c031103190b00c404030700021042c01200030000081e1a030a40b0345441403001c0c84003c81e40c401030b080c00000c0340640c1050074840d01c02c0c07c01c2090b1304050024592200345403144081d002d44c00c01035200300c1d80c00c00d01e10400c01c209004027584c040ca4000034240b9074200713803925a00801080300206610712401d090402c10701c1ca540c0d0a4480d00140103603c0086480e4a801503041c0020502800107a1081c81c82e0b600c00120b03903218000c110251251004c00c0e03030401c0b00d03a1090074051311035468154214080c1040104501071341911800040a1100000c20301240720000c0b501141c0395020482c4284501d001010007080d000500141c00c000140d80020b0b60340b60b030403401c8030302c0d004408c041c1c03908500701c0e031740020b0f8840460040c04a246086031301c81c600751103c02045540b841040c9810529840500030072415074600c4880300000c00407802c0412060520103180b800301d5400321742c054 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 804883615 1250 804882365 804882367
    0x20f0a020a150e03070605090a08030711101b0507050f0607090e150607080c100c09081c020a0f060b03060c071a07081501030b09010305010e12191209020d0602 70
    0x1605026031400da0040b92010260108541c01015003a41c0c2c49115481c0d020780116152030200d451001c00300a081c0b01560404d1540d0380700d007040c0500a081405403524031a107031040750500d40301ca0105100d04106143c40704520130414010a40a5950343c01200040d2454080c249984003070f1081400014490303c00d540c0c510540b98108401c400a0500180600020500785286a03a103a2100000c0b00c1101c0d07002001581c8910f16040114a0000030041c141080d45c2030100e46040150014010f006580b03200f000d4030b2001c0b0384800304285440e03220344048010b0f4000b21580000c1a1401c251418950040f40003140e68040100801c0c074200c2c064070700398034001d00010540c051000820f0a00b0b0444088525a0243d04108a00800398007010301400d0f5036001610110405a0081d4031410703180901401c156012360703490406500070030407841029214002c034002510860000022259070304c0308213040c03202140c407100b02180e030301413100300601c0420fa0356640807015170b80d0b041e10629100d01c160405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 804884865 1250 804883615 804883633
    0x9060e0f180906091b06180409030302250b01120309090525020d120e0109061122150818190201030b0d0c051302091c03080f0105061c020f0a02 63
    0x2ca1404800910203102900404140008520f007014640c0d03541e4001c9602c552660864010b048440240d030b00c03050703402440d104040c1e00305505038000d44001c0003200c0ca0b880b807004150100703406401803e8401003210b01210f0040c05007030f91010304840d01900078541026441c0d10740c14901c0c1100c0040d40c60092003840c0d011924080f01c0d51086482d90382d0500e00c0a84824107020b40060140584070b100d4041850302c80c100c0d1071200f20b095210100740c0b038100405200301c1c03c01c40d040c27000720342c401d21103600443c52625003022101401c05da11400c48406440030805000d0400c0c04840741c030b20107068082c0880d0b41c01c003044800d4070300304001104035503640040321301c40d02c00e88005400c0315010783d82d03240246035043d030003004611540080403c82d042031b01c82610a0100c2ca071ba4400a1141074160f50380200c40d0317502504110b1115418a040c103100303894080c0c55440300e145802000703101b4801c45a105900b00908400c01035020b001c0f4554006284001d8108203c0d405414169040f610416005900030410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 804886115 1250 804884865 804884881
    0x4081b0607170606040605030a0f0e01110913091509020f0405040308190605010903030c020d08030709210807030e03070b0a02010c022808160605010b19030b0109060e0f18 75
    0x820fa08908101c6038079240603e080d901400c6070100030545503110f0381c0e6160b000140180c0da013041e48403206040007002000101d9602c5002d80d009070078124004c000301640701c040003540c1c1c810800d4507600002540c20500280c20140050a07440f94102d0f04100f00504860140d29140200350040340b00b500c8600c0c0620380f241031184240003840909050342d003400c504020700c0e608440c40100741e0340c152802c040072a0080c00440c9108138902001495200f00004010b0b010b030780000a4000d5990171080d0540069090000d84038102020802501042d401c010240000303004140461003068080c2c203031140c030303540c030612880580c1104c840d0780d0250b5100c9801d03d2200e641403052aa5280e03140380b5001c2c224000d4000c1c003280302c400c3c00000345006000500449858190303811503000a40c08142404107685480d080001074006003001241c140d80c1c0000040788900030301442c4080070040e981d4058051030301c0001c6601d01c2c5240e0000d5044520412103c415495624554124050080c0f000c400d80c282404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 804887365 1250 804886115 804886157
    0x50406110601060f0c06231f050f010302090310091103011d150405030f0307020114060618040b010309050604060603050d09061202090a090f0c020105070c0b04081b0607 74
    0x80c0c4848a6006980180b1806803c051041c0643d01c09182088210840d490140001d182040c40352468080c0c00c50b518007007510102e42c6070310415104207040d05a2041c240c21000c0440c440c0a1030768040d080c0803c0302c0d4154801c7d8050140400014100d42c419104441d043c4221818000240c0e803c034400064882507040034014034241c245592081442e440d1100040303501d5082001861200400c01004102441410001c2d02c031a1103511244c0e81d640d0800246c040e000b8404000402004d003841c0000481e03500c0c208090b1407882c8070100003d03079010241410440140811100c090501da615500d83c000f0480400155214506c1001c000545c0b85c198102245071441d0b4540200400021880500c440c5612110310001105500000f68490040e80005402c01840f40c006280b482d10b00603000c000381d1a140c00c00b408440c0d46030000c0001d9151100202c0f0510140c281c06030a5881e0440440c0c000755008008001090002c401035804021418000b03043c00720035200440011103d400001010030044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 804888615 1250 804887365 804887387
    0xc090913060612110f01030615091d0105010509120106082a030105040312202d0910050c01090f080a03050703050f240303041e05100203191806050406 66
    0x3580c0b00c8860483c9a44541039850b56482180c0600300c0500d42c4285640680c00100260180520100307280e91381c0703480202038200c940306140e44602c0821140500e04004840305042c2d840c1039460382d20b41282681401a0b5400c03c0d10410380c5596107400003d2175140900030302601544280c1c80b40c10b049403010345116151006c0740c1c254801d9140c0414400001c0e0000080401c0307612005011070300140b89020024012034000f070001d0520300000390507440c410310a11445400f0070052000141d84009100d480701c5008da41c0d0b40ea50072214440800d0700c1203005c1c0d070240181400d440001f0504042c03603078850b0198021000304442c4130201180711092260103000d9141d1019140ca000c00c40b80c80c04405008038000040c00380b200402e491039204c2030034901400c00421000340075048994440d940c00c84402c4c6402c84010b40b11030000d0b2840301140c145080461040c480005500840c00c045140c1280c401040d00f01310588d06100904920190260b0881c034141d000341100d40380c1d5502c0d9454800c2c003804c031240759 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 804889865 1250 804888615 804888629
    0x11030409060f0828080c0706050a031401060926010e0a0c09020703121a03010c1d030f0601030303380406170a080d1118010f0c0b010b030c0909130606 66
    0x622200c00d00501031342800d060a2200a1a0502c107101420619014031513207800b40ca29000d03240010503155042001400101d406607801c02600c040401910304c110000e009250000f08064400c0090390008005074003d00f41d11480f14504094544000707007112021894201da03508194135580500c070400442100500300c00c0c1c1f0951600c507031035074010000c54814182015403580d50030ba507480c0000500f400c210303e500103402040400000c41c0040e010f140074000b0a808502c00c40b88444040c200890300c00d1110704083e0080c103559080d60340c103a0141c035078116042c02c400f0b50540d00c0f03000130034038450594401e04401540b16459203000b00780002d0300c00e0380d08140c04000404450249061000600110704d80d0004441629402030b500c014014029444502101410105044072840040585220b40c50000d0b25001c9081940c86000c1c3c600c0910071030302800005c4290b00400100002c6c0e801582e114000d6400e80345000400000209a0300303090f190105a00d003840c03002010404984a9040a4500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 804891115 1250 804889865 804889873
    0x1315080a171602060a030e0618010c09060203070f050111120702010c1103090118050d060609060503010c0801030b040203151906240521010308030a0b09041109040311030409060f08 79
    0x4100040000503078030710b80081c001c00700001d110f403405120b9480500c032210b00c002941e50608000507082541e12841030b4020555181c224001001805a41a28101c88154000d5818003501e42c075103191a4407007c2045e03607a5521100040300d00d201d4100280a242e0026520901c0c43c2018040242119800c0144000b40480c0d42a00c01c22510000203403602103100740fa0041c1400048590740d01d07608150382c0002d0308070111042032010404103805c54016200110802c1050b00e948030101806d0310003035050507010900ea17000510104685c02c0040f5440350002d012200714840040e442d54101c0e0085801c0110082702d0114a4140845130084200601181e04840f10690361410030140c42c10001595000f031080006030456480301c140450799425000c2d070003000031980e403030503d1a402d5008481074410745150501e0092240703032040c1c1190003030307410200d5200e4424105042c080b200101402c00c4c2d00788458182480c80e80f07001000100042d107038030380d00403d001e890540442d012007020340080d02c0c5500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 804892365 1250 804891115 804891127
    0x1e010606140c15090a14060c0f07150507020106030b0f0705030f070c150203071b020307150c02031209150309060c07030512070e12011a101803030801030c0e13021315080a17 76
    0x3a08000c2d00c1c41300400611036a03681c032481c40c0a80810a054040f4414030b810900dc105450760103520290407030f402280c440c0982d981e41443e40641e10300462300140440d07001d002207032800072814101903100c3d0701410f200141034130717544074550b500104070220f4074001e0f00001080341a50303004901c00311984284d01c0390300c2402c0c3c0980c000313616007940b4051030342d80c10301d282c1d040d1140c070707214000320a035503a0041d0946000c124202c40c0145950b03c2a0081401420351740f629800500b030500890344070300000320252446071909190041c403903000b1042035041120a11607411a1200b040d200c5006000d15210004809020300500401500481488245901d8020034880d11419606501c0e0300d4141269070101550103035000781c4004805d0341c00c0c801a25075414001c4101900090464143ca0203880540d00340c0380c0d11112001c0c83c030002c84901e803000008040100040c01c04a49e1202c0541e0700038000301c0c00e031404000004007102d07158000541d0303511504801c4144081d1106e8040562040c049240c41c2030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 804893615 1250 804892365 804892381
    0x21b0c03120a180806010f0f03110d030e0415030c140612070903051209040513030c11221e02040302010f1412091e010606140c15090a1406 61
    0x96541c9166039040c00000c42d10042d0303110701a00d50311030301d000e208410526103990b00690760318002d0250054001c1c40c0100401e884410041703c8003100c0e441060f03600c1c801d800b101445003005014101302d06100d014130b04890941e5880c0100e9505c0040f03032110300b0145156050074400d101c40c03a400034424880c03006000300385855000898100c2c041000109405480c1c090b402c0312154281e500140c42406503001000080464030003c00000c0030448060203503480b400c0e40c0303c80104c0c002e0340c0200451100307050000014040c102000c0000300c02021013221080c0c8021194081c1c124004080126a440d075042100700c890a0303c80d00111000c840440c1842c0c190f5001800d0010070510103814000380c13841b4401c3c03c102080440e2000124244802d0382414081002c40da288000702c1d01c420588444040f4005d1290b052040e070080b5032066441c03005901008000901a50140004010364028540e1178400c48000d07880c00340c0140c01c2d9800509204400c1d0500c200700e0100c20400302040d401a0060160740 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 804894865 1250 804893615 804893623
    0x1801060507060203060a0801091a010510050711012a1703060f12100903080f06090f061003020412111f080103080c0c03070323012007020102030408070306021b0c03 72
    0x2041e40050010b13600c0d01d0313000000307100e0101903011100075802c201001081012100c00b0400d9426080280401c590701c80c000c10414103a50a150703c0000ca0070b000420200344c0750500040200d8041c1003002c10703441003038000c52003440b410b0340d400121440700418104104014600c07284d10203603409a80d00794200f210000700101c1d0920f01c0140700d294203140b0028001c3c42880342600034203c528041040005900c1e000d03015401c1202c1c1c80554450f480b0000340700d400d1058440d40f040051034411903e03980ca88041000501c0450100f03402c0690034400460800d01d00401a07840500600d00304519000036010041c41003c0321180401005804800b100901c0d00b00070b100d13043d00d41c445005c5032140d50b03122195140402c07806039182d040c410014000240980207143d0940342050095041c4111481034015081e25150501611514410420b081d41ca411030400b6100e66403052040d0ba14095441c2d03400e501d4107a05800a0721140d50000c1c5030303814544600600d615600484001e0728001c0070a100194031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 804896115 1250 804894865 804894877
    0x30b03070303030c14070506060a080c03060402150412080d050705070b040201120b130b03100b031b2202031501030c020615060d0908031602060103051e010b040501060c0218010605 79
    0x14151038502c08813a00340200034060504200804941c0c0300c141505003035580389230513100b03d8002c0c00011b501103031030341010a00740242e441c081c006012076243d503400d005d601e080c0e20f5151100ca140500002c90014181c84078986498041e031001c645a03a03101484000b2104080e0800050100400c031810000d100509010b510a80908040074100c15000f82d8201605181d0092544802c0070058009210b4480e809800c80d0070043d01150103500102111000f1603210000c82a45030780b0412140102040d040307050806640041c00b041d00c0c2c50034840200021080e05030034805096004030400030f0707203031121a408100c00c1003440c0034810525000400b944074400608402c80f155030300039440070f05403135100842c1d521034800c240c2040b6041d0103040004160300103444240884a0342007400510301c1c030003e102810703260041c0c085c1c282e00c1801ea10075031701d42e248128130701115501c5042a200d40c3d0707107a20074a8003d2460b5210b00c110301c5400e20400c130960315019002d0300c2012044005004450703005060f1a8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 804897365 1250 804896115 804896117
    0x10806090d0f05041505130509090c0402030a2703080c04030c050904061518110a1709071d0906090625050d0c03021b01020c0c0d0f0b0103030504060e01030b03070303 73
    0x2d40340600808032003d00c502d80102d1581c03101141c05000443d0312000030078441c68070042e05900c85071078404000030014156002e141030b501040e080040b5241507802180c004d0065500092440e1504a14400c0110b1160403212030180b102c0000c424182c2004040d03a104142408031864107045035640b0030040c082e03010300c50041c0310035000541002403c0e40310806403454035041b4004907582d030400c00000300447e0070021810781003c0c1c1c103540403035020040d102e085803140c460380d6201c2c0b414054101100d80c0180711700b0144c07255400c00581141e80d6070721074244c98901400041c180c40e01041c101c1c500a400b0f030505425a100382c04004481c01801d86244029038800100c041c280380c0050229030500498641d05049481d09a110740c62070340590081c01050f980b00440c40918500c1508036080340201d1500749880e41003800e40326098500650410500c41c481c26010755025880c0c1c079280d01481e8240c104078007040000405110711038010740d14010041d0f091a00340004941c13000401d40300c0e103803848010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 804898615 1250 804897365 804897377
    0x303060a0608090a022d27060a120605010302041b0804032303010f0609060908060609100305010c080a0605030a02031002250f0c0b03011d280b0306010806090d 70
    0x6840103014805904d521350014125240c443c00b1220070310301002180d011800d10903401100556a040048110302000200090400d020300000120008044020000c9902c1003400c0e1010810621651078144910b0041d000000c440d81180305220072a091030800d4140020324428445813607034494081c1e070780560f01d45003070390f1030b40f1448944c4804281214040d10401c04040004544c0092891000b0300715a030b46d0761028041a030b01e44d0b090715180b4007802141c120350000400955279050500190b50040e1601c0449403045a69884440c00c40b0103100108002416030010b0240700302d40741c0600e1010303103000c8001c2c00f000c00301a17000980e40c0c0d80c001c40d0085607070340200c0c542c1026240c955080100d41341c03c11110405d6006031609191606400c00120f902d602044004141c00321a103044c0ca042c0c0d480210011000c8058804e40f0801e400010b203c07490198000d103001e64100c61303204030010704252035a0040303804000903041604100d0140c20050035070b4803140c00c21001035000039000a03801c0441c1066 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 804899865 1250 804898615 804898621
    0xc0f07031b15120b370308030106050f07080f09011818050a06030c1206110a0e0d05011104090f05010e04050c100207080303070c050c010f02030414061303140d020303060a0608 77
    0x414040c103002c488075a17208144051480666141e407008004003020644c681c00d152844042101a5800c039001c05448a07900f40300600105004000422202c601060303100d0800d917496540304250752040c3d501d4230f480ca0002c21000090758111031300d046112110131008a480e4140500c8009403440c8040030601d20b912507003c40e0550f00070b64086009950000101c4110039152025919405014101162000c2c6800c180c43c0c4010170b1017042da80001125502d01460031403603000c03c83c2c600c030f50010a490a540c0d4501242c0e501c412a0300a0005114458010500c141007558500172950140e0080d00c1c3c1c28090382c1004001103000c18618582401180c45540384c0c01070b020308925043c200c0d00080c00f00c1c40000280551581c200b00d080e90814455412221200d0b00301c001191000c002c101c800c3e025034002d010038011201302e908101d018010103801c95084c80341d4035041903400400d607441500c0c0302c04030207522400d01c201403203001070a000c140021840c500b054000308510b1115403041b00304202c004404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 804901115 1250 804899865 804899897
    0x405090c03061b210906071e0e04020d06090f06090608030d0522080d0501060f17070201020c030d0606020c030a0c030b0402040b030d0e0306100b030115050c0f07031b15 74
    0x240c8000d000164101408244220400c91030040d00345d820000621502c000610864030a0320400710082c89030702004099101c2e40820748080c080c10071541d0b0300c541c09001c038041d04001c80c400c10005001c2c5410210700d00382c2c145590400c640300741e08540390182c248407080c0039240000044810201011030001942d0340c8a11201600800c65007070081c480e42c03c054032009104c0c1c0310000d8040f041d43e600040040c3c0c0d0740e40314113031101d54607214403001065044508040f01101501015840602400050310b043d0710000090300310740c404c80a4195140c0d0b1024244200c030350401c00e030f11079400160b004011282e965142d00c00c42001c18400100010840000030f411910380b600007010144010f000c480244283e180045c0c4044200c3c011980a440384d0300005661900c001d418408a60382c0c2e002c014034503402c1c00302951481f20011808024020104201c00030300c1400c004040c000281000070f05105421071a140d0114011481007840c2008105810700140654140c0c1600400301801c10029070381040740307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 804902365 1250 804901115 804901117
    0x90c0512032208060c03010612090515070302130e010914061c0201050906280e010e010e1f05070308090d170405120c010b0f060304081b0309090a0b0405090c03061b 72
    0x10b0009401044103105e40e000d000000b81d41a202c0700c0d114011012200f24004040392000d00c00a0302a074000c404030701602c04001b40c510f811212078a4050f02c0d00e820801c50000610701948092482076849004020304041442241c0b580c010b03c10141000d0304000e0001111a84140b104c1201d10707022807a01411603005404486080401526850316850181e0146401040300c810084040e244045840c04d400d1042e05055418841610303407030351840001c00115008180503401c6500541d26a10006109e05041c40c90f551a0601d56146540e0f03080d03c7c50000d15480019013200f64590000401d42c1c03015030820000c514450654201d140301e60f40301d0500d285001003e00b50100d0120001403140915003040d00040190007040c0ca0000d4403c841c40f05000307440c441110090454601441918000001c1c4100812204110300807a130500745400000b8001d40026511045900e50342d030790342440d90500d802081c0c0d0001100003d00b10b01d501c14000700b6190302004249070500f8044108500840180e00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 804903615 1250 804902365 804902369
    0x1401060e06061c0f0504030314010308160c050d0602070519030c03080a1b0203180a230111010e0c100503070903060b010c170a080f1b0d1e090c05120322 67
    0x14014005113110032150b0000300380c01e0740c00f40c0010342854a01091050740880c8070b4100ca0748805064540310701810b0b40460b00c8802c4504462200c058000011203a0701d144055007058024540180e0b201041d1034100d02d09004d10401d00b1920680da03905401080e0000107001c04650141004459581c0b0600c8140041c13070210001c09482d50218000200329130b00002030310303400300441c004840b00b82189007000030010180c0b080b03141c1032035607440f80052102c040400d407801000605009501800c046692802d4503010041103113981d00080806c806803030900c14018500845003002865410084070041039500d02d8080500b40a49500c05600240d1040704410012074004a128500650303e0743e440e000f40d41b10003240c100040003080800c8445545145860158900d02801010710303202c0000c44d5a6a0031450401110f00c1e6030b924442e04c1000d400340c5018441554070000100c40181d40b51003a030124080c2c01481c000c00f0300301c04090261030000304403103054403200c00d80702d0b0180c542982c43e04440016 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 804904865 1250 804903615 804903667
    0x180f05090c03010c03060b0f0708070b0109140a23062704050f070501090303030b030709020711090c09010e0108040f0807052109010906031805191401060e0606 70
    0x40001490000c1441451000110000e00c0b98a1360160101d0030349205010f01c101013a0204400c0c02181c0040300100440c031b1181e60242d080c0200744d103420300b801201b68481030060343c4800700d054940c0c40d10854070f54031001302541003211000c50b40d040c0250485d0000741940c03070b501050204896513074807405411801c2954444400040b2000000e107000c6006490845143c1320301c0b02c0600481c1030200d55102501d5040e0344481800d0310303540b01100907114220200d0b4160080960104041025000402245000e0480e101c1164043c40500c259400000c111003044141406802c0040c0e07800549010120380901e4480d4080d00d45003030042880d0401310005024401c006401401c010f004614001070a01c00141d24181405034072805450b8451110744500003410b1480c21f10110740a544040e042c240710407282d11980c50030399030b0103107001009910411940d080900d01420041d42200803201260200003d201840c40c2c8601800300d4080074040b9481040081a20481100710300d90001c041c200e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 804906115 1250 804904865 804904871
    0xc23030f010509310201021905060609100f140f0301050114120708031b0d05030405060a2c2d0d200d080411011e140403050318011701030c180f 63
    0x414880780c40c0340003013103408034054001c030046000c090004034001710f03003150800c0241c807407a5175410400c0500c900041c0000100040703000c6c0464400c1d00841018003400c2c2030100075085003203580c10488140f4200c1400762103a81400c0040c00b012040d1851400d10500a4609900c0075091030b13900b604065540e00000260f20000c285120408071100707140012920040a44945220b00740c401c544502c02102d001e0826808003001c50341a0910b54440f00040048940304220703002c024800792407180440800b121b20394081c4004c6503100da0101e041a00c014025210303911030020503003d903a01c030140c1072002d0781800308070307000b140c540c03900c00310b4160b10000120190392000001880160041710250390995112008140f00107495000c0c40b1002c0b580312001e85156910500c51104503503151030049005100e5005020020000350204054030002c031119150403103a203080c8000400724040084114502d00c1e103080104049958600300f8000d031810300c0d044850300008241890082c01c0341c0d0070b419501c1c40ca = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 804907365 1250 804906115 804906181
    0x30e0c012106120b011403030a020a0f030c0506040f0506131505060402040f082d060a05100801090c08061302100f0e0a0305010b040b09011d1003060c23030f010509 72
    0x102003021074143ca95011b425404178a161043c16581c5c0514030951001d81c0c0441c000c0d80c0440e05010300240340314881e00d0007004600c600d0f0386079800c050081e10101d4a05118000c0101004000d000031940f1800b200012501d0804076207c803401294181044502a1341d00c80100d0b0041d1150f804680140c50440d05c140d44843e920080c1c0d5560301402d1424144060040c5140008003104500c00001000e10000030405503d4104130328008280140c01184001d8810304000795420080c0181c4004a0046d84080030040c6440301d55030506400078031030240c103800241c0726001a940c2c0c030f8042440d1925407511000901c50b10300c06072035010050381103551041c849440003040010542180a21f00c0e01a00c00b0b20013039020303c040c04070201007801500000b06000d050348138581983c18249511110102507507081d1a9a40c81e00001c480a10601800140c00030901c10749500810110b4540341581c03581e9980346217070042d401c51420f075040c0100742c8542c090801103040400d07141a46480629102d01441e8104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 804908615 1250 804907365 804907373
    0x512010f110c0c240a0e041503200a03081b030403060e01290d02010e100c0b07020f030a05031e070305100e0f070e01020f0706050307030e0c01210612 66
    0x90400d02e0307414802d110b044500300c00750802c01c00310555000b191151816451040d000920950400e0094504010403000e031900c003903442c1d00500898211001c0d81017107483c11400c042c41c02c042d414800665010740020210110385a6400410450341c00c41c0f04c168030741b281017980d400c84c00200c214659161001040120034800d00e90310602004000000030006d80c0b03000c4c1c445661302002181e1503245020148440074183c1815030141c8201c40c81450401c0001400000040390103003515402d40000c2e03da60000c40030000307220100b80d048000c1c0d0004010011503070301003540d01d1041050300e01c01c1290101c04204070041c00314038081140048820b11274149801072004004004c125007400e00e5500ca100d000844085158206001e007450000d407400b1075842500c01c1d1928011103411a04600c182c0d4460000b81405201e050f002d07200305c1d503034941d030303410b14100090070394290f100114120303044207400c0405681c00c1000c404000600d40c0800702d04014240380d0500800c3c09601846040c1e1054a51400304 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 804909865 1250 804908615 804908617
    0x50a060606030f150501080a0b09011202031e100c050c010c0f20060a0207030e1503060f040c0e240c010b040e03070305180f0406170c190512010f11 65
    0x184549503401c210340072600e00c00701c040c0c40b2828134110b0342d0001c0500500007540b1401050398040c2d092003000c10700000003000704024000c260302001e41821000b19000441c5404d00490700103070742c040a5020806401d416060b03d80207005105004c81d0340c0c60b800041050b02400030f840d401500e1100070809510308103009098140c1c10100d00340014400c012400302055240100341d559200e540c020481d564501c0c07042002541320035010f40500030b030801072150540d5200342e8600000c2c6000712050703c9040c840203000801c0c0c040003186100728100110b41c0481d5a0000381005220000c0b646900c81346003802180903018250010071764000d000050f8813042200541001c3d00070f1070240c0c3c040014411aa40d8261240203c10f0001d0014008000c0800314614a4000401e079480c02052981e044141c00000380480b003082c0c1c05071803201340c490041d00c4125030900c84c40040c0b100c103a5030b000645181151801460301c050142622031220700d010102e50740f80960040314000254074080040c910392004001311 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 804911115 1250 804909865 804909869
    0x210201091e02040b0a0f06050c010b120f060a110313030c0c0f0305120301060801230603151e01082814060a0f0b071103010f05040305130b16060e0a050a0606 69
    0x200d05014006880b810600509411240f0442c1b44104072410a07504071001d0f0b014140502556495942500320342e540e80321400100e4020600401e100030030b030031070386040890041001c890b4514002040003000c030280101c0342c1c0a04110310303c03078a40c5640d02d42a280c044c0c0c0c046014140d00c410a00100700b40d100031f003810040c1c900640446159a61120100707007180300c24010a0001045140100000150700da031400b5010482610f803000188400d020440c0d580003260000303840901412150b10508044003608525400c00f02c0c010031861503800042c011803c080c0004104d002c1d03240e00d07588042e1001c0c8185015905040052041960018101d03002013001d0310039030b22075480284000382080b00c10500c2c0702294104415035080400740e0704e88020400041c50441e03015500d40740360301e10b002c140344a03042c4034501c00d440352134a071201214115110140d0b5040201164030411080c0389032141c081042c09007560214020640300c0d8541300013030070400a00001843e81c403404141e0410072565070400f00c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 804912365 1250 804911115 804911119
    0x14180612101d0c04260627010b0315061210022109060121140115050d08030c07020d02090a020307020c0925031503050106140a03210201091e02 63
    0x400c810390a0403180300c03007a0f0308000d2a000070801002103441010300005414a103007a10550741402204003428490202c5241d00001500e468001c001c19114102e244000c0c2c02800070007400c0c3c40000801e61300c01e02c4040c04444000340000142d0b041e42c0e403070b9060707035000b480e5803c1e0743c0392902c1000d54901940015041208030081000700d50a600c01402c070151040c41a1401046140d02c0c040c1c5043c60301044071b043c41240c0b68420f00580c0852580c54509070b2803150000001082c030b008010382c04204a050300f145c1e01c16100f4900c94008191004241c1c0d402440000d80203607100321501c00100304031032141c8000e401c0b220300e0003041f45d003031010360156202d1001d070b40a5459000c91413013000900001210214103c280780000e881c4803807040201203024150a040c00905c80c0c51300008034800c1e40e42988101e5460303440d401c080c080c40340040c4030400541815030740c241d540c038115914000d10310004801c040001855000c03110900b0310035040481083d800c10035004c5503101c501c64407540250454800e034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 804913615 1250 804912365 804912389
    0x9030606010e0303030112080909280516050c07120302030a0909141303030609050903040f0f0b031902091c26090d0204060302091f061418061210 64
    0x24140e54001c50b12010182c0c00180030f18696800c012001a004864210031f4603400d005001c544540e07101e03c01480d0207800c001100d51030820119481200c1c1d0164031610640f074a0030003003070048030070540740540880ea00714100144c443c420b80f14024904100e5901401d00541080e00260a0607004802060030040b103a07030304e0f40050340b6181d000c0305595a1003296221407880800064100c0d001b0710700665603611a00d000f043c06541c403044c1c0c00644009640d40040fa41000a04001c85141d60b0a040010404c00d4042402c40d85450840b00301c501009010303040c940041c1d070320381c01042c07845d030b0440c0d1403544010314024407200e84080415000d40700c000b040301c2660b8200012038a102c480211b44882c04410f4541610702741d030700d9080c4540440200402c90300702e46c8030500480141da450401c3d92003001200600c4501072442610000d00d100c00d648000705010154142000801481c0d0490743e9007810b214600b198a080100400c00c1e0f441808102c00c0e03460360000a02c00070401181d4400d04a41481c0244 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 804914865 1250 804913615 804913621
    0x27090c080c09030a060507050d06081e06060906101806120f021c0e2404030e10080402370e090312010302040506030f16060215040201121d01020708090306 68
    0x307480300744030314070800d54141c0c481086400010b20303a0300202d903c07014510302182004c084811503810b807081c58212050b00d03042000d011001100c8069200c2160420740020816800c228006c581e880c1c0e000742c0124058141212001000c1d4021509100342e84266500075088550b14440100000502803800c2189030078080c079807444524500a03a00c42c45104074034200c48010390800d04004100726000c2c03e40d0360041e03401d00c0b04c01443c40b09280c006c5203101403122125242c20b14000701740b0043d020302640300b40c000c8050485650703804a02103030b0185e8141c07a004c64082e8100d04440500303d01c0304003101001c040711171030070607171161018031022030b82c0f4150740203040d4942400d0345071280030300e071000c001c4004c07510010030140c60542c101d65003005019055078a0400300c11034080c20424441d50212070140005410080c840d81000352141c0c249110071220703241c0c141940001c0154108550000d40952113030082c20000c1c244e1003004000f031a120001319543d0101f8a080360782030f04980c40d11440f0340100800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 804916115 1250 804914865 804914881
    0x905010503190b150c1005090604030507030c03170408120903032e1a0c06060102120d090309050603270f031b070302041104090b040908040627090c08 66
    0xd8a010301c1d0450314016108003010360b00780081003141000396100c84e022482c654500030010003030203072800200103005e50f01c2986006000781c030409001404140d105604100119610600b1f03901e0a541c1441c040e0100c40190800700d03121124200052016401c0206000400c91410300414001860400590361503844554803074603404102c5011056103071512840d002f002c00499000025690b41c01010503058944100010785407003c442c00780400800500101c800c2c0e4100700f0154406001d1000f06141c0d0010802903000d40072380100c003010151a80342220816009016441c0605000340a030780e100e180c5480c0941c82e043ca400c0011861141c581e500300040480441c0403050342807014001d52600c03e183c0845500391403003c410402c0c5026004000c40182d0f11800f4850322100c4400d200c0e51581d0921050710101c4420a400754400c500e0102c070280001d507a001520101d6006c2e091100d5440f00d201d07030500180005444d0703145550031120b008241403039a40c1c00405140b00c40d6407032024603521620 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 804917365 1250 804916115 804916117
    0xe0c1b011a13020d0608030403020a09020703120209040f05072703050726060916080d08010b0901032a090f0b0d050c1b0d020c15120615160309050105 66
    0x40d070a210460408403002260402154903061140da40000601d40680802d99404440641d0040c50309500b00040c1003042d890510404406002d5000d0704600d00790307a558016007809030f0f0200750440c445d000304060a01e90b0b143c1e80a000c90190031042442a490001030050010320000300400c0341c0100c0b4500501c20726580d030180d1060726030103801003c6142c100082134600601c0466a50301c40907500003016500c0b4000c2c00319502401c2d41d50010819181c54074a982580e0113503400c500611360215182c4c201240e0321084480c1115079201d60396940d03500c0c80703004078060040100c030300c8203101c1d55540c07004c1141c02d440b6900203828210384c0c48545241d126034502d6540c050a201c3c900d0307c107030f091090749903d2a040c1e10070b40c0c00c8000e0366010361502c52041c2494104803041507282c50a508180c1d90001016010700c04c3c400020011503100c60402c1c640354410b075060003912000f80c0c40004034070020b0250745404425402c4c0d131483e1a10141c42c0d103840201c404440f244d00307004a0003c3d0020f80001115402a8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 804918615 1250 804917365 804917381
    0xa24060e090405030408120309071d040303332301080c032205030705060115050403060504050709090b190c080601030b0d0204020d06081c08070807090e0c1b01 70
    0x103600e1805003000309040012401d405071054556000400000428000412009641c0012181d1903074603403402303004090900101da4080c07250b140b40800c1d401c90305da060780402036000b40d25081c00200d10f01d00701501c000100c0d002c0c5410302407110032103080e201e034120300e82914111083d000c9020340c0d030f404064500c100e882800300500d02041010f0042556414440c4c00303035500c07654845004005145000311412070041d000b005484030342001408030217204082c00414091700317040c0c00075032440350300c2c200042c40d512031440041d000c1556980407504000040c080e040003094101010301c020101c50403c0041032009803143c42c90050b0340002e0002d48402406042e19400f09a1900903440d0350b0000107401600c2c1e4688020303882500007031344100603603603407010b030801c443c01c500002070762810402058a01200513000719000c102405105103210380c401c100d25170215141c54480420784400a09450308100c94004c000d038946c1c040100a038030710b0510040d0003000d51941c0300c1c4074070064182c40d06088541d40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 804919865 1250 804918615 804918617
    0xd061122170d11010e070b0304030e12060c070309050306160801060914100c061e39051c090b061c0305030c0c060a0614030d0f0c030c0501050a2406 65
    0xb08403020b1400307000b1610002c60000583c0042000e004040c81282800f002d50010800c02401200f0301003850f074016001c4031490340a032414401410b01d50403003662010010b081c600c01d00c500280306c0003098801d0140b00d00408000c2c0403a426428007620071444028890200d600044584000050b2144203a1213001114103071410081c04802d11402e101403000c100c0f9490301032001129424000880c503200b083c90240e001c0700c1c100110305007100c0b514113403200d100c0404e440e03094180c44910305140d041c05690303100c1010700071007540c0180c0410560307890152000e003000c08540c00e00070014a80c01038100442a81c828041003540342d499804105040720b0000ca02144200d07800c90000c0080e01a40055801060b00ca040d1401e00001140b000e01d40700c000c0300c43c03600c03940d281c4070100b00d944007510281c0900c2d03604074040d15119400c035100609074945c44615204005441e6050800e250007000307500d41554200000344071904d8804c2c2c0b694041c01700019010308110f00e100c80041c1840140e20180c05880b11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 804921115 1250 804919865 804919873
    0x30f0304021005250210030b0102030d02030601020f060a05010905060109140d050c0d060e060a0506060a18030b180705011103070b0a15180c0810050d06112217 70
    0x1a03400b480003480c40501d0490900a04111401c40c0c0140ba066076188804400919190901c80d40b0521114050f034001031020f05041019a03440c982e008025039820a03000303540143c0f03e40d01d080040b882d041c01600241020f00443c03041c032400288680105044e5201d01c10107200e076441c1e80c8011228201540b06030340ea00000542d8a686610b80010602d1006020300101d40024007140700003201042401011616966245595154110184003041d84a45810410040740c41d041011869912620000d201001010b81d03000b0038161418941310090b50304041c09a44504c1c0c0701403941c4805110710341c001e0942c450b41c1c00004241d886480d904c20840a020051820b00ca81c03130350740035549140980840c5a181d1180704d155001ea0403002d200000f000c90941840014040030242821036002040f804100000340341007001c3c3c20703501d071209000c6680030380e50241545001c2c00c00000900c0e00b440400385900c800609086241e11000030314110081044001c5000c07556124509144030410311000da81e504 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 804922365 1250 804921115 804921121
    0xf150c090d051c030c030f0903050f0c1c09030b1501021209010e06070305030105151602010f021f06140108040c060804020d06060b0d0f020909011a1201030b01030302010c02030f03 79
    0x40540322200c036944550126070881d00c031010704001d0510f0250030800000d45d241d0709142180e80c90b000302c003869a81040c040040d0b11103500d0050251282203108054407200151003003000c5001c211181030300f658504510170315448080020941205884103a0b8100750110125021960000200c01e6203d0142c00415840c01280240c0000750401601c079414480780101c03a50b00c60311240002e111081c4281d03641c80e41c86d030415082046000342000c2900c8012014000b0100d100384a07024042584c3d02400c150b205ca00c54958100c3c9407480a400043d12030720705840d42d07030f051541d5400c000162500b03402c0040d090060030303004403003101c4200c6d009040076030210f204025290040d04000d81280c0060000c1c01d54408686408040da030140c0c2c00585120302c005010319004c20f5512407110031114841c0e0a40ca8038280e000050201d040c10300801030b0b000c012681c9400108803103c2225401642444942030039a504d042020300d19209200a8000d5400c1c01c041403120344c404011a0b41c0d90302c2c005040303404d41d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 804923615 1250 804922365 804922369
    0x10902090a06020606101215080a2616020a0b0c07030309080111071415090304240c03030b0609100e0f010318030503071202030a09030e1f0507061d0f150c09 69
    0x7400b060914250750b66030280c0304005240049203402419a80006092803180380c60071344881820b0000e6405081842f86920031940800d000711a041c5018044408410340c072400092280782c2203a004944400c400101c0c1c1400342d50201d00581241d0282e111002c5060b034070b4075002d090390007450a0154042c000c021203030001d43c18100b1111a0342d2402c0403503601e01e41c1070f05907044074402640c1c1241c159101180801c14400a0f682c0900003074041e81e5450f00d9a0743c1d024000c0c2c02c0d8480707608001c052644546003013000751902e01c180c9142140090003201e6219035254042d02c084007110ba01401000642450f01e100d50081c000c21b804001b12012840340d10070940c508540c0d640003d80b0005c00c0103200c40e46040070b906940061801526104400a0b52810034070300070380969140221140070f514500b205e01d20410400f0507a182c8040390741450390383c8000d01d10344074004060b07001d90300445510240803d85107400004260180340080412144c9598101000c004140011107607102072040c100440c040c54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 804924865 1250 804923615 804923627
    0x30e06010b0d09061d0f0d02162612070b0f010b07170c010603061b080405061b0f04090617011a0f010c023102031504180b010902090a0602060610 64
    0x440c05040001000c5e2503442d181c0424181c14a80c1d41000d920038481012101001c0c401c10002c001c0d540000d154415401840075031b80c0a440c800c610082d6088442601c00c02016040a92000003400c1034070400e612181607d81c898000380c00641d4603030702c1540011000c41c100450700c3e0503203010580072811310061385e0701c80655080100503030300c11160512460707140711000d00407200035522a03140450345550241d1102030782020701400c441001701410920021440c04102c0c0381d003010b10b40d04481070b980e041941650310b40c8100101d40d01c4e050000140010a5440347e13000f503041d83d8070101402207401c0c0001595081e5120f0540c3c070100010000003841070342c40d010825030388136007043c14943e00444054001440c0b000a0400d90a41e02d8a8000300c81000b40c00ca078501c29542000940850450804101554442c00800a06400349031b803092000415100c0081c8902c0c19940451042c001c2d6840d51440b101075000000c1c01402280c0c0c204010841c02d0010480e140700780d6001c0c00300711060142e03110407200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 804926115 1250 804924865 804924881
    0xa11030304031a04030f17060405060105040b07060f0b0607050d0509010908030a03050603010b0a0f0e07020f0d0e0310020306090601030f0b060f0705060106140f0f19030903030e06010b0d 82
    0x4103200800000000542021100b08160150320116600b880c040c00c020304031281c0c2c1803180c8100515000c4050003152148900d40d008002500c001500c0c0c1d4030403005954520480c1c0200c10484030210f4950b080110303e030028851420701c181e09100d41c9103402e082c800c450080800040664100809245e84030b48148040c1c900202c05140c00d015459076101c2c80c0e41035500104c1070800007a22a020000107040900071030342c020200b03960700c4440f50300d01440030884c01030f58028042114001004140110300c04c010907601090b546059500c4000e056602510510200300740301e0003400350078140c42e01c4001c50310071340344a80e2018012981c15582c82c40110001c18043c40c0072800c04c5e545200d4001152a10006884240c4030311040682e10320503030401a14200c3c05030b02140400450400110039900481c055030f000d0b810008180e9250152002881c0d102d00495050711a001c2191742c2080343c41d40d050308118070b01e0380a44c8081000b40d10130191192200000d0051b2580d8006c00c10131a59119048c0d40094a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 804927365 1250 804926115 804926119
    0xc0a11010e03210405100210241703250b09211c06090605091008030f0715051603050702070b0405010e030a152301050f04020c0a150614040204080a11 66
    0x102d000d0715100086c1e01080c08481040060703101403120307180d01c42a407180072000160b03950240000b611b00c0d0114203900b08a40208021604414002c2c2201d2801b04180c45040400c086080c0d03e2140400b080c808082c1c22010a41d01e0740000c01c00702c0c2c880328011802c0001d6600c8520349510fa0038980305041c64aa000404000030000c0c1c03c580039900350302910602c80030300b81c0d254000c80e007507140804210070010090300c0b5a03d1140c11580400904000004503001000e403152190703190300c0c09041400d4415008200d101815081c1010001c60010040c0481c05a10058804109546400368103c1e6116441d000309194042d04000600c503543c0070320007181d0181c10060444074020200e50728401d008140058194a868a801d81e581c0d554960822101da000345500707a2140c80e600d00000501d100c07850340c14150081d80d0000308e54202480a00144800e15009032a01000e81014030030840245072504c2003201800132803a400362149403d008490440b00f58400818030381009403202d890082e04110515 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 804928615 1250 804927365 804927367
    0x10902013504022101050a0f02040e0103020d0f0f081e070f021908070f1401020a0812060607020402070308150409080f030a060503060a0213060e0d12030b0301020c0a11010e0321 78
    0x580c200070540360380444c40c020b4000030030030707080500d42241031311074408100c08a940144811b00218841e0082541161740445990703a0072011410003181d02d5039032000182640703400000340ca0034810107400601c02c0964440c154424890825503113103050280010007010480c03201032400c058904090110b102030058205d68082c141e0380d000c124a000c1441d0300007520701140c80d00401c03d013004104031030381440007800a000c0010342c135a5042d101d8070910064150000c0c0c20b0011801795110001544d12155000d0411566148241000303480800c0c11140ca05030100340e414442c80c00d0800c4e0142c040f100f540100e40314100345605181304900d0704010a065041940d80c1800079550f43c04021150040800610060b641d089005081a86106035000a0203100e600e0070001000c4d2900607844d002150444615240995045811000f41c01c8a002041d070643c00440c0240c0c52a002013480b202c5144240065080e401c0810010f42c1d9040b59401d1050741a003105240102984144e8a83d205604140341c142d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 804929865 1250 804928615 804928639
    0x1b1512060406240e0612150f10090503061e0703020706060f031b051207090911030d05040603292101061706060306060d0308070e130204030506340507021201090201350402 75
    0x4147c4070381c200c214274030015810285c10442d03420306104482c1c1000d200401502d16010308501c1c0104102c001e41660105030340010120140806540035502902c200d4862030303240d07a0781c0c0c01d00343c00c000e0000c601010182007110300001c403447d10100c00e18000300301e0313005045000d207003580d4007005040590f0103841012142c903c0c0d811a43c1d0611200029203c145c440c0d540359820302600070304640a0921001c030501e0541d008140102451a03201d505102c100e581008005411040e8440100c003414040465805c14502040490f410120349074802003800c2110801e54500c41090381d0740a060b1402500701c041c0003800d1011921441649074040424100a050020310001180c1c0c2898240c0a018010341d02103401d104100f020f112168120702c242d201c0d2040e80c150500c001c020511003058440450800c1c11000310041d00070703000c0d2039a41350002e0640c17400c810b00042c003502900191004a0004204050b2100319040c2e0801c240700403090640d0000c0407461100c2c03845000000500181c1e4840142c500d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 804931115 1250 804929865 804929869
    0x30c091e050628080433060905070f020606092d0108030310050f0f06180d05010903300c1e021b1512060406240e0612150f 54
    0x40ca02201e05048083c00608040401d110761004420032108100700c502c01e10000c140000821059540c151805280d103090020041c0071180c000000e0500403030a103c000200f1840b0b50344807a208138060349a40802041c018012a195a030440710960b1001280f030100348221540c10300c0d41d402c031112111194402d504480c100d501c001e0264090202540000100407803420070112200061030166801d04128210030700041d4200c65440c00c6501468000c903100c5940240070401e9290203c010b042b02c492011542410303406040704000035404251922000c0180035062031034000c000210742a1080c15220700000c882c060a034401c03901c0e081002c0c1c55503c0114500480031040e00d980540c004101c101000b03014180c640c5900d0f8181d6110b02c54125124131102046811140c11210301041106241e5441f000140108416086035030320340c140b080c2041054030580100b0140ca0900d807504016103403220100032541c42070030225490040702002044c10175407007032506d5908100080080808000d0200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 804932365 1250 804931115 804931117
    0xa0c05041716090608102711031c090911190c0b0105010f12180c120c051c0204020304020f09100306181e080403021519030c091e0506 59
    0x400c9812604110b003000d6116101858540040c038400703405219581c81c0c010303450703140c14416060b04c01c0300d61102c10481485200384030700c985805146a00641103400383c02c10418542100100c10301074455503103101c040c0480448003503d100090b0742c0d111900c0d420580140301420544100880d0b1500521041c0f0192030010344040b5281d4095442c00034100f03c5040c10b00320400103070310290600001502e510003859103c21855080741c42d21001003a440340305030400803580840f94018003008200c1d507000c11000c0c00c89a18100c21405008004015a141e030308100303403409109000c420358142200c14100600340b90b00a1548503000400740034810050700c000c01c40b2154115400d003210300c105e01c41401000200d02c40c0341070104802c2c002c15030f01ca0055890401d001d00900c01e50030b2020656843c141044020703003c840195901030100c418046000411802c950007850000d210202c001c0c09103040640300c0d02ca1003200440b60b5807031850b00303032400b0042c0072142c6041e54020140d02d0002d4003c1104d4440380 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 804933615 1250 804932365 804932399
    0x40204050f130204150c0201031d2a062b0c052703070f0602070b030c040306021e12042001090e09030906040b030411120d030b061207080402030f150a0c0504 69
    0x900c40f55800b01b40c52000500300c407075411079400070501d40c01c19091203982c00900340100740011150b01142c0c2d04c0c24440c40440045c5882596803011000522507500320b4000130f000a808041d2889080c23614440150009a450480241c030018105002001800710003032882c095044604564480100045021a09101668101e0040d8441e016400c120f03990741000204020480c0070416421410a0611000d95100718407020307000d01c2d004190b81649942c604054144081008400c682d1143d02c006116400c900031202030b60044444080030600d126001b600c3d46150714160344041c0c07918200001e031080e0280c040c010541d5444140f0040c02940c0b100c90080018100c01f0a482c1d0b12403030140340206e07121942d0046240a81c0c00300d4a58230b0900d100082c608400320170f40c1008070f2442102e20200d07801c2e0003100382440b20325035540148080d160700000c40703500a50007a01520820207030220340c941e039110060103400c000340420001840e1100540d01c04401c10313109103050b40c81e29075500b100d8942c0302c00003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 804934865 1250 804933615 804933617
    0x80705090d110102100b0102031b150f0f01062a03030e16031b060f210912020106230909030f030c04060f02070b090402070f022d040204050f13020415 66
    0x2420355802c42c0d80c04016404811103580d00c24000b8400c0e000000351640644046242c0b00b030300911000e0310414007841410407075030340c00e21400e1680c50b11803454085110241c411100001604001281c141c0c41100c441184400716644078a01a80d0082c2000024a044805504260f51146504d0000710280040203407000980c403c0001c682c250b0601d0130159000034088982910b00040420005030030110301c0340e8400c0320382071180007603043c050000d0f5003050500710004901e01d46500701c030400c12400c05c20380c803a0b0500c0d40200a120b032606103035030b01c0300e625500288036001e20901045d0b091414541144e807000c0640180c80c1041018020042c10380c100740c900340240741021605000160744111100700d240e89620003069000d2030842d242c029032203501e101e140a0380d000680582030049982035801c0d016070150a400006410641021810055000310088008001e038000850300c0c09009850036103078010301054400070446c08000d146005240b2903000c46400f07110004181d500400f001403690780c4c3d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 804936115 1250 804934865 804934883
    0x200f060f070302070f210501110409021206010f1b08041802030612070b040b0c010207170a12090b0a020903120d060e07110616030204030f0f020901150c0201080705090d 74
    0x145000f9082c40c041e504040101228098100704100c0510056a105070701003601d9003030b01c00d00d824254090f0011915620102500103000034810b403881e4014102d4a8a00803032590a8440c480111400000c0001420001c0d5840302114860101c4003041c41000d40f0813500030303291030b40c1c4496094401c14081c035028242c0c1e0340881000303024144039000300003210106000c0c11145007010010020360081c7c0c0584040e2036404145419440301c00d50440c1c501c903400503100100004601c44e030340c0710782c0c4c0800b00c190005494000000740e0103409010313003105160320400300502c2d039645a01400081d080240d40c0c692610407542165041e0b1801c00003040c1c000c03035141e40410020306203c012200080301a202c0402c00c80d0030450090000008075a250700440180c2e81c000140650361003c802a0085d03810192001040300070704420441d40304005030103d4800c0c1d844102982c1d80d100a601031a0700c0c0c025000c04158100d00c1000150f11542c80c0d0f41d848810b909299007000c40d00e2001c0380002c0b210703040454140034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 804937365 1250 804936115 804936127
    0x611160909140316120e061303030f0318080f0f030115081b030a050408041d09060703020a0801060507260d050a0225081b030a090506030103200f060f 66
    0x80c2d00584114142c103001149814088010200108240540601009074544061015034441d0022202c0100003c144940712a00002c0340c15508019100840c08140d000d40c0da42d8886002e80078103680707508d40b40502d050704071241d2205c3c043d82d4080116084241010050184031865000155010f00749805001d1880308a052002d042200c0240000d04404030b1941140c400e4101581140d510232048500480c4c59225842c00824600854100c8031094845011100c2c2c801701004a452040e0b1b600300840700316894000c001d034101d10500d10010008bc5003000107110071801000203144140c4034417544228141407500c1c0d101a000c0800c42031500a0300012100d60381c0005014154100300a940c0840c9402c10006c040c000040880144411589001c0842818890840160f80550b410b41040995039070f03400300080d0700da6101c0801000031564507900810383d41001e8054034147c0f9884043c1c0d04c01c000e040751501080325844c000550340031207241e006c400c16803268806041c18101d004c0310b0320b80f240 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 804938615 1250 804937365 804937373
    0x51612050c0a0b030114030106080d0e01031a090730050f07030e100914010e0c030709020703230c010c0206220f0201080705370314010611160909 64
    0x10161101640b06071202e84083c048601c100c2c0c2240d04503030300403c05c461000340d040042400340c0a181e200350500d0284002c46141640c0100c8040411402607034100702c0814112249500c0004001c42250800000c3d030000d0344080c020b00e0300c0301a9080c80c0c0d0407162180c040641c89038200610845203440c05451724103119040c0306840000780c01542d11700707050050445046200f40d88094804e10b0350911500d6500384020710022a00c850700f4a09010003e00007080110380081d43c6280d00c041b242d0003031141590015519542d0f2080c0d94441d036140d80c40440c00c1d0555004000780501c2d0610002644004114a03d5200403d20410690308500c0c0c015103060316044003078400410310131851106403c644464100001c4040d23000c070b0b14442c0d090030300c8005074403020310841e00307402000311030390401482150b0f107164030a084c00345158455205810010020b0304000c21001c7e80c00d42500400e03414174650061084074090800010204c5490b412142000344680741801e0b03440c01640b111202540d200f8000c0140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 804939865 1250 804938615 804938623
    0x5120a030c030b010f020c01050315090901020315220b0111030a0f02060108190b04210c060f060311150f0f0d0608010c050409050a06090c030e0f120a030905161205 72
    0x1a40c2405c3c0400754030b001d079401a480300f142c00c1e01241080b03030000002c2c41c0c0030f5010803581501c20707015061480b20301c0c103496024000c5d841640c44201201e504842103200b841e12210b0101b08503111440d594282902d100f00f20083c0460300305850600001c0c4905202032030080000d01181c0d8002e9a4001c500a14860003a04189040e0060300054100b242d0091080b0740001300040065488000c40145a0b5039003418900140c075680d80e04540d010342d1158141003548540098419402504c1c1048140d2984100b1000c079541444014a0008841c0d0580e400340b8203005a0809401900348851600020320a00078060380030415402148001240a4000704500e110f688007a01a00e0000c10056100140181c00783c0901e01c2003140036a01e07000020352480f84c076000701c40185070307031401808050b00c032407002303400303091098521031083c0303e2a241e02d0400d10000403c00b0705a40b85541700742c07400000040c120040c083c54070081c0c0d240c3c0715100c20007103000f0b41078004c0e03070042001000da81c40d08900351034401d0034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 804941115 1250 804939865 804939881
    0x3200a060c0e030d0e0409050f15011d04060c020a0213060e0a060b0405131b0c020f0f100509010e0d121740140d0201020403081605120a030c03 63
    0x100b02d10b20010350000d803070010300d020000303415091940e03080d0300120003d00540607800d0000c01c0e60081200c60711200d0000542406101022407180c1c04a0b80c0341c40044201c40c42c0300c1c000500c201160b601080214030380d544801d80c403251501c15201d0030303031043d0003080c0d036803a61203020317004030b69a07200802405118840c41c1c0e8104002e85428004603207401c10241c114001c40c01281e1085c0c958128a583c180e0042c0d00070200f40d0070341c2ca0341b0303c074044148101601c00e600c0d44005a024010b5900260301074507040c8200583ca1000070088000c8500740101142c0c070750041201c9905010103580250034542c0c940c203081001c00d2084000d14001801020010000410680c2c00c04c59404103000b4032098244280c0d6484101b1780c40c4a64128052802c421a0368624407030000c0d4a071160090020020302c4120700380c0036580c1c0d203604111618440c005504034204c0c0700321320000e8401c8a09008071090800c5001c49150b41e180a40c1c121480030a070350342501c070158001804500829036980c802d034080c1380c06000300d8132 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 804942365 1250 804941115 804941117
    0x1401030b06030c010311122205070f06031808091201020f091008091c09090f051506040812030a020f030106050702030c040b1804170708070c05032803200a060c 70
    0x4046c1e04481014000c6001d508203041c01c518600300000c121601240780e11180303840342070607441410414109103449107113a0044144109206402280c0a1b0090149441d1607000c40c400460696890b00e030003105801851415601602c1c402052245600c01d0000d000d0032020681e0b4103036190708540c1004211109450003002b4407100b00100310f1101c0707004c10480c8550b0350130300c4010a11031403140f044a041400741c21400c0003514003070941c01c1c01d00156200c50300c6400d007144001303103040c0703400700b0060180038a00c0b500c04181d0081c0011542d00d0180d134061600414024005400d000030760b1104892900300b47c008a002030400f14880d000d5180401205001100681c1c080040502d0000410304480c11910050103103d07145020404124a9501546034009045007294650071907203081492940011030030f9a40002580012810380b5010502c0b5544090503500401c568201003049280302020110540601003110062084024980c2c50a08154210405000420318500d01f0000b22014446220 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 804943615 1250 804942365 804942371
    0xc050c030f0c061b0706020d0f0c0315081b0103020915120f0606161b080718050c041415090306071710050121060b19080106050705030703050d1401030b06030c0103 72
    0x1d241e01242c4104d44017035403c008056a50540a5401c001400c000d95240030f10500d045005805946d0540c00403881050075007081e0b005583d1000c1c0c4565a5240701034a1242d02c1003290074146540c00b075401810f81501c00740c030a00f00e083c100c0c410349146c1e82106c0c0b41054122410002c1041d4070541050842c0c1c4007130125401400e00c00c441120787c100e40000340c030052040c0d41d0440f9410387c40c903c0700780410091502d003045812054445200e00c0c03070a403421204005050400d8040b9290016030341c00c1c0ca00340e40c5046000a2002c0480b03081001400e00010a80c500c9d110411074280c40b51400d0010603c0b0b42165258480c2074606010030b4420460b005190350000c6540b003109100aa9120304408280780a2410429010202941441c0103003a150301100b000c220004009074502d119a0802030846041c1c1c4481c011a03a031080705565500c200a0010010381040184a0001c0d0166000c0c200d80c880c076030800a08292458204a01490300b030b0801ea4404540100f0030034603150400c04c40c3c0941000386414 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 804944865 1250 804943615 804943651
    0x90f06011211190507050a050d0f030b09070e0105120c0a11061003150605090405010c0e0901030b070503150306040f02040606020d0503160c0b0a05100e06010f030c050c030f0c06 78
    0x8002c250003280c0307003561040088840806218442d4003640c0210303400806448080b2454a0480e9440070002340780d8020814042e1403c02460003845580418200900b6400142e81c607180102e03136040490910a050107020300c40c0d01d2200f505400759030300c1500e14480aa640e80c000d2000940482c0c1d0002511503282d12000410210f102900c4c020002c8aa1002140b078840703252800303071405013050383c00590308183e20300c0802041c8001500440d02400b2507445000e1143d80c2c86040c404149401d00000d41800c41010200380c40502c20001503038071000038416012440415000242010001c0da010303201980485c040205500e2b041c4500b0b40140342d00c0c001404940308070180504980401801c074440e0300d08061b0302081203401541ba0309800c1d44d00c4a60750746107241c5030115400400056507a0040e8000d40c00c404143c40540f0400c8030300404058482031420441e5600890141c03030820603840401202b4094009092402c002400030300c86864109a00c9000b900d118a01d8448001d000d464a14026145 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 804946115 1250 804944865 804944891
    0x6010b0d14040507060e150d27050a110301150312051902030904060b090a060e03070b030c12071412090f0613060f0203060607021003110301030602030105041d0c01031a090f060112 79
    0xb11000e0400c0c0c804089109408a05004032009208609030441c009c204524001c000300861320311807407441000c2418890010006040c201c03030384840540c0c1d6080360780300e090011480081d049227075822186000c0b860714001000340d40380010325004040140c1d00228040c2214a8180910383c0589030b079800c007600380605000029000c00c06485441c0c24044034003134210b040d88003440781101400302c002d0610f9890400e60802c250720390010b9880680c4070000b501080416200d424a201008070304e10b0000d081c0000e4a128070700c1944003500c820f18500c5110303102444a01e062150b54491a0703508501e8550400a081c5002901e41540220761024410810002c2d5565642d045d1a17006406a44294441c99011419070040483c0160b020040e280440004200030300c07500110f040c0c0e10706a27010b010b540d0700c0d1089a0b00c070f108032101c00070f031942105a00080c0341d40300342e01054950f08103042031030700c400d00240814182103003525200c0700d02c0b1460b0100841540c200d60180501c1c5500e20b400c0200c0c01110b01303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 804947365 1250 804946115 804946117
    0x70519060e1b060c0a06050c0726120c0c060408031005030f0d050f130f05130c09031e1b03120801030503040e13020315011a0c06010b0d14040507060e15 67
    0xb0051050f4004075000310100d0341004034800300f50303120360104014209000215026040440c0840e944103843c554108003a01e0f280c40041c1e10720a04102c070303080c9055420212030303210004100304000e00d005d12040041c00010001203001c1da0090700c15660f242001c0f040000343c01e259803c2a4040e9004000500c04075400041c2502101c40c2840e20540b9a55600b461150921038180b101d0055160000040303110b403170342001e41c8112541120112100780c0d040d40c5c2d180560385a02038042c04150302103010808660858104000103621421000c0860002e54400030b014a00780031065000e0040d020034810440e00c405600c0f42865241440101989144d440541c2c03031266016403003800012201240b00114000060018554010190340075074a04841e00c0c0c0544109110f0040e2000550000d4600e041495003140e611500000181220360f0070701e14070320110341c4800300003260365640d4a02450403110341c1403180e0056110300d010309202d61600b08001c2c80051803402d1140f1909503103d01d5600c3d40402c0c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 804948615 1250 804947365 804947413
    0x1030213060b030a09110a03050c030d0806010806120c030712021008010b0a03090204060b0d02180604050105040504090206070605041a070815040509150108010c03051503070e0c070519060e 83
    0x400041080c22252405501c2c1b5860640d4541e008000108040300304680810300004400013a800c40d0ba0003041c1c1c0e1800c40b07100c2c05c01c0d54481c0c0492102d50200f0520700340204078200b4020514103d52040004001083c50b00c8050b510000207000d0000c40300c0c1c118900b110b01c4492001c014500a46c5950500885008038403a41c0132003002c2c1039580e4030017030031521160403940c010894400d01702e0320350402c1c082402c040e51081c1c40b40e840008920303000440c00d2070b00e40e0554041d106e06a48003424a0704100c18840101a448420f9a00000c103100070380004a10b802550301c981c0c80380764000318107043c101c580c1107503090180801d41406171a8040241e181188401109003480840f008203c07522080482800e101c0c0c07510a8661004109001050102054214458404460b9000c000a40e115504080783e40711340e21070f003a8107401000c4d0401c10303059006012a000f05079120713002c0c5081c805030340c0d0320302d0f0080d61003100342c104080e001e030710045c00740501c40c003030300c2c3c0c2150b01c05001c5002c050000c40561840c08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 804949865 1250 804948615 804948631
    0x114120c031026060601090602101d010c030606110601030206030c21040302010e120705060c1308010204151b0c210507030515010b0f040b07020d060f0501030213060b03 74
    0x10000442d01140c1441c0c41004000c1c1e10409102d01c15001075041d43c0da107199030160a40d120b20b00200e0610351040720000308440150740a00401d001c4400180b0203444400c000080003000e00d2562010180203208184200c4126100012201c1c07500c480600b0b480303000340312242590009801080580c85a008072540480c0c10810190364080c01c010b24280b4808980ba4400103008401c104802c0540540c040c0007060405011603c000e407103d4507200c0e01d442050401000c1d50010008501000c29843c0600044042f0030070346010075480e402c5c40390881e0416400040f0780704000c6101945690803980b24801c0038449105007440419546800009203024400c10340070169800d640c25610700c0b1400c088001540c050700b62642c1540c2c03400c040f41d461942246d0040d030341281100001e0110400021202c0f210302d0902440d0405d89014001d803699080048185d0300b00c0c5403500301e800024468070403061104000b00340090350794190b0052101710070080d0a280c000f40c1c9010700c1070044080b08002c0d244d0000c11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 804951115 1250 804949865 804949867
    0x1b02060106052107030504062d020c01110a03270f11150424020a020a120203031b0d0201150b220305011407020c060313121112090114120c 61
    0x420f00410852000052222191400c524188081d03d40d042d0030040c0241e01407071041c4101120200815102c1006074117401c00140d001103200d035903485e036401a1249490400002980c0300890000c1180c0e98488905c480004c0d654124070101c0c804511010210b14100d004903c07003540c110307039030b40c510160a602d01900c2c006610200114903910100e14074030300c6030a01c0c0c405441c0c0784e0f0388481d1981c01c841e241d170009510b0f40c02c1c3e03010b4209030310008a0b0583c0580081000d041680341038401c039000e00e82c1010681c0c050208112810b010555040044d051306001c3c1d008029901025070000d007111040f1009a0f40c45980400401000f4510b0080d210042c044405944100e90242100c0c190380d8003070307440100203500308981c404442e0100e0f08000d121303c41d07640a81d0851448001008101d120459880c40040380c1401c0541c00b00d04514080f2100d604c01d030410040c500d883ca5001b501c3c00014943c4c1c1c1c0880e150002d00c0d2500c0d2b590209481c002034101ca008a070401c103000b940c40034090b070020500091048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 804952365 1250 804951115 804951127
    0x61d0c0d0609020a030207050f0312010e0903070602031608070905130e0102071403030f07050921010915050912040b040608040f170307030501050d02030606090a090c0b0c011b0206010605 82
    0x4a5911000040090840c02c542c0c4d510001c1003e0041d410141003690617008803079042d5007619000c4102c4d03400005288128400d80c0c01c25511400c60034000e0108801484240090000500b040c03000314040e1401d4010b64500740140c0c14010f040e5a8020212070400104440c2040039864618040c5440e204200010490134500300d8803074024024440007070b0060551910034010f10001000650080b4004c3d01c1621311603440740b0007520305200791550140c020800c040c2d8000e4950342c41e0040e0440c181003030008941c032101500c511544201344902109003075568028845c3c900400c1000401d128640c0c3c0c80305007003618000c40c0021600480c4100c100b40002c07035001508004658581342d000c180d00150002e060000c1d480c00002e560021694000424900380c0082518900b9290b031010480e801001082e580d0344143c04d100009901800711003500303444001c1c10340096682241c44000d088180c000c2600e9020300c900711070030b4620221b0307480050300b423007140074102c01c0c2d001c504181558828244255140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 804953615 1250 804952365 804952387
    0xa020c1005060f0924030303100603230414010b030c010816180603060e0a09020d060c09080a05030306150703170702100516020f010b220621030201061d0c 68
    0x20000401490b4049080307020408015003000200100001406085038817108a10074140e42e480203036400c500100c07600008010f8540319421410700d80d6055a12114202e803512540004000203580c2101d01071440c5422181c080801d206010f002c0a084005000603107122001a005000240c0fa08141248000c600c2506a00401401082199280d1812101580c0d520010010203040c00390b504405441001b0408242041c0030301c42200350010b044041c91041c3d983c1e00001071610003c800e05110484000058490301403002d0000c03240120051aa40c9c6000360411180180c0c680950500e942e0a01c4000040381c2d0081c480c41414403030761308038007680e2201d0070260b103003442902103c00304e5801d0400304525040114041c400402c2d55400301d0741c000e5009003000303090ba605c49100c56040380c00b400320f4007000d90462015155000c502800000c0107034542104900100030018503000f030b00060040c040415509104403002451366400c0d06041c401442400307048024094444850040013003007201c2c0310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 804954865 1250 804953615 804953629
    0x2090f04020d11160b070509011403090106080d18120c06120209031b010e030127060e01020a180e04050d08090102160c08010f1824140f0a020c100506 66
    0x24550f0580c1562540e915028002124490b08804c481030300c81c01c00031030030890041098641e40e6005848035005e070881e5041c05005500700030300c4184179648490000030036410030310405002e820717a6601d00041c460701d62660035407440282d011100f02c0704111620408103544039940350a80d070661902800358031030700e2012006800750080c605e030b01d402a08802030141003000c11949100b442070701c0b40e048514042d01003500302d40010b0b481d01c1401558503050507c0c643c56034a0740c200c081c4255400502084c2d107a801c2401c98010b8801c28002c64000e5941d2441d8524100071103004100e8800c0b9051315107810f9582e56151030755000c621040c800d6580100324151020340554502c0c0700503900d0038803010b160b07052401400d071441c424508294601a0600309654045c020b6909030803240c0380c60b0043d4100d44e076403003101d82904100740350100d01c0815000c04840e003501403144100500140d074003407401c2c01280d0210400001d80941c1c00346d0b00c1005528154807002c1007515048103040070010f4a592598041109 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 804956115 1250 804954865 804954881
    0x5010c050a060e010218010804023f0304050f061c090602040e0f01060f02070e04080906071406010f150c150209060d02070501051003030504030b090309060307051b0102090f04020d 79
    0x842c605000c3c003030850181c15409030442d4803802804c0c03132100111000640d541201920013942012441000c4500038070a0400d15400050350740e10950860503519208216185000c6840180d402c001410001c5150a50254601c018126049850880e5940180161020109651090540b180e200380140681941580c0003440c40f071444080c03a00e00f030814000120024090600400c4010b42c05c04401c0d440000c0c030030306503868001c07511495166502c44140b25008810f842d980103c0400500340001c0211240503c4510100010545035040604c812000032068104a00f0010101c0da802d100720b501882941026800c04d04400681c1c1c2c0a042c03640283c4941655141c21607400256500300711040da000b044e0f128050402048241c0303854201a105080c079100207400184144010300c0422200110103420840c200d040300d00d425080c0b80170440d95002110a000416008904904003c005d01e040d095005035801c000c514044101000940c8402c0c0386040c0c501595000c20a040703825895445030341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 804957365 1250 804956115 804956123
    0xb0f070611040b0a030506150316030209060d1805060906041502090429012c060c03040f030b010612140a020c0a06061202130b2209020d080a0f0206040c05010c050a 72
    0x81d0310041c4c024003401418054407014000d000e0320380240c9000102006407070140031084c40c2046902c0a0010450123034010221569000d074042080c058441018411803003032240e25211189164041c1c00e0030707414044001d10380d80c60740d0409410000060080c0040020b4040a010016110f030b9080c0e01060042c60380c04120040081095080300205901c0c10140c40610030984e00c1c411000303004501c10302090103405017070000610045032100c051410001920380b083c03064084900303145d074504078142012196441607900160b000014082a40e0044020005000780a400d100b034200303103208000c07240740003400510301c640e02260005120401717210604003281c20078014000d003519851449880c280b0108102d1081d512104000f030342c004c40e4003c0c03005400c8018841c108030320115449102c0348045040c1d00c05855900d44002c0c0c010307512110310004c1c281c0212505500c40c1190240174009140e034a6259080d584030740e0400c00002c603500201800d8500c2840d0100c019501c0d8506180760201c1e0b074000038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 804958615 1250 804957365 804957367
    0x819031b14060a0e0f1b012a030f030b01020309030607080a0608061623071112190203010e0c030c060705031b0d0f090509041101020c031b09010b0f070611040b 70
    0x800769000d144c000101c040001c070151a03000c0c0c0c00c64101a91410004c001174100b040c0f61111205542c01800b0408000e58140441e00201c400b004500b509110007042c01c50105e8403203800300049070b0f4148501c458200c030a000035841c00b8601e10000b40e9502004120404020403040041d041480680020004003000012240c5901b0aa04401828070008400c1400905002602c80180ba0f00241e11500f12440340e194903e00740e04d03030311031100b440000d11903603801030f140c20020080b800e82004007448000c60801c1a40780383c601c510415013520150f407411203583d40100a0380c6600e0f540030172010004101250080d41c0c2e81c0312890594110b0060b1200f850380b2038014407000c444060041008090b0b12581d556007d10068401d109803002d007901c0c06040e070800b28600c0020001901c0d1260010300070014012100003102010010346010150301c1420b04584420150404c0b906099840318003402d031401c503960800c4040b0039812681e008011001d171940c1d854984054a040c0035100b1a006003000c0c8100c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 804959865 1250 804958615 804958621
    0xb04060602011b030203010b0a0f020a0c030302010903080c03060a14040f05090d090603060605030601030c031512060e0102120c130b070c1d01030309060f120e01060819031b1406 78
    0x7a0090003801420586400505003000b0740621900c21641601da507400c40c1814008020812101c5907054030280d02035101c0c408d0f0000205002681d400000c0d4070944c008200b180551074000c00d0ba25005d4440c14841d80181f081c0690380c0e94030030040e015140b0b005201c1d80740440700e0700042c003d0308031240c1100341c942c501002e01c40a542c0c040741076146950742d40c4a504c2c49039540d00d070490440710170b80b0600700010300034030115469601ca40c002c04d911350600e260200c0ea070b500080181d03101e46180e03880500100b018034204400c2128600880200a000c10021800d0a170455142801910003d10103442000d002524219545552003030401802c3c10f00c031219200c048900e8441420700c424002e06600031004000b44442142140303d240c1178a9141c1c1c2c0c0c06106a14003102035a9412465680308203001e04544643c040a1903403103920b101300764060011440c1450801d03850b003084980c079094841d55075520b0644c40400c0c1c10500282c1341e00f0035800d4000c454441424601c50b90305041d4907103010381c020314041c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 804961115 1250 804959865 804959867
    0x70305070b0f0610050703032003060102010c0c0f02010323090105071d0310022b020904050702031204110a03080703030e0601060e030601140a080a050a0605060105160212010b040606 80
    0x9442101e1146485031040d403652101c2125124003255000d0340301c1c8800102c081e40c680301d440a422518820705000ca5140c241d181d550600001400303207107a1703224000c02084510341c1c0c240a10604a41941000048513819841e00e88840a212402a0500d80c442c0d03044890810504140e800e2040e102000d1200f9003413400307442d030103080151a104006444118840350b1844030500420300c1c0c4600500a00890200041503006500f18400c0f12120070150401101840a5070803000d51002c0daa420041ea03d030b0440c4200012520060003000071503100780b012207074403101c0c002c0706904207406c2000c20002107103040000f83c500030b442e00000c0107a400410b02e481010f404d9040485040f0a0700c0a4076070310380e2a024225801d940030040a6455030040004122890b41c079201d50800d550058104220940c840800c58a841c80000302216154000d0401005000c1d80303108058100d0024a8803910780072100e00f015407440c00409001c2e1003415000742c034426038007095020511003600a0810f00a041d03503400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 804962365 1250 804961115 804961117
    0x20a02180a0b06091c031b0507030209010e09060112050304150e401b0807080702010c0f03020a030b040614031203070f08070207050604170c030a05100b0411070305 72
    0x10207866803400c120301d4108900d042c3c4141d030000341c8094207040140d16419481c0c0500c0d24158426000d00119a0b03d400c800e6112040031024980030740024100c1c01c1c9184140324460005900c907400000300c032401e21031181000304d0818110ba03e01c1800303120340c01c0141421400e521456208160507603101c0004166a904035042c0114480e00301d90700703042e40b003454041801440200103050301100007019030b0458071401200b07203030326122051000074041e07011b00100410008907074038841c00308009100700410a94802100e40d4070000074030090018a45141c2c01800c010071101c040001c1c950046082080c080c4681e00c1090280310040041c8403999a6140d140c0000d258034031030b24028011401240001001d4000b10790240e00581d64140445492100c112003070344001c1c0c9071b8000c501408500142d242e80e11805480941201e42c0300c41845109004041d02c1c01c803266840c14000c6d04800442400b00b40301098082c00d40d04890004140e25a51200040040170355192030070880f0000b003206020b02d03600c20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 804963615 1250 804962365 804962371
    0x19150c050f030427050405070521030301080c130b06090603040510050a020c010b03010501290f0a0203180904031e09050d0b06101b030302090d0206030a09110a06090510020a0218 78
    0x4041c2188a09010714004c00b924011100603240743d1100b44200140d042070030b40060314070450354070b2803090154400d03611300b198420780c00032800b6406452080c02e285881d128146142c1e8030380340e0800801d0b030b40d00b000c61150300450b400e040c850140400010140101407003103285403585041e08100525025000368000e4010f40c016192943c81c0035041318250505201c0d05042c0c901d01c01c10900f01141c400f0382e000c03202c0c4585003c5582c1c01e0090004448411000c4043c04020540741c02950f111400c0e0387c41140c41c00c40c0403141c98452031448084c0f001003508003601b00541d580a6031910f0000d4101c400a458015841e80030980241340c3c03403513920034400f40b403048a000c0c2c2012240c1203c0c0d0700c0825005c81b810101305003c0d030403412a90703034840d000900907402030010322000342600c49030b01071940010b0031940049446070f11003921148442c0801ca0001540310f20180101e0740840d04500706040149002c00d01c1c02001e00a038014407090a40c940200f0003d08065801001080004401c007402c00c01a4402c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 804964865 1250 804963615 804963659
    0x1b172112041203110903060c0708090612010509060a0312082d040515101707090504060c080619061404090626030405130c03090b0901020919150c050f0304 68
    0x449083c6a10b0300e03c0301180c0450030028007c01362611205104415607000d1081214070000402814217241c0f07409019000ba5908038140f9501c96141105110079400000d240c50300c1224007620500010380f4030248962000e00701d1170b2440560380c030340030410480e200c204901f54066079049070501d503400362464030500c250311032402d030364104d44c1c2c0c0b00c1d03d0140c0c00800e0710010500c00020805004101c4c10400d0844440790540443d002d296030f0f041d509080301c1c0252025500c01e0b84407140684a035070003034a400c1e0030180a030b0302922400150b4040341120609400780504010f141e1200020464484041d070b0302801045408000460b5682c2001100b01c0c002c00d0b441c03106c03403014640140b0b00c0b4004410783d01110b5014290114082ca20720401c0e00400e40700780c081c03003415a41c2c0f0300302d0003003140307040358512408a09000590b28a0303400c0030400d8001802250f000b060040120512414450260003010040641800078082801d490f220f402c0c0ba0003503c0090071807101180000c2c0782d80710b094400703402d8458 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 804966115 1250 804964865 804964871
    0x10e19020418030c03261e060a03081605010b060c031207020c03060c0c010e0703080408010f06050a0b0304020d05030c0105010509010b1e09041401031b172112041203 73
    0x307544500d002c444461400b80108032181090b001082c080c040d8480c071000040080080080c2803402d07001030060548424800c24000b14661501e40011310303210390032000807900812170900e542d41c0ca011610618043d80300000c58150740c0c9003001002d400c4807038018002410750b0384030b582c0a01071958a81141421244032240b0b0790204051500102e40000a4031000d000390a06584120102c3c809500c180554481996a00c54205452009000160145229110142e5101d00e0855010709403450000ca000c102441e001c4108916510103100200b00e6045110b110707100d0b0b640d40000f039100c1c0aa15000b4020703000c001070081c900d100c10b41c40b540c1a24030407608034820f81d80f6001128030380d000c1c170341d00c115007050291400807034081d070400a40400340b002400811000b42a1100c00c1081000382c2c01151100001ca60520040b081c1e43c4242000e0400041560710341180d002031541d5840403948510404560707c20100d010f810100b00300d98006203001c81c6410344e07043c64a008414100d2504a903000245 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 804967365 1250 804966115 804966131
    0x9140f0105010903050d1b0206030a090c0902130e06012001060f230915030f06090d0309200d0602040305030a0e0603070905120f07060f0e090f0703050603010e190204 73
    0x3c018160002501c0c0c111004024000c45500190303070354050b8040078408005032074000401607946400441c131851f80c41c2004034007000c451501002041c2c42e600b00241403801480f1413418401c0e0054114200c501d2441010070355190400140c81546a00030980050502c0841c0381014440540041040b901409a1040c0708c560b254407401c582000699040114844030030140401e16000c04180d0704010440045144480740c540020f181025100740c0c011150040e50401418140c00e01030300c3e900b2a61400d0911803040030380d54194400c0e03120448880480300000e500d0343c0d540c80350b12200c91003a0b4404011075a4035100d080c80340e925002492403000144015810b01c80901b171042c00d0328003800b0030381c45040f55a4181810030000071a8810001b000d48501010710301062800c005940091440c0e48803006a400d0310034004019990710a010380c0100031240c144160b03a10529100355200403603190008440d01c1c5c520020f4050000e00d0700146c45449500d1042c0d4444142c08080700c0e1b014400c07501008902c0b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 804968615 1250 804967365 804967367
    0xa031b08070f0e0405010608010e24070903031103070f0c33050706150303090f090e030a0804051603032606030d05030c071b0906080c101809140f010501 67
    0x1070500880080b10b500800c1000f2503d1461241c0e0382082c8280c2c000b094460700c60010030b00310b81003526420311640c407102340340a04a0380c1c01c40e202020552010043c0e03243c540003c0c0a4800407280c8402001c0020b1840300156003c0d0500030b89410650242642240c1c18150a207130110001c1806144031040503e54200c102004e800c118201c8580c18035150741007046038020940b06500000c005584a980307550340d0800c0020070400c51b401451082d11019101c0303061002e0001c44100700d03000110810300c0c0400d0740b20030110000c02d0310701500440c60001c6c1180d0307075840c16500b464019600d102e662880010702004058000680b80305100d0003050700040d4074048040c1000750181590f005416801004503158058800e0f80119071004445d0f40c001c0c0b500381150340e0b000fa614007e100400300501d031841d0a00115055029080c000d01015008215841034000000c040901c007085600074411410303055103401e034004088130024a1880000c011882611041c2049a40c003160402c00c0740203160b0010a242d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 804969865 1250 804968615 804968623
    0xb040b07030b06090d060e03130e0106090608070e100504081c1206050604031101050f0a11060f090d0e0307090c0e13111c0603080a0c0210020c01021002030a0b0a031b08 74
    0x92100174040c04040445486540080007828070340411400100501d039200181a1502002002c807444903a61030b61520078010300c820900c1d0044010440214140040719602580030603040700112a0700006040f510400d0707910b40300b00d40c40054940600103461300d001c2d02c1880c6400320420f040e12020043c2c6240b0558200f00c850318020182d105000344020b0020810707404d075103003036824181031642c81c0070501c20340d00341c16400244c040c10014140d0003d1801611040c03046a402c02c0c4240c1c00400315040080d13400752100c0c80a801182045540c420a0703e0655041008800402c40400208010172120400610500c16003510724001d04074000403194400c01c0703200b00980b44100c00201e0f824504000703003820740d5290144002c074400751900f50110100310204020841c03100c268444503c450454418030146103018601042036401202004503940d0700444c03141c040f8440300e0b400503601d03a04c050aa0000b00400241d40b0b801c00a84800802000104a00daa859104c042003a1540d143d4610b002952 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 804971115 1250 804969865 804969877
    0xc090103150b0f0f0c0a050714011806050a0215070e0f0a03080a08041106191107030c12050f0d08071404140f0d0f03182903070c0b040b07030b06 64
    0x141c52000c101050420904001900c10180002189441d144802c00c440c6d10700001c42d0000d4400e50000341c4100210303e56041c62000781c036020708114402d0700f01610501403040c0c10f8843c0000b8072100180302c8640c21710030300c042185da012068054040f4100700000901c0030000e004c0320350080c0c4050103c1d00d014940840c0340e500b101c0d4800200d6180c0344030104101c1351218090003c40b50303d20300b84500c420a69402018004004240e6842d0300d400c20001c1c13004103110541d2480708416007201c207043c8081800f60141006403510310042d07142c41c0d0028503107a480c0c0407058215519501480c81d0307280c2542d40c403001d09401000c19035103940144025600c64042031049104295200305501c03c00030050800b20700c0c7d9001240b0007001c0c0c0f900c03c80c058a070399920501840c021030025410143d08128400c09011050180140518054103044400403046404c0103680d14a4441e46c408000241c80c2407040994072251075010320750103a03508280c504020324800990701600800d00303085103004a400c0600070390f10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 804972365 1250 804971115 804971129
    0x60114070f020114070803010b190c12031a0316030512030919020402120901240f050409210309060513050d031a1507061a060d02160204050c09010315 66
    0x2408030000d0b070042d1480b0541400200c51620148a82004110418082c50003420111b58003640c030078001c8050f010b44650b26600c1801d000d8444500c001040d040c4100c06940c5c2c065040028006c0181c824030111000403082c0b00e070303151240440000d110007c1c461800301b02c1e4030035001c44410010f038800c41c00d62800112a24440c0c0d51100d01c480c400c03100941070f00050180040c00041c60300124400c2010341c88411104442c503a9103502040c0d5990081c0c10a011810075240e240c140403508018012020b18603521443d8482d98440000000b408681d8281082502203401000c2c0510031100b8051b0141c141d1080036a40d0a03c1c11001980500444034900450350f40030010303010174403541d1030580040414a80595424541019100c07668450078602074180d1150b00c60f0390740b136002c140fa0030800c0c1c9218a5005504104078156285183c40e50002e5030702c0700002d040300ad61500841080c0f02d9a0881010010b948135042005106081c4900e40040960340001eaa0920039440084c4041c208080341d0b00c1041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 804973615 1250 804972365 804972383
    0x50409170d1104170d020102040b22050405010305070e0f0402060409020c2e1a01022a19051207051f021e03040608070f02070e13020a03050606011407 66
    0x22840014900080001c0307000008005a2850003003058400740c0c1103500100d805500121609903000c1003003107481c4d0110b130548000e518240c00c114440340305029a803031400984500c0c00001401c000c40c00e40d014040d0501620400c02c1b50303902d00301103940b2003180c46441b484541d00d01c00300d40c4040c01c20508030300c103d4003c2c01c8549000e1924203044000d51001450078802e00620516103103901042c0c1070305110f2a40c41c1440810506031640c240200c2d1240b103140c004a41c1004042e010a03600403980e840c04d5000301144e460381d810400d0000201c04290398a440e07010a4104403000f103112000c001c0f000b921000d94080f04850380f1071800c00c1e55454540038080d030005003d104400086c00b14440940c01c1540b61041d00d10b491061f001e0b11055044000381c2d1600c540001c1414004290310081550303001030245400d0305403c680c840041d4590f545401440002050300c6c001070502c180036030160030b90715406401500304035900d0900a481e034070284c51290000b445e01c0f6480041814003c25a1820b0b90000030380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 804974865 1250 804973615 804973643
    0x90910060207061b0b0106110c0613050613091104032a050f030309060c0105040203010b01080f0115090803180a060302070201320c03030412080c0d050a0615090906050409 75
    0x640701010364044041d10502044e13003000c0007a05030580b01d4020b040c951518080120b200a1080c2080503d0095070300624060044244104a51f2051002c075241070321150b907608004440010952605c0d00501c014504040440d031901000d1801841140d000e0760820035580d504050b15000100300800044c0c10200c0c841d400c0c4450300c0d01c80500c5100101c02800c46c0d14000701c0d18041901904000740104840e590f41d0200015400c0a00811410107001d29040280d45000040340e030181c0303810701505a4440c00b0040c0c050780c0324040c0c03000e480070f004403004582d1503401780461a40380525048640b07000f030300d0301d100001d13403240280260f80c0c0e00f83e4140c4800b4810605925407420300407400904840c01407580c00c0c100c0400c0e480e58010300c038600c00d640c0615030720710f01400c1c42c10011402840010800c00010104003d034046082079605d0595111004102503c680c01c1c200054000c0e0342201c52202d883d0581c512104c0c0d04114910708542c5038850a01c00e01d03035604100404c403042c0311405000341d80328081c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 804976115 1250 804974865 804974867
    0xa05060a080a0506041820040b0306010e09031204081911102307350a0905010905160305010b030d0f050a02100f0b01020c0d03020304050d050a050607020309091006020706 75
    0xf613030701540203000061607454003001150524080402030354080031000350402065004400741c00c0580013078400303012071400800030a0b0740c0c001c14810110341c1c180300d20100380000d0301841120b02c14000311800c0e0015003441d051044580d400781c095602c8051400c203c150b42305005043c44070004000401a000484412101c140504146c0d4040d070203192280046194445d00c0106550290269640708071400000f8043c0c2441da84145803600c207103081020340e01030b01f0b50f9070100469000755070040100e01c1008038039150380586440c1e2002051801880f848100784841c0c0e2446000701e0f40124028007030002c468050540f02c6110122020004c3c0320740f036215441500440050a6442c1c00d441281c9610009406800407100510b42d02400f4640341c6aa074659980c0c100003030007540ca02180c1718002800507541c065503a20440c8560350150788204071a100348001840848440364022058409516007404005c3d00e030b501c681516446907580304041000b40822000400613500b990b001040703807a081000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 804977365 1250 804976115 804976121
    0x40c1203050c12090a0e01030203060112080c0d181205100507090b030109090b070302090a1703280906021c03050a0b030a060c0f0e0607020f01020a02030613020a05060a080a 76
    0x280960502004000d80052400d0800a4088804002e0041c64448030b04900f00051580c055005601102c00e4800500150f07038003058440c1114840015943c05548629241a00d4010220056140e0080009007864160040a109100c40c0080c4841c01e21980310007240320030304141407014005034000d01c08110501c441d54445c0e6045400740c18503040d0540c0c0e03050954841c2c0d000b60040b211307a5071100200810070200001440d00203032039040c258140708038840411004200351107190742504078803011590025082c0112038020700c5024802ca80a24044651940000e1810070400043da030f40302e000031510310110390314110b1a208003007200c0041408070110081d007000b400c040e45403651603c01c0b0005035010402150b010f84034100104000714680c0f0050924521600501d00784540c060640003590780d541c04650384103030f046a49401d0103c2002c0101e1828860480c020f405202c1ea009011401003403810700610310780300304d402480c070384d031214207100440c05035841000100f014403010603d4808250 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 804978615 1250 804977365 804977399
    0x140109032007030c0602070e070807020a03030b150a0815060f0f0903120a080f0106080705040902030415020304080d0506040908030a330e010b0a080402091e0117060f040c 75
    0x100490b04110303160b407100c1110744100d82c032070000340c0d1010008208011019005641c001c4150501002c5494007804c040c0d1540980c000040030590749034a060b055039901070b100007240aa4010b0282c413616900c4024054410030b0300e085130f4000200c03e1641c00ba1070810f040301e410700c81403c00207060000000d2410290f42182d5000c80e40b601900240c200242a058090207000300c0d560784800c544c3c01c02010504140b401038014000300b000070340c200840f0039081b2086600f29105c0120040e500e59690a25185008481040c0340045e800081407100f4420020054140000d103124200110b031a0f2500300011545040d2004100f00c8061001503072041c06584260000c0c4d144003500340d0404104a0f81c481c803041444ca82e00e80805141c1010b20a4a4010402030f0140940000243c90800c8012001c2e08664000b00001e2013121500c002414080c80d40802240ca00107850007032842d940c542107408001c181e100c1400c1d6151140700005614429441c40c818002d80e0070012110b409420040043d46000d100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 804979865 1250 804978615 804978677
    0x1f02040f2105030d0b01030507030608031918030f03080c07020901140621070f02061902131205033f060301140f09070f180c030e0f070314010903 64
    0x1407804101165080c002090644440040040e10107071940002d0100e0740b016100101300f51402809000301a800003c84119040302e0700300001c88591580e08603951100441010a40008020001f04000542c030f0844141403103034a801090356500880c08c05540986400070b076011480c0401040b040e10b80c45010043d0101c0038101c1442d24043c450507011200207100d0b14502ea19044041000072075000c33103d143c8581032480a4502810030a4502c4a00c05d11039241c2c4911950008401d1040d450303200c08000280701144542c2d2440c1130508207252660403807056041c0305950301842d030340941c080c070900f0b151581c5d0940c001401c0000d20140144d1182d001044a0b4041d0350360300014001006048100f807041c49aa061607850b0305d40800b000d4200340c91340c2c3c00310103220020b207014062401100c8403140c1c0441c411000041c0580140411000780060500c01c914900464414043c0068089100415a8050305401d80c1181280010b80c0c200e03000c0c0d60b00a0000340c1c00d03002c6091148190b031921030601d008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 804981115 1250 804979865 804979919
    0x15050306060a1416060b010e010503060415120501051f031e0501020d110301210201051603050405040e03180f01270803040f08060a0506011b02030a05010507021f02040f 74
    0x1c440f48034001035100920b40121680300002400c1042094084e00302a00c40031f28050207804c8814002911500000d0002c80c4110745410341134580803401000340c0c00178070340c3d010014002600390819034000c2005039400841000e1400315030480600542d24082200e500554445041c2103210000d0705519005100701e070301e0354080100030300480f29805612910301c0302d041c460703035254903001d80800700481c604036680710006102c0d810405030303030840195554148405066406490580380440b11403046800c1142e019140a01040c1001400000307003114480c0403860344000c82d48401004264040e243c8482d00040041d10207005900310f2200d03100c00d42043c1700703e07080d2880e2621545811900240c00c404284103d40c0000c0050900810400c1c2e00615150300070400c0e4104000020003228040c407200b0b10302e150b8044140119107041103599000398100000304024140854000d456094040e095412005e1403140e280c400c8c40d151084508590419104410b090300d040784e010741c03194a460300b03040e620740 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 804982365 1250 804981115 804981137
    0x24010818120a050a090824150d060606081302281d040209010f030b010504020a1803030915080f0a051009020a09030b0a050601021e030c070b0a020715050306060a 71
    0x62400c0640348080c91911800e84440d5a50030040924203e035001ba0740d260301c0f010040c054102485500301d2464101195148665600041c1d0300d4031075185400c9942220100c007000e401d0160705d0f0711800c2500d82c60b9496918a03120f80350518800c110b030202c041c0d4820b10f6030502c0700980605440041c54820b1088200101555682c0c3e42e15064010500c400240d080001c100011031600180c4030b805000400c0f000d186040c1143c558210903101402080d020700d0340010000c40c040d001309422075104182c9101c6a4050748c803890000c00e889190f21481d03c120321040324a1101c103014501107842940d11801c00003c982d1024100c2001c1d1201030911180c0c44c10940001c00c2440042c0000d04c1c0d0541c00352503c4d200c85245180480c50842d0007009550305501c0c1005200350381e0790101d203446144030684006202c09592014950a41c41200501d01d018450084002041c402c500c016008903c1c0503000d070307a042961224000f440740720100380c0c800040d10400008525107440805020701c1e031554600070a60362 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 804983615 1250 804982365 804982393
    0x10b03063706090e0a080a0507030507080309100e153106060f17061f050307030308010305010b010e10050c24090c011107050105030a020f040303050324010818 70
    0xc0541c401c0c0d000c01e03481e1030083c0815100b038001c145007840c0b140002c0004c0c503071a85503075045000f020300b14400c1010002307010082c18401e1054a1000381c110310314550782d040c0020401e0b84c80c180c050b441150182080da40c500001c0c00460000342404849000214a036195050080d142e071007909462a039601140000c0201c8503c0312003109064458900020700d81d081c8180c200c41c0e060030380d00403200745000380c0d0116020301d800310b50703290000481030782150300250369954006003130840d8100f03981522405000206243c0d10680c0b0504890290300204a40e50b680401140c6071026810300c42d070480782101d00c074200503209000a11695544400b0350724454402d2031040b019451200085203000b40c29402e024440030b051220b80c6640400342000800f41604803c4151103034050300c900350500c14040700050b201116601226540c46030f0702c0400d43c1e119202d2602810f190000d54001d590150300d18010740b10041804011884001c1c16142c00c01240d55407205590003c580c000c0300c45060040da04003070261 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 804984865 1250 804983615 804983701
    0x2030c0408012c030906120907032a1415071518111f03020f1e130b03040f020409050a06050c091002031612110601090906060602010b0306 61
    0x45043e40010075603901103141c2400e0302e2900b00000250000c102c0700b07500380d44403402c0764402000311041101b00e5442d0380020f4200561030b400941000905501c80c2c0d401034404a4568258240c1c80b212000c00313031181d216032074a0044400d140e810007101c10b0b0003c06c0c0a43c2c0e5009d040040d1160028868001c202040441501e8580a41c0006020300e11901d4042022f15465200d10301429942d210002e10001002c8002d0380040c54500c092640c0082c2400503021010125200040c090b0288418190100046c0312680d1043c818844500d801d91400301d00016558116030007990003004d0308500e500d054080100420070050200d070188039110501c000192a801141d00c1410350300b50840d01c4034010018400800c031542c0c0801e085400410071251030030800027800280300d8021285110b00c3c04252019202c140110b40314480e644145800003901c0c040ca5044124243e10401081c4219a41d0703081c00c0c0d098445001c4515410b4101100141c4a00d1519030343c0c4210300140c50f80c00070680240e42004181c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 804986115 1250 804984865 804984881
    0x807061d1c0215340f0620180103110c030f18040c020c01020609010603050a0b040609150501060f030c0f080924090609070f03030f020c06040803070501060b130902030c040801 77
    0xd40c00586107204500080d0751004910440201c00d161920041903441840f810701c1e545e001400d2a903268a40c11170488410080c0c03891241c0e000c0f5840c0d03100f0620f0360141359000400034081c0041c2c2422203000200e0403001c25240640b020320015400c01c1280d009509054004c08502da00c04105ea20310b101550f92076005400204003150064074510003503038002801c0ca040108060f0341a030501600308001880012412000e9400c1080f86015407981c0c90040060b00c15004041c1103180d440840c00c42075440c590040b4129209074684400c16960800240c3c1690b207514050350100310501802a501c50080350501e5124818105640000701141041d048003004410500403031052441001109102000410b8011410f0002003050b9403402082e108020840d002c024100883c440c81c2c0c0c1140d0b402005000e070745510080c0542d4540d9103c481003940c075004003030143c0359582000d0b00080e4400d030440442b1050030305130440c18445810003c1c2d001c00ba5101500c2400102020030002a14078000c2c0315080d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 804987365 1250 804986115 804986137
    0x301020f12040b01240c0204020f0a090f080114130f0c0621060b1e07020a030b04150b0a05010320070c150f020a03031d070807061d1c0215 61
    0x105600b0503061690322101c050304a4240610030072904600308804000521001043d46011007000b0076900c00f00d8040e02844e0520f4250940c0401c0401b0069004091107003680c0101c65040c040c6030b0780e080c1c032500384d1b520812442680300382180480c1c80c0b81c03142c15504112a000d039082019a11269540c200d404500d40c3c03094000401e0f4482c2a0b42500441c0c1c0c01040d4082035101c03d02245062000202081c400c0e20000f401d90010404002007980403003082d1483c042c0c000303204001c11603403410a45c104c4003084600320382241640d2101103541c5814820303081030200140c42500403500303210042d001001d891030074080402c598204202d14a400e24014030015204820311208035142000c0102000e4010b0200420f000b28165060f244941c0043c40c500016018600410540c1c44001104c41c061021a000d0325a03000c1c030540031030807140000b0103808882071566081c4000101982c1d071880764020b2000e03a03500190501001c1030034000340c4000400b0500041041b407405011105032406580101e110340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 804988615 1250 804987365 804987397
    0x21c0c030b0907050411180a0329070c1208100902030a0209011b110f0d02100e1c1109220f03172a16050c040b061c0b0301020f 56
    0x4458580c2c00e00c8018001c110036034040c4070031015680b03240518006d450711040d0503011260380340d6a0350742c0c06c0d00d000000c641201c7c4602c1142d500c0c0d05844001001e21081c103000c41c14100104e1103071880750b010406920341195a00044160006048a60b8031000e032048020345006100450720101c0c0e4030085008031100000141e503942c0000001d04221104000245d20242d40344603200803600b812030025054800700c9a4a01c12000900082c9100804c000060340200480000d030010a07007010307007440001003ca846603004002c002d4041f10306854441c004104882541d050440c5041c0207444640203044031209800124400c000600003101520050328056100110f400606420040c00b03c018182070f0f40c07040d150303d4446140341100c004d1118030f00c40d14522a83c0d0416450b800c1003504d801c1605807001d80d0003c40d460401d90381e45d6441d011440d1007189842401030b411300d842412200d07007907580c4c29242491034a00903444002c000c98490b940c1c055400f0072101c064000e4003c010240c010f8010044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 804989865 1250 804988615 804988621
    0x313060c021e07050907090315020703050f1c0501090c09091a03120301060f0206010e15010c051b2b022b060e190c18060f0b040303020f0109020607021c0c030b 70
    0x178401c40060300040c14403070192018004100c50000d000020005424050f0307079544e031440c0c112503a11442d2502c14801c400032403844444580d01040251041113a601444241d072500034840c100c0b04a091b501c004600359100c104940c0d01c8a401c1003410f4144000d0341050060301c8004241050340c00890136404003000801440216049001820306c1401e034402403c466040c02e150b0708000001400900903d5007008580d0403aa1151001e0031001d80c2c804103032174440c0300801040c82a4411111018400e005c00000c5172070051000c0081c05400030448c1c90022540d41c2502070003400055504041c0840c040008031603401000c0d10391540e9840c0c42035100183c1d00740d024030081e080080b41440c0d980340c4444aa8401c0100f51a83c0008095170800100488103030f45a0711050014245030b8445003140c181340720001580010a0003400443c0d0282c0c090b24051075498000d1400c8070400b22000750700080c2401080003605080440c0300261150110490700c43c1b2254890388107131000d56004880c0000e4000070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 804991115 1250 804989865 804989869
    0x3020d14011701020301151b0c0602010e0d020102090618030a0807030f08090c0f12010605040f14060105030c03040b070306030b15010e100c11031f060602120313060c021e0705 77
    0x510b150140003103003554100038100d50f680e2013040440c002c000341d1440302100150451956454658442810010182d903424007034080c0030203c2c0d00d1384080c0944040c14580314011300844081c007030020311041c6441d80001c44010562a08007809406d4803503201c1840015651000400e01140a5240c0b9007039540040c0d0001d2031800e0042000610303411a50900c4100d85502600c000084400c580c00c81c0d031240e408640d1401403540e54816035105041c00342031004d001d000d03400011851400c5146095541e2005c0042d541f520080e18204c025960400004022540107899203030000103500d404120710741c0d20745030503152007130030b6401070064100c03134038512015038005041d0007020300103850040c072000c00d83c1e4020f05a200c0c1100080c000404000d141e4050769020702007170350559800c140d00245144502004002400d8030702680707003d03100b9038120041030b003000415070f0700c01d409284c4119608182d0b55a0900503010800210081d4440d11488258078a64020400c20700302404005150440c0340c001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 804992365 1250 804991115 804991139
    0x307020304211b060c0b0a0f151508070f0e0d020915180108030a0c140f0616080402061c0b130207200901150c0615060f0e0f0d020103020d1401 63
    0x107620100004142c0b0308204c1903401c01c10010603075070403850740d800300e036982a006000f034142046001c104501d4000c04030310081c1008440d400745c0300960724400c00364003c03113003c0e11510740c11b48006001c81c620712052a2428460701c44800100c000ae026442825155800b01e01403040c150741d000070071403240300410310f00d091040300030b411070310000e00e0102d50b94907084503540c0b64414412100c04000c100b01c4014180304074010000302c401e01e818202d0780d2000c81d0715842c40c0c03190410384400c0c00c540a9800c03c1403225100303a81c8140150703002000245400d40715400f074007541d21400c01c160005a180d07500c01000d90b40718501d5079200543d108001d603540900d45840c4014441620781e1510303040400c1000b103459128078080701e040d0b41642520005501d0344050560310541d913424003d000c01e06000c100d0024140d0482d200c0200c550b1743c0c0310294602c403001c100703880c80d203026500d040e00200c6070310a01c461031420070303000490240181401450306920390f4106080e21258450359220b004420010080612020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 804993615 1250 804992365 804992393
    0xf05160305010501090b180d080309070f030b13050c030a050c0a05030316140f1b04050106050319020901050c0f0609150408031311120a03140717030702030421 70
    0xc901040650b0400300040d001040741e02685544241c0840d051504402d00100707041100d40003810048140701514100c18983d00448440700c40c0e015000e000255111001008003d0381d50040b41c036840356a034081c0800c940c034810312050320320b80f180d400c83d404161028084401d41d0b5024001034940b041c080c83c140506d20142d507200701e009600402404000341085038482c3c107900d81c4070100e002c014803c021047c1c0f400d040081140c580e4010001c2103c6401245101105420426a014070050380d0b034100550703240c001140c54401101040c50310007500d4046500030030040e601414640c0c10580741201e854500341c424804c2d818143d0049040c061200030811441d5840340c40501e845000e454642daa00d6403038040070304450b052080081900c410006844940d58132380001800c129981c00c049a8156618021118181d0210b00ca95401c40c10240c1034200b1941c0c1c16800030b0f8190304000d041c002101c1300382e100804000441c0818000814210040e80600022182901d80850a10180e0a00000a507544 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 804994865 1250 804993615 804993617
    0x91e180402100e0f040e120d0b1906051b070b0c0f061b0a08090a020d061d0c0607030e030c2d0402130905060d0507060207060e030c09190f0f0516 64
    0x20320680d03c090b40e1256002c40b4040d00a83c0e011900b085e049800903d070520828111440c004042581d041034a4983d005500b000e208903030384a003101072040032002d600311030300a000000788100b00750001c50030303084206222412002e040703c80882d51107080343c06a0b0805085440346402420482e103d45008001040e00031091100617071031609001040342040c40790764090014400703464006805254103224842519802402c40160b043e41d5290440041a82001c8999840150300d101e00e029a0f001801c00d403031040140c2441c1c50180f0a0718152000c84005005c0c40d4144102100c8203902d4807002d13601040c10030003c0a02c0f807020b40794051235000846211303080c0d003e14414030030040a1110b0704010070459410303000000e1103884280c04524028034200024003c0e1080311000122654009000c03001c0755015940d00c080c0005020805440b0880c88451591200e00d000c04075940a45001450035001071035200094628101d50f00901911018000304211030381d40d1080100f840b41000d010b207122511 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 804996115 1250 804994865 804994877
    0x10e0d41010b0303090909011b03061806060509040b12010f0204050a0b093d020c15090f0603071713020117241504091508030a0203091e18040210 64
    0x102c140030950b80d0140c400002d10501000c008141085020340c0080b401c02c04c0b20b54031822a080f1194060041c00c0d15200300c0d10960003001580a0303103c1548110341c00c1d0f40842d80d0302481c1103c041e0401000e0b0010410840e4072442c1d0980b03445c1c00c06401d101e14205418403460240e207403894134081007210010740d80700d81d05120080040c44016590780980b0044005d061904440c8600e43c1030365910f18083c040d8801e9140380c2480d401038032140d00011160074007070088410050340540c0314034030a07450207540f0f0140d4001c07030301821003003444c074082d0055a405101c41c68241ca4142c04091448900001940d04100c1802050a105c0665074007081e00e81903402c01028810403414140c643d40c40880483c0070b10101038010581451031aa034401103292400d164516040c0c6494a17003910f000202603e20f12801861216a4000760fa43c101206860491415802841c00e00901c4010301c001002007070007894400c900c80c100c003c020369503654210030810344003030143c3c00e0f0300e42403040c081507910218002d401e00407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 804997365 1250 804996115 804996131
    0xc150a060e130807031b06060305060903090d020d03020c0d0b0a05060904120f0e06040306050609010f0b07170706020d021206040227030f1516030b010e0d4101 70
    0x40e00402c2d0481907800000f1075070b079005909084400e442000340003d400d0110585d850188076140c1c0092040e64010310644043c0d03100c05031503941d248960740709947c1105840104001629001000c0001d55020f80140c61020030003600041c1640c03050f04044070703c0a03005090240f0304e40346109140c3d0144003547c07066068201920b50004d01c8a2402a60040000c0c0c1c07520303800c40910031341d210035182030301802c15038442c4e440b464918041d040c2140c3c07060103010a903000050282600c2d009c04200c1d0a0411294079007040742d160066281841680d407400c8200401c103034000540d0910007040c140b00c0c00180180c80700c04214015582e01d6014040c14492801800010f11650074250407000c01c0c0c04052034900035000c1f010109090241e07621258085010704006011480044518188038102c020040741551082c4401a000c0312040c0c0000350018041000c801c146041c50f20400740302c140119418412048400d4103011851264204442c04203001c40f8403882d1003155030096018042008000c0c801c0304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 804998615 1250 804997365 804997381
    0x405070806060715150603050f04030507080c070506191709030a051b030a23070308070305090138061611010c120f0f0e0a0b0f0c150a060e 61
    0xc00a4900c602c01c0c040040d4001c01c21110081c42c880c540c0040038180001202c1030742c071516942040c81202c1c0401d041c08009484a090550b10b81e20565050325418105016034441c0b040c103401048114549100c0c0f98404240c95a8810250054005030952041007a241c0c010082104000d0110161101c52400a001c40d100c4040161606e0036100d00d00742c0d860340d13208804c0c01000300c15440d00380e82c1400b0000350a0003465000717a445400742c46000c800d05c1c940a0085070040a4442c000c806000580114007282c441c51003500041d4007e1519800410903e51509250000e80c0e15000000070403030400c210381c1c030f22100100c01800e00410480d021800c0c821001d0030803003008036490004000052070491290f851307002d05500314126030809121400201c001c400940044001140d250115081402512215111311a42904c1c10390140c0780f002000e140a040d000103801940c1212014081442012241c01082008821f014002442e5021034103056080108442140d00800741c2400c07000c2c1008003603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 804999865 1250 804998615 804998627
    0x90e0309010f1b0606030605180d02030904050c0f0a0806102618070609091d150901020d020a02070510020106030c0b160b0a1b0807022e0e070311040507 67
    0x110b078203041c500040608540407500e02d600500e001000c42e45819008014028079030f002a1103001d00108811040c1c1c3c2504805a6a80c86094500016401001204d29a00b032680000e6017103400d04243e50b007080d4441c009240941c01c0001701c000004c58000802045140580304074011030840c1c20f25200c015141e4180340110140d4a106180c0d0300b4420001c15500c1d414540b001c190040c1960964503c5621410000c00305039042c403d0701e101c2414856661841d005002200310040000001007100806e140c840340203840000785421907556080c0803003d401300e075030b00050800003401c0c2d003d458400c0c1040300700061a10540002011680342040038400115200f00384000d0714043c9032905e8442004005500d00074500c100300401d80c0409806112502009800c400c1c030b040c0c001300d0b441c01360107481c4c801210b080d20b04641d0000143d0141980324111803080308180340a103405040380210340501101e40007030301c80800c42002035a020040400602400001807171034410111024040c9040c181c4c801003030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 805001115 1250 804999865 804999887
    0xc041b0e0a0f030318051906030f051005010815090a0e060a110f0c160b070b180601090b01030b04060303020a15060f060302090d0609060e0705090c0f13120c090e030901 74
    0x84c0f190099185d601070340b0086020000b0800101460151008442c1010900b40d10340314180c0464180320612808000c1d80c080c1030305c250f00a1103500b040524160044415400107400e4000400350745440108a45404086c14824940c0031400300e17440345461007030b610701040280900e601d2840c9c6202d0805070007940c000c50b051086103c5407661940c1c54000b40d14140801001c02400c2155011300004013850110060903220b4042e446a941d02c0e59200d00d0a08424081c1d0b0008950743c20020062102c030065500041400a06140000e40400130402117021135000760810340241c1d0000d80e1010400200c40400500c4010081c0244159450103151140c00360702030054009154000c101080c0f1a02c0704980100000d401c50818842580c00b4103085c03000304159891760740f19015200000c01c207400c150016900824001741002e203001c4a802c00b41d61241c110400640c00610019030001d21446c0c079070314413541c1a00520f546240f0340c1ca03002e080c80403620103000d410082c0d00180300b5856160b0700210035101c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 805002365 1250 805001115 805001117
    0x150102030c030336010f0f020c06071b05011104141c0b071202032406070b0c0c0a08040e070f1d0103110f0a0c0510020f1602030c041b0e0a0f0303 64
    0x1c002c41e10302c40b1900d00b28042451548042d0811151000e6607801500820320140c603c02c81004840808241f0106900c5a0100100c00788e10040214444600c030780407034440d4452605080100e0300030b554030182507403420b651101802070085000d0000300d020101c40c0101c17880c125400c024403400e800d035805150f400c02c1000f0780041002c000007803806018070300003616000c00320011542c4c2e18003071001c12017040b1521f2492036200405031008050f424003030201c494075030704690645055a030b095140041030f44031400c1d0444500644020300009007000020f03001408004c0c501034000e08e031020b0020103584041a804042200440f01211140f0a00c00d00c20b03000c400c20f20380861450140b0020707074014868906106410313000000d018240c980c0c000c0c0300d001c1c5244244180c0e841d819812600005901911078041d80708001000780d015080e0042030980022407001c0d05a85000301740800183c1202e07200c8010011151801c10b00d0001c456014101c21a2a0b8040320701c200191300b03100c00c12000f9642c40c00020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 805003615 1250 805002365 805002391
    0xb0412110f040c0822470f0a060803090d0203010f0c020604260306100324030c0f06020706050703031514031515040c021e011407091512090218150102030c0303 70
    0x400c3d8801d5948800c40d420100340d040100e1b50403000340403c42000c12603244600c01804008104200414040c00040300d521200039400c10243e8810811a0380900c80f089034150350300c001c00091080701340208815904036801814191400d4208444032000e181180b010b5142d840e520040407100300c2086e240c100038166000b00071044005e40640c000c14550440c00070400c8045900001d41948904d80402c1d0b030f11507504004456925070401c130410046015060268011040a00c18944508080c00c840c9029103130118240c1301007400e0081c50741140e0010511404002283c0c3d585040402460718421000b22036403119203403500000343d4050f0030003540d910032038440c00c0d0b5003941842004200c004680700820600300404180d1031900802046003280c2c3e86252490001c4c14060183c0700d4003080707546100d0202540100d156046445034040311036101c803941e54030034120160319032100d0041700d00021400800faa007030001c042d8010110321000300e0f0465001b004041d00308440401900d0700700701400420 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 805004865 1250 805003615 805003673
    0xb13110d09081204080a02010c02010509190206120108100b06070203070501200715020c0a0b040501052a010b010212090112090809030303040c0f0b0412110f040c0822 73
    0x100740d610950f00c06034141c103000814001444074403001066181c1ea00d4008002d203503d1017005a080c1c1e00f048601c0c01c51a00191761400e0180420400058810310003000d81e0702e484003d41c50310014000a0b00a500c650307201d4040c00d00040894803c0d0b0325600000c40d070b0309003082050340c006035403040785015079810044142c589440644100c03903c0c072031020202c4140da0680c2c0d19829040390510703a0107031070300c014443c601c10858641007600d2075405558180140720320700f0382003100558003a84411040d60301540424860400b040250116441c220103180022444c0010301000a1400220206d42a1f00c054108240e401a0ba0440b9515025034140345010485124074140380f06240200d15070705426000c008100004c00c42818051070580e0000c40c6895086900c031010310006014a006a449045100701d801c03000c10b00c0c04480c901d401800070100c201f0074091401107400d50300302d0000e01c400b1941c2d000034082a1701d4428580310360070400031040c85d490300b05603c886c0320100c440080c100e4082e40d041d00c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 805006115 1250 805004865 805004873
    0x7060f02162610230105040203070c060b1c03050306030d141e07020301060b12070201060e04031b150606030e06040f03142107110c01020705040c090e0a0b13110d09 72
    0x500aa0a04070031020080c1c040f91440300e004407030040341400313048003c4800114040c5024401e59020310760950742d50325520b00d103a1740e20008101c01d583c080d40c005010011184600d1050101c440464032a680b201e80320b0602e001418075000d101e40403901400b481210312000c024200c02601d66402c950ba04013401907421110102592250600203500741d400d0810100ba0408480c0081400c50450a6101c503150380d03142040382200c259010b01a00e4540701c401040c0400d00c0f64000f0407007a00d5001540c601c83e04996941c2c601421030005032046103480d000f0420045815100d81801004454080c014624140c0c0d510100802c981d92300505201800e10340f1901c5024401c15600d03000340220010384000d062400c1d001030004102c400c43d001a04403010340790b00c104003141903004003a0607001402003604110400c40900000710207141004088131001078252203128115019900700c440010340d41502d0704c00d200c4400010220040018180702207031241d0500c400c2101c0d00388201d00b400140821103850 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 805007365 1250 805006115 805006123
    0x9060118030c060201061508010605030c0c03120117010b091003080717130302090a1a06091302070f1209180b0112020a09090c0903080d0903020f07060f021626 70
    0x26000d082c9159011485640542c401400d0341d65001401c540c0241e00c000880b412407090098600050062000c034a0440829016050301909901541c1c1040200c07440d41c8100d80d000d9028403d20b40004140c01d144010070b100b50f02184d00152180e502916282c20b4400d8000403510000300f00c1c1d00001200b0081c13160482010312110321114003503980e40d1902e44182c030030340d640b400160f00c90075210001c074400c65000c0c482c200441141801c140d04c00004c1400304445074100a05040d0804a9a4030760341a04090344003e00d6100c2c80344140c400c80c02400e09081d400c0c4114100f2540a010901500340404040a1418007124071559800304e000f03c0300500403076041e803401c100f11000c180007003158040150041c04240989003100d4040210000c03040e4215002081c47c0710180580c10b08209a10b081801500700005181c0240100e070b0510305001c0c19a8130307110240e4000c80001b000c071002c0c04003030b660521010441000558071400c0090610018640b0280c4007211080d40c0042451020407400c4184 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 805008615 1250 805007365 805007369
    0x3130b0a1104120606030506090a03090b1813022a0f0102041a07020f090405011d0105060609010c020612312003100509100501080712230a03030c03180209060118 71
    0x34040e0b032340d282090b19065503140c040f9081200402c5615801003114221030007a601e200c01c4252000510010300000c0c05104880b2184130701c41e0b150201b01595542103685a01d221380c03160281d80045602298910906210b00001d101134280d004010070020b254034103101056461a03404141e0365004141700040c40c11402241d40c94001d1042000c010900c5810f40c824451006410f401881141d001e0304400d00301c4004881c4540c0c011070500020304194407074241d82c1c94462014202c2d0b4504000480c28001c0360308122203084504103660400c41040154544000004a01851403100101c113039440c0b98941745801c40c15000710405920301d410a0741d04001d04a10820580020444c074100040a662587c40d010f818602550a1200008102900094060071105500b00040c0032000c265501c48070406030044507186c140300c01a0840105405219604245200b92800208103000c1e8902500740e420441031050640a41c0180070301584480c04840d078014002d2130500a40400381d03206604450180e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 805009865 1250 805008615 805008623
    0x509120114010e1f27060b180102190b010e07050d050c130b030402150a0519020703060f050412120f0204030615082a01050c0303130b0a110412060603 66
    0x40000010f41485090080e801003849010300c03084185000d2007010160210300c40d4a1070703540b84002c1600581350b0003444010032424140082035550f60f0300d4900c845900814048120402405000f9616603010468090824604401891008090385440820200c1480352482c08941500015215841001110045a04c0c04410042c90905680459580d000125058941607100303c0102c0c1c0d1040d480300b40c9210796802801c80c07038034541d05a11852590001016441440340a000100440082c0381d130001ca21280c1d5401400000d1540c00c04ea01690014403048492600d001d060201003480328451005040c510300301104442c4000590600918501107407000851011a0100c2040640c0d0800c407030010b81c8c0402e8200700d60300d4a1210313459001e00001070350242e00e429607040404a80181d0f086418070305050031420a50380e041d405041d0b9108980f00c030f5a00a0b034080190801500302a00c5420000c500c408110300d0209440c0148540f25600501c01441003201080e0100031041e00008065644 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 805011115 1250 805009865 805009901
    0xf1a0706021c0b040608031206190b07060509010606030204060e04111b1b01030c021b030c06040308030f07110a030e0402070606030807050f0c0f060a111209130203010605091201 78
    0xc85864031000f440c2034014a4495400c129001400c00d800101b42c44c40c0080b50014015a0b0301c8131820044e003004e07290040607046410101c00a02c1c0f01c0d08102a28280f0700803100440c0c0e41c80e24040c86800c507009500048185072051000f4000d482c4d200906070222003003a5000070300d81a00046071030087c0181403504030050003c43c10b80c010f100c4082490f0034000042e5000b0b00e8004402001541500d07403c01514005078481d101c0140480c2584039108030709003003d0b095035514100480420349640c00780d0005d03a8461000010b010307004003030007070030750303002015103000003890040710304464607003458180c0901013001c04003851b001c0b070340e45d03038120303001c075075001c84100b00050f07507480c01c840749401c2844282e91600a01c800b428200c0c1011455801c0e00c04014149806000f98404004040d00038043ca48100042c070340c003260035043c0400c00702c00140114550180c82d0314034081044260005600e03402c801074014801004800c0d0810295465488212030440041d40c807190031a0050410009506600311 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 805012365 1250 805011115 805011157
    0xc0c0510111014100506030f07030212070f0f0908060117010e1b0312041d07031506093201050304031b1a09010203090d03050903091203030601090f1a070602 69
    0x606502c844480000000f8503160380d030301c0102c918002e00041c4165604070008100160107120010b030748030341c000c082e03050041c1082248140288031440c2250000b021403001c216180b04030f500200c90303c82d004107515140480c24180020140c40c1d90041c0716089440c1030040103440e0848083d000f00309004940c400f01c5242c242c10380c4104202d555494801406402003442c6c0c47d5031242160304403000c5e501a440403411080040803140100e04006285504259840301c84803040421000d2903402040699260200e0034201064904d200c84036907110010004650f1284040a03041ca205180b02002401d186840340c1d41c40c201a2000315429110100c90003256000c0d00c104800d08129820000f4144003a0043c0ea403280601400c0317200584d001e0104c0d074044030411494500c2500440d42c85204441500d050111110100300b030480b0400c0c0c2a02c0e650404000c00115580c0038101c1002403802e0301031500020302e020030320082d041d030759001d0100c00140003507050b0501c101d0360111500c0300da0344801603034110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 805013615 1250 805012365 805012393
    0x20a020312250f0f0804090f0b030105090102070c0314190303020c010b04020c0a0f080d090503090f010f080118020f0a05030a06090e030d02071115070b01060c0c051011 74
    0xa8000900c907011542034078200b110b8040e400080359400c40d4082200d100c0c401c2c20b07803a4007401160b007410458107032004201c0824001d900e4024000c5054058801040086080f0101825984000c01d0994182c1c03040c80071001140d80b000b041c108903500715241c52102c2000e0500c450610078100c407140c42e07000e403078280c502c201603141d8014075041e4000002081203c44c1141040284e1058240802c880d90240c0107072004140302c82c0c2c904854512a003a058507020110024a0079910b1010058855800118900d05941850602c0040c007200903e0400d120110605000d032601c081802280800500710100551096181e41110b038110741c000212600c0384480c10004001d0b0f802290003032640f50170310000141c1c1146d9400368040075013480c4065418101e18590352030094012810039a4480b06600c1c0700700079904c450b5402000800740d4050740e42e683d0f00c10300b002e40300301106078001010442c100c98100d01140e0a5142d400680f04100c40405840b00c551404031039a030001e030301112840c000d08020207401e03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 805014865 1250 805013615 805013617
    0x6031e070809060606070312051312030c030b040513030c0311011b1701030803010b0f12010305010203040201110610141f0203031f080304060e030f0304030803010f050d02011e020a020312 82
    0xc0c1600300c120f41c12a0346840a00c0b000b8020440700401003000300240400303606a50704010b9000d41c0351100c00c0165450307500c6810440f8681440d08021950350a6004413441d41030059131800001680c040c4003d0034802e00003880c006684c0320103010010882915400c2603c10f032645100c2d030800d00000c1c04280c80c408940e14142000c0880e03031000c0303117003624600d8205e60702d00780c00e9048a410100c01419a80f8082001e49141d00540480000407410014141400c0d03295050602071070242000585a10700f0b407002624004a181d669201644880b04102c01132407120032394030903100c0c0a00084442410740740814000c07401c41403440130700505020308207031559000000e94812408d1109030400030400014030000e100c164000c003809900200f206102c0c00780610301c04601c45a001c3c084429020141c2c0300c950454100f6001240c1c89000040100700d006407820143c405000d00319800c1683e0011503002904ca260303035508081c1030607140071941c1c02ca1030091020000c2950060b0a58200641580110300c20f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 805016115 1250 805014865 805014871
    0x206031906151d0d03030b150c1605011b020d0807060203040b0f0709030203060112051c090501181203030504210c05100e03070305181e18100506031e0708 68
    0x80e8481d614481c3d0780700210344a0181020182030600c07000e42c0b0b900c0407006401854031150300700e00300422071260138408400130618010003401030400710890448840c454600ca61220303042082001a00c002c1c0e14031a20781c095040d0f030407100018101c1d45403903d21541c2c003520401070100b0b4800720412090059440d9440c1c0320350b0a540c000c81080d030343d165003a41d2800701da0201942640c0518014003029405858801129028000711758400300c2c207000703114102c0b42903001a40007401000e4100082d50300406840003c1e400d412212081c2c0303007003200800c5101d00840d03001d0201511070340828148004220111319917031885109200402c1d90000242c00328100b0541100c2c203216807104031111028a209540342d22000c0b0015510b4004151007c5610303401000281d86100750149004c2c0c915030302d80c408a00780300486401c0e041240035000c00c0205148281209070b0600e0401d00400c4a182c81104514061390422102c080d2292215032045d030303441c46880940e0181a2000c01401209600281c003184 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 805017365 1250 805016115 805016117
    0x7030f03052d0d1e1d06010905070f030c11030408031b0c0f0613121104150e1b0405090112171801080a150e070e0a0b07020603190615 59
    0xba01109840c601d001c0d0b03a405850520890b4424440325202c0d041c150030080540c4036a80c581e514005404081c0c00840d0070300c001300201d1940b400040e00210304240f041d14010000c200c4200300a1812440c09403910900d400700074205940c6a41c01d2940307900484980d50300e240e00f00d00302c0b03849a032501d01e071030b03a44e42c44284005031407401d00300e202007504400140c1081c801d00c0039040c100a030341c0c80e000340821508000c115100082c8a0f0b100407aa05103500049020f03075008203000b981c1612824248001c80304000101403403c519900306121340c01e008000c19401c44981a884155488001459000d90049410a650020904000080720440040b03880ca003e4042e14a424102425124001c181c2c82110160301c003107000e01c0d4004400758007a25110727500c14900b40001c0348843c0c40220802da070348840d421400c0031030404404c2c46902d9a02c003009803116401554241461414062100340c04d0044980081c41000000b00080d110895660000710072401c100c0140f21098861000c000c4a8030700c04600b41c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 805018615 1250 805017365 805017397
    0x1050d150620030a200d030c030b03030309070312300e072114010e0f0d11070b0a023307030507120905070513020306121c08060307030f0305 62
    0x8004040400241e510750102c07402189442254041662401c1c00034009203c01c01504e4408a01389009000d030410504183e680000d000c4801100502151000c03400c29019610510800209240008100040e0394121031103140e060307920306088a103404e00311088488000c0030701c1c0000000702059052062519148424016000200da400d030395000544640181080c110b046861881f018031150400b10303005001c4004111200c0740f81500b9174052001107510366001a034421220074090002030000320482c074102074203d202c0c0010b555901c0349406041c080d0440000d200114900070010710b00b02c00c48005e0011030510320014401507038099110030184440c01000003590651081c0302d547d1041d121902e0b90442d080c0401402401002d800004642d2031041d13440c085034641d07070004881c050b1401e43d4000b60b5a072a0900070f100c21400c0344128110250302c0080a9850340d421002c0192201d9980d14225403280e4074800001d04e440b100d03a00241440c64860000b03018154418024500390078844049 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 805019865 1250 805018615 805018637
    0x10120f091b0b030f0a092919020a051e0421120e2b0816020f030105040f031116091d0f0706050a0201060b040801050405060106020a02010c02090601050d1506 69
    0x1803100c1c0c40102d40e4030b981a41030200003005c0e900c5035402004403d0207800d550013000b1034510840b022685c1141c0300303100c40d0700e98010051a240d00c42c0f01c001030031a015009500b0000c0e148400f910318080d4156002a0014940001181072144d0054600038040702941c2c40d85240004024030210165503070580d0101c008100b1030b00e229002e016056412040070300035510b503007022800c0072196841c80c0315450302f041e004d00003840450390700c10140c5248003680c40400515030b040d1040150b521408494140242d040c5810003004c1081621074520060f0035081183c41040c102d1601070501861450400030907800c000c020075100b000354070080b8548160035480700001d00d80c043d40f41d43e9004412801295030302c007120500c54544204050000318040d4000850051345980d202c2e4041e800a810501c000d0b9920030420082c0b1404001c0d40380108010700280140e940650002051185000c502902550b008800310782164498000c03213810015040042259400d2483e0f8038001940a1003440000354180d202 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 805021115 1250 805019865 805019879
    0x2604050120120c15090601140d0b0a02091f030213060c230c0303030c0d0612030801120201110d030506030714010503012d030f051203040210120f091b 66
    0x5100340e1001d500424024040e0181902036521103d10403d480c0225001000000860100e05000d500400d010749819810160030488002d600030f1490b00c50701000340c1503404151a0031a10b42c1044803a800580da030040c50007c142010180070300c0400c82c007040a0058103142d4590b0207881c0050b190f2050461403541d0b25811104248038840162045050404081040203840843c40040d02224265120035203c00000790440d042221210000c141c001030002e5070340d40a102d43c50107015079045d0003d0700159510003d0011105010703002074541e03140e68480940e8054460f0103201402d4000300c90060110940c02800f1f000b094900b01c0c0a03211702e90000c2407100c881c07004155403100603920542580e1802c1301d00c031030071301c030440d204052801c17512034140700d50400d611100003541c02030f003e8060030702403450900d2820803007103412840c1c5d103020300030f03c40147d884440e0388868a2152428403103440300441039000501041c0c0c0c65006040c588164402000000d02c40d51014888031000300340c02559443d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 805022365 1250 805021115 805021157
    0x50a151404080d0e07050301111c0e1f0b040207080c1b012a05030f03011805060a0e0a0b060c010b09010e1e0403120c080f160f030926040501 62
    0x3078000d14242c03051140d10000089039004100040d0710b0f40458100558800c00f02c0e0131903800311900741140c60b0000d6144c8800c240031084028410b021b0908121070781c48801c44a4403629070085002150054103051220072401d42c001550f2107000030011035560135545132030120796201d001d03100818003440a180203071031320700004601c50500603100c3c0e40c0759100308030669000076030345149880719009040d16140451030400240c101c1c89548025031343e0300d506161112401500011300303118000e09000401c0410380300c042e8003204039490001c0d03022442d25020041005803c00c00701543d041039010408044038034054100750b6003000140d0390285140d0b02d80c41c00300900c500456510a62105405404907824070129101c3d90040c002d152814411403181c01003c16a14801c00081c0091082f4090080120071542c8032030b0089550f10070800700a588610191040c401d5144a40c141603440406105004402c540034407920741107102426400f4105803010010781003405498005220840000d2502440702 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 805023615 1250 805022365 805022371
    0x209010f09060909090606080a0308090708072105030c010f0f06050d0b060d03020312070206070801050d0c15021009080d050106080c0403230d110f0321070c050a1514 73
    0x26841000450501801d4406003003080d0044031459500c7e00300003100e003014440b15046502ca5a120800783c1007030f0114500c0c021480d000754a261300040c108205841e0440407440798450180819203041c0751604106080d8020081002c15035400c0c01c05060010fa101c1d805a4040c0700a203400300406a19107040c42104000010028405240d000225000f07140010089000c03a10030320440b0301d4903140c4040120b20321003c0c0d40031005a40f01000b030240311500001498050075065400100b03030099038542c0c28400a8a10404030403a00c156100e00b01c03184248004000c0d0303c00c250090102070f4641c94124100d50014100c10040307440d140c004642c081c8501e40c514044c101c0c485005040c18107540321340a004a88401180c3c10401c4130034148204101030060001402c580c0d00c880e007103100990034031400d0000e07000d196a1285c1041201380207502c244500c240c44080c008031040342c02c5e96620305c1030310714554000019084d40b1418581e4010030485480c0701c4607a5a010b2000c3c801c07401254500c0c21000d02c02c7d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 805024865 1250 805023615 805023617
    0x617161404170a12020d05181f030e0d110a030e011103131415120a0f06090506041a01120e03090307080303090d0201090c030305160b0115020c0307080a0215070b0a0209010f0906 78
    0x1040800c0540607648c103c003904001c020500d6085c0154149441207228001c1d904a010907103134050203d4840b82030004c03501c0c0c44914140700990204c0f041050381c03904410364000b0103101c0700d43c0000c4040c1c4d00c00e45034800180e51040403039a6420300d0414104ca180c0c40761051400100a422042d030380d03400e0440f401c115041d8840c079490f050910301c40c1c60b0a0403900040003642d00a070340c2c05410061f401c4a000d100c00400e14500001003604021003840f054400c03207240240b21000101d080700d11641d20100140300c000d1b055100041c0600c403d03015505511840c683c40f2b601d8400c100010501d81d1022000314012506c50381190b007001c1c0d1036003040c0c0c20f80c0d00344200549195116101000030034018802461085654081d040386031026940d6155030071000c0c1c01000d040300c6084c00c84800340c2d404122505003141d0850052038407614000500307942c4c070b800c0314000b07004803607100241d0060519a81a40e0603198020400107180c50a2a09100203400c440b20312800194a0302d500e0540f94001c44581d4256105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 805026115 1250 805024865 805024867
    0x916090b0607150b0d03121a01081302030106031a0105120607051801050c070305010606030c05040e0c0f121f12170f090a0e010617161404170a12020d05 67
    0xc1510b40080e04208207030f000240d107450b40e030340c08034641c0c62500c4040344900c41e40300c806040808030652011070300e084a1001d903d40306104066001c0e80c210b10034503400007031014004510307903207440428090809a032000f080503401c2c14103401c400d1100f64032030381650345c00e1310100642e0340c640c0c0c1c10540e00c0e0010348038540814001c0164410000b0102c0200512140604046141121408540e1300d4466941c2c41a2080c0e59105828002c09130715000c0d0a003509003614104d0b00301030410600701820345026140da50448000200151030403a9201a510f0b4025109802da020b80352800001d5140c1a070801c1c1150027041180001c41d041e50380700f000e55211a0400e5440b820003a0394031000314079511000c8804200c5505106100301360b945c49800c200980081c42801ca01d65260a00290041400040e403031007030b042c0344040000b100c41107501201c4c001900e1400800c860407062280030244600c2c0c0243c511145442408001d00e1400990381c09881c0c030580010880080d07050b0100d0303d49201c0b0304610001a4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 805027365 1250 805026115 805026127
    0x15090d090b0910090806160f021b06130509090708010b060f09191802120105060a05180d081603120b1e0a080d02060103260306090a060b030916090b06 66
    0x740a0701450416115090018495171518030507498204101c80d0110004010007012a0030307940020444142d81040c001072107003156000b0b00c003414035003801225003d50408224210440780034410180200005010750100d818220f40c01501c0d1005400303052115070900346c0703c01c4941006001c0743e2130003071030724a4141042409810401c49820032510040100e076400300101c1d449585c00345800c0c0d405041c0c80010781d103020a48031500a90016401540314042c01e01040c540e0301d40200441d00c1c1c45928881000440c0c5040d400101c1c0c0d400725881c0582000301c0810803040118030001d440042ca4025250026410310f5010648241c400748584980c008d0b90f02c0a980283c001244020141094024103200005450f0f0310154580054003194000503400b000c010001d100896595040c20986180c0e200c403c81d810081c440035030320015003240d008585000015400c80e01a074090b80140074070051040d40ea06100309015950500342900350800900c240001034101958816070800c0d4801504403800e0203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 805028615 1250 805027365 805027369
    0x6020a030801090e0c04050c2a0d12091a0601030b0f0a05010f05120f0403261305030702040f1e020301050d03030507021c02150f09071e050315090d090b09 68
    0xd400138441004c2c4101110a141582c9901400c0e214501da00c880c04e807611501d40d51020310030007600702910188a02c50502020b484086162807503050141031203c01d400400c10780300300921450780701611010311100080c03001c80101904c1c03400348074266014426003a1810400415207460080c030303540b101c0c2c000420042540900110041a4280c3c100681042c8006a0308070b140c0340121580d0013282c8911007000109a00061f40d0072004807060044140203804c01c0c48880c030004058440d2110341402204002041010400c403a41c40e640a4420b0101d040e18080d8203000c0d0030340c2034109803254503054103c60910158400d4078102c900044c0480440c0415480a6006003070180501d011401040d041d10303a031003815401c0360603101107507004048980310540101950301d40900540c1000220070180024544c0c002100001e440201850341e45c4481079186040c02400c41da44055003501a1f041d1a604c40c130002200c05201d00408400d072807103440e03801000ca54003403042c01811410581030051001ea4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 805029865 1250 805028615 805028621
    0xb0f101103070807150509030f2a0a06060503010b01020f070506030604090803011205010c0c0f03180f06020307050c0a03020307060309080906040305030d061a09091005041506080106020a03080109 86
    0x118110192442c0c181103807100c0741d141d8000d15013660869114800c50003080164810745a00c41e6980c0701450800846d10506c4101c1e00ca03642601d21565445121100c85127400c03070340c0e01ca0400583d03085407101e00e503900e032280150200d485070350300c02d510b002201c0b1490750000ca60034a001d07036040040e000b05e40c28103041004941014120703940240c1d40711130344000990030030000d502030300700d8404880e000c05081c40d0243c20341b07801d64400800c024074034044000044c200a1203160301c82c7d050515440200381ca40101005401561100e40c038564100400503503d0740100090481d28007078003e85448242c20010300c800d0a03528071000790140c5c0103000410089129600100c90a88909041342c60000800002078403600290002d0761580c2000030030b070403a1038091007010002c102c0c518090700c0081c0c40410068040c0211500b0314010207194000030560b280012891020308402401081142d02200d60104d08101f540981e10104180380008030f01580000f070707003407a0a503041d55a8030300c81c0e0800e0142e0b805 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 805031115 1250 805029865 805029887
    0x6060f0310090e100c090f0e04062403050c03010e03041a16030e090609190c09030b041b14060405130902090c19030e1c1119060b0f10 59
    0x101c08038050010620701164010b030700b281070880380204211000c005540e011079003152111414001d040c03404002018441c01500201c42194011308000d6880b8105500034010030030400701e40180700c02820050350b941103a4142500d00410840e01c0309420300301030500302c0e007518601151562003440300300449030b90343d50310b41d01d4403540401450034a10301299000d404000301c4000c4010840a1072200d0150070100c040ca80e01003c212040000c600b070040e0741e00034140159141200254880105004a60040001000541c0d200040032000c2c40d00d42804e07420310681078400b00140103441c00010f442062140c1e8820000701c01030142d0710b0a0710305000c200750305013000141104652a00348e400003507130340c11024a00c02c400300071103195116101c044241d06e00c840510b406042c0b624102156042e050001000307100e070b1100809035000c0030004102581c0d0400344c90117441d07545c400c0130420b9a22803000500c40c141d2512404043c0009011441000440c1c00881030b141c0d04404001c06040c06503109820340d405c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 805032365 1250 805031115 805031131
    0x22d040b0604140a08010e0c040b220203181b010f020615010806150d0902040608030c03070213020708190801050103140f0a11071a01050904330c030e0d0806060f03 72
    0x5045035175049030341e0944810304441c0500b50444400091642040c0c00b515171800c90481e0810498840007905092220200d811000030390790110029500f01514503160549060404c1203615600c07180d0a201e007940b40a8100318009160001c0c900340c41400007a1150194070300ca8004071a401031040111b42014004182c40e0340460058402034071201540b005049040080c0e2002c610b6100500501c815122a503003c518141d00c00c00071020700d01004410b6510480e0304540d42140c03840d840040c1e002a000e10400034280010014694100754440701203540350381015251008180e80c0c48e030040d41100d07010003034091950361038000149050100184164041065000000c0803644980030b0a0719030401c4d003003280c0f02402096610301d8022a14240340c01824220b8060302c452926540706440007280000c140e07824a05a0301c151011403149002c0070900c1d103000301c10000300740701c2240100507080360303060f0ba0b24038010b407031442d0701c0329200e03d420350322070880a06520b00d0000030004003491540000c10541c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 805033615 1250 805032365 805032379
    0x108060a0902040207060c3b0d050c06031603050c0901090e060d0b10030c171c03020919050405090109410f060c0a09060309030c022d040b060414 64
    0x80041e80e54070a0144040c10342d541d00303071b8080c210200350003048d08800502040c01d00098480e642c00034042030301c1210401c01d41d84070f0074444403031030103500d842c6001502940c052030110030040074002a00c0a205a120141e80511854864802c0580c6601c02c007004180021440e02040c49031021107881e280d00110042c10b80c80114103d0744681e8011107050715580e11801504400f04184416400741d04003415002051ba004d0140d0b01c4481940c4440d81c40c141e40d00c0b149035845441d001c03800380c0e041e100c01e04e0780a00f0b21710307000040f280c07904070441490095601c031300c1c9800d0104103001c1c4144501048280e00040c000b030300381c1c011464407110756544084000c51a501d0460043c1e840d500d01981070541e0780e40d400510042ca9411201414690003c04000315200148100d956207644042c1e40400c4030894200010b600d0118102192404080c0c1c8000e034101c402415921404d50030402041c644405426802e00704c81c0c019000c000644002d030b82090b5104105200c141302c250034130700f60020100002000720b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 805034865 1250 805033615 805033627
    0x30909071e020304081b031c1e030902040e010c080a0b0d020a0b0a0905090c0313030e03030c0c0109050a060507110a17010501030c0b0403022101060b040b04150302030108060a09020402 81
    0x3990075180000072480050700046030400c60340b141000041407941a502c40c40c3c902c0e10f040000300340d840c40c220480d1035000314a0002c84070346c2070150300000348100c0e1b5108100e050711000354000c6e001c4c0240030400ca002d5407030901141d80008040c030a180200e081c1c0d544140d0303103031114a0304002070000040d04550210720005c038480140e403080711a5008146212a0030349400c0c42400103088030300184d000340e00480f1250100030101c920718007182e50080880d410042511100d003400c40b400411044c140750107100c0051543e05a6100050100505000740e0f10010b202e500e442c240900b081c5140301c1d403008144140310741c0f800914082c400c9610008003400c1d44107178a43c2d4a01b05041e010703401c2c000e5181c59540c0c4d00140207000c07030900104003038007aa5100320b14042c55a0301180c2c601c24508442d084032041ca407045801e024003900030324001c141c0c04413115101c036110403074610240e2041c41100e0708280d0100d60400103500038000c0d02d04a032042006014039a0780c081c844400b400c11848120b9003c0e03801c00c60 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 805035971 1106 805034865 805034897
    0x50d03080c0403020d0f02100201021602040b0d1b17030a050f1602090702030c060a09083a020a1209050c1203040518061003090503090907 61
    0x94821691681903491042c01283c200035400081400ea070014400300710503810440340210380420503180444000c1e4203e10805d0039000c0400b00803142c110244c5060360010309042e0700070381240c100600719503411110440b05507040740c00c1e8401890510448800130b0070940100000d074015031030042c0000000d0920b0041202280c04200000ba10300c410402c15400c95040560141810100d401c02e920040e4a0b41c200c07191800e420703c65071001030781a80d190702521a0061300700ea40149440d04003a079443c01d80121040c00605401e94016800f001c40703080e80d1000107980402070060712030a5800c1c0c020b02128071030502c08101c030304046d11080880c1c404150200420000c540e40c0e03040300741c8042c4035411409190b00956100c030843c001725007881040781d00d2520403034040381d00c900d01400e8505c1c02d44c1240c0300020050048c1c2d1091011100740e05101d0b403001d8015402d420304e110390a86c4040b07 = true := by decide +kernel

theorem cover : BRFrame.Cov 804856115 805035971 := by
  have h0 := BRFrame.cov_init 804856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 804856115 ≤ n) (h2 : n < 805035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
